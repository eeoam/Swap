{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Swap where

import Control.Monad hiding (fmap)
import Data.Aeson (FromJSON, ToJSON)
import Data.List (find)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Monoid (Last (..))
import Data.Text (Text, pack)
import GHC.Generics (Generic)
import Plutus.Contract as Contract
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), (<$>), unless, mapMaybe, find)
import Ledger hiding (singleton)
import Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value as Value
import Ledger.Ada as Ada hiding (divide)
import Prelude (Semigroup (..), Show (..), String, (<$>), undefined)
import qualified Prelude

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

data SellerInfo = SellerInfo
    { sellerPkh :: !PubKeyHash
    , aAsset, bAsset   :: !AssetClass
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq, Prelude.Ord)

PlutusTx.makeLift ''SellerInfo

data RateRedeemer = SetRate | GetRate 
    deriving Show

PlutusTx.unstableMakeIsData ''RateRedeemer

{-# INLINABLE getRate #-}
getRate :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe Integer
getRate txo f = do
    dh <- txOutDatum txo
    Datum d <- f dh
    PlutusTx.fromBuiltinData d

{-# INLINABLE mkRateValidator #-}
mkRateValidator :: SellerInfo -> Integer -> RateRedeemer -> ScriptContext -> Bool
mkRateValidator seller rate action ctx =
    case action of
        SetRate -> traceIfFalse "seller signature missing" (txSignedBy info $ sellerPkh seller)
                  &&
                  traceIfFalse "invalid output datum" validOutputDatum
        GetRate ->    traceIfFalse "rate changed" (outputDatum == Just rate)
    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        validOutputDatum :: Bool
        validOutputDatum = isJust outputDatum

        outputDatum :: Maybe Integer
        outputDatum = getRate ownOutput (`findDatum` info)

        ownOutput :: TxOut
        ownOutput = case getContinuingOutputs ctx of
            [txo] -> txo
            _ -> traceError "expected exactly one output"

data Rating
instance Scripts.ValidatorTypes Rating where
    type instance DatumType Rating = Integer
    type instance RedeemerType Rating = RateRedeemer

typedRateValidator :: SellerInfo -> Scripts.TypedValidator Rating
typedRateValidator seller = Scripts.mkTypedValidator @Rating
    ($$(PlutusTx.compile [|| mkRateValidator ||])
     `PlutusTx.applyCode` PlutusTx.liftCode seller)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @Integer @RateRedeemer

rateValidator :: SellerInfo -> Validator
rateValidator = Scripts.validatorScript . typedRateValidator

rateAddress :: SellerInfo -> Ledger.Address
rateAddress = scriptAddress . rateValidator

-- | OFF-CHAIN | --
data SellerParams = SellerParams
    { aSymbol, bSymbol :: !CurrencySymbol
    , aToken, bToken :: !TokenName
    } deriving (Show, Generic, FromJSON, ToJSON)

initSeller :: forall w s. SellerParams -> Contract w s Text SellerInfo
initSeller params = do
    pkh <- pubKeyHash <$> Contract.ownPubKey 
    let seller = SellerInfo 
            { sellerPkh = pkh
            , aAsset = AssetClass (aSymbol params, aToken params)
            , bAsset = AssetClass (bSymbol params, bToken params)
            }
    logInfo @String $ "initialised seller " ++ show seller
    return seller

setRate :: forall w s. SellerInfo -> Integer -> Contract w s Text ()
setRate seller rate = do
    m <- getRateTxo seller
    let c = Constraints.mustPayToTheScript rate $ Ada.lovelaceValueOf 0
    case m of
        Nothing -> do -- setting rate for the first time
            ledgerTx <- submitTxConstraints (typedRateValidator seller) c
            awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "set initial rate to " ++ show rate
        Just (txoId, txo, _) -> do
            let lookups = Constraints.unspentOutputs (Map.singleton txoId txo)
                          <> Constraints.typedValidatorLookups (typedRateValidator seller)
                          <> Constraints.otherScript (rateValidator seller)
                tx = c <> Constraints.mustSpendScriptOutput txoId (Redeemer $ PlutusTx.toBuiltinData SetRate)
            ledgerTx <- submitTxConstraintsWith @Rating lookups tx
            awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "updated rate to " ++ show rate

getRateTxo :: forall w s. SellerInfo -> Contract w s Text (Maybe (TxOutRef, TxOutTx, Integer))
getRateTxo seller = do
    utxos <- utxoAt (rateAddress seller)
    return $ case Map.toList utxos of
        [ (txoId, txo)] -> do
            rate <- getRate (txOutTxOut txo) $ \dh -> Map.lookup dh $ txData $ txOutTxTx txo
            return (txoId, txo, rate)
        _ -> Nothing

type RateSchema = Endpoint "setRate" Integer 

goSeller :: SellerParams -> Contract (Last SellerInfo) RateSchema Text ()
goSeller params = do
    seller <- initSeller params
    tell $ Last $ Just seller
    go seller
    where
        go :: SellerInfo -> Contract (Last SellerInfo) RateSchema Text a
        go seller = do
            rate <- endpoint @"setRate"
            setRate seller rate
            go seller

-- ON-CHAIN SWAPPING

{-# INLINABLE price #-}
price :: Integer -> Integer -> Integer
price amtA rate = (amtA * rate) `divide` 1000000

{-# INLINABLE mkSwapValidator #-}
mkSwapValidator :: SellerInfo -> Address -> PubKeyHash -> () -> ScriptContext -> Bool
mkSwapValidator seller addr pkh () cxt =
    txSignedBy info pkh 
    ||
    (traceIfFalse "expected exactly two inputs to script" hasTwoScriptInputs &&
     traceIfFalse "seller not paid"                       sellerPaid)
     where
         info :: TxInfo
         info = scriptContextTxInfo cxt

         hasTwoScriptInputs :: Bool
         hasTwoScriptInputs =
             let
                 p = isJust . toValidatorHash . txOutAddress . txInInfoResolved
                 xs = filter p $ txInfoInputs info
             in length xs == 2
            
         sellerPaid :: Bool
         sellerPaid =
             let
                 pricePaid :: Integer
                 pricePaid = assetClassValueOf (valuePaidTo info pkh) (bAsset seller)
             in pricePaid >= minPrice

         minPrice :: Integer
         minPrice =
              let
                  amtA = case findOwnInput cxt of
                      Nothing -> traceError "own input not found"
                      Just i -> assetClassValueOf (txOutValue $ txInInfoResolved i) (aAsset seller)
              in price amtA sellerRate

         sellerRate :: Integer
         sellerRate = case getRate sellerInput (`findDatum` info) of
              Nothing -> traceError "Value for rate not found"
              Just rate -> rate

         sellerInput :: TxOut
         sellerInput =
              let 
                  xs = [ txo
                        | i <- txInfoInputs info
                        , let txo = txInInfoResolved i
                        , txOutAddress txo == addr
                        ]
              in case xs of
                  [ txo ] -> txo
                  _ -> traceError "Seller rate value not found"

data Swapping
instance Scripts.ValidatorTypes Swapping where
    type instance DatumType Swapping = PubKeyHash
    type instance RedeemerType Swapping = ()

typedSwapValidator :: SellerInfo -> Scripts.TypedValidator Swapping
typedSwapValidator seller = Scripts.mkTypedValidator @Swapping
    ($$(PlutusTx.compile [|| mkSwapValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode seller
        `PlutusTx.applyCode` PlutusTx.liftCode (rateAddress seller))
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @PubKeyHash @()

swapValidator :: SellerInfo -> Validator
swapValidator = Scripts.validatorScript . typedSwapValidator

swapAddress :: SellerInfo -> Ledger.Address
swapAddress = scriptAddress . swapValidator

-- SWAP.OFF-CHAIN --
makeOffer :: forall w s. SellerInfo -> Integer -> Contract w s Text ()
makeOffer seller amtA = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let tx = Constraints.mustPayToTheScript pkh $ assetClassValue (aAsset seller) amtA
    ledgerTx <- submitTxConstraints (typedSwapValidator seller) tx
    awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ "offered " ++ show amtA ++ " A tokens for swap" 

withdrawOffer :: forall w s. SellerInfo -> Contract w s Text ()
withdrawOffer seller = do
    pkh <- pubKeyHash <$> ownPubKey
    xs <- findSwaps seller (== pkh)
    case xs of 
        [] -> logInfo @String "no swaps found"
        _ -> do
            let lookups = Constraints.unspentOutputs (Map.fromList [(txoId, txo) | (txoId, txo, _) <- xs])
                          <> Constraints.otherScript (swapValidator seller)
                tx = mconcat [ Constraints.mustSpendScriptOutput txoId $ Redeemer $ PlutusTx.toBuiltinData () 
                             | (txoId, _, _) <- xs
                             ]
            ledgerTx <- submitTxConstraintsWith @Swapping lookups tx
            awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "retrieved " ++ show (length xs) ++ " swap(s)"
        
findSwaps :: forall w s. SellerInfo -> (PubKeyHash -> Bool) 
                                -> Contract w s Text [(TxOutRef, TxOutTx, PubKeyHash)]
findSwaps seller p = do
    utxos <- utxoAt $ swapAddress seller
    return $ mapMaybe g $ Map.toList utxos
    where
        g :: (TxOutRef, TxOutTx) -> Maybe (TxOutRef, TxOutTx, PubKeyHash)
        g (txoId, txo) = do
            pkh <- f txo
            guard (p pkh)
            return (txoId, txo, pkh)

        f :: TxOutTx -> Maybe PubKeyHash
        f txo = do
            dh <- txOutDatumHash (txOutTxOut txo)
            Datum d <- Map.lookup dh (txData $ txOutTxTx txo)
            PlutusTx.fromBuiltinData d

-- | TODO change to executeTrade
goTrade :: forall w s. SellerInfo -> Contract w s Text ()
goTrade seller = do
    funds <- ownFunds
    let amtB = assetClassValueOf funds $ bAsset seller
    logInfo @String $ "available assets: " ++ show amtB
    m <- getRateTxo seller
    case m of
        Nothing -> logInfo @String "rate not found"
        Just (txoId, txo, rate) -> do
            logInfo @String $ "found rate " ++ show rate
            pkh <- pubKeyHash <$> Contract.ownPubKey
            swaps <- findSwaps seller (/= pkh)
            case find (f amtB rate) swaps of
                Nothing -> logInfo @String "no suitable swap found"
                Just (txoId', txo', pkh') -> do
                    let amtA = assetClassValueOf (txOutValue $ txOutTxOut txo') (aAsset seller)
                        amtPrice = price amtA rate
                        bVal = assetClassValue (bAsset seller) amtPrice
                            
                        lookups = Constraints.otherScript (swapValidator seller) <>
                                  Constraints.otherScript (rateValidator seller) <>
                                  Constraints.unspentOutputs (Map.fromList [(txoId, txo), (txoId', txo')])
                        tx = Constraints.mustSpendScriptOutput txoId (Redeemer $ PlutusTx.toBuiltinData GetRate) 
                             <> Constraints.mustSpendScriptOutput txoId' (Redeemer $ PlutusTx.toBuiltinData ())
                             <> Constraints.mustPayToOtherScript
                                    (validatorHash $ rateValidator seller)
                                    (Datum $ PlutusTx.toBuiltinData rate)
                                    (Ada.lovelaceValueOf 0)
                             <> Constraints.mustPayToPubKey pkh' bVal
                    ledgerTx <- submitTxConstraintsWith @Swapping lookups tx
                    awaitTxConfirmed $ txId ledgerTx
                    logInfo @String $ "made swap with price " ++ show (Value.flattenValue bVal)
    where
        f :: Integer -> Integer -> (TxOutRef, TxOutTx, PubKeyHash) -> Bool
        f amt rate (_, txo, _) = getPrice rate txo <= amt

        getPrice :: Integer -> TxOutTx -> Integer -- make this go after price as a helper if TxOutTx isData?
        getPrice rate txo = let amtA = assetClassValueOf (txOutValue $ txOutTxOut txo) (aAsset seller)
                            in price amtA rate

ownFunds :: forall w s. Contract w s Text Value
ownFunds = do
    pk <- Contract.ownPubKey
    utxos <- utxoAt $ pubKeyAddress pk
    let val = mconcat $ Map.elems $ txOutValue . txOutTxOut <$> utxos
    logInfo @String $ "own funds: " ++ show (Value.flattenValue val)
    return val

type SwapSchema =
    Endpoint "offer" Integer
    .\/ Endpoint "cancel" ()
    .\/ Endpoint "trade" ()

swap :: SellerInfo -> Contract (Last Value) SwapSchema Text ()
swap seller = (offer `select` cancel `select` trade) >> swap seller
    where
        offer :: Contract (Last Value) SwapSchema Text ()
        offer = handleError logError $ do
            amt <- endpoint @"offer"
            makeOffer seller amt

        cancel :: Contract (Last Value) SwapSchema Text ()
        cancel = handleError logError $ do
            endpoint @"cancel"
            withdrawOffer seller

        trade :: Contract (Last Value) SwapSchema Text ()
        trade = handleError logError $ do
            endpoint @"trade"
            goTrade seller