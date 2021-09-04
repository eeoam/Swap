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
import Data.List (find)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)
import Data.Monoid (Last (..))
import Data.Text (Text, pack)
import Plutus.Contract as Contract
import qualified PlutusTx
import PlutusTx.Prelude hiding (Semigroup (..), (<$>), unless, mapMaybe, find)
import Ledger hiding (singleton)
import Ledger.Constraints as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import Ledger.Value as Value
import Ledger.Ada as Ada hiding (divide)
import Prelude as Haskell (Semigroup (..), Show (..), String, (<$>), undefined)

{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | The purpose of this contract is for a seller to deposit Token A
-- and exchange it for token B.
-- The price, that is, the amount of B to be paid for A will be determined by the seller.
{-# INLINABLE asset_class_b #-}
asset_class_b :: AssetClass
asset_class_b = AssetClass ("a", "B")

-- | We will start with a helper function called price, which, 
-- given a number of A the exchange rate, returns the B price.
-- For simplicity, we assume rates are integers. TODO change this to more realistic rate.
{-# INLINABLE price #-}
price :: Integer -> Integer -> Integer
price a_tok rate = (a_tok * rate) 

-- | The next helper function, amount_a, uses a function from 
-- Ledger.Value to extract the number of A from a Value.
{-# INLINABLE amount_a #-}
amount_a :: Value -> Integer
amount_a v = valueOf v "a" "A"

-- | This swap validator accepts one parameter: the current exchange rate.
-- For the datum, we use the public key hash of the seller.
-- As we do not use a redeemer, so it is the type ().
-- The swap transaction should have two inputs and two outputs: ?Should rate be another UTxO on blockchain
-- Inputs:  the swap UTxO that holds the B tokens 
--    and the source of the buyer's funds.
-- Outputs: The B tokens for the seller and the A tokens for the buyer.
--
-- We also want to support the scenario where the seller can retrieve the A tokens
-- in the case that they no longer want to swap. 
-- Otherwise, if no one wished to swap, the A tokens could be locked forever.
-- Hence, if the seller signs the transaction, they will receive back their A tokens.
{-# INLINABLE mkSwapValidator #-}
mkSwapValidator :: Integer -> PubKeyHash -> () -> ScriptContext -> Bool
mkSwapValidator rate pkh () ctx =
    txSignedBy info pkh
    ||
    (traceIfFalse "expected exactly one script input" has_one_script_input && -- prevent interference with other smart contracts
     traceIfFalse "price not paid"                    sellerPaid) 
    where
        info :: TxInfo
        info = scriptContextTxInfo ctx

        has_one_script_input :: Bool
        has_one_script_input =
            let
                xs = filter (isJust . toValidatorHash . txOutAddress . txInInfoResolved) $ txInfoInputs info
            in length xs == 1

        minPrice :: Integer
        minPrice =
            let
                a_toks_in = case findOwnInput ctx of
                    Nothing -> traceError "own input not found"
                    Just i -> amount_a $ txOutValue $ txInInfoResolved i
            in
                price a_toks_in rate

        sellerPaid :: Bool
        sellerPaid = True
            --let
            --    pricePaid :: Integer
            --    pricePaid = 0 --assetClassValueOf (valuePaidTo info pkh) (asset_class_b) 
            --in pricePaid >= minPrice

-- | Standard on-chain boilerplate
data Swapping
instance Scripts.ValidatorTypes Swapping where
    type instance DatumType Swapping = PubKeyHash
    type instance RedeemerType Swapping = ()

typedSwapValidator :: Integer -> Scripts.TypedValidator Swapping
typedSwapValidator rate = Scripts.mkTypedValidator @Swapping
      ($$(PlutusTx.compile [|| mkSwapValidator ||])
          `PlutusTx.applyCode` PlutusTx.liftCode rate)
      $$(PlutusTx.compile [|| wrap ||])
      where
          wrap = Scripts.wrapValidator @PubKeyHash @()

swapValidator :: Integer -> Validator
swapValidator = Scripts.validatorScript . typedSwapValidator

swapAddress :: Integer -> Ledger.Address
swapAddress = scriptAddress . swapValidator

-- | This is for a seller who wants to offer a certain number of A tokens for exchange
offer_swap :: forall w s. Integer -> Integer -> Contract w s Text ()
offer_swap rate amt = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let tx = Constraints.mustPayToTheScript pkh $ a_value_of amt
    ledgerTx <- submitTxConstraints (typedSwapValidator rate) tx
    awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ "offered " ++ show amt ++ " A tokens for swap"

a_value_of :: Integer -> Value
a_value_of amt = Value.singleton "a" "A" amt

retrieve_swaps :: forall w s. Integer -> Contract w s Text ()
retrieve_swaps rate = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    xs <- find_swaps rate (== pkh)
    case xs of
        [] -> logInfo @String "no swaps found"
        _ -> do
            let lookups = Constraints.unspentOutputs (Map.fromList [(oref, o) | (oref, o, _) <- xs])
                        <> Constraints.otherScript (swapValidator rate)
                tx = mconcat 
                         [ Constraints.mustSpendScriptOutput oref $ Redeemer $ PlutusTx.toBuiltinData ()
                         | (oref, _, _) <- xs ]
            ledgerTx <- submitTxConstraintsWith @Swapping lookups tx
            awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "retrieved " ++ show (length xs) ++ " swap(s)"

find_swaps :: forall w s. Integer -> (PubKeyHash -> Bool) -> Contract w s Text [(TxOutRef, TxOutTx, PubKeyHash)]
find_swaps rate p = do
    utxos <- utxoAt $ swapAddress rate -- get all UTxOs at swap contract address
    return $ mapMaybe g $ Map.toList utxos -- filter utxos for right public key hash
    where
        g :: (TxOutRef, TxOutTx) -> Maybe (TxOutRef, TxOutTx, PubKeyHash) -- return utxo and pk hash if it matches criteria
        g (oref, o) = do
            pkh <- f o
            guard $ p pkh
            return (oref, o, pkh)

        f :: TxOutTx -> Maybe PubKeyHash -- get the public key hash from a utxo
        f o = do
            dh <- txOutDatumHash $ txOutTxOut o
            Datum d <- Map.lookup dh $ (txData . txOutTxTx) o
            PlutusTx.fromBuiltinData d
 
do_swap :: forall w s. Integer -> Contract w s Text ()
do_swap rate = do
    funds <- own_funds -- add up all the money in wallet
    let amt = assetClassValueOf funds asset_class_b
    logInfo @String $ "available assets: " ++ show amt
    logInfo @String $ "exchange rate: " ++ show rate
    pkh <- pubKeyHash <$> Contract.ownPubKey
    swaps <- find_swaps rate (/= pkh)
    case find (f amt rate) swaps of -- Find a swap we can afford
        Nothing -> logInfo @String "no suitable swap found"
        Just (oref', o', pkh') -> do
            -- the B tokens we need to pay
            let payment = assetClassValue asset_class_b $ price (amount_a $ txOutValue $ txOutTxOut o') rate
                lookups = Constraints.otherScript (swapValidator rate)
                          <> Constraints.unspentOutputs (Map.fromList [(oref', o')])
                tx = Constraints.mustSpendScriptOutput oref' (Redeemer $ PlutusTx.toBuiltinData ())
                     <> Constraints.mustPayToPubKey pkh' payment
            ledgerTx <- submitTxConstraintsWith @Swapping lookups tx
            awaitTxConfirmed $ txId ledgerTx
            logInfo @String $ "made swap with price " ++ show (Value.flattenValue payment)
    where
        f :: Integer -> Integer -> (TxOutRef, TxOutTx, PubKeyHash) -> Bool
        f amt rate (_, o, _) = get_price rate o <= amt

        get_price :: Integer -> TxOutTx -> Integer
        get_price rate o = price (amount_a $ txOutValue $ txOutTxOut o) rate

own_funds :: forall w s. Contract w s Text Value
own_funds = do
    pk <- ownPubKey
    utxos <- utxoAt $ pubKeyAddress pk
    let val = mconcat $ Map.elems $ txOutValue . txOutTxOut <$> utxos
    logInfo @String $ "own funds: " ++ show (Value.flattenValue val)
    return val

type SwapSchema
    = Endpoint "offer" Integer -- seller makes offer
    .\/ Endpoint "cancel" () --seller cancels offer
    .\/ Endpoint "accept" () -- buyer accepts offer
    .\/ Endpoint "funds" () 
    .\/ Endpoint "rate" Integer -- seller provides exchange rate

swap :: Integer -> Contract (Last Value) SwapSchema Text ()
swap rate = (offer `select` cancel `select` accept `select` funds) >> swap rate
  where
      handle :: Contract (Last Value) SwapSchema Text () -> Contract (Last Value) SwapSchema Text ()
      handle = handleError logError

      offer :: Contract (Last Value) SwapSchema Text ()
      offer = handle $ do
          amt <- endpoint @"offer"
          offer_swap rate amt

      cancel :: Contract (Last Value) SwapSchema Text ()
      cancel = handle $ do
          endpoint @"cancel"
          retrieve_swaps rate

      accept :: Contract (Last Value) SwapSchema Text ()
      accept = handle $ do
          endpoint @"accept" 
          do_swap rate

      funds :: Contract (Last Value) SwapSchema Text ()
      funds = handle $ do
          endpoint @"funds"
          v <- own_funds
          tell $ Last $ Just v
       



