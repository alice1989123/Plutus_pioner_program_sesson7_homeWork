{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Week07.RockPaperScissors
    ( Game (..)
    , GameChoice (..)
    , FirstParams (..)
    , SecondParams (..)
    , GameSchema
    , Last (..)
    , ThreadToken
    , Text
    , endpoints
    ) where

import           Control.Monad                hiding (fmap)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Monoid                  (Last (..))
import           Data.Text                    (Text, pack)
import           GHC.Generics                 (Generic)
import           Ledger                       hiding (singleton)
import           Ledger.Ada                   as Ada
import           Ledger.Constraints           as Constraints
import           Ledger.Typed.Tx
import qualified Ledger.Typed.Scripts         as Scripts
import           Plutus.Contract              as Contract
import           Plutus.Contract.StateMachine
import qualified PlutusTx
import           PlutusTx.Prelude             hiding (Semigroup(..), check, unless)
import           Playground.Contract          (ToSchema)
import           Prelude                      (Semigroup (..), Show (..), String)
import qualified Prelude

data Game = Game
    { gFirst          :: !PubKeyHash
    , gSecond         :: !PubKeyHash
    , gStake          :: !Integer
    , gPlayDeadline   :: !POSIXTime
    , gRevealDeadline :: !POSIXTime
    , gToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON, Prelude.Eq)

PlutusTx.makeLift ''Game

data GameChoice = Rock | Paper | Scissors
    deriving (Show, Generic, FromJSON, ToJSON, ToSchema, Prelude.Eq, Prelude.Ord)

{-# INLINABLE emptybs #-}
emptybs :: ByteString
emptybs =  emptyByteString

instance Eq GameChoice where
    {-# INLINABLE (==) #-}
    Rock == Rock = True
    Paper  == Paper  = True
    Scissors  == Scissors  = True

    _    == _    = False

PlutusTx.unstableMakeIsData ''GameChoice

{-# INLINABLE beats #-}
beats :: GameChoice -> GameChoice -> Bool
beats Rock Scissors = True
beats Paper Rock = True
beats Scissors Paper = True
beats _ _ = False


data GameDatum = GameDatum ByteString (Maybe GameChoice) | Finished
    deriving Show

instance Eq GameDatum where
    {-# INLINABLE (==) #-}
    GameDatum bs mc == GameDatum bs' mc' = (bs == bs') && (mc == mc')
    Finished        == Finished          = True
    _               == _                 = False

PlutusTx.unstableMakeIsData ''GameDatum

data GameRedeemer = Play GameChoice | Reveal ByteString GameChoice | ClaimFirst | ClaimSecond
    deriving Show

PlutusTx.unstableMakeIsData ''GameRedeemer

{-# INLINABLE lovelaces #-}
lovelaces :: Value -> Integer
lovelaces = Ada.getLovelace . Ada.fromValue

{-# INLINABLE gameDatum #-}
gameDatum :: TxOut -> (DatumHash -> Maybe Datum) -> Maybe GameDatum
gameDatum o f = do
    dh      <- txOutDatum o
    Datum d <- f dh
    PlutusTx.fromBuiltinData d

{-# INLINABLE transition #-}
transition :: Game -> State GameDatum -> GameRedeemer -> Maybe (TxConstraints Void Void, State GameDatum)
transition game s r = case (stateValue s, stateData s, r) of
    (v, GameDatum bs Nothing, Play c)
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (to $ gPlayDeadline game)
                                                     , State (GameDatum bs $ Just c) (lovelaceValueOf $ 2 * gStake game)
                                                     )
    (v, GameDatum _ (Just c), Reveal _ c') 
        | lovelaces v == (2 * gStake game)   -> if beats c' c  then 
                                                Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)
                                                     , State Finished mempty
                                                     )
                                                else if c' == c then 
                                                Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (to $ gRevealDeadline game)       <>
                                                       Constraints.mustPayToPubKey (gFirst game) (lovelaceValueOf $  gStake game)
                                                     , State (GameDatum emptybs $ Just c') (lovelaceValueOf $  gStake game)
                                                     )
                                                else Nothing 
    (v, GameDatum _ Nothing, ClaimFirst)
        | lovelaces v == gStake game         -> Just ( Constraints.mustBeSignedBy (gFirst game)                     <>
                                                       Constraints.mustValidateIn (from $ 1 + gPlayDeadline game)
                                                     , State Finished mempty
                                                     )
    (v, GameDatum _ (Just _), ClaimSecond)
        | lovelaces v >= ( gStake game)   -> Just ( Constraints.mustBeSignedBy (gSecond game)                    <>
                                                       Constraints.mustValidateIn (from $ 1 + gRevealDeadline game)
                                                     , State Finished mempty
                                                     )
    _                                        -> Nothing

{-# INLINABLE final #-}
final :: GameDatum -> Bool
final Finished = True
final _        = False

{-# INLINABLE check #-}
check :: ByteString -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
check bsPaper' bsRock'  bsScissors' (GameDatum bs (Just _)) (Reveal nonce c  ) _ = 
     sha2_256 (nonce `concatenate` if c == Paper then bsPaper'  else if c == Rock  then bsRock'  else  bsScissors' ) == bs
      
check _       _      _             _          _              _ = True
 

{-# INLINABLE gameStateMachine #-}
gameStateMachine :: Game -> ByteString -> ByteString -> ByteString -> StateMachine GameDatum GameRedeemer
gameStateMachine game  bsPaper' bsRock' bsScissors' = StateMachine
    { smTransition  = transition game
    , smFinal       = final
    , smCheck       = check bsPaper' bsRock' bsScissors'
    , smThreadToken = Just $ gToken game
    }

{-# INLINABLE mkGameValidator #-}
mkGameValidator :: Game -> ByteString -> ByteString -> ByteString -> GameDatum -> GameRedeemer -> ScriptContext -> Bool
mkGameValidator game bsPaper' bsRock' bsScissors' = mkValidator $ gameStateMachine game bsPaper' bsRock' bsScissors'

type Gaming = StateMachine GameDatum GameRedeemer

bsScissors, bsPaper , bsRock  :: ByteString
bsScissors = "0"
bsPaper  = "1"
bsRock = "01"

gameStateMachine' :: Game -> StateMachine GameDatum GameRedeemer
gameStateMachine' game = gameStateMachine game bsPaper bsRock bsScissors

typedGameValidator :: Game -> Scripts.TypedValidator Gaming
typedGameValidator game = Scripts.mkTypedValidator @Gaming
    ($$(PlutusTx.compile [|| mkGameValidator ||])
        `PlutusTx.applyCode` PlutusTx.liftCode game
        `PlutusTx.applyCode` PlutusTx.liftCode bsPaper
        `PlutusTx.applyCode` PlutusTx.liftCode bsRock
        `PlutusTx.applyCode` PlutusTx.liftCode bsScissors)
    $$(PlutusTx.compile [|| wrap ||])
  where
    wrap = Scripts.wrapValidator @GameDatum @GameRedeemer

gameValidator :: Game -> Validator
gameValidator = Scripts.validatorScript . typedGameValidator

gameAddress :: Game -> Ledger.Address
gameAddress = scriptAddress . gameValidator

gameClient :: Game -> StateMachineClient GameDatum GameRedeemer
gameClient game = mkStateMachineClient $ StateMachineInstance (gameStateMachine' game) (typedGameValidator game)

data FirstParams = FirstParams
    { fpSecond         :: !PubKeyHash
    , fpStake          :: !Integer
    , fpPlayDeadline   :: !POSIXTime
    , fpRevealDeadline :: !POSIXTime
    , fpNonce          :: !ByteString
    , fpChoice         :: !GameChoice
    } deriving (Show, Generic, FromJSON, ToJSON, ToSchema)

mapError' :: Contract w s SMContractError a -> Contract w s Text a
mapError' = mapError $ pack . show

waitUntilTimeHasPassed :: AsContractError e => POSIXTime -> Contract w s e ()
waitUntilTimeHasPassed t = void $ awaitTime t >> waitNSlots 1

firstGame :: forall s. FirstParams -> Contract (Last ThreadToken) s Text ()
firstGame fp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    tt  <- mapError' getThreadToken
    let game   = Game
            { gFirst          = pkh
            , gSecond         = fpSecond fp
            , gStake          = fpStake fp
            , gPlayDeadline   = fpPlayDeadline fp
            , gRevealDeadline = fpRevealDeadline fp
            , gToken          = tt
            }
        client = gameClient game
        v      = lovelaceValueOf (fpStake fp)
        c      = fpChoice fp
        bs     = sha2_256 $ fpNonce fp `concatenate`  if c == Rock then bsRock else if c == Paper then bsPaper else bsScissors

           

    void $ mapError' $ runInitialise client (GameDatum bs Nothing) v
    logInfo @String $ "made first move: " ++ show (fpChoice fp)
    tell $ Last $ Just tt

    waitUntilTimeHasPassed $ fpPlayDeadline fp

    m <- mapError' $ getOnChainState client
    case m of
        Nothing             -> throwError "game output not found"
        Just ((o, _), _) -> case tyTxOutData o of

            GameDatum _ Nothing -> do
                logInfo @String "second player did not play"
                void $ mapError' $ runStep client ClaimFirst
                logInfo @String "first player reclaimed stake"

            GameDatum _ (Just c') | c' == c -> do
                logInfo @String $ "second player played "++ show (c')++" it's a tie!!"
                void $ mapError' $ runStep client $ Reveal  (fpNonce  fp )  (fpChoice  fp )
                logInfo @String "Player 1 reclames back half of the Stake"
            GameDatum _ (Just c') | beats c c' -> do
                logInfo @String $ "second player played "++ show (c')++" player 1 wins !!"
                void $ mapError' $ runStep client $ Reveal  (fpNonce  fp )  (fpChoice  fp )
                logInfo @String "first player reclaimed stake"

            

data SecondParams = SecondParams
    { spFirst          :: !PubKeyHash
    , spStake          :: !Integer
    , spPlayDeadline   :: !POSIXTime
    , spRevealDeadline :: !POSIXTime
    , spChoice         :: !GameChoice
    , spToken          :: !ThreadToken
    } deriving (Show, Generic, FromJSON, ToJSON)

secondGame :: forall w s. SecondParams -> Contract w s Text ()
secondGame sp = do
    pkh <- pubKeyHash <$> Contract.ownPubKey
    let game   = Game
            { gFirst          = spFirst sp
            , gSecond         = pkh
            , gStake          = spStake sp
            , gPlayDeadline   = spPlayDeadline sp
            , gRevealDeadline = spRevealDeadline sp
            , gToken          = spToken sp
            }
        client = gameClient game
    m <- mapError' $ getOnChainState client
    case m of
        Nothing          -> logInfo @String "no running game found"
        Just ((o, _), _) -> case tyTxOutData o of
            GameDatum _ Nothing -> do
                logInfo @String "running game found"
                void $ mapError' $ runStep client $ Play $ spChoice sp
                logInfo @String $ "made second move: " ++ show (spChoice sp)

                waitUntilTimeHasPassed $ spRevealDeadline sp

                m' <- mapError' $ getOnChainState client
                case m' of
                    Nothing -> logInfo @String "first player revealed and won :'( ... life sucks"
                    
                    Just ((o', _), _) -> case tyTxOutData o' of
                        GameDatum bs' _ | bs' == emptybs  ->   do
                         logInfo @String "it was a tie!!"
                         void $ mapError' $ runStep client $ ClaimSecond

                        GameDatum bs' _ | bs' /= emptybs  ->   do
                         logInfo @String "first player didn't reveal... well... who knows what happened with him! but all the Stake goes  to player 2!"
                         void $ mapError' $ runStep client $ ClaimSecond
                        
                        _ -> logInfo @String "unexpected datum ... What the hell i going on!"

                        
                       
                    

            _ -> throwError "unexpected datum"

type GameSchema = Endpoint "first" FirstParams .\/ Endpoint "second" SecondParams

endpoints :: Contract (Last ThreadToken) GameSchema Text ()
endpoints = (first `select` second) >> endpoints
  where
    first  = endpoint @"first"  >>= firstGame
    second = endpoint @"second" >>= secondGame

