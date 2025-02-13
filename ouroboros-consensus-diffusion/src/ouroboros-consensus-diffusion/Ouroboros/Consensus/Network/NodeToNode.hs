{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

-- | Intended for qualified import
module Ouroboros.Consensus.Network.NodeToNode (
    -- * Handlers
    Handlers (..)
  , mkHandlers
    -- * Codecs
  , Codecs (..)
  , defaultCodecs
  , identityCodecs
    -- * Byte Limits
  , ByteLimits
  , byteLimits
  , noByteLimits
    -- * Tracers
  , Tracers
  , Tracers' (..)
  , nullTracers
  , showTracers
    -- * Applications
  , Apps (..)
  , ClientApp
  , ServerApp
  , mkApps
    -- ** Projections
  , initiator
  , initiatorAndResponder
    -- * Re-exports
  , ChainSyncTimeout (..)
  ) where

import           Codec.CBOR.Decoding (Decoder)
import qualified Codec.CBOR.Decoding as CBOR
import           Codec.CBOR.Encoding (Encoding)
import qualified Codec.CBOR.Encoding as CBOR
import           Codec.CBOR.Read (DeserialiseFailure)
import           Control.Monad.Class.MonadTime.SI (MonadTime)
import           Control.Monad.Class.MonadTimer.SI (MonadTimer)
import           Control.Tracer
import           Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as BSL
import           Data.Int (Int64)
import           Data.Map.Strict (Map)
import           Data.Void (Void)
import           Network.TypedProtocol.Codec
import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.Ledger.SupportsMempool
import           Ouroboros.Consensus.Ledger.SupportsProtocol
import           Ouroboros.Consensus.MiniProtocol.BlockFetch.Server
import           Ouroboros.Consensus.MiniProtocol.ChainSync.Client
import           Ouroboros.Consensus.MiniProtocol.ChainSync.Server
import           Ouroboros.Consensus.Node.ExitPolicy
import           Ouroboros.Consensus.Node.NetworkProtocolVersion
import           Ouroboros.Consensus.Node.Run
import           Ouroboros.Consensus.Node.Serialisation
import qualified Ouroboros.Consensus.Node.Tracers as Node
import           Ouroboros.Consensus.NodeKernel
import qualified Ouroboros.Consensus.Storage.ChainDB.API as ChainDB
import           Ouroboros.Consensus.Storage.Serialisation (SerialisedHeader)
import           Ouroboros.Consensus.Util (ShowProxy)
import           Ouroboros.Consensus.Util.IOLike
import           Ouroboros.Consensus.Util.Orphans ()
import           Ouroboros.Consensus.Util.ResourceRegistry
import           Ouroboros.Network.AnchoredFragment (AnchoredFragment)
import           Ouroboros.Network.Block (Serialised (..), decodePoint,
                     decodeTip, encodePoint, encodeTip)
import           Ouroboros.Network.BlockFetch
import           Ouroboros.Network.BlockFetch.Client (BlockFetchClient,
                     blockFetchClient)
import           Ouroboros.Network.Channel
import           Ouroboros.Network.DeltaQ
import           Ouroboros.Network.Driver
import           Ouroboros.Network.Driver.Limits
import           Ouroboros.Network.KeepAlive
import           Ouroboros.Network.Mux
import           Ouroboros.Network.NodeToNode
import           Ouroboros.Network.NodeToNode.Version (isPipeliningEnabled)
import           Ouroboros.Network.PeerSelection.PeerMetric.Type
                     (FetchedMetricsTracer, HeaderMetricsTracer,
                     ReportPeerMetrics (..))
import qualified Ouroboros.Network.PeerSelection.PeerSharing as PSTypes
import           Ouroboros.Network.PeerSharing (PeerSharingController,
                     bracketPeerSharingClient, peerSharingClient,
                     peerSharingServer)
import           Ouroboros.Network.Protocol.BlockFetch.Codec
import           Ouroboros.Network.Protocol.BlockFetch.Server (BlockFetchServer,
                     blockFetchServerPeer)
import           Ouroboros.Network.Protocol.BlockFetch.Type (BlockFetch (..))
import           Ouroboros.Network.Protocol.ChainSync.ClientPipelined
import           Ouroboros.Network.Protocol.ChainSync.Codec
import           Ouroboros.Network.Protocol.ChainSync.PipelineDecision
import           Ouroboros.Network.Protocol.ChainSync.Server
import           Ouroboros.Network.Protocol.ChainSync.Type
import           Ouroboros.Network.Protocol.KeepAlive.Client
import           Ouroboros.Network.Protocol.KeepAlive.Codec
import           Ouroboros.Network.Protocol.KeepAlive.Server
import           Ouroboros.Network.Protocol.KeepAlive.Type
import           Ouroboros.Network.Protocol.PeerSharing.Client
                     (PeerSharingClient, peerSharingClientPeer)
import           Ouroboros.Network.Protocol.PeerSharing.Codec
                     (byteLimitsPeerSharing, codecPeerSharing,
                     codecPeerSharingId, timeLimitsPeerSharing)
import           Ouroboros.Network.Protocol.PeerSharing.Server
                     (PeerSharingServer, peerSharingServerPeer)
import           Ouroboros.Network.Protocol.PeerSharing.Type (PeerSharing,
                     PeerSharingAmount)
import           Ouroboros.Network.Protocol.TxSubmission2.Client
import           Ouroboros.Network.Protocol.TxSubmission2.Codec
import           Ouroboros.Network.Protocol.TxSubmission2.Server
import           Ouroboros.Network.Protocol.TxSubmission2.Type
import           Ouroboros.Network.TxSubmission.Inbound
import           Ouroboros.Network.TxSubmission.Mempool.Reader
                     (mapTxSubmissionMempoolReader)
import           Ouroboros.Network.TxSubmission.Outbound

{-------------------------------------------------------------------------------
  Handlers
-------------------------------------------------------------------------------}

-- | Protocol handlers for node-to-node (remote) communication
data Handlers m addr blk = Handlers {
      hChainSyncClient
        :: ConnectionId addr
        -> NodeToNodeVersion
        -> ControlMessageSTM m
        -> HeaderMetricsTracer m
        -> StrictTVar m (AnchoredFragment (Header blk))
        -> ChainSyncClientPipelined (Header blk) (Point blk) (Tip blk) m ChainSyncClientResult
        -- TODO: we should consider either bundling these context parameters
        -- into a record, or extending the protocol handler representation
        -- to support bracket-style initialisation so that we could have the
        -- closure include these and not need to be explicit about them here.

    , hChainSyncServer
        :: NodeToNodeVersion
        -> ChainDB.Follower m blk (ChainDB.WithPoint blk (SerialisedHeader blk))
        -> ChainSyncServer (SerialisedHeader blk) (Point blk) (Tip blk) m ()

    -- TODO block fetch client does not have GADT view of the handlers.
    , hBlockFetchClient
        :: NodeToNodeVersion
        -> ControlMessageSTM m
        -> FetchedMetricsTracer m
        -> BlockFetchClient (Header blk) blk m ()

    , hBlockFetchServer
        :: NodeToNodeVersion
        -> ResourceRegistry m
        -> BlockFetchServer (Serialised blk) (Point blk) m ()

    , hTxSubmissionClient
        :: NodeToNodeVersion
        -> ControlMessageSTM m
        -> ConnectionId addr
        -> TxSubmissionClient (GenTxId blk) (GenTx blk) m ()

    , hTxSubmissionServer
        :: NodeToNodeVersion
        -> ConnectionId addr
        -> TxSubmissionServerPipelined (GenTxId blk) (GenTx blk) m ()

    , hKeepAliveClient
        :: NodeToNodeVersion
        -> ControlMessageSTM m
        -> ConnectionId addr
        -> StrictTVar m (Map (ConnectionId addr) PeerGSV)
        -> KeepAliveInterval
        -> KeepAliveClient m ()

    , hKeepAliveServer
        :: NodeToNodeVersion
        -> ConnectionId addr
        -> KeepAliveServer m ()

    , hPeerSharingClient
        :: NodeToNodeVersion
        -> ControlMessageSTM m
        -> addr
        -> PeerSharingController addr m
        -> m (PeerSharingClient addr m ())

    , hPeerSharingServer
        :: NodeToNodeVersion
        -> addr
        -> PeerSharingServer addr m
    }

mkHandlers
  :: forall m blk addrNTN addrNTC.
     ( IOLike m
     , MonadTime m
     , MonadTimer m
     , LedgerSupportsMempool blk
     , HasTxId (GenTx blk)
     , LedgerSupportsProtocol blk
     , Ord addrNTN
     )
  => NodeKernelArgs m addrNTN addrNTC blk
  -> NodeKernel     m addrNTN addrNTC blk
  -> (PeerSharingAmount -> m [addrNTN])
  -- ^ Peer Sharing result computation callback
  -> Handlers       m addrNTN           blk
mkHandlers
      NodeKernelArgs {keepAliveRng, miniProtocolParameters}
      NodeKernel {getChainDB, getMempool, getTopLevelConfig, getTracers = tracers}
      computePeers =
    Handlers {
        hChainSyncClient = \peer ->
          chainSyncClient
            (pipelineDecisionLowHighMark
              (chainSyncPipeliningLowMark  miniProtocolParameters)
              (chainSyncPipeliningHighMark miniProtocolParameters))
            (contramap (TraceLabelPeer peer) (Node.chainSyncClientTracer tracers))
            getTopLevelConfig
            (defaultChainDbView getChainDB)
      , hChainSyncServer = \_version ->
          chainSyncHeadersServer
            (Node.chainSyncServerHeaderTracer tracers)
            getChainDB
      , hBlockFetchClient =
          blockFetchClient
      , hBlockFetchServer = \version ->
          blockFetchServer
            (Node.blockFetchServerTracer tracers)
            getChainDB
            version
      , hTxSubmissionClient = \version controlMessageSTM peer ->
          txSubmissionOutbound
            (contramap (TraceLabelPeer peer) (Node.txOutboundTracer tracers))
            (txSubmissionMaxUnacked miniProtocolParameters)
            (mapTxSubmissionMempoolReader txForgetValidated $ getMempoolReader getMempool)
            version
            controlMessageSTM
      , hTxSubmissionServer = \version peer ->
          txSubmissionInbound
            (contramap (TraceLabelPeer peer) (Node.txInboundTracer tracers))
            (txSubmissionMaxUnacked miniProtocolParameters)
            (mapTxSubmissionMempoolReader txForgetValidated $ getMempoolReader getMempool)
            (getMempoolWriter getMempool)
            version
      , hKeepAliveClient = \_version -> keepAliveClient (Node.keepAliveClientTracer tracers) keepAliveRng
      , hKeepAliveServer = \_version _peer -> keepAliveServer
      , hPeerSharingClient = \_version controlMessageSTM _peer -> peerSharingClient controlMessageSTM
      , hPeerSharingServer = \_version _peer -> peerSharingServer computePeers
      }

{-------------------------------------------------------------------------------
  Codecs
-------------------------------------------------------------------------------}

-- | Node-to-node protocol codecs needed to run 'Handlers'.
data Codecs blk addr e m bCS bSCS bBF bSBF bTX bKA bPS = Codecs {
      cChainSyncCodec            :: Codec (ChainSync (Header blk) (Point blk) (Tip blk))           e m bCS
    , cChainSyncCodecSerialised  :: Codec (ChainSync (SerialisedHeader blk) (Point blk) (Tip blk)) e m bSCS
    , cBlockFetchCodec           :: Codec (BlockFetch blk (Point blk))                             e m bBF
    , cBlockFetchCodecSerialised :: Codec (BlockFetch (Serialised blk) (Point blk))                e m bSBF
    , cTxSubmission2Codec        :: Codec (TxSubmission2 (GenTxId blk) (GenTx blk))                e m bTX
    , cKeepAliveCodec            :: Codec KeepAlive                                                e m bKA
    , cPeerSharingCodec          :: Codec (PeerSharing addr)                                       e m bPS
    }

-- | Protocol codecs for the node-to-node protocols
defaultCodecs :: forall m blk addr.
                ( IOLike m
                , SerialiseNodeToNodeConstraints blk
                )
              => CodecConfig       blk
              -> BlockNodeToNodeVersion blk
              -> (addr -> CBOR.Encoding)
              -> (forall s . CBOR.Decoder s addr)
              -> NodeToNodeVersion
              -> Codecs blk addr DeserialiseFailure m
                   ByteString ByteString ByteString ByteString ByteString ByteString ByteString
defaultCodecs ccfg version encAddr decAddr _nodeToNodeVersion = Codecs {
      cChainSyncCodec =
        codecChainSync
          enc
          dec
          (encodePoint (encodeRawHash p))
          (decodePoint (decodeRawHash p))
          (encodeTip   (encodeRawHash p))
          (decodeTip   (decodeRawHash p))

    , cChainSyncCodecSerialised =
        codecChainSync
          enc
          dec
          (encodePoint (encodeRawHash p))
          (decodePoint (decodeRawHash p))
          (encodeTip   (encodeRawHash p))
          (decodeTip   (decodeRawHash p))

    , cBlockFetchCodec =
        codecBlockFetch
          enc
          dec
          (encodePoint (encodeRawHash p))
          (decodePoint (decodeRawHash p))

    , cBlockFetchCodecSerialised =
        codecBlockFetch
          enc
          dec
          (encodePoint (encodeRawHash p))
          (decodePoint (decodeRawHash p))

    , cTxSubmission2Codec =
        codecTxSubmission2
          enc
          dec
          enc
          dec

    , cKeepAliveCodec = codecKeepAlive_v2

    , cPeerSharingCodec = codecPeerSharing encAddr decAddr
    }
  where
    p :: Proxy blk
    p = Proxy

    enc :: SerialiseNodeToNode blk a => a -> Encoding
    enc = encodeNodeToNode ccfg version

    dec :: SerialiseNodeToNode blk a => forall s. Decoder s a
    dec = decodeNodeToNode ccfg version

-- | Identity codecs used in tests.
identityCodecs :: Monad m
               => Codecs blk addr CodecFailure m
                    (AnyMessage (ChainSync (Header blk) (Point blk) (Tip blk)))
                    (AnyMessage (ChainSync (SerialisedHeader blk) (Point blk) (Tip blk)))
                    (AnyMessage (BlockFetch blk (Point blk)))
                    (AnyMessage (BlockFetch (Serialised blk) (Point blk)))
                    (AnyMessage (TxSubmission2 (GenTxId blk) (GenTx blk)))
                    (AnyMessage KeepAlive)
                    (AnyMessage (PeerSharing addr))
identityCodecs = Codecs {
      cChainSyncCodec            = codecChainSyncId
    , cChainSyncCodecSerialised  = codecChainSyncId
    , cBlockFetchCodec           = codecBlockFetchId
    , cBlockFetchCodecSerialised = codecBlockFetchId
    , cTxSubmission2Codec        = codecTxSubmission2Id
    , cKeepAliveCodec            = codecKeepAliveId
    , cPeerSharingCodec          = codecPeerSharingId
    }

{-------------------------------------------------------------------------------
  Tracers
-------------------------------------------------------------------------------}

-- | A record of 'Tracer's for the different protocols.
type Tracers m peer blk e =
     Tracers'  peer blk e (Tracer m)

data Tracers' peer blk e f = Tracers {
      tChainSyncTracer            :: f (TraceLabelPeer peer (TraceSendRecv (ChainSync (Header blk) (Point blk) (Tip blk))))
    , tChainSyncSerialisedTracer  :: f (TraceLabelPeer peer (TraceSendRecv (ChainSync (SerialisedHeader blk) (Point blk) (Tip blk))))
    , tBlockFetchTracer           :: f (TraceLabelPeer peer (TraceSendRecv (BlockFetch blk (Point blk))))
    , tBlockFetchSerialisedTracer :: f (TraceLabelPeer peer (TraceSendRecv (BlockFetch (Serialised blk) (Point blk))))
    , tTxSubmission2Tracer        :: f (TraceLabelPeer peer (TraceSendRecv (TxSubmission2 (GenTxId blk) (GenTx blk))))
    }

instance (forall a. Semigroup (f a)) => Semigroup (Tracers' peer blk e f) where
  l <> r = Tracers {
        tChainSyncTracer            = f tChainSyncTracer
      , tChainSyncSerialisedTracer  = f tChainSyncSerialisedTracer
      , tBlockFetchTracer           = f tBlockFetchTracer
      , tBlockFetchSerialisedTracer = f tBlockFetchSerialisedTracer
      , tTxSubmission2Tracer        = f tTxSubmission2Tracer
      }
    where
      f :: forall a. Semigroup a
        => (Tracers' peer blk e f -> a)
        -> a
      f prj = prj l <> prj r

-- | Use a 'nullTracer' for each protocol.
nullTracers :: Monad m => Tracers m peer blk e
nullTracers = Tracers {
      tChainSyncTracer            = nullTracer
    , tChainSyncSerialisedTracer  = nullTracer
    , tBlockFetchTracer           = nullTracer
    , tBlockFetchSerialisedTracer = nullTracer
    , tTxSubmission2Tracer        = nullTracer
    }

showTracers :: ( Show blk
               , Show peer
               , Show (Header blk)
               , Show (GenTx blk)
               , Show (GenTxId blk)
               , HasHeader blk
               , HasNestedContent Header blk
               )
            => Tracer m String -> Tracers m peer blk e
showTracers tr = Tracers {
      tChainSyncTracer            = showTracing tr
    , tChainSyncSerialisedTracer  = showTracing tr
    , tBlockFetchTracer           = showTracing tr
    , tBlockFetchSerialisedTracer = showTracing tr
    , tTxSubmission2Tracer        = showTracing tr
    }

{-------------------------------------------------------------------------------
  Applications
-------------------------------------------------------------------------------}

-- | A node-to-node application
type ClientApp m peer bytes a =
     NodeToNodeVersion
  -> ControlMessageSTM m
  -> peer
  -> Channel m bytes
  -> m (a, Maybe bytes)

type ServerApp m peer bytes a =
     NodeToNodeVersion
  -> peer
  -> Channel m bytes
  -> m (a, Maybe bytes)

-- | Applications for the node-to-node protocols
--
-- See 'Network.Mux.Types.MuxApplication'
data Apps m addr bCS bBF bTX bKA bPS a b = Apps {
      -- | Start a chain sync client that communicates with the given upstream
      -- node.
      aChainSyncClient     :: ClientApp m (ConnectionId addr) bCS a

      -- | Start a chain sync server.
    , aChainSyncServer     :: ServerApp m (ConnectionId addr) bCS b

      -- | Start a block fetch client that communicates with the given
      -- upstream node.
    , aBlockFetchClient    :: ClientApp m (ConnectionId addr) bBF a

      -- | Start a block fetch server.
    , aBlockFetchServer    :: ServerApp m (ConnectionId addr) bBF b

      -- | Start a transaction submission v2 client that communicates with the
      -- given upstream node.
    , aTxSubmission2Client :: ClientApp m (ConnectionId addr) bTX a

      -- | Start a transaction submission v2 server.
    , aTxSubmission2Server :: ServerApp m (ConnectionId addr) bTX b

      -- | Start a keep-alive client.
    , aKeepAliveClient     :: ClientApp m (ConnectionId addr) bKA a

      -- | Start a keep-alive server.
    , aKeepAliveServer     :: ServerApp m (ConnectionId addr) bKA b

      -- | Start a peer-sharing client.
    , aPeerSharingClient   :: ClientApp m addr bPS a

      -- | Start a peer-sharing server.
    , aPeerSharingServer   :: ServerApp m addr bPS b
    }


-- | Per mini-protocol byte limits;  For each mini-protocol they provide
-- per-state byte size limits, i.e. how much data can arrive from the network.
--
-- They don't depend on the instantiation of the protocol parameters (which
-- block type is used, etc.), hence the use of 'RankNTypes'.
--
data ByteLimits bCS bBF bTX bKA = ByteLimits {
      blChainSync     :: forall header point tip.
                         ProtocolSizeLimits
                           (ChainSync  header point tip)
                           bCS

    , blBlockFetch    :: forall block point.
                         ProtocolSizeLimits
                           (BlockFetch block point)
                           bBF

    , blTxSubmission2 :: forall txid tx.
                         ProtocolSizeLimits
                           (TxSubmission2 txid tx)
                           bTX

    , blKeepAlive     :: ProtocolSizeLimits
                           KeepAlive
                           bKA

    }

noByteLimits :: ByteLimits bCS bBF bTX bKA
noByteLimits = ByteLimits {
    blChainSync     = byteLimitsChainSync     (const 0)
  , blBlockFetch    = byteLimitsBlockFetch    (const 0)
  , blTxSubmission2 = byteLimitsTxSubmission2 (const 0)
  , blKeepAlive     = byteLimitsKeepAlive     (const 0)
  }

byteLimits :: ByteLimits ByteString ByteString ByteString ByteString
byteLimits = ByteLimits {
      blChainSync     = byteLimitsChainSync     size
    , blBlockFetch    = byteLimitsBlockFetch    size
    , blTxSubmission2 = byteLimitsTxSubmission2 size
    , blKeepAlive     = byteLimitsKeepAlive     size
    }
  where
    size :: ByteString -> Word
    size = (fromIntegral :: Int64 -> Word)
         . BSL.length

-- | Construct the 'NetworkApplication' for the node-to-node protocols
mkApps
  :: forall m addrNTN addrNTC blk e bCS bBF bTX bKA bPS.
     ( IOLike m
     , MonadTimer m
     , Ord addrNTN
     , Exception e
     , LedgerSupportsProtocol blk
     , ShowProxy blk
     , ShowProxy (Header blk)
     , ShowProxy (TxId (GenTx blk))
     , ShowProxy (GenTx blk)
     )
  => NodeKernel m addrNTN addrNTC blk -- ^ Needed for bracketing only
  -> Tracers m (ConnectionId addrNTN) blk e
  -> (NodeToNodeVersion -> Codecs blk addrNTN e m bCS bCS bBF bBF bTX bKA bPS)
  -> ByteLimits bCS bBF bTX bKA
  -> m ChainSyncTimeout
  -> ReportPeerMetrics m (ConnectionId addrNTN)
  -> Handlers m addrNTN blk
  -> Apps m addrNTN bCS bBF bTX bKA bPS NodeToNodeInitiatorResult ()
mkApps kernel Tracers {..} mkCodecs ByteLimits {..} genChainSyncTimeout ReportPeerMetrics {..} Handlers {..} =
    Apps {..}
  where
    aChainSyncClient
      :: NodeToNodeVersion
      -> ControlMessageSTM m
      -> ConnectionId addrNTN
      -> Channel m bCS
      -> m (NodeToNodeInitiatorResult, Maybe bCS)
    aChainSyncClient version controlMessageSTM them channel = do
      labelThisThread "ChainSyncClient"
      -- Note that it is crucial that we sync with the fetch client "outside"
      -- of registering the state for the sync client. This is needed to
      -- maintain a state invariant required by the block fetch logic: that for
      -- each candidate chain there is a corresponding block fetch client that
      -- can be used to fetch blocks for that chain.
      bracketSyncWithFetchClient
        (getFetchClientRegistry kernel) them $
        bracketChainSyncClient
            (contramap (TraceLabelPeer them) (Node.chainSyncClientTracer (getTracers kernel)))
            (defaultChainDbView (getChainDB kernel))
            (getNodeCandidates kernel)
            them
            version $ \varCandidate -> do
              chainSyncTimeout <- genChainSyncTimeout
              (r, trailing) <-
                runPipelinedPeerWithLimits
                  (contramap (TraceLabelPeer them) tChainSyncTracer)
                  (cChainSyncCodec (mkCodecs version))
                  blChainSync
                  (timeLimitsChainSync chainSyncTimeout)
                  channel
                  $ chainSyncClientPeerPipelined
                  $ hChainSyncClient them version controlMessageSTM
                      (TraceLabelPeer them `contramap` reportHeader)
                      varCandidate
              return (ChainSyncInitiatorResult r, trailing)

    aChainSyncServer
      :: NodeToNodeVersion
      -> ConnectionId addrNTN
      -> Channel m bCS
      -> m ((), Maybe bCS)
    aChainSyncServer version them channel = do
      labelThisThread "ChainSyncServer"
      chainSyncTimeout <- genChainSyncTimeout
      bracketWithPrivateRegistry
        (chainSyncHeaderServerFollower
           (getChainDB kernel)
           ( case isPipeliningEnabled version of
              ReceivingTentativeBlocks    -> ChainDB.TentativeChain
              NotReceivingTentativeBlocks -> ChainDB.SelectedChain
           )
        )
        ChainDB.followerClose
        $ \flr ->
          runPeerWithLimits
            (contramap (TraceLabelPeer them) tChainSyncSerialisedTracer)
            (cChainSyncCodecSerialised (mkCodecs version))
            blChainSync
            (timeLimitsChainSync chainSyncTimeout)
            channel
            $ chainSyncServerPeer
            $ hChainSyncServer version flr

    aBlockFetchClient
      :: NodeToNodeVersion
      -> ControlMessageSTM m
      -> ConnectionId addrNTN
      -> Channel m bBF
      -> m (NodeToNodeInitiatorResult, Maybe bBF)
    aBlockFetchClient version controlMessageSTM them channel = do
      labelThisThread "BlockFetchClient"
      bracketFetchClient (getFetchClientRegistry kernel) version
                         isPipeliningEnabled them $ \clientCtx -> do
        ((), trailing) <- runPipelinedPeerWithLimits
          (contramap (TraceLabelPeer them) tBlockFetchTracer)
          (cBlockFetchCodec (mkCodecs version))
          blBlockFetch
          timeLimitsBlockFetch
          channel
          $ hBlockFetchClient version controlMessageSTM
                              (TraceLabelPeer them `contramap` reportFetch) clientCtx
        return (NoInitiatorResult, trailing)

    aBlockFetchServer
      :: NodeToNodeVersion
      -> ConnectionId addrNTN
      -> Channel m bBF
      -> m ((), Maybe bBF)
    aBlockFetchServer version them channel = do
      labelThisThread "BlockFetchServer"
      withRegistry $ \registry ->
        runPeerWithLimits
          (contramap (TraceLabelPeer them) tBlockFetchSerialisedTracer)
          (cBlockFetchCodecSerialised (mkCodecs version))
          blBlockFetch
          timeLimitsBlockFetch
          channel
          $ blockFetchServerPeer
          $ hBlockFetchServer version registry

    aTxSubmission2Client
      :: NodeToNodeVersion
      -> ControlMessageSTM m
      -> ConnectionId addrNTN
      -> Channel m bTX
      -> m (NodeToNodeInitiatorResult, Maybe bTX)
    aTxSubmission2Client version controlMessageSTM them channel = do
      labelThisThread "TxSubmissionClient"
      ((), trailing) <- runPeerWithLimits
        (contramap (TraceLabelPeer them) tTxSubmission2Tracer)
        (cTxSubmission2Codec (mkCodecs version))
        blTxSubmission2
        timeLimitsTxSubmission2
        channel
        (txSubmissionClientPeer (hTxSubmissionClient version controlMessageSTM them))
      return (NoInitiatorResult, trailing)

    aTxSubmission2Server
      :: NodeToNodeVersion
      -> ConnectionId addrNTN
      -> Channel m bTX
      -> m ((), Maybe bTX)
    aTxSubmission2Server version them channel = do
      labelThisThread "TxSubmissionServer"
      runPipelinedPeerWithLimits
        (contramap (TraceLabelPeer them) tTxSubmission2Tracer)
        (cTxSubmission2Codec (mkCodecs version))
        blTxSubmission2
        timeLimitsTxSubmission2
        channel
        (txSubmissionServerPeerPipelined (hTxSubmissionServer version them))

    aKeepAliveClient
      :: NodeToNodeVersion
      -> ControlMessageSTM m
      -> ConnectionId addrNTN
      -> Channel m bKA
      -> m (NodeToNodeInitiatorResult, Maybe bKA)
    aKeepAliveClient version controlMessageSTM them channel = do
      labelThisThread "KeepAliveClient"
      let kacApp = \dqCtx ->
                       runPeerWithLimits
                         nullTracer
                         (cKeepAliveCodec (mkCodecs version))
                         blKeepAlive
                         timeLimitsKeepAlive
                         channel
                         $ keepAliveClientPeer
                         $ hKeepAliveClient version controlMessageSTM them dqCtx
                             (KeepAliveInterval 10)

      ((), trailing) <- bracketKeepAliveClient (getFetchClientRegistry kernel) them kacApp
      return (NoInitiatorResult, trailing)

    aKeepAliveServer
      :: NodeToNodeVersion
      -> ConnectionId addrNTN
      -> Channel m bKA
      -> m ((), Maybe bKA)
    aKeepAliveServer version _them channel = do
      labelThisThread "KeepAliveServer"
      runPeerWithLimits
        nullTracer
        (cKeepAliveCodec (mkCodecs version))
        (byteLimitsKeepAlive (const 0)) -- TODO: Real Bytelimits, see #1727
        timeLimitsKeepAlive
        channel
        $ keepAliveServerPeer
        $ keepAliveServer


    aPeerSharingClient
      :: NodeToNodeVersion
      -> ControlMessageSTM m
      -> addrNTN
      -> Channel m bPS
      -> m (NodeToNodeInitiatorResult, Maybe bPS)
    aPeerSharingClient version controlMessageSTM them channel = do
      labelThisThread "PeerSharingClient"
      bracketPeerSharingClient (getPeerSharingRegistry kernel) them
        $ \controller -> do
          psClient <- hPeerSharingClient version controlMessageSTM them controller
          ((), trailing) <- runPeerWithLimits
            nullTracer
            (cPeerSharingCodec (mkCodecs version))
            (byteLimitsPeerSharing (const 0))
            timeLimitsPeerSharing
            channel
            (peerSharingClientPeer psClient)
          return (NoInitiatorResult, trailing)

    aPeerSharingServer
      :: NodeToNodeVersion
      -> addrNTN
      -> Channel m bPS
      -> m ((), Maybe bPS)
    aPeerSharingServer version them channel = do
      labelThisThread "PeerSharingServer"
      runPeerWithLimits
        nullTracer
        (cPeerSharingCodec (mkCodecs version))
        (byteLimitsPeerSharing (const 0))
        timeLimitsPeerSharing
        channel
        $ peerSharingServerPeer
        $ hPeerSharingServer version them

{-------------------------------------------------------------------------------
  Projections from 'Apps'
-------------------------------------------------------------------------------}

-- | A projection from 'NetworkApplication' to a client-side
-- 'OuroborosApplication' for the node-to-node protocols.
--
-- Implementation note: network currently doesn't enable protocols conditional
-- on the protocol version, but it eventually may; this is why @_version@ is
-- currently unused.
initiator
  :: MiniProtocolParameters
  -> NodeToNodeVersion
  -> PSTypes.PeerSharing
  -> Apps m addr b b b b b a c
  -> OuroborosBundle 'InitiatorMode addr b m a Void
initiator miniProtocolParameters version ownPeerSharing Apps {..} =
    nodeToNodeProtocols
      miniProtocolParameters
      -- TODO: currently consensus is using 'ConnectionId' for its 'peer' type.
      -- This is currently ok, as we might accept multiple connections from the
      -- same ip address, however this will change when we will switch to
      -- p2p-governor & connection-manager.  Then consenus can use peer's ip
      -- address & port number, rather than 'ConnectionId' (which is
      -- a quadruple uniquely determinaing a connection).
      (\them controlMessageSTM -> NodeToNodeProtocols {
          chainSyncProtocol =
            (InitiatorProtocolOnly (MuxPeerRaw (aChainSyncClient version controlMessageSTM them))),
          blockFetchProtocol =
            (InitiatorProtocolOnly (MuxPeerRaw (aBlockFetchClient version controlMessageSTM them))),
          txSubmissionProtocol =
            (InitiatorProtocolOnly (MuxPeerRaw (aTxSubmission2Client version controlMessageSTM them))),
          keepAliveProtocol =
            (InitiatorProtocolOnly (MuxPeerRaw (aKeepAliveClient version controlMessageSTM them))),
          peerSharingProtocol =
            (InitiatorProtocolOnly (MuxPeerRaw (aPeerSharingClient version controlMessageSTM (remoteAddress them))))
        })
      version
      ownPeerSharing

-- | A bi-directional network applicaiton.
--
-- Implementation note: network currently doesn't enable protocols conditional
-- on the protocol version, but it eventually may; this is why @_version@ is
-- currently unused.
initiatorAndResponder
  :: MiniProtocolParameters
  -> NodeToNodeVersion
  -> PSTypes.PeerSharing
  -> Apps m addr b b b b b a c
  -> OuroborosBundle 'InitiatorResponderMode addr b m a c
initiatorAndResponder miniProtocolParameters version ownPeerSharing Apps {..} =
    nodeToNodeProtocols
      miniProtocolParameters
      (\them controlMessageSTM -> NodeToNodeProtocols {
          chainSyncProtocol =
            (InitiatorAndResponderProtocol
              (MuxPeerRaw (aChainSyncClient version controlMessageSTM them))
              (MuxPeerRaw (aChainSyncServer version                   them))),
          blockFetchProtocol =
            (InitiatorAndResponderProtocol
              (MuxPeerRaw (aBlockFetchClient version controlMessageSTM them))
              (MuxPeerRaw (aBlockFetchServer version                   them))),
          txSubmissionProtocol =
            (InitiatorAndResponderProtocol
              (MuxPeerRaw (aTxSubmission2Client version controlMessageSTM them))
              (MuxPeerRaw (aTxSubmission2Server version                   them))),
          keepAliveProtocol =
            (InitiatorAndResponderProtocol
              (MuxPeerRaw (aKeepAliveClient version controlMessageSTM them))
              (MuxPeerRaw (aKeepAliveServer version                   them))),

          peerSharingProtocol =
            (InitiatorAndResponderProtocol
              (MuxPeerRaw (aPeerSharingClient version controlMessageSTM (remoteAddress them)))
              (MuxPeerRaw (aPeerSharingServer version                   (remoteAddress them))))
        })
      version
      ownPeerSharing
