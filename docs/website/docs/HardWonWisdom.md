This document contains a loosely organized list of small summaries of realizations we had while working on the code base.

We do eventually want to integrate these lessons learned into more coherent and targetted documents.
But step one one is to record them at all; this file is supposed to make that easy.
Step two will be to occasionally extract cohesive insights from this bag, creating new documents or refining old ones accordingly.

## Why doesn't Ledger code ever return `PastHorizonException`?

One of the `HardForkBlock` combinator's major responsibilities is providing an `EpochInfo` to the ledger code.
This `EpochInfo` uses the `Either` monad to return `Right` only when the query can be answered with certainty.
For more information on when that is, see the Consensus Report and the recordings of Edsko's presentations at the Weekly IOG Seminar.

However, most of the the ledger code that interacts with the given `EpochInfo` assumes it cannot fail by using `epochInfoPure`.

```haskell
data Globals = Globals { epochInfo :: !(EpochInfo (Either Text)), ... }  

epochInfoPure :: Globals -> EpochInfo Identity
epochInfoPure = hoistEpochInfo (either (throw . EpochErr) pure) . epochInfo
```

Thus, it is the responsibility of the calling code (eg the Consensus code) to check that the `HardForkBlock`-derived `EpochInfo` will not fail when its invoking the ledger rules.
One example we've been looking at recently is the invocation of the `TICKF` rule, which is the `ledgerViewForecastAt` definition below.

```haskell
data Forecast a = Forecast {
      forecastAt  :: WithOrigin SlotNo

      -- Precondition: @At s >= forecastAt@
    , forecastFor :: SlotNo -> Except OutsideForecastRange (Ticked a)
    }

class ... => LedgerSupportsProtocol blk where
  ...
  ledgerViewForecastAt ::
       HasCallStack
    => LedgerConfig blk
    -> LedgerState blk
    -> Forecast (LedgerView (BlockProtocol blk))


instance ... => LedgerSupportsProtocol (ShelleyBlock (TPraos crypto) era) where
  ...
  ledgerViewForecastAt cfg ledgerState = Forecast at $ \for ->
    if
        | NotOrigin for == at ->
              return
            $ TPraos.TickedPraosLedgerView
            $ SL.currentLedgerView shelleyLedgerState
        | for < maxFor        -> return $ futureLedgerView for
        | otherwise           -> throwError OutsideForecastRange { ... }
    where
      ShelleyLedgerState {shelleyLedgerState} = ledgerState

      globals = shelleyLedgerGlobals cfg
      swindow = SL.stabilityWindow globals
      at      = ledgerTipSlot ledgerState

      futureLedgerView :: SlotNo -> Ticked (SL.LedgerView (EraCrypto era))
      futureLedgerView =
        either
          (\e -> error ("futureLedgerView failed: " <> show e))
          TPraos.TickedPraosLedgerView
          . SL.futureLedgerView globals shelleyLedgerState

      maxFor :: SlotNo   -- Exclusive upper bound
      maxFor = addSlots swindow $ succWithOrigin at
```

When we returned to this code for the first time in a while, we thought it was odd that the code both handles an `Either` in the return type of `SL.futureLedgerView` and also does its own `for < maxFor` check; can't the Ledger code instead return `Left` whenever `for >= maxFor`?

We looked at the upstream code to investigate; how easily could we arrange that?
The answer is: it could be done, but the core architecture of the State Transition System code in the core Ledger library does not currently naturally allow for that (at least in our subjective opinion of _naturally_ and specifically for the `TICKF` example).
At the moment, any rule that can _fail_ must also provide a "default" value for the rest of the rule to use (see the `Predicate` constructor of the `Clause` GADT, specifically its argument of type `a`).
For the Ledger's code implementing the `TICKF` rule to observe the `Either` layer of the `EpochInfo` would require that the rule has some way to continue when the `EpochInfo` query (used to determine if the requested forecast crosses an epoch transition) fails.

It is not obvious how to do that when `EpochInfo` returns `Left`.
While it may be possible to work something out, such as perhaps the `TICKF` rule emits a new `PredicateFailure` and simply leaves the `NewEpochState` unchanged, no idea seems natural to us.
They all involve creating an incorrect `LedgerView` and then only throwing it away at the last moment.
And notably, the rest of the rule could emit additional errors, all of which would be presumably spurious given that we already know the very first check (ie querying the `EpochInfo`) failed.

So instead, for now at least, the Consensus code must do its own checking before invoking Ledger code that relies on the `EpochInfo` never failing.

- By design, any invocation of Ledger code that causes the `EpochInfo` to return `Left` would be a _bug_, with no obvious way to recover.
  Thus this isn't a particularly burdensome requirement; not much extra code (such as `for < maxFor` above).
  And also thus: throwing these exceptions from pure code is reasonable choice.

- We asked the Ledger team, and they didn't immediately reject the possibility of enriching the base monad's feature set to include short-circuiting failure (eg adding an `ExceptT` in the Ledger rules) for use in computations such as the given `EpochInfo Either` where it would make sense to immediately abort the rule computation.

A couple more observations:

- The ways the `TICKF` rule can currently fail are all sanity checks.
  In particular, if they fail, then there's no way this chain could ever successfully cross the epoch boundary, not via `TICKF` nor via the full `TICK`.
  This justifies the use of `error` in the `where`-clause `futureLedgerView` above---there is no useful way to recover from this error; the node is doomed to never tick past the epoch boundary until an operator manually truncates its chain so it can switch to a better one (if one exists :fingers-crossed:) that isn't doomed.

- At least one part of the ledger _does_ use the `EpochInfo Either` as a test: the validation of the `ValidityInterval` of a transaction that contains a Plutus script.
  The code here accommodates the inflexibility of the `Predicate` rule by using an additional `whenFailureFree` combinator to skip over invalid tx, thus avoiding the computation that would require the result of the `EpochInfo` that instead returns `Left`.
  ... I wonder if every use of the `epochInfo` could do that same thing.

So, either by mimicking the approach of the existing `ValidityInterval` validation logic or by altering the STS innards to allow short-circuiting failure, we could reify the `EpochInfo` failures into the `PredicateFailure` hierarchy, and thereby leverage the types to force each invocation of the Ledger API to independently handle the possibility of `PastHorizonException`s.
But it's not obvious that that is definitely worth the extra complexity it would introduce on the Ledger code.

## Why use the Honest Chain Growth window as the Ledger's Stability Window?

Suppose we have selected a different chain than our peer and that our selected chain has L blocks after the intersection and their selected chain has R blocks after the intersection.

REQ1: If k<L, we must promptly disconnect from the peer (b/c of Common Prefix violation and Limit on Rollback).

REQ2: If L≤k (see REQ1) and L<R, we must validate at least L+1 of their headers, because Praos requires us to fetch and select the longer chain, and validating those headers is the first step towards selecting those blocks.
(This requirement ignores tiebreakers here because the security argument must hold even if the adversary wins a tiebreaker.)

The most demanding case of REQ2 is L=k: at most we'll need to validate k+1 of the peer's headers.
Thus using HCG window as Stability Window ensures that forecasting can't disrupt REQ2 when the peer is serving honest blocks.
(We can tick the intersection ledger state to their first header, and then forecast 3k/f from there which by HCG will get us at least the remaining k headers if they're serving an honest chain.)

## Which slots/times/epochs can we translate?

TODO Confirm and emphasize that this exact same logic is used by the node itself to determine which slot the current wall clock is in.

TODO How does this explanation/motivation compare to which headers we can validate via forecasting?

In early May 2023, we spent the Consensus Office Hours discussing a node test of the `slot-number` CLI command, which translates a slot to a UTC time.
In particular, the tester's question was essentialy "When is the slot-number command expected to fail?".
The answer is ultimately not too complicated, and generalizes to other translations between slots, epochs, and times.
But this is the nth time we've answered it (sometimes we asked ourselves), and each time required a substantial effort to re-learn it so that we could answer confidently.
This topic definitely deserves better docs/dedicated tests/etc---but we're (as always) strapped for time, so I'm writing this as a band-aid (that's the point of this whole file).
I will summarize abstrtactly and then point to key parts of the implementation.

The Hard Fork Combinator lets us specify eras separately and compose them into a single type of chain (ie a "block type") that can fork through some prefix of those eras.
Any piece of code supports some sequence of eras.
For example, the original Cardano code only supported Byron.
At some point we added Shelley to the code.
And at some later point we added Allegra.
And so on.
It's notable that the Cardano chain hard forked into the latest era before the addition of each subsequent era.
To be pedantically concrete: the code supported only Byron and the chain was in Byron, then the code also supported Shelley, then the chain forked into Shelley (hurray!), then the code also supported Allegra, then the code forked into Allegra, and so on.
In general, it's possible the code could know about an arbitrary number of future eras before forking into them.
Or it could know about a future era and we could change our minds about it, deleting that era without ever forking into it.
But, so far, on Cardano the code has always been either zero or one eras ahead of the whole network's chain (ie "the Cardano chain").
Even so, a new node syncing today will at some point have only synced enough of the chain to be in, say, Mary, even though the code knows about multiple eras after Mary.
So, despite Cardano doing the simplest possible thing with respect to the whole network's chain, new (or even just very stale) nodes will exercise the more general possibilities (ie the code knowing about multiple eras beyond the tip of the node's current selection).

Thus, at any given time the code supports some non-empty sequence of eras.
And, at that same time, all valid Cardano chains and their prefixes (aka all valid Cardano blocks) will inhabit some prefix of that sequence---in the absence of catastrophic release and/or operator failure.

A Hard Fork Combinator ledger state provides enough information to determine which era it is in.
It must also determine (ie record) when that era and every preceding era started.
Trivially, this also determines when all the _preceding_ eras ended (ie when the successor started).
The ledger state _might_ also determine when the ledger state's own era will end.
Thus, every ledger state determines the start time of N eras and the end time of the preceding N-1 eras (note: there's one more start time than end times), where the ledger state inhabits either the N-1th or the Nth era.
Subsequent ledger states may have greater Ns, but the invariant remains true.
Every N will be at least 1, at most the length of the sequence of eras the code supports, and subsequent ledger states on a chain cannot have a lesser N.

Warning.
(Skip this on your first read of this section.)
That invariant was coyly worded to exclude one perhaps-surprising exception: the code allows for an era to be specified to never end.
The above invariants remain true, but can be tightened in this case.
Specifically, when the ledger state reaches the era that is specified to never end, it is thereafter always definitely in the Nth era, and there will never be a greater N.
(The code may support eras after an unending one, but that would be an awkard/wasteful choice.)
No Cardano era is specified to never end, and we currently do not foresee every doing so.
The behavior is only supported for tests and for reuse by other blockchain implementors that are not concerned with extensibility.

For interpreting slot/time/epoch translation queries, the key motivating fact is that each era can have a different size of epoch (in slots) and/or a different length of slot (a time duration).
Thus, we cannot handle a translation query unless we know which era its argument is in and the durations of all preceding eras, or, equivalently, the start times of all eras up-to-and-including the argument is in.

Each query is handled by some piece of code and with respect to some ledger state.
The code (including config files) determines the supported eras (including their epoch size and slot length), and the ledger state determines which prefix of eras has known start times.
The known start times are enough to recognize when the given argument is during some era with a known end time, in which case the translation succeeds.
Otherwise, we need more information to know whether the given argument is during the last era with a known start time, ie the first era with an unknown end time.
Even if the query argument is after that start time, it _might_ instead be in a future era with a different epoch size/slot length, and so the correct translation may differ from the hypothetical response derived from the assumption the query argument precedes the first unknown end time.

For the first era with an unknown end time (ie the last era with a known start time), the code relies an a lower bound for that end time, ie the soonest that era could possibly end (aka "the horizon" or "the forecast horizon").
If the query argument precedes that horizon, then the translation succeeds, otherwise it fails.
For this purpose, the code (including config files) cannot support an era unless it also knows a "safe zone" for that era, where the safe zone (along with any additional assumptions the Consensus code makes) is enough information to determine the horizon induced by a given the ledger state.

In general, it would be possible to design a system such that even the final ledger state in an era did not determine when that era would end.
That'd be an empty safe zone, consisting of zero slots.
For example, perhaps the first block of an era identifies itself as such simply by setting some field in its header.
For that kind of chain, some ledger states would not provide enough information to do any translations whatsoever of slots/times/epochs _after_ that ledger state's tip.

For the case of Cardano, however, other concerns (not directly related to slot/epoch/time translations) already require a seperate cutoff, similar to the horizon, to be above some minimum.
For the sake of simplicity, we take that same minimum to be the safe zone.
As a result, the safe zone is equal to one _stability window_, which is `2k` slots for Byron and `3k/f` slots for every Shelley era.

Warning.
(Skip this on your first several reads of this section.)

- Headers declare what era they are in.

- The stake distribution of the next epoch is determined at least one stability window before it starts, regardless of whether that next epoch is in the next era.

In conjunction, a header that satisifes its declared era's rules can be validated as such by some ledger state even if there is an era transition between the two.
On the other hand, there is no guarantee that the ledger state the header actually extends is indeed in the era the header claims to be in; so it could satisfy the rules of its claimed era but still actually be an invalid header (when that claim is a lie).
Moreover, era transitions are not the only updates that can affect the validity of headers.
One excellent example is the the Transitional Praos (aka "TPraos") decentralization parameter `d` (any protocol parameter change requires a version change, but it could be minor---only major version changes can possibly cause proper era transitions).
Another example is that no part of the design beyond (probably wise) convention is preventing a so-called "intra-era" fork from influencing the header validity.

So, an adversary could lie about what era their header is in order to send an apparently valid header that is actually revealed as invalid once the intervening blocks are available.
Obviously that's undesirable, but is it truly problematic?
We generally consider that the Header-Body Split requires a ledger state can correctly determine the validity of any header within one stability window of the (last applied block of the) ledger state.
But that's just an ideal case; we could relax that, if we had a reason to embrace the additional complexity it involves.
The actual fundamental requirement derived from Praos is two-fold.

- No false alarams for honest headers: an honest (which is by definition actually valid) header must never appear as invalid.

- Never too many missed positives: no adversary can mint a chain of apparently-valid headers that has `k` or more headers after its intersection with any honest chain within the stability window. (TODO Is this constraint overly-precise?)

Roughly: the rule is to not (at all) underestimate the honest chain growth and to not (significantly) over-estimate the adversarial chain growth.

Consider some examples.

- Even in this laxer rule, the real `d` parameter cannot change within the stability window, because if it does change, then honest headers that are in an overlay slot according to the reduced `d` might not be in an overlay slot according to the unreduced `d`, and that would lead to false negatives for honest (overlay) headers.

- It would be possible to have defined the overlay schedule such the overlaidness of a slot was monotonic in `d`, even though we didn't do it that way.
  Even if we had, then there still would have been false alarms for honest headers, because some honest headers in slots that were actually not overlaid would be rejected since the incorrectly greater `d` would interpret those slots as overlaid.
  So the `d` parameter is something that even the laxer rule could not accomodate (even when assuming it can't increase, because the its overall influence on honest headers is not monotonic).

- As of epoch 257, `d=0` (ie no slots are overlaid).
  Since then, no change to the Cardano protocol parameters (including era transitions) has changed the (average) number of slots any given issuer leads during any given interval of slots.
  Also since then, every change that has at all affected the validity of headers has been an era transition.
  Therefore, _none of those subsequent changes truly required a stability window of warning_.
  Honest headers after such change would correctly identify themselves as such by claiming the new era, and therefore would be correctly validated.
  An adversarial header, in this hypothetical, could have falsely claimed to be from the new era, but the crucial insight is that doing so wouldn't have (TODO "significantly" or "at all"?) increased the chance the adversary could create an apparently-valid chain that is long enough to cause problems.

Recall that that discussion was merely theoretical, to better delineate the fundamental requirements.
The real Cardano ledger always has and still does ensure that header validity is fully determined at least one stability window in advance.
We have had no motivating reason to eliminate that simplification, as of yet; so far we don't anticipate one arising soon.
(
Currently, the protocol parameter changes are currently even known two stabilty windows early!
But some factors are still just singly stable, eg the stake distribution is only frozen one stability window before the next epoch.
)

TODO What about the config file overrides that result in empty epochs?
(
I'm actually unsure how that's working now... does it only work if a whole prefix of the static era sequence is skipped?
EG you can't skip only the 3rd era?
)

Warning.
(Skip this on your first read of this section.)
That reasoning implies some non-empty suffix of the ledger states in an era will each determine the exact end time of that era.
It's technically possible a ledger state could also determine the end time of subseqeuent eras, but the Cardano ledger rules do not permit that.
On `mainnet` Cardano, only blocks in an era can cause that era to end (technically false, but it's the right sentiment).
This also implies each era with a known end time on a `mainnet` chain must contain some blocks on that chain.
On the other hand, the Consensus Layer configuration inputs do permit overriding the era transition rules for the sake of testing, in which case a ledger state could anticipate the end time of several subsequent eras and eras could be empty (eg main use case is skipping from Byron to some later Shelley era ASAP, in which case all the intervening eras have no blocks but also have no slots!).

Warning.
(Skip this on your first several reads of this section.)
There is one last notable caveat at this abstract level.
The Byron and Shelley ledgers already had some logic for the evolution of proposals that can change the protocol (eg incur an era transition).
When designing and implementing the Hard Fork Combinator for use at the Byron-to-Shelley transition, Edsko de Vries reasoned through that the state machines of that logic needed to be adjusted to ensure "double stability".
The best resource we have for motivating this constraint is [Edsko de Vries' IOG seminar from 2020 June on the HFC and time](https://drive.google.com/file/d/1QIJ-VBlj-txB6K6E7DIEnY5TzaD89qQm/view).

- At the 16m04s mark he motivates that the forewarning must suffice for at least k+1 headers.

- At the 22m42s mark he starts explaining the Byron proposal state machine, and this ends up motivating "stably stable", aka "doubly stable", aka "double stability", aka "stable stability".
  (This recording was made before the Byron-to-Shelley fork happened.)

- From 30m46s to 38m52s, he explains the justification for cross-chain translations (and off-handedly that it's technically optional).

For example, [Shelley the `PPUP` ledger rule](https://github.com/input-output-hk/cardano-ledger/blob/180271602640bcac1214084b6de61d0468332f00/eras/shelley/impl/src/Cardano/Ledger/Shelley/Rules/Ppup.hs#L192) requires update proposals to be settled at least two stability windows before the end of the epoch (ie `6k/f`, not just `3k/f`).
(That links to the tip of the `master` branch at the time of writing this, although this constraint is not new.)

TODO Instead of double-stability in the ledger rules, we could instead only draw conclusions that should not be subject to roll back (such as time translations) from the youngest immutable ledger state.

The ultimate answer to the Office Hours question is that the query will fail if and only if its argument is beyond the conservative estimate for the end of the first era without a known end time.
That estimate will usually be the start of the least epoch that begins more than `6k/f` slots after the tip of ledger state that was used to answer the query.

The key corresponding parts of the implementation are as follows.

- The `ouroboros-consensus:Ouroboros.Consensus.HardFork.History.Qry` module defines `Interpreter`, `Qry`, and `interpretQuery`.
  Both `Interpeter` and `Qry` are opaque types, so in reality only whatever pre-defined queries that module exports, such as `slotToWallclock`, are available.

- These are ultimately used for every slot/epoch/time translation: `EpochInfo` passed to the ledger, the leadership check in a block-producing node, and all Consesus queries (see `ouroboros-consensus:Ouroboros.Consensus.HardFork.Combinator.Ledger.Query.GetInterpreter`).

- Every downstream use, such as the `slot-number` CLI command ultimately boils down to issuing the `GetInterpreter` query to the node itself and then invoking `interpretQuery`.

- Crucially, that interpretation can fail when the given interpreter cannot answer the given query, which is precisely the topic of the Office Hours question.

- Remark.
  A significantly fresher `Interpreter` will be able to answer more queries than a stale `Interpreter`.
  The `ouroboros-consensus:Ouroboros.Consensus.HardFork.History.Caching` module captures that idea.

- The `ouroboros-consensus:Ouroboros.Consensus.HardFork.History.EraParams.EraParams.EraParams` captures the data underlying the code's (including the configration files') support for an era.
  The (start/end) transition points are represented in triplicate: as a slot, as an epoch, and as a relative time (where `0` is `cardano-base:Cardano.Slotting.Time.SystemStart`, which is a UTC time).

- The interpretation only depends on the eras' start and end bounds, not on the safe zone.
  The safe zone is instead used in an preceding step to safely determine the least possible value of the first unknown end bound.
  This determination is implemented by the `ouroboros-consensus:Ouroboros.Consensus.HardFork.Combinator.State.reconstructSummaryLedger` function.
