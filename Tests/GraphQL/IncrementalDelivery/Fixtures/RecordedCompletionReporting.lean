import Tests.GraphQL.IncrementalDelivery.Execution
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginAnnotations

/-! Collected originating diagnostics survive selection of a smaller boundary report. -/

namespace GraphQL.IncrementalDelivery.Tests.RecordedCompletionReporting

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

private def failed : RecordedCompletion Unit :=
  RecordedCompletion.combine (fun _ _ => ())
    (.fault [0] (.ok ((), 7)) : RecordedCompletion Unit)
    (.fault [1] (.error 3) : RecordedCompletion Unit)

#guard failed.report.origins.length == 10
#guard same failed.report.outcome (.error 10 : Result Unit)
#guard same failed.erase.deliveryResult (.error 3 : Result Unit)

private def caught : RecordedCompletion ResponseValue :=
  failed.catchNull (fun _ => .object [])

-- A caught failure explains delivered null data with every collected diagnostic.
#guard caught.report.origins == failed.report.origins
#guard same caught.erase.deliveryResult (.ok (.null, 10) : Result ResponseValue)

private def rethrown : RecordedCompletion ResponseValue := caught.nonNull [2]

-- Rethrowing selects the original cause without erasing or minting recorded origins.
#guard rethrown.report.origins == failed.report.origins
#guard same rethrown.report.outcome (.error 10 : Result ResponseValue)
#guard same rethrown.erase.deliveryResult (.error 3 : Result ResponseValue)

private def deferred : RecordedWork :=
  .executionGroup [] [] (failed.map (fun _ => [])).outcome .empty

#guard deferred.origins == failed.report.origins
#guard
  match deferred.erase with
  | .executionGroup _ _ outcome _ => same outcome.deliveryResult (.error 3)
  | _ => false

private def streamed : RecordedWork :=
  .stream { ref := 0, path := [] } [(rethrown.outcome, .empty)]

#guard streamed.origins == failed.report.origins
#guard
  match streamed.erase with
  | .stream _ [(outcome, _)] => same outcome.deliveryResult (.error 3)
  | _ => false

end GraphQL.IncrementalDelivery.Tests.RecordedCompletionReporting
