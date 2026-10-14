import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginRecordingProtocol

/-! Couple each recording script to primitive/recursive report control flow.
Protocol legality alone cannot establish this correspondence. In particular a
cancel action must be the same positive fatal branch and exact skipped tail. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution

inductive RecordingDerivation
    : {α : Type} → Report α → Report α → List OriginAction → Prop where
  | pure (value : α) : RecordingDerivation (.pure value) (.pure value) []
  | fault (route : List Nat) (outcome : Result α)
    : RecordingDerivation (.fault route outcome) (.fault route outcome)
        (primitiveActions
          (primitiveOrigins route (ScheduledErrors.countedErrors outcome)))
  | combine (f : α → β → γ) {cut eager : Report α} {rest eagerRest : Report β}
    {actions later} (head : RecordingDerivation cut eager actions)
    (tail : RecordingDerivation rest eagerRest later)
    : RecordingDerivation (Report.combine f cut rest) (Report.combine f eager eagerRest)
        (actions ++ later)
  | map (f : α → β) {cut eager : Report α} {actions}
    (child : RecordingDerivation cut eager actions)
    : RecordingDerivation (cut.map f) (eager.map f) actions
  | catchNull (f : α → ResponseValue) {cut eager : Report α} {actions}
    (child : RecordingDerivation cut eager actions)
    : RecordingDerivation (cut.catchNull f) (eager.catchNull f) actions
  | nonNullKeep (route : List Nat) {cut eager : Report ResponseValue} {actions}
    (child : RecordingDerivation cut eager actions)
    (left : (cut.nonNull route).origins = cut.origins)
    (right : (eager.nonNull route).origins = eager.origins)
    : RecordingDerivation (cut.nonNull route) (eager.nonNull route)
        (actions ++ [.bubble cut.origins])
  | nonNullFresh (route : List Nat) {cut eager : Report ResponseValue} {actions}
    (child : RecordingDerivation cut eager actions) (left : cut.origins = [])
    (right : eager.origins = [])
    (newLeft : (cut.nonNull route).origins = primitiveOrigins route 1)
    (newRight : (eager.nonNull route).origins = primitiveOrigins route 1)
    : RecordingDerivation (cut.nonNull route) (eager.nonNull route)
        (actions ++ primitiveActions (primitiveOrigins route 1))
  | fatalCut (f : α → β → γ) (wrap : α → γ) {cut eagerHead : Report α} {actions}
    (eagerTail : Report β) (route : List Nat) (errors : Nat)
    (head : RecordingDerivation cut eagerHead actions)
    (fatal : cut.outcome = .error errors) (positive : 0 < errors)
    (headScope : Scoped (route ++ [0]) cut.origins)
    (tailScope : Scoped (route ++ [1]) eagerTail.origins)
    : RecordingDerivation (cut.map wrap) (Report.combine f eagerHead eagerTail)
        (actions ++ [.cancel ⟨route ++ [1], errors⟩ eagerTail.origins])
  | settle {cut eager : Report α} {actions}
    (child : RecordingDerivation cut eager actions)
    : RecordingDerivation cut eager (actions ++ [.settle cut.origins])

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
