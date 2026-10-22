import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.InitialStartupAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.NormalizedClosureLedger

/-! Initial synchronous activation establishes the source-derived publication replay frames. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Initial activation stores no successful value, even when tasks reject synchronously. -/
theorem State.initializeWithStartup_storedValues (work : Work) (startup : InitialStartup)
    (property : Occurrence → Execution.ExecutionGroupValue → Prop)
    : (State.initialize work startup).StoredValuesSatisfy property := by
  have empty : ({} : State).StoredValuesSatisfy property := by intro node member; cases member
  unfold State.initialize
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _
    startup.failures

/-- Initial startup has an empty exact publication inventory. -/
theorem State.initializeWithStartup_publicationInventory (work : Work)
    (startup : InitialStartup)
    : (State.initialize work startup).PublicationInventory (ObjectValueFrom []) [] :=
  ⟨by simp, by simp, State.initializeWithStartup_storedValues work startup _⟩

/-- The buffered-link invariant holds before any value has been stored. -/
theorem State.initializeWithStartup_storedTaskLinks (work : Work)
    (startup : InitialStartup)
    : (State.initialize work startup).StoredTaskLinks := by
  intro node member stored
  have empty := State.initializeWithStartup_storedValues work startup (fun _ _ => False)
  cases value : node.value with
  | none => simp [value] at stored
  | some payload => exact (empty node member payload value).elim

/-- Initial startup introduces no unsettled producer with attached child streams. -/
theorem State.initializeWithStartup_childStreamsSettled (work : Work)
    (startup : InitialStartup)
    : (State.initialize work startup).ChildStreamsSettled := by
  have empty : ({} : State).ChildStreamsSettled := by simp [State.ChildStreamsSettled]
  unfold State.initialize
  exact ((empty.integrateRoots work).pruneEmptyGroups _).startNewWork _ startup.failures

/-- Root activation preserves exact structural provenance for child-stream links. -/
theorem State.initializeWithStartup_childStreamsMatchWork (input : Work)
    (startup : InitialStartup) (work : Execution.Work)
    : (State.initialize input startup).ChildStreamsMatchWork work := by
  have empty : ({} : State).ChildStreamsMatchWork work := by simp [State.ChildStreamsMatchWork]
  unfold State.initialize
  exact ((empty.integrateRoots input).pruneEmptyGroups _).startNewWork _ startup.failures

/-- Removing failed roots retains declaration order in every surviving task-membership block. -/
theorem State.initializeWithStartup_groupMembershipOrder (work : Work)
    (startup : InitialStartup)
    : (State.initialize work startup).GroupMembershipOrder := by
  have empty : ({} : State).GroupMembershipOrder := by intro node member; cases member
  unfold State.initialize
  exact ((empty.maybeIntegrateWork work).pruneEmptyGroups _).startNewWork _
    startup.failures

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
