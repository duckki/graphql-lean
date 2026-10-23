import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ProtectedRootCompletion

/-! Failure-owner processing closes, rather than silently cancels, every removed active root. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Both active failure removal and latent error retention preserve announced-root accounting
-----------------------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Actual matching replay derives this frame without assuming output admission
-----------------------------------------------------------------------------------------

/-- Matching eventwise replay preserves canonical child links.
Witness: fold the existing individual-handler preservation theorem.
-/
theorem State.ChildLinksCanonical.replayGraphEvents {queue : State} {work parents}
    (links : queue.ChildLinksCanonical parents)
    (canonical
      : ∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
    (events : List GraphEvent) (matching : ∀ event ∈ events, event.MatchesWork work)
    : (queue.replayGraphEvents events).ChildLinksCanonical parents := by
  induction events generalizing queue with
  | nil => exact links
  | cons event rest ih =>
      exact ih (links.handleGraphEvent event (matching event List.mem_cons_self) canonical)
        (fun _ member => matching _ (List.mem_cons_of_mem _ member))

/-- Generated matching replay supplies the complete root-closure frame.
Witness: generated canonical ancestry, actual notice metadata, and independently proved
retirement preservation. Failure licensing and already-admitted outputs are not premises.
-/
theorem ExecutedWork.replay_rootClosureFrame {work before}
    (generated : ExecutedWork work) (matching : ∀ event ∈ before, event.MatchesWork work)
    : ∃ parents,
        (∀ node dependencies,
          GroupRecordAt work node dependencies → dependencies = parents node.ref)
        ∧ RootClosureFrame
            ((State.initialize (Work.fromExecution work)).replayGraphEvents before) work
            parents := by
  obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
  obtain ⟨_, records, support⟩ := generated.replay_noticeMetadata matching
  have links := createWorkQueue_childLinksCanonical (Work.fromExecution work) parents
    (fun _ member => workFromSpec_groups_parentCanonical_root canonical member)
  exact ⟨parents, canonical, records, links.replayGraphEvents canonical before matching,
    (generated.replayGraphEvents_structuralRetirement before matching).1, support.roots⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
