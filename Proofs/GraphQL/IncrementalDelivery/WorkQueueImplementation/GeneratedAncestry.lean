import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork

/-! Generated defer ancestry, independent of live failed-owner retirement. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- A group's full defer ancestry is its immediate parent followed by that parent's
full ancestry. Both descriptors belong to `work`; this is proof-side execution metadata,
not a new event-source or conformance premise.
-/
def GroupAncestryChains (work : Execution.Work) : Prop :=
  ∀ child dependencies producer parent parentDependencies parentProducer,
    NodeAt work child .group dependencies producer
    → NodeAt work parent .group parentDependencies parentProducer
    → dependencies.head? = some parent.key
    → dependencies = parent.key :: parentDependencies

/-- Registration ancestry follows exact parent chains, even through taskless records.
Witness: the child's suffix supplies a parent record; generated canonical dependencies
identify its tail with the supplied parent's ancestry. No producer claim is needed.
-/
theorem ExecutedWork.groupRecordAncestryChain {work : Execution.Work}
    (generated : ExecutedWork work) {child dependencies parent parentDependencies}
    (known : GroupRecordAt work child dependencies)
    (parentKnown : GroupRecordAt work parent parentDependencies)
    (head : dependencies.head? = some parent.key)
    : dependencies = parent.key :: parentDependencies := by
  cases dependencies with
  | nil => simp at head
  | cons first rest =>
      have same : first = parent.key := Option.some.inj head
      subst first
      obtain ⟨record, key, recordKnown⟩ := known.parent
      obtain ⟨parents, canonical⟩ := generated.groupRecordsCanonical
      have tail := canonical record rest recordKnown
      rw [key, ← canonical parent parentDependencies parentKnown] at tail
      rw [tail]

/-- Every execution-generated work tree has exact full-ancestry contributor chains.
Witness: contributing nodes are registration records, so the full-chain theorem applies.
This includes shared groups, stream items, errors, and every explicit execution fuel.
-/
theorem ExecutedWork.groupAncestryChains {work : Execution.Work}
    (generated : ExecutedWork work)
    : GroupAncestryChains work := by
  intro child dependencies producer parent parentDependencies parentProducer known parentKnown head
  exact generated.groupRecordAncestryChain (groupRecordAt_of_nodeAt known)
    (groupRecordAt_of_nodeAt parentKnown) head

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
