import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ConformancePlan
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutedWork
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.Minimality

/-! Terminal node accounting is the only independent terminal obligation for generated work. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Explained node accounting also accounts for every generated task
-----------------------------------------------------------------------------------------

/-- Terminal node accounting implies task accounting on the same explained history.
Witness: generated tasks have nonempty ownership; an outstanding task would have a healthy,
unclosed owner, contradicting that owner's terminal clause. No concrete root premise is
needed for this implication.
-/
theorem taskAccounting_of_nodes {work w} (generated : ExecutedWork work)
    (explained
      : Explains work (initialQueue work).initialGroups (initialQueue work).initialStreams
          w.events w.matching w.failures)
    (nodes : NodeAccounting work w)
    : TaskAccounting work w :=
  ((terminal_iff_nodes explained
      (fun _ _ _ _ known => generated.taskOwners_nonempty known)).mpr
    nodes).1

/-- Once event admission is explained, node accounting is equivalent to full termination.
Witness: derive the task clause from nonempty ownership, or project out the node clause.
-/
theorem terminal_iff_nodeAccounting {work w} (generated : ExecutedWork work)
    (explained
      : Explains work (initialQueue work).initialGroups (initialQueue work).initialStreams
          w.events w.matching w.failures)
    : Terminal work (initialRefs work) w.matching w.events w.failures
      ↔ NodeAccounting work w :=
  ⟨
    And.right,
    fun nodes => terminal (taskAccounting_of_nodes generated explained nodes) nodes
  ⟩

-----------------------------------------------------------------------------------------
-- Six independent constructions fill the existing seven-field certificate
-----------------------------------------------------------------------------------------

/-- The existing obligation package needs no independent terminal task construction.
Witness: assemble event admission first, then derive task accounting from node accounting
under the exact same matching and failure cuts. This is a proof dependency, not a stronger
source assumption or a change to the public scheduler contract.
-/
theorem obligations_of_nodeAccounting {work inputs w}
    (premises : ReplayPremises work inputs)
    (batching : BatchShape work inputs w) (announced : AnnouncedFailures work w)
    (uncancelled : UncancelledFailures work w)
    (publications : PublicationAdmission work w) (controls : ControlAdmission work w)
    (nodes
      : ((initialQueue work).runNormalized inputs).1.terminated = true
        → NodeAccounting work w)
    : Obligations work inputs w := by
  have explained := explains premises.initialized announced uncancelled publications controls
  exact ⟨batching, announced, uncancelled, publications, controls,
    fun done => taskAccounting_of_nodes premises.generated explained (nodes done), nodes⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
