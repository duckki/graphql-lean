import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledWorkCausality

/-! Exact key renaming is a special case of the recursive Work relation. These original
theorem interfaces reuse its causal transport rather than maintain a second kernel proof.
Failures and publication snapshots remain the same structural occurrences throughout. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics
open ScheduledWork (WorkRefines)

-----------------------------------------------------------------------------------------
-- Compatibility interfaces for exact retained-payload key renaming
-----------------------------------------------------------------------------------------

theorem task_owners {original occurrence owners}
    (known : TaskHasOwners original occurrence owners) (keys : Nat → Nat)
    : TaskHasOwners (work keys original) occurrence (owners.map keys) :=
  (WorkRefines.renaming keys original).task_owners known

theorem task_owners_original {keys original occurrence owners}
    (known : TaskHasOwners (work keys original) occurrence owners)
    : ∃ before, TaskHasOwners original occurrence before ∧ before.map keys = owners :=
  (WorkRefines.renaming keys original).task_owners_before known

theorem task_producer (keys : Nat → Nat) (original : Work) (occurrence : Occurrence)
    (producer : Option Occurrence)
    : TaskHasProducer (work keys original) occurrence producer
      ↔ TaskHasProducer original occurrence producer :=
  (WorkRefines.renaming keys original).task_producer occurrence producer

theorem task_succeeds (keys : Nat → Nat) (original : Work) (occurrence : Occurrence)
    : TaskSucceeds (work keys original) occurrence ↔ TaskSucceeds original occurrence :=
  (WorkRefines.renaming keys original).task_succeeds occurrence

theorem node_dependencies {original key kind dependencies}
    (known : NodeHasDependencies original key kind dependencies) (keys : Nat → Nat)
    : NodeHasDependencies (work keys original) (keys key) kind (dependencies.map keys) :=
  (WorkRefines.renaming keys original).node_dependencies known

theorem node_dependencies_original {keys original key kind dependencies}
    (injective : Function.Injective keys)
    (known : NodeHasDependencies (work keys original) (keys key) kind dependencies)
    : ∃ before,
        NodeHasDependencies original key kind before ∧ before.map keys = dependencies :=
  (WorkRefines.renaming keys original).node_dependencies_before injective known

theorem node_producer {keys} (injective : Function.Injective keys) (original : Work)
    (key : Nat) (producer : Option Occurrence)
    : NodeHasProducer (work keys original) (keys key) producer
      ↔ NodeHasProducer original key producer :=
  (WorkRefines.renaming keys original).node_producer injective key producer

theorem reachable (keys : Nat → Nat) (original : Work) (occurrence : Occurrence)
    : Reachable (work keys original) occurrence ↔ Reachable original occurrence :=
  (WorkRefines.renaming keys original).reachable occurrence

theorem node_failed_forward {keys original failed published key}
    (injective : Function.Injective keys)
    (failure : Causality.NodeFailed original failed published key)
    : Causality.NodeFailed (work keys original) failed published (keys key) :=
  (WorkRefines.renaming keys original).node_failed_forward injective failure

theorem task_cancelled_forward {keys original failed published occurrence}
    (injective : Function.Injective keys)
    (cancelled : Causality.TaskCancelled original failed published occurrence)
    : Causality.TaskCancelled (work keys original) failed published occurrence :=
  (WorkRefines.renaming keys original).task_cancelled_forward injective cancelled

theorem node_failed_original {keys original failed published renamed}
    (injective : Function.Injective keys)
    (failure : Causality.NodeFailed (work keys original) failed published renamed)
    : ∀ key, renamed = keys key → Causality.NodeFailed original failed published key :=
  (WorkRefines.renaming keys original).node_failed_before injective failure

theorem task_cancelled_original {keys original failed published occurrence}
    (injective : Function.Injective keys)
    (cancelled : Causality.TaskCancelled (work keys original) failed published occurrence)
    : Causality.TaskCancelled original failed published occurrence :=
  (WorkRefines.renaming keys original).task_cancelled_before injective cancelled

theorem failed_key_image {keys original failed published renamed}
    (failure : Causality.NodeFailed (work keys original) failed published renamed)
    : ∃ key, keys key = renamed :=
  (WorkRefines.renaming keys original).failed_key_image failure

theorem node_failed_coverage {keys original failed published renamed}
    (injective : Function.Injective keys)
    (failure : Causality.NodeFailed (work keys original) failed published renamed)
    : ∃ key, keys key = renamed ∧ Causality.NodeFailed original failed published key :=
  (ScheduledWork.recursiveWorkCausality_holds keys injective original
    (work keys original) (WorkRefines.renaming keys original) failed published).2.1
    renamed
  |>.mp failure

-----------------------------------------------------------------------------------------
-- Original checked root, derived from the general recursive Work transport root
-----------------------------------------------------------------------------------------

/-- At the same failure/publication cut, injective key renaming neither adds nor loses
reachability, node failure or task cancellation. The map's recursive execution/native
construction remains outside this conditional transport theorem. -/
def CausalKeyRenaming : Prop :=
  ∀ keys,
    Function.Injective keys
    → ∀ original failed published,
        (∀ occurrence,
          Reachable (work keys original) occurrence ↔ Reachable original occurrence)
        ∧ (∀ renamed,
            Causality.NodeFailed (work keys original) failed published renamed
            ↔ ∃ key,
                keys key = renamed ∧ Causality.NodeFailed original failed published key)
        ∧ (∀ occurrence,
            Causality.TaskCancelled (work keys original) failed published occurrence
            ↔ Causality.TaskCancelled original failed published occurrence)

theorem causalKeyRenaming_holds : CausalKeyRenaming := by
  intro keys injective original failed published
  exact ScheduledWork.recursiveWorkCausality_holds keys injective original
    (work keys original) (WorkRefines.renaming keys original) failed published

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming
