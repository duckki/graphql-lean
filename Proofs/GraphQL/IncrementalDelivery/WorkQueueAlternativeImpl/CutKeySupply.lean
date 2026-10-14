import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.KeyRenamingCausality
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingCuts
import Proofs.GraphQL.IncrementalDelivery.Semantics.ExecutedRefRegions

/-! Construct an injective key extension from the actual supplies of an atomic cut.
Previously allocated keys stay fixed; fresh keys cross the skipped eager interval.
This is an allocation-boundary construction, not recursive Work or native correspondence.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Insert a skipped allocation interval without changing earlier keys
-----------------------------------------------------------------------------------------

def insertGap (boundary gap key : Nat) : Nat :=
  if key < boundary then key else key + gap

theorem insertGap_earlier {boundary gap key} (earlier : key < boundary)
    : insertGap boundary gap key = key := by
  simp only [insertGap, earlier, ↓reduceIte]

theorem insertGap_later {boundary gap key} (later : boundary ≤ key)
    : insertGap boundary gap key = key + gap := by
  simp only [insertGap, Nat.not_lt.mpr later, ↓reduceIte]

theorem insertGap_strict (boundary gap : Nat) {left right : Nat} (ordered : left < right)
    : insertGap boundary gap left < insertGap boundary gap right := by
  unfold insertGap
  split <;> split <;> omega

theorem insertGap_injective (boundary gap : Nat)
    : Function.Injective (insertGap boundary gap) := by
  intro left right same
  rcases Nat.lt_trichotomy left right with smaller | equal | larger
  · have strict := insertGap_strict boundary gap smaller
    omega
  · exact equal
  · have strict := insertGap_strict boundary gap larger
    omega

/-- Later cuts extend one existing map rather than selecting unrelated maps per scope. -/
def extendAtCut (previous : Nat → Nat) (boundary gap : Nat) : Nat → Nat :=
  previous ∘ insertGap boundary gap

theorem extendAtCut_injective {previous} (injective : Function.Injective previous)
    (boundary gap : Nat)
    : Function.Injective (extendAtCut previous boundary gap) := by
  intro left right same
  exact insertGap_injective boundary gap (injective same)

theorem extendAtCut_earlier (previous : Nat → Nat) {boundary gap key}
    (earlier : key < boundary)
    : extendAtCut previous boundary gap key = previous key := by
  simp only [extendAtCut, Function.comp_apply, insertGap_earlier earlier]

theorem extendAtCut_later (previous : Nat → Nat) {boundary gap key}
    (later : boundary ≤ key)
    : extendAtCut previous boundary gap key = previous (key + gap) := by
  simp only [extendAtCut, Function.comp_apply, insertGap_later later]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics (
  id_pure_eq id_bind_eq id_map_eq run_bind run_map)
open KeyRenaming

-----------------------------------------------------------------------------------------
-- Actual prefix/suffix supply bounds, allowing inherited keys below the starting supply
-----------------------------------------------------------------------------------------

/-- Every listed action advances supply when started above the same context floor. -/
def MonotoneAbove (floor : Nat) (actions : List (StateM Nat (Completion α))) : Prop :=
  ∀ action ∈ actions, ∀ supply, floor ≤ supply → supply ≤ (action.run supply).2

theorem MonotoneAbove.tail {floor} {action : StateM Nat (Completion α)} {rest}
    (monotone : MonotoneAbove floor (action :: rest))
    : MonotoneAbove floor rest := by
  intro action member
  exact monotone action (List.mem_cons_of_mem _ member)

theorem observeActions_supply {floor supply} {actions : List (StateM Nat (Completion α))}
    (monotone : MonotoneAbove floor actions) (above : floor ≤ supply)
    : supply ≤ ((observeActions actions).run supply).2 := by
  induction actions generalizing supply with
  | nil => exact Nat.le_refl _
  | cons action rest ih =>
      have advanced := monotone action (by simp) supply above
      have later := ih monotone.tail (Nat.le_trans above advanced)
      simpa only [observeActions, run_bind, StateT.run_pure, id_pure_eq]
        using Nat.le_trans advanced later

/-- Bounds are derived from executed actions; the suffix retains the same context floor. -/
theorem ActionCut.supply {floor supply completed remaining next}
    {actions : List (StateM Nat (Completion α))}
    (cut : ActionCut actions supply completed remaining next)
    (monotone : MonotoneAbove floor actions) (above : floor ≤ supply)
    : supply ≤ next ∧ MonotoneAbove floor remaining := by
  induction cut with
  | empty => exact ⟨Nat.le_refl _, monotone⟩
  | fatal action rest supply completed next errors ran _ =>
      have advanced := monotone action (by simp) supply above
      rw [ran] at advanced
      exact ⟨advanced, monotone.tail⟩
  | success action rest supply completed next observed remaining finish value errors ran _ _ ih
    =>
      have advanced := monotone action (by simp) supply above
      rw [ran] at advanced
      obtain ⟨later, suffix⟩ := ih monotone.tail (Nat.le_trans above advanced)
      exact ⟨Nat.le_trans advanced later, suffix⟩

theorem fieldActions_monotone (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (floor : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < floor)
    : MonotoneAbove floor
        (fieldActions schema resolvers variables fuel parentType source fields path usages
          context) := by
  intro action member supply above
  obtain ⟨⟨name, group⟩, _, rfl⟩ := List.mem_map.mp member
  exact (Semantics.RefRegions.executeResponseField_regions schema resolvers variables fuel
    parentType source name group path usages context supply
    (fun key member => Nat.lt_of_lt_of_le (inherited key member) above)).monotone

theorem listActions_monotone (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    (floor : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < floor)
    : MonotoneAbove floor
        (listActions schema resolvers variables fuel itemType fields path usages context
          values index) := by
  induction values generalizing index with
  | nil => intro action member; cases member
  | cons value rest ih =>
      intro action member supply above
      simp only [listActions, List.mem_cons] at member
      rcases member with rfl | member
      · exact (Semantics.RefRegions.completeValue_regions schema resolvers variables fuel
          itemType fields value (path ++ [.index index]) usages context false supply
          (fun key member => Nat.lt_of_lt_of_le (inherited key member) above)).monotone
      · exact ih (index + 1) action member supply above

-----------------------------------------------------------------------------------------
-- Checked constructor: derive one injective map and its boundary from the same cut
-----------------------------------------------------------------------------------------

/-- The map is computed from the actual boundaries; no correspondence is assumed. -/
def SupplyExtension (start cut eager : Nat) : Prop :=
  let keys := insertGap cut (eager - cut)
  Function.Injective keys
  ∧ start ≤ cut
  ∧ cut ≤ eager
  ∧ (∀ key, key < cut → keys key = key)
  ∧ keys cut = eager

/-- Original atomic actions construct both supplies and the interval insertion. This
root asserts no equality of later recursive outcomes, child Work, or native histories.
-/
def CutSupplyExtension : Prop :=
  ∀ (α : Type) (actions : List (StateM Nat (Completion α))) supply,
    MonotoneAbove supply actions
    → let cut := (observeUntilFatal actions).run supply
      let eager := (observeActions actions).run supply
      SupplyExtension supply cut.2 eager.2

theorem cutSupplyExtension_holds : CutSupplyExtension := by
  intro α actions supply monotone
  let cut := (observeUntilFatal actions).run supply
  have history : ActionCut actions supply cut.1.1 cut.1.2 cut.2 := observeUntilFatal_cut ..
  obtain ⟨advanced, suffix⟩ := history.supply monotone (Nat.le_refl _)
  have later := observeActions_supply suffix advanced
  have finish : ((observeActions actions).run supply).2
      = ((observeActions cut.1.2).run cut.2).2 := by
    simpa only
      using congrArg (fun result : List (Completion α) × Nat => result.2) history.observed
  change Function.Injective (insertGap cut.2 (((observeActions actions).run supply).2 - cut.2))
    ∧ supply ≤ cut.2 ∧ cut.2 ≤ ((observeActions actions).run supply).2
    ∧ (∀ key, key < cut.2 → insertGap cut.2 _ key = key)
    ∧ insertGap cut.2 _ cut.2 = ((observeActions actions).run supply).2
  have bounded : cut.2 ≤ ((observeActions actions).run supply).2 := by
    rw [finish]
    exact later
  refine ⟨
    insertGap_injective ..,
    advanced,
    bounded,
    fun _ earlier => insertGap_earlier earlier,
    ?_
  ⟩
  rw [insertGap_later (Nat.le_refl _)]
  change cut.2 + (((observeActions actions).run supply).2 - cut.2)
    = ((observeActions actions).run supply).2
  omega

/-- Original field recursion derives the constructor's supply premise at this call site. -/
theorem executeCollectedFields_cut_supply (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : CollectedFieldsMap)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (supply : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < supply)
    : SupplyExtension supply
        ((cutActions List.append []
            (fieldActions schema resolvers variables fuel parentType source fields path
              usages context)).run
          supply).2
        ((executeCollectedFields schema resolvers variables fuel parentType source fields
            path usages context).run
          supply).2 := by
  have constructed := cutSupplyExtension_holds _
    (fieldActions schema resolvers variables fuel parentType source fields path usages context)
    supply (fieldActions_monotone schema resolvers variables fuel parentType source fields
      path usages context supply inherited)
  simpa only [cutActions, run_bind, StateT.run_pure, id_pure_eq,
    executeCollectedFields_actions, executeActions_observed] using constructed

/-- Original list-item recursion likewise derives the supply premise, not native timing. -/
theorem completeListValue_cut_supply (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (index : Nat) (usages : List Nat) (context : DeferMap)
    (supply : Nat)
    (inherited : ∀ key ∈ context.flatMap Semantics.RefRoles.fragmentRefs, key < supply)
    : SupplyExtension supply
        ((cutActions List.cons []
            (listActions schema resolvers variables fuel itemType fields path usages
              context values index)).run
          supply).2
        ((completeListValue schema resolvers variables fuel itemType fields values path
            index usages context).run
          supply).2 := by
  have constructed := cutSupplyExtension_holds _
    (listActions schema resolvers variables fuel itemType fields path usages context values index)
    supply (listActions_monotone schema resolvers variables fuel itemType fields values
      path index usages context supply inherited)
  simpa only [cutActions, run_bind, StateT.run_pure, id_pure_eq,
    completeListValue_actions, executeActions_observed] using constructed

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledErrors
