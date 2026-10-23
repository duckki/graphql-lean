import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.KeyTailExtension
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingWorkRefinement

/-! Checked sibling-composition edge with a map constructed and extended by each child.
The same final witness relates the whole retained Work and both actual final supplies.
Recursive child witnesses remain explicit leaves; no public conformance assumption or
native history is strengthened to supply them. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.RefRegions
open KeyRenaming ScheduledErrors

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

-----------------------------------------------------------------------------------------
-- A child constructs one extending witness at its actual input/output boundaries
-----------------------------------------------------------------------------------------

structure SupplyMap (keys : Nat → Nat) (left right : Nat) : Prop where
  injective : Function.Injective keys
  images : PrefixBelow keys left right
  boundary : keys left = right
  fresh : FreshTail keys left

theorem SupplyMap.advance {keys : Nat → Nat} {left right finish : Nat}
    (known : SupplyMap keys left right) (advanced : left ≤ finish)
    : SupplyMap keys finish (keys finish) :=
  ⟨
    known.injective,
    PrefixBelow.advance (by simpa only [known.boundary] using known.images) known.fresh
      advanced,
    rfl,
    known.fresh.advance advanced
  ⟩

/-- A single child run certificate. Bounds include every hidden stream-item key;
earlier metadata images remain unchanged when the child constructs its new map. -/
structure RunRefines (initial next : Nat → Nat) (left right : Nat)
    (scheduled eager : Completion α × Nat)
    : Prop where
  compatible : ∀ key < left, next key = initial key
  supplies : SupplyMap next scheduled.2 eager.2
  scheduledMonotone : left ≤ scheduled.2
  eagerMonotone : right ≤ eager.2
  bounded : ∀ key ∈ allRefs scheduled.1.work, key < scheduled.2
  completion : CompletionRefines next scheduled.1 eager.1

theorem RunRefines.map {initial next left right} {scheduled eager : Completion α × Nat}
    (known : RunRefines initial next left right scheduled eager) (wrap : α → β)
    : RunRefines initial next left right (scheduled.1.map wrap, scheduled.2)
        (eager.1.map wrap, eager.2) := by
  refine ⟨known.compatible, known.supplies, known.scheduledMonotone, known.eagerMonotone,
    ?_, known.completion.map wrap⟩
  cases outcome : scheduled.1.result with
  | error errors =>
      simp [Completion.map, Completion.error, outcome, allRefs, rootRefs, hiddenRegions]
  | ok value => simpa only [Completion.map, outcome] using known.bounded

theorem RunRefines.catchNull {initial next left right}
    {scheduled eager : Completion α × Nat}
    (known : RunRefines initial next left right scheduled eager)
    (wrap : α → ResponseValue)
    : RunRefines initial next left right (scheduled.1.catchNull wrap, scheduled.2)
        (eager.1.catchNull wrap, eager.2) := by
  refine ⟨known.compatible, known.supplies, known.scheduledMonotone, known.eagerMonotone,
    ?_, known.completion.catchNull wrap⟩
  cases outcome : scheduled.1.result with
  | error errors => simp [Completion.catchNull, outcome, allRefs, rootRefs, hiddenRegions]
  | ok value => simpa only [Completion.catchNull, outcome] using known.bounded

/-- The recursive leaf must construct its map from these actual actions. `continues`
can carry the caller's inherited metadata/domain relation to the following sibling. -/
def GrowingActionRefines (continues : (Nat → Nat) → Nat → Nat → Prop)
    (scheduled eager : StateM Nat (Completion α))
    : Prop :=
  ∀ keys left right,
    SupplyMap keys left right
    → continues keys left right
    → BasicErrors.PositiveFailure (scheduled.run left).1.result
      ∧ ∃ next,
          RunRefines keys next left right (scheduled.run left) (eager.run right)
          ∧ continues next (scheduled.run left).2 (eager.run right).2

inductive PairedGrowingActions (continues : (Nat → Nat) → Nat → Nat → Prop)
    : List (StateM Nat (Completion α)) → List (StateM Nat (Completion α)) → Prop where
  | nil : PairedGrowingActions continues [] []
  | cons {scheduled eager scheduledRest eagerRest}
    (head : GrowingActionRefines continues scheduled eager)
    (rest : PairedGrowingActions continues scheduledRest eagerRest)
    : PairedGrowingActions continues (scheduled :: scheduledRest) (eager :: eagerRest)

-----------------------------------------------------------------------------------------
-- Actual eager suffixes advance; fatal semantic folds discard all child Work
-----------------------------------------------------------------------------------------

private theorem executeActions_monotone (combine : α → β → β) (base : β)
    {floor start : Nat} {actions : List (StateM Nat (Completion α))}
    (monotone : MonotoneAbove floor actions) (above : floor ≤ start)
    : start ≤ ((executeActions combine base actions).run start).2 := by
  induction actions generalizing start with
  | nil => exact Nat.le_refl _
  | cons head tail ih =>
      have first := monotone head (by simp) start above
      have later := ih monotone.tail (Nat.le_trans above first)
      simpa only [executeActions, run_bind, StateT.run_pure, id_pure_eq]
        using Nat.le_trans first later

private theorem completionCombine_bounded (combine : α → β → γ)
    {left : Completion α} {right : Completion β} {bound : Nat}
    (head : ∀ key ∈ allRefs left.work, key < bound)
    (tail : ∀ key ∈ allRefs right.work, key < bound)
    : ∀ key ∈ allRefs (Completion.combine combine left right).work, key < bound := by
  cases before : left.result <;> cases later : right.result <;>
    simp only [Completion.combine, before, later, Result.combine]
  all_goals first
    | exact fun key member => ((mem_allRefs_combine _ _ _).mp member).elim
        (head key) (tail key)
    | simp [Completion.error, allRefs, rootRefs, hiddenRegions]

-----------------------------------------------------------------------------------------
-- Compose extending maps, preserving all earlier siblings with the final witness
-----------------------------------------------------------------------------------------

/-- Conditional recursive edge, not the child-construction root. Healthy children
extend the current map; a fatal cut retargets its unused tail to the eager suffix's actual
final supply. All retained siblings use the same final map, including after a later cut. -/
def GrowingSiblingRefinement : Prop :=
  ∀ (α β : Type) (continues : (Nat → Nat) → Nat → Nat → Prop)
    (combine : α → β → β) (base : β)
    (scheduled eager : List (StateM Nat (Completion α))) keys left right floor,
    PairedGrowingActions continues scheduled eager
    → SupplyMap keys left right
    → continues keys left right
    → MonotoneAbove floor eager
    → floor ≤ right
    → ∃ next,
        RunRefines keys next left right ((cutActions combine base scheduled).run left)
          ((executeActions combine base eager).run right)
        ∧ (isFatal ((cutActions combine base scheduled).run left).1.result = false
            → continues next ((cutActions combine base scheduled).run left).2
                ((executeActions combine base eager).run right).2)

theorem growingSiblingRefinement_holds : GrowingSiblingRefinement := by
  intro α β continues combine base scheduled eager keys left right floor paired initial
    continuation monotone above
  induction paired generalizing keys left right with
  | nil =>
      refine ⟨keys, ⟨fun _ _ => rfl, initial, Nat.le_refl _, Nat.le_refl _, ?_,
        CompletionRefines.pure keys base⟩, fun _ => continuation⟩
      change ∀ key ∈ allRefs .empty, key < left
      simp [allRefs, rootRefs, hiddenRegions]
  | @cons scheduledHead eagerHead scheduledTail eagerTail head rest ih =>
      obtain ⟨positive, middle, first, continued⟩ := head keys left right initial continuation
      rw [cutActions_cons]
      simp only [executeActions, run_bind]
      cases outcome : (scheduledHead.run left).1.result with
      | error errors =>
          let target := ((executeActions combine base eagerTail).run (eagerHead.run right).2).2
          have suffix := executeActions_monotone combine base monotone.tail
            (Nat.le_trans above first.eagerMonotone)
          have images : PrefixBelow middle (scheduledHead.run left).2 target :=
            fun key earlier => Nat.lt_of_lt_of_le (first.supplies.images key earlier) suffix
          let next := retargetTail middle (scheduledHead.run left).2 target
          simp only [StateT.run_pure, id_pure_eq, Completion.error, isFatal,
            Bool.true_eq_false, false_implies, and_true]
          refine ⟨next, ⟨?_, ?_, first.scheduledMonotone,
            Nat.le_trans first.eagerMonotone suffix, ?_, ?_⟩⟩
          · intro key earlier
            exact (retargetTail_earlier middle
              (Nat.lt_of_lt_of_le earlier first.scheduledMonotone)).trans (first.compatible key earlier)
          · exact ⟨retargetTail_injective first.supplies.injective images,
              retargetTail_prefix images, retargetTail_boundary ..,
              retargetTail_fresh middle (scheduledHead.run left).2 target⟩
          · simp [allRefs, rootRefs, hiddenRegions]
          · rw [first.completion.2.2]
            exact CompletionRefines.fatal_cut combine _
              (by simpa only [outcome] using first.completion.1) (positive errors outcome)
      | ok value =>
          obtain ⟨next, later, continuedLater⟩ := ih middle _ _ first.supplies continued
            monotone.tail (Nat.le_trans above first.eagerMonotone)
          simp only [run_bind, StateT.run_pure, id_pure_eq]
          refine ⟨next, ⟨?_, later.supplies,
            Nat.le_trans first.scheduledMonotone later.scheduledMonotone,
            Nat.le_trans first.eagerMonotone later.eagerMonotone, ?_, ?_⟩, ?_⟩
          · intro key earlier
            exact (later.compatible key (Nat.lt_of_lt_of_le earlier first.scheduledMonotone)).trans
              (first.compatible key earlier)
          · exact completionCombine_bounded combine
              (fun key member => Nat.lt_of_lt_of_le (first.bounded key member)
                later.scheduledMonotone) later.bounded
          · exact (first.completion.rekey (fun key member =>
              later.compatible key (first.bounded key member))).combine combine later.completion
          · intro healthy
            rw [completion_combine_result, isFatal_combine, outcome] at healthy
            exact continuedLater (by simpa only [isFatal, Bool.false_or] using healthy)

-----------------------------------------------------------------------------------------
-- Actual recursive field/list driver edges; child construction remains explicit
-----------------------------------------------------------------------------------------

theorem executeCollectedFields_growing_of_children
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (parentType : Name) (source : ResolverValue ObjectRef)
    (cutFields eagerFields : CollectedFieldsMap) (path : ResponsePath)
    (cutUsages eagerUsages : List Nat) (cutContext eagerContext : DeferMap)
    (continues : (Nat → Nat) → Nat → Nat → Prop) (keys : Nat → Nat)
    (left right floor : Nat)
    (children
      : PairedGrowingActions continues
          (ScheduledExecution.fieldActions schema resolvers variables fuel parentType
            source cutFields path cutUsages cutContext)
          (ScheduledErrors.fieldActions schema resolvers variables fuel parentType source
            eagerFields path eagerUsages eagerContext))
    (initial : SupplyMap keys left right) (continuation : continues keys left right)
    (inherited : ∀ key ∈ eagerContext.flatMap RefRoles.fragmentRefs, key < floor)
    (above : floor ≤ right)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.executeCollectedFields schema resolvers variables fuel
              parentType source cutFields path cutUsages cutContext).run
            left)
          ((Execution.executeCollectedFields schema resolvers variables fuel parentType
              source eagerFields path eagerUsages eagerContext).run
            right) := by
  rw [ScheduledExecution.executeCollectedFields_actions, executeCollectedFields_actions]
  obtain ⟨next, related, _⟩ := growingSiblingRefinement_holds _ _ continues List.append []
    _ _ keys left right floor children initial continuation
    (fieldActions_monotone schema resolvers variables fuel parentType source eagerFields path
      eagerUsages eagerContext floor inherited) above
  exact ⟨next, related⟩

theorem completeListValue_growing_of_children
    (schema : Schema) (resolvers : Resolvers ObjectRef) (variables : VariableValues)
    (fuel : Nat) (itemType : TypeRef) (cutFields eagerFields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (cutUsages eagerUsages : List Nat) (cutContext eagerContext : DeferMap)
    (continues : (Nat → Nat) → Nat → Nat → Prop) (keys : Nat → Nat)
    (left right floor : Nat)
    (children
      : PairedGrowingActions continues
          (ScheduledExecution.listActions schema resolvers variables fuel itemType
            cutFields path cutUsages cutContext values index)
          (ScheduledErrors.listActions schema resolvers variables fuel itemType
            eagerFields path eagerUsages eagerContext values index))
    (initial : SupplyMap keys left right) (continuation : continues keys left right)
    (inherited : ∀ key ∈ eagerContext.flatMap RefRoles.fragmentRefs, key < floor)
    (above : floor ≤ right)
    : ∃ next,
        RunRefines keys next left right
          ((ScheduledExecution.completeListValue schema resolvers variables fuel itemType
              cutFields values path index cutUsages cutContext).run
            left)
          ((Execution.completeListValue schema resolvers variables fuel itemType
              eagerFields values path index eagerUsages eagerContext).run
            right) := by
  rw [ScheduledExecution.completeListValue_actions, completeListValue_actions]
  obtain ⟨next, related, _⟩ := growingSiblingRefinement_holds _ _ continues List.cons []
    _ _ keys left right floor children initial continuation
    (listActions_monotone schema resolvers variables fuel itemType eagerFields values path index
      eagerUsages eagerContext floor inherited) above
  exact ⟨next, related⟩

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
