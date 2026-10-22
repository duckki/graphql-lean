import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.WorkKeyRenaming
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.SiblingResultRefinement

/-! Proof-only recursive Work correspondence for changed counts and allocation keys.
The constructors retain every structural address, item position, descriptor path/label,
owner and producer, using one map throughout. Retained payloads satisfy ResultRefines,
not literal equality. This does not construct the map from recursive execution, choose
a native history, or justify omitting errors already recorded by that history. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork

open GraphQL.IncrementalDelivery.Execution WorkQueueSemantics
open ScheduledErrors (ResultRefines)

-----------------------------------------------------------------------------------------
-- Recursive relation: one key map, unchanged structure, related retained payloads
-----------------------------------------------------------------------------------------

/-- Collected outcomes may omit diagnostics, while the same escaping cause is retained.
This extra component is necessary: diagnostic-count refinement alone says nothing about
which error reaches an incremental boundary.
-/
def TaskOutcomeRefines (scheduled eager : TaskOutcome α) : Prop :=
  ResultRefines scheduled.result eager.result ∧ scheduled.cause = eager.cause

theorem TaskOutcomeRefines.refl (outcome : TaskOutcome α)
    : TaskOutcomeRefines outcome outcome :=
  ⟨ResultRefines.refl _, rfl⟩

/-- Coupled cause metadata also relates the outcomes actually delivered by each task. -/
theorem TaskOutcomeRefines.deliveryResult {left right : TaskOutcome α}
    (known : TaskOutcomeRefines left right)
    : ResultRefines left.deliveryResult right.deliveryResult := by
  rcases left with ⟨left, cause⟩
  rcases right with ⟨right, otherCause⟩
  obtain ⟨related, rfl⟩ := known
  cases left <;> cases right <;> cases cause <;>
    simp_all [ResultRefines, ScheduledErrors.SameData, TaskOutcome.deliveryResult,
      ScheduledErrors.countedErrors]

mutual
  /-- Retained Work has the same structure and data; counts may decrease and keys use
  one shared map. No extra/missing tasks or stream positions are permitted. -/
  inductive WorkRefines (keys : Nat → Nat) : Work → Work → Prop where
    | empty : WorkRefines keys .empty .empty
    | combine {left right eagerLeft eagerRight}
      (head : WorkRefines keys left eagerLeft)
      (tail : WorkRefines keys right eagerRight)
      : WorkRefines keys (.combine left right) (.combine eagerLeft eagerRight)
    | executionGroup {groups path result eagerResult children eagerChildren}
      (payload : TaskOutcomeRefines result eagerResult)
      (nested : WorkRefines keys children eagerChildren)
      : WorkRefines keys (.executionGroup groups path result children)
          (.executionGroup (groups.map (KeyRenaming.fragment keys)) path eagerResult
            eagerChildren)
    | stream {node items eagerItems} (nested : ItemsRefine keys items eagerItems)
      : WorkRefines keys (.stream node items)
          (.stream (KeyRenaming.node keys node) eagerItems)

  /-- Same ordered stream positions, with related payloads and recursively related Work. -/
  inductive ItemsRefine (keys : Nat → Nat)
      : List (TaskOutcome ResponseValue × Work) → List (TaskOutcome ResponseValue × Work)
        → Prop where
    | nil : ItemsRefine keys [] []
    | cons {result eagerResult children eagerChildren rest eagerRest}
      (payload : TaskOutcomeRefines result eagerResult)
      (nested : WorkRefines keys children eagerChildren)
      (tail : ItemsRefine keys rest eagerRest)
      : ItemsRefine keys ((result, children) :: rest)
          ((eagerResult, eagerChildren) :: eagerRest)
end

/-- A completion relates its initial result and all retained Work using the same map. -/
def CompletionRefines (keys : Nat → Nat) (scheduled eager : Completion α) : Prop :=
  ResultRefines scheduled.result eager.result
  ∧ WorkRefines keys scheduled.work eager.work
  ∧ scheduled.cause = eager.cause

mutual
  /-- Exact key renaming is a special case; no retained count changes are required. -/
  theorem WorkRefines.renaming (keys : Nat → Nat) (original : Work)
      : WorkRefines keys original (KeyRenaming.work keys original) := by
    cases original with
    | empty => simpa only [KeyRenaming.work] using WorkRefines.empty (keys := keys)
    | combine left right =>
        simpa only [KeyRenaming.work]
          using WorkRefines.combine (WorkRefines.renaming keys left)
            (WorkRefines.renaming keys right)
    | executionGroup groups path result children =>
        simpa only [KeyRenaming.work]
          using WorkRefines.executionGroup (groups := groups) (path := path)
            (TaskOutcomeRefines.refl result) (WorkRefines.renaming keys children)
    | stream node items =>
        simpa only [KeyRenaming.work]
          using WorkRefines.stream (node := node) (ItemsRefine.renaming keys items)
  termination_by sizeOf original

  theorem ItemsRefine.renaming (keys : Nat → Nat)
      (items : List (TaskOutcome ResponseValue × Work))
      : ItemsRefine keys items
          (items.map (fun item => (item.1, KeyRenaming.work keys item.2))) := by
    cases items with
    | nil => exact .nil
    | cons item rest =>
        exact .cons (TaskOutcomeRefines.refl item.1) (WorkRefines.renaming keys item.2)
          (ItemsRefine.renaming keys rest)
  termination_by sizeOf items
  decreasing_by
    all_goals simp_wf
    all_goals try decreasing_trivial
    rcases item with ⟨result, children⟩
    simp only [Prod.mk.sizeOf_spec]
    omega
end

/-- Fixed object paths or mapped item descriptors, with related data/status/counts. -/
inductive PayloadRefines (keys : Nat → Nat) : Payload → Payload → Prop where
  | object {path result eagerResult} (known : ResultRefines result eagerResult)
    : PayloadRefines keys (.object path result) (.object path eagerResult)
  | item {node result eagerResult} (known : ResultRefines result eagerResult)
    : PayloadRefines keys (.item node result)
        (.item (KeyRenaming.node keys node) eagerResult)

-----------------------------------------------------------------------------------------
-- Completion constructors preserve the recursive relation
-----------------------------------------------------------------------------------------

theorem CompletionRefines.pure (keys : Nat → Nat) (value : α)
    : CompletionRefines keys (.pure value) (.pure value) :=
  ⟨ResultRefines.refl _, .empty, rfl⟩

theorem CompletionRefines.error {keys : Nat → Nat} {left right : Nat}
    (known : ResultRefines (.error left : Result α) (.error right)) (same : left = right)
    : CompletionRefines keys (.error left : Completion α) (.error right) :=
  ⟨known, .empty, congrArg some same⟩

/-- A fatal scope discards semantic child Work on both sides, including an eager suffix.
The positive actual failure is essential to preserve zero-error equivalence. -/
theorem CompletionRefines.fatal_cut (combine : α → β → γ)
    {keys : Nat → Nat} {errors : Nat} {head : Completion α} (tail : Completion β)
    (known : ResultRefines (.error errors) head.result) (positive : 0 < errors)
    : CompletionRefines keys
        ({ result := .error errors, cause := head.cause } : Completion γ)
        (Completion.combine combine head tail) := by
  have result := known.fatal_cut combine tail.result positive
  refine ⟨by simpa only [ScheduledErrors.completion_combine_result] using result, ?_, ?_⟩
  all_goals cases outcome : head.result with
  | error count =>
      cases later : tail.result <;>
        simp only [Completion.combine, outcome, later, Result.combine]
      all_goals first | rfl | exact .empty
  | ok value => simp [ResultRefines, ScheduledErrors.SameData, outcome] at known

/-- Related completions retain related future-task outcomes. -/
theorem CompletionRefines.outcome {keys : Nat → Nat} {left right : Completion α}
    (known : CompletionRefines keys left right)
    : TaskOutcomeRefines left.outcome right.outcome :=
  ⟨known.1, known.2.2⟩

theorem CompletionRefines.combine (combine : α → β → γ)
    {keys : Nat → Nat} {left eagerLeft : Completion α} {right eagerRight : Completion β}
    (head : CompletionRefines keys left eagerLeft)
    (tail : CompletionRefines keys right eagerRight)
    : CompletionRefines keys (Completion.combine combine left right)
        (Completion.combine combine eagerLeft eagerRight) := by
  have result := head.1.combine combine tail.1
  refine ⟨by simpa only [ScheduledErrors.completion_combine_result] using result, ?_, ?_⟩
  all_goals
    cases hl : left.result <;> cases he : eagerLeft.result <;>
      cases hr : right.result <;> cases her : eagerRight.result <;>
      simp_all only [CompletionRefines, ResultRefines, ScheduledErrors.SameData, false_and]
  all_goals simp_all only [Completion.combine, Result.combine]
  all_goals first | exact .empty | exact .combine head.2.1 tail.2.1

theorem CompletionRefines.map (wrap : α → β) {keys : Nat → Nat}
    {left right : Completion α} (known : CompletionRefines keys left right)
    : CompletionRefines keys (left.map wrap) (right.map wrap) := by
  refine ⟨known.1.completion_map wrap, ?_, ?_⟩
  all_goals
    cases hl : left.result <;> cases hr : right.result <;>
      simp_all only [CompletionRefines, ResultRefines, ScheduledErrors.SameData, false_and]
  all_goals simp_all only [Completion.map]
  all_goals exact .empty

theorem CompletionRefines.catchNull (wrap : α → ResponseValue) {keys : Nat → Nat}
    {left right : Completion α} (known : CompletionRefines keys left right)
    : CompletionRefines keys (left.catchNull wrap) (right.catchNull wrap) := by
  refine ⟨known.1.catchNull wrap, ?_, ?_⟩
  all_goals
    cases hl : left.result <;> cases hr : right.result <;>
      simp_all only [CompletionRefines, ResultRefines, ScheduledErrors.SameData, false_and]
  all_goals simp_all only [Completion.catchNull]
  all_goals exact .empty

theorem CompletionRefines.nonNull {keys : Nat → Nat}
    {left right : Completion ResponseValue} (known : CompletionRefines keys left right)
    : CompletionRefines keys left.nonNull right.nonNull := by
  refine ⟨known.1.nonNull, ?_, ?_⟩
  · rcases left with ⟨left, leftWork⟩
    rcases right with ⟨right, rightWork⟩
    rcases left with errors | ⟨value, errors⟩
    <;> rcases right with eagerErrors | ⟨eagerValue, eagerErrors⟩
    <;> simp_all only [CompletionRefines, ResultRefines, ScheduledErrors.SameData,
      false_and]
    · exact .empty
    · obtain ⟨⟨rfl, bounded, zero⟩, nested, sameCause⟩ := known
      cases value with
      | null => cases errors <;> cases eagerErrors <;> exact .empty
      | scalar | object | list => exact nested
  · rcases left with ⟨left, leftWork, leftCause⟩
    rcases right with ⟨right, rightWork, rightCause⟩
    rcases left with errors | ⟨value, errors⟩
    <;> rcases right with eagerErrors | ⟨eagerValue, eagerErrors⟩
    <;> simp_all only [CompletionRefines, ResultRefines, ScheduledErrors.SameData, false_and]
    · simp [Completion.nonNull, nonNullCompletion]
    · obtain ⟨⟨rfl, bounded, zero⟩, nested, sameCause⟩ := known
      cases value <;> simp [Completion.nonNull, nonNullCompletion]

-----------------------------------------------------------------------------------------
-- Coupled lookups include absence and preserve ordered enclosing owners/producers
-----------------------------------------------------------------------------------------

/-- Absence agrees, or the two actual lookup results satisfy the chosen relation. -/
def OptionRefines (related : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some left, some right => related left right
  | _, _ => False

/-- A coupled location has related subwork and the same structural producer. -/
def LocationRefines (keys : Nat → Nat) (left right : WorkLocation) : Prop :=
  WorkRefines keys left.current right.current
  ∧ right.producer = left.producer
  ∧ right.owners = left.owners.map keys

theorem ItemsRefine.getElem? {keys left right} (known : ItemsRefine keys left right)
    (index : Nat)
    : OptionRefines
        (fun before after =>
          TaskOutcomeRefines before.1 after.1 ∧ WorkRefines keys before.2 after.2)
        left[index]? right[index]? := by
  induction index generalizing left right with
  | zero =>
      cases known with
      | nil => trivial
      | cons payload nested tail => exact ⟨payload, nested⟩
  | succ index ih =>
      cases known with
      | nil => trivial
      | cons payload nested tail => exact ih tail

theorem LocationRefines.child {keys left right} (known : LocationRefines keys left right)
    (address : Address) (index : Nat)
    : OptionRefines (LocationRefines keys)
        (left.child? address index) (right.child? address index) := by
  rcases left with ⟨left, producer, owners⟩
  rcases right with ⟨right, eagerProducer, eagerOwners⟩
  dsimp only [LocationRefines] at known
  obtain ⟨related, rfl, rfl⟩ := known
  cases related with
  | empty => trivial
  | combine head tail =>
      cases index with
      | zero => exact ⟨head, rfl, rfl⟩
      | succ index =>
          cases index with
          | zero => exact ⟨tail, rfl, rfl⟩
          | succ => trivial
  | executionGroup payload nested =>
      cases index with
      | zero => exact ⟨nested, rfl, KeyRenaming.group_keys ..⟩
      | succ => trivial
  | @stream node items eagerItems nested =>
      have entry := nested.getElem? index
      cases before : items[index]? with
      | none =>
          cases after : eagerItems[index]? <;>
            simp_all [WorkLocation.child?, OptionRefines]
      | some before =>
          cases after : eagerItems[index]? with
          | none => simp_all [OptionRefines]
          | some after =>
              simp only [before, after, OptionRefines] at entry
              simp only [WorkLocation.child?, before, after, Option.map_some,
                OptionRefines]
              exact ⟨entry.2, rfl, rfl⟩

theorem LocationRefines.traverse {keys left right}
    (known : LocationRefines keys left right) (route rest : Address)
    : OptionRefines (LocationRefines keys)
        (locateWork.go route left rest) (locateWork.go route right rest) := by
  induction rest generalizing route left right with
  | nil => exact known
  | cons index rest ih =>
      have step := known.child route index
      cases before : left.child? route index with
      | none => cases after : right.child? route index <;>
          simp_all [locateWork.go, OptionRefines]
      | some before =>
          cases after : right.child? route index with
          | none => simp_all [OptionRefines]
          | some after =>
              simp only [before, after, OptionRefines] at step
              simpa [locateWork.go, before, after] using ih step (route ++ [index])

theorem WorkRefines.locate {keys left right} (known : WorkRefines keys left right)
    (address : Address)
    : OptionRefines (LocationRefines keys)
        (locateWork left address) (locateWork right address) :=
  LocationRefines.traverse (left := ⟨left, none, []⟩) (right := ⟨right, none, []⟩)
    ⟨known, rfl, rfl⟩ [] address

theorem WorkRefines.located {keys left right address current producer owners}
    (related : WorkRefines keys left right)
    (found : Located left address current producer owners)
    : ∃ after,
        Located right address after producer (owners.map keys)
        ∧ WorkRefines keys current after := by
  have lookup := related.locate address
  unfold Located at found ⊢
  rw [found] at lookup
  cases eager : locateWork right address with
  | none => simp [eager, OptionRefines] at lookup
  | some after =>
      rw [eager] at lookup
      rcases after with ⟨after, birth, enclosing⟩
      dsimp only [OptionRefines, LocationRefines] at lookup
      obtain ⟨nested, rfl, rfl⟩ := lookup
      exact ⟨after, rfl, nested⟩

theorem WorkRefines.located_before {keys left right address current producer owners}
    (related : WorkRefines keys left right)
    (found : Located right address current producer owners)
    : ∃ before enclosing,
        Located left address before producer enclosing
        ∧ enclosing.map keys = owners
        ∧ WorkRefines keys before current := by
  have lookup := related.locate address
  unfold Located at found ⊢
  rw [found] at lookup
  cases scheduled : locateWork left address with
  | none => simp [scheduled, OptionRefines] at lookup
  | some before =>
      rw [scheduled] at lookup
      rcases before with ⟨before, birth, enclosing⟩
      dsimp only [OptionRefines, LocationRefines] at lookup
      obtain ⟨nested, rfl, rfl⟩ := lookup
      exact ⟨before, enclosing, rfl, rfl, nested⟩

-----------------------------------------------------------------------------------------
-- Task/node soundness and coverage include every nested stream position
-----------------------------------------------------------------------------------------

theorem WorkRefines.task {keys left right occurrence owners producer value}
    (related : WorkRefines keys left right)
    (known : TaskAt left occurrence owners producer value)
    : ∃ after,
        TaskAt right occurrence (owners.map keys) producer after
        ∧ PayloadRefines keys value after := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup found =>
      obtain ⟨after, located, nested⟩ := related.located found.toCurrent
      cases nested with
      | executionGroup payload children =>
          exact ⟨
            _,
            by simpa only [KeyRenaming.group_keys] using TaskAt.executionGroup located,
            .object payload.deliveryResult
          ⟩
  | @item address node items producer enclosing index result children found entry =>
      obtain ⟨after, located, nested⟩ := related.located found.toCurrent
      cases nested with
      | @stream _ _ eagerItems paired =>
          have item := paired.getElem? index
          rw [entry] at item
          cases eager : eagerItems[index]? with
          | none => simp [eager, OptionRefines] at item
          | some after =>
              rw [eager] at item
              rcases after with ⟨eagerResult, eagerChildren⟩
              exact ⟨
                _,
                by
                  simpa only [List.map_singleton, KeyRenaming.node]
                    using TaskAt.item located eager,
                .item item.1.deliveryResult
              ⟩

theorem WorkRefines.task_before {keys left right occurrence owners producer value}
    (related : WorkRefines keys left right)
    (known : TaskAt right occurrence owners producer value)
    : ∃ before outcome,
        TaskAt left occurrence before producer outcome
        ∧ before.map keys = owners
        ∧ PayloadRefines keys outcome value := by
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup found =>
      obtain ⟨before, enclosing, located, _, nested⟩ :=
        related.located_before found.toCurrent
      cases nested with
      | executionGroup payload children =>
          exact ⟨_, _, TaskAt.executionGroup located,
            (KeyRenaming.group_keys ..).symm, .object payload.deliveryResult⟩
  | @item address node items producer enclosing index result children found entry =>
      obtain ⟨before, enclosing, located, _, nested⟩ :=
        related.located_before found.toCurrent
      cases nested with
      | @stream beforeNode beforeItems _ paired =>
          have item := paired.getElem? index
          rw [entry] at item
          cases scheduled : beforeItems[index]? with
          | none => simp [scheduled, OptionRefines] at item
          | some before =>
              rw [scheduled] at item
              rcases before with ⟨beforeResult, beforeChildren⟩
              exact ⟨_, _, TaskAt.item located scheduled, rfl, .item item.1.deliveryResult⟩

theorem WorkRefines.delivery_node {keys left right node kind dependencies producer}
    (related : WorkRefines keys left right)
    (known : NodeAt left node kind dependencies producer)
    : NodeAt right (KeyRenaming.node keys node) kind (dependencies.map keys)
        producer := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group found member =>
      obtain ⟨after, located, nested⟩ := related.located found.toCurrent
      cases nested with
      | executionGroup payload children =>
          simpa only [KeyRenaming.fragment, KeyRenaming.node, List.map_map,
            Function.comp_def]
            using NodeAt.group located (List.mem_map_of_mem member)
  | stream found =>
      obtain ⟨after, located, nested⟩ := related.located found.toCurrent
      cases nested with
      | stream paired => exact NodeAt.stream located

theorem WorkRefines.node_before {keys left right node kind dependencies producer}
    (related : WorkRefines keys left right)
    (known : NodeAt right node kind dependencies producer)
    : ∃ before parents,
        NodeAt left before kind parents producer
        ∧ KeyRenaming.node keys before = node
        ∧ parents.map keys = dependencies := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group found member =>
      obtain ⟨before, enclosing, located, _, nested⟩ :=
        related.located_before found.toCurrent
      cases nested with
      | executionGroup payload children =>
          obtain ⟨original, oldMember, rfl⟩ := List.mem_map.mp member
          exact ⟨_, _, NodeAt.group located oldMember, rfl,
            (KeyRenaming.ancestor_keys ..).symm⟩
  | stream found =>
      obtain ⟨before, enclosing, located, mapped, nested⟩ :=
        related.located_before found.toCurrent
      cases nested with
      | stream paired => exact ⟨_, _, NodeAt.stream located, rfl, mapped⟩

theorem PayloadRefines.failure_status {keys left right}
    (known : PayloadRefines keys left right)
    : right.failure = none ↔ left.failure = none := by
  cases known with
  | @object path result eagerResult refined =>
      cases result <;> cases eagerResult <;>
        simp_all [ResultRefines, ScheduledErrors.SameData, Payload.failure]
  | @item node result eagerResult refined =>
      cases result <;> cases eagerResult <;>
        simp_all [ResultRefines, ScheduledErrors.SameData, Payload.failure]

-----------------------------------------------------------------------------------------
-- Checked structural root: a relation is transported, not assumed to be constructed
-----------------------------------------------------------------------------------------

/-- Changed retained counts do not add/lose structural tasks or nodes. The recursive
executor must still construct this Work relation and its compatible key map. -/
def RecursiveWorkStructure : Prop :=
  ∀ keys left right,
    WorkRefines keys left right
    → (∀ address,
        OptionRefines (LocationRefines keys)
          (locateWork left address) (locateWork right address))
      ∧ (∀ occurrence owners producer value,
          TaskAt left occurrence owners producer value
          → ∃ after,
              TaskAt right occurrence (owners.map keys) producer after
              ∧ PayloadRefines keys value after)
      ∧ (∀ occurrence owners producer value,
          TaskAt right occurrence owners producer value
          → ∃ before outcome,
              TaskAt left occurrence before producer outcome
              ∧ before.map keys = owners
              ∧ PayloadRefines keys outcome value)
      ∧ (∀ node kind dependencies producer,
          NodeAt right node kind dependencies producer
          ↔ ∃ before parents,
              NodeAt left before kind parents producer
              ∧ KeyRenaming.node keys before = node
              ∧ parents.map keys = dependencies)

theorem recursiveWorkStructure_holds : RecursiveWorkStructure := by
  intro keys left right related
  refine ⟨related.locate, ?_, ?_, ?_⟩
  · intro occurrence owners producer value
    exact related.task
  · intro occurrence owners producer value
    exact related.task_before
  · intro node kind dependencies producer
    constructor
    · exact related.node_before
    · rintro ⟨before, parents, known, rfl, rfl⟩
      exact related.delivery_node known

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.ScheduledWork
