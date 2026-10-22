import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.GrowingSiblingRefinement
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ScheduledLiteralFields

/-! Actual literal execution at differently mapped supplies. Non-stream literal
completion ignores defer metadata and allocates nothing; an eligible outer stream
transports its one fresh boundary. These exact eager laws construct growing field
witnesses together with the existing recursive cut-count proof. Objects are excluded
by the resolver-domain predicate, not by an assumed output relation. -/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open ScheduledWork

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

def completion (keys : Nat → Nat) (original : Completion α) : Completion α :=
  { original with work := work keys original.work }

theorem completion_combine (keys : Nat → Nat) (combine : α → β → γ)
    (left : Completion α) (right : Completion β)
    : completion keys (Completion.combine combine left right)
      = Completion.combine combine (completion keys left) (completion keys right) := by
  simp only [Completion.combine]
  split <;> simp_all [completion, Completion.error, work]

theorem completion_map (keys : Nat → Nat) (wrap : α → β) (original : Completion α)
    : completion keys (original.map wrap) = (completion keys original).map wrap := by
  cases known : original.result <;> simp [completion, Completion.map, Completion.error,
    known, work]

theorem completion_catchNull (keys : Nat → Nat) (wrap : α → ResponseValue)
    (original : Completion α)
    : completion keys (original.catchNull wrap)
      = (completion keys original).catchNull wrap := by
  cases known : original.result <;> simp [completion, Completion.catchNull, known, work]

theorem completion_nonNull (keys : Nat → Nat) (original : Completion ResponseValue)
    : completion keys original.nonNull = (completion keys original).nonNull := by
  simp only [Completion.nonNull]
  split <;> simp_all [completion, Completion.error, work]

-----------------------------------------------------------------------------------------
-- No-stream literal runs ignore all field/defer metadata and the initial supply
-----------------------------------------------------------------------------------------

/-- A single actual eager output, independent of inherited metadata and supply, and
unchanged by any key map. Structural empty combines are retained exactly. -/
def MetadataFreeRun
    (action : List FieldDetails → List Nat → DeferMap → StateM Nat (Completion α))
    : Prop :=
  ∃ completed,
    (∀ keys, completion keys completed = completed)
    ∧ ∀ fields usages context start,
        (action fields usages context).run start = (completed, start)

theorem MetadataFreeRun.pure (completed : Completion α)
    (fixed : ∀ keys, completion keys completed = completed)
    : MetadataFreeRun (fun _ _ _ => pure completed) :=
  ⟨completed, fixed, fun _ _ _ _ => rfl⟩

theorem MetadataFreeRun.map {action}
    (known : MetadataFreeRun action) (wrap : Completion α → Completion β)
    (commutes
      : ∀ keys completed,
          completion keys (wrap completed) = wrap (completion keys completed))
    : MetadataFreeRun
        (fun fields usages context => do
          return wrap (← action fields usages context)) := by
  obtain ⟨completed, fixed, actual⟩ := known
  refine ⟨wrap completed, fun keys => by rw [commutes, fixed], ?_⟩
  intro fields usages context start
  simp only [run_bind, actual, StateT.run_pure, id_pure_eq]

mutual
  theorem literal_value_metadataFree (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
      (value : ResolverValue ObjectRef) (path : ResponsePath)
      (literal : LiteralValue value)
      : MetadataFreeRun
          (fun fields usages context =>
            Execution.completeValue schema resolvers variables fuel fieldType fields value
              path usages context false) := by
    cases fuel with
    | zero =>
        simp only [Execution.completeValue]
        exact MetadataFreeRun.pure (Completion.error 1 : Completion ResponseValue)
          (fun _ => by simp [completion, Completion.error, work])
    | succ fuel =>
        cases fieldType with
        | nonNull inner =>
            simpa only [Execution.completeValue]
              using (literal_value_metadataFree schema resolvers variables (fuel + 1)
                      inner value path literal).map
                Completion.nonNull completion_nonNull
        | named name =>
            cases literal with
            | null =>
                simp only [Execution.completeValue]
                exact MetadataFreeRun.pure (.pure ResponseValue.null)
                  (fun _ => by simp [completion, Completion.pure, work])
            | scalar scalar =>
                simp only [Execution.completeValue]
                split
                · exact MetadataFreeRun.pure (Completion.error 1 : Completion ResponseValue)
                    (fun _ => by simp [completion, Completion.error, work])
                · exact MetadataFreeRun.pure (.pure (ResponseValue.scalar scalar))
                    (fun _ => by simp [completion, Completion.pure, work])
            | list values =>
                simp only [Execution.completeValue]
                exact MetadataFreeRun.pure (Completion.error 1 : Completion ResponseValue)
                  (fun _ => by simp [completion, Completion.error, work])
        | list inner =>
            cases literal with
            | null =>
                simp only [Execution.completeValue]
                exact MetadataFreeRun.pure (.pure ResponseValue.null)
                  (fun _ => by simp [completion, Completion.pure, work])
            | scalar scalar =>
                simp only [Execution.completeValue]
                exact MetadataFreeRun.pure (Completion.error 1 : Completion ResponseValue)
                  (fun _ => by simp [completion, Completion.error, work])
            | @list values known =>
                simpa only [Execution.completeValue,
                  Execution.completeListValueWithStream, Bool.false_eq_true, ↓reduceIte]
                  using (literal_list_metadataFree schema resolvers variables fuel inner
                          values path 0 known).map
                    (Completion.catchNull ResponseValue.list)
                    (fun keys => completion_catchNull keys ResponseValue.list)
  termination_by (fuel, 1, sizeOf fieldType, 0)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right

  theorem literal_list_metadataFree (schema : Schema) (resolvers : Resolvers ObjectRef)
      (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
      (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
      (literal : ∀ value ∈ values, LiteralValue value)
      : MetadataFreeRun
          (fun fields usages context =>
            Execution.completeListValue schema resolvers variables fuel itemType fields
              values path index usages context) := by
    cases values with
    | nil =>
        simp only [Execution.completeListValue]
        exact MetadataFreeRun.pure (Completion.pure ([] : List ResponseValue))
          (fun _ => by simp [completion, Completion.pure, work])
    | cons value rest =>
        obtain ⟨head, headFixed, headRun⟩ := literal_value_metadataFree schema resolvers
          variables fuel itemType value (path ++ [.index index]) (literal value (by simp))
        obtain ⟨tail, tailFixed, tailRun⟩ := literal_list_metadataFree schema resolvers variables
          fuel itemType rest path (index + 1)
          (fun value member => literal value (List.mem_cons_of_mem _ member))
        refine ⟨Completion.combine List.cons head tail, ?_, ?_⟩
        · intro keys
          rw [completion_combine, headFixed, tailFixed]
        · intro fields usages context start
          simp only [Execution.completeListValue, run_bind, headRun, tailRun,
            StateT.run_pure, id_pure_eq]
  termination_by (fuel, 2, sizeOf itemType, sizeOf values)
  decreasing_by
    all_goals subst_vars; simp_wf
    all_goals repeat first | apply Prod.Lex.left; omega | apply Prod.Lex.right
    all_goals try omega
end

-----------------------------------------------------------------------------------------
-- Literal stream items still use the original first-fatal stop and ordered positions
-----------------------------------------------------------------------------------------

theorem literal_items_metadataFree (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (values : List (ResolverValue ObjectRef)) (path : ResponsePath) (index : Nat)
    (literal : ∀ value ∈ values, LiteralValue value)
    : ∃ items : List (TaskOutcome ResponseValue × Work),
        (∀ keys, items.map (fun item => (item.1, work keys item.2)) = items)
        ∧ ∀ fields start,
            (Execution.completeStreamItems schema resolvers variables fuel itemType fields
              values path index).run
              start
            = (items, start) := by
  induction values generalizing index with
  | nil => exact ⟨[], fun _ => rfl, fun _ _ => by simp [Execution.completeStreamItems]⟩
  | cons value rest ih =>
      obtain ⟨head, headFixed, headRun⟩ := literal_value_metadataFree schema resolvers
        variables fuel itemType value (path ++ [.index index]) (literal value (by simp))
      obtain ⟨tail, tailFixed, tailRun⟩ := ih (index + 1)
        (fun value member => literal value (List.mem_cons_of_mem _ member))
      cases outcome : head.result with
      | error errors =>
          refine ⟨[(head.outcome, .empty)], fun _ => by simp [work], ?_⟩
          intro fields start
          simp only [Execution.completeStreamItems, run_bind, headRun, outcome,
            StateT.run_pure, id_pure_eq]
      | ok value =>
          refine ⟨(head.outcome, head.work) :: tail, ?_, ?_⟩
          · intro keys
            have same := congrArg Completion.work (headFixed keys)
            simp only [completion] at same
            simp only [List.map_cons, same, tailFixed]
          · intro fields start
            simp only [Execution.completeStreamItems, run_bind, headRun, outcome, tailRun,
              StateT.run_pure, id_pure_eq]

-----------------------------------------------------------------------------------------
-- Exact eager transport: arbitrary metadata mapping and one fresh stream boundary
-----------------------------------------------------------------------------------------

theorem literal_listWithStream_maps (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (itemType : TypeRef)
    (fields : List FieldDetails) (values : List (ResolverValue ObjectRef))
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (literal : ∀ value ∈ values, LiteralValue value) (keys : Nat → Nat) (start : Nat)
    (fresh : FreshTail keys start)
    : (Execution.completeListValueWithStream schema resolvers variables fuel itemType
        (fields.map (field keys)) values path (usages.map keys)
        (context.map (fragment keys)) allowStream).run
        (keys start)
      = (
        completion keys
          ((Execution.completeListValueWithStream schema resolvers variables fuel itemType
              fields values path usages context allowStream).run
            start).1,
        keys
          ((Execution.completeListValueWithStream schema resolvers variables fuel itemType
              fields values path usages context allowStream).run
            start).2
      ) := by
  have directives : ((fields.map (field keys)).head?.map FieldDetails.directives).getD []
      = (fields.head?.map FieldDetails.directives).getD [] := by
    cases fields <;> rfl
  simp only [Execution.completeListValueWithStream, directives]
  split
  · simp [completion, work]
  · obtain ⟨initial, fixed, actual⟩ := literal_list_metadataFree schema resolvers variables
      fuel itemType values path 0 literal
    simp only [run_bind, actual, StateT.run_pure, id_pure_eq]
    rw [completion_catchNull, fixed]
  · rename_i usageResult usage usageKnown
    obtain ⟨initial, fixed, actual⟩ := literal_list_metadataFree schema resolvers variables
      fuel itemType (values.take usage.initialCount) path 0
      (fun value member => literal value (List.mem_of_mem_take member))
    simp only [run_bind, actual]
    cases outcome : initial.result with
    | error errors =>
        simp only [StateT.run_pure, id_pure_eq]
        rw [completion_catchNull, fixed]
    | ok value =>
        simp only
        split
        · simp only [StateT.run_pure, id_pure_eq]
          rw [completion_catchNull, fixed]
        · obtain ⟨items, itemsFixed, itemsRun⟩ := literal_items_metadataFree schema resolvers
            variables fuel itemType (values.drop usage.initialCount) path usage.initialCount
            (fun value member => literal value (List.mem_of_mem_drop member))
          have successor : keys (start + 1) = keys start + 1 := fresh 1
          have caught := congrArg Completion.work
            (show completion keys (initial.catchNull ResponseValue.list)
              = initial.catchNull ResponseValue.list by rw [completion_catchNull, fixed])
          simp only [completion] at caught
          simp only [freshNodeRef, run_bind, StateT.run_get, StateT.run_set,
            StateT.run_pure, id_pure_eq, itemsRun, completion, work, caught, node,
            itemsFixed, successor]

theorem literal_value_maps (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (fieldType : TypeRef)
    (fields : List FieldDetails) (value : ResolverValue ObjectRef)
    (path : ResponsePath) (usages : List Nat) (context : DeferMap) (allowStream : Bool)
    (literal : LiteralValue value) (keys : Nat → Nat) (start : Nat)
    (fresh : FreshTail keys start)
    : (Execution.completeValue schema resolvers variables fuel fieldType
        (fields.map (field keys)) value path (usages.map keys)
        (context.map (fragment keys)) allowStream).run
        (keys start)
      = (
        completion keys
          ((Execution.completeValue schema resolvers variables fuel fieldType fields value
              path usages context allowStream).run
            start).1,
        keys
          ((Execution.completeValue schema resolvers variables fuel fieldType fields value
              path usages context allowStream).run
            start).2
      ) := by
  induction fieldType generalizing fuel with
  | nonNull inner ih =>
      cases fuel with
      | zero => simp [Execution.completeValue, completion, work, Completion.error]
      | succ fuel =>
          simp only [Execution.completeValue, run_bind, ih (fuel + 1),
            StateT.run_pure, id_pure_eq, completion_nonNull]
  | named name =>
      cases fuel with
      | zero => simp [Execution.completeValue, completion, work, Completion.error]
      | succ fuel =>
          cases literal <;> simp only [Execution.completeValue]
          · simp [completion, Completion.pure, work]
          · split <;> simp [completion, Completion.error, Completion.pure, work]
          · simp [completion, Completion.error, work]
  | list inner _ =>
      cases fuel with
      | zero => simp [Execution.completeValue, completion, work, Completion.error]
      | succ fuel =>
          cases literal with
          | null => simp [Execution.completeValue, completion, Completion.pure, work]
          | scalar => simp [Execution.completeValue, completion, Completion.error, work]
          | list values =>
              simpa only [Execution.completeValue]
                using literal_listWithStream_maps schema resolvers variables fuel inner
                  fields _ path usages context allowStream values keys start fresh

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.KeyRenaming
