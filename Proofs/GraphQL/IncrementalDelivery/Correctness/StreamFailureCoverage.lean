import Proofs.GraphQL.IncrementalDelivery.Correctness.ReferenceFailureCoverage
import Proofs.GraphQL.IncrementalDelivery.Correctness.BasicListErrors
import Proofs.GraphQL.IncrementalDelivery.Correctness.ArgumentValidity

/-! Plain streamed tails account for ordinary list positions even when items fail. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

attribute [local simp] Semantics.id_pure_eq Semantics.id_bind_eq Semantics.id_map_eq
  Semantics.run_bind Semantics.run_map

-----------------------------------------------------------------------------------------
-- Successful items occur in the prepared source inventory
-----------------------------------------------------------------------------------------

/-- Splitting list data shifts the suffix's absolute response indices by prefix length.
Witness: list induction; the equation includes or omits nested containers consistently.
-/
theorem positions_items_append (containers : Bool) (path : ResponsePath) (index : Nat)
    (left right : List ResponseValue)
    : ResponsePositions.items containers path index (left ++ right)
      = ResponsePositions.items containers path index left
        ++ ResponsePositions.items containers path (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [ResponsePositions.items]
  | cons head rest ih =>
      simp only [List.cons_append, ResponsePositions.items, ih, List.length_cons,
        List.append_assoc, Nat.add_assoc, Nat.add_comm 1]

/-- Successful direct stream-item positions belong to the full source-task inventory.
Witness: item-list induction keeps the head's positions and shifts the tail's index.
Nested child tasks may contribute additional positions; they are not assumed empty.
-/
theorem sourceItemTasks_success_positions (containers : Bool)
    (address : Address) (producer : Option Occurrence) (node : DeliveryNode)
    (index ordinal : Nat) (items : List (TaskOutcome ResponseValue × Work))
    (entries : List (ResponseValue × Nat))
    (successful : items.map (fun item => item.1.result) = entries.map Except.ok)
    : ResponsePositions.items containers node.path index (entries.map Prod.fst)
      ⊆ (sourceItemTasks address producer node index ordinal items).flatMap
          (SourceTask.positions containers) := by
  induction items generalizing entries index ordinal with
  | nil =>
      cases entries <;> simp_all [ResponsePositions.items]
  | cons item rest ih =>
      rcases item with ⟨result, children⟩
      cases entries with
      | nil => simp at successful
      | cons entry entries =>
          simp only [List.map_cons, List.cons.injEq] at successful
          obtain ⟨headResult, remaining⟩ := successful
          have tail := ih (index + 1) (ordinal + 1) entries remaining
          simp only [List.map_cons, ResponsePositions.items, sourceItemTasks,
            List.flatMap_cons, List.flatMap_append, SourceTask.positions,
            TaskOutcome.deliveryResult, headResult, DeliveryPaths.result]
          intro position member
          rcases List.mem_append.mp member with head | later
          · exact List.mem_append_left _ head
          · exact List.mem_append_right _ (List.mem_append_right _ (tail later))

-----------------------------------------------------------------------------------------
-- Ordinary list success or bubbling is represented by the retained stream
-----------------------------------------------------------------------------------------

/-- A plain streamed suffix covers every ordinary list position after a successful prefix.
Witness: successful tails retain exact item data even with nullable errors; a bubbled tail
has an actual failed TaskAt at the list attachment. This is a pure execution certificate,
not a queue assumption, and does not require zero errors or an unexhausted suffix.
-/
theorem preparedResponseCovers_plain_stream (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef)) (count : Nat)
    (plain : Semantics.ItemFieldsInContext none fields) (initial : List ResponseValue)
    (initialErrors : Nat) (initialWork : Work)
    (prefixCompleted
      : GraphQL.Execution.completeValueList schema resolvers variables fuel itemType
          (fields.map Semantics.eraseField) (values.take count)
        = .ok (initial, initialErrors))
    (node : DeliveryNode) (nodePath : node.path = []) (state : NodeRef)
    (containers : Bool)
    : let items :=
        ((completeStreamItems schema resolvers variables fuel itemType fields
            (values.drop count) [] initial.length).run
          state).1
      PreparedResponseCovers
        (match GraphQL.Execution.completeValueList schema resolvers variables fuel
                itemType (fields.map Semantics.eraseField) values with
          | .error _ => .null
          | .ok (data, _) => .list data)
        { data := .list initial, errors := initialErrors }
        (.combine initialWork (.stream node items)) containers := by
  have splitList := SourceReconstruction.basicList_split_result schema resolvers variables
    fuel itemType (fields.map Semantics.eraseField) values count
  rw [prefixCompleted] at splitList
  have matched := (Semantics.completeStreamItems_itemContext schema resolvers variables fuel
    itemType fields (values.drop count) plain [] initial.length state).2.1
  cases tailCompleted
        : GraphQL.Execution.completeValueList schema resolvers variables fuel
            itemType (fields.map Semantics.eraseField) (values.drop count) with
  | error errors =>
      obtain ⟨failureErrors, cause, children, failed⟩ :=
        (SourceReconstruction.completeStreamItems_itemContext_failure_iff schema resolvers
          variables fuel itemType fields (values.drop count) plain [] initial.length
          state).mpr ⟨errors, tailCompleted⟩
      obtain ⟨ordinal, selected⟩ := List.mem_iff_getElem?.mp failed
      simp only [tailCompleted, GraphQL.Execution.Result.combine] at splitList
      dsimp only
      rw [splitList]
      intro path member
      obtain rfl : path = [] := by simpa [ResponsePositions.value] using member
      refine Or.inr ⟨.item [1] ordinal, [node.ref], none,
        .item node (.error (cause.getD failureErrors)), ?_, rfl, Or.inl ?_⟩
      · exact ⟨node, _, [], { result := .error failureErrors, cause }, children, rfl, selected, rfl, rfl⟩
      · simp [Payload.path, nodePath]
  | ok pair =>
      obtain ⟨entries, outcomes, sameData, _⟩ :=
        SourceReconstruction.basicList_success_streamResults schema resolvers variables fuel
          itemType fields (values.drop count) tailCompleted
      have supplied := matched.trans outcomes
      have tailPositions := sourceItemTasks_success_positions containers [1] none node
        initial.length 0 _ entries supplied
      simp only [nodePath, sameData] at tailPositions
      simp only [tailCompleted, GraphQL.Execution.Result.combine] at splitList
      dsimp only
      rw [splitList]
      intro path member
      apply Or.inl
      change path ∈ (if containers then [[]] else [])
        ++ ResponsePositions.items containers [] 0 (initial ++ pair.1) at member
      rw [positions_items_append, Nat.zero_add] at member
      have belongs : path ∈ ResponsePositions.value containers [] (.list initial)
          ++ ResponsePositions.items containers [] initial.length pair.1 := by
        simpa only [ResponsePositions.value, List.append_assoc] using member
      rcases List.mem_append.mp belongs with first | later
      · exact List.mem_append_left _ first
      · apply List.mem_append_right
        simp only [sourceTasks, List.flatMap_append]
        apply List.mem_append_right
        have retained := tailPositions later
        simpa [ResponsePositions.cursorAt, ResponsePositions.listCursors,
          nodePath] using retained

-----------------------------------------------------------------------------------------
-- The actual list-completion stream hook
-----------------------------------------------------------------------------------------

/-- Equal initial/reference data already covers every ordinary position.
Witness: initial positions are the first component of the prepared source inventory.
Neither retained work nor the response's counted errors are restricted.
-/
private theorem preparedResponseCovers_initial (response : Response) (work : Work)
    (containers : Bool)
    : PreparedResponseCovers response.data response work containers :=
  fun _ member => Or.inl (List.mem_append_left _ member)

/-- The executable stream hook satisfies prepared coverage for plain item selections.
Witness: valid arguments select an ordinary or counted stream boundary; item-context
completion identifies the prefix, and the stream-tail certificate handles success/failure.
This includes disabled streams, prefix failures, exhausted tails, and nullable item errors.
-/
theorem completeListValueWithStream_plain_coverage (schema : Schema)
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (itemType : TypeRef) (fields : List FieldDetails)
    (values : List (ResolverValue ObjectRef))
    (context : Option DeferUsage) (contextValid : Semantics.ContextWellFormed context)
    (deferMap : DeferMap) (plain : Semantics.ItemFieldsInContext context fields)
    (valid : ∀ field ∈ fields, ArgumentValidity.FieldArgumentsValid variables field)
    (allowStream : Bool) (state : NodeRef) (containers : Bool)
    : let completed :=
        ((completeListValueWithStream schema resolvers variables fuel itemType fields
            values [] (Semantics.contextRefs context) deferMap allowStream).run
          state).1
      ∃ data errors,
        completed.result = .ok (data, errors)
        ∧ PreparedResponseCovers
            (match GraphQL.Execution.completeValueList schema resolvers variables fuel
                    itemType (fields.map Semantics.eraseField) values with
              | .error _ => .null
              | .ok (data, _) => .list data)
            { data := data, errors := errors } completed.work containers := by
  obtain ⟨usage, usageOK⟩ : ∃ usage,
      (if allowStream then
        getStreamUsage variables (fields.head?.map FieldDetails.directives |>.getD [])
      else .ok none) = .ok usage := by
    cases allowStream
    · exact ⟨none, rfl⟩
    · exact ArgumentValidity.fields_getStreamUsage_ok variables fields valid
  dsimp only
  simp only [completeListValueWithStream, usageOK]
  cases usage with
  | none =>
      have matched := Semantics.completeListValue_itemContext context contextValid deferMap
        schema resolvers variables fuel itemType
        fields values plain [] 0 state
      simp only [Semantics.RunMatches, Semantics.CompletionMatches] at matched
      generalize completedEq : (completeListValue schema resolvers variables fuel itemType
        fields values [] 0 (Semantics.contextRefs context) deferMap).run state = pair at matched
      rcases pair with ⟨initial, final⟩
      rcases matched with ⟨finalEq, resultEq, _⟩
      dsimp only at finalEq resultEq
      subst final
      simp only [Semantics.run_bind, completedEq, StateT.run_pure, Semantics.id_pure_eq]
      rw [← resultEq]
      cases initialResult : initial.result with
      | error errors =>
          exact ⟨
            .null,
            errors,
            by simp [Completion.catchNull, initialResult],
            by
              simpa [Completion.catchNull, initialResult]
                using preparedResponseCovers_initial { data := .null, errors := errors }
                  .empty containers
          ⟩
      | ok pair =>
          exact ⟨
            .list pair.1,
            pair.2,
            by simp [Completion.catchNull, initialResult],
            by
              simpa [Completion.catchNull, initialResult]
                using preparedResponseCovers_initial
                  { data := .list pair.1, errors := pair.2 } initial.work containers
          ⟩
  | some usage =>
      have matched := Semantics.completeListValue_itemContext context contextValid deferMap
        schema resolvers variables fuel itemType
        fields (values.take usage.initialCount) plain [] 0 state
      simp only [Semantics.RunMatches, Semantics.CompletionMatches] at matched
      generalize completedEq : (completeListValue schema resolvers variables fuel itemType
        fields (values.take usage.initialCount) [] 0 (Semantics.contextRefs context)
        deferMap).run state = pair at matched
      rcases pair with ⟨initial, final⟩
      rcases matched with ⟨finalEq, resultEq, _⟩
      dsimp only at finalEq resultEq
      subst final
      simp only [Semantics.run_bind, completedEq]
      have splitList := SourceReconstruction.basicList_split_result schema resolvers
        variables fuel itemType (fields.map Semantics.eraseField) values usage.initialCount
      rw [← resultEq] at splitList
      cases initialResult : initial.result with
      | error errors =>
          cases tailResult : GraphQL.Execution.completeValueList schema resolvers variables
              fuel itemType (fields.map Semantics.eraseField) (values.drop usage.initialCount)
            <;> simp only [initialResult, tailResult, GraphQL.Execution.Result.combine] at splitList
          all_goals
            refine ⟨.null, errors, ?_, ?_⟩
            · simp [initialResult, Completion.catchNull]
            · simpa [initialResult, Completion.catchNull, splitList]
                using preparedResponseCovers_initial { data := .null, errors := errors }
                  .empty containers
      | ok pair =>
          by_cases exhausted : values.length < usage.initialCount
          · have takeAll : values.take usage.initialCount = values :=
              List.take_of_length_le (by omega)
            rw [initialResult, takeAll] at resultEq
            refine ⟨.list pair.1, pair.2, ?_, ?_⟩
            · simp [initialResult, exhausted, Completion.catchNull]
            · simpa [initialResult, exhausted, Completion.catchNull, ← resultEq]
                using preparedResponseCovers_initial
                  { data := .list pair.1, errors := pair.2 } initial.work containers
          · have countLength : pair.1.length = usage.initialCount := by
              have basicPrefix := initialResult ▸ resultEq
              have length := SourceReconstruction.basicList_length schema resolvers variables
                fuel itemType (fields.map Semantics.eraseField) (values.take usage.initialCount)
                pair.1 pair.2 basicPrefix.symm
              have within : usage.initialCount ≤ values.length := by omega
              simpa only [List.length_take, Nat.min_eq_left within] using length
            let streamFields := fields.map (fun field => { field with deferUsage := none })
            have streamPlain : Semantics.ItemFieldsInContext none streamFields := by
              intro field member
              change field ∈ fields.map (fun field => { field with deferUsage := none })
                at member
              obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
              exact ⟨rfl, (plain original originalMember).2⟩
            have erased : streamFields.map Semantics.eraseField
                = fields.map Semantics.eraseField := Semantics.eraseFields_clearDefer fields
            have basicPrefix : GraphQL.Execution.completeValueList schema resolvers variables
                fuel itemType (streamFields.map Semantics.eraseField)
                (values.take usage.initialCount) = .ok pair := by
              rw [erased]
              exact resultEq.symm.trans initialResult
            have covered := preparedResponseCovers_plain_stream schema resolvers variables
              fuel itemType streamFields values usage.initialCount streamPlain pair.1 pair.2
              initial.work basicPrefix { ref := state, path := [], label := usage.label }
              rfl (state + 1) containers
            dsimp only at covered
            rw [erased] at covered
            refine ⟨.list pair.1, pair.2, ?_, ?_⟩
            · simp [initialResult, exhausted, freshNodeRef, Completion.catchNull]
            · simpa [initialResult, exhausted, freshNodeRef, Completion.catchNull,
                streamFields, countLength]
                using covered

end GraphQL.IncrementalDelivery.Correctness
