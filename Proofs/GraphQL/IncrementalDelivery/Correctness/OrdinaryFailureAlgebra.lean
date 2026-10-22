import Proofs.GraphQL.IncrementalDelivery.Correctness.FailureCoverageAlgebra
import Proofs.GraphQL.IncrementalDelivery.Correctness.InitialFailureAlgebra

/-! Ordinary failures reflected into initial results or retained descendant tasks. -/

namespace GraphQL.IncrementalDelivery.Correctness.OrdinaryFailures
open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Pure execution witnesses, independent of notices and schedules
-----------------------------------------------------------------------------------------

/-- The retained `work` contains a failed task at or below the response attachment `path`.
This is structural evidence about computed outcomes, not a wire failure-scope assumption.
-/
def FailedBelow (path : ResponsePath) (work : Work) : Prop :=
  ∃ occurrence owners producer payload,
    TaskAt work occurrence owners producer payload
    ∧ payload.failure.isSome = true
    ∧ path.IsPrefix payload.path

/-- An ordinary bubble either already bubbles initially or has retained failure evidence.
The counts may differ; `path` bounds the descendant attachment of that evidence.
-/
def BubblesExplained (path : ResponsePath) (ordinary : Result α) (initial : Completion α)
    : Prop :=
  ∀ errors,
    ordinary = .error errors
    → (∃ count, initial.result = .error count) ∨ FailedBelow path initial.work

/-- Ordinary null additionally requires an initial null/bubble or a retained failure.
This extra implication is needed when a non-null wrapper turns ordinary null into a
bubble, while the initial value still exposes a partial object or list.
-/
def ValueFailuresExplained (path : ResponsePath) (ordinary : Result ResponseValue)
    (initial : Completion ResponseValue)
    : Prop :=
  BubblesExplained path ordinary initial
  ∧ ∀ errors,
      ordinary = .ok (.null, errors)
      → (∃ count, initial.result = .error count)
        ∨ (∃ count, initial.result = .ok (.null, count))
        ∨ FailedBelow path initial.work

/-- Some retained stream entry fails itself or contains failed work below `path`.
The list is the actual short-circuit stream outcome, not the full resolver input list.
-/
def ItemsHaveFailure (path : ResponsePath)
    (items : List (TaskOutcome ResponseValue × Work))
    : Prop :=
  ∃ result children,
    (result, children) ∈ items
    ∧ ((∃ errors, result.result = .error errors) ∨ FailedBelow path children)

/-- A containing response attachment also bounds the same failed task.
Witness: transitivity of attachment prefixes; the payload and structural task stay fixed.
-/
theorem FailedBelow.at_ancestor {path ancestor work}
    (failed : FailedBelow path work) (ancestorPrefix : ancestor.IsPrefix path)
    : FailedBelow ancestor work := by
  obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := failed
  exact ⟨occurrence, owners, producer, payload, known, fails, ancestorPrefix.trans below⟩

/-- A retained failure remains in the left component of combined work.
Witness: payload-preserving task embedding at the left structural edge.
-/
theorem FailedBelow.combine_left {path work} (failed : FailedBelow path work)
    (right : Work)
    : FailedBelow path (.combine work right) := by
  obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := failed
  obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_combine_left known right
  exact ⟨occurrence, owners, producer, payload, embedded, fails, below⟩

/-- A retained failure remains in the right component of combined work.
Witness: payload-preserving task embedding at the right structural edge.
-/
theorem FailedBelow.combine_right {path work} (failed : FailedBelow path work)
    (left : Work)
    : FailedBelow path (.combine left work) := by
  obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := failed
  obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_combine_right known left
  exact ⟨occurrence, owners, producer, payload, embedded, fails, below⟩

/-- A deferred execution group's own bubbling outcome is retained failure evidence.
Witness: the root execution-group task, with exactly its response attachment.
-/
theorem FailedBelow.executionGroup_error (groups : List DeferredFragment)
    (path : ResponsePath) (errors : Nat) (children : Work) {cause : Option Nat}
    : FailedBelow path
        (.executionGroup groups path { result := .error errors, cause } children) := by
  exact ⟨
    _,
    _,
    _,
    .object path (.error (cause.getD errors)),
    (StructuralEquivalence.TaskAt.executionGroup .root).toCurrent,
    rfl,
    ⟨[], by simp [Payload.path]⟩
  ⟩

/-- Child failure evidence survives retention beneath an execution-group task.
Witness: structural child embedding; the child's attachment is unchanged.
-/
theorem FailedBelow.executionGroup_child {path children}
    (failed : FailedBelow path children) (groups : List DeferredFragment)
    (attachment : ResponsePath) (result : TaskOutcome (List (Name × ResponseValue)))
    : FailedBelow path (.executionGroup groups attachment result children) := by
  obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := failed
  obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_located known
    (StructuralEquivalence.Located.executionGroup .root).toCurrent
  exact ⟨occurrence, owners, producer, payload, embedded, fails, below⟩

/-- Failure in an actual retained entry supplies a failed task in its stream work.
Witness: membership gives the structural item index; failed entries are item tasks, and
child failures embed at that same index. Both use the real stream's list attachment.
-/
theorem ItemsHaveFailure.in_stream {path items} (failed : ItemsHaveFailure path items)
    (node : DeliveryNode) (attachment : path.IsPrefix node.path)
    : FailedBelow path (.stream node items) := by
  obtain ⟨result, children, member, fails⟩ := failed
  obtain ⟨index, entry⟩ := List.mem_iff_getElem?.mp member
  rcases fails with itemFailed | childFailed
  · obtain ⟨errors, failed⟩ := itemFailed
    exact ⟨_, _, _, .item node result.deliveryResult,
      (StructuralEquivalence.TaskAt.item .root entry).toCurrent,
      by simp [Payload.failure, TaskOutcome.deliveryResult, failed], attachment⟩
  · obtain ⟨occurrence, owners, producer, payload, known, fails, below⟩ := childFailed
    obtain ⟨occurrence, owners, producer, embedded⟩ := TaskAt.in_located known
      (StructuralEquivalence.Located.item .root entry).toCurrent
    exact ⟨occurrence, owners, producer, payload, embedded, fails, below⟩

/-- Appending an earlier retained stream entry cannot lose a later failure witness.
Witness: list membership; no relation between the earlier value and its errors is needed.
-/
theorem ItemsHaveFailure.cons {path items} (failed : ItemsHaveFailure path items)
    (head : TaskOutcome ResponseValue × Work)
    : ItemsHaveFailure path (head :: items) := by
  obtain ⟨result, children, member, fails⟩ := failed
  exact ⟨result, children, List.mem_cons_of_mem head member, fails⟩

/-- Identical ordinary and initial results explain bubbles without retained work.
Witness: reuse the initial result; its work is unrestricted.
-/
theorem BubblesExplained.refl (path : ResponsePath) (initial : Completion α)
    : BubblesExplained path initial.result initial :=
  fun errors failed => Or.inl ⟨errors, failed⟩

/-- A successful ordinary result has no bubbling obligation to explain.
Witness: the ordinary success/error constructors are disjoint.
-/
theorem BubblesExplained.ok (path : ResponsePath) (data : α) (errors : Nat)
    (initial : Completion α)
    : BubblesExplained path (.ok (data, errors)) initial := by
  intro count failed
  cases failed

/-- Identical value results explain both ordinary bubbles and ordinary nulls.
Witness: constructor equality; retained child work needs no restriction.
-/
theorem ValueFailuresExplained.refl (path : ResponsePath)
    (initial : Completion ResponseValue)
    : ValueFailuresExplained path initial.result initial :=
  ⟨
    BubblesExplained.refl path initial,
    fun errors isNull => Or.inr (Or.inl ⟨errors, isNull⟩)
  ⟩

/-- Exact result equality explains ordinary bubbling; retained work is unrestricted.
Witness: transport to the initial result and use the reflexive comparison.
-/
theorem BubblesExplained.of_result_eq (path : ResponsePath) (ordinary : Result α)
    (initial : Completion α) (same : initial.result = ordinary)
    : BubblesExplained path ordinary initial := by
  rw [← same]
  exact BubblesExplained.refl path initial

/-- Exact result equality explains ordinary nulls as well as bubbling.
Witness: result transport and the reflexive value comparison.
-/
theorem ValueFailuresExplained.of_result_eq (path : ResponsePath)
    (ordinary : Result ResponseValue) (initial : Completion ResponseValue)
    (same : initial.result = ordinary)
    : ValueFailuresExplained path ordinary initial := by
  rw [← same]
  exact ValueFailuresExplained.refl path initial

/-- A non-null ordinary success imposes no ordinary-failure obligation.
Witness: success cannot bubble and the ordinary value cannot equal null.
-/
theorem ValueFailuresExplained.nonNullOk (path : ResponsePath) (data : ResponseValue)
    (errors : Nat) (notNull : data ≠ .null) (initial : Completion ResponseValue)
    : ValueFailuresExplained path (.ok (data, errors)) initial := by
  refine ⟨BubblesExplained.ok path data errors initial, ?_⟩
  intro count isNull
  exact False.elim (notNull (congrArg Prod.fst (Except.ok.inj isNull)))

-----------------------------------------------------------------------------------------
-- Completion wrappers and accumulation preserve the same witnesses
-----------------------------------------------------------------------------------------

/-- Combining completed results preserves each ordinary bubbling explanation.
Witness: a bubbling combined initial result suffices directly. Otherwise both initial
parts are successful, their child work is retained, and the failed ordinary part supplies
an embedded descendant task. No successful-data equivalence is assumed.
-/
theorem BubblesExplained.combine (combine : α → β → γ)
    {path ordinaryLeft ordinaryRight} {initialLeft : Completion α}
    {initialRight : Completion β}
    (left : BubblesExplained path ordinaryLeft initialLeft)
    (right : BubblesExplained path ordinaryRight initialRight)
    : BubblesExplained path (Result.combine combine ordinaryLeft ordinaryRight)
        (Completion.combine combine initialLeft initialRight) := by
  intro errors failed
  cases first : initialLeft.result with
  | error count =>
      cases last : initialRight.result with
      | error other =>
          exact Or.inl
            ⟨
              count + other,
              by simp [Completion.combine, Completion.error,
                Result.combine, first, last]
            ⟩
      | ok pair =>
          exact Or.inl
            ⟨
              count + pair.2,
              by simp [Completion.combine, Completion.error,
                Result.combine, first, last]
            ⟩
  | ok head =>
      cases last : initialRight.result with
      | error count =>
          exact Or.inl
            ⟨
              head.2 + count,
              by simp [Completion.combine, Completion.error,
                Result.combine, first, last]
            ⟩
      | ok tail =>
          have fromLeft (count) (bubbles : ordinaryLeft = .error count) := left count bubbles
          have fromRight (count) (bubbles : ordinaryRight = .error count) := right count bubbles
          cases ordinaryHead : ordinaryLeft with
          | error count =>
              rcases fromLeft count ordinaryHead with already | retained
              · obtain ⟨count, impossible⟩ := already
                simp [first] at impossible
              · exact Or.inr (by
                  simpa [Completion.combine, Result.combine, first, last] using
                    retained.combine_left initialRight.work)
          | ok value =>
              cases ordinaryTail : ordinaryRight with
              | error count =>
                  rcases fromRight count ordinaryTail with already | retained
                  · obtain ⟨count, impossible⟩ := already
                    simp [last] at impossible
                  · exact Or.inr (by
                      simpa [Completion.combine, Result.combine, first, last] using
                        retained.combine_right initialLeft.work)
              | ok value => simp [Result.combine, ordinaryHead, ordinaryTail] at failed

/-- Mapping a completed result retains its explanation whenever the initial result does
not already bubble. Witness: mapping preserves successful child work and ordinary errors.
-/
theorem BubblesExplained.map (transform : α → β) {path ordinary}
    {initial : Completion α} (explained : BubblesExplained path ordinary initial)
    : BubblesExplained path
        (match ordinary with
          | .error errors => .error errors
          | .ok (data, errors) => .ok (transform data, errors))
        (initial.map transform) := by
  intro errors failed
  cases ordinaryResult : ordinary with
  | ok value => simp [ordinaryResult] at failed
  | error count =>
      rcases explained count ordinaryResult with already | retained
      · obtain ⟨count, initialFailed⟩ := already
        exact Or.inl ⟨count, by simp [Completion.map, Completion.error, initialFailed]⟩
      · cases initialResult : initial.result with
        | error count =>
            exact Or.inl
              ⟨count, by simp [Completion.map, Completion.error, initialResult]⟩
        | ok value =>
            exact Or.inr (by simpa [Completion.map, initialResult] using retained)

/-- Nullable catching changes an explained ordinary bubble into an explained null.
Witness: an initial bubble is caught too; otherwise successful child work keeps the
descendant failure. Non-null wrapped values cannot create ordinary null spuriously.
-/
theorem BubblesExplained.catchNull (wrap : α → ResponseValue)
    (notNull : ∀ data, wrap data ≠ .null) {path ordinary} {initial : Completion α}
    (explained : BubblesExplained path ordinary initial)
    : ValueFailuresExplained path (GraphQL.Execution.catchBubbleAsNull wrap ordinary)
        (initial.catchNull wrap) := by
  constructor
  · intro errors failed
    cases ordinary <;> simp [GraphQL.Execution.catchBubbleAsNull] at failed
  · intro errors isNull
    cases ordinaryResult : ordinary with
    | error count =>
        rcases explained count ordinaryResult with already | retained
        · obtain ⟨count, initialFailed⟩ := already
          exact Or.inr (Or.inl ⟨count, by simp [Completion.catchNull, initialFailed]⟩)
        · cases initialResult : initial.result with
          | error count =>
              exact Or.inr (Or.inl ⟨count, by simp [Completion.catchNull, initialResult]⟩)
          | ok value =>
              exact Or.inr
                (Or.inr (by simpa [Completion.catchNull, initialResult] using retained))
    | ok value =>
        obtain ⟨data, count⟩ := value
        simp only [ordinaryResult, GraphQL.Execution.catchBubbleAsNull, Except.ok.injEq,
          Prod.mk.injEq] at isNull
        exact False.elim (notNull data isNull.1)

/-- Changing to a containing attachment preserves a bubbling explanation.
Witness: an initial bubble is unchanged; the failed task's path bound composes.
-/
theorem BubblesExplained.at_ancestor {path ancestor ordinary} {initial : Completion α}
    (explained : BubblesExplained path ordinary initial)
    (ancestorPrefix : ancestor.IsPrefix path)
    : BubblesExplained ancestor ordinary initial := by
  intro errors failed
  rcases explained errors failed with initialFailed | retained
  · exact Or.inl initialFailed
  · exact Or.inr (retained.at_ancestor ancestorPrefix)

/-- Extra retained work cannot invalidate an existing bubbling explanation.
Witness: initial results stay fixed and the failed task embeds in the left component.
-/
theorem BubblesExplained.retain_right {path ordinary} {initial : Completion α}
    (explained : BubblesExplained path ordinary initial) (right : Work)
    : BubblesExplained path ordinary
        { initial with work := .combine initial.work right } := by
  intro errors failed
  rcases explained errors failed with initialFailed | retained
  · exact Or.inl initialFailed
  · exact Or.inr (retained.combine_left right)

/-- Non-null wrapping preserves a bubble or descendant failure explanation.
Witness: a null initial value bubbles under the wrapper; other successful initial values
retain child work. The ordinary wrapper cannot return null.
-/
theorem ValueFailuresExplained.nonNull {path ordinary}
    {initial : Completion ResponseValue}
    (explained : ValueFailuresExplained path ordinary initial)
    : ValueFailuresExplained path (GraphQL.Execution.nonNullCompletion ordinary)
        initial.nonNull := by
  have lift
      (evidence : (∃ count, initial.result = .error count)
        ∨ (∃ count, initial.result = .ok (.null, count)) ∨ FailedBelow path initial.work)
      : (∃ count, initial.nonNull.result = .error count)
        ∨ FailedBelow path initial.nonNull.work := by
    cases outcome : initial.result with
    | error count =>
        exact Or.inl
          ⟨
            count,
            by simp [Completion.nonNull, Completion.error,
              GraphQL.Execution.nonNullCompletion, outcome]
          ⟩
    | ok pair =>
        obtain ⟨data, count⟩ := pair
        cases data with
        | null =>
            cases count with
            | zero =>
                exact Or.inl
                  ⟨
                    1,
                    by simp [Completion.nonNull, Completion.error,
                      GraphQL.Execution.nonNullCompletion, outcome]
                  ⟩
            | succ count =>
                exact Or.inl
                  ⟨
                    count + 1,
                    by simp [Completion.nonNull,
                      Completion.error, GraphQL.Execution.nonNullCompletion, outcome]
                  ⟩
        | scalar scalar | object fields | list values =>
            rcases evidence with failed | isNull | retained
            · obtain ⟨errors, impossible⟩ := failed
              simp [outcome] at impossible
            · obtain ⟨errors, impossible⟩ := isNull
              simp [outcome] at impossible
            · exact Or.inr (by simpa [Completion.nonNull,
                GraphQL.Execution.nonNullCompletion, outcome] using retained)
  constructor
  · intro errors failed
    cases ordinaryResult : ordinary with
    | error count =>
        rcases explained.1 count ordinaryResult with initialFailed | retained
        · exact lift (Or.inl initialFailed)
        · exact lift (Or.inr (Or.inr retained))
    | ok pair =>
        obtain ⟨data, count⟩ := pair
        cases data with
        | null => exact lift (explained.2 count ordinaryResult)
        | scalar scalar | object fields | list values =>
            simp [GraphQL.Execution.nonNullCompletion, ordinaryResult] at failed
  · intro errors isNull
    cases ordinary with
    | error count => simp [GraphQL.Execution.nonNullCompletion] at isNull
    | ok pair =>
        obtain ⟨data, count⟩ := pair
        cases data <;> cases count <;>
          simp [GraphQL.Execution.nonNullCompletion] at isNull

/-- Field-result permutation preserves ordinary bubbling explanations.
Witness: equivalent field results have the same success/error constructor; successful
data permutations and nonzero nullable errors need no additional hypothesis.
-/
theorem BubblesExplained.of_fieldEquivalent {path ordinary other}
    {initial : Completion (List (Name × ResponseValue))}
    (equivalent : TypedResponse.FieldResultsEquivalent ordinary other)
    (explained : BubblesExplained path other initial)
    : BubblesExplained path ordinary initial := by
  intro errors failed
  rw [failed] at equivalent
  cases other with
  | error count => exact explained count rfl
  | ok pair => simp [TypedResponse.FieldResultsEquivalent] at equivalent

end GraphQL.IncrementalDelivery.Correctness.OrdinaryFailures
