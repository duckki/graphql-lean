import Proofs.GraphQL.IncrementalDelivery.Correctness
import Tests.GraphQL.IncrementalDelivery.Execution

/-! Exhausted stream boundaries remain real work, with no synthetic item publication. -/

namespace GraphQL.IncrementalDelivery.Tests.EmptyStreams

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.WorkScheduler

-----------------------------------------------------------------------------------------
-- Reaching the stream boundary
-----------------------------------------------------------------------------------------

/-- A fixture operation with an explicit initial count and an optional response alias. -/
def streamed (name : Name) (count : Nat) (alias : Option Name := none) : Operation :=
  { selectionSet := [field name [] [.stream (.boolean true) none (.int count)] alias] }

/-- Inspect generated work independently of any scheduler choice. -/
def prepared (operation : Operation) : Completion (List (Name × ResponseValue)) :=
  ((executeRootSelectionSetCore schema resolvers [] 12 "Query" (.object "Query" 0)
      operation.selectionSet).run
    0).1

/-- The exhausted stream's key and response path are still allocated normally. -/
def node (name : Name) : DeliveryNode := { key := 0, path := [.field name] }

-----------------------------------------------------------------------------------------
-- A boundary can complete without publishing an item
-----------------------------------------------------------------------------------------

/-- Fixture-only shape: empty work and one repeated stream descriptor, without tasks. -/
inductive BoundaryTree (node : DeliveryNode) : Work → Prop where
  | empty : BoundaryTree node .empty
  | combine {left right}
    : BoundaryTree node left → BoundaryTree node right
      → BoundaryTree node (.combine left right)
  | stream : BoundaryTree node (.stream node [])

/-- Navigation preserves the task-free shape and root context, by address induction. -/
theorem BoundaryTree.located {node work address current producer owners}
    (shape : BoundaryTree node work)
    (known : Located work address current producer owners)
    : BoundaryTree node current ∧ producer = none ∧ owners = [] := by
  replace known := StructuralEquivalence.located_of_current known
  induction known with
  | root => exact ⟨shape, rfl, rfl⟩
  | left _ ih =>
      cases ih.1 with
      | combine left _ => exact ⟨left, ih.2⟩
  | right _ ih =>
      cases ih.1 with
      | combine _ right => exact ⟨right, ih.2⟩
  | executionGroup _ ih => cases ih.1
  | item _ entry ih => cases ih.1; simp at entry

/-- No task exists at a zero-item boundary, by task provenance and the fixture shape. -/
theorem BoundaryTree.noTask {node work occurrence owners producer payload}
    (shape : BoundaryTree node work)
    : ¬TaskAt work occurrence owners producer payload := by
  intro known
  cases StructuralEquivalence.taskAt_of_current known with
  | executionGroup located => cases (shape.located located.toCurrent).1
  | item located entry => cases (shape.located located.toCurrent).1; simp at entry

/-- Every descriptor is the fixture's stream, by structural provenance. -/
theorem BoundaryTree.node {node work other kind parents birth}
    (shape : BoundaryTree node work) (known : NodeAt work other kind parents birth)
    : other = node := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located _ => cases (shape.located located.toCurrent).1
  | stream located => cases (shape.located located.toCurrent).1; rfl

/-- A zero-item boundary admits announcement, completion, and termination without values.
Witness: the existing queue contract; no extra admission case or silent-end task is used.
-/
theorem BoundaryTree.run {node work} (shape : BoundaryTree node work)
    (known : NodeAt work node .stream [] none)
    : AdmissibleRun work
        ⟨[], [node], [[.streamSuccess node, .workQueueTermination]]⟩ := by
  let matching : PublicationMatching := fun _ => .executionGroup []
  have initialized : Initializes work [] [node] := by
    refine ⟨⟨by simp, by simp, ?_⟩, by simp⟩
    intro stream member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨[], none, known, by simp [announcedKeys, pendingKeys],
      fun failure => failure.nonempty rfl, Or.inl rfl, by simp, Or.inl rfl⟩
  have initial : Explains work [] [node] [] matching [] :=
    ⟨initialized, by simp [FailureWitness], by simp⟩
  have allowed : EventAllowed work [node.key] matching [] [] (.streamSuccess node) := by
    refine ⟨⟨[], none, known⟩, ?_, fun failure => failure.nonempty rfl, ?_⟩
    · simp [Open, announcedKeys, completedKeys]
    · rintro occurrence owners ⟨producer, payload, task⟩ _
      exact False.elim (shape.noTask task)
  have explained := initial.append_event (by simpa [failedBefore] using allowed)
  refine ⟨[.streamSuccess node], matching, [], explained, ?_, ?_⟩
  · constructor
    · intro occurrence owners producer payload task
      exact False.elim (shape.noTask task)
    · intro other kind parents birth descriptor
      obtain rfl := shape.node descriptor
      exact Or.inl (by simp [completedKeys, eventCompleted])
  · exact .cons (tail := []) (by simp) (.separate _ (.separate _ .nil)) .nil

/-- The precise wire trace has a pending ID and its completion, but no item patch. -/
def wire (name : Name) (data : List ResponseValue) : ExecutionObservation :=
  .incremental
    {
      data := .object [(name, .list data)],
      pending := [{ id := "0", path := [.field name] }],
      hasNext := true
    }
    [{ hasNext := false, completed := [{ id := "0" }] }]

/-- The empty list reaches the public query relation with a complete zero-item lifecycle.
Witness: generated work, the unchanged queue contract, and actual response realization.
-/
theorem empty_outcome
    : queryOutcome schema resolvers [] (streamed "empty" 0) 12
        (.object "Query" 0) (wire "empty" []) := by
  apply queryObservation_iff_workHistory.mpr
  rw [ite_eq_left (by decide)]
  change WorkObservation (selectionSetResultToResponse (prepared (streamed "empty" 0)).result)
    (prepared (streamed "empty" 0)).work true (wire "empty" [])
  have response : selectionSetResultToResponse (prepared (streamed "empty" 0)).result =
      { data := .object [("empty", .list [])] } := by cbv
  rw [response]
  have workEq : (prepared (streamed "empty" 0)).work =
      .combine (.combine (.combine .empty (.stream (node "empty") [])) .empty) .empty := by cbv
  have shape : BoundaryTree (node "empty") (prepared (streamed "empty" 0)).work := by
    rw [workEq]
    exact .combine (.combine (.combine .empty .stream) .empty) .empty
  have known : NodeAt (prepared (streamed "empty" 0)).work (node "empty") .stream [] none := by
    rw [workEq]
    exact .stream (.right (.left (.left .root)))
  exact .incremental [] [node "empty"]
    [[[.streamSuccess (node "empty"), .workQueueTermination]]]
    (by rw [workEq]; decide)
    (by simp)
    (Or.inr (shape.run known))
    (fun _ => shape.run known)

/-- Exact positive counts also retain the stream after all initial data is returned.
Witness: the same task-free history, now following a three-item initial prefix.
-/
theorem exact_outcome
    : queryOutcome schema resolvers [] (streamed "values" 3) 12
        (.object "Query" 0) (wire "values" [.scalar "x", .null, .scalar "z"]) := by
  apply queryObservation_iff_workHistory.mpr
  rw [ite_eq_left (by decide)]
  change WorkObservation (selectionSetResultToResponse (prepared (streamed "values" 3)).result)
    (prepared (streamed "values" 3)).work true
    (wire "values" [.scalar "x", .null, .scalar "z"])
  have response : selectionSetResultToResponse (prepared (streamed "values" 3)).result =
      { data := .object [("values", .list [.scalar "x", .null, .scalar "z"])] } := by cbv
  rw [response]
  have workEq : (prepared (streamed "values" 3)).work =
      .combine (.combine (.combine
        (.combine .empty (.combine .empty (.combine .empty .empty)))
        (.stream (node "values") [])) .empty) .empty := by cbv
  have shape : BoundaryTree (node "values") (prepared (streamed "values" 3)).work := by
    rw [workEq]
    exact .combine (.combine (.combine
      (.combine .empty (.combine .empty (.combine .empty .empty))) .stream) .empty) .empty
  have known : NodeAt (prepared (streamed "values" 3)).work (node "values") .stream [] none := by
    rw [workEq]
    exact .stream (.right (.left (.left .root)))
  exact .incremental [] [node "values"]
    [[[.streamSuccess (node "values"), .workQueueTermination]]]
    (by rw [workEq]; decide)
    (by simp)
    (Or.inr (shape.run known))
    (fun _ => shape.run known)

-----------------------------------------------------------------------------------------
-- A stream with no items is not an empty collection of streams
-----------------------------------------------------------------------------------------

/-- Any retained boundary excludes an ordinary query outcome, regardless of scheduler.
Witness: ordinary work observations require zero work, not merely absence of item tasks.
-/
theorem boundary_no_single (name : Name) (count : Nat)
    (nonempty : (prepared (streamed name count)).work.size ≠ 0) (response : Response)
    : ¬queryOutcome schema resolvers [] (streamed name count) 12
        (.object "Query" 0) (.single response) := by
  intro observed
  have witness := queryObservation_workHistory observed
  rw [ite_eq_left (by rfl)] at witness
  change WorkObservation _ (prepared (streamed name count)).work true
    (.single response) at witness
  cases witness with
  | single empty => exact nonempty empty

/-- An empty list at initialCount zero must retain incremental response form.
Witness: its positive-size stream boundary and the ordinary-outcome exclusion.
-/
theorem empty_no_single (response : Response)
    : ¬queryOutcome schema resolvers [] (streamed "empty" 0) 12
        (.object "Query" 0) (.single response) :=
  boundary_no_single "empty" 0 (by cbv) response

/-- Exact positive counts also exclude ordinary outcomes after creating a stream.
Witness: the same branch exclusion for the fully consumed initial prefix.
-/
theorem exact_no_single (response : Response)
    : ¬queryOutcome schema resolvers [] (streamed "values" 3) 12
        (.object "Query" 0) (.single response) :=
  boundary_no_single "values" 3 (by cbv) response

/-- Even an empty notice frontier cannot switch nonempty work to an ordinary response.
Witness: executable root packaging branches on work before consulting the supplied queue.
-/
example (response ordinary : Response)
    : executionFromWork unavailable response (.stream (node "empty") [])
      ≠ .single ordinary := by
  simp [executionFromWork, Work.size, yieldIncrementalResults, unavailable]

-----------------------------------------------------------------------------------------
-- Boundary scope, nesting, and errors
-----------------------------------------------------------------------------------------

/-- Bounded fixture inspection collects stream descriptors and item counts, including
streams in future child work. It is not part of execution or scheduler admission.
-/
def boundaries : Nat → Work → List (DeliveryNode × Nat)
  | 0, _ => []
  | fuel + 1, work =>
      match work with
      | .empty => []
      | .combine left right => boundaries fuel left ++ boundaries fuel right
      | .executionGroup _ _ _ children => boundaries fuel children
      | .stream stream items =>
          (stream, items.length) :: items.flatMap (fun item => boundaries fuel item.2)

/-- A nonempty tail still streams its remaining item. Witness: finite evaluation. -/
example : boundaries 20 (prepared (streamed "values" 2)).work = [(node "values", 1)] := by
  cbv

/-- Exhaustion before initialCount still returns an ordinary response, without a queue.
Witness: the public entry point with an intentionally unavailable scheduler.
-/
example
    : executeQueryWithFuel unavailable schema resolvers [] (streamed "values" 4) 12
        (.object "Query" 0)
      = .single
          { data := .object [("values", .list [.scalar "x", .null, .scalar "z"])] } := by
  cbv

/-- An empty list does not reach a positive count. Witness: zero generated work. -/
example : (prepared (streamed "empty" 1)).work.size = 0 := by cbv

/-- A disabled directive never creates a boundary, even at zero. Witness: no work. -/
example
    : (prepared
        {
          selectionSet :=
            [field "empty" [] [.stream (.boolean false)]]
        }).work.size
      = 0 := by cbv

/-- Skipped selections likewise do not allocate stream boundaries. Witness: no work. -/
example
    : (prepared
        {
          selectionSet :=
            [field "empty" [] [.stream, .skip (.boolean true)]]
        }).work.size
      = 0 := by cbv

/-- Initial-prefix failure nulls the list without creating a stream under it.
Witness: the non-null item failure precedes boundary allocation.
-/
example
    : (prepared (streamed "strict" 3)).result = .ok ([("strict", .null)], 1)
      ∧ (prepared (streamed "strict" 3)).work.size = 0 := by cbv

/-- Labels and aliases survive an empty boundary. Witness: generated descriptor metadata.
-/
example
    : boundaries 20
        (prepared
          {
            selectionSet :=
              [field "empty" [] [.stream (.boolean true) (some (.string "E"))]
                (some "alias")]
          }).work
      = [({ key := 0, path := [.field "alias"], label := some (.string "E") }, 0)] := by
  cbv

/-- Inner list wrappers remain synchronous at an exact outer boundary.
Witness: there is only one stream, despite an inner list also having length two.
-/
example : boundaries 20 (prepared (streamed "matrix" 2)).work = [(node "matrix", 0)] := by
  cbv

/-- Empty boundaries retain their full path inside an immediate object.
Witness: ordinary composite completion preserves the stream descriptor.
-/
example
    : boundaries 20
        (prepared
          {
            selectionSet :=
              [field "user" [(field "values" [] [.stream (.boolean true) none (.int 3)])]]
          }).work
      = [({ key := 0, path := [.field "user", .field "values"] }, 0)] := by cbv

/-- Deferred producers retain empty child streams. Witness: the child has its own key.
-/
example
    : boundaries 20
        (prepared
          {
            selectionSet :=
              [defer (streamed "values" 3).selectionSet]
          }).work
      = [({ key := 1, path := [.field "values"] }, 0)] := by cbv

/-- Two streamed objects each produce an empty child stream with a fresh key and index.
Witness: finite generated work, including future item children.
-/
example
    : boundaries 20
        (prepared
          {
            selectionSet :=
              [field "users" (streamed "values" 3).selectionSet [.stream]]
          }).work
      = [
        ({ key := 0, path := [.field "users"] }, 2),
        ({ key := 1, path := [.field "users", .index 0, .field "values"] }, 0),
        ({ key := 2, path := [.field "users", .index 1, .field "values"] }, 0)
      ] := by cbv

/-- Independent empty and nonempty streams consume distinct keys.
Witness: the empty stream is not erased from work allocation.
-/
example
    : boundaries 20
        (prepared
          {
            selectionSet :=
              (streamed "empty" 0).selectionSet ++ (streamed "values" 2).selectionSet
          }).work
      = [(node "empty", 0), ({ key := 1, path := [.field "values"] }, 1)] := by cbv

/-- Overlapping defer owners still share a single empty child stream.
Witness: field partitioning precedes the stream-boundary allocation.
-/
example
    : boundaries 20
        (prepared
          {
            selectionSet :=
              [
                defer (streamed "values" 3).selectionSet,
                defer (streamed "values" 3).selectionSet
              ]
          }).work
      = [({ key := 2, path := [.field "values"] }, 0)] := by cbv

/-- The new exact-count trace satisfies the existing lifecycle theorem.
Witness: the public theorem applied to its actual query outcome.
-/
example : (wire "values" [.scalar "x", .null, .scalar "z"]).deliveryComplete = true :=
  deliveryLifecycleValid_holds schema (streamed "values" 3) resolvers [] 12
    (.object "Query" 0) _ exact_outcome

/-- Empty-stream completion adds no data or error contribution.
Witness: reconstruction of the exact concrete wire trace.
-/
example
    : mergeExecutionObservation (wire "values" [.scalar "x", .null, .scalar "z"])
      = some
          { data := .object [("values", .list [.scalar "x", .null, .scalar "z"])] } := by
  cbv

end GraphQL.IncrementalDelivery.Tests.EmptyStreams
