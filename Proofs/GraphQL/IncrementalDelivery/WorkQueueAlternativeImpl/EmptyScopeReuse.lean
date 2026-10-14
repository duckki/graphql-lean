import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.ReaderLifecycle

/-! Empty-only sequential item-scope reuse at completed-item boundaries. Inputs retain
the actual Lean stream occurrence, value/errors and lowered child work. This allocator
simulation neither evaluates resolvers nor proves native absence of late field callbacks.
The latter completion barrier and finished-scope immutability remain native obligations.
-/

namespace GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement

-----------------------------------------------------------------------------------------
-- Empty-scope fast-path guard, optional work result, and allocation observer
-----------------------------------------------------------------------------------------

structure CompletedItemScope where
  item : ReferenceWorkQueue.StreamItem
  aborted : Bool := false
deriving Repr

/-- SequentialStreamItemExecutor.buildStreamItemResult's exact inventory/abort guard.
This is not a guard proving that native field callbacks have all settled.
-/
def CompletedItemScope.canReuse (scope : CompletedItemScope) : Bool :=
  !scope.aborted
  && scope.item.value.errors == 0
  && scope.item.work.groups.isEmpty
  && scope.item.work.tasks.isEmpty
  && scope.item.work.streams.isEmpty

/-- An immutable observer of a built result. A nonempty/failed scope finishes, so its
work is observed as retained; the fast path omits work rather than exposing empty arrays.
-/
structure ScopedItemResult where
  occurrence : WorkQueueSemantics.Occurrence
  value : Execution.StreamItemValue
  work : Option ReferenceWorkQueue.Work
deriving Repr

def ScopedItemResult.project (result : ScopedItemResult)
    : ReferenceWorkQueue.StreamItem :=
  ⟨result.occurrence, result.value, result.work.getD {}⟩

def CompletedItemScope.buildResult (scope : CompletedItemScope) : ScopedItemResult :=
  ⟨
    scope.item.occurrence,
    scope.item.value,
    if scope.canReuse then none else some scope.item.work
  ⟩

/-- Observer of sequential source-local allocations, not a ported pool or runtime layout. -/
structure ScopeReuseRun where
  reusable : Bool
  results : List ScopedItemResult
  allocations : Nat
deriving Repr

/-- Completion ends reuse on errors/child work/abort. The next item then allocates afresh;
no finished scope is reset. Each early overlapping item instead starts with reusable=false.
-/
def runSequentialScopes (reusable : Bool) : List CompletedItemScope → ScopeReuseRun
  | [] => ⟨reusable, [], 0⟩
  | scope :: rest =>
      let last := runSequentialScopes scope.canReuse rest
      ⟨
        last.reusable,
        scope.buildResult :: last.results,
        (if reusable then 0 else 1) + last.allocations
      ⟩

/-- Joint same-input result refinement and allocator bound, with no assumed output equality.
All native invocation timing, callback barriers and mutable-container correspondence remain
outside this finite completed-item observer.
-/
def EmptySequentialScopeOptimization : Prop :=
  ∀ scopes : List CompletedItemScope,
    let observed := runSequentialScopes false scopes
    observed.results.map ScopedItemResult.project = scopes.map CompletedItemScope.item
    ∧ observed.allocations ≤ scopes.length

-----------------------------------------------------------------------------------------
-- Guard-derived emptiness and mixed-result same-run projection
-----------------------------------------------------------------------------------------

theorem CompletedItemScope.canReuse_inventory (scope : CompletedItemScope)
    (eligible : scope.canReuse = true)
    : scope.aborted = false ∧ scope.item.value.errors = 0 ∧ scope.item.work = {} := by
  rcases scope with ⟨⟨occurrence, value, ⟨groups, tasks, streams⟩⟩, aborted⟩
  simp [CompletedItemScope.canReuse] at eligible
  obtain ⟨⟨⟨⟨healthy, errors⟩, groupsEmpty⟩, tasksEmpty⟩, streamsEmpty⟩ := eligible
  exact ⟨healthy, errors, by simp [groupsEmpty, tasksEmpty, streamsEmpty]⟩

/-- Errors, occurrences and all child-work identities survive the optional-work optimization. -/
theorem CompletedItemScope.buildResult_project (scope : CompletedItemScope)
    : scope.buildResult.project = scope.item := by
  unfold CompletedItemScope.buildResult ScopedItemResult.project
  cases eligible : scope.canReuse with
  | false => simp
  | true =>
      have empty := (scope.canReuse_inventory eligible).2.2
      simp only [↓reduceIte, Option.getD_none]
      rw [← empty]

theorem runSequentialScopes_projection (reusable : Bool)
    (scopes : List CompletedItemScope)
    : (runSequentialScopes reusable scopes).results.map ScopedItemResult.project
      = scopes.map CompletedItemScope.item := by
  induction scopes generalizing reusable with
  | nil => rfl
  | cons scope rest ih =>
      simp [runSequentialScopes, scope.buildResult_project, ih]

theorem runSequentialScopes_allocations_le (reusable : Bool)
    (scopes : List CompletedItemScope)
    : (runSequentialScopes reusable scopes).allocations ≤ scopes.length := by
  induction scopes generalizing reusable with
  | nil => simp [runSequentialScopes]
  | cons scope rest ih =>
      have tail := ih scope.canReuse
      cases reusable <;>
        simp only [runSequentialScopes, List.length_cons, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem EmptySequentialScopeOptimization_holds : EmptySequentialScopeOptimization := by
  intro scopes
  exact ⟨runSequentialScopes_projection false scopes, runSequentialScopes_allocations_le false scopes⟩

/-- The derived projection is the actual reader's same batch, so queue accounting,
ownership effects, response mapping and finish behavior are unchanged together.
-/
theorem runSequentialScopes_reader (cursor : ResponseStreamCursor)
    (stream : Execution.DeliveryNode) (scopes : List CompletedItemScope)
    : cursor.handleBatch
        [.streamItems stream
          ((runSequentialScopes false scopes).results.map ScopedItemResult.project)]
      = cursor.handleBatch
          [.streamItems stream (scopes.map CompletedItemScope.item)] := by
  rw [runSequentialScopes_projection]

/-- A nonempty run of eligible empty scopes allocates exactly once; errors/nonempty scopes
remain handled by the mixed-result theorem, not by weakening this eligibility condition.
-/
theorem runSequentialScopes_empty_allocations (reusable : Bool)
    (scopes : List CompletedItemScope)
    (eligible : ∀ scope ∈ scopes, scope.canReuse = true)
    : (runSequentialScopes reusable scopes).allocations
      = if scopes.isEmpty || reusable then 0 else 1 := by
  induction scopes generalizing reusable with
  | nil => simp [runSequentialScopes]
  | cons scope rest ih =>
      have head := eligible scope (by simp)
      have tail := ih true (fun item member => eligible item (by simp [member]))
      simp [runSequentialScopes, head, tail]

-----------------------------------------------------------------------------------------
-- Omitting the reused scope's mutable arrays prevents old-result work aliasing
-----------------------------------------------------------------------------------------

/-- A ghost view of native work arrays. An omitted field reads as empty work; a retained
view can see later heap updates. This is not another queue implementation or heap model.
-/
inductive ScopeWorkView where
  | omitted
  | retained (scope : Nat)
deriving Repr, DecidableEq

def ScopeWorkView.read (heap : Nat → ReferenceWorkQueue.Work)
    : ScopeWorkView → ReferenceWorkQueue.Work
  | .omitted => {}
  | .retained scope => heap scope

def ScopedItemResult.workView (result : ScopedItemResult) (scope : Nat) : ScopeWorkView :=
  if result.work.isNone then .omitted else .retained scope

/-- The actual fast path exposes no work view, regardless of how a later item mutates
that scope. This does not prove immutability of a retained finished/nonempty scope.
-/
theorem CompletedItemScope.empty_result_noninterference (scope : CompletedItemScope)
    (eligible : scope.canReuse = true) (key : Nat)
    (before after : Nat → ReferenceWorkQueue.Work)
    : scope.buildResult.work = none
      ∧ scope.buildResult.value.errors = 0
      ∧ scope.buildResult.occurrence = scope.item.occurrence
      ∧ (scope.buildResult.workView key).read before = scope.item.work
      ∧ (scope.buildResult.workView key).read after = scope.item.work := by
  obtain ⟨_, errors, empty⟩ := scope.canReuse_inventory eligible
  simp [CompletedItemScope.buildResult, eligible, ScopedItemResult.workView,
    ScopeWorkView.read, errors, empty]

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
