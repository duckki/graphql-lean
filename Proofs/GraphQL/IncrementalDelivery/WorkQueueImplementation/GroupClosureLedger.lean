import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GroupNoticeAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationHistory
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingFailureFrames

/-! Distinct group-removal and notification ledgers use separate retirement predicates. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open WorkQueueSemantics

/-- Group refs closed by raw success/failure events, excluding stream completions. -/
def rawGroupClosureRefs : WorkQueueEvent → NodeRefs
  | .groupSuccess group _ _ | .groupFailure group _ => [group.ref]
  | _ => []

/-- A segment closes distinct refs, retires each one, and cannot close an old retired ref.
The before/result states are the actual executable states; no history admission is assumed.
-/
structure GroupClosureAccounting (before : State) (result : State × List WorkQueueEvent)
    (retirement : State → NodeRef → Prop := State.RetiredGroup)
    : Prop where
  unique : (result.2.flatMap rawGroupClosureRefs).Nodup
  closed : ∀ ref ∈ result.2.flatMap rawGroupClosureRefs, retirement result.1 ref
  preserves : ∀ ref, retirement before ref → retirement result.1 ref
  excludes : ∀ ref, retirement before ref → ref ∉ result.2.flatMap rawGroupClosureRefs

/-- A silent transition only needs to retain earlier retirement certificates.
Witness: its empty output has no new closure or duplicate.
-/
theorem GroupClosureAccounting.silent {before after : State}
    {retirement : State → NodeRef → Prop}
    (preserves : ∀ ref, retirement before ref → retirement after ref)
    : GroupClosureAccounting before (after, []) retirement :=
  ⟨by simp, by simp, preserves, by simp⟩

/-- Sequential segments cannot repeat a closure from an earlier segment.
Witness: every earlier closure supplies the retirement certificate excluded by the next.
-/
theorem GroupClosureAccounting.append {before first second}
    {retirement : State → NodeRef → Prop}
    (left : GroupClosureAccounting before first retirement)
    (right : GroupClosureAccounting first.1 second retirement)
    : GroupClosureAccounting before (second.1, first.2 ++ second.2) retirement := by
  refine ⟨?_, ?_, fun ref retired => right.preserves ref (left.preserves ref retired), ?_⟩
  · rw [List.flatMap_append]
    exact List.nodup_append.mpr ⟨left.unique, right.unique, by
      intro ref earlier other later same
      subst other
      exact right.excludes ref (left.closed ref earlier) later⟩
  · intro ref member
    rw [List.flatMap_append] at member
    rcases List.mem_append.mp member with earlier | later
    · exact right.preserves ref (left.closed ref earlier)
    · exact right.closed ref later
  · intro ref retired member
    rw [List.flatMap_append] at member
    rcases List.mem_append.mp member with earlier | later
    · exact left.excludes ref retired earlier
    · exact right.excludes ref (left.preserves ref retired) later

/-- A final silent state change preserves closure accounting if it preserves retirement.
Witness: transport every newly or previously retired ref through that state change.
-/
theorem GroupClosureAccounting.post {before result after}
    {retirement : State → NodeRef → Prop}
    (accounted : GroupClosureAccounting before result retirement)
    (preserves : ∀ ref, retirement result.1 ref → retirement after ref)
    : GroupClosureAccounting before (after, result.2) retirement :=
  ⟨
    accounted.unique,
    fun ref member => preserves ref (accounted.closed ref member),
    fun ref retired => preserves ref (accounted.preserves ref retired),
    accounted.excludes
  ⟩

/-- Reordering output preserves a closure ledger with the same final queue.
Witness: permutation retains uniqueness and exactly the same closing refs.
-/
theorem GroupClosureAccounting.permute {before result events}
    {retirement : State → NodeRef → Prop}
    (accounted : GroupClosureAccounting before result retirement)
    (same : result.2.Perm events)
    : GroupClosureAccounting before (result.1, events) retirement := by
  have refs := same.flatMap_right rawGroupClosureRefs
  exact ⟨refs.nodup accounted.unique,
    fun ref member => accounted.closed ref (refs.mem_iff.mpr member),
    accounted.preserves,
    fun ref retired member => accounted.excludes ref retired (refs.mem_iff.mpr member)⟩

/-- A retired group has no remaining failure notification waiting to be forwarded.
Taskless pruned groups can satisfy this predicate without an observable completion. -/
def State.GroupClosed (queue : State) (ref : NodeRef) : Prop :=
  queue.RetiredGroup ref ∧ ref ∉ queue.pendingGroupFailureRefs

/-- Notification accounting excludes a ref only after its pending control is consumed. -/
abbrev NotificationClosureAccounting (before : State)
    (result : State × List WorkQueueEvent) :=
  GroupClosureAccounting before result State.GroupClosed

/-- Pending failure refs are distinct, permanently retired group identities.
This invariant is derived from initialization and actual enqueue/consume transitions. -/
structure State.PendingGroupFailures (queue : State) : Prop where
  unique : queue.pendingGroupFailureRefs.Nodup
  retired : ∀ ref ∈ queue.pendingGroupFailureRefs, queue.RetiredGroup ref

/-- Failure controls retain exactly the refs of their queued notice payloads. -/
theorem failureClosureEvents_refs (notices : List GroupFailureEvent)
    : (notices.map
        (fun failure => WorkQueueEvent.groupFailure failure.group failure.errors)).flatMap
        rawGroupClosureRefs
      = notices.map (fun failure => failure.group.ref) := by
  induction notices with
  | nil => rfl
  | cons notice rest ih =>
      simpa only [List.map_cons, List.flatMap_cons,
        rawGroupClosureRefs, List.singleton_append] using congrArg (List.cons notice.group.ref) ih

/-- Cache visibility preserves closed-group status and outstanding notice identities. -/
theorem State.GroupClosed.cacheTaskFailures {queue : State} {ref : NodeRef}
    (closed : queue.GroupClosed ref) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).GroupClosed ref := by
  refine ⟨closed.1.cacheTaskFailures available, ?_⟩
  simpa only [State.pendingGroupFailureRefs, State.cacheTaskFailures_groupFailureEvents] using closed.2

/-- Exposing rejections changes no pending notice and preserves its retirement evidence. -/
theorem State.PendingGroupFailures.cacheTaskFailures {queue : State}
    (pending : queue.PendingGroupFailures) (available : List (Occurrence × Nat))
    : (queue.cacheTaskFailures available).PendingGroupFailures := by
  refine ⟨?_, ?_⟩
  · simpa only [State.pendingGroupFailureRefs, State.cacheTaskFailures_groupFailureEvents]
      using pending.unique
  · intro ref member
    rw [State.pendingGroupFailureRefs, State.cacheTaskFailures_groupFailureEvents] at member
    exact (pending.retired ref member).cacheTaskFailures available

/-- Consuming one distinct pending head completes its notification exactly once. -/
theorem State.PendingGroupFailures.groupFailure {queue : State}
    (pending : queue.PendingGroupFailures) (supplied : GroupFailureEvent)
    : (queue.groupFailure supplied).1.PendingGroupFailures
      ∧ NotificationClosureAccounting queue (queue.groupFailure supplied) := by
  cases queued : queue.groupFailureEvents with
  | nil =>
      simp only [State.groupFailure, queued]
      exact ⟨pending, .silent (fun _ closed => closed)⟩
  | cons first rest =>
      have refs : queue.pendingGroupFailureRefs
          = first.group.ref :: rest.map (fun failure => failure.group.ref) := by
        simp only [State.pendingGroupFailureRefs, queued, List.map_cons]
      have distinct := List.nodup_cons.mp (refs ▸ pending.unique)
      have headMember : first.group.ref ∈ queue.pendingGroupFailureRefs := by
        rw [refs]; exact List.mem_cons_self
      simp only [State.groupFailure, queued]
      split
      · refine ⟨⟨distinct.2, ?_⟩, ⟨by simp [rawGroupClosureRefs], ?_, ?_, ?_⟩⟩
        · intro ref member
          exact pending.retired ref (by rw [refs]; exact List.mem_cons_of_mem _ member)
        · intro ref member
          have same : ref = first.group.ref := by simpa only [List.flatMap_singleton,
            rawGroupClosureRefs, List.mem_singleton] using member
          subst ref
          exact ⟨pending.retired _ headMember, distinct.1⟩
        · intro ref closed
          refine ⟨closed.1, ?_⟩
          intro member
          exact closed.2 (by rw [refs]; exact List.mem_cons_of_mem _ member)
        · intro ref closed member
          have same : ref = first.group.ref := by simpa only [List.flatMap_singleton,
            rawGroupClosureRefs, List.mem_singleton] using member
          subst ref
          exact closed.2 headMember
      · exact ⟨pending, .silent (fun _ closed => closed)⟩

/-- Ordinary initialization begins with no outstanding failure notice. -/
theorem createWorkQueue_pendingGroupFailures (work : Work)
    : (State.initialize work).PendingGroupFailures := by
  refine ⟨?_, ?_⟩
  · simp only [State.pendingGroupFailureRefs, State.initialize_groupFailureEvents,
      List.map_nil, List.nodup_nil]
  · intro ref member
    simp only [State.pendingGroupFailureRefs, State.initialize_groupFailureEvents,
      List.map_nil, List.not_mem_nil] at member

/-- Fresh removals reserve new pending notices while immediate closures finish once.
Earlier pending refs are already retired, so the removal ledger excludes reusing them. -/
theorem State.PendingGroupFailures.enqueue_closureAccounting {before after : State}
    (pending : before.PendingGroupFailures) (events : List WorkQueueEvent)
    (notices : List GroupFailureEvent)
    (accounted
      : GroupClosureAccounting before
          (
            after,
            events
            ++ notices.map (fun failure => .groupFailure failure.group failure.errors)
          ))
    (same : after.groupFailureEvents = before.groupFailureEvents)
    : (after.enqueueGroupFailures notices).PendingGroupFailures
      ∧ NotificationClosureAccounting before
          (after.enqueueGroupFailures notices, events) := by
  let emitted := events.flatMap rawGroupClosureRefs
  let fresh := notices.map (fun failure => failure.group.ref)
  have projected : (events ++ notices.map (fun failure =>
        WorkQueueEvent.groupFailure failure.group failure.errors)).flatMap rawGroupClosureRefs
      = emitted ++ fresh := by
    rw [List.flatMap_append, failureClosureEvents_refs]
  have outputMember {ref} (member : ref ∈ emitted)
      : ref ∈ (events ++ notices.map (fun failure =>
          WorkQueueEvent.groupFailure failure.group failure.errors)).flatMap rawGroupClosureRefs := by
    rw [projected]; exact List.mem_append_left _ member
  have freshMember {ref} (member : ref ∈ fresh)
      : ref ∈ (events ++ notices.map (fun failure =>
          WorkQueueEvent.groupFailure failure.group failure.errors)).flatMap rawGroupClosureRefs := by
    rw [projected]; exact List.mem_append_right _ member
  have counted : (emitted ++ fresh).Nodup := projected ▸ accounted.unique
  obtain ⟨outputUnique, freshUnique, separate⟩ := List.nodup_append.mp counted
  have queued : (after.enqueueGroupFailures notices).pendingGroupFailureRefs
      = before.pendingGroupFailureRefs ++ fresh := by
    simp only [State.pendingGroupFailureRefs, State.enqueueGroupFailures, List.map_append, same]
    rfl
  refine ⟨⟨?_, ?_⟩, ⟨outputUnique, ?_, ?_, ?_⟩⟩
  · rw [queued]
    apply List.nodup_append.mpr ⟨pending.unique, freshUnique, ?_⟩
    intro ref old other added equal
    subst other
    exact accounted.excludes ref (pending.retired ref old) (freshMember added)
  · intro ref member
    rw [queued] at member
    rcases List.mem_append.mp member with old | added
    · exact accounted.preserves ref (pending.retired ref old)
    · exact accounted.closed ref (freshMember added)
  · intro ref member
    refine ⟨accounted.closed ref (outputMember member), ?_⟩
    intro waiting
    rw [queued] at waiting
    rcases List.mem_append.mp waiting with old | added
    · exact accounted.excludes ref (pending.retired ref old) (outputMember member)
    · exact separate ref member ref added rfl
  · intro ref closed
    refine ⟨accounted.preserves ref closed.1, ?_⟩
    intro waiting
    rw [queued] at waiting
    rcases List.mem_append.mp waiting with old | added
    · exact closed.2 old
    · exact accounted.excludes ref closed.1 (freshMember added)
  · intro ref closed member
    exact accounted.excludes ref closed.1 (outputMember member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
