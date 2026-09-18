import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.EventAccounting

/-! Identity and conditional liveness derived from output histories, not scheduler states.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- Derived notice uniqueness, support, and closure-reference facts for the observed
prefix; these are not admission premises.
-/
structure NoticeFacts (work : Work) (initial : Keys) (events : List WorkEvent)
    : Prop where
  announcedUnique : (announcedKeys initial events).Nodup
  completedUnique : (completedKeys events).Nodup
  supported : ∀ key ∈ announcedKeys initial events, Supported work key
  closed : ∀ key ∈ completedKeys events, key ∈ announcedKeys initial events

/-- A permitted output preserves notice facts, by fresh append and open-key closure. -/
theorem NoticeFacts.extend {work initial before event}
    (h : NoticeFacts work initial before)
    (step : EventAccounting work initial before event)
    : NoticeFacts work initial (before ++ [event]) := by
  have announced : announcedKeys initial (before ++ [event]) =
      announcedKeys initial before ++ eventPending event := by
    simp [announcedKeys, pendingKeys, List.append_assoc]
  have completed : completedKeys (before ++ [event]) =
      completedKeys before ++ eventCompleted event := by simp [completedKeys]
  constructor
  · rw [announced]
    exact List.nodup_append.mpr ⟨h.announcedUnique, step.pendingUnique,
      fun a ha b hb equal => step.fresh b hb (equal ▸ ha)⟩
  · rw [completed]
    exact List.nodup_append.mpr ⟨h.completedUnique, step.completedUnique,
      fun a ha b hb equal => (step.completion b hb).2 (equal ▸ ha)⟩
  · intro key member
    rw [announced] at member
    exact (List.mem_append.mp member).elim (h.supported key) (step.supported key)
  · intro key member
    rw [announced]
    apply List.mem_append_left
    rw [completed] at member
    exact (List.mem_append.mp member).elim (h.closed key) (fun hk => (step.completion key hk).1)

/-- The initialized prefix has unique supported notices and no completions. -/
theorem Initializes.noticeFacts {work groups streams}
    (h : Initializes work groups streams)
    : NoticeFacts work ((groups ++ streams).map DeliveryNode.key) [] := by
  obtain ⟨unique, support⟩ := initializes_notices h
  exact ⟨
    by simpa [announcedKeys, pendingKeys] using unique,
    by simp [completedKeys],
    by simpa [announcedKeys, pendingKeys] using support,
    by simp [completedKeys]
  ⟩

/-- Notice facts extend along any explained output suffix, by list induction. -/
theorem NoticeHistory.facts {work initial before events}
    (h : NoticeHistory work initial before events)
    (facts : NoticeFacts work initial before)
    : NoticeFacts work initial (before ++ events) := by
  induction events generalizing before with
  | nil => simpa using facts
  | cons event rest ih =>
      simpa [List.append_assoc] using ih h.2 (facts.extend h.1)

/-- Every explained history has unique notices and causal closure references. -/
theorem Explains.noticeFacts {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    : NoticeFacts work ((groups ++ streams).map DeliveryNode.key) events := by
  simpa using h.notices.facts h.1.noticeFacts

/-- Terminal work accounting closes all structurally supported announced keys. -/
theorem Explains.allCompleted {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    (done
      : Terminal work ((groups ++ streams).map DeliveryNode.key) matching events
          (failedBefore failures events.length))
    : ∀ key ∈ announcedKeys ((groups ++ streams).map DeliveryNode.key) events,
        key ∈ completedKeys events := by
  intro key member
  obtain ⟨node, kind, parents, birth, known, rfl⟩ := h.noticeFacts.supported key member
  exact (done.2 node kind parents birth known).resolve_right (fun hidden => hidden.1 member)

/-- (liveEvents events) requires every newly announced key in the supplied atomic output
list to complete in that event or a later event.
-/
def liveEvents : List WorkEvent → Prop
  | [] => True
  | event :: rest =>
      (∀ key ∈ eventPending event, key ∈ completedKeys (event :: rest)) ∧ liveEvents rest

/-- Fresh notices cannot use an earlier completion; global closure therefore gives causal
liveness.
-/
theorem NoticeHistory.liveEvents {work initial before events}
    (h : NoticeHistory work initial before events)
    (facts : NoticeFacts work initial before)
    (closed
      : ∀ key ∈ announcedKeys initial (before ++ events),
          key ∈ completedKeys (before ++ events))
    : liveEvents events := by
  induction events generalizing before with
  | nil => trivial
  | cons event rest ih =>
      constructor
      · intro key member
        have known : key ∈ announcedKeys initial (before ++ event :: rest) := by
          simp only [announcedKeys, pendingKeys, List.flatMap_append, List.flatMap_cons]
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_left _ member))
        have completes := closed key known
        simp only [completedKeys, List.flatMap_append] at completes
        rcases List.mem_append.mp completes with earlier | later
        · exact False.elim (h.1.fresh key member (facts.closed key earlier))
        · exact later
      · apply ih h.2 (facts.extend h.1)
        simpa [List.append_assoc] using closed

/-- Every explained terminal history has causal node liveness, by support and fresh
release.
-/
theorem Explains.liveEvents {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    (done
      : Terminal work ((groups ++ streams).map DeliveryNode.key) matching events
          (failedBefore failures events.length))
    : liveEvents events := by
  apply h.notices.liveEvents h.1.noticeFacts
  simpa using h.allCompleted done

end GraphQL.IncrementalDelivery.WorkScheduler
