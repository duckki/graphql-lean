import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.EventAccounting

/-! Identity and conditional liveness derived from output histories, not scheduler states.
-/

namespace GraphQL.IncrementalDelivery.WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution

/-- Derived notice uniqueness, support, and closure-reference facts for the observed
prefix; these are not admission premises.
-/
structure NoticeFacts (work : Work) (initial : NodeRefs) (events : List WorkQueueEvent)
    : Prop where
  announcedUnique : (announcedRefs initial events).Nodup
  completedUnique : (completedRefs events).Nodup
  supported : ∀ ref ∈ announcedRefs initial events, Supported work ref
  closed : ∀ ref ∈ completedRefs events, ref ∈ announcedRefs initial events

/-- A permitted output preserves notice facts, by fresh append and open-ref closure. -/
theorem NoticeFacts.extend {work initial before event}
    (h : NoticeFacts work initial before)
    (step : EventAccounting work initial before event)
    : NoticeFacts work initial (before ++ [event]) := by
  have announced : announcedRefs initial (before ++ [event]) =
      announcedRefs initial before ++ eventPending event := by
    simp [announcedRefs, pendingRefs, List.append_assoc]
  have completed : completedRefs (before ++ [event]) =
      completedRefs before ++ eventCompleted event := by simp [completedRefs]
  constructor
  · rw [announced]
    exact List.nodup_append.mpr ⟨h.announcedUnique, step.pendingUnique,
      fun a ha b hb equal => step.fresh b hb (equal ▸ ha)⟩
  · rw [completed]
    exact List.nodup_append.mpr ⟨h.completedUnique, step.completedUnique,
      fun a ha b hb equal => (step.completion b hb).2 (equal ▸ ha)⟩
  · intro ref member
    rw [announced] at member
    exact (List.mem_append.mp member).elim (h.supported ref) (step.supported ref)
  · intro ref member
    rw [announced]
    apply List.mem_append_left
    rw [completed] at member
    exact (List.mem_append.mp member).elim (h.closed ref) (fun hk => (step.completion ref hk).1)

/-- The initialized prefix has unique supported notices and no completions. -/
theorem Initializes.noticeFacts {work groups streams}
    (h : Initializes work groups streams)
    : NoticeFacts work ((groups ++ streams).map DeliveryNode.ref) [] := by
  obtain ⟨unique, support⟩ := initializes_notices h
  exact ⟨
    by simpa [announcedRefs, pendingRefs] using unique,
    by simp [completedRefs],
    by simpa [announcedRefs, pendingRefs] using support,
    by simp [completedRefs]
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
    : NoticeFacts work ((groups ++ streams).map DeliveryNode.ref) events := by
  simpa using h.notices.facts h.1.noticeFacts

/-- Terminal work accounting closes all structurally supported announced refs. -/
theorem Explains.allCompleted {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    (done
      : Terminal work ((groups ++ streams).map DeliveryNode.ref) matching events failures)
    : ∀ ref ∈ announcedRefs ((groups ++ streams).map DeliveryNode.ref) events,
        ref ∈ completedRefs events := by
  intro ref member
  obtain ⟨node, kind, dependencies, birth, known, rfl⟩ := h.noticeFacts.supported ref member
  exact (done.2 node kind dependencies birth known).resolve_right (fun hidden => hidden.1 member)

/-- (liveEvents events) requires every newly announced ref in the supplied atomic output
list to complete in that event or a later event.
-/
def liveEvents : List WorkQueueEvent → Prop
  | [] => True
  | event :: rest =>
      (∀ ref ∈ eventPending event, ref ∈ completedRefs (event :: rest)) ∧ liveEvents rest

/-- Fresh notices cannot use an earlier completion; global closure therefore gives causal
liveness.
-/
theorem NoticeHistory.liveEvents {work initial before events}
    (h : NoticeHistory work initial before events)
    (facts : NoticeFacts work initial before)
    (closed
      : ∀ ref ∈ announcedRefs initial (before ++ events),
          ref ∈ completedRefs (before ++ events))
    : liveEvents events := by
  induction events generalizing before with
  | nil => trivial
  | cons event rest ih =>
      constructor
      · intro ref member
        have known : ref ∈ announcedRefs initial (before ++ event :: rest) := by
          simp only [announcedRefs, pendingRefs, List.flatMap_append, List.flatMap_cons]
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_left _ member))
        have completes := closed ref known
        simp only [completedRefs, List.flatMap_append] at completes
        rcases List.mem_append.mp completes with earlier | later
        · exact False.elim (h.1.fresh ref member (facts.closed ref earlier))
        · exact later
      · apply ih h.2 (facts.extend h.1)
        simpa [List.append_assoc] using closed

/-- Every explained terminal history has causal node liveness, by support and fresh
release.
-/
theorem Explains.liveEvents {work groups streams events matching failures}
    (h : Explains work groups streams events matching failures)
    (done
      : Terminal work ((groups ++ streams).map DeliveryNode.ref) matching events failures)
    : liveEvents events := by
  apply h.notices.liveEvents h.1.noticeFacts
  simpa using h.allCompleted done

end GraphQL.IncrementalDelivery.WorkQueueSemantics
