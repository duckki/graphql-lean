import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginAnnotations

/-! Scope-local uniqueness helpers for primitive error references. Child call cones
are disjoint; bubbling may remove future inventories but cannot duplicate references.
These are pure retained-outcome invariants, not native recording-time observations. -/

namespace
  GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting

open GraphQL.IncrementalDelivery.Execution

/-- Every retained origin is unique and belongs to this recursive call's route cone. -/
structure Scoped (route : List Nat) (origins : List Origin) : Prop where
  unique : origins.Nodup
  within : ∀ origin ∈ origins, route.IsPrefix origin.1

namespace Scoped

theorem empty (route : List Nat) : Scoped route [] := ⟨by simp, by simp⟩

theorem primitive (route : List Nat) (errors : Nat)
    : Scoped route (primitiveOrigins route errors) := by
  refine ⟨?_, ?_⟩
  · exact List.Pairwise.map _ (fun _ _ different same => different (congrArg Prod.snd same))
      List.nodup_range
  · intro origin member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact ⟨[], by simp⟩

theorem rebase {route child : List Nat} {origins : List Origin}
    (known : Scoped child origins) (earlier : route.IsPrefix child)
    : Scoped route origins :=
  ⟨known.unique, fun origin member => earlier.trans (known.within origin member)⟩

theorem parent {route : List Nat} {tag : Nat} {origins : List Origin}
    (known : Scoped (route ++ [tag]) origins)
    : Scoped route origins :=
  known.rebase ⟨[tag], rfl⟩

theorem left {route : List Nat} {left right : List Origin}
    (known : Scoped route (left ++ right))
    : Scoped route left :=
  ⟨
    (List.nodup_append.mp known.unique).1,
    fun origin member => known.within origin (List.mem_append_left _ member)
  ⟩

theorem right {route : List Nat} {left right : List Origin}
    (known : Scoped route (left ++ right))
    : Scoped route right :=
  ⟨
    (List.nodup_append.mp known.unique).2.1,
    fun origin member => known.within origin (List.mem_append_right _ member)
  ⟩

theorem perm {route : List Nat} {origins changed : List Origin}
    (known : Scoped route origins) (permutation : origins.Perm changed)
    : Scoped route changed :=
  ⟨
    permutation.nodup known.unique,
    fun origin member => known.within origin (permutation.mem_iff.mpr member)
  ⟩

/-- Binary child cones cannot identify the same primitive, at any depth. -/
theorem separated (route target : List Nat)
    (left : (route ++ [0]).IsPrefix target)
    (right : (route ++ [1]).IsPrefix target)
    : False := by
  obtain ⟨leftTail, leftEq⟩ := left
  obtain ⟨rightTail, rightEq⟩ := right
  have same := leftEq.trans rightEq.symm
  simp only [List.append_assoc, List.singleton_append, List.append_cancel_left_eq,
    List.cons.injEq] at same
  omega

theorem join {route : List Nat} {left right : List Origin}
    (head : Scoped (route ++ [0]) left) (tail : Scoped (route ++ [1]) right)
    : Scoped route (left ++ right) := by
  refine ⟨List.nodup_append.mpr ⟨head.unique, tail.unique, ?_⟩, ?_⟩
  · intro first firstMember second secondMember same
    subst second
    exact separated route first.1 (head.within first firstMember)
      (tail.within first secondMember)
  · intro origin member
    rcases List.mem_append.mp member with member | member
    · exact head.parent.within origin member
    · exact tail.parent.within origin member

end Scoped

-----------------------------------------------------------------------------------------
-- Completion operators preserve identities and discard only future inventories
-----------------------------------------------------------------------------------------

theorem pure_scoped (route : List Nat) (value : α)
    : Scoped route (RecordedCompletion.pure value).origins := by
  simpa [RecordedCompletion.origins, RecordedCompletion.pure, Report.pure,
    RecordedWork.origins]
    using Scoped.empty route

theorem fault_scoped (route : List Nat) (outcome : Result α)
    : Scoped route (RecordedCompletion.fault route outcome).origins := by
  simpa [RecordedCompletion.origins, RecordedCompletion.fault, Report.fault,
    RecordedWork.origins]
    using Scoped.primitive route (ScheduledErrors.countedErrors outcome)

theorem combine_scoped (f : α → β → γ) (left : RecordedCompletion α)
    (right : RecordedCompletion β) (route : List Nat)
    (head : Scoped (route ++ [0]) left.origins)
    (tail : Scoped (route ++ [1]) right.origins)
    : Scoped route (RecordedCompletion.combine f left right).origins := by
  have reports := Scoped.join head.left tail.left
  have whole := Scoped.join head tail
  have canonical : Scoped route (left.report.origins ++
      (left.work.origins ++ (right.report.origins ++ right.work.origins))) := by
    simpa only [RecordedCompletion.origins, List.append_assoc] using whole
  have reordered := canonical.perm
    (List.Perm.append_left left.report.origins
      (List.perm_append_comm_assoc left.work.origins right.report.origins right.work.origins))
  simp only [RecordedCompletion.combine, Report.combine]
  split
  · simpa only [RecordedCompletion.origins, RecordedWork.origins, List.append_nil]
      using reports
  · simpa only [RecordedCompletion.origins, RecordedWork.origins, List.append_assoc]
      using reordered

theorem map_scoped (f : α → β) (completed : RecordedCompletion α) (route : List Nat)
    (known : Scoped route completed.origins)
    : Scoped route (completed.map f).origins := by
  cases h : completed.report.outcome <;>
    simp only [RecordedCompletion.map, Report.map, h, RecordedCompletion.origins,
      RecordedWork.origins, List.append_nil]
  · exact known.left
  · exact known

theorem catchNull_scoped (wrap : α → ResponseValue) (completed : RecordedCompletion α)
    (route : List Nat) (known : Scoped route completed.origins)
    : Scoped route (completed.catchNull wrap).origins := by
  cases h : completed.report.outcome <;>
    simp only [RecordedCompletion.catchNull, Report.catchNull, h, RecordedCompletion.origins,
      RecordedWork.origins, List.append_nil]
  · exact known.left
  · exact known

theorem nonNull_scoped (completed : RecordedCompletion ResponseValue) (route : List Nat)
    (known : Scoped (route ++ [0]) completed.origins)
    : Scoped route (completed.nonNull route).origins := by
  obtain ⟨⟨outcome, origins, accounts⟩, work⟩ := completed
  cases outcome with
  | error errors =>
      simpa [RecordedCompletion.nonNull, RecordedCompletion.origins, Report.nonNull,
        RecordedWork.origins] using known.left.parent
  | ok value =>
      obtain ⟨value, errors⟩ := value
      cases value with
      | null =>
          cases errors with
          | zero =>
              simpa [RecordedCompletion.nonNull, RecordedCompletion.origins,
                Report.nonNull, Report.fault, RecordedWork.origins,
                ScheduledErrors.countedErrors]
                using Scoped.primitive route 1
          | succ errors =>
              simpa [RecordedCompletion.nonNull, RecordedCompletion.origins, Report.nonNull,
                RecordedWork.origins] using known.left.parent
      | scalar value =>
          simpa [RecordedCompletion.nonNull, RecordedCompletion.origins, Report.nonNull]
            using known.parent
      | object fields =>
          simpa [RecordedCompletion.nonNull, RecordedCompletion.origins, Report.nonNull]
            using known.parent
      | list values =>
          simpa [RecordedCompletion.nonNull, RecordedCompletion.origins, Report.nonNull]
            using known.parent

theorem appendWork_scoped (completed : RecordedCompletion α) (work : RecordedWork)
    (route : List Nat) (initial : Scoped (route ++ [0]) completed.origins)
    (future : Scoped (route ++ [1]) work.origins)
    : Scoped route ({ completed with work := .combine completed.work work }).origins := by
  simpa only [RecordedCompletion.origins, RecordedWork.origins, List.append_assoc]
    using Scoped.join initial future

end GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement.OriginAccounting
