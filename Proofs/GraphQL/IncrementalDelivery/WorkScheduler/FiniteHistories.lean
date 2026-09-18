import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.PublicationExtension
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.StructuralEquivalence
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.Publication

/-! A finite bound on independently admitted atomic histories. The inventory below is
proof-only: it counts possible publications and closures, without ordering future events.
-/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

-----------------------------------------------------------------------------------------
-- A finite inventory of one-shot observations
-----------------------------------------------------------------------------------------

/-- A publication occurrence or completion key. Equal payloads have distinct occurrences;
repeated node descriptors intentionally share the same completion token.
-/
abbrev ObservationToken := Sum Occurrence Nat

/-- All possible observation tokens below this absolute work address. This projection
may repeat completion keys; a history can consume each token at most once.
-/
def observationTokens (address : Address) : Work → List ObservationToken
  | .empty => []
  | .append left right =>
      observationTokens (address ++ [0]) left ++ observationTokens (address ++ [1]) right
  | .deferred groups _ _ children =>
      .inl (.deferred address)
      :: (groups.map (fun group => .inr group.node.key)
          ++ observationTokens (address ++ [0]) children)
  | .stream node items =>
      .inr node.key
      :: (List.finRange items.length).flatMap
          (fun (index : Fin items.length) =>
            .inl (.item address index.val)
            :: observationTokens (address ++ [index.val]) items[index.val].2)
termination_by work => sizeOf work
decreasing_by
  all_goals simp_wf
  all_goals try decreasing_trivial
  have smaller := List.sizeOf_lt_of_mem (List.getElem_mem (l := items) index.isLt)
  have pairSize : sizeOf items[index.val] =
      1 + sizeOf items[index.val].1 + sizeOf items[index.val].2 := by
    exact Prod.mk.sizeOf_spec _ _
  omega

/-- Every located subtree's token inventory is contained in the root inventory.
Witness: structural navigation, selecting the corresponding append side or stream item.
-/
theorem Located.observationTokens {work address current producer owners}
    (located : Located work address current producer owners)
    : (observationTokens address current).Subset (observationTokens [] work) := by
  have navigation := StructuralEquivalence.located_of_current located
  clear located
  induction navigation with
  | root => exact List.Subset.refl _
  | left _ ih =>
      intro token member
      apply ih
      rw [WorkScheduler.observationTokens]
      exact List.mem_append_left _ member
  | right _ ih =>
      intro token member
      apply ih
      rw [WorkScheduler.observationTokens]
      exact List.mem_append_right _ member
  | deferred _ ih =>
      intro token member
      apply ih
      rw [WorkScheduler.observationTokens]
      exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  | @item address node items producer owners index result children _ entry ih =>
      intro token member
      apply ih
      rw [WorkScheduler.observationTokens]
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      have bound := (List.getElem?_eq_some_iff.mp entry).1
      refine ⟨⟨index, bound⟩, List.mem_finRange _, ?_⟩
      have selected : items[index] = (result, children) :=
        (List.getElem?_eq_some_iff.mp entry).2
      simpa only [selected] using List.mem_cons_of_mem (.inl (.item address index)) member

/-- Every structural task contributes its publication token. Witness: its located
deferred boundary or selected stream item in the finite inventory.
-/
theorem TaskAt.observationToken {work occurrence owners producer payload}
    (known : TaskAt work occurrence owners producer payload)
    : .inl occurrence ∈ observationTokens [] work := by
  cases StructuralEquivalence.taskAt_of_current known with
  | deferred located =>
      exact located.toCurrent.observationTokens (by simp [observationTokens])
  | @item address node items producer enclosing index result children located entry =>
      apply located.toCurrent.observationTokens
      rw [observationTokens]
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      have bound := (List.getElem?_eq_some_iff.mp entry).1
      exact ⟨⟨index, bound⟩, List.mem_finRange _, by simp⟩

/-- Every node descriptor contributes its completion key. Witness: the group membership
or stream boundary, transported from its located subtree to the root.
-/
theorem NodeAt.observationToken {work node kind parents birth}
    (known : NodeAt work node kind parents birth)
    : .inr node.key ∈ observationTokens [] work := by
  cases StructuralEquivalence.nodeAt_of_current known with
  | group located member =>
      apply located.toCurrent.observationTokens
      rw [observationTokens]
      exact List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.mpr ⟨_, member, rfl⟩))
  | stream located =>
      exact located.toCurrent.observationTokens (by simp [observationTokens])

/-- An atomic value consumes its matched occurrence; a control event consumes its
completion key. The termination case is unused by Explains and handled separately.
-/
def observationToken (occurrence : Occurrence) : WorkEvent → ObservationToken
  | .groupValues .. | .streamValues .. => .inl occurrence
  | .groupSuccess node ..
  | .groupFailure node _
  | .streamSuccess node
  | .streamFailure node _ => .inr node.key
  | .workQueueTermination => .inr 0

/-- Every permitted atomic event consumes a token present in its original work.
Witness: the successful task provenance or the control event's node descriptor.
-/
theorem EventAllowed.observationToken {work initial matching before failed event}
    (allowed : EventAllowed work initial matching before failed event)
    : observationToken (matching before.length) event ∈ observationTokens [] work := by
  cases event with
  | groupValues node values =>
      obtain ⟨_, _, _, _, _, _, known, _⟩ := allowed
      exact known.observationToken
  | streamValues node values groups streams =>
      obtain ⟨_, _, _, _, _, known, _⟩ := allowed
      exact known.observationToken
  | groupSuccess node groups streams | groupFailure node errors
  | streamSuccess node | streamFailure node errors =>
      obtain ⟨_, _, known⟩ := allowed.1
      exact known.observationToken
  | workQueueTermination => exact False.elim allowed

-----------------------------------------------------------------------------------------
-- Histories cannot reuse inventory tokens
-----------------------------------------------------------------------------------------

/-- Every permitted event is either a value publication or exactly one completion.
Witness: the six admitted event constructors; termination is excluded by EventAllowed.
-/
theorem EventAllowed.token_cases {work initial matching before failed event}
    (allowed : EventAllowed work initial matching before failed event)
    (occurrence : Occurrence)
    : (IsValue event ∧ WorkScheduler.observationToken occurrence event = .inl occurrence)
      ∨ ∃ key,
          WorkScheduler.observationToken occurrence event = .inr key
          ∧ eventCompleted event = [key] := by
  cases event <;> simp_all [EventAllowed, IsValue, WorkScheduler.observationToken,
    eventCompleted]

/-- Two admitted event positions cannot consume the same observation token. Witness:
value freshness for publications, or an earlier closure contradicting an open-key rule.
-/
theorem Explains.observationToken_unique {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    {left right first second}
    (firstAt : events[left]? = some first) (secondAt : events[right]? = some second)
    (same
      : observationToken (matching left) first = observationToken (matching right) second)
    : left = right := by
  have earlier {i j a b} (atI : events[i]? = some a) (atJ : events[j]? = some b)
      (equal : observationToken (matching i) a = observationToken (matching j) b)
      (less : i < j) : False := by
    have first := explained.2.2 i a atI
    have second := explained.2.2 j b atJ
    rcases first.token_cases (matching i) with ⟨valueI, tokenI⟩ | ⟨keyI, tokenI, closedI⟩
    · rcases second.token_cases (matching j) with ⟨valueJ, tokenJ⟩ | ⟨keyJ, tokenJ, _⟩
      · have matchingSame : matching i = matching j := by
          simpa only [tokenI, tokenJ, Sum.inl.injEq] using equal
        have eq := explained.publication_unique atI valueI atJ valueJ matchingSame
        omega
      · simp only [tokenI, tokenJ, reduceCtorEq] at equal
    · rcases second.token_cases (matching j) with ⟨_, tokenJ⟩ | ⟨keyJ, tokenJ, closedJ⟩
      · simp only [tokenI, tokenJ, reduceCtorEq] at equal
      · have keys : keyI = keyJ := by simpa only [tokenI, tokenJ, Sum.inr.injEq] using equal
        subst keyJ
        have active := second.accounting.completion keyI (by simp [closedJ])
        apply active.2
        exact List.mem_flatMap.mpr ⟨a,
          List.mem_of_getElem? ((List.getElem?_take_of_lt less).trans atI),
          by simp [closedI]⟩
  by_cases less : left < right
  · exact False.elim (earlier firstAt secondAt same less)
  · by_cases greater : right < left
    · exact False.elim (earlier secondAt firstAt same.symm greater)
    · omega

/-- Every atomic history is bounded by the finite source-token inventory. Witness:
inject its event positions into the inventory using the one-shot observation theorem.
No success, termination, key-order, or generated-work premise is needed.
-/
theorem Explains.length_le_observationTokens
    {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : events.length ≤ (observationTokens [] work).length := by
  let used := List.ofFn (fun (index : Fin events.length) =>
    observationToken (matching index.val) events[index.val])
  have unique : used.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj less equal
    simp only [used, List.getElem_ofFn] at equal
    have eq := explained.observationToken_unique
      (List.getElem?_eq_getElem (by simpa only [used, List.length_ofFn] using hi))
      (List.getElem?_eq_getElem (by simpa only [used, List.length_ofFn] using hj)) equal
    omega
  have subset : used.Subset (observationTokens [] work) := by
    intro token member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    have known := (explained.2.2 index.val events[index.val]
      (List.getElem?_eq_getElem index.isLt)).observationToken
    simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt index.isLt)] using known
  simpa only [used, List.length_ofFn] using unique.length_le_of_subset subset

-----------------------------------------------------------------------------------------
-- Maximal finite continuations exist, but need not be complete
-----------------------------------------------------------------------------------------

/-- Work batching cannot introduce more batches than input atoms. Witness: every batch
consumes a nonempty input group, independently of optional value coalescing.
-/
theorem WorkBatching.length_le {events batches} (batched : WorkBatching events batches)
    : batches.length ≤ events.length := by
  induction batched with
  | nil => exact Nat.le_refl _
  | @cons batch tail grouped rest nonempty values subsequent ih =>
      have positive := List.length_pos_iff.mpr nonempty
      simp only [List.length_cons, List.length_append]
      omega

/-- An admitted prefix has at most one batch per source observation token. Witness:
unbatched history finiteness followed by the nonempty work-batching bound.
-/
theorem AdmissiblePrefix.length_le_observationTokens {work history}
    (admitted : AdmissiblePrefix work history)
    : history.batches.length ≤ (observationTokens [] work).length := by
  obtain ⟨events, matching, failures, explained, batched⟩ := admitted
  exact Nat.le_trans batched.length_le explained.length_le_observationTokens

/-- A complete work run needs at most one additional batch for termination. Witness:
the same atomic bound, with the single final termination marker included before batching.
-/
theorem AdmissibleRun.length_le_observationTokens {work history}
    (admitted : AdmissibleRun work history)
    : history.batches.length ≤ (observationTokens [] work).length + 1 := by
  obtain ⟨events, matching, failures, explained, terminal, batched⟩ := admitted
  have atoms := explained.length_le_observationTokens
  have batches := batched.length_le
  simp only [List.length_append, List.length_singleton] at batches
  omega

/-- Every valid work history has a uniform finite batch bound, including interrupted
prefixes, errors, and all grouping choices. Witness: its prefix or terminal admission.
-/
theorem ValidHistory.length_le_observationTokens {work history}
    (admitted : ValidHistory work history)
    : history.batches.length ≤ (observationTokens [] work).length + 1 := by
  rcases admitted with admittedPrefix | complete
  · exact Nat.le_trans admittedPrefix.length_le_observationTokens (Nat.le_succ _)
  · exact complete.length_le_observationTokens

/-- A nonempty bounded set of natural lengths has a greatest member. Witness: induction
on the bound, retaining it when present and otherwise using the smaller bound.
-/
private theorem bounded_maximum (predicate : Nat → Prop) (bound : Nat)
    (inhabited : ∃ length, predicate length)
    (bounded : ∀ length, predicate length → length ≤ bound)
    : ∃ length, predicate length ∧ ∀ other, predicate other → other ≤ length := by
  classical
  induction bound with
  | zero =>
      obtain ⟨length, member⟩ := inhabited
      exact ⟨length, member, fun other known => Nat.le_trans (bounded other known)
        (Nat.zero_le _)⟩
  | succ bound ih =>
      by_cases present : predicate (bound + 1)
      · exact ⟨bound + 1, present, bounded⟩
      · apply ih
        intro length member
        have upper := bounded length member
        have different : length ≠ bound + 1 := fun equal => present (equal ▸ member)
        omega

/-- A proof construction can retain its own witness property while maximizing admitted
continuations. Witness: bound lengths by the same finite observation inventory, restricting
only this existential choice. The property is not a premise of public work admission.
-/
theorem Explains.maximal_extension_preserving
    {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    (property : List WorkEvent → PublicationMatching → FailureCuts → Prop)
    (holds : property events matching failures)
    : ∃ tail next cuts,
        Explains work groups streams (events ++ tail) next cuts
        ∧ property (events ++ tail) next cuts
        ∧ ∀ suffix later laterCuts,
            Explains work groups streams (events ++ tail ++ suffix) later laterCuts
            → property (events ++ tail ++ suffix) later laterCuts
            → suffix = [] := by
  let possible (length : Nat) := ∃ tail next cuts,
    Explains work groups streams (events ++ tail) next cuts
    ∧ property (events ++ tail) next cuts
    ∧ (events ++ tail).length = length
  have inhabited : ∃ length, possible length :=
    ⟨events.length, [], matching, failures, by simpa using explained,
      by simpa using holds, by simp⟩
  have bounded : ∀ length, possible length → length ≤ (observationTokens [] work).length := by
    rintro length ⟨tail, next, cuts, admitted, _, rfl⟩
    exact admitted.length_le_observationTokens
  obtain ⟨length, ⟨tail, next, cuts, admitted, retained, equal⟩, greatest⟩ :=
    bounded_maximum possible (observationTokens [] work).length inhabited bounded
  refine ⟨tail, next, cuts, admitted, retained, ?_⟩
  intro suffix later laterCuts extended preserved
  have upper := greatest (events ++ tail ++ suffix).length
    ⟨tail ++ suffix, later, laterCuts, by simpa only [List.append_assoc] using extended,
      by simpa only [List.append_assoc] using preserved,
      by simp only [List.append_assoc]⟩
  apply List.eq_nil_of_length_eq_zero
  simp only [List.length_append] at equal upper
  omega

/-- An explained prefix has a longest admitted continuation with the same initial
notices and observed events. Witness: the property-preserving construction with `True`.
This is not a terminal-run theorem: a maximal history may be blocked by its notice choices.
Matching and failure evidence remain existential explanations of the supplied outputs.
-/
theorem Explains.maximal_extension {work groups streams events matching failures}
    (explained : Explains work groups streams events matching failures)
    : ∃ tail next cuts,
        Explains work groups streams (events ++ tail) next cuts
        ∧ ∀ suffix later laterCuts,
            Explains work groups streams (events ++ tail ++ suffix) later laterCuts
            → suffix = [] := by
  obtain ⟨tail, next, cuts, admitted, _, maximal⟩ :=
    explained.maximal_extension_preserving (fun _ _ _ => True) trivial
  exact ⟨tail, next, cuts, admitted, fun suffix later laterCuts extended =>
    maximal suffix later laterCuts extended trivial⟩

end GraphQL.IncrementalDelivery.WorkScheduler
