import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamRegistrationOrigins
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedLookupPreservation

/-! Fresh stream inputs are neither lost by deduplication nor omitted from producer attachment. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- First-encounter selection covers every previously unregistered supplied key
-----------------------------------------------------------------------------------------

/-- Deduplicating the supplied streams retains every key absent from the old registry.
Witness: preceding selections retain keys, and the selected descriptor either finds its
key already selected or appends it. Later selections cannot remove it.
-/
theorem State.addStreams_selection_covers (queue : State) (streams : List Stream)
    {stream : Stream} (member : stream ∈ streams)
    (absent : queue.stream? stream.node.key = none)
    : let selected :=
        streams.foldl
          (fun selected candidate =>
            if (queue.stream? candidate.node.key).isSome
                || selected.any (fun known => known.node.key == candidate.node.key) then
              selected
            else
              selected ++ [candidate])
          []
      stream.node.key ∈ selected.map (fun candidate => candidate.node.key) := by
  let step (selected : List Stream) (candidate : Stream) :=
    if (queue.stream? candidate.node.key).isSome
        || selected.any (fun known => known.node.key == candidate.node.key) then selected
    else selected ++ [candidate]
  have preserves (selected : List Stream) (candidate : Stream)
      (present : stream.node.key ∈ selected.map (fun known => known.node.key))
      : stream.node.key ∈ (step selected candidate).map (fun known => known.node.key) := by
    unfold step
    split
    · exact present
    · rw [List.map_append]; exact List.mem_append_left _ present
  have selects (selected : List Stream)
      : stream.node.key ∈ (step selected stream).map (fun known => known.node.key) := by
    unfold step
    simp only [absent, Option.isSome_none, Bool.false_or]
    split
    · rename_i present
      obtain ⟨known, included, equal⟩ := List.any_eq_true.mp present
      exact List.mem_map.mpr ⟨known, included, beq_iff_eq.mp equal⟩
    · rw [List.map_append]
      exact List.mem_append_right _ List.mem_cons_self
  have loop (more selected : List Stream)
      (present : stream ∈ more ∨ stream.node.key ∈ selected.map (fun known => known.node.key))
      : stream.node.key ∈ (more.foldl step selected).map (fun known => known.node.key) := by
    induction more generalizing selected with
    | nil =>
        rcases present with impossible | included
        · cases impossible
        · exact included
    | cons candidate rest ih =>
        apply ih (step selected candidate)
        rcases present with incoming | earlier
        · rcases List.mem_cons.mp incoming with rfl | later
          · exact .inr (selects selected)
          · exact .inl later
        · exact .inr (preserves selected candidate earlier)
  exact loop streams [] (.inl member)

/-- Registering a fresh root stream returns its key in the immediate notice list.
Witness: complete first-encounter selection and the literal root-return branch.
-/
theorem State.addStreams_fresh_root_notice (queue : State) (streams : List Stream)
    {stream : Stream} (member : stream ∈ streams)
    (absent : queue.stream? stream.node.key = none)
    : stream.node.key
      ∈ ((queue.addStreams streams none).2.map Execution.DeliveryNode.key) := by
  simpa only [State.addStreams, List.map_map, Function.comp_def]
    using queue.addStreams_selection_covers streams member absent

/-- Registering a fresh child stream attaches it to its live producer and keeps the value.
Witness: complete selection supplies the child key; exact first-match replacement retains
the same task and buffered value while extending its child-stream list.
-/
theorem State.addStreams_fresh_child_attached {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (streams : List Stream)
    {stream : Stream} (member : stream ∈ streams)
    (absent : queue.stream? stream.node.key = none)
    : ∃ next,
        (queue.addStreams streams (some occurrence)).1.taskNode? occurrence = some next
        ∧ next.task = node.task
        ∧ next.value = node.value
        ∧ stream.node.key ∈ next.childStreams := by
  have selected := queue.addStreams_selection_covers streams member absent
  unfold State.addStreams
  dsimp only
  split
  · rename_i missing
    have impossible : some node = none := found.symm.trans missing
    cases impossible
  · rename_i current lookup
    have same : current = node := Option.some.inj (lookup.symm.trans found)
    subst current
    refine ⟨_, State.putTaskNode_lookup_same lookup _ (State.taskNode?_some found).2,
      rfl, rfl, List.mem_append_right _ selected⟩

-----------------------------------------------------------------------------------------
-- The complete object-integration boundary retains the newly attached stream
-----------------------------------------------------------------------------------------

/-- Child integration attaches every fresh supplied stream to its successful producer.
Witness: group/task registration preserves the producer lookup and stream registry;
the final stream stage therefore cannot drop the descriptor or miss the producer.
-/
theorem State.maybeIntegrateWork_fresh_stream_attached {queue : State} {occurrence node}
    (found : queue.taskNode? occurrence = some node) (work : Work) {stream : Stream}
    (member : stream ∈ work.streams) (absent : queue.stream? stream.node.key = none)
    : ∃ next,
        (queue.maybeIntegrateWork work (some occurrence)).1.taskNode? occurrence
          = some next
        ∧ next.task = node.task
        ∧ next.value = node.value
        ∧ stream.node.key ∈ next.childStreams := by
  have grouped : (queue.addGroups work.groups).1.taskNode? occurrence = some node := by
    simpa only [State.taskNode?, State.addGroups_taskNodes] using found
  have loop (tasks : List Task) (current : State)
      (lookup : current.taskNode? occurrence = some node)
      : (tasks.foldl State.addTask current).taskNode? occurrence = some node := by
    induction tasks generalizing current with
    | nil => exact lookup
    | cons task rest ih => exact ih _ (State.addTask_taskNode?_of_some lookup task)
  have attached := loop work.tasks _ grouped
  apply State.addStreams_fresh_child_attached attached work.streams member
  simpa only [State.stream?,
    fold_projection State.streams State.addTask State.addTask_streams,
    State.addGroups_streams]
    using absent

/-- A fresh matched object input cannot lose a supplied stream during preparation.
Witness: generated replay proves absence from the old registry; installing the value and
integrating its children attaches the stream to that exact value-bearing producer lookup.
Publication/release of the retained link is a separate subsequent proof obligation.
-/
theorem ExecutedWork.taskSuccess_prepared_childStream
    {work before occurrence result node stream} (generated : ExecutedWork work)
    (valid : ValidGraphEvents work before)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (fresh : (GraphEvent.taskSuccess occurrence result).Fresh before)
    (found
      : ((State.initialize (Work.fromExecution work)).replayGraphEvents before).taskNode?
          occurrence
        = some node)
    (member : stream ∈ result.work.streams)
    : let queue := (State.initialize (Work.fromExecution work)).replayGraphEvents before
      ∃ next,
        ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1.taskNode?
            occurrence
          = some next
        ∧ next.task = node.task
        ∧ next.value = some result.value
        ∧ stream.node.key ∈ next.childStreams := by
  exact State.maybeIntegrateWork_fresh_stream_attached
    (State.putTaskNode_value_lookup found result.value) result.work member
    (generated.replayGraphEvents_taskChildStream_absent valid matching fresh member)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
