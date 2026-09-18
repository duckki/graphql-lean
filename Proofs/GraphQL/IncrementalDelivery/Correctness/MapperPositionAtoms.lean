import Proofs.GraphQL.IncrementalDelivery.Correctness.WirePositionAtoms
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkPatchShapes
import Proofs.GraphQL.IncrementalDelivery.Correctness.NoticeMetadata

/-! The actual mapper encodes every absolute data atom with its stable wire ID. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- One object entry retains its absolute attachment under the allocated owner ID.
Witness: ensureID correctness and exact reconstruction from the owner's subPath.
-/
theorem getIncrementalEntry_positionAtoms {paths : Nat → ResponsePath}
    (node : DeliveryNode) (value : GroupValue) (ids : IDState)
    (path : paths node.key = node.path)
    (absolute : node.path ++ value.path.drop node.path.length = value.path)
    : EntryPositionAtoms paths
        ((getIncrementalEntry (m := StateM IDState) node value ensureID).run ids).2
        ((getIncrementalEntry (m := StateM IDState) node value ensureID).run ids).1
        [.object value.path value.data] := by
  have encoded := EntryPositionAtoms.object (paths := paths)
    (data := value.data) (errors := value.errors)
    (subPath := value.path.drop node.path.length) (ensureID_spec node ids).2
  simpa only [getIncrementalEntry, StateT.run, StateT.bind, StateT.pure, bind, pure,
    path, absolute] using encoded

/-- Mapping an ordered object-value list encodes every absolute object atom in order.
Witness: mapM induction and transport of the first ID through subsequent allocations.
-/
theorem getIncrementalEntries_positionAtoms {paths : Nat → ResponsePath}
    (node : DeliveryNode) (values : List GroupValue) (ids : IDState)
    (shape : EventPatchShape paths (.groupValues node values))
    : let action :=
        fun value => getIncrementalEntry (m := StateM IDState) node value ensureID
      EntriesPositionAtoms paths ((values.mapM action).run ids).2
        ((values.mapM action).run ids).1
        (values.map (fun value => PositionAtom.object value.path value.data)) := by
  let action := fun value => getIncrementalEntry (m := StateM IDState) node value ensureID
  change EntriesPositionAtoms paths ((values.mapM action).run ids).2
    ((values.mapM action).run ids).1 _
  induction values generalizing ids with
  | nil => exact .nil
  | cons value rest ih =>
      have head := getIncrementalEntry_positionAtoms node value ids shape.1
        (shape.2 value (by simp))
      have tailShape : EventPatchShape paths (.groupValues node rest) :=
        ⟨shape.1, fun value member => shape.2 value (by simp [member])⟩
      have tail := ih ((action value).run ids).2 tailShape
      have preserved := mapM_preserves action (getIncrementalEntry_preserves node)
        rest ((action value).run ids).2
      have encoded := EntriesPositionAtoms.cons (head.mono preserved) tail
      cases first : action value ids with
      | mk entry middle =>
          cases remaining : rest.mapM action middle with
          | mk entries final =>
              simp only [action] at first remaining
              simpa only [List.mapM_cons, List.map_cons, StateT.run, StateT.bind,
                StateT.pure, bind, pure, action, first, remaining, List.singleton_append]
                using encoded

/-- One actual event-mapper step preserves previous data atoms and appends its own.
Witness: object list mapping, stable stream IDs, or unchanged entries for controls.
-/
theorem eventLoop_positionAtoms {paths : Nat → ResponsePath} (event : WorkEvent)
    (initial update : IncrementalStreamUpdateResult) (ids next : IDState)
    {prior : List PositionAtom} (shape : EventPatchShape paths event)
    (encoded : EntriesPositionAtoms paths ids initial.incremental prior)
    (mapped : (eventLoop event initial).run ids = (.yield update, next))
    : EntriesPositionAtoms paths next update.incremental
        (prior ++ eventPositionAtoms event) := by
  have preserved : Preserves ids next := by
    obtain ⟨other, state, equal, facts⟩ := eventLoop_spec event initial ids
    have same := equal.symm.trans mapped
    injection same with output states
    injection output with outputs
    subst state
    exact facts.preserves
  have previous := encoded.mono preserved
  cases event with
  | groupValues node values =>
      let action := fun value => getIncrementalEntry (m := StateM IDState) node value ensureID
      have fresh := getIncrementalEntries_positionAtoms node values ids shape
      cases entriesAt : (values.mapM action).run ids with
      | mk entries final =>
          change EntriesPositionAtoms paths ((values.mapM action).run ids).2
            ((values.mapM action).run ids).1 _ at fresh
          rw [entriesAt] at fresh
          simp only [StateT.run, action] at entriesAt
          simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure,
            entriesAt] at mapped
          cases mapped
          exact previous.append fresh
  | streamValues node values groups streams =>
      cases allocated : ensureID node ids with
      | mk id middle =>
          have known := (ensureID_spec node ids).2
          rw [allocated] at known
          cases pending
                : (getPendingEntry (m := StateM IDState) groups streams ensureID).run
                    middle with
          | mk notices final =>
              have fresh : EntriesPositionAtoms paths final
                  [.list id (values.map StreamValue.item) ((values.map StreamValue.errors).sum)]
                  (eventPositionAtoms (.streamValues node values groups streams)) := by
                have stream := EntryPositionAtoms.list (paths := paths)
                  (data := values.map StreamValue.item)
                  (errors := (values.map StreamValue.errors).sum)
                  ((getPendingEntry_of_eq pending).1 _ _ known)
                  (by simpa using shape.2)
                simpa only [eventPositionAtoms, List.map_map, Function.comp_def, shape.1,
                  List.append_nil]
                  using EntriesPositionAtoms.cons stream .nil
              simp only [StateT.run] at pending
              simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure,
                allocated, pending] at mapped
              cases mapped
              exact previous.append fresh
  | groupSuccess node groups streams | groupFailure node errors | streamSuccess node
  | streamFailure node errors | workQueueTermination =>
      simp only [eventLoop, StateT.run, StateT.bind, StateT.pure, bind, pure] at mapped
      all_goals
        repeat first | split at mapped | cases mapped
        simpa only [eventPositionAtoms, List.append_nil] using previous

/-- Finite event mapping concatenates the exact encoded absolute atoms, by loop induction.
-/
theorem loop_positionAtoms {paths : Nat → ResponsePath}
    (events : List WorkEvent) (initial : IncrementalStreamUpdateResult) (ids : IDState)
    {prior : List PositionAtom} (shapes : ∀ event ∈ events, EventPatchShape paths event)
    (encoded : EntriesPositionAtoms paths ids initial.incremental prior)
    : EntriesPositionAtoms paths ((forIn events initial eventLoop).run ids).2
        ((forIn events initial eventLoop).run ids).1.incremental
        (prior ++ events.flatMap eventPositionAtoms) := by
  induction events generalizing initial ids prior with
  | nil =>
      simpa only [List.forIn_nil, StateT.run, StateT.pure, pure, List.flatMap_nil,
        List.append_nil] using encoded
  | cons event rest ih =>
      obtain ⟨middle, next, mapped, _⟩ := eventLoop_spec event initial ids
      have current := eventLoop_positionAtoms event initial middle ids next
        (shapes event (by simp)) encoded mapped
      have tail := ih middle next (fun event member => shapes event (by simp [member])) current
      simp only [StateT.run] at mapped tail
      simpa [List.forIn_cons, StateT.run, StateT.bind, bind, mapped, List.append_assoc]
        using tail

/-- Public work-batch mapping encodes precisely the batch's absolute atoms. -/
theorem mapWorkEventBatch_positionAtoms {paths : Nat → ResponsePath}
    (events : List WorkEvent) (ids : IDState)
    (shapes : ∀ event ∈ events, EventPatchShape paths event)
    : EntriesPositionAtoms paths ((mapWorkEventBatch events).run ids).2
        ((mapWorkEventBatch events).run ids).1.incremental
        (events.flatMap eventPositionAtoms) := by
  rw [mapWorkEventBatch_loop]
  simpa using loop_positionAtoms events { hasNext := true } ids shapes EntriesPositionAtoms.nil

/-- Finite mapped batches retain the complete ordered data atom sequence in final IDs.
Witness: batch induction and stable allocation through later supplied batches.
-/
theorem mappedTrace_positionAtoms {paths : Nat → ResponsePath}
    (batches : List (List WorkEvent)) (ids : IDState)
    (shapes : ∀ event ∈ batches.flatten, EventPatchShape paths event)
    : EntriesPositionAtoms paths (finalIDs batches ids)
        ((mappedTrace batches ids).flatMap IncrementalStreamUpdateResult.incremental)
        (batches.flatten.flatMap eventPositionAtoms) := by
  induction batches generalizing ids with
  | nil => exact .nil
  | cons batch rest ih =>
      have head := mapWorkEventBatch_positionAtoms batch ids
        (fun event member => shapes event (List.mem_append_left _ member))
      cases mapped : (mapWorkEventBatch batch).run ids with
      | mk update next =>
          simp only [mapped] at head
          have tail := ih next (fun event member => shapes event (List.mem_append_right _ member))
          simpa only [mappedTrace, finalIDs, mapped, List.flatMap_cons, List.flatten_cons,
            List.flatMap_append]
            using (head.mono (mappedTrace_spec rest next).1).append tail

end GraphQL.IncrementalDelivery.Correctness
