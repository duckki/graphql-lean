import GraphQL.IncrementalDelivery.Correctness
import Proofs.GraphQL.IncrementalDelivery.WorkQueueSemantics.BatchLifecycle

/-! Stable wire identities and exact ordered node/ID correspondence. These proofs
do not require numerical ID freshness: lookup stability suffices for liveness.
-/

namespace GraphQL.IncrementalDelivery.Correctness.MapperIdentity

open GraphQL.IncrementalDelivery.Execution
open WorkQueueSemantics

def Known (state : IDState) (ref : NodeRef) (id : String) : Prop :=
  state.ids.find? (fun entry => entry.1 == ref) = some (ref, id)

def Preserves (before after : IDState) : Prop :=
  ∀ ref id, Known before ref id → Known after ref id

/-- A state preserves its own ref lookups, by identity. -/
theorem Preserves.refl (state : IDState) : Preserves state state := fun _ _ h => h

/-- Lookup preservation composes through the intermediate state. -/
theorem Preserves.trans {before middle after : IDState}
    (left : Preserves before middle) (right : Preserves middle after)
    : Preserves before after :=
  fun ref id h => right ref id (left ref id h)

/-- One ref has one ID in a state, by uniqueness of the lookup result. -/
theorem Known.unique {state : IDState} {ref : NodeRef} {left right : String}
    (hl : Known state ref left) (hr : Known state ref right)
    : left = right := by
  have he := hl.symm.trans hr
  exact congrArg Prod.snd (Option.some.inj he)

/-- Allocation preserves old lookups and records the requested ref, by lookup cases. -/
theorem ensureID_spec (node : DeliveryNode) (state : IDState)
    : Preserves state (ensureID node state).2
      ∧ Known (ensureID node state).2 node.ref (ensureID node state).1 := by
  cases h : state.ids.find? (fun entry => entry.1 == node.ref) with
  | none =>
      simp only [ensureID, h]
      constructor
      · intro ref id known
        change state.ids.find? (fun entry => entry.1 == ref) = some (ref, id) at known
        change (state.ids ++ [(node.ref, toString state.nextID)]).find?
          (fun entry => entry.1 == ref) = some (ref, id)
        rw [List.find?_append, known]
        rfl
      · simp [Known, List.find?_append, h]
  | some pair =>
      obtain ⟨ref, id⟩ := pair
      have predicate := List.find?_some h
      have hk : ref = node.ref := by simpa using predicate
      subst ref
      exact ⟨
        by simpa [ensureID, h] using Preserves.refl state,
        by simp only [ensureID, h]; exact h
      ⟩

/-- Preserve occurrences and order, not just membership: safety needs to rule out
duplicated output entries even when membership sets would remain unchanged.
-/
inductive Encodes (state : IDState) : List Nat → List String → Prop where
  | nil : Encodes state [] []
  | cons {ref id refs ids} (known : Known state ref id) (tail : Encodes state refs ids)
    : Encodes state (ref :: refs) (id :: ids)

/-- Every encoded ID has a contributing ref, by induction on the encoding. -/
theorem Encodes.fromID {state : IDState} {refs : List Nat} {ids : List String}
    (h : Encodes state refs ids)
    : ∀ id ∈ ids, ∃ ref ∈ refs, Known state ref id := by
  induction h with
  | nil => simp
  | @cons ref id refs ids known tail ih =>
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨ref, List.mem_cons_self, known⟩
      · obtain ⟨ref, hk, known⟩ := ih value hv
        exact ⟨ref, List.mem_cons_of_mem _ hk, known⟩

/-- Every encoded ref has an ID, by induction on the encoding. -/
theorem Encodes.fromRef {state : IDState} {refs : List Nat} {ids : List String}
    (h : Encodes state refs ids)
    : ∀ ref ∈ refs, ∃ id ∈ ids, Known state ref id := by
  induction h with
  | nil => simp
  | @cons ref id refs ids known tail ih =>
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨id, List.mem_cons_self, known⟩
      · obtain ⟨id, hi, known⟩ := ih value hv
        exact ⟨id, List.mem_cons_of_mem _ hi, known⟩

/-- One known lookup encodes the singleton ref/ID pair. -/
theorem Encodes.singleton {state : IDState} {ref : NodeRef} {id : String}
    (h : Known state ref id)
    : Encodes state [ref] [id] :=
  .cons h .nil

/-- Lookup preservation transports the entire encoding, by induction. -/
theorem Encodes.mono {before after : IDState} {refs : List Nat} {ids : List String}
    (h : Encodes before refs ids) (preserves : Preserves before after)
    : Encodes after refs ids := by
  induction h with
  | nil => exact .nil
  | cons known tail ih => exact .cons (preserves _ _ known) ih

/-- Concatenated ref/ID sequences remain encoded, by induction on the first list. -/
theorem Encodes.append {state : IDState} {left right : List Nat} {ids more : List String}
    (hl : Encodes state left ids) (hr : Encodes state right more)
    : Encodes state (left ++ right) (ids ++ more) := by
  induction hl with
  | nil => exact hr
  | cons known tail ih => exact .cons known ih

/-- Mapping preserves old lookups, by induction and sequential preservation. -/
theorem mapM_preserves {α β : Type} (action : α → StateM IDState β)
    (h : ∀ value state, Preserves state ((action value).run state).2)
    (values : List α) (state : IDState)
    : Preserves state ((values.mapM action).run state).2 := by
  induction values generalizing state with
  | nil => exact .refl state
  | cons value rest ih =>
      cases ha : action value state with
      | mk first middle =>
          cases hb : rest.mapM action middle with
          | mk tail final =>
              simpa [List.mapM_cons, StateT.run, StateT.bind, StateT.pure, bind, pure, ha,
                hb]
                using (h value state).trans (ih ((action value).run state).2)

/-- Mapping retains ordered ref/ID occurrences, by induction over allocation. -/
theorem mapM_encodes {α β : Type} (action : α → StateM IDState β)
    (refFor : α → Nat) (idFor : β → String)
    (h
      : ∀ value state,
          Preserves state ((action value).run state).2
          ∧ Known ((action value).run state).2 (refFor value)
              (idFor ((action value).run state).1))
    (values : List α) (state : IDState)
    : Preserves state ((values.mapM action).run state).2
      ∧ Encodes ((values.mapM action).run state).2 (values.map refFor)
          (((values.mapM action).run state).1.map idFor) := by
  induction values generalizing state with
  | nil => exact ⟨.refl state, .nil⟩
  | cons value rest ih =>
      obtain ⟨hp, hk⟩ := h value state
      obtain ⟨tp, tk⟩ := ih ((action value).run state).2
      have known := tp _ _ hk
      cases ha : action value state with
      | mk first middle =>
          cases hb : rest.mapM action middle with
          | mk tail final =>
              simpa [List.mapM_cons, StateT.run, StateT.bind, StateT.pure, bind, pure, ha,
                hb]
                using And.intro (hp.trans tp) ((Encodes.singleton known).append tk)

/-- Pending notices encode their ordered node refs, using the allocation map. -/
theorem getPendingEntry_spec (groups streams : List DeliveryNode) (state : IDState)
    : let (pending, next) :=
        (getPendingEntry (m := StateM IDState) groups streams ensureID).run state
      Preserves state next
      ∧ Encodes next ((groups ++ streams).map DeliveryNode.ref)
          (pending.map IncrementalPendingNotice.id) := by
  apply mapM_encodes
  intro node state
  exact ensureID_spec node state

/-- Completion retains the stable node ID, using the allocation specification. -/
theorem getCompletedEntry_spec (node : DeliveryNode) (errors : Nat) (state : IDState)
    : let (completed, next) :=
        (getCompletedEntry (m := StateM IDState) node errors ensureID).run state
      Preserves state next ∧ Known next node.ref completed.id :=
  ensureID_spec node state

/-- An explicit pending-allocation result inherits the ordered encoding witness. -/
theorem getPendingEntry_of_eq {groups streams : List DeliveryNode} {state next : IDState}
    {pending : List IncrementalPendingNotice}
    (h
      : (getPendingEntry (m := StateM IDState) groups streams ensureID).run state
        = (pending, next))
    : Preserves state next
      ∧ Encodes next ((groups ++ streams).map DeliveryNode.ref)
          (pending.map IncrementalPendingNotice.id) := by
  have fact := getPendingEntry_spec groups streams state
  rw [h] at fact
  exact fact

/-- An explicit completion result inherits its stable lookup witness. -/
theorem getCompletedEntry_of_eq {node : DeliveryNode} {errors : Nat}
    {state next : IDState} {completed : IncrementalCompletionNotice}
    (h
      : (getCompletedEntry (m := StateM IDState) node errors ensureID).run state
        = (completed, next))
    : Preserves state next ∧ Known next node.ref completed.id := by
  have fact := getCompletedEntry_spec node errors state
  rw [h] at fact
  exact fact

/-- Object patch construction preserves old IDs, by its single allocation. -/
theorem getIncrementalEntry_preserves (node : DeliveryNode) (value : ExecutionGroupValue)
    (state : IDState)
    : Preserves state
        ((getIncrementalEntry (m := StateM IDState) node value ensureID).run state).2 :=
  (ensureID_spec node state).1

end GraphQL.IncrementalDelivery.Correctness.MapperIdentity
