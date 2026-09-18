import GraphQL.IncrementalDelivery.Correctness
import Proofs.GraphQL.IncrementalDelivery.WorkScheduler.BatchLifecycle

/-! Stable wire identities and exact ordered node/ID correspondence. These proofs
do not require numerical ID freshness: lookup stability suffices for liveness.
-/

namespace GraphQL.IncrementalDelivery.Correctness.MapperIdentity

open GraphQL.IncrementalDelivery.Execution
open WorkScheduler

def Known (state : IDState) (key : Nat) (id : String) : Prop :=
  state.ids.find? (fun entry => entry.1 == key) = some (key, id)

def Preserves (before after : IDState) : Prop :=
  ∀ key id, Known before key id → Known after key id

/-- A state preserves its own key lookups, by identity. -/
theorem Preserves.refl (state : IDState) : Preserves state state := fun _ _ h => h

/-- Lookup preservation composes through the intermediate state. -/
theorem Preserves.trans {before middle after : IDState}
    (left : Preserves before middle) (right : Preserves middle after)
    : Preserves before after :=
  fun key id h => right key id (left key id h)

/-- One key has one ID in a state, by uniqueness of the lookup result. -/
theorem Known.unique {state : IDState} {key : Nat} {left right : String}
    (hl : Known state key left) (hr : Known state key right)
    : left = right := by
  have he := hl.symm.trans hr
  exact congrArg Prod.snd (Option.some.inj he)

/-- Allocation preserves old lookups and records the requested key, by lookup cases. -/
theorem ensureID_spec (node : DeliveryNode) (state : IDState)
    : Preserves state (ensureID node state).2
      ∧ Known (ensureID node state).2 node.key (ensureID node state).1 := by
  cases h : state.ids.find? (fun entry => entry.1 == node.key) with
  | none =>
      simp only [ensureID, h]
      constructor
      · intro key id known
        change state.ids.find? (fun entry => entry.1 == key) = some (key, id) at known
        change (state.ids ++ [(node.key, toString state.nextID)]).find?
          (fun entry => entry.1 == key) = some (key, id)
        rw [List.find?_append, known]
        rfl
      · simp [Known, List.find?_append, h]
  | some pair =>
      obtain ⟨key, id⟩ := pair
      have predicate := List.find?_some h
      have hk : key = node.key := by simpa using predicate
      subst key
      exact ⟨
        by simpa [ensureID, h] using Preserves.refl state,
        by simp only [ensureID, h]; exact h
      ⟩

/-- Preserve occurrences and order, not just membership: safety needs to rule out
duplicated output entries even when membership sets would remain unchanged.
-/
inductive Encodes (state : IDState) : List Nat → List String → Prop where
  | nil : Encodes state [] []
  | cons {key id keys ids} (known : Known state key id) (tail : Encodes state keys ids)
    : Encodes state (key :: keys) (id :: ids)

/-- Every encoded ID has a contributing key, by induction on the encoding. -/
theorem Encodes.fromID {state : IDState} {keys : List Nat} {ids : List String}
    (h : Encodes state keys ids)
    : ∀ id ∈ ids, ∃ key ∈ keys, Known state key id := by
  induction h with
  | nil => simp
  | @cons key id keys ids known tail ih =>
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨key, List.mem_cons_self, known⟩
      · obtain ⟨key, hk, known⟩ := ih value hv
        exact ⟨key, List.mem_cons_of_mem _ hk, known⟩

/-- Every encoded key has an ID, by induction on the encoding. -/
theorem Encodes.fromKey {state : IDState} {keys : List Nat} {ids : List String}
    (h : Encodes state keys ids)
    : ∀ key ∈ keys, ∃ id ∈ ids, Known state key id := by
  induction h with
  | nil => simp
  | @cons key id keys ids known tail ih =>
      intro value hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨id, List.mem_cons_self, known⟩
      · obtain ⟨id, hi, known⟩ := ih value hv
        exact ⟨id, List.mem_cons_of_mem _ hi, known⟩

/-- One known lookup encodes the singleton key/ID pair. -/
theorem Encodes.singleton {state : IDState} {key : Nat} {id : String}
    (h : Known state key id)
    : Encodes state [key] [id] :=
  .cons h .nil

/-- Lookup preservation transports the entire encoding, by induction. -/
theorem Encodes.mono {before after : IDState} {keys : List Nat} {ids : List String}
    (h : Encodes before keys ids) (preserves : Preserves before after)
    : Encodes after keys ids := by
  induction h with
  | nil => exact .nil
  | cons known tail ih => exact .cons (preserves _ _ known) ih

/-- Concatenated key/ID sequences remain encoded, by induction on the first list. -/
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

/-- Mapping retains ordered key/ID occurrences, by induction over allocation. -/
theorem mapM_encodes {α β : Type} (action : α → StateM IDState β)
    (keyFor : α → Nat) (idFor : β → String)
    (h
      : ∀ value state,
          Preserves state ((action value).run state).2
          ∧ Known ((action value).run state).2 (keyFor value)
              (idFor ((action value).run state).1))
    (values : List α) (state : IDState)
    : Preserves state ((values.mapM action).run state).2
      ∧ Encodes ((values.mapM action).run state).2 (values.map keyFor)
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

/-- Pending notices encode their ordered node keys, using the allocation map. -/
theorem getPendingEntry_spec (groups streams : List DeliveryNode) (state : IDState)
    : let (pending, next) :=
        (getPendingEntry (m := StateM IDState) groups streams ensureID).run state
      Preserves state next
      ∧ Encodes next ((groups ++ streams).map DeliveryNode.key)
          (pending.map IncrementalPendingNotice.id) := by
  apply mapM_encodes
  intro node state
  exact ensureID_spec node state

/-- Completion retains the stable node ID, using the allocation specification. -/
theorem getCompletedEntry_spec (node : DeliveryNode) (errors : Nat) (state : IDState)
    : let (completed, next) :=
        (getCompletedEntry (m := StateM IDState) node errors ensureID).run state
      Preserves state next ∧ Known next node.key completed.id :=
  ensureID_spec node state

/-- An explicit pending-allocation result inherits the ordered encoding witness. -/
theorem getPendingEntry_of_eq {groups streams : List DeliveryNode} {state next : IDState}
    {pending : List IncrementalPendingNotice}
    (h
      : (getPendingEntry (m := StateM IDState) groups streams ensureID).run state
        = (pending, next))
    : Preserves state next
      ∧ Encodes next ((groups ++ streams).map DeliveryNode.key)
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
    : Preserves state next ∧ Known next node.key completed.id := by
  have fact := getCompletedEntry_spec node errors state
  rw [h] at fact
  exact fact

/-- Object patch construction preserves old IDs, by its single allocation. -/
theorem getIncrementalEntry_preserves (node : DeliveryNode) (value : GroupValue)
    (state : IDState)
    : Preserves state
        ((getIncrementalEntry (m := StateM IDState) node value ensureID).run state).2 :=
  (ensureID_spec node state).1

end GraphQL.IncrementalDelivery.Correctness.MapperIdentity
