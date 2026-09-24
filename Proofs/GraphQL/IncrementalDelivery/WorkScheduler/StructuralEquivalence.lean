import GraphQL.IncrementalDelivery.WorkScheduler

/-! Structural lookup agrees with the former occurrence judgments for arbitrary Work. -/

namespace GraphQL.IncrementalDelivery.WorkScheduler
open GraphQL.IncrementalDelivery.Execution

/-- Address traversal composes by retaining the consumed absolute route. -/
theorem locateWork.go_append (route : Address) (location : WorkLocation)
    (left right : Address)
    : go route location (left ++ right)
      = (go route location left).bind (fun next => go (route ++ left) next right) := by
  induction left generalizing route location with
  | nil => simp [go]
  | cons index rest ih =>
      simp [go, ih, Option.bind_assoc, List.append_assoc]

/-- A final edge is looked up after its entire route, by traversal composition. -/
theorem locateWork_snoc (work : Work) (address : Address) (index : Nat)
    : locateWork work (address ++ [index])
      = (locateWork work address).bind
          (fun location => location.child? address index) := by
  simp [locateWork, locateWork.go_append, locateWork.go]

namespace StructuralEquivalence

/-- (Located root address current producer owners) finds current at address in root;
producer is its generating task (none at the root), and owners are enclosing defer keys.
-/
inductive Located (root : Work) : Address → Work → Option Occurrence → Keys → Prop where
  | root : Located root [] root none []
  | left {address left right producer owners}
    (located : Located root address (.combine left right) producer owners)
    : Located root (address ++ [0]) left producer owners
  | right {address left right producer owners}
    (located : Located root address (.combine left right) producer owners)
    : Located root (address ++ [1]) right producer owners
  | executionGroup {address groups path result children producer owners}
    (located
      : Located root address (.executionGroup groups path result children) producer
          owners)
    : Located root (address ++ [0]) children (some (.executionGroup address))
        (groups.map (fun group => group.node.key))
  | item {address node items producer owners index result children}
    (located : Located root address (.stream node items) producer owners)
    (entry : items[index]? = some (result, children))
    : Located root (address ++ [index]) children (some (.item address index)) []

/-- (TaskAt work occurrence owners producer payload) identifies a task in work by its
structural occurrence, contributing owner keys, optional producer occurrence, and fixed
payload.
-/
inductive TaskAt (work : Work)
    : Occurrence → Keys → Option Occurrence → Payload → Prop where
  | executionGroup {address groups path result children producer owners}
    (located
      : Located work address (.executionGroup groups path result children) producer
          owners)
    : TaskAt work (.executionGroup address) (groups.map (fun group => group.node.key))
        producer (.object path result)
  | item {address node items producer owners index result children}
    (located : Located work address (.stream node items) producer owners)
    (entry : items[index]? = some (result, children))
    : TaskAt work (.item address index) [node.key] producer (.item node result)

/-- (NodeAt work node kind dependencies birth) identifies node's metadata in work: kind is
defer/stream, dependencies are ancestor or enclosing-owner keys, and birth is its optional
producer occurrence.
-/
inductive NodeAt (work : Work)
    : DeliveryNode → NodeKind → Keys → Option Occurrence → Prop where
  | group {address groups path result children producer owners group}
    (located
      : Located work address (.executionGroup groups path result children) producer
          owners)
    (member : group ∈ groups)
    : NodeAt work group.node .group (group.ancestors.map DeliveryNode.key) producer
  | stream {address node items producer owners}
    (located : Located work address (.stream node items) producer owners)
    : NodeAt work node .stream owners producer

/-- One successful lookup edge is exactly one former navigation rule. -/
theorem Located.child {root address current producer owners index next}
    (h : Located root address current producer owners)
    (step : WorkLocation.child? ⟨current, producer, owners⟩ address index = some next)
    : Located root (address ++ [index]) next.current next.producer next.owners := by
  cases current with
  | empty => simp [WorkLocation.child?] at step
  | combine left right =>
      cases index with
      | zero =>
          simp [WorkLocation.child?] at step
          subst next
          exact .left h
      | succ index =>
          cases index with
          | zero =>
              simp [WorkLocation.child?] at step
              subst next
              exact .right h
          | succ index => simp [WorkLocation.child?] at step
  | executionGroup groups path result children =>
      cases index with
      | zero =>
          simp [WorkLocation.child?] at step
          subst next
          exact .executionGroup h
      | succ index => simp [WorkLocation.child?] at step
  | stream node items =>
      simp only [WorkLocation.child?, Option.map_eq_some_iff] at step
      obtain ⟨⟨result, children⟩, entry, rfl⟩ := step
      exact .item h entry

/-- Every former location is returned by the functional lookup, by navigation induction.
-/
theorem Located.toCurrent {root address current producer owners}
    (h : Located root address current producer owners)
    : WorkScheduler.Located root address current producer owners := by
  induction h with
  | root => rfl
  | left _ ih | right _ ih | executionGroup _ ih =>
      unfold WorkScheduler.Located at ih ⊢
      simp [locateWork_snoc, ih, WorkLocation.child?]
  | item _ entry ih =>
      unfold WorkScheduler.Located at ih ⊢
      simp [locateWork_snoc, ih, WorkLocation.child?, entry]

/-- A successful traversal extends a former location by each remaining edge. -/
theorem located_go {root route location rest next}
    (h : Located root route location.current location.producer location.owners)
    (found : locateWork.go route location rest = some next)
    : Located root (route ++ rest) next.current next.producer next.owners := by
  induction rest generalizing route location with
  | nil =>
      simp only [locateWork.go, Option.some.injEq] at found
      subst next
      simpa using h
  | cons index rest ih =>
      change (location.child? route index).bind
        (fun child => locateWork.go (route ++ [index]) child rest) = some next at found
      obtain ⟨child, step, found⟩ := Option.bind_eq_some_iff.mp found
      have extended := h.child step
      simpa [List.append_assoc] using ih extended found

/-- Every successful lookup has a former location witness, by edge-by-edge traversal. -/
theorem located_of_current {root address current producer owners}
    (h : WorkScheduler.Located root address current producer owners)
    : Located root address current producer owners := by
  simpa using located_go (location := ⟨root, none, []⟩) Located.root h

/-- The two location predicates agree without assumptions on raw work. -/
theorem located_iff {root address current producer owners}
    : Located root address current producer owners
      ↔ WorkScheduler.Located root address current producer owners :=
  ⟨Located.toCurrent, located_of_current⟩

/-- Former task witnesses produce the same lookup-based owners and payload. -/
theorem TaskAt.toCurrent {work occurrence owners producer payload}
    (h : TaskAt work occurrence owners producer payload)
    : WorkScheduler.TaskAt work occurrence owners producer payload := by
  cases h with
  | executionGroup located => exact ⟨_, _, _, _, _, located.toCurrent, rfl, rfl⟩
  | item located entry => exact ⟨_, _, _, _, _, located.toCurrent, entry, rfl, rfl⟩

/-- The functional task predicate recovers a former witness by occurrence case analysis.
-/
theorem taskAt_of_current {work occurrence owners producer payload}
    (h : WorkScheduler.TaskAt work occurrence owners producer payload)
    : TaskAt work occurrence owners producer payload := by
  cases occurrence with
  | executionGroup address =>
      obtain ⟨groups, path, result, children, enclosing, located, rfl, rfl⟩ := h
      exact .executionGroup (located_of_current located)
  | item address index =>
      obtain ⟨node, items, enclosing, result, children, located, entry, rfl, rfl⟩ := h
      exact .item (located_of_current located) entry

/-- Structural task identity, ownership, and payload are unchanged for all work. -/
theorem taskAt_iff {work occurrence owners producer payload}
    : TaskAt work occurrence owners producer payload
      ↔ WorkScheduler.TaskAt work occurrence owners producer payload :=
  ⟨TaskAt.toCurrent, taskAt_of_current⟩

/-- Former node descriptors remain witnesses of the existential location predicate. -/
theorem NodeAt.toCurrent {work node kind dependencies birth}
    (h : NodeAt work node kind dependencies birth)
    : WorkScheduler.NodeAt work node kind dependencies birth := by
  cases h with
  | group located member =>
      exact ⟨_, _, _, _, _, _, _, located.toCurrent, member, rfl, rfl⟩
  | stream located => exact ⟨_, _, located.toCurrent⟩

/-- Each lookup-based descriptor recovers a former witness, without deduplicating keys. -/
theorem nodeAt_of_current {work node kind dependencies birth}
    (h : WorkScheduler.NodeAt work node kind dependencies birth)
    : NodeAt work node kind dependencies birth := by
  cases kind with
  | group =>
      obtain ⟨address, groups, path, result, children, enclosing, group,
        located, member, rfl, rfl⟩ := h
      exact .group (located_of_current located) member
  | stream =>
      obtain ⟨address, items, located⟩ := h
      exact .stream (located_of_current located)

/-- Every node occurrence and its metadata is preserved, even when keys repeat. -/
theorem nodeAt_iff {work node kind dependencies birth}
    : NodeAt work node kind dependencies birth
      ↔ WorkScheduler.NodeAt work node kind dependencies birth :=
  ⟨NodeAt.toCurrent, nodeAt_of_current⟩

end StructuralEquivalence

/-- Root lookup retains the initial context; witness: computation. -/
theorem Located.root {root} : Located root [] root none [] := rfl

/-- Combine-left lookup preserves context; witness: final-edge computation. -/
theorem Located.left {root address left right producer owners}
    (h : Located root address (.combine left right) producer owners)
    : Located root (address ++ [0]) left producer owners :=
  (StructuralEquivalence.Located.left
    (StructuralEquivalence.located_of_current h)).toCurrent

/-- Combine-right lookup preserves context; witness: final-edge computation. -/
theorem Located.right {root address left right producer owners}
    (h : Located root address (.combine left right) producer owners)
    : Located root (address ++ [1]) right producer owners :=
  (StructuralEquivalence.Located.right
    (StructuralEquivalence.located_of_current h)).toCurrent

/-- Execution-group child lookup records its actual producer and owners; witness:
navigation. -/
theorem Located.executionGroup {root address groups path result children producer owners}
    (h
      : Located root address (.executionGroup groups path result children) producer
          owners)
    : Located root (address ++ [0]) children (some (.executionGroup address))
        (groups.map (fun group => group.node.key)) :=
  (StructuralEquivalence.Located.executionGroup
    (StructuralEquivalence.located_of_current h)).toCurrent

/-- Item-child lookup records the indexed producer; witness: the selected list entry. -/
theorem Located.item {root address node items producer owners index result children}
    (h : Located root address (.stream node items) producer owners)
    (entry : items[index]? = some (result, children))
    : Located root (address ++ [index]) children (some (.item address index)) [] :=
  (StructuralEquivalence.Located.item
    (StructuralEquivalence.located_of_current h) entry).toCurrent

/-- A located execution group gives its task descriptor; witness: existential
introduction. -/
theorem TaskAt.executionGroup {work address groups path result children producer owners}
    (located
      : Located work address (.executionGroup groups path result children) producer
          owners)
    : TaskAt work (.executionGroup address) (groups.map (fun group => group.node.key))
        producer (.object path result) :=
  ⟨_, _, _, _, _, located, rfl, rfl⟩

/-- A located stream entry gives its task descriptor; witness: the indexed entry. -/
theorem TaskAt.item {work address node items producer owners index result children}
    (located : Located work address (.stream node items) producer owners)
    (entry : items[index]? = some (result, children))
    : TaskAt work (.item address index) [node.key] producer (.item node result) :=
  ⟨_, _, _, _, _, located, entry, rfl, rfl⟩

/-- Every defer-group member supplies a node descriptor; witness: its containing location.
-/
theorem NodeAt.group {work address groups path result children producer owners group}
    (located
      : Located work address (.executionGroup groups path result children) producer
          owners)
    (member : group ∈ groups)
    : NodeAt work group.node .group (group.ancestors.map DeliveryNode.key) producer :=
  ⟨_, _, _, _, _, _, _, located, member, rfl, rfl⟩

/-- A stream supplies its descriptor with enclosing owners; witness: its location. -/
theorem NodeAt.stream {work address node items producer owners}
    (located : Located work address (.stream node items) producer owners)
    : NodeAt work node .stream owners producer :=
  ⟨_, _, located⟩

end GraphQL.IncrementalDelivery.WorkScheduler
