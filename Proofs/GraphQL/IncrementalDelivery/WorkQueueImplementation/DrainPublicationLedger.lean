import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StoredClosureCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StreamReleaseAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublicationBlockOrder
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.BufferedOwnerConservation
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PublishedMemberships

/-! One publication ledger covers every buffered contribution at every drain closure. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- A simultaneous coverage property over one occurrence-labelled output sequence
-----------------------------------------------------------------------------------------

/-- Every successful carrier in `events` covers its initially buffered contributors.
`queue` is the input state and `published` labels all object values in output order. The
strict event-prefix value count selects the corresponding prefix of those same labels.
This proof-only property does not account for initially missing or unresolved tasks.
-/
def State.BufferedClosuresCovered (queue : State) (published : List ObjectPublication)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ index group groups streams,
    events[index]? = some (.groupSuccess group groups streams)
    → ∀ occurrence node value,
        queue.taskNode? occurrence = some node
        → node.value = some value
        → group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
        → (occurrence, value)
          ∈ published.take
              ((events.take index).flatMap WorkQueueEvent.objectValues).length

/-- Empty output has no completion to justify. Witness: indexed lookup is always absent.
-/
theorem State.BufferedClosuresCovered.nil (queue : State)
    : queue.BufferedClosuresCovered [] [] := by
  intro index group groups streams impossible
  simp at impossible

/-- Coverage composes when earlier execution publishes or retains every buffered value.
Witness: split the selected carrier by its output position and use the exact payload count
to align prefixes of the single concatenated label list. No equality-of-payload argument
is used to identify source occurrences.
-/
theorem State.BufferedClosuresCovered.append_forCarriers {queue next : State}
    {first second left right} (before : queue.BufferedClosuresCovered first left)
    (after : next.BufferedClosuresCovered second right)
    (values : first.map Prod.snd = left.flatMap WorkQueueEvent.objectValues)
    (conserved
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → ∀ group groups streams,
              .groupSuccess group groups streams ∈ right
              → group.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
              → (occurrence, value) ∈ first ∨ next.taskNode? occurrence = some node)
    : queue.BufferedClosuresCovered (first ++ second) (left ++ right) := by
  have size : first.length = (left.flatMap WorkQueueEvent.objectValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  intro index group groups streams selected occurrence node value found stored contributes
  by_cases earlier : index < left.length
  · have atLeft := (List.getElem?_append_left earlier).symm.trans selected
    have count : ((left.take index).flatMap WorkQueueEvent.objectValues).length
        ≤ first.length := by
      have split := congrArg (fun events : List WorkQueueEvent =>
        (events.flatMap WorkQueueEvent.objectValues).length) (List.take_append_drop index left)
      simp only [List.flatMap_append, List.length_append] at split
      omega
    rw [List.take_append_of_le_length (Nat.le_of_lt earlier),
      List.take_append_of_le_length count]
    exact before index group groups streams atLeft occurrence node value found stored contributes
  · have later : left.length ≤ index := by omega
    have atRight := (List.getElem?_append_right later).symm.trans selected
    rw [List.take_append (l₁ := left), List.take_of_length_le later, List.flatMap_append,
      List.length_append, ← size, List.take_append (l₁ := first)]
    simp only [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    rcases conserved occurrence node value found stored group groups streams
        (List.mem_of_getElem? atRight) contributes with published | retained
    · exact List.mem_append_left _ published
    · exact List.mem_append_right _
        (after (index - left.length) group groups streams atRight
          occurrence node value retained stored contributes)

/-- Unconditional buffer retention specializes carrier-specific coverage composition. -/
theorem State.BufferedClosuresCovered.append {queue next : State}
    {first second left right} (before : queue.BufferedClosuresCovered first left)
    (after : next.BufferedClosuresCovered second right)
    (values : first.map Prod.snd = left.flatMap WorkQueueEvent.objectValues)
    (conserved
      : ∀ occurrence node value,
          queue.taskNode? occurrence = some node
          → node.value = some value
          → (occurrence, value) ∈ first ∨ next.taskNode? occurrence = some node)
    : queue.BufferedClosuresCovered (first ++ second) (left ++ right) :=
  before.append_forCarriers after values
    (fun occurrence node value found stored _ _ _ _ _ =>
      conserved occurrence node value found stored)

-----------------------------------------------------------------------------------------
-- The same complete flush selection supplies coverage and value conservation
-----------------------------------------------------------------------------------------

/-- A successful flush simultaneously covers buffered contributors and conserves values.
Witness: one complete executable node selection supplies the fresh ledger, every buffered
membership, and removal. Nonmembers retain their exact lookup. The same labels also
support child-stream release when supplied with the established structural stream facts.
-/
theorem State.PublicationInventory.finishGroupSuccess_bufferedCoverage {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (links : queue.StoredTaskLinks) (group : GroupNode) (live : group ∈ queue.groupNodes)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added (queue.finishGroupSuccess group).2.1
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (occurrence, value) ∈ added
              ∨ (queue.finishGroupSuccess group).1.taskNode? occurrence = some node)
        ∧ (∀ work,
            ExecutedWork work
            → queue.ChildStreamsSettled
            → queue.ChildStreamsMatchWork work
            → StreamReleasePublications work added (queue.finishGroupSuccess group).2.1)
        ∧ (queue.GroupMembershipOrder
            → BlocksFollowRegistrations queue.tasks added
                (queue.finishGroupSuccess group).2.1)
        ∧ queue.StoredOwnersConserved added (queue.finishGroupSuccess group).1
        ∧ ∀ publication ∈ added,
            (queue.finishGroupSuccess group).1.TaskMembershipAbsent publication.1 := by
  obtain ⟨selected, unique, known, output, retained, absent, released, complete, ordered⟩ :=
    queue.finishGroupSuccess_completeSelection group
  obtain ⟨values, final⟩ := inventory.finishGroupSuccess_selected group selected unique known
    output retained absent
  let added := storedPublications selected
  have covered : ∀ occurrence ∈ group.tasks, ∀ node value,
      queue.taskNode? occurrence = some node → node.value = some value
      → (occurrence, value) ∈ added := by
    intro occurrence member node value found stored
    exact List.mem_filterMap.mpr ⟨node, complete occurrence member node found,
      by simp only [stored, Option.map_some, (State.taskNode?_some found).2]⟩
  have conserved : ∀ occurrence node value,
      queue.taskNode? occurrence = some node → node.value = some value
      → (occurrence, value) ∈ added
        ∨ (queue.finishGroupSuccess group).1.taskNode? occurrence = some node := by
    intro occurrence node value found stored
    by_cases member : occurrence ∈ group.tasks
    · exact Or.inl (covered occurrence member node value found stored)
    · exact Or.inr ((queue.finishGroupSuccess_lookup_unselected group member).trans found)
  refine ⟨added, values, final, ?_, conserved, ?_, ?_,
    State.finishGroupSuccess_storedOwnersConserved links group live conserved, ?_⟩
  · intro index owner groups streams selected occurrence node value found stored contributes
    obtain ⟨strict, sameOwner, carrier, strictPrefix⟩ :=
      queue.finishGroupSuccess_index_prefix group selected
    have size : added.length = (strict.flatMap WorkQueueEvent.objectValues).length := by
      simpa only [carrier, List.flatMap_append, List.flatMap_singleton,
        WorkQueueEvent.objectValues, List.append_nil, List.length_map]
        using congrArg List.length values
    rw [strictPrefix, ← size, List.take_length]
    have known := State.taskNode?_some found
    apply covered occurrence _ node value found stored
    rw [← known.2]
    exact links node known.1 (by simp only [stored, Option.isSome_some]) group live
      (sameOwner ▸ contributes)
  · intro work generated settled childLinks
    rw [output, ← storedPublications_values]
    apply StreamReleasePublications.flush
    intro stream member dependencies producer structural
    obtain ⟨node, selectedNode, linked⟩ := released stream member
    have inQueue := (known node selectedNode).1
    have same := childLinks.producer generated inQueue structural linked
    cases stored : node.value with
    | none =>
        have empty := settled node inQueue stored
        simp [empty] at linked
    | some value =>
        refine ⟨
          node.task.occurrence,
          same,
          List.mem_map.mpr ⟨(node.task.occurrence, value), ?_, rfl⟩
        ⟩
        exact List.mem_filterMap.mpr ⟨node, selectedNode, by simp [stored]⟩
  · intro memberships
    rw [output, ← storedPublications_values]
    exact BlocksFollowRegistrations.flush
      ((storedPublications_occurrences_sublist selected).trans
        (ordered.trans (memberships group live)))
  · intro publication member
    obtain ⟨node, selectedNode, occurrenceEq, _⟩ := storedPublications_member member
    rw [← occurrenceEq]
    exact queue.finishGroupSuccess_selectedMembershipAbsent group
      (known node selectedNode).1 (known node selectedNode).2

-----------------------------------------------------------------------------------------
-- One ledger for all successful carriers in a recursive drain
-----------------------------------------------------------------------------------------

/-- An eventual drain carrier's group was already live at the drain's input boundary.
Witness: recover its exact pre-closure state, then trace surviving group records back
through the bounded prefix. Activation can reveal records but never creates group records.
-/
theorem State.drainReadyGroups_go_success_live (fuel : Nat) (queue : State)
    (available : List (Occurrence × Nat) := [])
    {index : Nat} {group : Execution.DeliveryNode}
    {groups streams : List Execution.DeliveryNode}
    (selected
      : (State.drainReadyGroups.go available fuel queue).2.1[index]?
        = some (.groupSuccess group groups streams))
    : ∃ node, queue.groupNode? group.ref = some node := by
  obtain ⟨steps, node, _, _, found, _, _, same, _⟩ :=
    State.drainReadyGroups_go_success_boundary fuel queue available selected
  obtain ⟨old, present, _⟩ :=
    State.drainReadyGroups_go_groupEdgesFrom steps queue available _ _ found
  exact ⟨old, by simpa only [same] using present⟩

/-- The common output ledger is already cleared at each successful flush, before
cached child startup can remove the child record named by its notice.
-/
def State.DrainStartupMembershipsCleared (queue : State) (fuel : Nat)
    (published : List ObjectPublication) (available : List (Occurrence × Nat))
    (prior : List WorkQueueEvent := [])
    : Prop :=
  ∀ steps,
    steps < fuel
    → ∀ node,
        let boundary := State.drainReadyGroups.go available steps queue
        boundary.1.rootGroups.findSome?
            (fun ref => do
              let candidate ← boundary.1.groupNode? ref
              if candidate.pending == 0 then some candidate else none)
          = some node
        → ∀ publication ∈
            published.take
              ((prior ++ boundary.2.1 ++ (boundary.1.finishGroupSuccess node).2.1).flatMap
                WorkQueueEvent.objectValues).length,
            (boundary.1.finishGroupSuccess node).1.TaskMembershipAbsent publication.1

/-- Prepending already-cleared output labels preserves every pre-startup boundary. -/
theorem State.DrainStartupMembershipsCleared.prepend {queue fuel available published}
    (cleared : State.DrainStartupMembershipsCleared queue fuel published available)
    (first : List ObjectPublication) (events : List WorkQueueEvent)
    (size : first.length = (events.flatMap WorkQueueEvent.objectValues).length)
    (absent : ∀ publication ∈ first, queue.TaskMembershipAbsent publication.1)
    : queue.DrainStartupMembershipsCleared fuel (first ++ published) available
        events := by
  intro steps bounded node
  dsimp only
  intro selected publication member
  simp only [List.flatMap_append, List.length_append, ← size, List.take_append,
    List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    Nat.add_assoc] at member
  rcases List.mem_append.mp member with old | fresh
  · exact ((absent publication old).drainReadyGroups_go steps available).finishGroupSuccess node
  · apply cleared steps bounded node selected publication
    simpa only [List.nil_append, List.flatMap_append, List.length_append] using fresh

/-- One full-drain ledger covers every initially buffered contributor at every completion.
Witness: simultaneously induct over exact flush selection, publication conservation, and
strict-prefix coverage. Startup removal retains any value whose contributor closes later;
each successful branch concatenates one shared label list, not per-carrier existentials.
That same list supports child-stream release and conserves buffered owners at every
internal drain prefix, not only at the completed drain's endpoint.
-/
theorem State.PublicationInventory.drainReadyGroups_go_prefixCoverage_withStartup
    {queue : State} {property published}
    (inventory : queue.PublicationInventory property published)
    (links : queue.StoredTaskLinks) (fuel : Nat)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value _ errors member; cases member)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (State.drainReadyGroups.go available fuel queue).2.1.flatMap
              WorkQueueEvent.objectValues
        ∧ (State.drainReadyGroups.go available fuel queue).1.PublicationInventory property
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added
            (State.drainReadyGroups.go available fuel queue).2.1
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner,
                  (State.drainReadyGroups.go available fuel queue).1.groupNode?
                    contributor.ref
                  = some owner)
            → (occurrence, value) ∈ added
              ∨ (State.drainReadyGroups.go available fuel queue).1.taskNode? occurrence
                = some node)
        ∧ (∀ work,
            ExecutedWork work
            → queue.ChildStreamsSettled
            → queue.ChildStreamsMatchWork work
            → StreamReleasePublications work added
                (State.drainReadyGroups.go available fuel queue).2.1)
        ∧ (queue.GroupMembershipOrder
            → BlocksFollowRegistrations queue.tasks added
                (State.drainReadyGroups.go available fuel queue).2.1)
        ∧ (∀ steps,
            steps ≤ fuel
            → queue.StoredOwnersConserved
                (added.take
                  ((State.drainReadyGroups.go available steps queue).2.1.flatMap
                    WorkQueueEvent.objectValues).length)
                (State.drainReadyGroups.go available steps queue).1)
        ∧ (∀ steps,
            steps ≤ fuel
            → ∀ publication ∈
                added.take
                  ((State.drainReadyGroups.go available steps queue).2.1.flatMap
                    WorkQueueEvent.objectValues).length,
                (State.drainReadyGroups.go available steps queue).1.TaskMembershipAbsent
                  publication.1)
        ∧ queue.DrainStartupMembershipsCleared fuel added available := by
  induction fuel generalizing queue published with
  | zero =>
      exact ⟨
        [],
        rfl,
        by simpa only [State.drainReadyGroups.go, List.append_nil] using inventory,
        .nil queue,
        (fun _ _ _ found _ _ => Or.inr found),
        (fun work _ _ _ => StreamReleasePublications.nil work),
        (fun _ => .nil _ _),
        (fun steps bounded => by
          have same : steps = 0 := by omega
          subst steps
          exact .refl queue),
        (by simp),
        (by intro steps bounded; omega)
      ⟩
  | succ fuel ih =>
      unfold State.drainReadyGroups.go
      dsimp only
      split
      · refine ⟨
          [],
          rfl,
          by simpa using inventory,
          .nil queue,
          (fun _ _ _ found _ _ => Or.inr found),
          (fun work _ _ _ => StreamReleasePublications.nil work),
          (fun _ => .nil _ _),
          ?_,
          (by simp),
          (by simp [State.DrainStartupMembershipsCleared])
        ⟩
        intro steps bounded
        cases steps with
        | zero => exact .refl queue
        | succ steps =>
            simp only [*]
            exact .refl queue
      · rename_i group selected
        have found := List.mem_of_find?_eq_some (State.readyGroup_sound selected).1
        obtain ⟨first, firstValues, flushed, firstCoverage, firstConserved, firstStreams,
          firstOrder, firstOwners, firstCleared⟩ :=
          inventory.finishGroupSuccess_bufferedCoverage links group found
        have activated := State.PublicationInventory.mk flushed.unique flushed.provenance
          (flushed.stored.startNewWork (queue.finishGroupSuccess group).2.2 available)
        obtain ⟨later, laterValues, final, laterCoverage, laterConserved, laterStreams,
          laterOrder, laterOwners, laterCleared, laterStartup⟩ :=
          ih activated ((links.finishGroupSuccess group).startNewWork _ available)
        let activatedState := ((queue.finishGroupSuccess group).1.startNewWork
          (queue.finishGroupSuccess group).2.2 available).1
        have own {occurrence node value} (lookup : queue.taskNode? occurrence = some node)
            (stored : node.value = some value) : ∀ errors, (occurrence, errors) ∉ available := by
          have source := (inventory.stored node (State.taskNode?_some lookup).1 value stored).1
          rw [(State.taskNode?_some lookup).2] at source
          exact clean occurrence value source
        have kept : ∀ occurrence node value,
            queue.taskNode? occurrence = some node → node.value = some value
            → ∀ owner groups streams,
                .groupSuccess owner groups streams
                  ∈ (State.drainReadyGroups.go available fuel activatedState).2.1
                → owner.ref ∈ node.task.groups.map Execution.DeliveryNode.ref
                → (occurrence, value) ∈ first
                  ∨ activatedState.taskNode? occurrence = some node := by
          intro occurrence node value lookup stored owner groups streams emitted contributes
          rcases firstConserved occurrence node value lookup stored with published | retained
          · exact .inl published
          · obtain ⟨index, atEvent⟩ := List.mem_iff_getElem?.mp emitted
            obtain ⟨survivor, present⟩ :=
              State.drainReadyGroups_go_success_live fuel activatedState available atEvent
            obtain ⟨contributor, listed, same⟩ := List.mem_map.mp contributes
            exact .inr (State.startNewWork_lookup_existing retained _ available (own lookup stored)
              listed (List.mem_of_find?_eq_some present)
              ((State.groupNode?_ref present).trans same.symm))
        refine ⟨
          first ++ later,
          ?_,
          ?_,
          firstCoverage.append_forCarriers laterCoverage firstValues kept,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_,
          ?_
        ⟩
        · simp only [List.map_append, List.flatMap_append, firstValues, laterValues]
        · simpa only [List.append_assoc] using final
        · intro occurrence node value lookup stored live
          rcases firstConserved occurrence node value lookup stored with earlier | retained
          · exact Or.inl (List.mem_append_left _ earlier)
          · obtain ⟨contributor, listed, owner, present⟩ := live
            obtain ⟨survivor, survives, _⟩ :=
              State.drainReadyGroups_go_groupEdgesFrom fuel activatedState available _ _ present
            have kept := State.startNewWork_lookup_existing retained _ available (own lookup stored)
              listed (List.mem_of_find?_eq_some survives) (State.groupNode?_ref survives)
            exact (laterConserved occurrence node value kept stored
              ⟨contributor, listed, owner, present⟩).imp_left (List.mem_append_right _)
        · intro work generated settled childLinks
          exact (firstStreams work generated settled childLinks).append
            (laterStreams work generated
              ((settled.finishGroupSuccess group).startNewWork _ available)
              ((childLinks.finishGroupSuccess group).startNewWork _ available)) firstValues
        · intro memberships
          have next := laterOrder ((memberships.finishGroupSuccess group).startNewWork _ available)
          rw [State.startNewWork_tasks _ _ available,
            State.finishGroupSuccess_tasks] at next
          exact (firstOrder memberships).append next
            (by simpa only [List.length_map] using congrArg List.length firstValues)
        · intro steps bounded
          cases steps with
          | zero => exact .refl queue
          | succ steps =>
              have activatedOwners := firstOwners.append
                (State.startNewWork_storedOwnersConserved _
                  (queue.finishGroupSuccess group).2.2 available
                  (flushed.stored.mono (fun occurrence value source => clean _ _ source.1)))
                (State.startNewWork_cancelledGroups_subset _ _ available)
              have conserved := activatedOwners.append
                (laterOwners steps (by omega))
                (State.drainReadyGroups_go_cancelledGroups_subset steps _ available)
              have size : first.length
                  = ((queue.finishGroupSuccess group).2.1.flatMap
                    WorkQueueEvent.objectValues).length := by
                simpa only [List.length_map] using congrArg List.length firstValues
              simpa only [State.drainReadyGroups.go, selected, List.flatMap_append,
                List.length_append, ← size, List.take_append,
                List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
                List.append_nil]
                using conserved
        · intro steps bounded publication member
          cases steps with
          | zero => simp at member
          | succ steps =>
              have size : first.length
                  = ((queue.finishGroupSuccess group).2.1.flatMap
                    WorkQueueEvent.objectValues).length := by
                simpa only [List.length_map] using congrArg List.length firstValues
              simp only [selected, List.flatMap_append,
                List.length_append, ← size, List.take_append,
                List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
                at member ⊢
              rcases List.mem_append.mp member with old | new
              · exact ((firstCleared publication old).startNewWork
                  (queue.finishGroupSuccess group).2.2 available).drainReadyGroups_go
                  steps available
              · exact laterCleared steps (by omega) publication new
        · intro steps bounded next
          dsimp only
          intro chosen publication member
          cases steps with
          | zero =>
              simp only [State.drainReadyGroups.go] at chosen
              rw [selected] at chosen
              obtain rfl := Option.some.inj chosen
              have size : first.length
                  = ((queue.finishGroupSuccess group).2.1.flatMap
                    WorkQueueEvent.objectValues).length := by
                simpa only [List.length_map] using congrArg List.length firstValues
              have inFirst : publication ∈ first := by
                simpa only [State.drainReadyGroups.go, List.nil_append, ← size,
                  List.take_left]
                  using member
              exact firstCleared publication inFirst
          | succ steps =>
              have size : first.length
                  = ((queue.finishGroupSuccess group).2.1.flatMap
                    WorkQueueEvent.objectValues).length := by
                simpa only [List.length_map] using congrArg List.length firstValues
              have readyLater :
                  (State.drainReadyGroups.go available steps activatedState).1.rootGroups.findSome?
                    (fun ref => do
                      let candidate ←
                        (State.drainReadyGroups.go available steps activatedState).1.groupNode? ref
                      if candidate.pending == 0 then some candidate else none) = some next := by
                simpa only [State.drainReadyGroups.go, selected] using chosen
              have included : publication ∈ first ++ later.take
                  (((State.drainReadyGroups.go available steps activatedState).2.1
                    ++ (State.finishGroupSuccess
                      (State.drainReadyGroups.go available steps activatedState).1
                        next).2.1).flatMap
                    WorkQueueEvent.objectValues).length := by
                simpa only [State.drainReadyGroups.go, selected, List.nil_append,
                  List.flatMap_append, List.length_append, ← size, Nat.add_assoc,
                  List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
                  Nat.add_sub_cancel_left]
                  using member
              rcases List.mem_append.mp included with old | fresh
              · have absent := (((firstCleared publication old).startNewWork
                  (queue.finishGroupSuccess group).2.2 available).drainReadyGroups_go
                    steps available).finishGroupSuccess next
                simpa only [State.drainReadyGroups.go, selected] using absent
              · have absent := laterStartup steps (by omega) next readyLater publication fresh
                simpa only [State.drainReadyGroups.go, selected] using absent

/-- Project the established endpoint and prefix interface from the same stronger ledger. -/
theorem State.PublicationInventory.drainReadyGroups_go_prefixCoverage {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (links : queue.StoredTaskLinks) (fuel : Nat)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value _ errors member; cases member)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (State.drainReadyGroups.go available fuel queue).2.1.flatMap
              WorkQueueEvent.objectValues
        ∧ (State.drainReadyGroups.go available fuel queue).1.PublicationInventory property
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added
            (State.drainReadyGroups.go available fuel queue).2.1
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner,
                  (State.drainReadyGroups.go available fuel queue).1.groupNode?
                    contributor.ref
                  = some owner)
            → (occurrence, value) ∈ added
              ∨ (State.drainReadyGroups.go available fuel queue).1.taskNode? occurrence
                = some node)
        ∧ (∀ work,
            ExecutedWork work
            → queue.ChildStreamsSettled
            → queue.ChildStreamsMatchWork work
            → StreamReleasePublications work added
                (State.drainReadyGroups.go available fuel queue).2.1)
        ∧ (queue.GroupMembershipOrder
            → BlocksFollowRegistrations queue.tasks added
                (State.drainReadyGroups.go available fuel queue).2.1)
        ∧ (∀ steps,
            steps ≤ fuel
            → queue.StoredOwnersConserved
                (added.take
                  ((State.drainReadyGroups.go available steps queue).2.1.flatMap
                    WorkQueueEvent.objectValues).length)
                (State.drainReadyGroups.go available steps queue).1)
        ∧ ∀ steps,
            steps ≤ fuel
            → ∀ publication ∈
                added.take
                  ((State.drainReadyGroups.go available steps queue).2.1.flatMap
                    WorkQueueEvent.objectValues).length,
                (State.drainReadyGroups.go available steps queue).1.TaskMembershipAbsent
                  publication.1 := by
  obtain ⟨added, values, final, coverage, conserved, streams, ordered, owners, cleared, _⟩ :=
    inventory.drainReadyGroups_go_prefixCoverage_withStartup links fuel available clean
  exact ⟨added, values, final, coverage, conserved, streams, ordered, owners, cleared⟩

/-- Full-drain coverage retains the earlier endpoint interface on the same prefix ledger.
Witness: specialize the internal-prefix certificate to the entire drain; exact object
projection makes its counted ledger prefix the full publication list.
-/
theorem State.PublicationInventory.drainReadyGroups_go_bufferedCoverage {queue : State}
    {property published} (inventory : queue.PublicationInventory property published)
    (links : queue.StoredTaskLinks) (fuel : Nat)
    (available : List (Occurrence × Nat) := [])
    (clean
      : ∀ occurrence value,
          property occurrence value → ∀ errors, (occurrence, errors) ∉ available := by
        intro occurrence value _ errors member; cases member)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (State.drainReadyGroups.go available fuel queue).2.1.flatMap
              WorkQueueEvent.objectValues
        ∧ (State.drainReadyGroups.go available fuel queue).1.PublicationInventory property
            (published ++ added)
        ∧ queue.BufferedClosuresCovered added
            (State.drainReadyGroups.go available fuel queue).2.1
        ∧ (∀ occurrence node value,
            queue.taskNode? occurrence = some node
            → node.value = some value
            → (∃ contributor ∈ node.task.groups,
                ∃ owner,
                  (State.drainReadyGroups.go available fuel queue).1.groupNode?
                    contributor.ref
                  = some owner)
            → (occurrence, value) ∈ added
              ∨ (State.drainReadyGroups.go available fuel queue).1.taskNode? occurrence
                = some node)
        ∧ (∀ work,
            ExecutedWork work
            → queue.ChildStreamsSettled
            → queue.ChildStreamsMatchWork work
            → StreamReleasePublications work added
                (State.drainReadyGroups.go available fuel queue).2.1)
        ∧ (queue.GroupMembershipOrder
            → BlocksFollowRegistrations queue.tasks added
                (State.drainReadyGroups.go available fuel queue).2.1)
        ∧ queue.StoredOwnersConserved added
            (State.drainReadyGroups.go available fuel queue).1 := by
  obtain ⟨added, values, final, coverage, conserved, streams, ordered, prefixes, _⟩ :=
    inventory.drainReadyGroups_go_prefixCoverage links fuel available clean
  refine ⟨added, values, final, coverage, conserved, streams, ordered, ?_⟩
  have size : added.length = ((State.drainReadyGroups.go available fuel queue).2.1.flatMap
      WorkQueueEvent.objectValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  simpa only [← size, List.take_length] using prefixes fuel (Nat.le_refl _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
