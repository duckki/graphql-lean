import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.DescriptorMetadata
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.TaskMemberships

/-! Publisher-side selection of effective shared-value owners. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (ExecutionGroupValue)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Publisher-side selection of a shared value's observable owner
-----------------------------------------------------------------------------------------

/-- The publisher's fold selects an active candidate of maximal path length among
the candidates seen so far. Its initial candidate is assumed active.
-/
private theorem IncrementalPublisher.ownerFold_max
    (publisher : IncrementalPublisher)
    (candidates : List Execution.DeliveryNode)
    (initial : Execution.DeliveryNode)
    (initialActive : publisher.active.any (fun node => node.ref == initial.ref) = true)
    : let choose (best candidate : Execution.DeliveryNode) :=
        if publisher.active.any (fun node => node.ref == candidate.ref)
            && best.path.length < candidate.path.length then
          candidate
        else
          best
      let selected := candidates.foldl choose initial
      publisher.active.any (fun node => node.ref == selected.ref) = true
      ∧ (selected = initial ∨ selected ∈ candidates)
      ∧ initial.path.length ≤ selected.path.length
      ∧ ∀ candidate ∈ candidates,
          publisher.active.any (fun node => node.ref == candidate.ref) = true
          → candidate.path.length ≤ selected.path.length := by
  let active (node : Execution.DeliveryNode) : Bool :=
    publisher.active.any (fun known => known.ref == node.ref)
  let choose (best candidate : Execution.DeliveryNode) :=
    if active candidate && best.path.length < candidate.path.length then
      candidate else best
  have step (best candidate : Execution.DeliveryNode) (bestActive : active best = true)
      : active (choose best candidate) = true
        ∧ (choose best candidate = best ∨ choose best candidate = candidate)
        ∧ best.path.length ≤ (choose best candidate).path.length
        ∧ (active candidate = true
            → candidate.path.length ≤ (choose best candidate).path.length) := by
    unfold choose
    split
    · rename_i selected
      have candidateActive : active candidate = true :=
        (Bool.and_eq_true_iff.mp selected).1
      have longer : best.path.length < candidate.path.length := by
        simpa using (Bool.and_eq_true_iff.mp selected).2
      exact ⟨candidateActive, Or.inr rfl, Nat.le_of_lt longer, fun _ => Nat.le_refl _⟩
    · rename_i skipped
      have bound : active candidate = true →
          candidate.path.length ≤ best.path.length := by
        intro candidateActive
        exact Nat.le_of_not_gt (by
          intro longer
          exact skipped (by simp [candidateActive, longer]))
      exact ⟨bestActive, Or.inl rfl, Nat.le_refl _, bound⟩
  have fold (more : List Execution.DeliveryNode) :
      ∀ best, active best = true →
        let selected := more.foldl choose best
        active selected = true
        ∧ (selected = best ∨ selected ∈ more)
        ∧ best.path.length ≤ selected.path.length
        ∧ ∀ candidate ∈ more,
            active candidate = true → candidate.path.length ≤ selected.path.length := by
    induction more with
    | nil =>
        intro best bestActive
        exact ⟨bestActive, Or.inl rfl, Nat.le_refl _, by simp⟩
    | cons candidate rest ih =>
        intro best bestActive
        obtain ⟨nextActive, nextOrigin, nextLength, candidateLength⟩ :=
          step best candidate bestActive
        obtain ⟨finalActive, finalOrigin, finalLength, restLength⟩ :=
          ih (choose best candidate) nextActive
        change active (rest.foldl choose (choose best candidate)) = true
          ∧ (rest.foldl choose (choose best candidate) = best
              ∨ rest.foldl choose (choose best candidate) ∈ candidate :: rest)
          ∧ best.path.length ≤ (rest.foldl choose (choose best candidate)).path.length
          ∧ ∀ other ∈ candidate :: rest,
              active other = true
              → other.path.length ≤ (rest.foldl choose (choose best candidate)).path.length
        refine ⟨finalActive, ?_, Nat.le_trans nextLength finalLength, ?_⟩
        · rcases finalOrigin with atNext | inRest
          · rw [atNext]
            rcases nextOrigin with atBest | atCandidate
            · exact Or.inl atBest
            · exact Or.inr (by simp [atCandidate])
          · exact Or.inr (by simp [inRest])
        · intro other member otherActive
          rcases List.mem_cons.mp member with atCandidate | inRest
          · subst other
            exact Nat.le_trans (candidateLength otherActive) finalLength
          · exact restLength other inRest otherActive
  simpa only [active, choose] using fold candidates initial initialActive

/-- A shared value is assigned to an active contributor with a longest response
path among all active contributors. Witness: the publisher's max-selection fold.
-/
theorem IncrementalPublisher.getBestIdAndSubPath_longest
    (publisher : IncrementalPublisher)
    (initial : Execution.DeliveryNode) (value : ExecutionGroupValue)
    (initialActive : publisher.active.any (fun node => node.ref == initial.ref) = true)
    (initialContributor : initial ∈ value.deliveryGroups)
    : let selected := publisher.getBestIdAndSubPath initial value
      publisher.active.any (fun node => node.ref == selected.ref) = true
      ∧ selected ∈ value.deliveryGroups
      ∧ ∀ candidate ∈ value.deliveryGroups,
          publisher.active.any (fun node => node.ref == candidate.ref) = true
          → candidate.path.length ≤ selected.path.length := by
  obtain ⟨active, origin, _, longest⟩ :=
    publisher.ownerFold_max value.deliveryGroups initial initialActive
  unfold IncrementalPublisher.getBestIdAndSubPath
  refine ⟨active, ?_, longest⟩
  rcases origin with same | member
  · rw [same]
    exact initialContributor
  · exact member

/-- With coherent generated node refs, an open owner whose ref occurs in
the value's contributor list is that very contributor, not another node sharing
its ref. Witness: ref membership plus `NodeRefCoherent`.
-/
theorem openOwner_contributor_of_coherent (work : Execution.Work)
    (coherent : NodeRefCoherent work) (value : ExecutionGroupValue)
    (contributorsLocated
      : ∀ group ∈ value.deliveryGroups,
          ∃ kind dependencies producer, NodeAt work group kind dependencies producer)
    (initialRefs : NodeRefs) (events : List Execution.WorkQueueEvent)
    (candidate : Execution.DeliveryNode)
    (available
      : OpenOwner work initialRefs events
          (value.deliveryGroups.map Execution.DeliveryNode.ref) candidate)
    : candidate ∈ value.deliveryGroups := by
  obtain ⟨⟨candidateKind, candidateDependencies, candidateProducer, candidateLocated⟩,
    candidateRef, _⟩ := available
  obtain ⟨group, member, refEquality⟩ := List.mem_map.mp candidateRef
  obtain ⟨groupKind, groupDependencies, groupProducer, groupLocated⟩ :=
    contributorsLocated group member
  have same := coherent candidate candidateKind candidateDependencies candidateProducer
    group groupKind groupDependencies groupProducer candidateLocated groupLocated
      refEquality.symm
  exact same.symm ▸ member

/-- Publisher selection satisfies the spec-facing `PublicationOwner` rule once the queue's
active-contributor registry coincides with open owners and a separate healthy supporter
exists. These bridge premises are local proof obligations, not added source laws.
-/
theorem IncrementalPublisher.getBestIdAndSubPath_owner (publisher : IncrementalPublisher)
    (work : Execution.Work) (initialRefs : NodeRefs) (publications : PublicationMatching)
    (events : List Execution.WorkQueueEvent) (failed : FailureCuts)
    (initial : Execution.DeliveryNode) (value : ExecutionGroupValue)
    (initialActive : publisher.active.any (fun node => node.ref == initial.ref) = true)
    (initialContributor : initial ∈ value.deliveryGroups)
    (activeOpen
      : ∀ candidate ∈ value.deliveryGroups,
          (publisher.active.any (fun node => node.ref == candidate.ref) = true)
          ↔ OpenOwner work initialRefs events
              (value.deliveryGroups.map Execution.DeliveryNode.ref) candidate)
    (supported
      : ∃ candidate,
          HealthyOpenOwner work initialRefs publications events failed
            (value.deliveryGroups.map Execution.DeliveryNode.ref) candidate)
    (coherent : NodeRefCoherent work)
    (contributorsLocated
      : ∀ group ∈ value.deliveryGroups,
          ∃ kind dependencies producer, NodeAt work group kind dependencies producer)
    : PublicationOwner work initialRefs publications events failed
        (value.deliveryGroups.map Execution.DeliveryNode.ref)
        (publisher.getBestIdAndSubPath initial value) := by
  obtain ⟨selectedActive, selectedContributor, longest⟩ :=
    publisher.getBestIdAndSubPath_longest initial value initialActive
      initialContributor
  constructor
  · exact (activeOpen _ selectedContributor).mp selectedActive
  · refine ⟨supported, ?_⟩
    intro candidate candidateAvailable
    have contributor := openOwner_contributor_of_coherent work coherent value
      contributorsLocated initialRefs events candidate candidateAvailable
    exact longest candidate contributor
      ((activeOpen candidate contributor).mpr candidateAvailable)

/-- For a conforming successful host settlement, source matching already supplies
every contributor's Work location. Active/open agreement and separate healthy support
connect the publisher's choice to the abstract `PublicationOwner` rule.
-/
theorem IncrementalPublisher.taskSuccess_owner (publisher : IncrementalPublisher)
    (work : Execution.Work) (initialRefs : NodeRefs) (publications : PublicationMatching)
    (events : List Execution.WorkQueueEvent) (failed : FailureCuts)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (initial : Execution.DeliveryNode)
    (initialActive : publisher.active.any (fun node => node.ref == initial.ref) = true)
    (initialContributor : initial ∈ result.value.deliveryGroups)
    (coherent : NodeRefCoherent work)
    (activeOpen
      : ∀ candidate ∈ result.value.deliveryGroups,
          (publisher.active.any (fun node => node.ref == candidate.ref) = true)
          ↔ OpenOwner work initialRefs events
              (result.value.deliveryGroups.map Execution.DeliveryNode.ref) candidate)
    (supported
      : ∃ candidate,
          HealthyOpenOwner work initialRefs publications events failed
            (result.value.deliveryGroups.map Execution.DeliveryNode.ref) candidate)
    : PublicationOwner work initialRefs publications events failed
        (result.value.deliveryGroups.map Execution.DeliveryNode.ref)
        (publisher.getBestIdAndSubPath initial result.value) := by
  apply publisher.getBestIdAndSubPath_owner work initialRefs publications events failed initial
    result.value initialActive initialContributor activeOpen supported coherent
  intro group member
  obtain ⟨dependencies, producer, located⟩ :=
    matching.success_contributorsLocated group member
  exact ⟨.group, dependencies, producer, located⟩

/-- At the initial frontier, active publisher nodes are precisely announced,
open contributors. No failure has yet occurred, so a matched task's located
contributor is available exactly when its ref occurs in the initial notices.
-/
theorem IncrementalPublisher.initialTask_activeAvailable
    (work : Execution.Work) (initialNodes : List Execution.DeliveryNode)
    (publications : PublicationMatching)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (candidate : Execution.DeliveryNode)
    (contributor : candidate ∈ result.value.deliveryGroups)
    : ((initialNodes.any (fun node => node.ref == candidate.ref)) = true)
      ↔ HealthyOpenOwner work
          (initialNodes.map Execution.DeliveryNode.ref) publications [] []
          (result.value.deliveryGroups.map Execution.DeliveryNode.ref) candidate := by
  obtain ⟨dependencies, producer, located⟩ :=
    matching.success_contributorsLocated candidate contributor
  have refMember : candidate.ref ∈
      result.value.deliveryGroups.map Execution.DeliveryNode.ref :=
    List.mem_map.mpr ⟨candidate, contributor, rfl⟩
  have activeIff : (initialNodes.any (fun node => node.ref == candidate.ref)) = true
      ↔ candidate.ref ∈ initialNodes.map Execution.DeliveryNode.ref := by
    simp [List.any_eq_true]
  constructor
  · intro active
    refine ⟨⟨⟨.group, dependencies, producer, located⟩, refMember, ?_⟩, ?_⟩
    · exact ⟨by simpa [announcedRefs, pendingRefs] using activeIff.mp active,
        by simp [completedRefs]⟩
    · intro failure
      exact failure.nonempty rfl
  · intro available
    have announced := available.1.2.2.1
    exact activeIff.mpr (by simpa [announcedRefs, pendingRefs] using announced)

/-- For an initially announced group, the concrete publisher selects a valid
spec owner for a matched task success. This is the zero-history base case of
the active/open registry simulation.
-/
theorem IncrementalPublisher.initialTask_owner
    (work : Execution.Work) (initialNodes : List Execution.DeliveryNode)
    (publications : PublicationMatching)
    (occurrence : Occurrence) (result : TaskResult)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (coherent : NodeRefCoherent work)
    (initial : Execution.DeliveryNode)
    (initialNotice : initial ∈ initialNodes)
    (initialContributor : initial ∈ result.value.deliveryGroups)
    : PublicationOwner work (initialNodes.map Execution.DeliveryNode.ref) publications []
        [] (result.value.deliveryGroups.map Execution.DeliveryNode.ref)
        (({ active := initialNodes } : IncrementalPublisher).getBestIdAndSubPath
          initial result.value) := by
  let publisher : IncrementalPublisher := { active := initialNodes }
  have initialActive : publisher.active.any
      (fun node => node.ref == initial.ref) = true := by
    simp only [publisher]
    simp [List.any_eq_true]
    exact ⟨initial, initialNotice, by simp⟩
  apply publisher.taskSuccess_owner work
    (initialNodes.map Execution.DeliveryNode.ref) publications [] [] occurrence result
    matching initial initialActive initialContributor coherent
  · intro candidate member
    have available := initialTask_activeAvailable work initialNodes publications occurrence
      result matching candidate member
    constructor
    · exact fun active => (available.mp active).1
    · exact fun opened => available.mpr ⟨opened, fun failure => failure.nonempty rfl⟩
  · exact ⟨initial, (initialTask_activeAvailable work initialNodes publications occurrence
      result matching initial initialContributor).mp initialActive⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
