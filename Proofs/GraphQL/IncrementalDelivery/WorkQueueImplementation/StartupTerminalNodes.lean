import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupGroupCompletion
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.StartupTerminalFailureReports

/-! Actual startup terminal replay completes every announced node ref. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
open GraphQL.IncrementalDelivery.WorkQueueSemantics

/-- Every announced ref, group or stream, actually completes when canonical replay ends.
Witness: split actual notices by their two carrier lists and combine concrete group and
stream completion. No lifecycle checker, scheduler admission, or terminal accounting is
assumed, so this can discharge the announced branch of the conformance node leaf.
-/
theorem startup_announced_terminalCompleted {work inputs ref} {w : Witness}
    (generated : ExecutedWork work) (startup : InitialStartup)
    (valid : ValidGraphEvents work inputs.flatten)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (announced : ref ∈ announcedRefs (initialRefs work) w.events)
    : ref ∈ completedRefs w.events := by
  have groupDone
      (noticed : ref ∈ (initialQueue work).initialGroups.map Execution.DeliveryNode.ref ++
        w.events.flatMap groupNoticeRefs)
      : ref ∈ completedRefs w.events := by
    rcases startup_groupNoticeRefs_tracked generated startup valid
      ended history ref noticed with active |
        closed
    · have empty := ((State.initialize (Work.fromExecution work)
        startup)).runNormalized_terminalRoots (by
          rw [State.initializeWithStartup_terminated]
          intro impossible; cases impossible) inputs ended
      rw [empty.1] at active
      cases active
    · exact groupClosureRefs_subset_completed w.events closed
  have streamDone := startup_streamNoticeRefs_terminalCompleted (ref := ref) startup valid
    history ended
  rcases List.mem_append.mp announced with initial | carried
  · rw [initialRefs, List.map_append] at initial
    rcases List.mem_append.mp initial with group | stream
    · apply groupDone
      apply List.mem_append_left
      exact group
    · exact streamDone (List.mem_append_left _ stream)
  · obtain ⟨event, emitted, noticed⟩ := List.mem_flatMap.mp carried
    cases event <;> simp only [eventPending] at noticed
    case groupSuccess owner groups streams | streamValues owner values groups streams =>
      rw [List.map_append] at noticed
      rcases List.mem_append.mp noticed with group | stream
      · exact groupDone (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, emitted, group⟩))
      · exact streamDone (List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, emitted, stream⟩))
    all_goals cases noticed

/-- Complete task accounting gives the unchanged latent-node terminal alternative.
Actual group and stream tracking separately closes every announced ref.
-/
theorem startup_terminal_nodes_of_tasks {work inputs w} (generated : ExecutedWork work)
    (startup : InitialStartup) (valid : ValidGraphEvents work inputs.flatten)
    (history
      : let initial := State.initialize (Work.fromExecution work) startup
        w.events = initial.nonterminalAtoms inputs)
    (ended
      : let initial := State.initialize (Work.fromExecution work) startup
        (initial.runNormalized inputs).1.terminated = true)
    (tasks : TaskAccounting work w)
    : NodeAccounting work w := by
  intro node kind dependencies producer known
  classical
  by_cases announced : node.ref ∈ announcedRefs (initialRefs work) w.events
  · exact .inl (startup_announced_terminalCompleted generated startup valid history ended announced)
  · refine .inr ⟨announced, .inr ?_⟩
    intro occurrence owners descriptor contributes
    obtain ⟨parent, payload, task⟩ := descriptor
    exact tasks occurrence owners parent payload task

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.ConformancePlan
