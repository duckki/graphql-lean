import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.RegistrationCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.PendingBoundPreservation

/-! Membership completeness for unsettled registered tasks, without health assumptions. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Permanent registration prevents late owner reintroduction
-----------------------------------------------------------------------------------------

/-- Integrating groups preserves links whose contributor keys are already registered.
Witness: only fresh unregistered keys enter the group-registration fold; the existing
link-preservation theorem therefore applies even to retired contributors with no live node.
-/
theorem State.TaskLinkedOn.addRegisteredGroups
    {queue : State} {occurrence : Occurrence} {keys : Keys}
    (linked : queue.TaskLinkedOn occurrence keys) (unique : queue.GroupKeysUnique)
    (registered : keys.Subset queue.registeredGroups) (groups : List Group)
    : (queue.addGroups groups).1.TaskLinkedOn occurrence keys := by
  let fresh := groups.filter (fun group =>
    !queue.registeredGroups.contains group.node.key
      && (queue.groupNode? group.node.key).isNone)
  have retained := linked.addGroups unique fresh (by
    intro group member contributor
    have absent : group.node.key ∉ queue.registeredGroups := by
      have chosen := (List.mem_filter.mp member).2
      simpa using (Bool.and_eq_true_iff.mp chosen).1
    exact (absent (registered contributor)).elim)
  simpa only [State.addGroups, fresh, List.filter_filter, Bool.and_self] using retained

/-- Each unsettled permanent task is linked in every surviving contributor node.
Unlike healthy registration accounting, this asserts no owner-node existence and ignores
health: a cancelled or retired owner may be absent, but a retained failed owner still links
its other unsettled tasks. `settled` records the task outcomes already processed.
-/
def State.UnsettledTaskLinks (queue : State) (settled : List Occurrence) : Prop :=
  ∀ task ∈ queue.tasks,
    task.occurrence ∉ settled
    → queue.TaskLinkedOn task.occurrence (task.groups.map Execution.DeliveryNode.key)

/-- Enlarging the processed-outcome list weakens membership obligations.
Witness: every still-unsettled task was unsettled before the enlargement.
-/
theorem State.UnsettledTaskLinks.weaken {queue : State} {before after : List Occurrence}
    (linked : queue.UnsettledTaskLinks before) (included : before.Subset after)
    : queue.UnsettledTaskLinks after := by
  intro task member fresh
  exact linked task member (fun settled => fresh (included settled))

/-- Protected group introduction preserves all unsettled permanent-task links.
Witness: the permanent task-group registry supplies protected keys for every old task.
-/
theorem State.UnsettledTaskLinks.addGroups {queue : State} {settled : List Occurrence}
    (linked : queue.UnsettledTaskLinks settled) (unique : queue.GroupKeysUnique)
    (registered : queue.TaskGroupsRegistered) (groups : List Group)
    : (queue.addGroups groups).1.UnsettledTaskLinks settled := by
  intro task member fresh
  rw [State.addGroups_tasks] at member
  exact (linked task member fresh).addRegisteredGroups unique
    (fun _ contributor => registered task member _ contributor) groups

/-- Registering a task establishes its links and preserves every older task's links.
Witness: the add-task membership theorem and append-only permanent task registration.
-/
theorem State.UnsettledTaskLinks.addTask {queue : State} {settled : List Occurrence}
    (linked : queue.UnsettledTaskLinks settled) (unique : queue.GroupKeysUnique)
    (task : Task)
    : (queue.addTask task).UnsettledTaskLinks settled := by
  intro other member fresh
  rw [State.addTask_tasks] at member
  rcases List.mem_append.mp member with old | new
  · exact (linked other old fresh).addTask unique task
  · have same := List.mem_singleton.mp new
    subst other
    exact queue.addTask_links unique task

/-- Stream integration changes no group membership or permanent task definition.
Witness: its registry equation and the per-task link-preservation theorem.
-/
theorem State.UnsettledTaskLinks.addStreams {queue : State} {settled : List Occurrence}
    (linked : queue.UnsettledTaskLinks settled) (streams : List Stream)
    (producer : Option Occurrence)
    : (queue.addStreams streams producer).1.UnsettledTaskLinks settled := by
  intro task member fresh
  rw [State.addStreams_tasks] at member
  exact (linked task member fresh).addStreams streams producer

/-- Work integration preserves all unsettled links without requiring retired owners live.
Witness: protect old registered keys during group creation, then establish each new task's
links. This is a bookkeeping theorem, with no work-health or output-admission premise.
-/
theorem State.UnsettledTaskLinks.maybeIntegrateWork {queue : State}
    {settled : List Occurrence} (linked : queue.UnsettledTaskLinks settled)
    (unique : queue.GroupKeysUnique) (registered : queue.TaskGroupsRegistered)
    (work : Work) (producer : Option Occurrence := none)
    : (queue.maybeIntegrateWork work producer).1.UnsettledTaskLinks settled := by
  have groupLinks := linked.addGroups unique registered work.groups
  have groupKeys := unique.addGroups work.groups
  have loop (tasks : List Task) (current : State)
      (currentLinks : current.UnsettledTaskLinks settled)
      (currentKeys : current.GroupKeysUnique)
      : (tasks.foldl State.addTask current).UnsettledTaskLinks settled := by
    induction tasks generalizing current with
    | nil => exact currentLinks
    | cons task rest ih =>
        exact ih (current.addTask task) (currentLinks.addTask currentKeys task)
          (currentKeys.addTask task)
  exact (loop work.tasks _ groupLinks groupKeys).addStreams work.streams producer

/-- Mutable started-task values do not affect permanent-task membership obligations.
Witness: the permanent task list and group-node map are definitionally unchanged.
-/
theorem State.UnsettledTaskLinks.putTaskNode {queue : State} {settled : List Occurrence}
    (linked : queue.UnsettledTaskLinks settled) (node : TaskNode)
    : (queue.putTaskNode node).UnsettledTaskLinks settled :=
  linked

/-- Counter and cache updates preserve links when the selected node keeps its task list.
Witness: unique-key replacement preserves each individual registered task's links.
-/
theorem State.UnsettledTaskLinks.putGroupNodeSameTasks {queue : State}
    {settled : List Occurrence} (linked : queue.UnsettledTaskLinks settled)
    (unique : queue.GroupKeysUnique) (node : GroupNode) (member : node ∈ queue.groupNodes)
    (updated : GroupNode) (sameKey : updated.group.node.key = node.group.node.key)
    (sameTasks : updated.tasks = node.tasks)
    : (queue.putGroupNode updated).UnsettledTaskLinks settled := by
  intro task present fresh
  exact (linked task present fresh).putGroupNodeSameTasks unique node member updated
    sameKey sameTasks

-----------------------------------------------------------------------------------------
-- Cleanup and activation preserve links of tasks not yet settled
-----------------------------------------------------------------------------------------

/-- Removing settled memberships preserves every other registered task's links.
Witness: an unsettled task differs from the removed occurrence.
-/
theorem State.UnsettledTaskLinks.removeSettledTask {queue : State}
    {settled : List Occurrence} (linked : queue.UnsettledTaskLinks settled)
    (occurrence : Occurrence) (already : occurrence ∈ settled)
    : (queue.removeTask occurrence).UnsettledTaskLinks settled := by
  intro task member fresh
  exact (linked task member fresh).removeOtherTask occurrence
    (fun same => fresh (same.symm ▸ already))

/-- Group cancellation removes owner nodes but preserves links on every survivor.
Witness: the per-task removal theorem; the permanent task registry is unchanged.
-/
theorem State.UnsettledTaskLinks.removeGroup {queue : State} {settled : List Occurrence}
    (linked : queue.UnsettledTaskLinks settled) (key : Nat)
    : (queue.removeGroup key).UnsettledTaskLinks settled := by
  intro task member fresh
  exact (linked task member fresh).removeGroup key

/-- Pruning removes only group nodes and never forgets a permanent task.
Witness: unchanged task registry and per-task pruning preservation.
-/
theorem State.UnsettledTaskLinks.pruneEmptyGroups {queue : State}
    {settled : List Occurrence} (linked : queue.UnsettledTaskLinks settled)
    (groups : List Execution.DeliveryNode)
    : (queue.pruneEmptyGroups groups).1.UnsettledTaskLinks settled := by
  intro task member fresh
  rw [State.pruneEmptyGroups_tasks] at member
  exact (linked task member fresh).pruneEmptyGroups groups

/-- Starting released work preserves links, even when cached failure skips task starts.
Witness: activation leaves the permanent task registry and group nodes unchanged.
-/
theorem State.UnsettledTaskLinks.startNewWork {queue : State} {settled : List Occurrence}
    (linked : queue.UnsettledTaskLinks settled) (work : NewWork)
    : (queue.startNewWork work).UnsettledTaskLinks settled := by
  intro task member fresh
  rw [(queue.startNewWork_groupCore work).2.1] at member
  exact (linked task member fresh).startNewWork work

/-- Every initialized task is linked to each of its live contributors.
Witness: initial task integration, pruning, and activation, before any outcome settles.
-/
theorem createWorkQueue_unsettledTaskLinks (work : Work)
    : (State.initialize work).UnsettledTaskLinks [] := by
  let integrated := (({} : State).maybeIntegrateWork work).1
  let released := (({} : State).maybeIntegrateWork work).2
  have initial : integrated.UnsettledTaskLinks [] :=
    fun task member _ => State.initialWorkTaskLinks work task member
  exact (initial.pruneEmptyGroups released.newGroups).startNewWork _

/-- A successful group flush preserves every still-unsettled task's links.
Witness: each flushed occurrence is settled, hence differs from every task still covered
by the invariant; the permanent registry is unchanged throughout the flush.
-/
theorem State.UnsettledTaskLinks.finishGroupSuccess {queue : State}
    {settled : List Occurrence} (linked : queue.UnsettledTaskLinks settled)
    (group : GroupNode) (all : ∀ occurrence ∈ group.tasks, occurrence ∈ settled)
    : (queue.finishGroupSuccess group).1.UnsettledTaskLinks settled := by
  intro task member fresh
  rw [State.finishGroupSuccess_tasks] at member
  exact (linked task member fresh).finishOtherGroupSuccess group
    (fun present => fresh (all task.occurrence present))

/-- Pending lower bounds justify every success flush in a recursive drain.
Witness: joint drain induction on the bound and unsettled links; failure removal
and activation preserve the same invariant without any group-health assumption.
-/
theorem State.UnsettledTaskLinks.drainReadyGroups_ofBound {queue : State}
    {settled : List Occurrence} (linked : queue.UnsettledTaskLinks settled)
    (bounded : queue.PendingBound (fun _ => True) settled)
    : queue.drainReadyGroups.1.UnsettledTaskLinks settled := by
  have final := State.drainReadyGroups_preserves
    (fun current => current.UnsettledTaskLinks settled ∧
      current.PendingBound (fun _ => True) settled)
    (by
      intro current node prior member _ _ zero
      have all := prior.2.allSettled member trivial zero
      exact ⟨(prior.1.finishGroupSuccess node all).startNewWork _,
        (prior.2.finishGroupSuccess node all).startNewWork _⟩)
    (fun _ node _ prior _ _ _ =>
      ⟨prior.1.removeGroup node.group.node.key, prior.2.removeGroup node.group.node.key⟩)
    ⟨linked, bounded⟩
  exact final.1

/-- Exact counters are a sufficient special case of bounded-counter drain safety.
Witness: every exact ledger implies the lower bound used by the generalized proof.
-/
theorem State.UnsettledTaskLinks.drainReadyGroups {queue : State}
    {settled : List Occurrence} (linked : queue.UnsettledTaskLinks settled)
    (tracks : queue.PendingTracks settled)
    : queue.drainReadyGroups.1.UnsettledTaskLinks settled :=
  linked.drainReadyGroups_ofBound
    (fun node member _ => Nat.le_of_eq (tracks node member).symm)

/-- Sound membership and complete unsettled links identify a registered task's owners.
Witness: structural task-group uniqueness identifies any membership witness with the
selected task; complete links supply the converse even for latent failed owners.
-/
theorem State.UnsettledTaskLinks.ownedExactlyBy
    {queue : State} {settled : List Occurrence} {work : Execution.Work}
    (linked : queue.UnsettledTaskLinks settled) (sound : queue.GroupMembershipSound)
    (matching : queue.RegisteredTasksMatch work)
    {task : Task} (member : task ∈ queue.tasks) (fresh : task.occurrence ∉ settled)
    : queue.OwnedExactlyBy task.occurrence
        (task.groups.map Execution.DeliveryNode.key) := by
  intro node nodeMember
  constructor
  · intro present
    obtain ⟨witness, registered, same, owner⟩ := sound node nodeMember task.occurrence present
    have witnessExact := (matching witness registered).2
    have taskExact := (matching task member).2
    rw [same] at witnessExact
    have groups := Option.some.inj (witnessExact.symm.trans taskExact)
    simpa only [groups] using owner
  · exact linked task member fresh node nodeMember

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
