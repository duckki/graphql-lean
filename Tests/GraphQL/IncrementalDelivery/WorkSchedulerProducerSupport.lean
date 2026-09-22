import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.WorkSchedulerProducerAvailability

/-! Generated nested defer release and publication regressions. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducerSupport
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Actual successful release follows the earlier root's post-integration subtree
-----------------------------------------------------------------------------------------

/-- Settling the parent publishes its object and promotes the nested child as sole root.
Witness: evaluation of the real single-pass task-success handler on generated work. -/
theorem success_promotes_child
    : (queue.taskSuccess parentTask result).1.rootGroups = [child.key] := by
  cbv

/-- The child promoted by the full handler comes from the earlier parent's subtree.
Witness: the general root-origin theorem rules out retention of an old root and
extracts the original parent from the initial root list. The snapshot is taken after
child integration, before the successful loop removes the parent. -/
theorem promoted_child_origin
    : let integrated :=
        ((queue.putTaskNode
            { task := producer, value := some result.value }).maybeIntegrateWork
          result.work (some parentTask)).1
      integrated.LiveDescendant parent.key child.key := by
  have active : child.key ∈ (queue.taskSuccess parentTask result).1.rootGroups := by
    rw [success_promotes_child]
    exact List.mem_cons_self
  have roots : queue.rootGroups = [parent.key] := by cbv
  have origins := State.taskSuccess_rootOrigins (createWorkQueue_groupKeysUnique _)
    parentTask result { task := producer } (by cbv) child.key active
  rcases origins with old | ⟨key, member, path⟩
  · have absent : child.key ∉ queue.rootGroups := by rw [roots]; decide
    exact False.elim (absent old)
  · change key ∈ queue.rootGroups at member
    rw [roots] at member
    have same := List.mem_singleton.mp member
    exact same ▸ path

-----------------------------------------------------------------------------------------
-- Successive handlers publish distinct occurrences through real normalized batches
-----------------------------------------------------------------------------------------

private def childTask : Occurrence := .executionGroup [1, 0, 0, 0, 1, 0]

private def childResult : TaskResult :=
  {
    value :=
      {
        deliveryGroups := [child], path := child.path, data := [("name", .scalar "name1")]
      }
  }

private def publicationInputs : List (List GraphEvent) :=
  [[.taskSuccess parentTask result], [.taskSuccess childTask childResult]]

/-- The produced child starts after its parent publishes and then settles legally.
Witness: exact child provenance, preceding producer success, freshness, and the actual
queue start checker; each input is in a separate batch. -/
theorem publication_inputs_valid_started
    : ValidGraphEvents work publicationInputs.flatten
      ∧ inputsStarted work publicationInputs = true := by
  have parentKnown : TaskAt work parentTask [parent.key] none
      (.object [] (.ok ([("user", .object [])], 0))) := by
    refine ⟨[⟨parent, []⟩], [], _, children, [], ?_, rfl, rfl⟩
    cbv
  have childKnown : TaskAt work childTask [child.key] (some parentTask)
      (.object child.path (.ok (childResult.value.data, 0))) := by
    refine ⟨[⟨child, [parent]⟩], child.path, _, .combine .empty .empty, [parent.key],
      ?_, rfl, rfl⟩
    cbv
  have first : ValidGraphEvents work [.taskSuccess parentTask result] :=
    .append .nil matching
      (by simp [GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, parentKnown, by intro source impossible; cases impossible⟩
  refine ⟨.append first ⟨_, _, childKnown, by cbv, by cbv⟩ ?_ ?_, by cbv⟩
  · simp [GraphEvent.Fresh, GraphEvent.identities, parentTask, childTask]
  · refine ⟨_, _, _, childKnown, ?_⟩
    intro source same
    cases same
    simp [GraphEvent.successes]

/-- Actual normalized output across two different successful handlers has fresh occurrences.
Witness: the general publication inventory plus evaluation of both nonempty object
publications. The parent value is not restored when its produced child is started. -/
theorem successive_publications_unique
    : ∃ published : List ObjectPublication,
        (published.map Prod.fst).Nodup
        ∧ published.map (fun publication => publication.2)
          = [result.value, childResult.value]
        ∧ ∀ publication ∈ published,
            ObjectValueFrom publicationInputs.flatten publication.1 publication.2 := by
  obtain ⟨published, values, inventory⟩ := createWorkQueue_runNormalized_publications
    publication_inputs_valid_started.1
  have actual : (queue.runNormalized publicationInputs).2.flatten.flatMap normalizedObjectValues =
      [result.value, childResult.value] := by cbv
  exact ⟨published, inventory.unique, values.trans actual, inventory.provenance⟩

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerProducerSupport
