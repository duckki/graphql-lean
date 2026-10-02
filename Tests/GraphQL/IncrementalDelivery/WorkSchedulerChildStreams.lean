import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation
import Tests.GraphQL.IncrementalDelivery.Execution

/-! A deferred stream stays buffered with its producer until shared-owner release. -/

namespace GraphQL.IncrementalDelivery.Tests.WorkSchedulerChildStreams
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Generated overlapping defers with a task-produced stream
-----------------------------------------------------------------------------------------

private def parent : DeliveryNode := { key := 0, path := [], label := some (.string "P") }
private def other : DeliveryNode := { key := 1, path := [], label := some (.string "Q") }
private def stream : DeliveryNode := { key := 2, path := [.field "values"] }
private def producerTask : Occurrence := .executionGroup [1, 0]
private def sharedTask : Occurrence := .executionGroup [1, 1, 0]

private def producerValue : ExecutionGroupValue :=
  { deliveryGroups := [parent], path := [], data := [("values", .list [])] }

private def sharedValue : ExecutionGroupValue :=
  { deliveryGroups := [parent, other], path := [], data := [("b", .scalar "b")] }

private def children : Execution.Work :=
  .combine
    (.combine .empty
      (.stream stream
        [
          (.ok (.scalar "x", 0), .empty),
          (.ok (.null, 0), .empty),
          (.ok (.scalar "z", 0), .empty)
        ]))
    .empty

private def work : Execution.Work :=
  .combine .empty
    (.combine
      (.executionGroup [⟨parent, []⟩] [] (.ok (producerValue.data, 0)) children)
      (.combine
        (.executionGroup [⟨parent, []⟩, ⟨other, []⟩] [] (.ok (sharedValue.data, 0))
          (.combine .empty .empty))
        .empty))

private def producerResult : TaskResult :=
  { value := producerValue, work := Work.fromExecution children [1, 0, 0] }

private def sharedResult : TaskResult := { value := sharedValue }
private def first : GraphEvent := .taskSuccess producerTask producerResult
private def shared : GraphEvent := .taskSuccess sharedTask sharedResult
private def initial : State := State.initialize (Work.fromExecution work)
private def waiting : State := (initial.runNormalized [[first]]).1

/-- The buffered stream comes from real query execution, not arbitrary raw work.
Witness: overlapping P { values @stream b } and Q { b }, with finite pure test resolvers.
-/
theorem generated : ExecutedWork work := by
  refine ⟨Nat, schema, resolvers, [], 50, "Query", .object "Query" 0,
    [defer [field "values" [] [.stream], field "b"] (some "P"),
      defer [field "b"] (some "Q")], ?_⟩
  cbv

/-- The producer is the root task whose success returns the empty initial list.
Witness: its exact generated task descriptor and child stream subtree. -/
private theorem producerKnown
    : TaskAt work producerTask [parent.key] none
        (.object [] (.ok (producerValue.data, 0))) := by
  refine ⟨[⟨parent, []⟩], [], _, children, [], ?_, rfl, rfl⟩
  cbv

/-- The independent shared task supplies b to both pending groups.
Witness: its generated two-owner descriptor. -/
private theorem sharedKnown
    : TaskAt work sharedTask [parent.key, other.key] none
        (.object [] (.ok (sharedValue.data, 0))) := by
  refine ⟨[⟨parent, []⟩, ⟨other, []⟩], [], _, .combine .empty .empty, [], ?_, rfl, rfl⟩
  cbv

/-- Both input settlements obey source semantics and are accepted in their actual states.
Witness: exact outcomes/child lowering, fresh root task identities, and start checking.
-/
theorem inputs_valid_started
    : ValidGraphEvents work [first, shared]
      ∧ inputsStarted work [[first], [shared]] = true := by
  have before : ValidGraphEvents work [first] :=
    .append .nil ⟨_, _, producerKnown, by cbv, by cbv⟩
      (by simp [first, GraphEvent.Fresh, GraphEvent.identities])
      ⟨_, _, _, producerKnown, by intro source impossible; cases impossible⟩
  refine ⟨.append before ⟨_, _, sharedKnown, by cbv, by cbv⟩ ?_ ?_, by cbv⟩
  · simp [first, shared, producerTask, sharedTask, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, sharedKnown, by intro source impossible; cases impossible⟩

/-- The produced stream is structurally below the buffered producer task.
Witness: navigate the executor's exact child-work address and retain its enclosing owner.
-/
private theorem streamKnown
    : NodeAt work stream .stream [parent.key] (some producerTask) := by
  refine ⟨[1, 0, 0, 0, 1],
    [(.ok (.scalar "x", 0), .empty), (.ok (.null, 0), .empty),
      (.ok (.scalar "z", 0), .empty)], ?_⟩
  cbv

/-- Settlement alone neither publishes the producer nor starts its child stream.
Witness: the other shared contributor keeps P pending; its producer value and stream
key remain stored together in the live task node. -/
theorem producer_and_stream_wait
    : (initial.runNormalized [[first]]).2 = []
      ∧ waiting.rootStreams = []
      ∧ waiting.taskNode? producerTask
        = some
            {
              task := ⟨producerTask, [parent]⟩,
              value := some producerValue,
              childStreams := [stream.key]
            }
      ∧ waiting.ChildStreamsSettled := by
  refine ⟨by cbv, by cbv, by cbv, ?_⟩
  exact createWorkQueue_runNormalized_childStreamsSettled _ _

/-- Replay derives the structural producer for the stored stream key without a new premise.
Witness: restrict the valid source history to its first input and apply general replay
provenance; the actual buffered node and child link are checked by evaluation. -/
theorem waiting_stream_producer
    : waiting.ChildStreamsMatchWork work
      ∧ ∀ node ∈ waiting.taskNodes,
          stream.key ∈ node.childStreams → node.task.occurrence = producerTask := by
  have valid : ValidGraphEvents work [first] :=
    inputs_valid_started.1.prefix ⟨[shared], rfl⟩
  have matching := createWorkQueue_runNormalized_childStreamsMatchWork (batches := [[first]]) valid
  refine ⟨matching, ?_⟩
  intro node member linked
  exact (Option.some.inj (matching.producer generated member streamKnown linked)).symm

-----------------------------------------------------------------------------------------
-- The later shared success flushes the producer before the stream notice
-----------------------------------------------------------------------------------------

private def closing : GroupNode :=
  { group := ⟨parent, none⟩, tasks := [producerTask, sharedTask] }

private def atFlush : State :=
  (waiting.putTaskNode
    { task := ⟨sharedTask, [parent, other]⟩, value := some sharedValue }).putGroupNode
    closing

private def publisher : IncrementalPublisher := { active := [parent, other] }

/-- The local flush state inherits the replay invariant before the contributor closes.
Witness: settled-value installation and the pending-only group update preserve it. -/
private theorem atFlush_settled : atFlush.ChildStreamsSettled := by
  have waited := createWorkQueue_runNormalized_childStreamsSettled (Work.fromExecution work) [[first]]
  exact (waited.putTaskNode _ (by simp)).putGroupNode _

/-- The actual flush intermediate retains its stored links' structural producer evidence.
Witness: replay provenance followed by value installation and the pending-only update.
-/
private theorem atFlush_matches : atFlush.ChildStreamsMatchWork work := by
  exact (waiting_stream_producer.1.putTaskNode _ (by simp)).putGroupNode _

/-- The actual successful handler reaches this flush, then closes the other owner.
Witness: evaluation of the single-pass shared-owner handler; no stream was started early.
-/
theorem delayed_release
    : (waiting.taskSuccess sharedTask sharedResult).2
        = (atFlush.finishGroupSuccess closing).2.1 ++ [.groupSuccess other [] []]
      ∧ (waiting.taskSuccess sharedTask sharedResult).1.rootStreams = [stream.key] := by
  constructor <;> cbv

/-- The delayed stream's active key is justified by an emitted notice, not initialization.
Witness: the general active-stream announcement invariant after the actual shared release;
the generated work has no initial streams, so its witness must come from the output.
-/
theorem active_stream_has_emitted_notice
    : stream.key
      ∈ (initial.runNormalized [[first], [shared]]).2.flatten.flatMap
          streamNoticeKeys := by
  have active : stream.key ∈ (initial.runNormalized [[first], [shared]]).1.rootStreams := by
    change stream.key ∈ [stream.key]
    exact List.mem_cons_self
  have announced := createWorkQueue_runNormalized_streamRoots (Work.fromExecution work)
    [[first], [shared]] active
  exact announced

/-- An initially active empty stream is covered by an initial notice without any output.
Witness: the initialization invariant applied to an exhausted stream; no item settlement
or generated-work assumption is needed for this bookkeeping fact.
-/
theorem empty_stream_has_initial_notice
    : stream.key
      ∈ (State.initialize (Work.fromExecution (.stream stream []))).initialStreams.map
          DeliveryNode.key := by
  apply createWorkQueue_streamRoots
  change stream.key ∈ [stream.key]
  exact List.mem_cons_self

/-- The stream's release witness identifies its buffered producer, not the later task.
Witness: apply the general release theorem; only the producer node has this child key.
-/
theorem release_has_exact_producer
    : ∃ node ∈ atFlush.taskNodes,
        ∃ values,
          node.task.occurrence = producerTask
          ∧ node.value = some producerValue
          ∧ producerValue ∈ values
          ∧ (atFlush.finishGroupSuccess closing).2.1
            = [.groupValues parent values, .groupSuccess parent [] [stream]] := by
  have released : stream ∈ (atFlush.finishGroupSuccess closing).2.2.newStreams := by
    change stream ∈ [stream]
    exact List.mem_cons_self
  obtain ⟨node, member, value, values, _, child, stored, valueMember, output⟩ :=
    atFlush_settled.finishGroupSuccess_release closing released
  have nodes : atFlush.taskNodes =
      [{ task := ⟨producerTask, [parent]⟩, value := some producerValue,
          childStreams := [stream.key] },
        { task := ⟨sharedTask, [parent, other]⟩, value := some sharedValue }] := by cbv
  have producer : node =
      { task := ⟨producerTask, [parent]⟩, value := some producerValue,
        childStreams := [stream.key] } := by
    rw [nodes] at member
    rcases List.mem_cons.mp member with same | sharedNode
    · exact same
    · have same := List.mem_singleton.mp sharedNode
      simp [same] at child
  subst node
  have sameValue : value = producerValue := (Option.some.inj stored).symm
  subst value
  exact ⟨_, member, values, rfl, rfl, valueMember, output⟩

/-- Publisher normalization retains the producer-before-notice ordering on this flush.
Witness: the general normalized release theorem, applied before shared-owner cleanup.
-/
theorem normalized_release_order
    : ∃ node ∈ atFlush.taskNodes,
        ∃ value,
          stream.key ∈ node.childStreams
          ∧ node.value = some value
          ∧ [
              Execution.WorkQueueEvent.groupValues
                (publisher.getBestIdAndSubPath parent value) [value],
              .groupSuccess parent [] [stream]
            ].Sublist
              (publisher.normalizeBatch (atFlush.finishGroupSuccess closing).2.1).2 := by
  have released : stream ∈ (atFlush.finishGroupSuccess closing).2.2.newStreams := by
    change stream ∈ [stream]
    exact List.mem_cons_self
  obtain ⟨node, member, value, _, child, stored, ordered⟩ :=
    atFlush_settled.finishGroupSuccess_normalized_release publisher closing released
  exact ⟨node, member, value, child, stored, ordered⟩

/-- The normalized release theorem identifies the structural producer of this stream.
Witness: actual intermediate link invariants, generated key uniqueness, and the stream's
independent structural descriptor; the preceding publication belongs to producerTask.
-/
theorem structural_producer_release
    : ∃ node ∈ atFlush.taskNodes,
        ∃ value,
          node.task.occurrence = producerTask
          ∧ node.value = some value
          ∧ [
              Execution.WorkQueueEvent.groupValues
                (publisher.getBestIdAndSubPath parent value) [value],
              .groupSuccess parent [] [stream]
            ].Sublist
              (publisher.normalizeBatch (atFlush.finishGroupSuccess closing).2.1).2 := by
  have released : stream ∈ (atFlush.finishGroupSuccess closing).2.2.newStreams := by
    change stream ∈ [stream]
    exact List.mem_cons_self
  obtain ⟨node, member, value, source, stored, ordered⟩ :=
    atFlush_matches.finishGroupSuccess_producer_release atFlush_settled generated publisher
      closing streamKnown released
  exact ⟨node, member, value, (Option.some.inj source).symm, stored, ordered⟩

/-- The real next handler uses one fresh source inventory for values and stream release.
Witness: the replay/handler theorem, with the stream carrier at raw output index one;
its producer is among the two earlier values, not merely among settled input tasks.
-/
theorem handler_release_inventory
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (waiting.taskSuccess sharedTask sharedResult).2.flatMap
              WorkQueueEvent.objectValues
        ∧ (added.map Prod.fst).Nodup
        ∧ (∀ publication ∈ added,
            ObjectValueFrom [first, shared] publication.1 publication.2)
        ∧ producerTask ∈ (added.take 2).map Prod.fst := by
  obtain ⟨published, added, _, values, unique, provenance, supported⟩ :=
    createWorkQueue_runNormalized_taskSuccess_streamRelease (batches := [[first]]) generated
      inputs_valid_started.1
  obtain ⟨occurrence, producer, earlier⟩ :=
    supported 1 parent [] [stream] (by cbv) stream List.mem_cons_self
      [parent.key] (some producerTask) streamKnown
  have same := Option.some.inj producer
  subst occurrence
  refine ⟨added, values, ?_, ?_, ?_⟩
  · exact (List.nodup_append.mp (by simpa only [List.map_append] using unique)).2.1
  · intro publication member
    exact provenance publication (List.mem_append_right published member)
  · exact earlier

/-- Split and joined arrivals produce the same value-before-notice output batch.
Witness: execute both real replay paths; the first settlement alone has no output.
-/
theorem normalized_batches
    : ∀ batches ∈ [[[first], [shared]], [[first, shared]]],
        (initial.runNormalized batches).2
          = [[
              .groupValues parent [producerValue],
              .groupValues parent [sharedValue],
              .groupSuccess parent [] [stream],
              .groupSuccess other [] []
            ]]
        ∧ (initial.runNormalized batches).1.ChildStreamsSettled := by
  intro batches member
  refine ⟨?_, createWorkQueue_runNormalized_childStreamsSettled _ _⟩
  rcases List.mem_cons.mp member with same | later
  · subst batches
    cbv
  · have same := List.mem_singleton.mp later
    subst batches
    cbv

/-- Split, joined, and empty-interspersed batches retain the same fresh release inventory.
Witness: full replay derives the joint ledger; the actual normalized stream carrier is
after both object publications, even though they came from separate source settlements.
-/
theorem normalized_release_inventory
    : ∀ batches ∈
        [[[first], [shared]], [[first, shared]], [[], [first], [], [shared], []]],
        ∃ published : List ObjectPublication,
          published.map (fun publication => publication.2)
            = (initial.runNormalized batches).2.flatten.flatMap normalizedObjectValues
          ∧ (published.map Prod.fst).Nodup
          ∧ (∀ publication ∈ published,
              ObjectValueFrom batches.flatten publication.1 publication.2)
          ∧ NormalizedStreamReleasePublications work published
              (initial.runNormalized batches).2.flatten
          ∧ producerTask ∈ (published.take 2).map Prod.fst := by
  intro batches member
  have choices : batches = [[first], [shared]] ∨ batches = [[first, shared]]
      ∨ batches = [[], [first], [], [shared], []] := by simpa using member
  have flat : batches.flatten = [first, shared] := by
    rcases choices with rfl | rfl | rfl <;> rfl
  have outputs : (initial.runNormalized batches).2
      = [[.groupValues parent [producerValue],
          .groupValues parent [sharedValue], .groupSuccess parent [] [stream],
          .groupSuccess other [] []]] := by
    rcases choices with rfl | rfl | rfl <;> cbv
  have valid : ValidGraphEvents work batches.flatten := flat ▸ inputs_valid_started.1
  obtain ⟨published, values, ledger, supported⟩ :=
    createWorkQueue_runNormalized_streamReleasePublications generated valid
  refine ⟨published, values, ledger.unique, ledger.provenance, supported, ?_⟩
  have carrier : (initial.runNormalized batches).2.flatten[2]?
      = some (.groupSuccess parent [] [stream]) := by rw [outputs]; rfl
  obtain ⟨occurrence, producer, earlier⟩ :=
    supported 2 parent [] [stream] carrier stream List.mem_cons_self
      [parent.key] (some producerTask) streamKnown
  have same := Option.some.inj producer
  subst occurrence
  change producerTask ∈ (published.take
    (((initial.runNormalized batches).2.flatten.take 2).flatMap
      normalizedObjectValues).length).map Prod.fst at earlier
  rw [outputs] at earlier
  exact earlier

/-- The child stream cannot supply any input until the producer's later publication.
Witness: the executable start checker rejects it while buffered and accepts it after
the shared-task flush; even source settlement order alone would not establish this.
-/
theorem stream_start_barrier
    : waiting.acceptsGraphEvent (.streamSuccess stream) = false
      ∧ (waiting.taskSuccess sharedTask sharedResult).1.acceptsGraphEvent
          (.streamSuccess stream)
        = true := by
  constructor <;> cbv

-----------------------------------------------------------------------------------------
-- One joint matching for the released producer and the subsequent streamed items
-----------------------------------------------------------------------------------------

private def streamEntries : List (Result ResponseValue × Execution.Work) :=
  [
    (.ok (.scalar "x", 0), .empty),
    (.ok (.null, 0), .empty),
    (.ok (.scalar "z", 0), .empty)
  ]

private def item (index : Nat) : StreamItem :=
  {
    occurrence := .item [1, 0, 0, 0, 1] index,
    value :=
      {
        item :=
          if index = 0 then .scalar "x" else if index = 1 then .null else .scalar "z"
      }
  }

private def items : GraphEvent := .streamItems stream [item 0, item 1, item 2]
private def finish : GraphEvent := .streamSuccess stream

private def completeInputs : List (List GraphEvent) :=
  [[first], [shared], [items, finish]]

/-- The three-item stream retains the buffered object's structural producer.
Witness: the exact generated child location, with its original enclosing defer owner. -/
private theorem streamLocated
    : Located work [1, 0, 0, 0, 1] (.stream stream streamEntries)
        (some producerTask) [parent.key] := by cbv

/-- Each stream input carries its exact finite item and empty child boundary.
Witness: indexed lookup at the generated stream location, retaining the producing task.
-/
private theorem itemMatches (index : Nat) (bound : index < 3)
    : ∃ owners producer,
        TaskAt work (item index).occurrence owners producer
          (.item stream (.ok ((item index).value.item, (item index).value.errors)))
        ∧ streamItemWork? work (item index).occurrence = some (item index).work := by
  have entry : streamEntries[index]? = some (.ok ((item index).value.item, 0), .empty) := by
    have casesIndex : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases casesIndex with rfl | rfl | rfl <;> rfl
  refine ⟨[stream.key], some producerTask, ?_, ?_⟩
  · exact ⟨stream, streamEntries, [parent.key], _, .empty, streamLocated, entry, rfl, rfl⟩
  · have located : locateWork work [1, 0, 0, 0, 1]
        = some ⟨.stream stream streamEntries, some producerTask, [parent.key]⟩ := streamLocated
    simp [streamItemWork?, item, located, entry, Work.fromExecution]

/-- The released stream can legally supply all items and finish after the two task inputs.
Witness: fixed outcomes, fresh occurrences, prior producer settlement, contiguous indices,
and the executable start checker at every input, including same-batch stream completion.
-/
theorem complete_inputs_valid_started
    : ValidGraphEvents work completeInputs.flatten
      ∧ inputsStarted work completeInputs = true := by
  have itemInput : items.MatchesWork work := by
    intro value member
    have choices : value = item 0 ∨ value = item 1 ∨ value = item 2 := by simpa [items] using member
    rcases choices with rfl | rfl | rfl
    · exact itemMatches 0 (by decide)
    · exact itemMatches 1 (by decide)
    · exact itemMatches 2 (by decide)
  have settled : ValidGraphEvents work [first, shared, items] :=
    .append inputs_valid_started.1 itemInput
      (by simp [items, item, first, shared, GraphEvent.Fresh, GraphEvent.identities,
        producerTask, sharedTask])
      ⟨_, _, _, _, streamLocated, by simp, by simp [first, shared, GraphEvent.identities],
        (by intro source same; cases same; simp [first, shared, GraphEvent.successes]), by cbv⟩
  refine ⟨.append settled ⟨_, _, streamKnown⟩ ?_ ?_, by cbv⟩
  · simp [finish, first, shared, items, GraphEvent.Fresh, GraphEvent.identities]
  · exact ⟨_, _, _, _, streamLocated,
      (by intro source same; cases same; simp [first, shared, items, GraphEvent.successes]),
      by cbv⟩

/-- The actual complete replay contains both object values, all three items, and termination.
Witness: evaluate the unchanged runner; atomic expansion only splits the one item batch.
-/
theorem complete_output_atoms
    : (initial.runNormalized completeInputs).1.terminated = true
      ∧ (initial.runNormalized completeInputs).2.flatten.flatMap publicationAtoms
        = [
          .groupValues parent [producerValue],
          .groupValues parent [sharedValue],
          .groupSuccess parent [] [stream],
          .groupSuccess other [] [],
          .streamValues stream [⟨.scalar "x", 0⟩] [] [],
          .streamValues stream [⟨.null, 0⟩] [] [],
          .streamValues stream [⟨.scalar "z", 0⟩] [] [],
          .streamSuccess stream,
          .workQueueTermination
        ] := by
  constructor <;> cbv

/-- All input successes, including the task-produced stream's items, are reachable.
Witness: the general source-readiness induction follows their successful producer chains;
this does not infer that the earlier buffered task was published when it first settled.
-/
theorem complete_source_successes_reachable
    : ∀ occurrence ∈ completeInputs.flatten.flatMap GraphEvent.successes,
        Reachable work occurrence :=
  complete_inputs_valid_started.1.successes_reachable generated

/-- Stream values and completion use earlier notices, including within one joined batch.
Witness: the general strict-prefix announcement theorem for both exact input groupings;
source validity is unchanged by flattening the batch boundaries.
-/
theorem complete_stream_references_announced
    : ∀ batches ∈ [completeInputs, [completeInputs.flatten]],
        ∀ index event,
          ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
            = some event
          → ∀ key ∈ streamReferenceKeys event,
              key
              ∈ announcedKeys
                  ((initial.initialGroups ++ initial.initialStreams).map DeliveryNode.key)
                  ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms
                    |>.take index) := by
  intro batches member index event atEvent key reference
  have valid : ValidGraphEvents work batches.flatten := by
    rcases List.mem_cons.mp member with same | last
    · subst batches; exact complete_inputs_valid_started.1
    · have same := List.mem_singleton.mp last
      subst batches
      simpa using complete_inputs_valid_started.1
  exact createWorkQueue_runNormalized_streamAnnouncedAt valid atEvent reference

/-- Split and joined complete runs never reference an already-completed stream.
Witness: valid source order transported through actual output and its atomic expansion;
the single three-item input expands to three references without adding a closure.
-/
theorem complete_stream_references_unclosed
    : ∀ batches ∈ [completeInputs, [completeInputs.flatten]],
        ∀ index event,
          ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
            = some event
          → ∀ key ∈ streamReferenceKeys event,
              (key, true)
              ∉ (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                  index).filterMap
                  streamAction := by
  intro batches member index event atEvent key reference
  have valid : ValidGraphEvents work batches.flatten := by
    rcases List.mem_cons.mp member with same | last
    · subst batches; exact complete_inputs_valid_started.1
    · have same := List.mem_singleton.mp last
      subst batches
      simpa using complete_inputs_valid_started.1
  exact createWorkQueue_runNormalized_streamUnclosedAt valid atEvent reference

/-- Completing both defer owners before their child stream does not close that stream's key.
Witness: full Open at every stream value and closure, in split and joined actual runs,
using generated role separation as well as the source's stream-closure ordering.
-/
theorem complete_stream_references_open
    : ∀ batches ∈ [completeInputs, [completeInputs.flatten]],
        ∀ index event,
          ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[index]?
            = some event
          → ∀ key ∈ streamReferenceKeys event,
              Open
                ((initial.initialGroups ++ initial.initialStreams).map DeliveryNode.key)
                (((initial.runNormalized batches).2.flatten.flatMap publicationAtoms).take
                  index)
                key := by
  intro batches member index event atEvent key reference
  have valid : ValidGraphEvents work batches.flatten := by
    rcases List.mem_cons.mp member with same | last
    · subst batches; exact complete_inputs_valid_started.1
    · have same := List.mem_singleton.mp last
      subst batches
      simpa using complete_inputs_valid_started.1
  exact createWorkQueue_runNormalized_streamOpenAt generated valid atEvent reference

/-- The real mixed run uses one matching for freshness, item order, and producer release.
Witness: the general joint theorem applied to the complete generated execution; its stream
carrier at index two has the buffered producer already published in the strict prefix.
-/
theorem complete_joint_release_matching
    : let outputs := (initial.runNormalized completeInputs).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → PublicationAt work (matching index) event
              ∧ ¬Published matching (atoms.take index) (matching index)
              ∧ ∀ address first second,
                  matching index = .item address second
                  → first < second
                  → Published matching (atoms.take index) (.item address first))
        ∧ Published matching (atoms.take 2) producerTask := by
  obtain ⟨matching, batching, publications, released⟩ :=
    createWorkQueue_runNormalized_locatedStreamReleaseMatching generated
      complete_inputs_valid_started.1 complete_inputs_valid_started.2
  refine ⟨matching, batching, publications, ?_⟩
  obtain ⟨dependencies, occurrence, producer, earlier⟩ :=
    released 2 parent [] [stream] (by
      change ((initial.runNormalized completeInputs).2.flatten.flatMap publicationAtoms)[2]? = _
      rw [complete_output_atoms.2]
      rfl)
      stream List.mem_cons_self
  have same := Option.some.inj (generated.streamProducer_unique producer streamKnown rfl)
  subst occurrence
  exact earlier

/-- The later stream value retains its deferred task's prior publication under one matching.
Witness: apply the general stream-reference readiness theorem at the first actual item atom,
with the same matching that guarantees fresh publications throughout the mixed run.
-/
theorem complete_stream_reference_producer
    : let outputs := (initial.runNormalized completeInputs).2
      let atoms := outputs.flatten.flatMap publicationAtoms
      ∃ matching : PublicationMatching,
        WorkBatching atoms outputs
        ∧ (∀ index event,
            atoms[index]? = some event
            → IsValue event
            → ¬Published matching (atoms.take index) (matching index))
        ∧ Published matching (atoms.take 4) producerTask := by
  obtain ⟨matching, batching, values, _, references⟩ :=
    createWorkQueue_runNormalized_streamProducerReadinessMatching generated
      complete_inputs_valid_started.1 complete_inputs_valid_started.2
  refine ⟨matching, batching, fun index event atEvent value =>
    (values index event atEvent value).2.1, ?_⟩
  exact references 4 (.streamValues stream [⟨.scalar "x", 0⟩] [] [])
    (by
      change ((initial.runNormalized completeInputs).2.flatten.flatMap publicationAtoms)[4]? = _
      rw [complete_output_atoms.2]
      rfl)
    stream [parent.key] (some producerTask) List.mem_cons_self streamKnown producerTask
    rfl

/-- Successful closure accounts for all three items under the producer's own matching.
Witness: the general completion theorem for split and joined batches, retaining fresh
values and the earlier producer publication. The concrete closing atom is at index seven;
accounting holds for arbitrary cuts because each item is already published.
-/
theorem complete_stream_completion_accounted
    : ∀ batches ∈ [completeInputs, [completeInputs.flatten]],
        let outputs := (initial.runNormalized batches).2
        let atoms := outputs.flatten.flatMap publicationAtoms
        ∃ matching : PublicationMatching,
          WorkBatching atoms outputs
          ∧ (∀ index event,
              atoms[index]? = some event
              → IsValue event
              → ¬Published matching (atoms.take index) (matching index))
          ∧ Published matching (atoms.take 7) producerTask
          ∧ ∀ failures,
              NodeAccounted work matching (atoms.take 7) failures stream.key := by
  intro batches member
  have valid : ValidGraphEvents work batches.flatten := by
    rcases List.mem_cons.mp member with same | last
    · subst batches; exact complete_inputs_valid_started.1
    · have same := List.mem_singleton.mp last
      subst batches
      simpa using complete_inputs_valid_started.1
  have started : inputsStarted work batches = true := by
    rcases List.mem_cons.mp member with same | last
    · subst batches; exact complete_inputs_valid_started.2
    · have same := List.mem_singleton.mp last
      subst batches
      cbv
  have atSuccess
      : ((initial.runNormalized batches).2.flatten.flatMap publicationAtoms)[7]?
        = some (.streamSuccess stream) := by
    rcases List.mem_cons.mp member with rfl | last
    · cbv
    · have same := List.mem_singleton.mp last
      subst batches
      cbv
  obtain ⟨matching, batching, values, notices, closures⟩ :=
    createWorkQueue_runNormalized_streamCompletionMatching generated valid started
  have earlier := createWorkQueue_runNormalized_streamReference_producerPublished generated valid
    matching notices atSuccess List.mem_cons_self streamKnown rfl
  exact ⟨matching, batching,
    fun index event atEvent value => (values index event atEvent value).2.1, earlier,
    (closures 7 stream atSuccess).2⟩

/-- The real buffered stream registry retains its exact structural descriptor after completion.
Witness: the general replay registry theorem, independent of generated-key uniqueness and
start checking; the completed stream's descriptor remains in the permanent registry.
-/
theorem completed_stream_registry_located
    : (initial.runNormalized completeInputs).1.StreamsSatisfy (StreamLocated work)
      ∧ StreamLocated work stream := by
  have registry := createWorkQueue_runNormalized_streamsLocated complete_inputs_valid_started.1
  refine ⟨registry, ?_⟩
  apply registry ⟨stream⟩
  change (⟨stream⟩ : Stream) ∈ [⟨stream⟩]
  exact List.mem_cons_self

-----------------------------------------------------------------------------------------
-- Item-produced stream descriptors retain their generating item, not the outer stream key
-----------------------------------------------------------------------------------------

private def nestedStream : DeliveryNode := { key := 3, path := [.index 0] }

private def itemProducedWork : Execution.Work :=
  .stream stream [(.ok (.list [], 0), .stream nestedStream [])]

private def producingItem : StreamItem :=
  {
    occurrence := .item [] 0,
    value := ⟨.list [], 0⟩,
    work := Work.fromExecution (.stream nestedStream []) [0]
  }

/-- A matched item input locates its immediate child stream at that exact item producer.
Witness: the exact finite source descriptor and child lowering, followed by the general
item-stream provenance theorem. This raw source fixture needs no generated-work premise.
-/
theorem item_stream_retains_producer
    : NodeAt itemProducedWork nestedStream .stream []
        (some producingItem.occurrence) := by
  have matching : (GraphEvent.streamItems stream [producingItem]).MatchesWork itemProducedWork := by
    intro item member
    have same := List.mem_singleton.mp member
    subst item
    refine ⟨[stream.key], none, ?_, by cbv⟩
    exact ⟨stream, [(.ok (.list [], 0), .stream nestedStream [])], [],
      .ok (.list [], 0), .stream nestedStream [], Located.root, rfl, rfl, rfl⟩
  apply matching.streamItem_childStream_producer List.mem_cons_self
    (child := ⟨nestedStream⟩)
  exact List.mem_cons_self

-----------------------------------------------------------------------------------------
-- Prior announcement neither borrows the current notice nor asserts continued openness
-----------------------------------------------------------------------------------------

/-- A stream cannot justify its own reference with a child notice in the same event.
Witness: the ordered relation checks references before adding that event's notice keys.
This artificial trace tests the proof boundary, not an actual implementation output.
-/
theorem same_event_notice_is_not_prior
    : ¬ReferencesAnnounced streamNoticeKeys streamReferenceKeys []
        [.streamValues stream [⟨.scalar "x", 0⟩] [] [stream]] := by
  intro announced
  exact List.not_mem_nil (announced.1 List.mem_cons_self)

/-- Previously announced is deliberately weaker than still open.
Witness: this artificial trace references an initially known key after closing it; it
satisfies the bookkeeping relation but not Open. Actual closure freshness is a later proof.
-/
theorem prior_notice_does_not_imply_open
    : ReferencesAnnounced streamNoticeKeys streamReferenceKeys [stream.key]
        [.streamSuccess stream, .streamValues stream [⟨.scalar "x", 0⟩] [] []]
      ∧ ¬Open [stream.key] [.streamSuccess stream] stream.key := by
  constructor
  · simp [ReferencesAnnounced, streamNoticeKeys, streamReferenceKeys, List.Subset]
  · simp [Open, completedKeys, eventCompleted]

-----------------------------------------------------------------------------------------
-- Equal response payloads do not identify the producer in a publication inventory
-----------------------------------------------------------------------------------------

private def equalPayloadEvents : List WorkQueueEvent :=
  [
    .groupValues parent [producerValue],
    .groupSuccess parent [] [stream],
    .groupValues parent [producerValue]
  ]

/-- Swapping equal-payload labels preserves the erased output but can lose release support.
Witness: only the wrong task is in the strict prefix of the stream notice. This is an
inventory-boundary counterexample, not a claim that the queue emits this artificial trace.
-/
theorem equal_payloads_do_not_identify_producer
    : let right : List ObjectPublication :=
        [(producerTask, producerValue), (sharedTask, producerValue)]
      let wrong : List ObjectPublication :=
        [(sharedTask, producerValue), (producerTask, producerValue)]
      right.map Prod.snd = wrong.map Prod.snd
      ∧ wrong.map Prod.snd = equalPayloadEvents.flatMap WorkQueueEvent.objectValues
      ∧ StreamReleasePublications work right equalPayloadEvents
      ∧ ¬StreamReleasePublications work wrong equalPayloadEvents := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro index group groups streams atEvent noticed member dependencies producer known
    cases index with
    | zero => cases atEvent
    | succ index =>
        cases index with
        | zero =>
            simp only [equalPayloadEvents, List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq, Execution.WorkQueueEvent.groupSuccess.injEq] at atEvent
            obtain ⟨rfl, rfl, rfl⟩ := atEvent
            have same := List.mem_singleton.mp member
            subst noticed
            exact ⟨producerTask, generated.streamProducer_unique known streamKnown rfl,
              List.mem_cons_self⟩
        | succ index =>
            cases index with
            | zero => cases atEvent
            | succ index => simp [equalPayloadEvents] at atEvent
  · intro supported
    obtain ⟨occurrence, producer, earlier⟩ :=
      supported 1 parent [] [stream] rfl stream List.mem_cons_self
        [parent.key] (some producerTask) streamKnown
    have same := Option.some.inj producer
    subst occurrence
    simp [equalPayloadEvents, WorkQueueEvent.objectValues, producerTask, sharedTask] at earlier

/-- Publisher remapping retains the correct labels and still rejects the swapped inventory.
Witness: transport the raw witness without changing its labels; after normalization the
notice still precedes the second equally valued object publication.
-/
theorem normalized_equal_payloads_do_not_identify_producer
    : NormalizedStreamReleasePublications work
        [(producerTask, producerValue), (sharedTask, producerValue)]
        (publisher.normalizeBatch equalPayloadEvents).2
      ∧ ¬NormalizedStreamReleasePublications work
          [(sharedTask, producerValue), (producerTask, producerValue)]
          (publisher.normalizeBatch equalPayloadEvents).2 := by
  refine ⟨equal_payloads_do_not_identify_producer.2.2.1.normalizeBatch publisher, ?_⟩
  intro supported
  obtain ⟨occurrence, producer, earlier⟩ :=
    supported 1 parent [] [stream] rfl stream List.mem_cons_self
      [parent.key] (some producerTask) streamKnown
  have same := Option.some.inj producer
  subst occurrence
  change producerTask ∈ [sharedTask] at earlier
  simp [producerTask, sharedTask] at earlier

-----------------------------------------------------------------------------------------
-- Raw duplicate stream keys explain why producer identification uses generated work
-----------------------------------------------------------------------------------------

private def duplicateStreamWork : Execution.Work :=
  .combine
    (.executionGroup [⟨parent, []⟩] [] (.ok ([], 0)) (.stream stream []))
    (.executionGroup [⟨other, []⟩] [] (.ok ([], 0)) (.stream stream []))

/-- Permissive raw work can reuse a stream key below two distinct task producers.
Witness: two exact stream locations; generated allocation uniqueness must not be silently
assumed when reasoning about arbitrary work or introduced as a new host obligation.
-/
theorem raw_stream_producers_differ
    : NodeAt duplicateStreamWork stream .stream [parent.key] (some (.executionGroup [0]))
      ∧ NodeAt duplicateStreamWork stream .stream [other.key] (some (.executionGroup [1]))
      ∧ ¬ExecutedWork duplicateStreamWork := by
  have firstAt : NodeAt duplicateStreamWork stream .stream [parent.key]
      (some (.executionGroup [0])) := ⟨[0, 0], [], by cbv⟩
  have secondAt : NodeAt duplicateStreamWork stream .stream [other.key]
      (some (.executionGroup [1])) := ⟨[1, 0], [], by cbv⟩
  refine ⟨firstAt, secondAt, ?_⟩
  intro generated
  have impossible := generated.streamProducer_unique firstAt secondAt rfl
  cases impossible

end GraphQL.IncrementalDelivery.Tests.WorkSchedulerChildStreams
