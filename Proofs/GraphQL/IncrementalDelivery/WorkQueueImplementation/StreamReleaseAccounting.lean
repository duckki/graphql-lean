import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ChildStreamProvenance

/-! Stream release refers to earlier entries in the same occurrence-labelled inventory. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open GraphQL.IncrementalDelivery.Execution (WorkQueueEvent)
open GraphQL.IncrementalDelivery.WorkQueueSemantics

-----------------------------------------------------------------------------------------
-- Release support uses publication occurrences, not equality of response payloads
-----------------------------------------------------------------------------------------

/-- A group's stream notice refers to a producer already in the strict output prefix's
object-publication inventory. `published` labels object values in `events`, in order;
the inventory's exact payload projection is supplied by the accompanying ledger theorem.
-/
def StreamReleasePublications (work : Execution.Work) (published : List ObjectPublication)
    (events : List WorkQueueEvent)
    : Prop :=
  ∀ index group groups streams,
    events[index]? = some (.groupSuccess group groups streams)
    → ∀ stream ∈ streams,
        ∀ dependencies producer,
          NodeAt work stream .stream dependencies producer
          → ∃ occurrence,
              producer = some occurrence
              ∧ occurrence
                ∈ (published.take
                    ((events.take index).flatMap WorkQueueEvent.objectValues).length).map
                    Prod.fst

/-- Empty output has no stream release to justify.
Witness: no index selects an event from an empty list. -/
theorem StreamReleasePublications.nil (work : Execution.Work)
    : StreamReleasePublications work [] [] := by
  intro index group groups streams impossible
  simp at impossible

/-- Concatenation preserves release support in one concatenated publication inventory.
Witness: split the carrier's index between the two output segments. The exact first
payload projection identifies the inventory offset of every carrier in the second.
-/
theorem StreamReleasePublications.append {work first second left right}
    (before : StreamReleasePublications work first left)
    (after : StreamReleasePublications work second right)
    (values : first.map Prod.snd = left.flatMap WorkQueueEvent.objectValues)
    : StreamReleasePublications work (first ++ second) (left ++ right) := by
  have size : first.length = (left.flatMap WorkQueueEvent.objectValues).length := by
    simpa only [List.length_map] using congrArg List.length values
  intro index group groups streams atEvent stream member dependencies producer known
  by_cases earlier : index < left.length
  · have atLeft := (List.getElem?_append_left earlier).symm.trans atEvent
    obtain ⟨occurrence, same, published⟩ :=
      before index group groups streams atLeft stream member dependencies producer known
    have count : ((left.take index).flatMap WorkQueueEvent.objectValues).length ≤ first.length := by
      have split := congrArg (fun events : List WorkQueueEvent =>
        (events.flatMap WorkQueueEvent.objectValues).length) (List.take_append_drop index left)
      simp only [List.flatMap_append, List.length_append] at split
      omega
    refine ⟨occurrence, same, ?_⟩
    rw [List.take_append_of_le_length (Nat.le_of_lt earlier),
      List.take_append_of_le_length count]
    exact published
  · have later : left.length ≤ index := by omega
    have atRight := (List.getElem?_append_right later).symm.trans atEvent
    obtain ⟨occurrence, same, published⟩ := after (index - left.length) group groups streams
      atRight stream member dependencies producer known
    refine ⟨occurrence, same, ?_⟩
    rw [List.take_append (l₁ := left), List.take_of_length_le later, List.flatMap_append,
      List.length_append, ← size, List.take_append (l₁ := first)]
    simp only [List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.map_append]
    exact List.mem_append_right _ published

/-- One flush's common selection places every released stream producer before its carrier.
Witness: all selected successful values precede the sole group-success event, and their
occurrence-labelled inventory has exactly that value-list length. -/
theorem StreamReleasePublications.flush {work : Execution.Work}
    (published : List ObjectPublication) (group : Execution.DeliveryNode)
    (groups streams : List Execution.DeliveryNode)
    (supported
      : ∀ stream ∈ streams,
          ∀ dependencies producer,
            NodeAt work stream .stream dependencies producer
            → ∃ occurrence,
                producer = some occurrence ∧ occurrence ∈ published.map Prod.fst)
    : StreamReleasePublications work published
        ((if (published.map Prod.snd).isEmpty then
            []
          else
            [.groupValues group (published.map Prod.snd)])
          ++ [.groupSuccess group groups streams]) := by
  intro index trigger newGroups newStreams atEvent stream member dependencies producer known
  cases published with
  | nil =>
      have same : index = 0 := by
        by_cases equal : index = 0
        · exact equal
        · simp [equal] at atEvent
      subst index
      simp only [List.map_nil, List.isEmpty_nil, ↓reduceIte, List.nil_append,
        List.getElem?_cons_zero, Option.some.injEq, Execution.WorkQueueEvent.groupSuccess.injEq] at atEvent
      obtain ⟨rfl, rfl, rfl⟩ := atEvent
      obtain ⟨_, _, impossible⟩ := supported stream member dependencies producer known
      cases impossible
  | cons head rest =>
      cases index with
      | zero => simp at atEvent
      | succ index =>
          have zero : index = 0 := by
            by_cases equal : index = 0
            · exact equal
            · simp [equal] at atEvent
          subst index
          simp only [List.map_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
            List.cons_append, List.nil_append, List.getElem?_cons_succ,
            List.getElem?_cons_zero, Option.some.injEq,
            Execution.WorkQueueEvent.groupSuccess.injEq] at atEvent
          obtain ⟨rfl, rfl, rfl⟩ := atEvent
          obtain ⟨occurrence, same, published⟩ :=
            supported stream member dependencies producer known
          refine ⟨occurrence, same, ?_⟩
          simpa [WorkQueueEvent.objectValues] using published

-----------------------------------------------------------------------------------------
-- The flush witness extends freshness and release support with the same labels
-----------------------------------------------------------------------------------------

/-- A successful flush supplies one inventory for both freshness and stream release.
Witness: use a single executable node selection for value labels and child refs. The
settled-link invariant gives each selected producer a value; structural provenance and
generated ref uniqueness identify it as the released stream's producer.
-/
theorem State.PublicationInventory.finishGroupSuccess_streamRelease {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (settled : queue.ChildStreamsSettled) (links : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) (group : GroupNode)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.finishGroupSuccess group).2.1.flatMap WorkQueueEvent.objectValues
        ∧ (queue.finishGroupSuccess group).1.PublicationInventory property
            (published ++ added)
        ∧ StreamReleasePublications work added (queue.finishGroupSuccess group).2.1 := by
  obtain ⟨selected, unique, known, events, retained, absent, released⟩ :=
    queue.finishGroupSuccess_selection group
  obtain ⟨values, final⟩ := inventory.finishGroupSuccess_selected
    group selected unique known events retained absent
  refine ⟨storedPublications selected, values, final, ?_⟩
  rw [events, ← storedPublications_values]
  apply StreamReleasePublications.flush
  intro stream member dependencies producer structural
  obtain ⟨node, selectedNode, linked⟩ := released stream member
  have inQueue := (known node selectedNode).1
  have same := links.producer generated inQueue structural linked
  cases stored : node.value with
  | none =>
      have empty := settled node inQueue stored
      simp [empty] at linked
  | some value =>
      refine ⟨node.task.occurrence, same, ?_⟩
      apply List.mem_map.mpr
      refine ⟨(node.task.occurrence, value), ?_, rfl⟩
      exact List.mem_filterMap.mpr ⟨node, selectedNode, by simp [stored]⟩

-----------------------------------------------------------------------------------------
-- One common inventory passes through every contributor in the real success handler
-----------------------------------------------------------------------------------------

/-- Recursive draining publishes each released stream's producer before its carrier.
Witness: one common selection per successful flush extends both the inventory and release
support; failed closures emit no stream notices, and later drains preserve earlier offsets.
-/
theorem State.PublicationInventory.drainReadyGroups_streamRelease {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (settled : queue.ChildStreamsSettled) (links : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd = queue.drainReadyGroups.2.flatMap WorkQueueEvent.objectValues
        ∧ queue.drainReadyGroups.1.PublicationInventory property (published ++ added)
        ∧ StreamReleasePublications work added queue.drainReadyGroups.2 := by
  have loop (fuel : Nat) (current : State) (priorPublished : List ObjectPublication)
      (prior : current.PublicationInventory property priorPublished)
      (ready : current.ChildStreamsSettled) (childLinks : current.ChildStreamsMatchWork work)
      : ∃ added : List ObjectPublication,
          added.map Prod.snd
            = (State.drainReadyGroups.go fuel current).2.flatMap WorkQueueEvent.objectValues
          ∧ (State.drainReadyGroups.go fuel current).1.PublicationInventory property
              (priorPublished ++ added)
          ∧ StreamReleasePublications work added (State.drainReadyGroups.go fuel current).2 := by
    induction fuel generalizing current priorPublished with
    | zero =>
        exact ⟨
          [],
          rfl,
          by simpa only [State.drainReadyGroups.go, List.append_nil] using prior,
          StreamReleasePublications.nil work
        ⟩
    | succ fuel ih =>
        unfold State.drainReadyGroups.go
        dsimp only
        split
        · exact ⟨[], rfl, by simpa using prior, StreamReleasePublications.nil work⟩
        · rename_i node selected
          cases cached : node.failure with
          | none =>
              dsimp only
              obtain ⟨first, firstValues, flushed, firstSupport⟩ :=
                prior.finishGroupSuccess_streamRelease ready childLinks generated node
              obtain ⟨later, laterValues, final, laterSupport⟩ := ih _ _
                ⟨flushed.unique, flushed.provenance,
                  flushed.stored.startNewWork (current.finishGroupSuccess node).2.2⟩
                ((ready.finishGroupSuccess node).startNewWork _)
                ((childLinks.finishGroupSuccess node).startNewWork _)
              refine ⟨first ++ later, ?_, ?_, firstSupport.append laterSupport firstValues⟩
              · simp only [List.map_append, List.flatMap_append, firstValues, laterValues]
              · simpa only [List.append_assoc] using final
          | some errors =>
              dsimp only
              obtain ⟨added, values, final, supported⟩ := ih _ _
                ⟨prior.unique, prior.provenance, prior.stored.removeGroup _⟩
                (ready.removeGroup _) (childLinks.removeGroup _)
              have control : StreamReleasePublications work []
                  [(current.finishGroupFailure node errors).2] := by
                intro index group groups streams atEvent
                cases index <;> simp [State.finishGroupFailure] at atEvent
              refine ⟨added, ?_, final, ?_⟩
              · simpa only [State.finishGroupFailure, List.flatMap_append,
                  List.flatMap_singleton, WorkQueueEvent.objectValues, List.nil_append]
                  using values
              · exact control.append supported rfl
  exact loop _ queue published inventory settled links

/-- One contributor step preserves stream links and extends one common publication ledger.
Witness: a flushing branch appends its joint value/release selection; nonflushing branches
only update counters. Release offsets are calculated from the exact earlier value count.
-/
theorem successGroupStep_streamRelease {work property published}
    (generated : ExecutedWork work) (acc : State × List WorkQueueEvent × NewWork)
    (group : Execution.DeliveryNode) (settled : acc.1.ChildStreamsSettled)
    (links : acc.1.ChildStreamsMatchWork work) {added : List ObjectPublication}
    (values : added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues)
    (inventory : acc.1.PublicationInventory property (published ++ added))
    (supported : StreamReleasePublications work added acc.2.1)
    : (successGroupStep acc group).1.ChildStreamsSettled
      ∧ (successGroupStep acc group).1.ChildStreamsMatchWork work
      ∧ ∃ next : List ObjectPublication,
          next.map Prod.snd
            = (successGroupStep acc group).2.1.flatMap WorkQueueEvent.objectValues
          ∧ (successGroupStep acc group).1.PublicationInventory property
              (published ++ next)
          ∧ StreamReleasePublications work next (successGroupStep acc group).2.1 := by
  obtain ⟨queue, events, released⟩ := acc
  dsimp only [successGroupStep]
  split
  · exact ⟨settled, links, added, values, inventory, supported⟩
  · rename_i node found
    let updated := { node with pending := node.pending - 1 }
    have current := inventory.putGroupNode updated
    have currentSettled := settled.putGroupNode updated
    have currentLinks := links.putGroupNode updated
    split
    · obtain ⟨extra, extraValues, final, releasedSupport⟩ :=
        current.finishGroupSuccess_streamRelease currentSettled currentLinks generated updated
      refine ⟨currentSettled.finishGroupSuccess updated, currentLinks.finishGroupSuccess updated,
        added ++ extra, ?_, ?_, supported.append releasedSupport values⟩
      · simp only [List.map_append, List.flatMap_append, values, extraValues]
        rfl
      · simpa only [List.append_assoc] using final
    · exact ⟨currentSettled, currentLinks, added, values, current, supported⟩

/-- The actual task-success handler publishes each released stream's structural producer
before its notice, using the same labels as its fresh object-publication inventory.
Witness: install the input once, then thread the joint ledger through the single-pass
contributor fold, released-work activation, and the final recursive drain.
-/
theorem State.PublicationInventory.taskSuccess_streamRelease {queue : State}
    {work property published} (inventory : queue.PublicationInventory property published)
    (settled : queue.ChildStreamsSettled) (links : queue.ChildStreamsMatchWork work)
    (generated : ExecutedWork work) {occurrence result}
    (source : (GraphEvent.taskSuccess occurrence result).MatchesWork work)
    (allowed : property occurrence result.value)
    (fresh : occurrence ∉ published.map Prod.fst)
    : ∃ added : List ObjectPublication,
        added.map Prod.snd
          = (queue.taskSuccess occurrence result).2.flatMap WorkQueueEvent.objectValues
        ∧ (queue.taskSuccess occurrence result).1.PublicationInventory property
            (published ++ added)
        ∧ StreamReleasePublications work added
            (queue.taskSuccess occurrence result).2 := by
  cases found : queue.taskNode? occurrence with
  | none =>
      simp only [State.taskSuccess, found]
      refine ⟨[], rfl, ?_, StreamReleasePublications.nil work⟩
      simpa only [List.append_nil] using inventory
  | some node =>
      obtain ⟨member, same⟩ := State.taskNode?_some found
      have installed := inventory.stored.putTaskNode { node with value := some result.value } (by
        intro value equal
        cases equal
        simpa only [same] using And.intro allowed fresh)
      have integrated := installed.maybeIntegrateWork result.work (some occurrence)
      have integratedSettled := settled.integrateSuccess found result
      have integratedLinks := (links.putTaskNode { node with value := some result.value }
        (links node member)).maybeIntegrateWork result.work (some occurrence) (by
          intro producer sameProducer stream supplied
          cases sameProducer
          exact source.childStream_producer supplied)
      let invariant := fun acc : State × List WorkQueueEvent × NewWork =>
        acc.1.ChildStreamsSettled ∧ acc.1.ChildStreamsMatchWork work
        ∧ ∃ added : List ObjectPublication,
            added.map Prod.snd = acc.2.1.flatMap WorkQueueEvent.objectValues
            ∧ acc.1.PublicationInventory property (published ++ added)
            ∧ StreamReleasePublications work added acc.2.1
      have loop (groups : List Execution.DeliveryNode) (acc : State × List WorkQueueEvent × NewWork)
          (prior : invariant acc) : invariant (groups.foldl successGroupStep acc) := by
        induction groups generalizing acc with
        | nil => exact prior
        | cons group rest ih =>
            obtain ⟨ready, childLinks, added, exactValues, ledger, releaseSupport⟩ := prior
            exact ih _ (successGroupStep_streamRelease generated acc group ready childLinks
              exactValues ledger releaseSupport)
      have initialLedger : PublicationInventory
          ((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
            result.work (some occurrence)).1 property (published ++ []) := by
        simpa only [List.append_nil]
          using State.PublicationInventory.mk inventory.unique inventory.provenance
            integrated
      obtain ⟨ready, childLinks, added, values, final, supported⟩ :=
        loop node.task.groups (_, [], {})
          ⟨integratedSettled, integratedLinks, [], rfl, initialLedger,
            StreamReleasePublications.nil work⟩
      rw [queue.taskSuccess_eq occurrence result node found]
      split
      · refine ⟨[], rfl, ?_, ?_⟩
        · simpa only [List.append_nil]
            using State.PublicationInventory.mk inventory.unique inventory.provenance
              (inventory.stored.removeTask occurrence)
        · exact StreamReleasePublications.nil work
      let released := node.task.groups.foldl successGroupStep
        (((queue.putTaskNode { node with value := some result.value }).maybeIntegrateWork
          result.work (some occurrence)).1, [], {})
      have activated := State.PublicationInventory.mk final.unique final.provenance
        (final.stored.startNewWork released.2.2)
      obtain ⟨later, laterValues, drained, laterSupport⟩ :=
        activated.drainReadyGroups_streamRelease (ready.startNewWork _)
          (childLinks.startNewWork _) generated
      refine ⟨added ++ later, ?_, ?_, supported.append laterSupport values⟩
      · simp only [List.map_append, List.flatMap_append, values, laterValues]
        rfl
      · simpa only [List.append_assoc] using drained

-----------------------------------------------------------------------------------------
-- Valid source replay supplies every state premise at an actual next-handler boundary
-----------------------------------------------------------------------------------------

/-- A legal next task success extends the real replay's occurrence inventory with release
support at every emitted group-success position. Witness: prior replay supplies stored
values and links; source freshness permits the new value; the joint handler theorem
retains exact prior/next payload projections, provenance, and global occurrence uniqueness.
No full-history admission or producer-publication hypothesis is assumed.
-/
theorem createWorkQueue_runNormalized_taskSuccess_streamRelease {work : Execution.Work}
    {batches : List (List GraphEvent)} (generated : ExecutedWork work)
    {occurrence result}
    (valid : ValidGraphEvents work (batches.flatten ++ [.taskSuccess occurrence result]))
    : let before := (State.initialize (Work.fromExecution work)).runNormalized batches
      ∃ published added : List ObjectPublication,
        published.map (fun publication => publication.2)
          = before.2.flatten.flatMap normalizedObjectValues
        ∧ added.map Prod.snd
          = (before.1.taskSuccess occurrence result).2.flatMap WorkQueueEvent.objectValues
        ∧ ((published ++ added).map Prod.fst).Nodup
        ∧ (∀ publication ∈ published ++ added,
            ObjectValueFrom (batches.flatten ++ [.taskSuccess occurrence result])
              publication.1 publication.2)
        ∧ StreamReleasePublications work added
            (before.1.taskSuccess occurrence result).2 := by
  have priorValid := valid.prefix (List.prefix_append _ _)
  obtain ⟨source, fresh, _⟩ := valid.atPrefix
    (before := batches.flatten) (event := .taskSuccess occurrence result) ⟨[], by simp⟩
  obtain ⟨published, priorValues, inventory⟩ :=
    createWorkQueue_runNormalized_publications priorValid
  have newInventory := inventory.mono (fun _ _ old =>
    old.mono (List.subset_append_left _ [GraphEvent.taskSuccess occurrence result]))
  obtain ⟨added, values, final, supported⟩ := newInventory.taskSuccess_streamRelease
    (createWorkQueue_runNormalized_childStreamsSettled _ _)
    (createWorkQueue_runNormalized_childStreamsMatchWork priorValid) generated source
    ⟨result, List.mem_append_right _ List.mem_cons_self, rfl⟩ (inventory.fresh_success fresh)
  exact ⟨published, added, priorValues, values, final.unique, final.provenance, supported⟩

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
