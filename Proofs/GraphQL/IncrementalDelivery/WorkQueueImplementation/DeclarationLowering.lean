import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.ExecutionDeclarations
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.GraphEvents

/-! Ordered lowering retains the declaration contexts used by every task integration. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.DeclarationCoverage
open WorkQueueSemantics
open GraphQL.IncrementalDelivery.Execution (DeliveryNode DeferredFragment)
open Semantics.Ancestry (mapRefs)

/-- An empty plan annotation adds no registration candidates or task addresses.
Witness: lowering prepends the empty declaration list to the same work records.
-/
theorem fromExecution_empty_declarations (work : Execution.Work) (address : Address)
    : Work.fromExecution (.declareGroups [] work) address
      = Work.fromExecution work address :=
  rfl

/-- Ref inventory of actual registration candidates, independent of task contributors. -/
def candidateRefs (work : Work) : NodeRefs :=
  work.groups.map (fun group => group.node.ref)

/-- Every explicit immediate declaration is retained as a registration candidate. -/
theorem declarations_subset_candidates (work : Execution.Work) (address : Address)
    : (declarations work).Subset (candidateRefs (Work.fromExecution work address)) := by
  cases work with
  | empty | executionGroup | stream => intro ref member; cases member
  | combine left right =>
      intro ref member
      simp only [candidateRefs, Work.fromExecution, Work.combine, List.map_append]
      rcases List.mem_append.mp member with first | second
      · exact List.mem_append_left _ (declarations_subset_candidates left _ first)
      · exact List.mem_append_right _ (declarations_subset_candidates right _ second)
  | declareGroups groups tasks =>
      intro ref member
      simp only [candidateRefs, Work.fromExecution, List.map_append,
        List.map_map, Function.comp_def, Work.fromExecution.lowerGroup]
      rcases List.mem_append.mp member with first | second
      · obtain ⟨group, included, rfl⟩ := List.mem_map.mp first
        exact List.mem_append_left _ (List.mem_map_of_mem included)
      · exact List.mem_append_right _ (declarations_subset_candidates tasks _ second)
termination_by work

private theorem left_context {known : NodeRefs} (left right : Execution.Work)
    (address : Address)
    : ((known ++ declarations right)
        ++ candidateRefs (Work.fromExecution left (address ++ [0]))).Subset
        (known ++ candidateRefs (Work.fromExecution (.combine left right) address)) := by
  intro ref member
  simp only [candidateRefs, Work.fromExecution, Work.combine, List.map_append,
    List.mem_append] at member ⊢
  rcases member with (prior | declaration) | candidate
  · exact .inl prior
  · exact .inr (.inr (declarations_subset_candidates right _ declaration))
  · exact .inr (.inl candidate)

private theorem right_context {known : NodeRefs} (left right : Execution.Work)
    (address : Address)
    : ((known ++ declarations left)
        ++ candidateRefs (Work.fromExecution right (address ++ [1]))).Subset
        (known ++ candidateRefs (Work.fromExecution (.combine left right) address)) := by
  intro ref member
  simp only [candidateRefs, Work.fromExecution, Work.combine, List.map_append,
    List.mem_append] at member ⊢
  rcases member with (prior | declaration) | candidate
  · exact .inl prior
  · exact .inr (.inl (declarations_subset_candidates left _ declaration))
  · exact .inr (.inr candidate)

private theorem declaration_context {known : NodeRefs} (groups : List DeferredFragment)
    (tasks : Execution.Work) (address : Address)
    : ((known ++ mapRefs groups)
        ++ candidateRefs (Work.fromExecution tasks address)).Subset
        (known
          ++ candidateRefs
              (Work.fromExecution (.declareGroups groups tasks) address)) := by
  intro ref member
  simp only [candidateRefs, Work.fromExecution, List.map_append, List.map_map,
    Function.comp_def, Work.fromExecution.lowerGroup, mapRefs, List.mem_append] at member ⊢
  rcases member with (prior | declaration) | candidate
  · exact .inl prior
  · exact .inr (.inl declaration)
  · exact .inr (.inr candidate)

/-- A lowered task's contributors were declared earlier or accompany this integration. -/
theorem Certified.immediate {known work} (certified : Certified known work)
    (address : Address) {task : Task}
    (member : task ∈ (Work.fromExecution work address).tasks)
    {ref : NodeRef} (contributes : ref ∈ task.groups.map DeliveryNode.ref)
    : ref ∈ known ++ candidateRefs (Work.fromExecution work address) := by
  cases work with
  | empty | stream => cases member
  | combine left right =>
      rw [Certified] at certified
      rcases List.mem_append.mp member with first | second
      · exact left_context left right address
          (certified.1.immediate _ first contributes)
      · exact right_context left right address
          (certified.2.immediate _ second contributes)
  | declareGroups groups tasks =>
      rw [Certified] at certified
      exact declaration_context groups tasks address
        (certified.2.immediate address member contributes)
  | executionGroup groups path result children =>
      obtain rfl := List.mem_singleton.mp member
      rw [Certified] at certified
      exact List.mem_append_left _
        (certified.1
          (by simpa only [List.map_map, Function.comp_def, mapRefs] using contributes))
termination_by work

/-- Candidate parents were declared earlier or accompany this integration. -/
theorem Certified.parents {known work} (certified : Certified known work)
    (address : Address) {group : Group}
    (member : group ∈ (Work.fromExecution work address).groups)
    {parent : NodeRef} (same : group.parent = some parent)
    : parent ∈ known ++ candidateRefs (Work.fromExecution work address) := by
  cases work with
  | empty | stream => cases member
  | combine left right =>
      rw [Certified] at certified
      rcases List.mem_append.mp member with first | second
      · exact left_context left right address (certified.1.parents _ first same)
      · exact right_context left right address (certified.2.parents _ second same)
  | declareGroups groups tasks =>
      rw [Certified] at certified
      rcases List.mem_append.mp member with fresh | nested
      · obtain ⟨fragment, included, rfl⟩ := List.mem_map.mp fresh
        exact declaration_context groups tasks address
          (List.mem_append_left _ (certified.1 fragment included parent same))
      · exact declaration_context groups tasks address
          (certified.2.parents address nested same)
  | executionGroup => cases member
termination_by work

/-- Permanent task evidence retains the declaration context for its actual child chunk. -/
def TaskChildrenCertified (root : Execution.Work) (known : NodeRefs) (task : Task)
    : Prop :=
  ∀ address groups path result children producer owners,
    task.occurrence = .executionGroup address
    → Located root address (.executionGroup groups path result children) producer owners
    → Certified known children

/-- Previously registered refs may be retained when further groups are integrated. -/
theorem TaskChildrenCertified.mono {root known more task}
    (certified : TaskChildrenCertified root known task) (included : known.Subset more)
    : TaskChildrenCertified root more task := by
  intro address groups path result children producer owners same located
  exact (certified _ _ _ _ _ _ _ same located).mono included

/-- Integrating a certified chunk establishes the contexts of all newly registered tasks. -/
theorem Certified.children {known root current address producer owners}
    (certified : Certified known current)
    (located : Located root address current.withoutDeclarations producer owners)
    {task : Task}
    (member : task ∈ (Work.fromExecution current address).tasks)
    : TaskChildrenCertified root
        (known ++ candidateRefs (Work.fromExecution current address)) task := by
  cases current with
  | empty | stream => cases member
  | combine left right =>
      rw [Certified] at certified
      rcases List.mem_append.mp member with first | second
      · exact (certified.1.children located.left first).mono
          (left_context left right address)
      · exact (certified.2.children located.right second).mono
          (right_context left right address)
  | declareGroups groups tasks =>
      rw [Certified] at certified
      exact (certified.2.children located member).mono
        (declaration_context groups tasks address)
  | executionGroup groups path result children =>
      obtain rfl := List.mem_singleton.mp member
      intro query otherGroups otherPath otherResult otherChildren otherProducer otherOwners same actual
      have sameAddress : address = query := Occurrence.executionGroup.inj same
      subst query
      have sameLocation := congrArg WorkLocation.current (Option.some.inj (located.symm.trans actual))
      cases sameLocation
      rw [Certified] at certified
      exact certified.2.mono (List.subset_append_left _ _)
termination_by current

/-- Normalizing an address can remove metadata, while retaining an extended context. -/
theorem Certified.withoutDeclarations {known work} (certified : Certified known work)
    : ∃ more, Certified more work.withoutDeclarations := by
  cases work with
  | declareGroups groups tasks =>
      rw [Certified] at certified
      exact certified.2.withoutDeclarations
  | _ => exact ⟨known, certified⟩
termination_by work

/-- Any actual stream item's child chunk has no inherited defer declarations. -/
theorem Certified.streamItem
    {known root address node items producer owners result children} {index : Nat}
    (certified : Certified known root)
    (located : Located root address (.stream node items) producer owners)
    (entry : items[index]? = some (result, children))
    : Certified [] children := by
  have context {address current birth enclosing}
      (navigation : StructuralEquivalence.Located root address current birth enclosing)
      : ∃ more, Certified more current := by
    induction navigation with
    | root => exact certified.withoutDeclarations
    | left _ ih =>
        obtain ⟨more, localKnown⟩ := ih
        rw [Certified] at localKnown
        exact localKnown.1.withoutDeclarations
    | right _ ih =>
        obtain ⟨more, localKnown⟩ := ih
        rw [Certified] at localKnown
        exact localKnown.2.withoutDeclarations
    | executionGroup _ ih =>
        obtain ⟨more, localKnown⟩ := ih
        rw [Certified] at localKnown
        exact localKnown.2.withoutDeclarations
    | item _ selected ih =>
        obtain ⟨more, localKnown⟩ := ih
        rw [Certified] at localKnown
        exact (localKnown _ (List.mem_of_getElem? selected)).withoutDeclarations
  obtain ⟨more, localKnown⟩ := context (StructuralEquivalence.located_of_current located)
  rw [Certified] at localKnown
  exact localKnown _ (List.mem_of_getElem? entry)

/-- A supplied runtime chunk retains task owners and future child contexts. -/
structure WorkCertificate (root : Execution.Work) (known : NodeRefs) (chunk : Work)
    : Prop where
  contributors
    : ∀ task ∈ chunk.tasks,
      ∀ ref ∈ task.groups.map DeliveryNode.ref,
        ref ∈ known ∨ ∃ group ∈ chunk.groups, group.node.ref = ref
  parents
    : ∀ group ∈ chunk.groups,
        ∀ parent,
          group.parent = some parent
          → parent ∈ known ∨ ∃ candidate ∈ chunk.groups, candidate.node.ref = parent
  children
    : ∀ task ∈ chunk.tasks, TaskChildrenCertified root (known ++ candidateRefs chunk) task

/-- Lowering preserves both immediate and future registration evidence. -/
theorem Certified.lower {known root current address producer owners}
    (certified : Certified known current)
    (located : Located root address current.withoutDeclarations producer owners)
    : WorkCertificate root known (Work.fromExecution current address) := by
  constructor
  · intro task member ref contributes
    rcases List.mem_append.mp (certified.immediate address member contributes) with prior | candidate
    · exact .inl prior
    · exact .inr (List.mem_map.mp candidate)
  · intro group member parent same
    rcases List.mem_append.mp (certified.parents address member same) with prior | candidate
    · exact .inl prior
    · exact .inr (List.mem_map.mp candidate)
  · exact fun task member => certified.children located member

/-- A registered producer's certified context licenses the exact supplied child chunk. -/
theorem TaskChildrenCertified.sourceChild {root known task occurrence result}
    (certified : TaskChildrenCertified root known task)
    (same : task.occurrence = occurrence)
    (matching : (GraphEvent.taskSuccess occurrence result).MatchesWork root)
    : WorkCertificate root known result.work := by
  obtain ⟨_, producer, known, _, childrenWork⟩ := matching
  cases occurrence with
  | item => cases childrenWork
  | executionGroup address =>
      obtain ⟨groups, path, outcome, children, enclosing, located, _, _⟩ := known
      change locateWork root address = some
        ⟨.executionGroup groups path outcome children, producer, enclosing⟩ at located
      have lowering : result.work = Work.fromExecution children (address ++ [0]) := by
        simpa [taskChildWork?_eq_lookup, located] using childrenWork.symm
      rw [lowering]
      exact (certified _ _ _ _ _ _ _ same located).lower
        (Located.executionGroup (root := root) located)

/-- Stream items reset the defer context and certify their own fresh registration chunk. -/
theorem Certified.sourceStreamItem {known root stream items}
    (certified : Certified known root)
    (matching : (GraphEvent.streamItems stream items).MatchesWork root)
    {item : StreamItem} (member : item ∈ items) (registered : NodeRefs)
    : WorkCertificate root registered item.work := by
  obtain ⟨_, producer, known, childrenWork⟩ := matching item member
  cases occurrence : item.occurrence with
  | executionGroup => simp [streamItemWork?_eq_lookup, occurrence] at childrenWork
  | item address index =>
      rw [occurrence] at known
      obtain ⟨node, entries, enclosing, result, children, located, entry, _, _⟩ := known
      change locateWork root address = some ⟨.stream node entries, producer, enclosing⟩ at located
      have lowering : item.work = Work.fromExecution children (address ++ [index]) := by
        simpa [streamItemWork?_eq_lookup, occurrence, located, entry]
          using childrenWork.symm
      have childKnown := certified.streamItem located entry
      rw [lowering]
      exact (childKnown.mono (by intro ref impossible; cases impossible)).lower
        (Located.item located entry)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.DeclarationCoverage

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics DeclarationCoverage
open GraphQL.IncrementalDelivery.Execution (DeliveryNode)

/-- Pure root execution supplies the declaration certificate without a source assumption. -/
theorem ExecutedWork.declarations {work : Execution.Work} (generated : ExecutedWork work)
    : Certified [] work := by
  obtain ⟨ObjectRef, schema, resolvers, variables, fuel, parentType, source, selections, same⟩ := generated
  exact same ▸ (executeRoot_declarations schema resolvers variables fuel parentType source selections 0).1

/-- Generated root work declares every immediate task contributor during initialization. -/
theorem ExecutedWork.immediateGroupsCoverTasks {work : Execution.Work}
    (generated : ExecutedWork work) (address : Address)
    {task : Task} (member : task ∈ (Work.fromExecution work address).tasks)
    {ref : NodeRef} (contributes : ref ∈ task.groups.map DeliveryNode.ref)
    : ∃ group ∈ (Work.fromExecution work address).groups, group.node.ref = ref := by
  have covered := (ExecutedWork.declarations generated).immediate address member contributes
  exact List.mem_map.mp ((List.mem_append.mp covered).resolve_left (by simp))

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
