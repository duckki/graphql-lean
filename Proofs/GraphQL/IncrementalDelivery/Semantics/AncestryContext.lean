import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedAncestry

/-! Deferred execution contexts are preserved during nested field collection.
Support is stated first on raw usage ancestors, then transported through the coherent
ref assignment to all future work owned by the current execution group.
-/

namespace GraphQL.IncrementalDelivery.Semantics.Ancestry

open GraphQL.IncrementalDelivery.Execution

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

def UsageUnder (owners : List Nat) (usage : DeferUsage) : Prop :=
  ∃ owner ∈ owners, owner = usage.ref ∨ owner ∈ usage.ancestors

def OptionalUnder (owners : List Nat) (usage : Option DeferUsage) : Prop :=
  owners = [] ∨ ∃ actual, usage = some actual ∧ UsageUnder owners actual

def FieldsUnder (owners : List Nat) (fields : List FieldDetails) : Prop :=
  ∀ field ∈ fields, OptionalUnder owners field.deferUsage

def GroupsUnder (owners : List Nat) (groups : CollectedFieldsMap) : Prop :=
  GroupsSatisfy (fun field => OptionalUnder owners field.deferUsage) groups

theorem optionalUnder_fresh (owners : List Nat) (parent : Option DeferUsage)
    (ref : NodeRef) (label : Option DirectiveLabel) (h : OptionalUnder owners parent)
    : OptionalUnder owners
        (some
          {
            ref,
            label,
            ancestors := (parent.map (fun usage => usage.ref :: usage.ancestors)).getD []
          }) := by
  rcases h with h | ⟨usage, rfl, owner, ho, hu⟩
  · exact Or.inl h
  · refine Or.inr ⟨_, rfl, owner, ho, Or.inr ?_⟩
    simpa only [Option.map_some, Option.getD_some, List.mem_cons] using hu

mutual
  theorem collectSelection_under (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (usage : Option DeferUsage) (owners : List Nat) (state : Nat)
      (h : OptionalUnder owners usage)
      : GroupsUnder owners
          ((collectSelection schema variables parentType source usage selection).run
            state).1.collectedFieldsMap := by
    cases selection with
    | field name fieldName arguments directives children =>
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, ha, GroupsUnder, GroupsSatisfy, h]
    | inlineFragment condition directives children =>
        cases ha : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, ha, GroupsUnder, GroupsSatisfy]
        · cases ht : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, ha, ht, GroupsUnder, GroupsSatisfy]
          · cases hd : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, ha, ht, hd]
                  using collectFields_under schema variables parentType source children
                    usage owners state h
            | some label =>
                simpa [collectSelection, ha, ht, hd, freshNodeRef]
                  using collectFields_under schema variables parentType source children _
                    owners (state + 1) (optionalUnder_fresh owners usage state label h)
  termination_by sizeOf selection

  theorem collectFields_under (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (owners : List Nat) (state : Nat)
      (h : OptionalUnder owners usage)
      : GroupsUnder owners
          ((collectFields schema variables parentType source selections usage).run
            state).1.collectedFieldsMap := by
    cases selections with
    | nil => simp [collectFields, GroupsUnder, GroupsSatisfy]
    | cons selection rest =>
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq, FieldCollection.append]
        exact groupsSatisfy_merge _ _ _
          (collectSelection_under schema variables parentType source selection usage owners state h)
          (collectFields_under schema variables parentType source rest usage owners _ h)
  termination_by sizeOf selections
end

theorem collectSubfields_under (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    (owners : List Nat) (state : Nat) (h : FieldsUnder owners fields)
    : GroupsUnder owners
        ((collectSubfields schema variables parentType source fields).run
          state).1.collectedFieldsMap := by
  induction fields generalizing state with
  | nil => simp [collectSubfields, GroupsUnder, GroupsSatisfy]
  | cons field rest ih =>
      simp only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq, FieldCollection.append]
      exact groupsSatisfy_merge _ _ _
        (collectFields_under schema variables parentType source field.selectionSet
          field.deferUsage owners state (h field (by simp)))
        (ih _ (fun f hf => h f (List.mem_cons_of_mem field hf)))

def Scoped (parents : Assignment) (owners : List Nat) (work : Work) : Prop :=
  owners = [] ∨ WorkUnder parents owners work

def PartitionsAt (parents : Assignment) (deferMap : DeferMap) (owners : List Nat)
    (partitions : List (List Nat × CollectedFieldsMap))
    : Prop :=
  ∀ partition ∈ partitions,
    partition.1 ≠ []
    ∧ partition.1.Subset (mapRefs deferMap)
    ∧ GroupsUnder partition.1 partition.2
    ∧ (owners = [] ∨ ∀ ref ∈ partition.1, Descends parents owners ref)

theorem mapAt_ref_bound {parents : Assignment} {bound : Nat} {deferMap : DeferMap}
    (hm : MapAt parents bound deferMap) {ref : NodeRef} (hk : ref ∈ mapRefs deferMap)
    : ref < bound := by
  obtain ⟨fragment, hf, he⟩ := List.mem_map.mp hk
  simpa only [he] using (hm fragment hf).1.1

theorem PartitionsAt.extend {parents next : Assignment} {start finish : Nat}
    {deferMap : DeferMap} {owners : List Nat}
    {partitions : List (List Nat × CollectedFieldsMap)}
    (h : PartitionsAt parents deferMap owners partitions)
    (hm : MapAt parents start deferMap) (he : Extends start parents next)
    (_hle : start ≤ finish)
    : PartitionsAt next deferMap owners partitions := by
  intro partition hp
  have hh := h partition hp
  refine ⟨hh.1, hh.2.1, hh.2.2.1, ?_⟩
  rcases hh.2.2.2 with h | h
  · exact Or.inl h
  · refine Or.inr (fun ref hk => ?_)
    simpa only [Descends, he ref (mapAt_ref_bound hm (hh.2.1 hk))] using h ref hk

theorem filterMap_fragment_refs (deferMap : DeferMap) (refs : List Nat)
    (hk : refs.Subset (mapRefs deferMap))
    : mapRefs (refs.filterMap (lookupDeferredFragment? deferMap)) = refs := by
  induction refs with
  | nil => rfl
  | cons ref rest ih =>
      obtain ⟨fragment, hf⟩ := lookup_exists (hk (by simp : ref ∈ ref :: rest))
      have hrest : rest.Subset (mapRefs deferMap) := by
        intro next hn
        exact hk (List.mem_cons_of_mem ref hn)
      simpa [hf, mapRefs, lookup_ref hf] using congrArg (List.cons ref) (ih hrest)

theorem filterMap_fragmentAt {parents : Assignment} {bound : Nat} {deferMap : DeferMap}
    (hm : MapAt parents bound deferMap) (refs : List Nat) (fragment : DeferredFragment)
    (hf : fragment ∈ refs.filterMap (lookupDeferredFragment? deferMap))
    : FragmentAt parents bound fragment := by
  obtain ⟨ref, _, hf⟩ := List.mem_filterMap.mp hf
  exact (hm fragment (List.mem_of_find?_eq_some hf)).1

theorem WorkUnder.extend {parents next : Assignment} {start finish : Nat}
    {owners : List Nat} {work : Work} (h : WorkUnder parents owners work)
    (hw : WorkAt parents start work) (he : Extends start parents next)
    (hle : start ≤ finish)
    : WorkUnder next owners work := by
  cases work with
  | empty => trivial
  | combine left right => exact ⟨h.1.extend hw.1 he hle, h.2.extend hw.2 he hle⟩
  | executionGroup groups path result children =>
      refine ⟨?_, h.2.extend hw.2.2.2 he hle⟩
      intro group hg
      obtain ⟨owner, ho, hh⟩ := h.1 group hg
      exact ⟨owner, ho, by simpa only [he group.node.ref (hw.2.1 group hg).1] using hh⟩
  | stream node items => exact False.elim h
termination_by sizeOf work

theorem WorkAt.extend {parents next : Assignment} {start finish : Nat} {work : Work}
    (h : WorkAt parents start work) (he : Extends start parents next)
    (hle : start ≤ finish)
    : WorkAt next finish work := by
  cases work with
  | empty => trivial
  | combine left right => exact ⟨h.1.extend he hle, h.2.extend he hle⟩
  | executionGroup groups path result children =>
      exact ⟨h.1, fun g hg => (h.2.1 g hg).extend he hle,
        h.2.2.1.extend h.2.2.2 he hle, h.2.2.2.extend he hle⟩
  | stream node items => exact False.elim h
termination_by sizeOf work

theorem descends_trans {parents : Assignment} {bound : Nat} {ref : NodeRef}
    {inner outer : List Nat}
    (hv : Valid parents bound) (hk : ref < bound) (h : Descends parents inner ref)
    (hs : ∀ owner ∈ inner, Descends parents outer owner)
    : Descends parents outer ref := by
  obtain ⟨middle, hm, he⟩ := h
  obtain ⟨owner, ho, ha⟩ := hs middle hm
  refine ⟨owner, ho, ?_⟩
  rcases he with rfl | he
  · exact ha
  rcases ha with rfl | ha
  · exact Or.inr he
  · exact Or.inr ((hv ref hk middle he).2 ha)

theorem WorkUnder.mono {parents : Assignment} {bound : Nat} {inner outer : List Nat}
    {work : Work} (h : WorkUnder parents inner work) (hw : WorkAt parents bound work)
    (hv : Valid parents bound) (hs : ∀ owner ∈ inner, Descends parents outer owner)
    : WorkUnder parents outer work := by
  cases work with
  | empty => trivial
  | combine left right => exact ⟨h.1.mono hw.1 hv hs, h.2.mono hw.2 hv hs⟩
  | executionGroup groups path result children =>
      exact ⟨fun group hg => descends_trans hv (hw.2.1 group hg).1 (h.1 group hg) hs,
        h.2.mono hw.2.2.2 hv hs⟩
  | stream node items => exact False.elim h
termination_by sizeOf work

theorem Scoped.extend {parents next : Assignment} {start finish : Nat} {owners : List Nat}
    {work : Work} (h : Scoped parents owners work) (hw : WorkAt parents start work)
    (he : Extends start parents next) (hle : start ≤ finish)
    : Scoped next owners work :=
  h.imp_right (fun hh => hh.extend hw he hle)

def Output (parents : Assignment) (start : Nat) (owners : List Nat)
    (work : Work) (finish : Nat)
    : Prop :=
  start ≤ finish
  ∧ ∃ next,
      Extends start parents next
      ∧ Valid next finish
      ∧ WorkAt next finish work
      ∧ Scoped next owners work

def Completed (parents : Assignment) (start : Nat) (owners : List Nat)
    (output : Completion α × Nat)
    : Prop :=
  Output parents start owners output.1.work output.2

theorem output_empty (parents : Assignment) (state : Nat) (owners : List Nat)
    (hv : Valid parents state)
    : Output parents state owners .empty state :=
  ⟨Nat.le_refl _, parents, Extends.refl _ _, hv, trivial, Or.inr trivial⟩

theorem scoped_combine {parents : Assignment} {owners : List Nat} {left right : Work}
    (hl : Scoped parents owners left) (hr : Scoped parents owners right)
    : Scoped parents owners (.combine left right) := by
  rcases hl with h | hl
  · exact Or.inl h
  rcases hr with h | hr
  · exact Or.inl h
  exact Or.inr ⟨hl, hr⟩

theorem workAt_completionCombine (parents : Assignment) (bound : Nat) (owners : List Nat)
    (f : α → β → γ) (left : Completion α) (right : Completion β)
    (hl : WorkAt parents bound left.work ∧ Scoped parents owners left.work)
    (hr : WorkAt parents bound right.work ∧ Scoped parents owners right.work)
    : WorkAt parents bound (Completion.combine f left right).work
      ∧ Scoped parents owners (Completion.combine f left right).work := by
  cases hleft : left.result <;> cases hright : right.result <;>
    simp only [Completion.combine, hleft, hright, GraphQL.Execution.Result.combine]
  all_goals first
  | exact ⟨⟨hl.1, hr.1⟩, scoped_combine hl.2 hr.2⟩
  | exact ⟨trivial, Or.inr trivial⟩

theorem workAt_map (parents : Assignment) (bound : Nat) (owners : List Nat)
    (f : α → β) (completed : Completion α)
    (h : WorkAt parents bound completed.work ∧ Scoped parents owners completed.work)
    : WorkAt parents bound (completed.map f).work
      ∧ Scoped parents owners (completed.map f).work := by
  cases he : completed.result <;> simp only [Completion.map, he]
  · exact ⟨trivial, Or.inr trivial⟩
  · exact h

theorem workAt_catchNull (parents : Assignment) (bound : Nat) (owners : List Nat)
    (f : α → ResponseValue) (completed : Completion α)
    (h : WorkAt parents bound completed.work ∧ Scoped parents owners completed.work)
    : WorkAt parents bound (completed.catchNull f).work
      ∧ Scoped parents owners (completed.catchNull f).work := by
  cases he : completed.result <;> simp only [Completion.catchNull, he]
  · exact ⟨trivial, Or.inr trivial⟩
  · exact h

theorem workAt_nonNull (parents : Assignment) (bound : Nat) (owners : List Nat)
    (completed : Completion ResponseValue)
    (h : WorkAt parents bound completed.work ∧ Scoped parents owners completed.work)
    : WorkAt parents bound completed.nonNull.work
      ∧ Scoped parents owners completed.nonNull.work := by
  unfold Completion.nonNull
  split
  · exact ⟨trivial, Or.inr trivial⟩
  · exact h

theorem deferred_workAt (parents : Assignment) (bound : Nat) (deferMap : DeferMap)
    (refs owners : List Nat) (path : ResponsePath)
    (result : Result (List (Name × ResponseValue))) (children : Work)
    (hv : Valid parents bound) (hm : MapAt parents bound deferMap)
    (hne : refs ≠ []) (hk : refs.Subset (mapRefs deferMap))
    (hs : owners = [] ∨ ∀ ref ∈ refs, Descends parents owners ref)
    (hc : WorkAt parents bound children ∧ Scoped parents refs children)
    : WorkAt parents bound
        (.executionGroup (refs.filterMap (lookupDeferredFragment? deferMap)) path result
          children)
      ∧ Scoped parents owners
          (.executionGroup (refs.filterMap (lookupDeferredFragment? deferMap)) path result
            children) := by
  have hrefs := filterMap_fragment_refs deferMap refs hk
  have hchildren := hc.2.resolve_left hne
  constructor
  · refine ⟨?_, filterMap_fragmentAt hm refs, ?_, hc.1⟩
    · intro he
      simp only [he, mapRefs, List.map_nil] at hrefs
      exact hne hrefs.symm
    · simpa only [hrefs] using hchildren
  · rcases hs with hs | hs
    · exact Or.inl hs
    · refine Or.inr ⟨?_, hchildren.mono hc.1 hv hs⟩
      intro group hg
      obtain ⟨ref, hk, he⟩ := List.mem_filterMap.mp hg
      simpa only [lookup_ref he] using hs ref hk

theorem groupsKnown_extend {parents next : Assignment} {start finish : Nat}
    {deferMap : DeferMap} {groups : CollectedFieldsMap}
    (h
      : GroupsSatisfy
          (fun field => OptionalUsageAt parents start deferMap field.deferUsage) groups)
    (he : Extends start parents next) (hle : start ≤ finish)
    : GroupsSatisfy (fun field => OptionalUsageAt next finish deferMap field.deferUsage)
        groups := by
  intro group hg field hf
  exact (h group hg field hf).extend he hle (List.Subset.refl _)

theorem fieldsKnown_extend {parents next : Assignment} {start finish : Nat}
    {deferMap : DeferMap} {fields : List FieldDetails}
    (h : ∀ field ∈ fields, OptionalUsageAt parents start deferMap field.deferUsage)
    (he : Extends start parents next) (hle : start ≤ finish)
    : ∀ field ∈ fields, OptionalUsageAt next finish deferMap field.deferUsage := by
  intro field hf
  exact (h field hf).extend he hle (List.Subset.refl _)

end GraphQL.IncrementalDelivery.Semantics.Ancestry
