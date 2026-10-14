import Proofs.GraphQL.IncrementalDelivery.Semantics.SharedAncestorConstruction

/-! Collection supplies exact parent suffixes at every defer-map fold step of the
proof-facing shared constructor. Arbitrary helper inputs still use the filtered-lookup
builder. No runtime suffix comparison is needed on the generated path proved here. -/

namespace GraphQL.IncrementalDelivery.Semantics.SharedAncestorConstruction

open GraphQL.IncrementalDelivery.Execution
open Ancestry

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

def parentOfKeys : List Nat → Option DeferUsage
  | [] => none
  | key :: ancestors => some { ref := key, ancestors }

theorem parentOfKeys_matching {context : DeferMap} {parent : Option DeferUsage}
    (matching : ParentMatches context parent)
    : ParentMatches context (parentOfKeys (parentKeys parent)) := by
  cases parent with
  | none => simp [ParentMatches, parentOfKeys, parentKeys]
  | some usage =>
      intro actual member fragment found
      have equal : actual = { ref := usage.ref, ancestors := usage.ancestors } := by
        simpa [parentOfKeys, parentKeys] using member.symm
      subst actual
      exact matching usage rfl fragment found

/-- Generated nonempty paths resolve their immediate parent without taking the fallback. -/
def ParentAvailable (context : DeferMap) (parent : Option DeferUsage) : Prop :=
  ∀ usage ∈ parent, ∃ fragment, lookupDeferredFragment? context usage.ref = some fragment

theorem parentOfKeys_available {parents : Assignment} {bound : Nat}
    {context : DeferMap} {parent : Option DeferUsage}
    (known : OptionalUsageAt parents bound context parent)
    : ParentAvailable context (parentOfKeys (parentKeys parent)) := by
  cases parent with
  | none => simp [ParentAvailable, parentOfKeys, parentKeys]
  | some usage =>
      intro actual member
      have equal : actual = { ref := usage.ref, ancestors := usage.ancestors } := by
        simpa [parentOfKeys, parentKeys] using member.symm
      subst actual
      exact lookup_exists (known usage rfl).2.2

/-- Each fold step may reuse the parent suffix in that step's actual context. -/
def ReuseTrace (path : ResponsePath) : List DeferUsage → DeferMap → Prop
  | [], _ => True
  | usage :: rest, context =>
      ParentMatches context (parentOfKeys usage.ancestors)
      ∧ ParentAvailable context (parentOfKeys usage.ancestors)
      ∧ ReuseTrace path rest (getNewDeferMap [usage] path context)

theorem ReuseTrace.append {path : ResponsePath} {left right : List DeferUsage}
    {context : DeferMap} (first : ReuseTrace path left context)
    (second : ReuseTrace path right (getNewDeferMap left path context))
    : ReuseTrace path (left ++ right) context := by
  induction left generalizing context with
  | nil => exact second
  | cons usage rest ih =>
      exact ⟨first.1, first.2.1, ih first.2.2 second⟩

/-- Short name for the proof-facing shared constructor, not the public executor. -/
abbrev build := getNewDeferMapShared

theorem parentKeys_parentOfKeys (keys : List Nat)
    : parentKeys (parentOfKeys keys) = keys := by
  cases keys <;> rfl

theorem build_eq {usages : List DeferUsage} {path : ResponsePath} {context : DeferMap}
    (coherent : Coherent context) (trace : ReuseTrace path usages context)
    : build usages path context = getNewDeferMap usages path context := by
  induction usages generalizing context with
  | nil => rfl
  | cons usage rest ih =>
      have ancestors : sharedDeferAncestors context usage.ancestors =
          fromParent context (parentOfKeys usage.ancestors) := by
        simp only [fromParent, parentKeys_parentOfKeys]
      have step : extendFromParent context usage.ref path usage.label
          (parentOfKeys usage.ancestors) = getNewDeferMap [usage] path context := by
        simp only [extendFromParent, getNewDeferMap, List.foldl_cons, List.foldl_nil]
        rw [fromParent_eq coherent _ trace.1, parentKeys_parentOfKeys]
        rfl
      simp only [build, getNewDeferMapShared, List.foldl_cons]
      rw [ancestors]
      change build rest path
          (extendFromParent context usage.ref path usage.label (parentOfKeys usage.ancestors))
        = getNewDeferMap rest path (getNewDeferMap [usage] path context)
      rw [step]
      exact ih (coherent_getNewDeferMap _ _ coherent) trace.2.2

mutual
  theorem collectSelection_reuseTrace (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (usage : Option DeferUsage) (parents : Assignment) (state : Nat)
      (context : DeferMap) (path : ResponsePath) (valid : Valid parents state)
      (metadata : MapAt parents state context)
      (known : OptionalUsageAt parents state context usage)
      : ReuseTrace path
          ((collectSelection schema variables parentType source usage selection).run
            state).1.newDeferUsages context := by
    cases selection with
    | field name fieldName arguments directives children =>
        cases ha : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, ha, ReuseTrace]
    | inlineFragment condition directives children =>
        cases ha : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, ha, ReuseTrace]
        · cases ht : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, ha, ht, ReuseTrace]
          · cases hd : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, ha, ht, hd]
                  using collectFields_reuseTrace schema variables parentType source
                    children usage parents state context path valid metadata known
            | some label =>
                let ancestors := parentKeys usage
                let fresh : DeferUsage := { ref := state, label, ancestors }
                let next := allocate parents state ancestors
                let nextMap := getNewDeferMap [fresh] path context
                have hm := mapAt_allocate parents state path context usage label metadata known
                have hv : Valid next (state + 1) := allocate_valid parents state usage valid
                  (fun u hu => ⟨(known u hu).1, (known u hu).2.1⟩)
                have tail := collectFields_reuseTrace schema variables parentType source
                  children (some fresh) next (state + 1) nextMap path hv hm.1
                  (by intro u hu; cases hu; exact hm.2)
                have head := parentOfKeys_matching (parentMatches_of_generated metadata known)
                have available := parentOfKeys_available known
                simpa only [collectSelection, ha, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, ht, hd, freshNodeRef, run_bind, StateT.run_pure, id_pure_eq,
                  StateT.run_get, StateT.run_set, ReuseTrace, fresh, ancestors,
                  parentKeys, nextMap]
                  using And.intro head ⟨available, tail⟩
  termination_by sizeOf selection

  theorem collectFields_reuseTrace (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (parents : Assignment) (state : Nat)
      (context : DeferMap) (path : ResponsePath) (valid : Valid parents state)
      (metadata : MapAt parents state context)
      (known : OptionalUsageAt parents state context usage)
      : ReuseTrace path
          ((collectFields schema variables parentType source selections usage).run
            state).1.newDeferUsages context := by
    cases selections with
    | nil => simp [collectFields, ReuseTrace]
    | cons selection rest =>
        have head := collectSelection_reuseTrace schema variables parentType source
          selection usage parents state context path valid metadata known
        obtain ⟨hle, next, he, hv, hm, _⟩ := collectSelection_ancestry schema variables
          parentType source selection usage parents state context path valid metadata known
        have tail := collectFields_reuseTrace schema variables parentType source rest
          usage next _ _ path hv hm
          (known.extend he hle (getNewDeferMap_keeps_refs _ _ _))
        simpa only [collectFields, run_bind, StateT.run_pure, id_pure_eq,
          FieldCollection.append] using head.append tail
  termination_by sizeOf selections
end

theorem collectSubfields_reuseTrace (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    (parents : Assignment) (state : Nat) (context : DeferMap) (path : ResponsePath)
    (valid : Valid parents state) (metadata : MapAt parents state context)
    (known : ∀ field ∈ fields, OptionalUsageAt parents state context field.deferUsage)
    : ReuseTrace path
        ((collectSubfields schema variables parentType source fields).run
          state).1.newDeferUsages
        context := by
  induction fields generalizing parents state context with
  | nil => simp [collectSubfields, ReuseTrace]
  | cons field rest ih =>
      have head := collectFields_reuseTrace schema variables parentType source
        field.selectionSet field.deferUsage parents state context path valid metadata
        (known field (by simp))
      obtain ⟨hle, next, he, hv, hm, _⟩ := collectFields_ancestry schema variables
        parentType source field.selectionSet field.deferUsage parents state context path
        valid metadata (known field (by simp))
      have tail := ih next _ _ hv hm (fun f hf =>
        (known f (List.mem_cons_of_mem field hf)).extend he hle
          (getNewDeferMap_keeps_refs _ _ _))
      simpa only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq,
        FieldCollection.append]
        using head.append tail

/-- Root-facing construction target, with no assumed cache or generated-input certificate. -/
def RootConstructionExact : Prop :=
  ∀ (ObjectRef : Type) (schema : Schema) (variables : VariableValues) parentType
    (source : ResolverValue ObjectRef) selections state path,
    let usages :=
      ((collectFields schema variables parentType source selections none).run
        state).1.newDeferUsages
    build usages path [] = getNewDeferMap usages path []

theorem rootConstructionExact_holds : RootConstructionExact := by
  intro ObjectRef schema variables parentType source selections state path
  exact build_eq coherent_empty
    (collectFields_reuseTrace schema variables parentType source selections none
      (fun _ => []) state [] path (by simp [Valid]) (by simp [MapAt])
      (by simp [OptionalUsageAt]))

/-- Inherited subfield contexts retain the same exact construction boundary. -/
theorem subfields_build_eq (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    (parents : Assignment) (state : Nat) (context : DeferMap) (path : ResponsePath)
    (valid : Valid parents state) (metadata : MapAt parents state context)
    (known : ∀ field ∈ fields, OptionalUsageAt parents state context field.deferUsage)
    (coherent : Coherent context)
    : let usages :=
        ((collectSubfields schema variables parentType source fields).run
          state).1.newDeferUsages
      build usages path context = getNewDeferMap usages path context :=
  build_eq coherent
    (collectSubfields_reuseTrace schema variables parentType source
      fields parents state context path valid metadata known)

end GraphQL.IncrementalDelivery.Semantics.SharedAncestorConstruction
