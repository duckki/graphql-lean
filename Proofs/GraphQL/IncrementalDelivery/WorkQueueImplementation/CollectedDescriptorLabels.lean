import Proofs.GraphQL.IncrementalDelivery.Semantics.CollectedSupply

/-! Fresh collection refs determine their labels before work lowering. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue.DescriptorMetadata
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics
open GraphQL.IncrementalDelivery.Semantics.OwnerPaths

attribute [local simp] id_pure_eq id_bind_eq id_map_eq run_bind run_map

/-- Repeated refs in `usages` agree on the full optional label, including explicit null.
This is allocation evidence, not a uniqueness requirement on user-supplied labels.
-/
def LabelsCoherent (usages : List DeferUsage) : Prop :=
  ∀ first ∈ usages, ∀ second ∈ usages, first.ref = second.ref → first.label = second.label

/-- Collections from disjoint allocation intervals have compatible labels.
Witness: equal refs cannot cross the boundary; each side supplies its own agreement.
-/
theorem labelsCoherent_append {start middle finish : Nat} {left right : FieldCollection}
    (leftBounds : SupplyBounds start (left, middle))
    (rightBounds : SupplyBounds middle (right, finish))
    (leftLabels : LabelsCoherent left.newDeferUsages)
    (rightLabels : LabelsCoherent right.newDeferUsages)
    : LabelsCoherent (left.append right).newDeferUsages := by
  intro first firstMember second secondMember same
  rcases List.mem_append.mp firstMember with firstLeft | firstRight
  · rcases List.mem_append.mp secondMember with secondLeft | secondRight
    · exact leftLabels first firstLeft second secondLeft same
    · have := (leftBounds.2 first firstLeft).2
      have := (rightBounds.2 second secondRight).1
      simp only [NodeRef] at *
      omega
  · rcases List.mem_append.mp secondMember with secondLeft | secondRight
    · have := (leftBounds.2 second secondLeft).2
      have := (rightBounds.2 first firstRight).1
      simp only [NodeRef] at *
      omega
    · exact rightLabels first firstRight second secondRight same

mutual
  /-- A selection's freshly allocated refs determine their labels.
  Witness: selection induction; a new defer ref precedes every ref allocated below it.
  -/
  theorem collectSelection_labels (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selection : Selection)
      (usage : Option DeferUsage) (state : Nat)
      : LabelsCoherent
          ((collectSelection schema variables parentType source usage selection).run
            state).1.newDeferUsages := by
    cases selection with
    | field name fieldName arguments directives children =>
        cases allowed : selectionDirectivesAllowBool variables directives <;>
          simp [collectSelection, allowed, LabelsCoherent]
    | inlineFragment condition directives children =>
        cases allowed : selectionDirectivesAllowBool variables directives
        · simp [collectSelection, allowed, LabelsCoherent]
        · cases applies : condition.all (doesFragmentTypeApplyBool schema parentType source)
          · simp [collectSelection, allowed, applies, LabelsCoherent]
          · cases deferred : activeDefer? variables directives with
            | none =>
                simpa [collectSelection, allowed, applies, deferred]
                  using collectFields_labels schema variables parentType source children
                    usage state
            | some label =>
                let next : DeferUsage := {
                  ref := state, label := label,
                  ancestors := (usage.map (fun value => value.ref :: value.ancestors)).getD [] }
                have labels := collectFields_labels schema variables parentType source
                  children (some next) (state + 1)
                have bounds := collectFields_supply schema variables parentType source
                  children (some next) (state + 1)
                simp only [collectSelection, allowed, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, applies, deferred, freshNodeRef, run_bind,
                  StateT.run_pure, id_pure_eq, StateT.run_get, StateT.run_set]
                change LabelsCoherent (next :: _)
                intro first firstMember second secondMember same
                rcases List.mem_cons.mp firstMember with rfl | firstTail
                · rcases List.mem_cons.mp secondMember with rfl | secondTail
                  · rfl
                  · have := (bounds.2 second secondTail).1
                    change state = second.ref at same
                    omega
                · rcases List.mem_cons.mp secondMember with rfl | secondTail
                  · have := (bounds.2 first firstTail).1
                    change first.ref = state at same
                    simp only [NodeRef] at *
                    omega
                  · exact labels first firstTail second secondTail same
  termination_by sizeOf selection

  /-- Field-list collection preserves label identity across successive allocations.
  Witness: the two recursive collections allocate disjoint ref intervals.
  -/
  theorem collectFields_labels (schema : Schema) (variables : VariableValues)
      (parentType : Name) (source : ResolverValue ObjectRef) (selections : List Selection)
      (usage : Option DeferUsage) (state : Nat)
      : LabelsCoherent
          ((collectFields schema variables parentType source selections usage).run
            state).1.newDeferUsages := by
    cases selections with
    | nil => simp [collectFields, LabelsCoherent]
    | cons selection rest =>
        simp only [collectFields, run_bind, StateT.run_pure, id_pure_eq]
        exact labelsCoherent_append
          (collectSelection_supply schema variables parentType source selection usage state)
          (collectFields_supply schema variables parentType source rest usage _)
          (collectSelection_labels schema variables parentType source selection usage state)
          (collectFields_labels schema variables parentType source rest usage _)
  termination_by sizeOf selections
end

/-- Merged subfield collections retain the label associated with every fresh ref.
Witness: field induction and the same disjoint-allocation interval argument.
-/
theorem collectSubfields_labels (schema : Schema) (variables : VariableValues)
    (parentType : Name) (source : ResolverValue ObjectRef) (fields : List FieldDetails)
    (state : Nat)
    : LabelsCoherent
        ((collectSubfields schema variables parentType source fields).run
          state).1.newDeferUsages := by
  induction fields generalizing state with
  | nil => simp [collectSubfields, LabelsCoherent]
  | cons field rest ih =>
      simp only [collectSubfields, run_bind, StateT.run_pure, id_pure_eq]
      exact labelsCoherent_append
        (collectFields_supply schema variables parentType source field.selectionSet
          field.deferUsage state)
        (collectSubfields_supply schema variables parentType source rest _)
        (collectFields_labels schema variables parentType source field.selectionSet
          field.deferUsage state) (ih _)

end GraphQL.IncrementalDelivery.ReferenceWorkQueue.DescriptorMetadata
