import Proofs.GraphQL.Theories.NormalForm.GroundTypeNormalization.Uniqueness.DataSeparation

/-!
Runtime data-difference witness predicates and conversions.

Finite-support construction proofs live in `FocusedContextualSeparation`.
This module keeps the shared witness surface independent of those constructions.
-/

namespace GraphQL

namespace NormalForm

namespace GroundTypeNormalization

def selectionSetRuntimeDataDiffWitness
    (schema : Schema) (parentType runtimeType : Name)
    (left right : List Selection)
    : Prop :=
  schema.typeIncludesObjectBool parentType runtimeType = true
  ∧ ∃ ObjectRef : Type,
    ∃ resolvers : Execution.Resolvers ObjectRef,
    ∃ variableValues : Execution.VariableValues,
    ∃ fuel : Nat,
    ∃ ref : ObjectRef,
      ¬ Execution.ResponseValue.semanticEquivalent
          (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            runtimeType (.object runtimeType ref) left).data
          (Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
            runtimeType (.object runtimeType ref) right).data

def selectionSetContextualRuntimeDataDiffWitness
    (schema : Schema) (parentType runtimeType : Name)
    (left right : List Selection)
    (support : List Selection -> Prop)
    : Prop :=
  schema.typeIncludesObjectBool parentType runtimeType = true
  ∧ ∃ ObjectRef : Type,
    ∃ resolvers : Execution.Resolvers ObjectRef,
    ∃ variableValues : Execution.VariableValues,
    ∃ fuel : Nat,
    ∃ ref : ObjectRef,
      (∀ selectionSet,
        support selectionSet
        -> ∃ fields errors,
            Execution.executeSelectionSetAsResponse schema resolvers variableValues fuel
              runtimeType (.object runtimeType ref) selectionSet
            = ({ data := Execution.ResponseValue.object fields, errors := errors }
                : Execution.Response))
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel runtimeType (.object runtimeType ref) left).data
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel runtimeType (.object runtimeType ref) right).data

def selectionSetContextualRuntimeDataDiffWitnessWithFuelGe
    (schema : Schema) (parentType runtimeType : Name)
    (left right : List Selection)
    {variableValues : Execution.VariableValues}
    (support : List Selection -> Prop) (minFuel : Nat)
    : Prop :=
  schema.typeIncludesObjectBool parentType runtimeType = true
  ∧ ∃ ObjectRef : Type,
    ∃ resolvers : Execution.Resolvers ObjectRef,
    ∃ fuel : Nat,
    ∃ ref : ObjectRef,
      minFuel ≤ fuel
      ∧ (∀ selectionSet,
          support selectionSet
          -> ∃ fields errors,
              Execution.executeSelectionSetAsResponse schema resolvers variableValues
                fuel runtimeType (.object runtimeType ref) selectionSet
              = ({ data := Execution.ResponseValue.object fields, errors := errors }
                  : Execution.Response))
      ∧ ¬ Execution.ResponseValue.semanticEquivalent
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel runtimeType (.object runtimeType ref) left).data
            (Execution.executeSelectionSetAsResponse schema resolvers variableValues
              fuel runtimeType (.object runtimeType ref) right).data

theorem responseValue_semanticEquivalent_symm {left right : Execution.ResponseValue}
    : Execution.ResponseValue.semanticEquivalent left right
      -> Execution.ResponseValue.semanticEquivalent right left := by
  intro hsemantic
  exact hsemantic.symm

theorem selectionSetsDataEquivalent_symm
    {schema : Schema} {parentType : Name} {left right : List Selection}
    : selectionSetsDataEquivalent schema parentType left right
      -> selectionSetsDataEquivalent schema parentType right left := by
  intro hdata ObjectRef resolvers variableValues fuel source hsource
  exact responseValue_semanticEquivalent_symm
    (hdata resolvers variableValues fuel source hsource)

theorem selectionSetRuntimeDataDiffWitness_of_contextualRuntimeDataDiffWitness
    {schema : Schema} {parentType runtimeType : Name}
    {left right : List Selection} {support : List Selection -> Prop}
    : selectionSetContextualRuntimeDataDiffWitness schema parentType runtimeType
        left right support
      -> selectionSetRuntimeDataDiffWitness schema parentType runtimeType left right := by
  intro hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, resolvers, variableValues, fuel, ref,
      _hsupport, hnot⟩
  exact ⟨hinclude, ObjectRef, resolvers, variableValues, fuel, ref, hnot⟩

theorem selectionSetContextualRuntimeDataDiffWitness_of_withFuelGe
    {schema : Schema} {parentType runtimeType : Name}
    {left right : List Selection} {support : List Selection -> Prop}
    {minFuel : Nat}
    : selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
        runtimeType left right (variableValues := variableValues) support minFuel
      -> selectionSetContextualRuntimeDataDiffWitness schema parentType
          runtimeType left right support := by
  intro hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, resolvers, fuel, ref, _hfuel,
      hsupport, hnot⟩
  exact ⟨hinclude, ObjectRef, resolvers, variableValues, fuel, ref, hsupport, hnot⟩

theorem selectionSetRuntimeDataDiffWitness_of_contextualRuntimeDataDiffWitnessWithFuelGe
    {schema : Schema} {parentType runtimeType : Name}
    {left right : List Selection} {support : List Selection -> Prop}
    {minFuel : Nat}
    : selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
        runtimeType left right (variableValues := variableValues) support minFuel
      -> selectionSetRuntimeDataDiffWitness schema parentType runtimeType left right := by
  intro hwitness
  exact
    selectionSetRuntimeDataDiffWitness_of_contextualRuntimeDataDiffWitness
      (selectionSetContextualRuntimeDataDiffWitness_of_withFuelGe hwitness)

theorem not_selectionSetsDataEquivalent_of_contextualRuntimeDataDiffWitnessWithFuelGe
    {schema : Schema} {parentType runtimeType : Name}
    {left right : List Selection} {support : List Selection -> Prop}
    {minFuel : Nat}
    : objectTypeNameBool schema parentType = true
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
          runtimeType left right (variableValues := variableValues) support minFuel
      -> ¬ selectionSetsDataEquivalent schema parentType left right := by
  intro hobject hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, resolvers, fuel, ref, _hfuel,
      _hsupport, hnot⟩
  have hruntimeEq : runtimeType = parentType :=
    typeIncludesObjectBool_eq_of_objectTypeNameBool_true schema hobject
      hinclude
  subst runtimeType
  exact
    not_selectionSetsDataEquivalent_of_responseData_counterexample
      resolvers variableValues fuel (.object parentType ref)
      ⟨parentType, ref, rfl, hinclude⟩ hnot

theorem selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_mono_support
    {schema : Schema} {parentType runtimeType : Name}
    {left right : List Selection}
    {sourceSupport targetSupport : List Selection -> Prop}
    {minFuel : Nat}
    : (∀ selectionSet, targetSupport selectionSet -> sourceSupport selectionSet)
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
          runtimeType left right (variableValues := variableValues) sourceSupport minFuel
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
          runtimeType left right (variableValues := variableValues) targetSupport
          minFuel := by
  intro hsubset hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, resolvers, fuel, ref, hfuel,
      hsupport, hnot⟩
  exact ⟨
    hinclude,
    ObjectRef,
    resolvers,
    fuel,
    ref,
    hfuel,
    (by
      intro selectionSet htarget
      exact hsupport selectionSet (hsubset selectionSet htarget)),
    hnot
  ⟩

theorem selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_minFuel_le
    {schema : Schema} {parentType runtimeType : Name}
    {left right : List Selection} {support : List Selection -> Prop}
    {sourceMinFuel targetMinFuel : Nat}
    : targetMinFuel ≤ sourceMinFuel
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
          runtimeType left right (variableValues := variableValues) support sourceMinFuel
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
          runtimeType left right (variableValues := variableValues) support
          targetMinFuel := by
  intro hfuelLe hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, resolvers, fuel, ref, hfuel,
      hsupport, hnot⟩
  exact ⟨
    hinclude,
    ObjectRef,
    resolvers,
    fuel,
    ref,
    Nat.le_trans hfuelLe hfuel,
    hsupport,
    hnot
  ⟩

theorem selectionSetContextualRuntimeDataDiffWitnessWithFuelGe_symm
    {schema : Schema} {parentType runtimeType : Name}
    {left right : List Selection} {support : List Selection -> Prop}
    {minFuel : Nat}
    : selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
        runtimeType right left (variableValues := variableValues) support minFuel
      -> selectionSetContextualRuntimeDataDiffWitnessWithFuelGe schema parentType
          runtimeType left right (variableValues := variableValues) support minFuel := by
  intro hwitness
  rcases hwitness with
    ⟨hinclude, ObjectRef, resolvers, fuel, ref, hfuel,
      hsupport, hnot⟩
  exact ⟨
    hinclude,
    ObjectRef,
    resolvers,
    fuel,
    ref,
    hfuel,
    hsupport,
    (by
      intro hsemantic
      exact hnot (responseValue_semanticEquivalent_symm hsemantic))
  ⟩

end GroundTypeNormalization

end NormalForm

end GraphQL
