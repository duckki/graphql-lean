import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality

/-!
Boolean-support facts derived from complete-normal equality up to reordering.
-/

namespace GraphQL

namespace NormalForm

namespace CompleteNormalization

private theorem mem_selectionSetBooleanVariables_iff
    (varName : BoolVar) (selectionSet : List Selection)
    : varName ∈ selectionSetBooleanVariables selectionSet
      ↔ ∃ selection,
          selection ∈ selectionSet ∧ varName ∈ selectionBooleanVariables selection := by
  induction selectionSet with
  | nil =>
      simp [selectionSetBooleanVariables]
  | cons selection rest ih =>
      simp [selectionSetBooleanVariables, ih]

private theorem selectionBooleanVariables_mem_iff_of_equalUpToReordering
    {schema : Schema} {leftValues rightValues : Execution.VariableValues}
    {parentType : Name}
    {left right : Selection}
    (hequal
      : SelectionEqualUpToReorderingWithCoercion schema leftValues rightValues
          parentType left right)
    (varName : BoolVar)
    : varName ∈ selectionBooleanVariables left
      ↔ varName ∈ selectionBooleanVariables right := by
  refine SelectionEqualUpToReorderingWithCoercion.rec
    (motive_1 := fun _parentType left right _hequal =>
      ∀ varName,
        varName ∈ selectionBooleanVariables left
          ↔ varName ∈ selectionBooleanVariables right)
    (motive_2 := fun _parentType left right _hequal =>
      ∀ varName,
        varName ∈ selectionSetBooleanVariables left
          ↔ varName ∈ selectionSetBooleanVariables right)
    ?_ ?_ ?_ hequal varName
  · intro _parentType responseName fieldName leftArguments rightArguments directives
      leftSelectionSet rightSelectionSet _fieldDefinition _hlookup _harguments
      _hselectionSet ih varName
    simp only [selectionBooleanVariables, List.mem_append]
    exact or_congr Iff.rfl (ih varName)
  · intro _parentType typeCondition directives leftSelectionSet rightSelectionSet
      _hselectionSet ih varName
    simp only [selectionBooleanVariables, List.mem_append]
    exact or_congr Iff.rfl (ih varName)
  · intro _parentType left right pairs hleft hright _hpairs ih varName
    rw [mem_selectionSetBooleanVariables_iff,
      mem_selectionSetBooleanVariables_iff]
    constructor
    · rintro ⟨leftSelection, hleftMem, hvarMem⟩
      have hleftPairMem :
          leftSelection ∈ pairs.map Prod.fst :=
        hleft.mem_iff.mpr hleftMem
      rcases List.mem_map.mp hleftPairMem with
        ⟨pair, hpairMem, hpairLeft⟩
      refine ⟨pair.2, hright.mem_iff.mp ?_, ?_⟩
      · exact List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
      · exact (ih pair hpairMem varName).mp
          (by simpa [hpairLeft] using hvarMem)
    · rintro ⟨rightSelection, hrightMem, hvarMem⟩
      have hrightPairMem :
          rightSelection ∈ pairs.map Prod.snd :=
        hright.mem_iff.mpr hrightMem
      rcases List.mem_map.mp hrightPairMem with
        ⟨pair, hpairMem, hpairRight⟩
      refine ⟨pair.1, hleft.mem_iff.mp ?_, ?_⟩
      · exact List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
      · exact (ih pair hpairMem varName).mpr
          (by simpa [hpairRight] using hvarMem)

private theorem selectionSetBooleanVariables_mem_iff_of_equalUpToReordering
    {schema : Schema} {leftValues rightValues : Execution.VariableValues}
    {parentType : Name}
    {left right : List Selection}
    (hequal
      : SelectionSetEqualUpToReorderingWithCoercion schema leftValues rightValues
          parentType left right)
    (varName : BoolVar)
    : varName ∈ selectionSetBooleanVariables left
      ↔ varName ∈ selectionSetBooleanVariables right := by
  refine SelectionSetEqualUpToReorderingWithCoercion.rec
    (motive_1 := fun _parentType left right _hequal =>
      ∀ varName,
        varName ∈ selectionBooleanVariables left
          ↔ varName ∈ selectionBooleanVariables right)
    (motive_2 := fun _parentType left right _hequal =>
      ∀ varName,
        varName ∈ selectionSetBooleanVariables left
          ↔ varName ∈ selectionSetBooleanVariables right)
    ?_ ?_ ?_ hequal varName
  · intro _parentType responseName fieldName leftArguments rightArguments directives
      leftSelectionSet rightSelectionSet _fieldDefinition _hlookup _harguments
      _hselectionSet ih varName
    simp only [selectionBooleanVariables, List.mem_append]
    exact or_congr Iff.rfl (ih varName)
  · intro _parentType typeCondition directives leftSelectionSet rightSelectionSet
      _hselectionSet ih varName
    simp only [selectionBooleanVariables, List.mem_append]
    exact or_congr Iff.rfl (ih varName)
  · intro _parentType left right pairs hleft hright _hpairs ih varName
    rw [mem_selectionSetBooleanVariables_iff,
      mem_selectionSetBooleanVariables_iff]
    constructor
    · rintro ⟨leftSelection, hleftMem, hvarMem⟩
      have hleftPairMem :
          leftSelection ∈ pairs.map Prod.fst :=
        hleft.mem_iff.mpr hleftMem
      rcases List.mem_map.mp hleftPairMem with
        ⟨pair, hpairMem, hpairLeft⟩
      refine ⟨pair.2, hright.mem_iff.mp ?_, ?_⟩
      · exact List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
      · exact (ih pair hpairMem varName).mp
          (by simpa [hpairLeft] using hvarMem)
    · rintro ⟨rightSelection, hrightMem, hvarMem⟩
      have hrightPairMem :
          rightSelection ∈ pairs.map Prod.snd :=
        hright.mem_iff.mpr hrightMem
      rcases List.mem_map.mp hrightPairMem with
        ⟨pair, hpairMem, hpairRight⟩
      refine ⟨pair.1, hleft.mem_iff.mp ?_, ?_⟩
      · exact List.mem_map.mpr ⟨pair, hpairMem, rfl⟩
      · exact (ih pair hpairMem varName).mpr
          (by simpa [hpairRight] using hvarMem)

private theorem operationBoolVarsEquivalent_of_selectionSetEqualUpToReordering
    {schema : Schema} {leftValues rightValues : Execution.VariableValues}
    {left right : Operation}
    (hequal
      : SelectionSetEqualUpToReorderingWithCoercion schema leftValues rightValues
          (left.rootType schema) left.selectionSet right.selectionSet)
    : operationBoolVarsEquivalent left right := by
  intro varName
  simp only [operationBoolVars, mem_dedupBoolVars_iff]
  exact
    selectionSetBooleanVariables_mem_iff_of_equalUpToReordering hequal varName

private theorem completeNormalBoolCasesEquivalent_variables
    {leftVariables rightVariables : List BoolVar}
    {leftCase rightCase : BoolCase}
    (hleft : completeNormalBoolCase leftVariables leftCase)
    (hright : completeNormalBoolCase rightVariables rightCase)
    (hequivalent : completeNormalBoolCasesEquivalent leftCase rightCase)
    : ∀ varName, varName ∈ leftVariables ↔ varName ∈ rightVariables := by
  intro varName
  constructor
  · intro hmem
    have hcaseMem : varName ∈ leftCase.map Prod.fst :=
      (hleft.2.2 varName).2 hmem
    rcases List.mem_map.mp hcaseMem with
      ⟨⟨candidate, value⟩, hpairMem, hcandidate⟩
    simp only at hcandidate
    subst candidate
    have hrightPair : (varName, value) ∈ rightCase :=
      (hequivalent varName value).1 hpairMem
    exact (hright.2.2 varName).1
      (List.mem_map.mpr ⟨(varName, value), hrightPair, rfl⟩)
  · intro hmem
    have hcaseMem : varName ∈ rightCase.map Prod.fst :=
      (hright.2.2 varName).2 hmem
    rcases List.mem_map.mp hcaseMem with
      ⟨⟨candidate, value⟩, hpairMem, hcandidate⟩
    simp only at hcandidate
    subst candidate
    have hleftPair : (varName, value) ∈ leftCase :=
      (hequivalent varName value).2 hpairMem
    exact (hleft.2.2 varName).1
      (List.mem_map.mpr ⟨(varName, value), hleftPair, rfl⟩)

theorem
    operationBoolVarsEquivalent_of_completeNormalOperationsEqualUpToReorderingWithCoercion
    {schema : Schema} {left right : Operation}
    (hequal : completeNormalOperationsEqualUpToReorderingWithCoercion schema left right)
    : operationBoolVarsEquivalent left right := by
  rcases hequal with ⟨_hroot, hselectionEqual⟩
  cases hleftVars : operationBoolVars left with
  | nil =>
      rw [hleftVars] at hselectionEqual
      exact operationBoolVarsEquivalent_of_selectionSetEqualUpToReordering
        (hselectionEqual [])
  | cons leftVar leftVariables =>
      have hleftSelectionSetNonempty : left.selectionSet ≠ [] := by
        intro hnil
        rw [operationBoolVars, hnil] at hleftVars
        simp [selectionSetBooleanVariables, dedupBoolVars] at hleftVars
      rw [hleftVars] at hselectionEqual
      rcases hselectionEqual with ⟨pairs, hpairsLeft, _hpairsRight, hpairsEqual⟩
      cases pairs with
      | nil =>
          have : left.selectionSet = [] := by
            exact (List.Perm.nil_eq hpairsLeft).symm
          exact False.elim (hleftSelectionSetNonempty this)
      | cons pair pairs =>
          rcases hpairsEqual pair (by simp) with
            ⟨leftCase, rightCase, _leftBody, _rightBody,
              hleftCase, hrightCase, _hleftStem, _hrightStem,
              hequivalent, _hbodyEqual⟩
          intro varName
          simpa [hleftVars] using
            completeNormalBoolCasesEquivalent_variables
              hleftCase hrightCase hequivalent varName

end CompleteNormalization

end NormalForm

end GraphQL
