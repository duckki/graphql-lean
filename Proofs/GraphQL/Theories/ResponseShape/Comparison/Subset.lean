import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.Uniqueness.BoolCases
import Proofs.GraphQL.Theories.ResponseShape.Comparison.Enumeration
import Proofs.GraphQL.Theories.ResponseShape.Correspondence.Equivalence
import Proofs.GraphQL.Theories.ResponseShape.Relations.Basics

/-!
Proof-carrying executable decision of response-shape subset.

The finite semantic basis is computed before readiness classification. A
proof-carrying rejection therefore outranks malformed-shape uncertainty; absence of
a semantic counterexample establishes the raw `ShapeSubset` proposition, while
positive API acceptance additionally requires `ShapeComparisonReady`.
-/

namespace GraphQL

namespace ResponseShape

open NormalForm
open NormalForm.CompleteNormalization

private theorem BoolCase.pair_mem_of_lookup?_eq_some {varName : BoolVar} {value : Bool}
    : ∀ {assignment : BoolCase},
        assignment.lookup? varName = some value → (varName, value) ∈ assignment
  | [], hlookup => by
      simp [BoolCase.lookup?] at hlookup
  | (candidate, candidateValue) :: rest, hlookup => by
      by_cases heq : candidate = varName
      · subst candidate
        simp [BoolCase.lookup?] at hlookup
        subst candidateValue
        simp
      · have hrest : BoolCase.lookup? rest varName = some value := by
          simpa [BoolCase.lookup?, heq] using hlookup
        exact List.mem_cons_of_mem _
          (BoolCase.pair_mem_of_lookup?_eq_some hrest)

/-- Every arbitrary complete assignment has an extensionally equal generated
representative. This is the constructive exhaustiveness bridge for the
explicit `2^n` `allBoolCases` traversal. -/
theorem allBoolCases_complete_representative
    {support : List BoolVar} {assignment : BoolCase}
    (hcomplete : completeNormalBoolCase support assignment)
    : ∃ representative,
        representative ∈ allBoolCases support
        ∧ completeNormalBoolCasesEquivalent assignment representative := by
  have hlookupComplete :
      ∀ varName, varName ∈ support →
        ∃ value, assignment.lookup? varName = some value := by
    intro varName hvar
    have hcaseVar : varName ∈ assignment.map Prod.fst :=
      (hcomplete.2.2 varName).2 hvar
    rcases List.mem_map.mp hcaseVar with
      ⟨⟨candidate, value⟩, hpair, hcandidate⟩
    change candidate = varName at hcandidate
    subst candidate
    exact ⟨value,
      BoolCase.lookup?_eq_of_pair_mem_nodup hcomplete.2.1 hpair⟩
  rcases allBoolCases_complete
      (variables := support) (f := assignment.lookup?) hlookupComplete with
    ⟨representative, hrepresentative, hlookup⟩
  have hrepresentativeComplete :
      completeNormalBoolCase support representative :=
    completeNormalBoolCase_of_mem_allBoolCases
      hcomplete.1 hrepresentative
  refine ⟨representative, hrepresentative, ?_⟩
  intro varName value
  constructor
  · intro hassignmentPair
    have hvar : varName ∈ support :=
      (hcomplete.2.2 varName).1
        (List.mem_map.mpr ⟨(varName, value), hassignmentPair, rfl⟩)
    have hassignmentLookup :
        assignment.lookup? varName = some value :=
      BoolCase.lookup?_eq_of_pair_mem_nodup
        hcomplete.2.1 hassignmentPair
    have hrepresentativeLookup :
        representative.lookup? varName = some value :=
      (hlookup varName hvar).trans hassignmentLookup
    exact BoolCase.pair_mem_of_lookup?_eq_some hrepresentativeLookup
  · intro hrepresentativePair
    have hvar : varName ∈ support :=
      (hrepresentativeComplete.2.2 varName).1
        (List.mem_map.mpr ⟨(varName, value), hrepresentativePair, rfl⟩)
    have hrepresentativeLookup :
        representative.lookup? varName = some value :=
      BoolCase.lookup?_eq_of_pair_mem_nodup
        hrepresentativeComplete.2.1 hrepresentativePair
    have hassignmentLookup : assignment.lookup? varName = some value :=
      (hlookup varName hvar).symm.trans hrepresentativeLookup
    exact BoolCase.pair_mem_of_lookup?_eq_some hassignmentLookup

private theorem Clause.holdsIn_iff_of_boolCaseEquivalent
    {left right : BoolCase} {clause : Clause}
    (hleftNodup : (left.map Prod.fst).Nodup)
    (hrightNodup : (right.map Prod.fst).Nodup)
    (hequivalent : completeNormalBoolCasesEquivalent left right)
    : clause.HoldsIn left ↔ clause.HoldsIn right := by
  constructor
  · intro hholds literal hliteral
    have hleftLookup := hholds literal hliteral
    have hleftPair : literal ∈ left :=
      BoolCase.pair_mem_of_lookup?_eq_some hleftLookup
    exact BoolCase.lookup?_eq_of_pair_mem_nodup hrightNodup
      ((hequivalent literal.1 literal.2).mp hleftPair)
  · intro hholds literal hliteral
    have hrightLookup := hholds literal hliteral
    have hrightPair : literal ∈ right :=
      BoolCase.pair_mem_of_lookup?_eq_some hrightLookup
    exact BoolCase.lookup?_eq_of_pair_mem_nodup hleftNodup
      ((hequivalent literal.1 literal.2).mpr hrightPair)

private theorem ResponseShape.denotesPath_of_boolCaseEquivalent
    {left right : BoolCase}
    (hleftNodup : (left.map Prod.fst).Nodup)
    (hrightNodup : (right.map Prod.fst).Nodup)
    (hequivalent : completeNormalBoolCasesEquivalent left right)
    : ∀ {schema : Schema} {parentType : Name} {shape : ResponseShape}
          {path : List PathStep},
        shape.DenotesPath schema left parentType path
        → shape.DenotesPath schema right parentType path := by
  intro schema parentType shape path hdenotes
  induction hdenotes with
  | field runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds =>
      exact .field runtimePossible positionMem possibleMem runtimeMem
        definitionMem
        ((Clause.holdsIn_iff_of_boolCaseEquivalent
          hleftNodup hrightNodup hequivalent).mp clauseHolds)
  | child runtimePossible positionMem possibleMem runtimeMem definitionMem
      clauseHolds subshapeEq childDenotes ih =>
      exact .child runtimePossible positionMem possibleMem runtimeMem
        definitionMem
        ((Clause.holdsIn_iff_of_boolCaseEquivalent
          hleftNodup hrightNodup hequivalent).mp clauseHolds)
        subshapeEq ih

/-- Exact path denotation is invariant under extensionally equal complete
Boolean assignments, including assignment-list reordering. -/
theorem ResponseShape.denotesPath_iff_of_completeBoolCasesEquivalent
    {schema : Schema} {support : List BoolVar} {left right : BoolCase}
    {parentType : Name} {shape : ResponseShape} {path : List PathStep}
    (hleft : completeNormalBoolCase support left)
    (hright : completeNormalBoolCase support right)
    (hequivalent : completeNormalBoolCasesEquivalent left right)
    : shape.DenotesPath schema left parentType path
      ↔ shape.DenotesPath schema right parentType path := by
  constructor
  · exact ResponseShape.denotesPath_of_boolCaseEquivalent
      hleft.2.1 hright.2.1 hequivalent
  · exact ResponseShape.denotesPath_of_boolCaseEquivalent
      hright.2.1 hleft.2.1
      (completeNormalBoolCasesEquivalent_symm hequivalent)

/-- Equivalent-path denotation is invariant under extensionally equal complete
Boolean assignments. -/
theorem ResponseShape.denotesEquivalentPath_iff_of_completeBoolCasesEquivalent
    {schema : Schema} {support : List BoolVar} {left right : BoolCase}
    {parentType : Name} {shape : ResponseShape} {path : List PathStep}
    (hleft : completeNormalBoolCase support left)
    (hright : completeNormalBoolCase support right)
    (hequivalent : completeNormalBoolCasesEquivalent left right)
    : shape.DenotesEquivalentPath schema left parentType path
      ↔ shape.DenotesEquivalentPath schema right parentType path := by
  unfold ResponseShape.DenotesEquivalentPath
  constructor
  · rintro ⟨denotedPath, hdenotes, hpath⟩
    exact ⟨denotedPath,
      (ResponseShape.denotesPath_iff_of_completeBoolCasesEquivalent
        hleft hright hequivalent).mp hdenotes,
      hpath⟩
  · rintro ⟨denotedPath, hdenotes, hpath⟩
    exact ⟨denotedPath,
      (ResponseShape.denotesPath_iff_of_completeBoolCasesEquivalent
        hleft hright hequivalent).mpr hdenotes,
      hpath⟩

private theorem firstCoveringPath?_isSome_iff (requiredPath : List PathStep)
    : ∀ providedPaths : List (List PathStep),
        (firstCoveringPath? requiredPath providedPaths).isSome = true
        ↔ ∃ providedPath ∈ providedPaths,
            PathsSemanticallyEquivalent providedPath requiredPath
  | [] => by
      simp [firstCoveringPath?]
  | providedPath :: rest => by
      by_cases hequivalent :
          PathsSemanticallyEquivalent providedPath requiredPath
      · have hequivalentBool :
            pathsSemanticallyEquivalentBool providedPath requiredPath = true :=
          (pathsSemanticallyEquivalentBool_iff
            providedPath requiredPath).mpr hequivalent
        simp [firstCoveringPath?, hequivalentBool, hequivalent]
      · have hequivalentBool :
            pathsSemanticallyEquivalentBool providedPath requiredPath = false := by
          cases hvalue :
              pathsSemanticallyEquivalentBool providedPath requiredPath
          · rfl
          · exact False.elim
              (hequivalent
                ((pathsSemanticallyEquivalentBool_iff
                  providedPath requiredPath).mp hvalue))
        simp [firstCoveringPath?, hequivalentBool, hequivalent,
          firstCoveringPath?_isSome_iff requiredPath rest]

private theorem firstCoveringPath?_eq_some_properties
    {requiredPath providedPath : List PathStep}
    : ∀ {providedPaths : List (List PathStep)},
        firstCoveringPath? requiredPath providedPaths = some providedPath
        → providedPath ∈ providedPaths
          ∧ PathsSemanticallyEquivalent providedPath requiredPath
  | [], hsome => by
      simp [firstCoveringPath?] at hsome
  | candidate :: rest, hsome => by
      by_cases hequivalent :
          PathsSemanticallyEquivalent candidate requiredPath
      · have hequivalentBool :
            pathsSemanticallyEquivalentBool candidate requiredPath = true :=
          (pathsSemanticallyEquivalentBool_iff
            candidate requiredPath).mpr hequivalent
        simp [firstCoveringPath?, hequivalentBool] at hsome
        subst candidate
        exact ⟨by simp, hequivalent⟩
      · have hequivalentBool :
            pathsSemanticallyEquivalentBool candidate requiredPath = false := by
          cases hvalue :
              pathsSemanticallyEquivalentBool candidate requiredPath
          · rfl
          · exact False.elim
              (hequivalent
                ((pathsSemanticallyEquivalentBool_iff
                  candidate requiredPath).mp hvalue))
        have hrest :
            firstCoveringPath? requiredPath rest = some providedPath := by
          simpa [firstCoveringPath?, hequivalentBool] using hsome
        have hproperties :=
          firstCoveringPath?_eq_some_properties hrest
        exact ⟨List.mem_cons_of_mem _ hproperties.1, hproperties.2⟩

/-- The executable coverage bit is exactly existential semantic path coverage. -/
theorem pathCoveredBool_iff
    (providedPaths : List (List PathStep)) (requiredPath : List PathStep)
    : pathCoveredBool providedPaths requiredPath = true
      ↔ ∃ providedPath ∈ providedPaths,
          PathsSemanticallyEquivalent providedPath requiredPath := by
  exact firstCoveringPath?_isSome_iff requiredPath providedPaths

private theorem exists_mem_zipIdx_of_mem
    {α : Type} {value : α} {values : List α}
    (hmem : value ∈ values)
    : ∃ index, (value, index) ∈ values.zipIdx := by
  have hmapped : value ∈ (values.zipIdx.map Prod.fst) := by
    simpa using hmem
  rcases List.mem_map.mp hmapped with
    ⟨⟨candidate, index⟩, hzip, heq⟩
  change candidate = value at heq
  subst candidate
  exact ⟨index, hzip⟩

private theorem applicableObligation_mem_of_generated
    (schema : Schema) (required provided : OperationShape)
    {assignment : BoolCase} {path : List PathStep}
    (hassignment
      : assignment
        ∈ allBoolCases (supportUnion required.boolSupport provided.boolSupport))
    (hpath : path ∈ required.root.enumeratePaths schema assignment required.rootType)
    : ∃ origin,
        ({
            origin := origin
            obligation := { assignment := assignment, path := path }
          }
          : ApplicableObligation)
        ∈ applicableObligations schema required provided := by
  rcases exists_mem_zipIdx_of_mem hassignment with
    ⟨assignmentIndex, hassignmentIndex⟩
  rcases exists_mem_zipIdx_of_mem hpath with
    ⟨pathIndex, hpathIndex⟩
  refine ⟨{ assignmentIndex := assignmentIndex, pathIndex := pathIndex }, ?_⟩
  rw [applicableObligations, List.mem_flatMap]
  refine ⟨(assignment, assignmentIndex), hassignmentIndex, ?_⟩
  rw [List.mem_map]
  exact ⟨(path, pathIndex), hpathIndex, rfl⟩

private theorem ApplicableObligation.generated
    {schema : Schema} {required provided : OperationShape}
    {applicable : ApplicableObligation}
    (hmem : applicable ∈ applicableObligations schema required provided)
    : applicable.obligation.assignment
        ∈ allBoolCases (supportUnion required.boolSupport provided.boolSupport)
      ∧ applicable.obligation.path
        ∈ required.root.enumeratePaths
            schema applicable.obligation.assignment required.rootType := by
  rw [applicableObligations, List.mem_flatMap] at hmem
  rcases hmem with
    ⟨⟨assignment, assignmentIndex⟩, hassignment, hpath⟩
  rw [List.mem_map] at hpath
  rcases hpath with ⟨⟨path, pathIndex⟩, hpath, heq⟩
  subst applicable
  exact ⟨List.fst_mem_of_mem_zipIdx hassignment,
    List.fst_mem_of_mem_zipIdx hpath⟩

private theorem ApplicableObligation.requiredDenotes
    {schema : Schema} {required provided : OperationShape}
    {applicable : ApplicableObligation}
    (hmem : applicable ∈ applicableObligations schema required provided)
    : required.root.DenotesPath schema applicable.obligation.assignment
        required.rootType applicable.obligation.path :=
  (ResponseShape.mem_enumeratePaths_iff
    required.root schema applicable.obligation.assignment required.rootType
    applicable.obligation.path).mp
    (ApplicableObligation.generated hmem).2

private theorem ApplicableObligation.completeAssignment
    {schema : Schema} {required provided : OperationShape}
    {applicable : ApplicableObligation}
    (hmem : applicable ∈ applicableObligations schema required provided)
    : completeNormalBoolCase
        (supportUnion required.boolSupport provided.boolSupport)
        applicable.obligation.assignment :=
  completeNormalBoolCase_of_mem_allBoolCases
    (supportUnion_nodup required.boolSupport provided.boolSupport)
    (ApplicableObligation.generated hmem).1

private theorem ApplicableObligation.toContribution_mem
    {schema : Schema} {required provided : OperationShape}
    {applicable : ApplicableObligation}
    (hmem : applicable ∈ applicableObligations schema required provided)
    : applicable.toContribution schema provided
      ∈ obligationContributions schema required provided := by
  exact List.mem_map.mpr ⟨applicable, hmem, rfl⟩

private theorem applicable_of_contribution_mem
    {schema : Schema} {required provided : OperationShape}
    {contribution : ObligationContribution}
    (hmem : contribution ∈ obligationContributions schema required provided)
    : ∃ applicable,
        applicable ∈ applicableObligations schema required provided
        ∧ applicable.toContribution schema provided = contribution := by
  exact List.mem_map.mp hmem

private def originsForAssignment
    (schema : Schema) (required : OperationShape)
    (indexedAssignment : BoolCase × Nat)
    : List ObligationOrigin :=
  (required.root.enumeratePaths schema indexedAssignment.1 required.rootType).zipIdx.map
    fun indexedPath =>
      {
        assignmentIndex := indexedAssignment.2
        pathIndex := indexedPath.2
      }

private theorem originsForAssignment_nodup
    (schema : Schema) (required : OperationShape)
    (indexedAssignment : BoolCase × Nat)
    : (originsForAssignment schema required indexedAssignment).Nodup := by
  let paths := required.root.enumeratePaths
    schema indexedAssignment.1 required.rootType
  have hindices : (paths.zipIdx.map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hmapped :
      ((paths.zipIdx.map Prod.snd).map
        (fun pathIndex : Nat =>
          ({ assignmentIndex := indexedAssignment.2
             pathIndex := pathIndex } : ObligationOrigin))).Nodup :=
    List.Pairwise.map
      (fun pathIndex : Nat =>
        ({ assignmentIndex := indexedAssignment.2
           pathIndex := pathIndex } : ObligationOrigin))
      (by
        intro left right hne heq
        apply hne
        exact congrArg ObligationOrigin.pathIndex heq)
      hindices
  rw [List.map_map] at hmapped
  change (paths.zipIdx.map
    (fun indexedPath : List PathStep × Nat =>
      ({ assignmentIndex := indexedAssignment.2
         pathIndex := indexedPath.2 } : ObligationOrigin))).Nodup at hmapped
  simpa only [originsForAssignment, paths] using hmapped

private theorem assignmentIndex_eq_of_mem_originsForAssignment
    {schema : Schema} {required : OperationShape}
    {indexedAssignment : BoolCase × Nat} {origin : ObligationOrigin}
    (hmem : origin ∈ originsForAssignment schema required indexedAssignment)
    : origin.assignmentIndex = indexedAssignment.2 := by
  rw [originsForAssignment, List.mem_map] at hmem
  rcases hmem with ⟨indexedPath, _hpath, heq⟩
  subst origin
  rfl

private theorem applicableObligation_origins_nodup
    (schema : Schema) (required provided : OperationShape)
    : ((applicableObligations schema required provided).map
        ApplicableObligation.origin).Nodup := by
  let assignments :=
    (allBoolCases
      (supportUnion required.boolSupport provided.boolSupport)).zipIdx
  have hassignmentIndices : (assignments.map Prod.snd).Nodup := by
    dsimp [assignments]
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have hassignmentPairwise :
      assignments.Pairwise (fun left right => left.2 ≠ right.2) := by
    exact List.pairwise_map.mp hassignmentIndices
  have hflat :
      (assignments.flatMap (originsForAssignment schema required)).Nodup :=
    List.pairwise_flatMap.mpr
      ⟨by
        intro indexedAssignment _hmem
        exact originsForAssignment_nodup schema required indexedAssignment,
       hassignmentPairwise.imp (by
        intro left right hindices leftOrigin _hleft rightOrigin _hright heq
        apply hindices
        exact
          (assignmentIndex_eq_of_mem_originsForAssignment _hleft).symm.trans
            ((congrArg ObligationOrigin.assignmentIndex heq).trans
              (assignmentIndex_eq_of_mem_originsForAssignment _hright)))⟩
  rw [applicableObligations, List.map_flatMap]
  simp only [List.map_map]
  change (assignments.flatMap (originsForAssignment schema required)).Nodup
  exact hflat

private theorem countP_origin_eq_one_of_mem_nodup
    {α : Type} (origin : α → ObligationOrigin)
    : ∀ {values : List α} {value : α},
        (values.map origin).Nodup
        → value ∈ values
        → values.countP (fun candidate => decide (origin candidate = origin value)) = 1
  | [], _value, _hnodup, hmem => by
      simp at hmem
  | head :: rest, value, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with heq | hrest
      · subst value
        have htailZero :
            rest.countP
              (fun candidate => decide (origin candidate = origin head)) = 0 :=
          List.countP_eq_zero.mpr (by
            intro candidate hcandidate hequal
            have horigin : origin candidate = origin head :=
              of_decide_eq_true hequal
            exact hparts.1
              (List.mem_map.mpr
                ⟨candidate, hcandidate, horigin⟩))
        simp [htailZero]
      · have hheadNe : origin head ≠ origin value := by
          intro heq
          exact hparts.1
            (List.mem_map.mpr ⟨value, hrest, heq.symm⟩)
        have hheadFalse : decide (origin head = origin value) = false := by
          simp [hheadNe]
        simp [hheadFalse,
          countP_origin_eq_one_of_mem_nodup origin hparts.2 hrest]

/-- Every precomputed applicable obligation contributes exactly once, by its
stable `(assignmentIndex, pathIndex)` origin, independently of classification. -/
theorem everyApplicableObligationContributesExactlyOnce
    (schema : Schema) (required provided : OperationShape)
    (applicable : ApplicableObligation)
    (hmem : applicable ∈ applicableObligations schema required provided)
    : (obligationContributions schema required provided).countP
        (fun contribution => decide (contribution.origin = applicable.origin))
      = 1 := by
  have happlicableCount :=
    countP_origin_eq_one_of_mem_nodup ApplicableObligation.origin
      (applicableObligation_origins_nodup schema required provided) hmem
  rw [obligationContributions, List.countP_map]
  change (applicableObligations schema required provided).countP
    (fun candidate => decide (candidate.origin = applicable.origin)) = 1
  exact happlicableCount

private theorem firstUncoveredContribution?_eq_none_iff
    (contributions : List ObligationContribution)
    : firstUncoveredContribution? contributions = none
      ↔ ∀ contribution ∈ contributions, contribution.covered = true := by
  induction contributions with
  | nil => simp [firstUncoveredContribution?]
  | cons contribution rest ih =>
      by_cases hcovered : contribution.covered = true
      · simp [firstUncoveredContribution?, hcovered, ih]
      · have hfalse : contribution.covered = false := by
          cases hvalue : contribution.covered
          · rfl
          · exact False.elim (hcovered hvalue)
        simp [firstUncoveredContribution?, hfalse]

/-- No executable semantic counterexample is exactly finite header agreement
plus coverage of every precomputed contribution. -/
theorem shapeSubsetCounterexample?_eq_none_iff
    (schema : Schema) (required provided : OperationShape)
    : shapeSubsetCounterexample? schema required provided = none
      ↔ required.operationType = provided.operationType
        ∧ required.rootType = provided.rootType
        ∧ ∀ contribution,
            contribution ∈ obligationContributions schema required provided
            → contribution.covered = true := by
  have hoperation : required.operationType = provided.operationType := by
    cases required.operationType
    cases provided.operationType
    rfl
  by_cases hroot : required.rootType = provided.rootType
  · cases hfirst : firstUncoveredContribution?
        (obligationContributions schema required provided) with
    | none =>
        have hall :=
          (firstUncoveredContribution?_eq_none_iff
            (obligationContributions schema required provided)).mp hfirst
        simp [shapeSubsetCounterexample?, hoperation, hroot, hfirst]
        exact hall
    | some contribution =>
        have hnotAll : ¬ ∀ candidate,
            candidate ∈ obligationContributions schema required provided →
              candidate.covered = true := by
          intro hall
          have hnone :=
            (firstUncoveredContribution?_eq_none_iff
              (obligationContributions schema required provided)).mpr hall
          rw [hfirst] at hnone
          contradiction
        simp [shapeSubsetCounterexample?, hoperation, hroot, hfirst, hnotAll]
  · simp [shapeSubsetCounterexample?, hoperation, hroot]

/-- The finite semantic counterexample search is exact for `ShapeSubset`. -/
theorem shapeSubsetCounterexample?_eq_none_iff_shapeSubset
    (schema : Schema) (required provided : OperationShape)
    : shapeSubsetCounterexample? schema required provided = none
      ↔ ShapeSubset schema required provided := by
  constructor
  · intro hnone
    have hparts :=
      (shapeSubsetCounterexample?_eq_none_iff schema required provided).mp hnone
    refine ⟨hparts.1, hparts.2.1, ?_⟩
    intro assignment hcomplete path hrequired
    rcases allBoolCases_complete_representative hcomplete with
      ⟨representative, hrepresentativeMem, hequivalent⟩
    have hrepresentativeComplete :
        completeNormalBoolCase
          (supportUnion required.boolSupport provided.boolSupport)
          representative :=
      completeNormalBoolCase_of_mem_allBoolCases
        (supportUnion_nodup required.boolSupport provided.boolSupport)
        hrepresentativeMem
    have hrequiredRepresentative :
        required.root.DenotesPath
          schema representative required.rootType path :=
      (ResponseShape.denotesPath_iff_of_completeBoolCasesEquivalent
        hcomplete hrepresentativeComplete hequivalent).mp hrequired
    have hrequiredMem :
        path ∈ required.root.enumeratePaths
          schema representative required.rootType :=
      (ResponseShape.mem_enumeratePaths_iff
        required.root schema representative required.rootType path).mpr
        hrequiredRepresentative
    rcases applicableObligation_mem_of_generated
        schema required provided hrepresentativeMem hrequiredMem with
      ⟨origin, happlicable⟩
    let applicable : ApplicableObligation :=
      { origin := origin
        obligation := { assignment := representative, path := path } }
    have happlicableMem :
        applicable ∈ applicableObligations schema required provided := by
      exact happlicable
    have hcontribution :=
      ApplicableObligation.toContribution_mem happlicableMem
    have hcovered := hparts.2.2
      (applicable.toContribution schema provided) hcontribution
    have hcoverage :=
      (pathCoveredBool_iff
        (provided.root.enumeratePaths
          schema representative provided.rootType) path).mp hcovered
    rcases hcoverage with
      ⟨providedPath, hprovidedMem, hpathEquivalent⟩
    have hprovidedRepresentative :
        provided.root.DenotesPath
          schema representative provided.rootType providedPath :=
      (ResponseShape.mem_enumeratePaths_iff
        provided.root schema representative provided.rootType providedPath).mp
        hprovidedMem
    have hprovided :
        provided.root.DenotesPath
          schema assignment provided.rootType providedPath :=
      (ResponseShape.denotesPath_iff_of_completeBoolCasesEquivalent
        hcomplete hrepresentativeComplete hequivalent).mpr
        hprovidedRepresentative
    exact ⟨providedPath, hprovided, hpathEquivalent⟩
  · intro hsubset
    apply (shapeSubsetCounterexample?_eq_none_iff
      schema required provided).mpr
    refine ⟨hsubset.1, hsubset.2.1, ?_⟩
    intro contribution hcontribution
    rcases applicable_of_contribution_mem hcontribution with
      ⟨applicable, happlicable, heq⟩
    subst contribution
    have hcomplete := ApplicableObligation.completeAssignment happlicable
    have hrequired := ApplicableObligation.requiredDenotes happlicable
    have hprovided :=
      hsubset.2.2 applicable.obligation.assignment hcomplete
        applicable.obligation.path hrequired
    rcases hprovided with
      ⟨providedPath, hprovidedDenotes, hpathEquivalent⟩
    apply (pathCoveredBool_iff
      (provided.root.enumeratePaths schema applicable.obligation.assignment
        provided.rootType) applicable.obligation.path).mpr
    exact ⟨providedPath,
      (ResponseShape.mem_enumeratePaths_iff
        provided.root schema applicable.obligation.assignment
          provided.rootType providedPath).mpr hprovidedDenotes,
      hpathEquivalent⟩

/-- `ShapeSubset` has a constructive decision procedure given by the finite
semantic-counterexample search. -/
instance instDecidableShapeSubset (schema : Schema) (required provided : OperationShape)
    : Decidable (ShapeSubset schema required provided) :=
  if hnone :
    shapeSubsetCounterexample? schema required provided = none
  then
    isTrue
      ((shapeSubsetCounterexample?_eq_none_iff_shapeSubset schema required provided).mp
        hnone)
  else
    isFalse
      fun hsubset =>
        hnone
          ((shapeSubsetCounterexample?_eq_none_iff_shapeSubset schema required provided).mpr
            hsubset)

/-- Readiness diagnostics are absent exactly when all four readiness premises
hold. -/
theorem readinessFailure?_eq_none_iff
    (schema : Schema) (required provided : OperationShape)
    : readinessFailure? schema required provided = none
      ↔ ShapeComparisonReady schema required provided := by
  by_cases hrequiredWellFormed : required.WellFormed schema
  · by_cases hrequiredFullMinterm : required.FullMinterm
    · by_cases hprovidedWellFormed : provided.WellFormed schema
      · by_cases hprovidedFullMinterm : provided.FullMinterm
        · simp [readinessFailure?, ShapeComparisonReady, hrequiredWellFormed,
            hrequiredFullMinterm, hprovidedWellFormed,
            hprovidedFullMinterm]
        · simp [readinessFailure?, ShapeComparisonReady, hrequiredWellFormed,
            hrequiredFullMinterm, hprovidedWellFormed,
            hprovidedFullMinterm]
      · simp [readinessFailure?, ShapeComparisonReady, hrequiredWellFormed,
          hrequiredFullMinterm, hprovidedWellFormed]
    · simp [readinessFailure?, ShapeComparisonReady, hrequiredWellFormed,
        hrequiredFullMinterm]
  · simp [readinessFailure?, ShapeComparisonReady, hrequiredWellFormed]

private theorem readinessFailure?_eq_some_not_ready
    {schema : Schema} {required provided : OperationShape}
    {reason : ShapeUnknownReason}
    (hreason : readinessFailure? schema required provided = some reason)
    : ¬ ShapeComparisonReady schema required provided := by
  intro hready
  have hnone :=
    (readinessFailure?_eq_none_iff schema required provided).mpr hready
  rw [hreason] at hnone
  contradiction

/-- Absence of a semantic counterexample produces the proof-relevant finite
coverage basis retained in an accepted verdict. -/
def subsetAcceptedBasis_of_noCounterexample
    {schema : Schema} {required provided : OperationShape}
    (hnone : shapeSubsetCounterexample? schema required provided = none)
    : SubsetAcceptedBasis schema required provided := by
  have hparts :=
    (shapeSubsetCounterexample?_eq_none_iff schema required provided).mp hnone
  refine
    { operationTypeEq := hparts.1
      rootTypeEq := hparts.2.1
      coverage := ?_ }
  intro applicable happlicable
  have hrequired := ApplicableObligation.requiredDenotes happlicable
  have hcontribution :=
    ApplicableObligation.toContribution_mem happlicable
  have hcovered := hparts.2.2
    (applicable.toContribution schema provided) hcontribution
  let providedPaths :=
    provided.root.enumeratePaths schema applicable.obligation.assignment
      provided.rootType
  change pathCoveredBool providedPaths applicable.obligation.path = true
    at hcovered
  cases hfirst : firstCoveringPath?
      applicable.obligation.path providedPaths with
  | none =>
      have hfalse : pathCoveredBool
          providedPaths applicable.obligation.path = false := by
        simp [pathCoveredBool, hfirst]
      rw [hfalse] at hcovered
      contradiction
  | some providedPath =>
      have hproperties :=
        firstCoveringPath?_eq_some_properties hfirst
      exact
        { requiredDenotes := hrequired
          providedPath := providedPath
          providedDenotes :=
            (ResponseShape.mem_enumeratePaths_iff
              provided.root schema applicable.obligation.assignment
                provided.rootType providedPath).mp hproperties.1
          pathsEquivalent := hproperties.2 }

/-- The retained finite coverage basis independently proves shape subset. -/
theorem SubsetAcceptedBasis.sound
    {schema : Schema} {required provided : OperationShape}
    (basis : SubsetAcceptedBasis schema required provided)
    : ShapeSubset schema required provided := by
  refine ⟨basis.operationTypeEq, basis.rootTypeEq, ?_⟩
  intro assignment hcomplete path hrequired
  rcases allBoolCases_complete_representative hcomplete with
    ⟨representative, hrepresentativeMem, hequivalent⟩
  have hrepresentativeComplete :
      completeNormalBoolCase
        (supportUnion required.boolSupport provided.boolSupport)
        representative :=
    completeNormalBoolCase_of_mem_allBoolCases
      (supportUnion_nodup required.boolSupport provided.boolSupport)
      hrepresentativeMem
  have hrequiredRepresentative :
      required.root.DenotesPath
        schema representative required.rootType path :=
    (ResponseShape.denotesPath_iff_of_completeBoolCasesEquivalent
      hcomplete hrepresentativeComplete hequivalent).mp hrequired
  have hrequiredMem :
      path ∈ required.root.enumeratePaths
        schema representative required.rootType :=
    (ResponseShape.mem_enumeratePaths_iff
      required.root schema representative required.rootType path).mpr
      hrequiredRepresentative
  rcases applicableObligation_mem_of_generated
      schema required provided hrepresentativeMem hrequiredMem with
    ⟨origin, happlicable⟩
  let applicable : ApplicableObligation :=
    { origin := origin
      obligation := { assignment := representative, path := path } }
  have happlicableMem :
      applicable ∈ applicableObligations schema required provided :=
    happlicable
  let witness := basis.coverage applicable happlicableMem
  have hprovided :
      provided.root.DenotesPath
        schema assignment provided.rootType witness.providedPath :=
    (ResponseShape.denotesPath_iff_of_completeBoolCasesEquivalent
      hcomplete hrepresentativeComplete hequivalent).mpr
      witness.providedDenotes
  exact ⟨witness.providedPath, hprovided, witness.pathsEquivalent⟩

/-- Every returned semantic counterexample accompanies a proof that subset is
false. -/
theorem shapeSubsetCounterexample?_eq_some_not_shapeSubset
    {schema : Schema} {required provided : OperationShape}
    {witness : SubsetCounterexample}
    (hsome : shapeSubsetCounterexample? schema required provided = some witness)
    : ¬ ShapeSubset schema required provided := by
  intro hsubset
  have hnone :=
    (shapeSubsetCounterexample?_eq_none_iff_shapeSubset
      schema required provided).mpr hsubset
  rw [hsome] at hnone
  contradiction

private inductive SemanticSubsetVerdict
    (schema : Schema) (required provided : OperationShape) where
  | accepted
    (proof : ShapeSubset schema required provided)
    (basis : SubsetAcceptedBasis schema required provided)
  | rejected
    (proof : ¬ ShapeSubset schema required provided)
    (witness : SubsetCounterexample)

private def decideSemanticShapeSubset
    (schema : Schema) (required provided : OperationShape)
    : SemanticSubsetVerdict schema required provided :=
  match hcounter : shapeSubsetCounterexample? schema required provided with
  | some witness =>
      .rejected (shapeSubsetCounterexample?_eq_some_not_shapeSubset hcounter) witness
  | none =>
      .accepted
        ((shapeSubsetCounterexample?_eq_none_iff_shapeSubset schema required provided).mp
          hcounter)
        (subsetAcceptedBasis_of_noCounterexample hcounter)

/--
Proof-carrying three-valued subset decision.

Semantic counterexamples are computed first. Consequently rejection outranks
readiness uncertainty; only a fully covered but unready pair returns `unknown`.
-/
def decideShapeSubset (schema : Schema) (required provided : OperationShape)
    : ShapeSubsetVerdict schema required provided :=
  match decideSemanticShapeSubset schema required provided with
  | .accepted proof basis =>
      match readinessFailure? schema required provided with
      | some reason => .unknown reason
      | none => .accepted proof basis
  | .rejected proof witness => .rejected proof witness

/-- Every accepted verdict carries a sound subset proof. -/
theorem shapeSubset_accepted_sound
    {schema : Schema} {required provided : OperationShape}
    (haccepted
      : ∃ proof basis,
          decideShapeSubset schema required provided
          = CertifiedVerdict.accepted proof basis)
    : ShapeSubset schema required provided := by
  rcases haccepted with ⟨_proof, basis, _hresult⟩
  exact basis.sound

/-- Every rejected verdict carries a sound negated-subset proof. -/
theorem shapeSubset_rejected_sound
    {schema : Schema} {required provided : OperationShape}
    (hrejected
      : ∃ proof witness,
          decideShapeSubset schema required provided
          = CertifiedVerdict.rejected proof witness)
    : ¬ ShapeSubset schema required provided := by
  rcases hrejected with ⟨proof, _witness, _hresult⟩
  exact proof

/-- Unknown means exactly: no proof-carrying semantic counterexample was found, the
subset relation therefore holds, and the reported readiness failure prevents
positive evidence. This uses readiness reasons rather than synthetic
path obligations for malformed-shape uncertainty. -/
theorem shapeSubset_unknown_characterization
    {schema : Schema} {required provided : OperationShape}
    (reason : ShapeUnknownReason)
    : decideShapeSubset schema required provided = CertifiedVerdict.unknown reason
      ↔ shapeSubsetCounterexample? schema required provided = none
        ∧ readinessFailure? schema required provided = some reason
        ∧ ShapeSubset schema required provided
        ∧ ¬ ShapeComparisonReady schema required provided := by
  constructor
  · intro hunknown
    cases hsemantic : decideSemanticShapeSubset schema required provided with
    | rejected proof witness =>
        simp [decideShapeSubset, hsemantic] at hunknown
    | accepted proof basis =>
      cases hreadiness : readinessFailure? schema required provided with
      | none =>
          simp [decideShapeSubset, hsemantic, hreadiness] at hunknown
      | some actualReason =>
          have heq : actualReason = reason := by
            simpa [decideShapeSubset, hsemantic, hreadiness] using hunknown
          subst actualReason
          have hcounter :=
            (shapeSubsetCounterexample?_eq_none_iff_shapeSubset
              schema required provided).mpr proof
          refine ⟨hcounter, rfl, proof, ?_⟩
          exact readinessFailure?_eq_some_not_ready hreadiness
  · rintro ⟨hcounter, hreadiness, _hsubset, _hnotReady⟩
    have hsubset :=
      (shapeSubsetCounterexample?_eq_none_iff_shapeSubset
        schema required provided).mp hcounter
    cases hsemantic : decideSemanticShapeSubset schema required provided with
    | accepted proof basis =>
        simp [decideShapeSubset, hsemantic, hreadiness]
    | rejected proof witness =>
        exact False.elim (proof hsubset)

/-- Under readiness, acceptance is equivalent to the subset proposition. -/
theorem decideShapeSubset_accepted_iff
    {schema : Schema} {required provided : OperationShape}
    (hready : ShapeComparisonReady schema required provided)
    : (∃ proof basis,
        decideShapeSubset schema required provided
        = CertifiedVerdict.accepted proof basis)
      ↔ ShapeSubset schema required provided := by
  constructor
  · exact shapeSubset_accepted_sound
  · intro hsubset
    have hreadiness :=
      (readinessFailure?_eq_none_iff schema required provided).mpr hready
    cases hsemantic : decideSemanticShapeSubset schema required provided with
    | accepted proof basis =>
        exact ⟨proof, basis,
          by simp [decideShapeSubset, hsemantic, hreadiness]⟩
    | rejected proof witness =>
        exact False.elim (proof hsubset)

/-- Under readiness, rejection is equivalent to failure of subset. -/
theorem decideShapeSubset_rejected_iff
    {schema : Schema} {required provided : OperationShape}
    (_hready : ShapeComparisonReady schema required provided)
    : (∃ proof witness,
        decideShapeSubset schema required provided
        = CertifiedVerdict.rejected proof witness)
      ↔ ¬ ShapeSubset schema required provided := by
  constructor
  · exact shapeSubset_rejected_sound
  · intro hnotSubset
    cases hsemantic : decideSemanticShapeSubset schema required provided with
    | accepted proof basis =>
        exact False.elim (hnotSubset proof)
    | rejected proof witness =>
        exact ⟨proof, witness, by simp [decideShapeSubset, hsemantic]⟩

/-- A ready comparison never returns unknown. -/
theorem decideShapeSubset_complete
    {schema : Schema} {required provided : OperationShape}
    (hready : ShapeComparisonReady schema required provided)
    : (∃ proof basis,
        decideShapeSubset schema required provided
        = CertifiedVerdict.accepted proof basis)
      ∨ (∃ proof witness,
          decideShapeSubset schema required provided
          = CertifiedVerdict.rejected proof witness) := by
  cases hsemantic : decideSemanticShapeSubset schema required provided with
  | accepted proof basis =>
      left
      have hreadiness :=
        (readinessFailure?_eq_none_iff schema required provided).mpr hready
      exact ⟨proof, basis,
        by simp [decideShapeSubset, hsemantic, hreadiness]⟩
  | rejected proof witness =>
      right
      exact ⟨proof, witness, by simp [decideShapeSubset, hsemantic]⟩

end ResponseShape

end GraphQL
