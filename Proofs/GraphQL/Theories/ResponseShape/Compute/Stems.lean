import GraphQL.Theories.ResponseShape.Compute
import Proofs.GraphQL.Theories.NormalForm.CompleteNormalization.OperationNormality

/-!
Decoder facts for Boolean stems emitted by complete normalization.
-/

namespace GraphQL

namespace ResponseShape

/-- The stem-directive decoder is a left inverse of the normalizer's encoder. -/
theorem decodeStemDirective_directiveForBit
    (varName : NormalForm.BoolVar) (value : Bool)
    : decodeStemDirective (NormalForm.directiveForBit varName value)
        = .ok (varName, value) := by
  cases value <;> rfl

/--
Decoding a nonempty generated stem recovers its Boolean case and nonempty body.
The body premise matches `completeNormalizeRootBranch`, which omits empty cases.
-/
theorem decodeCompleteStem_wrapWithBoolCase
    : ∀ {boolCase : NormalForm.BoolCase} {body : List Selection}
        {selection : Selection},
        boolCase ≠ [] ->
        body ≠ [] ->
        NormalForm.wrapWithBoolCase boolCase body = [selection] ->
        decodeCompleteStem boolCase.length selection = .ok (boolCase, body)
  | [], _body, _selection, hcase, _hbody, _hwrap => by
      exact False.elim (hcase rfl)
  | [(varName, value)], body, selection, _hcase, hbody, hwrap => by
      simp [NormalForm.wrapWithBoolCase] at hwrap
      subst selection
      rw [decodeCompleteStem.eq_def]
      simp only [List.length_cons, List.length_nil]
      cases value <;>
        simp [NormalForm.directiveForBit, decodeStemDirective, hbody] <;>
        rfl
  | (varName, value) :: (nextVar, nextValue) :: rest,
      body, selection, _hcase, hbody, hwrap => by
      simp [NormalForm.wrapWithBoolCase] at hwrap
      subst selection
      have htail :=
        decodeCompleteStem_wrapWithBoolCase
          (boolCase := (nextVar, nextValue) :: rest)
          (body := body)
          (selection :=
            .inlineFragment none
              [NormalForm.directiveForBit nextVar nextValue]
              (NormalForm.wrapWithBoolCase rest body))
          (by simp) hbody rfl
      have htail' :
          decodeCompleteStem (rest.length + 1)
              (.inlineFragment none
                [NormalForm.directiveForBit nextVar nextValue]
                (NormalForm.wrapWithBoolCase rest body)) =
            .ok ((nextVar, nextValue) :: rest, body) := by
        simpa using htail
      rw [decodeCompleteStem.eq_def]
      simp only [List.length_cons]
      cases value with
      | false =>
          change
            (do
              let decoded ←
                decodeCompleteStem (rest.length + 1)
                  (.inlineFragment none
                    [NormalForm.directiveForBit nextVar nextValue]
                    (NormalForm.wrapWithBoolCase rest body))
              .ok ((varName, false) :: decoded.1, decoded.2)) =
              .ok ((varName, false) :: (nextVar, nextValue) :: rest, body)
          rw [htail']
          rfl
      | true =>
          change
            (do
              let decoded ←
                decodeCompleteStem (rest.length + 1)
                  (.inlineFragment none
                    [NormalForm.directiveForBit nextVar nextValue]
                    (NormalForm.wrapWithBoolCase rest body))
              .ok ((varName, true) :: decoded.1, decoded.2)) =
              .ok ((varName, true) :: (nextVar, nextValue) :: rest, body)
          rw [htail']
          rfl

private theorem insertLiteralSorted_perm (literal : BoolLiteral)
    : ∀ literals,
        (Clause.insertLiteralSorted literal literals).Perm (literal :: literals)
  | [] => List.Perm.refl _
  | candidate :: rest => by
      by_cases hle : literal.1 ≤ candidate.1
      · simp [Clause.insertLiteralSorted, hle]
      · rw [Clause.insertLiteralSorted]
        simp only [hle, if_false]
        exact
          ((insertLiteralSorted_perm literal rest).cons candidate).trans
            (List.Perm.swap literal candidate rest)

theorem sortLiterals_perm
    : ∀ literals, (Clause.sortLiterals literals).Perm literals
  | [] => List.Perm.refl _
  | literal :: rest =>
      (insertLiteralSorted_perm literal (Clause.sortLiterals rest)).trans
        ((sortLiterals_perm rest).cons literal)

private theorem insertLiteralSorted_pairwise (literal : BoolLiteral)
    : ∀ literals,
        literal.1 ∉ literals.map Prod.fst ->
        List.Pairwise (fun left right : BoolLiteral => left.1 < right.1) literals ->
        List.Pairwise (fun left right : BoolLiteral => left.1 < right.1)
          (Clause.insertLiteralSorted literal literals)
  | [], _hfresh, _hsorted => by
      simp [Clause.insertLiteralSorted]
  | candidate :: rest, hfresh, hsorted => by
      have hcandidateRest :
          ∀ restLiteral ∈ rest, candidate.1 < restLiteral.1 :=
        (List.pairwise_cons.mp hsorted).1
      have hrestSorted :
          List.Pairwise (fun left right : BoolLiteral => left.1 < right.1) rest :=
        (List.pairwise_cons.mp hsorted).2
      have hnameNe : literal.1 ≠ candidate.1 := by
        intro heq
        apply hfresh
        simp [heq]
      have hrestFresh : literal.1 ∉ rest.map Prod.fst := by
        intro hmem
        exact hfresh (by simp [hmem])
      by_cases hle : literal.1 ≤ candidate.1
      · rw [Clause.insertLiteralSorted]
        simp only [hle, if_true]
        apply List.pairwise_cons.mpr
        constructor
        · intro restLiteral hmem
          rcases List.mem_cons.mp hmem with hhead | htail
          · subst restLiteral
            exact Std.lt_of_le_of_ne hle hnameNe
          · exact String.lt_trans (Std.lt_of_le_of_ne hle hnameNe)
              (hcandidateRest restLiteral htail)
        · exact hsorted
      · rw [Clause.insertLiteralSorted]
        simp only [hle, if_false]
        apply List.pairwise_cons.mpr
        constructor
        · intro restLiteral hmem
          have hmem' : restLiteral = literal ∨ restLiteral ∈ rest := by
            have hperm := insertLiteralSorted_perm literal rest
            have : restLiteral ∈ literal :: rest := hperm.mem_iff.mp hmem
            simpa only [List.mem_cons] using this
          rcases hmem' with hfield | hrest
          · subst restLiteral
            exact String.not_le.mp hle
          · exact hcandidateRest restLiteral hrest
        · exact insertLiteralSorted_pairwise literal rest hrestFresh hrestSorted

private theorem sortLiterals_pairwise
    : ∀ literals,
        (literals.map Prod.fst).Nodup ->
        List.Pairwise (fun left right : BoolLiteral => left.1 < right.1)
          (Clause.sortLiterals literals)
  | [], _hnodup => by
      simp [Clause.sortLiterals]
  | literal :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      have hrestSorted := sortLiterals_pairwise rest hparts.2
      have hfresh : literal.1 ∉ (Clause.sortLiterals rest).map Prod.fst := by
        intro hmem
        have hmapPerm := (sortLiterals_perm rest).map Prod.fst
        exact hparts.1 (hmapPerm.mem_iff.mp hmem)
      exact insertLiteralSorted_pairwise literal
        (Clause.sortLiterals rest) hfresh hrestSorted

private theorem pairwise_map_fst
    : ∀ {literals : List BoolLiteral},
        List.Pairwise (fun left right : BoolLiteral => left.1 < right.1) literals ->
        List.Pairwise (fun left right : Name => left < right)
          (literals.map Prod.fst)
  | [], _hsorted => by simp
  | literal :: rest, hsorted => by
      apply List.pairwise_cons.mpr
      constructor
      · intro restName hmem
        rcases List.mem_map.mp hmem with ⟨restLiteral, hrest, heq⟩
        subst restName
        exact (List.pairwise_cons.mp hsorted).1 restLiteral hrest
      · exact pairwise_map_fst (List.pairwise_cons.mp hsorted).2

private theorem allLiteralNamesContained
    (support : List NormalForm.BoolVar)
    : ∀ literals : List BoolLiteral,
        (∀ literal ∈ literals, literal.1 ∈ support) ->
        literals.all (fun literal => support.contains literal.1) = true
  | [], _hsubset => rfl
  | literal :: rest, hsubset => by
      apply Bool.and_eq_true_iff.mpr
      constructor
      · simpa using hsubset literal (by simp)
      · exact allLiteralNamesContained support rest
          (fun candidate hmem =>
            hsubset candidate (List.mem_cons_of_mem literal hmem))

private theorem validBool_eq_true_of_pairwise
    (support : List NormalForm.BoolVar)
    : ∀ literals : List BoolLiteral,
        List.Pairwise (fun left right : Name => left < right)
            (literals.map Prod.fst) ->
        literals.all (fun literal => support.contains literal.1) = true ->
        Clause.validBool support { literals := literals } = true
  | [], _hsorted, _hcontained => by
      unfold Clause.validBool
      rfl
  | [literal], _hsorted, hcontained => by
      unfold Clause.validBool
      apply Bool.and_eq_true_iff.mpr
      exact ⟨rfl, hcontained⟩
  | first :: second :: rest, hsorted, hcontained => by
      have hheadLT : first.1 < second.1 :=
        (List.pairwise_cons.mp hsorted).1 second.1 (by simp)
      have htailSorted :
          List.Pairwise (fun left right : Name => left < right)
            ((second :: rest).map Prod.fst) :=
        (List.pairwise_cons.mp hsorted).2
      have htailContained :
          (second :: rest).all
              (fun literal => support.contains literal.1) = true :=
        (Bool.and_eq_true_iff.mp hcontained).2
      have htailValid :=
        validBool_eq_true_of_pairwise support (second :: rest)
          htailSorted htailContained
      unfold Clause.validBool at htailValid ⊢
      apply Bool.and_eq_true_iff.mpr
      constructor
      · have htailIncreasing := (Bool.and_eq_true_iff.mp htailValid).1
        change (decide (first.1 < second.1) && _) = true
        simp [hheadLT]
        exact htailIncreasing
      · exact hcontained

private theorem canonicalClause_valid
    (support : List NormalForm.BoolVar) (literals : List BoolLiteral)
    (hnodup : (literals.map Prod.fst).Nodup)
    (hsubset : ∀ literal ∈ literals, literal.1 ∈ support)
    : (Clause.canonical { literals := literals }).Valid support := by
  unfold Clause.Valid Clause.canonical
  apply validBool_eq_true_of_pairwise
  · exact pairwise_map_fst (sortLiterals_pairwise literals hnodup)
  · apply allLiteralNamesContained
    intro literal hmem
    exact hsubset literal ((sortLiterals_perm literals).mem_iff.mp hmem)

private theorem anyLiteralWithName
    (varName : NormalForm.BoolVar)
    : ∀ literals : List BoolLiteral,
        (∃ value, (varName, value) ∈ literals) ->
        literals.any (fun literal => literal.1 == varName) = true
  | [], hexists => by
      rcases hexists with ⟨value, hmem⟩
      cases hmem
  | literal :: rest, hexists => by
      rcases hexists with ⟨value, hmem⟩
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        simp
      · by_cases hsame : literal.1 = varName
        · simp [hsame]
        · simp [anyLiteralWithName varName rest ⟨value, htail⟩]

private theorem allNamesHaveLiterals
    (literals : List BoolLiteral)
    : ∀ support : List NormalForm.BoolVar,
        (∀ varName ∈ support, ∃ value, (varName, value) ∈ literals) ->
        support.all
            (fun varName =>
              literals.any (fun literal => literal.1 == varName)) = true
  | [], _hexists => rfl
  | varName :: rest, hexists => by
      apply Bool.and_eq_true_iff.mpr
      constructor
      · exact anyLiteralWithName varName literals
          (hexists varName (by simp))
      · exact allNamesHaveLiterals literals rest
          (fun candidate hmem =>
            hexists candidate (List.mem_cons_of_mem varName hmem))

/-- Duplicate-free name lists pass the decoder's first-duplicate check. -/
theorem firstDuplicate?_eq_none_of_nodup
    : ∀ names : List Name,
        names.Nodup -> firstDuplicate? names = none
  | [], _hnodup => rfl
  | candidate :: rest, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      simp [firstDuplicate?, hparts.1,
        firstDuplicate?_eq_none_of_nodup rest hparts.2]

private theorem firstOutsideSupport?_eq_none_of_subset
    (support : List NormalForm.BoolVar)
    : ∀ literals : List BoolLiteral,
        (∀ literal ∈ literals, literal.1 ∈ support) ->
        firstOutsideSupport? support literals = none
  | [], _hsubset => rfl
  | literal :: rest, hsubset => by
      have hhead := hsubset literal (by simp)
      have htail : ∀ candidate ∈ rest, candidate.1 ∈ support :=
        fun candidate hmem =>
          hsubset candidate (List.mem_cons_of_mem literal hmem)
      simp [firstOutsideSupport?, hhead,
        firstOutsideSupport?_eq_none_of_subset support rest htail]

private theorem firstMissingStemVariable?_eq_none_of_complete
    (literals : List BoolLiteral)
    : ∀ support : List NormalForm.BoolVar,
        (∀ varName ∈ support, ∃ value, (varName, value) ∈ literals) ->
        firstMissingStemVariable? literals support = none
  | [], _hcomplete => rfl
  | varName :: rest, hcomplete => by
      have hhead := anyLiteralWithName varName literals
        (hcomplete varName (by simp))
      have htail :
          ∀ candidate ∈ rest, ∃ value, (candidate, value) ∈ literals :=
        fun candidate hmem =>
          hcomplete candidate (List.mem_cons_of_mem varName hmem)
      simp [firstMissingStemVariable?, hhead,
        firstMissingStemVariable?_eq_none_of_complete literals rest htail]

/-- Every generated case has the same length as its support. -/
theorem boolCase_length_of_mem_allBoolCases
    {support : List NormalForm.BoolVar} {boolCase : NormalForm.BoolCase}
    (hcase : boolCase ∈ NormalForm.allBoolCases support)
    : boolCase.length = support.length := by
  have hnames :=
    NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
      hcase
  simpa using congrArg List.length hnames

/-- A generated case canonicalizes to a valid clause over its support. -/
theorem canonicalClause_valid_of_mem_allBoolCases
    (support : List NormalForm.BoolVar) {boolCase : NormalForm.BoolCase}
    (hsupport : support.Nodup)
    (hcase : boolCase ∈ NormalForm.allBoolCases support)
    : (Clause.canonical { literals := boolCase }).Valid support := by
  have hnames : boolCase.map Prod.fst = support :=
    NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
      hcase
  apply canonicalClause_valid support boolCase
  · simpa [hnames] using hsupport
  · intro literal hmem
    have : literal.1 ∈ boolCase.map Prod.fst :=
      List.mem_map.mpr ⟨literal, hmem, rfl⟩
    simpa [hnames] using this

/-- A generated case canonicalizes to a complete minterm over its support. -/
theorem canonicalClause_completeMinterm_of_mem_allBoolCases
    (support : List NormalForm.BoolVar) {boolCase : NormalForm.BoolCase}
    (hsupport : support.Nodup)
    (hcase : boolCase ∈ NormalForm.allBoolCases support)
    : (Clause.canonical { literals := boolCase }).CompleteMinterm support := by
  have hnames : boolCase.map Prod.fst = support :=
    NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
      hcase
  have hvalid :
      (Clause.canonical { literals := boolCase }).Valid support := by
    exact canonicalClause_valid_of_mem_allBoolCases support hsupport hcase
  have hall :
      support.all
          (fun varName =>
            (Clause.canonical { literals := boolCase }).literals.any
              (fun literal => literal.1 == varName)) = true := by
    apply allNamesHaveLiterals
    intro varName hvar
    have hvar' : varName ∈ boolCase.map Prod.fst := by
      simpa [hnames] using hvar
    rcases List.mem_map.mp hvar' with ⟨literal, hliteral, heq⟩
    have hsorted :
        literal ∈ (Clause.canonical { literals := boolCase }).literals :=
      (sortLiterals_perm boolCase).mem_iff.mpr hliteral
    rcases literal with ⟨literalName, value⟩
    simp only at heq
    subst literalName
    exact ⟨value, hsorted⟩
  unfold Clause.Valid at hvalid
  unfold Clause.CompleteMinterm Clause.completeMintermBool
  simp [hsupport, hvalid, hall]

/-- Every generated Boolean case passes clause validation and canonicalization. -/
theorem clauseFromCompleteStem_allBoolCases
    (support : List NormalForm.BoolVar) {boolCase : NormalForm.BoolCase}
    (hsupport : support.Nodup)
    (hcase : boolCase ∈ NormalForm.allBoolCases support)
    : clauseFromCompleteStem support boolCase =
        .ok (Clause.canonical { literals := boolCase }) := by
  have hnames : boolCase.map Prod.fst = support :=
    NormalForm.CompleteNormalization.boolCase_map_fst_of_mem_allBoolCases
      hcase
  have hcaseNamesNodup : (boolCase.map Prod.fst).Nodup := by
    simpa [hnames] using hsupport
  have hsubset : ∀ literal ∈ boolCase, literal.1 ∈ support := by
    intro literal hmem
    have : literal.1 ∈ boolCase.map Prod.fst :=
      List.mem_map.mpr ⟨literal, hmem, rfl⟩
    simpa [hnames] using this
  have hcomplete :
      ∀ varName ∈ support, ∃ value, (varName, value) ∈ boolCase := by
    intro varName hmem
    have : varName ∈ boolCase.map Prod.fst := by
      simpa [hnames] using hmem
    rcases List.mem_map.mp this with ⟨literal, hliteral, heq⟩
    rcases literal with ⟨literalName, value⟩
    simp only at heq
    subst literalName
    exact ⟨value, hliteral⟩
  have houtside :=
    firstOutsideSupport?_eq_none_of_subset support boolCase hsubset
  have hduplicate :=
    firstDuplicate?_eq_none_of_nodup (boolCase.map Prod.fst)
      hcaseNamesNodup
  have hmissing :=
    firstMissingStemVariable?_eq_none_of_complete boolCase support hcomplete
  have hminterm :=
    canonicalClause_completeMinterm_of_mem_allBoolCases
      support hsupport hcase
  unfold Clause.CompleteMinterm at hminterm
  simp [clauseFromCompleteStem, houtside, hduplicate, hmissing, hminterm]

/-- A generated case activates its own canonical clause. -/
theorem canonicalClause_holdsIn_of_mem_allBoolCases
    (support : List NormalForm.BoolVar) {boolCase : NormalForm.BoolCase}
    (hsupport : support.Nodup)
    (hcase : boolCase ∈ NormalForm.allBoolCases support)
    : (Clause.canonical { literals := boolCase }).HoldsIn boolCase := by
  unfold Clause.HoldsIn
  intro literal hsorted
  change literal ∈ Clause.sortLiterals boolCase at hsorted
  have hliteral : literal ∈ boolCase :=
    (sortLiterals_perm boolCase).mem_iff.mp hsorted
  exact
    NormalForm.CompleteNormalization.BoolCase.lookup?_eq_of_pair_mem_allBoolCases_nodup
      hsupport hcase hliteral

/-- Canonical clauses distinguish distinct generated cases for one support. -/
theorem canonicalClause_injective_of_mem_allBoolCases
    (support : List NormalForm.BoolVar) {left right : NormalForm.BoolCase}
    (hsupport : support.Nodup)
    (hleft : left ∈ NormalForm.allBoolCases support)
    (hright : right ∈ NormalForm.allBoolCases support)
    (heq : Clause.canonical { literals := left }
      = Clause.canonical { literals := right })
    : left = right := by
  apply
    NormalForm.CompleteNormalization.boolCase_eq_of_mem_allBoolCases_equivalent
      hsupport hleft hright
  intro varName value
  constructor
  · intro hmem
    have hleftSorted :
        (varName, value) ∈ Clause.sortLiterals left :=
      (sortLiterals_perm left).mem_iff.mpr hmem
    have hrightSorted :
        (varName, value) ∈ Clause.sortLiterals right := by
      have hliterals := congrArg Clause.literals heq
      change Clause.sortLiterals left = Clause.sortLiterals right at hliterals
      rw [← hliterals]
      exact hleftSorted
    exact (sortLiterals_perm right).mem_iff.mp hrightSorted
  · intro hmem
    have hrightSorted :
        (varName, value) ∈ Clause.sortLiterals right :=
      (sortLiterals_perm right).mem_iff.mpr hmem
    have hleftSorted :
        (varName, value) ∈ Clause.sortLiterals left := by
      have hliterals := congrArg Clause.literals heq
      change Clause.sortLiterals left = Clause.sortLiterals right at hliterals
      rw [hliterals]
      exact hrightSorted
    exact (sortLiterals_perm left).mem_iff.mp hleftSorted

/-- Distinct generated cases cannot produce equal canonical clauses. -/
theorem canonicalClause_ne_of_distinct_allBoolCases
    (support : List NormalForm.BoolVar) {left right : NormalForm.BoolCase}
    (hsupport : support.Nodup)
    (hleft : left ∈ NormalForm.allBoolCases support)
    (hright : right ∈ NormalForm.allBoolCases support)
    (hne : left ≠ right)
    : Clause.canonical { literals := left }
      ≠ Clause.canonical { literals := right } := by
  intro heq
  exact hne
    (canonicalClause_injective_of_mem_allBoolCases support
      hsupport hleft hright heq)

/-- Any successful clause decode returns the canonical input as a valid minterm. -/
theorem clauseFromCompleteStem_ok
    (support : List NormalForm.BoolVar) (literals : List BoolLiteral)
    {clause : Clause}
    (hok : clauseFromCompleteStem support literals = .ok clause)
    : clause = Clause.canonical { literals := literals }
      ∧ clause.Valid support
      ∧ clause.CompleteMinterm support := by
  unfold clauseFromCompleteStem at hok
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  simp only at hok
  split at hok <;> try contradiction
  rename_i hcomplete
  simp only [Except.ok.injEq] at hok
  subst clause
  constructor
  · rfl
  · constructor
    · unfold Clause.Valid
      unfold Clause.completeMintermBool at hcomplete
      simp only [Bool.and_eq_true] at hcomplete
      exact hcomplete.1.2
    · exact hcomplete

/-- A successfully decoded generated case activates the returned clause. -/
theorem clauseFromCompleteStem_ok_holdsIn
    (support : List NormalForm.BoolVar) {boolCase : NormalForm.BoolCase}
    {clause : Clause}
    (hsupport : support.Nodup)
    (hcase : boolCase ∈ NormalForm.allBoolCases support)
    (hok : clauseFromCompleteStem support boolCase = .ok clause)
    : clause.HoldsIn boolCase := by
  have hdecoded := clauseFromCompleteStem_ok support boolCase hok
  rw [hdecoded.1]
  exact canonicalClause_holdsIn_of_mem_allBoolCases support hsupport hcase

end ResponseShape

end GraphQL
