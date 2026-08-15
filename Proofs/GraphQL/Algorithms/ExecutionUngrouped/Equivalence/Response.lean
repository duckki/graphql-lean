import Proofs.GraphQL.Algorithms.ExecutionUngrouped.Equivalence.Collection.StateInvariant

namespace GraphQL

namespace Algorithms
namespace ExecutionUngroupedUncached
namespace Eager

open GraphQL.Execution

theorem lookupResponseField?_mergeResponseField_same
    (responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : lookupResponseField? responseName (mergeResponseField responseName incoming fields)
      = some
          (match lookupResponseField? responseName fields with
            | some existing => mergeResponse existing incoming
            | none => incoming) := by
  induction fields with
  | nil =>
      simp [lookupResponseField?, mergeResponseField]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName existing =>
          by_cases h : fieldResponseName == responseName
          · simp [lookupResponseField?, mergeResponseField, h]
          · simp [lookupResponseField?, mergeResponseField, h, ih]

theorem lookupResponseField?_mergeResponseField_other
    (target responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : target ≠ responseName
      -> lookupResponseField? target (mergeResponseField responseName incoming fields)
          = lookupResponseField? target fields := by
  intro htarget
  induction fields with
  | nil =>
      have hbeq : (responseName == target) = false := by
        simp [beq_eq_false_iff_ne, htarget.symm]
      simp [lookupResponseField?, mergeResponseField, hbeq]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName existing =>
          by_cases hmerge : fieldResponseName == responseName
          · have htargetFalse : (fieldResponseName == target) = false := by
              have hfield : fieldResponseName = responseName :=
                beq_iff_eq.mp hmerge
              simp [beq_eq_false_iff_ne, hfield, htarget.symm]
            simp [lookupResponseField?, mergeResponseField, hmerge,
              htargetFalse]
          · by_cases hfieldTarget : fieldResponseName == target
            · simp [lookupResponseField?, mergeResponseField, hmerge,
                hfieldTarget]
            · simp [lookupResponseField?, mergeResponseField, hmerge,
                hfieldTarget, ih]

theorem lookupResponseField?_some_mem
    (responseName : Name) (response : ResponseValue)
    (fields : List (Name × ResponseValue))
    : lookupResponseField? responseName fields = some response
      -> (responseName, response) ∈ fields := by
  induction fields with
  | nil =>
      simp [lookupResponseField?]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName fieldResponse =>
          by_cases h : fieldResponseName == responseName
          · intro hlookup
            simp [lookupResponseField?, h] at hlookup
            rw [← hlookup]
            simp [beq_iff_eq.mp h]
          · intro hlookup
            simp [lookupResponseField?, h] at hlookup
            simpa using Or.inr (ih hlookup)

theorem lookupResponseField?_some_of_mem
    (responseName : Name) (fields : List (Name × ResponseValue))
    : responseName ∈ fields.map Prod.fst
      -> ∃ response, lookupResponseField? responseName fields = some response := by
  induction fields with
  | nil =>
      intro hmem
      simp at hmem
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, fieldResponse⟩
      intro hmem
      by_cases h : fieldResponseName == responseName
      · exact ⟨fieldResponse, by simp [lookupResponseField?, h]⟩
      · have hne : fieldResponseName ≠ responseName := by
          intro heq
          simp [heq] at h
        simp only [List.map_cons, List.mem_cons] at hmem
        rcases hmem with hhead | hrest
        · exact False.elim (hne hhead.symm)
        · rcases ih hrest with ⟨response, hlookup⟩
          exact ⟨response, by simp [lookupResponseField?, h, hlookup]⟩

theorem lookupResponseField?_append_of_some_left
    (responseName : Name) (fields suffix : List (Name × ResponseValue))
    (response : ResponseValue)
    : lookupResponseField? responseName fields = some response
      -> lookupResponseField? responseName (fields ++ suffix) = some response := by
  intro hlookup
  induction fields with
  | nil =>
      simp [lookupResponseField?] at hlookup
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, fieldResponse⟩
      by_cases h : fieldResponseName == responseName
      · simp [lookupResponseField?, h] at hlookup ⊢
        exact hlookup
      · simp [lookupResponseField?, h] at hlookup ⊢
        exact ih hlookup

theorem responseObjectField?_object_append_of_some_left
    (responseName : Name) (fields suffix : List (Name × ResponseValue))
    (response : ResponseValue)
    : responseObjectField? responseName (.object fields) = some response
      -> responseObjectField? responseName (.object (fields ++ suffix))
          = some response := by
  intro hlookup
  simpa [responseObjectField?] using
    lookupResponseField?_append_of_some_left responseName fields suffix
      response (by simpa [responseObjectField?] using hlookup)

theorem lookupResponseField?_none_of_not_mem
    (responseName : Name) (fields : List (Name × ResponseValue))
    : responseName ∉ fields.map Prod.fst
      -> lookupResponseField? responseName fields = none := by
  intro hnot
  induction fields with
  | nil =>
      simp [lookupResponseField?]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName fieldResponse =>
          have hrestNot : responseName ∉ rest.map Prod.fst := by
            intro hmem
            exact hnot (by simp [hmem])
          by_cases h : fieldResponseName == responseName
          · exact False.elim (hnot (by simp [beq_iff_eq.mp h]))
          · simp [lookupResponseField?, h, ih hrestNot]

theorem responseObjectField?_none_of_not_mem
    (responseName : Name) (fields : List (Name × ResponseValue))
    : responseName ∉ fields.map Prod.fst
      -> responseObjectField? responseName (.object fields) = none := by
  intro hnot
  simpa [responseObjectField?] using
    lookupResponseField?_none_of_not_mem responseName fields hnot

theorem responseObjectField?_mergeResponseFieldIntoObject_same (responseName : Name)
    (incoming : ResponseValue) (fields : List (Name × ResponseValue))
    : responseObjectField? responseName
        (mergeResponseFieldIntoObject responseName incoming (.object fields))
      = some
          (match responseObjectField? responseName (.object fields) with
            | some existing => mergeResponse existing incoming
            | none => incoming) := by
  simp [responseObjectField?, mergeResponseFieldIntoObject,
    lookupResponseField?_mergeResponseField_same]

theorem responseObjectField?_mergeResponseFieldIntoObject_other
    (target responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : target ≠ responseName
      -> responseObjectField? target
            (mergeResponseFieldIntoObject responseName incoming (.object fields))
          = responseObjectField? target (.object fields) := by
  intro htarget
  simp [responseObjectField?, mergeResponseFieldIntoObject,
    lookupResponseField?_mergeResponseField_other target responseName incoming
      fields htarget]

theorem mergeResponseFieldIntoObject_empty
    (responseName : Name) (response : ResponseValue)
    : mergeResponseFieldIntoObject responseName response (.object [])
      = .object [(responseName, response)] := by
  simp [mergeResponseFieldIntoObject, mergeResponseField]

theorem mergeResponseField_of_not_mem
    (responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : responseName ∉ fields.map Prod.fst
      -> mergeResponseField responseName incoming fields
          = fields ++ [(responseName, incoming)] := by
  intro hnot
  induction fields with
  | nil =>
      simp [mergeResponseField]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName existing =>
          have hrestNot : responseName ∉ rest.map Prod.fst := by
            intro hmem
            exact hnot (by simp [hmem])
          have hne : ¬ fieldResponseName = responseName := by
            intro heq
            exact hnot (by simp [heq])
          simp [mergeResponseField, hne, ih hrestNot]

theorem mergeResponseField_append_of_mem_left
    (responseName : Name) (incoming : ResponseValue)
    (fields suffix : List (Name × ResponseValue))
    : responseName ∈ fields.map Prod.fst
      -> mergeResponseField responseName incoming (fields ++ suffix)
          = mergeResponseField responseName incoming fields ++ suffix := by
  intro hmem
  induction fields with
  | nil =>
      simp at hmem
  | cons field rest ih =>
      rcases field with ⟨fieldResponseName, existing⟩
      by_cases h : fieldResponseName == responseName
      · simp [mergeResponseField, h]
      · have hrestMem : responseName ∈ rest.map Prod.fst := by
          have hne : fieldResponseName ≠ responseName := by
            intro heq
            simp [heq] at h
          simp at hmem
          rcases hmem with hhead | hrest
          · exact False.elim (hne hhead.symm)
          · rcases hrest with ⟨response, hpair⟩
            exact List.mem_map.mpr
              ⟨(responseName, response), hpair, rfl⟩
        simp [mergeResponseField, h, ih hrestMem]

theorem mergeResponseFields_append_of_disjoint
    (existing incoming : List (Name × ResponseValue))
    : PairKeysNodup incoming
      -> (∀ responseName,
            responseName ∈ incoming.map Prod.fst -> responseName ∉ existing.map Prod.fst)
      -> mergeResponseFields existing incoming = existing ++ incoming := by
  intro hnodup hdisjoint
  induction incoming generalizing existing with
  | nil =>
      simp [mergeResponseFields]
  | cons field rest ih =>
      cases field with
      | mk responseName response =>
          have hresponseNotExisting :
              responseName ∉ existing.map Prod.fst := by
            exact hdisjoint responseName (by simp)
          have hrestNodup : PairKeysNodup rest := by
            unfold PairKeysNodup at hnodup ⊢
            exact hnodup.tail
          have hresponseNotRest : responseName ∉ rest.map Prod.fst := by
            unfold PairKeysNodup at hnodup
            exact (List.nodup_cons.mp hnodup).1
          have hrestDisjoint :
              ∀ restName, restName ∈ rest.map Prod.fst ->
                restName ∉ (existing ++ [(responseName, response)]).map Prod.fst := by
            intro restName hrestMem
            simp only [List.map_append, List.map_cons, List.map_nil,
              List.mem_append, List.mem_singleton]
            intro hmem
            rcases hmem with hmemExisting | heq
            · exact hdisjoint restName (by simp [hrestMem]) hmemExisting
            · exact hresponseNotRest (by simpa [heq] using hrestMem)
          simp [mergeResponseFields,
            mergeResponseField_of_not_mem responseName response existing
              hresponseNotExisting]
          rw [ih (existing ++ [(responseName, response)]) hrestNodup
            hrestDisjoint]
          simp [List.append_assoc]

theorem PairKeysNodup_append_of_disjoint {α : Type} (left right : List (Name × α))
    : PairKeysNodup left
      -> PairKeysNodup right
      -> (∀ responseName,
            responseName ∈ right.map Prod.fst -> responseName ∉ left.map Prod.fst)
      -> PairKeysNodup (left ++ right) := by
  intro hleft hright hdisjoint
  induction left with
  | nil =>
      simpa [PairKeysNodup]
  | cons field rest ih =>
      rcases field with ⟨responseName, response⟩
      have hparts := List.nodup_cons.mp hleft
      have hrest : PairKeysNodup rest := hparts.2
      have hresponseNotRest : responseName ∉ rest.map Prod.fst := hparts.1
      have hresponseNotRight : responseName ∉ right.map Prod.fst := by
        intro hmem
        exact hdisjoint responseName hmem (by simp)
      have hrestDisjoint :
          ∀ rightName, rightName ∈ right.map Prod.fst ->
            rightName ∉ rest.map Prod.fst := by
        intro rightName hrightMem hrestMem
        exact hdisjoint rightName hrightMem (by simp [hrestMem])
      unfold PairKeysNodup at hleft hright hrest ⊢
      simp only [List.map_append, List.map_cons]
      apply List.nodup_cons.mpr
      constructor
      · intro hmem
        rcases List.mem_append.mp hmem with hrestMem | hrightMem
        · exact hresponseNotRest hrestMem
        · exact hresponseNotRight hrightMem
      · simpa [PairKeysNodup, List.map_append] using
          ih hparts.2 hrestDisjoint

theorem mergeResponse_object_append_of_disjoint
    (existing incoming : List (Name × ResponseValue))
    : PairKeysNodup incoming
      -> (∀ responseName,
            responseName ∈ incoming.map Prod.fst -> responseName ∉ existing.map Prod.fst)
      -> mergeResponse (.object existing) (.object incoming)
          = .object (existing ++ incoming) := by
  intro hnodup hdisjoint
  simp [mergeResponse,
    mergeResponseFields_append_of_disjoint existing incoming hnodup hdisjoint]

theorem mergeResponse_object_assoc_of_disjoint
    (left middle right : List (Name × ResponseValue))
    : PairKeysNodup middle
      -> PairKeysNodup right
      -> (∀ responseName,
            responseName ∈ middle.map Prod.fst -> responseName ∉ left.map Prod.fst)
      -> (∀ responseName,
            responseName ∈ right.map Prod.fst -> responseName ∉ middle.map Prod.fst)
      -> (∀ responseName,
            responseName ∈ right.map Prod.fst -> responseName ∉ left.map Prod.fst)
      -> mergeResponse (mergeResponse (.object left) (.object middle)) (.object right)
          = mergeResponse (.object left)
              (mergeResponse (.object middle) (.object right)) := by
  intro hmiddle hright hmiddleLeft hrightMiddle hrightLeft
  have hrightLeftMiddle :
      ∀ responseName, responseName ∈ right.map Prod.fst ->
        responseName ∉ (left ++ middle).map Prod.fst := by
    intro responseName hrightMem
    simp only [List.map_append, List.mem_append]
    intro hmem
    rcases hmem with hleft | hmiddleMem
    · exact hrightLeft responseName hrightMem hleft
    · exact hrightMiddle responseName hrightMem hmiddleMem
  have hmiddleRight :
      PairKeysNodup (middle ++ right) :=
    PairKeysNodup_append_of_disjoint middle right hmiddle hright
      hrightMiddle
  have hmiddleRightLeft :
      ∀ responseName, responseName ∈ (middle ++ right).map Prod.fst ->
        responseName ∉ left.map Prod.fst := by
    intro responseName hmem
    simp only [List.map_append, List.mem_append] at hmem
    rcases hmem with hmiddleMem | hrightMem
    · exact hmiddleLeft responseName hmiddleMem
    · exact hrightLeft responseName hrightMem
  rw [mergeResponse_object_append_of_disjoint left middle hmiddle
    hmiddleLeft]
  rw [mergeResponse_object_append_of_disjoint (left ++ middle) right hright
    hrightLeftMiddle]
  rw [mergeResponse_object_append_of_disjoint middle right hright
    hrightMiddle]
  rw [mergeResponse_object_append_of_disjoint left (middle ++ right)
    hmiddleRight hmiddleRightLeft]
  simp [List.append_assoc]

theorem mergeResponseFields_nil_left_of_pairKeysNodup
    (fields : List (Name × ResponseValue))
    : PairKeysNodup fields -> mergeResponseFields [] fields = fields := by
  intro hnodup
  simpa using
    mergeResponseFields_append_of_disjoint [] fields hnodup
      (by intro responseName hmem; simp)

theorem mergeResponse_empty_object_left_of_pairKeysNodup
    (fields : List (Name × ResponseValue))
    : PairKeysNodup fields
      -> mergeResponse (.object []) (.object fields) = .object fields := by
  intro hnodup
  simp [mergeResponse, mergeResponseFields_nil_left_of_pairKeysNodup fields hnodup]

theorem mergeResponse_empty_object_right (response : ResponseValue)
    : mergeResponse response (.object []) = response := by
  cases response <;> simp [mergeResponse, mergeResponseFields]

theorem ResponseAbsorbs_empty_object_left (fields : List (Name × ResponseValue))
    : PairKeysNodup fields -> ResponseAbsorbs (.object []) (.object fields) := by
  intro hnodup
  exact mergeResponse_empty_object_left_of_pairKeysNodup fields hnodup

theorem ResponseAbsorbs_object_iff (base output : List (Name × ResponseValue))
    : ResponseAbsorbs (.object base) (.object output)
      ↔ mergeResponseFields base output = output := by
  simp [ResponseAbsorbs, mergeResponse]

theorem ResponseAbsorbs_list_iff (base output : List ResponseValue)
    : ResponseAbsorbs (.list base) (.list output)
      ↔ mergeResponseLists base output = output := by
  simp [ResponseAbsorbs, mergeResponse]

theorem ResponseMergeReady_object (fields : List (Name × ResponseValue))
    : PairKeysNodup fields
      -> (∀ responseName response,
            (responseName, response) ∈ fields -> ResponseMergeReady response)
      -> ResponseMergeReady (.object fields) := by
  intro hnodup hfields
  exact ResponseMergeReady.object fields hnodup hfields

theorem ResponseMergeReady_object_pairKeysNodup (fields : List (Name × ResponseValue))
    : ResponseMergeReady (.object fields) -> PairKeysNodup fields := by
  intro hready
  cases hready with
  | object _ hnodup _ => exact hnodup

theorem ResponseMergeReady_object_field
    (fields : List (Name × ResponseValue))
    (responseName : Name) (response : ResponseValue)
    : ResponseMergeReady (.object fields)
      -> (responseName, response) ∈ fields
      -> ResponseMergeReady response := by
  intro hready hmem
  cases hready with
  | object _ _ hfields => exact hfields responseName response hmem

theorem ResponseMergeReady_object_append (left right : List (Name × ResponseValue))
    : ResponseMergeReady (.object left)
      -> ResponseMergeReady (.object right)
      -> (∀ responseName,
            responseName ∈ right.map Prod.fst -> responseName ∉ left.map Prod.fst)
      -> ResponseMergeReady (.object (left ++ right)) := by
  intro hleft hright hdisjoint
  apply ResponseMergeReady.object
  · exact PairKeysNodup_append_of_disjoint left right
      (ResponseMergeReady_object_pairKeysNodup left hleft)
      (ResponseMergeReady_object_pairKeysNodup right hright)
      hdisjoint
  · intro responseName response hmem
    rcases List.mem_append.mp hmem with hleftMem | hrightMem
    · exact ResponseMergeReady_object_field left responseName response hleft
        hleftMem
    · exact ResponseMergeReady_object_field right responseName response hright
        hrightMem

theorem responseObjectField?_some_ready
    (responseName : Name) (response : ResponseValue)
    (fields : List (Name × ResponseValue))
    : ResponseMergeReady (.object fields)
      -> responseObjectField? responseName (.object fields) = some response
      -> ResponseMergeReady response := by
  intro hready hlookup
  exact ResponseMergeReady_object_field fields responseName response hready
    (lookupResponseField?_some_mem responseName response fields hlookup)

theorem ResponseMergeReady_list (values : List ResponseValue)
    : (∀ response, response ∈ values -> ResponseMergeReady response)
      -> ResponseMergeReady (.list values) := by
  intro hvalues
  exact ResponseMergeReady.list values hvalues

theorem ResponseMergeReady_list_value
    (values : List ResponseValue) (response : ResponseValue)
    : ResponseMergeReady (.list values)
      -> response ∈ values
      -> ResponseMergeReady response := by
  intro hready hmem
  cases hready with
  | list _ hvalues => exact hvalues response hmem

theorem ResponseMergeReady_empty_object : ResponseMergeReady (.object []) :=
  ResponseMergeReady.object [] (by simp [PairKeysNodup])
    (by intro responseName response hmem; simp at hmem)

theorem ResponseMergeReady_empty_list : ResponseMergeReady (.list []) :=
  ResponseMergeReady.list [] (by intro response hmem; simp at hmem)

theorem ResponseMergeReady_scalar_response_list (values : List String)
    : ResponseMergeReady
        (.list (values.map (fun value => (.scalar value : ResponseValue)))) := by
  apply ResponseMergeReady.list
  intro response hmem
  rcases List.mem_map.mp hmem with ⟨value, _hvalue, hresponse⟩
  rw [← hresponse]
  exact ResponseMergeReady.scalar value

theorem ResponseMergeReady_outOfFuel
    : ResponseMergeReady (Result.getD .null (outOfFuel : Result ResponseValue)) := by
  simp [outOfFuel, Result.getD]
  exact ResponseMergeReady.null

theorem mergeResponseField_key_mem
    (responseName key : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : key ∈ (mergeResponseField responseName incoming fields).map Prod.fst
      -> key = responseName ∨ key ∈ fields.map Prod.fst := by
  induction fields with
  | nil =>
      simp [mergeResponseField]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName existing =>
          by_cases h : fieldResponseName == responseName
          · intro hmem
            simp [mergeResponseField, h] at hmem
            rcases hmem with hhead | hrest
            · exact Or.inr (by simp [hhead])
            · exact Or.inr (by simp [hrest])
          · intro hmem
            simp [mergeResponseField, h] at hmem
            rcases hmem with hhead | htail
            · exact Or.inr (by simp [hhead])
            · rcases ih (by simpa [List.mem_map] using htail) with hkey | hrest
              · exact Or.inl hkey
              · exact Or.inr (by simp [hrest])

theorem mergeResponseField_pairKeysNodup
    (responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : PairKeysNodup fields
      -> PairKeysNodup (mergeResponseField responseName incoming fields) := by
  intro hnodup
  induction fields with
  | nil =>
      simp [PairKeysNodup, mergeResponseField]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName existing =>
          by_cases h : fieldResponseName == responseName
          · simpa [PairKeysNodup, mergeResponseField, h] using hnodup
          · unfold PairKeysNodup at hnodup ⊢
            simp only [mergeResponseField, h]
            apply List.nodup_cons.mpr
            constructor
            · intro hmem
              rcases
                mergeResponseField_key_mem responseName fieldResponseName
                  incoming rest hmem
                with heq | hrest
              · have hne : fieldResponseName ≠ responseName := by
                  intro heq'
                  simp [heq'] at h
                exact hne heq
              · exact (List.nodup_cons.mp hnodup).1 hrest
            · exact ih (by
                unfold PairKeysNodup
                exact (List.nodup_cons.mp hnodup).2)

theorem mergeResponseFields_pairKeysNodup
    (existing incoming : List (Name × ResponseValue))
    : PairKeysNodup existing
      -> PairKeysNodup (mergeResponseFields existing incoming) := by
  intro hnodup
  induction incoming generalizing existing with
  | nil =>
      simpa [mergeResponseFields] using hnodup
  | cons field rest ih =>
      cases field with
      | mk responseName incomingResponse =>
          simp [mergeResponseFields]
          exact ih
            (mergeResponseField responseName incomingResponse existing)
            (mergeResponseField_pairKeysNodup responseName incomingResponse
              existing hnodup)

theorem mergeResponseFields_cons_left_of_not_mem
    (responseName : Name) (response : ResponseValue)
    (existing incoming : List (Name × ResponseValue))
    : responseName ∉ incoming.map Prod.fst
      -> mergeResponseFields ((responseName, response) :: existing) incoming
          = (responseName, response) :: mergeResponseFields existing incoming := by
  intro hnot
  induction incoming generalizing existing with
  | nil =>
      simp [mergeResponseFields]
  | cons field rest ih =>
      cases field with
      | mk incomingName incomingResponse =>
          have hne : responseName ≠ incomingName := by
            intro heq
            exact hnot (by simp [heq])
          have hbeq : (responseName == incomingName) = false := by
            simp [beq_eq_false_iff_ne, hne]
          have hrestNot : responseName ∉ rest.map Prod.fst := by
            intro hmem
            exact hnot (by simp [hmem])
          simp [mergeResponseFields, mergeResponseField, hbeq,
            ih (mergeResponseField incomingName incomingResponse existing)
              hrestNot]

theorem mergeResponseField_field_ready
    (responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : ResponseMergeReady incoming
      -> (∀ fieldResponseName response,
            (fieldResponseName, response) ∈ fields -> ResponseMergeReady response)
      -> (∀ existing,
            (responseName, existing) ∈ fields
            -> ResponseMergeReady (mergeResponse existing incoming))
      -> ∀ fieldResponseName response,
          (fieldResponseName, response) ∈ mergeResponseField responseName incoming fields
          -> ResponseMergeReady response := by
  intro hincoming hfields hmerge
  induction fields with
  | nil =>
      intro fieldResponseName response hmem
      simp [mergeResponseField] at hmem
      rcases hmem with ⟨hname, hresponse⟩
      rw [hresponse]
      exact hincoming
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName existing =>
          by_cases h : fieldResponseName == responseName
          · intro candidateName response hmem
            simp [mergeResponseField, h] at hmem
            rcases hmem with hhead | htail
            · rcases hhead with ⟨_hname, hresponse⟩
              rw [hresponse]
              apply hmerge existing
              simp [beq_iff_eq.mp h]
            · exact hfields candidateName response (by simp [htail])
          · intro candidateName response hmem
            simp [mergeResponseField, h] at hmem
            rcases hmem with hhead | htail
            · exact hfields candidateName response (by simp [hhead])
            · apply ih
              · intro restName restResponse hrest
                exact hfields restName restResponse (by simp [hrest])
              · intro existing' hcollision
                exact hmerge existing' (by simp [hcollision])
              · exact htail

theorem mergeResponseField_object_ready
    (responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : ResponseMergeReady (.object fields)
      -> ResponseMergeReady incoming
      -> (∀ existing,
            (responseName, existing) ∈ fields
            -> ResponseMergeReady (mergeResponse existing incoming))
      -> ResponseMergeReady
          (.object (mergeResponseField responseName incoming fields)) := by
  intro hfieldsReady hincoming hmerge
  apply ResponseMergeReady.object
  · exact mergeResponseField_pairKeysNodup responseName incoming fields
      (ResponseMergeReady_object_pairKeysNodup fields hfieldsReady)
  · exact mergeResponseField_field_ready responseName incoming fields
      hincoming
      (by
        intro fieldResponseName response hmem
        exact ResponseMergeReady_object_field fields fieldResponseName response
          hfieldsReady hmem)
      hmerge

theorem mergeResponseFields_object_ready_of_steps
    (existing incoming : List (Name × ResponseValue))
    : ResponseMergeReady (.object existing)
      -> MergeResponseFieldsReadySteps existing incoming
      -> ResponseMergeReady (.object (mergeResponseFields existing incoming)) := by
  intro hexisting hsteps
  induction incoming generalizing existing with
  | nil =>
      simpa [mergeResponseFields] using hexisting
  | cons field rest ih =>
      cases field with
      | mk responseName incomingResponse =>
          simp [MergeResponseFieldsReadySteps] at hsteps
          rcases hsteps with ⟨hincoming, hcollision, hrest⟩
          simp [mergeResponseFields]
          exact ih (mergeResponseField responseName incomingResponse existing)
            (mergeResponseField_object_ready responseName incomingResponse
              existing hexisting hincoming hcollision)
            hrest

mutual
  theorem mergeResponse_self_of_ready
      : ∀ response : ResponseValue,
          ResponseMergeReady response -> mergeResponse response response = response
    | .null, _hready => by
        simp [mergeResponse]
    | .scalar value, _hready => by
        simp [mergeResponse]
    | .object fields, hready => by
        cases hready with
        | object _ hnodup hfields =>
            simp [mergeResponse]
            exact mergeResponseFields_self_of_ready fields hnodup hfields
    | .list values, hready => by
        cases hready with
        | list _ hvalues =>
            simp [mergeResponse]
            exact mergeResponseLists_self_of_ready values hvalues

  theorem mergeResponseFields_self_of_ready
      : ∀ fields : List (Name × ResponseValue),
          PairKeysNodup fields
          -> (∀ responseName response,
                (responseName, response) ∈ fields -> ResponseMergeReady response)
          -> mergeResponseFields fields fields = fields
    | [], _hnodup, _hfields => by
        simp [mergeResponseFields]
    | (responseName, response) :: rest, hnodup, hfields => by
        have hresponseReady :
            ResponseMergeReady response := by
          exact hfields responseName response (by simp)
        have hresponseSelf :
            mergeResponse response response = response :=
          mergeResponse_self_of_ready response hresponseReady
        have hrestNodup : PairKeysNodup rest := by
          unfold PairKeysNodup at hnodup ⊢
          exact (List.nodup_cons.mp hnodup).2
        have hresponseNameNotRest :
            responseName ∉ rest.map Prod.fst := by
          unfold PairKeysNodup at hnodup
          exact (List.nodup_cons.mp hnodup).1
        have hrestFields :
            ∀ restName restResponse,
              (restName, restResponse) ∈ rest ->
                ResponseMergeReady restResponse := by
          intro restName restResponse hmem
          exact hfields restName restResponse (by simp [hmem])
        have hrestSelf :
            mergeResponseFields rest rest = rest :=
          mergeResponseFields_self_of_ready rest hrestNodup hrestFields
        simp [mergeResponseFields, mergeResponseField, hresponseSelf,
          mergeResponseFields_cons_left_of_not_mem responseName response rest
            rest hresponseNameNotRest, hrestSelf]

  theorem mergeResponseLists_self_of_ready
      : ∀ values : List ResponseValue,
          (∀ response, response ∈ values -> ResponseMergeReady response)
          -> mergeResponseLists values values = values
    | [], _hvalues => by
        simp [mergeResponseLists]
    | response :: rest, hvalues => by
        have hresponseReady :
            ResponseMergeReady response := by
          exact hvalues response (by simp)
        have hresponseSelf :
            mergeResponse response response = response :=
          mergeResponse_self_of_ready response hresponseReady
        have hrestValues :
            ∀ restResponse, restResponse ∈ rest ->
              ResponseMergeReady restResponse := by
          intro restResponse hmem
          exact hvalues restResponse (by simp [hmem])
        have hrestSelf :
            mergeResponseLists rest rest = rest :=
          mergeResponseLists_self_of_ready rest hrestValues
        simp [mergeResponseLists, hresponseSelf, hrestSelf]
end

theorem ResponseAbsorbs_refl_of_ready (response : ResponseValue)
    : ResponseMergeReady response -> ResponseAbsorbs response response := by
  intro hready
  exact mergeResponse_self_of_ready response hready

theorem mergeResponseFields_cons_left_exists
    (responseName : Name) (response : ResponseValue)
    (fields incoming : List (Name × ResponseValue))
    : ∃ response' fields',
        mergeResponseFields ((responseName, response) :: fields) incoming
        = (responseName, response') :: fields' := by
  induction incoming generalizing response fields with
  | nil =>
      exact ⟨response, fields, by simp [mergeResponseFields]⟩
  | cons incomingField rest ih =>
      rcases incomingField with ⟨incomingName, incomingResponse⟩
      by_cases h : responseName == incomingName
      · obtain ⟨response', fields', hrest⟩ :=
          ih (mergeResponse response incomingResponse) fields
        exact ⟨
          response',
          fields',
          by simpa [mergeResponseFields, mergeResponseField, h] using hrest
        ⟩
      · obtain ⟨response', fields', hrest⟩ :=
          ih response (mergeResponseField incomingName incomingResponse fields)
        exact ⟨
          response',
          fields',
          by simpa [mergeResponseFields, mergeResponseField, h] using hrest
        ⟩

mutual
  inductive ResponseAbsorptionShape : ResponseValue -> ResponseValue -> Prop where
    | null : ResponseAbsorptionShape .null .null
    | toNull (base : ResponseValue) : ResponseAbsorptionShape base .null
    | scalar (value : String) : ResponseAbsorptionShape (.scalar value) (.scalar value)
    | object {base output : List (Name × ResponseValue)}
      : ResponseFieldsAbsorptionShape base output
        -> ResponseAbsorptionShape (.object base) (.object output)
    | list {base output : List ResponseValue}
      : ResponseListAbsorptionShape base output
        -> ResponseAbsorptionShape (.list base) (.list output)

  inductive ResponseFieldsAbsorptionShape
      : List (Name × ResponseValue) -> List (Name × ResponseValue) -> Prop where
    | nil (output : List (Name × ResponseValue))
      : ResponseMergeReady (.object output) -> ResponseFieldsAbsorptionShape [] output
    | cons (responseName : Name)
      {baseResponse outputResponse : ResponseValue}
      {baseRest outputRest : List (Name × ResponseValue)}
      : ResponseMergeReady (.object ((responseName, outputResponse) :: outputRest))
        -> ResponseAbsorptionShape baseResponse outputResponse
        -> ResponseFieldsAbsorptionShape baseRest outputRest
        -> ResponseFieldsAbsorptionShape
            ((responseName, baseResponse) :: baseRest)
            ((responseName, outputResponse) :: outputRest)

  inductive ResponseListAbsorptionShape
      : List ResponseValue -> List ResponseValue -> Prop where
    | nil : ResponseListAbsorptionShape [] []
    | cons {baseResponse outputResponse : ResponseValue}
      {baseRest outputRest : List ResponseValue}
      : ResponseMergeReady (.list (outputResponse :: outputRest))
        -> ResponseAbsorptionShape baseResponse outputResponse
        -> ResponseListAbsorptionShape baseRest outputRest
        -> ResponseListAbsorptionShape
            (baseResponse :: baseRest) (outputResponse :: outputRest)
end

mutual
  theorem ResponseAbsorptionShape.output_ready
      : ∀ {base output : ResponseValue},
          ResponseAbsorptionShape base output -> ResponseMergeReady output
    | .null, .null, ResponseAbsorptionShape.null =>
        ResponseMergeReady.null
    | _base, .null, ResponseAbsorptionShape.toNull _ =>
        ResponseMergeReady.null
    | .scalar value, .scalar _, ResponseAbsorptionShape.scalar _ =>
        ResponseMergeReady.scalar value
    | .object _base,
      .object _output,
      ResponseAbsorptionShape.object hfields =>
        ResponseFieldsAbsorptionShape.output_ready hfields
    | .list _base,
      .list _output,
      ResponseAbsorptionShape.list hvalues =>
        ResponseListAbsorptionShape.output_ready hvalues

  theorem ResponseFieldsAbsorptionShape.output_ready
      : ∀ {base output : List (Name × ResponseValue)},
          ResponseFieldsAbsorptionShape base output -> ResponseMergeReady (.object output)
    | _base, _output, hshape => by
        cases hshape with
        | nil _ hready => exact hready
        | cons _ hready _ _ => exact hready

  theorem ResponseListAbsorptionShape.output_ready
      : ∀ {base output : List ResponseValue},
          ResponseListAbsorptionShape base output -> ResponseMergeReady (.list output)
    | [], [], ResponseListAbsorptionShape.nil =>
        ResponseMergeReady_empty_list
    | _baseResponse :: _baseRest,
      _outputResponse :: _outputRest,
      ResponseListAbsorptionShape.cons hready _ _ =>
        hready
end

mutual
  theorem ResponseAbsorptionShape.trans
      {base middle output : ResponseValue}
      (hbaseMiddle : ResponseAbsorptionShape base middle)
      (hmiddleOutput : ResponseAbsorptionShape middle output)
      : ResponseAbsorptionShape base output := by
    cases hmiddleOutput with
    | null =>
        exact ResponseAbsorptionShape.toNull base
    | toNull _middle =>
        exact ResponseAbsorptionShape.toNull base
    | scalar _value =>
        exact hbaseMiddle
    | object hmiddleOutput =>
        cases hbaseMiddle with
        | object hbaseMiddle =>
            exact ResponseAbsorptionShape.object
              (ResponseFieldsAbsorptionShape.trans hbaseMiddle hmiddleOutput)
    | list hmiddleOutput =>
        cases hbaseMiddle with
        | list hbaseMiddle =>
            exact ResponseAbsorptionShape.list
              (ResponseListAbsorptionShape.trans hbaseMiddle hmiddleOutput)

  theorem ResponseFieldsAbsorptionShape.trans
      : ∀ {base middle output : List (Name × ResponseValue)},
          ResponseFieldsAbsorptionShape base middle
          -> ResponseFieldsAbsorptionShape middle output
          -> ResponseFieldsAbsorptionShape base output
    | _base, _middle, _output, hbaseMiddle, hmiddleOutput => by
        cases hbaseMiddle with
        | nil _ _ =>
            exact ResponseFieldsAbsorptionShape.nil _
              hmiddleOutput.output_ready
        | cons responseName _ hbaseMiddleResponse hbaseMiddleRest =>
            cases hmiddleOutput with
            | cons _ houtputReady hmiddleOutputResponse hmiddleOutputRest =>
                exact
                  ResponseFieldsAbsorptionShape.cons responseName houtputReady
                    (ResponseAbsorptionShape.trans hbaseMiddleResponse
                      hmiddleOutputResponse)
                    (ResponseFieldsAbsorptionShape.trans hbaseMiddleRest
                      hmiddleOutputRest)

  theorem ResponseListAbsorptionShape.trans
      : ∀ {base middle output : List ResponseValue},
          ResponseListAbsorptionShape base middle
          -> ResponseListAbsorptionShape middle output
          -> ResponseListAbsorptionShape base output
    | [],
      [],
      [],
      ResponseListAbsorptionShape.nil,
      ResponseListAbsorptionShape.nil =>
        ResponseListAbsorptionShape.nil
    | _baseResponse :: _baseRest,
      _middleResponse :: _middleRest,
      _outputResponse :: _outputRest,
      ResponseListAbsorptionShape.cons _ hbaseMiddleResponse hbaseMiddleRest,
      ResponseListAbsorptionShape.cons houtputReady hmiddleOutputResponse
        hmiddleOutputRest =>
        ResponseListAbsorptionShape.cons houtputReady
          (ResponseAbsorptionShape.trans hbaseMiddleResponse hmiddleOutputResponse)
          (ResponseListAbsorptionShape.trans hbaseMiddleRest hmiddleOutputRest)
end

mutual
  theorem ResponseAbsorptionShape.to_absorbs
      : ∀ {base output : ResponseValue},
          ResponseAbsorptionShape base output -> ResponseAbsorbs base output
    | .null, .null, ResponseAbsorptionShape.null => by
        simp [ResponseAbsorbs, mergeResponse]
    | base, .null, ResponseAbsorptionShape.toNull _ => by
        cases base <;> simp [ResponseAbsorbs, mergeResponse]
    | .scalar _value, .scalar _,
        ResponseAbsorptionShape.scalar _ => by
        simp [ResponseAbsorbs, mergeResponse]
    | .object _base, .object _output,
        ResponseAbsorptionShape.object hfields => by
        simp [ResponseAbsorbs, mergeResponse]
        exact ResponseFieldsAbsorptionShape.to_merge hfields
    | .list _base, .list _output,
        ResponseAbsorptionShape.list hvalues => by
        simp [ResponseAbsorbs, mergeResponse]
        exact ResponseListAbsorptionShape.to_merge hvalues

  theorem ResponseFieldsAbsorptionShape.to_merge
      : ∀ {base output : List (Name × ResponseValue)},
          ResponseFieldsAbsorptionShape base output
          -> mergeResponseFields base output = output
    | _base, output, hshape => by
      cases hshape with
      | nil _ houtputReady =>
        exact mergeResponseFields_nil_left_of_pairKeysNodup output
          (ResponseMergeReady_object_pairKeysNodup output houtputReady)
      | cons responseName houtputReady hresponse hrest =>
        rename_i baseResponse outputResponse baseRest outputRest
        have hresponseAbsorbs :
            mergeResponse baseResponse outputResponse = outputResponse := by
          simpa [ResponseAbsorbs] using
            ResponseAbsorptionShape.to_absorbs hresponse
        have hrestMerge :
            mergeResponseFields baseRest outputRest = outputRest :=
          ResponseFieldsAbsorptionShape.to_merge hrest
        have hresponseNameNotRest :
            responseName ∉ outputRest.map Prod.fst :=
          PairKeysNodup.head_not_mem_tail
            (ResponseMergeReady_object_pairKeysNodup
              ((responseName, outputResponse) :: outputRest) houtputReady)
        simp [mergeResponseFields, mergeResponseField, hresponseAbsorbs]
        rw [mergeResponseFields_cons_left_of_not_mem responseName
          outputResponse baseRest outputRest hresponseNameNotRest]
        simp [hrestMerge]

  theorem ResponseListAbsorptionShape.to_merge
      : ∀ {base output : List ResponseValue},
          ResponseListAbsorptionShape base output
          -> mergeResponseLists base output = output
    | [], [], ResponseListAbsorptionShape.nil => by
        simp [mergeResponseLists]
    | baseResponse :: baseRest, outputResponse :: outputRest,
        ResponseListAbsorptionShape.cons _houtputReady hresponse hrest => by
        have hresponseAbsorbs :
            mergeResponse baseResponse outputResponse = outputResponse := by
          simpa [ResponseAbsorbs] using
            ResponseAbsorptionShape.to_absorbs hresponse
        have hrestMerge :
            mergeResponseLists baseRest outputRest = outputRest :=
          ResponseListAbsorptionShape.to_merge hrest
        simp [mergeResponseLists, hresponseAbsorbs, hrestMerge]
end

mutual
  theorem ResponseAbsorptionShape.of_absorbs
      : ∀ (base output : ResponseValue),
          ResponseMergeReady base
          -> ResponseMergeReady output
          -> ResponseAbsorbs base output
          -> ResponseAbsorptionShape base output
    | .null, .null, _hbaseReady, _houtputReady, _habsorbs =>
        ResponseAbsorptionShape.null
    | .null, .scalar _value, _hbaseReady, _houtputReady, habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .null, .object _fields, _hbaseReady, _houtputReady, habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .null, .list _values, _hbaseReady, _houtputReady, habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .scalar _baseValue, .null, _hbaseReady, _houtputReady, _habsorbs =>
        ResponseAbsorptionShape.toNull _
    | .scalar baseValue, .scalar outputValue, _hbaseReady, _houtputReady,
        habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
        subst outputValue
        exact ResponseAbsorptionShape.scalar baseValue
    | .scalar _baseValue, .object _fields, _hbaseReady, _houtputReady,
        habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .scalar _baseValue, .list _values, _hbaseReady, _houtputReady,
        habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .object _baseFields, .null, _hbaseReady, _houtputReady, _habsorbs =>
        ResponseAbsorptionShape.toNull _
    | .object _baseFields, .scalar _value, _hbaseReady, _houtputReady,
        habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .object baseFields, .object outputFields, hbaseReady, houtputReady,
        habsorbs =>
        ResponseAbsorptionShape.object
          (ResponseFieldsAbsorptionShape.of_merge baseFields outputFields
            hbaseReady houtputReady (by
              simpa [ResponseAbsorbs, mergeResponse] using habsorbs))
    | .object _baseFields, .list _values, _hbaseReady, _houtputReady,
        habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .list _baseValues, .null, _hbaseReady, _houtputReady, _habsorbs =>
        ResponseAbsorptionShape.toNull _
    | .list _baseValues, .scalar _value, _hbaseReady, _houtputReady,
        habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .list _baseValues, .object _fields, _hbaseReady, _houtputReady,
        habsorbs => by
        simp [ResponseAbsorbs, mergeResponse] at habsorbs
    | .list baseValues, .list outputValues, hbaseReady, houtputReady,
        habsorbs =>
        ResponseAbsorptionShape.list
          (ResponseListAbsorptionShape.of_merge baseValues outputValues
            hbaseReady houtputReady (by
              simpa [ResponseAbsorbs, mergeResponse] using habsorbs))

  theorem ResponseFieldsAbsorptionShape.of_merge
      : ∀ (base output : List (Name × ResponseValue)),
          ResponseMergeReady (.object base)
          -> ResponseMergeReady (.object output)
          -> mergeResponseFields base output = output
          -> ResponseFieldsAbsorptionShape base output
    | [], output, _hbaseReady, houtputReady, _hmerge =>
        ResponseFieldsAbsorptionShape.nil output houtputReady
    | (responseName, baseResponse) :: baseRest, [], _hbaseReady,
        _houtputReady, hmerge => by
        simp [mergeResponseFields] at hmerge
    | (responseName, baseResponse) :: baseRest,
        (outputName, outputResponse) :: outputRest, hbaseReady, houtputReady,
        hmerge => by
        obtain ⟨headResponse, restFields, hhead⟩ :=
          mergeResponseFields_cons_left_exists responseName baseResponse
            baseRest ((outputName, outputResponse) :: outputRest)
        rw [hmerge] at hhead
        injection hhead with houtputName houtputTail
        cases houtputName
        have hbaseResponseReady :
            ResponseMergeReady baseResponse :=
          ResponseMergeReady_object_field
            ((responseName, baseResponse) :: baseRest) responseName
            baseResponse hbaseReady (by simp)
        have hbaseRestReady :
            ResponseMergeReady (.object baseRest) := by
          apply ResponseMergeReady.object
          · exact (ResponseMergeReady_object_pairKeysNodup
              ((responseName, baseResponse) :: baseRest) hbaseReady).tail
          · intro restName restResponse hmem
            exact ResponseMergeReady_object_field
              ((responseName, baseResponse) :: baseRest) restName restResponse
              hbaseReady (by simp [hmem])
        have houtputResponseReady :
            ResponseMergeReady outputResponse :=
          ResponseMergeReady_object_field
            ((responseName, outputResponse) :: outputRest) responseName
            outputResponse houtputReady (by simp)
        have houtputRestReady :
            ResponseMergeReady (.object outputRest) := by
          apply ResponseMergeReady.object
          · exact (ResponseMergeReady_object_pairKeysNodup
              ((responseName, outputResponse) :: outputRest) houtputReady).tail
          · intro restName restResponse hmem
            exact ResponseMergeReady_object_field
              ((responseName, outputResponse) :: outputRest) restName
              restResponse houtputReady (by simp [hmem])
        have hresponseNameNotRest :
            responseName ∉ outputRest.map Prod.fst :=
          PairKeysNodup.head_not_mem_tail
            (ResponseMergeReady_object_pairKeysNodup
              ((responseName, outputResponse) :: outputRest) houtputReady)
        have hmerge' :
            (responseName, mergeResponse baseResponse outputResponse) ::
              mergeResponseFields baseRest outputRest =
            (responseName, outputResponse) :: outputRest := by
          have hformula :
              mergeResponseFields ((responseName, baseResponse) :: baseRest)
                ((responseName, outputResponse) :: outputRest) =
              (responseName, mergeResponse baseResponse outputResponse) ::
                mergeResponseFields baseRest outputRest := by
            simp [mergeResponseFields, mergeResponseField]
            rw [mergeResponseFields_cons_left_of_not_mem responseName
              (mergeResponse baseResponse outputResponse) baseRest
              outputRest hresponseNameNotRest]
          rw [hformula] at hmerge
          exact hmerge
        injection hmerge' with hresponseMerge hrestMerge
        exact
          ResponseFieldsAbsorptionShape.cons responseName houtputReady
            (ResponseAbsorptionShape.of_absorbs baseResponse outputResponse
              hbaseResponseReady houtputResponseReady
              (by simpa [ResponseAbsorbs] using hresponseMerge))
            (ResponseFieldsAbsorptionShape.of_merge baseRest outputRest
              hbaseRestReady houtputRestReady hrestMerge)

  theorem ResponseListAbsorptionShape.of_merge
      : ∀ (base output : List ResponseValue),
          ResponseMergeReady (.list base)
          -> ResponseMergeReady (.list output)
          -> mergeResponseLists base output = output
          -> ResponseListAbsorptionShape base output
    | [], [], _hbaseReady, _houtputReady, _hmerge =>
        ResponseListAbsorptionShape.nil
    | [], outputResponse :: outputRest, _hbaseReady, _houtputReady,
        hmerge => by
        simp [mergeResponseLists] at hmerge
    | baseResponse :: baseRest, [], _hbaseReady, _houtputReady, hmerge => by
        simp [mergeResponseLists] at hmerge
    | baseResponse :: baseRest, outputResponse :: outputRest, hbaseReady,
        houtputReady, hmerge => by
        simp [mergeResponseLists] at hmerge
        rcases hmerge with ⟨hresponseMerge, hrestMerge⟩
        have hbaseResponseReady :
            ResponseMergeReady baseResponse :=
          ResponseMergeReady_list_value (baseResponse :: baseRest)
            baseResponse hbaseReady (by simp)
        have hbaseRestReady :
            ResponseMergeReady (.list baseRest) :=
          ResponseMergeReady.list baseRest
            (by
              intro response hmem
              exact ResponseMergeReady_list_value
                (baseResponse :: baseRest) response hbaseReady
                (by simp [hmem]))
        have houtputResponseReady :
            ResponseMergeReady outputResponse :=
          ResponseMergeReady_list_value (outputResponse :: outputRest)
            outputResponse houtputReady (by simp)
        have houtputRestReady :
            ResponseMergeReady (.list outputRest) :=
          ResponseMergeReady.list outputRest
            (by
              intro response hmem
              exact ResponseMergeReady_list_value
                (outputResponse :: outputRest) response houtputReady
                (by simp [hmem]))
        exact
          ResponseListAbsorptionShape.cons houtputReady
            (ResponseAbsorptionShape.of_absorbs baseResponse outputResponse
              hbaseResponseReady houtputResponseReady
              (by simpa [ResponseAbsorbs] using hresponseMerge))
            (ResponseListAbsorptionShape.of_merge baseRest outputRest
              hbaseRestReady houtputRestReady hrestMerge)
end

theorem ResponseAbsorbs_trans_of_ready (base middle output : ResponseValue)
    : ResponseMergeReady base
      -> ResponseMergeReady middle
      -> ResponseMergeReady output
      -> ResponseAbsorbs base middle
      -> ResponseAbsorbs middle output
      -> ResponseAbsorbs base output := by
  intro hbaseReady hmiddleReady houtputReady hbaseMiddle hmiddleOutput
  exact
    ResponseAbsorptionShape.to_absorbs
      (ResponseAbsorptionShape.trans
        (ResponseAbsorptionShape.of_absorbs base middle hbaseReady
          hmiddleReady hbaseMiddle)
        (ResponseAbsorptionShape.of_absorbs middle output hmiddleReady
          houtputReady hmiddleOutput))

mutual
  theorem mergeResponse_ready
      : ∀ existing incoming : ResponseValue,
          ResponseMergeReady existing
          -> ResponseMergeReady incoming
          -> ResponseMergeReady (mergeResponse existing incoming)
    | .object existingFields, .object incomingFields, hexisting, hincoming => by
        simp [mergeResponse]
        exact mergeResponseFields_object_ready_of_steps existingFields
          incomingFields hexisting
          (mergeResponseFields_ready_steps_of_ready existingFields
            incomingFields hexisting hincoming)
    | .list existingValues, .list incomingValues, hexisting, hincoming => by
        simp [mergeResponse]
        exact mergeResponseLists_ready existingValues incomingValues
          hexisting hincoming
    | .null, _, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .scalar _value, .null, _hexisting, _hincoming => by
        simpa [mergeResponse] using ResponseMergeReady.null
    | .scalar value, .scalar _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .scalar value, .object _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .scalar value, .list _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .object _fields, .null, _hexisting, _hincoming => by
        simpa [mergeResponse] using ResponseMergeReady.null
    | .object fields, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .object fields, .list values, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .list _values, .null, _hexisting, _hincoming => by
        simpa [mergeResponse] using ResponseMergeReady.null
    | .list values, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting
    | .list values, .object fields, hexisting, _hincoming => by
        simpa [mergeResponse] using hexisting

  theorem mergeResponseFields_ready_steps_of_ready
      : ∀ existing incoming : List (Name × ResponseValue),
          ResponseMergeReady (.object existing)
          -> ResponseMergeReady (.object incoming)
          -> MergeResponseFieldsReadySteps existing incoming
    | existing, [], _hexisting, _hincoming => by
        simp [MergeResponseFieldsReadySteps]
    | existing, (responseName, incomingResponse) :: rest, hexisting,
        hincoming => by
        have hincomingResponse :
            ResponseMergeReady incomingResponse := by
          exact ResponseMergeReady_object_field
            ((responseName, incomingResponse) :: rest) responseName
            incomingResponse hincoming (by simp)
        have hrestIncoming :
            ResponseMergeReady (.object rest) := by
          apply ResponseMergeReady.object
          · exact (ResponseMergeReady_object_pairKeysNodup
              ((responseName, incomingResponse) :: rest) hincoming).tail
          · intro restName restResponse hmem
            exact ResponseMergeReady_object_field
              ((responseName, incomingResponse) :: rest) restName restResponse
              hincoming (by simp [hmem])
        have hcollision :
            ∀ existingResponse,
              (responseName, existingResponse) ∈ existing ->
                ResponseMergeReady
                  (mergeResponse existingResponse incomingResponse) := by
          intro existingResponse hmem
          exact mergeResponse_ready existingResponse incomingResponse
            (ResponseMergeReady_object_field existing responseName
              existingResponse hexisting hmem)
            hincomingResponse
        have hupdatedReady :
            ResponseMergeReady
              (.object
                (mergeResponseField responseName incomingResponse existing)) :=
          mergeResponseField_object_ready responseName incomingResponse
            existing hexisting hincomingResponse hcollision
        have hrestSteps :
            MergeResponseFieldsReadySteps
              (mergeResponseField responseName incomingResponse existing) rest :=
          mergeResponseFields_ready_steps_of_ready
            (mergeResponseField responseName incomingResponse existing) rest
            hupdatedReady hrestIncoming
        exact ⟨hincomingResponse, hcollision, hrestSteps⟩

  theorem mergeResponseLists_ready
      : ∀ existing incoming : List ResponseValue,
          ResponseMergeReady (.list existing)
          -> ResponseMergeReady (.list incoming)
          -> ResponseMergeReady (.list (mergeResponseLists existing incoming))
    | [], _incoming, _hexisting, _hincoming => by
        simp [mergeResponseLists]
        exact ResponseMergeReady_empty_list
    | existing, [], hexisting, _hincoming => by
        cases existing <;> simpa [mergeResponseLists] using hexisting
    | existing :: existingRest, incoming :: incomingRest, hexisting,
        hincoming => by
        apply ResponseMergeReady.list
        intro response hmem
        simp [mergeResponseLists] at hmem
        rcases hmem with hhead | htail
        · rw [hhead]
          exact mergeResponse_ready existing incoming
            (ResponseMergeReady_list_value (existing :: existingRest)
              existing hexisting (by simp))
            (ResponseMergeReady_list_value (incoming :: incomingRest)
              incoming hincoming (by simp))
        · exact ResponseMergeReady_list_value
            (mergeResponseLists existingRest incomingRest) response
            (mergeResponseLists_ready existingRest incomingRest
              (ResponseMergeReady.list existingRest
                (by
                  intro restResponse hrest
                  exact ResponseMergeReady_list_value
                    (existing :: existingRest) restResponse hexisting
                    (by simp [hrest])))
              (ResponseMergeReady.list incomingRest
                (by
                  intro restResponse hrest
                  exact ResponseMergeReady_list_value
                    (incoming :: incomingRest) restResponse hincoming
                    (by simp [hrest]))))
            htail
end

theorem mergeResponseField_object_absorbs
    (responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : ResponseMergeReady (.object fields)
      -> (∀ existing,
            (responseName, existing) ∈ fields
            -> ResponseAbsorbs existing (mergeResponse existing incoming))
      -> ResponseAbsorbs (.object fields)
          (.object (mergeResponseField responseName incoming fields)) := by
  intro hfieldsReady hcollisionAbsorbs
  unfold ResponseAbsorbs
  simp [mergeResponse]
  induction fields with
  | nil =>
      simp [mergeResponseFields, mergeResponseField]
  | cons field rest ih =>
      cases field with
      | mk fieldResponseName existing =>
          have hexistingReady :
              ResponseMergeReady existing := by
            exact ResponseMergeReady_object_field
              ((fieldResponseName, existing) :: rest) fieldResponseName existing
              hfieldsReady (by simp)
          have hrestReady :
              ResponseMergeReady (.object rest) := by
            apply ResponseMergeReady.object
            · exact (ResponseMergeReady_object_pairKeysNodup
                ((fieldResponseName, existing) :: rest) hfieldsReady).tail
            · intro restName restResponse hmem
              exact ResponseMergeReady_object_field
                ((fieldResponseName, existing) :: rest) restName restResponse
                hfieldsReady (by simp [hmem])
          have hfieldResponseNameNotRest :
              fieldResponseName ∉ rest.map Prod.fst := by
            exact (List.nodup_cons.mp
              (ResponseMergeReady_object_pairKeysNodup
                ((fieldResponseName, existing) :: rest) hfieldsReady)).1
          by_cases h : fieldResponseName == responseName
          · have hcollision :
                ResponseAbsorbs existing (mergeResponse existing incoming) := by
              exact hcollisionAbsorbs existing (by simp [beq_iff_eq.mp h])
            have hrestSelf :
                mergeResponseFields rest rest = rest := by
              exact mergeResponseFields_self_of_ready rest
                (ResponseMergeReady_object_pairKeysNodup rest hrestReady)
                (by
                  intro restName restResponse hmem
                  exact ResponseMergeReady_object_field rest restName
                    restResponse hrestReady hmem)
            simp [mergeResponseField, h, mergeResponseFields,
              ResponseAbsorbs] at hcollision ⊢
            rw [hcollision]
            exact mergeResponseFields_cons_left_of_not_mem fieldResponseName
              (mergeResponse existing incoming) rest rest
              hfieldResponseNameNotRest ▸ by simp [hrestSelf]
          · have hfieldSelf :
                mergeResponse existing existing = existing :=
              mergeResponse_self_of_ready existing hexistingReady
            have hfieldResponseNameNotMerged :
                fieldResponseName ∉
                  (mergeResponseField responseName incoming rest).map
                    Prod.fst := by
              intro hmem
              rcases mergeResponseField_key_mem responseName fieldResponseName
                incoming rest hmem with heq | hrest
              · have hne : fieldResponseName ≠ responseName := by
                  intro heq'
                  simp [heq'] at h
                exact hne heq
              · exact hfieldResponseNameNotRest hrest
            have hrestCollision :
                ∀ existing',
                  (responseName, existing') ∈ rest ->
                    ResponseAbsorbs existing'
                      (mergeResponse existing' incoming) := by
              intro existing' hmem
              exact hcollisionAbsorbs existing' (by simp [hmem])
            have hrestAbsorbs :
                mergeResponseFields rest
                  (mergeResponseField responseName incoming rest) =
                mergeResponseField responseName incoming rest := by
              exact ih hrestReady hrestCollision
            simp [mergeResponseField, h, mergeResponseFields, hfieldSelf]
            rw [mergeResponseFields_cons_left_of_not_mem fieldResponseName
              existing rest (mergeResponseField responseName incoming rest)
              hfieldResponseNameNotMerged]
            simp [hrestAbsorbs]

theorem mergeResponseField_object_ready_of_ready
    (responseName : Name) (incoming : ResponseValue)
    (fields : List (Name × ResponseValue))
    : ResponseMergeReady (.object fields)
      -> ResponseMergeReady incoming
      -> ResponseMergeReady
          (.object (mergeResponseField responseName incoming fields)) := by
  intro hfieldsReady hincoming
  exact mergeResponseField_object_ready responseName incoming fields
    hfieldsReady hincoming
    (by
      intro existing hmem
      exact mergeResponse_ready existing incoming
        (ResponseMergeReady_object_field fields responseName existing
          hfieldsReady hmem)
        hincoming)

theorem mergeResponseFields_object_ready_of_ready
    (existing incoming : List (Name × ResponseValue))
    : ResponseMergeReady (.object existing)
      -> ResponseMergeReady (.object incoming)
      -> ResponseMergeReady (.object (mergeResponseFields existing incoming)) := by
  intro hexisting hincoming
  simpa [mergeResponse] using
    mergeResponse_ready (.object existing) (.object incoming) hexisting
      hincoming

mutual
  theorem ResponseAbsorbs_merge_of_ready
      : ∀ existing incoming : ResponseValue,
          ResponseMergeReady existing
          -> ResponseMergeReady incoming
          -> ResponseAbsorbs existing (mergeResponse existing incoming)
    | .object existingFields, .object incomingFields, hexisting, hincoming => by
        simp [mergeResponse]
        exact mergeResponseFields_object_absorbs_merge_of_ready existingFields
          incomingFields hexisting hincoming
    | .list existingValues, .list incomingValues, hexisting, hincoming => by
        simp [mergeResponse]
        exact mergeResponseLists_absorbs_merge_of_ready existingValues
          incomingValues hexisting hincoming
    | .null, _, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready .null hexisting
    | .scalar _value, .null, _hexisting, _hincoming => by
        simp [ResponseAbsorbs, mergeResponse]
    | .scalar value, .scalar _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready (.scalar value) hexisting
    | .scalar value, .object _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready (.scalar value) hexisting
    | .scalar value, .list _incoming, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready (.scalar value) hexisting
    | .object _fields, .null, _hexisting, _hincoming => by
        simp [ResponseAbsorbs, mergeResponse]
    | .object fields, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready (.object fields) hexisting
    | .object fields, .list values, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready (.object fields) hexisting
    | .list _values, .null, _hexisting, _hincoming => by
        simp [ResponseAbsorbs, mergeResponse]
    | .list values, .scalar value, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready (.list values) hexisting
    | .list values, .object fields, hexisting, _hincoming => by
        simpa [mergeResponse] using
          ResponseAbsorbs_refl_of_ready (.list values) hexisting

  theorem mergeResponseFields_object_absorbs_merge_of_ready
      : ∀ existing incoming : List (Name × ResponseValue),
          ResponseMergeReady (.object existing)
          -> ResponseMergeReady (.object incoming)
          -> ResponseAbsorbs (.object existing)
              (.object (mergeResponseFields existing incoming))
    | existing, [], hexisting, _hincoming => by
        simpa [mergeResponseFields] using
          ResponseAbsorbs_refl_of_ready (.object existing) hexisting
    | existing, (responseName, incomingResponse) :: rest, hexisting,
        hincoming => by
        have hincomingResponse :
            ResponseMergeReady incomingResponse :=
          ResponseMergeReady_object_field
            ((responseName, incomingResponse) :: rest) responseName
            incomingResponse hincoming (by simp)
        have hrestIncoming :
            ResponseMergeReady (.object rest) := by
          apply ResponseMergeReady.object
          · exact (ResponseMergeReady_object_pairKeysNodup
              ((responseName, incomingResponse) :: rest) hincoming).tail
          · intro restName restResponse hmem
            exact ResponseMergeReady_object_field
              ((responseName, incomingResponse) :: rest) restName restResponse
              hincoming (by simp [hmem])
        have hbaseUpdated :
            ResponseAbsorbs (.object existing)
              (.object
                (mergeResponseField responseName incomingResponse existing)) :=
          mergeResponseField_object_absorbs responseName incomingResponse
            existing hexisting
            (by
              intro existingResponse hmem
              exact ResponseAbsorbs_merge_of_ready existingResponse
                incomingResponse
                (ResponseMergeReady_object_field existing responseName
                  existingResponse hexisting hmem)
                hincomingResponse)
        have hupdatedReady :
            ResponseMergeReady
              (.object
                (mergeResponseField responseName incomingResponse existing)) :=
          mergeResponseField_object_ready_of_ready responseName incomingResponse
            existing hexisting hincomingResponse
        have hupdatedFinal :
            ResponseAbsorbs
              (.object
                (mergeResponseField responseName incomingResponse existing))
              (.object
                (mergeResponseFields
                  (mergeResponseField responseName incomingResponse existing)
                  rest)) :=
          mergeResponseFields_object_absorbs_merge_of_ready
            (mergeResponseField responseName incomingResponse existing) rest
            hupdatedReady hrestIncoming
        have hfinalReady :
            ResponseMergeReady
              (.object
                (mergeResponseFields
                  (mergeResponseField responseName incomingResponse existing)
                  rest)) :=
          mergeResponseFields_object_ready_of_ready
            (mergeResponseField responseName incomingResponse existing) rest
            hupdatedReady hrestIncoming
        simpa [mergeResponseFields] using
          ResponseAbsorbs_trans_of_ready (.object existing)
            (.object
              (mergeResponseField responseName incomingResponse existing))
            (.object
              (mergeResponseFields
                (mergeResponseField responseName incomingResponse existing)
                rest))
            hexisting hupdatedReady hfinalReady hbaseUpdated hupdatedFinal

  theorem mergeResponseLists_absorbs_merge_of_ready
      : ∀ existing incoming : List ResponseValue,
          ResponseMergeReady (.list existing)
          -> ResponseMergeReady (.list incoming)
          -> ResponseAbsorbs (.list existing)
              (.list (mergeResponseLists existing incoming))
    | [], _incoming, _hexisting, _hincoming => by
        simp [mergeResponseLists, ResponseAbsorbs, mergeResponse]
    | existing, [], hexisting, _hincoming => by
        cases existing with
        | nil =>
            simp [mergeResponseLists, ResponseAbsorbs, mergeResponse]
        | cons response rest =>
            simpa [mergeResponseLists] using
              ResponseAbsorbs_refl_of_ready (.list (response :: rest))
                hexisting
    | existing :: existingRest, incoming :: incomingRest, hexisting,
        hincoming => by
        have hexistingHead :
            ResponseMergeReady existing :=
          ResponseMergeReady_list_value (existing :: existingRest) existing
            hexisting (by simp)
        have hincomingHead :
            ResponseMergeReady incoming :=
          ResponseMergeReady_list_value (incoming :: incomingRest) incoming
            hincoming (by simp)
        have hexistingRest :
            ResponseMergeReady (.list existingRest) :=
          ResponseMergeReady.list existingRest
            (by
              intro response hmem
              exact ResponseMergeReady_list_value
                (existing :: existingRest) response hexisting
                (by simp [hmem]))
        have hincomingRest :
            ResponseMergeReady (.list incomingRest) :=
          ResponseMergeReady.list incomingRest
            (by
              intro response hmem
              exact ResponseMergeReady_list_value
                (incoming :: incomingRest) response hincoming
                (by simp [hmem]))
        have hhead :
            mergeResponse existing (mergeResponse existing incoming) =
              mergeResponse existing incoming := by
          simpa [ResponseAbsorbs] using
            ResponseAbsorbs_merge_of_ready existing incoming hexistingHead
              hincomingHead
        have htail :
            mergeResponseLists existingRest
                (mergeResponseLists existingRest incomingRest) =
              mergeResponseLists existingRest incomingRest := by
          simpa [ResponseAbsorbs, mergeResponse] using
            mergeResponseLists_absorbs_merge_of_ready existingRest incomingRest
              hexistingRest hincomingRest
        simp [ResponseAbsorbs, mergeResponse, mergeResponseLists, hhead, htail]
end

theorem mergeResponseFields_object_absorbs_from_steps
    (base current incoming : List (Name × ResponseValue))
    : MergeResponseFieldsAbsorbsFrom base current incoming
      -> ResponseAbsorbs (.object base)
          (.object (mergeResponseFields current incoming)) := by
  intro hsteps
  induction incoming generalizing current with
  | nil =>
      simpa [mergeResponseFields, MergeResponseFieldsAbsorbsFrom] using hsteps
  | cons field rest ih =>
      cases field with
      | mk responseName incomingResponse =>
          simp [MergeResponseFieldsAbsorbsFrom] at hsteps
          rcases hsteps with ⟨_hcurrent, hrest⟩
          simp [mergeResponseFields]
          exact ih
            (mergeResponseField responseName incomingResponse current) hrest

theorem emptySelectionStateEquivalent
    {ObjectIdentity : Type}
    (schema : Schema) (resolvers : Resolvers ObjectIdentity)
    (variableValues : VariableValues) (depth : Nat)
    (parentType : Name) (source : ResolverValue ObjectIdentity)
    (initial : ResponseValue)
    : ExecutionStateEquivalent
        {
          window :=
            {
              schema := schema
              resolvers := resolvers
              variableValues := variableValues
              depth := depth
              parentType := parentType
              source := source
              selectionSet := []
            }
          initial := initial
        } := by
    simp [ExecutionStateEquivalent, ResponseResultEquivalent,
      ExecutionEquivalenceState.ungroupedProjectionResult,
      ExecutionEquivalenceState.specProjectionResult,
      GraphQL.Execution.collectFields, GraphQL.Execution.executeCollectedFields,
      mergeResponse_empty_object_right]

end Eager
end ExecutionUngroupedUncached
end Algorithms

end GraphQL
