import Proofs.GraphQL.Theories.NormalForm.Shared.Execution

/-!
Execution ignores later repetitions of executable fields that have already occurred in
the same response-name group. This is the proof-only absorption layer needed when a
static named-fragment expansion retains occurrences that spec `CollectFields` filters
through `visitedFragments`.
-/

namespace GraphQL
namespace Execution
namespace DuplicateFields

variable {ObjectRef : Type}

inductive FirstOccurrences {α : Type} : List α -> List α -> List α -> Prop where
  | nil (seen : List α) : FirstOccurrences seen [] []
  | keep (seen : List α) (item : α) {left right : List α}
    (rest : FirstOccurrences (item :: seen) left right)
    : FirstOccurrences seen (item :: left) (item :: right)
  | duplicate (seen : List α) (item : α) {left right : List α}
    (hseen : item ∈ seen) (rest : FirstOccurrences seen left right)
    : FirstOccurrences seen left (item :: right)

theorem FirstOccurrences.refl (seen : List α)
    : ∀ items : List α, FirstOccurrences seen items items
  | [] => .nil seen
  | item :: rest => .keep seen item (FirstOccurrences.refl (item :: seen) rest)

theorem FirstOccurrences.weaken (hsubset : ∀ item, item ∈ seen -> item ∈ larger)
    : FirstOccurrences seen left right -> FirstOccurrences larger left right := by
  intro htrace
  induction htrace generalizing larger with
  | nil seen => exact .nil larger
  | keep seen item rest ih =>
      apply FirstOccurrences.keep larger item
      exact ih (by
        intro candidate hcandidate
        simp at hcandidate ⊢
        exact hcandidate.elim Or.inl (fun hmem => Or.inr (hsubset candidate hmem)))
  | duplicate seen item hseen rest ih =>
      exact FirstOccurrences.duplicate larger item (hsubset item hseen) (ih hsubset)

theorem FirstOccurrences.onlyDuplicates (hseen : ∀ item, item ∈ extra -> item ∈ seen)
    : FirstOccurrences seen [] extra := by
  induction extra with
  | nil => exact .nil seen
  | cons item rest ih =>
      apply FirstOccurrences.duplicate seen item
      · exact hseen item (by simp)
      · exact ih (by
          intro candidate hcandidate
          exact hseen candidate (by simp [hcandidate]))

theorem FirstOccurrences.append
    (hleft : FirstOccurrences seen left right)
    (hright : FirstOccurrences (left.reverse ++ seen) left' right')
    : FirstOccurrences seen (left ++ left') (right ++ right') := by
  induction hleft generalizing left' right' with
  | nil seen => simpa using hright
  | keep seen item rest ih =>
      apply FirstOccurrences.keep seen item
      apply ih
      simpa [List.reverse_cons, List.append_assoc] using hright
  | duplicate seen item hseen rest ih =>
      exact FirstOccurrences.duplicate seen item hseen (ih hright)

theorem FirstOccurrences.appendSame
    {α : Type} {seen left right : List α}
    (htrace : FirstOccurrences seen left right)
    (suffix : List α)
    : FirstOccurrences seen (left ++ suffix) (right ++ suffix) := by
  apply htrace.append
  exact FirstOccurrences.refl (left.reverse ++ seen) suffix

theorem FirstOccurrences.appendDuplicates
    {α : Type} {seen left right extra : List α}
    (htrace : FirstOccurrences seen left right)
    (hduplicates : ∀ item, item ∈ extra -> item ∈ left)
    : FirstOccurrences seen left (right ++ extra) := by
  simpa using htrace.append
    (FirstOccurrences.onlyDuplicates (seen := left.reverse ++ seen) (by
      intro item hitem
      have : item ∈ left.reverse := by simpa using hduplicates item hitem
      exact List.mem_append_left _ this))

inductive GroupFirstOccurrences
    : List (Name × List ExecutableField)
      -> List (Name × List ExecutableField) -> Prop where
  | nil : GroupFirstOccurrences [] []
  | cons (responseName : Name) {leftFields rightFields}
    {leftGroups rightGroups}
    (fields : FirstOccurrences [] leftFields rightFields)
    (rest : GroupFirstOccurrences leftGroups rightGroups)
    : GroupFirstOccurrences
        ((responseName, leftFields) :: leftGroups)
        ((responseName, rightFields) :: rightGroups)

theorem GroupFirstOccurrences.refl
    : ∀ groups : List (Name × List ExecutableField), GroupFirstOccurrences groups groups
  | [] => .nil
  | (responseName, fields) :: rest =>
      .cons responseName (FirstOccurrences.refl [] fields)
        (GroupFirstOccurrences.refl rest)

theorem FirstOccurrences.right_mem_left_or_seen
    (htrace : FirstOccurrences seen left right)
    : ∀ field, field ∈ right -> field ∈ left ∨ field ∈ seen := by
  intro field hfield
  induction htrace with
  | nil => simp at hfield
  | keep seen item rest ih =>
      simp only [List.mem_cons] at hfield
      cases hfield with
      | inl hitem =>
          subst field
          exact Or.inl (by simp)
      | inr hrest =>
          rcases ih hrest with hleft | hseen
          · exact Or.inl (by simp [hleft])
          · simp only [List.mem_cons] at hseen
            exact hseen.elim (fun hitem => Or.inl (by simp [hitem])) Or.inr
  | duplicate seen item hseen rest ih =>
      simp only [List.mem_cons] at hfield
      exact hfield.elim (fun hitem => Or.inr (by simpa [hitem] using hseen)) ih

theorem FirstOccurrences.right_mem_left (htrace : FirstOccurrences [] left right)
    : ∀ field, field ∈ right -> field ∈ left := by
  intro field hfield
  rcases htrace.right_mem_left_or_seen field hfield with hleft | hseen
  · exact hleft
  · simp at hseen

def GroupContained
    (groups : List (Name × List ExecutableField))
    (group : Name × List ExecutableField)
    : Prop :=
  ∃ fields, (group.fst, fields) ∈ groups ∧ ∀ field, field ∈ group.snd -> field ∈ fields

def GroupsContained (groups incoming : List (Name × List ExecutableField)) : Prop :=
  ∀ group, group ∈ incoming -> GroupContained groups group

theorem groupsContained_trans
    (hleft : GroupsContained left middle)
    (hright : GroupsContained middle right)
    : GroupsContained left right := by
  intro group hgroup
  rcases hright group hgroup with
    ⟨middleFields, hmiddleMem, hmiddleFields⟩
  rcases hleft (group.fst, middleFields) hmiddleMem with
    ⟨leftFields, hleftMem, hleftFields⟩
  exact ⟨leftFields, hleftMem,
    fun field hfield => hleftFields field (hmiddleFields field hfield)⟩

theorem GroupFirstOccurrences.rightContainedInLeft
    (hgroups : GroupFirstOccurrences left right)
    : GroupsContained left right := by
  intro group hgroup
  induction hgroups with
  | nil => simp at hgroup
  | cons responseName fields rest ih =>
      simp only [List.mem_cons] at hgroup
      cases hgroup with
      | inl hhead =>
          subst group
          exact ⟨_, by simp, fields.right_mem_left⟩
      | inr htail =>
          rcases ih htail with ⟨containedFields, hmem, hfields⟩
          exact ⟨containedFields, by simp [hmem], hfields⟩

theorem GroupFirstOccurrences.names_eq (hgroups : GroupFirstOccurrences left right)
    : left.map Prod.fst = right.map Prod.fst := by
  induction hgroups with
  | nil => rfl
  | cons responseName fields rest ih => simp [ih]

theorem GroupFirstOccurrences.right_namesNodup
    (hgroups : GroupFirstOccurrences left right)
    (hnodup : NormalForm.executableGroupNamesNodup left)
    : NormalForm.executableGroupNamesNodup right := by
  induction hgroups with
  | nil => exact hnodup
  | cons responseName fields rest ih =>
      exact ⟨by simpa [rest.names_eq] using hnodup.1, ih hnodup.2⟩

theorem GroupFirstOccurrences.left_namesNodup
    (hgroups : GroupFirstOccurrences left right)
    (hnodup : NormalForm.executableGroupNamesNodup right)
    : NormalForm.executableGroupNamesNodup left := by
  induction hgroups with
  | nil => exact hnodup
  | cons responseName fields rest ih =>
      exact ⟨by simpa [rest.names_eq] using hnodup.1, ih hnodup.2⟩

theorem groupContained_add_self
    (group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    : GroupContained (addExecutableGroup group groups) group := by
  induction groups with
  | nil =>
      refine ⟨group.snd, ?_, ?_⟩
      · simp [addExecutableGroup]
      · intro field hfield
        exact hfield
  | cons head rest ih =>
      rcases head with ⟨responseName, fields⟩
      rcases group with ⟨groupName, groupFields⟩
      by_cases hname : responseName == groupName
      · have heq : responseName = groupName := beq_iff_eq.mp hname
        subst responseName
        refine ⟨fields ++ groupFields, ?_, ?_⟩
        · simp [addExecutableGroup]
        · intro field hfield
          exact List.mem_append_right fields hfield
      · rcases ih with ⟨containedFields, hmem, hfields⟩
        refine ⟨containedFields, ?_, hfields⟩
        simp [addExecutableGroup, hname, hmem]

theorem groupContained_add_of_contained
    (incoming group : Name × List ExecutableField)
    (groups : List (Name × List ExecutableField))
    (hcontained : GroupContained groups group)
    : GroupContained (addExecutableGroup incoming groups) group := by
  induction groups with
  | nil => simp [GroupContained] at hcontained
  | cons head rest ih =>
      rcases head with ⟨responseName, fields⟩
      rcases incoming with ⟨incomingName, incomingFields⟩
      rcases group with ⟨groupName, groupFields⟩
      rcases hcontained with ⟨containedFields, hmem, hfields⟩
      simp only [List.mem_cons] at hmem
      by_cases hname : responseName == incomingName
      · have heq : responseName = incomingName := beq_iff_eq.mp hname
        subst responseName
        cases hmem with
        | inl hhead =>
            have hgroupName : groupName = incomingName := congrArg Prod.fst hhead
            have hcontainedFields : containedFields = fields := by
              simpa [hgroupName] using congrArg Prod.snd hhead
            subst groupName
            subst containedFields
            refine ⟨fields ++ incomingFields, ?_, ?_⟩
            · simp [addExecutableGroup]
            · intro field hfield
              exact List.mem_append_left _ (hfields field hfield)
        | inr hrest =>
            refine ⟨containedFields, ?_, hfields⟩
            simp [addExecutableGroup, hrest]
      · cases hmem with
        | inl hhead =>
            refine ⟨containedFields, ?_, hfields⟩
            simp [addExecutableGroup, hname, hhead]
        | inr hrest =>
            have htail : GroupContained rest (groupName, groupFields) :=
              ⟨containedFields, hrest, hfields⟩
            rcases ih htail with ⟨newFields, hnewMem, hnewFields⟩
            refine ⟨newFields, ?_, hnewFields⟩
            simp [addExecutableGroup, hname, hnewMem]

theorem groupsContained_add_of_contained
    (incoming : Name × List ExecutableField)
    (groups old : List (Name × List ExecutableField))
    (hcontained : GroupsContained groups old)
    : GroupsContained (addExecutableGroup incoming groups) old := by
  intro group hgroup
  exact groupContained_add_of_contained incoming group groups
    (hcontained group hgroup)

theorem GroupFirstOccurrences.addSame (group : Name × List ExecutableField)
    : GroupFirstOccurrences left right
      -> GroupFirstOccurrences (addExecutableGroup group left)
          (addExecutableGroup group right) := by
  intro hgroups
  induction hgroups with
  | nil => exact GroupFirstOccurrences.refl [group]
  | cons responseName fields rest ih =>
      rcases group with ⟨groupName, groupFields⟩
      by_cases hname : responseName == groupName
      · simp [addExecutableGroup, hname]
        exact .cons responseName (fields.appendSame groupFields) rest
      · simp [addExecutableGroup, hname]
        exact .cons responseName fields ih

theorem FirstOccurrences.appendRelated
    (hleft : FirstOccurrences [] left right)
    (hright : FirstOccurrences [] left' right')
    : FirstOccurrences [] (left ++ left') (right ++ right') := by
  apply hleft.append
  exact hright.weaken (by simp)

theorem GroupFirstOccurrences.addRelated
    (responseName : Name)
    (fields : FirstOccurrences [] leftFields rightFields)
    : ∀ {leftGroups rightGroups},
        GroupFirstOccurrences leftGroups rightGroups
        -> GroupFirstOccurrences
            (addExecutableGroup (responseName, leftFields) leftGroups)
            (addExecutableGroup (responseName, rightFields) rightGroups)
  | [], [], .nil => .cons responseName fields .nil
  | (currentName, currentLeft) :: leftRest,
      (rightCurrentName, currentRight) :: rightRest, hgroups => by
      cases hgroups with
      | cons _ currentFields rest =>
          by_cases hname : currentName == responseName
          · simp [addExecutableGroup, hname]
            exact .cons currentName (currentFields.appendRelated fields) rest
          · simp [addExecutableGroup, hname]
            exact .cons currentName currentFields
              (GroupFirstOccurrences.addRelated responseName fields rest)

theorem GroupFirstOccurrences.mergeRelated
    : ∀ {incomingLeft incomingRight},
        GroupFirstOccurrences incomingLeft incomingRight
        -> GroupFirstOccurrences left right
        -> GroupFirstOccurrences
            (mergeExecutableGroups left incomingLeft)
            (mergeExecutableGroups right incomingRight)
  | [], [], .nil, hgroups => by
      simpa [mergeExecutableGroups] using hgroups
  | (responseName, leftFields) :: leftRest,
      (rightResponseName, rightFields) :: rightRest, incomingGroups, hgroups => by
      cases incomingGroups with
      | cons _ fields rest =>
          simp only [mergeExecutableGroups, List.foldl_cons]
          exact GroupFirstOccurrences.mergeRelated rest
            (hgroups.addRelated responseName fields)

theorem GroupFirstOccurrences.addDuplicatesRight (group : Name × List ExecutableField)
    : ∀ {left right},
        NormalForm.executableGroupNamesNodup left
        -> GroupContained left group
        -> GroupFirstOccurrences left right
        -> GroupFirstOccurrences left (addExecutableGroup group right)
  | [], [], _hnodup, hcontained, .nil => by
      simp [GroupContained] at hcontained
  | (responseName, leftFields) :: leftGroups,
      (rightResponseName, rightFields) :: rightGroups,
      hnodup, hcontained, hgroups => by
      cases hgroups with
      | cons _ fields rest =>
          rcases group with ⟨groupName, groupFields⟩
          rcases hcontained with ⟨containedFields, hmem, hfieldMem⟩
          simp only [List.mem_cons] at hmem
          by_cases hname : responseName == groupName
          · have heq : responseName = groupName := beq_iff_eq.mp hname
            subst responseName
            have hhead : containedFields = leftFields := by
              cases hmem with
              | inl hmem => simpa using congrArg Prod.snd hmem
              | inr hmem =>
                  exfalso
                  exact hnodup.1 (List.mem_map_of_mem hmem)
            subst containedFields
            simp [addExecutableGroup]
            exact .cons groupName (fields.appendDuplicates hfieldMem) rest
          · have hrestContained :
                GroupContained leftGroups (groupName, groupFields) := by
              cases hmem with
              | inl hmem =>
                  have heq : groupName = responseName := congrArg Prod.fst hmem
                  subst groupName
                  simp at hname
              | inr hmem => exact ⟨containedFields, hmem, hfieldMem⟩
            simp [addExecutableGroup, hname]
            exact .cons responseName fields
              (GroupFirstOccurrences.addDuplicatesRight (groupName, groupFields)
                hnodup.2 hrestContained rest)

theorem GroupFirstOccurrences.mergeSame (incoming : List (Name × List ExecutableField))
    : GroupFirstOccurrences left right
      -> GroupFirstOccurrences (mergeExecutableGroups left incoming)
          (mergeExecutableGroups right incoming) := by
  intro hgroups
  induction incoming generalizing left right with
  | nil => simpa [mergeExecutableGroups] using hgroups
  | cons group rest ih =>
      simp only [mergeExecutableGroups, List.foldl_cons]
      exact ih (hgroups.addSame group)

theorem GroupFirstOccurrences.mergeDuplicatesRight
    (incoming : List (Name × List ExecutableField))
    (hnodup : NormalForm.executableGroupNamesNodup left)
    (hcontained : GroupsContained left incoming)
    : GroupFirstOccurrences left right
      -> GroupFirstOccurrences left (mergeExecutableGroups right incoming) := by
  intro hgroups
  induction incoming generalizing right with
  | nil => simpa [mergeExecutableGroups] using hgroups
  | cons group rest ih =>
      simp only [mergeExecutableGroups, List.foldl_cons]
      apply ih
      · intro candidate hcandidate
        exact hcontained candidate (by simp [hcandidate])
      · exact hgroups.addDuplicatesRight group hnodup
          (hcontained group (by simp))

theorem groupsContained_merge_left
    (left incoming old : List (Name × List ExecutableField))
    (hcontained : GroupsContained left old)
    : GroupsContained (mergeExecutableGroups left incoming) old := by
  induction incoming generalizing left with
  | nil => simpa [mergeExecutableGroups] using hcontained
  | cons group rest ih =>
      simp only [mergeExecutableGroups, List.foldl_cons]
      exact ih (addExecutableGroup group left) (groupsContained_add_of_contained
        group left old hcontained)

theorem groupsContained_merge_right (left incoming : List (Name × List ExecutableField))
    : GroupsContained (mergeExecutableGroups left incoming) incoming := by
  induction incoming generalizing left with
  | nil =>
      intro group hgroup
      simp at hgroup
  | cons group rest ih =>
      simp only [mergeExecutableGroups, List.foldl_cons]
      intro candidate hcandidate
      simp only [List.mem_cons] at hcandidate
      cases hcandidate with
      | inl hcandidate =>
          subst candidate
          exact groupsContained_merge_left (addExecutableGroup group left) rest [group]
            (by
              intro singleton hsingleton
              simp at hsingleton
              subst singleton
              exact groupContained_add_self group left)
            group (by simp)
      | inr hcandidate =>
          exact ih (addExecutableGroup group left) candidate hcandidate

def collectSubfieldsFold
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectRef)
    : List (Name × List ExecutableField) -> List ExecutableField
      -> List (Name × List ExecutableField)
  | groups, [] => groups
  | groups, field :: rest =>
      collectSubfieldsFold schema variableValues objectType objectValue
        (mergeExecutableGroups groups
          (collectFields schema variableValues objectType objectValue field.selectionSet))
        rest

theorem collectSubfields_namesNodup
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectRef)
    : ∀ fields,
        NormalForm.executableGroupNamesNodup
          (collectSubfields schema variableValues objectType objectValue fields)
  | [] => by simp [collectSubfields, NormalForm.executableGroupNamesNodup]
  | field :: rest => by
      simp only [collectSubfields]
      exact NormalForm.mergeExecutableGroups_namesNodup _ _
        (NormalForm.collectFields_namesNodup schema variableValues objectType
          objectValue field.selectionSet)

theorem collectSubfieldsFold_eq_merge
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectRef)
    (groups : List (Name × List ExecutableField))
    (hnodup : NormalForm.executableGroupNamesNodup groups)
    : ∀ fields,
        collectSubfieldsFold schema variableValues objectType objectValue groups fields
        = mergeExecutableGroups groups
            (collectSubfields schema variableValues objectType objectValue fields) := by
  intro fields
  induction fields generalizing groups with
  | nil => simp [collectSubfieldsFold, collectSubfields, mergeExecutableGroups]
  | cons field rest ih =>
      simp only [collectSubfieldsFold, collectSubfields]
      rw [ih]
      · rw [NormalForm.mergeExecutableGroups_assoc_of_namesNodup]
        · exact NormalForm.collectFields_namesNodup schema variableValues
            objectType objectValue field.selectionSet
        · exact collectSubfields_namesNodup schema variableValues objectType
            objectValue rest
      · exact NormalForm.mergeExecutableGroups_namesNodup _ _ hnodup

theorem collectSubfieldsFold_nil
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectRef)
    (fields : List ExecutableField)
    : collectSubfieldsFold schema variableValues objectType objectValue [] fields
      = collectSubfields schema variableValues objectType objectValue fields := by
  rw [collectSubfieldsFold_eq_merge]
  · rw [NormalForm.mergeExecutableGroups_nil_left_of_namesNodup]
    induction fields with
    | nil => simp [collectSubfields, NormalForm.executableGroupNamesNodup]
    | cons field rest ih =>
        simp only [collectSubfields]
        exact NormalForm.mergeExecutableGroups_namesNodup _ _
          (NormalForm.collectFields_namesNodup schema variableValues objectType
            objectValue field.selectionSet)
  · simp [NormalForm.executableGroupNamesNodup]

theorem collectSubfieldsFold_firstOccurrences
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectRef)
    (htrace : FirstOccurrences seen leftFields rightFields)
    (hgroups : GroupFirstOccurrences leftGroups rightGroups)
    (hnodup : NormalForm.executableGroupNamesNodup leftGroups)
    (hseen
      : ∀ field,
          field ∈ seen
          -> GroupsContained leftGroups
              (collectFields schema variableValues objectType objectValue
                field.selectionSet))
    : GroupFirstOccurrences
        (collectSubfieldsFold schema variableValues objectType objectValue
          leftGroups leftFields)
        (collectSubfieldsFold schema variableValues objectType objectValue
          rightGroups rightFields) := by
  induction htrace generalizing leftGroups rightGroups with
  | nil seen => exact hgroups
  | keep seen field rest ih =>
      let contribution :=
        collectFields schema variableValues objectType objectValue field.selectionSet
      have hcontributionNodup : NormalForm.executableGroupNamesNodup contribution :=
        NormalForm.collectFields_namesNodup schema variableValues objectType
          objectValue field.selectionSet
      apply ih
      · exact hgroups.mergeSame contribution
      · exact NormalForm.mergeExecutableGroups_namesNodup _ _ hnodup
      · intro candidate hcandidate
        simp only [List.mem_cons] at hcandidate
        cases hcandidate with
        | inl hcandidate =>
            subst candidate
            exact groupsContained_merge_right leftGroups contribution
        | inr hcandidate =>
            exact groupsContained_merge_left leftGroups contribution _
              (hseen candidate hcandidate)
  | duplicate seen field hfieldSeen rest ih =>
      let contribution :=
        collectFields schema variableValues objectType objectValue field.selectionSet
      apply ih
      · exact hgroups.mergeDuplicatesRight contribution hnodup
          (hseen field hfieldSeen)
      · exact hnodup
      · exact hseen

theorem collectSubfields_firstOccurrences
    (schema : Schema) (variableValues : VariableValues)
    (objectType : Name) (objectValue : ResolverValue ObjectRef)
    (htrace : FirstOccurrences [] leftFields rightFields)
    : GroupFirstOccurrences
        (collectSubfields schema variableValues objectType objectValue leftFields)
        (collectSubfields schema variableValues objectType objectValue rightFields) := by
  rw [← collectSubfieldsFold_nil schema variableValues objectType objectValue
    leftFields]
  rw [← collectSubfieldsFold_nil schema variableValues objectType objectValue
    rightFields]
  exact collectSubfieldsFold_firstOccurrences schema variableValues objectType
    objectValue htrace .nil (by simp [NormalForm.executableGroupNamesNodup])
    (by simp)

mutual
  theorem executeCollectedFields_firstOccurrences
      : ∀ (schema : Schema) (resolvers : Resolvers ObjectRef)
          (variableValues : VariableValues) (fuel : Nat)
          (source : ResolverValue ObjectRef) (left right),
          GroupFirstOccurrences left right
          -> executeCollectedFields schema resolvers variableValues fuel source left
              = executeCollectedFields schema resolvers variableValues fuel source right
    | schema, resolvers, variableValues, fuel, source, [], [], .nil => by
        rfl
    | schema, resolvers, variableValues, fuel, source,
        (responseName, leftFields) :: leftRest,
        (rightResponseName, rightFields) :: rightRest, hgroups => by
        cases hgroups with
        | cons _ fields rest =>
            simp [executeCollectedFields,
              executeField_firstOccurrences schema resolvers variableValues fuel source
                responseName fields,
              executeCollectedFields_firstOccurrences schema resolvers variableValues fuel
                source leftRest rightRest rest]
  termination_by _schema _resolvers _variableValues fuel _source left _right _trace =>
    (fuel, 4, 0, sizeOf left)

  theorem executeField_firstOccurrences
      : ∀ (schema : Schema) (resolvers : Resolvers ObjectRef)
          (variableValues : VariableValues) (fuel : Nat)
          (source : ResolverValue ObjectRef) (responseName : Name)
          {left right : List ExecutableField},
          FirstOccurrences [] left right
          -> executeField schema resolvers variableValues fuel source responseName left
              = executeField schema resolvers variableValues fuel source responseName
                  right
    | schema, resolvers, variableValues, fuel, source, responseName,
        left, right, trace => by
        cases trace with
        | nil => simp [executeField]
        | duplicate seen item hseen rest => simp at hseen
        | keep seen field rest =>
            cases fuel with
            | zero => simp [executeField]
            | succ fuel =>
                cases hlookup : schema.lookupField field.parentType field.fieldName with
                | none => simp [executeField, hlookup]
                | some fieldDefinition =>
                    cases hresolve : resolvers.resolve field.parentType field.fieldName
                      field.arguments source with
                    | none => simp [executeField, hlookup, hresolve]
                    | some resolved =>
                        simp [executeField, hlookup, hresolve,
                          completeValue_firstOccurrences schema resolvers variableValues
                            fuel fieldDefinition.outputType resolved
                            (FirstOccurrences.keep [] field rest)]
  termination_by _schema _resolvers _variableValues fuel _source _responseName left
      _right _trace =>
    (fuel, 3, 0, sizeOf left)

  theorem completeValue_firstOccurrences
      : ∀ (schema : Schema) (resolvers : Resolvers ObjectRef)
          (variableValues : VariableValues) (fuel : Nat) (fieldType : TypeRef)
          (value : ResolverValue ObjectRef) {left right : List ExecutableField},
          FirstOccurrences [] left right
          -> completeValue schema resolvers variableValues fuel fieldType left value
              = completeValue schema resolvers variableValues fuel fieldType right value
    | schema, resolvers, variableValues, 0, fieldType, value, left, right, trace => by
        simp [completeValue]
    | schema, resolvers, variableValues, fuel + 1, .nonNull inner, value,
        left, right, trace => by
        simp [completeValue,
          completeValue_firstOccurrences schema resolvers variableValues (fuel + 1)
            inner value trace]
    | schema, resolvers, variableValues, fuel + 1, .named typeName, .null,
        left, right, trace => by
        simp [completeValue]
    | schema, resolvers, variableValues, fuel + 1, .named typeName, .scalar value,
        left, right, trace => by
        simp [completeValue]
    | schema, resolvers, variableValues, fuel + 1, .named parentType,
        value@(.object runtimeType ref), left, right, trace => by
        by_cases happly : schema.typeIncludesObjectBool parentType runtimeType = true
        · simpa only [completeValue, happly, ↓reduceIte] using
            congrArg (catchBubbleAsNull ResponseValue.object)
              (executeCollectedFields_firstOccurrences schema resolvers variableValues fuel
                (ResolverValue.object runtimeType ref)
                (collectSubfields schema variableValues runtimeType
                  (ResolverValue.object runtimeType ref) left)
                (collectSubfields schema variableValues runtimeType
                  (ResolverValue.object runtimeType ref) right)
                (collectSubfields_firstOccurrences schema variableValues runtimeType
                  (ResolverValue.object runtimeType ref) trace))
        · simp [completeValue, happly]
    | schema, resolvers, variableValues, fuel + 1, .named typeName, .list values,
        left, right, trace => by
        simp [completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner, .list values,
        left, right, trace => by
        simp [completeValue]
        exact congrArg (catchBubbleAsNull ResponseValue.list)
          (completeValueList_firstOccurrences schema resolvers variableValues fuel inner
            values trace)
    | schema, resolvers, variableValues, fuel + 1, .list inner, .null,
        left, right, trace => by
        simp [completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner, .scalar value,
        left, right, trace => by
        simp [completeValue]
    | schema, resolvers, variableValues, fuel + 1, .list inner,
        .object runtimeType ref, left, right, trace => by
        simp [completeValue]
  termination_by _schema _resolvers _variableValues fuel fieldType _value left _right
      _trace =>
    (fuel, 1, sizeOf fieldType, sizeOf left)

  theorem completeValueList_firstOccurrences
      : ∀ (schema : Schema) (resolvers : Resolvers ObjectRef)
          (variableValues : VariableValues) (fuel : Nat) (itemType : TypeRef)
          (values : List (ResolverValue ObjectRef)) {left right : List ExecutableField},
          FirstOccurrences [] left right
          -> completeValueList schema resolvers variableValues fuel itemType left values
              = completeValueList schema resolvers variableValues fuel itemType right
                  values
    | schema, resolvers, variableValues, fuel, itemType, [], left, right, trace => by
        simp [completeValueList]
    | schema, resolvers, variableValues, fuel, itemType, value :: values,
        left, right, trace => by
        simp [completeValueList,
          completeValue_firstOccurrences schema resolvers variableValues fuel itemType
            value trace,
          completeValueList_firstOccurrences schema resolvers variableValues fuel itemType
            values trace]
  termination_by _schema _resolvers _variableValues fuel itemType values left _right
      _trace =>
    (fuel, 2, sizeOf itemType, sizeOf values + sizeOf left)
  decreasing_by
    all_goals
      simp_wf
      repeat first
        | apply Prod.Lex.left; omega
        | apply Prod.Lex.right
      try omega
end

end DuplicateFields
end Execution
end GraphQL
