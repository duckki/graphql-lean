import Proofs.GraphQL.SchemaWellFormedness.FieldLookup

/-!
Finite interface-inheritance reachability, including cyclic raw declarations, and
explicit-ancestor and acyclicity consequences of schema well-formedness.
-/

namespace GraphQL

private theorem lookupInterface_type {schema : Schema} {name : Name}
    {interfaceType : InterfaceType}
    (hlookup : schema.lookupInterface name = some interfaceType)
    : schema.lookupType name = some (.interface interfaceType) := by
  cases htype : schema.lookupType name with
  | none => simp [Schema.lookupInterface, htype] at hlookup
  | some typeDefinition =>
      cases typeDefinition <;> simp [Schema.lookupInterface, htype] at hlookup
      case interface candidate =>
        subst candidate
        rfl

private theorem lookupInterface_name_mem {schema : Schema} {name : Name}
    {interfaceType : InterfaceType}
    (hlookup : schema.lookupInterface name = some interfaceType)
    : name ∈ schema.types.map TypeDefinition.name := by
  have htype := lookupInterface_type hlookup
  have hname : interfaceType.name = name := by
    simpa [TypeDefinition.name] using List.find?_some htype
  have hmem : .interface interfaceType ∈ schema.allTypes :=
    List.mem_of_find?_eq_some htype
  have hmem' : .interface interfaceType ∈ schema.types := by
    simpa [Schema.builtinScalarDefinitions] using List.mem_append.mp hmem
  exact hname ▸ List.mem_map.mpr ⟨.interface interfaceType, hmem', rfl⟩

-- The list records edge sources, excluding the terminal name. Removing a cycle
-- therefore leaves at most one source per schema declaration.
private inductive InterfacePath (schema : Schema)
    : Name -> Name -> List Name -> Prop where
  | refl (name : Name) : InterfacePath schema name name []
  | step {source parent target : Name} {interfaceType : InterfaceType} {path : List Name}
    (hlookup : schema.lookupInterface source = some interfaceType)
    (hparent : parent ∈ interfaceType.interfaces)
    (htail : InterfacePath schema parent target path)
    : InterfacePath schema source target (source :: path)

private theorem InterfacePath.suffix {schema : Schema} {source target name : Name}
    {path : List Name} (hpath : InterfacePath schema source target path)
    (hmem : name ∈ path)
    : ∃ suffix, InterfacePath schema name target suffix ∧ suffix.Sublist path := by
  induction hpath with
  | refl => simp at hmem
  | @step source parent target interfaceType path hlookup hparent htail ih =>
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst name
        exact ⟨source :: path, .step hlookup hparent htail, .refl _⟩
      · rcases ih hmem with ⟨suffix, hsuffix, hsublist⟩
        exact ⟨suffix, hsuffix, hsublist.cons source⟩

private theorem interfaceInheritance_simplePath {schema : Schema} {source target : Name}
    (h : schema.interfaceTypeImplementsInterface source target)
    : ∃ path, InterfacePath schema source target path ∧ path.Nodup := by
  induction h with
  | refl name => exact ⟨[], .refl name, by simp⟩
  | trans source target interfaceType parent hlookup hparent htail ih =>
      rcases ih with ⟨path, hpath, hnodup⟩
      by_cases hmem : source ∈ path
      · rcases hpath.suffix hmem with ⟨suffix, hsuffix, hsublist⟩
        exact ⟨suffix, hsuffix, hsublist.nodup hnodup⟩
      · exact ⟨source :: path, .step hlookup hparent hpath,
          List.nodup_cons.mpr ⟨hmem, hnodup⟩⟩

private theorem InterfacePath.names {schema : Schema} {source target : Name}
    {path : List Name} (hpath : InterfacePath schema source target path)
    : path ⊆ schema.types.map TypeDefinition.name := by
  induction hpath with
  | refl => simp
  | step hlookup hparent htail ih =>
      intro name hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact lookupInterface_name_mem hlookup
      · exact ih hmem

theorem interfaceTypeImplementsInterfaceBoundedBool_mono (schema : Schema)
    {bound larger : Nat} {source target : Name}
    (hle : bound ≤ larger)
    (h : schema.interfaceTypeImplementsInterfaceBoundedBool bound source target = true)
    : schema.interfaceTypeImplementsInterfaceBoundedBool larger source target = true := by
  induction bound generalizing larger source with
  | zero => simp [Schema.interfaceTypeImplementsInterfaceBoundedBool] at h
  | succ bound ih =>
      cases larger with
      | zero => omega
      | succ larger =>
          simp only [Schema.interfaceTypeImplementsInterfaceBoundedBool,
            Bool.or_eq_true, beq_iff_eq] at h ⊢
          rcases h with rfl | h
          · exact Or.inl rfl
          · right
            cases hlookup : schema.lookupInterface source with
            | none => simp [hlookup] at h
            | some interfaceType =>
                simp only [hlookup, List.any_eq_true] at h ⊢
                rcases h with ⟨parent, hparent, htail⟩
                exact ⟨parent, hparent, ih (by omega) htail⟩

theorem interfaceTypeImplementsInterfaceBoundedBool_sound (schema : Schema)
    {bound : Nat} {source target : Name}
    (h : schema.interfaceTypeImplementsInterfaceBoundedBool bound source target = true)
    : schema.interfaceTypeImplementsInterface source target := by
  induction bound generalizing source with
  | zero => simp [Schema.interfaceTypeImplementsInterfaceBoundedBool] at h
  | succ bound ih =>
      simp only [Schema.interfaceTypeImplementsInterfaceBoundedBool,
        Bool.or_eq_true, beq_iff_eq] at h
      rcases h with rfl | h
      · exact .refl _
      · cases hlookup : schema.lookupInterface source with
        | none => simp [hlookup] at h
        | some interfaceType =>
            simp only [hlookup, List.any_eq_true] at h
            rcases h with ⟨parent, hparent, htail⟩
            exact .trans source target interfaceType parent hlookup hparent (ih htail)

private theorem InterfacePath.bounded {schema : Schema} {source target : Name}
    {path : List Name} (hpath : InterfacePath schema source target path)
    : schema.interfaceTypeImplementsInterfaceBoundedBool (path.length + 1) source target
      = true := by
  induction hpath with
  | refl => simp [Schema.interfaceTypeImplementsInterfaceBoundedBool]
  | step hlookup hparent htail ih =>
      simp only [List.length_cons]
      rw [Schema.interfaceTypeImplementsInterfaceBoundedBool, Bool.or_eq_true]
      right
      rw [hlookup]
      exact List.any_eq_true.mpr ⟨_, hparent, ih⟩

theorem interfaceTypeImplementsInterfaceBool_iff (schema : Schema) (source target : Name)
    : schema.interfaceTypeImplementsInterfaceBool source target = true
      ↔ schema.interfaceTypeImplementsInterface source target := by
  constructor
  · exact interfaceTypeImplementsInterfaceBoundedBool_sound schema
  · intro h
    rcases interfaceInheritance_simplePath h with ⟨path, hpath, hnodup⟩
    have hlength : path.length ≤ schema.types.length := by
      simpa using hnodup.length_le_of_subset hpath.names
    exact interfaceTypeImplementsInterfaceBoundedBool_mono schema
      (by omega) hpath.bounded

theorem objectTypeImplementsInterfaceBool_iff (schema : Schema)
    (objectType : ObjectType) (target : Name)
    : schema.objectTypeImplementsInterfaceBool objectType target = true
      ↔ schema.objectTypeImplementsInterface objectType target := by
  simp only [Schema.objectTypeImplementsInterfaceBool, List.any_eq_true,
    Schema.objectTypeImplementsInterface, interfaceTypeImplementsInterfaceBool_iff]

theorem interfaceTypeImplementsInterface_trans {schema : Schema}
    {source middle target : Name}
    (hleft : schema.interfaceTypeImplementsInterface source middle)
    (hright : schema.interfaceTypeImplementsInterface middle target)
    : schema.interfaceTypeImplementsInterface source target := by
  induction hleft with
  | refl => exact hright
  | trans source middle interfaceType parent hlookup hparent htail ih =>
      exact .trans source target interfaceType parent hlookup hparent (ih hright)

namespace SchemaWellFormedness

theorem interfacesIncludeInherited_reachable {schema : Schema} {interfaces : List Name}
    (hclosed : interfacesIncludeInherited schema interfaces) {source target : Name}
    (hreach : schema.interfaceTypeImplementsInterface source target)
    : source ∈ interfaces -> target ∈ interfaces := by
  induction hreach with
  | refl => exact id
  | trans source target interfaceType parent hlookup hparent _hrest ih =>
      intro hsource
      exact ih (hclosed source hsource interfaceType hlookup hparent)

theorem objectTypeWellFormed_reachableInterface_declared
    {schema : Schema} {objectType : ObjectType} {source target : Name}
    (hobject : objectTypeWellFormed schema objectType)
    (hsource : source ∈ objectType.interfaces)
    (hreach : schema.interfaceTypeImplementsInterface source target)
    : target ∈ objectType.interfaces :=
  interfacesIncludeInherited_reachable hobject.2.2.2 hreach hsource

theorem interfaceTypeWellFormed_reachableInterface_declared
    {schema : Schema} {interfaceType : InterfaceType} {source target : Name}
    (hinterface : interfaceTypeWellFormed schema interfaceType)
    (hsource : source ∈ interfaceType.interfaces)
    (hreach : schema.interfaceTypeImplementsInterface source target)
    : target ∈ interfaceType.interfaces :=
  interfacesIncludeInherited_reachable hinterface.2.2.2.2 hreach hsource

-- Reachability is reflexive on raw names. A cycle needs an initial declared edge,
-- followed by any (possibly reflexive) return path to the implementing interface.
theorem interfaceTypeWellFormed_noInheritanceCycle
    {schema : Schema} {interfaceType : InterfaceType} {parent : Name}
    (hinterface : interfaceTypeWellFormed schema interfaceType)
    (hparent : parent ∈ interfaceType.interfaces)
    : ¬ schema.interfaceTypeImplementsInterface parent interfaceType.name := by
  intro hreturn
  exact hinterface.2.2.2.1
    (interfaceTypeWellFormed_reachableInterface_declared hinterface hparent hreturn)

theorem schemaWellFormed_interface_noInheritanceCycle
    {schema : Schema} {name parent : Name} {interfaceType : InterfaceType}
    (hschema : schemaWellFormed schema)
    (hlookup : schema.lookupInterface name = some interfaceType)
    (hparent : parent ∈ interfaceType.interfaces)
    : ¬ schema.interfaceTypeImplementsInterface parent name := by
  have htype := lookupInterface_type hlookup
  have hname : interfaceType.name = name := by
    simpa [TypeDefinition.name] using List.find?_some htype
  have hinterface : interfaceTypeWellFormed schema interfaceType :=
    schemaWellFormed_lookupType_typeDefinitionWellFormed hschema htype
  simpa [hname] using interfaceTypeWellFormed_noInheritanceCycle hinterface hparent

end SchemaWellFormedness

end GraphQL
