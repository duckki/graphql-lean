import Proofs.GraphQL.SchemaWellFormedness.PossibleTypes

namespace GraphQL.Tests.SchemaWellFormedness.InterfaceInheritance

private def schema : Schema :=
  {
    queryType := "Object",
    types :=
      [
        .object { name := "Object", fields := [], interfaces := ["Start"] },
        .interface { name := "Start", fields := [], interfaces := ["Middle"] },
        .interface { name := "Middle", fields := [], interfaces := ["Start", "Last"] },
        .interface { name := "Last", fields := [], interfaces := ["Missing"] }
      ]
  }

-- These raw declarations are intentionally cyclic, empty, and dangling. The
-- executable/propositional bridge must not assume schema well-formedness.
theorem cyclicInheritance_reachesParent
    : schema.interfaceTypeImplementsInterface "Start" "Last" := by
  apply (interfaceTypeImplementsInterfaceBool_iff schema "Start" "Last").mp
  decide

theorem danglingTerminal_reachable
    : schema.interfaceTypeImplementsInterface "Start" "Missing" := by
  apply (interfaceTypeImplementsInterfaceBool_iff schema "Start" "Missing").mp
  decide

theorem cycleDoesNotReachUnrelated
    : ¬ schema.interfaceTypeImplementsInterface "Start" "Unrelated" := by
  intro h
  have hfalse := (interfaceTypeImplementsInterfaceBool_iff schema "Start" "Unrelated").mpr h
  have hvalue
      : schema.interfaceTypeImplementsInterfaceBool "Start" "Unrelated" = false := by
    decide
  rw [hvalue] at hfalse
  contradiction

theorem missingIdentity_accepted
    : schema.interfaceTypeImplementsInterfaceBool "Missing" "Missing" = true := by
  exact (interfaceTypeImplementsInterfaceBool_iff schema "Missing" "Missing").mpr (.refl _)

theorem boundIsNecessary
    : schema.interfaceTypeImplementsInterfaceBoundedBool 2 "Start" "Last" = false
      ∧ schema.interfaceTypeImplementsInterfaceBoundedBool 3 "Start" "Last" = true := by
  decide

theorem inheritedObjectImplementation
    : schema.objectTypeImplementsInterface
        { name := "Object", fields := [], interfaces := ["Start"] } "Last" := by
  apply (objectTypeImplementsInterfaceBool_iff schema _ "Last").mp
  decide

theorem nominalSubtype_preservesInheritedPossibleTypes
    : schema.isSubType "Middle" "Last"
      ∧ schema.typeIncludesObjectBool "Middle" "Object" = true
      ∧ schema.typeIncludesObjectBool "Last" "Object" = true := by
  have hsubtype : schema.isSubType "Middle" "Last" := by
    right
    change "Last" ∈ (["Start", "Last"] : List Name)
    simp
  have hinclude : schema.typeIncludesObjectBool "Middle" "Object" = true := by decide
  exact ⟨hsubtype, hinclude, typeIncludesObjectBool_of_isSubType schema hsubtype hinclude⟩

theorem covariantWrappers_preserveInheritedPossibleTypes
    : schema.typeIncludesObjectBool (TypeRef.named "Last").namedType "Object" = true := by
  apply typeIncludesObjectBool_of_outputTypeSubtype_namedType schema
    (implementation := .nonNull (.named "Middle")) (expected := .named "Last")
  · change schema.namedOutputTypeSubtype "Middle" "Last"
    refine ⟨?_, ?_, nominalSubtype_preservesInheritedPossibleTypes.1⟩
    · exact ⟨.interface { name := "Middle", fields := [], interfaces := ["Start", "Last"] },
        rfl, trivial⟩
    · exact ⟨.interface { name := "Last", fields := [], interfaces := ["Missing"] },
        rfl, trivial⟩
  · exact nominalSubtype_preservesInheritedPossibleTypes.2.1

end GraphQL.Tests.SchemaWellFormedness.InterfaceInheritance
