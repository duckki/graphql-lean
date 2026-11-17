import GraphQL.Execution
import Proofs.GraphQL.Schema.Typename

/-! Built-in type-name resolution and its resolver-argument law. -/

namespace GraphQL.Execution

theorem resolveFieldValue_typename (resolvers : Resolvers ObjectRef) (parentType : Name)
    (arguments : CoercedArguments) (source : ResolverValue ObjectRef)
    : resolveFieldValue resolvers parentType "__typename" arguments source
      = resolveTypenameField source := by
  rfl

theorem resolveFieldValue_argumentsEquivalent (resolvers : Resolvers ObjectRef)
    (parentType fieldName : Name) (firstArguments laterArguments : CoercedArguments)
    (source : ResolverValue ObjectRef)
    (hargs : CoercedArgument.argumentsEquivalent firstArguments laterArguments)
    : resolveFieldValue resolvers parentType fieldName firstArguments source
      = resolveFieldValue resolvers parentType fieldName laterArguments source := by
  unfold resolveFieldValue
  split
  · rfl
  · exact resolvers.resolve_argumentsEquivalent _ _ _ _ _ hargs

theorem executeField_typename (schema : Schema) (resolvers : Resolvers ObjectRef)
    (values : VariableValues) (fuel : Nat) (parentType runtimeType responseName : Name)
    (ref : ObjectRef) (arguments : List Argument) (children : List Selection)
    (fields : List ExecutableField) (hparent : schema.isCompositeType parentType)
    : executeField schema resolvers values (fuel + 2) parentType (.object runtimeType ref)
        responseName
        ({ fieldName := "__typename", arguments, selectionSet := children } :: fields)
      = .ok ([(responseName, .scalar runtimeType)], 0) := by
  have hlookup := Schema.lookupField_typename hparent
  simp [executeField, hlookup, Schema.typenameFieldDefinition, coerceArgumentValues,
    resolveFieldValue, resolveTypenameField, completeValue, nonNullCompletion,
    TypeRef.isCompositeBool, Schema.lookupType, Schema.allTypes, Schema.builtinScalarDefinitions,
    TypeDefinition.name, BuiltinScalar.name, TypeRef.namedType, List.find?,
    singleFieldResult]

theorem executeField_typename_eq {LeftRef RightRef : Type} (schema : Schema)
    (left : Resolvers LeftRef) (right : Resolvers RightRef) (values : VariableValues)
    (fuel : Nat) (parentType responseName : Name) (leftSource : ResolverValue LeftRef)
    (rightSource : ResolverValue RightRef) (arguments : List Argument)
    (children : List Selection) (fields : List ExecutableField)
    (hsources : runtimeObjectType? leftSource = runtimeObjectType? rightSource)
    : executeField schema left values fuel parentType leftSource responseName
        ({ fieldName := "__typename", arguments, selectionSet := children } :: fields)
      = executeField schema right values fuel parentType rightSource responseName
          ({ fieldName := "__typename", arguments, selectionSet := children }
            :: fields) := by
  cases fuel with
  | zero => simp [executeField]
  | succ fuel =>
      cases hlookup : schema.lookupField parentType "__typename" with
      | none => simp [executeField, hlookup]
      | some definition =>
          rcases Schema.lookupField_eq_some_cases hlookup with ⟨_, rfl, _⟩ | ⟨hne, _⟩
          · cases fuel <;> cases leftSource <;> cases rightSource <;>
              simp_all [runtimeObjectType?, executeField, Schema.typenameFieldDefinition,
                coerceArgumentValues, resolveFieldValue, resolveTypenameField, completeValue,
                nonNullCompletion, singleFieldResult, handleFieldError, TypeRef.isCompositeBool,
                TypeRef.namedType, Schema.lookupType, Schema.allTypes,
                Schema.builtinScalarDefinitions, TypeDefinition.name, BuiltinScalar.name, List.find?]
          · exact False.elim (hne rfl)

end GraphQL.Execution
