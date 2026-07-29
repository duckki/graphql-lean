import GraphQL.Operation

/-! Fragment-aware GraphQL operation syntax.

This module deliberately does not change `GraphQL.Operation`. It defines a
separate operation surface for named-fragment work while reusing the existing
schema, argument, variable, and directive syntax.
-/

namespace GraphQL
namespace NamedFragment

-- Spec 2.5-2.9 selection syntax extended with named fragment spreads.
inductive Selection where
  | field
    (responseName : Name)
    (fieldName : Name)
    (arguments : List Argument)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
  | inlineFragment
    (typeCondition : Option Name)
    (directives : List DirectiveApplication)
    (selectionSet : List Selection)
  | fragmentSpread (fragmentName : Name) (directives : List DirectiveApplication)
deriving Repr

-- Spec 2.9.1 fragment definitions, restricted to the modeled executable subset.
structure FragmentDefinition where
  name : Name
  typeCondition : Name
  selectionSet : List Selection
deriving Repr

-- Single query operation plus the fragment definitions it can reference.
structure Operation where
  name : Option Name := none
  operationType : OperationType := .query
  variableDefinitions : List VariableDefinition := []
  fragmentDefinitions : List FragmentDefinition := []
  selectionSet : List Selection
deriving Repr

namespace Operation

def rootType (operation : Operation) (schema : Schema) : Name :=
  operation.operationType.rootType schema

end Operation

mutual
  -- Non-spec structural metric used by bounded transformations.
  def Selection.size : Selection -> Nat
    | .field _ _ _ _ selectionSet => 1 + SelectionSet.size selectionSet
    | .inlineFragment _ _ selectionSet => 1 + SelectionSet.size selectionSet
    | .fragmentSpread _ _ => 1

  def SelectionSet.size : List Selection -> Nat
    | [] => 0
    | selection :: rest => selection.size + SelectionSet.size rest
end

def FragmentDefinition.size (fragment : FragmentDefinition) : Nat :=
  SelectionSet.size fragment.selectionSet

def FragmentDefinitionList.size : List FragmentDefinition -> Nat
  | [] => 0
  | fragment :: rest => fragment.size + FragmentDefinitionList.size rest

def Operation.size (operation : Operation) : Nat :=
  SelectionSet.size operation.selectionSet
  + FragmentDefinitionList.size operation.fragmentDefinitions

def lookupFragment? (fragments : List FragmentDefinition) (name : Name)
    : Option FragmentDefinition :=
  fragments.find? (fun fragment => fragment.name == name)

def lookupFragmentAndRestLt? (fragmentName : Name)
    : (fragments : List FragmentDefinition)
      -> Option
          (FragmentDefinition
            × { remaining : List FragmentDefinition
                // remaining.length < fragments.length })
  | [] => none
  | fragment :: rest =>
      if fragment.name == fragmentName then
        some (fragment, ⟨rest, by simp⟩)
      else
        match lookupFragmentAndRestLt? fragmentName rest with
        | none => none
        | some (found, remaining) =>
            some (found, ⟨fragment :: remaining.val, by
              have hlt := remaining.property
              simp at hlt ⊢
              omega⟩)

end NamedFragment
end GraphQL
