import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Collection

/-!
Resolver facts for the batched breadth resolver adapter.
-/

namespace GraphQL

namespace Algorithms
namespace ExecutionBreadth

open GraphQL.Execution

variable {ObjectRef : Type}

theorem fromSpecResolvers_resolve_eq_map
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (parentType fieldName : Name) (arguments : CoercedArguments)
    (sources : List (ResolverValue ObjectRef))
    : (ResolverMap.fromSpecResolvers resolvers).resolve parentType fieldName
        arguments sources
      = sources.map
          (fun source => resolvers.resolve parentType fieldName arguments source) := by
  rfl

theorem fromSpecResolvers_resolve_length
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (parentType fieldName : Name) (arguments : CoercedArguments)
    (sources : List (ResolverValue ObjectRef))
    : ((ResolverMap.fromSpecResolvers resolvers).resolve parentType fieldName
        arguments sources).length
      = sources.length := by
  simp [fromSpecResolvers_resolve_eq_map]

theorem fromSpecResolvers_resolve_nil
    (resolvers : GraphQL.Execution.Resolvers ObjectRef)
    (parentType fieldName : Name) (arguments : CoercedArguments)
    : (ResolverMap.fromSpecResolvers resolvers).resolve parentType fieldName arguments []
      = [] := by
  rfl

end ExecutionBreadth

end Algorithms

end GraphQL
