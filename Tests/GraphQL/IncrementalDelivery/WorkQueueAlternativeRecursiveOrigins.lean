import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginPlanComposition
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.OriginListComposition
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveOriginCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.PairedOriginCoverage
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveCutAccounting
import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.RecursiveRecordingCorrespondence

/-! Exact construction-graph consumers. Metadata premises describe allocated
inputs; these low-fuel constructions have no related-output or child-coverage premise. -/

namespace AlternativeRecursiveOriginChecks

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.AlternativeWorkQueue.NativeRefinement
open OriginAccounting ScheduledWork

example : RecursiveOriginCoverage := recursiveOriginCoverage_holds
example : RecursiveOriginSubsequence := recursiveOriginSubsequence_holds
example : PairedOriginCoverage := pairedOriginCoverage_holds
example : RecursiveCutConstruction := recursiveCutConstruction_holds
example : RecursiveCutAccounting := recursiveCutAccounting_holds
example : RecursiveRecordingCorrespondence := recursiveRecordingCorrespondence_holds

example (schema : GraphQL.Schema) (resolvers : Resolvers ObjectRef) variables fuel
    : ValueOriginsConstruction schema resolvers variables fuel :=
  valueOriginsConstruction_holds schema resolvers variables fuel

example (schema : GraphQL.Schema) (resolvers : Resolvers ObjectRef) variables fuel
    : FieldOriginsConstruction schema resolvers variables fuel :=
  fieldOriginsConstruction_holds schema resolvers variables fuel

example (schema : GraphQL.Schema) (resolvers : Resolvers ObjectRef) variables fuel
    : PlanOriginsConstruction schema resolvers variables fuel :=
  planOriginsConstruction_holds schema resolvers variables fuel

example (schema : GraphQL.Schema) (resolvers : Resolvers ObjectRef) variables
    : ValueOriginsConstruction schema resolvers variables 0 :=
  valueOrigins_zero schema resolvers variables

example (schema : GraphQL.Schema) (resolvers : Resolvers ObjectRef) variables
    : FieldOriginsConstruction schema resolvers variables 1 :=
  fields_origins_of_values schema resolvers variables 1
    (valueOrigins_zero schema resolvers variables)

example (schema : GraphQL.Schema) (resolvers : Resolvers ObjectRef) variables
    : PlanOriginsConstruction schema resolvers variables 0 :=
  plan_origins_of_fields schema resolvers variables 0
    (fields_origins_of_values schema resolvers variables 0
      (valueOrigins_zero schema resolvers variables))

#print axioms value_mapped_run
#print axioms fields_mapped_run
#print axioms valueOrigins_zero
#print axioms fields_origins_of_values
#print axioms groups_origins_of_fields
#print axioms object_origins_of_plan
#print axioms listWithStream_origins_of_values
#print axioms valueOriginsConstruction_holds
#print axioms fieldOriginsConstruction_holds
#print axioms planOriginsConstruction_holds
#print axioms recursiveOriginCoverage_holds
#print axioms recursiveOriginSubsequence_holds
#print axioms pairedOriginCoverage_holds
#print axioms recursiveCutConstruction_holds
#print axioms recursiveCutAccounting_holds
#print axioms recursiveRecordingCorrespondence_holds

end AlternativeRecursiveOriginChecks
