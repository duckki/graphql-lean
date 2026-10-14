import Proofs.GraphQL.IncrementalDelivery.WorkQueueAlternativeImpl.FusedRemovalAccounting

/-! Exact accounting projection and independently derived generated-prefix premises.
Task-node correspondence, handler/replay lifting and native resource acquisition are not
assumed or certified by these accounting-only targets.
-/

namespace AlternativeFusedRemovalAccountingChecks
open GraphQL.IncrementalDelivery.AlternativeWorkQueue

example : FusedRemovalAccounting := FusedRemovalAccounting_holds
example : GeneratedReferenceRemovalAccounting := GeneratedReferenceRemovalAccounting_holds

#print axioms ownerlessTask_membership_absent
#print axioms removeOwnerlessTask_eq
#print axioms removeGroup_walk_accounting
#print axioms FusedRemovalAccounting_holds
#print axioms GeneratedReferenceRemovalAccounting_holds

end AlternativeFusedRemovalAccountingChecks
