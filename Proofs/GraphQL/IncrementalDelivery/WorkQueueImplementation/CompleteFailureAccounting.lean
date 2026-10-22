import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionSettlement

/-! Failure accounting follows retained rejected tasks, with no group-level error sum.
`State.RetainedFailures` supplies contributor retention and fresh-ref exclusion; selected
numeric causes are certified separately by `GroupFailureSourceCause`.
-/
