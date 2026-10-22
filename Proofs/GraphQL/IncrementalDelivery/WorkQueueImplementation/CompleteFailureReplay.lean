import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.FailureRetentionReplay
import Proofs.GraphQL.IncrementalDelivery.WorkQueueImplementation.CompleteFailureAccounting

/-! The replay boundary uses the success-only counter ledger and retained task rejections.
`ExecutedWork.runNormalized_retainedFailures` derives both retention and fresh-ref exclusion
from generated work, valid source events, and actual task-start eligibility.
-/
