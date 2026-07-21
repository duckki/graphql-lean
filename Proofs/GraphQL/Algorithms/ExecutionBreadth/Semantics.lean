import GraphQL.Algorithms.ExecutionBreadth
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Invariants
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Resolver
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Slots
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Scope
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Queue
import Proofs.GraphQL.Algorithms.ExecutionBreadth.Semantics.Final

/-!
Semantic surface for the breadth execution algorithm.

The executable breadth model schedules field batches by `ScheduleKey` and keeps child
continuations on `ScheduleSegment`s. This proof-facing surface exposes collection,
resolver-adapter, slot-completion, scope-scheduling, queue-drain, and final
query-envelope facts, including the completed preservation theorem for the public
runtime proposition.
-/
