import GraphQL.Schema
import GraphQL.Operation
import GraphQL.Validation
import GraphQL.SchemaWellFormedness
import GraphQL.Execution
import GraphQL.NamedFragment.Operation
import GraphQL.NamedFragment.Validation
import GraphQL.NamedFragment.Execution
import GraphQL.NamedFragment.Inline
import GraphQL.NamedFragment.Translate
import GraphQL.Algorithms.Common
import GraphQL.Algorithms.ExecutionCancelingSiblings
import GraphQL.Algorithms.ExecutionBreadth
import GraphQL.Algorithms.ExecutionUngrouped
import GraphQL.Theories.NormalForm
import GraphQL.Theories.ResponseShape

/-!
Spec reference: GraphQL September 2025.
- 2 Language, 3 Type System, 5 Validation, 6 Execution, and 7 Response: this root module
  re-exports the partial GraphQL formalization modules.
- This root module intentionally imports only public definition surfaces. Import `Proofs`
  or localized `Proofs.GraphQL.*` modules when working with theorem surfaces.
- Import order follows the intended reading order for the scoped model: schema and
  validation, execution, named fragments, public algorithms, then public theory modules.
-/
