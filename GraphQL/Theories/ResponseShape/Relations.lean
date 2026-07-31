import GraphQL.Theories.ResponseShape.Correspondence

/-!
Subset and equivalence relations for operation response shapes.

`ShapeSubset schema required provided` is oriented from a client-required shape
to a candidate-provided shape. It compares every complete Boolean assignment
over the combined source support. The executable comparator enumerates these
assignments with an explicit `2^n` case cost for `n` distinct variables in that
union, before traversing the paths represented by either shape.

The relation keeps the required path exact and places its semantic-path
envelope only on the provided side. This preserves a concrete required path as
a rejection witness while respecting field collection's semantic argument
comparison. In particular, the envelope retains
`Argument.argumentsEquivalent` as defined (bilateral set containment, without
a multiplicity or list-permutation strengthening). These definitions do not
assume symmetry or transitivity of the path envelope; those properties are
proved separately from this public relation slice.
-/

namespace GraphQL

namespace ResponseShape

/-- The duplicate-free Boolean support needed to evaluate either shape. -/
def supportUnion (left right : List NormalForm.BoolVar) : List NormalForm.BoolVar :=
  NormalForm.dedupBoolVars (left ++ right)

/-- Extensional equality of Boolean supports. List order is not observable. -/
def BoolSupportEquivalent (left right : List NormalForm.BoolVar) : Prop :=
  ∀ varName, varName ∈ left ↔ varName ∈ right

/--
Every exact path required by `required` has a semantically equivalent path in
`provided`, under every complete assignment covering both source supports.

The operation-type header equality is automatic while `OperationType` contains
only `.query`; the corresponding mismatch result is unreachable in the current
model.
Root-type equality keeps both sides in the same GraphQL response domain.
Completeness over `supportUnion` ensures that no source Boolean variable used
by either side is left unassigned. Exact
`DenotesPath` on the required side retains the concrete counterexample path;
`DenotesEquivalentPath` on the provided side is the narrow envelope needed
because GraphQL field collection ignores argument and input-object field order.
No well-formedness premise is embedded here: callers that need provenance or
executable guarantees supply those facts at their own trust boundary.
-/
def ShapeSubset (schema : Schema) (required provided : OperationShape) : Prop :=
  required.operationType = provided.operationType
  ∧ required.rootType = provided.rootType
  ∧ ∀ assignment,
      NormalForm.completeNormalBoolCase
        (supportUnion required.boolSupport provided.boolSupport) assignment
      → ∀ path,
          required.root.DenotesPath schema assignment required.rootType path
          → provided.root.DenotesEquivalentPath schema assignment provided.rootType path

/-- Mutual response-footprint inclusion. -/
def ShapeEquivalent (schema : Schema) (left right : OperationShape) : Prop :=
  ShapeSubset schema left right ∧ ShapeSubset schema right left

/--
Footprint equivalence together with equality of source Boolean support.

The explicit support conjunct preserves the current complete normalizer's
non-minimizing canonicity contract: a semantically redundant source variable is
still observable here even when it does not change the response footprint.
-/
def StrictShapeEquivalent (schema : Schema) (left right : OperationShape) : Prop :=
  ShapeEquivalent schema left right
  ∧ BoolSupportEquivalent left.boolSupport right.boolSupport

end ResponseShape

end GraphQL
