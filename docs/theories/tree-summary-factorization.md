# Factoring Syntactic Tree-Summary Cases

`TreeSummary.Syntactic` summarizes every immediate branch once, then reuses that
summary in a node-local case circuit. Type and Boolean branches use separate circuits:
type conditions are selected by materializable symbolic runtime-type regions, while
Boolean conditions are factored directly by variable. The two families are combined,
never multiplied into a Cartesian product.

## Why factor cases?

At one condition-tree node, several sibling branches can be active together. Joining
every branch independently is unsound because it treats simultaneous contributions as
alternatives. Combining every branch is sound but pessimistically assumes they are all
active together.

Write `+` for `Algebra.join` and `*` for `Algebra.combine`. A correct local summary has
the shape of a monotone sum of products: products contain simultaneous contributions,
and sums separate runtime alternatives. This is the same control shape used by
provenance polynomials and factorized query results, although a tree-summary algebra is
not required to satisfy semiring laws. See Green, Karvounarakis, and Tannen's
[Provenance Semirings](https://www.cs.ucdavis.edu/~green/papers/pods07.pdf) and Olteanu
and Závodný's
[Factorised Representations of Query Results](https://arxiv.org/abs/1104.0867).

## Boolean alternatives

Every immediate Boolean edge contains one literal. The executable traversal therefore
does not enumerate complete assignments or build activation masks. It collects branch
summaries into a syntax-ordered association list:

```text
variable x
  false -> combine every @skip(if: $x) contribution
  true  -> combine every @include(if: $x) contribution
```

For an unresolved variable, the two present alternatives are joined. For a supplied
value, only the matching alternative is retained. Results for distinct variables are
combined because the condition-tree invariant makes immediate Boolean variables
independent at that node. A missing side is represented by `none`, not by
`Algebra.empty`: no branch for one value is absence of an alternative, whereas `empty`
is the identity of a simultaneous product.

The executable pieces are:

- `BooleanBranchSummary`, one widened summary paired with its literal;
- `BooleanAlternatives`, the optional false and true products for one variable;
- `collectBooleanAlternatives`, the direct per-variable fold;
- `summarizeBooleanBranchSummaries`, known-value selection or unknown-value join.

The coverage proof chooses an arbitrary concrete Boolean assignment, selects exactly its
matching branch summaries, and proves that product lies below the direct circuit. This
uses only `Algebra.Lawful`: `combine` is a commutative monoid and monotone, `empty` is
least, and `join` bounds both inputs. It does not require distributivity or least joins.

## Type alternatives

Each `TypeBranchSummary` stores the cumulative possible-type set already cached on the
branch body and one widened recursive summary. Their possible-type sets refine the node
scope into nonempty equivalence regions. Object types remain together precisely when
they activate the same immediate type branches. `summarizeTypeBranchRegion?` evaluates
one representative per region, and `summarizeTypeRuntimeCases` joins the active products.

This is not summary-value deduplication. Different materializable activation products
are kept even when a particular algebra maps them to equal summaries. The construction
therefore requires neither decidable equality on `Summary` nor idempotence of
`Algebra.join`. Region refinement scans the finite object-type scope under each cached
condition rather than enumerating a raw powerset; its number of evaluated products is at
most the number of object types and can be much smaller.

The proof theorem `summarizeImmediateBranches_cardinality_le` states the structural
compactness guarantee: the type- and Boolean-family lengths sum to at most the number of
input branches. Thus the node compiler cannot duplicate one source branch across the two
families; infeasible and known-false branches make the inequality strict.

## Widening and precision

A syntactic branch can occur in several refined runtime cases, so its recursive summary
would not literally be the same factor in every fully expanded product. The fast backend
first performs a deliberate widening:

- a type branch is summarized under the incoming scope intersected with the cumulative
  possible-type set stored on its body;
- a Boolean branch is summarized under the incoming values, leaving unresolved local
  variables unknown;
- child traversal resolves conditions below that widened branch context.

The runtime-coverage proof shows that each widened branch summary covers every concrete
occurrence. Equality with a fully expanded traversal is not claimed. The exact-case
backend remains the choice when cross-branch correlation and global response-name
grouping are required.

## Proof boundary

`Proofs.GraphQL.Theories.TreeSummary.Syntactic.Factorization` contains the compactness
theorem and algebraic Boolean coverage lemmas. `Syntactic.Coverage.RuntimeSummary`
relates a concrete runtime assignment and runtime object type directly to the compact
branch summaries selected by the tree traversal, and
`Syntactic.Coverage.FactorizedCase` lifts both local case families through recursive
tree summarization.

The proof keeps three responsibilities separate:

1. condition-tree extraction establishes feasible, coherent branch structure;
2. the syntactic backend compiles local type and Boolean alternatives;
3. the algebra interprets simultaneous composition and alternative joins.
