import Proofs.GraphQL.IncrementalDelivery.Correctness.SourcePositions
import Proofs.GraphQL.IncrementalDelivery.Correctness.Query
import Proofs.GraphQL.IncrementalDelivery.Semantics.WireLeafPositions

/-! Basic response positions are unique, independently of incremental scheduling. -/

namespace GraphQL.IncrementalDelivery.Correctness.BasicPositions
open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Semantics

/-- Embed one ordinary directive without introducing incremental syntax. -/
def liftDirective : GraphQL.DirectiveApplication → DirectiveApplication
  | .skip condition => .skip condition
  | .include condition => .include condition

mutual
  /-- Embed an ordinary selection while retaining aliases, arguments, and conditions. -/
  def liftSelection : GraphQL.Selection → Selection
    | .field name field arguments directives children =>
        .field name field arguments (directives.map liftDirective)
          (liftSelections children)
    | .inlineFragment condition directives children =>
        .inlineFragment condition (directives.map liftDirective) (liftSelections children)

  /-- Embed the ordinary selection list in its original order. -/
  def liftSelections : List GraphQL.Selection → List Selection
    | [] => []
    | selection :: rest => liftSelection selection :: liftSelections rest
end

/-- Erasing an embedded directive list is identity, by directive-list induction. -/
theorem lift_directives_erase (directives : List GraphQL.DirectiveApplication)
    : ((directives.map liftDirective).filterMap DirectiveApplication.eraseIncremental?)
      = directives := by
  induction directives with
  | nil => rfl
  | cons directive rest ih =>
      cases directive <;> simp [liftDirective, DirectiveApplication.eraseIncremental?, ih]

/-- Embedded directives are all ordinary, by their two constructors. -/
theorem lift_directives_plain (directives : List GraphQL.DirectiveApplication)
    : DirectivesPlain (directives.map liftDirective) := by
  induction directives with
  | nil => rfl
  | cons directive rest ih =>
      cases directive <;>
        simp_all [DirectivesPlain, liftDirective, DirectiveApplication.isIncremental]

mutual
  /-- Erasure inverts a selection's embedding, by mutual syntax induction. -/
  theorem lift_selection_erase (selection : GraphQL.Selection)
      : (liftSelection selection).eraseIncrementalDirectives = selection := by
    cases selection <;>
      simp only [liftSelection, Selection.eraseIncrementalDirectives,
        lift_directives_erase, lift_selections_erase]

  /-- Erasure inverts the selection-list embedding, by mutual syntax induction. -/
  theorem lift_selections_erase (selections : List GraphQL.Selection)
      : SelectionSet.eraseIncrementalDirectives (liftSelections selections)
        = selections := by
    cases selections <;>
      simp [liftSelections, SelectionSet.eraseIncrementalDirectives, lift_selection_erase,
        lift_selections_erase]
end

mutual
  /-- An embedded selection has no incremental directives, including in descendants. -/
  theorem lift_selection_plain (selection : GraphQL.Selection)
      : (liftSelection selection).hasIncrementalDirectives = false := by
    cases selection <;>
      simp only [liftSelection, Selection.hasIncrementalDirectives, lift_directives_plain,
        lift_selections_plain, Bool.false_or]

  /-- Embedded selection lists satisfy directive-free execution's premise. -/
  theorem lift_selections_plain (selections : List GraphQL.Selection)
      : SelectionsPlain (liftSelections selections) := by
    cases selections <;>
      simp [liftSelections, SelectionsPlain, SelectionSet.hasIncrementalDirectives,
        lift_selection_plain, lift_selections_plain]
end

/-- Every basic root response has unique paths, with or without containers. Witness:
embed syntax, use plain execution equality and disjoint source positions, then drop
container positions if requested. No validation or successful-execution premise is used.
-/
theorem rootResponse_nodup (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (fuel : Nat) (parentType : Name)
    (source : ResolverValue ObjectRef) (selections : List GraphQL.Selection)
    (containers : Bool)
    : (ResponsePositions.value containers []
        (GraphQL.Execution.selectionSetResultToResponse
          (GraphQL.Execution.executeRootSelectionSet schema resolvers variables fuel
            parentType source selections)).data).Nodup := by
  have plain := executeRootSelectionSetCore_plain schema resolvers variables fuel
    parentType source (liftSelections selections) (lift_selections_plain selections) 0
  obtain ⟨_, _, positions⟩ := executeRoot_source_positions schema resolvers variables fuel
    parentType source (liftSelections selections) 0
  have unique := (List.nodup_append.mp positions).1
  have equal := plain.2.1
  rw [lift_selections_erase] at equal
  rw [equal] at unique
  cases containers with
  | true => exact unique
  | false => exact (leaf_value_sublist [] _).nodup unique

/-- Basic query execution has no duplicate response paths, including invalid-root and
counted-error responses; witness: root uniqueness or the singleton null position.
-/
theorem executeQueryWithFuel_nodup (schema : Schema) (resolvers : Resolvers ObjectRef)
    (variables : VariableValues) (operation : GraphQL.Operation) (fuel : Nat)
    (source : ResolverValue ObjectRef) (containers : Bool)
    : (ResponsePositions.value containers []
        (GraphQL.Execution.executeQueryWithFuel schema resolvers variables operation fuel
          source).data).Nodup := by
  unfold GraphQL.Execution.executeQueryWithFuel
  split
  · exact rootResponse_nodup schema resolvers _ fuel _ source operation.selectionSet containers
  · simp [ResponsePositions.value]

end GraphQL.IncrementalDelivery.Correctness.BasicPositions
