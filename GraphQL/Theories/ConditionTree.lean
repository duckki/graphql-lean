import GraphQL.Theories.SelectionConditions

/-! Minimal Boolean/type condition trees for GraphQL selection sets.

The tree is a project-analysis representation, not a GraphQL specification feature.
It identifies an inline-fragment path by its cumulative possible-object intersection
and canonical conjunction of modeled `@skip`/`@include` conditions. Equivalent source
paths share one tree node, infeasible paths are omitted, and retained paths use a
minimal subsequence of source-derived single-condition branches.

Fields at the same cumulative condition are collected by response name. Modeled
`@skip`/`@include` directives on fields become Boolean condition-tree branches, and
the retained field selections have empty directive lists. Nested field selection sets
form independent condition-tree boundaries when a consumer recursively extracts them.
-/

namespace GraphQL
namespace ConditionTree

open GraphQL.Execution

-- The condition algebra is shared with analyses that do not need a tree. These exports
-- preserve the original condition-tree API while making `SelectionConditions` the owner.
export SelectionConditions (
  BooleanLiteral BranchCondition Condition booleanBranchConditions
  booleanConditionAllows
  branchConditionsAllow branchConditionsForDirectives?
  branchConditionsForInlineFragment? canonicalBooleanCondition conditionForBranch?
  conditionForBranches? directiveBooleanVariable? insertBooleanLiteral
  intersectPossibleTypes literalsForDirective literalsForDirectives
  parentTypeForBranches rootCondition selectionBooleanVariables
  selectionSetBooleanVariables
)

namespace BooleanLiteral

export SelectionConditions.BooleanLiteral (
  allows complement negative orderedBeforeOrEqual positive requiredValue toDirective
  variableName
)

end BooleanLiteral

namespace BranchCondition

export SelectionConditions.BranchCondition (
  allows booleanLiteral isTypeCondition parentType toSelection typeCondition
)

end BranchCondition

namespace Condition

export SelectionConditions.Condition (allows FeasibleUnder)

end Condition

-- Replaces a retained type-condition sequence with its unique possible object.
-- Rechecking the candidate against the cumulative target keeps this helper total on
-- permissive schemas, including malformed object-name and possible-type data.
def singletonObjectBranchPath? (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (start target : Condition) (retained : List BranchCondition)
    : Option (List BranchCondition) :=
  if !retained.any BranchCondition.isTypeCondition then
    none
  else
    match target.possibleTypes with
    | [objectTypeName] =>
        match schema.lookupObject objectTypeName with
        | none => none
        | some _objectType =>
            let candidate :=
              .typeCondition objectTypeName :: booleanBranchConditions retained
            if conditionForBranches? schema inheritedBooleanCondition start candidate
                = some target then
              some candidate
            else
              none
    | _ => none

-- Greedily removes source-derived branches whenever the remainder still reaches the
-- target cumulative condition. If the retained type intersection denotes exactly one
-- object, its type branches are then replaced by that object condition. This keeps the
-- resulting node under the concrete object scope, so a later `... on X` field can merge
-- into it. The reverse merge can move an abstract-scoped field under `X`. Note: this is
-- not always validity preserving (GraphQL spec issue #1121) when rendered into a query.
def shrinkBranches (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (start target : Condition)
    (source : List BranchCondition)
    : List BranchCondition :=
  let retained := go [] source
  (singletonObjectBranchPath? schema inheritedBooleanCondition start target retained).getD
    retained
where
  go : List BranchCondition -> List BranchCondition -> List BranchCondition
    | retained, [] => retained
    | retained, branch :: rest =>
        if conditionForBranches? schema inheritedBooleanCondition start (retained ++ rest)
            = some target then
          go retained rest
        else
          go (retained ++ [branch]) rest

-----------------------------------------------------------------------------------------
-- Tree construction
-----------------------------------------------------------------------------------------

-- Every non-root branch has exactly one condition and one body.
structure Branch (α : Type) where
  condition : BranchCondition
  body : α
deriving Repr

-- A field occurrence stored in a condition tree. Its modeled directives have already
-- been extracted into tree branches, and its response name belongs to the enclosing
-- group. Nested selections remain raw syntax because they form a separate tree boundary.
structure Field where
  fieldName : Name
  arguments : List Argument
  selectionSet : List Selection
deriving Repr

def Field.toSelection (responseName : Name) (field : Field) : Selection :=
  .field responseName field.fieldName field.arguments [] field.selectionSet

-- A field paired with its response name while it is being inserted. `NamedField` is an
-- extraction value, not a stored tree node: once grouped, `FieldGroup` owns the name.
structure NamedField where
  responseName : Name
  field : Field
deriving Repr

def NamedField.toSelection (field : NamedField) : Selection :=
  field.field.toSelection field.responseName

-- Fields at one cumulative condition are collected by response name. The head/tail
-- representation makes every group nonempty, while `Field` rules out directives and
-- inline fragments by construction.
structure FieldGroup where
  responseName : Name
  first : Field
  rest : List Field
deriving Repr

def FieldGroup.fields (group : FieldGroup) : List Field :=
  group.first :: group.rest

def FieldGroup.selections (group : FieldGroup) : List Selection :=
  group.fields.map (Field.toSelection group.responseName)

def FieldGroup.mergedSelectionSet (group : FieldGroup) : List Selection :=
  SelectionSet.mergeSelectionSets group.selections

-- The root has no incoming branch condition. Each entry in `branches` carries one
-- condition, and its body carries the resulting cumulative state and local fields.
structure Tree where
  condition : Condition
  fields : List FieldGroup
  branches : List (Branch Tree)
deriving Repr

def Tree.root (condition : Condition) : Tree :=
  { condition, fields := [], branches := [] }

mutual
  -- Preorder list of every cumulative condition in one boundary.
  def Tree.nodeConditions (tree : Tree) : List Condition :=
    tree.condition :: branchNodeConditions tree.branches
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def branchNodeConditions : List (Branch Tree) -> List Condition
    | [] => []
    | branch :: rest =>
        branch.body.nodeConditions ++ branchNodeConditions rest
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

mutual
  -- Every stored branch edge must be exactly the transition computed from its
  -- parent condition. This makes the tree shape, not a downstream consumer,
  -- responsible for the coherence of extracted paths.
  def Tree.BranchesCoherent (schema : Schema)
      (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
      : Prop :=
    branchesCoherent schema inheritedBooleanCondition tree.condition tree.branches
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_wf
    omega

  def branchesCoherent (schema : Schema)
      (inheritedBooleanCondition : List BooleanLiteral) (parent : Condition)
      : List (Branch Tree) -> Prop
    | [] => True
    | branch :: rest =>
        conditionForBranch? schema inheritedBooleanCondition parent branch.condition
          = some branch.body.condition
        ∧ branch.body.BranchesCoherent schema inheritedBooleanCondition
        ∧ branchesCoherent schema inheritedBooleanCondition parent rest
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

mutual
  def Tree.modifyAtCondition? (target : Condition) (modify : Tree -> Tree) (tree : Tree)
      : Option Tree :=
    if tree.condition = target then
      some (modify tree)
    else
      match modifyBranchesAtCondition? target modify tree.branches with
      | none => none
      | some branches => some { tree with branches }
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def modifyBranchesAtCondition? (target : Condition) (modify : Tree -> Tree)
      : List (Branch Tree) -> Option (List (Branch Tree))
    | [] => none
    | branch :: rest =>
        match branch.body.modifyAtCondition? target modify with
        | some modifiedBody => some ({ branch with body := modifiedBody } :: rest)
        | none =>
            match modifyBranchesAtCondition? target modify rest with
            | none => none
            | some modifiedRest => some (branch :: modifiedRest)
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

mutual
  -- Allocation-free membership test for cumulative conditions in one tree boundary.
  def Tree.containsCondition (tree : Tree) (target : Condition) : Bool :=
    (tree.condition == target) || branchesContainCondition tree.branches target
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def branchesContainCondition : List (Branch Tree) -> Condition -> Bool
    | [], _target => false
    | branch :: rest, target =>
        branch.body.containsCondition target || branchesContainCondition rest target
  termination_by branches _target => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

def addFieldWithResponseName (responseName : Name) (field : Field)
    : List FieldGroup -> List FieldGroup
  | [] =>
      [{ responseName, first := field, rest := [] }]
  | group :: rest =>
      if responseName == group.responseName then
        { group with rest := group.rest ++ [field] } :: rest
      else
        group :: addFieldWithResponseName responseName field rest

def addFieldToGroups (field : NamedField) (groups : List FieldGroup) : List FieldGroup :=
  addFieldWithResponseName field.responseName field.field groups

def collectFieldGroups (fields : List NamedField) : List FieldGroup :=
  fields.foldl (fun groups field => addFieldToGroups field groups) []

def Tree.appendAtCondition? (tree : Tree) (condition : Condition)
    (fields : List NamedField) (branches : List (Branch Tree))
    : Option Tree :=
  tree.modifyAtCondition? condition
    fun node =>
      {
        node with
          fields :=
            fields.foldl (fun groups field => addFieldToGroups field groups) node.fields
          branches := node.branches ++ branches
      }

def pathForBranches? (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (start : Condition)
    : List BranchCondition -> Option (List (BranchCondition × Condition))
  | [] => some []
  | branch :: rest => do
      let condition ← conditionForBranch? schema inheritedBooleanCondition start branch
      let path ← pathForBranches? schema inheritedBooleanCondition condition rest
      some ((branch, condition) :: path)

def pathEnd : Condition -> List (BranchCondition × Condition) -> Condition
  | start, [] => start
  | _start, (_branch, condition) :: rest => pathEnd condition rest

def pathPrefixThrough (target : Condition)
    : List (BranchCondition × Condition) -> List (BranchCondition × Condition)
  | [] => []
  | edge :: rest =>
      if edge.2 = target then
        [edge]
      else
        edge :: pathPrefixThrough target rest

def erasePathCyclesFrom (kept : List (BranchCondition × Condition))
    : List (BranchCondition × Condition) -> List (BranchCondition × Condition)
  | [] => kept
  | edge :: rest =>
      let nextKept :=
        if (kept.map Prod.snd).contains edge.2 then
          pathPrefixThrough edge.2 kept
        else
          kept ++ [edge]
      erasePathCyclesFrom nextKept rest

-- Removes repeated cumulative states from a retained branch path.
def erasePathCycles (path : List (BranchCondition × Condition))
    : List (BranchCondition × Condition) :=
  erasePathCyclesFrom [] path

def branchesForPath
    : List (BranchCondition × Condition) -> List NamedField -> List (Branch Tree)
  | [], _fields => []
  | [(branchCondition, condition)], fields =>
      [{
        condition := branchCondition
        body := { condition, fields := collectFieldGroups fields, branches := [] }
      }]
  | (branchCondition, condition) :: rest, fields =>
      [{
        condition := branchCondition
        body :=
          {
            condition
            fields := []
            branches := branchesForPath rest fields
          }
      }]

def deepestExistingPrefixFrom (tree : Tree)
    : List (BranchCondition × Condition)
      -> (Condition × List (BranchCondition × Condition))
      -> (Condition × List (BranchCondition × Condition))
  | [], best => best
  | (_branch, condition) :: rest, best =>
      let nextBest :=
        if tree.containsCondition condition then
          (condition, rest)
        else
          best
      deepestExistingPrefixFrom tree rest nextBest

def deepestExistingPrefix (tree : Tree) (start : Condition)
    (path : List (BranchCondition × Condition))
    : Condition × List (BranchCondition × Condition) :=
  deepestExistingPrefixFrom tree path (start, path)

def Tree.insertField (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral) (tree : Tree)
    (sourcePath : List BranchCondition)
    (target : Condition) (field : NamedField)
    : Tree :=
  match tree.appendAtCondition? target [field] [] with
  | some modifiedTree => modifiedTree
  | none =>
      match pathForBranches? schema inheritedBooleanCondition tree.condition
              sourcePath with
      | none => tree
      | some sourcePath =>
          let sourcePrefix := deepestExistingPrefix tree tree.condition sourcePath
          let remainingBranches := sourcePrefix.2.map Prod.fst
          let shrunk :=
            shrinkBranches schema inheritedBooleanCondition sourcePrefix.1 target
              remainingBranches
          let retainedPath :=
            match pathForBranches? schema inheritedBooleanCondition sourcePrefix.1
                    shrunk with
            | some path =>
                if pathEnd sourcePrefix.1 path = target then
                  path
                else
                  sourcePrefix.2
            | none => sourcePrefix.2
          let retainedPrefix := deepestExistingPrefix tree sourcePrefix.1 retainedPath
          match retainedPrefix.2 with
          | [] =>
              match tree.appendAtCondition? retainedPrefix.1 [field] [] with
              | some modifiedTree => modifiedTree
              | none => tree
          | missingPath =>
              let simplePath := erasePathCycles missingPath
              match tree.appendAtCondition? retainedPrefix.1 []
                      (branchesForPath simplePath [field]) with
              | some modifiedTree => modifiedTree
              | none => tree

-- Walks source syntax and inserts every feasible directive-free field at the node for
-- its cumulative type and Boolean condition. Tree insertion merges equivalent
-- conditions and minimizes paths.
def insertSelections (schema : Schema)
    (inheritedBooleanCondition : List BooleanLiteral)
    (currentCondition : Condition) (branches : List BranchCondition) (tree : Tree)
    : List Selection -> Tree
  | [] => tree
  | .field responseName fieldName arguments directives selectionSet :: rest =>
      let treeAfterField :=
        match branchConditionsForDirectives? directives with
        | none => tree
        | some nextBranches =>
            match conditionForBranches? schema inheritedBooleanCondition
                    currentCondition nextBranches with
            | none => tree
            | some nextCondition =>
                let field : NamedField :=
                  {
                    responseName
                    field := { fieldName, arguments, selectionSet }
                  }
                tree.insertField schema inheritedBooleanCondition
                  (branches ++ nextBranches) nextCondition field
      insertSelections schema inheritedBooleanCondition currentCondition branches
        treeAfterField rest
  | .inlineFragment typeCondition directives selectionSet :: rest =>
      let treeAfterFragment :=
        match branchConditionsForInlineFragment? typeCondition directives with
        | none => tree
        | some nextBranches =>
            match conditionForBranches? schema inheritedBooleanCondition
                    currentCondition nextBranches with
            | none => tree
            | some nextCondition =>
                insertSelections schema inheritedBooleanCondition nextCondition
                  (branches ++ nextBranches) tree selectionSet
      insertSelections schema inheritedBooleanCondition currentCondition branches
        treeAfterFragment rest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

-- Extracts one boundary relative to the globally inherited Boolean literals of its
-- parent field. Repeated inherited literals are omitted and their complements are
-- infeasible.
def ofSelectionSetInScope (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Tree :=
  let condition := rootCondition schema parentType
  insertSelections schema inheritedBooleanCondition condition []
    (Tree.root condition) selectionSet

-- Root extraction has no inherited Boolean condition.
def ofSelectionSet (schema : Schema) (parentType : Name) (selectionSet : List Selection)
    : Tree :=
  ofSelectionSetInScope schema parentType [] selectionSet

def ofOperation (schema : Schema) (operation : Operation) : Tree :=
  ofSelectionSet schema (operation.rootType schema) operation.selectionSet

-----------------------------------------------------------------------------------------
-- Boolean variable collection
-----------------------------------------------------------------------------------------

mutual
  -- Every modeled Boolean variable represented in a condition tree, including variables
  -- in child selection sets that form later extraction boundaries.
  def conditionTreeBooleanVariables (tree : Tree) : List Name :=
    match tree with
    | { fields, branches, .. } =>
        fields.flatMap
          (fun group =>
            group.fields.flatMap
              fun field => selectionSetBooleanVariables field.selectionSet)
        ++ conditionTreeBranchesBooleanVariables branches
  termination_by 2 * sizeOf tree
  decreasing_by
    all_goals
      simp_wf
      omega

  def conditionTreeBranchesBooleanVariables (branches : List (Branch Tree)) : List Name :=
    match branches with
    | [] => []
    | { condition, body } :: rest =>
        (match condition with
          | .typeCondition _typeName => []
          | .booleanLiteral literal => [literal.variableName])
        ++ conditionTreeBooleanVariables body
        ++ conditionTreeBranchesBooleanVariables rest
  termination_by 2 * sizeOf branches + 1
  decreasing_by
    all_goals
      simp_wf
      omega
end

-----------------------------------------------------------------------------------------
-- Known-false pruning based on supplied variable values
-----------------------------------------------------------------------------------------

-- Whether a modeled variable directive is known inactive in an already-coerced request
-- environment. Constant and unresolved arguments remain canonical extraction's concern.
def directiveKnownFalse (variableValues : VariableValues) : DirectiveApplication -> Bool
  | .include (.variable variableName) =>
      inputValueBoolean? variableValues (.variable variableName) == some false
  | .skip (.variable variableName) =>
      inputValueBoolean? variableValues (.variable variableName) == some true
  | _directive => false

def directivesKnownFalse (variableValues : VariableValues)
    (directives : List DirectiveApplication)
    : Bool :=
  directives.any (directiveKnownFalse variableValues)

-- Removes selections known inactive at one response-field boundary. Inline fragments
-- stay in the same boundary and are traversed immediately; field children are preserved
-- verbatim and receive their own request-aware extraction when the backend recurses.
def pruneKnownFalseSelections (variableValues : VariableValues)
    : List Selection -> List Selection
  | [] => []
  | selection@(.field _responseName _fieldName _arguments directives _selectionSet)
    :: rest =>
      let prunedRest := pruneKnownFalseSelections variableValues rest
      if directivesKnownFalse variableValues directives then
        prunedRest
      else
        selection :: prunedRest
  | .inlineFragment typeCondition directives selectionSet :: rest =>
      let prunedRest := pruneKnownFalseSelections variableValues rest
      if directivesKnownFalse variableValues directives then
        prunedRest
      else
        .inlineFragment typeCondition directives
          (pruneKnownFalseSelections variableValues selectionSet)
        :: prunedRest
termination_by selectionSet => SelectionSet.size selectionSet
decreasing_by
  all_goals
    simp_wf
    simp_all [SelectionSet.size, Selection.size]
    omega

-- Extracts one boundary after request variables and operation defaults have already
-- been combined. Only known-inactive selections are omitted.
def ofSelectionSetInScopeWithKnownFalsePruning (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (variableValues : VariableValues) (selectionSet : List Selection)
    : Tree :=
  ofSelectionSetInScope schema parentType inheritedBooleanCondition
    (pruneKnownFalseSelections variableValues selectionSet)

-----------------------------------------------------------------------------------------
-- Public invariant
-----------------------------------------------------------------------------------------

def booleanConditionsDisjoint (left right : List BooleanLiteral) : Prop :=
  ∀ literal, literal ∈ left -> literal ∉ right

mutual
  -- Response names are unique at every node because fields are stored as collected
  -- groups. The selections inside one group remain available to field handlers.
  def Tree.fieldGroupsUnique (tree : Tree) : Prop :=
    (tree.fields.map FieldGroup.responseName).Nodup
    ∧ branchFieldGroupsUnique tree.branches
  termination_by sizeOf tree
  decreasing_by
    cases tree
    simp_all
    omega

  def branchFieldGroupsUnique : List (Branch Tree) -> Prop
    | [] => True
    | branch :: rest =>
        branch.body.fieldGroupsUnique ∧ branchFieldGroupsUnique rest
  termination_by branches => sizeOf branches
  decreasing_by
    all_goals
      cases branch
      simp_wf
      omega
end

-- A valid tree has globally unique, feasible cumulative conditions; no local node
-- repeats a literal already supplied by its parent field; every branch edge agrees with
-- the condition transition function; and response names are unique at every node. Field
-- syntax and nonemptiness are enforced by `FieldGroup` itself.
structure Tree.WellFormed (schema : Schema) (tree : Tree)
    (inheritedBooleanCondition : List BooleanLiteral)
    : Prop where
  nodeConditionsNodup : tree.nodeConditions.Nodup
  conditionsFeasible
    : ∀ condition,
        condition ∈ tree.nodeConditions
        -> condition.FeasibleUnder inheritedBooleanCondition
  conditionsDisjointFromInherited
    : ∀ condition,
        condition ∈ tree.nodeConditions
        -> booleanConditionsDisjoint inheritedBooleanCondition condition.booleanCondition
  branchesCoherent : tree.BranchesCoherent schema inheritedBooleanCondition
  fieldGroupsUnique : tree.fieldGroupsUnique

-- Public correctness statement for extraction. The proof witness is
-- `ConditionTree.extraction_correct` in
-- `Proofs.GraphQL.Theories.ConditionTree.Extraction`.
def ExtractionCorrect (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Prop :=
  schema.getPossibleTypes parentType ≠ []
  -> (canonicalBooleanCondition inheritedBooleanCondition).isSome = true
  -> Tree.WellFormed schema
      (ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
      inheritedBooleanCondition

-- Every condition extracted at this selection-set boundary is feasible under the
-- Boolean condition inherited from its parent field. Its theorem witness is
-- `extraction_conditionGroups_feasible` in the condition-tree invariant proof module.
def ExtractionConditionGroupsFeasible (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Prop :=
  schema.getPossibleTypes parentType ≠ []
  -> (canonicalBooleanCondition inheritedBooleanCondition).isSome = true
  -> ∀ condition,
      condition
        ∈ (ofSelectionSetInScope schema parentType inheritedBooleanCondition
            selectionSet).nodeConditions
      -> condition.FeasibleUnder inheritedBooleanCondition

-- Every extracted cumulative condition is globally unique. This is stronger than
-- sibling non-overlap: two sibling subtrees cannot share a condition when the preorder
-- list of every condition is duplicate-free. Its theorem witness is
-- `extraction_conditionGroups_separated` in the condition-tree invariant proof module.
def ExtractionConditionGroupsSeparated (schema : Schema) (parentType : Name)
    (inheritedBooleanCondition : List BooleanLiteral)
    (selectionSet : List Selection)
    : Prop :=
  schema.getPossibleTypes parentType ≠ []
  -> (canonicalBooleanCondition inheritedBooleanCondition).isSome = true
  -> ((ofSelectionSetInScope schema parentType inheritedBooleanCondition selectionSet)
      |>.nodeConditions).Nodup

end ConditionTree
end GraphQL
