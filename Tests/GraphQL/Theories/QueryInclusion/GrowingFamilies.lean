import GraphQL.Theories.QueryInclusion
import Tests.GraphQL.Common

/-! Query-inclusion families growing in depth.

The operations of each family grow linearly with their depth, while the type configurations
a response can take multiply with it. Each verdict is checked at small sizes beside a
rejected neighbour. A family the checker decides without enumerating configurations is
also checked at a size no enumeration finishes. There is no timing assertion: the check
simply stops terminating if the search enumerates again.
-/

namespace GraphQL.Tests.QueryInclusionGrowingFamilies

open GraphQL.QueryInclusion

-----------------------------------------------------------------------------------------
-- Complementary contributions over independent ancestors
-----------------------------------------------------------------------------------------

def chainFields : List FieldDefinition :=
  [testObjectFieldDefinition "next" "I", testObjectFieldDefinition "leaf" "Leaf"]

-- Every level of the chain is an `A` or a `B`, independently, ending in a `leaf`:
--
-- ```graphql
-- interface I { next: I  leaf: Leaf }
-- type A implements I { next: I  leaf: Leaf }
-- type B implements I { next: I  leaf: Leaf }
-- type Leaf { f: String }
-- type Query { root: I }
-- ```
def complementaryAncestorsSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object { name := "Query", fields := [testObjectFieldDefinition "root" "I"] },
        .interface { name := "I", fields := chainFields },
        .object { name := "A", fields := chainFields, interfaces := ["I"] },
        .object { name := "B", fields := chainFields, interfaces := ["I"] },
        .object { name := "Leaf", fields := [testStringFieldDefinition "f"] }
      ]
  }

-- `next { … { inner } … }`, `depth` levels of `next`.
def nexts : Nat -> List Selection -> List Selection
  | 0, inner => inner
  | depth + 1, inner => [.field "next" "next" [] [] (nexts depth inner)]

def levelField (level : Nat) : Selection :=
  .field s!"f{level}" "f" [] [] []

-- What the left selects at `level` and below, with `remaining` levels left including this
-- one: the leaf's `f{level}` under each type of `types level`, then the next level.
def complementaryLevels (types : Nat -> List Name) (level : Nat) : Nat -> List Selection
  | 0 => []
  | remaining + 1 =>
      let leaf := nexts remaining [.field "leaf" "leaf" [] [] [levelField level]]
      let copies :=
        (types level).map fun typeName => Selection.inlineFragment (some typeName) [] leaf
      if remaining == 0 then
        copies
      else
        copies
        ++ [.field "next" "next" [] [] (complementaryLevels types (level + 1) remaining)]

-- Selects every `f{level}` twice at its level, once under each type the level can be,
-- except `f{missing}`, which is selected under `A` alone:
--
-- ```graphql
-- { root {
--     ... on A { next { … leaf { f0: f } … } }
--     ... on B { next { … leaf { f0: f } … } }
--     next {
--       ... on A { … leaf { f1: f } … }
--       ... on B { … leaf { f1: f } … }
--       next { … }
--     }
-- } }
-- ```
def complementaryAncestorsLeft (depth : Nat) (missing : Option Nat) : Operation :=
  let types := fun level => if missing == some level then ["A"] else ["A", "B"]
  { selectionSet := [.field "root" "root" [] [] (complementaryLevels types 0 depth)] }

-- Every level's field at the leaf except `f{omitted}`:
-- `{ root { next { … next { leaf { f0: f  f1: f  …  f{depth-1}: f } } … } } }`.
def complementaryAncestorsRight (depth : Nat) (omitted : Option Nat := none)
    : Operation :=
  let levels := (List.range depth).filter fun level => omitted != some level
  let leaf : Selection := .field "leaf" "leaf" [] [] (levels.map levelField)
  { selectionSet := [.field "root" "root" [] [] (nexts (depth - 1) [leaf])] }

def complementaryAncestorsIncludesBool (depth : Nat) (missing : Option Nat)
    (omitted : Option Nat := none)
    : Bool :=
  includesBool complementaryAncestorsSchema (complementaryAncestorsLeft depth missing)
    (complementaryAncestorsRight depth omitted)

-- Each `f{level}` is selected by two copies, one under each type its level can be, and
-- between them it is selected whatever every level is. Without the `B` copy, `f{level}` is
-- missing where that level is a `B`.
theorem complementaryAncestors_coverEveryAncestorTypeSmoke
    : [1, 2, 5].all
        (fun depth =>
          complementaryAncestorsIncludesBool depth none
          && !complementaryAncestorsIncludesBool depth (some (depth / 2)))
      = true := by
  native_decide

-- The growth guard: at depth 64 the levels' types have 2^64 combinations. Each level's two
-- copies give its two type regions equal child obligations, which are decided once.
theorem complementaryAncestors_deepAcceptedSmoke
    : complementaryAncestorsIncludesBool 64 none = true := by
  native_decide

theorem complementaryAncestors_deepMissingCopyRejectedSmoke
    : complementaryAncestorsIncludesBool 64 (some 32) = false := by
  native_decide

-- The rejection is for `f32` alone: without it, the remaining fields are still covered.
theorem complementaryAncestors_deepMissingCopyOnlyLosesItsFieldSmoke
    : complementaryAncestorsIncludesBool 64 (some 32) (some 32) = true := by
  native_decide

-----------------------------------------------------------------------------------------
-- Independent pairs of levels
-----------------------------------------------------------------------------------------

def pairFields (nextType : Name) : List FieldDefinition :=
  [testObjectFieldDefinition "next" nextType, testObjectFieldDefinition "leaf" "Leaf"]

-- Each pair of levels is an `A` over a `C` or a `B` over a `D`, independently of every
-- other pair:
--
-- ```graphql
-- interface I { next: J  leaf: Leaf }
-- type A implements I { next: C  leaf: Leaf }
-- type B implements I { next: D  leaf: Leaf }
-- interface J { next: I  leaf: Leaf }
-- type C implements J { next: I  leaf: Leaf }
-- type D implements J { next: I  leaf: Leaf }
-- type Leaf { f: String }
-- type Query { root: I }
-- ```
def independentPairsSchema : Schema :=
  {
    queryType := "Query"
    types :=
      [
        .object { name := "Query", fields := [testObjectFieldDefinition "root" "I"] },
        .interface { name := "I", fields := pairFields "J" },
        .object { name := "A", fields := pairFields "C", interfaces := ["I"] },
        .object { name := "B", fields := pairFields "D", interfaces := ["I"] },
        .interface { name := "J", fields := pairFields "I" },
        .object { name := "C", fields := pairFields "I", interfaces := ["J"] },
        .object { name := "D", fields := pairFields "I", interfaces := ["J"] },
        .object { name := "Leaf", fields := [testStringFieldDefinition "f"] }
      ]
  }

-- What is selected at `level` and below, with `remaining` levels left including this one:
-- the field of the level's pair under `under level`, if any, then the next level. The last
-- level selects its `leaf`.
def pairLevels (under : Nat -> Option Name) (level : Nat) : Nat -> List Selection
  | 0 => [.field "leaf" "leaf" [] [] [.field "f" "f" [] [] []]]
  | remaining + 1 =>
      let leaf :=
        nexts (remaining + 1) [.field "leaf" "leaf" [] [] [levelField (level / 2)]]
      let fragments :=
        (under level).toList.map
          fun typeName => Selection.inlineFragment (some typeName) [] leaf
      fragments ++ [.field "next" "next" [] [] (pairLevels under (level + 1) remaining)]

-- Selects pair `k`'s field under `... on C` at the pair's second level, or under `D` for
-- pair `changed`.
def independentPairsLeft (pairs : Nat) (changed : Option Nat) : Operation :=
  let under :=
    fun level =>
      if level % 2 == 1 then
        some (if changed == some (level / 2) then "D" else "C")
      else
        none
  { selectionSet := [.field "root" "root" [] [] (pairLevels under 0 (2 * pairs))] }

-- Asks for pair `k`'s field under `... on A` at the pair's first level.
def independentPairsRight (pairs : Nat) : Operation :=
  let under := fun level => if level % 2 == 0 then some "A" else none
  { selectionSet := [.field "root" "root" [] [] (pairLevels under 0 (2 * pairs))] }

def independentPairsIncludesBool (pairs : Nat) (changed : Option Nat) : Bool :=
  includesBool independentPairsSchema (independentPairsLeft pairs changed)
    (independentPairsRight pairs)

-- An `A`'s `next` is a `C`, so a pair's field selected under its `C` is there wherever it
-- is asked under its `A`. Selected under one pair's `D` instead, it is missing where that
-- pair is an `A` over a `C`. Which fields the right owes at the leaf depends on every
-- pair's type, so the checker's work still doubles with each pair; there is no growth
-- guard for this family.
theorem independentPairs_eachSupplyTheirOwnFieldSmoke
    : [1, 2, 4].all
        (fun pairs =>
          independentPairsIncludesBool pairs none
          && !independentPairsIncludesBool pairs (some (pairs / 2)))
      = true := by
  native_decide

end GraphQL.Tests.QueryInclusionGrowingFamilies
