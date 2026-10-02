/-! Opaque finite event sources, shared by execution and queue implementations. -/

namespace GraphQL.IncrementalDelivery

/-- An opaque source language and its observed prefix, not a preselected future trace.
This state is intentionally partial: many next values may be admissible. Observations are
finite and single-threaded; host waiting is not an emitted value.
-/
structure EventSource (α : Type) where
  admissible : List α → Prop
  finished : List α → Prop
  history : List α := []

/-- Every intermediate prefix must be allowed, including when several source values are
aggregated into one observation. No value being available does not imply finished.
-/
def EventSource.Allows (source : EventSource α) (values : List α) : Prop :=
  ∀ initial, initial.IsPrefix values → source.admissible (source.history ++ initial)

/-- Retain the supplied observations without choosing a future value. -/
def EventSource.advance (source : EventSource α) (values : List α) : EventSource α :=
  { source with history := source.history ++ values }

/-- The observed history is a finished source history. -/
def EventSource.IsFinished (source : EventSource α) : Prop :=
  source.finished source.history

/-- A fixed finite source for fixtures and replay, not the default source model. -/
def EventSource.ofList (values : List α) : EventSource α :=
  { admissible := (·.IsPrefix values), finished := (· = values) }

/-- Available source events grouped for one-at-a-time aggregated observation. Groups are
nonempty and ordered; every intermediate source prefix must remain admissible. This starts
at the source's current history, not at the beginning of a consumed source.
-/
def EventSource.batch (source : EventSource α) : EventSource (List α) :=
  let admitted :=
    fun groups : List (List α) =>
      (∀ group ∈ groups, group ≠ []) ∧ source.Allows groups.flatten
  {
    admissible := admitted,
    finished := fun groups => admitted groups ∧ (source.advance groups.flatten).IsFinished
  }

end GraphQL.IncrementalDelivery
