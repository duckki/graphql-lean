import GraphQL.IncrementalDelivery.WorkQueueImplementation

/-! Exact source projections through the shared structural task lookup. -/

namespace GraphQL.IncrementalDelivery.ReferenceWorkQueue
open WorkQueueSemantics

/-- Shared lookup preserves the original group-child projection for every work value. -/
theorem taskChildWork?_eq_lookup (work : Execution.Work) (occurrence : Occurrence)
    : taskChildWork? work occurrence
      = match occurrence with
        | .executionGroup address => do
            let location ← locateWork work address
            match location.current with
            | .executionGroup _ _ _ children =>
                some (Work.fromExecution children (address ++ [0]))
            | _ => none
        | .item _ _ => none := by
  cases occurrence with
  | item => rfl
  | executionGroup address =>
      cases located : locateWork work address with
      | none => simp [taskChildWork?, taskContext?, located]
      | some location =>
          cases current : location.current <;> simp [taskChildWork?, taskContext?, located, current]

/-- Shared lookup preserves exactly the group's contributor descriptors. -/
theorem taskGroups?_eq_lookup (work : Execution.Work) (occurrence : Occurrence)
    : taskGroups? work occurrence
      = match occurrence with
        | .executionGroup address => do
            let location ← locateWork work address
            match location.current with
            | .executionGroup groups _ _ _ =>
                some (groups.map Execution.DeferredFragment.node)
            | _ => none
        | .item _ _ => none := by
  cases occurrence with
  | item => rfl
  | executionGroup address =>
      cases located : locateWork work address with
      | none => simp [taskGroups?, taskContext?, located]
      | some location =>
          cases current : location.current <;> simp [taskGroups?, taskContext?, located, current]

/-- Shared lookup preserves item children, including absent addresses and indices. -/
theorem streamItemWork?_eq_lookup (work : Execution.Work) (occurrence : Occurrence)
    : streamItemWork? work occurrence
      = match occurrence with
        | .item address index => do
            let location ← locateWork work address
            match location.current with
            | .stream _ items =>
                let (_, children) ← items[index]?
                some (Work.fromExecution children (address ++ [index]))
            | _ => none
        | .executionGroup _ => none := by
  cases occurrence with
  | executionGroup => rfl
  | item address index =>
      cases located : locateWork work address with
      | none => simp [streamItemWork?, taskContext?, located]
      | some location =>
          cases current : location.current with
          | stream node items =>
              cases entry : items[index]? with
              | none => simp [streamItemWork?, taskContext?, located, current, entry]
              | some pair =>
                  rcases pair with ⟨outcome, children⟩
                  simp [streamItemWork?, taskContext?, located, current, entry]
          | _ => simp [streamItemWork?, taskContext?, located, current]

end GraphQL.IncrementalDelivery.ReferenceWorkQueue
