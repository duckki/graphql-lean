import GraphQL.IncrementalDelivery.Correctness

/-! Public correctness statements are available without importing proof modules.
Wire-position decoding rejects missing owners and does not assume successful merging.
-/

namespace GraphQL.IncrementalDelivery.Tests.Correctness

open GraphQL.IncrementalDelivery.Execution
open GraphQL.IncrementalDelivery.Correctness

/-! The public surface has no enumerator or obsolete defer-only slice model. -/

example : ExecutionObservation → ExecutionObservation := id
#guard_msgs (drop info) in
#check_failure QueryResult
#guard_msgs (drop info) in
#check_failure enumerateQueryOutcomes
#guard_msgs (drop info) in
#check_failure ExecutionObservation.DeliversObjectSlices
#guard_msgs (drop info) in
#check_failure Operation.streamFree

/-- Proposed queue premises are separately named and available without proof modules. -/
example (result : WorkQueueResult) (work : Work) (h : result.Conforms work)
    : result.Initialized
      ∧ result.PrefixClosed
      ∧ result.AccountsForWork work
      ∧ result.TerminationMatchesWork work :=
  h

example (schema : Schema) (operation : Operation)
    (hl : deliveryIDsEventuallyComplete schema operation)
    (hd : deliverySlicesDisjoint schema operation)
    (hp : deliveredResponsePositionsEquivalentToBasic schema operation)
    (ho : basicLeavesDeliveredExactlyOnce schema operation)
    : deliveryIDsEventuallyComplete schema operation
      ∧ deliverySlicesDisjoint schema operation
      ∧ deliveredResponsePositionsEquivalentToBasic schema operation
      ∧ basicLeavesDeliveredExactlyOnce schema operation :=
  ⟨hl, hd, hp, ho⟩

example (response : Response)
    : (ExecutionObservation.single response).idsEventuallyComplete :=
  trivial

example (schema : Schema) (operation : Operation)
    (hu : deliveryIDsUnique schema operation)
    (hp : deliveryPatchesAnnounced schema operation) {ObjectRef : Type}
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef) (result : ExecutionObservation)
    (observed : queryObservation schema resolvers variables operation fuel source result)
    : result.idsUnique ∧ result.patchesAnnounced :=
  ⟨
    hu resolvers variables fuel source result observed,
    hp resolvers variables fuel source result observed
  ⟩

example (schema : Schema) (operation : Operation)
    (h : deliveryLifecycleValid schema operation) {ObjectRef : Type}
    (resolvers : Resolvers ObjectRef) (variables : VariableValues) (fuel : Nat)
    (source : ResolverValue ObjectRef) (result : ExecutionObservation)
    (observed : queryOutcome schema resolvers variables operation fuel source result)
    : result.deliveryComplete = true :=
  h resolvers variables fuel source result observed

example (response : Response) (containers : Bool)
    : (ExecutionObservation.single response).DeliversSlices containers
        [ResponsePositions.value containers [] response.data] :=
  rfl

def duplicateCompletion : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "0", path := [] }], hasNext := true }
    [{ hasNext := false, completed := [{ id := "0" }, { id := "0" }] }]

/-- Eventual completion alone does not establish full lifecycle validity. -/
example : duplicateCompletion.idsEventuallyComplete := by
  simp [duplicateCompletion, ExecutionObservation.idsEventuallyComplete,
    DeliveryTrace.completedIDs, DeliveryTrace.announcementsEventuallyComplete]

#guard !duplicateCompletion.deliveryComplete

example : ¬duplicateCompletion.idUsageValid := by
  simp [duplicateCompletion, ExecutionObservation.idUsageValid, DeliveryTrace.idUsageValid,
    List.nodup_cons]

/-- Announcement uniqueness and causal patch references do not establish unique
completions.
-/
example : duplicateCompletion.idsUnique ∧ duplicateCompletion.patchesAnnounced := by
  simp [duplicateCompletion, ExecutionObservation.idsUnique, DeliveryTrace.pendingIDs,
    ExecutionObservation.patchesAnnounced, DeliveryTrace.patchesAnnounced, List.nodup_cons]

def duplicateAnnouncement : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "0", path := [] }], hasNext := true }
    [{
      hasNext := false,
      pending := [{ id := "0", path := [] }],
      completed := [{ id := "0" }]
    }]

example : ¬duplicateAnnouncement.idsUnique := by
  simp [duplicateAnnouncement, ExecutionObservation.idsUnique, DeliveryTrace.pendingIDs,
    List.nodup_cons]

/-- Same-update announcements are available to both object and list patches. -/
def sameUpdateNotice : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
    [{
      hasNext := false,
      pending := [{ id := "s", path := [.field "values"] }],
      incremental := [.object "d" [("values", .list [])], .list "s" [.null]],
      completed := [{ id := "d" }, { id := "s" }]
    }]

example : sameUpdateNotice.idsUnique ∧ sameUpdateNotice.patchesAnnounced := by
  simp [sameUpdateNotice, ExecutionObservation.idsUnique, DeliveryTrace.pendingIDs,
    ExecutionObservation.patchesAnnounced, DeliveryTrace.patchesAnnounced, IncrementalResult.id,
    List.nodup_cons]

#guard sameUpdateNotice.deliveryComplete

/-- A defer payload can introduce a list before its same-update stream append. -/
example
    : mergeExecutionObservation sameUpdateNotice
      = some { data := .object [("values", .list [.null])] } := by
  rfl

example : sameUpdateNotice.idUsageValid := by
  simp [sameUpdateNotice, ExecutionObservation.idUsageValid, DeliveryTrace.idUsageValid,
    IncrementalResult.id, List.nodup_cons]

def lateAnnouncement : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
    [
      { hasNext := true, incremental := [.list "s" [.null]] },
      {
        hasNext := false,
        pending := [{ id := "s", path := [.field "values"] }],
        completed := [{ id := "d" }, { id := "s" }]
      }
    ]

example : ¬lateAnnouncement.patchesAnnounced := by
  simp [lateAnnouncement, ExecutionObservation.patchesAnnounced, DeliveryTrace.patchesAnnounced,
    IncrementalResult.id]

/-- History-based resolution is deliberately weaker than requiring an open ID. -/
def closedReference : ExecutionObservation :=
  .incremental
    { data := .list [], pending := [{ id := "s", path := [] }], hasNext := true }
    [
      { hasNext := true, completed := [{ id := "s" }] },
      { hasNext := false, incremental := [.list "s" [.null]] }
    ]

example : closedReference.idsUnique ∧ closedReference.patchesAnnounced := by
  simp [closedReference, ExecutionObservation.idsUnique, DeliveryTrace.pendingIDs,
    ExecutionObservation.patchesAnnounced, DeliveryTrace.patchesAnnounced, IncrementalResult.id,
    List.nodup_cons]

#guard !closedReference.deliveryComplete

example : ¬closedReference.idUsageValid := by
  simp [closedReference, ExecutionObservation.idUsageValid, DeliveryTrace.idUsageValid,
    IncrementalResult.id, List.nodup_cons]

/-- A completion cannot use an unannounced ID, even if no payload references it. -/
example
    : ¬ExecutionObservation.idUsageValid
        (.incremental
          { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
          [{ hasNext := false, completed := [{ id := "unknown" }] }]) := by
  simp [ExecutionObservation.idUsageValid, DeliveryTrace.idUsageValid, List.nodup_cons]

/-- ID usage is safety for a finite observation, not proof that delivery has finished. -/
def incompleteObservation : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true } []

example : incompleteObservation.idUsageValid := by
  simp [incompleteObservation, ExecutionObservation.idUsageValid, DeliveryTrace.idUsageValid,
    List.nodup_cons]

example : ¬incompleteObservation.idsCompleteExactlyOnce := by
  simp [incompleteObservation, ExecutionObservation.idsCompleteExactlyOnce,
    DeliveryTrace.pendingIDs, DeliveryTrace.completedIDs]

#guard !incompleteObservation.deliveryComplete

def separatedTermination : ExecutionObservation :=
  .incremental
    { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
    [{ hasNext := true, completed := [{ id := "d" }] }, { hasNext := false }]

#guard separatedTermination.deliveryComplete

/-- Reconstruction counts initial, object/list-patch, and completion errors once. -/
def errorEnvelopes : ExecutionObservation :=
  .incremental
    {
      data := .object [],
      errors := 1,
      pending := [{ id := "d", path := [] }],
      hasNext := true
    }
    [{
      hasNext := false,
      pending := [{ id := "s", path := [.field "values"] }],
      incremental := [.object "d" [("values", .list [])] 2, .list "s" [.null] 4],
      completed := [{ id := "d", errors := 8 }, { id := "s", errors := 16 }]
    }]

#guard errorEnvelopes.deliveryComplete
#guard errorEnvelopes.totalErrors == 31

example
    : mergeExecutionObservation errorEnvelopes
      = some { data := .object [("values", .list [.null])], errors := 31 } := by
  rfl

/-- Safe and completed IDs do not imply that a patch has an attachment point. -/
def missingParent : ExecutionObservation :=
  .incremental
    {
      data := .object [],
      pending := [{ id := "s", path := [.field "missing"] }],
      hasNext := true
    }
    [{
      hasNext := false, incremental := [.list "s" [.null]], completed := [{ id := "s" }]
    }]

#guard missingParent.deliveryComplete
#guard (mergeExecutionObservation missingParent).isNone

/-! Finishing one announced ID cannot hide a second uncompleted ID. -/

#guard
  !ExecutionObservation.deliveryComplete
    (.incremental
      { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
      [{
        hasNext := false,
        pending := [{ id := "s", path := [] }],
        completed := [{ id := "d" }]
      }])

/-! Completing the same ID in separate updates is also invalid. -/

#guard
  !ExecutionObservation.deliveryComplete
    (.incremental
      { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
      [
        { hasNext := true, completed := [{ id := "d" }] },
        { hasNext := false, completed := [{ id := "d" }] }
      ])

/-! All continuation flags must agree with the observed suffix, not just the final one. -/

#guard
  !ExecutionObservation.deliveryComplete
    (.incremental
      { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
      [{ hasNext := false, completed := [{ id := "d" }] }, { hasNext := false }])

/-! Closing all IDs does not excuse claiming another update that never appears. -/

#guard
  !ExecutionObservation.deliveryComplete
    (.incremental
      { data := .object [], pending := [{ id := "d", path := [] }], hasNext := true }
      [{ hasNext := true, completed := [{ id := "d" }] }])

/-- Missing owner notices fail decoding, independently of cursor state. -/
example (id : String) (data : List (Name × ResponseValue))
    (containers : Bool) (cursors : ResponsePositions.Cursors)
    : DeliveryTrace.decodePatch containers [] cursors (.object id data) = none :=
  rfl

example (id : String)
    : ¬ExecutionObservation.idsEventuallyComplete
        (.incremental { data := .object [], pending := [], hasNext := true }
          [
            { hasNext := true, completed := [{ id }] },
            { hasNext := false, pending := [{ id, path := [] }] }
          ]) := by
  simp [ExecutionObservation.idsEventuallyComplete, DeliveryTrace.announcementsEventuallyComplete,
    DeliveryTrace.completedIDs]

end GraphQL.IncrementalDelivery.Tests.Correctness
