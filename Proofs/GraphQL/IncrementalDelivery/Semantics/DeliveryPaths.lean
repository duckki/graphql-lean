import GraphQL.IncrementalDelivery.Correctness

/-! Proof-facing absolute response positions introduced by defer-only execution slices.
An object patch's attachment path is not itself introduced by the patch. Containers
can be included to distinguish introducing an object/list from adding its descendants.
With `containers = false`, only scalar and null leaves are counted.

Work slices describe execution before scheduling; objectPatch/updateSlices decode the
actual wire representation using only available notices. The stream constructor is
intentionally excluded; use only in the stream-free domain.
-/

namespace GraphQL.IncrementalDelivery.Execution.DeliveryPaths

deriving instance ReflBEq, LawfulBEq for ResponsePathSegment

mutual
  def value (containers : Bool) (path : ResponsePath) : ResponseValue → List ResponsePath
    | .null | .scalar _ => [path]
    | .object data => (if containers then [path] else []) ++ fields containers path data
    | .list data => (if containers then [path] else []) ++ items containers path 0 data

  def fields (containers : Bool) (path : ResponsePath)
      : List (Name × ResponseValue) → List ResponsePath
    | [] => []
    | (name, data) :: rest =>
        value containers (path ++ [.field name]) data ++ fields containers path rest

  def items (containers : Bool) (path : ResponsePath) (index : Nat)
      : List ResponseValue → List ResponsePath
    | [] => []
    | data :: rest =>
        value containers (path ++ [.index index]) data
        ++ items containers path (index + 1) rest
end

def result (paths : α → List ResponsePath) : Result α → List ResponsePath
  | .error _ => []
  | .ok (data, _) => paths data

def work (containers : Bool) : Work → List ResponsePath
  | .empty | .stream .. => []
  | .append left right => work containers left ++ work containers right
  | .deferred _ path completed children =>
      result (fields containers path) completed ++ work containers children

def completion (containers : Bool) (paths : α → List ResponsePath)
    (completed : Completion α)
    : List ResponsePath :=
  result paths completed.result ++ work containers completed.work

/-- One entry per task, not per owning defer ID. Empty/error slices are harmless. -/
def workSlices (containers : Bool) : Work → List (List ResponsePath)
  | .empty | .stream .. => []
  | .append left right => workSlices containers left ++ workSlices containers right
  | .deferred _ path completed children =>
      result (fields containers path) completed :: workSlices containers children

def completionSlices (containers : Bool) (paths : α → List ResponsePath)
    (completed : Completion α)
    : List (List ResponsePath) :=
  result paths completed.result :: workSlices containers completed.work

/-- Match the initial envelope constructed by ExecuteRootSelectionSet, including errors.
-/
def rootSlices (containers : Bool) (completed : Completion (List (Name × ResponseValue)))
    : List (List ResponsePath) :=
  value containers [] (selectionSetResultToResponse completed.result).data
  :: workSlices containers completed.work

/-- Internal uniqueness is separate from cross-slice disjointness: both are needed. -/
def SlicesDisjoint (slices : List (List ResponsePath)) : Prop :=
  slices.Pairwise (fun left right => ∀ path ∈ left, path ∉ right)

/-- Decode an object patch using the notices available at its publication boundary. This
is a path projection, not a lifecycle validator. Missing IDs and streamed-item patches are
rejected; stream item offsets need a separate stateful projection.
-/
def objectPatch (containers : Bool) (notices : List IncrementalPendingNotice)
    : IncrementalResult → Option (List ResponsePath)
  | .object id data _ subPath => do
      let notice ← notices.find? (fun notice => notice.id == id)
      return fields containers (notice.path ++ subPath) data
  | .list .. => none

/-- Process each update with only the notices available at that point in the stream. -/
def updateSlices (containers : Bool) (notices : List IncrementalPendingNotice)
    : List IncrementalStreamUpdateResult → Option (List (List ResponsePath))
  | [] => some []
  | update :: rest => do
      let available := notices ++ update.pending
      let head ← update.incremental.mapM (objectPatch containers available)
      let tail ← updateSlices containers available rest
      return head ++ tail

/-- Initial data and subsequently introduced paths, decoded in observable update order.
This rejects missing IDs and streamed-item patches, but does not validate lifecycles.
-/
def querySlices (containers : Bool) : QueryResult → Option (List (List ResponsePath))
  | .single response => some [value containers [] response.data]
  | .incremental initial subsequent => do
      let tail ← updateSlices containers initial.pending subsequent
      return value containers [] initial.data :: tail

end GraphQL.IncrementalDelivery.Execution.DeliveryPaths
