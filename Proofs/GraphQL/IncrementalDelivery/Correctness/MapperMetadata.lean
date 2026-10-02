import Proofs.GraphQL.IncrementalDelivery.Correctness.MapperAllocation
import Proofs.GraphQL.IncrementalDelivery.Correctness.WorkMetadata

/-! Stable numeric IDs retain exact pending-notice attachment metadata. -/

namespace GraphQL.IncrementalDelivery.Correctness
open GraphQL.IncrementalDelivery.Execution
open MapperIdentity

/-- Ordered notice encoding retains each node's key, path, and label in the final state.
-/
inductive NodeNotices (ids : IDState)
    : List DeliveryNode → List IncrementalPendingNotice → Prop where
  | nil : NodeNotices ids [] []
  | cons {node notice nodes notices}
    (known : Known ids node.key notice.id)
    (path : notice.path = node.path) (label : notice.label = node.label)
    (tail : NodeNotices ids nodes notices)
    : NodeNotices ids (node :: nodes) (notice :: notices)

/-- Lookup preservation transports every encoded notice without changing metadata. -/
theorem NodeNotices.mono {before after nodes notices}
    (encoded : NodeNotices before nodes notices) (preserves : Preserves before after)
    : NodeNotices after nodes notices := by
  induction encoded with
  | nil => exact .nil
  | cons known path label tail ih => exact .cons (preserves _ _ known) path label ih

/-- Pending allocation retains ordered node metadata, by allocation-list induction. -/
theorem getPendingEntry_metadata (nodes : List DeliveryNode) (ids : IDState)
    : let (pending, next) :=
        (getPendingEntry (m := StateM IDState) nodes [] ensureID).run ids
      Preserves ids next ∧ NodeNotices next nodes pending := by
  let action : DeliveryNode → StateM IDState IncrementalPendingNotice := fun node => do
    let id ← ensureID node
    return { id, path := node.path, label := node.label }
  have go (nodes : List DeliveryNode) (ids : IDState)
      : Preserves ids ((nodes.mapM action).run ids).2
        ∧ NodeNotices ((nodes.mapM action).run ids).2 nodes
            ((nodes.mapM action).run ids).1 := by
    induction nodes generalizing ids with
    | nil => exact ⟨.refl _, .nil⟩
    | cons node rest ih =>
        have spec : Preserves ids ((action node).run ids).2
            ∧ Known ((action node).run ids).2 node.key ((action node).run ids).1.id :=
          ensureID_spec node ids
        have path : ((action node).run ids).1.path = node.path := rfl
        have label : ((action node).run ids).1.label = node.label := rfl
        obtain ⟨tailPreserves, tail⟩ := ih ((action node).run ids).2
        have encoded := NodeNotices.cons (tailPreserves _ _ spec.2) path label tail
        have preserved := spec.1.trans tailPreserves
        cases allocated : action node ids with
        | mk notice middle =>
            cases remaining : rest.mapM action middle with
            | mk pending final =>
                simpa only [List.mapM_cons, StateT.run, StateT.bind, StateT.pure,
                  bind, pure, allocated, remaining] using And.intro preserved encoded
  simp only [getPendingEntry, List.append_nil]
  change match (nodes.mapM action).run ids with
    | (pending, next) => Preserves ids next ∧ NodeNotices next nodes pending
  cases mapped : (nodes.mapM action).run ids with
  | mk pending next => simpa [mapped] using go nodes ids

/-- A pending-allocation equation exposes the same metadata witness for both node kinds.
-/
theorem getPendingEntry_metadata_of_eq {groups streams ids next pending}
    (allocated
      : (getPendingEntry (m := StateM IDState) groups streams ensureID).run ids
        = (pending, next))
    : NodeNotices next (groups ++ streams) pending := by
  have metadata := getPendingEntry_metadata (groups ++ streams) ids
  have equation : (getPendingEntry (m := StateM IDState) (groups ++ streams) []
      ensureID).run ids = (pending, next) := by
    simpa only [getPendingEntry, List.append_nil] using allocated
  rw [equation] at metadata
  exact metadata.2

/-- Each visible notice names one allocated key and that key's absolute source path. -/
def NoticePaths (paths : Nat → ResponsePath) (ids : IDState)
    (notices : List IncrementalPendingNotice)
    : Prop :=
  ∀ notice ∈ notices, ∃ key, Known ids key notice.id ∧ paths key = notice.path

/-- Ordered metadata and a coherent node assignment imply visible notice paths. -/
theorem NodeNotices.paths {paths ids nodes notices}
    (encoded : NodeNotices ids nodes notices)
    (coherent : ∀ node ∈ nodes, paths node.key = node.path)
    : NoticePaths paths ids notices := by
  induction encoded with
  | nil => simp [NoticePaths]
  | @cons node notice nodes notices known path label tail ih =>
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨node.key, known, (coherent node (by simp)).trans path.symm⟩
      · exact ih (fun node member => coherent node (by simp [member])) entry member

/-- Allocation growth preserves already visible notice paths. -/
theorem NoticePaths.mono {paths before after notices}
    (valid : NoticePaths paths before notices) (preserves : Preserves before after)
    : NoticePaths paths after notices := by
  intro notice member
  obtain ⟨key, known, path⟩ := valid notice member
  exact ⟨key, preserves _ _ known, path⟩

/-- Concatenation preserves notice metadata by membership in either input list. -/
theorem NoticePaths.append {paths ids left right}
    (first : NoticePaths paths ids left) (second : NoticePaths paths ids right)
    : NoticePaths paths ids (left ++ right) := by
  intro notice member
  rcases List.mem_append.mp member with member | member
  · exact first notice member
  · exact second notice member

/-- A looked-up wire notice has the target node's actual path. Witness: stable-ID
injectivity identifies its encoded key, and coherent metadata identifies its path.
-/
theorem NoticePaths.lookup {paths ids notices id notice} {node : DeliveryNode}
    (valid : NoticePaths paths ids notices) (allocated : Allocated ids)
    (known : Known ids node.key id) (path : paths node.key = node.path)
    (found : notices.find? (fun notice => notice.id == id) = some notice)
    : notice.path = node.path := by
  obtain ⟨key, noticeKnown, noticePath⟩ := valid notice (List.mem_of_find?_eq_some found)
  have sameID : notice.id = id := by simpa using List.find?_some found
  rw [sameID] at noticeKnown
  have sameKey := Known.injective allocated noticeKnown known
  rw [sameKey] at noticePath
  exact noticePath.symm.trans path

end GraphQL.IncrementalDelivery.Correctness
