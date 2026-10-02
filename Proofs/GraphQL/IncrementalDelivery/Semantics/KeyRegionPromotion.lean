import Proofs.GraphQL.IncrementalDelivery.Semantics.KeyRegions

/-! Revealing one streamed item promotes its region into the registered region.
Discarding cancelled work can only narrow that region or remove hidden regions.
-/

namespace GraphQL.IncrementalDelivery.Semantics.KeyRegions

theorem promote_region {root region : List Nat} {before after : List (List Nat)}
    (h : (root :: (before ++ region :: after)).Pairwise Disjoint)
    : ((root ++ region) :: (before ++ after)).Pairwise Disjoint := by
  have hroot := List.pairwise_cons.mp h
  have hregion := List.pairwise_cons.mp
    ((List.pairwise_middle Disjoint.symm).mp hroot.2)
  have hm : (before ++ after).Subset (before ++ region :: after) := by
    intro other ho
    rcases List.mem_append.mp ho with ho | ho
    · exact List.mem_append_left _ ho
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)
  refine List.pairwise_cons.mpr ⟨?_, hregion.2⟩
  intro other ho
  exact (hroot.1 other (hm ho)).append_left (hregion.1 other ho)

theorem separated_narrow {root nextRoot : List Nat}
    {hidden nextHidden : List (List Nat)}
    (h : (root :: hidden).Pairwise Disjoint)
    (hr : nextRoot.Subset root) (hh : nextHidden.Sublist hidden)
    : (nextRoot :: nextHidden).Pairwise Disjoint := by
  have hs := List.pairwise_cons.mp h
  exact List.pairwise_cons.mpr
    ⟨fun region hm => (hs.1 region (hh.subset hm)).mono hr (List.Subset.refl _),
      hs.2.sublist hh⟩

end GraphQL.IncrementalDelivery.Semantics.KeyRegions
