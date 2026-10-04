import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialHalfBigonSelection

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- An essential representative cannot be trapped in a mark-free-interior
disk with at most one boundary mark. This derives the endpoint collision
and uses essentiality to exclude the resulting loop. -/
theorem actual_essential_arc_not_in_one_mark_disk
    (M : HyperellipticModel E S) (c : EssentialMarkedArc M)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d) (p : S)
    (hmarks : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S))
    (hcorner : ∀ z ∈ range d, z ∈ M.cover.branch → z = p) :
    ¬ c.val.image ⊆ range d := by
  intro hsub
  have h0 : c.val.map (0 : Interval) = p :=
    hcorner _ (hsub (Set.mem_range_self _)) c.val.start_marked
  have h1 : c.val.map (1 : Interval) = p :=
    hcorner _ (hsub (Set.mem_range_self _)) c.val.end_marked
  exact actual_essential_loop_not_in_interior_free_disk M c (h0.trans h1.symm) d hd hmarks hsub

/-- An actual target-dependent half-bigon bounded by subarcs of a and b
PRODUCES interior avoidance of any essential protected representative
disjoint from both. It includes selected loops and shared marked endpoints;
neither graph clearance nor a relative isotopy is an input. -/
theorem actual_target_half_bigon_avoids_protected_arc
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (hca : Disjoint (arcInterior M c) (arcInterior M a))
    (hcb : Disjoint (arcInterior M c) (arcInterior M b))
    (firstSide newSide : C(Interval,S))
    (hfirst : range firstSide ⊆ a.val.image) (hnew : range newSide ⊆ b.val.image)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d) (p : S)
    (hmarks : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S))
    (hcorner : ∀ z ∈ range d, z ∈ M.cover.branch → z = p)
    (hboundary : d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      range firstSide ∪ range newSide) :
    Disjoint (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      c.val.image := by
  letI : T2Space S := M.sphere.symm.t2Space
  let U := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
  let H := range firstSide ∪ range newSide
  have hU := actual_embedded_disk_interior_component M d hd
  rw [hboundary] at hU
  have havoid : arcInterior M c ⊆ Hᶜ := by
    intro z hz hzH
    rcases hzH with hfirst' | hnew'
    · exact Set.disjoint_left.mp hca hz ⟨hfirst hfirst',hz.2⟩
    · exact Set.disjoint_left.mp hcb hz ⟨hnew hnew',hz.2⟩
  obtain ⟨hc,hdense⟩ := actual_bigon_arc_interior_connected_dense M c
  apply Set.disjoint_left.mpr
  intro z hzU hzc
  have hzI : z ∈ arcInterior M c := ⟨hzc,Set.disjoint_left.mp hmarks hzU⟩
  have heq : U = connectedComponentIn Hᶜ z := by
    exact (hU.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (havoid hzI))
      (hU.2.1.isPreconnected.subset_connectedComponentIn hzU hU.2.2.1)
      (connectedComponentIn_subset _ _)).symm
  have hi : arcInterior M c ⊆ U := by
    rw [heq]
    exact hc.isPreconnected.subset_connectedComponentIn hzI havoid
  have hcl : closure U ⊆ range d :=
    closure_minimal (Set.image_subset_range _ _) (isCompact_range d.continuous).isClosed
  exact actual_essential_arc_not_in_one_mark_disk M c d hd p hmarks hcorner
    ((hdense.trans (closure_mono hi)).trans hcl)

/-- Original J-graph clearance for an actual prescribed old/target half-bigon
is produced directly from the two disjoint named families and their literal
J alignment. This covers selected loops as well as non-loops. -/
theorem actual_target_half_bigon_avoids_original_aligned_graph
    (M : HyperellipticModel E S) (J T F : Finset (EssentialArcClass M))
    (hJT : J ⊆ T) (hTF : T ⊆ F)
    (r : {w // w ∈ F} → EssentialMarkedArc M)
    (hdF : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (rT : {w // w ∈ T} → EssentialMarkedArc M)
    (hdT : ∀ w z, w ≠ z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (haligned : ∀ w : {w // w ∈ T}, w.val ∈ J → r ⟨w.val,hTF w.property⟩ = rT w)
    (u : {w // w ∈ T}) (hu : u.val ∉ J)
    (firstSide newSide : C(Interval,S))
    (hfirst : range firstSide ⊆ (r ⟨u.val,hTF u.property⟩).val.image)
    (hnew : range newSide ⊆ (rT u).val.image)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
    (hd : IsEmbedding d) (p : S)
    (hmarks : Disjoint
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (M.cover.branch : Set S))
    (hcorner : ∀ z ∈ range d, z ∈ M.cover.branch → z = p)
    (hboundary : d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
      range firstSide ∪ range newSide) :
    Disjoint (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
      (actualObjectTrace M r J) := by
  apply Set.disjoint_left.mpr
  intro z hz hzG
  obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hzG
  obtain ⟨hvJ,hzv⟩ := Set.mem_iUnion.mp hv
  let uF : {w // w ∈ F} := ⟨u.val,hTF u.property⟩
  let vT : {w // w ∈ T} := ⟨v.val,hJT hvJ⟩
  have hneF : v ≠ uF := by intro he; exact hu (congrArg Subtype.val he ▸ hvJ)
  have hneT : vT ≠ u := by intro he; exact hu (congrArg Subtype.val he ▸ hvJ)
  have heF : (⟨vT.val,hTF vT.property⟩ : {w // w ∈ F}) = v := Subtype.ext rfl
  have hrv : r v = rT vT := by simpa only [heF] using haligned vT hvJ
  have hcb : Disjoint (arcInterior M (r v)) (arcInterior M (rT u)) := by
    rw [hrv]
    exact hdT vT u hneT
  exact Set.disjoint_left.mp
    (actual_target_half_bigon_avoids_protected_arc M (r uF) (rT u) (r v)
      (hdF v uF hneF) hcb firstSide newSide hfirst hnew d hd p hmarks hcorner hboundary)
    hz hzv

#print axioms actual_essential_arc_not_in_one_mark_disk
#print axioms actual_target_half_bigon_avoids_protected_arc
#print axioms actual_target_half_bigon_avoids_original_aligned_graph
end CurveComplex.HyperellipticModel
