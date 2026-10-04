import CurveComplexGenusTwo.Topology.CapBandGeometry.SquareHalfPatch

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

/-- An exterior cap fills the actual exposed square side away from its finite
corner set. The patch is constructed inside the complement of both bands. -/
theorem actual_band_exposed_square_cap_interior
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    {c : Curve S} (hfront : frontier (bandUnion D B) = c.image)
    (f : C(CapDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' capBoundary = c.image)
    (houtside : f '' capInterior ⊆ interior (bandUnion D B)ᶜ)
    (z : SupSquare D.radius)
    (hz : (z : ℝ × ℝ) ∈ Metric.sphere ((0, 0) : ℝ × ℝ) D.radius)
    (hcorner : ¬ (|(z : ℝ × ℝ).1| = D.radius ∧ |(z : ℝ × ℝ).2| = D.radius))
    (hfirst : D.square z ∉ Set.range B.first)
    (hsecond : D.square z ∉ Set.range B.second) :
    D.square z ∈ interior (bandUnion D B ∪ Set.range f) := by
  obtain ⟨i, x, hx0, hx1, hez⟩ := supSquare_noncorner_side_chart D.radius D.radius_pos z hz hcorner
  let E := D.square ∘ squareSymmetry D.radius i
  have hE : IsEmbedding E := D.square_embedded.comp (squareSymmetry D.radius i).isEmbedding
  have hRangeE : Set.range E = Set.range D.square := by
    change Set.range (D.square ∘ squareSymmetry D.radius i) = _
    rw [Set.range_comp, (squareSymmetry D.radius i).surjective.range_eq, Set.image_univ]
  let C := Set.range B.first ∪ Set.range B.second
  have hC : IsClosed C := (isCompact_range B.first_embedded.continuous).isClosed.union
    (isCompact_range B.second_embedded.continuous).isClosed
  have hpoint : E ⟨(x, D.radius), supSquare_top_mem _ _ D.radius_pos hx0 hx1⟩ ∈ Cᶜ := by
    change D.square (squareSymmetry D.radius i _) ∉ C
    rw [hez]
    exact fun h => h.elim hfirst hsecond
  obtain ⟨L, hL, hLrange, hLcenter, hcoords⟩ := embedded_square_top_half_patch
    D.radius D.radius_pos E hE x hx0 hx1 Cᶜ hC.isOpen_compl hpoint
  have hLN : Set.range L ⊆ bandUnion D B := by
    intro y hy
    exact Or.inl (Or.inl (hRangeE ▸ (hLrange hy).1))
  have hLfront (p : BandWidth × I) : L p ∈ c.image ↔ p.2 = 0 := by
    obtain ⟨w, hwp, htop, hwx, hwy⟩ := hcoords p
    constructor
    · intro hp
      have hpfront : L p ∈ frontier (bandUnion D B) := hfront.symm ▸ hp
      by_contra hn
      have hwyhi : (w : ℝ × ℝ).2 < D.radius := by
        have hwclosed : dist (w : ℝ × ℝ) (0, 0) ≤ D.radius := w.property
        have hwmax : max |w.val.1| |w.val.2| ≤ D.radius := by
          simpa only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
            Prod.fst_zero, Prod.snd_zero, sub_zero, Real.norm_eq_abs] using hwclosed
        have hwyle := (max_le_iff.mp hwmax).2
        exact lt_of_le_of_ne (le_trans (le_abs_self _) hwyle)
          (fun he => hn (htop.mp he))
      have hwball : (w : ℝ × ℝ) ∈ Metric.ball ((0, 0) : ℝ × ℝ) D.radius := by
        simpa [Metric.mem_ball, dist_eq_norm, Prod.norm_def, Real.norm_eq_abs,
          max_lt_iff, abs_lt] using And.intro hwx (And.intro hwy hwyhi)
      have hwball' := (squareSymmetry_ball D.radius i w).mpr hwball
      have hO : L p ∈ D.openSquare := by
        rw [D.openSquare_eq]
        exact ⟨squareSymmetry D.radius i w, hwball', hwp⟩
      have hOsub : D.openSquare ⊆ bandUnion D B := by
        rw [D.openSquare_eq]
        exact fun _ hx => Or.inl (Or.inl (Set.image_subset_range _ _ hx))
      exact hpfront.2 ((D.openSquare_open.subset_interior_iff.mpr hOsub) hO)
    · intro hp0
      have hwtop : (w : ℝ × ℝ).2 = D.radius := htop.mpr hp0
      have hwsphere : (w : ℝ × ℝ) ∈ Metric.sphere ((0, 0) : ℝ × ℝ) D.radius := by
        simp only [Metric.mem_sphere, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
          Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero, Real.norm_eq_abs,
          hwtop, abs_of_pos D.radius_pos]
        exact max_eq_right (abs_le.mpr ⟨hwx.1.le, hwx.2.le⟩)
      have hwsphere' := (squareSymmetry_sphere D.radius i w).mpr hwsphere
      have hwfront : ((squareSymmetry D.radius i w : SupSquare D.radius) : ℝ × ℝ) ∈
          frontier (Metric.closedBall ((0, 0) : ℝ × ℝ) D.radius) := by
        rw [frontier_closedBall _ D.radius_pos.ne']
        exact hwsphere'
      have hsourcefront := embedded_crossing_square_frontier D.radius D.square
        D.square_embedded (squareSymmetry D.radius i w) hwfront
      have hnotC : L p ∉ C := (hLrange (Set.mem_range_self p)).2
      have hactualfront : L p ∈ frontier (bandUnion D B) := by
        change L p ∈ frontier ((Set.range D.square ∪ Set.range B.first) ∪ Set.range B.second)
        rw [Set.union_assoc]
        apply mem_frontier_union_of_not_mem_closed hC hnotC
        exact hwp ▸ hsourcefront
      exact hfront ▸ hactualfront
  have hi := embedded_half_rectangle_cap_seam (bandUnion D B)
    (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed c hfront
    f hf hboundary houtside L hL hLN hLfront ⟨0, by norm_num⟩ (by norm_num) (by norm_num)
  have heq : L (⟨0, by norm_num⟩, 0) = D.square z := hLcenter.trans (congrArg D.square hez)
  rwa [heq] at hi

#print axioms actual_band_exposed_square_cap_interior
end CurveComplex.CapBandGeometry
