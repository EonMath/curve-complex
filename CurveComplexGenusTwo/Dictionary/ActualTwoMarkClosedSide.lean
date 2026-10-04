import CurveComplexGenusTwo.Dictionary.ScratchCoordinatePullback
import CurveComplexGenusTwo.Foundations.PlanarSquareDiscWitness
import CurveComplexGenusTwo.Dictionary.PuncturedCircleClosedSides
open Set Topology Metric
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

/-- The full preimage of an actual two-mark closed disc boundary cannot be
an embedded upstairs circle. All cells and lift-pasting are produced by the
existing coordinate-pullback obstruction. -/
theorem no_curve_of_two_mark_closed_side
    (M : HyperellipticModel E S) (a : PuncturedCircle M)
    (c : Curve E) (hc : c.image = M.cover.projection ⁻¹' a.image)
    (U : Set S)
    (d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure U)
    (hcl : closure U = U ∪ a.image)
    (hdb : ∀ x, (d x : S) ∈ a.image ↔ ‖x.val‖ = 1)
    (hdi : ∀ x, (d x : S) ∈ U ↔ ‖x.val‖ < 1)
    (hcount : (by classical exact (M.cover.branch.filter (· ∈ U)).card = 2)) :
    False := by
  have hrect (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 2) ℝ).symm
    let K := e '' (Icc a b ×ˢ Icc c d)
    ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K,
      (∀ x, (h x : Schoenflies.Plane) ∈ interior K ↔ ‖x.val‖ < 1) ∧
      (∀ x, (h x : Schoenflies.Plane) ∈ frontier K ↔ ‖x.val‖ = 1) := by
    dsimp only
    let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
    let K := e '' (Icc a b ×ˢ Icc c d)
    change ∃ h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K, _
    have hcompact : IsCompact K :=
      (isCompact_Icc.prod isCompact_Icc).image e.continuous
    have hconvex : Convex ℝ K :=
      ((convex_Icc a b).prod (convex_Icc c d)).linear_image e.toLinearEquiv.toLinearMap
    have hne : (interior K).Nonempty := by
      have hm : ((a + b) / 2, (c + d) / 2) ∈ interior (Icc a b ×ˢ Icc c d) := by
        rw [interior_prod_eq, interior_Icc, interior_Icc]
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      refine ⟨e ((a + b) / 2, (c + d) / 2), ?_⟩
      change e.toHomeomorph ((a + b) / 2, (c + d) / 2) ∈
        interior (e.toHomeomorph '' (Icc a b ×ˢ Icc c d))
      rw [← e.toHomeomorph.image_interior]
      exact mem_image_of_mem e hm
    obtain ⟨g, hgi, hgc, hgf⟩ :=
      exists_homeomorph_image_interior_closure_frontier_eq_unitBall hconvex hne hcompact.isBounded
    have hgK : g '' K = Metric.closedBall (0 : Schoenflies.Plane) 1 := by
      simpa [hcompact.isClosed.closure_eq] using hgc
    let h : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ K :=
      (Homeomorph.sets g (by
        ext x
        constructor
        · intro hx
          rw [← hgK]
          exact mem_image_of_mem g hx
        · intro hx
          rw [← hgK] at hx
          rcases hx with ⟨y, hy, hxy⟩
          exact g.injective hxy ▸ hy)).symm
    refine ⟨h, ?_, ?_⟩
    · intro x
      change g.symm x.val ∈ interior K ↔ ‖x.val‖ < 1
      rw [← mem_ball_zero_iff]
      constructor
      · intro hx
        rw [← hgi]
        exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
      · intro hx
        rw [← hgi] at hx
        rcases hx with ⟨y, hy, hyx⟩
        simpa [← hyx] using hy
    · intro x
      change g.symm x.val ∈ frontier K ↔ ‖x.val‖ = 1
      rw [← dist_zero_right x.val]
      change g.symm x.val ∈ frontier K ↔ x.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1
      constructor
      · intro hx
        rw [← hgf]
        exact ⟨g.symm x.val, hx, g.apply_symm_apply x.val⟩
      · intro hx
        rw [← hgf] at hx
        rcases hx with ⟨y, hy, hyx⟩
        simpa [← hyx] using hy
  classical
  let fd : C(Metric.closedBall (0 : Schoenflies.Plane) 1, S) :=
    ⟨fun x => (d x : S), continuous_subtype_val.comp d.continuous⟩
  have hfd : IsEmbedding fd := IsEmbedding.subtypeVal.comp d.isEmbedding
  have hdbrange : fd '' {x | ‖x.val‖ = 1} = a.image := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hdb x).mpr hx
    · intro hy
      let yy : closure U := ⟨y, hcl.symm ▸ Or.inr hy⟩
      refine ⟨d.symm yy, ?_, ?_⟩
      · apply (hdb _).mp
        simpa only [d.apply_symm_apply] using hy
      · change (d (d.symm yy) : S) = y
        rw [d.apply_symm_apply]
  have hdinterior : fd '' {x | ‖x.val‖ < 1} = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hdi x).mpr hx
    · intro hy
      let yy : closure U := ⟨y, subset_closure hy⟩
      refine ⟨d.symm yy, ?_, ?_⟩
      · apply (hdi _).mp
        simpa only [d.apply_symm_apply] using hy
      · change (d (d.symm yy) : S) = y
        rw [d.apply_symm_apply]
  obtain ⟨h, hi, hb⟩ := hrect (-1) 1 (-1) 1 (by norm_num) (by norm_num)
  change Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ dictPullbackSquare at h
  change ∀ x, (h x : Schoenflies.Plane) ∈ interior dictPullbackSquare ↔ ‖x.val‖ < 1 at hi
  change ∀ x, (h x : Schoenflies.Plane) ∈ frontier dictPullbackSquare ↔ ‖x.val‖ = 1 at hb
  let f : C(dictPullbackSquare, S) := fd.comp ⟨h.symm, h.symm.continuous⟩
  have hf : IsEmbedding f := hfd.comp h.symm.isEmbedding
  have hboundary (z : dictPullbackSquare) :
      f z ∈ a.image ↔ z.val ∈ frontier dictPullbackSquare := by
    change (d (h.symm z) : S) ∈ a.image ↔ _
    rw [hdb, ← hb, h.apply_symm_apply]
  have hbrange : f '' {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} = a.image := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hboundary z).mpr hz
    · intro hy
      obtain ⟨x, hx, hxy⟩ := hdbrange.symm ▸ hy
      refine ⟨h x, (hb x).mpr hx, ?_⟩
      change fd (h.symm (h x)) = y
      rw [h.symm_apply_apply]
      exact hxy
  have hirange : f '' {z : dictPullbackSquare | z.val ∈ interior dictPullbackSquare} = U := by
    rw [← hdinterior]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨h.symm z, ?_, rfl⟩
      apply (hi _).mp
      change z.val ∈ interior dictPullbackSquare at hz
      simpa only [h.apply_symm_apply] using hz
    · rintro ⟨x, hx, rfl⟩
      refine ⟨h x, (hi x).mpr hx, ?_⟩
      change fd (h.symm (h x)) = fd x
      rw [h.symm_apply_apply]
  have havoid : ∀ z, z.val ∈ frontier dictPullbackSquare → f z ∉ M.cover.branch := by
    intro z hz hbranch
    exact Set.disjoint_left.mp a.avoids_branch ((hboundary z).mpr hz) hbranch
  have hcard : (M.cover.branch.filter (fun b => b ∈ f '' {z |
      z.val ∈ interior dictPullbackSquare})).card = 2 := by
    rw [hirange]
    exact hcount
  exact two_marked_disc_chart_obstruction_coordinate_pullback M a f hf havoid hcard hbrange c hc

/-- A punctured-circle full preimage that is an actual upstairs circle has
neither a two-mark side nor its exchanged orientation. -/
theorem full_preimage_curve_splits_no_two
    (M : HyperellipticModel E S) (a : PuncturedCircle M)
    (c : Curve E) (hc : c.image = M.cover.projection ⁻¹' a.image)
    (m n : ℕ) (hsplit : SplitsMarked M a m n) : m ≠ 2 ∧ n ≠ 2 := by
  classical
  obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
    M.puncturedCircle_closedSides a
  obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWn,hZn,hWZ,hWZcover,hWcount,hZcount⟩ := hsplit
  have hNoTwo (A B : Set S) (hAo : IsOpen A) (hBo : IsOpen B)
      (hAc : IsConnected A) (hAn : A.Nonempty) (hAB : Disjoint A B)
      (hABcover : A ∪ B = a.imageᶜ)
      (hcount : (M.cover.branch.filter (· ∈ A)).card = 2) : False := by
    have hAsub : A ⊆ U ∪ V := by
      rw [hcover, ← hABcover]
      exact subset_union_left
    have hUsub : U ⊆ A ∪ B := by
      rw [hABcover, ← hcover]
      exact subset_union_left
    have hVsub : V ⊆ A ∪ B := by
      rw [hABcover, ← hcover]
      exact subset_union_right
    have hEq : A = U ∨ A = V := by
      rcases hAc.isPreconnected.subset_or_subset hUo hVo hUV hAsub with hAU | hAV
      · left
        apply Set.Subset.antisymm hAU
        rcases hUc.isPreconnected.subset_or_subset hAo hBo hAB hUsub with hUA | hUB
        · exact hUA
        · obtain ⟨x,hx⟩ := hAn
          exact False.elim (Set.disjoint_left.mp hAB hx (hUB (hAU hx)))
      · right
        apply Set.Subset.antisymm hAV
        rcases hVc.isPreconnected.subset_or_subset hAo hBo hAB hVsub with hVA | hVB
        · exact hVA
        · obtain ⟨x,hx⟩ := hAn
          exact False.elim (Set.disjoint_left.mp hAB hx (hVB (hAV hx)))
    rcases hEq with hEq | hEq
    · apply no_curve_of_two_mark_closed_side M a c hc U dU hclU hUb hUi
      rwa [← hEq]
    · apply no_curve_of_two_mark_closed_side M a c hc V dV hclV hVb hVi
      rwa [← hEq]
  constructor
  · intro hm
    apply hNoTwo W Z hWo hZo hWc hWn hWZ hWZcover
    exact hWcount.trans hm
  · intro hn
    apply hNoTwo Z W hZo hWo hZc hZn hWZ.symm
    · rw [Set.union_comm]
      exact hWZcover
    · exact hZcount.trans hn

#print axioms CurveComplex.HyperellipticModel.no_curve_of_two_mark_closed_side
#print axioms CurveComplex.HyperellipticModel.full_preimage_curve_splits_no_two
end CurveComplex.HyperellipticModel
