import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
import CurveComplexGenusTwo.Dictionary.Circle24.ActualCorridor
import CurveComplexGenusTwo.Dictionary.Circle24.UnbranchedRectangle
open Set Topology Metric
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 12000000
theorem two_mark_closed_side_actual_square_chart
    (M : HyperellipticModel E S) (a : PuncturedCircle M)
    (U : Set S)
    (d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure U)
    (hcl : closure U = U ∪ a.image)
    (hdb : ∀ x, (d x : S) ∈ a.image ↔ ‖x.val‖ = 1)
    (hdi : ∀ x, (d x : S) ∈ U ↔ ‖x.val‖ < 1)
    (hcount : (by classical exact (M.cover.branch.filter (· ∈ U)).card = 2)) :
    ∃ f : C(dictPullbackSquare,S), IsEmbedding f ∧
      (∀ z, z.val ∈ frontier dictPullbackSquare → f z ∉ M.cover.branch) ∧
      (by classical exact (M.cover.branch.filter (fun b => b ∈ f ''
        {z | z.val ∈ interior dictPullbackSquare})).card = 2) ∧
      f '' {z | z.val ∈ frontier dictPullbackSquare} = a.image ∧
      f '' {z | z.val ∈ interior dictPullbackSquare} = U := by
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
  exact ⟨f,hf,havoid,hcard,hbrange,hirange⟩

private theorem corridor_pullback_image_frontier :
    dictPullbackHomeomorph '' {x : dictPullbackRect | x.val ∈ frontier dictPullbackRect} =
      {z : dictPullbackSquare | z.val ∈ frontier dictPullbackSquare} := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change dictPullbackEquiv.toHomeomorph x.val ∈
      frontier (dictPullbackEquiv.toHomeomorph '' dictPullbackRect)
    rw [← dictPullbackEquiv.toHomeomorph.image_frontier]
    exact ⟨x.val,hx,rfl⟩
  · intro hz
    change z.val ∈ frontier (dictPullbackEquiv.toHomeomorph '' dictPullbackRect) at hz
    rw [← dictPullbackEquiv.toHomeomorph.image_frontier] at hz
    rcases hz with ⟨x,hx,hxz⟩
    have hclosed : IsClosed dictPullbackRect := isClosed_Icc.prod isClosed_Icc
    exact ⟨⟨x,hclosed.frontier_subset hx⟩,hx,Subtype.ext hxz⟩

private theorem corridor_pullback_image_interior :
    dictPullbackHomeomorph '' {x : dictPullbackRect | x.val ∈ interior dictPullbackRect} =
      {z : dictPullbackSquare | z.val ∈ interior dictPullbackSquare} := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    change dictPullbackEquiv.toHomeomorph x.val ∈
      interior (dictPullbackEquiv.toHomeomorph '' dictPullbackRect)
    rw [← dictPullbackEquiv.toHomeomorph.image_interior]
    exact ⟨x.val,hx,rfl⟩
  · intro hz
    change z.val ∈ interior (dictPullbackEquiv.toHomeomorph '' dictPullbackRect) at hz
    rw [← dictPullbackEquiv.toHomeomorph.image_interior] at hz
    rcases hz with ⟨x,hx,hxz⟩
    exact ⟨⟨x,interior_subset hx⟩,hx,Subtype.ext hxz⟩

/-- Every Circle24 object has an actual square chart with exactly its two
interior marks and its own circle as outer boundary. -/
theorem actual_circle24_rectangle_chart (M : HyperellipticModel E S) (a : Circle24 M) :
    ∃ f : C(Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,S), IsEmbedding f ∧
      (∀ z, z.val ∈ frontier (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) → f z ∉ M.cover.branch) ∧
      (by classical exact (M.cover.branch.filter (fun b => b ∈ f '' {z | z.val ∈
        interior (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)})).card = 2) ∧
      f '' {z | z.val ∈ frontier (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)} = a.val.image ∧
      IsOpen (f '' {z | z.val ∈ interior (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)}) := by
  classical
  obtain ⟨U,d,hU,hconn,hcl,hb,hi,hcount⟩ := M.actual_circle24_two_mark_closed_side a
  obtain ⟨f,hf,havoid,hcard,houter,hinterior⟩ :=
    two_mark_closed_side_actual_square_chart M a.val U d hcl hb hi hcount
  let g : C(dictPullbackRect,S) := f.comp ⟨dictPullbackHomeomorph,dictPullbackHomeomorph.continuous⟩
  have hg : IsEmbedding g := hf.comp dictPullbackHomeomorph.isEmbedding
  have hmap (A : Set dictPullbackRect) : g '' A = f '' (dictPullbackHomeomorph '' A) := by
    change (f ∘ dictPullbackHomeomorph) '' A = _
    simpa only [Function.comp_def] using
      (Set.image_image (⇑f) (⇑dictPullbackHomeomorph) A).symm
  refine ⟨g,hg,?_,?_,?_,?_⟩
  · intro z hz
    apply havoid
    change dictPullbackHomeomorph z ∈ {x | x.val ∈ frontier dictPullbackSquare}
    rw [← corridor_pullback_image_frontier]
    exact ⟨z,hz,rfl⟩
  · change (M.cover.branch.filter (fun b => b ∈ g '' {z | z.val ∈ interior dictPullbackRect})).card = 2
    rw [hmap,corridor_pullback_image_interior]
    exact hcard
  · change g '' {z | z.val ∈ frontier dictPullbackRect} = a.val.image
    rw [hmap,corridor_pullback_image_frontier]
    exact houter
  · change IsOpen (g '' {z | z.val ∈ interior dictPullbackRect})
    rw [hmap,corridor_pullback_image_interior,hinterior]
    exact hU

/-- From only a Circle24 object, construct a branch-free dividing corridor
and its two embedded rectangle lifts, with opposite-side branch labels. -/
theorem actual_circle24_dividing_corridor_two_lifts
    (M : HyperellipticModel E S) (a : Circle24 M) :
    ∃ f : C(Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,S), IsEmbedding f ∧
      f '' {z | z.val ∈ frontier (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)} = a.val.image ∧
      IsOpen (f '' {z | z.val ∈ interior (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)}) ∧
    ∃ l r b t : ℝ, l < r ∧ b < t ∧
    ∃ hsub : (Icc l r ×ˢ Icc b t) ⊆ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1),
      ((b = -1 ∧ t = 1 ∧ -1 < l ∧ r < 1) ∨
       (l = -1 ∧ r = 1 ∧ -1 < b ∧ t < 1)) ∧
    ∃ p₀ p₁ : Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1,
      (∀ z, f z ∈ M.cover.branch ↔ z=p₀ ∨ z=p₁) ∧
      (((p₀.val.1 < l ∧ r < p₁.val.1) ∨ (p₁.val.1 < l ∧ r < p₀.val.1)) ∨
       ((p₀.val.2 < b ∧ t < p₁.val.2) ∨ (p₁.val.2 < b ∧ t < p₀.val.2))) ∧
    ∃ g : C(Icc l r ×ˢ Icc b t,S),
      (∀ z, g z = f ⟨z.val,hsub z.property⟩) ∧
    ∃ F G : C(Icc l r ×ˢ Icc b t,E), IsEmbedding F ∧ IsEmbedding G ∧
      (∀ z, M.cover.projection (F z) = g z) ∧
      (∀ z, M.cover.projection (G z) = g z) ∧
      (∀ z, G z = M.cover.deck (F z)) ∧
      Disjoint (Set.range F) (Set.range G) ∧
      Set.range F ∪ Set.range G = M.cover.projection ⁻¹' Set.range g := by
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨f,hf,hboundary,hcount,houter,hopen⟩ := M.actual_circle24_rectangle_chart a
  obtain ⟨l,r,b,t,hlr,hbt,hsub,hshape,p₀,p₁,hmarks,hsep,havoid⟩ :=
    M.cover.two_mark_square_has_branch_free_corridor f hf hboundary hcount
  let g : C(Icc l r ×ˢ Icc b t,S) :=
    f.comp ⟨Set.inclusion hsub,continuous_inclusion hsub⟩
  have hg : IsEmbedding g := hf.comp (Topology.IsEmbedding.inclusion hsub)
  have hgavoid (z : Icc l r ×ˢ Icc b t) : g z ∉ M.cover.branch :=
    havoid ⟨z.val,hsub z.property⟩ z.property
  obtain ⟨F,G,hF,hG,hFπ,hGπ,hdeck,hdisj,hcover⟩ :=
    M.cover.closed_rectangle_two_sheet_lifts l r b t hlr hbt g hg hgavoid
  exact ⟨f,hf,houter,hopen,l,r,b,t,hlr,hbt,hsub,hshape,p₀,p₁,hmarks,hsep,
    g,fun _ => rfl,F,G,hF,hG,hFπ,hGπ,hdeck,hdisj,hcover⟩

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_circle24_rectangle_chart
#print axioms CurveComplex.HyperellipticModel.actual_circle24_dividing_corridor_two_lifts
