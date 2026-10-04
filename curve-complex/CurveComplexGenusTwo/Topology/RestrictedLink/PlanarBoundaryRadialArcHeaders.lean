import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.RestrictedLink.HomeomorphismComponentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RegionComponentHeaders
import CurveComplexGenusTwo.Topology.ArcStraightening
import Mathlib.Analysis.Convex.Topology
namespace CurveComplex.HyperellipticModel
open Set Schoenflies unitInterval
theorem planar_boundary_radial_arc {C : Set Plane} (hC : IsJordanCurve C) {x q : Plane}
    (hx : x ∈ C) (hq : q ∈ inside C) :
    ∃ A : Set Plane, IsArcBetween A x q ∧ A \ {x} ⊆ inside C := by
  classical
  have chart {C : Set Plane} (hC : IsJordanCurve C) :
      ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
    classical
    have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
        IsComplementComponent C (outside C) := by
      have hs := jordan_curve_theorem hC
      refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
      intro V hV hsub hVc
      apply Set.Subset.antisymm
      · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
        · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
          exact ⟨x, hsub hx, hx⟩
        · intro x hx
          rw [(IsRegionOf.outside C).closure_eq hs] at hx
          rcases hx.1 with hi | hc
          · exact hi
          · exact False.elim (hVc hx.2 hc)
      · exact hsub
    obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
    obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
    have him : F '' C = modelCurve := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [hF ⟨y, hy⟩]
        exact (e ⟨y, hy⟩).property
      · intro hx
        let y := e.symm ⟨x, hx⟩
        refine ⟨y.val, y.property, ?_⟩
        rw [hF y]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
    rw [him] at hc
    have hi := jordan_inside_complement_component isJordanCurve_modelCurve
    have ho := outsideComponent isJordanCurve_modelCurve
    obtain ⟨x, hx⟩ := hc.1
    have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
      (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
    have heinside : F '' inside C = inside modelCurve := by
      rcases hxin with hxI | hxO
      · by_contra hn
        exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
      · have heoutside : F '' inside C = outside modelCurve := by
          by_contra hn
          exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
        have hs := jordan_curve_theorem hC
        have hk : IsCompact (closure (inside C)) :=
          Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
        have hb : Bornology.IsBounded (F '' inside C) :=
          (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
        exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
          (heoutside ▸ hb))
    exact ⟨F, him, heinside.trans inside_modelCurve⟩
  obtain ⟨F,himage,hin⟩ := chart hC
  have hFx : F x ∈ modelCurve := himage ▸ mem_image_of_mem F hx
  have hFq : F q ∈ Plane.openSquare 0 1 := hin ▸ mem_image_of_mem F hq
  have hxy : F x ≠ F q := by
    intro he
    have h1 : Plane.supNorm (F x) = 1 := hFx
    have h2 : Plane.supNorm (F q) < 1 := mem_openSquare_zero_one.mp hFq
    rw [he] at h1
    linarith
  let l : ℝ → Plane := fun t => F x + t • (F q - F x)
  have hl : l = AffineMap.lineMap (F x) (F q) := by
    ext t
    simp [l,AffineMap.lineMap_apply_module]
    <;> ring
  have hli : Function.Injective l := hl ▸ AffineMap.lineMap_injective ℝ hxy
  have hinside (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : l t ∈ Plane.openSquare 0 1 := by
    have h := (Plane.convex_closedSquare 0 1).add_smul_sub_mem_interior
      (modelCurve_subset_closedSquare hFx)
      (show F q ∈ interior (Plane.closedSquare 0 1) by rw [interior_closedSquare_zero_one]; exact hFq) ht
    rwa [interior_closedSquare_zero_one] at h
  let a : ℝ → Plane := fun t => F.symm (l t)
  have hac : Continuous a := F.symm.continuous.comp (by dsimp [l]; fun_prop)
  have hai : Function.Injective a := F.symm.injective.comp hli
  have ha0 : a 0 = x := by simp [a,l]
  have ha1 : a 1 = q := by simp [a,l]
  refine ⟨a '' I,⟨a,hac.continuousOn,hai.injOn,rfl,ha0,ha1⟩,?_⟩
  rintro z ⟨⟨t,ht,rfl⟩,hn⟩
  have ht0 : t ≠ 0 := by
    intro he
    apply hn
    simp [he,ha0]
  have hti : t ∈ Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne' ht.1 ht0,ht.2⟩
  have hh : l t ∈ F '' inside C := hin.symm ▸ hinside t hti
  obtain ⟨z,hz,he⟩ := hh
  change F.symm (l t) ∈ inside C
  simpa [← he] using hz
end CurveComplex.HyperellipticModel
