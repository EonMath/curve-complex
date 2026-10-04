import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import Schoenflies.JordanSchoenflies

open Set Topology Metric

namespace CurveComplex

theorem curve_image_minus_point_isPreconnected
    {S : Type} [TopologicalSpace S] (c : Curve S) (p : S) (hp : p ∈ c.image) :
    IsPreconnected (c.image \ {p}) := by
  obtain ⟨z,rfl⟩ := hp
  have heq : c.image \ {c.map z} = c.map '' ({z}ᶜ : Set Circle) := by
    ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,ht⟩
      exact ⟨t,fun he => ht (by simpa using congrArg c.map (Set.mem_singleton_iff.mp he)),rfl⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,rfl⟩,fun he => ht (by simpa using c.embedded.injective (Set.mem_singleton_iff.mp he))⟩
  rw [heq]
  exact (Circle.isPathConnected_compl_singleton z).isConnected.isPreconnected.image
    c.map c.embedded.continuous.continuousOn

/-- A transverse crossing cannot be the only intersection of two actual
plane circles. This uses actual Jordan regions, not essential-circle parity. -/
theorem planar_curves_cannot_cross_once
    (c d : Curve Schoenflies.Plane) (p : Schoenflies.Plane)
    (hcross : CrossesAt c d p) (hinter : c.image ∩ d.image = {p}) : False := by
  classical
  obtain ⟨U,V,hpU,h,hU,hV,hpzero,haxes⟩ := hcross
  have hpC : p ∈ c.image := (haxes p hpU).1.mpr (by rw [hpzero])
  have hpD : p ∈ d.image := (haxes p hpU).2.mpr (by rw [hpzero])
  have hJordan : Schoenflies.IsJordanCurve c.image :=
    isJordanCurve_range_of_isEmbedding_circle ⟨c.map,c.embedded.continuous⟩ c.embedded
  have hsep := Schoenflies.jordan_curve_theorem hJordan
  have hdp : d.image \ {p} ⊆ c.imageᶜ := by
    intro x hx hxc
    have hxp : x ∈ ({p} : Set Schoenflies.Plane) := hinter ▸ ⟨hxc,hx.1⟩
    exact hx.2 hxp
  have regionImpossible (R T : Set Schoenflies.Plane)
      (hR : IsOpen R) (hT : IsOpen T) (hRT : Disjoint R T)
      (hcover : R ∪ T = c.imageᶜ) (hfront : frontier T = c.image)
      (hdR : d.image \ {p} ⊆ R) : False := by
    have hpcl : p ∈ closure T := frontier_subset_closure (hfront.symm ▸ hpC)
    have h0V : ((0,0) : ℝ × ℝ) ∈ V := hpzero ▸ (h ⟨p,hpU⟩).property
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hV (0,0) h0V
    let N : Set U := h ⁻¹' {v : V | v.val ∈ Metric.ball (0 : ℝ × ℝ) r}
    have hN : IsOpen N :=
      ((Metric.isOpen_ball.preimage continuous_subtype_val).preimage h.continuous)
    have hNU : IsOpen (Subtype.val '' N : Set Schoenflies.Plane) :=
      hU.isOpenEmbedding_subtypeVal.isOpenMap _ hN
    have hpN : p ∈ Subtype.val '' N := by
      refine ⟨⟨p,hpU⟩,?_,rfl⟩
      change (h ⟨p,hpU⟩).val ∈ Metric.ball (0 : ℝ × ℝ) r
      rw [hpzero]
      simpa using hr
    obtain ⟨z,hzN,hzT⟩ := mem_closure_iff_nhds.mp hpcl _ (hNU.mem_nhds hpN)
    obtain ⟨zu,hzu,rfl⟩ := hzN
    let v : ℝ × ℝ := (h zu).val
    have hvball : v ∈ Metric.ball (0 : ℝ × ℝ) r := hzu
    have hvne : v.1 ≠ 0 := by
      intro hv0
      have hzC : zu.val ∈ c.image := (haxes zu.val zu.property).1.mpr hv0
      have hzcompl : zu.val ∈ c.imageᶜ := by rw [← hcover]; exact Or.inr hzT
      exact hzcompl hzC
    let A : Set (ℝ × ℝ) := Metric.ball 0 r ∩ {y | 0 < v.1 * y.1}
    have hAconn : IsPreconnected A := by
      let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := v.1 • LinearMap.fst ℝ ℝ ℝ
      exact ((convex_ball (0 : ℝ × ℝ) r).inter
        ((convex_Ioi (0 : ℝ)).linear_preimage L)).isPreconnected
    let i : A → V := fun y => ⟨y.val,hball y.property.1⟩
    let F : C(A,Schoenflies.Plane) :=
      ⟨fun y => (h.symm (i y)).val, by fun_prop⟩
    have hFconn : IsPreconnected (Set.range F) := by
      letI : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hAconn
      exact isPreconnected_range F.continuous
    have hFcover : Set.range F ⊆ R ∪ T := by
      rintro x ⟨y,rfl⟩
      rw [hcover]
      intro hc
      have he := (haxes (h.symm (i y)).val (h.symm (i y)).property).1.mp hc
      have hh : (h ⟨(h.symm (i y)).val,(h.symm (i y)).property⟩).val = y.val :=
        congrArg Subtype.val (h.apply_symm_apply (i y))
      rw [hh] at he
      have hp := y.property.2
      change 0 < v.1 * y.val.1 at hp
      rw [he,mul_zero] at hp
      exact lt_irrefl 0 hp
    have hvA : v ∈ A := ⟨hvball,mul_self_pos.mpr hvne⟩
    have hFv : F ⟨v,hvA⟩ = zu.val := by
      change (h.symm (i ⟨v,hvA⟩)).val = zu.val
      have hi : i ⟨v,hvA⟩ = h zu := Subtype.ext rfl
      rw [hi,h.symm_apply_apply]
    have hFallT : Set.range F ⊆ T := hFconn.subset_right_of_subset_union
      hR hT hRT hFcover ⟨zu.val,⟨⟨⟨v,hvA⟩,hFv⟩,hzT⟩⟩
    have hvflat : (v.1,0) ∈ Metric.ball (0 : ℝ × ℝ) r := by
      change dist (v.1,0) (0 : ℝ × ℝ) < r
      change dist v (0 : ℝ × ℝ) < r at hvball
      apply lt_of_le_of_lt ?_ hvball
      rw [Prod.dist_eq,Prod.dist_eq]
      change max (dist v.1 0) (dist (0 : ℝ) 0) ≤ max (dist v.1 0) (dist v.2 0)
      rw [dist_self]
      exact max_le_max le_rfl dist_nonneg
    let y : A := ⟨(v.1,0),hvflat,mul_self_pos.mpr hvne⟩
    have hFyD : F y ∈ d.image :=
      (haxes (h.symm (i y)).val (h.symm (i y)).property).2.mpr (by
        change ((h (h.symm (i y))).val).2 = 0
        rw [h.apply_symm_apply]
        )
    have hFyp : F y ≠ p := by
      intro he
      have hpcoord : (h (h.symm (i y))).val = (h ⟨p,hpU⟩).val := by
        congr 2
        exact Subtype.ext he
      rw [h.apply_symm_apply,hpzero] at hpcoord
      exact hvne (congrArg Prod.fst hpcoord)
    exact Set.disjoint_left.mp hRT (hdR ⟨hFyD,hFyp⟩) (hFallT ⟨y,rfl⟩)
  have hregions : d.image \ {p} ⊆ Schoenflies.inside c.image ∪ Schoenflies.outside c.image := by
    rw [Schoenflies.inside_union_outside]
    exact hdp
  obtain hi | ho := (curve_image_minus_point_isPreconnected d p hpD).subset_or_subset
    hsep.isOpen_inside hsep.isOpen_outside Schoenflies.disjoint_inside_outside hregions
  · exact regionImpossible _ _ hsep.isOpen_inside hsep.isOpen_outside
      Schoenflies.disjoint_inside_outside (Schoenflies.inside_union_outside _)
      hsep.frontier_outside hi
  · exact regionImpossible _ _ hsep.isOpen_outside hsep.isOpen_inside
      Schoenflies.disjoint_inside_outside.symm
      (by rw [Set.union_comm,Schoenflies.inside_union_outside]) hsep.frontier_inside ho

end CurveComplex
