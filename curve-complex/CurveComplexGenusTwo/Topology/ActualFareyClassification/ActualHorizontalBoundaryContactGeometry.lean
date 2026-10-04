import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalLocalSubdiskGeometry
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalFiberSetCrossing
import CurveComplexGenusTwo.Topology.ActualFareyClassification.FiberBoundaryInterior

open Set Topology Schoenflies Metric

theorem horizontal_grid_free_jordan_boundary_in_adjacent_slab
    (C : Set Plane) (hC : IsJordanCurve C) (c T : ℝ) (hT : 0<T)
    (p : Plane) (hp : p∈C) (hpc : p 1=c)
    (hno : ∀ z∈inside C, z 1≠c ∧ z 1≠c-T ∧ z 1≠c+T) :
    (∀ z∈C, c-T≤z 1 ∧ z 1≤c) ∨ (∀ z∈C, c≤z 1 ∧ z 1≤c+T) := by
  let f : Plane → ℝ := fun z => z 1
  have hf : Continuous f := by fun_prop
  have hc := jordan_curve_theorem hC
  let S := f '' inside C
  have hs : IsPreconnected S := hc.isConnected_inside.isPreconnected.image f hf.continuousOn
  have part (d : ℝ) (hd : ∀ z∈inside C, z 1≠d) :
      S⊆Iio d ∨ S⊆Ioi d := by
    apply hs.subset_or_subset isOpen_Iio isOpen_Ioi (disjoint_left.mpr (by intro x hx hy; exact lt_asymm (show x<d from hx) (show d<x from hy)))
    rintro x ⟨z,hz,rfl⟩
    exact lt_or_gt_of_ne (hd z hz)
  have hpcl : p∈closure (inside C) :=
    frontier_subset_closure (hc.frontier_inside.symm ▸ hp)
  have closedBound (d : ℝ) (hd : S⊆Iio d) : ∀ z∈C, z 1≤d := by
    have hi : inside C⊆f ⁻¹' Iic d := by
      intro z hz
      exact le_of_lt (show f z<d from hd ⟨z,hz,rfl⟩)
    have hcl := (isClosed_Iic.preimage hf).closure_subset_iff.mpr hi
    intro z hz
    exact hcl (frontier_subset_closure (hc.frontier_inside.symm ▸ hz))
  have closedLower (d : ℝ) (hd : S⊆Ioi d) : ∀ z∈C, d≤z 1 := by
    have hi : inside C⊆f ⁻¹' Ici d := by
      intro z hz
      exact le_of_lt (show d<f z from hd ⟨z,hz,rfl⟩)
    have hcl := (isClosed_Ici.preimage hf).closure_subset_iff.mpr hi
    intro z hz
    exact hcl (frontier_subset_closure (hc.frontier_inside.symm ▸ hz))
  rcases part c (fun z hz => (hno z hz).1) with hl|hr
  · left
    rcases part (c-T) (fun z hz => (hno z hz).2.1) with hll|hlr
    · have hh := closedBound (c-T) hll p hp
      rw [hpc] at hh
      linarith
    · exact fun z hz => ⟨closedLower (c-T) hlr z hz,closedBound c hl z hz⟩
  · right
    rcases part (c+T) (fun z hz => (hno z hz).2.2) with hrl|hrr
    · exact fun z hz => ⟨closedLower c hr z hz,closedBound (c+T) hrl z hz⟩
    · have hh := closedLower (c+T) hrr p hp
      rw [hpc] at hh
      linarith

theorem jordan_horizontal_fiber_upper_halfball_inside
    (C : Set Plane) (hC : IsJordanCurve C) (q : Plane) (hq : q∈C)
    (c ρ : ℝ) (_hqc : q 1=c) (hρ : 0<ρ)
    (hside : ∀ z∈C, c≤z 1)
    (hlocal : ∀ z∈ball q ρ, z∈C → z 1=c) :
    ball q ρ ∩ {z : Plane | c<z 1} ⊆ inside C := by
  let H := ball q ρ ∩ {z : Plane | c<z 1}
  have hc := jordan_curve_theorem hC
  have hconn : IsPreconnected H := by
    apply Convex.isPreconnected
    exact (convex_ball q ρ).inter
      ((convex_Ioi c).is_linear_preimage (EuclideanSpace.proj 1).isLinear)
  have hdis : H⊆Cᶜ := by
    intro z hz hzC
    exact (ne_of_lt hz.2).symm (hlocal z hz.1 hzC)
  have hpart : H⊆inside C ∪ outside C := by
    rw [inside_union_outside]
    exact hdis
  have hqcl : q∈closure (inside C) :=
    frontier_subset_closure (hc.frontier_inside.symm ▸ hq)
  obtain ⟨z,⟨hzball,hzin⟩⟩ :=
    (_root_.mem_closure_iff.mp hqcl) (ball q ρ) isOpen_ball (mem_ball_self hρ)
  have hzlower : c≤z 1 := jordan_coordinate_lower_bound hC 1 c hside z (subset_closure hzin)
  have hzneq : z 1≠c := jordan_inside_avoids_supporting_horizontal_fiber C hC c (Or.inr hside) z hzin
  have hzH : z∈H := ⟨hzball,lt_of_le_of_ne hzlower (Ne.symm hzneq)⟩
  exact hconn.subset_left_of_subset_union hc.isOpen_inside hc.isOpen_outside
    disjoint_inside_outside hpart ⟨z,hzH,hzin⟩

/-- The analogous left half-ball belongs to the actual left-sided Jordan disk. -/
theorem jordan_horizontal_fiber_lower_halfball_inside
    (C : Set Plane) (hC : IsJordanCurve C) (q : Plane) (hq : q∈C)
    (c ρ : ℝ) (_hqc : q 1=c) (hρ : 0<ρ)
    (hside : ∀ z∈C, z 1≤c)
    (hlocal : ∀ z∈ball q ρ, z∈C → z 1=c) :
    ball q ρ ∩ {z : Plane | z 1<c} ⊆ inside C := by
  let H := ball q ρ ∩ {z : Plane | z 1<c}
  have hc := jordan_curve_theorem hC
  have hconn : IsPreconnected H := by
    apply Convex.isPreconnected
    exact (convex_ball q ρ).inter
      ((convex_Iio c).is_linear_preimage (EuclideanSpace.proj 1).isLinear)
  have hdis : H⊆Cᶜ := by
    intro z hz hzC
    exact (ne_of_lt hz.2) (hlocal z hz.1 hzC)
  have hpart : H⊆inside C ∪ outside C := by
    rw [inside_union_outside]
    exact hdis
  have hqcl : q∈closure (inside C) :=
    frontier_subset_closure (hc.frontier_inside.symm ▸ hq)
  obtain ⟨z,⟨hzball,hzin⟩⟩ :=
    (_root_.mem_closure_iff.mp hqcl) (ball q ρ) isOpen_ball (mem_ball_self hρ)
  have hzupper : z 1≤c := jordan_coordinate_upper_bound hC 1 c hside z (subset_closure hzin)
  have hzneq : z 1≠c := jordan_inside_avoids_supporting_horizontal_fiber C hC c (Or.inl hside) z hzin
  have hzH : z∈H := ⟨hzball,lt_of_le_of_ne hzupper hzneq⟩
  exact hconn.subset_left_of_subset_union hc.isOpen_inside hc.isOpen_outside
    disjoint_inside_outside hpart ⟨z,hzH,hzin⟩

theorem transverse_horizontal_fiber_contact_of_empty_bigon_on_curve_side
    (G : C(ℝ,Plane)) (r s c : ℝ) (hr : G r 1=c) (hs : G s 1=c)
    (hJ : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (L : Set Plane)
    (he : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) L)
    (hside : (∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s), z 1≤c) ∨
      (∀ z∈(G '' Icc r s) ∪ segment ℝ (G r) (G s), c≤z 1))
    (q : Plane) (hq : q∈segment ℝ (G r) (G s)) (_hqL : q∈L)
    (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (hq0 : ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0))
    (haxes : ∀ z (hz : z∈U),
      (z 1=c ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈L ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) : q∈G '' Icc r s := by
  by_contra hqG
  have hqcoord : q 1=c := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨u,hu,heq⟩ := hq
    have hh := congrArg (fun z : Plane => z 1) heq
    simp only [AffineMap.lineMap_apply] at hh
    change u*(G s 1-G r 1)+G r 1=q 1 at hh
    rw [hr,hs] at hh
    linarith
  have hclosed : IsClosed (G '' Icc r s) := (isCompact_Icc.image G.continuous).isClosed
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl q hqG
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  have hlocal (z : Plane) (hz : z∈ball q ρ) (hzC : z∈C) : z 1=c := by
    rcases hzC with hzC|hzC
    · exact False.elim (hball hz hzC)
    · rw [segment_eq_image_lineMap] at hzC
      obtain ⟨u,hu,rfl⟩ := hzC
      simp only [AffineMap.lineMap_apply]
      change u*(G s 1-G r 1)+G r 1=c
      rw [hr,hs]
      ring
  obtain ⟨hleft,hright⟩ := actual_horizontal_fiber_set_crossing_has_both_sides L q c hqcoord U V hqU h hU hV hq0 haxes
    (ball q ρ) isOpen_ball (mem_ball_self hρ)
  rcases hside with hl|hr
  · obtain ⟨z,⟨hzB,hzL⟩,hzleft⟩ := hleft
    have hzin := jordan_horizontal_fiber_lower_halfball_inside C hJ q (Or.inr hq) c ρ hqcoord hρ hl hlocal ⟨hzB,hzleft⟩
    exact disjoint_left.mp he hzin hzL
  · obtain ⟨z,⟨hzB,hzL⟩,hzright⟩ := hright
    have hzin := jordan_horizontal_fiber_upper_halfball_inside C hJ q (Or.inr hq) c ρ hqcoord hρ hr hlocal ⟨hzB,hzright⟩
    exact disjoint_left.mp he hzin hzL


#print axioms transverse_horizontal_fiber_contact_of_empty_bigon_on_curve_side
#print axioms horizontal_grid_free_jordan_boundary_in_adjacent_slab
