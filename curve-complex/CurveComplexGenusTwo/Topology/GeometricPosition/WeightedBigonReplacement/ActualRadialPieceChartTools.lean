import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualRadialAffineCrossingTools
open Set Topology Schoenflies
namespace CurveComplex

theorem actual_positive_radial_horizontal_piece_chart
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (F : OpenPartialHomeomorph S Plane) (d : Curve S) (a b : Plane)
    (ρ : ℝ) (ha : 0 < a 1) (hb : b 1 < 0)
    (hmodel : ∀ x ∈ F.source, ‖F x‖ < ρ →
      (x ∈ d.image ↔ F x ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b))
    (δ h : ℝ) (hh : 0 < h)
    (hseg : segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target)
    (p : S) (hp : p ∈ F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h))
    (hpd : p ∈ d.image) (hpn : ‖F p‖ < ρ) :
    ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), p ∈ E.source ∧ E.source ⊆ F.source ∧
      (∀ x, E x = (F x 0,F x 1)) ∧
      (∀ x ∈ (F.symm '' segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)) ∩ E.source, (E x).2 = h) ∧
      (∀ x ∈ E.source, x ∈ d.image ↔ (E x).1 = (a 0/a 1)*h+(a 0/a 1)*((E x).2-h)) := by
  have hsy : ∀ q ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h), q 1 = h := by
    intro q hq
    rw [segment_eq_image'] at hq
    obtain ⟨t,ht,he⟩ := hq
    have hy := congrArg (fun q : Plane => q 1) he
    change h+t*(h-h) = q 1 at hy
    simpa using hy.symm
  obtain ⟨q,hq,hqp⟩ := hp
  have hpF : p ∈ F.source := hqp ▸ F.map_target (hseg hq)
  have hFp : F p = q := by rw [←hqp,F.right_inv (hseg hq)]
  have hpy : 0 < F p 1 := by rw [hFp,hsy q hq]; exact hh
  let O := F.source ∩ F ⁻¹' (Metric.ball (0 : Plane) ρ ∩ {q : Plane | 0 < q 1})
  have hO : IsOpen O := F.isOpen_inter_preimage
    (Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop)))
  let xy : Plane ≃ₜ ℝ × ℝ := {
    toFun := fun q => (q 0,q 1)
    invFun := fun q => Plane.mk q.1 q.2
    left_inv := by intro q; ext i; fin_cases i <;> rfl
    right_inv := by intro q; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let E0 := (F.restrOpen O hO).transHomeomorph xy
  have hpE0 : p ∈ E0.source := ⟨hpF,hpF,by simpa only [Metric.mem_ball,dist_zero_right] using hpn,hpy⟩
  have hgraph : ∀ x ∈ d.image ∩ E0.source,
      (E0 x).1 = (a 0/a 1)*h+(a 0/a 1)*((E0 x).2-h) := by
    intro x hx
    have hxF : x ∈ F.source := hx.2.1
    have hxn : ‖F x‖ < ρ := by simpa only [Metric.mem_ball,dist_zero_right] using hx.2.2.2.1
    have hxy : 0 < F x 1 := hx.2.2.2.2
    have hg := actual_positive_radial_segment_graph a b (F x) ha hb hxy ((hmodel x hxF hxn).mp hx.1)
    change F x 0 = (a 0/a 1)*h+(a 0/a 1)*(F x 1-h)
    rw [hg]; ring
  obtain ⟨E,hpE,hSub,hValue,hAxis⟩ := actual_embedded_curve_local_affine_graph_trace
    d E0 p ⟨hpd,hpE0⟩ h ((a 0/a 1)*h) (a 0/a 1) hgraph
  refine ⟨E,hpE,(fun x hx => (hSub hx).1),hValue,?_,hAxis⟩
  rintro x ⟨⟨q,hq,rfl⟩,hx⟩
  rw [hValue]
  change F (F.symm q) 1 = h
  rw [F.right_inv (hseg hq)]
  exact hsy q hq

/-- Real corner connectors have genuine crossing charts against each incident
third curve. The nonzero selected-start intercept forces a nonparallel radial
direction at every actual intersection. -/
theorem actual_signed_radial_fan_piece_chart
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (F : OpenPartialHomeomorph S Plane) (d : Curve S) (a b : Plane)
    (ρ : ℝ) (ha : 0 < a 1) (hb : b 1 < 0)
    (hmodel : ∀ x ∈ F.source, ‖F x‖ < ρ →
      (x ∈ d.image ↔ F x ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b))
    (x0 x1 y1 : ℝ) (hx0 : x0 ≠ 0) (hy1 : y1 ≠ 0)
    (hseg : segment ℝ (Plane.mk x0 0) (Plane.mk x1 y1) ⊆ F.target)
    (p : S) (hp : p ∈ F.symm '' segment ℝ (Plane.mk x0 0) (Plane.mk x1 y1))
    (hpd : p ∈ d.image) (hpn : ‖F p‖ < ρ) (hpy : F p 1 ≠ 0) :
    ∃ E : OpenPartialHomeomorph S (ℝ × ℝ), ∃ α k : ℝ,
      p ∈ E.source ∧ E.source ⊆ F.source ∧
      (∀ x, E x = (F x 1,F x 0-x0-((x1-x0)/y1)*F x 1)) ∧
      (∀ x ∈ (F.symm '' segment ℝ (Plane.mk x0 0) (Plane.mk x1 y1)) ∩ E.source, (E x).2 = 0) ∧
      (∀ x ∈ E.source, x ∈ d.image ↔ (E x).1 = α+k*(E x).2) := by
  obtain ⟨q,hq,hqp⟩ := hp
  have hpF : p ∈ F.source := hqp ▸ F.map_target (hseg hq)
  have hFp : F p = q := by rw [←hqp,F.right_inv (hseg hq)]
  have hFpSeg : F p ∈ segment ℝ (Plane.mk x0 0) (Plane.mk x1 y1) := hFp.symm ▸ hq
  obtain ⟨L,α,k,hValue,hLine,hGraph⟩ := actual_signed_fan_segment_radial_affine_chart
    x0 x1 y1 hx0 hy1 a b (F p) ha hb hpy hFpSeg ((hmodel p hpF hpn).mp hpd)
  let O := F.source ∩ F ⁻¹' (Metric.ball (0 : Plane) ρ ∩ {q : Plane | 0 < q 1*F p 1})
  have hO : IsOpen O := F.isOpen_inter_preimage
    (Metric.isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop)))
  let E0 := (F.restrOpen O hO).transHomeomorph L
  have hpE0 : p ∈ E0.source := ⟨hpF,hpF,by simpa only [Metric.mem_ball,dist_zero_right] using hpn,mul_self_pos.mpr hpy⟩
  have hgraph : ∀ x ∈ d.image ∩ E0.source, (E0 x).1 = α+k*((E0 x).2-0) := by
    intro x hx
    have hxF : x ∈ F.source := hx.2.1
    have hxn : ‖F x‖ < ρ := by simpa only [Metric.mem_ball,dist_zero_right] using hx.2.2.2.1
    have hxy : 0 < F x 1*F p 1 := hx.2.2.2.2
    change (L (F x)).1 = α+k*((L (F x)).2-0)
    simpa only [sub_zero] using hGraph (F x) hxy ((hmodel x hxF hxn).mp hx.1)
  obtain ⟨E,hpE,hSub,hEValue,hAxis⟩ := actual_embedded_curve_local_affine_graph_trace
    d E0 p ⟨hpd,hpE0⟩ 0 α k hgraph
  refine ⟨E,α,k,hpE,(fun x hx => (hSub hx).1),?_,?_,?_⟩
  · intro x
    rw [hEValue]
    exact hValue (F x)
  · rintro x ⟨⟨q,hq,rfl⟩,hx⟩
    rw [hEValue]
    change (L (F (F.symm q))).2 = 0
    rw [F.right_inv (hseg hq)]
    exact hLine q hq
  · intro x hx
    simpa only [sub_zero] using hAxis x hx

end CurveComplex
