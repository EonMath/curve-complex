import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualCompactParameterBall
namespace CurveComplex
open Set Topology Schoenflies
/-- An ACTUAL uniform displacement radius places every truncated translated
corner trace in a prescribed open neighborhood of its original two legs.
The radius is constructed by compact continuous affine families. -/
theorem source_translated_truncated_corner_trace_in_open
    {S : Type} [TopologicalSpace S]
    (E : OpenPartialHomeomorph S Plane)
    (hsquare : Plane.closedSquare 0 1 ⊆ E.target)
    (h0 h1 : ℝ) (hh0 : 0<h0 ∧ h0≤1/8) (hh1 : 0<h1 ∧ h1≤1/8)
    (W : Set S) (hW : IsOpen W)
    (hlegs : ∀ x ∈ E.source,
      (E x 0=0 ∧ 0≤E x 1 ∧ E x 1≤h0) ∨ (0≤E x 0 ∧ E x 0≤h1 ∧ E x 1=0) → x ∈ W) :
    ∃ r : ℝ, 0<r ∧ r≤1/32 ∧ r ≤ (min h0 h1)/4 ∧
      ∀ v : Plane, ‖v‖<r → ∀ x ∈ E.source,
        (E x 0=v 0 ∧ v 1≤E x 1 ∧ E x 1≤h0) ∨ (v 0≤E x 0 ∧ E x 0≤h1 ∧ E x 1=v 1) → x ∈ W := by
  let O : Set Plane := E '' (E.source ∩ W)
  have hO : IsOpen O := E.isOpen_image_source_inter hW
  have haxes (p : Plane) (hp : (p 0=0 ∧ 0≤p 1 ∧ p 1≤h0) ∨ (0≤p 0 ∧ p 0≤h1 ∧ p 1=0)) : p ∈ O := by
    have hpt : p ∈ E.target := hsquare (by
      rw [mem_closedSquare_zero_one]
      rcases hp with hp|hp
      · change max |p 0| |p 1|≤1
        rw [hp.1,abs_zero,abs_of_nonneg hp.2.1]
        exact max_le (by norm_num) (hp.2.2.trans (by linarith [hh0.2]))
      · change max |p 0| |p 1|≤1
        rw [hp.2.2,abs_zero,abs_of_nonneg hp.1]
        exact max_le (hp.2.1.trans (by linarith [hh1.2])) (by norm_num))
    have hs : E.symm p ∈ E.source := E.map_target hpt
    have he : E (E.symm p)=p := E.right_inv hpt
    exact ⟨E.symm p,⟨hs,hlegs _ hs (he.symm ▸ hp)⟩,he⟩
  let f0 : C(Interval × Plane,Plane) := ⟨fun q=>Plane.mk (q.2 0) ((1-(q.1:ℝ))*h0+(q.1:ℝ)*q.2 1),by fun_prop⟩
  let f1 : C(Interval × Plane,Plane) := ⟨fun q=>Plane.mk ((1-(q.1:ℝ))*q.2 0+(q.1:ℝ)*h1) (q.2 1),by fun_prop⟩
  have hf0 (t : Interval) : f0 (t,0) ∈ O := haxes _ (Or.inl ⟨rfl,by
    change 0≤(1-(t:ℝ))*h0+(t:ℝ)*(0:ℝ) ∧ (1-(t:ℝ))*h0+(t:ℝ)*(0:ℝ)≤h0
    constructor <;> nlinarith [t.property.1,t.property.2,hh0.1]⟩)
  have hf1 (t : Interval) : f1 (t,0) ∈ O := haxes _ (Or.inr ⟨by
    change 0≤(1-(t:ℝ))*(0:ℝ)+(t:ℝ)*h1
    nlinarith [t.property.1,hh1.1],by
    change (1-(t:ℝ))*(0:ℝ)+(t:ℝ)*h1≤h1
    nlinarith [t.property.2,hh1.1],rfl⟩)
  obtain ⟨r0,hr0,hball0⟩ := source_compact_plane_parameter_uniform_open_ball Interval f0 O hO hf0
  obtain ⟨r1,hr1,hball1⟩ := source_compact_plane_parameter_uniform_open_ball Interval f1 O hO hf1
  let r := min (min r0 r1) (min (1/32) (min h0 h1/4))
  have hr : 0<r := lt_min (lt_min hr0 hr1) (lt_min (by norm_num) (div_pos (lt_min hh0.1 hh1.1) (by norm_num)))
  have hrr0 : r≤r0 := (min_le_left _ _).trans (min_le_left _ _)
  have hrr1 : r≤r1 := (min_le_left _ _).trans (min_le_right _ _)
  have hr32 : r≤1/32 := (min_le_right _ _).trans (min_le_left _ _)
  have hrh : r ≤ (min h0 h1)/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,hr32,hrh,?_⟩
  intro v hv x hx hshape
  have hv0 : v 0<h1 := by
    have hh := (le_abs_self (v 0)).trans ((Plane.abs_zero_le_supNorm v).trans (Plane.supNorm_le_norm v))
    have hmin := min_le_right h0 h1
    linarith
  have hv1 : v 1<h0 := by
    have hh := (le_abs_self (v 1)).trans ((Plane.abs_one_le_supNorm v).trans (Plane.supNorm_le_norm v))
    have hmin := min_le_left h0 h1
    linarith
  have hxO : E x ∈ O := by
    rcases hshape with hh|hh
    · let t : Interval := ⟨(h0-E x 1)/(h0-v 1),by
        constructor
        · exact div_nonneg (by linarith [hh.2.2]) (by linarith)
        · apply (div_le_one (by linarith : 0<h0-v 1)).mpr
          linarith [hh.2.1]⟩
      have he : f0 (t,v)=E x := by
        ext j
        fin_cases j
        · exact hh.1.symm
        · change (1-(h0-E x 1)/(h0-v 1))*h0+((h0-E x 1)/(h0-v 1))*v 1=E x 1
          have hmul := div_mul_cancel₀ (h0-E x 1) (by linarith : h0-v 1≠0)
          nlinarith
      exact he ▸ hball0 t v (hv.trans_le hrr0)
    · let t : Interval := ⟨(E x 0-v 0)/(h1-v 0),by
        constructor
        · exact div_nonneg (by linarith [hh.1]) (by linarith)
        · apply (div_le_one (by linarith : 0<h1-v 0)).mpr
          linarith [hh.2.1]⟩
      have he : f1 (t,v)=E x := by
        ext j
        fin_cases j
        · change (1-(E x 0-v 0)/(h1-v 0))*v 0+((E x 0-v 0)/(h1-v 0))*h1=E x 0
          have hmul := div_mul_cancel₀ (E x 0-v 0) (by linarith : h1-v 0≠0)
          nlinarith
        · exact hh.2.2.symm
      exact he ▸ hball1 t v (hv.trans_le hrr1)
  obtain ⟨y,hy,he⟩ := hxO
  have hyx : y=x := E.injOn hy.1 hx he
  exact hyx ▸ hy.2
end CurveComplex
#print axioms CurveComplex.source_translated_truncated_corner_trace_in_open
