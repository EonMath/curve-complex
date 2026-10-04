import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualInitialAxisPortImage
import Mathlib.Topology.Homeomorph.Lemmas
namespace CurveComplex
open Set Topology Schoenflies
/-- An actual chart segment included in an embedded source arc is its whole
initial source prefix. Internality/order and entire-prefix chart containment
follow from the inverse embedding and one-dimensional intermediate values. -/
theorem source_axis_segment_is_initial_source_prefix
    {S : Type} [TopologicalSpace S]
    (f : C(Interval,S)) (hf : IsEmbedding f) (E : OpenPartialHomeomorph S Plane)
    (u : Interval) (hp : f 0 ∈ E.source) (hzero : E (f 0)=0)
    (huE : f u ∈ E.source) (hu0 : E (f u) 0=0)
    (huheight : 0<E (f u) 1 ∧ E (f u) 1≤1/8)
    (hsquare : Plane.closedSquare 0 1 ⊆ E.target)
    (hsegment : ∀ x ∈ E.source, E x 0=0 → 0≤E x 1 → E x 1≤E (f u) 1 → x ∈ Set.range f) :
    f '' Set.Icc (0:Interval) u =
      {x : S | x ∈ E.source ∧ E x 0=0 ∧ 0≤E x 1 ∧ E x 1≤E (f u) 1} ∧
      (∀ t : Interval, t≤u → f t ∈ E.source) ∧
      ∀ t : Interval, f t ∈ E.source → E (f t) 0=0 →
        0≤E (f t) 1 → E (f t) 1≤E (f u) 1 → t≤u := by
  classical
  let h : ℝ := E (f u) 1
  let j : Interval → S := fun t=>E.symm (Plane.mk 0 ((t:ℝ)*h))
  have htarget (t : Interval) : Plane.mk 0 ((t:ℝ)*h) ∈ E.target := hsquare (by
    rw [mem_closedSquare_zero_one]
    change max |(0:ℝ)| |(t:ℝ)*h|≤1
    apply max_le
    · norm_num
    · change |(t:ℝ)*h|≤1
      have hnon : 0≤(t:ℝ)*h := mul_nonneg t.property.1 huheight.1.le
      rw [abs_of_nonneg hnon]
      have hh := mul_le_mul_of_nonneg_right t.property.2 huheight.1.le
      dsimp [h] at *
      linarith)
  have hjs (t) : j t ∈ E.source := E.map_target (htarget t)
  have hjE (t) : E (j t)=Plane.mk 0 ((t:ℝ)*h) := E.right_inv (htarget t)
  have hjrange (t) : j t ∈ Set.range f := hsegment (j t) (hjs t)
    (by rw [hjE]; rfl) (by rw [hjE]; exact mul_nonneg t.property.1 huheight.1.le)
    (by rw [hjE]; exact mul_le_of_le_one_left huheight.1.le t.property.2)
  let jR : Interval → Set.range f := fun t=>⟨j t,hjrange t⟩
  have hjc : Continuous j := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (E.symm.continuousAt (htarget t)).comp
      (f := fun s : Interval=>Plane.mk 0 ((s:ℝ)*h)) (by fun_prop)
  let g : C(Interval,Interval) := ⟨fun t=>hf.toHomeomorph.symm (jR t),
    hf.toHomeomorph.symm.continuous.comp (hjc.subtype_mk hjrange)⟩
  have hfg (t) : f (g t)=j t := by
    have hh := hf.toHomeomorph.apply_symm_apply (jR t)
    exact congrArg Subtype.val hh
  have hg0 : g 0=0 := by
    apply hf.injective
    rw [hfg]
    apply E.injOn (hjs 0) hp
    rw [hjE,hzero]
    ext k
    fin_cases k <;> norm_num
  have hg1 : g 1=u := by
    apply hf.injective
    rw [hfg]
    apply E.injOn (hjs 1) huE
    rw [hjE]
    ext k
    fin_cases k
    · exact hu0.symm
    · change (1:ℝ)*h=E (f u) 1; simp [h]
  have hgi : Function.Injective g := by
    intro s t he
    have hh := congrArg (fun x : S=>E x 1) (congrArg f he)
    rw [hfg,hfg,hjE,hjE] at hh
    apply Subtype.ext
    change (s:ℝ)*h=(t:ℝ)*h at hh
    exact mul_right_cancel₀ huheight.1.ne' hh
  have hgm : StrictMono g := by
    rcases g.continuous.strictMono_of_inj_boundedOrder' hgi with hm|hm
    · exact hm
    · have hh := hm (by norm_num : (0:Interval)<1)
      rw [hg0,hg1] at hh
      exact ((not_lt_of_ge u.property.1) hh).elim
  have hu : 0<(u:ℝ) := by have hh := hgm (by norm_num : (0:Interval)<1); rw [hg0,hg1] at hh; exact hh
  have hI : Set.Icc (0:Interval) 1=Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact ⟨t.property.1,t.property.2⟩
  have hgrange : Set.range g=Set.Icc (0:Interval) u := by
    rw [← Set.image_univ,hI.symm,g.continuous.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0:Interval)≤1) (hgm.monotone.monotoneOn _),hg0,hg1]
  have hprefix (t : Interval) (ht : t≤u) : f t ∈ E.source := by
    obtain ⟨s,hs⟩ := hgrange.symm ▸ (show t ∈ Set.Icc (0:Interval) u from ⟨t.property.1,ht⟩)
    rw [← hs,hfg]
    exact hjs s
  have haxis (t : Interval) (ht : t≤u) : E (f t) 0=0 := by
    obtain ⟨s,hs⟩ := hgrange.symm ▸ (show t ∈ Set.Icc (0:Interval) u from ⟨t.property.1,ht⟩)
    rw [← hs,hfg,hjE]
    rfl
  obtain ⟨himage,horder⟩ := source_initial_axis_port_exact_image f hf E u hu hprefix hzero haxis huheight.1
  exact ⟨himage,hprefix,horder⟩
end CurveComplex
#print axioms CurveComplex.source_axis_segment_is_initial_source_prefix
