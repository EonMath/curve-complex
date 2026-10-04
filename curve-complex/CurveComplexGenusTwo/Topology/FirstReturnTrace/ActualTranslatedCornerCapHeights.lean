import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualTranslatedCornerCrossings
import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualEmbeddedArcConcatenation
namespace CurveComplex
open Set Topology Schoenflies
/-- Produce an actual embedded corner cap lying on the WHOLE translated
curve. Its outer ports have fixed positive longitudinal height, so they can
be identified with framed first/closing tracks by chart injectivity. -/
theorem source_translated_corner_embedded_cap_with_heights
    {S : Type} [TopologicalSpace S] [T2Space S]
    (d : Curve S) (E : OpenPartialHomeomorph S Plane)
    (hsquare : Plane.closedSquare 0 1 ⊆ E.target)
    (h0 h1 : ℝ) (hh0 : 0<h0 ∧ h0≤1/8) (hh1 : 0<h1 ∧ h1≤1/8)
    (v : Plane) (hv : ‖v‖ < min h0 h1/4)
    (hd : ∀ x ∈ E.source, ‖E x-v‖≤1/4 →
      (x ∈ d.image ↔
        (E x 0=v 0 ∧ v 1≤E x 1) ∨ (v 0≤E x 0 ∧ E x 1=v 1))) :
    ∃ f : C(Interval,S), IsEmbedding f ∧ Set.range f ⊆ E.source ∩ d.image ∧
      (∀ x ∈ Set.range f, ‖E x-v‖<1/4) ∧
      E (f 0)=Plane.mk (v 0) h0 ∧ E (f 1)=Plane.mk h1 (v 1) ∧
      E.symm v ∈ Set.range f ∧
      Set.range f =
        {x : S | x ∈ E.source ∧ E x 0=v 0 ∧ v 1≤E x 1 ∧ E x 1≤h0} ∪
        {x : S | x ∈ E.source ∧ v 0≤E x 0 ∧ E x 0≤h1 ∧ E x 1=v 1} := by
  have hsmall : ‖v‖<1/32 := hv.trans_le (by
    have hm := min_le_left h0 h1
    nlinarith [hh0.2])
  have hv0 : |v 0|<1/32 := (Plane.supNorm_le_norm v).trans_lt hsmall |>.trans_le' (le_max_left _ _)
  have hv1 : |v 1|<1/32 := (Plane.supNorm_le_norm v).trans_lt hsmall |>.trans_le' (le_max_right _ _)
  have hvx : v 0<h1 := by
    have hn := (Plane.supNorm_le_norm v).trans_lt hv
    have hb : |v 0| < min h0 h1/4 := (le_max_left _ _).trans_lt hn
    have hm := min_le_right h0 h1
    nlinarith [le_abs_self (v 0),hh1.1]
  have hvy : v 1<h0 := by
    have hn := (Plane.supNorm_le_norm v).trans_lt hv
    have hb : |v 1| < min h0 h1/4 := (le_max_right _ _).trans_lt hn
    have hm := min_le_left h0 h1
    nlinarith [le_abs_self (v 1),hh0.1]
  let z0 : Interval → Plane := fun t => Plane.mk (v 0) ((1-(t:ℝ))*h0+(t:ℝ)*v 1)
  let z1 : Interval → Plane := fun t => Plane.mk ((1-(t:ℝ))*v 0+(t:ℝ)*h1) (v 1)
  have hb0 (t : Interval) : v 1≤z0 t 1 ∧ z0 t 1≤h0 := by
    change v 1≤(1-(t:ℝ))*h0+(t:ℝ)*v 1 ∧ (1-(t:ℝ))*h0+(t:ℝ)*v 1≤h0
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hb1 (t : Interval) : v 0≤z1 t 0 ∧ z1 t 0≤h1 := by
    change v 0≤(1-(t:ℝ))*v 0+(t:ℝ)*h1 ∧ (1-(t:ℝ))*v 0+(t:ℝ)*h1≤h1
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hz0 (t : Interval) : z0 t ∈ E.target := by
    apply hsquare
    rw [mem_closedSquare_zero_one]
    change max |v 0| |z0 t 1|≤1
    exact max_le (hv0.le.trans (by norm_num)) (abs_le.mpr ⟨by linarith [hb0 t |>.1,neg_le_abs (v 1)],by linarith [hb0 t |>.2,hh0.2]⟩)
  have hz1 (t : Interval) : z1 t ∈ E.target := by
    apply hsquare
    rw [mem_closedSquare_zero_one]
    change max |z1 t 0| |v 1|≤1
    exact max_le (abs_le.mpr ⟨by linarith [hb1 t |>.1,neg_le_abs (v 0)],by linarith [hb1 t |>.2,hh1.2]⟩) (hv1.le.trans (by norm_num))
  have hn0 (t : Interval) : ‖z0 t-v‖<1/4 := by
    have he : z0 t-v=Plane.mk 0 (z0 t 1-v 1) := by
      ext j
      fin_cases j
      · change v 0-v 0=0; ring
      · rfl
    rw [he]
    simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
    rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (by linarith [hb0 t |>.1])]
    linarith [hb0 t |>.2,neg_le_abs (v 1),hh0.2]
  have hn1 (t : Interval) : ‖z1 t-v‖<1/4 := by
    have he : z1 t-v=Plane.mk (z1 t 0-v 0) 0 := by
      ext j
      fin_cases j
      · rfl
      · change v 1-v 1=0; ring
    rw [he]
    simp [EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
    rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (by linarith [hb1 t |>.1])]
    linarith [hb1 t |>.2,neg_le_abs (v 0),hh1.2]
  let f : C(Interval,S) := ⟨E.symm ∘ z0,E.continuousOn_symm.comp_continuous (by dsimp [z0]; fun_prop) hz0⟩
  let g : C(Interval,S) := ⟨E.symm ∘ z1,E.continuousOn_symm.comp_continuous (by dsimp [z1]; fun_prop) hz1⟩
  have hfs (t) : f t ∈ E.source := E.symm.map_source (hz0 t)
  have hgs (t) : g t ∈ E.source := E.symm.map_source (hz1 t)
  have hfc (t) : E (f t)=z0 t := E.right_inv (hz0 t)
  have hgc (t) : E (g t)=z1 t := E.right_inv (hz1 t)
  have hfi : Function.Injective f := by
    intro t u he
    have hh := congrArg (fun x => E x 1) he
    rw [hfc,hfc] at hh
    apply Subtype.ext
    dsimp [z0,Plane.mk] at hh
    nlinarith
  have hgi : Function.Injective g := by
    intro t u he
    have hh := congrArg (fun x => E x 0) he
    rw [hgc,hgc] at hh
    apply Subtype.ext
    dsimp [z1,Plane.mk] at hh
    nlinarith
  have hfg : f 1=g 0 := by simp [f,g,z0,z1,Plane.mk]
  have hmeet : Set.range f ∩ Set.range g={f 1} := by
    ext x
    constructor
    · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
      apply Set.mem_singleton_iff.mpr
      apply E.injOn (hfs t) (hfs 1)
      have hh := congrArg (fun x => E x 1) hu
      rw [hgc,hfc] at hh
      rw [hfc,hfc]
      ext j
      fin_cases j
      · rfl
      · simpa [z0,z1,Plane.mk] using hh.symm
    · rintro rfl
      exact ⟨Set.mem_range_self _,⟨0,hfg.symm⟩⟩
  obtain ⟨h,hh,hzero,hone,himage⟩ := source_embedded_arc_concatenation f g
    (f.continuous.isClosedEmbedding hfi).isEmbedding (g.continuous.isClosedEmbedding hgi).isEmbedding hfg hmeet
  have hfD (t) : f t ∈ d.image := by
    apply (hd (f t) (hfs t) (by rw [hfc]; exact (hn0 t).le)).mpr
    rw [hfc]
    exact Or.inl ⟨rfl,(hb0 t).1⟩
  have hgD (t) : g t ∈ d.image := by
    apply (hd (g t) (hgs t) (by rw [hgc]; exact (hn1 t).le)).mpr
    rw [hgc]
    exact Or.inr ⟨(hb1 t).1,rfl⟩
  refine ⟨h,hh,?_,?_,?_,?_,?_,?_⟩
  · rw [himage]
    rintro x (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · exact ⟨hfs t,hfD t⟩
    · exact ⟨hgs t,hgD t⟩
  · rw [himage]
    rintro x (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · rw [hfc]; exact hn0 t
    · rw [hgc]; exact hn1 t
  · rw [hzero,hfc]; simp [z0,Plane.mk]
  · rw [hone,hgc]; simp [z1,Plane.mk]
  · rw [himage]
    left
    refine ⟨1,?_⟩
    simp [f,z0,Plane.mk]
    congr 1
    ext j
    fin_cases j <;> rfl
  · rw [himage]
    congr 1
    · ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨hfs t,by rw [hfc]; rfl,by rw [hfc]; exact (hb0 t).1,by rw [hfc]; exact (hb0 t).2⟩
      · rintro ⟨hx,hx0,hxlo,hxhi⟩
        let t : Interval := ⟨(h0-E x 1)/(h0-v 1),by
          constructor
          · exact div_nonneg (by linarith) (by linarith)
          · apply (div_le_one (by linarith : 0<h0-v 1)).mpr; linarith⟩
        refine ⟨t,?_⟩
        apply E.injOn (hfs t) hx
        rw [hfc]
        ext j
        fin_cases j
        · exact hx0.symm
        · change (1-(h0-E x 1)/(h0-v 1))*h0+((h0-E x 1)/(h0-v 1))*v 1=E x 1
          have hmul := div_mul_cancel₀ (h0-E x 1) (by linarith : h0-v 1≠0)
          nlinarith
    · ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨hgs t,by rw [hgc]; exact (hb1 t).1,by rw [hgc]; exact (hb1 t).2,by rw [hgc]; rfl⟩
      · rintro ⟨hx,hxlo,hxhi,hx1⟩
        let t : Interval := ⟨(E x 0-v 0)/(h1-v 0),by
          constructor
          · exact div_nonneg (by linarith) (by linarith)
          · apply (div_le_one (by linarith : 0<h1-v 0)).mpr; linarith⟩
        refine ⟨t,?_⟩
        apply E.injOn (hgs t) hx
        rw [hgc]
        ext j
        fin_cases j
        · change (1-(E x 0-v 0)/(h1-v 0))*v 0+((E x 0-v 0)/(h1-v 0))*h1=E x 0
          have hmul := div_mul_cancel₀ (E x 0-v 0) (by linarith : h1-v 0≠0)
          nlinarith
        · exact hx1.symm
end CurveComplex
#print axioms CurveComplex.source_translated_corner_embedded_cap_with_heights
