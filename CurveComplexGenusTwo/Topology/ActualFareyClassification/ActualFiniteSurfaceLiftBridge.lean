import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTorusProjectionLocality

open Set Topology Schoenflies CurveComplex

/-- A half-period neighborhood of an actual grid point contains no other
reference fiber; the integer exclusion is proved from the actual coordinates. -/
theorem actual_half_period_grid_has_unique_fiber
    (T c : ℝ) (hT : 0 < T) (i : ℤ) (z : Plane)
    (hz : |z 0-(c+(i:ℝ)*T)| < T/2) :
    (∃ j : ℤ, z 0=c+(j:ℝ)*T) ↔ z 0=c+(i:ℝ)*T := by
  constructor
  · rintro ⟨j,hj⟩
    have hb := abs_lt.mp hz
    have hji : j=i := by
      have hl : (-1:ℝ) < ((j-i:ℤ):ℝ) := by push_cast; nlinarith
      have hu : ((j-i:ℤ):ℝ) < 1 := by push_cast; nlinarith
      have hl' : (-1:ℤ) < j-i := by exact_mod_cast hl
      have hu' : j-i < 1 := by exact_mod_cast hu
      omega
    simpa [hji] using hj
  · exact fun h => ⟨i,h⟩

/-- Actual finite transverse torus data produces the exact finite fiber and
whole-family axis data needed by marked descent. The source/reference image
identities are literal projection identities, not lifted chart certificates. -/
theorem actual_finite_transverse_torus_has_normalized_lift_data
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (c : ℝ)
    (hp : ∀ (i : ℤ) x, G (x+(i:ℝ)*(2*Real.pi))=
      G x+Plane.mk ((i:ℝ)*(2*Real.pi)) 0)
    (hcoll : ∀ (x y : ℝ) (i j : ℤ),
      G x=G y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) → j=0)
    (a b : Curve (Circle×Circle))
    (ha : a.image={z : Circle×Circle | z.1=Circle.exp c})
    (hb : b.image=(fun z : Plane => (Circle.exp (z 0),Circle.exp (z 1))) '' range G)
    (hab : Transverse a b) :
    {t : ℝ | G t 0=c}.Finite ∧
    (∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi)))) →
      q 0=c+(i:ℝ)*(2*Real.pi) →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 0=c+(i:ℝ)*(2*Real.pi) ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi)))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0))) := by
  let π : Plane → Circle×Circle := fun z => (Circle.exp (z 0),Circle.exp (z 1))
  have hpre : π ⁻¹' b.image=⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi))) := by
    rw [hb]
    exact actual_normalized_projection_preimage_is_whole_row_family G (2*Real.pi) rfl hp
  have hgrid (z : Plane) : π z∈a.image ↔ ∃ j : ℤ, z 0=c+(j:ℝ)*(2*Real.pi) := by
    rw [ha]
    exact Circle.exp_eq_exp
  constructor
  · apply hab.1.of_injOn (f:=fun t => π (G t))
    · intro t ht
      refine ⟨?_,?_⟩
      · exact (hgrid (G t)).mpr ⟨0,by simpa using ht⟩
      · rw [hb]
        exact ⟨G t,mem_range_self t,rfl⟩
    · intro x hx y hy hxy
      obtain ⟨i,hi⟩ := Circle.exp_eq_exp.mp (congrArg Prod.fst hxy)
      obtain ⟨j,hj⟩ := Circle.exp_eq_exp.mp (congrArg Prod.snd hxy)
      change G x 0=c at hx
      change G y 0=c at hy
      have hi0 : i=0 := by
        have hz : (i:ℝ)=0 := by nlinarith [Real.pi_pos]
        exact_mod_cast hz
      have hvec : G x=G y+Plane.mk ((i:ℝ)*(2*Real.pi)) ((j:ℝ)*(2*Real.pi)) := by
        ext k
        fin_cases k <;> assumption
      have hj0 := hcoll x y i j hvec
      apply hG.injective
      have hz : Plane.mk 0 0=(0:Plane) := by ext k; fin_cases k <;> rfl
      simpa [hi0,hj0,hz] using hvec
  · intro q i hq hqi
    have hqb : π q∈b.image := by change q∈π ⁻¹' b.image; rw [hpre]; exact hq
    have hqa : π q∈a.image := (hgrid q).mpr ⟨i,hqi⟩
    obtain ⟨U,V,hqU,h,hU,hV,hzero,haxes⟩ :=
      actual_crossing_axis_chart_lifts_through_local_homeomorph π
        actual_plane_exponential_projection_is_local_homeomorph a b q (hab.2 (π q) ⟨hqa,hqb⟩)
    let N : Set Plane := {z | |z 0-(c+(i:ℝ)*(2*Real.pi))| < (2*Real.pi)/2}
    have hN : IsOpen N := isOpen_lt (by fun_prop) continuous_const
    have hqN : q∈N := by simp [N,hqi,Real.pi_pos]
    obtain ⟨W,hW,E,hEval⟩ := actual_crossing_chart_restrict_to_open U V hU hV h N hN
    refine ⟨U∩N,W,⟨hqU,hqN⟩,E,hU.inter hN,hW,?_,?_⟩
    · exact (hEval q ⟨hqU,hqN⟩).trans hzero
    · intro z hz
      have hg := actual_half_period_grid_has_unique_fiber (2*Real.pi) c
        (by positivity) i z hz.2
      have hza := ((hgrid z).trans hg).symm.trans (haxes z hz.1).1
      have hzb : (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi))))) ↔ π z∈b.image := by
        change z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*(2*Real.pi)))) ↔ z∈π ⁻¹' b.image
        rw [hpre]
      have he := hEval z hz
      exact ⟨hza.trans (by rw [he]), hzb.trans ((haxes z hz.1).2.trans (by rw [he]))⟩

#print axioms actual_half_period_grid_has_unique_fiber
#print axioms actual_finite_transverse_torus_has_normalized_lift_data
