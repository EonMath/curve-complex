import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopMeshCenterPerturbation
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual coordinate shift in the supplied embedded old-arc strip. The
homotopy is constructed by the strip embedding and fixes every point whose
supported weight is zero. -/
theorem actual_common_strip_normal_shift_movie
    (M : HyperellipticModel E S)
    (G : C(Interval × Interval,S)) (T : Set (Interval × Interval))
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (hBCmarks : ∀ z,BC z ∉ (M.cover.branch : Set S))
    (Q : C(T,range BC)) (hQ : ∀ z : T,(Q z).val=G z.val)
    (ψ : C(T,ℝ)) (hψ : ∀ z : T,ψ z=((hBC.toHomeomorph.symm (Q z)).2:ℝ))
    (hψbounds : ∀ z : T,-1<ψ z ∧ ψ z<1)
    (weight : C(Interval × Interval,ℝ)) (hweight : ∀ z,0≤weight z)
    (δ : ℝ) (hδ : 0≤δ) (hupper : ∀ z : T,ψ z+δ*weight z.val<1) :
    ∃ J : C(T × Interval,S),
      (∀ z,J (z,0)=G z.val) ∧
      (∀ z σ,weight z.val=0 → J (z,σ)=G z.val) ∧
      (∀ z,J z ∉ (M.cover.branch : Set S)) ∧
      (∀ z,J z=BC ((hBC.toHomeomorph.symm (Q z.1)).1,
        ⟨ψ z.1+z.2.val*δ*weight z.1.val,by
          constructor
          · have hp := (hψbounds z.1).1
            have hs := mul_nonneg (mul_nonneg z.2.property.1 hδ) (hweight z.1.val)
            linarith only [hp,hs]
          · have hs : z.2.val*δ*weight z.1.val≤δ*weight z.1.val :=
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right z.2.property.2 hδ) (hweight z.1.val)).trans
                (by simp only [one_mul]; exact le_rfl)
            exact ((add_le_add le_rfl hs).trans (hupper z.1).le)⟩)) := by
  let normal : C(T × Interval,ℝ) :=
    ⟨fun z => ψ z.1+z.2.val*δ*weight z.1.val,by fun_prop⟩
  have hn (z : T × Interval) : normal z ∈ Icc (-1:ℝ) 1 := by
    have hp := (hψbounds z.1).1
    have hs0 := mul_nonneg (mul_nonneg z.2.property.1 hδ) (hweight z.1.val)
    have hs1 : z.2.val*δ*weight z.1.val≤δ*weight z.1.val := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right z.2.property.2 hδ) (hweight z.1.val)
      simpa only [one_mul] using hh
    constructor
    · change -1≤ψ z.1+z.2.val*δ*weight z.1.val
      linarith only [hp,hs0]
    · exact (add_le_add le_rfl hs1).trans (hupper z.1).le
  let coord : C(T × Interval,Interval × Icc (-1:ℝ) 1) :=
    ⟨fun z => ((hBC.toHomeomorph.symm (Q z.1)).1,⟨normal z,hn z⟩),
      ((continuous_fst.comp (hBC.toHomeomorph.symm.continuous.comp
        (Q.continuous.comp continuous_fst))).prodMk (normal.continuous.subtype_mk hn))⟩
  let J : C(T × Interval,S) := ⟨fun z => BC (coord z),hBC.continuous.comp coord.continuous⟩
  have hfixed (z : T) (σ : Interval) (he : normal (z,σ)=ψ z) : J (z,σ)=G z.val := by
    have hc : coord (z,σ)=hBC.toHomeomorph.symm (Q z) := by
      apply Prod.ext
      · rfl
      apply Subtype.ext
      exact he.trans (hψ z)
    change BC (coord (z,σ))=G z.val
    rw [hc]
    have hh := congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Q z))
    exact hh.trans (hQ z)
  refine ⟨J,?_,?_,(fun z => hBCmarks (coord z)),(fun _ => rfl)⟩
  · intro z
    apply hfixed
    simp [normal]
  · intro z σ hz
    apply hfixed
    simp [normal,hz]
end CurveComplex.HyperellipticModel
