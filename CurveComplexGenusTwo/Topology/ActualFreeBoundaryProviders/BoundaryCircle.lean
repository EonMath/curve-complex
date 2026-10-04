import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.AffineCircleCore

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Metric

theorem chartSphere_curve (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (E : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2))) (p : (EuclideanSpace ℝ (Fin 2))) (R : ℝ) (hR : 0<R)
    (htarget : closedBall p R ⊆ E.target) :
    ∃ c : Curve S, c.image=E.symm '' sphere p R := by
  classical
  let L : ℂ ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)) := Complex.equivRealProdCLM.trans
    ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
      (EuclideanSpace.equiv (Fin 2) ℝ).symm)
  have hnorm (z : ℂ) : ‖L z‖ = ‖z‖ := by
    simp [L, EuclideanSpace.norm_eq, Fin.sum_univ_two,
      Complex.norm_def, Complex.normSq_apply, Real.norm_eq_abs, pow_two]
  let q : Circle → (EuclideanSpace ℝ (Fin 2)) := fun z => p+R • L (z:ℂ)
  have hqmem (z : Circle) : q z∈sphere p R := by
    rw [mem_sphere,dist_eq_norm]
    dsimp [q]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hnorm,Circle.norm_coe,mul_one]
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqi : Function.Injective q := by
    intro z w he
    have hs : R • L (z:ℂ)=R • L (w:ℂ) := add_left_cancel he
    exact Subtype.ext (L.injective ((smul_right_injective (EuclideanSpace ℝ (Fin 2)) hR.ne') hs))
  have hqr : range q=sphere p R := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact hqmem z
    · intro hy
      let v : (EuclideanSpace ℝ (Fin 2)) := R⁻¹ • (y-p)
      have hv : ‖v‖=1 := by
        dsimp [v]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
        have hn : ‖y-p‖=R := by simpa [mem_sphere,dist_eq_norm] using hy
        rw [hn,inv_mul_cancel₀ hR.ne']
      have hz : ‖L.symm v‖=1 := by rw [←hnorm (L.symm v),L.apply_symm_apply,hv]
      let z : Circle := ⟨L.symm v,by change L.symm v∈sphere (0:ℂ) 1; simpa only [mem_sphere,dist_zero_right] using hz⟩
      refine ⟨z,?_⟩
      dsimp [q,z]
      rw [L.apply_symm_apply]
      dsimp [v]
      rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul]
      abel
  have hqt (z : Circle) : q z∈E.target := htarget (sphere_subset_closedBall (hqmem z))
  let f : Circle → S := E.symm ∘ q
  have hfc : Continuous f := E.continuousOn_symm.comp_continuous hqc hqt
  have hfi : Function.Injective f := by
    intro z w he
    exact hqi (E.symm.injOn (hqt z) (hqt w) he)
  let c : Curve S := ⟨f,(hfc.isClosedEmbedding hfi).isEmbedding⟩
  refine ⟨c,?_⟩
  change range (E.symm ∘ q)=_
  rw [range_comp,hqr]


lemma actual_boundary_circle
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    Nonempty (Circle ≃ₜ B) := by
  intro Q B
  let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
  obtain ⟨c, hc⟩ := chartSphere_curve S E (E x) R hR htarget
  have hmem (z : Circle) : c.map z ∈ E.symm '' sphere (E x) R := by
    rw [← hc]; exact mem_range_self z
  have hQ (z : Circle) : c.map z ∈ Q := by
    rintro ⟨u, hu, heu⟩
    obtain ⟨v, hv, hev⟩ := hmem z
    have huv : u = v := E.symm.injOn (htarget (ball_subset_closedBall hu))
      (htarget (sphere_subset_closedBall hv)) (heu.trans hev.symm)
    exact (ne_of_lt (mem_ball.mp hu)) (huv ▸ mem_sphere.mp hv)
  let f : Circle → B := fun z => ⟨⟨c.map z, hQ z⟩, hmem z⟩
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact c.embedded.continuous
  have hfi : Function.Injective f := by
    intro z w he
    exact c.embedded.injective (congrArg (fun y : B => y.val.val) he)
  have hfs : Function.Surjective f := by
    intro y
    have hy : y.val.val ∈ c.image := hc.symm ▸ y.property
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, Subtype.ext (Subtype.ext hz)⟩
  have hf := hfc.isClosedEmbedding hfi
  let e := hf.isEmbedding.toHomeomorph
  have hr : range f = univ := Set.range_eq_univ.mpr hfs
  exact ⟨e.trans ((Homeomorph.setCongr hr).trans (Homeomorph.Set.univ B))⟩

end CoherentEndpointMotion.FreeBoundaryContactRepair
