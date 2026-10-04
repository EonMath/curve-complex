import CurveComplexGenusTwo.Hyperbolic.OriginalG1.OriginalLoopDefinitions

namespace CurveComplex.Hyperbolic

private theorem actual_circle_homeomorph_conjugated_rotated_inverse_free_homotopic_inverse
    (e : Circle ≃ₜ Circle) (u : Circle) :
    FreeHomotopic
      ⟨fun z => e (u * (e.symm z)⁻¹), by fun_prop⟩
      ⟨fun z => z⁻¹, by fun_prop⟩ := by
  let lift (φ : Circle ≃ₜ Circle) :
      ∃ ψ : ℝ ≃ₜ ℝ, ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t) := by
    let f : C(ℝ, Circle) := ⟨fun t => φ (Circle.exp t),
      φ.continuous.comp Circle.exp.continuous⟩
    obtain ⟨a, ha⟩ := Circle.exp_surjective (f 0)
    obtain ⟨F, hF, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 a ha
    let g : C(ℝ, Circle) := ⟨fun t => φ.symm (Circle.exp t),
      φ.symm.continuous.comp Circle.exp.continuous⟩
    have hg : Circle.exp 0 = g a := by
      change Circle.exp 0 = φ.symm (Circle.exp a)
      rw [ha]
      exact (φ.symm_apply_apply (Circle.exp 0)).symm
    obtain ⟨G, hG, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g a 0 hg
    have hFl (t : ℝ) : Circle.exp (F t) = φ (Circle.exp t) := congrFun hF.2 t
    have hGl (t : ℝ) : Circle.exp (G t) = φ.symm (Circle.exp t) := congrFun hG.2 t
    have hGF : (fun t => G (F t)) = id := by
      refine Circle.isCoveringMap_exp.eq_of_comp_eq
        (G.continuous.comp F.continuous) continuous_id ?_ 0 ?_
      · funext t
        change Circle.exp (G (F t)) = Circle.exp t
        rw [hGl, hFl]
        exact φ.symm_apply_apply _
      · change G (F 0) = 0
        rw [hF.1, hG.1]
    have hFG : (fun t => F (G t)) = id := by
      refine Circle.isCoveringMap_exp.eq_of_comp_eq
        (F.continuous.comp G.continuous) continuous_id ?_ a ?_
      · funext t
        change Circle.exp (F (G t)) = Circle.exp t
        rw [hFl, hGl]
        exact φ.apply_symm_apply _
      · change F (G a) = a
        rw [hG.1, hF.1]
    let ψ : ℝ ≃ₜ ℝ :=
      { toFun := F
        invFun := G
        left_inv := fun t => congrFun hGF t
        right_inv := fun t => congrFun hFG t
        continuous_toFun := F.continuous
        continuous_invFun := G.continuous }
    exact ⟨ψ, fun t => congrFun hF.2 t⟩
  let drift (φ : Circle ≃ₜ Circle) (ψ : ℝ ≃ₜ ℝ)
      (hψ : ∀ t : ℝ, Circle.exp (ψ t) = φ (Circle.exp t)) :
      ∃ n : ℤ, ∀ t : ℝ, ψ (t + 2 * Real.pi) = ψ t + (n : ℝ) * (2 * Real.pi) := by
    have hbase : Circle.exp (ψ (2 * Real.pi)) = Circle.exp (ψ 0) := by
      rw [hψ, hψ, Circle.exp_two_pi, Circle.exp_zero]
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hbase
    refine ⟨n, ?_⟩
    have heq : (fun t : ℝ => ψ (t + 2 * Real.pi)) =
        (fun t : ℝ => ψ t + (n : ℝ) * (2 * Real.pi)) := by
      refine Circle.isCoveringMap_exp.eq_of_comp_eq
        (ψ.continuous.comp (continuous_id.add continuous_const))
        (ψ.continuous.add continuous_const) ?_ 0 ?_
      · funext t
        change Circle.exp (ψ (t + 2 * Real.pi)) =
          Circle.exp (ψ t + (n : ℝ) * (2 * Real.pi))
        rw [hψ, Circle.exp_add_two_pi, Circle.exp_add,
          Circle.exp_int_mul_two_pi, mul_one, hψ]
      · simpa only [zero_add] using hn
    exact fun t => congrFun heq t
  obtain ⟨ψ, hψ⟩ := lift e
  obtain ⟨n, hn⟩ := drift e ψ hψ
  have hG (t : ℝ) : Circle.exp (ψ.symm t) = e.symm (Circle.exp t) := by
    have h := congrArg e.symm (hψ (ψ.symm t))
    simpa only [ψ.apply_symm_apply, e.symm_apply_apply] using h.symm
  obtain ⟨m, hm⟩ := drift e.symm ψ.symm hG
  have hnm : n * m = 1 := by
    let error (t : ℝ) := ψ t - (n : ℝ) * t
    have hperiodic : Function.Periodic error (2 * Real.pi) := by
      intro t
      dsimp [error]
      rw [hn]
      ring
    have hshift := hperiodic.zsmul m (ψ.symm 0)
    have hshift' : ψ (ψ.symm 0 + (m : ℝ) * (2 * Real.pi)) =
        ψ (ψ.symm 0) + (n : ℝ) * (m : ℝ) * (2 * Real.pi) := by
      dsimp [error] at hshift
      simp only [zsmul_eq_mul] at hshift
      linarith
    have hone : (n : ℝ) * (m : ℝ) = 1 := by
      rw [← hm 0, ψ.apply_symm_apply, ψ.apply_symm_apply] at hshift'
      have hp := Real.pi_pos
      nlinarith
    exact_mod_cast hone
  have hψshift (k : ℤ) (t : ℝ) :
      ψ (t + (k : ℝ) * (2 * Real.pi)) =
        ψ t + (n : ℝ) * (k : ℝ) * (2 * Real.pi) := by
    let error (x : ℝ) := ψ x - (n : ℝ) * x
    have hperiodic : Function.Periodic error (2 * Real.pi) := by
      intro x
      dsimp [error]
      rw [hn]
      ring
    have hshift := hperiodic.zsmul k t
    dsimp [error] at hshift
    simp only [zsmul_eq_mul] at hshift
    linarith
  have hGshift (k : ℤ) (t : ℝ) :
      ψ.symm (t + (k : ℝ) * (2 * Real.pi)) =
        ψ.symm t + (m : ℝ) * (k : ℝ) * (2 * Real.pi) := by
    let error (x : ℝ) := ψ.symm x - (m : ℝ) * x
    have hperiodic : Function.Periodic error (2 * Real.pi) := by
      intro x
      dsimp [error]
      rw [hm]
      ring
    have hshift := hperiodic.zsmul k t
    dsimp [error] at hshift
    simp only [zsmul_eq_mul] at hshift
    linarith
  obtain ⟨a, ha⟩ := Circle.exp_surjective u
  let F (t : ℝ) : ℝ := ψ (a - ψ.symm t)
  have hFexp (t : ℝ) :
      Circle.exp (F t) = e (u * (e.symm (Circle.exp t))⁻¹) := by
    dsimp [F]
    rw [hψ, Circle.exp_sub, ha, hG]
    rfl
  have hFshift (k : ℤ) (t : ℝ) :
      F (t + (k : ℝ) * (2 * Real.pi)) =
        F t - (k : ℝ) * (2 * Real.pi) := by
    dsimp [F]
    rw [hGshift]
    have harg : a - (ψ.symm t + (m : ℝ) * (k : ℝ) * (2 * Real.pi)) =
        (a - ψ.symm t) + ((-m * k : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      ring
    rw [harg, hψshift]
    have hnmR : (n : ℝ) * (m : ℝ) = 1 := by exact_mod_cast hnm
    push_cast
    calc
      ψ (a - ψ.symm t) + (n : ℝ) * (-(m : ℝ) * (k : ℝ)) * (2 * Real.pi) =
          ψ (a - ψ.symm t) - ((n : ℝ) * (m : ℝ)) * (k : ℝ) * (2 * Real.pi) := by ring
      _ = ψ (a - ψ.symm t) - (k : ℝ) * (2 * Real.pi) := by rw [hnmR]; ring
  let L (p : ℝ × Interval) : ℝ :=
    (1 - (p.2 : ℝ)) * F p.1 - (p.2 : ℝ) * p.1
  have hLshift (k : ℤ) (p : ℝ × Interval) :
      L (p.1 + (k : ℝ) * (2 * Real.pi), p.2) =
        L p - (k : ℝ) * (2 * Real.pi) := by
    dsimp [L]
    rw [hFshift]
    ring
  let Lcircle (p : ℝ × Interval) : Circle := Circle.exp (L p)
  have hLcircle_cont : Continuous Lcircle := by
    dsimp [Lcircle, L, F]
    fun_prop
  have hLcircle_eq (p q : ℝ × Interval)
      (hpq : Prod.map Circle.exp (id : Interval → Interval) p =
        Prod.map Circle.exp (id : Interval → Interval) q) :
      Lcircle p = Lcircle q := by
    change (Circle.exp p.1, p.2) = (Circle.exp q.1, q.2) at hpq
    have htime : p.2 = q.2 := congrArg (fun x : Circle × Interval => x.2) hpq
    have hcircle : Circle.exp p.1 = Circle.exp q.1 :=
      congrArg (fun x : Circle × Interval => x.1) hpq
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hcircle
    have hp : p = (q.1 + (k : ℝ) * (2 * Real.pi), q.2) := by
      cases p
      cases q
      simp_all only
    rw [hp]
    dsimp [Lcircle]
    rw [hLshift, Circle.exp_sub, Circle.exp_int_mul_two_pi, div_one]
  let rep (z : Circle) : ℝ := Classical.choose (Circle.exp_surjective z)
  have hrep (z : Circle) : Circle.exp (rep z) = z :=
    Classical.choose_spec (Circle.exp_surjective z)
  let H (p : Circle × Interval) : Circle := Lcircle (rep p.1, p.2)
  have hquot : Topology.IsQuotientMap (Prod.map Circle.exp (id : Interval → Interval)) :=
    (Circle.isCoveringMap_exp.isOpenMap.prodMap IsOpenMap.id).isQuotientMap
      (Circle.exp.continuous.prodMap continuous_id)
      (Circle.exp_surjective.prodMap Function.surjective_id)
  have hHcont : Continuous H := by
    apply hquot.continuous_iff.mpr
    have hcomp : H ∘ Prod.map Circle.exp (id : Interval → Interval) = Lcircle := by
      funext p
      apply hLcircle_eq
      exact Prod.ext (hrep (Circle.exp p.1)) rfl
    rwa [hcomp]
  refine ⟨⟨H, hHcont⟩, ?_, ?_⟩
  · intro z
    change Circle.exp ((1 - ((0 : Interval) : ℝ)) * F (rep z) -
      ((0 : Interval) : ℝ) * rep z) = e (u * (e.symm z)⁻¹)
    norm_num
    rw [hFexp, hrep]
  · intro z
    change Circle.exp ((1 - ((1 : Interval) : ℝ)) * F (rep z) -
      ((1 : Interval) : ℝ) * rep z) = z⁻¹
    norm_num
    exact hrep z

end CurveComplex.Hyperbolic
