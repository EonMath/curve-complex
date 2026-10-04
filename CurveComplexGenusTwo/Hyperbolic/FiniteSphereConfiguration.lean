import CurveComplexGenusTwo.Hyperbolic.FinitePlanarConfiguration
import CurveComplexGenusTwo.Cover.HemisphereDisk
namespace CurveComplex.Hyperbolic
open Set AlternatingSphereCover
open scoped OnePoint

private theorem sphere_point_transport (p q : Sphere) :
    ∃ h : Sphere ≃ₜ Sphere, h p = q := by
  let R := Submodule.reflection (ℝ ∙ ((p : EuclideanSpace ℝ (Fin 3)) - q))ᗮ
  let h : Sphere ≃ₜ Sphere := R.toHomeomorph.subtype (fun x => by
    simp only [Metric.mem_sphere, dist_zero_right]
    change ‖x‖ = 1 ↔ ‖R x‖ = 1
    rw [R.norm_map])
  refine ⟨h, ?_⟩
  apply Subtype.ext
  exact Submodule.reflection_sub (by simp)

private theorem onePoint_configuration_transport {ι : Type*} [Fintype ι]
    (a b : ι → OnePoint (ℝ × ℝ)) (ha : Function.Injective a)
    (hb : Function.Injective b) (i₀ : ι)
    (ha₀ : a i₀ = ∞) (hb₀ : b i₀ = ∞) :
    ∃ h : OnePoint (ℝ × ℝ) ≃ₜ OnePoint (ℝ × ℝ), ∀ i, h (a i) = b i := by
  classical
  let J := {i : ι // i ≠ i₀}
  have hae (i : J) : ∃ x : ℝ × ℝ, a i.val = x := by
    cases he : a i.val using OnePoint.rec with
    | infty => exact False.elim (i.property (ha (he.trans ha₀.symm)))
    | coe x => exact ⟨x, rfl⟩
  have hbe (i : J) : ∃ x : ℝ × ℝ, b i.val = x := by
    cases he : b i.val using OnePoint.rec with
    | infty => exact False.elim (i.property (hb (he.trans hb₀.symm)))
    | coe x => exact ⟨x, rfl⟩
  let A (i : J) := (hae i).choose
  let B (i : J) := (hbe i).choose
  have hA (i : J) : a i.val = (A i : OnePoint (ℝ × ℝ)) := (hae i).choose_spec
  have hB (i : J) : b i.val = (B i : OnePoint (ℝ × ℝ)) := (hbe i).choose_spec
  have hAi : Function.Injective A := by
    intro i j hij
    apply Subtype.ext
    apply ha
    rw [hA i, hA j, hij]
  have hBi : Function.Injective B := by
    intro i j hij
    apply Subtype.ext
    apply hb
    rw [hB i, hB j, hij]
  obtain ⟨k, hk⟩ := finite_planar_configuration_transport A B hAi hBi
  refine ⟨k.onePointCongr, ?_⟩
  intro i
  by_cases hi : i = i₀
  · subst i
    rw [ha₀, hb₀]
    rfl
  · rw [hA ⟨i, hi⟩, hB ⟨i, hi⟩]
    change (k (A ⟨i, hi⟩) : OnePoint (ℝ × ℝ)) = B ⟨i, hi⟩
    rw [hk]

theorem finite_sphere_configuration_transport {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → Sphere) (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ h : Sphere ≃ₜ Sphere, ∀ i, h (a i) = b i := by
  classical
  let e : OnePoint (ℝ × ℝ) ≃ₜ Sphere := onePointEquivSphereOfFinrankEq (by simp)
  let i₀ : ι := Classical.arbitrary ι
  obtain ⟨u, hu⟩ := sphere_point_transport (a i₀) (e ∞)
  obtain ⟨v, hv⟩ := sphere_point_transport (b i₀) (e ∞)
  let A := u.trans e.symm
  let B := v.trans e.symm
  obtain ⟨h, hh⟩ := onePoint_configuration_transport
    (fun i => A (a i)) (fun i => B (b i)) (A.injective.comp ha) (B.injective.comp hb) i₀
    (by simp [A, hu]) (by simp [B, hv])
  refine ⟨A.trans (h.trans B.symm), ?_⟩
  intro i
  change B.symm (h (A (a i))) = b i
  rw [hh, B.symm_apply_apply]
end CurveComplex.Hyperbolic
