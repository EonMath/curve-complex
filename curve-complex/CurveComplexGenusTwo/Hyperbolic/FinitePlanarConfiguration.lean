import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.Algebra.Polynomial

namespace CurveComplex.Hyperbolic
open Set

private def verticalShear (f : ℝ → ℝ) (hf : Continuous f) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1, p.2 + f p.1)
  invFun p := (p.1, p.2 - f p.1)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (hf.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hf.comp continuous_fst))

private def horizontalShear (f : ℝ → ℝ) (hf : Continuous f) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.prodComm ℝ ℝ).trans ((verticalShear f hf).trans (Homeomorph.prodComm ℝ ℝ))

private theorem finite_continuous_interpolation {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (hx : Function.Injective x) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∀ i, f (x i) = y i := by
  classical
  let p := Lagrange.interpolate Finset.univ x y
  refine ⟨fun t => p.eval t, p.continuous, ?_⟩
  intro i
  exact Lagrange.eval_interpolate_at_node y (fun i _ j _ h => hx h) (Finset.mem_univ i)

theorem finite_configuration_distinct_first_transport {ι : Type*} [Fintype ι]
    (a b : ι → ℝ × ℝ)
    (ha : Function.Injective (fun i => (a i).1))
    (hb : Function.Injective (fun i => (b i).1)) :
    ∃ h : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ i, h (a i) = b i := by
  obtain ⟨f, hf, hfi⟩ := finite_continuous_interpolation (fun i => (a i).1)
    (fun i => (b i).1 - (a i).2) ha
  obtain ⟨g, hg, hgi⟩ := finite_continuous_interpolation (fun i => (b i).1)
    (fun i => (b i).1 - (a i).1) hb
  obtain ⟨k, hk, hki⟩ := finite_continuous_interpolation (fun i => (b i).1)
    (fun i => (b i).2 - (b i).1) hb
  refine ⟨(verticalShear f hf).trans ((horizontalShear g hg).trans (verticalShear k hk)), ?_⟩
  intro i
  simp [Homeomorph.trans_apply, verticalShear, horizontalShear, hfi, hgi, hki]

theorem finite_configuration_generic_projection {ι : Type*} [Fintype ι]
    (a : ι → ℝ × ℝ) (ha : Function.Injective a) :
    ∃ t : ℝ, Function.Injective (fun i => (a i).1 + t * (a i).2) := by
  classical
  let bad : Finset ℝ := Finset.univ.image (fun ij : ι × ι =>
    ((a ij.2).1 - (a ij.1).1) / ((a ij.1).2 - (a ij.2).2))
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
  refine ⟨t, ?_⟩
  intro i j hij
  dsimp only at hij
  by_cases hy : (a i).2 = (a j).2
  · apply ha
    rw [hy] at hij
    exact Prod.ext (by linarith) hy
  · have hne : (a i).2 - (a j).2 ≠ 0 := sub_ne_zero.mpr hy
    have he : t = ((a j).1 - (a i).1) / ((a i).2 - (a j).2) :=
      (eq_div_iff hne).mpr (by nlinarith)
    exact False.elim (ht (he ▸ Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩))

theorem finite_planar_configuration_transport {ι : Type*} [Fintype ι]
    (a b : ι → ℝ × ℝ) (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ h : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ i, h (a i) = b i := by
  obtain ⟨t, ht⟩ := finite_configuration_generic_projection a ha
  obtain ⟨s, hs⟩ := finite_configuration_generic_projection b hb
  let A := horizontalShear (fun y => t * y) (continuous_const.mul continuous_id)
  let B := horizontalShear (fun y => s * y) (continuous_const.mul continuous_id)
  obtain ⟨h, hh⟩ := finite_configuration_distinct_first_transport
    (fun i => A (a i)) (fun i => B (b i)) ht hs
  refine ⟨A.trans (h.trans B.symm), ?_⟩
  intro i
  change B.symm (h (A (a i))) = b i
  rw [hh, B.symm_apply_apply]

end CurveComplex.Hyperbolic
