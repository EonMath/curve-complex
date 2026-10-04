import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.Smoothing.RegularCrosscut
import Mathlib.Analysis.Calculus.ContDiff.WithLp

open Set
open scoped ContDiff
namespace CurveComplex
open Schoenflies

/-- A vertical graph displacement extends to an actual plane homeomorphism. -/
def graphShear (d : ℝ → ℝ) (hd : Continuous d) (s : ℝ) : Plane ≃ₜ Plane where
  toFun z := Plane.mk (z 0) (z 1 + s * d (z 0))
  invFun z := Plane.mk (z 0) (z 1 - s * d (z 0))
  left_inv z := by ext i; fin_cases i <;> simp
  right_inv z := by ext i; fin_cases i <;> simp
  continuous_toFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact PiLp.continuous_apply 2 _ 0
    · exact (PiLp.continuous_apply 2 _ 1).add
        (continuous_const.mul (hd.comp (PiLp.continuous_apply 2 _ 0)))
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact PiLp.continuous_apply 2 _ 0
    · exact (PiLp.continuous_apply 2 _ 1).sub
        (continuous_const.mul (hd.comp (PiLp.continuous_apply 2 _ 0)))

/-- The displacement itself is a jointly continuous ambient isotopy. -/
def graphShearIsotopy (d : ℝ → ℝ) (hd : Continuous d) : AmbientIsotopy Plane where
  map := ⟨fun z => Plane.mk (z.2 0) (z.2 1 + z.1.val * d (z.2 0)), by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact (PiLp.continuous_apply 2 _ 0).comp continuous_snd
    · exact ((PiLp.continuous_apply 2 _ 1).comp continuous_snd).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (hd.comp ((PiLp.continuous_apply 2 _ 0).comp continuous_snd)))⟩
  homeomorphism_at := fun t => ⟨graphShear d hd t.val, fun _ => rfl⟩
  at_zero z := by ext i; fin_cases i <;> simp

theorem graphShearIsotopy_image (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (T : Set ℝ) :
    (graphShearIsotopy (g - f) (hg.sub hf)).finalMap ''
      ((fun t => Plane.mk t (f t)) '' T) = ((fun t => Plane.mk t (g t)) '' T) := by
  rw [Set.image_image]
  congr 1
  funext t
  ext i
  fin_cases i <;> simp [AmbientIsotopy.finalMap, graphShearIsotopy]

theorem graphShearIsotopy_fixes (d : ℝ → ℝ) (hd : Continuous d)
    (t : Interval) (z : Plane) (hz : d (z 0) = 0) :
    (graphShearIsotopy d hd).map (t, z) = z := by
  ext i
  fin_cases i <;> simp [graphShearIsotopy, hz]

/-- Every smooth graph is globally regular: its first coordinate has velocity one. -/
theorem regular_graph (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun t => Plane.mk t (g t)) ∧
      ∀ t : ℝ, fderiv ℝ (fun t => Plane.mk t (g t)) t ≠ 0 := by
  have hgraph : ContDiff ℝ ∞ (fun t => Plane.mk t (g t)) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_id
    · exact hg
  refine ⟨hgraph, ?_⟩
  intro t ht
  let L : Plane →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  have hc : (L ∘ (fun r => Plane.mk r (g r))) = id := rfl
  have hderiv := fderiv_comp t L.differentiableAt
    (hgraph.differentiable (by simp) t)
  rw [hc, fderiv_id] at hderiv
  rw [ht] at hderiv
  have hv := congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) hderiv
  simp at hv

#print axioms graphShearIsotopy_image
#print axioms regular_graph
end CurveComplex
