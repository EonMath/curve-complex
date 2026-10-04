import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

namespace CurveComplex
open scoped ContDiff
open Set Schoenflies

/-- The affine segment has a globally smooth parametrization with nonzero
Fréchet derivative at every real parameter, including both endpoints. -/
theorem regular_lineMap {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p q : V) (hpq : p ≠ q) :
    ContDiff ℝ ∞ (AffineMap.lineMap p q : ℝ → V) ∧
      ∀ t : ℝ, fderiv ℝ (AffineMap.lineMap p q : ℝ → V) t ≠ 0 := by
  refine ⟨AffineMap.contDiff_lineMap p q, ?_⟩
  intro t ht
  have hderiv := (AffineMap.hasDerivAt_lineMap (a := p) (b := q) (x := t)).deriv
  have hzero : deriv (AffineMap.lineMap p q : ℝ → V) t = 0 := by
    rw [deriv, ht]
    rfl
  exact hpq ((sub_eq_zero.mp (hderiv.symm.trans hzero)).symm)

/-- A proper square crosscut is smoothed to the straight crosscut by a
supported ambient isotopy. The output carries its actual global smooth
parametrization and endpoint regularity; no smoothability premise is used. -/
theorem position_crosscut_regular_segment_smoothing
    (A : Set Plane) (p q : Plane) (hA : IsArcBetween A p q)
    (hpq : p ≠ q) (hp : p ∈ modelCurve) (hq : q ∈ modelCurve)
    (hAi : A \ {p, q} ⊆ Plane.openSquare 0 1)
    (hsegment : segment ℝ p q \ {p, q} ⊆ Plane.openSquare 0 1) :
    ∃ (H : AmbientIsotopy Plane) (γ : ℝ → Plane),
      H.finalMap '' A = γ '' Icc (0 : ℝ) 1 ∧
      (∀ t x, x ∉ Plane.openSquare 0 1 → H.map (t, x) = x) ∧
      ContDiff ℝ ∞ γ ∧
      (∀ t : ℝ, fderiv ℝ γ t ≠ 0) ∧
      γ 0 = p ∧ γ 1 = q ∧ Set.InjOn γ (Icc (0 : ℝ) 1) := by
  obtain ⟨R, H, hR, hHA, hball, hfix⟩ :=
    position_crosscut_supported_isotopy A (segment ℝ p q) p q hA
      (isArcBetween_segment hpq) hp hq hAi hsegment
  obtain ⟨hsmooth, hregular⟩ := regular_lineMap p q hpq
  refine ⟨H, AffineMap.lineMap p q, ?_, hfix, hsmooth, hregular, ?_, ?_, ?_⟩
  · exact hHA.trans (segment_eq_image_lineMap ℝ p q)
  · simp
  · simp
  · exact injOn_lineMap hpq

#print axioms regular_lineMap
#print axioms position_crosscut_regular_segment_smoothing
end CurveComplex
