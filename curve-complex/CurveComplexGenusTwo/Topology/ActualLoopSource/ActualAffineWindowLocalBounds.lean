import CurveComplexGenusTwo.Dictionary.MarkedSphere
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The literal source affine window stays strictly within the marked arc. -/
theorem actual_affine_window_strict_interior
    (r₀ r₁ : ℝ) (hr₀ : 0<r₀) (horder : r₀<r₁) (hr₁ : r₁<1)
    (φ : C(unitInterval,unitInterval))
    (hφ : ∀ t,(φ t:ℝ)=r₀+(r₁-r₀)*(t:ℝ)) :
    ∀ t,0<(φ t:ℝ) ∧ (φ t:ℝ)<1 := by
  intro t
  rw [hφ]
  have hprod := mul_nonneg (sub_pos.mpr horder).le t.property.1
  have hupper := mul_le_mul_of_nonneg_left t.property.2 (sub_pos.mpr horder).le
  constructor <;> nlinarith only [hr₀,hr₁,hprod,hupper]
/-- Source small geometric weight gives the actual quarter-window margin. -/
theorem actual_small_weighted_quarter_margin
    (ε d : ℝ) (hε : 0<ε) (hd : d<1/2) : ε*d/4<ε := by
  have hh := mul_pos hε (show 0<1-d/4 by linarith)
  nlinarith only [hh]
/-- The actual affine window contains the entire original crossing middle. -/
theorem actual_affine_window_contains_middle
    (r₀ r₁ ε : ℝ) (horder : r₀<r₁) (hr₀ε : r₀<ε) (hεr₁ : 1-ε<r₁)
    (φ : C(unitInterval,unitInterval))
    (hφ : ∀ t,(φ t:ℝ)=r₀+(r₁-r₀)*(t:ℝ))
    (t : unitInterval) (hlo : ε<(t:ℝ)) (hhi : (t:ℝ)<1-ε) : ∃ s,φ s=t := by
  have hd : 0<r₁-r₀ := sub_pos.mpr horder
  let s : unitInterval := ⟨((t:ℝ)-r₀)/(r₁-r₀),by
    constructor
    · exact div_nonneg (by linarith only [hr₀ε,hlo]) hd.le
    · exact (div_le_one hd).mpr (by linarith only [hεr₁,hhi])⟩
  refine ⟨s,Subtype.ext ?_⟩
  rw [hφ]
  dsimp [s]
  field_simp [hd.ne']
  ring
end CurveComplex.HyperellipticModel
