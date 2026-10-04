import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.ChartTransitionDerivative
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

open TopologicalSpace
open scoped Manifold ContDiff Bundle
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

/-- The derivative `dw/dz` of two charts in the original complex atlas. -/
def smoothZeroSubmodule : Submodule ℂ (E → ℂ) where
  carrier := {f | ∀ a : E, ContDiffOn ℝ ∞
    (fun z : ℂ => f ((extChartAt 𝓘(ℂ) a).symm z))
    (extChartAt 𝓘(ℂ) a).target}
  zero_mem' := by
    intro a
    exact contDiffOn_const
  add_mem' := by
    intro f g hf hg a
    exact (hf a).add (hg a)
  smul_mem' := by
    intro c f hf a
    exact (hf a).const_smul c

abbrev SmoothZero (E : Type u) [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] := smoothZeroSubmodule (E := E)

/-- Smooth `(0,1)` forms presented by coefficients in all preferred charts.
Each coefficient is zero off its chart source, smooth on its chart target,
and transforms by the conjugate inverse derivative on overlaps. -/
def smoothZeroOneSubmodule : Submodule ℂ (E → E → ℂ) where
  carrier := {α |
    (∀ a x, x ∉ (extChartAt 𝓘(ℂ) a).source → α a x = 0) ∧
    (∀ a : E, ContDiffOn ℝ ∞
      (fun z : ℂ => α a ((extChartAt 𝓘(ℂ) a).symm z))
      (extChartAt 𝓘(ℂ) a).target) ∧
    (∀ a b x, x ∈ (extChartAt 𝓘(ℂ) a).source →
      x ∈ (extChartAt 𝓘(ℂ) b).source →
      α b x = α a x / star (chartTransitionDerivative a b x))}
  zero_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro a x hx
      rfl
    · intro a
      exact contDiffOn_const
    · intro a b x ha hb
      simp
  add_mem' := by
    intro α β hα hβ
    refine ⟨?_, ?_, ?_⟩
    · intro a x hx
      simp only [Pi.add_apply, hα.1 a x hx, hβ.1 a x hx, add_zero]
    · intro a
      exact (hα.2.1 a).add (hβ.2.1 a)
    · intro a b x ha hb
      simp only [Pi.add_apply]
      rw [hα.2.2 a b x ha hb, hβ.2.2 a b x ha hb, add_div]
  smul_mem' := by
    intro c α hα
    refine ⟨?_, ?_, ?_⟩
    · intro a x hx
      simp only [Pi.smul_apply, hα.1 a x hx, smul_zero]
    · intro a
      exact (hα.2.1 a).const_smul c
    · intro a b x ha hb
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hα.2.2 a b x ha hb, mul_div_assoc]

abbrev SmoothZeroOne (E : Type u) [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℂ) ∞ E] := smoothZeroOneSubmodule (E := E)

/-- Charts are tested on their open targets; compact subsets of this subtype
are exactly the compact sets used for local `C∞` convergence. -/
abbrev ChartTarget (a : E) := {z : ℂ // z ∈ (extChartAt 𝓘(ℂ) a).target}

abbrev RealJet (n : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin n => ℂ) ℂ

/-- A jet of a smooth function, as an actual continuous map on a chart target. -/
noncomputable def smoothZeroJet (a : E) (n : ℕ) (f : SmoothZero E) :
    C(ChartTarget a, RealJet n) where
  toFun z := iteratedFDeriv ℝ n
    (fun w : ℂ => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) z.1
  continuous_toFun := by
    exact (ContinuousOn.continuousOn_iteratedFDeriv (f.property a)
      (isOpen_extChartAt_target a) (by simp)).domRestrict

/-- A jet of a form coefficient in chart `a`. -/
noncomputable def smoothZeroOneJet (a : E) (n : ℕ) (α : SmoothZeroOne E) :
    C(ChartTarget a, RealJet n) where
  toFun z := iteratedFDeriv ℝ n
    (fun w : ℂ => α.1 a ((extChartAt 𝓘(ℂ) a).symm w)) z.1
  continuous_toFun := by
    exact (ContinuousOn.continuousOn_iteratedFDeriv (α.property.2.1 a)
      (isOpen_extChartAt_target a) (by simp)).domRestrict

/-- `C∞` topology: initial topology of all real jets, with compact-open
topology on each continuous-map target. No arbitrary norm on H¹ is assumed. -/
noncomputable instance (priority := 1100) smoothZeroTopology :
    TopologicalSpace (SmoothZero E) :=
  TopologicalSpace.induced (fun f => fun (a : E) (n : ℕ) => smoothZeroJet a n f)
    inferInstance

noncomputable instance (priority := 1100) smoothZeroOneTopology :
    TopologicalSpace (SmoothZeroOne E) :=
  TopologicalSpace.induced (fun α => fun (a : E) (n : ℕ) => smoothZeroOneJet a n α)
    inferInstance

/-- Topological vector-space properties of these specified jet topologies. -/
instance smoothZero_isTopologicalAddGroup : IsTopologicalAddGroup (SmoothZero E) := by
  let L : SmoothZero E →ₗ[ℂ] (∀ (a : E) (n : ℕ), C(ChartTarget a, RealJet n)) :=
    { toFun := fun f a n => smoothZeroJet a n f
      map_add' := by
        intro f g
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          ((fun w : ℂ => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) +
           (fun w : ℂ => g.1 ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_add_apply
          ((f.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
          ((g.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
      map_smul' := by
        intro c f
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          (c • (fun w : ℂ => f.1 ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_const_smul_apply
          ((f.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp)) }
  exact isTopologicalAddGroup_induced L

instance smoothZero_continuousSMul : ContinuousSMul ℂ (SmoothZero E) := by
  let L : SmoothZero E →ₗ[ℂ] (∀ (a : E) (n : ℕ), C(ChartTarget a, RealJet n)) :=
    { toFun := fun f a n => smoothZeroJet a n f
      map_add' := by
        intro f g
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          ((fun w : ℂ => f.1 ((extChartAt 𝓘(ℂ) a).symm w)) +
           (fun w : ℂ => g.1 ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_add_apply
          ((f.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
          ((g.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
      map_smul' := by
        intro c f
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          (c • (fun w : ℂ => f.1 ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_const_smul_apply
          ((f.property a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp)) }
  exact continuousSMul_induced L

instance smoothZeroOne_isTopologicalAddGroup : IsTopologicalAddGroup (SmoothZeroOne E) := by
  let L : SmoothZeroOne E →ₗ[ℂ] (∀ (a : E) (n : ℕ), C(ChartTarget a, RealJet n)) :=
    { toFun := fun f a n => smoothZeroOneJet a n f
      map_add' := by
        intro f g
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          ((fun w : ℂ => f.1 a ((extChartAt 𝓘(ℂ) a).symm w)) +
           (fun w : ℂ => g.1 a ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_add_apply
          ((f.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
          ((g.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
      map_smul' := by
        intro c f
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          (c • (fun w : ℂ => f.1 a ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_const_smul_apply
          ((f.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp)) }
  exact isTopologicalAddGroup_induced L

instance smoothZeroOne_continuousSMul : ContinuousSMul ℂ (SmoothZeroOne E) := by
  let L : SmoothZeroOne E →ₗ[ℂ] (∀ (a : E) (n : ℕ), C(ChartTarget a, RealJet n)) :=
    { toFun := fun f a n => smoothZeroOneJet a n f
      map_add' := by
        intro f g
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          ((fun w : ℂ => f.1 a ((extChartAt 𝓘(ℂ) a).symm w)) +
           (fun w : ℂ => g.1 a ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_add_apply
          ((f.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
          ((g.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
      map_smul' := by
        intro c f
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          (c • (fun w : ℂ => f.1 a ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_const_smul_apply
          ((f.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp)) }
  exact continuousSMul_induced L

end SameAtlasAnalyticCohomology
