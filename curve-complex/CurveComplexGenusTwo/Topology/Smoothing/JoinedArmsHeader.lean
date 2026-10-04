import ClassificationOfSurfaces.Moise.GraphPolygonalization
import Schoenflies.Subarc

open Set unitInterval
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open Schoenflies

namespace CurveComplex.SeedProbeHeaders

theorem joined_embedded_arms_arc {a p b : Schoenflies.Plane} (γ : Path a p) (δ : Path p b)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hinter : range γ ∩ range δ = {p}) :
    IsArcBetween (range γ ∪ range δ) a b ∧
      p ∈ (range γ ∪ range δ) \ {a,b} := by
  let η := γ.trans δ
  have hη : Function.Injective η := Path.trans_injective_of_range_inter γ δ hγ hδ hinter
  constructor
  · refine ⟨η.extend, η.continuous_extend.continuousOn, ?_, ?_, η.extend_zero, η.extend_one⟩
    · intro s hs t ht he
      rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at he
      exact congrArg Subtype.val (hη he)
    · exact (η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans (Path.trans_range γ δ)
  · refine ⟨Or.inl ⟨1,γ.target⟩, ?_⟩
    intro hp
    have hcases : p = a ∨ p = b := by simpa using hp
    rcases hcases with ha | hb
    · have he : (1 : I) = 0 := hγ (γ.target.trans (ha.trans γ.source.symm))
      exact one_ne_zero he
    · have he : (0 : I) = 1 := hδ (δ.source.trans (hb.trans δ.target.symm))
      exact zero_ne_one he

end CurveComplex.SeedProbeHeaders

#print axioms CurveComplex.SeedProbeHeaders.joined_embedded_arms_arc
