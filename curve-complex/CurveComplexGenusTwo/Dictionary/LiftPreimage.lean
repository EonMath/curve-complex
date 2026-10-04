import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex
namespace HyperellipticModel

open Topology

variable {E S : Type}
  [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
  (M : HyperellipticModel E S)

theorem lift_preimage (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (L : AmbientIsotopy E)
    (hlift : ∀ t x, M.cover.projection (L.map (t, x)) =
      H.map (t, M.cover.projection x)) (A : Set S) :
    L.finalMap '' (M.cover.projection ⁻¹' A) =
      M.cover.projection ⁻¹' (H.finalMap '' A) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change M.cover.projection (L.map (⟨1, by norm_num⟩, x)) ∈ H.finalMap '' A
    rw [hlift]
    exact ⟨M.cover.projection x, hx, rfl⟩
  · intro hy
    obtain ⟨h, hh⟩ := L.homeomorphism_at ⟨1, by norm_num⟩
    let x := h.symm y
    have hL : L.finalMap x = y := by
      change L.map (⟨1, by norm_num⟩, x) = y
      rw [← hh]
      exact h.apply_symm_apply y
    refine ⟨x, ?_, hL⟩
    obtain ⟨a, ha, heq⟩ := hy
    change M.cover.projection x ∈ A
    have hproj : H.finalMap (M.cover.projection x) = M.cover.projection y := by
      calc
        H.finalMap (M.cover.projection x) = M.cover.projection (L.finalMap x) :=
          (hlift ⟨1, by norm_num⟩ x).symm
        _ = M.cover.projection y := by rw [hL]
    have hinj : Function.Injective H.finalMap := by
      obtain ⟨g, hg⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
      have hfun : g = H.finalMap := funext hg
      rw [← hfun]
      exact g.injective
    have hxa : M.cover.projection x = a := hinj (hproj.trans heq.symm)
    exact hxa ▸ ha

end HyperellipticModel
end CurveComplex
