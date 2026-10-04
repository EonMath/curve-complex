import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
namespace CurveComplex.HyperellipticModel
open Set
theorem homeomorphism_complement_component {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {H W : Set X} (hW : IsComplementComponent H W) :
    IsComplementComponent (e '' H) (e '' W) := by
  have hc : IsConnected (e '' W) := hW.2.1.image e e.continuous.continuousOn
  refine ⟨hc.nonempty, hc, ?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩ ⟨z, hz, he⟩
    exact hW.2.2.1 hx (e.injective he ▸ hz)
  · intro V hV hsub hVH
    have hv : IsConnected (e.symm '' V) := hV.image e.symm e.symm.continuous.continuousOn
    have hWV : W ⊆ e.symm '' V := by
      intro x hx
      exact ⟨e x, hsub ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
    have hVc : e.symm '' V ⊆ Hᶜ := by
      rintro x ⟨y, hy, rfl⟩ hxH
      exact hVH hy ⟨e.symm y, hxH, e.apply_symm_apply y⟩
    have heq : e.symm '' V = W := hW.2.2.2 _ hv hWV hVc
    apply Set.Subset.antisymm
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      rw [← heq]
      exact ⟨y, hy, rfl⟩
    · exact hsub

end CurveComplex.HyperellipticModel
