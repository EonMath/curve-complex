import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorPointNearbySlide
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

namespace CurveComplex
open Set
noncomputable section

def actualIsotopyReverseTime (t : Interval) : Interval :=
  ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩

def actualIsotopyEndpointInverse {S : Type} [TopologicalSpace S]
    (G : AmbientIsotopy S) : AmbientIsotopy S := by
  let h := HyperellipticModel.ArcSurgery.timeHomeomorph G 1
  have hrev : Continuous actualIsotopyReverseTime := by unfold actualIsotopyReverseTime; fun_prop
  exact {
    map := ⟨fun z => G.map (actualIsotopyReverseTime z.1,h.symm z.2),
      G.map.continuous.comp ((hrev.comp continuous_fst).prodMk
        (h.symm.continuous.comp continuous_snd))⟩
    homeomorphism_at := fun t => ⟨h.symm.trans
      (HyperellipticModel.ArcSurgery.timeHomeomorph G (actualIsotopyReverseTime t)),
      fun z => HyperellipticModel.ArcSurgery.timeHomeomorph_apply G _ _⟩
    at_zero := fun z => by
      change G.map (actualIsotopyReverseTime ⟨0,by norm_num⟩,h.symm z) = z
      rw [show actualIsotopyReverseTime ⟨0,by norm_num⟩ = (1:Interval) by
        apply Subtype.ext; norm_num [actualIsotopyReverseTime]]
      exact (HyperellipticModel.ArcSurgery.timeHomeomorph_apply G 1 (h.symm z)).symm.trans
        (h.apply_symm_apply z) }

theorem actualIsotopyEndpointInverse_final {S : Type} [TopologicalSpace S]
    (G : AmbientIsotopy S) (z : S) :
    (actualIsotopyEndpointInverse G).finalMap z =
      (HyperellipticModel.ArcSurgery.timeHomeomorph G 1).symm z := by
  change G.map (actualIsotopyReverseTime (1:Interval),_) = _
  rw [show actualIsotopyReverseTime (1:Interval) = ⟨0,by norm_num⟩ by
    apply Subtype.ext; norm_num [actualIsotopyReverseTime]]
  exact G.at_zero _

theorem actualIsotopyEndpointInverse_fixes {S : Type} [TopologicalSpace S]
    (G : AmbientIsotopy S) (P : Set S)
    (hP : ∀ t z, z ∈ P → G.map (t,z) = z) :
    ∀ t z, z ∈ P → (actualIsotopyEndpointInverse G).map (t,z) = z := by
  intro t z hz
  let h := HyperellipticModel.ArcSurgery.timeHomeomorph G 1
  have hz' : h.symm z = z := by
    apply h.injective
    rw [h.apply_symm_apply]
    exact ((HyperellipticModel.ArcSurgery.timeHomeomorph_apply G 1 z).trans (hP 1 z hz)).symm
  change G.map (actualIsotopyReverseTime t,h.symm z) = z
  rw [hz']
  exact hP _ z hz

theorem actualIsotopyEndpointInverse_image {S : Type} [TopologicalSpace S]
    (G : AmbientIsotopy S) (P : Set S)
    (hP : ∀ t, (fun z => G.map (t,z)) '' P = P) :
    ∀ t, (fun z => (actualIsotopyEndpointInverse G).map (t,z)) '' P = P := by
  intro t
  let h := HyperellipticModel.ArcSurgery.timeHomeomorph G 1
  have hh : h '' P = P := by
    simpa only [h,HyperellipticModel.ArcSurgery.timeHomeomorph_apply] using hP 1
  have hi : h.symm '' P = P := by
    calc
      h.symm '' P = h.symm '' (h '' P) := by rw [hh]
      _ = P := by
        rw [← Set.image_comp]
        simp only [Function.comp_def,h.symm_apply_apply]
        change id '' P = P
        exact Set.image_id _
  change (fun z => G.map (actualIsotopyReverseTime t,h.symm z)) '' P = P
  calc
    _ = (fun z => G.map (actualIsotopyReverseTime t,z)) '' (h.symm '' P) :=
      (Set.image_image _ _ _).symm
    _ = P := by rw [hi]; exact hP _
end
end CurveComplex
