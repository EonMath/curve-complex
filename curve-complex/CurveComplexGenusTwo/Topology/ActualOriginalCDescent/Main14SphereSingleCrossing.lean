import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14CrossingChartTransport

open Set Topology

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable def puncturedPlaneCurve (M : HyperellipticModel E S)
    (pole : S) (c : Curve S) (hc : pole ∉ c.image) : Curve Schoenflies.Plane := by
  let g : Circle → {x : S // x ≠ pole} :=
    fun t => ⟨c.map t,fun he => hc (he ▸ Set.mem_range_self t)⟩
  have hg : IsEmbedding g := IsEmbedding.subtypeVal.of_comp_iff.mp c.embedded
  exact ⟨M.puncturedPlane pole ∘ g,(M.puncturedPlane pole).isEmbedding.comp hg⟩

theorem puncturedPlaneCurve_image (M : HyperellipticModel E S)
    (pole : S) (c : Curve S) (hc : pole ∉ c.image) :
    (fun z : Schoenflies.Plane => ((M.puncturedPlane pole).symm z).val) ''
      (M.puncturedPlaneCurve pole c hc).image = c.image := by
  apply Set.Subset.antisymm
  · rintro z ⟨w,⟨t,rfl⟩,rfl⟩
    change ((M.puncturedPlane pole).symm
      ((M.puncturedPlane pole) ⟨c.map t,_⟩)).val ∈ c.image
    rw [Homeomorph.symm_apply_apply]
    exact Set.mem_range_self t
  · rintro z ⟨t,rfl⟩
    refine ⟨(M.puncturedPlaneCurve pole c hc).map t,Set.mem_range_self t,?_⟩
    change ((M.puncturedPlane pole).symm
      ((M.puncturedPlane pole) ⟨c.map t,_⟩)).val = c.map t
    rw [Homeomorph.symm_apply_apply]

/-- The sphere single-crossing obstruction in a stereographic chart that
avoids both actual circles. A branch mark supplies such a pole for punctured
circles; it is not an intersection-parity certificate. -/
theorem sphere_curves_cannot_cross_once
    (M : HyperellipticModel E S) (pole : S) (c d : Curve S)
    (hc : pole ∉ c.image) (hd : pole ∉ d.image)
    (p : S) (hcross : CrossesAt c d p) (hinter : c.image ∩ d.image = {p}) : False := by
  letI : T2Space S := M.sphere.symm.t2Space
  let e := M.puncturedPlane pole
  let j : Schoenflies.Plane → S := fun z => (e.symm z).val
  have hj : IsOpenEmbedding j :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
  have hpC : p ∈ c.image := by
    have hp : p ∈ c.image ∩ d.image := hinter.symm ▸ Set.mem_singleton p
    exact hp.1
  have hpne : p ≠ pole := fun he => hc (he ▸ hpC)
  let a := M.puncturedPlaneCurve pole c hc
  let b := M.puncturedPlaneCurve pole d hd
  let pp := e ⟨p,hpne⟩
  have hjpp : j pp = p := congrArg Subtype.val (e.symm_apply_apply ⟨p,hpne⟩)
  have ha : c.image = j '' a.image := (M.puncturedPlaneCurve_image pole c hc).symm
  have hb : d.image = j '' b.image := (M.puncturedPlaneCurve_image pole d hd).symm
  have hpCross : CrossesAt a b pp := crossesAt_of_openEmbedding j hj a b c d ha hb pp
    (hjpp.symm ▸ hcross)
  apply planar_curves_cannot_cross_once a b pp hpCross
  apply Set.Subset.antisymm
  · intro z hz
    have hzj : j z ∈ c.image ∩ d.image :=
      ⟨ha.symm ▸ Set.mem_image_of_mem j hz.1,hb.symm ▸ Set.mem_image_of_mem j hz.2⟩
    have he : j z = p := Set.mem_singleton_iff.mp (hinter ▸ hzj)
    exact Set.mem_singleton_iff.mpr (hj.injective (he.trans hjpp.symm))
  · intro z hz
    have he : z = pp := Set.mem_singleton_iff.mp hz
    subst z
    have hp : p ∈ c.image ∩ d.image := hinter.symm ▸ Set.mem_singleton p
    constructor
    · obtain ⟨w,hw,hwp⟩ := ha ▸ hp.1
      exact hj.injective (hwp.trans hjpp.symm) ▸ hw
    · obtain ⟨w,hw,hwp⟩ := hb ▸ hp.2
      exact hj.injective (hwp.trans hjpp.symm) ▸ hw

end CurveComplex.HyperellipticModel
