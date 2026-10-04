import CurveComplexGenusTwo.Dependencies.SpherePort
import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

namespace CurveComplex

open SpherePort

private lemma sphere_compl_pair_preconnected
    (q b : SpherePort.Sphere) (hqb : q ≠ b) :
    IsPreconnected ({q, b}ᶜ : Set SpherePort.Sphere) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e := stereographic' 2 q
  have ht : e.target = Set.univ := stereographic'_target q
  have hs : e.source = {q}ᶜ := stereographic'_source q
  let z : EuclideanSpace ℝ (Fin 2) := e b
  have hz : b ∈ e.source := by
    simpa only [hs, Set.mem_compl_iff, Set.mem_singleton_iff] using hqb.symm
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [← Module.finrank_eq_rank]
    simp
  have hc : IsPreconnected ({z}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) :=
    (isConnected_compl_singleton_of_one_lt_rank hrank z).isPreconnected
  have hcont : ContinuousOn e.symm ({z}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    exact e.continuousOn_symm.mono (by simp [ht])
  have heq : e.symm '' ({z}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) =
      ({q, b}ᶜ : Set SpherePort.Sphere) := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_insert_iff, not_or]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hys : y ∈ e.target := by simp only [ht, Set.mem_univ]
      have hxq : e.symm y ∈ e.source := e.map_target hys
      have hxb : e.symm y ≠ b := by
        intro h
        have : e (e.symm y) = e b := congrArg e h
        exact hy (by simpa [z, e.right_inv hys] using this)
      have hxq' : e.symm y ≠ q := by
        simpa only [hs, Set.mem_compl_iff, Set.mem_singleton_iff] using hxq
      exact ⟨hxq', hxb⟩
    · rintro ⟨hxq, hxb⟩
      have hxs : x ∈ e.source := by simpa [hs] using hxq
      refine ⟨e x, ?_, e.left_inv hxs⟩
      intro h
      exact hxb (e.injOn hxs hz h)
  rw [← heq]
  exact hc.image e.symm hcont

end CurveComplex

namespace CurveComplex

/-- An embedded circle cannot fill the two-sphere: deleting two points would
otherwise be both preconnected and disconnected. -/
theorem sphere_embedded_circle_omits_point (c : Curve SpherePort.Sphere) :
    (Set.range c.map)ᶜ.Nonempty := by
  by_contra hmiss
  have hsurj : Function.Surjective c.map := by
    intro q
    by_contra hq
    exact hmiss ⟨q, hq⟩
  let e : Circle ≃ₜ SpherePort.Sphere := c.embedded.toHomeomorphOfSurjective hsurj
  let a : Circle := 1
  have ha : a ≠ -a := (Circle.neg_ne_self a).symm
  have hneq : e a ≠ e (-a) := e.injective.ne ha
  have hconn : IsPreconnected ({e a, e (-a)}ᶜ : Set SpherePort.Sphere) :=
    sphere_compl_pair_preconnected (e a) (e (-a)) hneq
  have hpreim : e ⁻¹' ({e a, e (-a)}ᶜ : Set SpherePort.Sphere) =
      ({a, -a}ᶜ : Set Circle) := by
    ext x
    simp [e.injective.eq_iff]
  have hcircle : IsPreconnected ({a, -a}ᶜ : Set Circle) := by
    rw [← hpreim]
    exact e.isPreconnected_preimage.mpr hconn
  exact (Circle.not_isPreconnected_compl_pair ha) hcircle

end CurveComplex
