
import Mathlib.Topology.Covering.Quotient

open Set Topology
namespace CurveComplex.LocalSurgery

/-- Conjugate an actual quotient-cover action through a homeomorphism of its domain. -/
theorem actual_quotient_cover_domain_homeomorph_transport
    {G E F S : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    [TopologicalSpace F] [TopologicalSpace S]
    (p : E → S) (hp : IsQuotientCoveringMap p G) (h : F ≃ₜ E) :
    ∃ a : MulAction G F, letI := a
      IsQuotientCoveringMap (p ∘ h : F → S) G := by
  let a : MulAction G F := {
    smul := fun g x => h.symm (g • h x)
    one_smul := fun x => by
      change h.symm ((1 : G) • h x) = x
      simp
    mul_smul := fun g k x => by
      change h.symm ((g * k) • h x) = h.symm (g • h (h.symm (k • h x)))
      simp [mul_smul] }
  letI := a
  refine ⟨a, { hp.toIsQuotientMap.comp h.isQuotientMap with
    continuous_const_smul := ?_
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }⟩
  · intro g
    change Continuous (fun x : F => h.symm (g • h x))
    exact h.symm.continuous.comp ((hp.continuous_const_smul g).comp h.continuous)
  · intro x y
    change p (h x) = p (h y) ↔ ∃ g : G, h.symm (g • h y) = x
    rw [hp.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g,hg⟩
      change g • h y = h x at hg
      exact ⟨g,by rw [hg,h.symm_apply_apply]⟩
    · rintro ⟨g,hg⟩
      refine ⟨g,?_⟩
      exact (h.symm_apply_eq.mp hg)
  · intro x
    obtain ⟨U,hU,hdis⟩ := hp.disjoint (h x)
    refine ⟨h ⁻¹' U,h.continuous.continuousAt.preimage_mem_nhds hU,?_⟩
    intro g hg
    apply hdis g
    obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hg
    refine ⟨h (g • z),⟨h z,hz,?_⟩,hy⟩
    change g • h z = h (h.symm (g • h z))
    simp


end CurveComplex.LocalSurgery
