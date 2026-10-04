import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Homeomorph.Defs
open Topology
namespace CurveComplex.Hyperbolic

theorem pants_boundary_exchange_normalizes_group {G : Type*} [Group G] (a b j : G)
    (ha : j * a * j⁻¹ = b) (hb : j * b * j⁻¹ = a) :
    j ∈ Subgroup.normalizer (Subgroup.closure ({a,b} : Set G) : Set G) := by
  apply Subgroup.normalizer_le_normalizer_closure ({a,b} : Set G)
  apply Subgroup.mem_normalizer_iff_conj_image_eq.mpr
  simp only [Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply, ha, hb]
  exact Set.pair_comm b a

theorem pants_actual_quotient_involution_descends {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (hp : IsQuotientMap p) (j : X ≃ₜ X)
    (hfib : ∀ x z, p x = p z → p (j x) = p (j z))
    (hsquare : ∀ x, p (j (j x)) = p x) :
    ∃ J : Y ≃ₜ Y, (∀ x, J (p x) = p (j x)) ∧ Function.Involutive J := by
  classical
  let s : Y → X := fun y => Classical.choose (hp.surjective y)
  have hs (y : Y) : p (s y) = y := Classical.choose_spec (hp.surjective y)
  let F : Y → Y := fun y => p (j (s y))
  have hF (x : X) : F (p x) = p (j x) := hfib _ _ (hs (p x))
  have hcont : Continuous F := by
    apply hp.continuous_iff.mpr
    have heq : F ∘ p = p ∘ j := funext hF
    rw [heq]
    exact hp.continuous.comp j.continuous
  have hinv : Function.Involutive F := by
    intro y
    obtain ⟨x,rfl⟩ := hp.surjective y
    rw [hF x,hF (j x)]
    exact hsquare x
  let J : Y ≃ₜ Y := {
    toFun := F
    invFun := F
    left_inv := hinv
    right_inv := hinv
    continuous_toFun := hcont
    continuous_invFun := hcont }
  exact ⟨J,hF,hinv⟩

end CurveComplex.Hyperbolic
