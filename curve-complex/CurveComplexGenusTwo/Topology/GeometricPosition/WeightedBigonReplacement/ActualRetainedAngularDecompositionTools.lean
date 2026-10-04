import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
open Set Topology
namespace CurveComplex

theorem actual_original_angular_subarc {S : Type*} [TopologicalSpace S] [T2Space S]
    (c : Curve S) (q : Circle) (u v : ℝ) (huv : u < v) (hlen : v-u < 2*Real.pi) :
    ∃ f : Path (c.map (q*Circle.exp u)) (c.map (q*Circle.exp v)),
      Topology.IsEmbedding f ∧ Set.range f = (fun θ => c.map (q*Circle.exp θ)) '' Set.Icc u v := by
  let γ : ℝ → S := fun θ => c.map (q*Circle.exp θ)
  have hγ : Continuous γ := c.embedded.continuous.comp (continuous_const.mul Circle.exp.continuous)
  let f : Path (γ u) (γ v) := {
    toFun := fun t => γ (u+(t : ℝ)*(v-u))
    continuous_toFun := hγ.comp (by fun_prop)
    source' := by simp
    target' := by simp }
  have hparam (t : unitInterval) : u+(t : ℝ)*(v-u) ∈ Icc u v := by
    constructor <;> nlinarith [t.property.1,t.property.2]
  have hinj : Function.Injective f := by
    intro t s he
    have hcir := mul_left_cancel (c.embedded.injective he)
    have hp := Circle.exp_injOn_Icc hlen (hparam t) (hparam s) hcir
    apply Subtype.ext
    nlinarith
  have hrange : Set.range f = γ '' Icc u v := by
    ext p
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨u+(t : ℝ)*(v-u),hparam t,rfl⟩
    · rintro ⟨θ,hθ,rfl⟩
      have ht : (θ-u)/(v-u) ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith [hθ.1]) (by linarith)
        · apply (div_le_one (by linarith : 0 < v-u)).mpr
          linarith [hθ.2]
      refine ⟨⟨(θ-u)/(v-u),ht⟩,?_⟩
      change γ (u+(θ-u)/(v-u)*(v-u)) = γ θ
      rw [div_mul_cancel₀ _ (by linarith : v-u ≠ 0)]
      congr 1
      ring
  exact ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,hrange⟩

theorem actual_original_circle_subarc_and_retained_remainder
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (c : Curve S) (q : Circle) (L R : ℝ) (hLR : L < R) (hspan : R-L < 2*Real.pi) :
    let γ := fun θ : ℝ => c.map (q*Circle.exp θ)
    ∃ a : Path (γ L) (γ R), ∃ r : Path (γ R) (γ (L+2*Real.pi)),
      Topology.IsEmbedding a ∧ Topology.IsEmbedding r ∧
      Set.range a = γ '' Set.Icc L R ∧
      Set.range r = γ '' Set.Icc R (L+2*Real.pi) ∧
      c.image = Set.range a ∪ Set.range r ∧
      Set.range a ∩ Set.range r = {γ L,γ R} ∧ r 1 = γ L := by
  let γ := fun θ : ℝ => c.map (q*Circle.exp θ)
  have hperiod : γ (L+2*Real.pi) = γ L := by
    dsimp [γ]
    rw [Circle.periodic_exp L]
  obtain ⟨a,ha,hA⟩ := actual_original_angular_subarc c q L R hLR hspan
  obtain ⟨r,hr,hR⟩ := actual_original_angular_subarc c q R (L+2*Real.pi)
    (by linarith only [hspan]) (by linarith only [hLR])
  have hcircle : Circle.exp '' Set.Icc L (L+2*Real.pi) = Set.univ := by
    rw [Circle.periodic_exp.image_Icc (by positivity : 0 < 2*Real.pi) L]
    exact Circle.exp_surjective.range_eq
  have hfull : c.image = γ '' Set.Icc L (L+2*Real.pi) := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      have hz : q⁻¹*z ∈ Circle.exp '' Set.Icc L (L+2*Real.pi) := hcircle.symm ▸ Set.mem_univ _
      obtain ⟨θ,hθ,hEq⟩ := hz
      refine ⟨θ,hθ,?_⟩
      dsimp [γ]
      rw [hEq]
      simp
    · rintro ⟨θ,hθ,rfl⟩
      exact ⟨q*Circle.exp θ,rfl⟩
  have hdecomp : c.image = Set.range a ∪ Set.range r := by
    rw [hA,hR,← Set.image_union,Set.Icc_union_Icc_eq_Icc hLR.le (by linarith only [hspan])]
    exact hfull
  have hmeet : Set.range a ∩ Set.range r = {γ L,γ R} := by
    rw [hA,hR]
    ext x
    constructor
    · rintro ⟨⟨θ,hθ,hθx⟩,⟨ψ,hψ,hψx⟩⟩
      have hExp : Circle.exp θ = Circle.exp ψ := mul_left_cancel (c.embedded.injective (hθx.trans hψx.symm))
      have hθψ : θ ≤ ψ := hθ.2.trans hψ.1
      by_cases hshort : ψ-θ < 2*Real.pi
      · have heq := Circle.exp_injOn_Icc hshort ⟨le_rfl,hθψ⟩ ⟨hθψ,le_rfl⟩ hExp
        have hθR : θ = R := by linarith only [hθ.2,hψ.1,heq]
        apply Set.mem_insert_of_mem
        apply Set.mem_singleton_iff.mpr
        rw [← hθx,hθR]
      · have hθL : θ = L := by linarith only [hθ.1,hψ.2,le_of_not_gt hshort]
        rw [← hθx,hθL]
        exact Set.mem_insert _ _
    · intro hx
      rcases Set.mem_insert_iff.mp hx with hx | hx
      · subst x
        refine ⟨⟨L,⟨le_rfl,hLR.le⟩,rfl⟩,?_⟩
        exact ⟨L+2*Real.pi,⟨by linarith only [hspan],le_rfl⟩,hperiod⟩
      · have hxR : x = γ R := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨⟨R,⟨hLR.le,le_rfl⟩,rfl⟩,⟨R,⟨le_rfl,by linarith only [hspan]⟩,rfl⟩⟩
  exact ⟨a,r,ha,hr,hA,hR,hdecomp,hmeet,r.target.trans hperiod⟩
end CurveComplex
