import CurveComplexGenusTwo.Foundations.ConeRealization
import CurveComplexGenusTwo.Foundations.RealizationCW

open CurveComplex Set
open scoped BigOperators

/-- Affine pushforward sums weights over label fibers, including collisions. -/
noncomputable def regionalFiniteSimplexPushforward
    {V W : Type*} (σ : Finset V) (τ : Finset W) (f : ↥σ → ↥τ)
    (p : FiniteSimplex σ) : FiniteSimplex τ := by
  classical
  refine ⟨fun v => ∑ i : ↥σ, if f i = v then p.val i else 0,?_,?_⟩
  · intro v
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact p.property.1 i
    · exact le_rfl
  · rw [Finset.sum_comm]
    simpa using p.property.2

theorem regionalFiniteSimplexPushforward_continuous
    {V W : Type*} (σ : Finset V) (τ : Finset W) (f : ↥σ → ↥τ) :
    Continuous (regionalFiniteSimplexPushforward σ τ f) := by
  classical
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  apply continuous_finsetSum
  intro i hi
  by_cases h : f i = v
  · change Continuous (fun p : FiniteSimplex σ => if f i = v then p.val i else 0)
    simp only [if_pos h]
    exact (continuous_apply i).comp continuous_subtype_val
  · change Continuous (fun p : FiniteSimplex σ => if f i = v then p.val i else 0)
    simp only [if_neg h]
    exact continuous_const

/-- Joint linear interpolation in a SINGLE common finite target simplex. -/
noncomputable def regionalFiniteSimplexInterpolation
    {V : Type*} (σ : Finset V)
    (p q : FiniteSimplex σ) (t : ConeTime) : FiniteSimplex σ := by
  refine ⟨fun v => (1-(t : ℝ))*p.val v + (t : ℝ)*q.val v,?_,?_⟩
  · intro v
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) (p.property.1 v))
      (mul_nonneg t.property.1 (q.property.1 v))
  · simp only [Finset.sum_add_distrib,← Finset.mul_sum,p.property.2,q.property.2]
    ring

theorem regionalFiniteSimplexInterpolation_continuous
    {V : Type*} (σ : Finset V) :
    Continuous (fun z : ConeTime × FiniteSimplex σ × FiniteSimplex σ =>
      regionalFiniteSimplexInterpolation σ z.2.1 z.2.2 z.1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  have ht : Continuous (fun z : ConeTime × FiniteSimplex σ × FiniteSimplex σ =>
      (z.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
  have hp : Continuous (fun z : ConeTime × FiniteSimplex σ × FiniteSimplex σ =>
      z.2.1.val v) := (continuous_apply v).comp
        (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  have hq : Continuous (fun z : ConeTime × FiniteSimplex σ × FiniteSimplex σ =>
      z.2.2.val v) := (continuous_apply v).comp
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact ((continuous_const.sub ht).mul hp).add (ht.mul hq)


#print axioms regionalFiniteSimplexPushforward
#print axioms regionalFiniteSimplexPushforward_continuous
#print axioms regionalFiniteSimplexInterpolation
#print axioms regionalFiniteSimplexInterpolation_continuous
