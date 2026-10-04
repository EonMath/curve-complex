import CurveComplexGenusTwo.Foundations.SingularComparison
import CurveComplexGenusTwo.Foundations.EdgeHomotopy

open CategoryTheory Topology Convexity
open scoped Simplicial
namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

/-- Faces whose vertices all have positive weight at one point of S. -/
def realizationCarrier (K : FiniteComplex V) (S : Set (geometricRealization K)) :
    FiniteComplex V where
  simplices := {σ | ∃ x ∈ S, ∀ v ∈ σ,
    ∃ hv : ({v} : Finset V) ∈ K, 0 < x.weight ⟨v, hv⟩}
  down_closed := by
    intro σ τ hsub hσ
    obtain ⟨x, hx, hpos⟩ := hσ
    exact ⟨x, hx, fun v hv => hpos v (hsub hv)⟩

theorem realizationCarrier_mono (K : FiniteComplex V)
    {S T : Set (geometricRealization K)} (h : S ⊆ T) :
    (realizationCarrier K S).simplices ⊆ (realizationCarrier K T).simplices := by
  rintro σ ⟨x, hx, hpos⟩
  exact ⟨x, h hx, hpos⟩

theorem realizationCarrier_subcomplex (K : FiniteComplex V)
    (S : Set (geometricRealization K)) :
    (realizationCarrier K S).simplices ⊆ K.simplices := by
  intro σ hσ
  obtain ⟨x, hx, hpos⟩ := hσ
  obtain ⟨τ, hτ, hzero, _⟩ := x.liesInFace
  apply K.down_closed (σ := τ.image Subtype.val) _ hτ.2
  intro v hv
  obtain ⟨hactive, hweight⟩ := hpos v hv
  have hmem : (⟨v, hactive⟩ : ActiveVertex K) ∈ τ := by
    by_contra hn
    have hz := hzero ⟨v, hactive⟩ hn
    linarith
  exact Finset.mem_image.mpr ⟨⟨v, hactive⟩, hmem, rfl⟩

theorem realizationCarrier_isNonemptyCone (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (hS : S.Nonempty)
    (v : ActiveVertex K)
    (hstar : S ⊆ CurveComplex.openVertexStar (geometricComplex K) v) :
    IsNonemptyCone (realizationCarrier K S) := by
  refine ⟨v.1, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hS
    refine ⟨x, hx, ?_⟩
    intro w hw
    have hwv : w = v.1 := Finset.mem_singleton.mp hw
    subst w
    exact ⟨v.2, hstar hx⟩
  · intro σ hσ
    obtain ⟨x, hx, hpos⟩ := hσ
    refine ⟨x, hx, ?_⟩
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact ⟨v.2, hstar hx⟩
    · exact hpos w hw

theorem realizationCarrier_reducedHomology (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (hS : S.Nonempty)
    (v : ActiveVertex K)
    (hstar : S ⊆ CurveComplex.openVertexStar (geometricComplex K) v)
    (q : ℤ) (hq : -1 ≤ q) :
    Subsingleton (reducedHomology (realizationCarrier K S) q) := by
  exact nonemptyCone_reducedHomology _
    (realizationCarrier_isNonemptyCone K S hS v hstar) q hq
end CurveGenusTwo.Filtration
