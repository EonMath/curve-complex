import CurveComplexGenusTwo.Filtration.RealizationCarrier

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

theorem realizationCarrier_cycle_bounds (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (hS : S.Nonempty)
    (v : ActiveVertex K)
    (hstar : S ⊆ CurveComplex.openVertexStar (geometricComplex K) v)
    (q : ℤ) (hq : -1 ≤ q) (c : cycles (realizationCarrier K S) q) :
    c.1 ∈ boundaries (realizationCarrier K S) q := by
  letI := realizationCarrier_reducedHomology K S hS v hstar q hq
  have hzero : (QuotientAddGroup.mk c : reducedHomology (realizationCarrier K S) q) = 0 :=
    Subsingleton.elim _ _
  change c ∈ (boundaries (realizationCarrier K S) q).comap
    (cycles (realizationCarrier K S) q).subtype
  exact (QuotientAddGroup.eq_zero_iff c).mp hzero
end CurveGenusTwo.Filtration
