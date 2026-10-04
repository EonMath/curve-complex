import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopWholeMeshMoviePreparation
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Infinite
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Finite literal boundary events produce an arbitrarily fine UNIFORM mesh
whose interior nodes avoid every event. A prime denominator beyond the finite
rational event denominators is constructed, so no displaced mesh is assumed. -/
theorem actual_finite_boundary_avoiding_uniform_mesh
    (events : Set Interval) (hfinite : events.Finite) (lower : ℕ) :
    ∃ n : ℕ,∃ _hn : 0<n,lower<n ∧
      ∀ (k : Fin n),0<k.val → ∀ t : Interval,
        t.val=(k.val:ℝ)/n → t ∉ events := by
  classical
  let rationalEvents : Set ℚ := (fun q : ℚ => (q:ℝ)) ⁻¹' (Subtype.val '' events)
  have hrational : rationalEvents.Finite :=
    (hfinite.image Subtype.val).preimage (Rat.cast_injective (α:=ℝ)).injOn
  let maxDen := hrational.toFinset.sup Rat.den
  obtain ⟨n,hnBound,hprime⟩ := Nat.exists_infinite_primes (max lower maxDen+1)
  have hn : 0<n := hprime.pos
  have hnLower : lower<n := by omega
  have hnDen : maxDen<n := by omega
  refine ⟨n,hn,hnLower,?_⟩
  intro k hk t ht hte
  let q : ℚ := (k.val:ℚ)/n
  have hq : q ∈ rationalEvents := by
    change (q:ℝ) ∈ Subtype.val '' events
    refine ⟨t,hte,?_⟩
    simpa only [q,Rat.cast_div,Rat.cast_natCast] using ht
  have hcop : Nat.Coprime k.val n :=
    (hprime.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk k.isLt)).symm
  have hden : q.den=n := by
    have hh := Rat.den_div_eq_of_coprime (a:=(k.val:ℤ)) (b:=(n:ℤ))
      (by exact_mod_cast hn) (by simpa only [Int.natAbs_natCast] using hcop)
    have he : (q.den:ℤ)=(n:ℤ) := by simpa only [q,Int.cast_natCast] using hh
    exact_mod_cast he
  have hmax : q.den≤ maxDen := Finset.le_sup (f:=Rat.den) (hrational.mem_toFinset.mpr hq)
  omega
end CurveComplex.HyperellipticModel
