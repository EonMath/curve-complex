import CurveComplexGenusTwo.Topology.FareyRealization
import CurveComplexGenusTwo.Topology.FareyArithmetic
import CurveComplexGenusTwo.Topology.FareyParents
import CurveComplexGenusTwo.Foundations.FullSubcomplexWeakTopology
import CurveComplexGenusTwo.Foundations.FiniteSupportTopology

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- The denominator filtration of the actual weak Farey realization. -/
def fareyStage (n : ℕ) : Set (RealizationPoint fareyComplex) :=
  fullSupportLocus fareyComplex (fun v => fareyDenominator v ≤ n)

theorem fareyStage_isClosed (n : ℕ) : IsClosed (fareyStage n) :=
  isClosed_fullSupportLocus fareyComplex _

def fareyStageFaceIndex (n : ℕ) :=
  FullFaceIndex fareyComplex (fun v => fareyDenominator v ≤ n)

noncomputable def fareyStageCoverMap (n : ℕ) :
    (Σ σ : fareyStageFaceIndex n, FiniteSimplex σ.1) → fareyStage n :=
  fullFaceCoverMap fareyComplex (fun v => fareyDenominator v ≤ n)

theorem fareyStageCoverMap_isQuotientMap (n : ℕ) :
    Topology.IsQuotientMap (fareyStageCoverMap n) :=
  fullFaceCoverMap_isQuotientMap fareyComplex
    (fun v => fareyDenominator v ≤ n)

theorem fareyStage_mono {m n : ℕ} (hmn : m ≤ n) :
    fareyStage m ⊆ fareyStage n := by
  intro x hx w hnot
  exact hx w (fun hwm => hnot (hwm.trans hmn))

theorem fareyStage_exhaustive (x : RealizationPoint fareyComplex) :
    ∃ n : ℕ, x ∈ fareyStage n := by
  obtain ⟨σ, hσ, hzero, hsum⟩ := x.liesInFace
  let n : ℕ := σ.sup fareyDenominator
  refine ⟨n, ?_⟩
  intro w hw
  by_contra hneq
  have hwσ : w ∈ σ := by
    by_contra hnot
    exact hneq (hzero w hnot)
  exact hw (Finset.le_sup (f := fareyDenominator) hwσ)

theorem continuous_fareyStageHomotopy_of_faces
    {Y : Type*} [TopologicalSpace Y]
    (n : ℕ) (f : fareyStage n × ConeTime → Y)
    (hfaces : Continuous (fun p :
      (Σ σ : fareyStageFaceIndex n, FiniteSimplex σ.1) × ConeTime =>
      f (fareyStageCoverMap n p.1, p.2))) :
    Continuous f :=
  (fareyStageCoverMap_isQuotientMap n).continuous_lift_prod_left hfaces

/-- A face in the `n`-th stage containing a vertex of denominator `n > 1`
has no other vertex of that denominator. -/
theorem fareyFace_unique_top_vertex
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (n : ℕ) (hn : 1 < n)
    (hstage : ∀ w ∈ σ, fareyDenominator w ≤ n)
    (v : FareySlope) (hv : v ∈ σ) (hvn : fareyDenominator v = n) :
    ∀ w ∈ σ, w ≠ v → fareyDenominator w < n := by
  intro w hw hne
  have hle := hstage w hw
  have hneq : fareyDenominator w ≠ n := by
    intro heq
    have h := fareyFace_atMostOne_of_denominator_gt_one σ hσ.2 n hn
      w v hw hv heq hvn
    exact hne h
  omega

/-- Every other vertex of such a face is one of the two Farey parents.
This is the geometric input for the elementary two-simplex collapse. -/
theorem fareyFace_other_vertices_are_parents
    (σ : Finset FareySlope) (hσ : σ ∈ fareyComplex.faces)
    (n : ℕ) (hn : 1 < n)
    (hstage : ∀ w ∈ σ, fareyDenominator w ≤ n)
    (p : ℚ) (hp : some p ∈ σ) (hpn : p.den = n) :
    ∃ l r : ℚ,
      l.den < n ∧ r.den < n ∧
      FareyAdjacent (some l) (some r) ∧
      FareyAdjacent (some l) (some p) ∧
      FareyAdjacent (some r) (some p) ∧
      (∀ w ∈ σ, w ≠ some p → w = some l ∨ w = some r) := by
  have hpgt : 1 < p.den := by omega
  obtain ⟨l, r, hld, hrd, hlp, hrp, hlr, _, _, _, hlink⟩ :=
    farey_parents_and_lower_link p hpgt
  refine ⟨l, r, by omega, by omega, hlr, hlp, hrp, ?_⟩
  intro w hw hwp
  have hsmall : fareyDenominator w < n :=
    fareyFace_unique_top_vertex σ hσ n hn hstage (some p) hp
      (by simpa [fareyDenominator] using hpn) w hw hwp
  have hadj : FareyAdjacent w (some p) := hσ.2 hw hp hwp
  cases w with
  | none =>
      exact False.elim (farey_infinity_not_lower_neighbor p hpgt hadj)
  | some q =>
      have hlow : q.den < p.den := by
        simpa [fareyDenominator, hpn] using hsmall
      exact (hlink (some q) hlow).mp hadj

end CurveComplexGenusTwo.Topology
