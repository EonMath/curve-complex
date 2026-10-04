import CurveComplexGenusTwo.Topology.ArcCounts.GeneralNonloopIncidence
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopLowDegree
import CurveComplexGenusTwo.Topology.ArcCounts.ActualStrongQuantitativeEulerLowerBound
import CurveComplexGenusTwo.Topology.ArcCounts.GlobalFaceCoverage
namespace CurveComplex.HyperellipticModel
open Set
open scoped Classical BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_nonloop_weighted_face_bound
    (M : HyperellipticModel E S) {sigma : Finset (EssentialArcClass M)}
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hnonloop : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U) :
    3 * F.card ≤ 2 * sigma.card +
      3 * (6 - (markedFamilyVertices (fun i => (r i).val)).card) := by
  classical
  have hp : ∀ V ∈ F, (3:ℕ) ≤ actualIncidentEdgeDegree M r V +
      3 * (if actualIncidentEdgeDegree M r V < 3 then 1 else 0) := by
    intro V hVF
    by_cases h : actualIncidentEdgeDegree M r V < 3
    · simp [h]
    · simp only [h,ite_false,mul_zero,add_zero]
      omega
  have hs := Finset.sum_le_sum hp
  have hcount : (∑ V ∈ F, 3 * (if actualIncidentEdgeDegree M r V < 3 then 1 else 0)) =
      3 * (F.filter (fun V => actualIncidentEdgeDegree M r V < 3)).card := by
    rw [← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_boole,Nat.cast_id]
  simp only [Finset.sum_add_distrib] at hs
  rw [hcount] at hs
  have htotal := actual_nonloop_incident_degree_sum_le M r hd hnonloop F hF
  rw [Fintype.card_coe] at htotal
  have hlow := actual_nonloop_low_degree_faces_card_le_unused_branch M hsigma r hr hd hnonloop F hF
  have h3 : 3 * F.card ≤ (∑ V ∈ F, actualIncidentEdgeDegree M r V) +
      3 * (F.filter (fun V => actualIncidentEdgeDegree M r V < 3)).card := by
    simpa [Nat.mul_comm] using hs
  omega

theorem actual_nonloop_class_family_card_le_twelve
    (M : HyperellipticModel E S) (sigma : Finset (EssentialArcClass M))
    (hsigma : sigma.Nonempty)
    (r : {v // v ∈ sigma} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hnonloop : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1) : sigma.card ≤ 12 := by
  classical
  letI : Nonempty {v // v ∈ sigma} := hsigma.to_subtype
  obtain ⟨F,hEuler,hF⟩ := actual_strong_quantitative_euler_lower_bound M r hd
  apply card12_of_one_weighted_face_family M sigma hsigma r hr hd F hF hEuler
  intro hF
  have hw := actual_nonloop_weighted_face_bound M hsigma r hr hd hnonloop F hF
  omega
end CurveComplex.HyperellipticModel
