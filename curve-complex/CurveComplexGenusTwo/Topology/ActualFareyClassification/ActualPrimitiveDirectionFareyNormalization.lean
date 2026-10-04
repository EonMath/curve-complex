import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualFareySlopeDirectionSource
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalPrimitiveTorusStraightening
open Set Topology Schoenflies CurveComplex
open CurveComplexGenusTwo.Topology CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
/-- A primitive integer direction determines the actual Farey reference image;
the sole sign ambiguity is removed by reversing the circle parameter. -/
theorem actual_primitive_winding_has_farey_reference_image
    (m n : ℤ) (h : m.gcd n=1) :
    ∃ s : FareySlope,range (torusWindingMap m n)=
      range (torusWindingMap (slopeDirection s).1 (slopeDirection s).2) := by
  have hpositive (a b : ℤ) (hb : 0<b) (hab : a.gcd b=1) :
      ∃ q : ℚ,q.num=a ∧ (q.den:ℤ)=b := by
    have hc : a.natAbs.Coprime b.natAbs := hab
    let q := Rat.mk' a b.natAbs (by omega) hc
    refine ⟨q,rfl,?_⟩
    change (b.natAbs:ℤ)=b
    simpa only [Int.natCast_natAbs,abs_of_pos hb]
  by_cases hn : n=0
  · subst n
    have hm : m=1 ∨ m= -1 := by
      have hmabs : m.natAbs=1 := by simpa using h
      exact Int.natAbs_eq_iff.mp hmabs
    refine ⟨none,?_⟩
    rcases hm with rfl | rfl
    · rfl
    · simpa only [slopeDirection,neg_zero] using torusWindingMap_neg_range 1 0
  · rcases lt_or_gt_of_ne hn with hneg | hpos
    · obtain ⟨q,hqnum,hqden⟩ := hpositive (-m) (-n) (neg_pos.mpr hneg) (by simpa using h)
      refine ⟨some q,?_⟩
      change range (torusWindingMap m n)=range (torusWindingMap q.num (q.den:ℤ))
      rw [hqnum,hqden,torusWindingMap_neg_range]
    · obtain ⟨q,hqnum,hqden⟩ := hpositive m n hpos h
      refine ⟨some q,?_⟩
      change range (torusWindingMap m n)=range (torusWindingMap q.num (q.den:ℤ))
      rw [hqnum,hqden]
#print axioms actual_primitive_winding_has_farey_reference_image
