import CurveComplexGenusTwo.Topology.ArcStraightening
import Schoenflies.JordanSchoenflies

open Set Topology Schoenflies

namespace CurveComplex.HyperellipticModel

private theorem point_of_inter_singleton {K L : Set Plane} {p z : Plane}
    (h : K ∩ L = {p}) (hzK : z ∈ K) (hzL : z ∈ L) : z = p :=
  Set.mem_singleton_iff.mp (h ▸ ⟨hzK, hzL⟩)

private theorem points_of_inter_pair {K L : Set Plane} {p q z : Plane}
    (h : K ∩ L = {p, q}) (hzK : z ∈ K) (hzL : z ∈ L) : z = p ∨ z = q := by
  have hz : z ∈ ({p, q} : Set Plane) := h ▸ ⟨hzK, hzL⟩
  simpa using hz

/-- Closed regions of an arbitrary Jordan crosscut meet exactly at the cut. -/
theorem arbitrary_crosscut_closed_regions_inter
    {C P A B : Set Plane} {p q : Plane}
    (hC : IsJordanCurve C) (hP : IsArcBetween P p q)
    (hcut : IsCutPair C p q A B) (hPi : P \ {p, q} ⊆ inside C) :
    closure (inside (A ∪ P)) ∩ closure (inside (B ∪ P)) = P := by
  have hAP : A ∩ P = {p, q} := by
    ext z
    constructor
    · intro hz
      by_contra hn
      exact inside_subset_compl (hPi ⟨hz.2, hn⟩) (hcut.fst_subset hz.1)
    · rintro (rfl | rfl)
      · exact ⟨hcut.fst.left_mem, hP.left_mem⟩
      · exact ⟨hcut.fst.right_mem, hP.right_mem⟩
  have hBP : B ∩ P = {p, q} := by
    ext z
    constructor
    · intro hz
      by_contra hn
      exact inside_subset_compl (hPi ⟨hz.2, hn⟩) (hcut.snd_subset hz.1)
    · rintro (rfl | rfl)
      · exact ⟨hcut.snd.left_mem, hP.left_mem⟩
      · exact ⟨hcut.snd.right_mem, hP.right_mem⟩
  have hJA := IsJordanCurve.of_two_arcs hcut.fst hP.reverse
    (fun z hzA hzP => points_of_inter_pair hAP hzA hzP)
  have hJB := IsJordanCurve.of_two_arcs hcut.snd hP.reverse
    (fun z hzB hzP => points_of_inter_pair hBP hzB hzP)
  have hsplit := general_crosscut_arbitrary_of_endpoints hC hP hcut hPi
  have hAsub : inside (A ∪ P) ⊆ inside C := by
    intro z hz
    exact (show z ∈ inside C \ P from hsplit.1 ▸ Or.inl hz).1
  have hBsub : inside (B ∪ P) ⊆ inside C := by
    intro z hz
    exact (show z ∈ inside C \ P from hsplit.1 ▸ Or.inr hz).1
  rw [(IsRegionOf.inside _).closure_eq (jordan_curve_theorem hJA),
    (IsRegionOf.inside _).closure_eq (jordan_curve_theorem hJB)]
  ext z
  constructor
  · rintro ⟨hzA | (hzA | hzP), hzB | (hzB | hzP')⟩
    · exact False.elim (disjoint_left.mp hsplit.2.1 hzA hzB)
    · exact False.elim ((hAsub hzA).1 (hcut.snd_subset hzB))
    · exact hzP'
    · exact False.elim ((hBsub hzB).1 (hcut.fst_subset hzA))
    · have hz := hcut.inter_eq ▸ (show z ∈ A ∩ B from ⟨hzA, hzB⟩)
      rcases hz with rfl | rfl
      · exact hP.left_mem
      · exact hP.right_mem
    · exact hzP'
    · exact hzP
    · exact hzP
    · exact hzP
  · intro hz
    exact ⟨Or.inr (Or.inr hz), Or.inr (Or.inr hz)⟩

/-- Two cuts choose compatible regions for nested tangent Jordan boundaries.
The choice is made by the side containing the unused inner arc. -/
theorem tangent_jordan_connector_half_regions
    {C D A₀ A₁ B₀ B₁ P : Set Plane} {p x y : Plane}
    (hC : IsJordanCurve C)
    (hA : IsCutPair C p x A₀ A₁) (hB : IsCutPair D p y B₀ B₁)
    (hP : IsArcBetween P x y)
    (hCD : C ∩ D = {p}) (hPC : P ∩ C = {x}) (hPD : P ∩ D = {y})
    (hDi : D \ {p} ⊆ inside C) (hPi : P \ {x} ⊆ inside C) :
    ∃ flip : Bool,
      let J₀ := A₀ ∪ P ∪ (if flip then B₁ else B₀)
      let J₁ := A₁ ∪ P ∪ (if flip then B₀ else B₁)
      IsJordanCurve J₀ ∧ IsJordanCurve J₁ ∧
        closure (inside J₀) ∩ closure (inside J₁) = P ∪ {p} ∧
        inside C \ inside D ⊆ closure (inside J₀) ∪ closure (inside J₁) := by
  have hPB₀ : ∀ z ∈ B₀, z ∈ P → z = y := by
    intro z hzB hzP
    exact point_of_inter_singleton hPD (hzP) (hB.fst_subset hzB)
  have hQ : IsArcBetween (B₀ ∪ P) p x := hB.fst.concatenate hP.reverse hPB₀
  have hQi : (B₀ ∪ P) \ {p, x} ⊆ inside C := by
    rintro z ⟨hz | hz, hn⟩
    · exact hDi ⟨hB.fst_subset hz, fun he => hn (Or.inl he)⟩
    · exact hPi ⟨hz, fun he => hn (Or.inr he)⟩
  have hsplit := general_crosscut_arbitrary_of_endpoints hC hQ hA hQi
  have hB₁cover : B₁ \ {p, y} ⊆ inside (A₀ ∪ (B₀ ∪ P)) ∪ inside (A₁ ∪ (B₀ ∪ P)) := by
    rw [← hsplit.1]
    rintro z ⟨hz, hn⟩
    refine ⟨hDi ⟨hB.snd_subset hz, fun he => hn (Or.inl he)⟩, ?_⟩
    rintro (hz₀ | hzP)
    · exact hn (hB.inter_eq ▸ ⟨hz₀, hz⟩)
    · have he : z = y := point_of_inter_singleton hPD (hzP) (hB.snd_subset hz)
      exact hn (Or.inr he)
  have choose := hB.snd.isPreconnected_diff.subset_or_subset
    (isOpen_inside (by exact (hA.fst.isArc.isCompact.union hQ.isArc.isCompact).isClosed))
    (isOpen_inside (by exact (hA.snd.isArc.isCompact.union hQ.isArc.isCompact).isClosed))
    hsplit.2.1 hB₁cover
  have oriented {A A' : Set Plane}
      (hAA : IsCutPair C p x A A')
      (hside : B₁ \ {p, y} ⊆ inside (A ∪ (B₀ ∪ P))) :
      IsJordanCurve (A ∪ P ∪ B₁) ∧ IsJordanCurve (A' ∪ P ∪ B₀) ∧
        closure (inside (A ∪ P ∪ B₁)) ∩ closure (inside (A' ∪ P ∪ B₀)) = P ∪ {p} ∧
        inside C \ inside D ⊆ closure (inside (A ∪ P ∪ B₁)) ∪
          closure (inside (A' ∪ P ∪ B₀)) := by
    have hAP : ∀ z ∈ A, z ∈ P → z = x := by
      intro z hzA hzP
      exact point_of_inter_singleton hPC (hzP) (hAA.fst_subset hzA)
    have hAPArc : IsArcBetween (A ∪ P) p y := hAA.fst.concatenate hP hAP
    have hAB₀ : (A ∪ P) ∩ B₀ = {p, y} := by
      apply subset_antisymm
      · rintro z ⟨hzA | hzP, hzB⟩
        · have he : z = p := point_of_inter_singleton hCD (hAA.fst_subset hzA) (hB.fst_subset hzB)
          exact Or.inl he
        · exact Or.inr (point_of_inter_singleton hPD (hzP) (hB.fst_subset hzB))
      · rintro z (rfl | rfl)
        · exact ⟨hAPArc.left_mem, hB.fst.left_mem⟩
        · exact ⟨hAPArc.right_mem, hB.fst.right_mem⟩
    have hOld : IsJordanCurve (A ∪ (B₀ ∪ P)) := by
      have h := IsJordanCurve.of_two_arcs hAPArc hB.fst.reverse
        (fun z hzA hzB => points_of_inter_pair hAB₀ hzA hzB)
      convert h using 1; ext z; simp only [mem_union]; tauto
    have hSecond : IsCutPair (A ∪ (B₀ ∪ P)) p y (A ∪ P) B₀ :=
      ⟨hAPArc, hB.fst, by ext z; simp only [mem_union]; tauto, hAB₀⟩
    have hsplit₂ := general_crosscut_arbitrary_of_endpoints hOld hB.snd hSecond hside
    have hNewMeet : (A ∪ P) ∩ B₁ = {p, y} := by
      apply subset_antisymm
      · rintro z ⟨hzA | hzP, hzB⟩
        · exact Or.inl (point_of_inter_singleton hCD (hAA.fst_subset hzA) (hB.snd_subset hzB))
        · exact Or.inr (point_of_inter_singleton hPD (hzP) (hB.snd_subset hzB))
      · rintro z (rfl | rfl)
        · exact ⟨hAPArc.left_mem, hB.snd.left_mem⟩
        · exact ⟨hAPArc.right_mem, hB.snd.right_mem⟩
    have hNew : IsJordanCurve (A ∪ P ∪ B₁) :=
      IsJordanCurve.of_two_arcs hAPArc hB.snd.reverse
        (fun z hzA hzB => points_of_inter_pair hNewMeet hzA hzB)
    have hOther : IsJordanCurve (A' ∪ P ∪ B₀) := by
      have hMeet : A' ∩ (B₀ ∪ P) ⊆ {p, x} := by
        rintro z ⟨hzA, hzB | hzP⟩
        · exact Or.inl (point_of_inter_singleton hCD (hAA.snd_subset hzA) (hB.fst_subset hzB))
        · exact Or.inr (point_of_inter_singleton hPC (hzP) (hAA.snd_subset hzA))
      have h := IsJordanCurve.of_two_arcs hAA.snd hQ.reverse
        (fun z hzA hzQ => hMeet ⟨hzA, hzQ⟩)
      convert h using 1; ext z; simp only [mem_union]; tauto
    have hNewSub : closure (inside (A ∪ P ∪ B₁)) ⊆ closure (inside (A ∪ (B₀ ∪ P))) := by
      apply closure_mono
      intro z hz
      exact (show z ∈ inside (A ∪ (B₀ ∪ P)) \ B₁ from hsplit₂.1 ▸ Or.inl hz).1
    have hOldMeet := arbitrary_crosscut_closed_regions_inter hC hQ hAA hQi
    have hOtherEq : A' ∪ P ∪ B₀ = A' ∪ (B₀ ∪ P) := by
      ext z; simp only [mem_union]; tauto
    have hLabel : closure (inside (A ∪ P ∪ B₁)) ∩ (A ∪ (B₀ ∪ P)) = A ∪ P :=
      hsplit₂.2.2.2.2.2.2.2.2.1
    refine ⟨hNew, hOther, subset_antisymm ?_ ?_, ?_⟩
    · intro z hz
      have hzQ : z ∈ B₀ ∪ P := hOldMeet ▸
        ⟨hNewSub hz.1, by simpa only [hOtherEq] using hz.2⟩
      have hzAP : z ∈ A ∪ P := hLabel ▸ ⟨hz.1, Or.inr hzQ⟩
      rcases hzAP with hzA | hzP
      · rcases hzQ with hzB | hzP
        · exact Or.inr (point_of_inter_singleton hCD (hAA.fst_subset hzA) (hB.fst_subset hzB))
        · exact Or.inl hzP
      · exact Or.inl hzP
    · intro z hz
      have hzNew : z ∈ A ∪ P ∪ B₁ := by
        rcases hz with hz | rfl
        · exact Or.inl (Or.inr hz)
        · exact Or.inl (Or.inl hAA.fst.left_mem)
      have hzOther : z ∈ A' ∪ P ∪ B₀ := by
        rcases hz with hz | rfl
        · exact Or.inl (Or.inr hz)
        · exact Or.inl (Or.inl hAA.snd.left_mem)
      exact ⟨frontier_subset_closure ((jordan_curve_theorem hNew).frontier_inside.symm ▸ hzNew),
        frontier_subset_closure ((jordan_curve_theorem hOther).frontier_inside.symm ▸ hzOther)⟩
    · intro z hz
      have hmemNew (h : z ∈ A ∪ P ∪ B₁) : z ∈ closure (inside (A ∪ P ∪ B₁)) :=
        frontier_subset_closure ((jordan_curve_theorem hNew).frontier_inside.symm ▸ h)
      have hmemOther (h : z ∈ A' ∪ P ∪ B₀) : z ∈ closure (inside (A' ∪ P ∪ B₀)) :=
        frontier_subset_closure ((jordan_curve_theorem hOther).frontier_inside.symm ▸ h)
      by_cases hzQ : z ∈ B₀ ∪ P
      · rcases hzQ with hzB | hzP
        · exact Or.inr (hmemOther (Or.inr hzB))
        · exact Or.inl (hmemNew (Or.inl (Or.inr hzP)))
      have hfirst := general_crosscut_arbitrary_of_endpoints hC hQ hAA hQi
      have hcases : z ∈ inside (A ∪ (B₀ ∪ P)) ∪ inside (A' ∪ (B₀ ∪ P)) :=
        hfirst.1 ▸ ⟨hz.1, hzQ⟩
      rcases hcases with hzOld | hzOther
      · by_cases hzB : z ∈ B₁
        · exact Or.inl (hmemNew (Or.inr hzB))
        have hcases₂ : z ∈ inside (A ∪ P ∪ B₁) ∪ inside (B₀ ∪ B₁) :=
          hsplit₂.1 ▸ ⟨hzOld, hzB⟩
        rcases hcases₂ with hzNew | hzD
        · exact Or.inl (subset_closure hzNew)
        · exact False.elim (hz.2 (by simpa only [hB.union_eq] using hzD))
      · exact Or.inr (subset_closure (by simpa only [hOtherEq] using hzOther))
  rcases choose with h | h
  · exact ⟨true, oriented hA h⟩
  · obtain ⟨h₁, h₀, hmeet, hcover⟩ := oriented hA.symm h
    exact ⟨false, h₀, h₁, by simpa [inter_comm] using hmeet,
      by simpa [union_comm] using hcover⟩

end CurveComplex.HyperellipticModel
