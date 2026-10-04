import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.FourComponentCrosscut
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.SamePairSubdisk

namespace CurveComplex.LocalSurgery
open Set Topology

private def otherFin2 (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

private theorem otherFin2_ne (i : Fin 2) : otherFin2 i ≠ i := by
  fin_cases i <;> simp [otherFin2]

private theorem two_family_union (A : Fin 2 → Set E) (i : Fin 2) :
    A i ∪ A (otherFin2 i) = A 0 ∪ A 1 := by
  fin_cases i <;> simp [otherFin2, Set.union_comm]

private def swapTwoCurveDisk {E : Type} [TopologicalSpace E]
    {a b : Curve E} (D : TwoCurveDisk a b) : TwoCurveDisk b a := {
  firstCorner := D.firstCorner
  secondCorner := D.secondCorner
  corners_ne := D.corners_ne
  firstSide := D.secondSide
  secondSide := D.firstSide
  first_embedded := D.second_embedded
  second_embedded := D.first_embedded
  first_zero := D.second_zero
  second_zero := D.first_zero
  first_one := D.second_one
  second_one := D.first_one
  first_on_curve := D.second_on_curve
  second_on_curve := D.first_on_curve
  sides_inter := by rw [Set.inter_comm]; exact D.sides_inter
  disk := D.disk
  disk_embedded := D.disk_embedded
  boundary_eq := by rw [D.boundary_eq, Set.union_comm] }

theorem four_component_disk_has_globally_empty_interior
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (A B : Fin 2 → EssentialCurve E)
    (hAd : Disjoint (A 0).val.image (A 1).val.image)
    (hBd : Disjoint (B 0).val.image (B 1).val.image)
    (ht : ∀ i j, Transverse (A i).val (B j).val)
    (i0 j0 : Fin 2) (D0 : TwoCurveDisk (A i0).val (B j0).val) :
    ∃ i j, ∃ D : TwoCurveDisk (A i).val (B j).val,
      Disjoint D.openInterior
        (((A 0).val.image ∪ (A 1).val.image) ∪
          ((B 0).val.image ∪ (B 1).val.image)) := by
  classical
  let X : Set E := ((A 0).val.image ∪ (A 1).val.image) ∩
    ((B 0).val.image ∪ (B 1).val.image)
  have hX : X.Finite := by
    have h00 := (ht 0 0).1
    have h01 := (ht 0 1).1
    have h10 := (ht 1 0).1
    have h11 := (ht 1 1).1
    apply (((h00.union h01).union h10).union h11).subset
    intro x hx
    dsimp [X] at hx
    rcases hx with ⟨ha, hb⟩
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (Or.inl (Or.inl ⟨ha, hb⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨ha, hb⟩))
    · exact Or.inl (Or.inr ⟨ha, hb⟩)
    · exact Or.inr ⟨ha, hb⟩
  have cornerX (i j : Fin 2) (D : TwoCurveDisk (A i).val (B j).val) :
      D.firstCorner ∈ X ∧ D.secondCorner ∈ X := by
    constructor
    · exact ⟨(two_family_union (fun k => (A k).val.image) i).symm ▸
        (Or.inl (D.first_on_curve ⟨0, D.first_zero⟩)),
        (two_family_union (fun k => (B k).val.image) j).symm ▸
        (Or.inl (D.second_on_curve ⟨0, D.second_zero⟩))⟩
    · exact ⟨(two_family_union (fun k => (A k).val.image) i).symm ▸
        (Or.inl (D.first_on_curve ⟨1, D.first_one⟩)),
        (two_family_union (fun k => (B k).val.image) j).symm ▸
        (Or.inl (D.second_on_curve ⟨1, D.second_one⟩))⟩
  let P : ℕ → Prop := fun n => ∃ i j, ∃ D : TwoCurveDisk (A i).val (B j).val,
    (X ∩ range D.disk).ncard = n
  have hex : ∃ n, P n := ⟨(X ∩ range D0.disk).ncard, i0, j0, D0, rfl⟩
  obtain ⟨i, j, D, hD⟩ := Nat.find_spec hex
  refine ⟨i, j, D, ?_⟩
  apply Set.disjoint_iff_inter_eq_empty.mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have minContradiction {k l : Fin 2} (D' : TwoCurveDisk (A k).val (B l).val)
      (hlt : (X ∩ range D'.disk).ncard < (X ∩ range D.disk).ncard) : False := by
    have hlt' : (X ∩ range D'.disk).ncard < Nat.find hex := hlt.trans_eq hD
    exact Nat.find_min hex hlt' ⟨k, l, D', rfl⟩
  have hOtherA : Disjoint (A (otherFin2 i)).val.image (A i).val.image := by
    fin_cases i
    · simpa [otherFin2] using hAd.symm
    · simpa [otherFin2] using hAd
  have hOtherB : Disjoint (B (otherFin2 j)).val.image (B j).val.image := by
    fin_cases j
    · simpa [otherFin2] using hBd.symm
    · simpa [otherFin2] using hBd
  obtain ⟨hxI, hxAB⟩ := hx
  rcases hxAB with hxA | hxB
  · have hxA' : x ∈ (A i).val.image ∪ (A (otherFin2 i)).val.image := by
      rw [two_family_union (fun k => (A k).val.image) i]
      exact hxA
    rcases hxA' with hxAi | hxAo
    · have hin : (D.openInterior ∩ ((A i).val.image ∪ (B j).val.image)).Nonempty :=
        ⟨x, hxI, Or.inl hxAi⟩
      obtain ⟨D', _, hlt⟩ :=
        nonempty_two_curve_disk_strict_finite_count (A i) (B j) (ht i j)
          D hin X hX (cornerX i j D).1 (cornerX i j D).2
      exact minContradiction D' hlt
    · obtain ⟨D', _, _, _, hlt⟩ :=
        other_component_intrusion_strict_finite_count
          (A i) (B j) (A (otherFin2 i)) D hOtherA
          ⟨x, hxAo, hxI⟩ X hX (cornerX i j D).1
      exact minContradiction D' hlt
  · have hxB' : x ∈ (B j).val.image ∪ (B (otherFin2 j)).val.image := by
      rw [two_family_union (fun k => (B k).val.image) j]
      exact hxB
    rcases hxB' with hxBj | hxBo
    · have hin : (D.openInterior ∩ ((A i).val.image ∪ (B j).val.image)).Nonempty :=
        ⟨x, hxI, Or.inr hxBj⟩
      obtain ⟨D', _, hlt⟩ :=
        nonempty_two_curve_disk_strict_finite_count (A i) (B j) (ht i j)
          D hin X hX (cornerX i j D).1 (cornerX i j D).2
      exact minContradiction D' hlt
    · obtain ⟨D', _, _, _, hlt⟩ :=
        other_component_intrusion_strict_finite_count
          (B j) (A i) (B (otherFin2 j)) (swapTwoCurveDisk D) hOtherB
          ⟨x, hxBo, hxI⟩ X hX (cornerX i j D).1
      exact minContradiction (swapTwoCurveDisk D') hlt

end CurveComplex.LocalSurgery
