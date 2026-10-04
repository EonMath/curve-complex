import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.FourComponentInnermost
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.WeightedBigonReplacementStatement
import CurveComplexGenusTwo.Topology.IntersectionParity.EmptyDiskSidesStatement

namespace CurveComplex.HyperellipticModel
open Set Topology

private theorem transverse_of_disjoint
    {E : Type} [TopologicalSpace E]
    (a b : Curve E) (h : Disjoint a.image b.image) : Transverse a b := by
  have heq : a.image ∩ b.image = ∅ := Set.disjoint_iff_inter_eq_empty.mp h
  constructor
  · rw [heq]
    exact Set.finite_empty
  · intro p hp
    rw [heq] at hp
    simpa using hp

theorem four_component_global_bigon_weighted_drop
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (A B : Fin 2 → EssentialCurve E)
    (hAd : Disjoint (A 0).val.image (A 1).val.image)
    (hBd : Disjoint (B 0).val.image (B 1).val.image)
    (ht : ∀ i j, Transverse (A i).val (B j).val)
    (i j : Fin 2) (D : LocalSurgery.TwoCurveDisk (A i).val (B j).val)
    (hGlobal : Disjoint D.openInterior
      (((A 0).val.image ∪ (A 1).val.image) ∪
        ((B 0).val.image ∪ (B 1).val.image)))
    (V : Set E) (hV : IsOpen V) (hDV : range D.disk ⊆ V) :
    let r : Bool × Fin 2 → EssentialCurve E :=
      fun p => if p.1 then B p.2 else A p.2
    ∃ k : Bool × Fin 2, ∃ H : AmbientIsotopy E,
      ∃ r' : Bool × Fin 2 → EssentialCurve E,
        (k = (false, i) ∨ k = (true, j)) ∧
        (∀ l, l ≠ k → r' l = r l) ∧
        H.finalMap '' (r k).val.image = (r' k).val.image ∧
        (∀ t x, x ∉ V → H.map (t, x) = x) ∧
        (∀ l, Quotient.mk (essentialCurveSetoid E) (r' l) =
          Quotient.mk (essentialCurveSetoid E) (r l)) ∧
        (∀ p q, p ≠ q → Transverse (r' p).val (r' q).val) ∧
        (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
          if p = q then 0 else
            ((r' p).val.image ∩ (r' q).val.image).ncard) <
        (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
          if p = q then 0 else
            ((r p).val.image ∩ (r q).val.image).ncard) := by
  classical
  let r : Bool × Fin 2 → EssentialCurve E :=
    fun p => if p.1 then B p.2 else A p.2
  have hAD : Transverse (A 0).val (A 1).val :=
    transverse_of_disjoint _ _ hAd
  have hDA : Transverse (A 1).val (A 0).val :=
    transverse_of_disjoint _ _ hAd.symm
  have hBD : Transverse (B 0).val (B 1).val :=
    transverse_of_disjoint _ _ hBd
  have hDB : Transverse (B 1).val (B 0).val :=
    transverse_of_disjoint _ _ hBd.symm
  have hr : ∀ p q, p ≠ q → Transverse (r p).val (r q).val := by
    intro p q hpq
    rcases p with ⟨bp, ip⟩
    rcases q with ⟨bq, iq⟩
    cases bp <;> cases bq <;> fin_cases ip <;> fin_cases iq
    all_goals simp [r] at hpq ⊢
    all_goals first
      | exact hAD
      | exact hDA
      | exact hBD
      | exact hDB
      | exact ht _ _
      | exact transverse_symm_of_chart (ht _ _)
      | exact False.elim (hpq rfl)
  have hAi : (A i).val.image ⊆ (A 0).val.image ∪ (A 1).val.image := by
    fin_cases i
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have hBj : (B j).val.image ⊆ (B 0).val.image ∪ (B 1).val.image := by
    fin_cases j
    · exact Set.subset_union_left
    · exact Set.subset_union_right
  have hpair : Disjoint D.openInterior ((A i).val.image ∪ (B j).val.image) :=
    hGlobal.mono_right (Set.union_subset
      (hAi.trans Set.subset_union_left)
      (hBj.trans Set.subset_union_right))
  have hclean := LocalSurgery.empty_two_curve_disk_has_clean_sides
    (A i) (B j) (ht i j) D hpair
  exact FiniteMinimalCompatibility.finite_family_weighted_bigon_replacement
    E (Bool × Fin 2) r hr (false, i) (true, j) (by simp)
    D.firstCorner D.secondCorner D.corners_ne
    D.firstSide D.secondSide D.first_embedded D.second_embedded
    D.first_zero D.second_zero D.first_one D.second_one
    D.first_on_curve D.second_on_curve hclean.1 hclean.2
    D.disk D.disk_embedded D.boundary_eq hpair V hV hDV

end CurveComplex.HyperellipticModel
