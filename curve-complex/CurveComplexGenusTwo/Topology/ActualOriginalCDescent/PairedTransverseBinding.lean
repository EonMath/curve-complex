import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedLocalWeightedStep
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14PairedSupportedTransversality
import CurveComplexGenusTwo.Topology.IsotopyCurveTransport

namespace CurveComplex.HyperellipticModel
open Set Topology

private theorem transverse_of_same_images
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (a b c d : Curve E)
    (ha : a.image = c.image) (hb : b.image = d.image)
    (ht : Transverse c d) : Transverse a b := by
  refine ⟨?_, ?_⟩
  · simpa only [ha, hb] using ht.1
  · intro p hp
    apply crossesAt_of_curve_images_agree_on_open
      a b c d p Set.univ isOpen_univ (Set.mem_univ p)
    · intro x _
      rw [ha]
    · intro x _
      rw [hb]
    · exact ht.2 p (by simpa only [ha, hb] using hp)

theorem paired_deck_transverse_of_image_equalities
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a b a' b' : Curve E)
    (ha : a'.image = q.deck '' a.image)
    (hb : b'.image = q.deck '' b.image)
    (ht : Transverse a b) : Transverse a' b' := by
  obtain ⟨ht', _⟩ := LocalSurgery.transverse_homeomorph_count q.deck a b ht
  have hia : (LocalSurgery.homeomorphCurve q.deck a).image =
      q.deck '' a.image := Set.range_comp q.deck a.map
  have hib : (LocalSurgery.homeomorphCurve q.deck b).image =
      q.deck '' b.image := Set.range_comp q.deck b.map
  exact transverse_of_same_images a' b'
    (LocalSurgery.homeomorphCurve q.deck a)
    (LocalSurgery.homeomorphCurve q.deck b)
    (ha.trans hia.symm) (hb.trans hib.symm) ht'

theorem paired_first_side_weighted_transverse_bind
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 b1 a0' a1' : EssentialCurve E)
    (hDB : q.deck '' b0.val.image = b1.val.image)
    (r' : Bool × Fin 2 → EssentialCurve E)
    (hfixed : ∀ p, p ≠ (false, 0) →
      r' p = if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2))
    (h0 : a0'.val.image = (r' (false, 0)).val.image)
    (h1 : a1'.val.image = q.deck '' (r' (false, 0)).val.image)
    (htrans : ∀ p q, p ≠ q → Transverse (r' p).val (r' q).val) :
    Transverse a0'.val b0.val ∧ Transverse a0'.val b1.val ∧
      Transverse a1'.val b0.val ∧ Transverse a1'.val b1.val := by
  have hB0 : (r' (true, 0)).val.image = b0.val.image := by
    simpa using congrArg (fun c : EssentialCurve E => c.val.image)
      (hfixed (true, 0) (by decide))
  have hB1 : (r' (true, 1)).val.image = b1.val.image := by
    simpa using congrArg (fun c : EssentialCurve E => c.val.image)
      (hfixed (true, 1) (by decide))
  have hDBrev : q.deck '' b1.val.image = b0.val.image := by
    rw [← hDB, Set.image_image]
    simp [q.deck_involution]
  have ht0 (j : Fin 2) : Transverse (r' (false, 0)).val
      (![b0, b1] j).val := by
    fin_cases j
    · exact transverse_of_same_images _ _ _ _ rfl hB0.symm
        (htrans (false, 0) (true, 0) (by decide))
    · exact transverse_of_same_images _ _ _ _ rfl hB1.symm
        (htrans (false, 0) (true, 1) (by decide))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact transverse_of_same_images _ _ _ _ h0 rfl (ht0 0)
  · exact transverse_of_same_images _ _ _ _ h0 rfl (ht0 1)
  · exact paired_deck_transverse_of_image_equalities q
      (r' (false, 0)).val b1.val a1'.val b0.val h1 hDBrev.symm (ht0 1)
  · exact paired_deck_transverse_of_image_equalities q
      (r' (false, 0)).val b0.val a1'.val b1.val h1 hDB.symm (ht0 0)

theorem paired_second_side_weighted_transverse_bind
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 b1 b0' b1' : EssentialCurve E)
    (hDA : q.deck '' a0.val.image = a1.val.image)
    (r' : Bool × Fin 2 → EssentialCurve E)
    (hfixed : ∀ p, p ≠ (true, 0) →
      r' p = if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2))
    (h0 : b0'.val.image = (r' (true, 0)).val.image)
    (h1 : b1'.val.image = q.deck '' (r' (true, 0)).val.image)
    (htrans : ∀ p q, p ≠ q → Transverse (r' p).val (r' q).val) :
    Transverse a0.val b0'.val ∧ Transverse a0.val b1'.val ∧
      Transverse a1.val b0'.val ∧ Transverse a1.val b1'.val := by
  have hA0 : (r' (false, 0)).val.image = a0.val.image := by
    simpa using congrArg (fun c : EssentialCurve E => c.val.image)
      (hfixed (false, 0) (by decide))
  have hA1 : (r' (false, 1)).val.image = a1.val.image := by
    simpa using congrArg (fun c : EssentialCurve E => c.val.image)
      (hfixed (false, 1) (by decide))
  have hDArev : q.deck '' a1.val.image = a0.val.image := by
    rw [← hDA, Set.image_image]
    simp [q.deck_involution]
  have ht0 (i : Fin 2) : Transverse (![a0, a1] i).val
      (r' (true, 0)).val := by
    fin_cases i
    · exact transverse_of_same_images _ _ _ _ hA0.symm rfl
        (htrans (false, 0) (true, 0) (by decide))
    · exact transverse_of_same_images _ _ _ _ hA1.symm rfl
        (htrans (false, 1) (true, 0) (by decide))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact transverse_of_same_images _ _ _ _ rfl h0 (ht0 0)
  · exact paired_deck_transverse_of_image_equalities q
      a1.val (r' (true, 0)).val a0.val b1'.val hDArev.symm h1 (ht0 1)
  · exact transverse_of_same_images _ _ _ _ rfl h0 (ht0 1)
  · exact paired_deck_transverse_of_image_equalities q
      a0.val (r' (true, 0)).val a1.val b1'.val hDA.symm h1 (ht0 0)

end CurveComplex.HyperellipticModel
