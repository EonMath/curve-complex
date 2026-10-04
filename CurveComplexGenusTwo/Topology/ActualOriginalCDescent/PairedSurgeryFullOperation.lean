import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedCountBinding
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedTransverseBinding
import CurveComplexGenusTwo.Topology.IsotopyCurveTransport
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14TransverseImageEquality

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem paired_globally_empty_disk_full_four_component_operation
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (ht00 : Transverse a0.val b0.val)
    (ht01 : Transverse a0.val b1.val)
    (ht10 : Transverse a1.val b0.val)
    (ht11 : Transverse a1.val b1.val)
    (D : LocalSurgery.TwoCurveDisk a0.val b0.val)
    (hGlobal : Disjoint D.openInterior
      ((a0.val.image ∪ a1.val.image) ∪
        (b0.val.image ∪ b1.val.image))) :
    ∃ K : AmbientIsotopy E,
      (∀ t x, K.map (t, M.cover.deck x) =
        M.cover.deck (K.map (t, x))) ∧
      (∀ t x, M.cover.projection x ∈ M.cover.branch → K.map (t, x) = x) ∧
      ((∃ a0' a1' : EssentialCurve E,
        a0'.val.image = K.finalMap '' a0.val.image ∧
        a1'.val.image = K.finalMap '' a1.val.image ∧
        Transverse a0'.val b0.val ∧ Transverse a0'.val b1.val ∧
        Transverse a1'.val b0.val ∧ Transverse a1'.val b1.val ∧
        ((a0'.val.image ∪ a1'.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard) ∨
      (∃ b0' b1' : EssentialCurve E,
        b0'.val.image = K.finalMap '' b0.val.image ∧
        b1'.val.image = K.finalMap '' b1.val.image ∧
        Transverse a0.val b0'.val ∧ Transverse a0.val b1'.val ∧
        Transverse a1.val b0'.val ∧ Transverse a1.val b1'.val ∧
        ((a0.val.image ∪ a1.val.image) ∩
          (b0'.val.image ∪ b1'.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard)) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let r : Bool × Fin 2 → EssentialCurve E :=
    fun p => if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2)
  obtain ⟨V, J, K, k, r', _, _, _, _, hchoice, hfixed, himage,
    hfix, hpartner, htrans, hdrop, hK, hKeq, hKV, _, hKram⟩ :=
    paired_local_four_component_weighted_motion M a0 a1 b0 b1
      hAd hBd hDA hDB ht00 ht01 ht10 ht11 D hGlobal
  have hImages := paired_supported_motion_component_images M.cover
    a0 a1 b0 b1 hDA hDB V J K hfix hpartner hK hKV
  have ht : ∀ i j : Fin 2,
      Transverse (![a0, a1] i).val (![b0, b1] j).val := by
    intro i j
    fin_cases i
    · fin_cases j
      · exact ht00
      · exact ht01
    · fin_cases j
      · exact ht10
      · exact ht11
  refine ⟨K, hKeq, hKram, ?_⟩
  rcases hchoice with hk | hk
  · subst k
    obtain ⟨a0', ha0', _⟩ := position_essential_curve_of_isotopy K a0
    obtain ⟨a1', ha1', _⟩ := position_essential_curve_of_isotopy K a1
    have hfixedA : ∀ p, p ≠ (false, 0) → r' p = r p := hfixed
    have himageA : J.finalMap '' a0.val.image = (r' (false, 0)).val.image := by
      simpa [r] using himage
    have htransA := paired_first_side_weighted_transverse_bind M.cover
      a0 a1 b0 b1 a0' a1' hDB r' hfixedA
      (ha0'.trans (hImages.1.trans himageA))
      (ha1'.trans (hImages.2.1.trans
        (congrArg (M.cover.deck '' ·) himageA))) htrans
    have hstrictA := paired_first_side_weighted_data_strict_count M
      a0 a1 b0 b1 hAd hBd hDA hDB ht J K r' hfixedA himageA
      (fun t x hx => hpartner t x (Or.inl hx))
      hImages.1 hImages.2.1 htrans (by simpa only [r] using hdrop)
    left
    exact ⟨a0', a1', ha0', ha1', htransA.1, htransA.2.1,
      htransA.2.2.1, htransA.2.2.2,
      by simpa only [ha0', ha1'] using hstrictA⟩
  · subst k
    obtain ⟨b0', hb0', _⟩ := position_essential_curve_of_isotopy K b0
    obtain ⟨b1', hb1', _⟩ := position_essential_curve_of_isotopy K b1
    have hfixedB : ∀ p, p ≠ (true, 0) → r' p = r p := hfixed
    have himageB : J.finalMap '' b0.val.image = (r' (true, 0)).val.image := by
      simpa [r] using himage
    have htransB := paired_second_side_weighted_transverse_bind M.cover
      a0 a1 b0 b1 b0' b1' hDA r' hfixedB
      (hb0'.trans (hImages.2.2.1.trans himageB))
      (hb1'.trans (hImages.2.2.2.trans
        (congrArg (M.cover.deck '' ·) himageB))) htrans
    have hstrictB := paired_second_side_weighted_data_strict_count M
      a0 a1 b0 b1 hAd hBd hDA hDB ht J K r' hfixedB himageB
      (fun t x hx => hpartner t x (Or.inr hx))
      hImages.2.2.1 hImages.2.2.2 htrans
      (by simpa only [r] using hdrop)
    right
    exact ⟨b0', b1', hb0', hb1', htransB.1, htransB.2.1,
      htransB.2.2.1, htransB.2.2.2,
      by simpa only [hb0', hb1'] using hstrictB⟩

private def pairedOtherIndex (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem paired_any_globally_empty_disk_full_four_component_operation
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (ht00 : Transverse a0.val b0.val)
    (ht01 : Transverse a0.val b1.val)
    (ht10 : Transverse a1.val b0.val)
    (ht11 : Transverse a1.val b1.val)
    (i j : Fin 2)
    (D : LocalSurgery.TwoCurveDisk (![a0, a1] i).val (![b0, b1] j).val)
    (hGlobal : Disjoint D.openInterior
      ((a0.val.image ∪ a1.val.image) ∪
        (b0.val.image ∪ b1.val.image))) :
    ∃ K : AmbientIsotopy E,
      (∀ t x, K.map (t, M.cover.deck x) =
        M.cover.deck (K.map (t, x))) ∧
      (∀ t x, M.cover.projection x ∈ M.cover.branch → K.map (t, x) = x) ∧
      ((∃ a0' a1' : EssentialCurve E,
        a0'.val.image = K.finalMap '' a0.val.image ∧
        a1'.val.image = K.finalMap '' a1.val.image ∧
        Transverse a0'.val b0.val ∧ Transverse a0'.val b1.val ∧
        Transverse a1'.val b0.val ∧ Transverse a1'.val b1.val ∧
        ((a0'.val.image ∪ a1'.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard) ∨
      (∃ b0' b1' : EssentialCurve E,
        b0'.val.image = K.finalMap '' b0.val.image ∧
        b1'.val.image = K.finalMap '' b1.val.image ∧
        Transverse a0.val b0'.val ∧ Transverse a0.val b1'.val ∧
        Transverse a1.val b0'.val ∧ Transverse a1.val b1'.val ∧
        ((a0.val.image ∪ a1.val.image) ∩
          (b0'.val.image ∪ b1'.val.image)).ncard <
        ((a0.val.image ∪ a1.val.image) ∩
          (b0.val.image ∪ b1.val.image)).ncard)) := by
  classical
  let A : Fin 2 → EssentialCurve E := ![a0, a1]
  let B : Fin 2 → EssentialCurve E := ![b0, b1]
  have hDArev : M.cover.deck '' a1.val.image = a0.val.image := by
    rw [← hDA, Set.image_image]
    simp [M.cover.deck_involution]
  have hDBrev : M.cover.deck '' b1.val.image = b0.val.image := by
    rw [← hDB, Set.image_image]
    simp [M.cover.deck_involution]
  have hAU : (A i).val.image ∪ (A (pairedOtherIndex i)).val.image =
      a0.val.image ∪ a1.val.image := by
    fin_cases i <;> simp [A, pairedOtherIndex, Set.union_comm]
  have hBU : (B j).val.image ∪ (B (pairedOtherIndex j)).val.image =
      b0.val.image ∪ b1.val.image := by
    fin_cases j <;> simp [B, pairedOtherIndex, Set.union_comm]
  have hAd' : Disjoint (A i).val.image (A (pairedOtherIndex i)).val.image := by
    fin_cases i
    · simpa [A, pairedOtherIndex] using hAd
    · simpa [A, pairedOtherIndex] using hAd.symm
  have hBd' : Disjoint (B j).val.image (B (pairedOtherIndex j)).val.image := by
    fin_cases j
    · simpa [B, pairedOtherIndex] using hBd
    · simpa [B, pairedOtherIndex] using hBd.symm
  have hDA' : M.cover.deck '' (A i).val.image =
      (A (pairedOtherIndex i)).val.image := by
    fin_cases i
    · simpa [A, pairedOtherIndex] using hDA
    · simpa [A, pairedOtherIndex] using hDArev
  have hDB' : M.cover.deck '' (B j).val.image =
      (B (pairedOtherIndex j)).val.image := by
    fin_cases j
    · simpa [B, pairedOtherIndex] using hDB
    · simpa [B, pairedOtherIndex] using hDBrev
  have ht : ∀ u v, Transverse (A u).val (B v).val := by
    intro u v
    fin_cases u
    · fin_cases v
      · exact ht00
      · exact ht01
    · fin_cases v
      · exact ht10
      · exact ht11
  have hGlobal' : Disjoint D.openInterior
      (((A i).val.image ∪ (A (pairedOtherIndex i)).val.image) ∪
        ((B j).val.image ∪ (B (pairedOtherIndex j)).val.image)) := by
    rw [hAU, hBU]
    exact hGlobal
  obtain ⟨K, hKeq, hKram, hcase⟩ :=
    paired_globally_empty_disk_full_four_component_operation M
      (A i) (A (pairedOtherIndex i)) (B j) (B (pairedOtherIndex j))
      hAd' hBd' hDA' hDB' (ht i j) (ht i (pairedOtherIndex j))
      (ht (pairedOtherIndex i) j)
      (ht (pairedOtherIndex i) (pairedOtherIndex j)) D hGlobal'
  refine ⟨K, hKeq, hKram, ?_⟩
  rcases hcase with hcase | hcase
  · obtain ⟨P0, P1, hP0, hP1, hT00, hT01, hT10, hT11, hstrict⟩ := hcase
    let a0' : EssentialCurve E := if i = 0 then P0 else P1
    let a1' : EssentialCurve E := if i = 0 then P1 else P0
    have h0 : a0'.val.image = K.finalMap '' a0.val.image := by
      fin_cases i
      · simpa [a0', A] using hP0
      · simpa [a0', A, pairedOtherIndex] using hP1
    have h1 : a1'.val.image = K.finalMap '' a1.val.image := by
      fin_cases i
      · simpa [a1', A, pairedOtherIndex] using hP1
      · simpa [a1', A] using hP0
    have hT : Transverse a0'.val b0.val ∧ Transverse a0'.val b1.val ∧
        Transverse a1'.val b0.val ∧ Transverse a1'.val b1.val := by
      fin_cases i <;> fin_cases j <;>
        simp [a0', a1', B, pairedOtherIndex] at hT00 hT01 hT10 hT11 ⊢ <;>
        tauto
    have hPU : a0'.val.image ∪ a1'.val.image =
        P0.val.image ∪ P1.val.image := by
      fin_cases i <;> simp [a0', a1', Set.union_comm]
    left
    exact ⟨a0', a1', h0, h1, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2,
      by simpa only [hPU, hAU, hBU] using hstrict⟩
  · obtain ⟨Q0, Q1, hQ0, hQ1, hT00, hT01, hT10, hT11, hstrict⟩ := hcase
    let b0' : EssentialCurve E := if j = 0 then Q0 else Q1
    let b1' : EssentialCurve E := if j = 0 then Q1 else Q0
    have h0 : b0'.val.image = K.finalMap '' b0.val.image := by
      fin_cases j
      · simpa [b0', B] using hQ0
      · simpa [b0', B, pairedOtherIndex] using hQ1
    have h1 : b1'.val.image = K.finalMap '' b1.val.image := by
      fin_cases j
      · simpa [b1', B, pairedOtherIndex] using hQ1
      · simpa [b1', B] using hQ0
    have hT : Transverse a0.val b0'.val ∧ Transverse a0.val b1'.val ∧
        Transverse a1.val b0'.val ∧ Transverse a1.val b1'.val := by
      fin_cases i <;> fin_cases j <;>
        simp [b0', b1', A, pairedOtherIndex] at hT00 hT01 hT10 hT11 ⊢ <;>
        tauto
    have hPU : b0'.val.image ∪ b1'.val.image =
        Q0.val.image ∪ Q1.val.image := by
      fin_cases j <;> simp [b0', b1', Set.union_comm]
    right
    exact ⟨b0', b1', h0, h1, hT.1, hT.2.1, hT.2.2.1, hT.2.2.2,
      by simpa only [hPU, hAU, hBU] using hstrict⟩

end CurveComplex.HyperellipticModel
