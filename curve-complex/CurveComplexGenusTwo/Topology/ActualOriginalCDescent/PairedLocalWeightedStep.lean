import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.FourComponentWeightedDrop
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedPartnerAvoidance
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedBigonSupport
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14PairedDeckOperation

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem paired_local_four_component_weighted_motion
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
    let r : Bool × Fin 2 → EssentialCurve E :=
      fun p => if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2)
    ∃ V : Set E, ∃ H K : AmbientIsotopy E,
      ∃ k : Bool × Fin 2, ∃ r' : Bool × Fin 2 → EssentialCurve E,
        IsOpen V ∧ range D.disk ⊆ V ∧
        Disjoint (closure V) (M.cover.deck '' closure V) ∧
        Disjoint (closure V) (a1.val.image ∪ b1.val.image) ∧
        (k = (false, 0) ∨ k = (true, 0)) ∧
        (∀ l, l ≠ k → r' l = r l) ∧
        H.finalMap '' (r k).val.image = (r' k).val.image ∧
        (∀ t x, x ∉ V → H.map (t, x) = x) ∧
        (∀ t x, x ∈ a1.val.image ∪ b1.val.image → H.map (t, x) = x) ∧
        (∀ p q, p ≠ q → Transverse (r' p).val (r' q).val) ∧
        (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
          if p = q then 0 else
            ((r' p).val.image ∩ (r' q).val.image).ncard) <
        (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
          if p = q then 0 else
            ((r p).val.image ∩ (r q).val.image).ncard) ∧
        (∀ t x, K.map (t, x) = M.cover.deck
          (H.map (t, M.cover.deck (H.map (t, x))))) ∧
        (∀ t x, K.map (t, M.cover.deck x) = M.cover.deck (K.map (t, x))) ∧
        (∀ t x, x ∈ V → K.map (t, x) = H.map (t, x)) ∧
        (∀ t x, x ∈ M.cover.deck '' V →
          K.map (t, x) = M.cover.deck (H.map (t, M.cover.deck x))) ∧
        (∀ t x, M.cover.projection x ∈ M.cover.branch → K.map (t, x) = x) := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hDArev : M.cover.deck '' a1.val.image = a0.val.image := by
    rw [← hDA, Set.image_image]
    simp [M.cover.deck_involution]
  have hDBrev : M.cover.deck '' b1.val.image = b0.val.image := by
    rw [← hDB, Set.image_image]
    simp [M.cover.deck_involution]
  have hU : M.cover.deck ''
      ((a0.val.image ∪ a1.val.image) ∪ (b0.val.image ∪ b1.val.image)) =
      ((a0.val.image ∪ a1.val.image) ∪ (b0.val.image ∪ b1.val.image)) := by
    simp only [Set.image_union, hDA, hDArev, hDB, hDBrev]
    ac_rfl
  have hdis := LocalSurgery.paired_globally_empty_disk_disjoint_deck
    M.cover a0 a1 b0 b1 hAd hBd hDA hDB ht01 ht10 D
    ((a0.val.image ∪ a1.val.image) ∪ (b0.val.image ∪ b1.val.image))
    hU
    (by exact Set.subset_union_left.trans Set.subset_union_left)
    (by exact Set.subset_union_right.trans Set.subset_union_left)
    (by exact Set.subset_union_left.trans Set.subset_union_right)
    (by exact Set.subset_union_right.trans Set.subset_union_right)
    hGlobal
  have hPartner := LocalSurgery.globally_empty_disk_misses_paired_partners
    a0 a1 b0 b1 hAd hBd ht01 ht10 D hGlobal
  have hFclosed : IsClosed (a1.val.image ∪ b1.val.image) :=
    (isCompact_range a1.val.embedded.continuous).isClosed.union
      (isCompact_range b1.val.embedded.continuous).isClosed
  obtain ⟨V, hV, hDV, hsep, _, hVpartner⟩ :=
    paired_disk_has_deck_separated_support_avoiding M D hdis
      (a1.val.image ∪ b1.val.image) hFclosed hPartner
  let A : Fin 2 → EssentialCurve E := ![a0, a1]
  let B : Fin 2 → EssentialCurve E := ![b0, b1]
  have ht : ∀ i j, Transverse (A i).val (B j).val := by
    intro i j
    fin_cases i
    · fin_cases j
      · exact ht00
      · exact ht01
    · fin_cases j
      · exact ht10
      · exact ht11
  obtain ⟨k, H, r', hchoice, hfixed, himage, hfix, _, htrans, hdrop⟩ :=
    four_component_global_bigon_weighted_drop A B hAd hBd ht 0 0 D
      hGlobal V hV hDV
  have hVsep : Disjoint V (M.cover.deck '' V) :=
    hsep.mono subset_closure (Set.image_mono subset_closure)
  obtain ⟨K, hK, hKeq, hKV, hKdeckV, _, hKram⟩ :=
    M.cover.supported_paired_deck_operation H V hVsep hfix
  have hfixPartner (t x) (hx : x ∈ a1.val.image ∪ b1.val.image) :
      H.map (t, x) = x := by
    have hxNotV : x ∉ V := by
      intro hxV
      exact Set.disjoint_left.mp hVpartner (subset_closure hxV) hx
    exact hfix t x hxNotV
  exact ⟨V, H, K, k, r', hV, hDV, hsep, hVpartner,
    hchoice, hfixed, himage, hfix, hfixPartner, htrans, hdrop,
    hK, hKeq, hKV, hKdeckV, hKram⟩

theorem paired_supported_motion_component_images
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hDA : q.deck '' a0.val.image = a1.val.image)
    (hDB : q.deck '' b0.val.image = b1.val.image)
    (V : Set E) (H K : AmbientIsotopy E)
    (hfix : ∀ t x, x ∉ V → H.map (t, x) = x)
    (hpartner : ∀ t x, x ∈ a1.val.image ∪ b1.val.image → H.map (t, x) = x)
    (hK : ∀ t x, K.map (t, x) = q.deck
      (H.map (t, q.deck (H.map (t, x)))))
    (hKV : ∀ t x, x ∈ V → K.map (t, x) = H.map (t, x)) :
    K.finalMap '' a0.val.image = H.finalMap '' a0.val.image ∧
      K.finalMap '' a1.val.image = q.deck '' (H.finalMap '' a0.val.image) ∧
      K.finalMap '' b0.val.image = H.finalMap '' b0.val.image ∧
      K.finalMap '' b1.val.image = q.deck '' (H.finalMap '' b0.val.image) := by
  have hDArev : q.deck '' a1.val.image = a0.val.image := by
    rw [← hDA, Set.image_image]
    simp [q.deck_involution]
  have hDBrev : q.deck '' b1.val.image = b0.val.image := by
    rw [← hDB, Set.image_image]
    simp [q.deck_involution]
  have hzero (X Y : Set E) (hXY : q.deck '' X = Y)
      (hY : ∀ t x, x ∈ Y → H.map (t, x) = x) :
      K.finalMap '' X = H.finalMap '' X := by
    apply Set.image_congr
    intro x hx
    by_cases hxV : x ∈ V
    · exact hKV _ x hxV
    · have hdeckx : q.deck x ∈ Y := by
        rw [← hXY]
        exact ⟨x, hx, rfl⟩
      change K.map (⟨1, by norm_num⟩, x) = H.map (⟨1, by norm_num⟩, x)
      rw [hK, hfix _ x hxV, hY _ (q.deck x) hdeckx,
        q.deck_involution]
  have hone (X Y : Set E) (hYX : q.deck '' Y = X)
      (hY : ∀ t x, x ∈ Y → H.map (t, x) = x) :
      K.finalMap '' Y = q.deck '' (H.finalMap '' X) := by
    calc
      K.finalMap '' Y = (fun x => q.deck (H.finalMap (q.deck x))) '' Y := by
        apply Set.image_congr
        intro x hx
        change K.map (⟨1, by norm_num⟩, x) =
          q.deck (H.map (⟨1, by norm_num⟩, q.deck x))
        rw [hK, hY _ x hx]
      _ = q.deck '' (H.finalMap '' (q.deck '' Y)) := by
        simp only [Set.image_image]
      _ = q.deck '' (H.finalMap '' X) := by rw [hYX]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hzero _ _ hDA (fun t x hx => hpartner t x (Or.inl hx))
  · exact hone _ _ hDArev (fun t x hx => hpartner t x (Or.inl hx))
  · exact hzero _ _ hDB (fun t x hx => hpartner t x (Or.inr hx))
  · exact hone _ _ hDBrev (fun t x hx => hpartner t x (Or.inr hx))

end CurveComplex.HyperellipticModel
