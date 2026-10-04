import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedLocalWeightedStep
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.FourComponentEnergyAlgebra

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem paired_first_side_weighted_data_strict_count
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (ht : ∀ i j : Fin 2,
      Transverse (![a0, a1] i).val (![b0, b1] j).val)
    (H K : AmbientIsotopy E) (r' : Bool × Fin 2 → EssentialCurve E)
    (hfixed : ∀ p, p ≠ (false, 0) →
      r' p = if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2))
    (himage : H.finalMap '' a0.val.image = (r' (false, 0)).val.image)
    (hpartner : ∀ t x, x ∈ a1.val.image → H.map (t, x) = x)
    (hK0 : K.finalMap '' a0.val.image = H.finalMap '' a0.val.image)
    (hK1 : K.finalMap '' a1.val.image =
      M.cover.deck '' (H.finalMap '' a0.val.image))
    (htrans : ∀ p q, p ≠ q → Transverse (r' p).val (r' q).val)
    (hdrop :
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((r' p).val.image ∩ (r' q).val.image).ncard) <
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2)).val.image ∩
            (if q.1 then (![b0, b1] q.2) else (![a0, a1] q.2)).val.image).ncard)) :
    (((K.finalMap '' a0.val.image) ∪ (K.finalMap '' a1.val.image)) ∩
      (b0.val.image ∪ b1.val.image)).ncard <
    ((a0.val.image ∪ a1.val.image) ∩
      (b0.val.image ∪ b1.val.image)).ncard := by
  classical
  let C0 := H.finalMap '' a0.val.image
  let C1 := K.finalMap '' a1.val.image
  have hHinj : Function.Injective H.finalMap := by
    obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
    intro x y hxy
    apply e.injective
    change H.map (⟨1, by norm_num⟩, x) =
      H.map (⟨1, by norm_num⟩, y) at hxy
    simpa only [← he] using hxy
  have hKinj : Function.Injective K.finalMap := by
    obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
    intro x y hxy
    apply e.injective
    change K.map (⟨1, by norm_num⟩, x) =
      K.map (⟨1, by norm_num⟩, y) at hxy
    simpa only [← he] using hxy
  have hHa1 : H.finalMap '' a1.val.image = a1.val.image := by
    calc
      H.finalMap '' a1.val.image = (id : E → E) '' a1.val.image := by
        apply Set.image_congr
        intro x hx
        exact hpartner _ x hx
      _ = a1.val.image := Set.image_id _
  have hMutAd : Disjoint C0 a1.val.image := by
    rw [← hHa1]
    exact Set.disjoint_image_of_injective hHinj hAd
  have hNewAd : Disjoint C0 C1 := by
    change Disjoint (H.finalMap '' a0.val.image)
      (K.finalMap '' a1.val.image)
    rw [← hK0]
    exact Set.disjoint_image_of_injective hKinj hAd
  have hDC : M.cover.deck '' C0 = C1 := hK1.symm
  have hOldFin : ∀ i j : Fin 2,
      ((![(a0.val.image), a1.val.image] i) ∩
        (![b0.val.image, b1.val.image] j)).Finite := by
    intro i j
    fin_cases i
    · fin_cases j
      · simpa using (ht 0 0).1
      · simpa using (ht 0 1).1
    · fin_cases j
      · simpa using (ht 1 0).1
      · simpa using (ht 1 1).1
  have hMutFin : ∀ j : Fin 2,
      (C0 ∩ (![b0.val.image, b1.val.image] j)).Finite := by
    intro j
    fin_cases j
    · have h := (htrans (false, 0) (true, 0) (by decide)).1
      simpa [C0, himage, hfixed] using h
    · have h := (htrans (false, 0) (true, 1) (by decide)).1
      simpa [C0, himage, hfixed] using h
  obtain ⟨hNewFin0, hNewFin1⟩ :=
    paired_partner_crosspair_finite M.cover.deck M.cover.deck_involution
      C0 C1 b0.val.image b1.val.image hDC hDB (hMutFin 0) (hMutFin 1)
  have hNewFin : ∀ j : Fin 2,
      (C1 ∩ (![b0.val.image, b1.val.image] j)).Finite := by
    intro j
    fin_cases j
    · exact hNewFin0
    · exact hNewFin1
  have hdrop' :
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![b0.val.image, b1.val.image] p.2)
              else (![C0, a1.val.image] p.2)) ∩
            (if q.1 then (![b0.val.image, b1.val.image] q.2)
              else (![C0, a1.val.image] q.2))).ncard) <
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![b0.val.image, b1.val.image] p.2)
              else (![a0.val.image, a1.val.image] p.2)) ∩
            (if q.1 then (![b0.val.image, b1.val.image] q.2)
              else (![a0.val.image, a1.val.image] q.2))).ncard) := by
    have hRF (p : Bool × Fin 2) : (r' p).val.image =
        (if p.1 then (![b0.val.image, b1.val.image] p.2)
          else (![C0, a1.val.image] p.2)) := by
      rcases p with ⟨bp, i⟩
      cases bp
      · fin_cases i
        · simpa [C0] using himage.symm
        · simpa using congrArg (fun c : EssentialCurve E => c.val.image)
            (hfixed (false, 1) (by decide))
      · fin_cases i
        · simpa using congrArg (fun c : EssentialCurve E => c.val.image)
            (hfixed (true, 0) (by decide))
        · simpa using congrArg (fun c : EssentialCurve E => c.val.image)
            (hfixed (true, 1) (by decide))
    have hRO (p : Bool × Fin 2) :
        (if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2)).val.image =
        (if p.1 then (![b0.val.image, b1.val.image] p.2)
          else (![a0.val.image, a1.val.image] p.2)) := by
      rcases p with ⟨bp, i⟩
      cases bp <;> fin_cases i <;> rfl
    simpa only [hRF, hRO] using hdrop
  have hstrict := paired_first_family_one_component_drop M.cover.deck
    M.cover.deck_involution a0.val.image a1.val.image b0.val.image b1.val.image
    C0 C1 hDA hDB hDC hAd hBd hMutAd hNewAd hOldFin hMutFin hNewFin hdrop'
  simpa only [C0, C1, hK0] using hstrict

theorem paired_second_side_weighted_data_strict_count
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (hDA : M.cover.deck '' a0.val.image = a1.val.image)
    (hDB : M.cover.deck '' b0.val.image = b1.val.image)
    (ht : ∀ i j : Fin 2,
      Transverse (![a0, a1] i).val (![b0, b1] j).val)
    (H K : AmbientIsotopy E) (r' : Bool × Fin 2 → EssentialCurve E)
    (hfixed : ∀ p, p ≠ (true, 0) →
      r' p = if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2))
    (himage : H.finalMap '' b0.val.image = (r' (true, 0)).val.image)
    (hpartner : ∀ t x, x ∈ b1.val.image → H.map (t, x) = x)
    (hK0 : K.finalMap '' b0.val.image = H.finalMap '' b0.val.image)
    (hK1 : K.finalMap '' b1.val.image =
      M.cover.deck '' (H.finalMap '' b0.val.image))
    (htrans : ∀ p q, p ≠ q → Transverse (r' p).val (r' q).val)
    (hdrop :
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((r' p).val.image ∩ (r' q).val.image).ncard) <
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2)).val.image ∩
            (if q.1 then (![b0, b1] q.2) else (![a0, a1] q.2)).val.image).ncard)) :
    ((a0.val.image ∪ a1.val.image) ∩
      ((K.finalMap '' b0.val.image) ∪ (K.finalMap '' b1.val.image))).ncard <
    ((a0.val.image ∪ a1.val.image) ∩
      (b0.val.image ∪ b1.val.image)).ncard := by
  classical
  let C0 := H.finalMap '' b0.val.image
  let C1 := K.finalMap '' b1.val.image
  have hHinj : Function.Injective H.finalMap := by
    obtain ⟨e, he⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
    intro x y hxy
    apply e.injective
    change H.map (⟨1, by norm_num⟩, x) =
      H.map (⟨1, by norm_num⟩, y) at hxy
    simpa only [← he] using hxy
  have hKinj : Function.Injective K.finalMap := by
    obtain ⟨e, he⟩ := K.homeomorphism_at ⟨1, by norm_num⟩
    intro x y hxy
    apply e.injective
    change K.map (⟨1, by norm_num⟩, x) =
      K.map (⟨1, by norm_num⟩, y) at hxy
    simpa only [← he] using hxy
  have hHb1 : H.finalMap '' b1.val.image = b1.val.image := by
    calc
      H.finalMap '' b1.val.image = (id : E → E) '' b1.val.image := by
        apply Set.image_congr
        intro x hx
        exact hpartner _ x hx
      _ = b1.val.image := Set.image_id _
  have hMutBd : Disjoint C0 b1.val.image := by
    rw [← hHb1]
    exact Set.disjoint_image_of_injective hHinj hBd
  have hNewBd : Disjoint C0 C1 := by
    change Disjoint (H.finalMap '' b0.val.image)
      (K.finalMap '' b1.val.image)
    rw [← hK0]
    exact Set.disjoint_image_of_injective hKinj hBd
  have hDC : M.cover.deck '' C0 = C1 := hK1.symm
  have hOldFin : ∀ i j : Fin 2,
      ((![(a0.val.image), a1.val.image] i) ∩
        (![b0.val.image, b1.val.image] j)).Finite := by
    intro i j
    fin_cases i
    · fin_cases j
      · simpa using (ht 0 0).1
      · simpa using (ht 0 1).1
    · fin_cases j
      · simpa using (ht 1 0).1
      · simpa using (ht 1 1).1
  have hMutFin : ∀ i : Fin 2,
      ((![a0.val.image, a1.val.image] i) ∩ C0).Finite := by
    intro i
    fin_cases i
    · have h := (htrans (false, 0) (true, 0) (by decide)).1
      simpa [C0, himage, hfixed] using h
    · have h := (htrans (false, 1) (true, 0) (by decide)).1
      simpa [C0, himage, hfixed] using h
  have hMutFinC : (C0 ∩ a0.val.image).Finite ∧
      (C0 ∩ a1.val.image).Finite := by
    constructor
    · rw [Set.inter_comm]; simpa using hMutFin 0
    · rw [Set.inter_comm]; simpa using hMutFin 1
  obtain ⟨hNewFinC0, hNewFinC1⟩ :=
    paired_partner_crosspair_finite M.cover.deck M.cover.deck_involution
      C0 C1 a0.val.image a1.val.image hDC hDA hMutFinC.1 hMutFinC.2
  have hNewFin : ∀ i : Fin 2,
      ((![a0.val.image, a1.val.image] i) ∩ C1).Finite := by
    intro i
    fin_cases i
    · rw [Set.inter_comm]; exact hNewFinC0
    · rw [Set.inter_comm]; exact hNewFinC1
  have hdrop' :
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![C0, b1.val.image] p.2)
              else (![a0.val.image, a1.val.image] p.2)) ∩
            (if q.1 then (![C0, b1.val.image] q.2)
              else (![a0.val.image, a1.val.image] q.2))).ncard) <
      (∑ p : Bool × Fin 2, ∑ q : Bool × Fin 2,
        if p = q then 0 else
          ((if p.1 then (![b0.val.image, b1.val.image] p.2)
              else (![a0.val.image, a1.val.image] p.2)) ∩
            (if q.1 then (![b0.val.image, b1.val.image] q.2)
              else (![a0.val.image, a1.val.image] q.2))).ncard) := by
    have hRF (p : Bool × Fin 2) : (r' p).val.image =
        (if p.1 then (![C0, b1.val.image] p.2)
          else (![a0.val.image, a1.val.image] p.2)) := by
      rcases p with ⟨bp, i⟩
      cases bp
      · fin_cases i
        · simpa using congrArg (fun c : EssentialCurve E => c.val.image)
            (hfixed (false, 0) (by decide))
        · simpa using congrArg (fun c : EssentialCurve E => c.val.image)
            (hfixed (false, 1) (by decide))
      · fin_cases i
        · simpa [C0] using himage.symm
        · simpa using congrArg (fun c : EssentialCurve E => c.val.image)
            (hfixed (true, 1) (by decide))
    have hRO (p : Bool × Fin 2) :
        (if p.1 then (![b0, b1] p.2) else (![a0, a1] p.2)).val.image =
        (if p.1 then (![b0.val.image, b1.val.image] p.2)
          else (![a0.val.image, a1.val.image] p.2)) := by
      rcases p with ⟨bp, i⟩
      cases bp <;> fin_cases i <;> rfl
    simpa only [hRF, hRO] using hdrop
  have hstrict := paired_second_family_one_component_drop M.cover.deck
    M.cover.deck_involution a0.val.image a1.val.image b0.val.image b1.val.image
    C0 C1 hDA hDB hDC hAd hBd hMutBd hNewBd hOldFin hMutFin hNewFin hdrop'
  simpa only [C0, C1, hK0] using hstrict

end CurveComplex.HyperellipticModel
