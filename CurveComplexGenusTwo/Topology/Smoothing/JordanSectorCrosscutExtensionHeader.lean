import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
open Set Schoenflies
open CurveComplex

-- Relative extension for an actual Jordan sector; no chosen square chart is
-- assumed. This uses its own two closed Jordan subdisks directly.
theorem jordan_sector_prescribed_crosscut_ambient_extension {C A B : Set Plane} {a b : Plane}
    (hC : IsJordanCurve C) (ha : a ∈ C) (hb : b ∈ C)
    (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
    (hAi : A \ {a,b} ⊆ inside C) (hBi : B \ {a,b} ⊆ inside C)
    (h : ArcHomeo A B a b a b) :
    ∃ F : Plane ≃ₜ Plane, (∀ x ∈ A, F x = h.toFun x) ∧
      F '' A = B ∧ ∀ x, x ∉ inside C → F x = x := by
  have partition {P R₁ R₂ : Set Plane}
      (hP : IsArcBetween P a b) (hcut : IsCutPair C a b R₁ R₂)
      (hPi : P \ {a,b} ⊆ inside C) :
      (((R₁ ∪ P) ∪ inside (R₁ ∪ P)) ∪
        ((R₂ ∪ P) ∪ inside (R₂ ∪ P)) = C ∪ inside C) ∧
      (((R₁ ∪ P) ∪ inside (R₁ ∪ P)) ∩
        ((R₂ ∪ P) ∪ inside (R₂ ∪ P)) = P) := by
    have hclass := general_crosscut_arbitrary_of_endpoints
      hC hP hcut hPi
    have hside₁ : inside (R₁ ∪ P) ⊆ inside C \ P := by
      intro x hx
      rw [hclass.1]
      exact Or.inl hx
    have hside₂ : inside (R₂ ∪ P) ⊆ inside C \ P := by
      intro x hx
      rw [hclass.1]
      exact Or.inr hx
    have hPclosed : P ⊆ C ∪ inside C := by
      intro x hx
      by_cases he : x ∈ ({a,b} : Set Plane)
      · rcases (by simpa using he : x = a ∨ x = b) with rfl | rfl
        · exact Or.inl (hcut.fst_subset hcut.fst.left_mem)
        · exact Or.inl (hcut.fst_subset hcut.fst.right_mem)
      · exact Or.inr (hPi ⟨hx,he⟩)
    constructor
    · ext x
      constructor
      · intro hx
        have hx' : x ∈ C ∪ inside C := by
          rcases hx with ((hR₁ | hP₁) | hi₁) | ((hR₂ | hP₂) | hi₂)
          · exact Or.inl (hcut.fst_subset hR₁)
          · exact hPclosed hP₁
          · exact Or.inr (hside₁ hi₁).1
          · exact Or.inl (hcut.snd_subset hR₂)
          · exact hPclosed hP₂
          · exact Or.inr (hside₂ hi₂).1
        exact hx'
      · intro hx
        have hx' : x ∈ C ∪ inside C :=
          hx
        rcases hx' with hxC | hxin
        · have hxb : x ∈ R₁ ∪ R₂ := hcut.union_eq.symm ▸ hxC
          rcases hxb with hR₁ | hR₂
          · exact Or.inl (Or.inl (Or.inl hR₁))
          · exact Or.inr (Or.inl (Or.inl hR₂))
        · by_cases hxP : x ∈ P
          · exact Or.inl (Or.inl (Or.inr hxP))
          · have hinside : x ∈ inside (R₁ ∪ P) ∪ inside (R₂ ∪ P) := by
              rw [← hclass.1]
              exact ⟨hxin, hxP⟩
            rcases hinside with hi₁ | hi₂
            · exact Or.inl (Or.inr hi₁)
            · exact Or.inr (Or.inr hi₂)
    · ext x
      constructor
      · rintro ⟨hx₁, hx₂⟩
        rcases hx₁ with (hR₁ | hP₁) | hi₁
        · rcases hx₂ with (hR₂ | hP₂) | hi₂
          · have hxEnds : x ∈ ({a, b} : Set Plane) :=
              hcut.inter_eq ▸ ⟨hR₁, hR₂⟩
            rcases (by simpa using hxEnds : x = a ∨ x = b) with rfl | rfl
            · exact hP.left_mem
            · exact hP.right_mem
          · exact hP₂
          · exact False.elim (inside_subset_compl (hside₂ hi₂).1 (hcut.fst_subset hR₁))
        · exact hP₁
        · rcases hx₂ with (hR₂ | hP₂) | hi₂
          · exact False.elim (inside_subset_compl (hside₁ hi₁).1 (hcut.snd_subset hR₂))
          · exact hP₂
          · exact False.elim (Set.disjoint_left.1 hclass.2.1 hi₁ hi₂)
      · intro hxP
        exact ⟨Or.inl (Or.inr hxP), Or.inl (Or.inr hxP)⟩
  have closedCrosscut {P : Set Plane} (hP : IsArcBetween P a b)
      (hPi : P \ {a,b} ⊆ inside C) : P ⊆ C ∪ inside C := by
    intro x hx
    by_cases he : x ∈ ({a,b} : Set Plane)
    · rcases (by simpa using he : x = a ∨ x = b) with rfl | rfl
      · exact Or.inl ha
      · exact Or.inl hb
    · exact Or.inr (hPi ⟨hx,he⟩)
  have meet {R P : Set Plane} (hR : IsArcBetween R a b)
      (hRC : R ⊆ C) (hP : IsArcBetween P a b)
      (hPi : P \ {a,b} ⊆ inside C) : R ∩ P = {a,b} := by
    ext x
    constructor
    · rintro ⟨hxR,hxP⟩
      by_contra he
      exact inside_subset_compl (hPi ⟨hxP,he⟩) (hRC hxR)
    · intro he
      rcases (by simpa using he : x = a ∨ x = b) with rfl | rfl
      · exact ⟨hR.left_mem,hP.left_mem⟩
      · exact ⟨hR.right_mem,hP.right_mem⟩
  have closedSubdisk {R P : Set Plane}
      (hR : IsArcBetween R a b) (hP : IsArcBetween P a b)
      (hRP : R ∩ P = {a,b}) : IsClosed ((R ∪ P) ∪ inside (R ∪ P)) := by
    have hJ : IsJordanCurve (R ∪ P) := by
      apply isJordanCurve_union hR hP
      intro x hxR hxP
      have he : x ∈ ({a,b} : Set Plane) := hRP ▸ ⟨hxR,hxP⟩
      simpa using he
    exact isClosed_union_inside (jordan_curve_theorem hJ)
  classical
  obtain ⟨R₁, R₂, hcut⟩ :=
    exists_isCutPair hC ha hb hA.ne
  obtain ⟨F₁, G₁, h₁, hF₁fixed, hF₁arc, hF₁image⟩ :=
    exists_closed_subdisk_homeomorph_fixing_arc hcut.fst hA hB
      (meet hcut.fst hcut.fst_subset hA hAi)
      (meet hcut.fst hcut.fst_subset hB hBi) h
  obtain ⟨F₂, G₂, h₂, hF₂fixed, hF₂arc, hF₂image⟩ :=
    exists_closed_subdisk_homeomorph_fixing_arc hcut.snd hA hB
      (meet hcut.snd hcut.snd_subset hA hAi)
      (meet hcut.snd hcut.snd_subset hB hBi) h
  let D₁ : Set Plane := (R₁ ∪ A) ∪ inside (R₁ ∪ A)
  let D₂ : Set Plane := (R₂ ∪ A) ∪ inside (R₂ ∪ A)
  let E₁ : Set Plane := (R₁ ∪ B) ∪ inside (R₁ ∪ B)
  let E₂ : Set Plane := (R₂ ∪ B) ∪ inside (R₂ ∪ B)
  let S : Set Plane := C ∪ inside C
  have hpartA : D₁ ∪ D₂ = S ∧ D₁ ∩ D₂ = A :=
    partition hA hcut hAi
  have hpartB : E₁ ∪ E₂ = S ∧ E₁ ∩ E₂ = B :=
    partition hB hcut hBi
  have hR₁A := meet hcut.fst
    hcut.fst_subset hA hAi
  have hR₂A := meet hcut.snd
    hcut.snd_subset hA hAi
  have hR₁B := meet hcut.fst
    hcut.fst_subset hB hBi
  have hR₂B := meet hcut.snd
    hcut.snd_subset hB hBi
  have hD₁ : IsClosed D₁ := closedSubdisk hcut.fst hA hR₁A
  have hD₂ : IsClosed D₂ := closedSubdisk hcut.snd hA hR₂A
  have hE₁ : IsClosed E₁ := closedSubdisk hcut.fst hB hR₁B
  have hE₂ : IsClosed E₂ := closedSubdisk hcut.snd hB hR₂B
  have hagree : ∀ x ∈ D₁ ∩ D₂, F₁ x = F₂ x := by
    intro x hx
    have hxA : x ∈ A := hpartA.2 ▸ hx
    rw [hF₁arc x hxA, hF₂arc x hxA]
  have himageOverlap : F₁ '' (D₁ ∩ D₂) = E₁ ∩ E₂ := by
    rw [hpartA.2, hpartB.2]
    exact hF₁image
  obtain ⟨F, G, hFG, hFD₁, hFD₂⟩ :=
    glue_closed_homeoOn hD₁ hD₂ hE₁ hE₂ h₁ h₂ hagree himageOverlap
  have hFGS : IsHomeoOn F G S S := by
    simpa only [hpartA.1, hpartB.1] using hFG
  let E : S ≃ S := {
    toFun := fun x => ⟨F x, hFGS.mapsTo x.property⟩
    invFun := fun y => ⟨G y, hFGS.mapsTo_inv y.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact hFGS.invOn.1 x.property
    right_inv := by
      intro y
      apply Subtype.ext
      exact hFGS.invOn.2 y.property }
  let e : S ≃ₜ S := {
    toEquiv := E
    continuous_toFun := hFGS.continuousOn.domRestrict.subtype_mk _
    continuous_invFun := hFGS.continuousOn_inv.domRestrict.subtype_mk _ }
  have hboundary : ∀ x : S, (x : Plane) ∈ C → e x = x := by
    intro x hxC
    have hxR : (x : Plane) ∈ R₁ ∪ R₂ := hcut.union_eq.symm ▸ hxC
    apply Subtype.ext
    rcases hxR with hxR₁ | hxR₂
    · exact (hFD₁ x (Or.inl (Or.inl hxR₁))).trans (hF₁fixed x hxR₁)
    · exact (hFD₂ x (Or.inl (Or.inl hxR₂))).trans (hF₂fixed x hxR₂)
  have hFA : F '' A = B := by
    have hEq : EqOn F F₁ A := by
      intro x hxA
      exact hFD₁ x (Or.inl (Or.inr hxA))
    exact hEq.image_eq.trans hF₁image
  have hAclosed : A ⊆ S := closedCrosscut hA hAi
  have hBclosed : B ⊆ S := closedCrosscut hB hBi
  have heImage : e '' {x : S | (x : Plane) ∈ A} =
      {x : S | (x : Plane) ∈ B} := by
    ext y
    constructor
    · rintro ⟨x, hxA, rfl⟩
      have hxB : F x ∈ B := by
        rw [← hFA]
        exact ⟨x, hxA, rfl⟩
      exact hxB
    · intro hyB
      have hyImage : (y : Plane) ∈ F '' A := by rw [hFA]; exact hyB
      obtain ⟨x, hxA, hxy⟩ := hyImage
      refine ⟨⟨x, hAclosed hxA⟩, hxA, ?_⟩
      apply Subtype.ext
      exact hxy
  let U : Set Plane := inside C
  have hSU : U ⊆ S := fun _ hx => Or.inr hx
  have hfix : ∀ x : S, (x : Plane) ∉ U → e x = x := by
    intro x hx
    apply hboundary
    exact x.property.resolve_right hx
  let H := extendClosedHomeomorph S U (isClosed_union_inside (jordan_curve_theorem hC))
    (isOpen_inside hC.isClosed) hSU e hfix
  have hpoint : ∀ x ∈ A, H x = h.toFun x := by
    intro x hx
    have hxS : x ∈ S := hAclosed hx
    have he : (e ⟨x, hxS⟩ : Plane) = h.toFun x :=
      (hFD₁ x (Or.inl (Or.inr hx))).trans (hF₁arc x hx)
    simpa [H, extendClosedHomeomorph, hxS] using he
  refine ⟨H, hpoint, ?_, ?_⟩
  · exact (show EqOn H h.toFun A from hpoint).image_eq.trans h.image_eq
  · intro x hx
    exact extendClosedHomeomorph_apply_outside S U (isClosed_union_inside (jordan_curve_theorem hC))
      (isOpen_inside hC.isClosed) hSU e hfix x hx

#print axioms jordan_sector_prescribed_crosscut_ambient_extension
