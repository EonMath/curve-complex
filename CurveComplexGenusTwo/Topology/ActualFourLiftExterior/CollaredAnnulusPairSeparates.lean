import CurveComplexGenusTwo.Hyperbolic.OriginalG3Annulus.ActualDisjointHomotopicAnnulus

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem collared_annulus_level_pair_separates
    {E : Type} [TopologicalSpace E] [T2Space E]
    (B : Circle × Interval → E) (hB : Topology.IsEmbedding B)
    (hBopen : IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1))) :
    ¬ IsConnected
      ((Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩)) ∪
        Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩)))ᶜ) := by
  let Inner : Set (Circle × Interval) := Set.univ ×ˢ Set.Ioo (0:Interval) 1
  let Middle : Set (Circle × Interval) :=
    {p | (1/3 : ℝ) < (p.2 : ℝ) ∧ (p.2 : ℝ) < 2/3}
  let ClosedMiddle : Set (Circle × Interval) :=
    {p | (1/3 : ℝ) ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2/3}
  let C := Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩))
  let D := Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩))
  let X := B '' Middle
  let K := B '' ClosedMiddle
  have hMiddleInner : Middle ⊆ Inner := by
    rintro ⟨z,t⟩ ⟨ht0,ht1⟩
    exact ⟨Set.mem_univ _, by
      change (0 : Interval) < t ∧ t < 1
      constructor
      · change (0 : ℝ) < (t : ℝ)
        linarith
      · change (t : ℝ) < 1
        linarith⟩
  let f : Inner → E := fun p => B p.val
  have hfEmb : Topology.IsEmbedding f :=
    hB.comp Topology.IsEmbedding.subtypeVal
  have hfRange : Set.range f = B '' Inner := by
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p.val,p.property,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,hp⟩,rfl⟩
  have hfOpen : Topology.IsOpenEmbedding f :=
    ⟨hfEmb,hfRange.symm ▸ hBopen⟩
  have hMiddleOpen : IsOpen X := by
    have hSourceOpen : IsOpen
        {p : Inner | (p.val.2 : ℝ) ∈ Set.Ioo (1/3 : ℝ) (2/3 : ℝ)} :=
      isOpen_Ioo.preimage (by fun_prop)
    have hImage : f '' {p : Inner |
        (p.val.2 : ℝ) ∈ Set.Ioo (1/3 : ℝ) (2/3 : ℝ)} = X := by
      ext x
      constructor
      · rintro ⟨p,hp,rfl⟩
        exact ⟨p.val,hp,rfl⟩
      · rintro ⟨p,hp,rfl⟩
        exact ⟨⟨p,hMiddleInner hp⟩,hp,rfl⟩
    rw [← hImage]
    exact hfOpen.isOpenMap _ hSourceOpen
  have hMiddleAvoid : X ⊆ (C ∪ D)ᶜ := by
    rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩ (hxC | hxD)
    · obtain ⟨w,hw⟩ := hxC
      have he := congrArg (fun p : Circle × Interval => (p.2 : ℝ))
        (hB.injective hw)
      change (1/3 : ℝ) = (t : ℝ) at he
      linarith
    · obtain ⟨w,hw⟩ := hxD
      have he := congrArg (fun p : Circle × Interval => (p.2 : ℝ))
        (hB.injective hw)
      change (2/3 : ℝ) = (t : ℝ) at he
      linarith
  have hClosedMiddleClosed : IsClosed ClosedMiddle := by
    have hcont : Continuous (fun p : Circle × Interval => (p.2 : ℝ)) := by fun_prop
    exact (isClosed_Icc.preimage hcont)
  have hKclosed : IsClosed K :=
    (hClosedMiddleClosed.isCompact.image hB.continuous).isClosed
  have hKcover : K ⊆ X ∪ (C ∪ D) := by
    rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩
    by_cases hlow : (t : ℝ) = 1/3
    · right
      left
      have ht : t = (⟨1/3,by norm_num⟩ : Interval) := Subtype.ext hlow
      rw [ht]
      exact ⟨z,rfl⟩
    by_cases hhigh : (t : ℝ) = 2/3
    · right
      right
      have ht : t = (⟨2/3,by norm_num⟩ : Interval) := Subtype.ext hhigh
      rw [ht]
      exact ⟨z,rfl⟩
    · left
      exact ⟨(z,t),⟨lt_of_le_of_ne ht0 (Ne.symm hlow),
        lt_of_le_of_ne ht1 hhigh⟩,rfl⟩
  have hXsubK : X ⊆ K := by
    rintro x ⟨p,hp,rfl⟩
    exact ⟨p,⟨hp.1.le,hp.2.le⟩,rfl⟩
  have hdisjXK : Disjoint X Kᶜ :=
    Set.disjoint_left.mpr (fun x hx hnot => hnot (hXsubK hx))
  have hCover : (C ∪ D)ᶜ ⊆ X ∪ Kᶜ := by
    intro x hx
    by_cases hxK : x ∈ K
    · rcases hKcover hxK with hxX | hxCD
      · exact Or.inl hxX
      · exact False.elim (hx hxCD)
    · exact Or.inr hxK
  have hXin : X.Nonempty := by
    exact ⟨B (1,⟨1/2,by norm_num⟩),
      ⟨(1,⟨1/2,by norm_num⟩),⟨by norm_num,by norm_num⟩,rfl⟩⟩
  have hOuter : ∃ x ∈ (C ∪ D)ᶜ, x ∉ X := by
    let t : Interval := ⟨1/6,by norm_num⟩
    let x := B (1,t)
    have hxC : x ∉ C := by
      rintro ⟨z,hz⟩
      have he := congrArg (fun p : Circle × Interval => (p.2 : ℝ))
        (hB.injective hz)
      change (1/3 : ℝ) = (t : ℝ) at he
      norm_num [t] at he
    have hxD : x ∉ D := by
      rintro ⟨z,hz⟩
      have he := congrArg (fun p : Circle × Interval => (p.2 : ℝ))
        (hB.injective hz)
      change (2/3 : ℝ) = (t : ℝ) at he
      norm_num [t] at he
    have hxX : x ∉ X := by
      rintro ⟨p,hp,he⟩
      have he' := congrArg (fun p : Circle × Interval => (p.2 : ℝ))
        (hB.injective he)
      change (p.2 : ℝ) = (t : ℝ) at he'
      dsimp [t] at he'
      linarith [hp.1]
    refine ⟨x, ?_, hxX⟩
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨hxC,hxD⟩
  intro hconn
  rcases hconn.isPreconnected.subset_or_subset
    hMiddleOpen hKclosed.isOpen_compl hdisjXK hCover with hSubX | hSubK
  · obtain ⟨x,hx,hnot⟩ := hOuter
    exact hnot (hSubX hx)
  · obtain ⟨x,hx⟩ := hXin
    exact hSubK (hMiddleAvoid hx) (hXsubK hx)

end CurveComplex.HyperellipticModel
