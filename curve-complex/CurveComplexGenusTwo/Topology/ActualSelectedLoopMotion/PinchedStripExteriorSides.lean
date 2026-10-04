import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.UnmarkedOppositeSideNested

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

private theorem preconnected_subset_complement_side
    {A C U : Set S} (hU : IsComplementComponent A U)
    (hC : IsPreconnected C) (hCA : C ⊆ Aᶜ)
    {x : S} (hxC : x ∈ C) (hxU : x ∈ U) : C ⊆ U := by
  have heq : U = connectedComponentIn Aᶜ x := by
    exact (hU.2.2.2 _ (isConnected_connectedComponentIn_iff.mpr (hU.2.2.1 hxU))
      (hU.2.1.isPreconnected.subset_connectedComponentIn hxU hU.2.2.1)
      (connectedComponentIn_subset _ _)).symm
  rw [heq]
  exact hC.subset_connectedComponentIn hxC hCA

/-- Choose the two exterior Jordan disks from the strip itself. Their open
interiors avoid every point of the old strip and are disjoint from each other. -/
theorem pinched_strip_exterior_disc_sides
    (M : HyperellipticModel E S) (base : S) (G : C(Interval × Interval,S))
    (hends : ∀ w, G (0,w) = base ∧ G (1,w) = base)
    (hinj : ∀ s w s' w', G (s,w) = G (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (a b : C(Interval,S)) (ha : ∀ s, a s = G (s,0)) (hb : ∀ s, b s = G (s,1)) :
    ∃ U V : Set S, Nonempty (UnmarkedComplementaryDiscSide a U) ∧
      Nonempty (UnmarkedComplementaryDiscSide b V) ∧ Disjoint U V ∧
      (∀ s w, G (s,w) ∉ U) ∧ (∀ s w, G (s,w) ∉ V) := by
  classical
  have habase : a 0 = base := (ha 0).trans (hends 0).1
  have hbbase : b 0 = base := (hb 0).trans (hends 1).1
  have haloop : a 0 = a 1 := habase.trans ((ha 1).trans (hends 0).2).symm
  have hbloop : b 0 = b 1 := hbbase.trans ((hb 1).trans (hends 1).2).symm
  have hloopinj (f : C(Interval,S)) (w : Interval) (hf : ∀ s, f s = G (s,w)) :
      ∀ s s', f s = f s' → s = s' ∨ (s = 0 ∧ s' = 1) ∨ (s = 1 ∧ s' = 0) := by
    intro s s' he
    rcases hinj s w s' w ((hf s).symm.trans (he.trans (hf s'))) with he | he
    · exact Or.inl he.1
    · rcases he with ⟨hs | hs,hs' | hs'⟩
      · exact Or.inl (hs.trans hs'.symm)
      · exact Or.inr (Or.inl ⟨hs,hs'⟩)
      · exact Or.inr (Or.inr ⟨hs,hs'⟩)
      · exact Or.inl (hs.trans hs'.symm)
  let mid : Interval := ⟨1/2,by norm_num⟩
  have hmid : mid ∈ Ioo (0 : Interval) 1 := by
    constructor
    · change (0 : ℝ) < 1/2
      norm_num
    · change (1/2 : ℝ) < 1
      norm_num
  have hne (s w : Interval) (hs : s ∈ Ioo (0 : Interval) 1) : G (s,w) ≠ base := by
    intro he
    rcases hinj s w 0 0 (he.trans (hends 0).1.symm) with he | he
    · exact (ne_of_gt hs.1) he.1
    · rcases he.1 with he | he
      · exact (ne_of_gt hs.1) he
      · exact (ne_of_lt hs.2) he
  have hstrict {s w : Interval} (he : G (s,w) ≠ base) : s ∈ Ioo (0 : Interval) 1 := by
    constructor
    · exact lt_of_le_of_ne s.property.1 (fun hz => he (hz ▸ (hends w).1))
    · exact lt_of_le_of_ne s.property.2 (fun hz => he (hz ▸ (hends w).2))
  have hpuncture (f : C(Interval,S)) (w : Interval) (hw : w = 0 ∨ w = 1)
      (hf : ∀ s, f s = G (s,w)) : G (mid,mid) ∉ range f := by
    rintro ⟨s,he⟩
    rcases hinj mid mid s w (he.symm.trans (hf s)) with he | he
    · rcases hw with hw | hw
      · exact (ne_of_gt hmid.1) (he.2.trans hw)
      · exact (ne_of_lt hmid.2) (he.2.trans hw)
    · rcases he.1 with he | he
      · exact (ne_of_gt hmid.1) he
      · exact (ne_of_lt hmid.2) he
  obtain ⟨A⟩ := unmarked_loop_disc_decomposition_exists M a haloop
    (hloopinj a 0 ha) (G (mid,mid)) (hpuncture a 0 (Or.inl rfl) ha)
  obtain ⟨B⟩ := unmarked_loop_disc_decomposition_exists M b hbloop
    (hloopinj b 1 hb) (G (mid,mid)) (hpuncture b 1 (Or.inr rfl) hb)
  have hmeet : range a ∩ range b = {a 0} := by
    ext x
    constructor
    · rintro ⟨⟨s,hs⟩,⟨s',hs'⟩⟩
      rcases hinj s 0 s' 1 ((ha s).symm.trans (hs.trans (hs'.symm.trans (hb s')))) with he | he
      · have hbad := congrArg Subtype.val he.2
        norm_num at hbad
      · rw [mem_singleton_iff,habase]
        rcases he.1 with he | he
        · rw [← hs,ha,he,(hends 0).1]
        · rw [← hs,ha,he,(hends 0).2]
    · intro hx
      have he : x = base := (mem_singleton_iff.mp hx).trans habase
      constructor
      · exact ⟨0,habase.trans he.symm⟩
      · exact ⟨0,hbbase.trans he.symm⟩
  let C : Set S := G '' (Ioo (0 : Interval) 1 ×ˢ Ioc (0 : Interval) 1)
  have hC : IsPreconnected C :=
    (isPreconnected_Ioo.prod isPreconnected_Ioc).image G G.continuous.continuousOn
  have hCA : C ⊆ (range a)ᶜ := by
    rintro x ⟨⟨s,w⟩,hsw,rfl⟩ ⟨s',he⟩
    rcases hinj s w s' 0 (he.symm.trans (ha s')) with he | he
    · exact (ne_of_gt hsw.2.1) he.2
    · rcases he.1 with he | he
      · exact (ne_of_gt hsw.1.1) he
      · exact (ne_of_lt hsw.1.2) he
  have hxC : G (mid,1) ∈ C := ⟨(mid,1),⟨hmid,by constructor <;> norm_num⟩,rfl⟩
  let W := connectedComponentIn (range a)ᶜ (G (mid,1))
  have hW : IsComplementComponent (range a) W :=
    complementComponent_iff_componentIn.mpr ⟨_,hCA hxC,rfl⟩
  obtain ⟨i,hi⟩ := (A.all_components W).mp hW
  have hCi : C ⊆ A.side i := hi ▸ hC.subset_connectedComponentIn hxC hCA
  have hbi : range b \ {a 0} ⊆ A.side i := by
    rintro x ⟨⟨s,hs⟩,hnebase⟩
    have hsne : G (s,1) ≠ base := by
      intro he
      apply hnebase
      rw [mem_singleton_iff,habase]
      exact hs.symm.trans ((hb s).trans he)
    exact hCi ⟨(s,1),⟨hstrict hsne,by constructor <;> norm_num⟩,(hb s).symm.trans hs⟩
  let j : Fin 2 := if i = 0 then 1 else 0
  have hij : i ≠ j := by fin_cases i <;> norm_num [j]
  have hAij : Disjoint (A.side i) (A.side j) := by
    fin_cases i
    · simpa [j] using A.disjoint
    · simpa [j] using A.disjoint.symm
  obtain ⟨k,hAjB,hak⟩ := unmarked_common_base_opposite_side_nested a b hmeet A B i j hij hbi
  let l : Fin 2 := if k = 0 then 1 else 0
  have hkl : k ≠ l := by fin_cases k <;> norm_num [l]
  have hBkl : Disjoint (B.side k) (B.side l) := by
    fin_cases k
    · simpa [l] using B.disjoint
    · simpa [l] using B.disjoint.symm
  let D : Set S := G '' (Ioo (0 : Interval) 1 ×ˢ Ico (0 : Interval) 1)
  have hD : IsPreconnected D :=
    (isPreconnected_Ioo.prod isPreconnected_Ico).image G G.continuous.continuousOn
  have hDB : D ⊆ (range b)ᶜ := by
    rintro x ⟨⟨s,w⟩,hsw,rfl⟩ ⟨s',he⟩
    rcases hinj s w s' 1 (he.symm.trans (hb s')) with he | he
    · exact (ne_of_lt hsw.2.2) he.2
    · rcases he.1 with he | he
      · exact (ne_of_gt hsw.1.1) he
      · exact (ne_of_lt hsw.1.2) he
  have hxD : G (mid,0) ∈ D := ⟨(mid,0),⟨hmid,by constructor <;> norm_num⟩,rfl⟩
  have hxk : G (mid,0) ∈ B.side k := hak ⟨⟨mid,ha mid⟩,by
    rw [mem_singleton_iff,habase]
    exact hne mid 0 hmid⟩
  have hDk : D ⊆ B.side k :=
    preconnected_subset_complement_side (B.discs k).component hD hDB hxD hxk
  refine ⟨A.side j,B.side l,⟨A.discs j⟩,⟨B.discs l⟩,
    hBkl.mono_left hAjB,?_,?_⟩
  · intro s w hx
    by_cases he : G (s,w) = base
    · apply (A.discs j).component.2.2.1 hx
      exact ⟨0,habase.trans he.symm⟩
    · by_cases hw : w = 0
      · apply (A.discs j).component.2.2.1 hx
        exact ⟨s,(ha s).trans (congrArg (fun w => G (s,w)) hw.symm)⟩
      · have hwi : 0 < w := lt_of_le_of_ne w.property.1 (Ne.symm hw)
        exact Set.disjoint_left.mp hAij
          (hCi ⟨(s,w),⟨hstrict he,hwi,w.property.2⟩,rfl⟩) hx
  · intro s w hx
    by_cases he : G (s,w) = base
    · apply (B.discs l).component.2.2.1 hx
      exact ⟨0,hbbase.trans he.symm⟩
    · by_cases hw : w = 1
      · apply (B.discs l).component.2.2.1 hx
        exact ⟨s,(hb s).trans (congrArg (fun w => G (s,w)) hw.symm)⟩
      · have hwi : w < 1 := lt_of_le_of_ne w.property.2 hw
        exact Set.disjoint_left.mp hBkl
          (hDk ⟨(s,w),⟨hstrict he,w.property.1,hwi⟩,rfl⟩) hx

end CurveComplex.HyperellipticModel
