import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalFiniteFaceTransport
import Mathlib.Topology.Subpath
import ClassificationOfSurfaces.Moise.GraphPolygonalization

open Set CurveComplex

/-- The two literal concatenated paths at a first regional contact. The first
    path follows the anchor from its boundary endpoint; the second follows
    one of the two halves of the current proper arc. -/
noncomputable def regionalRawSurgeryBranch
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor current : C(Interval, ↥F))
    (r s : Interval) (hcontact : anchor r = current s)
    (right : Bool) :
    Path (anchor 0) (if right then current 1 else current 0) := by
  let β : Path (anchor 0) (anchor 1) :=
    { toContinuousMap := anchor, source' := rfl, target' := rfl }
  let α : Path (current 0) (current 1) :=
    { toContinuousMap := current, source' := rfl, target' := rfl }
  let first : Path (anchor 0) (current s) := (β.subpath 0 r).cast rfl hcontact.symm
  let second₁ : Path (current s) (current 1) := by simpa [α] using α.subpath s 1
  let second₀ : Path (current s) (current 0) := by simpa [α] using α.subpath s 0
  cases right
  · exact first.trans second₀
  · exact first.trans second₁

theorem regionalRawSurgeryBranch_range
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor current : C(Interval, ↥F))
    (r s : Interval) (hcontact : anchor r = current s)
    (right : Bool) :
    Set.range (regionalRawSurgeryBranch anchor current r s hcontact right) =
      (anchor '' Set.Icc 0 r) ∪
        (current '' (if right then Set.Icc s 1 else Set.Icc 0 s)) := by
  classical
  dsimp [regionalRawSurgeryBranch]
  cases right
  · rw [Path.trans_range, Path.cast_coe]
    rw [Path.range_subpath_of_le _ _ _ (by exact r.property.1),
      Path.range_subpath_of_ge _ _ _ (by exact s.property.1)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [Path.trans_range, Path.cast_coe]
    rw [Path.range_subpath_of_le _ _ _ (by exact r.property.1),
      Path.range_subpath_of_le _ _ _ (by exact s.property.2)]
    simp only [↓reduceIte]
    rfl

/-- Both halves together recover the whole current arc, with only the cut
    point in common when the current arc is embedded. -/
theorem regionalRawSurgeryBranch_halves
    {S : Type} [TopologicalSpace S] {F : Set S}
    (current : C(Interval, ↥F)) (hemb : Topology.IsEmbedding current)
    (s : Interval) :
    (current '' Set.Icc 0 s) ∪ (current '' Set.Icc s 1) =
      Set.range current ∧
    (current '' Set.Icc 0 s) ∩ (current '' Set.Icc s 1) = {current s} := by
  constructor
  · rw [← Set.image_union]
    have hcover : Set.Icc (0 : Interval) s ∪ Set.Icc s 1 = Set.univ := by
      ext t
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_univ, iff_true]
      rcases le_total t s with h | h
      · exact Or.inl ⟨by exact t.property.1, h⟩
      · exact Or.inr ⟨h, by exact t.property.2⟩
    simp [hcover]
  · rw [← Set.image_inter hemb.injective]
    have hinter : Set.Icc (0 : Interval) s ∩ Set.Icc s 1 = {s} := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_singleton_iff]
      constructor
      · intro h; exact le_antisymm h.1.2 h.2.1
      · intro h; subst t; exact ⟨⟨by exact s.property.1, le_refl _⟩, ⟨le_refl _, by exact s.property.2⟩⟩
    simp [hinter]

/-- If the chosen anchor parameter is its first meeting with the old arc,
    its initial subarc touches the old arc only at the splice point. -/
theorem regional_first_contact_prefix_inter
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor current : C(Interval, ↥F))
    (r s : Interval) (hcontact : anchor r = current s)
    (hfirst : ∀ u : Interval, u < r → anchor u ∉ Set.range current) :
    (anchor '' Set.Icc 0 r) ∩ Set.range current = {current s} := by
  ext x
  constructor
  · rintro ⟨⟨u,hu,rfl⟩,hcurrent⟩
    have hur : u = r := by
      rcases lt_or_eq_of_le hu.2 with h | h
      · exact False.elim ((hfirst u h) hcurrent)
      · exact h
    simp [hur, hcontact]
  · intro hx
    have hxs : x = current s := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨⟨r, ⟨r.property.1, le_refl _⟩, hcontact⟩,
      Set.mem_range_self s⟩

/-- Removing the shared anchor prefix deletes the splice contact from each
    old half, so the residual old/anchor contact budget drops strictly. -/
theorem regionalRawSurgeryBranch_strict_contact_budget
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor current : C(Interval, ↥F))
    (r s : Interval) (hcontact : anchor r = current s)
    (right : Bool)
    (hfinite : (Set.range current ∩ Set.range anchor).Finite) :
    let branch := regionalRawSurgeryBranch anchor current r s hcontact right
    let oldHalf := current '' (if right then Set.Icc s 1 else Set.Icc 0 s)
    ((Set.range branch \ (anchor '' Set.Icc 0 r)) ∩ Set.range anchor).ncard <
      (oldHalf ∩ Set.range anchor).ncard := by
  classical
  dsimp
  rw [regionalRawSurgeryBranch_range]
  let half := current '' (if right then Set.Icc s 1 else Set.Icc 0 s)
  let pref := anchor '' Set.Icc 0 r
  have hsub : (((pref ∪ half) \ pref) ∩ Set.range anchor) ⊆
      half ∩ Set.range anchor := by
    rintro x ⟨⟨hx,hn⟩,ha⟩
    exact ⟨hx.resolve_left hn,ha⟩
  have hhalf : (half ∩ Set.range anchor).Finite :=
    hfinite.subset (by
      rintro x ⟨⟨t,ht,rfl⟩,ha⟩
      exact ⟨Set.mem_range_self t,ha⟩)
  have hpHalf : current s ∈ half := by
    refine ⟨s,?_,rfl⟩
    cases right
    · exact ⟨s.property.1,le_refl _⟩
    · exact ⟨le_refl _,s.property.2⟩
  have hpOld : current s ∈ half ∩ Set.range anchor :=
    ⟨hpHalf, ⟨r,hcontact⟩⟩
  have hpPrefix : current s ∈ pref :=
    ⟨r,⟨r.property.1,le_refl _⟩,hcontact⟩
  have hmissing : current s ∉ (((pref ∪ half) \ pref) ∩ Set.range anchor) :=
    fun h => h.1.2 hpPrefix
  apply Set.ncard_lt_ncard _ hhalf
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro he
  exact hmissing (he.symm ▸ hpOld)

#print axioms regional_first_contact_prefix_inter
#print axioms regionalRawSurgeryBranch_strict_contact_budget

/-- Outside the new shared anchor segment, either surgery branch retains no
    anchor contacts beyond contacts already present on its chosen old half. -/
theorem regionalRawSurgeryBranch_contact_budget
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor current : C(Interval, ↥F))
    (r s : Interval) (hcontact : anchor r = current s)
    (right : Bool)
    (hfinite : (Set.range current ∩ Set.range anchor).Finite) :
    let branch := regionalRawSurgeryBranch anchor current r s hcontact right
    let oldHalf := current '' (if right then Set.Icc s 1 else Set.Icc 0 s)
    ((Set.range branch \ (anchor '' Set.Icc 0 r)) ∩ Set.range anchor).Finite ∧
    ((Set.range branch \ (anchor '' Set.Icc 0 r)) ∩ Set.range anchor).ncard ≤
      (oldHalf ∩ Set.range anchor).ncard := by
  classical
  dsimp
  rw [regionalRawSurgeryBranch_range]
  have hsub : (((anchor '' Set.Icc 0 r) ∪
      (current '' (if right then Set.Icc s 1 else Set.Icc 0 s))) \
      (anchor '' Set.Icc 0 r)) ∩ Set.range anchor ⊆
      (current '' (if right then Set.Icc s 1 else Set.Icc 0 s)) ∩
        Set.range anchor := by
    rintro x ⟨⟨hx, hn⟩, ha⟩
    rcases hx with hx | hx
    · exact False.elim (hn hx)
    · exact ⟨hx, ha⟩
  have hhalf : (current '' (if right then Set.Icc s 1 else Set.Icc 0 s)) ∩
      Set.range anchor ⊆ Set.range current ∩ Set.range anchor := by
    rintro x ⟨⟨t, ht, rfl⟩, ha⟩
    exact ⟨Set.mem_range_self t, ha⟩
  exact ⟨hfinite.subset (hsub.trans hhalf),
    Set.ncard_le_ncard hsub (hfinite.subset hhalf)⟩

#print axioms regionalRawSurgeryBranch_range
#print axioms regionalRawSurgeryBranch_halves
#print axioms regionalRawSurgeryBranch_contact_budget

theorem regional_subpath_injective_of_embedded
    {S : Type} [TopologicalSpace S]
    {x y : S} (γ : Path x y) (hγ : Function.Injective γ)
    (u v : Interval) (huv : u ≠ v) :
    Function.Injective (γ.subpath u v) := by
  intro t w he
  have h := hγ he
  have hv := congrArg Subtype.val h
  dsimp [Icc.convexComb] at hv
  apply Subtype.ext
  have hne : (u : ℝ) ≠ (v : ℝ) := by
    intro huv'
    exact huv (Subtype.ext huv')
  have hmul : ((t : ℝ) - (w : ℝ)) * ((v : ℝ) - (u : ℝ)) = 0 := by
    nlinarith [hv]
  rcases mul_eq_zero.mp hmul with htw | huv'
  · exact sub_eq_zero.mp htw
  · exact False.elim (hne (sub_eq_zero.mp huv').symm)

#print axioms regional_subpath_injective_of_embedded

/-- Literal first-contact surgery gives two embedded paths in the original
    regional subspace. They generally represent new arc classes. -/
theorem regionalRawSurgeryBranch_embedded
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (anchor current : C(Interval, ↥F))
    (hanchor : Topology.IsEmbedding anchor)
    (hcurrent : Topology.IsEmbedding current)
    (r s : Interval) (hr : (0 : Interval) < r)
    (hs : s ∈ Set.Ioo (0 : Interval) 1)
    (hcontact : anchor r = current s)
    (hfirst : ∀ u : Interval, u < r → anchor u ∉ Set.range current)
    (right : Bool) :
    Topology.IsEmbedding
      (regionalRawSurgeryBranch anchor current r s hcontact right) := by
  let β : Path (anchor 0) (anchor 1) :=
    { toContinuousMap := anchor, source' := rfl, target' := rfl }
  let α : Path (current 0) (current 1) :=
    { toContinuousMap := current, source' := rfl, target' := rfl }
  let first : Path (anchor 0) (current s) := (β.subpath 0 r).cast rfl hcontact.symm
  let second : Path (current s) (if right then current 1 else current 0) :=
    if h : right = true then (α.subpath s 1).cast rfl (by simp [h, α])
    else (α.subpath s 0).cast rfl (by simp [Bool.eq_false_iff.mpr h, α])
  have hfirstInj : Function.Injective first := by
    change Function.Injective ((β.subpath 0 r).cast rfl hcontact.symm)
    rw [Path.cast_coe]
    exact regional_subpath_injective_of_embedded β hanchor.injective 0 r (ne_of_lt hr)
  have hsecondInj : Function.Injective second := by
    dsimp [second]
    split_ifs with h
    · rw [Path.cast_coe]
      exact regional_subpath_injective_of_embedded α hcurrent.injective s 1 (ne_of_lt hs.2)
    · rw [Path.cast_coe]
      exact regional_subpath_injective_of_embedded α hcurrent.injective s 0 (ne_of_gt hs.1)
  have hfirstRange : Set.range first = anchor '' Set.Icc 0 r := by
    change Set.range ((β.subpath 0 r).cast rfl hcontact.symm) = _
    rw [Path.cast_coe, Path.range_subpath_of_le _ _ _ (le_of_lt hr)]
    rfl
  have hsecondRange : Set.range second ⊆ Set.range current := by
    intro x hx
    dsimp [second] at hx
    split_ifs at hx with h
    · rw [Path.cast_coe, Path.range_subpath] at hx
      rcases hx with ⟨t,ht,rfl⟩
      exact ⟨t,rfl⟩
    · rw [Path.cast_coe, Path.range_subpath] at hx
      rcases hx with ⟨t,ht,rfl⟩
      exact ⟨t,rfl⟩
  have hinter : Set.range first ∩ Set.range second = {current s} := by
    ext x
    constructor
    · intro hx
      have h : x ∈ (anchor '' Set.Icc 0 r) ∩ Set.range current :=
        ⟨by rw [← hfirstRange]; exact hx.1, hsecondRange hx.2⟩
      rw [regional_first_contact_prefix_inter anchor current r s hcontact hfirst] at h
      exact h
    · intro hx
      have hxs : x = current s := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨1, first.target⟩,⟨0, second.source⟩⟩
  have hinj : Function.Injective (first.trans second) :=
    LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter
      first second hfirstInj hsecondInj hinter
  have hbranch : regionalRawSurgeryBranch anchor current r s hcontact right =
      first.trans second := by
    cases right <;> rfl
  rw [hbranch]
  exact ((first.trans second).continuous.isClosedEmbedding hinj).isEmbedding

#print axioms regionalRawSurgeryBranch_embedded

theorem regionalRawSurgeryBranch_frontier_only_endpoints
    {S : Type} [TopologicalSpace S] {F : Set S}
    (anchor current : C(Interval, ↥F))
    (hanchor : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (anchor t).val ∉ frontier F)
    (hcurrent : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (current t).val ∉ frontier F)
    (r s : Interval) (hr : r ∈ Set.Ioo (0 : Interval) 1)
    (hs : s ∈ Set.Ioo (0 : Interval) 1)
    (hcontact : anchor r = current s) (right : Bool) :
    ∀ x ∈ Set.range (regionalRawSurgeryBranch anchor current r s hcontact right),
      x.val ∈ frontier F →
      x = anchor 0 ∨ x = (if right then current 1 else current 0) := by
  intro x hx hxf
  rw [regionalRawSurgeryBranch_range] at hx
  rcases hx with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
  · by_cases ht0 : t = 0
    · exact Or.inl (by simp [ht0])
    · have hti : t ∈ Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_lt ht.2 hr.2⟩
      exact False.elim (hanchor t hti hxf)
  · cases right
    · by_cases ht0 : t = 0
      · exact Or.inr (by simp [ht0])
      · have hti : t ∈ Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_lt ht.2 hs.2⟩
        exact False.elim (hcurrent t hti hxf)
    · by_cases ht1 : t = 1
      · exact Or.inr (by simp [ht1])
      · have hti : t ∈ Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_ne t.property.2 ht1⟩
        exact False.elim (hcurrent t hti hxf)

#print axioms regionalRawSurgeryBranch_frontier_only_endpoints

/-- The embedded first-contact branches satisfy the same literal properness
    and distinguished-boundary endpoint conditions as the source arc type. -/
theorem regionalRawSurgeryBranch_proper
    {S : Type} [TopologicalSpace S] [T2Space S] {F B : Set S}
    (anchor current : C(Interval, ↥F))
    (hanchorEmb : Topology.IsEmbedding anchor)
    (hcurrentEmb : Topology.IsEmbedding current)
    (hanchorProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (anchor t).val ∉ frontier F)
    (hcurrentProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (current t).val ∉ frontier F)
    (hanchorZero : (anchor 0).val ∈ B)
    (hcurrentZero : (current 0).val ∈ B)
    (hcurrentOne : (current 1).val ∈ B)
    (r s : Interval) (hr : r ∈ Set.Ioo (0 : Interval) 1)
    (hs : s ∈ Set.Ioo (0 : Interval) 1)
    (hcontact : anchor r = current s)
    (hfirst : ∀ u : Interval, u < r → anchor u ∉ Set.range current)
    (right : Bool) :
    let branch := regionalRawSurgeryBranch anchor current r s hcontact right
    Topology.IsEmbedding branch ∧ (branch 0).val ∈ B ∧
      (branch 1).val ∈ B ∧
      ∀ t ∈ Set.Ioo (0 : Interval) 1, (branch t).val ∉ frontier F := by
  let branch := regionalRawSurgeryBranch anchor current r s hcontact right
  have hemb := regionalRawSurgeryBranch_embedded anchor current
    hanchorEmb hcurrentEmb r s hr.1 hs hcontact hfirst right
  refine ⟨hemb, ?_, ?_, ?_⟩
  · rw [branch.source]
    exact hanchorZero
  · rw [branch.target]
    cases right <;> assumption
  · intro t ht hbad
    have hends := regionalRawSurgeryBranch_frontier_only_endpoints
      anchor current hanchorProper hcurrentProper r s hr hs hcontact right
      (branch t) ⟨t,rfl⟩ hbad
    rcases hends with hleft | hright
    · have hzero : t = 0 := hemb.injective
        (hleft.trans branch.source.symm)
      exact (ne_of_gt ht.1) hzero
    · have hone : t = 1 := hemb.injective
        (hright.trans branch.target.symm)
      exact (ne_of_lt ht.2) hone

#print axioms regionalRawSurgeryBranch_proper

/-- The first anchor contact is chosen across all representatives of a
    simultaneous finite face, so the prefix avoids every represented arc. -/
theorem regional_finite_family_first_interior_contact
    {S : Type} [TopologicalSpace S] {F : Set S}
    {ι : Type} [Fintype ι]
    (anchor : C(Interval, ↥F)) (hanchor : Topology.IsEmbedding anchor)
    (a : ι → C(Interval, ↥F))
    (hfinite : ∀ i, (Set.range anchor ∩ Set.range (a i)).Finite)
    (hpositive : ∃ (u : Interval) (i : ι) (s : Interval),
      u ∈ Set.Ioo (0 : Interval) 1 ∧
      s ∈ Set.Ioo (0 : Interval) 1 ∧ anchor u = a i s) :
    ∃ (r : Interval) (k : ι) (s : Interval),
      r ∈ Set.Ioo (0 : Interval) 1 ∧
      s ∈ Set.Ioo (0 : Interval) 1 ∧ anchor r = a k s ∧
      ∀ (u : Interval) (i : ι) (v : Interval),
        u ∈ Set.Ioo (0 : Interval) 1 →
        v ∈ Set.Ioo (0 : Interval) 1 →
        u < r → anchor u ≠ a i v := by
  classical
  let C : Set ↥F := ⋃ i, Set.range (a i)
  have hC : (Set.range anchor ∩ C).Finite := by
    dsimp [C]
    rw [Set.inter_iUnion]
    exact Set.finite_iUnion hfinite
  let T : Set Interval :=
    {u | u ∈ Set.Ioo (0 : Interval) 1 ∧
      ∃ (i : ι) (s : Interval),
        s ∈ Set.Ioo (0 : Interval) 1 ∧ anchor u = a i s}
  have hTf : T.Finite := hC.of_injOn
    (show Set.MapsTo anchor T (Set.range anchor ∩ C) from by
      intro u hu
      obtain ⟨i,s,hs,he⟩ := hu.2
      exact ⟨Set.mem_range_self u, Set.mem_iUnion.mpr ⟨i,⟨s,he.symm⟩⟩⟩)
    (fun u _ v _ he => hanchor.injective he)
  have hTn : T.Nonempty := by
    obtain ⟨u,i,s,hu,hs,he⟩ := hpositive
    exact ⟨u,hu,⟨i,s,hs,he⟩⟩
  obtain ⟨r,hr,hmin⟩ := Set.exists_min_image T
    (fun u : Interval => u.val) hTf hTn
  obtain ⟨k,s,hs,he⟩ := hr.2
  refine ⟨r,k,s,hr.1,hs,he,?_⟩
  intro u i v hu hv hur hcontact
  have huT : u ∈ T := ⟨hu,i,v,hv,hcontact⟩
  exact (not_lt_of_ge (hmin u huT)) hur

#print axioms regional_finite_family_first_interior_contact

/-- With boundary endpoints separated from the anchor start, the selected
    first interior contact is the first contact with every arc range. -/
theorem regional_global_first_contact_prefix_clear
    {S : Type} [TopologicalSpace S] {F : Set S}
    {ι : Type} [Fintype ι]
    (anchor : C(Interval, ↥F)) (a : ι → C(Interval, ↥F))
    (hanchorProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (anchor t).val ∉ frontier F)
    (hends : ∀ i, (a i 0).val ∈ frontier F ∧
      (a i 1).val ∈ frontier F)
    (hstart : ∀ i, anchor 0 ∉ Set.range (a i))
    (r : Interval) (hr : r ∈ Set.Ioo (0 : Interval) 1)
    (hfirst : ∀ (u : Interval) (i : ι) (v : Interval),
      u ∈ Set.Ioo (0 : Interval) 1 →
      v ∈ Set.Ioo (0 : Interval) 1 →
      u < r → anchor u ≠ a i v) :
    ∀ (u : Interval) (i : ι), u < r →
      anchor u ∉ Set.range (a i) := by
  intro u i hur ⟨v,huv⟩
  have hu0 : u ≠ 0 := by
    intro he
    exact hstart i (he ▸ ⟨v,huv⟩)
  have hui : u ∈ Set.Ioo (0 : Interval) 1 :=
    ⟨lt_of_le_of_ne u.property.1 (Ne.symm hu0),
      lt_trans hur hr.2⟩
  by_cases hv0 : v = 0
  · have hf : (anchor u).val ∈ frontier F := by
      rw [← huv, hv0]
      exact (hends i).1
    exact hanchorProper u hui hf
  by_cases hv1 : v = 1
  · have hf : (anchor u).val ∈ frontier F := by
      rw [← huv, hv1]
      exact (hends i).2
    exact hanchorProper u hui hf
  have hvi : v ∈ Set.Ioo (0 : Interval) 1 :=
    ⟨lt_of_le_of_ne v.property.1 (Ne.symm hv0),
      lt_of_le_of_ne v.property.2 hv1⟩
  exact hfirst u i v hui hvi hur huv.symm

#print axioms regional_global_first_contact_prefix_clear

/-- A finite simultaneous family with finite anchor intersections admits a
    chosen literal proper surgery pair at its globally first contact. -/
theorem regional_finite_family_first_proper_surgery_pair
    {S : Type} [TopologicalSpace S] [T2Space S]
    {F B : Set S} {ι : Type} [Fintype ι]
    (anchor : C(Interval, ↥F)) (a : ι → C(Interval, ↥F))
    (hanchorEmb : Topology.IsEmbedding anchor)
    (haEmb : ∀ i, Topology.IsEmbedding (a i))
    (hanchorProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (anchor t).val ∉ frontier F)
    (haProper : ∀ (i : ι) (t : Interval),
      t ∈ Set.Ioo (0 : Interval) 1 → ((a i) t).val ∉ frontier F)
    (hBFront : B ⊆ frontier F)
    (hanchorZero : (anchor 0).val ∈ B)
    (haEnds : ∀ i, ((a i) 0).val ∈ B ∧ ((a i) 1).val ∈ B)
    (hstart : ∀ i, anchor 0 ∉ Set.range (a i))
    (hfinite : ∀ i, (Set.range anchor ∩ Set.range (a i)).Finite)
    (hpositive : ∃ (u : Interval) (i : ι) (s : Interval),
      u ∈ Set.Ioo (0 : Interval) 1 ∧
      s ∈ Set.Ioo (0 : Interval) 1 ∧ anchor u = a i s) :
    ∃ (r : Interval) (k : ι) (s : Interval),
      r ∈ Set.Ioo (0 : Interval) 1 ∧
      s ∈ Set.Ioo (0 : Interval) 1 ∧
      ∃ hcontact : anchor r = a k s,
      (∀ i u, u < r → anchor u ∉ Set.range (a i)) ∧
      ∀ right : Bool,
        let branch := regionalRawSurgeryBranch anchor (a k) r s
          hcontact right
        Topology.IsEmbedding branch ∧ (branch 0).val ∈ B ∧
          (branch 1).val ∈ B ∧
          (∀ t ∈ Set.Ioo (0 : Interval) 1,
            (branch t).val ∉ frontier F) ∧
          ((Set.range branch \ (anchor '' Set.Icc 0 r)) ∩
            Set.range anchor).ncard <
            ((a k '' (if right then Set.Icc s 1 else Set.Icc 0 s)) ∩
              Set.range anchor).ncard := by
  obtain ⟨r,k,s,hr,hs,hcontact,hfirst⟩ :=
    regional_finite_family_first_interior_contact anchor hanchorEmb a
      hfinite hpositive
  have hclear : ∀ (u : Interval) (i : ι), u < r →
      anchor u ∉ Set.range (a i) :=
    regional_global_first_contact_prefix_clear anchor a
      hanchorProper (fun i => ⟨hBFront (haEnds i).1,
        hBFront (haEnds i).2⟩) hstart r hr hfirst
  refine ⟨r,k,s,hr,hs,hcontact,fun i u hu => hclear u i hu,?_⟩
  intro right
  have hproper := regionalRawSurgeryBranch_proper anchor (a k)
    hanchorEmb (haEmb k) hanchorProper (haProper k)
    hanchorZero (haEnds k).1 (haEnds k).2
    r s hr hs hcontact (fun u hu => hclear u k hu) right
  refine ⟨hproper.1,hproper.2.1,hproper.2.2.1,hproper.2.2.2,?_⟩
  exact regionalRawSurgeryBranch_strict_contact_budget anchor (a k)
    r s hcontact right (by simpa [Set.inter_comm] using hfinite k)

#print axioms regional_finite_family_first_proper_surgery_pair

/-- The globally selected anchor prefix, including the surgery contact,
    has an open neighborhood disjoint from every other face representative. -/
theorem regional_first_contact_prefix_open_support_avoiding_face
    {S : Type} [TopologicalSpace S] [T2Space S]
    {F : Set S} {ι : Type} [Fintype ι]
    (anchor : C(Interval, ↥F)) (a : ι → C(Interval, ↥F))
    (hface : ∀ i j, i ≠ j →
      Disjoint (Set.range (a i)) (Set.range (a j)))
    (r s : Interval) (k : ι) (hcontact : anchor r = a k s)
    (hclear : ∀ i u, u < r → anchor u ∉ Set.range (a i)) :
    ∃ U : Set ↥F, IsOpen U ∧
      anchor '' Set.Icc 0 r ⊆ U ∧
      ∀ i, i ≠ k → Disjoint U (Set.range (a i)) := by
  classical
  let O : Set ↥F := ⋃ i : {i : ι // i ≠ k}, Set.range (a i.val)
  have hO : IsClosed O := isClosed_iUnion_of_finite
    (fun i => (isCompact_range (a i.val).continuous).isClosed)
  refine ⟨Oᶜ,hO.isOpen_compl,?_,?_⟩
  · rintro x ⟨u,hu,rfl⟩ hxO
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hxO
    rcases lt_or_eq_of_le hu.2 with hur | hur
    · exact hclear i.val u hur hi
    · have hp : a k s ∈ Set.range (a i.val) := by
        simpa [hur, hcontact] using hi
      exact Set.disjoint_left.mp (hface k i.val i.property.symm)
        (Set.mem_range_self s) hp
  · intro i hik
    apply Set.disjoint_left.mpr
    intro x hxU hxi
    exact hxU (Set.mem_iUnion.mpr ⟨⟨i,hik⟩,hxi⟩)

#print axioms regional_first_contact_prefix_open_support_avoiding_face

/-- Both class-changing raw branches are already compatible with every
    unselected member of the simultaneous face. -/
theorem regional_raw_branch_disjoint_remaining_face
    {S : Type} [TopologicalSpace S]
    {F : Set S} {ι : Type} [Fintype ι]
    (anchor : C(Interval, ↥F)) (a : ι → C(Interval, ↥F))
    (hface : ∀ i j, i ≠ j →
      Disjoint (Set.range (a i)) (Set.range (a j)))
    (r s : Interval) (k : ι) (hcontact : anchor r = a k s)
    (hclear : ∀ i u, u < r → anchor u ∉ Set.range (a i))
    (right : Bool) :
    ∀ i, i ≠ k →
      Disjoint
        (Set.range (regionalRawSurgeryBranch anchor (a k) r s hcontact right))
        (Set.range (a i)) := by
  intro i hik
  apply Set.disjoint_left.mpr
  intro x hx hi
  rw [regionalRawSurgeryBranch_range] at hx
  rcases hx with ⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩
  · rcases lt_or_eq_of_le hu.2 with hur | hur
    · exact hclear i u hur hi
    · have hp : a k s ∈ Set.range (a i) := by
        simpa [hur,hcontact] using hi
      exact Set.disjoint_left.mp (hface k i hik.symm)
        (Set.mem_range_self s) hp
  · exact Set.disjoint_left.mp (hface k i hik.symm)
      (Set.mem_range_self v) hi

#print axioms regional_raw_branch_disjoint_remaining_face

/-- The whole raw surgery branch has an open support neighborhood that avoids
    every unselected arc of the finite simultaneous face. -/
theorem regional_raw_branch_open_support_avoiding_face
    {S : Type} [TopologicalSpace S] [T2Space S]
    {F : Set S} {ι : Type} [Fintype ι]
    (anchor : C(Interval, ↥F)) (a : ι → C(Interval, ↥F))
    (hface : ∀ i j, i ≠ j →
      Disjoint (Set.range (a i)) (Set.range (a j)))
    (r s : Interval) (k : ι) (hcontact : anchor r = a k s)
    (hclear : ∀ i u, u < r → anchor u ∉ Set.range (a i))
    (right : Bool) :
    ∃ O : Set ↥F, IsOpen O ∧
      Set.range (regionalRawSurgeryBranch anchor (a k) r s hcontact right) ⊆ O ∧
      ∀ i, i ≠ k → Disjoint O (Set.range (a i)) := by
  classical
  let U : Set ↥F := ⋃ i : {i : ι // i ≠ k}, Set.range (a i.val)
  have hU : IsClosed U := isClosed_iUnion_of_finite
    (fun i => (isCompact_range (a i.val).continuous).isClosed)
  refine ⟨Uᶜ,hU.isOpen_compl,?_,?_⟩
  · intro x hx hxU
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hxU
    exact Set.disjoint_left.mp
      (regional_raw_branch_disjoint_remaining_face anchor a hface
        r s k hcontact hclear right i.val i.property) hx hi
  · intro i hik
    apply Set.disjoint_left.mpr
    intro x hxO hxi
    exact hxO (Set.mem_iUnion.mpr ⟨⟨i,hik⟩,hxi⟩)

#print axioms regional_raw_branch_open_support_avoiding_face
