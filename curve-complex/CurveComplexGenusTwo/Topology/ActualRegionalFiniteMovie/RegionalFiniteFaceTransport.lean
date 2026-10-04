import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib

open CurveComplex Set
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/- Transport of one simultaneous regional face by an actual ambient isotopy.
   `Arc` can be instantiated with the protected intrinsic essential-arc subtype. -/
theorem regional_finite_face_ambient_transport
    {S : Type} [TopologicalSpace S]
    (F B frontier : Set S) (Arc : Type)
    (underlying : Arc → C(Interval, ↥F))
    (H : AmbientIsotopy ↥F)
    (hB : ∀ t, (fun y => H.map (t, y)) '' {y : ↥F | y.val ∈ B} =
      {y : ↥F | y.val ∈ B})
    (hfrontier : ∀ t, (fun y => H.map (t, y)) ''
      {y : ↥F | y.val ∈ frontier} = {y : ↥F | y.val ∈ frontier}) :
    let rel : Arc → Arc → Prop := fun a b =>
      ∃ K : AmbientIsotopy ↥F,
        (∀ t, (fun y => K.map (t, y)) '' {y : ↥F | y.val ∈ B} =
          {y : ↥F | y.val ∈ B}) ∧
        (∀ t, (fun y => K.map (t, y)) ''
          {y : ↥F | y.val ∈ frontier} = {y : ↥F | y.val ∈ frontier}) ∧
        K.finalMap '' Set.range (underlying a) = Set.range (underlying b)
    ∀ (τ : Finset (Quot rel)) (a b : ↥τ → Arc),
      (∀ u, Quot.mk rel (a u) = u.val) →
      (∀ u w, u ≠ w →
        Disjoint (Set.range (underlying (a u))) (Set.range (underlying (a w)))) →
      (∀ u, H.finalMap '' Set.range (underlying (a u)) =
        Set.range (underlying (b u))) →
      (∀ u, Quot.mk rel (b u) = u.val) ∧
      (∀ u w, u ≠ w →
        Disjoint (Set.range (underlying (b u))) (Set.range (underlying (b w)))) := by
  classical
  intro rel τ a b hclass hdisjoint hmove
  have hinj : Function.Injective H.finalMap := by
    obtain ⟨e, he⟩ := H.homeomorphism_at 1
    intro x y hxy
    apply e.injective
    exact (he x).trans (hxy.trans (he y).symm)
  constructor
  · intro u
    exact (Quot.sound (show rel (a u) (b u) from
      ⟨H, hB, hfrontier, hmove u⟩)).symm.trans (hclass u)
  · intro u w huw
    apply Set.disjoint_left.mpr
    intro y hyu hyw
    rw [← hmove u] at hyu
    rw [← hmove w] at hyw
    obtain ⟨x, hx, hxy⟩ := hyu
    obtain ⟨z, hz, hzy⟩ := hyw
    have hxz : x = z := hinj (hxy.trans hzy.symm)
    exact Set.disjoint_left.mp (hdisjoint u w huw) hx (hxz ▸ hz)

#print axioms regional_finite_face_ambient_transport

/- A supported replacement at one vertex can be inserted into an actual
   simultaneous representative family when its ambient move fixes all others. -/
theorem regional_single_surgery_preserves_finite_face
    {S : Type} [TopologicalSpace S]
    (F B frontier : Set S) (Arc : Type)
    (underlying : Arc → C(Interval, ↥F)) :
    let rel : Arc → Arc → Prop := fun a b =>
      ∃ K : AmbientIsotopy ↥F,
        (∀ t, (fun y => K.map (t, y)) '' {y : ↥F | y.val ∈ B} =
          {y : ↥F | y.val ∈ B}) ∧
        (∀ t, (fun y => K.map (t, y)) ''
          {y : ↥F | y.val ∈ frontier} = {y : ↥F | y.val ∈ frontier}) ∧
        K.finalMap '' Set.range (underlying a) = Set.range (underlying b)
    ∀ (τ : Finset (Quot rel)) (a : ↥τ → Arc) (k : ↥τ) (r : Arc)
      (H : AmbientIsotopy ↥F),
      (∀ t, (fun y => H.map (t, y)) '' {y : ↥F | y.val ∈ B} =
        {y : ↥F | y.val ∈ B}) →
      (∀ t, (fun y => H.map (t, y)) ''
        {y : ↥F | y.val ∈ frontier} = {y : ↥F | y.val ∈ frontier}) →
      (∀ u, Quot.mk rel (a u) = u.val) →
      (∀ u w, u ≠ w →
        Disjoint (Set.range (underlying (a u))) (Set.range (underlying (a w)))) →
      (H.finalMap '' Set.range (underlying (a k)) = Set.range (underlying r)) →
      (∀ u, u ≠ k → ∀ y ∈ Set.range (underlying (a u)), H.finalMap y = y) →
      let b : ↥τ → Arc := fun u => if u = k then r else a u
      (∀ u, Quot.mk rel (b u) = u.val) ∧
      (∀ u w, u ≠ w →
        Disjoint (Set.range (underlying (b u))) (Set.range (underlying (b w)))) := by
  classical
  intro rel τ a k r H hB hfrontier hclass hdisjoint hmove hfix b
  apply regional_finite_face_ambient_transport F B frontier Arc underlying H
    hB hfrontier τ a b hclass hdisjoint
  intro u
  by_cases huk : u = k
  · subst u
    simpa [b] using hmove
  · have hfixed : H.finalMap '' Set.range (underlying (a u)) =
        Set.range (underlying (a u)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [hfix u huk z hz] using hz
      · intro hy
        exact ⟨y, hy, hfix u huk y hy⟩
    simpa [b, huk] using hfixed

#print axioms regional_single_surgery_preserves_finite_face

/- Exact intrinsic regional arc type from the protected source statement.
   The geometric crosscut producer supplies `r`, `H`, and `hmove`; its support
   avoidance supplies `hfix`. -/
theorem regional_intrinsic_single_surgery_preserves_face
    {S : Type} [TopologicalSpace S] (F B : Set S) :
    let RegionProperArc :=
      {a : C(Interval, ↥F) // Topology.IsEmbedding a ∧
        (a ⟨0, by norm_num⟩).val ∈ B ∧
        (a ⟨1, by norm_num⟩).val ∈ B ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval, ↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t, y)) '' {y | y.val ∈ B} =
          {y | y.val ∈ B}) ∧
        (∀ t, (fun y => H.map (t, y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    ∀ (τ : Finset (Quot intrinsicArcRel))
      (a : ↥τ → IntrinsicEssentialArc) (k : ↥τ)
      (r : IntrinsicEssentialArc) (H : AmbientIsotopy ↥F),
      (∀ t, (fun y => H.map (t, y)) '' {y | y.val ∈ B} =
        {y | y.val ∈ B}) →
      (∀ t, (fun y => H.map (t, y)) '' {y | y.val ∈ frontier F} =
        {y | y.val ∈ frontier F}) →
      (∀ u, Quot.mk intrinsicArcRel (a u) = u.val) →
      (∀ u w, u ≠ w →
        Disjoint (Set.range (a u).val.val) (Set.range (a w).val.val)) →
      (H.finalMap '' Set.range (a k).val.val = Set.range r.val.val) →
      (∀ u, u ≠ k → ∀ y ∈ Set.range (a u).val.val,
        H.finalMap y = y) →
      let b : ↥τ → IntrinsicEssentialArc := fun u =>
        if u = k then r else a u
      (∀ u, Quot.mk intrinsicArcRel (b u) = u.val) ∧
      (∀ u w, u ≠ w →
        Disjoint (Set.range (b u).val.val) (Set.range (b w).val.val)) := by
  classical
  intro RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel τ a k r H hB hfrontier hclass hdisjoint hmove hfix b
  exact regional_single_surgery_preserves_finite_face F B (frontier F)
    IntrinsicEssentialArc (fun z => z.val.val) τ a k r H hB hfrontier
    hclass hdisjoint hmove hfix

#print axioms regional_intrinsic_single_surgery_preserves_face

/- Contact-count bookkeeping for the literal old-subarc/new-subarc range
   equation returned by `actual_regional_proper_crosscut_arc_replacement`. -/
theorem regional_crosscut_replacement_strict_contact_decrease
    {S : Type} (old removed inserted anchor : Set S)
    (hremoved : removed ⊆ old)
    (hinserted : Disjoint inserted anchor)
    (hfinite : (old ∩ anchor).Finite)
    (p : S) (hp : p ∈ removed ∩ anchor) :
    ((((old \ removed) ∪ inserted) ∩ anchor).Finite) ∧
      (((old \ removed) ∪ inserted) ∩ anchor).ncard <
        (old ∩ anchor).ncard := by
  have hsub : ((old \ removed) ∪ inserted) ∩ anchor ⊆ old ∩ anchor := by
    rintro y ⟨hy, hya⟩
    rcases hy with hy | hy
    · exact ⟨hy.1, hya⟩
    · exact False.elim (Set.disjoint_left.mp hinserted hy hya)
  have hmissing : p ∉ ((old \ removed) ∪ inserted) ∩ anchor := by
    intro hnew
    rcases hnew.1 with hkeep | hnew
    · exact hkeep.2 hp.1
    · exact Set.disjoint_left.mp hinserted hnew hp.2
  refine ⟨hfinite.subset hsub, ?_⟩
  apply Set.ncard_lt_ncard _ hfinite
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  exact hmissing (heq.symm ▸ ⟨hremoved hp.1, hp.2⟩)

#print axioms regional_crosscut_replacement_strict_contact_decrease

/- First interior contact for two actual embedded arcs in the same region. -/
theorem regional_proper_arcs_first_interior_contact
    {S : Type} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval, ↥F))
    (ha : Topology.IsEmbedding a) (hb : Topology.IsEmbedding b)
    (hfinite : (Set.range a ∩ Set.range b).Finite)
    (hpositive : ∃ u v : Interval,
      u ∈ Set.Ioo (0 : Interval) 1 ∧
      v ∈ Set.Ioo (0 : Interval) 1 ∧ a u = b v) :
    ∃ r s : Interval,
      r ∈ Set.Ioo (0 : Interval) 1 ∧
      s ∈ Set.Ioo (0 : Interval) 1 ∧ a r = b s ∧
      ∀ u v : Interval,
        u ∈ Set.Ioo (0 : Interval) 1 →
        v ∈ Set.Ioo (0 : Interval) 1 →
        u < r → a u ≠ b v := by
  classical
  let T : Set (Interval × Interval) :=
    {z | z.1 ∈ Set.Ioo (0 : Interval) 1 ∧
      z.2 ∈ Set.Ioo (0 : Interval) 1 ∧ a z.1 = b z.2}
  have hTf : T.Finite := hfinite.of_injOn
    (show Set.MapsTo (fun z : Interval × Interval => a z.1) T
      (Set.range a ∩ Set.range b) from by
        intro z hz
        exact ⟨⟨z.1,rfl⟩,⟨z.2,hz.2.2.symm⟩⟩)
    (by
      intro z hz w hw he
      apply Prod.ext
      · exact ha.injective he
      · apply hb.injective
        exact hz.2.2.symm.trans (he.trans hw.2.2))
  have hTn : T.Nonempty := by
    obtain ⟨u,v,hu,hv,he⟩ := hpositive
    exact ⟨(u,v),hu,hv,he⟩
  obtain ⟨z,hz,hmin⟩ := Set.exists_min_image T
    (fun z : Interval × Interval => z.1.val) hTf hTn
  refine ⟨z.1,z.2,hz.1,hz.2.1,hz.2.2,?_⟩
  intro u v hu hv hur he
  have hmem : (u,v) ∈ T := ⟨hu,hv,he⟩
  exact (not_lt_of_ge (hmin (u,v) hmem)) hur

#print axioms regional_proper_arcs_first_interior_contact

/- Isolate one actual contact of an embedded regional proper arc. -/
theorem regional_proper_arc_isolated_contact_gap
    {S : Type} [TopologicalSpace S] {F : Set S}
    (a : C(Interval, ↥F)) (ha : Topology.IsEmbedding a)
    (C : Set ↥F) (hfinite : (Set.range a ∩ C).Finite)
    (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1)
    (hcontact : a t ∈ C) :
    ∃ l r : Interval, l < t ∧ t < r ∧
      ∀ s : Interval, s ∈ Set.Ioo l r → (a s ∈ C ↔ s = t) := by
  classical
  let K : Set Interval := {s | a s ∈ C}
  have hK : K.Finite := hfinite.of_injOn
    (show Set.MapsTo a K (Set.range a ∩ C) from by
      intro s hs
      exact ⟨Set.mem_range_self s, hs⟩)
    (fun x _ y _ he => ha.injective he)
  let A : Set Interval := K ∪ {0, 1}
  have hA : A.Finite := hK.union ((Set.finite_singleton (1 : Interval)).insert 0)
  obtain ⟨l, hl, hlmax⟩ := (hA.subset Set.inter_subset_left).isCompact.exists_isGreatest
    (show (A ∩ Set.Iio t).Nonempty from ⟨0, Or.inr (by simp), ht.1⟩)
  obtain ⟨r, hr, hrmin⟩ := (hA.subset Set.inter_subset_left).isCompact.exists_isLeast
    (show (A ∩ Set.Ioi t).Nonempty from ⟨1, Or.inr (by simp), ht.2⟩)
  refine ⟨l, r, hl.2, hr.2, ?_⟩
  intro s hs
  constructor
  · intro hsC
    have hsK : s ∈ K := hsC
    rcases lt_trichotomy s t with hst | he | hts
    · exact False.elim ((not_lt_of_ge (hlmax ⟨Or.inl hsK, hst⟩)) hs.1)
    · exact he
    · exact False.elim ((not_lt_of_ge (hrmin ⟨Or.inl hsK, hts⟩)) hs.2)
  · intro he
    exact he ▸ hcontact

#print axioms regional_proper_arc_isolated_contact_gap

/- The finite simultaneous representative family leaves room to localize a
   surgery square around any point on the selected arc. -/
theorem regional_finite_face_open_support_avoiding_others
    {S : Type} [TopologicalSpace S] [T2Space S] (F : Set S)
    {ι : Type} [Fintype ι] (a : ι → C(Interval, ↥F))
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint (Set.range (a i)) (Set.range (a j)))
    (k : ι) (p : ↥F) (hp : p ∈ Set.range (a k)) :
    ∃ U : Set ↥F, IsOpen U ∧ p ∈ U ∧
      ∀ i, i ≠ k → Disjoint U (Set.range (a i)) := by
  classical
  let O : Set ↥F := ⋃ i : {i : ι // i ≠ k}, Set.range (a i.val)
  have hO : IsClosed O := isClosed_iUnion_of_finite
    (fun i => (isCompact_range (a i.val).continuous).isClosed)
  refine ⟨Oᶜ, hO.isOpen_compl, ?_, ?_⟩
  · intro hpO
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpO
    exact Set.disjoint_left.mp (hdisjoint k i.val i.property.symm) hp hi
  · intro i hik
    apply Set.disjoint_left.mpr
    intro y hyU hyi
    exact hyU (Set.mem_iUnion.mpr ⟨⟨i,hik⟩,hyi⟩)

#print axioms regional_finite_face_open_support_avoiding_others

/- Square-supported version of the single-surgery face move. The support
   avoidance conclusion follows from disjointness with every other arc range. -/
theorem regional_supported_single_surgery_preserves_finite_face
    {S : Type} [TopologicalSpace S]
    (F B frontier : Set S) (Arc : Type)
    (underlying : Arc → C(Interval, ↥F)) :
    let rel : Arc → Arc → Prop := fun a b =>
      ∃ K : AmbientIsotopy ↥F,
        (∀ t, (fun y => K.map (t, y)) '' {y : ↥F | y.val ∈ B} =
          {y : ↥F | y.val ∈ B}) ∧
        (∀ t, (fun y => K.map (t, y)) ''
          {y : ↥F | y.val ∈ frontier} = {y : ↥F | y.val ∈ frontier}) ∧
        K.finalMap '' Set.range (underlying a) = Set.range (underlying b)
    ∀ (τ : Finset (Quot rel)) (a : ↥τ → Arc) (k : ↥τ) (r : Arc)
      (H : AmbientIsotopy ↥F) (U : Set ↥F),
      (∀ t, (fun y => H.map (t, y)) '' {y : ↥F | y.val ∈ B} =
        {y : ↥F | y.val ∈ B}) →
      (∀ t, (fun y => H.map (t, y)) ''
        {y : ↥F | y.val ∈ frontier} = {y : ↥F | y.val ∈ frontier}) →
      (∀ u, Quot.mk rel (a u) = u.val) →
      (∀ u w, u ≠ w →
        Disjoint (Set.range (underlying (a u))) (Set.range (underlying (a w)))) →
      (H.finalMap '' Set.range (underlying (a k)) = Set.range (underlying r)) →
      (∀ t y, y ∉ U → H.map (t, y) = y) →
      (∀ u, u ≠ k → Disjoint U (Set.range (underlying (a u)))) →
      let b : ↥τ → Arc := fun u => if u = k then r else a u
      (∀ u, Quot.mk rel (b u) = u.val) ∧
      (∀ u w, u ≠ w →
        Disjoint (Set.range (underlying (b u))) (Set.range (underlying (b w)))) := by
  classical
  intro rel τ a k r H U hB hfrontier hclass hdisjoint hmove houtside havoid b
  apply regional_single_surgery_preserves_finite_face F B frontier Arc
    underlying τ a k r H hB hfrontier hclass hdisjoint hmove
  intro u huk y hy
  have hyU : y ∉ U := by
    intro hmem
    exact Set.disjoint_left.mp (havoid u huk) hmem hy
  exact houtside 1 y hyU

#print axioms regional_supported_single_surgery_preserves_finite_face
