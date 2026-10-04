import HalfSignedGuidingChainRecord
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceStripGluing
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRelativeSupportNeighborhood

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
noncomputable local instance instDecidable_regionalHalfProfile187Supports (P : Prop) : Decidable P := Classical.propDecidable P

namespace HalfCollarScratch
open unitInterval

 private theorem glue_with_rows
    {X : Type} [TopologicalSpace X] [T2Space X]
    (L R : C(Interval × Interval,X)) (hL : IsEmbedding L) (hR : IsEmbedding R)
    (hseam : ∀ u, L (1,u) = R (0,u))
    (hmeet : range L ∩ range R = range (fun u => L (1,u))) :
    ∃ H : C(Interval × Interval,X), IsEmbedding H ∧
      range H = range L ∪ range R ∧
      (∀ u, H (0,u) = L (0,u)) ∧ (∀ u, H (1,u) = R (1,u)) ∧
      ∀ u, range (fun t => H (t,u)) =
        range (fun t => L (t,u)) ∪ range (fun t => R (t,u)) := by
  classical
  let rev : Interval × Interval → Interval × Interval := fun z => (unitInterval.symm z.1,z.2)
  have hrevc : Continuous rev := by dsimp [rev]; fun_prop
  have hrevi : Function.Injective rev := by
    intro z w he
    exact Prod.ext (unitInterval.symm_involutive.injective (congrArg Prod.fst he))
      (by simpa [rev] using congrArg Prod.snd he)
  let L' : C(Interval × Interval,X) := L.comp ⟨rev,hrevc⟩
  have hL' : IsEmbedding L' := ((hL.continuous.comp hrevc).isClosedEmbedding
    (hL.injective.comp hrevi)).isEmbedding
  have hL'range : range L' = range L := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact mem_range_self _
    · rintro ⟨z,rfl⟩
      refine ⟨rev z,?_⟩
      simp [L',rev]
  have hL'zero (u) : L' (0,u) = L (1,u) := by simp [L',rev]
  have hL'one (u) : L' (1,u) = L (0,u) := by simp [L',rev]
  have hmeet' : range L' ∩ range R = range (fun u => L' (0,u)) := by
    simp only [hL'range,hL'zero,hmeet]
  obtain ⟨f,hf,hfirst,hlast,hmid,hfrange,htrack⟩ :=
    source_glue_two_surface_strips L' R hL' hR
      (fun u => (hL'zero u).trans (hseam u)) hmeet'
  let H : C(Interval × Interval,X) := ⟨f,hf.continuous⟩
  have cross_width (s t u v : Interval) (he : L' (s,u) = R (t,v)) : u = v := by
    have hm : L' (s,u) ∈ range L' ∩ range R := ⟨mem_range_self _,⟨(t,v),he.symm⟩⟩
    rw [hmeet'] at hm
    obtain ⟨w,hw⟩ := hm
    have hu : w = u := congrArg Prod.snd (hL'.injective hw)
    have hv : w = v := congrArg Prod.snd (hR.injective
      ((hseam w).symm.trans ((hL'zero w).symm.trans (hw.trans he))))
    exact hu.symm.trans hv
  refine ⟨H,hf,by change range f = _; simpa only [hL'range] using hfrange,
    fun u => (hfirst u).trans (hL'one u),hlast,?_⟩
  intro u
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    obtain ⟨s,hs | hs⟩ := htrack (t,u)
    · exact Or.inl ⟨unitInterval.symm s,hs.symm⟩
    · exact Or.inr ⟨s,hs.symm⟩
  · intro hxRows
    have hx : x ∈ range f := by
      rw [hfrange,hL'range]
      rcases hxRows with ⟨t,rfl⟩ | ⟨t,rfl⟩
      · exact Or.inl (mem_range_self _)
      · exact Or.inr (mem_range_self _)
    obtain ⟨z,hz⟩ := hx
    have hzwidth : z.2 = u := by
      obtain ⟨s,hs | hs⟩ := htrack z
      · rcases hxRows with ⟨t,ht⟩ | ⟨t,ht⟩
        · have he : L' (s,z.2) = L' (unitInterval.symm t,u) := by
            simpa [L',rev] using hs.symm.trans (hz.trans ht.symm)
          exact congrArg Prod.snd (hL'.injective he)
        · exact cross_width s t z.2 u (hs.symm.trans (hz.trans ht.symm))
      · rcases hxRows with ⟨t,ht⟩ | ⟨t,ht⟩
        · have he : L' (unitInterval.symm t,u) = R (s,z.2) := by
            simpa [L',rev] using ht.trans (hz.symm.trans hs)
          exact (cross_width _ _ _ _ he).symm
        · exact congrArg Prod.snd (hR.injective (hs.symm.trans (hz.trans ht.symm)))
    refine ⟨z.1,?_⟩
    change f (z.1,u) = x
    rw [← hzwidth]
    exact hz

 private theorem finite_glue_with_rows
    {X : Type} [TopologicalSpace X] [T2Space X]
    (m : ℕ) (G : Fin (m+1) → C(Interval × Interval,X))
    (hG : ∀ i, IsEmbedding (G i))
    (hseam : ∀ i j, i.val+1 = j.val → ∀ u, G i (1,u) = G j (0,u))
    (hmeet : ∀ i j, i.val < j.val → range (G i) ∩ range (G j) =
      if i.val+1 = j.val then range (fun u => G i (1,u)) else ∅) :
    ∃ H : C(Interval × Interval,X), IsEmbedding H ∧
      range H = ⋃ i, range (G i) ∧
      (∀ u, H (0,u) = G 0 (0,u)) ∧ (∀ u, H (1,u) = G (Fin.last m) (1,u)) ∧
      ∀ u, range (fun t => H (t,u)) = ⋃ i, range (fun t => G i (t,u)) := by
  classical
  induction m with
  | zero =>
    refine ⟨G 0,hG 0,?_,fun _ => rfl,fun _ => rfl,?_⟩
    · have he : ∀ i : Fin (0+1), i = 0 := fun i => Fin.ext (by omega)
      simp only [he, iUnion_const]
    · intro u
      have he : ∀ i : Fin (0+1), i = 0 := fun i => Fin.ext (by omega)
      simp only [he, iUnion_const]
  | succ m ih =>
    let P : Fin (m+1) → C(Interval × Interval,X) := fun i => G i.castSucc
    have hP : ∀ i, IsEmbedding (P i) := fun i => hG _
    have hPs : ∀ i j : Fin (m+1), i.val+1 = j.val → ∀ u, P i (1,u) = P j (0,u) := by
      intro i j hij u
      exact hseam _ _ hij u
    have hPm : ∀ i j : Fin (m+1), i.val < j.val → range (P i) ∩ range (P j) =
        if i.val+1 = j.val then range (fun u => P i (1,u)) else ∅ := by
      intro i j hij
      exact hmeet _ _ hij
    obtain ⟨L,hL,hLrange,hL0,hL1,hLrows⟩ := ih P hP hPs hPm
    let R := G (Fin.last (m+1))
    have hR : IsEmbedding R := hG _
    have hLRs : ∀ u, L (1,u) = R (0,u) := by
      intro u
      rw [hL1]
      exact hseam _ _ (by simp) u
    have hLRm : range L ∩ range R = range (fun u => L (1,u)) := by
      ext x
      constructor
      · rintro ⟨hxL,hxR⟩
        rw [hLrange] at hxL
        obtain ⟨i,hi⟩ := mem_iUnion.mp hxL
        have hm : x ∈ range (P i) ∩ range R := ⟨hi,hxR⟩
        have he := hmeet i.castSucc (Fin.last (m+1)) (by simpa using i.isLt)
        change range (P i) ∩ range R = _ at he
        rw [he] at hm
        change x ∈ if i.val+1 = m+1 then range (fun u => P i (1,u)) else ∅ at hm
        by_cases hiLast : i.val+1 = m+1
        · rw [ite_eq_left hiLast] at hm
          obtain ⟨u,hu⟩ := hm
          have hiEq : i = Fin.last m := Fin.ext (by simp; omega)
          refine ⟨u,?_⟩
          change L (1,u) = x
          rw [hL1,← hiEq]
          exact hu
        · rw [ite_eq_right hiLast] at hm
          exact hm.elim
      · rintro ⟨u,rfl⟩
        refine ⟨mem_range_self _,?_⟩
        change L (1,u) ∈ range R
        rw [hLRs]
        exact mem_range_self _
    obtain ⟨H,hH,hHrange,hH0,hH1,hHrows⟩ := glue_with_rows L R hL hR hLRs hLRm
    refine ⟨H,hH,?_,fun u => (hH0 u).trans (hL0 u),hH1,?_⟩
    · rw [hHrange,hLrange]
      ext x
      constructor
      · rintro (hx | hx)
        · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨i.castSucc,hi⟩
        · exact mem_iUnion.mpr ⟨Fin.last (m+1),hx⟩
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        obtain ⟨j,rfl⟩ | rfl := i.eq_castSucc_or_eq_last
        · exact Or.inl (mem_iUnion.mpr ⟨j,hi⟩)
        · exact Or.inr hi
    · intro u
      rw [hHrows,hLrows]
      ext x
      constructor
      · rintro (hx | hx)
        · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
          exact mem_iUnion.mpr ⟨i.castSucc,hi⟩
        · exact mem_iUnion.mpr ⟨Fin.last (m+1),hx⟩
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        obtain ⟨j,rfl⟩ | rfl := i.eq_castSucc_or_eq_last
        · exact Or.inl (mem_iUnion.mpr ⟨j,hi⟩)
        · exact Or.inr hi

 private theorem affine_range (s t : Interval) :
    range (CurveComplex.BranchedDoubleCover.intervalAffine s t) = uIcc s t := by
  have hcont : Continuous (CurveComplex.BranchedDoubleCover.intervalAffine s t) :=
    (CurveComplex.BranchedDoubleCover.intervalSegment s t).continuous
  have hs : s ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine s t) :=
    ⟨0,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
  have ht : t ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine s t) :=
    ⟨1,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
  apply Subset.antisymm
  · rintro x ⟨q,rfl⟩
    rcases le_total s t with hst | hts
    · simpa [uIcc_of_le hst] using CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hst q
    · have he : CurveComplex.BranchedDoubleCover.intervalAffine s t q =
          CurveComplex.BranchedDoubleCover.intervalAffine t s (unitInterval.symm q) := by
        apply Subtype.ext
        simp [CurveComplex.BranchedDoubleCover.intervalAffine,unitInterval.symm]
        ring
      rw [he,uIcc_of_ge hts]
      exact CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hts _
  · exact (isPreconnected_range hcont).ordConnected.uIcc_subset hs ht

 private theorem normalize_bottom
    {X : Type} [TopologicalSpace X] [T2Space X]
    (H₀ : C(Interval × Interval,X)) (hH₀ : IsEmbedding H₀)
    (b : C(Interval,X)) (hb : IsEmbedding b)
    (hbottom : range (fun t => H₀ (t,0)) ⊆ range b)
    (hzero : H₀ (0,0) = b 0) (hone : H₀ (1,0) = b 1) :
    ∃ H : C(Interval × Interval,X), IsEmbedding H ∧
      range H = range H₀ ∧ (∀ t, H (t,0) = b t) ∧
      (∀ u, H (0,u) = H₀ (0,u)) ∧ (∀ u, H (1,u) = H₀ (1,u)) ∧
      ∀ u, range (fun t => H (t,u)) = range (fun t => H₀ (t,u)) := by
  let c : C(Interval,X) := H₀.comp ⟨fun t => (t,0),continuous_id.prodMk continuous_const⟩
  have hc : IsEmbedding c := hH₀.comp (isEmbedding_prodMkLeft (0 : Interval))
  let p : C(Interval,Interval) :=
    ⟨fun t => hb.toHomeomorph.symm ⟨c t,hbottom (mem_range_self t)⟩,
      hb.toHomeomorph.symm.continuous.comp (c.continuous.subtype_mk _)⟩
  have hp (t) : b (p t) = c t :=
    congrArg Subtype.val (hb.toHomeomorph.apply_symm_apply ⟨c t,hbottom (mem_range_self t)⟩)
  have hp0 : p 0 = 0 := hb.injective ((hp 0).trans hzero)
  have hp1 : p 1 = 1 := hb.injective ((hp 1).trans hone)
  have hprange : range p = univ := by
    apply eq_univ_of_univ_subset
    rw [unitInterval.univ_eq_Icc]
    exact (isPreconnected_range p.continuous).Icc_subset ⟨0,hp0⟩ ⟨1,hp1⟩
  have hcrange : range c = range b := by
    have he : (c : Interval → X) = b ∘ p := funext (fun t => (hp t).symm)
    rw [he,range_comp,hprange,image_univ]
  let g : Interval → range c := fun t => ⟨b t,by rw [hcrange]; exact mem_range_self t⟩
  have hgc : Continuous g := b.continuous.subtype_mk _
  let k : Interval → Interval := hc.toHomeomorph.symm ∘ g
  have hkc : Continuous k := hc.toHomeomorph.symm.continuous.comp hgc
  have hk (t) : c (k t) = b t := congrArg Subtype.val (hc.toHomeomorph.apply_symm_apply (g t))
  have hki : Function.Injective k := by
    intro t u he
    apply hb.injective
    rw [← hk t,← hk u,he]
  have hk0 : k 0 = 0 := hc.injective ((hk 0).trans hzero.symm)
  have hk1 : k 1 = 1 := hc.injective ((hk 1).trans hone.symm)
  have hkrange : range k = univ := by
    apply eq_univ_of_univ_subset
    rw [unitInterval.univ_eq_Icc]
    exact (isPreconnected_range hkc).Icc_subset ⟨0,hk0⟩ ⟨1,hk1⟩
  let f : Interval × Interval → Interval × Interval := fun z => (k z.1,z.2)
  have hfc : Continuous f := (hkc.comp continuous_fst).prodMk continuous_snd
  have hfi : Function.Injective f := by
    intro z w he
    exact Prod.ext (hki (congrArg Prod.fst he)) (by simpa [f] using congrArg Prod.snd he)
  have hfs : Function.Surjective f := by
    intro z
    have hz : z.1 ∈ range k := hkrange.symm ▸ mem_univ _
    obtain ⟨t,ht⟩ := hz
    exact ⟨(t,z.2),Prod.ext ht rfl⟩
  let H := H₀.comp ⟨f,hfc⟩
  refine ⟨H,hH₀.comp (hfc.isClosedEmbedding hfi).isEmbedding,?_,hk,?_,?_,?_⟩
  · change range (H₀ ∘ f) = range H₀
    rw [range_comp,hfs.range_eq,image_univ]
  · intro u; change H₀ (k 0,u) = H₀ (0,u); rw [hk0]
  · intro u; change H₀ (k 1,u) = H₀ (1,u); rw [hk1]
  · intro u
    change range ((fun t => H₀ (t,u)) ∘ k) = _
    rw [range_comp,hkrange,image_univ]

end HalfCollarScratch

set_option maxHeartbeats 1600000 in
theorem regional_half_guiding_cells_form_embedded_collar
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ (ι : Type) [Fintype ι] (r : ι → IntrinsicEssentialArc)
      (α : IntrinsicEssentialArc),
      FamilyInvariant (fun i => (r i).val.val) α.val.val →
      (∀ i j : Option ι, i ≠ j →
        RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
          (augmented (fun i => (r i).val.val) α.val.val i)
          (augmented (fun i => (r i).val.val) α.val.val j)) →
      ∀ v w : ι, v ≠ w →
      ∀ d : PairedHalfBigonDisk F {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F} (r v).val.val (r w).val.val,
      ∀ V : Set ↥F, IsOpen V → range d.disk ⊆ V →
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ boundaryCircle}) →
        let C₀ : Set ↥F := {d.first 1}
        let removed := fun j : ι => ((range d.first \ C₀) ∩ range (r j).val.val).ncard
        let guiding := fun j : ι => ((range d.second \ C₀) ∩ range (r j).val.val).ncard
        let offset := fun j : ι =>
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
            (C₀ ∩ range (r j).val.val).ncard
        (∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j else 0) ≤
          (∑ j : ι, if j ≠ v ∧ j ≠ w then removed j else 0) →
        ∀ fan : FiniteFanCarrier F
          (augmented (fun i => (r i).val.val) α.val.val) {some v,some w}
          (range d.first ∪ range d.second) V (range d.disk)
          (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v),
        ∀ gap : BoundaryEndpointGap {y : ↥F | y.val ∈ boundaryCircle} V
          (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v) d.boundarySide,
        ∀ chain : RegionalHalfSignedGuidingChain F {y | y.val ∈ boundaryCircle}
          {y : ↥F | y.val ∈ frontier F}
          (fun i => (r i).val.val) α.val.val v w d V fan gap,
        ∀ ρ : Ioo (0 : ℝ) chain.bound,
        let guideCarrier : Set ↥F := ⋃ i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val},
          regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i)
        let cornerCarrier : Set ↥F := chartPull F chain.cornerFan.chart
          (regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ))
        let orientedA : Interval → ↥F := fun t => (r v).val.val (chain.clock t)
        let z : Interval := chain.cuts ρ ⟨chain.n,by omega⟩
        ∃ H : C(Interval × Interval,↥F),
          IsEmbedding H ∧
          range H = guideCarrier ∪ cornerCarrier ∧
          range H ⊆ V ∧
          (∀ t, H (t,0) = d.second t) ∧
          range (fun t => H (t,1)) = chain.q ρ '' Icc (0 : Interval) z ∧
          (∀ u, H (0,u) = chain.boundaryLine ⟨ρ.val*u.val,by
            constructor
            · nlinarith [ρ.property.1,u.property.1]
            · nlinarith [ρ.property.2,chain.bound_lt_one,u.property.1,u.property.2]⟩) ∧
          (∀ u, (H (1,u)).val ∈ chain.cornerFan.chart.source ∧
            chain.cornerFan.chart (H (1,u)).val = Plane.mk (-chain.cornerDelta*u.val) 0) ∧
          range H ∩ range d.disk = range d.second ∧
          range H ∩ {y : ↥F | y.val ∈ frontier F} = range (fun u => H (0,u)) ∧
          H (0,1) = chain.beta ρ ∧ H (1,1) = orientedA chain.cut ∧
          range (fun u => H (1,u)) =
            orientedA '' Icc (chain.clock.symm d.aFinish) chain.cut := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset hcheap fan gap chain ρ
    guideCarrier cornerCarrier orientedA z
  let : ClosedSurface S := Classical.choice hS.2.1
  have guide_slab_in_V (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) :
      regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i) ⊆ V := by
    rintro y ⟨z, ⟨t, ht, _, _⟩, rfl⟩
    apply chain.guide_full_window_fibers z.1
    rw [ht]
    exact chain.guideCoordinates_window ρ i t
  have old_negative_in_V :
      regionalHalfOldNegativeBand F chain.oldStrip chain.clock chain.cut
        chain.oldNegativeWidth ⊆ V := by
    rintro y ⟨z, hz, rfl⟩
    exact chain.oldStrip_full_active_fibers z.1 (chain.activeWindow_prefix hz.1) z.2
  have corner_hull_in_V :
      chartPull F chain.cornerFan.chart
        (regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)) ⊆ V := by
    intro y hy
    obtain ⟨z, hz, he⟩ := (chain.cornerFan.source_closure (subset_closure hy.1)).1
    exact Subtype.ext he ▸ hz
  have ruled_guide_cells
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) :
      ∃ G : C(Interval × Interval, ↥F), IsEmbedding G ∧
        range G = regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i) ∧
        (∀ t, G (t,0) = (r w).val.val (chain.guideCoordinates ρ i t).1) ∧
        (∀ t, G (t,1) = chain.piece ρ i.val t) ∧ range G ⊆ V ∧
        (∀ t u, ∃ z : Interval × Icc (-1:ℝ) 1,
          z.1 = (chain.guideCoordinates ρ i t).1 ∧
          z.2.val = u.val * (chain.guideCoordinates ρ i t).2.val ∧ G (t,u) = chain.guideStrip z) := by
    let c := chain.guideCoordinates ρ i
    have hcpos (t : Interval) : 0 < (c t).2.val := (chain.guideCoordinates_width ρ i t).1
    have hcle (t : Interval) : (c t).2.val ≤ 1 := (c t).2.property.2
    let f (z : Interval × Interval) : Interval × Icc (-1 : ℝ) 1 :=
      ((c z.1).1, ⟨z.2.val * (c z.1).2.val, by
        constructor
        · have := mul_nonneg z.2.property.1 (hcpos z.1).le
          linarith
        · exact (mul_le_of_le_one_left (hcpos z.1).le z.2.property.2).trans (hcle z.1)⟩)
    have hfc : Continuous f := by
      dsimp [f]
      fun_prop
    have hfi : Function.Injective f := by
      intro z z' he
      have hfirst := congrArg Prod.fst he
      change (c z.1).1 = (c z'.1).1 at hfirst
      have ht : z.1 = z'.1 := (chain.guideCoordinates_order ρ i).injective
        (congrArg chain.guideClock.symm hfirst)
      have hu := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => p.2.val) he
      change z.2.val * (c z.1).2.val = z'.2.val * (c z'.1).2.val at hu
      rw [ht] at hu
      exact Prod.ext ht (Subtype.ext ((mul_right_cancel₀ (ne_of_gt (hcpos z'.1))) hu))
    let G : C(Interval × Interval, ↥F) := chain.guideStrip.comp ⟨f,hfc⟩
    have hG : IsEmbedding G := chain.guideStrip_embedded.comp
      (hfc.isClosedEmbedding hfi).isEmbedding
    have hGr : range G = regionalHalfGuideSlab F chain.guideStrip c := by
      ext y
      constructor
      · rintro ⟨⟨t,u⟩,rfl⟩
        refine ⟨f (t,u), ⟨t,rfl,?_,?_⟩,rfl⟩
        · exact mul_nonneg u.property.1 (hcpos t).le
        · exact mul_le_of_le_one_left (hcpos t).le u.property.2
      · rintro ⟨z,⟨t,ht,hl,hu⟩,rfl⟩
        let u : Interval := ⟨z.2.val / (c t).2.val,
          ⟨div_nonneg hl (hcpos t).le,(div_le_one (hcpos t)).mpr hu⟩⟩
        refine ⟨(t,u),?_⟩
        change chain.guideStrip (f (t,u)) = chain.guideStrip z
        apply congrArg chain.guideStrip
        apply Prod.ext
        · exact ht.symm
        · apply Subtype.ext
          exact div_mul_cancel₀ z.2.val (ne_of_gt (hcpos t))
    refine ⟨G,hG,hGr,?_,?_,?_,?_⟩
    · intro t
      change chain.guideStrip (f (t,0)) = _
      have hf0 : f (t,0) = ((c t).1,⟨0,by norm_num⟩) := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [f]
      rw [hf0,chain.guideStrip_center]
    · intro t
      change chain.guideStrip (f (t,1)) = _
      have hf1 : f (t,1) = c t := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          simp [f]
      rw [hf1]
      exact (chain.guideCoordinates_factor ρ i t).symm
    · rw [hGr]
      exact guide_slab_in_V i
    · intro t u
      exact ⟨f (t,u),rfl,rfl,rfl⟩
  have guide_coordinate_seam
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 = j.val.val) :
      chain.guideCoordinates ρ i 1 = chain.guideCoordinates ρ j 0 := by
    apply chain.guideStrip_embedded.injective
    rw [← chain.guideCoordinates_factor,← chain.guideCoordinates_factor,
      chain.piece_one,chain.piece_zero]
    exact congrArg (chain.port ρ) (Fin.ext hij)
  let P : C(Interval × Interval, Plane) :=
    ⟨fun z => (1-z.1.val) • ((1-z.2.val) • chain.cornerEntry +
        z.2.val • Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1)) +
      z.1.val • (z.2.val • Plane.mk (-chain.cornerDelta) 0), by fun_prop⟩
  have hP0 (t u : Interval) :
      P (t,u) 0 = (1-t.val)*(chain.cornerEntry 0-u.val*chain.cornerEpsilon ρ) -
        t.val*u.val*chain.cornerDelta := by
    simp [P]
    ring
  have hP1 (t u : Interval) : P (t,u) 1 = (1-t.val)*chain.cornerEntry 1 := by
    simp [P]
    ring
  have hP_hull (z : Interval × Interval) :
      P z ∈ regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ) := by
    let K := regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)
    have hc : Convex ℝ K := convex_convexHull ℝ _
    have hzero : (0 : Plane) ∈ K := subset_convexHull ℝ _ (by simp)
    have hA : Plane.mk (-chain.cornerDelta) 0 ∈ K := subset_convexHull ℝ _ (by simp)
    have hE : chain.cornerEntry ∈ K := subset_convexHull ℝ _ (by simp)
    have hD : Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1) ∈ K :=
      subset_convexHull ℝ _ (by simp)
    have hl := hc hE hD (sub_nonneg.mpr z.2.property.2) z.2.property.1 (by ring : 1-z.2.val+z.2.val=1)
    have hr := hc hzero hA (sub_nonneg.mpr z.2.property.2) z.2.property.1 (by ring : 1-z.2.val+z.2.val=1)
    simpa [P] using hc hl hr (sub_nonneg.mpr z.1.property.2) z.1.property.1
      (by ring : 1-z.1.val+z.1.val=1)
  have hP_injective : Function.Injective P := by
    rintro ⟨t,u⟩ ⟨t',u'⟩ he
    have hh := congrArg (fun z : Plane => z 1) he
    rw [hP1,hP1] at hh
    have htt : t = t' := Subtype.ext (by
      have hh' := mul_right_cancel₀ chain.cornerEntry_nonzero_height hh
      linarith)
    subst t'
    have hh0 := congrArg (fun z : Plane => z 0) he
    rw [hP0,hP0] at hh0
    have hwidth : 0 < (1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta := by
      rcases eq_or_lt_of_le t.property.1 with ht | ht
      · rw [← ht]
        simpa using chain.cornerEpsilon_pos ρ
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr t.property.2) (chain.cornerEpsilon_pos ρ).le)
          (mul_pos ht chain.cornerDelta_pos)
    have huu : u.val*((1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta) =
        u'.val*((1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta) := by
      nlinarith [hh0]
    exact Prod.ext rfl (Subtype.ext (mul_right_cancel₀ (ne_of_gt hwidth) huu))
  have hPt (z : Interval × Interval) : P z ∈ chain.cornerFan.chart.target :=
    chain.cornerFan.disk_in_target (Metric.ball_subset_closedBall (chain.cornerHull_open_unit ρ (hP_hull z)))
  have hPc_source (z : Interval × Interval) :
      chain.cornerFan.chart.symm (P z) ∈ chain.cornerFan.chart.source :=
    chain.cornerFan.chart.map_target (hPt z)
  let cornerCell : C(Interval × Interval, ↥F) :=
    ⟨fun z => ⟨chain.cornerFan.chart.symm (P z),
      interior_subset ((chain.cornerFan.source_closure (subset_closure (hPc_source z))).2)⟩,
      (chain.cornerFan.chart.continuousOn_symm.comp_continuous P.continuous hPt).subtype_mk _⟩
  have corner_cell_embedded : IsEmbedding cornerCell := by
    refine (cornerCell.continuous.isClosedEmbedding ?_).isEmbedding
    intro z z' he
    apply hP_injective
    have hv := congrArg (fun y : ↥F => chain.cornerFan.chart y.val) he
    change chain.cornerFan.chart (chain.cornerFan.chart.symm (P z)) =
      chain.cornerFan.chart (chain.cornerFan.chart.symm (P z')) at hv
    simpa only [chain.cornerFan.chart.right_inv (hPt z),chain.cornerFan.chart.right_inv (hPt z')] using hv
  have corner_cell_carrier : range cornerCell ⊆
      chartPull F chain.cornerFan.chart
        (regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)) := by
    rintro y ⟨z,rfl⟩
    refine ⟨hPc_source z,?_⟩
    change chain.cornerFan.chart (chain.cornerFan.chart.symm (P z)) ∈ _
    rw [chain.cornerFan.chart.right_inv (hPt z)]
    exact hP_hull z
  have corner_cell_in_V : range cornerCell ⊆ V := corner_cell_carrier.trans corner_hull_in_V
  have corner_cell_upper (t : Interval) : cornerCell (t,1) = chain.piece ρ chain.cornerIndex t := by
    apply Subtype.ext
    change chain.cornerFan.chart.symm (P (t,1)) = _
    rw [(chain.corner_formula ρ t).2]
    apply congrArg chain.cornerFan.chart.symm
    ext j
    fin_cases j
    · change P (t,1) 0 = -chain.cornerDelta +
        (1-t.val)*(chain.cornerEntry 0-chain.cornerEpsilon ρ+chain.cornerDelta)
      rw [hP0]
      norm_num
      ring
    · change P (t,1) 1 = chain.cornerEntry 1*(1-t.val)
      rw [hP1]
      ring
  have corner_hull_covered :
      regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ) ⊆ range P := by
    let scoord : Plane →ₗ[ℝ] ℝ := {
      toFun := fun z => z 1 / chain.cornerEntry 1
      map_add' := by intro a b; simp; ring
      map_smul' := by intro a b; simp; ring }
    let lcoord : Plane →ₗ[ℝ] ℝ := {
      toFun := fun z => scoord z * chain.cornerEntry 0 - z 0
      map_add' := by intro a b; simp; ring
      map_smul' := by intro a b; simp; ring }
    let ucoord : Plane →ₗ[ℝ] ℝ := lcoord - (chain.cornerEpsilon ρ-chain.cornerDelta) • scoord
    let K : Set Plane :=
      (scoord ⁻¹' Icc (0:ℝ) 1) ∩ (lcoord ⁻¹' Ici (0:ℝ)) ∩
        (ucoord ⁻¹' Iic chain.cornerDelta)
    have hK : Convex ℝ K := ((convex_Icc (0:ℝ) 1).linear_preimage scoord).inter
      ((convex_Ici (0:ℝ)).linear_preimage lcoord) |>.inter
      ((convex_Iic chain.cornerDelta).linear_preimage ucoord)
    have hvertices : ({0,Plane.mk (-chain.cornerDelta) 0,chain.cornerEntry,
        Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1)} : Set Plane) ⊆ K := by
      intro z hz
      simp only [mem_insert_iff,mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl <;>
        simp [K,scoord,lcoord,ucoord,chain.cornerEntry_nonzero_height] <;>
        nlinarith [chain.cornerDelta_pos,chain.cornerEpsilon_pos ρ]
    have hsub : regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ) ⊆ K :=
      convexHull_min hvertices hK
    intro z hz
    obtain ⟨⟨hs,hl⟩,hu⟩ := hsub hz
    change 0 ≤ scoord z ∧ scoord z ≤ 1 at hs
    change 0 ≤ lcoord z at hl
    change ucoord z ≤ chain.cornerDelta at hu
    let t : Interval := ⟨1-scoord z,⟨by linarith [hs.2],by linarith [hs.1]⟩⟩
    have hwpos : 0 < (1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta := by
      rcases eq_or_lt_of_le t.property.1 with ht | ht
      · rw [← ht]
        simpa using chain.cornerEpsilon_pos ρ
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr t.property.2) (chain.cornerEpsilon_pos ρ).le)
          (mul_pos ht chain.cornerDelta_pos)
    have hlw : lcoord z ≤ (1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta := by
      change lcoord z - (chain.cornerEpsilon ρ-chain.cornerDelta)*scoord z ≤ chain.cornerDelta at hu
      dsimp [t]
      nlinarith
    let u : Interval := ⟨lcoord z / ((1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta),
      ⟨div_nonneg hl hwpos.le,(div_le_one hwpos).mpr hlw⟩⟩
    refine ⟨(t,u),?_⟩
    have hueq : u.val * ((1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta) = lcoord z := by
      exact div_mul_cancel₀ _ (ne_of_gt hwpos)
    ext j
    fin_cases j
    · change P (t,u) 0 = z 0
      rw [hP0]
      change u.val * ((1-t.val)*chain.cornerEpsilon ρ+t.val*chain.cornerDelta) =
        scoord z * chain.cornerEntry 0 - z 0 at hueq
      have ht : t.val = 1-scoord z := rfl
      nlinarith [hueq]
    · change P (t,u) 1 = z 1
      rw [hP1]
      dsimp [t,scoord]
      convert div_mul_cancel₀ (z 1) chain.cornerEntry_nonzero_height using 1 <;> ring
  have corner_cell_range : range cornerCell =
      chartPull F chain.cornerFan.chart
        (regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)) := by
    apply Subset.antisymm corner_cell_carrier
    intro y hy
    obtain ⟨z,hz⟩ := corner_hull_covered hy.2
    refine ⟨z,?_⟩
    apply Subtype.ext
    change chain.cornerFan.chart.symm (P z) = y.val
    rw [hz]
    exact chain.cornerFan.chart.left_inv hy.1
  have guide_coordinate_bounds
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) (t : Interval) :
      chain.guidePortTime i.val.castSucc ≤ chain.guideClock.symm (chain.guideCoordinates ρ i t).1 ∧
      chain.guideClock.symm (chain.guideCoordinates ρ i t).1 ≤ chain.guidePortTime i.val.succ := by
    constructor
    · have h := (chain.guideCoordinates_order ρ i).monotone (show (0 : Interval) ≤ t from t.property.1)
      simpa only [chain.guideCoordinates_zero, chain.guideClock.symm_apply_apply] using h
    · have h := (chain.guideCoordinates_order ρ i).monotone (show t ≤ (1 : Interval) from t.property.2)
      simpa only [chain.guideCoordinates_one, chain.guideClock.symm_apply_apply] using h
  have guide_slabs_adjacent_inter
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 = j.val.val) :
      regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i) ∩
        regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ j) =
      chain.guideStrip '' {p | p.1 = (chain.guideCoordinates ρ i 1).1 ∧
        0 ≤ p.2.val ∧ p.2.val ≤ (chain.guideCoordinates ρ i 1).2.val} := by
    have hseam := guide_coordinate_seam i j hij
    have hp : i.val.succ = j.val.castSucc := Fin.ext hij
    ext y
    constructor
    · rintro ⟨⟨p,⟨t,ht,hl,hu⟩,hy⟩,⟨p',⟨t',ht',hl',hu'⟩,hy'⟩⟩
      have hpp : p = p' := chain.guideStrip_embedded.injective (hy.trans hy'.symm)
      have hcc : (chain.guideCoordinates ρ i t).1 = (chain.guideCoordinates ρ j t').1 :=
        ht.symm.trans ((congrArg Prod.fst hpp).trans ht')
      have hi := (guide_coordinate_bounds i t).2
      have hj := (guide_coordinate_bounds j t').1
      rw [hp] at hi
      rw [← hcc] at hj
      have htend : t = 1 := (chain.guideCoordinates_order ρ i).injective (by
        rw [chain.guideCoordinates_one, chain.guideClock.symm_apply_apply, hp]
        exact le_antisymm hi hj)
      subst t
      exact ⟨p,⟨ht,hl,hu⟩,hy⟩
    · rintro ⟨p,⟨ht,hl,hu⟩,hy⟩
      refine ⟨⟨p,⟨1,ht,hl,hu⟩,hy⟩,⟨p,⟨0,?_,hl,?_⟩,hy⟩⟩
      · exact ht.trans (congrArg Prod.fst hseam)
      · simpa only [hseam] using hu
  have guide_slabs_nonadjacent_disjoint
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 < j.val.val) :
      Disjoint (regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i))
        (regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ j)) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨p,⟨t,ht,_,_⟩,hy⟩ ⟨p',⟨t',ht',_,_⟩,hy'⟩
    have hpp : p = p' := chain.guideStrip_embedded.injective (hy.trans hy'.symm)
    have hcc : (chain.guideCoordinates ρ i t).1 = (chain.guideCoordinates ρ j t').1 :=
      ht.symm.trans ((congrArg Prod.fst hpp).trans ht')
    have hi := (guide_coordinate_bounds i t).2
    have hj := (guide_coordinate_bounds j t').1
    have hp : chain.guidePortTime i.val.succ < chain.guidePortTime j.val.castSucc :=
      chain.guidePortTime_order _ _ hij j.property.le
    rw [← hcc] at hj
    exact (not_le_of_gt hp) (hj.trans hi)
  have corner_cell_source (t u : Interval) :
      (cornerCell (t,u)).val ∈ chain.cornerFan.chart.source := hPc_source (t,u)
  have corner_cell_chart (t u : Interval) :
      chain.cornerFan.chart (cornerCell (t,u)).val = P (t,u) :=
    chain.cornerFan.chart.right_inv (hPt (t,u))
  have corner_cell_last (u : Interval) :
      chain.cornerFan.chart (cornerCell (1,u)).val = Plane.mk (-chain.cornerDelta*u.val) 0 := by
    rw [corner_cell_chart]
    ext j
    fin_cases j
    · change P (1,u) 0 = -chain.cornerDelta*u.val
      rw [hP0]
      norm_num
      ring
    · change P (1,u) 1 = 0
      rw [hP1]
      norm_num
  have guide_corner_full_face
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hi : i.val.val+1 = chain.cornerIndex.val) :
      ∀ G : C(Interval × Interval,↥F),
        (∀ t u, ∃ p : Interval × Icc (-1:ℝ) 1,
          p.1 = (chain.guideCoordinates ρ i t).1 ∧
          p.2.val = u.val * (chain.guideCoordinates ρ i t).2.val ∧ G (t,u) = chain.guideStrip p) →
        ∀ u, G (1,u) = cornerCell (0,u) := by
    intro G hG u
    obtain ⟨p,hp1,hp2,hpG⟩ := hG 1 u
    have hpnonneg : 0 ≤ p.2.val := by
      rw [hp2]
      exact mul_nonneg u.property.1 (chain.guideCoordinates_width ρ i 1).1.le
    have hpwidth : p.2.val ≤ (chain.guideCoordinates ρ i 1).2.val := by
      rw [hp2]
      exact mul_le_of_le_one_left (chain.guideCoordinates_width ρ i 1).1.le u.property.2
    have hptrans := chain.guide_corner_width_transition ρ i hi p.2 hpnonneg hpwidth
    rw [← hp1] at hptrans
    rw [hpG]
    apply Subtype.ext
    apply chain.cornerFan.chart.injOn hptrans.1 (corner_cell_source 0 u)
    rw [hptrans.2, corner_cell_chart]
    ext j
    fin_cases j
    · change chain.cornerEntry 0-p.2.val/(chain.guideCoordinates ρ i 1).2.val*chain.cornerEpsilon ρ = P (0,u) 0
      rw [hP0]
      rw [hp2, mul_div_cancel_right₀ _ (ne_of_gt (chain.guideCoordinates_width ρ i 1).1)]
      norm_num
    · change chain.cornerEntry 1 = P (0,u) 1
      rw [hP1]
      norm_num
  choose G G_emb G_range G_bottom G_top G_V G_coords using ruled_guide_cells
  have guide_cell_face_range
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) (t : Interval) :
      range (fun u => G i (t,u)) =
      chain.guideStrip '' {p | p.1 = (chain.guideCoordinates ρ i t).1 ∧
        0 ≤ p.2.val ∧ p.2.val ≤ (chain.guideCoordinates ρ i t).2.val} := by
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      obtain ⟨p,hp1,hp2,hpG⟩ := G_coords i t u
      refine ⟨p,⟨hp1,?_,?_⟩,hpG.symm⟩
      · rw [hp2]; exact mul_nonneg u.property.1 (chain.guideCoordinates_width ρ i t).1.le
      · rw [hp2]; exact mul_le_of_le_one_left (chain.guideCoordinates_width ρ i t).1.le u.property.2
    · rintro ⟨p,⟨hp1,hpl,hpu⟩,rfl⟩
      let u : Interval := ⟨p.2.val/(chain.guideCoordinates ρ i t).2.val,
        ⟨div_nonneg hpl (chain.guideCoordinates_width ρ i t).1.le,
          (div_le_one (chain.guideCoordinates_width ρ i t).1).mpr hpu⟩⟩
      obtain ⟨p',hp'1,hp'2,hp'G⟩ := G_coords i t u
      refine ⟨u,?_⟩
      change G i (t,u) = chain.guideStrip p
      rw [hp'G]
      apply congrArg chain.guideStrip
      apply Prod.ext
      · exact hp'1.trans hp1.symm
      · apply Subtype.ext
        rw [hp'2]
        exact div_mul_cancel₀ _ (ne_of_gt (chain.guideCoordinates_width ρ i t).1)
  have guide_cells_full_seam
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 = j.val.val) (u : Interval) : G i (1,u) = G j (0,u) := by
    obtain ⟨p,hp1,hp2,hpG⟩ := G_coords i 1 u
    obtain ⟨p',hp'1,hp'2,hp'G⟩ := G_coords j 0 u
    rw [hpG,hp'G]
    apply congrArg chain.guideStrip
    apply Prod.ext
    · exact hp1.trans ((congrArg Prod.fst (guide_coordinate_seam i j hij)).trans hp'1.symm)
    · apply Subtype.ext
      rw [hp2,hp'2,guide_coordinate_seam i j hij]
  let idx (i : Fin (chain.cornerIndex.val+1)) (hi : i.val < chain.cornerIndex.val) :
      {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val} := ⟨⟨i.val,by omega⟩,hi⟩
  let cells : Fin (chain.cornerIndex.val+1) → C(Interval × Interval,↥F) := fun i =>
    if hi : i.val < chain.cornerIndex.val then G (idx i hi) else cornerCell
  have cells_guide (i : Fin (chain.cornerIndex.val+1)) (hi : i.val < chain.cornerIndex.val) :
      cells i = G (idx i hi) := dite_eq_left hi
  have cells_corner (i : Fin (chain.cornerIndex.val+1)) (hi : i.val = chain.cornerIndex.val) :
      cells i = cornerCell := dite_eq_right (by omega)
  have cells_emb (i) : IsEmbedding (cells i) := by
    by_cases hi : i.val < chain.cornerIndex.val
    · rw [cells_guide i hi]; exact G_emb _
    · rw [cells_corner i (by omega)]; exact corner_cell_embedded
  have cells_seam (i j : Fin (chain.cornerIndex.val+1)) (hij : i.val+1 = j.val) (u) :
      cells i (1,u) = cells j (0,u) := by
    have hi : i.val < chain.cornerIndex.val := by omega
    rw [cells_guide i hi]
    by_cases hj : j.val < chain.cornerIndex.val
    · rw [cells_guide j hj]
      exact guide_cells_full_seam _ _ hij u
    · rw [cells_corner j (by omega)]
      exact guide_corner_full_face _ (by dsimp [idx]; omega) _ (G_coords _) u
  have cells_meet (i j : Fin (chain.cornerIndex.val+1)) (hij : i.val < j.val) :
      range (cells i) ∩ range (cells j) =
        if i.val+1 = j.val then range (fun u => cells i (1,u)) else ∅ := by
    have hi : i.val < chain.cornerIndex.val := by omega
    rw [cells_guide i hi]
    by_cases hj : j.val < chain.cornerIndex.val
    · rw [cells_guide j hj,G_range,G_range]
      by_cases hadj : i.val+1 = j.val
      · rw [ite_eq_left hadj,guide_slabs_adjacent_inter _ _ hadj,guide_cell_face_range]
      · rw [ite_eq_right hadj]
        exact (guide_slabs_nonadjacent_disjoint _ _ (by dsimp [idx]; omega)).inter_eq
    · have hjc : j.val = chain.cornerIndex.val := by omega
      rw [cells_corner j hjc,G_range,corner_cell_range,chain.guide_corner_inter]
      by_cases hadj : i.val+1 = j.val
      · have hlast : (idx i hi).val.val+1 = chain.cornerIndex.val := by dsimp [idx]; omega
        rw [ite_eq_left hlast,ite_eq_left hadj,guide_cell_face_range]
      · have hnot : ¬ (idx i hi).val.val+1 = chain.cornerIndex.val := by dsimp [idx]; omega
        rw [ite_eq_right hnot,ite_eq_right hadj]
  obtain ⟨H₀,H₀_emb,H₀_range,H₀_first,H₀_last,H₀_rows⟩ :=
    HalfCollarScratch.finite_glue_with_rows chain.cornerIndex.val cells cells_emb cells_seam cells_meet
  have hcornerpos : 0 < chain.cornerIndex.val := by
    have := chain.corner_position
    have := chain.guiding_piece_exists
    omega
  have H₀_filled : range H₀ = guideCarrier ∪ cornerCarrier := by
    rw [H₀_range]
    ext y
    constructor
    · intro hy
      obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      by_cases h : i.val < chain.cornerIndex.val
      · rw [cells_guide i h,G_range] at hi
        exact Or.inl (mem_iUnion.mpr ⟨idx i h,hi⟩)
      · rw [cells_corner i (by omega),corner_cell_range] at hi
        exact Or.inr hi
    · rintro (hy | hy)
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hy
        let j : Fin (chain.cornerIndex.val+1) := ⟨i.val.val,by omega⟩
        apply mem_iUnion.mpr
        refine ⟨j,?_⟩
        rw [cells_guide j i.property,G_range]
        have he : idx j i.property = i := Subtype.ext (Fin.ext rfl)
        rw [he]
        exact hi
      · apply mem_iUnion.mpr
        refine ⟨Fin.last chain.cornerIndex.val,?_⟩
        rw [cells_corner _ (by simp),corner_cell_range]
        exact hy
  have H₀_V : range H₀ ⊆ V := by
    rw [H₀_filled]
    apply union_subset
    · exact iUnion_subset guide_slab_in_V
    · exact corner_hull_in_V
  have H₀_last_corner (u : Interval) : H₀ (1,u) = cornerCell (1,u) := by
    rw [H₀_last,cells_corner _ (by simp)]
  have H₀_first_line (u : Interval) :
      ∃ p : Icc (-1 : ℝ) 1, p.val = ρ.val*u.val ∧ H₀ (0,u) = chain.boundaryLine p := by
    have hi : (0 : Fin (chain.cornerIndex.val+1)).val < chain.cornerIndex.val := hcornerpos
    rw [H₀_first,cells_guide 0 hi]
    obtain ⟨p,hp1,hp2,hpG⟩ := G_coords (idx 0 hi) 0 u
    refine ⟨p.2,?_,?_⟩
    · rw [hp2,chain.guideCoordinates_first_width ρ _ (by rfl)]
      ring
    · rw [hpG,chain.boundaryLine_eq]
      apply congrArg chain.guideStrip
      apply Prod.ext
      · rw [hp1,chain.guideCoordinates_zero]
        have he : (idx 0 hi).val.castSucc = 0 := Fin.ext rfl
        rw [he,chain.guidePortTime_zero,chain.guideClock_start]
      · rfl
  have H₀_bottom_zero : H₀ (0,0) = d.second 0 := by
    obtain ⟨p,hp,he⟩ := H₀_first_line 0
    have hp0 : p = ⟨0,by norm_num⟩ := Subtype.ext (by simpa using hp)
    rw [he,hp0,chain.boundaryLine_zero]
  have H₀_bottom_one : H₀ (1,0) = d.second 1 := by
    rw [H₀_last_corner]
    apply Subtype.ext
    apply chain.cornerFan.chart.injOn (corner_cell_source 1 0)
      (d.corner_eq ▸ chain.cornerFan.contact_in_source)
    rw [corner_cell_last]
    rw [← d.corner_eq,chain.cornerFan.contact_zero]
    simp
  have second_range : range d.second = (r w).val.val '' uIcc d.bStart d.bFinish := by
    have he : (d.second : Interval → ↥F) =
        (r w).val.val ∘ CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish :=
      funext d.second_eq
    rw [he,range_comp,HalfCollarScratch.affine_range]
  have guide_coordinate_selected
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) (t : Interval) :
      (chain.guideCoordinates ρ i t).1 ∈ uIcc d.bStart d.bFinish := by
    have hb := guide_coordinate_bounds i t
    have hl := chain.guidePortTime_selected i.val.castSucc (by dsimp; omega)
    have hr := chain.guidePortTime_selected i.val.succ (by dsimp; omega)
    have hi : chain.guideClock (chain.guideClock.symm (chain.guideCoordinates ρ i t).1) ∈
        Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
      rcases chain.guideClock_increasing with hm | ha
      · exact ⟨hl.1.trans (hm.monotone hb.1),(hm.monotone hb.2).trans hr.2⟩
      · exact ⟨hr.1.trans (ha.antitone hb.2),(ha.antitone hb.1).trans hl.2⟩
    simpa only [chain.guideClock.apply_symm_apply, uIcc] using hi
  have corner_bottom_second (t : Interval) : cornerCell (t,0) ∈ range d.second := by
    have haxis : cornerCell (t,0) ∈ chartPull F chain.cornerFan.chart
        (segment ℝ (0 : Plane) chain.cornerEntry) := by
      refine ⟨corner_cell_source t 0,?_⟩
      rw [corner_cell_chart]
      refine ⟨t.val,1-t.val,t.property.1,sub_nonneg.mpr t.property.2,by ring,?_⟩
      simp [P]
    rw [chain.corner_b_axis_segment] at haxis
    exact image_subset_range _ _ haxis
  have H₀_bottom_subset : range (fun t => H₀ (t,0)) ⊆ range d.second := by
    rw [H₀_rows]
    intro y hy
    obtain ⟨i,⟨t,ht⟩⟩ := mem_iUnion.mp hy
    by_cases hi : i.val < chain.cornerIndex.val
    · change cells i (t,0) = y at ht
      rw [cells_guide i hi,G_bottom] at ht
      rw [← ht,second_range]
      exact ⟨_,guide_coordinate_selected _ t,rfl⟩
    · rw [cells_corner i (by omega)] at ht
      exact ht ▸ corner_bottom_second t
  obtain ⟨H,H_emb,H_range,H_bottom,H_first,H_last,H_rows⟩ :=
    HalfCollarScratch.normalize_bottom H₀ H₀_emb d.second d.second_embedded
      H₀_bottom_subset H₀_bottom_zero H₀_bottom_one
  have H_filled : range H = guideCarrier ∪ cornerCarrier := H_range.trans H₀_filled
  have H_V : range H ⊆ V := H_range ▸ H₀_V
  have H_first_line (u : Interval) : H (0,u) = chain.boundaryLine ⟨ρ.val*u.val,by
      constructor
      · nlinarith [ρ.property.1,u.property.1]
      · nlinarith [ρ.property.2,chain.bound_lt_one,u.property.1,u.property.2]⟩ := by
    rw [H_first]
    obtain ⟨p,hp,he⟩ := H₀_first_line u
    exact he.trans (congrArg chain.boundaryLine (Subtype.ext hp))
  have H_last_corner (u : Interval) : H (1,u) = cornerCell (1,u) :=
    (H_last u).trans (H₀_last_corner u)
  have H_last_chart (u : Interval) :
      (H (1,u)).val ∈ chain.cornerFan.chart.source ∧
      chain.cornerFan.chart (H (1,u)).val = Plane.mk (-chain.cornerDelta*u.val) 0 := by
    rw [H_last_corner]
    exact ⟨corner_cell_source 1 u,corner_cell_last u⟩
  have H_beta : H (0,1) = chain.beta ρ := by
    rw [H_first_line]
    obtain ⟨p,hp,hb⟩ := chain.beta_eq ρ
    rw [hb]
    apply congrArg chain.boundaryLine
    apply Subtype.ext
    simpa using hp.symm
  have q_z : chain.q ρ z = orientedA chain.cut := by
    have hclock := chain.piece_clock ρ (Fin.last chain.n) 0
    have hret := chain.retained_formula ρ 0
    have he : (Fin.last chain.n).castSucc = ⟨chain.n,by omega⟩ := Fin.ext rfl
    simp [CurveComplex.BranchedDoubleCover.intervalAffine] at hclock hret
    rw [he] at hclock
    exact hclock.symm.trans hret
  have corner_top_end : cornerCell (1,1) = chain.q ρ z := by
    rw [corner_cell_upper]
    have hc := chain.piece_clock ρ chain.cornerIndex 1
    have he : chain.cornerIndex.succ = ⟨chain.n,by omega⟩ := Fin.ext chain.corner_position
    simpa [CurveComplex.BranchedDoubleCover.intervalAffine,he] using hc
  have H_Acut : H (1,1) = orientedA chain.cut := (H_last_corner 1).trans (corner_top_end.trans q_z)
  have cells_top (i : Fin (chain.cornerIndex.val+1)) (t : Interval) :
      cells i (t,1) = chain.piece ρ ⟨i.val,by omega⟩ t := by
    by_cases hi : i.val < chain.cornerIndex.val
    · rw [cells_guide i hi,G_top]
    · rw [cells_corner i (by omega),corner_cell_upper]
      have he : (⟨i.val,by omega⟩ : Fin (chain.n+1)) = chain.cornerIndex :=
        Fin.ext (show i.val = chain.cornerIndex.val from by omega)
      rw [he]
  have H_top : range (fun t => H (t,1)) = chain.q ρ '' Icc (0 : Interval) z := by
    rw [H_rows,H₀_rows]
    ext y
    constructor
    · intro hy
      obtain ⟨i,⟨t,ht⟩⟩ := mem_iUnion.mp hy
      change cells i (t,1) = y at ht
      rw [cells_top,chain.piece_clock] at ht
      refine ⟨_,⟨?_,?_⟩,ht⟩
      · exact unitInterval.nonneg _
      · have hab : chain.cuts ρ (⟨i.val,by omega⟩ : Fin (chain.n+1)).castSucc ≤
            chain.cuts ρ (⟨i.val,by omega⟩ : Fin (chain.n+1)).succ :=
          (chain.cuts_strict ρ).monotone (by change i.val ≤ i.val+1; omega)
        have hu := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hab t).2
        have hl : chain.cuts ρ (⟨i.val,by omega⟩ : Fin (chain.n+1)).succ ≤ z :=
          (chain.cuts_strict ρ).monotone (by change i.val+1 ≤ chain.n; have := chain.corner_position; omega)
        exact hu.trans hl
    · rintro ⟨t,ht,rfl⟩
      have htq : chain.q ρ t ∈ range (chain.q ρ) := mem_range_self _
      rw [chain.q_range] at htq
      obtain ⟨i,⟨s,hs⟩⟩ := mem_iUnion.mp htq
      by_cases hi : i.val ≤ chain.cornerIndex.val
      · let j : Fin (chain.cornerIndex.val+1) := ⟨i.val,by omega⟩
        apply mem_iUnion.mpr
        refine ⟨j,s,?_⟩
        change cells j (s,1) = chain.q ρ t
        rw [cells_top]
        have he : (⟨j.val,by omega⟩ : Fin (chain.n+1)) = i := Fin.ext rfl
        rw [he]
        exact hs
      · have hiN : i = Fin.last chain.n := Fin.ext (by change i.val = chain.n; have := chain.corner_position; omega)
        have hs' := hs
        rw [chain.piece_clock] at hs'
        have hst := (chain.q_embedded ρ).injective hs'
        have hab : chain.cuts ρ i.castSucc ≤ chain.cuts ρ i.succ :=
          (chain.cuts_strict ρ).monotone (by change i.val ≤ i.val+1; omega)
        have hlow := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hab s).1
        have he : i.castSucc = ⟨chain.n,by omega⟩ := by rw [hiN]; apply Fin.ext; rfl
        rw [hst,he] at hlow
        have htz : t = z := le_antisymm ht.2 hlow
        rw [htz]
        apply mem_iUnion.mpr
        refine ⟨Fin.last chain.cornerIndex.val,1,?_⟩
        change cells _ (1,1) = chain.q ρ z
        rw [cells_corner _ (by simp)]
        exact corner_top_end
  have H_last_range : range (fun u => H (1,u)) =
      orientedA '' Icc (chain.clock.symm d.aFinish) chain.cut := by
    have haxis : range (fun u => cornerCell (1,u)) = chartPull F chain.cornerFan.chart
        (segment ℝ (0 : Plane) (Plane.mk (-chain.cornerDelta) 0)) := by
      ext y
      constructor
      · rintro ⟨u,rfl⟩
        refine ⟨corner_cell_source 1 u,?_⟩
        rw [corner_cell_last]
        refine ⟨1-u.val,u.val,sub_nonneg.mpr u.property.2,u.property.1,by ring,?_⟩
        ext j
        fin_cases j <;> simp <;> ring
      · rintro ⟨hy,⟨a,b,ha,hb,hab,he⟩⟩
        let u : Interval := ⟨b,⟨hb,by linarith⟩⟩
        refine ⟨u,?_⟩
        apply Subtype.ext
        apply chain.cornerFan.chart.injOn (corner_cell_source 1 u) hy
        rw [corner_cell_last,← he]
        ext j
        fin_cases j <;> simp [u] <;> ring
    have hr : (fun u => H (1,u)) = (fun u => cornerCell (1,u)) := funext H_last_corner
    rw [hr,haxis,chain.corner_a_axis_segment,image_image]
  have second_in_disk : range d.second ⊆ range d.disk := by
    intro y hy
    have hb : y ∈ range d.first ∪ range d.second ∪ range d.boundarySide := Or.inl (Or.inr hy)
    rw [← d.boundary_image] at hb
    exact image_subset_range _ _ hb
  have guide_slab_disk_subset
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) :
      regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i) ∩ range d.disk ⊆
        range d.second := by
    rintro y ⟨⟨p,⟨t,hpt,hpl,hpu⟩,hpy⟩,hyd⟩
    by_cases hp0 : p.2.val = 0
    · have hpzero : p.2 = ⟨0,by norm_num⟩ := Subtype.ext hp0
      have hpz : p = (p.1,⟨0,by norm_num⟩) := Prod.ext rfl hpzero
      rw [← hpy,hpz,chain.guideStrip_center,second_range]
      refine ⟨p.1,?_,rfl⟩
      rw [hpt]
      exact guide_coordinate_selected i t
    · have hpos : 0 < p.2.val := lt_of_le_of_ne hpl (Ne.symm hp0)
      have hbound : p.2.val < chain.bound := hpu.trans_lt (chain.guideCoordinates_width ρ i t).2
      have hsel : p.1 ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
        rw [hpt]
        exact guide_coordinate_selected i t
      have hex : y ∈ chain.guideStrip '' {p | p.1 ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) ∧
          0 < p.2.val ∧ p.2.val < chain.bound} := ⟨p,⟨hsel,hpos,hbound⟩,hpy⟩
      exact False.elim (Set.disjoint_left.mp chain.guiding_exterior hex hyd)
  have H_disk : range H ∩ range d.disk = range d.second := by
    rw [H_filled]
    ext y
    constructor
    · rintro ⟨hg | hc,hd⟩
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hg
        exact guide_slab_disk_subset i ⟨hi,hd⟩
      · have hcorner : y ∈ cornerCarrier ∩ range d.disk := ⟨hc,hd⟩
        change y ∈ chartPull F chain.cornerFan.chart
          (regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)) ∩ range d.disk at hcorner
        rw [chain.corner_disk_inter] at hcorner
        exact image_subset_range _ _ hcorner
    · rintro ⟨t,rfl⟩
      have hm : d.second t ∈ range H := ⟨(t,0),H_bottom t⟩
      exact ⟨H_filled ▸ hm,second_in_disk (mem_range_self _)⟩
  have boundary_in_frontier (y : ↥F) (hy : y.val ∈ boundaryCircle) : y.val ∈ frontier F := by
    rw [hfrontier]
    exact Or.inl hy
  have bFinish_off : (r w).val.val d.bFinish ∉ {y : ↥F | y.val ∈ frontier F} := by
    have he : d.second 1 = (r w).val.val d.bFinish := by
      simpa [CurveComplex.BranchedDoubleCover.intervalAffine] using d.second_eq 1
    rw [← he,← d.corner_eq]
    exact d.corner_off_frontier
  have bFinish_interior : d.bFinish ∈ Ioo (0 : Interval) 1 := by
    have h0 : d.bFinish ≠ 0 := by
      intro he
      apply bFinish_off
      rw [he]
      exact boundary_in_frontier _ (r w).val.property.2.1
    have h1 : d.bFinish ≠ 1 := by
      intro he
      apply bFinish_off
      rw [he]
      exact boundary_in_frontier _ (r w).val.property.2.2.1
    exact ⟨lt_of_le_of_ne (show (0 : Interval) ≤ d.bFinish from d.bFinish.property.1) (Ne.symm h0),
      lt_of_le_of_ne (show d.bFinish ≤ (1 : Interval) from d.bFinish.property.2) h1⟩
  have guide_frontier_face
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) :
      regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i) ∩
        {y : ↥F | y.val ∈ frontier F} ⊆ range (fun u => H (0,u)) := by
    rintro y ⟨⟨p,⟨t,hpt,hpl,hpu⟩,hpy⟩,hyF⟩
    have hpends : p.1 = 0 ∨ p.1 = 1 := by
      by_cases hp0 : p.1 = 0
      · exact Or.inl hp0
      · by_cases hp1 : p.1 = 1
        · exact Or.inr hp1
        · have hptI : p.1 ∈ Ioo (0 : Interval) 1 :=
            ⟨lt_of_le_of_ne (show (0 : Interval) ≤ p.1 from p.1.property.1) (Ne.symm hp0),
              lt_of_le_of_ne (show p.1 ≤ (1 : Interval) from p.1.property.2) hp1⟩
          have hi := chain.guideStrip_interior p.1 hptI p.2
          have hf : (chain.guideStrip p).val ∈ frontier F := hpy.symm ▸ hyF
          exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hi hf)
    have hsel : p.1 ∈ uIcc d.bStart d.bFinish := hpt ▸ guide_coordinate_selected i t
    have hpstart : p.1 = d.bStart := by
      rcases le_total d.bStart d.bFinish with hsf | hfs
      · rw [uIcc_of_le hsf] at hsel
        rcases hpends with hp0 | hp1
        · rw [hp0] at hsel
          exact hp0.trans (le_antisymm hsel.1 (show (0 : Interval) ≤ d.bStart from d.bStart.property.1)).symm
        · rw [hp1] at hsel
          exact False.elim ((not_le_of_gt bFinish_interior.2) hsel.2)
      · rw [uIcc_of_ge hfs] at hsel
        rcases hpends with hp0 | hp1
        · rw [hp0] at hsel
          exact False.elim ((not_le_of_gt bFinish_interior.1) hsel.1)
        · rw [hp1] at hsel
          exact hp1.trans (le_antisymm (show d.bStart ≤ (1 : Interval) from d.bStart.property.2) hsel.2).symm
    have hcoordzero : chain.guideClock.symm (chain.guideCoordinates ρ i t).1 = 0 := by
      rw [← hpt,hpstart,← chain.guideClock_start,chain.guideClock.symm_apply_apply]
    have hi0 : i.val.val = 0 := by
      by_contra hi
      have hipos : 0 < i.val.val := Nat.pos_of_ne_zero hi
      have hpord := chain.guidePortTime_order 0 i.val.castSucc hipos i.property.le
      rw [chain.guidePortTime_zero] at hpord
      have hbound := (guide_coordinate_bounds i t).1
      rw [hcoordzero] at hbound
      exact (not_le_of_gt hpord) hbound
    have hzeroindex : i.val.castSucc = 0 := Fin.ext hi0
    have ht0 : t = 0 := (chain.guideCoordinates_order ρ i).injective (by
      rw [hcoordzero,chain.guideCoordinates_zero,hzeroindex,chain.guidePortTime_zero,
        chain.guideClock.symm_apply_apply])
    subst t
    have hyface : y ∈ range (fun u => G i (0,u)) := by
      rw [guide_cell_face_range]
      exact ⟨p,⟨hpt,hpl,hpu⟩,hpy⟩
    obtain ⟨u,hu⟩ := hyface
    refine ⟨u,?_⟩
    change H (0,u) = y
    rw [H_first,H₀_first,cells_guide 0 hcornerpos]
    have hei : idx 0 hcornerpos = i := Subtype.ext (Fin.ext hi0.symm)
    rw [hei]
    exact hu
  have H_frontier : range H ∩ {y : ↥F | y.val ∈ frontier F} = range (fun u => H (0,u)) := by
    ext y
    constructor
    · rintro ⟨hyH,hyF⟩
      rw [H_filled] at hyH
      rcases hyH with hg | hc
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hg
        exact guide_frontier_face i ⟨hi,hyF⟩
      · have hi : y.val ∈ interior F :=
          (chain.cornerFan.source_closure (subset_closure hc.1)).2
        exact False.elim (Set.disjoint_left.mp disjoint_interior_frontier hi hyF)
    · rintro ⟨u,rfl⟩
      refine ⟨mem_range_self _,?_⟩
      change (H (0,u)).val ∈ frontier F
      rw [H_first]
      obtain ⟨p,hp,he⟩ := H₀_first_line u
      rw [he]
      have hpnonneg : 0 ≤ p.val := by rw [hp]; exact mul_nonneg ρ.property.1.le u.property.1
      have hpsmall : |p.val| < chain.bound := by
        rw [abs_of_nonneg hpnonneg,hp]
        exact (mul_le_of_le_one_right ρ.property.1.le u.property.2).trans_lt ρ.property.2
      exact boundary_in_frontier _ (chain.boundaryLine_local ⟨p,hpsmall,rfl⟩).1
  exact ⟨H,H_emb,H_filled,H_V,H_bottom,H_top,H_first_line,H_last_chart,H_disk,H_frontier,
    H_beta,H_Acut,H_last_range⟩
