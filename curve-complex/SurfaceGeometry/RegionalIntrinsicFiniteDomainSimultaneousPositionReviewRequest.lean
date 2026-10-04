import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalOriginalSupportedAmbientCopy
import RegionalIntrinsicCompatiblePairTotalContactDecrease
import CurveComplexGenusTwo.Topology.ActualRegionalPairContactPosition.RegionalIntrinsicPairContactPosition
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalActualGraphDescent
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalGraphCommonFaceMovie
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalTerminalGraphConeFace
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteLabelHomotopyAssembly
open CurveComplex Set Topology
open scoped Manifold ContDiff BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P
theorem regional_original_intrinsic_finite_domain_simultaneous_position
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
    ∀ (ι : Type) [Fintype ι] (K : AbstractSimplicialComplex ι)
      (labels : ι → IntrinsicArcVertex) (givenAnchor : IntrinsicEssentialArc),
      (∀ σ : Finset ι, σ ∈ K.faces → σ.image labels ∈ intrinsicArcComplex.faces) →
      ∃ (a : ι → IntrinsicEssentialArc) (anchor : IntrinsicEssentialArc),
        (∀ i, Quot.mk intrinsicArcRel (a i) = labels i) ∧
        Quot.mk intrinsicArcRel anchor = Quot.mk intrinsicArcRel givenAnchor ∧
        (∀ σ : Finset ι, σ ∈ K.faces → ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
          Disjoint (Set.range (a i).val.val) (Set.range (a j).val.val)) ∧
        (∀ i, anchor.val.val 0 ∉ Set.range (a i).val.val) ∧
        (∀ i, anchor.val.val 1 ∉ Set.range (a i).val.val) ∧
        (∀ i, (Set.range anchor.val.val ∩ Set.range (a i).val.val).Finite) := by
  classical
  intro B Proper Parallel Arc rel V faces L ι inst K labels givenAnchor hfaces
  by_cases hempty : IsEmpty ι
  · let := hempty
    let a : ι → Arc := fun i => isEmptyElim i
    refine ⟨a,givenAnchor,?_,rfl,?_,?_,?_,?_⟩
    · intro i
      exact isEmptyElim i
    · intro σ hσ i hi j hj hij
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i
    · intro i
      exact isEmptyElim i
  · by_cases hconstant : ∀ i, labels i = Quot.mk rel givenAnchor
    · let : ClosedSurface S := Classical.choice hS.2.1
      have copies : ∀ σ : Finset ι, ∃ a : ι → Arc,
          (∀ i ∈ σ, Quot.mk rel (a i) = Quot.mk rel givenAnchor) ∧
          (∀ i ∈ σ, Disjoint (Set.range givenAnchor.val.val) (Set.range (a i).val.val)) ∧
          (∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
            Disjoint (Set.range (a i).val.val) (Set.range (a j).val.val)) := by
        intro σ
        induction σ using Finset.induction_on with
        | empty => exact ⟨fun _ => givenAnchor,by simp,by simp,by simp⟩
        | @insert k σ hk ih =>
          obtain ⟨a,halabel,haclear,hadis⟩ := ih
          let retained : ↥σ → C(Interval,↥F) := fun i => (a i.val).val.val
          let U : Set ↥F := ⋃ i : ↥σ, Set.range (retained i)
          have hU : IsClosed U := isClosed_iUnion_of_finite
            (fun i => (isCompact_range (retained i).continuous).isClosed)
          have hanchorU : Set.range givenAnchor.val.val ⊆ Uᶜ := by
            intro y hy hyU
            obtain ⟨i,hyi⟩ := Set.mem_iUnion.mp hyU
            exact Set.disjoint_left.mp (haclear i.val i.property) hy hyi
          have havoid : ∀ i, Disjoint Uᶜ (Set.range (retained i)) := by
            intro i
            apply Set.disjoint_left.mpr
            intro y hy hyi
            exact hy (Set.mem_iUnion.mpr ⟨i,hyi⟩)
          obtain ⟨b,hb,hb0,hb1,hbp,hba,hbU,hbret,H,hHB,hHF,hmove,hout,hfix⟩ :=
            regional_original_proper_arc_supported_ambient_copy S g hg hS x R hR htarget
              F hFcompact hbase houtside J c hbaseDisjoint hfrontier
              givenAnchor.val.val givenAnchor.val.property.1
              givenAnchor.val.property.2.1 givenAnchor.val.property.2.2.1
              givenAnchor.val.property.2.2.2 Uᶜ hU.isOpen_compl hanchorU retained havoid
          have hbess := (regional_essential_arc_ambient_transport F B
            givenAnchor.val.val b H (hHB 1) hmove).mp givenAnchor.property
          let copy : Arc := ⟨⟨b,hb,hb0,hb1,hbp⟩,hbess⟩
          have hcopylabel : Quot.mk rel copy = Quot.mk rel givenAnchor :=
            (Quot.sound (show rel givenAnchor copy from ⟨H,hHB,hHF,hmove⟩)).symm
          refine ⟨Function.update a k copy,?_,?_,?_⟩
          · intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · simpa using hcopylabel
            · have hik : i ≠ k := fun he => hk (he ▸ hi)
              simpa [Function.update,hik] using halabel i hi
          · intro i hi
            rcases Finset.mem_insert.mp hi with rfl | hi
            · simpa [copy] using hba
            · have hik : i ≠ k := fun he => hk (he ▸ hi)
              simpa [Function.update,hik] using haclear i hi
          · intro i hi j hj hij
            by_cases hik : i = k
            · subst i
              have hjs : j ∈ σ := (Finset.mem_insert.mp hj).resolve_left hij.symm
              simpa [Function.update,hij.symm,copy] using hbret ⟨j,hjs⟩
            · have his : i ∈ σ := (Finset.mem_insert.mp hi).resolve_left hik
              by_cases hjk : j = k
              · subst j
                simpa [Function.update,hik,copy] using (hbret ⟨i,his⟩).symm
              · have hjs : j ∈ σ := (Finset.mem_insert.mp hj).resolve_left hjk
                simpa [Function.update,hik,hjk] using hadis i his j hjs hij
      obtain ⟨a,halabel,haclear,hadis⟩ := copies Finset.univ
      refine ⟨a,givenAnchor,?_,rfl,?_,?_,?_,?_⟩
      · intro i
        exact (halabel i (Finset.mem_univ i)).trans (hconstant i).symm
      · intro σ hσ i hi j hj hij
        exact hadis i (Finset.mem_univ i) j (Finset.mem_univ j) hij
      · intro i
        exact fun h => Set.disjoint_left.mp (haclear i (Finset.mem_univ i))
          (Set.mem_range_self 0) h
      · intro i
        exact fun h => Set.disjoint_left.mp (haclear i (Finset.mem_univ i))
          (Set.mem_range_self 1) h
      · intro i
        rw [Set.disjoint_iff_inter_eq_empty.mp (haclear i (Finset.mem_univ i))]
        exact Set.finite_empty
    · have hraw : ∃ a : ι → Arc, ∀ i, Quot.mk rel (a i) = labels i := by
        choose a ha using (fun i => Quot.exists_rep (labels i))
        exact ⟨a,ha⟩
      obtain ⟨a,ha⟩ := hraw
      let : ClosedSurface S := Classical.choice hS.2.1
      obtain ⟨init,initAnchor,hinit,hinitAnchor,hinitFinite,hinitEnds,hinitZero,hinitOne,hinitAnchorFinite⟩ :=
        regional_original_intrinsic_finite_family_pair_contact_position
          S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
          J c hdisjoint hbaseDisjoint hfrontier ι a givenAnchor
      let State := {s : (ι → Arc) × Arc //
        (∀ i, Quot.mk rel (s.1 i) = labels i) ∧
        Quot.mk rel s.2 = Quot.mk rel givenAnchor ∧
        (∀ i j, i ≠ j → (Set.range (s.1 i).val.val ∩ Set.range (s.1 j).val.val).Finite) ∧
        (∀ i j, i ≠ j → (s.1 i).val.val 0 ≠ (s.1 j).val.val 0 ∧
          (s.1 i).val.val 0 ≠ (s.1 j).val.val 1 ∧
          (s.1 i).val.val 1 ≠ (s.1 j).val.val 0 ∧
          (s.1 i).val.val 1 ≠ (s.1 j).val.val 1) ∧
        (∀ i, s.2.val.val 0 ∉ Set.range (s.1 i).val.val) ∧
        (∀ i, s.2.val.val 1 ∉ Set.range (s.1 i).val.val) ∧
        (∀ i, (Set.range s.2.val.val ∩ Set.range (s.1 i).val.val).Finite)}
      have hstate : Nonempty State := ⟨⟨(init,initAnchor),
        (fun i => (hinit i).trans (ha i)),hinitAnchor,hinitFinite,hinitEnds,
        hinitZero,hinitOne,hinitAnchorFinite⟩⟩
      let : Nonempty State := hstate
      let energy : State → ℕ := fun s => ∑ i : ι, ∑ j : ι,
        if i = j then 0 else (Set.range (s.val.1 i).val.val ∩ Set.range (s.val.1 j).val.val).ncard
      let least : State := Function.argmin energy
      have hpair : ∀ σ : Finset ι, σ ∈ K.faces → ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
          Disjoint (Set.range (least.val.1 i).val.val) (Set.range (least.val.1 j).val.val) := by
        intro σ hσ i hi j hj hij
        have hcompat : ∃ u v : Arc,
            Quot.mk rel u = Quot.mk rel (least.val.1 i) ∧
            Quot.mk rel v = Quot.mk rel (least.val.1 j) ∧
            Disjoint (Set.range u.val.val) (Set.range v.val.val) := by
          by_cases he : labels i = labels j
          · let old : Arc := least.val.1 i
            let retained : Fin 0 → C(Interval,↥F) := fun k => Fin.elim0 k
            obtain ⟨b,hb,hb0,hb1,hbp,hba,hbU,hbret,H,hHB,hHF,hmove,hout,hfix⟩ :=
              regional_original_proper_arc_supported_ambient_copy S g hg hS x R hR htarget
                F hFcompact hbase houtside J c hbaseDisjoint hfrontier
                old.val.val old.val.property.1 old.val.property.2.1 old.val.property.2.2.1
                old.val.property.2.2.2 Set.univ isOpen_univ (Set.subset_univ _) retained
                (fun k => Fin.elim0 k)
            have hbess := (regional_essential_arc_ambient_transport F B
              old.val.val b H (hHB 1) hmove).mp old.property
            let copy : Arc := ⟨⟨b,hb,hb0,hb1,hbp⟩,hbess⟩
            have hcopy : Quot.mk rel copy = Quot.mk rel old :=
              (Quot.sound (show rel old copy from ⟨H,hHB,hHF,hmove⟩)).symm
            refine ⟨old,copy,rfl,?_,hba⟩
            exact hcopy.trans ((least.property.1 i).trans (he.trans (least.property.1 j).symm))
          · have hf := hfaces σ hσ
            obtain ⟨hne,rep,hrep,hdis⟩ := hf
            let ui : ↥(σ.image labels) := ⟨labels i,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
            let uj : ↥(σ.image labels) := ⟨labels j,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩
            refine ⟨rep ui,rep uj,(hrep ui).trans (least.property.1 i).symm,
              (hrep uj).trans (least.property.1 j).symm,hdis ui uj ?_⟩
            intro hh
            exact he (congrArg Subtype.val hh)
        apply Set.disjoint_iff_inter_eq_empty.mpr
        apply (Set.ncard_eq_zero (least.property.2.2.1 i j hij)).mp
        by_contra hn
        obtain ⟨next,nextAnchor,hclass,hanchor,hfinite,hends,hzero,hone,hanchorfinite,hdrop⟩ :=
          regional_original_intrinsic_compatible_pair_total_contact_decrease
            S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
            J c hdisjoint hbaseDisjoint hfrontier ι least.val.1 least.val.2 i j hij hcompat
            least.property.2.2.1 least.property.2.2.2.1 least.property.2.2.2.2.1
            least.property.2.2.2.2.2.1 least.property.2.2.2.2.2.2 (Nat.pos_of_ne_zero hn)
        let successor : State := ⟨(next,nextAnchor),
          (fun k => (hclass k).trans (least.property.1 k)),
          hanchor.trans least.property.2.1,hfinite,hends,hzero,hone,hanchorfinite⟩
        exact Function.not_lt_argmin energy successor hdrop
      exact ⟨least.val.1,least.val.2,least.property.1,least.property.2.1,hpair,
        least.property.2.2.2.2.1,least.property.2.2.2.2.2.1,least.property.2.2.2.2.2.2⟩
