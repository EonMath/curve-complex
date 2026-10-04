import CurveComplexGenusTwo.Topology.ActualCutRecognition.SharedActualCut
import CurveComplexGenusTwo.Foundations.NonseparatingRealizationBridge
import CurveComplexGenusTwo.Topology.FareyDictionaryStarDeletionConsumer

set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CurveComplex.Hyperbolic CurveComplexGenusTwo.Topology
open Set _root_.Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
open LeanEval.Topology.ClassificationOfSurfaces
open scoped Manifold ContDiff

theorem source_genus_two_separating_actual_cut
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hS : IsGenus S 2) (c : Curve S) (hc : Essential c)
    (hdiv : ¬ IsConnected c.imageᶜ) :
    ∃ U V : Set S,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = c.imageᶜ ∧ frontier U = c.image ∧ frontier V = c.image ∧
      Nonempty (U ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) ∧
      Nonempty (V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) := by
  classical
  have hcompact (E : Type) [TopologicalSpace E]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
      (hE : IsGenus E 2) (c : Curve E) (hc : Essential c)
      (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
      (hUconn : IsConnected U) (hVconn : IsConnected V)
      (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
      (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image) :
      ∃ (p : ℕ) (e : (closure U) ≃ₜ Quot (OrientableRel p 1)),
        ∀ x : closure U,
          e x ∈ ActualOneBoundaryOrientableBoundary p ↔ x.val ∈ c.image := by
    classical
    letI : ClosedSurface E := Classical.choice hE.2.1
    let K := closure U
    have hK : K = U ∪ c.image := by
      exact (closure_eq_self_union_frontier U).trans (by rw [hfrontU])
    have hUsub : U ⊆ c.imageᶜ := by
      intro z hz
      rw [← hcover]
      exact Or.inl hz
    have hVsub : V ⊆ c.imageᶜ := by
      intro z hz
      rw [← hcover]
      exact Or.inr hz
    have hVK : Disjoint V K := by
      apply Set.disjoint_left.mpr
      intro z hzV hzK
      rw [hK] at hzK
      rcases hzK with hzU | hzc
      · exact Set.disjoint_left.mp hUV hzU hzV
      · exact hVsub hzV hzc
    have hKinterior : interior K = U := by
      apply Set.Subset.antisymm
      · intro z hz
        have hzK := interior_subset hz
        rw [hK] at hzK
        rcases hzK with hzU | hzc
        · exact hzU
        · have hzfrontV : z ∈ frontier V := hfrontV.symm ▸ hzc
          obtain ⟨w, hwInterior, hwV⟩ := mem_closure_iff.mp hzfrontV.1
            (interior K) isOpen_interior hz
          exact False.elim (Set.disjoint_left.mp hVK hwV (interior_subset hwInterior))
      · rw [← hU.interior_eq]
        exact interior_mono subset_closure
    have hKfrontier : frontier K = c.image := by
      rw [frontier, hKinterior]
      have hclosedK : IsClosed K := isClosed_closure
      rw [hclosedK.closure_eq, hK]
      ext z
      constructor
      · rintro ⟨hzU | hzc, hnotU⟩
        · exact False.elim (hnotU hzU)
        · exact hzc
      · intro hzc
        exact ⟨Or.inr hzc, fun hzU => hUsub hzU hzc⟩
    have hKcompact : IsCompact K := isClosed_closure.isCompact
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
    have hKconnected : IsConnected K := hUconn.closure
    have hboundaryCollar :
        ∃ b : C(Set.Ico (0 : ℝ) 1 × Circle, K),
          Topology.IsOpenEmbedding b ∧
          ∀ w : Circle, (b (⟨0, by norm_num⟩, w)).val = c.map w := by
      obtain ⟨e, he, hcore⟩ :=
        CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
          E 2 (by omega) hE ⟨c, hc⟩
      let T := Set.Ioo (-1 : ℝ) 1
      let Iplus : Set T := {t | 0 < t.val}
      let Iminus : Set T := {t | t.val < 0}
      have hplusImage : Subtype.val '' Iplus = Set.Ioo (0 : ℝ) 1 := by
        ext t
        constructor
        · rintro ⟨r, hr, rfl⟩
          exact ⟨hr, r.property.2⟩
        · intro ht
          exact ⟨⟨t, ⟨by linarith [ht.1], ht.2⟩⟩, ht.1, rfl⟩
      have hminusImage : Subtype.val '' Iminus = Set.Ioo (-1 : ℝ) 0 := by
        ext t
        constructor
        · rintro ⟨r, hr, rfl⟩
          exact ⟨r.property.1, hr⟩
        · intro ht
          exact ⟨⟨t, ⟨ht.1, by linarith [ht.2]⟩⟩, ht.2, rfl⟩
      have hplusConnected : _root_.IsPreconnected Iplus := by
        apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        rw [hplusImage]
        exact isPreconnected_Ioo
      have hminusConnected : _root_.IsPreconnected Iminus := by
        apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
        rw [hminusImage]
        exact isPreconnected_Ioo
      let Kplus := e '' (Iplus ×ˢ (Set.univ : Set Circle))
      let Kminus := e '' (Iminus ×ˢ (Set.univ : Set Circle))
      have hKplusConnected : _root_.IsPreconnected Kplus :=
        (hplusConnected.prod isPreconnected_univ).image e e.continuous.continuousOn
      have hKminusConnected : _root_.IsPreconnected Kminus :=
        (hminusConnected.prod isPreconnected_univ).image e e.continuous.continuousOn
      have hnoncore : ∀ p : T × Circle, p.1.val ≠ 0 → e p ∈ c.imageᶜ := by
        intro p hne hpc
        obtain ⟨w, hw⟩ := hpc
        have heq : e p = e (⟨0, by norm_num⟩, w) := by
          rw [hcore]
          exact hw.symm
        exact hne (congrArg (fun q : T × Circle => q.1.val) (he.injective heq))
      have hKplusSub : Kplus ⊆ c.imageᶜ := by
        rintro y ⟨p, hp, rfl⟩
        exact hnoncore p (ne_of_gt hp.1)
      have hKminusSub : Kminus ⊆ c.imageᶜ := by
        rintro y ⟨p, hp, rfl⟩
        exact hnoncore p (ne_of_lt hp.1)
      have hmeets : ∀ A : Set E, A ⊆ c.imageᶜ → c.map 1 ∈ closure A →
          (A ∩ Kplus).Nonempty ∨ (A ∩ Kminus).Nonempty := by
        intro A hAF hz
        have hzrange : c.map 1 ∈ Set.range e :=
          ⟨(⟨0, by norm_num⟩, 1), hcore 1⟩
        obtain ⟨y, hyrange, hyA⟩ := mem_closure_iff.mp hz (Set.range e) he.isOpen_range hzrange
        obtain ⟨p, rfl⟩ := hyrange
        have htime : p.1.val ≠ 0 := by
          intro hpzero
          have hp : p.1 = (⟨0, by norm_num [T]⟩ : T) := Subtype.ext hpzero
          apply hAF hyA
          refine ⟨p.2, ?_⟩
          calc c.map p.2 = e (⟨0, by norm_num⟩, p.2) := (hcore p.2).symm
            _ = e p := by rw [← hp]
        rcases lt_or_gt_of_ne htime with hnegative | hpositive
        · exact Or.inr ⟨e p, hyA, ⟨p, ⟨hnegative, Set.mem_univ _⟩, rfl⟩⟩
        · exact Or.inl ⟨e p, hyA, ⟨p, ⟨hpositive, Set.mem_univ _⟩, rfl⟩⟩
      have hsplitPlus : Kplus ⊆ U ∨ Kplus ⊆ V :=
        _root_.IsPreconnected.subset_or_subset hU hV hUV
          (by simpa [hcover] using hKplusSub) hKplusConnected
      have hsplitMinus : Kminus ⊆ U ∨ Kminus ⊆ V :=
        _root_.IsPreconnected.subset_or_subset hU hV hUV
          (by simpa [hcover] using hKminusSub) hKminusConnected
      have hUmeets := hmeets U hUsub
        (show c.map 1 ∈ closure U from frontier_subset_closure (hfrontU.symm ▸ ⟨1, rfl⟩))
      have hVmeets := hmeets V hVsub
        (show c.map 1 ∈ closure V from frontier_subset_closure (hfrontV.symm ▸ ⟨1, rfl⟩))
      have hbothImpossible : ∀ A B : Set E, Disjoint A B →
          Kplus ⊆ A → Kminus ⊆ A →
          ((B ∩ Kplus).Nonempty ∨ (B ∩ Kminus).Nonempty) → False := by
        intro A B hAB hplus hminus hmeet
        rcases hmeet with ⟨z, hzB, hzplus⟩ | ⟨z, hzB, hzminus⟩
        · exact Set.disjoint_left.mp hAB (hplus hzplus) hzB
        · exact Set.disjoint_left.mp hAB (hminus hzminus) hzB
      have hsign : (Kplus ⊆ U ∧ Kminus ⊆ V) ∨ (Kminus ⊆ U ∧ Kplus ⊆ V) := by
        rcases hsplitPlus with hplusU | hplusV
        · rcases hsplitMinus with hminusU | hminusV
          · exact False.elim (hbothImpossible U V hUV hplusU hminusU hVmeets)
          · exact Or.inl ⟨hplusU, hminusV⟩
        · rcases hsplitMinus with hminusU | hminusV
          · exact Or.inr ⟨hminusU, hplusV⟩
          · exact False.elim (hbothImpossible V U hUV.symm hplusV hminusV hUmeets)
      have horiented : ∃ f : C(T × Circle, E),
          Topology.IsOpenEmbedding f ∧
          (∀ w, f (⟨0, by norm_num [T]⟩, w) = c.map w) ∧
          (∀ p : T × Circle, 0 < p.1.val → f p ∈ U) ∧
          (∀ p : T × Circle, p.1.val < 0 → f p ∈ V) := by
        rcases hsign with ⟨hplusU, hminusV⟩ | ⟨hminusU, hplusV⟩
        · exact ⟨e, he, hcore,
            fun p hp => hplusU ⟨p, ⟨hp, Set.mem_univ _⟩, rfl⟩,
            fun p hp => hminusV ⟨p, ⟨hp, Set.mem_univ _⟩, rfl⟩⟩
        · let negT : T ≃ₜ T := {
            toFun := fun t => ⟨-t.val, by rcases t.property with ⟨hl, hr⟩; constructor <;> linarith⟩
            invFun := fun t => ⟨-t.val, by rcases t.property with ⟨hl, hr⟩; constructor <;> linarith⟩
            left_inv := fun t => Subtype.ext (neg_neg t.val)
            right_inv := fun t => Subtype.ext (neg_neg t.val)
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }
          let flip := negT.prodCongr (Homeomorph.refl Circle)
          let f : C(T × Circle, E) := ⟨fun p => e (flip p), e.continuous.comp flip.continuous⟩
          refine ⟨f, he.comp flip.isOpenEmbedding, ?_, ?_, ?_⟩
          · intro w
            change e (flip (⟨0, by norm_num [T]⟩, w)) = c.map w
            have heq : flip (⟨0, by norm_num [T]⟩, w) = (⟨0, by norm_num [T]⟩, w) := by
              apply Prod.ext
              · apply Subtype.ext; simp [flip, negT]
              · rfl
            rw [heq]
            exact hcore w
          · intro p hp
            apply hminusU
            exact ⟨flip p, ⟨by change -p.1.val < 0; linarith, Set.mem_univ _⟩, rfl⟩
          · intro p hp
            apply hplusV
            exact ⟨flip p, ⟨by change 0 < -p.1.val; linarith, Set.mem_univ _⟩, rfl⟩
      obtain ⟨f, hf, hfcore, hfplus, hfminus⟩ := horiented
      let H := Set.Ico (0 : ℝ) 1
      have hHsub : H ⊆ T := by
        intro t ht
        exact ⟨by linarith [ht.1], ht.2⟩
      let g : C(H × Circle, T × Circle) := {
        toFun := fun p => (Set.inclusion hHsub p.1, p.2)
        continuous_toFun := by fun_prop }
      have hg : Topology.IsEmbedding g :=
        (Topology.IsEmbedding.inclusion hHsub).prodMap Topology.IsEmbedding.id
      have hmem : ∀ p : H × Circle, f (g p) ∈ K := by
        intro p
        rw [hK]
        by_cases ht : p.1.val = 0
        · apply Or.inr
          have hgzero : g p = (⟨0, by norm_num [T]⟩, p.2) := by
            apply Prod.ext
            · exact Subtype.ext ht
            · rfl
          rw [hgzero, hfcore]
          exact ⟨p.2, rfl⟩
        · apply Or.inl
          exact hfplus (g p) (lt_of_le_of_ne p.1.property.1 (Ne.symm ht))
      let b : C(H × Circle, K) := ⟨fun p => ⟨f (g p), hmem p⟩,
        (f.continuous.comp g.continuous).subtype_mk _⟩
      have hb : Topology.IsEmbedding b := (hf.isEmbedding.comp hg).codRestrict K hmem
      have hbrange : Set.range b = Subtype.val ⁻¹' Set.range f := by
        ext q
        constructor
        · rintro ⟨p, rfl⟩
          exact ⟨g p, rfl⟩
        · rintro ⟨p, hp⟩
          have hnonneg : 0 ≤ p.1.val := by
            by_contra hneg
            have hpV : f p ∈ V := hfminus p (lt_of_not_ge hneg)
            have hpK : f p ∈ K := hp.symm ▸ q.property
            exact Set.disjoint_left.mp hVK hpV hpK
          let r : H × Circle := (⟨p.1.val, ⟨hnonneg, p.1.property.2⟩⟩, p.2)
          refine ⟨r, ?_⟩
          apply Subtype.ext
          exact hp
      refine ⟨b, ⟨hb, ?_⟩, ?_⟩
      · rw [hbrange]
        exact hf.isOpen_range.preimage continuous_subtype_val
      · intro w
        exact hfcore w
    have hnoBoundaryPreservingDisc :
        ¬ ∃ d : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ K,
          ∀ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
            (d x).val ∈ c.image ↔
              x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
      rintro ⟨d, hd⟩
      apply hc
      let f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E) :=
        ⟨fun x => (d x).val, continuous_subtype_val.comp d.continuous⟩
      refine ⟨f, Topology.IsEmbedding.subtypeVal.comp d.isEmbedding, ?_⟩
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hd x).mpr hx
      · intro hz
        have hzK : z ∈ K := by
          rw [hK]
          exact Or.inr hz
        let x := d.symm ⟨z, hzK⟩
        have hdx : d x = ⟨z, hzK⟩ := d.apply_symm_apply _
        refine ⟨x, ?_, ?_⟩
        · apply (hd x).mp
          simpa only [hdx] using hz
        · exact congrArg Subtype.val hdx
    have hboundaryCircle :
        ∃ e : Circle ≃ₜ {x : K // x.val ∈ c.image},
          ∀ w : Circle, (e w).val.val = c.map w := by
      let core : Circle → K := fun w => ⟨c.map w, by
        rw [hK]
        exact Or.inr ⟨w, rfl⟩⟩
      have hcoreEmbedding : Topology.IsEmbedding core :=
        c.embedded.codRestrict K (fun w => by
          rw [hK]
          exact Or.inr ⟨w, rfl⟩)
      have hcoreRange : Set.range core = {x : K | x.val ∈ c.image} := by
        ext x
        constructor
        · rintro ⟨w, rfl⟩
          exact ⟨w, rfl⟩
        · rintro ⟨w, hw⟩
          exact ⟨w, Subtype.ext hw⟩
      refine ⟨hcoreEmbedding.toHomeomorph.trans (Homeomorph.setCongr hcoreRange), ?_⟩
      intro w
      rfl
    have hfiniteInteriorAtlas :
        ∃ (b : C(Set.Ico (0 : ℝ) 1 × Circle, K)) (F : Finset K),
          Topology.IsOpenEmbedding b ∧
          (∀ w : Circle, (b (⟨0, by norm_num⟩, w)).val = c.map w) ∧
          (Set.univ : Set K) ⊆ Set.range b ∪
            ⋃ p ∈ F, Subtype.val ⁻¹'
              ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val).source ∩ U) := by
      obtain ⟨b, hb, hbcore⟩ := hboundaryCollar
      let N : K → Set K := fun p => Set.range b ∪ Subtype.val ⁻¹'
        ((chartAt (EuclideanSpace ℝ (Fin 2)) p.val).source ∩ U)
      have hNopen : ∀ p, IsOpen (N p) := by
        intro p
        exact hb.isOpen_range.union
          (((chartAt (EuclideanSpace ℝ (Fin 2)) p.val).open_source.inter hU).preimage
            continuous_subtype_val)
      have hNcover : (Set.univ : Set K) ⊆ ⋃ p, N p := by
        intro z _
        apply Set.mem_iUnion.mpr
        refine ⟨z, ?_⟩
        by_cases hz : z ∈ Set.range b
        · exact Or.inl hz
        · apply Or.inr
          refine ⟨mem_chart_source _ _, ?_⟩
          have hzK : z.val ∈ U ∪ c.image :=
            (show K ⊆ U ∪ c.image by rw [hK]) z.property
          rcases hzK with hzU | hzc
          · exact hzU
          · obtain ⟨w, hw⟩ := hzc
            apply False.elim
            apply hz
            refine ⟨(⟨0, by norm_num⟩, w), ?_⟩
            apply Subtype.ext
            exact (hbcore w).trans hw
      obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover N hNopen hNcover
      refine ⟨b, F, hb, hbcore, ?_⟩
      intro z hz
      obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp (hF hz)
      rcases hzp with hzb | hzp
      · exact Or.inl hzb
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨p, hp, hzp⟩)
    have hpositiveAmbientCharts :
        ∃ charts : ChartedSpace (EuclideanHalfSpace 2) E,
          letI := charts
          ∀ x : E, 0 < ((chartAt (EuclideanHalfSpace 2) x) x).val 0 := by
      let P := EuclideanSpace ℝ (Fin 2)
      let h : P ≃ₜ ℝ × ℝ :=
        (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans (Homeomorph.finTwoArrow (X := ℝ))
      let e : OpenPartialHomeomorph P P := h.toOpenPartialHomeomorph.trans
        ((Real.expPartialHomeomorph.prod (OpenPartialHomeomorph.refl ℝ)).trans
          h.symm.toOpenPartialHomeomorph)
      have es : e.source = univ := by simp [e]
      have et : e.target = {x : P | 0 < x 0} := by
        ext x
        simp [e, h, Homeomorph.finTwoArrow, Real.expPartialHomeomorph]
        rfl
      have ep (x : P) : 0 < e x 0 := by
        have hh := e.map_source (show x ∈ e.source by rw [es]; trivial)
        rwa [et] at hh
      let a : OpenPartialHomeomorph P (EuclideanHalfSpace 2) := {
        toFun := fun x => ⟨e x, le_of_lt (ep x)⟩
        invFun := fun y => e.symm y.val
        source := univ
        target := {y | 0 < y.val 0}
        map_source' := fun x _ => ep x
        map_target' := fun _ _ => mem_univ _
        left_inv' := fun x _ => e.left_inv (by rw [es]; trivial)
        right_inv' := by
          intro y hy
          apply Subtype.ext
          exact e.right_inv (by rwa [et])
        open_source := isOpen_univ
        open_target := isOpen_lt continuous_const
          (((continuous_apply 0).comp (EuclideanSpace.equiv (Fin 2) ℝ).continuous).comp continuous_subtype_val)
        continuousOn_toFun := by
          apply Continuous.continuousOn
          exact (continuousOn_univ.mp (by simpa only [es] using e.continuousOn)).subtype_mk _
        continuousOn_invFun := by
          apply e.symm.continuousOn.comp continuous_subtype_val.continuousOn
          intro y hy
          rwa [e.symm_source, et]
      }
      letI : ChartedSpace (EuclideanHalfSpace 2) P := {
        atlas := {a}
        chartAt := fun _ => a
        mem_chart_source := fun _ => mem_univ _
        chart_mem_atlas := fun _ => mem_singleton _
      }
      refine ⟨ChartedSpace.comp (EuclideanHalfSpace 2) P E, ?_⟩
      intro x
      change 0 < (a ((chartAt P x) x)).val 0
      exact ep ((chartAt P x) x)
    have hinteriorCharts : ∀ x : K, x.val ∈ U →
        ∃ e : OpenPartialHomeomorph K (EuclideanHalfSpace 2),
          x ∈ e.source ∧ 0 < (e x).val 0 := by
      obtain ⟨ambientCharts, hAmbientPositive⟩ := hpositiveAmbientCharts
      letI : ChartedSpace (EuclideanHalfSpace 2) E := ambientCharts
      let iUE : U → E := Subtype.val
      have hiUE : Topology.IsOpenEmbedding iUE := hU.isOpenEmbedding_subtypeVal
      let iUK : U → K := fun x => ⟨x.val, subset_closure x.property⟩
      have hiUKRange : Set.range iUK = Subtype.val ⁻¹' U := by
        ext x
        constructor
        · rintro ⟨y, rfl⟩
          exact y.property
        · intro hx
          exact ⟨⟨x.val, hx⟩, rfl⟩
      have hiUK : Topology.IsOpenEmbedding iUK := ⟨
        Topology.IsEmbedding.subtypeVal.codRestrict K
          (fun x => subset_closure x.property), by
        rw [hiUKRange]
        exact hU.preimage continuous_subtype_val⟩
      letI : Nonempty U := hUconn.nonempty.to_subtype
      intro x hxU
      let y : U := ⟨x.val, hxU⟩
      let e := (hiUE.toOpenPartialHomeomorph iUE).trans
        (chartAt (EuclideanHalfSpace 2) x.val)
      have hy : y ∈ e.source := by
        refine ⟨Set.mem_univ _, ?_⟩
        change x.val ∈ (chartAt (EuclideanHalfSpace 2) x.val).source
        exact mem_chart_source _ _
      refine ⟨e.lift_openEmbedding hiUK, ⟨y, hy, rfl⟩, ?_⟩
      change 0 < ((e.lift_openEmbedding hiUK) (iUK y)).val 0
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      change 0 < ((chartAt (EuclideanHalfSpace 2) x.val) x.val).val 0
      exact hAmbientPositive x.val
    have hboundaryCharts : ∀ (b : C(Set.Ico (0 : ℝ) 1 × Circle, K)),
        Topology.IsOpenEmbedding b → ∀ w : Circle,
          ∃ e : OpenPartialHomeomorph K (EuclideanHalfSpace 2),
            b (⟨0, by norm_num⟩, w) ∈ e.source ∧
            (e (b (⟨0, by norm_num⟩, w))).val 0 = 0 := by
      intro b hb
      classical
      let P1 := EuclideanSpace ℝ (Fin 1)
      let P2 := EuclideanSpace ℝ (Fin 2)
      let e1 : P1 ≃ₜ ℝ := (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans
        (Homeomorph.funUnique (Fin 1) ℝ)
      let e2 : P2 ≃ₜ ℝ × ℝ := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
        (Homeomorph.finTwoArrow (X := ℝ))
      let h1 : EuclideanHalfSpace 1 ≃ₜ Set.Ici (0 : ℝ) :=
        e1.subtype (fun x => by rfl)
      let h2 : EuclideanHalfSpace 2 ≃ₜ {p : ℝ × ℝ // 0 ≤ p.1} :=
        e2.subtype (fun x => by rfl)
      let hproduct : (Set.Ici (0 : ℝ) × ℝ) ≃ₜ {p : ℝ × ℝ // 0 ≤ p.1} := {
        toFun := fun p => ⟨(p.1.val, p.2), p.1.property⟩
        invFun := fun p => (⟨p.val.1, p.property⟩, p.val.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      let eCircle : EuclideanSpace ℝ (Fin 1) ≃ₜ ℝ :=
        (EuclideanSpace.equiv (Fin 1) ℝ).toHomeomorph.trans (Homeomorph.funUnique (Fin 1) ℝ)
      let model := ((Homeomorph.refl (EuclideanHalfSpace 1)).prodCongr eCircle).trans
        ((h1.prodCongr (Homeomorph.refl ℝ)).trans (hproduct.trans h2.symm))
      let H := Set.Ico (0 : ℝ) 1
      let J := Set.Icc (0 : ℝ) 1
      let i : H → J := Set.inclusion Set.Ico_subset_Icc_self
      have hiRange : Set.range i = {t : J | t.val < 1} := by
        ext t
        constructor
        · rintro ⟨x, rfl⟩
          exact x.property.2
        · intro ht
          exact ⟨⟨t.val, ⟨t.property.1, ht⟩⟩, rfl⟩
      have hi : Topology.IsOpenEmbedding i := ⟨Topology.IsEmbedding.inclusion _, by
        rw [hiRange]
        exact isOpen_lt continuous_subtype_val continuous_const⟩
      letI : Nonempty H := ⟨⟨0, by norm_num [H]⟩⟩
      let a := (hi.toOpenPartialHomeomorph i).prod (OpenPartialHomeomorph.refl Circle)
      intro w
      let p : H × Circle := (⟨0, by norm_num [H]⟩, w)
      let localChart := (a.trans
        (chartAt (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 1))) (i p.1, p.2))).trans
          model.toOpenPartialHomeomorph
      have hp : p ∈ localChart.source := by
        refine ⟨?_, ?_⟩
        · refine ⟨?_, ?_⟩
          · exact ⟨Set.mem_univ _, Set.mem_univ _⟩
          · change (i p.1, p.2) ∈
              (chartAt (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 1))) (i p.1, p.2)).source
            exact mem_chart_source _ _
        · exact Set.mem_univ _
      refine ⟨localChart.lift_openEmbedding hb, ⟨p, hp, rfl⟩, ?_⟩
      change ((localChart.lift_openEmbedding hb) (b p)).val 0 = 0
      rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
      simp [localChart, model, a, p, i, H, J, eCircle, h1, h2, hproduct, e1, e2,
        chartAt, prodChartedSpace, instIccChartedSpace, IccLeftChart,
        Homeomorph.subtype, Homeomorph.prodCongr, Homeomorph.finTwoArrow,
        Homeomorph.funUnique]
      rfl
    have hcutHalfSpaceManifold :
        ∃ charts : ChartedSpace (EuclideanHalfSpace 2) K,
          letI := charts
          IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 K := by
      obtain ⟨b, hb, hbcore⟩ := hboundaryCollar
      have hLocal : ∀ x : K,
          ∃ e : OpenPartialHomeomorph K (EuclideanHalfSpace 2), x ∈ e.source := by
        intro x
        by_cases hxU : x.val ∈ U
        · obtain ⟨e, he, hpositive⟩ := hinteriorCharts x hxU
          exact ⟨e, he⟩
        · have hxc : x.val ∈ c.image := by
            have hxK : x.val ∈ U ∪ c.image :=
              (show K ⊆ U ∪ c.image by rw [hK]) x.property
            exact hxK.resolve_left hxU
          obtain ⟨w, hw⟩ := hxc
          obtain ⟨e, he, hzero⟩ := hboundaryCharts b hb w
          refine ⟨e, ?_⟩
          have hx : b (⟨0, by norm_num⟩, w) = x :=
            Subtype.ext ((hbcore w).trans hw)
          exact hx ▸ he
      choose localChart hSource using hLocal
      let charts : ChartedSpace (EuclideanHalfSpace 2) K := {
        atlas := Set.range localChart
        chartAt := localChart
        mem_chart_source := hSource
        chart_mem_atlas := Set.mem_range_self }
      refine ⟨charts, ?_⟩
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      infer_instance
    have hliteralInteriorIntrinsic :
        ∀ charts : ChartedSpace (EuclideanHalfSpace 2) K,
          letI := charts
          ∀ x : K, x.val ∈ U →
            (modelWithCornersEuclideanHalfSpace 2).IsInteriorPoint x := by
      intro charts
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      intro x hxU
      obtain ⟨e, he, hpositive⟩ := hinteriorCharts x hxU
      apply (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
        (modelWithCornersEuclideanHalfSpace 2) he).mpr
      rw [interior_range_modelWithCornersEuclideanHalfSpace]
      exact hpositive
    have hliteralBoundaryIntrinsic :
        ∀ charts : ChartedSpace (EuclideanHalfSpace 2) K,
          letI := charts
          ∀ x : K, x.val ∈ c.image →
            (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint x := by
      intro charts
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      intro x hxc
      obtain ⟨b, hb, hbcore⟩ := hboundaryCollar
      obtain ⟨w, hw⟩ := hxc
      obtain ⟨e, he, hzero⟩ := hboundaryCharts b hb w
      have hx : b (⟨0, by norm_num⟩, w) = x :=
        Subtype.ext ((hbcore w).trans hw)
      have hsource : x ∈ e.source := hx ▸ he
      apply (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isBoundaryPoint_iff_any_chart
        (modelWithCornersEuclideanHalfSpace 2) hsource).mpr
      rw [frontier_range_modelWithCornersEuclideanHalfSpace]
      change 0 = (e x).val 0
      exact (hx ▸ hzero).symm
    have hactualIntrinsicBoundary :
        ∀ charts : ChartedSpace (EuclideanHalfSpace 2) K,
          letI := charts
          (modelWithCornersEuclideanHalfSpace 2).boundary K =
            Subtype.val ⁻¹' c.image := by
      intro charts
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      ext x
      constructor
      · intro hx
        have hxK : x.val ∈ U ∪ c.image :=
          (show K ⊆ U ∪ c.image by rw [hK]) x.property
        rcases hxK with hxU | hxc
        · exact False.elim (((modelWithCornersEuclideanHalfSpace 2).isInteriorPoint_iff_not_isBoundaryPoint x).mp
            (hliteralInteriorIntrinsic charts x hxU) hx)
        · exact hxc
      · exact hliteralBoundaryIntrinsic charts x
    have hactualIntrinsicBoundaryCircle :
        ∀ charts : ChartedSpace (EuclideanHalfSpace 2) K,
          letI := charts
          Nonempty (((modelWithCornersEuclideanHalfSpace 2).boundary K) ≃ₜ Circle) := by
      intro charts
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      obtain ⟨e, he⟩ := hboundaryCircle
      exact ⟨(Homeomorph.setCongr (hactualIntrinsicBoundary charts)).trans e.symm⟩
    have hactualBoundaryTransport :
        ∀ (X : Type) [TopologicalSpace X]
          [ChartedSpace (EuclideanHalfSpace 2) X]
          (charts : ChartedSpace (EuclideanHalfSpace 2) K) (e : K ≃ₜ X),
          letI := charts
          ∀ x : K, (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint (e x) ↔
            x.val ∈ c.image := by
      intro X _ _ charts e
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      intro x
      let a := chartAt (EuclideanHalfSpace 2) (e x)
      let b := e.toOpenPartialHomeomorph.trans a
      have hb : x ∈ b.source := ⟨Set.mem_univ _, mem_chart_source _ _⟩
      have hKboundary :=
        LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isBoundaryPoint_iff_any_chart
          (modelWithCornersEuclideanHalfSpace 2) hb
      have hXboundary :=
        LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isBoundaryPoint_iff_any_chart
          (modelWithCornersEuclideanHalfSpace 2) (mem_chart_source (EuclideanHalfSpace 2) (e x))
      have hpoint : b x = a (e x) := rfl
      rw [hpoint] at hKboundary
      have hliteral : (modelWithCornersEuclideanHalfSpace 2).IsBoundaryPoint x ↔
          x.val ∈ c.image := by
        change x ∈ (modelWithCornersEuclideanHalfSpace 2).boundary K ↔ _
        rw [hactualIntrinsicBoundary charts]
        rfl
      exact hXboundary.trans (hKboundary.symm.trans hliteral)
    have hsingleBoundaryFromComponents : ∀ n : ℕ,
        letI : TopologicalSpace (Fin n) := ⊥
        Nonempty ((Fin n × Circle) ≃ₜ Circle) → n = 1 := by
      intro n
      letI : TopologicalSpace (Fin n) := ⊥
      letI : DiscreteTopology (Fin n) := ⟨rfl⟩
      rintro ⟨e⟩
      letI : ConnectedSpace (Fin n × Circle) := e.connectedSpace_iff.mpr inferInstance
      have hfst : Function.Surjective (Prod.fst : Fin n × Circle → Fin n) :=
        fun i => ⟨(i, 1), rfl⟩
      letI : ConnectedSpace (Fin n) := hfst.connectedSpace continuous_fst
      letI : Subsingleton (Fin n) := PreconnectedSpace.trivial_of_discrete
      have hnle : n ≤ 1 := by simpa using ((Fintype.card_le_one_iff_subsingleton (α := Fin n)).mpr inferInstance)
      have hnpos : 0 < n := by
        have h := (e.symm 1).1.isLt
        omega
      omega
    have hnormalFormBoundaryCountConsumer :
        ∀ (p n : ℕ)
          (modelCharts : ChartedSpace (EuclideanHalfSpace 2) (Quot (OrientableRel p n)))
          (e : K ≃ₜ Quot (OrientableRel p n)),
          letI := modelCharts
          letI : TopologicalSpace (Fin n) := ⊥
          Nonempty (((modelWithCornersEuclideanHalfSpace 2).boundary
            (Quot (OrientableRel p n))) ≃ₜ (Fin n × Circle)) → n = 1 := by
      intro p n modelCharts e
      letI : ChartedSpace (EuclideanHalfSpace 2) (Quot (OrientableRel p n)) := modelCharts
      letI : TopologicalSpace (Fin n) := ⊥
      rintro ⟨hmodel⟩
      obtain ⟨cutCharts, hManifold⟩ := hcutHalfSpaceManifold
      letI : ChartedSpace (EuclideanHalfSpace 2) K := cutCharts
      obtain ⟨hCircle, hCircleCore⟩ := hboundaryCircle
      let hBoundary : {x : K // x.val ∈ c.image} ≃ₜ
          ((modelWithCornersEuclideanHalfSpace 2).boundary (Quot (OrientableRel p n))) :=
        e.subtype (fun x => (hactualBoundaryTransport (Quot (OrientableRel p n)) cutCharts e x).symm)
      exact hsingleBoundaryFromComponents n
        ⟨hmodel.symm.trans (hBoundary.symm.trans hCircle.symm)⟩
    have hnormalFormLiteralBoundaryConsumer :
        ∀ (p : ℕ)
          (modelCharts : ChartedSpace (EuclideanHalfSpace 2) (Quot (OrientableRel p 1)))
          (e : K ≃ₜ Quot (OrientableRel p 1)),
          letI := modelCharts
          ((modelWithCornersEuclideanHalfSpace 2).boundary (Quot (OrientableRel p 1)) =
            ActualOneBoundaryOrientableBoundary p) →
          ∀ x : K, e x ∈ ActualOneBoundaryOrientableBoundary p ↔ x.val ∈ c.image := by
      intro p modelCharts e
      letI : ChartedSpace (EuclideanHalfSpace 2) (Quot (OrientableRel p 1)) := modelCharts
      intro hrawBoundary x
      obtain ⟨cutCharts, hManifold⟩ := hcutHalfSpaceManifold
      letI : ChartedSpace (EuclideanHalfSpace 2) K := cutCharts
      rw [← hrawBoundary]
      exact hactualBoundaryTransport (Quot (OrientableRel p 1)) cutCharts e x
    have hnoAmbientLocalReflection : ∀ x : E,
        CurveComplex.GenusOrientationCandidate.LocalReflectionWitness x → False := by
      intro x W
      exact CurveComplex.GenusOrientationCandidate.no_local_reflection_witness
        2 hE x
        (CurveComplex.GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W
    have hnonorientableModelAmbientEmbedding :
        ∀ (p n : ℕ) (e : K ≃ₜ Quot (NonOrientableRel p n)),
          Topology.IsEmbedding (fun z => (e.symm z).val) := by
      intro p n e
      exact Topology.IsEmbedding.subtypeVal.comp e.symm.isEmbedding
    have hcrosscapSquareStripAmbientConsumer :
        ∀ (p n : ℕ) (e : K ≃ₜ Quot (NonOrientableRel p n))
          (ε : ℝ) (hε : 0 < ε)
          (square : Metric.closedBall ((0,0) : ℝ × ℝ) ε → Quot (NonOrientableRel p n))
          (band : unitInterval × CurveComplex.BandWidth → Quot (NonOrientableRel p n)),
          Topology.IsEmbedding square → Topology.IsEmbedding band →
          (∀ t, band (0,t) = square (CurveComplex.squarePort ε hε 2 t)) →
          (∀ t, band (1,t) = square (CurveComplex.squarePort ε hε 0
            (CurveComplex.flipBandWidth true t))) →
          Set.range band ∩ Set.range square =
            Set.range (fun t => square (CurveComplex.squarePort ε hε 2 t)) ∪
            Set.range (fun t => square (CurveComplex.squarePort ε hε 0 t)) →
          ∃ (squareE : Metric.closedBall ((0,0) : ℝ × ℝ) ε → E)
            (bandE : unitInterval × CurveComplex.BandWidth → E),
            Topology.IsEmbedding squareE ∧ Topology.IsEmbedding bandE ∧
            (∀ t, bandE (0,t) = squareE (CurveComplex.squarePort ε hε 2 t)) ∧
            (∀ t, bandE (1,t) = squareE (CurveComplex.squarePort ε hε 0
              (CurveComplex.flipBandWidth true t))) ∧
            Set.range bandE ∩ Set.range squareE =
              Set.range (fun t => squareE (CurveComplex.squarePort ε hε 2 t)) ∪
              Set.range (fun t => squareE (CurveComplex.squarePort ε hε 0 t)) := by
      intro p n e ε hε square band hs hb hbottom htop hmeet
      let f : Quot (NonOrientableRel p n) → E := fun z => (e.symm z).val
      have hf : Topology.IsEmbedding f := hnonorientableModelAmbientEmbedding p n e
      refine ⟨f ∘ square, f ∘ band, hf.comp hs, hf.comp hb, ?_, ?_, ?_⟩
      · intro t
        exact congrArg f (hbottom t)
      · intro t
        exact congrArg f (htop t)
      · change Set.range (f ∘ band) ∩ Set.range (f ∘ square) =
          Set.range (f ∘ (fun t => square (CurveComplex.squarePort ε hε 2 t))) ∪
          Set.range (f ∘ (fun t => square (CurveComplex.squarePort ε hε 0 t)))
        simp only [Set.range_comp]
        rw [← Set.image_inter hf.injective, hmeet, Set.image_union]
    have hcutFiniteTriangulation : Nonempty (GeometricTriangulation K) := by
      obtain ⟨charts, hManifold⟩ := hcutHalfSpaceManifold
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      letI : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 K := hManifold
      letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKconnected
      exact moise_triangulation K
    have hactualGenericNormalForm :
        Nonempty (K ≃ₜ SphereRepresentative) ∨
          ∃ p n,
            ((1 ≤ p ∨ 1 ≤ n) ∧ Nonempty (K ≃ₜ Quot (OrientableRel p n))) ∨
              (1 ≤ p ∧ Nonempty (K ≃ₜ Quot (NonOrientableRel p n))) := by
      obtain ⟨charts, hManifold⟩ := hcutHalfSpaceManifold
      letI : ChartedSpace (EuclideanHalfSpace 2) K := charts
      letI : IsManifold (modelWithCornersEuclideanHalfSpace 2) 0 K := hManifold
      letI : ConnectedSpace K := isConnected_iff_connectedSpace.mp hKconnected
      exact classification_of_surfaces K
    have hnoSphere : ¬ Nonempty (K ≃ₜ SphereRepresentative) := by
      rintro ⟨e⟩
      let x : K := ⟨c.map 1, by
        rw [hK]
        exact Or.inr ⟨1, rfl⟩⟩
      let q : SphereRepresentative := e x
      let a := chartAt (EuclideanSpace ℝ (Fin 2)) q
      let f : EuclideanSpace ℝ (Fin 2) → E := fun y => (e.symm (a.symm y)).val
      have hf : ContinuousOn f a.target :=
        (continuous_subtype_val.comp e.symm.continuous).continuousOn.comp
          a.symm.continuousOn (fun _ h => a.symm.map_source h)
      have hi : Set.InjOn f a.target := by
        intro y hy z hz h
        apply a.symm.injOn hy hz
        exact e.symm.injective (Subtype.ext h)
      have hopen : IsOpen (f '' a.target) :=
        CurveComplex.surface_invariance_of_domain_probe f a.target a.open_target hf hi
      have hsubset : f '' a.target ⊆ K := by
        rintro z ⟨y, hy, rfl⟩
        exact (e.symm (a.symm y)).property
      have hvalue : f (a q) = c.map 1 := by
        change (e.symm (a.symm (a (e x)))).val = c.map 1
        rw [a.left_inv (mem_chart_source _ _), e.symm_apply_apply]
      have hcoreInterior : c.map 1 ∈ interior K :=
        (hopen.subset_interior_iff.mpr hsubset)
          ⟨a q, a.map_source (mem_chart_source _ _), hvalue⟩
      have hcoreU : c.map 1 ∈ U := hKinterior ▸ hcoreInterior
      exact hUsub hcoreU ⟨1, rfl⟩
    -- The actual compact half-space manifold and actual finite triangulation
    -- are now constructed. This is the boundary/orientation specialization of
    -- the existing normal-form package, not a duplicate global classification.
    have hboundaryNormalForm :
        ∃ (p : ℕ) (e : K ≃ₜ Quot (OrientableRel p 1)),
          ∀ x : K,
            e x ∈ ActualOneBoundaryOrientableBoundary p ↔ x.val ∈ c.image := by
      rcases hactualGenericNormalForm with hsphere | ⟨p, n, hbranch⟩
      · exact (hnoSphere hsphere).elim
      · rcases hbranch with ⟨hadmissible, ⟨e⟩⟩ | hnonorientable
        · obtain ⟨cutCharts, hManifold⟩ := hcutHalfSpaceManifold
          letI : ChartedSpace (EuclideanHalfSpace 2) K := cutCharts
          let modelCharts : ChartedSpace (EuclideanHalfSpace 2)
              (Quot (OrientableRel p n)) := e.chartedSpace
          -- Exact approved atlas-relative raw-boundary producer, owned separately.
          have hrawBoundary :
              letI := modelCharts
              letI : TopologicalSpace (Fin n) := ⊥
              Nonempty (((modelWithCornersEuclideanHalfSpace 2).boundary
                (Quot (OrientableRel p n))) ≃ₜ (Fin n × Circle)) ∧
              (∀ hn : n = 1,
                (modelWithCornersEuclideanHalfSpace 2).boundary
                    (Quot (OrientableRel p n)) =
                  hn.symm ▸ ActualOneBoundaryOrientableBoundary p) := by
            exact actual_orientable_normal_form_intrinsic_boundary_components_of_atlas
              p n hadmissible modelCharts
          have hn : n = 1 :=
            hnormalFormBoundaryCountConsumer p n modelCharts e hrawBoundary.1
          subst n
          exact ⟨p, e, hnormalFormLiteralBoundaryConsumer p modelCharts e
            (hrawBoundary.2 rfl)⟩
        · obtain ⟨hp, ⟨e⟩⟩ := hnonorientable
          -- Exact approved literal raw-crosscap producer, owned separately.
          have hrawCrosscap :
              ∃ (ε : ℝ) (hε : 0 < ε)
                (square : Metric.closedBall ((0,0) : ℝ × ℝ) ε →
                  Quot (NonOrientableRel p n))
                (band : unitInterval × CurveComplex.BandWidth →
                  Quot (NonOrientableRel p n)),
                Topology.IsEmbedding square ∧ Topology.IsEmbedding band ∧
                (∀ t, band (0,t) = square (CurveComplex.squarePort ε hε 2 t)) ∧
                (∀ t, band (1,t) = square (CurveComplex.squarePort ε hε 0
                  (CurveComplex.flipBandWidth true t))) ∧
                Set.range band ∩ Set.range square =
                  Set.range (fun t => square (CurveComplex.squarePort ε hε 2 t)) ∪
                  Set.range (fun t => square (CurveComplex.squarePort ε hε 0 t)) := by
            exact actual_nonorientable_normal_form_first_crosscap_square_strip p n
              (by omega)
          obtain ⟨ε, hε, square, band, hs, hb, hbottom, htop, hmeet⟩ := hrawCrosscap
          obtain ⟨squareE, bandE, hsE, hbE, hbottomE, htopE, hmeetE⟩ :=
            hcrosscapSquareStripAmbientConsumer p n e ε hε square band
              hs hb hbottom htop hmeet
          obtain ⟨x, ⟨hreflection⟩⟩ :=
            CurveComplex.LocalSurgery.actual_square_twisted_band_produces_local_reflection
              E ε hε squareE hsE bandE hbE hbottomE htopE hmeetE
          exact (hnoAmbientLocalReflection x hreflection).elim
    exact hboundaryNormalForm
  have hpositive (E : Type) [TopologicalSpace E]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
      (hE : IsGenus E 2) (c : Curve E) (hc : Essential c)
      (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
      (hUconn : IsConnected U) (hVconn : IsConnected V)
      (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
      (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image) :
      ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
        Nonempty (U ≃ₜ ActualOneBoundaryOrientableOpenModel p) ∧
        Nonempty (V ≃ₜ ActualOneBoundaryOrientableOpenModel q) := by
    classical
    have hside : ∀ (U V : Set E), IsOpen U → IsOpen V →
        IsConnected U → IsConnected V → Disjoint U V →
        U ∪ V = c.imageᶜ → frontier U = c.image → frontier V = c.image →
        ∃ p : ℕ, 0 < p ∧ Nonempty (U ≃ₜ ActualOneBoundaryOrientableOpenModel p) := by
      intro U V hU hV hUconn hVconn hUV hcover hfrontU hfrontV
      let K := closure U
      have hK : K = U ∪ c.image :=
        (closure_eq_self_union_frontier U).trans (by rw [hfrontU])
      have hUsub : U ⊆ c.imageᶜ := by
        intro z hz
        rw [← hcover]
        exact Or.inl hz
      obtain ⟨p, e, hboundary⟩ :=
        hcompact E hE c hc U V
          hU hV hUconn hVconn hUV hcover hfrontU hfrontV
      have hp : 0 < p := by
        by_contra hn
        have hpzero : p = 0 := by omega
        subst p
        obtain ⟨d, hd⟩ := actual_zero_handle_one_boundary_model_closed_disc
        let f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E) :=
          ⟨fun x => (e.symm (d x)).val,
            continuous_subtype_val.comp (e.symm.continuous.comp d.continuous)⟩
        apply hc
        refine ⟨f, Topology.IsEmbedding.subtypeVal.comp
          (e.symm.isEmbedding.comp d.isEmbedding), ?_⟩
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          apply (hboundary (e.symm (d x))).mp
          simpa only [e.apply_symm_apply] using (hd x).mpr hx
        · intro hz
          have hzK : z ∈ closure U := by
            change z ∈ K
            rw [hK]
            exact Or.inr hz
          let x := d.symm (e ⟨z, hzK⟩)
          have hdx : d x = e ⟨z, hzK⟩ := d.apply_symm_apply _
          refine ⟨x, ?_, ?_⟩
          · apply (hd x).mp
            rw [hdx]
            exact (hboundary ⟨z, hzK⟩).mpr hz
          · change (e.symm (d x)).val = z
            rw [hdx, e.symm_apply_apply]
      let eInside : U ≃ₜ {x : K // x.val ∉ c.image} := {
        toFun := fun x => ⟨⟨x.val, subset_closure x.property⟩, hUsub x.property⟩
        invFun := fun x => ⟨x.val.val,
          ((show K ⊆ U ∪ c.image by rw [hK]) x.val.property).resolve_right x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      exact ⟨p, hp, ⟨eInside.trans
        (e.subtype (fun x => (not_congr (hboundary x)).symm))⟩⟩
    obtain ⟨p, hp, ep⟩ := hside U V hU hV hUconn hVconn hUV hcover hfrontU hfrontV
    obtain ⟨q, hq, eq⟩ := hside V U hV hU hVconn hUconn hUV.symm
      (by rw [union_comm]; exact hcover) hfrontV hfrontU
    exact ⟨p, q, hp, hq, ep, eq⟩
  have hhomology (E : Type) [TopologicalSpace E]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
      (hE : IsGenus E 2) (c : Curve E) (hc : Essential c)
      (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
      (hUconn : IsConnected U) (hVconn : IsConnected V)
      (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
      (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image) :
      Nonempty (integralHomology U 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
      Nonempty (integralHomology V 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) := by
    have hConsumer (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
      (c : Curve S) (hc : Essential c)
      (U V : Set S) (hU : IsOpen U) (hV : IsOpen V)
      (hUC : IsConnected U) (hVC : IsConnected V)
      (hUV : Disjoint U V) (hcover : U ∪ V=c.imageᶜ)
      (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
      (eU : H U 1 ≅ ModuleCat.of ℤ (Fin (2*p) → ℤ))
      (eV : H V 1 ≅ ModuleCat.of ℤ (Fin (2*q) → ℤ)) :
      Nonempty (H U 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ)) ∧
      Nonempty (H V 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ))  := by
      classical
      have hSides (S : Type) [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
        (c : Curve S) (L R : Set S) (hLO : IsOpen L) (hRO : IsOpen R)
        (hLC : IsConnected L) (hRC : IsConnected R) (hdis : Disjoint L R)
        (hcover : L ∪ R=c.imageᶜ)
        (e : C(Ioo (-1:ℝ) 1 × Circle,S)) (he : IsOpenEmbedding e)
        (hcore : ∀ w : Circle, e (⟨0,by norm_num⟩,w)=c.map w) :
        ∃ N : Set S, IsOpen N ∧ (L ∪ N) ∪ (R ∪ N)=univ ∧
          (L ∪ N) ∩ (R ∪ N)=N ∧
          homologyInclusion S (L ∪ N) 2=0 ∧ homologyInclusion S (R ∪ N) 2=0 ∧
          Nonempty (↥(L ∪ N) ≃ₜ L) ∧ Nonempty (↥(R ∪ N) ≃ₜ R) ∧
          N=e '' {z : Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Ioo (-1/2:ℝ) (1/2)}  := by
        classical
        let : ClosedSurface S := Classical.choice hS.2.1
        have hLQ : L ⊆ c.imageᶜ := by intro x hx; rw [←hcover];exact Or.inl hx
        have hRQ : R ⊆ c.imageᶜ := by intro x hx; rw [←hcover];exact Or.inr hx
        let pos : Set S := Set.range (fun z : Set.Ioo (0:ℝ) 1 × Circle =>
          e (⟨z.1.val,⟨by linarith [z.1.property.1],z.1.property.2⟩⟩,z.2))
        let neg : Set S := Set.range (fun z : Set.Ioo (-1:ℝ) 0 × Circle =>
          e (⟨z.1.val,⟨z.1.property.1,by linarith [z.1.property.2]⟩⟩,z.2))
        let : ConnectedSpace (Set.Ioo (0:ℝ) 1) := isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
        let : ConnectedSpace (Set.Ioo (-1:ℝ) 0) := isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
        have hpC : IsConnected pos := isConnected_range (by fun_prop)
        have hnC : IsConnected neg := isConnected_range (by fun_prop)
        have haxis (z : Set.Ioo (-1:ℝ) 1 × Circle) : e z ∈ c.image ↔ z.1.val=0 := by
          constructor
          · rintro ⟨w,hw⟩
            have hh := he.injective ((hcore w).trans hw)
            exact (congrArg (fun p => p.1.val) hh).symm
          · intro hz
            refine ⟨z.2,?_⟩
            rw [←hcore]
            apply congrArg e
            exact Prod.ext (Subtype.ext hz.symm) rfl
        have hpQ : pos ⊆ c.imageᶜ := by
          rintro x ⟨z,rfl⟩ hh
          have hz := (haxis _).mp hh
          exact (ne_of_gt z.1.property.1) hz
        have hnQ : neg ⊆ c.imageᶜ := by
          rintro x ⟨z,rfl⟩ hh
          have hz := (haxis _).mp hh
          exact (ne_of_lt z.1.property.2) hz
        have hpLR : pos ⊆ L ∨ pos ⊆ R :=
          hpC.isPreconnected.subset_or_subset hLO hRO hdis (hcover.symm ▸ hpQ)
        have hnLR : neg ⊆ L ∨ neg ⊆ R :=
          hnC.isPreconnected.subset_or_subset hLO hRO hdis (hcover.symm ▸ hnQ)
        have hrange : Set.range e ⊆ pos ∪ neg ∪ c.image := by
          rintro x ⟨z,rfl⟩
          rcases lt_trichotomy 0 z.1.val with hz|hz|hz
          · exact Or.inl (Or.inl ⟨(⟨z.1.val,⟨hz,z.1.property.2⟩⟩,z.2),rfl⟩)
          · exact Or.inr ((haxis z).mpr hz.symm)
          · exact Or.inl (Or.inr ⟨(⟨z.1.val,⟨z.1.property.1,hz⟩⟩,z.2),rfl⟩)
        have hcoreRange : c.image ⊆ Set.range e := by
          rintro x ⟨w,rfl⟩
          exact ⟨(⟨0,by norm_num⟩,w),hcore w⟩
        have hnotboth (A B : Set S) (hAO : IsOpen A) (hBO : IsOpen B)
            (hBne : B.Nonempty) (hD : Disjoint A B) (hAB : A ∪ B=c.imageᶜ)
            (hP : pos ⊆ A) (hN : neg ⊆ A) : False := by
          have hrr : Set.range e ⊆ A ∪ c.image := by
            intro x hx
            rcases hrange hx with (hp|hn)|hc
            · exact Or.inl (hP hp)
            · exact Or.inl (hN hn)
            · exact Or.inr hc
          have hEq : A ∪ c.image=A ∪ Set.range e := by
            apply Set.Subset.antisymm
            · exact Set.union_subset_union_right A hcoreRange
            · exact Set.union_subset (Set.subset_union_left) hrr
          have hACopen : IsOpen (A ∪ c.image) := hEq ▸ hAO.union he.isOpen_range
          have hBQ : B ⊆ c.imageᶜ := by intro x hx; rw [←hAB];exact Or.inr hx
          have hd : Disjoint (A ∪ c.image) B := by
            rw [Set.disjoint_left]
            rintro x (hx|hx) hy
            · exact Set.disjoint_left.mp hD hx hy
            · exact hBQ hy hx
          have hcu : Set.univ ⊆ (A ∪ c.image) ∪ B := by
            intro x _
            by_cases hx : x ∈ c.image
            · exact Or.inl (Or.inr hx)
            · have hh : x ∈ A ∪ B := hAB ▸ hx
              rcases hh with ha|hb
              · exact Or.inl (Or.inl ha)
              · exact Or.inr hb
          have hall : Set.univ ⊆ A ∪ c.image :=
            isPreconnected_univ.subset_left_of_subset_union hACopen hBO hd hcu
              ⟨c.map 1,Set.mem_univ _,Or.inr ⟨1,rfl⟩⟩
          obtain ⟨b,hb⟩ := hBne
          exact Set.disjoint_left.mp hd (hall (Set.mem_univ b)) hb
        have hopposite : (pos ⊆ L ∧ neg ⊆ R) ∨ (pos ⊆ R ∧ neg ⊆ L) := by
          rcases hpLR with hp|hp <;> rcases hnLR with hn|hn
          · exact (hnotboth L R hLO hRO hRC.nonempty hdis hcover hp hn).elim
          · exact Or.inl ⟨hp,hn⟩
          · exact Or.inr ⟨hp,hn⟩
          · exact (hnotboth R L hRO hLO hLC.nonempty hdis.symm (Set.union_comm _ _ ▸ hcover) hp hn).elim
        let W : Set (Set.Ioo (-1:ℝ) 1 × Circle) := {z | z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)}
        let N : Set S := e '' W
        have hNO : IsOpen N := he.isOpenMap _
          (isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_fst))
        have hcoreN : c.image ⊆ N := by
          rintro x ⟨w,rfl⟩
          exact ⟨(⟨0,by norm_num⟩,w),by norm_num [W],hcore w⟩
        let U := L ∪ N
        let V := R ∪ N
        have hUV : U ∪ V=Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          by_cases hx : x ∈ c.image
          · exact Or.inl (Or.inr (hcoreN hx))
          · have hh : x ∈ L ∪ R := hcover ▸ hx
            rcases hh with hL|hR
            · exact Or.inl (Or.inl hL)
            · exact Or.inr (Or.inl hR)
        have hI : U ∩ V=N := by
          ext x
          constructor
          · rintro ⟨hx|hx,hy|hy⟩
            · exact (Set.disjoint_left.mp hdis hx hy).elim
            · exact hy
            · exact hx
            · exact hx
          · intro hx
            exact ⟨Or.inr hx,Or.inr hx⟩
        have hproper (A : Set S) (x : S) (hx : x ∉ A) : homologyInclusion S A 2 = 0 := by
          let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
            (ModuleCat.of ℤ ℤ)
          let j : TopCat.of A ⟶ TopCat.of ↥({x}ᶜ : Set S) :=
            TopCat.ofHom ⟨fun a => ⟨a.val,fun he => hx (he ▸ a.property)⟩,
              continuous_subtype_val.subtype_mk _⟩
          have hh : j ≫ pairInclusion S ({x}ᶜ : Set S) = pairInclusion S A := by ext a; rfl
          change F.map (pairInclusion S A) = 0
          rw [← hh,F.map_comp]
          change F.map j ≫ homologyInclusion S ({x}ᶜ : Set S) 2 = 0
          rw [GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x,
            CategoryTheory.Limits.comp_zero]
        let p : S := e (⟨3/4,by norm_num⟩,1)
        let n : S := e (⟨-3/4,by norm_num⟩,1)
        have hp : p ∈ pos := ⟨(⟨3/4,by norm_num⟩,1),rfl⟩
        have hn : n ∈ neg := ⟨(⟨-3/4,by norm_num⟩,1),rfl⟩
        have hpN : p ∉ N := by
          rintro ⟨z,hz,hh⟩
          have heq := congrArg (fun z : Set.Ioo (-1:ℝ) 1 × Circle => z.1.val) (he.injective hh)
          have hhi := hz.2
          dsimp [p] at heq
          linarith
        have hnN : n ∉ N := by
          rintro ⟨z,hz,hh⟩
          have heq := congrArg (fun z : Set.Ioo (-1:ℝ) 1 × Circle => z.1.val) (he.injective hh)
          have hlo := hz.1
          dsimp [n] at heq
          linarith
        have hfinish (x y : S) (hx : x ∈ L) (hy : y ∈ R) (hxN : x ∉ N) (hyN : y ∉ N) :
            homologyInclusion S U 2=0 ∧ homologyInclusion S V 2=0 := by
          constructor
          · apply hproper U y
            rintro (hyL|hyN')
            · exact Set.disjoint_left.mp hdis hyL hy
            · exact hyN hyN'
          · apply hproper V x
            rintro (hxR|hxN')
            · exact Set.disjoint_left.mp hdis hx hxR
            · exact hxN hxN'
        have hzero : homologyInclusion S U 2=0 ∧ homologyInclusion S V 2=0 := by
          rcases hopposite with ⟨hP,hN⟩|⟨hP,hN⟩
          · exact hfinish p n (hP hp) (hN hn) hpN hnN
          · exact hfinish n p (hN hn) (hP hp) hnN hpN
        have hThicken {E : Type} [TopologicalSpace E] [T2Space E]
          (e : C(Ioo (-1:ℝ) 1 × Circle,E)) (he : IsOpenEmbedding e)
          (U : Set E) (hpos : ∀ z, e z ∈ U ↔ 0 < z.1.val) :
          ∃ F : E ≃ₜ E, F ⁻¹' U = U ∪
            e '' {z : Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Ioo (-1/2:ℝ) (1/2)}  := by
          classical
          have hWidth : ∃ φ : Icc (-3/4:ℝ) (3/4) ≃ₜ Icc (-3/4:ℝ) (3/4),
            (∀ t, (φ t).val > 0 ↔ t.val > -1/2) ∧
            (∀ t, t.val = -3/4 ∨ t.val = 3/4 → φ t = t)  := by
            let f : ℝ → ℝ := fun t => (3/5:ℝ)*t+3/10+(12/5)*min (t+1/2) 0
            let g : ℝ → ℝ := fun s => (5/3:ℝ)*s-1/2-(4/3)*min s 0
            have hfleft (t : ℝ) (ht : t ≤ -1/2) : f t=3*t+3/2 := by
              dsimp [f]; rw [min_eq_left (by linarith)]; ring
            have hfright (t : ℝ) (ht : -1/2 ≤ t) : f t=(3/5)*t+3/10 := by
              dsimp [f]; rw [min_eq_right (by linarith)]; ring
            have hgleft (s : ℝ) (hs : s ≤ 0) : g s=s/3-1/2 := by
              dsimp [g]; rw [min_eq_left hs]; ring
            have hgright (s : ℝ) (hs : 0 ≤ s) : g s=(5/3)*s-1/2 := by
              dsimp [g]; rw [min_eq_right hs]; ring
            have hfmem (t : Icc (-3/4:ℝ) (3/4)) : f t ∈ Icc (-3/4:ℝ) (3/4) := by
              rcases le_total t.val (-1/2) with ht|ht
              · rw [hfleft _ ht]; constructor <;> linarith [t.property.1,t.property.2]
              · rw [hfright _ ht]; constructor <;> linarith [t.property.1,t.property.2]
            have hgmem (s : Icc (-3/4:ℝ) (3/4)) : g s ∈ Icc (-3/4:ℝ) (3/4) := by
              rcases le_total s.val 0 with hs|hs
              · rw [hgleft _ hs]; constructor <;> linarith [s.property.1,s.property.2]
              · rw [hgright _ hs]; constructor <;> linarith [s.property.1,s.property.2]
            have hgf (t : ℝ) : g (f t)=t := by
              rcases le_total t (-1/2) with ht|ht
              · rw [hfleft _ ht,hgleft _ (by linarith)]; ring
              · rw [hfright _ ht,hgright _ (by linarith)]; ring
            have hfg (s : ℝ) : f (g s)=s := by
              rcases le_total s 0 with hs|hs
              · rw [hgleft _ hs,hfleft _ (by linarith)]; ring
              · rw [hgright _ hs,hfright _ (by linarith)]; ring
            let φ : Icc (-3/4:ℝ) (3/4) ≃ₜ Icc (-3/4:ℝ) (3/4) := {
              toFun := fun t => ⟨f t,hfmem t⟩
              invFun := fun s => ⟨g s,hgmem s⟩
              left_inv := by intro t; apply Subtype.ext; exact hgf t
              right_inv := by intro s; apply Subtype.ext; exact hfg s
              continuous_toFun := by apply Continuous.subtype_mk; dsimp [f]; fun_prop
              continuous_invFun := by apply Continuous.subtype_mk; dsimp [g]; fun_prop
            }
            refine ⟨φ,?_,?_⟩
            · intro t
              change 0 < f t ↔ -1/2 < t.val
              rcases le_total t.val (-1/2) with ht|ht
              · rw [hfleft _ ht]; constructor <;> intro h <;> linarith
              · rw [hfright _ ht]; constructor <;> intro h <;> linarith
            · intro t ht
              apply Subtype.ext
              change f t=t.val
              rcases ht with ht|ht
              · rw [hfleft _ (by linarith),ht]; norm_num
              · rw [hfright _ (by linarith),ht]; norm_num
          obtain ⟨φ,hφpos,hφfix⟩ := hWidth
          let j : Icc (-3/4:ℝ) (3/4) × Circle → Ioo (-1:ℝ) 1 × Circle :=
            fun t => (⟨t.1.val,⟨by linarith [t.1.property.1],by linarith [t.1.property.2]⟩⟩,t.2)
          have hjC : Continuous j := by dsimp [j]; fun_prop
          have hjE : IsEmbedding j := by
            apply (IsEmbedding.of_comp_iff (g := fun z : Ioo (-1:ℝ) 1 × Circle =>
              (z.1.val,z.2)) (IsEmbedding.subtypeVal.prodMap IsEmbedding.id)).mp
            exact IsEmbedding.subtypeVal.prodMap IsEmbedding.id
          let q : C(Icc (-3/4:ℝ) (3/4) × Circle,E) := ⟨e ∘ j,he.continuous.comp hjC⟩
          have hqE : IsEmbedding q := he.isEmbedding.comp hjE
          let C : Set E := range q
          have hC : IsCompact C := isCompact_range q.continuous
          let T : (Icc (-3/4:ℝ) (3/4) × Circle) ≃ₜ C := hqE.toHomeomorph
          let H := φ.prodCongr (Homeomorph.refl Circle)
          let Q : C ≃ₜ C := (T.symm.trans H).trans T
          let W0 : Set (Ioo (-1:ℝ) 1 × Circle) := {z | z.1.val ∈ Ioo (-3/4:ℝ) (3/4)}
          let W : Set E := e '' W0
          have hWO : IsOpen W := he.isOpenMap _
            (isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_fst))
          have hWC : W ⊆ C := by
            rintro x ⟨z,hz,rfl⟩
            refine ⟨(⟨z.1.val,⟨le_of_lt hz.1,le_of_lt hz.2⟩⟩,z.2),?_⟩
            apply congrArg e; apply Prod.ext <;> rfl
          have hWmem (t : Icc (-3/4:ℝ) (3/4) × Circle) :
              q t ∈ W ↔ t.1.val ∈ Ioo (-3/4:ℝ) (3/4) := by
            constructor
            · rintro ⟨z,hz,heq⟩
              have hzj : z=j t := he.injective heq
              simpa only [hzj,j,W0,mem_ofPred_eq] using hz
            · intro ht
              exact ⟨j t,ht,rfl⟩
          have hQfix : ∀ x : C, (x : E) ∉ W → Q x=x := by
            intro x hx
            let t := T.symm x
            have htq : q t=x.val := congrArg Subtype.val (T.apply_symm_apply x)
            have htW : t.1.val ∉ Ioo (-3/4:ℝ) (3/4) := by
              intro hh; exact hx (htq ▸ (hWmem t).mpr hh)
            have htend : t.1.val=-3/4 ∨ t.1.val=3/4 := by
              have hlo := t.1.property.1; have hhi := t.1.property.2
              by_cases hl : t.1.val=-3/4
              · exact Or.inl hl
              · right
                by_contra hh
                exact htW ⟨lt_of_le_of_ne hlo (Ne.symm hl),lt_of_le_of_ne hhi hh⟩
            have hHt : H t=t := Prod.ext (hφfix t.1 htend) rfl
            change T (H (T.symm x))=x
            rw [hHt]; exact T.apply_symm_apply x
          let F := extendClosedHomeomorph C W hC.isClosed hWO hWC Q hQfix
          have hFq (t : Icc (-3/4:ℝ) (3/4) × Circle) : F (q t)=q (H t) := by
            have htC : q t ∈ C := ⟨t,rfl⟩
            change (if hx : q t ∈ C then (Q ⟨q t,hx⟩ : E) else q t)=_
            rw [dite_eq_left htC]
            have hTt : (⟨q t,htC⟩ : C)=T t := rfl
            rw [hTt]
            change (T (H (T.symm (T t))) : E)=_
            rw [T.symm_apply_apply]; rfl
          let N : Set E := e '' {z : Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Ioo (-1/2:ℝ) (1/2)}
          have hNC : N ⊆ C := by
            rintro x ⟨z,hz,rfl⟩
            refine ⟨(⟨z.1.val,⟨by linarith [hz.1],by linarith [hz.2]⟩⟩,z.2),?_⟩
            apply congrArg e; apply Prod.ext <;> rfl
          have hNmem (t : Icc (-3/4:ℝ) (3/4) × Circle) :
              q t ∈ N ↔ t.1.val ∈ Ioo (-1/2:ℝ) (1/2) := by
            constructor
            · rintro ⟨z,hz,heq⟩
              have hzj : z=j t := he.injective heq
              simpa only [hzj,j,W0,mem_ofPred_eq] using hz
            · intro ht
              exact ⟨j t,ht,rfl⟩
          refine ⟨F,?_⟩
          ext x
          by_cases hxC : x ∈ C
          · obtain ⟨t,rfl⟩ := hxC
            change F (q t) ∈ U ↔ q t ∈ U ∪ N
            rw [hFq]
            have hUmem (v : Icc (-3/4:ℝ) (3/4) × Circle) : q v ∈ U ↔ 0 < v.1.val := hpos (j v)
            rw [mem_union,hUmem,hUmem,hNmem]
            change 0 < (φ t.1).val ↔ 0 < t.1.val ∨ t.1.val ∈ Ioo (-1/2:ℝ) (1/2)
            rw [show (0 < (φ t.1).val ↔ -1/2 < t.1.val) from hφpos t.1]
            constructor
            · intro ht
              by_cases htp : 0 < t.1.val
              · exact Or.inl htp
              · exact Or.inr ⟨ht,by linarith⟩
            · rintro (ht|ht)
              · linarith
              · exact ht.1
          · have hxW : x ∉ W := fun hw => hxC (hWC hw)
            have hxN : x ∉ N := fun hn => hxC (hNC hn)
            change F x ∈ U ↔ x ∈ U ∪ N
            rw [show F x=x from extendClosedHomeomorph_apply_outside C W hC.isClosed hWO hWC Q hQfix x hxW]
            simp only [mem_union,hxN,or_false]
        have hsign (A B : Set S) (hA : A ⊆ c.imageᶜ) (hD : Disjoint A B)
            (hP : pos ⊆ A) (hN : neg ⊆ B) : ∀ z, e z ∈ A ↔ 0 < z.1.val := by
          intro z
          constructor
          · intro hzA
            rcases lt_trichotomy 0 z.1.val with hz|hz|hz
            · exact hz
            · exact (hA hzA ((haxis z).mpr hz.symm)).elim
            · have hzB : e z ∈ B := hN ⟨(⟨z.1.val,⟨z.1.property.1,hz⟩⟩,z.2),rfl⟩
              exact (disjoint_left.mp hD hzA hzB).elim
          · intro hz
            exact hP ⟨(⟨z.1.val,⟨hz,z.1.property.2⟩⟩,z.2),rfl⟩
        let r : (Ioo (-1:ℝ) 1 × Circle) ≃ₜ (Ioo (-1:ℝ) 1 × Circle) := {
          toFun := fun z => (⟨-z.1.val,⟨by linarith [z.1.property.2],by linarith [z.1.property.1]⟩⟩,z.2)
          invFun := fun z => (⟨-z.1.val,⟨by linarith [z.1.property.2],by linarith [z.1.property.1]⟩⟩,z.2)
          left_inv := by intro z; apply Prod.ext; exact Subtype.ext (neg_neg z.1.val); rfl
          right_inv := by intro z; apply Prod.ext; exact Subtype.ext (neg_neg z.1.val); rfl
          continuous_toFun := by fun_prop
          continuous_invFun := by fun_prop
        }
        let en : C(Ioo (-1:ℝ) 1 × Circle,S) := e.comp ⟨r,r.continuous⟩
        have hen : IsOpenEmbedding en := he.comp r.isOpenEmbedding
        have hNflip : en '' {z : Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Ioo (-1/2:ℝ) (1/2)}=N := by
          ext x
          constructor
          · rintro ⟨z,hz,rfl⟩
            exact ⟨r z,⟨by change -1/2 < -z.1.val; linarith [hz.2],
              by change -z.1.val < 1/2; linarith [hz.1]⟩,rfl⟩
          · rintro ⟨z,hz,rfl⟩
            refine ⟨r.symm z,⟨?_,?_⟩,?_⟩
            · change -1/2 < -z.1.val; linarith [hz.2]
            · change -z.1.val < 1/2; linarith [hz.1]
            · change e (r (r.symm z))=e z
              rw [r.apply_symm_apply]
        have hTransport (A B : Set S) (hA : A ⊆ c.imageᶜ) (hB : B ⊆ c.imageᶜ)
            (hD : Disjoint A B) (hP : pos ⊆ A) (hN : neg ⊆ B) :
            Nonempty (↥(A ∪ N) ≃ₜ A) ∧ Nonempty (↥(B ∪ N) ≃ₜ B) := by
          obtain ⟨F,hF⟩ := hThicken e he A (hsign A B hA hD hP hN)
          have hsignn : ∀ z, en z ∈ B ↔ 0 < z.1.val := by
            intro z
            have hh : e (r z) ∈ B ↔ (r z).1.val < 0 := by
              constructor
              · intro hzB
                rcases lt_trichotomy 0 (r z).1.val with hz|hz|hz
                · have hzA : e (r z) ∈ A := hP ⟨(⟨(r z).1.val,⟨hz,(r z).1.property.2⟩⟩,(r z).2),rfl⟩
                  exact (disjoint_left.mp hD hzA hzB).elim
                · exact (hB hzB ((haxis (r z)).mpr hz.symm)).elim
                · exact hz
              · intro hz
                exact hN ⟨(⟨(r z).1.val,⟨(r z).1.property.1,hz⟩⟩,(r z).2),rfl⟩
            change e (r z) ∈ B ↔ 0 < z.1.val
            rw [hh]
            change -z.1.val < 0 ↔ 0 < z.1.val
            constructor <;> intro hh <;> linarith
          obtain ⟨G,hG⟩ := hThicken en hen B hsignn
          rw [hNflip] at hG
          exact ⟨⟨F.sets hF.symm⟩,⟨G.sets hG.symm⟩⟩
        have hHomeos : Nonempty (U ≃ₜ L) ∧ Nonempty (V ≃ₜ R) := by
          rcases hopposite with ⟨hP,hN⟩|⟨hP,hN⟩
          · exact hTransport L R hLQ hRQ hdis hP hN
          · have hh := hTransport R L hRQ hLQ hdis.symm hP hN
            exact ⟨hh.2,hh.1⟩
        exact ⟨N,hNO,hUV,hI,hzero.1,hzero.2,hHomeos.1,hHomeos.2,rfl⟩
      have hTube (S : Type) [TopologicalSpace S]
        (e : C(Set.Ioo (-1:ℝ) 1 × Circle,S)) (he : IsOpenEmbedding e) :
        ∃ h : (Set.Ioo (-1/2:ℝ) (1/2) × Circle) ≃ₜ
            ↥(e '' {z : Set.Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)}),
          ∀ z, (h z).val=e (⟨z.1.val,⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩⟩,z.2)  := by
        classical
        let j : Set.Ioo (-1/2:ℝ) (1/2) → Set.Ioo (-1:ℝ) 1 :=
          fun u => ⟨u.val,⟨by linarith [u.property.1],by linarith [u.property.2]⟩⟩
        have hj : IsEmbedding j := by
          apply (IsEmbedding.of_comp_iff (f:=j) (g:= (Subtype.val : Set.Ioo (-1:ℝ) 1 → ℝ)) IsEmbedding.subtypeVal).mp
          exact IsEmbedding.subtypeVal
        let q := e ∘ Prod.map j (id : Circle → Circle)
        have hq : IsEmbedding q := he.isEmbedding.comp (hj.prodMap IsEmbedding.id)
        have hEq : Set.range q = e ''
            {z : Set.Ioo (-1:ℝ) 1 × Circle | z.1.val ∈ Set.Ioo (-1/2:ℝ) (1/2)} := by
          ext x
          constructor
          · rintro ⟨z,rfl⟩
            exact ⟨(j z.1,z.2),z.1.property,rfl⟩
          · rintro ⟨z,hz,rfl⟩
            exact ⟨(⟨z.1.val,hz⟩,z.2),rfl⟩
        let h := hq.toHomeomorph.trans (Homeomorph.setCongr hEq)
        refine ⟨h,?_⟩
        intro z
        change (hq.toHomeomorph z).val= _
        rfl
      have hGenerator (X : Type) [TopologicalSpace X]
        (h : (Set.Ioo (-1/2:ℝ) (1/2) × Circle) ≃ₜ X) :
        ∀ q : H X 1, ∃ n : ℤ,
          n • HomologicalComplex.homologyMap
            (actualSingularFunctor.map (TopCat.ofHom
              ⟨fun w => h (⟨0,by norm_num⟩,w),by fun_prop⟩)) 1
            CircleFundamentalCycle.fundamentalClass=q  := by
        let a : C(Circle,X) := ⟨fun w => h (⟨0,by norm_num⟩,w),by fun_prop⟩
        let r : C(X,Circle) := ⟨fun x => (h.symm x).2,by fun_prop⟩
        have hwidth (t : unitInterval) (u : Set.Ioo (-1/2:ℝ) (1/2)) :
            (1-(t:ℝ))*(u:ℝ) ∈ Set.Ioo (-1/2:ℝ) (1/2) := by
          have h0 := t.property.1
          have h1 := t.property.2
          have hL := u.property.1
          have hR := u.property.2
          have hp := mul_nonneg h0 (le_of_lt (by linarith : 0 < (u:ℝ)+1/2))
          have hm := mul_nonneg h0 (le_of_lt (by linarith : 0 < 1/2-(u:ℝ)))
          constructor <;> nlinarith
        let Ht : ContinuousMap.Homotopy (ContinuousMap.id X) (a.comp r) := {
          toFun := fun z => h (⟨(1-(z.1:ℝ))*((h.symm z.2).1:ℝ),hwidth z.1 (h.symm z.2).1⟩,
            (h.symm z.2).2)
          continuous_toFun := by fun_prop
          map_zero_left := by intro x; simp
          map_one_left := by intro x; simp [a,r]
        }
        have hh : TopCat.Homotopy (𝟙 (TopCat.of X)) (TopCat.ofHom r ≫ TopCat.ofHom a) := Ht
        have hm := hh.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℤ ℤ) 1
        rw [actualSingularFunctor.map_id,HomologicalComplex.homologyMap_id,
          actualSingularFunctor.map_comp,HomologicalComplex.homologyMap_comp] at hm
        intro q
        have hq := congrArg (fun m => m q) hm
        change q=HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom a)) 1
          (HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom r)) 1 q) at hq
        obtain ⟨n,hn⟩ := CircleFundamentalCycle.fundamentalClass_generates
          (HomologicalComplex.homologyMap (actualSingularFunctor.map (TopCat.ofHom r)) 1 q)
        refine ⟨n,?_⟩
        rw [←hn,map_zsmul] at hq
        exact hq.symm
      have hRank (S : Type) [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
        (U V : Set S) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V=Set.univ)
        (hUZ : homologyInclusion S U 2=0) (hVZ : homologyInclusion S V 2=0)
        (f : C(Circle,↥(U ∩ V)))
        (hgen : ∀ z : H ↥(U ∩ V) 1, ∃ n : ℤ,
          n • HomologicalComplex.homologyMap
            (actualSingularFunctor.map (TopCat.ofHom f)) 1
            CircleFundamentalCycle.fundamentalClass=z)
        (hi0 : Function.Injective (actualMVDifference (TopCat.of S) U V 0))
        (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
        (eU : H U 1 ≅ ModuleCat.of ℤ (Fin (2*p) → ℤ))
        (eV : H V 1 ≅ ModuleCat.of ℤ (Fin (2*q) → ℤ)) : p=1 ∧ q=1  := by
        classical
        let d := actualMVConnecting (TopCat.of S) U V hU hV hcover 1
        have hsum : actualMVSum (TopCat.of S) U V 2=0 := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro q
          rw [actualMVSum_apply,hUZ,hVZ]
          simp
        have hdMono : Mono d :=
          (ShortComplex.exact_iff_mono _ hsum).mp
            (actualMV_exact_ambient (TopCat.of S) U V hU hV hcover 1)
        have hdInj := (ModuleCat.mono_iff_injective d).mp hdMono
        obtain ⟨e2⟩ := hS.2.2.1
        let z : H S 2 := e2.inv 1
        have hz : z ≠ 0 := by
          intro hh
          have he := e2.toLinearEquiv.apply_symm_apply (1:ℤ)
          change e2.hom z=1 at he
          rw [hh,map_zero] at he
          exact zero_ne_one he
        have hdz : d z ≠ 0 := by
          intro hh
          apply hz
          exact hdInj (hh.trans d.hom.map_zero.symm)
        obtain ⟨n,hn⟩ := hgen (d z)
        have hn0 : n ≠ 0 := by
          intro hh
          rw [hh,zero_smul] at hn
          exact hdz hn.symm
        have hdiff := congrArg (fun m => m z)
          (actualMVConnecting_difference (TopCat.of S) U V hU hV hcover 1)
        change actualMVDifference (TopCat.of S) U V 1 (d z)=0 at hdiff
        let y : H ↥(U ∩ V) 1 := HomologicalComplex.homologyMap
          (actualSingularFunctor.map (TopCat.ofHom f)) 1 CircleFundamentalCycle.fundamentalClass
        have hkill : n • actualMVDifference (TopCat.of S) U V 1 y=0 := by
          rw [←hn] at hdiff
          rw [map_zsmul] at hdiff
          exact hdiff
        let P := eU.toLinearEquiv.toAddEquiv.prodCongr eV.toLinearEquiv.toAddEquiv
        have hcorezero : actualMVDifference (TopCat.of S) U V 1 y=0 := by
          apply P.injective
          rw [P.map_zero]
          have hkill' : n • P (actualMVDifference (TopCat.of S) U V 1 y)=0 := by
            exact (map_zsmul P n _).symm.trans ((congrArg P hkill).trans P.map_zero)
          apply Prod.ext
          · funext i
            have hi := congrFun (congrArg Prod.fst hkill') i
            change n * (P (actualMVDifference (TopCat.of S) U V 1 y)).1 i=0 at hi
            exact (mul_eq_zero.mp hi).resolve_left hn0
          · funext i
            have hi := congrFun (congrArg Prod.snd hkill') i
            change n * (P (actualMVDifference (TopCat.of S) U V 1 y)).2 i=0 at hi
            exact (mul_eq_zero.mp hi).resolve_left hn0
        have hDzero : actualMVDifference (TopCat.of S) U V 1=0 := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro a
          obtain ⟨k,hk⟩ := hgen a
          change actualMVDifference (TopCat.of S) U V 1 a=0
          rw [←hk,map_zsmul,hcorezero]
          simp only [zsmul_zero]
        have hMmono : Mono (actualMVSum (TopCat.of S) U V 1) :=
          (ShortComplex.exact_iff_mono _ hDzero).mp
            (actualMV_exact_pair (TopCat.of S) U V hU hV hcover 1)
        have hMepi : Function.Surjective (actualMVSum (TopCat.of S) U V 1) := by
          intro a
          have hz : actualMVConnecting (TopCat.of S) U V hU hV hcover 0 a=0 := by
            apply hi0
            have hh := congrArg (fun m => m a)
              (actualMVConnecting_difference (TopCat.of S) U V hU hV hcover 0)
            change actualMVDifference (TopCat.of S) U V 0
              (actualMVConnecting (TopCat.of S) U V hU hV hcover 0 a)=0 at hh
            exact hh.trans (actualMVDifference (TopCat.of S) U V 0).hom.map_zero.symm
          exact (ShortComplex.moduleCat_exact_iff _).mp
            (actualMV_exact_ambient (TopCat.of S) U V hU hV hcover 0) a hz
        let B := AddEquiv.ofBijective (actualMVSum (TopCat.of S) U V 1).hom.toAddMonoidHom
          ⟨(ModuleCat.mono_iff_injective _).mp hMmono,hMepi⟩
        obtain ⟨e1⟩ := hS.2.2.2
        let R := (P.symm.trans B).trans e1.toLinearEquiv.toAddEquiv
        have hr := R.toIntLinearEquiv.finrank_eq
        simp only [Module.finrank_prod,Module.finrank_pi,
          Fintype.card_fin] at hr
        omega
      have hHZeroInjective (X : TopCat) (A B : Set X)
          [PathConnectedSpace ↥(A ∩ B)] :
          Function.Injective (actualMVDifference X A B 0) := by
        intro a b hab
        have hab' := congrArg Prod.fst hab
        dsimp only at hab'
        rw [actualMVDifference_apply, actualMVDifference_apply] at hab'
        have hn := CircleHomologyComputation.augmentation_naturality
          (singularSubsetInclusion X (A ∩ B) A Set.inter_subset_left)
        have ha := congrArg (fun f => f a) hn
        have hb := congrArg (fun f => f b) hn
        apply (ModuleCat.mono_iff_injective
          ((TopCat.of ↥(A ∩ B)).singularHomology₀ε CircleHomologyComputation.RZ)).mp inferInstance
        exact ha.symm.trans ((congrArg
          (fun x => (TopCat.of A).singularHomology₀ε CircleHomologyComputation.RZ x) hab').trans hb)
      let : ClosedSurface S := Classical.choice hS.2.1
      obtain ⟨e,he,hcore⟩ := LocalSurgery.actual_original_essential_circle_has_annular_collar
        S 2 (by omega) hS ⟨c,hc⟩
      obtain ⟨N,hNO,hAB,hI,hAzero,hBzero,⟨hA⟩,⟨hB⟩,hN⟩ :=
        hSides S hS c U V hU hV hUC hVC hUV hcover e he hcore
      let A := U ∪ N
      let B := V ∪ N
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)
      let eA : H A 1 ≅ ModuleCat.of ℤ (Fin (2*p) → ℤ) :=
        F.mapIso (TopCat.isoOfHomeo hA) ≪≫ eU
      let eB : H B 1 ≅ ModuleCat.of ℤ (Fin (2*q) → ℤ) :=
        F.mapIso (TopCat.isoOfHomeo hB) ≪≫ eV
      obtain ⟨hTube0,_⟩ := hTube S e he
      let hT : (Ioo (-1/2:ℝ) (1/2) × Circle) ≃ₜ ↥(A ∩ B) :=
        hTube0.trans (Homeomorph.setCongr (hI.trans hN).symm)
      let f : C(Circle,↥(A ∩ B)) := ⟨fun w => hT (⟨0,by norm_num⟩,w),by fun_prop⟩
      have hgen : ∀ z : H ↥(A ∩ B) 1, ∃ n : ℤ,
          n • HomologicalComplex.homologyMap
            (actualSingularFunctor.map (TopCat.ofHom f)) 1 CircleFundamentalCycle.fundamentalClass=z :=
        hGenerator _ hT
      let : ConnectedSpace (Ioo (-1/2:ℝ) (1/2)) :=
        isConnected_iff_connectedSpace.mp (isConnected_Ioo (by norm_num))
      let : LocallyPathConnectedSpace (Ioo (-1/2:ℝ) (1/2)) := isOpen_Ioo.locallyPathConnectedSpace
      let : PathConnectedSpace (Ioo (-1/2:ℝ) (1/2)) :=
        PathConnectedSpace.of_locallyPathConnectedSpace
      let : PathConnectedSpace ↥(A ∩ B) := hT.pathConnectedSpace
      obtain ⟨hp1,hq1⟩ := hRank S hS A B (hU.union hNO) (hV.union hNO) hAB
        hAzero hBzero f hgen (hHZeroInjective (TopCat.of S) A B) p q hp hq eA eB
      subst p
      subst q
      simpa only [Nat.mul_one] using And.intro (Nonempty.intro eU) (Nonempty.intro eV)
    have hDerivedSideRanks : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
        Nonempty (integralHomology U 1 ≅ ModuleCat.of ℤ (Fin (2*p) → ℤ)) ∧
        Nonempty (integralHomology V 1 ≅ ModuleCat.of ℤ (Fin (2*q) → ℤ)) := by
      obtain ⟨p,q,hp,hq,⟨eU⟩,⟨eV⟩⟩ :=
        hpositive E hE c hc U V
          hU hV hUconn hVconn hUV hcover hfrontU hfrontV
      obtain ⟨rU⟩ := actual_one_boundary_orientable_model_homology_one p
      obtain ⟨rV⟩ := actual_one_boundary_orientable_model_homology_one q
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)
      exact ⟨p,q,hp,hq,
        ⟨F.mapIso (TopCat.isoOfHomeo eU) ≪≫ rU⟩,
        ⟨F.mapIso (TopCat.isoOfHomeo eV) ≪≫ rV⟩⟩
    obtain ⟨p,q,hp,hq,⟨eU⟩,⟨eV⟩⟩ := hDerivedSideRanks
    exact hConsumer E hE c hc U V hU hV hUconn hVconn hUV hcover
      p q hp hq eU eV
  have hrecognition (E : Type) [TopologicalSpace E]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
      (hE : IsGenus E 2) (c : Curve E) (hc : Essential c)
      (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
      (hUconn : IsConnected U) (hVconn : IsConnected V)
      (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
      (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image)
      (hUone : Nonempty (integralHomology U 1 ≅ ModuleCat.of ℤ (Fin 2 → ℤ))) :
      Nonempty (U ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) := by
    classical
    obtain ⟨p, q, hp, hq, ⟨eU⟩, hmodelV⟩ :=
      hpositive E hE c hc U V
        hU hV hUconn hVconn hUV hcover hfrontU hfrontV
    let eHU := CircleHomologyComputation.homotopyHomologyIso eU.toHomotopyEquiv 1
    obtain ⟨eModelH1⟩ := actual_one_boundary_orientable_model_homology_one p
    obtain ⟨eUone⟩ := hUone
    let eRank : ModuleCat.of ℤ (Fin (2 * p) → ℤ) ≅ ModuleCat.of ℤ (Fin 2 → ℤ) :=
      eModelH1.symm ≪≫ eHU.symm ≪≫ eUone
    have hRank : 2 * p = 2 := by
      simpa using eRank.toLinearEquiv.finrank_eq
    have hpone : p = 1 := by omega
    subst p
    obtain ⟨eTorus⟩ := actual_one_handle_one_boundary_model_punctured_product_torus
    exact ⟨eU.trans eTorus⟩
  have hcut (E : Type) [TopologicalSpace E]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
      (hE : IsGenus E 2) (c : Curve E)
      (hc : Essential c) (hdiv : DividingCurve c) :
      ∃ U V : Set E,
        IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
        U ∪ V = c.imageᶜ ∧ frontier U = c.image ∧ frontier V = c.image ∧
        Nonempty (U ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) ∧
        Nonempty (V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) := by
    classical
    letI : ClosedSurface E := Classical.choice hE.2.1
    letI : LocallyConnectedSpace E :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin 2)) E
    have hclosed : IsClosed c.image :=
      (isCompact_range c.embedded.continuous).isClosed
    have hopen : IsOpen c.imageᶜ := hclosed.isOpen_compl
    have hnonempty : c.imageᶜ.Nonempty := by
      obtain ⟨W, Z, hp, e, hW, hZ, hzero, haxis⟩ :=
        CurveComplex.LocalSurgery.embedded_curve_has_local_axis_chart c
          (c.map 1) ⟨1, rfl⟩
      have hz : (0, 0) ∈ Z := by
        rw [← hzero]
        exact (e ⟨c.map 1, hp⟩).property
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hZ (0, 0) hz
      have hq : (r / 2, 0) ∈ Z := by
        apply hball
        change dist (r / 2, (0 : ℝ)) (0, 0) < r
        rw [Prod.dist_eq]
        have hhalf : 0 < r / 2 := by linarith
        simp only [Real.dist_eq, sub_zero, sub_self, abs_zero]
        rw [abs_of_pos hhalf, max_eq_left (le_of_lt hhalf)]
        linarith
      let x := e.symm ⟨(r / 2, 0), hq⟩
      refine ⟨x.val, ?_⟩
      intro hx
      have heq : ((e ⟨x.val, x.property⟩ : Z) : ℝ × ℝ) = (r / 2, 0) := by
        exact congrArg Subtype.val (e.apply_symm_apply ⟨(r / 2, 0), hq⟩)
      have hh := (haxis x.val x.property).mp hx
      rw [heq] at hh
      linarith
    obtain ⟨x, hx⟩ := hnonempty
    let U := connectedComponentIn c.imageᶜ x
    let V := c.imageᶜ \ U
    have hU : IsOpen U := hopen.connectedComponentIn
    have hxU : x ∈ U := mem_connectedComponentIn hx
    have hUsub : U ⊆ c.imageᶜ := connectedComponentIn_subset _ _
    have hV : IsOpen V := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      have hCopen : IsOpen (connectedComponentIn c.imageᶜ z) :=
        hopen.connectedComponentIn
      apply Filter.mem_of_superset (hCopen.mem_nhds (mem_connectedComponentIn hz.1))
      intro w hw
      refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
      intro hwU
      have h1 := connectedComponentIn_eq hw
      have h2 := connectedComponentIn_eq hwU
      have hzU : z ∈ U := by
        change z ∈ connectedComponentIn c.imageᶜ x
        rw [h2, ← h1]
        exact mem_connectedComponentIn hz.1
      exact hz.2 hzU
    have hUV : Disjoint U V := by
      exact Set.disjoint_left.mpr (fun z hzU hzV => hzV.2 hzU)
    have hcover : U ∪ V = c.imageᶜ := by
      ext z
      constructor
      · rintro (hzU | hzV)
        · exact hUsub hzU
        · exact hzV.1
      · intro hz
        by_cases hzU : z ∈ U
        · exact Or.inl hzU
        · exact Or.inr ⟨hz, hzU⟩
    have hVnonempty : V.Nonempty := by
      by_contra hnone
      have hVempty : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hnone
      have hF : c.imageᶜ = U := by simpa [hVempty] using hcover.symm
      apply hdiv
      rw [hF]
      exact isConnected_connectedComponentIn_iff.mpr hx
    have hfrontierSubset : ∀ A B : Set E,
        IsOpen A → IsOpen B → Disjoint A B → A ∪ B = c.imageᶜ →
        frontier A ⊆ c.image := by
      intro A B hA hB hAB hcoverAB z hz
      by_contra hzc
      have hzF : z ∈ c.imageᶜ := hzc
      rw [← hcoverAB] at hzF
      rcases hzF with hzA | hzB
      · have hn : z ∉ interior A := hz.2
        exact hn (hA.interior_eq.symm ▸ hzA)
      · obtain ⟨w, hwB, hwA⟩ :=
          mem_closure_iff.mp hz.1 B hB hzB
        exact Set.disjoint_left.mp hAB hwA hwB
    have hfrontierU : frontier U ⊆ c.image :=
      hfrontierSubset U V hU hV hUV hcover
    have hfrontierV : frontier V ⊆ c.image :=
      hfrontierSubset V U hV hU hUV.symm (by simpa [union_comm] using hcover)
    obtain ⟨e, he, hcore⟩ :=
      CurveComplex.LocalSurgery.actual_original_essential_circle_has_annular_collar
        E 2 (by omega) hE ⟨c, hc⟩
    let T := Set.Ioo (-1 : ℝ) 1
    let Iplus : Set T := {t | 0 < t.val}
    let Iminus : Set T := {t | t.val < 0}
    have hplusImage : Subtype.val '' Iplus = Set.Ioo (0 : ℝ) 1 := by
      ext t
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨hr, r.property.2⟩
      · intro ht
        exact ⟨⟨t, ⟨by linarith [ht.1], ht.2⟩⟩, ht.1, rfl⟩
    have hminusImage : Subtype.val '' Iminus = Set.Ioo (-1 : ℝ) 0 := by
      ext t
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r.property.1, hr⟩
      · intro ht
        exact ⟨⟨t, ⟨ht.1, by linarith [ht.2]⟩⟩, ht.2, rfl⟩
    have hplusConnected : _root_.IsPreconnected Iplus := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hplusImage]
      exact isPreconnected_Ioo
    have hminusConnected : _root_.IsPreconnected Iminus := by
      apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [hminusImage]
      exact isPreconnected_Ioo
    let Kplus := e '' (Iplus ×ˢ (Set.univ : Set Circle))
    let Kminus := e '' (Iminus ×ˢ (Set.univ : Set Circle))
    have hKplusConnected : _root_.IsPreconnected Kplus :=
      (hplusConnected.prod isPreconnected_univ).image e e.continuous.continuousOn
    have hKminusConnected : _root_.IsPreconnected Kminus :=
      (hminusConnected.prod isPreconnected_univ).image e e.continuous.continuousOn
    have hnoncore : ∀ p : T × Circle, p.1.val ≠ 0 → e p ∈ c.imageᶜ := by
      intro p hne hpc
      obtain ⟨w, hw⟩ := hpc
      have heq : e p = e (⟨0, by norm_num [T]⟩, w) := by
        rw [hcore]
        exact hw.symm
      have htime := congrArg (fun q : T × Circle => q.1.val) (he.injective heq)
      exact hne htime
    have hKplusSub : Kplus ⊆ c.imageᶜ := by
      rintro y ⟨p, hp, rfl⟩
      exact hnoncore p (ne_of_gt hp.1)
    have hKminusSub : Kminus ⊆ c.imageᶜ := by
      rintro y ⟨p, hp, rfl⟩
      exact hnoncore p (ne_of_lt hp.1)
    have hzeroPlus : (⟨0, by norm_num [T]⟩ : T) ∈ closure Iplus := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      change (0 : ℝ) ∈ closure (Subtype.val '' Iplus)
      rw [hplusImage, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨le_rfl, by norm_num [T]⟩
    have hzeroMinus : (⟨0, by norm_num [T]⟩ : T) ∈ closure Iminus := by
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
      change (0 : ℝ) ∈ closure (Subtype.val '' Iminus)
      rw [hminusImage, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
      exact ⟨by norm_num, le_rfl⟩
    have hcoreClosure : ∀ (I : Set T) (hz : (⟨0, by norm_num [T]⟩ : T) ∈ closure I),
        c.image ⊆ closure (e '' (I ×ˢ (Set.univ : Set Circle))) := by
      intro I hz y hy
      obtain ⟨w, rfl⟩ := hy
      let f : T → E := fun t => e (t, w)
      have hf : Continuous f :=
        e.continuous.comp (continuous_id.prodMk continuous_const)
      have hm : f ⟨0, by norm_num [T]⟩ ∈ closure (f '' I) :=
        mem_closure_image hf.continuousAt hz
      have hsub : f '' I ⊆ e '' (I ×ˢ (Set.univ : Set Circle)) := by
        rintro z ⟨t, ht, rfl⟩
        exact ⟨(t, w), ⟨ht, Set.mem_univ _⟩, rfl⟩
      have hmem := closure_mono hsub hm
      simpa only [f, hcore] using hmem
    have hcorePlus : c.image ⊆ closure Kplus := hcoreClosure Iplus hzeroPlus
    have hcoreMinus : c.image ⊆ closure Kminus := hcoreClosure Iminus hzeroMinus
    have hfullFrontier : ∀ A B : Set E,
        IsOpen A → IsOpen B → Disjoint A B → A ∪ B = c.imageᶜ →
        A.Nonempty → frontier A = c.image := by
      intro A B hA hB hAB hcoverAB hAne
      have hAsub : A ⊆ c.imageᶜ := by
        intro z hz
        rw [← hcoverAB]
        exact Or.inl hz
      have hAproper : A ≠ Set.univ := by
        intro hAU
        have hm : c.map 1 ∈ A := by rw [hAU]; trivial
        exact hAsub hm ⟨1, rfl⟩
      obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨hAne, hAproper⟩
      have hzcore := hfrontierSubset A B hA hB hAB hcoverAB hz
      obtain ⟨w, hw⟩ := hzcore
      have hzrange : z ∈ Set.range e := by
        exact ⟨(⟨0, by norm_num [T]⟩, w), (hcore w).trans hw⟩
      obtain ⟨y, hyrange, hyA⟩ := mem_closure_iff.mp hz.1 (Set.range e)
        he.isOpen_range hzrange
      obtain ⟨p, rfl⟩ := hyrange
      have htime : p.1.val ≠ 0 := by
        intro hpzero
        have hp : p.1 = (⟨0, by norm_num [T]⟩ : T) := Subtype.ext hpzero
        have hycore : e p ∈ c.image := by
          have heq : e p = c.map p.2 := by
            calc e p = e (p.1, p.2) := rfl
              _ = e (⟨0, by norm_num [T]⟩, p.2) := by rw [hp]
              _ = c.map p.2 := hcore p.2
          exact ⟨p.2, heq.symm⟩
        exact hAsub hyA hycore
      have hchoose : ∀ K : Set E, _root_.IsPreconnected K → K ⊆ c.imageᶜ →
          c.image ⊆ closure K → e p ∈ K → c.image ⊆ closure A := by
        intro K hK hKF hcoreK hpK
        have hsplit : K ⊆ A ∨ K ⊆ B :=
          _root_.IsPreconnected.subset_or_subset hA hB hAB
            (by simpa [hcoverAB] using hKF) hK
        rcases hsplit with hKA | hKB
        · exact hcoreK.trans (closure_mono hKA)
        · exact False.elim (Set.disjoint_left.mp hAB hyA (hKB hpK))
      have hcoreA : c.image ⊆ closure A := by
        rcases lt_or_gt_of_ne htime with hnegative | hpositive
        · exact hchoose Kminus hKminusConnected hKminusSub hcoreMinus
            ⟨p, ⟨hnegative, Set.mem_univ _⟩, rfl⟩
        · exact hchoose Kplus hKplusConnected hKplusSub hcorePlus
            ⟨p, ⟨hpositive, Set.mem_univ _⟩, rfl⟩
      apply Set.Subset.antisymm (hfrontierSubset A B hA hB hAB hcoverAB)
      intro y hy
      refine ⟨hcoreA hy, ?_⟩
      intro hyinterior
      exact hAsub (interior_subset hyinterior) hy
    have hfrontiers : frontier U = c.image ∧ frontier V = c.image :=
      ⟨hfullFrontier U V hU hV hUV hcover ⟨x, hxU⟩,
        hfullFrontier V U hV hU hUV.symm (by simpa [union_comm] using hcover) hVnonempty⟩
    have hrestOpen : ∀ z ∈ c.imageᶜ,
        IsOpen (c.imageᶜ \ connectedComponentIn c.imageᶜ z) := by
      intro z hz
      rw [isOpen_iff_mem_nhds]
      intro w hw
      have hWopen : IsOpen (connectedComponentIn c.imageᶜ w) := hopen.connectedComponentIn
      apply Filter.mem_of_superset (hWopen.mem_nhds (mem_connectedComponentIn hw.1))
      intro q hq
      refine ⟨connectedComponentIn_subset _ _ hq, ?_⟩
      intro hqz
      have h1 := connectedComponentIn_eq hq
      have h2 := connectedComponentIn_eq hqz
      apply hw.2
      rw [h2, ← h1]
      exact mem_connectedComponentIn hw.1
    have hcomponentHalf : ∀ z ∈ c.imageᶜ,
        Kplus ⊆ connectedComponentIn c.imageᶜ z ∨
        Kminus ⊆ connectedComponentIn c.imageᶜ z := by
      intro z hz
      let C := connectedComponentIn c.imageᶜ z
      let R := c.imageᶜ \ C
      have hCopen : IsOpen C := hopen.connectedComponentIn
      have hRopen : IsOpen R := hrestOpen z hz
      have hCsub : C ⊆ c.imageᶜ := connectedComponentIn_subset _ _
      have hCR : Disjoint C R :=
        Set.disjoint_left.mpr (fun q hqC hqR => hqR.2 hqC)
      have hCRcover : C ∪ R = c.imageᶜ := by
        ext q
        simp only [R, Set.mem_union, Set.mem_sdiff]
        exact ⟨fun h => h.elim (fun hq => hCsub hq) And.left,
          fun h => by by_cases hC : q ∈ C; exact Or.inl hC; exact Or.inr ⟨h, hC⟩⟩
      have hfront : frontier C = c.image :=
        hfullFrontier C R hCopen hRopen hCR hCRcover ⟨z, mem_connectedComponentIn hz⟩
      have hcorefront : c.map 1 ∈ frontier C := by
        rw [hfront]
        exact ⟨1, rfl⟩
      have hcorerange : c.map 1 ∈ Set.range e :=
        ⟨(⟨0, by norm_num [T]⟩, 1), hcore 1⟩
      obtain ⟨q, hqrange, hqC⟩ := mem_closure_iff.mp hcorefront.1
        (Set.range e) he.isOpen_range hcorerange
      obtain ⟨p, rfl⟩ := hqrange
      have htime : p.1.val ≠ 0 := by
        intro htime
        have ht : p.1 = (⟨0, by norm_num [T]⟩ : T) := Subtype.ext htime
        have hpimage : e p ∈ c.image := by
          refine ⟨p.2, ?_⟩
          calc c.map p.2 = e (⟨0, by norm_num [T]⟩, p.2) := (hcore p.2).symm
            _ = e p := by rw [← ht]
        exact hCsub hqC hpimage
      have hchoose : ∀ K : Set E, _root_.IsPreconnected K → K ⊆ c.imageᶜ →
          e p ∈ K → K ⊆ C := by
        intro K hK hKF hpK
        rcases _root_.IsPreconnected.subset_or_subset hCopen hRopen hCR
          (by simpa [hCRcover] using hKF) hK with hKC | hKR
        · exact hKC
        · exact False.elim (Set.disjoint_left.mp hCR hqC (hKR hpK))
      rcases lt_or_gt_of_ne htime with hnegative | hpositive
      · exact Or.inr (hchoose Kminus hKminusConnected hKminusSub
          ⟨p, ⟨hnegative, Set.mem_univ _⟩, rfl⟩)
      · exact Or.inl (hchoose Kplus hKplusConnected hKplusSub
          ⟨p, ⟨hpositive, Set.mem_univ _⟩, rfl⟩)
    have hplusNonempty : Kplus.Nonempty :=
      ⟨e (⟨1 / 2, by norm_num [T]⟩, 1),
        ⟨(⟨1 / 2, by norm_num [T]⟩, 1), ⟨by norm_num [T, Iplus], Set.mem_univ _⟩, rfl⟩⟩
    have hminusNonempty : Kminus.Nonempty :=
      ⟨e (⟨-1 / 2, by norm_num [T]⟩, 1),
        ⟨(⟨-1 / 2, by norm_num [T]⟩, 1), ⟨by norm_num [T, Iminus], Set.mem_univ _⟩, rfl⟩⟩
    have hcomponentDisjoint : ∀ z ∈ V, Disjoint (connectedComponentIn c.imageᶜ z) U := by
      intro z hz
      apply Set.disjoint_left.mpr
      intro q hqz hqU
      have h1 := connectedComponentIn_eq hqz
      have h2 := connectedComponentIn_eq hqU
      apply hz.2
      change z ∈ connectedComponentIn c.imageᶜ x
      rw [h2, ← h1]
      exact mem_connectedComponentIn hz.1
    have hforcedHalf : ∀ K L : Set E, K.Nonempty → K ⊆ U →
        ∀ z ∈ V, (K ⊆ connectedComponentIn c.imageᶜ z ∨
          L ⊆ connectedComponentIn c.imageᶜ z) → L ⊆ connectedComponentIn c.imageᶜ z := by
      intro K L hK hKU z hz hsplit
      rcases hsplit with hKC | hLC
      · obtain ⟨q, hq⟩ := hK
        exact False.elim (Set.disjoint_left.mp (hcomponentDisjoint z hz) (hKC hq) (hKU hq))
      · exact hLC
    obtain ⟨y, hy⟩ := hVnonempty
    have hsameComponent : ∀ z ∈ V,
        connectedComponentIn c.imageᶜ z = connectedComponentIn c.imageᶜ y := by
      intro z hz
      rcases hcomponentHalf x hx with hplusU | hminusU
      · have hmz := hforcedHalf Kplus Kminus hplusNonempty hplusU z hz (hcomponentHalf z hz.1)
        have hmy := hforcedHalf Kplus Kminus hplusNonempty hplusU y hy (hcomponentHalf y hy.1)
        obtain ⟨q, hq⟩ := hminusNonempty
        exact (connectedComponentIn_eq (hmz hq)).trans (connectedComponentIn_eq (hmy hq)).symm
      · have hpz := hforcedHalf Kminus Kplus hminusNonempty hminusU z hz (hcomponentHalf z hz.1).symm
        have hpy := hforcedHalf Kminus Kplus hminusNonempty hminusU y hy (hcomponentHalf y hy.1).symm
        obtain ⟨q, hq⟩ := hplusNonempty
        exact (connectedComponentIn_eq (hpz hq)).trans (connectedComponentIn_eq (hpy hq)).symm
    have hVcomponent : V = connectedComponentIn c.imageᶜ y := by
      apply Set.Subset.antisymm
      · intro z hz
        rw [← hsameComponent z hz]
        exact mem_connectedComponentIn hz.1
      · intro z hz
        exact ⟨connectedComponentIn_subset _ _ hz,
          fun hzU => Set.disjoint_left.mp (hcomponentDisjoint y hy) hz hzU⟩
    have hUconnected : IsConnected U := isConnected_connectedComponentIn_iff.mpr hx
    have hVconnected : IsConnected V := by
      rw [hVcomponent]
      exact isConnected_connectedComponentIn_iff.mpr hy.1
    have hclassification :
        Nonempty (U ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) ∧
        Nonempty (V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) := by
      obtain ⟨hUone, hVone⟩ :=
        hhomology E hE c hc U V hU hV
          hUconnected hVconnected hUV hcover hfrontiers.1 hfrontiers.2
      constructor
      · exact hrecognition E hE c hc U V
          hU hV hUconnected hVconnected hUV hcover hfrontiers.1 hfrontiers.2 hUone
      · exact hrecognition E hE c hc V U
          hV hU hVconnected hUconnected hUV.symm
          (by rw [union_comm]; exact hcover) hfrontiers.2 hfrontiers.1 hVone
    exact ⟨U, V, hU, hV, hUV, hcover, hfrontiers.1, hfrontiers.2,
      hclassification.1, hclassification.2⟩
  exact hcut S hS c hc hdiv
end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.source_genus_two_separating_actual_cut
