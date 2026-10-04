import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualOrientableBoundaryOfAtlas
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import CurveComplexGenusTwo.Topology.ActualBoundaryModels.Definitions
import CurveComplexGenusTwo.Topology.ActualBoundaryModels.ZeroHandleClosedDisc
import CurveComplexGenusTwo.Topology.ActualCutRecognition.TwistedBandReflectionExportStatement
import CurveComplexGenusTwo.Topology.ActualCrosscapGeometry.RawCrosscapSquareStrip
import ClassificationOfSurfaces.Triangulation
import ClassificationOfSurfaces.EvalStatement
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import Mathlib
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage

open scoped Manifold

namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Boundary-preserving compact classification of the actual cut closure.
Source: the compact one-boundary orientable surface classification used in
Lemmas 6.4/6.6. Caller: actual_essential_cut_positive_orientable_normal_forms,
local hcompactNormalForm, after constructing the literal closure, boundary
half-collar, and finite interior chart cover. No finite triangulation or
classification certificate is an input. -/
theorem actual_compact_cut_boundary_preserving_orientable_polygon
    (M : HyperellipticModel E S) (c : Curve E) (hc : Essential c)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUconn : IsConnected U) (hVconn : IsConnected V)
    (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
    (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image) :
    ∃ (p : ℕ) (e : (closure U) ≃ₜ Quot (OrientableRel p 1)),
      ∀ x : closure U,
        e x ∈ ActualOneBoundaryOrientableBoundary p ↔ x.val ∈ c.image := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
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
        E 2 (by omega) M.genusTwo ⟨c, hc⟩
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
      2 M.genusTwo x
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

end CurveComplex.Hyperbolic
