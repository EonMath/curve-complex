import OrdinarySignedPieceFamily
import RegionalWeightedMovieDefinitions
import OrdinaryMoviePreparation
import Mathlib.Data.Finset.Sort
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.GapMatchingTools
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.UniformContactPatchTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.CornerGeometryTools
import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.DiskExteriorHalfTools

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open CurveComplex.BranchedDoubleCover
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P


macro "paid_affine_subarc_range" : term => pure (Lean.mkIdent (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str .anonymous "_private") "OrdinaryMoviePreparation") 0) "affine_subarc_range"))

macro "paid_padded_interval_remainder" : term => pure (Lean.mkIdent (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str .anonymous "_private") "OrdinaryMoviePreparation") 0) "padded_interval_remainder"))

/-- G1: original M1 context, followed only by paid preparation and conditional M0 data. -/
theorem regional_ordinary_signed_contact_corner_families
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
      ∀ d : PairedBigonDisk F {y | y.val ∈ frontier F} (r v).val.val (r w).val.val,
      ∀ V : Set ↥F, IsOpen V → range d.disk ⊆ V →
        (∀ y ∈ closure V, y.val ∈ interior F) →
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ boundaryCircle}) →
        let C₀ : Set ↥F := {d.first 0,d.first 1}
        let removed := fun j : ι => ((range d.first \ C₀) ∩ range (r j).val.val).ncard
        let guiding := fun j : ι => ((range d.second \ C₀) ∩ range (r j).val.val).ncard
        let offset := fun j : ι =>
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
            (C₀ ∩ range (r j).val.val).ncard
        (∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j else 0) ≤
          (∑ j : ι, if j ≠ v ∧ j ≠ w then removed j else 0) →
        ∀ (A B : Interval) (K : Set ↥F),
        0 < A → A < min d.aStart d.aFinish → max d.aStart d.aFinish < B → B < 1 →
        (r v).val.val '' Icc A B ⊆ V → IsCompact K →
        range (r v).val.val = (r v).val.val '' Ioo A B ∪ K →
        Disjoint ((r v).val.val '' Icc (min d.aStart d.aFinish) (max d.aStart d.aFinish)) K →
        Disjoint (range d.disk) K →
        ∀ Edisk Eguide : OpenPartialHomeomorph S Plane,
        (∀ y ∈ range d.disk, y.val ∈ Edisk.source) →
        closure Edisk.source ⊆ Subtype.val '' (V \ K) ∩ interior F →
        Edisk.target = Metric.ball 0 1 →
        Eguide.source ⊆ Edisk.source ∩ Edisk.source →
        Plane.closedSquare 0 1 ⊆ Eguide.target →
        (∀ y ∈ (r w).val.val '' Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish),
          y.val ∈ Eguide.source) →
        Eguide ((r w).val.val (min d.bStart d.bFinish)).val = Plane.mk (-1) 0 →
        Eguide ((r w).val.val (max d.bStart d.bFinish)).val = Plane.mk 1 0 →
        (∀ y ∈ Eguide.source,
          y ∈ range (fun q => ((r w).val.val q).val) ↔ Eguide y 1 = 0) →
        ({y : ↥F | y.val ∈ Eguide.source ∧ Eguide y.val ∈ Plane.closedSquare 0 1} ∩
          range (r w).val.val = (r w).val.val '' Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish)) →
        FiniteFanCarrier F (augmented (fun i => (r i).val.val) α.val.val) {some v,some w}
          (range d.first ∪ range d.second) V (range d.disk)
          (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v) →
        Nonempty (OrdinarySignedPieceFamily F
          (augmented (fun i => (r i).val.val) α.val.val) v w d A B Edisk Eguide) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV hVinside havoid
    C₀ removed guiding offset hcheap
    A B K hA0 hAu hzB hB1 hpad hK hdecomp hcoreK hdK
    Edisk Eguide hdEdisk hEdiskClosure hEdiskTarget hGuideSource
    hGuideSquare hGuideCore hGuideZero hGuideOne hGuideAxis hGuideTrace fan
  let f : Option ι → C(Interval,↥F) := augmented (fun i => (r i).val.val) α.val.val
  let u := min d.aStart d.aFinish
  let z := max d.aStart d.aFinish
  let gu := min d.bStart d.bFinish
  let gz := max d.bStart d.bFinish
  have huz : u < z := min_lt_max.mpr d.a_distinct
  have hgugz : gu < gz := min_lt_max.mpr d.b_distinct
  have ha : IsEmbedding (f (some v)) := (r v).val.property.1
  have hb : IsEmbedding (f (some w)) := (r w).val.property.1
  have hfirstRange : range d.first = f (some v) '' Icc u z := by
    exact paid_affine_subarc_range (f (some v)) d.first d.aStart d.aFinish d.first_eq
  have hsecondRange : range d.second = f (some w) '' Icc gu gz := by
    exact paid_affine_subarc_range (f (some w)) d.second d.bStart d.bFinish d.second_eq
  have hfirstWhole : range d.first ⊆ range (f (some v)) := by
    rw [hfirstRange]
    exact image_subset_range _ _
  have hsecondWhole : range d.second ⊆ range (f (some w)) := by
    rw [hsecondRange]
    exact image_subset_range _ _
  have hfirstDisk : range d.first ⊆ range d.disk := by
    intro y hy
    exact (d.whole_first.symm ▸ hy).1
  have hsecondDisk : range d.second ⊆ range d.disk := by
    intro y hy
    exact (d.whole_second.symm ▸ hy).1
  have hsecondSource : ∀ y ∈ range d.second, y.val ∈ Eguide.source := by
    intro y hy
    exact hGuideCore y (hsecondRange ▸ hy)
  have hsecondZero : ∀ y ∈ range d.second, Eguide y.val 1 = 0 := by
    intro y hy
    apply (hGuideAxis y.val (hsecondSource y hy)).mp
    obtain ⟨q,hq⟩ := hsecondWhole hy
    exact ⟨q,congrArg Subtype.val hq⟩
  let P : Set ↥F := (range d.second \ C₀) ∩
    {p | ∃ i : Option ι, i ≠ some w ∧ p ∈ range (f i)}
  have hPfan : P ⊆ fan.events := by
    intro y hy
    rw [fan.events_exact]
    refine ⟨hdV (hsecondDisk hy.1.1),Or.inr hy.1.1,some w,by simp,?_⟩
    obtain ⟨i,hi,hyi⟩ := hy.2
    exact ⟨i,Ne.symm hi,hsecondWhole hy.1.1,hyi⟩
  have hPfinite : P.Finite := fan.events_finite.subset hPfan
  have hPselectedClear : Disjoint P (range (f (some v))) := by
    apply disjoint_left.mpr
    intro y hy hya
    have hyfirst : y ∈ range d.first := d.whole_first ▸ ⟨hsecondDisk hy.1.1,hya⟩
    apply hy.1.2
    change y ∈ {d.first 0,d.first 1}
    exact d.sides_inter ▸ ⟨hyfirst,hy.1.1⟩
  have hcoordinateInjective : Function.Injective (fun p : ↥P => Eguide p.val.val 0) := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    apply Eguide.injOn (hsecondSource p.val p.property.1.1)
      (hsecondSource q.val q.property.1.1)
    ext i
    fin_cases i
    · exact hpq
    · exact (hsecondZero p.val p.property.1.1).trans
        (hsecondZero q.val q.property.1.1).symm
  letI : Fintype ↥P := hPfinite.fintype
  letI : LinearOrder ↥P := LinearOrder.lift'
    (fun p : ↥P => Eguide p.val.val 0) hcoordinateInjective
  let m := Fintype.card ↥P
  let label : Fin m ≃ ↥P := (Fintype.orderIsoFinOfCardEq ↥P rfl).toEquiv
  have hlabelOrder : ∀ k j : Fin m, k < j →
      Eguide (label k).val.val 0 < Eguide (label j).val.val 0 := by
    intro k j hkj
    exact (Fintype.orderIsoFinOfCardEq ↥P rfl).strictMono hkj
  have hcorners : {f (some w) gu,f (some w) gz} = C₀ := by
    have hzero : d.second 0 = f (some w) d.bStart := by
      simpa [intervalAffine,f,augmented] using d.second_eq 0
    have hone : d.second 1 = f (some w) d.bFinish := by
      simpa [intervalAffine,f,augmented] using d.second_eq 1
    dsimp only [gu,gz,C₀]
    rw [d.zero_eq,d.one_eq,hzero,hone]
    rcases le_total d.bStart d.bFinish with h | h
    · rw [min_eq_left h,max_eq_right h]
    · rw [min_eq_right h,max_eq_left h]
      exact Set.pair_comm _ _
  have hcontacts (i j : Option ι) (hij : i ≠ j) :
      (range (f i) ∩ range (f j)).Finite := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hinv.2.2.2.2 j
    | some i =>
      cases j with
      | none =>
        apply (hinv.2.2.2.2 i).subset
        intro y hy
        exact ⟨hy.2,hy.1⟩
      | some j => exact hinv.1 i j (fun he => hij (congrArg some he))
  let bad : Set ↥F := (⋃ i : {i : Option ι // i ≠ some v},
    range (f (some v)) ∩ range (f i.val)) \ range d.first
  have hbadFinite : bad.Finite :=
    (Set.finite_iUnion (fun i : {i : Option ι // i ≠ some v} =>
      hcontacts (some v) i.val (Ne.symm i.property))).sdiff
  let O : Set ↥F := {y | y.val ∈ Edisk.source} \ bad
  have hO : IsOpen O := (Edisk.open_source.preimage continuous_subtype_val).sdiff
    hbadFinite.isClosed
  have hfirstO : f (some v) '' Icc u z ⊆ O := by
    intro y hy
    have hyfirst : y ∈ range d.first := hfirstRange.symm ▸ hy
    exact ⟨hdEdisk y (hfirstDisk hyfirst),fun hybad => hybad.2 hyfirst⟩
  obtain ⟨a',b',K',ha'0,ha'u,hzb',hb'1,hpad',hK',hdecomp',hcoreK',hdK'⟩ :=
    paid_padded_interval_remainder (f (some v)) ha u z (hA0.trans hAu)
      huz (hzB.trans hB1) O (range d.disk) hO hfirstO (d.whole_first.trans hfirstRange)
  obtain ⟨l,hl⟩ := exists_between (max_lt hAu ha'u)
  obtain ⟨q,hq⟩ := exists_between (lt_min hzB hzb')
  have hAl : A < l := (le_max_left _ _).trans_lt hl.1
  have hal : a' < l := (le_max_right _ _).trans_lt hl.1
  have hqB : q < B := hq.2.trans_le (min_le_left _ _)
  have hqb : q < b' := hq.2.trans_le (min_le_right _ _)
  have holdO : f (some v) '' Icc l q ⊆ O := by
    apply Set.Subset.trans _ hpad'
    apply Set.image_mono
    exact Icc_subset_Icc hal.le hqb.le
  have holdDisk : f (some v) '' Icc l q ⊆ {y | y.val ∈ Edisk.source} :=
    holdO.trans sdiff_subset
  have hattachmentClear : ∀ i : Option ι, i ≠ some v →
      Disjoint ((f (some v) '' Icc l q) \ range d.first) (range (f i)) := by
    intro i hi
    apply disjoint_left.mpr
    intro y hy hyi
    apply (holdO hy.1).2
    refine ⟨?_,hy.2⟩
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,image_subset_range _ _ hy.1,hyi⟩
  have hattachmentNotFirst : f (some v) l ∉ range d.first ∧
      f (some v) q ∉ range d.first := by
    constructor
    · rw [hfirstRange]
      rintro ⟨t,ht,he⟩
      have heq : t = l := ha.injective he
      exact (not_le_of_gt hl.2) (heq ▸ ht.1)
    · rw [hfirstRange]
      rintro ⟨t,ht,he⟩
      have heq : t = q := ha.injective he
      exact (not_le_of_gt hq.1) (heq ▸ ht.2)
  have hattachmentsClear : ∀ i : Option ι, i ≠ some v →
      f (some v) l ∉ range (f i) ∧ f (some v) q ∉ range (f i) := by
    intro i hi
    have hlq : l ≤ q := (hl.2.trans (huz.trans hq.1)).le
    exact ⟨fun hli => disjoint_left.mp (hattachmentClear i hi)
        ⟨⟨l,⟨le_rfl,hlq⟩,rfl⟩,hattachmentNotFirst.1⟩ hli,
      fun hqi => disjoint_left.mp (hattachmentClear i hi)
        ⟨⟨q,⟨hlq,le_rfl⟩,rfl⟩,hattachmentNotFirst.2⟩ hqi⟩
  let diskAmbient : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun t => (d.disk t).val,continuous_subtype_val.comp d.disk.continuous⟩
  have hdiskAmbient : IsEmbedding diskAmbient := IsEmbedding.subtypeVal.comp d.disk_embedded
  have hdiskRange : range diskAmbient = Subtype.val '' range d.disk := by
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨d.disk t,⟨t,rfl⟩,rfl⟩
    · rintro ⟨p,⟨t,rfl⟩,rfl⟩
      exact ⟨t,rfl⟩
  have hDiskDensity : closure (interior (range diskAmbient)) = range diskAmbient := by
    let Q : Set (Metric.closedBall (0 : Plane) 1) :=
      {t | t.val ∈ Metric.ball (0 : Plane) 1}
    have hQimage : Subtype.val '' Q = Metric.ball (0 : Plane) 1 := by
      ext y
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ht
      · intro hy
        exact ⟨⟨y,Metric.ball_subset_closedBall hy⟩,hy,rfl⟩
    have hQclosure : closure Q = univ := by
      rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,hQimage,
        closure_ball (0 : Plane) (by norm_num : (1 : ℝ) ≠ 0)]
      ext y
      simp only [mem_preimage,mem_univ,iff_true]
      exact y.property
    have hdense : range diskAmbient ⊆ closure (diskAmbient '' Q) := by
      rw [← image_univ,← hQclosure]
      exact image_closure_subset_closure_image diskAmbient.continuous
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq diskAmbient hdiskAmbient]
    exact Subset.antisymm
      (closure_minimal (image_subset_range _ _) (isCompact_range diskAmbient.continuous).isClosed)
      hdense
  have hDiskFrontier : frontier (range diskAmbient) =
      Subtype.val '' (range d.first ∪ range d.second) := by
    rw [(isCompact_range diskAmbient.continuous).isClosed.frontier_eq,
      CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq diskAmbient hdiskAmbient]
    rw [← d.boundary_image]
    ext y
    constructor
    · rintro ⟨⟨t,rfl⟩,htnot⟩
      refine ⟨d.disk t,⟨t,?_,rfl⟩,rfl⟩
      have htge : 1 ≤ dist t.val (0 : Plane) := by
        by_contra hnot
        exact htnot ⟨t,lt_of_not_ge hnot,rfl⟩
      exact le_antisymm t.property htge
    · rintro ⟨p,⟨t,ht,rfl⟩,rfl⟩
      refine ⟨⟨t,rfl⟩,?_⟩
      rintro ⟨u,hu,he⟩
      have hut : u = t := hdiskAmbient.injective he
      subst u
      change dist t.val (0 : Plane) < 1 at hu
      change dist t.val (0 : Plane) = 1 at ht
      exact (ne_of_lt hu) ht
  have hCornerOutsideDisk (arc : C(Interval,↥F))
      (hfirst : Disjoint (range arc) (range d.first))
      (hguide : Disjoint (range arc) (range (f (some w))))
      (hstart : arc 0 ∉ range d.disk) :
      ∀ t, arc t ∉ range d.disk := by
    let a : C(Interval,S) := ⟨fun t => (arc t).val,continuous_subtype_val.comp arc.continuous⟩
    have hclosed : IsClosed (range diskAmbient) := (isCompact_range diskAmbient.continuous).isClosed
    have hconn : IsPreconnected (range a) := isPreconnected_range a.continuous
    have hcover : range a ⊆ interior (range diskAmbient) ∪ (range diskAmbient)ᶜ := by
      rintro y ⟨t,rfl⟩
      by_cases hyd : a t ∈ range diskAmbient
      · left
        by_contra hyn
        have hyf : a t ∈ frontier (range diskAmbient) := hclosed.frontier_eq ▸ ⟨hyd,hyn⟩
        rw [hDiskFrontier] at hyf
        obtain ⟨z,hz,he⟩ := hyf
        have heq : z = arc t := Subtype.ext he
        subst z
        rcases hz with hz | hz
        · exact disjoint_left.mp hfirst ⟨t,rfl⟩ hz
        · exact disjoint_left.mp hguide ⟨t,rfl⟩ (hsecondWhole hz)
      · exact Or.inr hyd
    have hdis : Disjoint (interior (range diskAmbient)) (range diskAmbient)ᶜ :=
      disjoint_left.mpr (fun y hy hn => hn (interior_subset hy))
    rcases hconn.subset_or_subset isOpen_interior hclosed.isOpen_compl hdis hcover with hi | ho
    · apply False.elim
      apply hstart
      have he := interior_subset (hi ⟨0,rfl⟩)
      rw [hdiskRange] at he
      obtain ⟨y,hy,he⟩ := he
      exact (Subtype.ext he : y = arc 0) ▸ hy
    · intro t ht
      apply ho ⟨t,rfl⟩
      rw [hdiskRange]
      exact ⟨arc t,ht,rfl⟩
  have hGuideInterior : Eguide.source ⊆ interior F := by
    intro y hy
    exact (hEdiskClosure (subset_closure (hGuideSource hy).1)).2
  have hAxisPoint (ξ : ℝ) (hξ : ξ ∈ Icc (-1 : ℝ) 1) :
      ∃ y : ↥F, y.val ∈ Eguide.source ∧ y ∈ range d.second ∧
        Eguide y.val = Plane.mk ξ 0 := by
    have hsq : Plane.mk ξ 0 ∈ Plane.closedSquare 0 1 := by
      apply mem_closedSquare_zero_one.mpr
      change max |ξ| |(0 : ℝ)| ≤ 1
      exact max_le (abs_le.mpr hξ) (by norm_num)
    have htarget := hGuideSquare hsq
    have hsource := Eguide.map_target htarget
    let y : ↥F := ⟨Eguide.symm (Plane.mk ξ 0),interior_subset (hGuideInterior hsource)⟩
    have hcoord : Eguide y.val = Plane.mk ξ 0 := Eguide.right_inv htarget
    have hyb : y ∈ range (f (some w)) := by
      obtain ⟨t,ht⟩ := (hGuideAxis y.val hsource).mpr (by rw [hcoord]; rfl)
      exact ⟨t,Subtype.ext ht⟩
    refine ⟨y,hsource,?_,hcoord⟩
    rw [hsecondRange]
    apply Eq.mp (congrArg (fun U : Set ↥F => y ∈ U) hGuideTrace)
    exact ⟨⟨hsource,hcoord.symm ▸ hsq⟩,hyb⟩
  have hAxisSelectedClear (ξ : ℝ) (hξlo : -1 < ξ) (hξhi : ξ < 1) :
      ∃ y : S, y ∈ Eguide.source ∧ Eguide y = Plane.mk ξ 0 ∧
        y ∉ Subtype.val '' range (f (some v)) := by
    obtain ⟨y,hySource,hySecond,hyCoord⟩ := hAxisPoint ξ ⟨hξlo.le,hξhi.le⟩
    refine ⟨y.val,hySource,hyCoord,?_⟩
    rintro ⟨p,hp,hpy⟩
    have heq : p = y := Subtype.ext hpy
    have hyFirst : y ∈ range d.first := d.whole_first ▸ ⟨hsecondDisk hySecond,heq ▸ hp⟩
    have hyCorner : y ∈ C₀ := by
      change y ∈ {d.first 0,d.first 1}
      exact d.sides_inter ▸ ⟨hyFirst,hySecond⟩
    rw [← hcorners] at hyCorner
    rcases mem_insert_iff.mp hyCorner with he | he
    · rw [he] at hyCoord
      have hx := congrArg (fun p : Plane => p 0) (hGuideZero.symm.trans hyCoord)
      exact (ne_of_gt hξlo) hx.symm
    · have he' := mem_singleton_iff.mp he
      rw [he'] at hyCoord
      have hx := congrArg (fun p : Plane => p 0) (hGuideOne.symm.trans hyCoord)
      exact (ne_of_lt hξhi) hx.symm
  have hSelectedStrip (L R : ℝ) (hL : -1 < L) (hLR : L < R) (hR : R < 1) :
      ∃ ε : ℝ, 0 < ε ∧ ∀ z : Plane, z 0 ∈ Icc L R → |z 1| < ε →
        z ∈ Eguide.target ∧ Eguide.symm z ∉ Subtype.val '' range (f (some v)) := by
    let xy : Plane ≃ₜ ℝ × ℝ := {
      toFun := fun z => (z 0,z 1)
      invFun := fun z => Plane.mk z.1 z.2
      left_inv := by intro z; ext i; fin_cases i <;> rfl
      right_inv := by intro z; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let Q := Eguide '' (Eguide.source ∩ (Subtype.val '' range (f (some v)))ᶜ)
    have hQ : IsOpen Q := Eguide.isOpen_image_source_inter
      ((isCompact_range (f (some v)).continuous).image continuous_subtype_val).isClosed.isOpen_compl
    let O := xy '' Q
    have hO : IsOpen O := xy.isOpenMap _ hQ
    let T : Set (ℝ × ℝ) := (fun x : ℝ => (x,0)) '' Icc L R
    have hT : IsCompact T := isCompact_Icc.image (by fun_prop)
    have hTO : T ⊆ O := by
      rintro z ⟨ξ,hξ,rfl⟩
      obtain ⟨y,hyE,hEy,hyClear⟩ := hAxisSelectedClear ξ (hL.trans_le hξ.1)
        (hξ.2.trans_lt hR)
      refine ⟨Eguide y,⟨y,⟨hyE,hyClear⟩,rfl⟩,?_⟩
      rw [hEy]
      rfl
    obtain ⟨ε,hε,hclear⟩ := hT.exists_thickening_subset_open hO hTO
    refine ⟨ε,hε,?_⟩
    intro z hz hy
    have hxy : xy z ∈ O := by
      apply hclear
      apply Metric.mem_thickening_iff.mpr
      refine ⟨(z 0,0),⟨z 0,hz,rfl⟩,?_⟩
      change dist (z 0,z 1) (z 0,0) < ε
      simpa [Prod.dist_eq,Real.dist_eq] using hy
    obtain ⟨v,⟨y,⟨hyE,hyClear⟩,hEy⟩,hv⟩ := hxy
    have hEyZ : Eguide y = z := hEy.trans (xy.injective hv)
    refine ⟨hEyZ ▸ Eguide.map_source hyE,?_⟩
    rw [← hEyZ,Eguide.left_inv hyE]
    exact hyClear
  have hExteriorStrip (L R : ℝ) (hL : -1 < L) (hLR : L < R) (hR : R < 1) :
      ∃ ε σ : ℝ, 0 < ε ∧ (σ = -1 ∨ σ = 1) ∧
        (∀ z : Plane, L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε →
          z ∈ Eguide.target ∧ Eguide.symm z ∉ Subtype.val '' range (f (some v))) ∧
        (∀ z : Plane, L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε → z 1 ≠ 0 →
          (Eguide.symm z ∉ range diskAmbient ↔ 0 < σ * z 1)) := by
    obtain ⟨ε,hε,hclear⟩ := hSelectedStrip L R hL hLR hR
    have hTarget : {z : Plane | L < z 0 ∧ z 0 < R ∧ -ε < z 1 ∧ z 1 < ε} ⊆
        Eguide.target := fun z hz => (hclear z ⟨hz.1.le,hz.2.1.le⟩ (abs_lt.mpr hz.2.2)).1
    have hFrontier (z : Plane) (hzL : L < z 0) (hzR : z 0 < R)
        (hzlo : -ε < z 1) (hzhi : z 1 < ε) :
        Eguide.symm z ∈ frontier (range diskAmbient) ↔ z 1 = 0 := by
      have hzTarget := hTarget ⟨hzL,hzR,hzlo,hzhi⟩
      have hzSource := Eguide.map_target hzTarget
      have hcoord := Eguide.right_inv hzTarget
      constructor
      · intro hfront
        rw [hDiskFrontier] at hfront
        obtain ⟨y,hy,hyz⟩ := hfront
        rcases hy with hyFirst | hySecond
        · exact False.elim ((hclear z ⟨hzL.le,hzR.le⟩ (abs_lt.mpr ⟨hzlo,hzhi⟩)).2
            ⟨y,hfirstWhole hyFirst,hyz⟩)
        · have he : Eguide (Eguide.symm z) 1 = 0 := by
            rw [← hyz]
            exact hsecondZero y hySecond
          rwa [hcoord] at he
      · intro hz0
        obtain ⟨y,hySource,hySecond,hyCoord⟩ := hAxisPoint (z 0)
          ⟨(hL.trans hzL).le,(hzR.trans hR).le⟩
        have hmk : Plane.mk (z 0) 0 = z := by
          ext i
          fin_cases i
          · rfl
          · exact hz0.symm
        have hyz : y.val = Eguide.symm z := by
          apply Eguide.injOn hySource hzSource
          rw [hyCoord,hmk,hcoord]
        rw [hDiskFrontier]
        exact ⟨y,Or.inr hySecond,hyz⟩
    have hregularDisk : range diskAmbient ⊆ closure (interior (range diskAmbient)) := by
      rw [hDiskDensity]
    obtain ⟨σ,hσ,hside⟩ := actual_chart_strip_exterior_half Eguide (range diskAmbient)
      (isCompact_range diskAmbient.continuous).isClosed hregularDisk L R ε hLR hε
      hTarget hFrontier
    exact ⟨ε,σ,hε,hσ,fun z hzl hzr hzlo hzhi =>
      hclear z ⟨hzl.le,hzr.le⟩ (abs_lt.mpr ⟨hzlo,hzhi⟩),hside⟩
  have hFanTrace (p : ↥F) (W : IncidentFanWindow F f V p)
      (i : incidentIndex f p) (y : ↥F) (hy : y.val ∈ W.chart.source)
      (hyball : W.chart y.val ∈ Metric.closedBall (0 : Plane) 1) :
      y ∈ range (f i.val) ↔ W.chart y.val ∈
        segment ℝ (incidentPorts f p W.chart W.left W.right (i,false)) 0 ∪
          segment ℝ 0 (incidentPorts f p W.chart W.left W.right (i,true)) := by
    constructor
    · intro hyf
      have hcut : y ∈ f i.val '' Icc (W.left i) (W.right i) :=
        W.whole_closed i ▸ ⟨⟨hy,hyball⟩,hyf⟩
      obtain ⟨t,ht,rfl⟩ := hcut
      exact W.radial_trace i ▸ ⟨t,ht,rfl⟩
    · intro hyf
      obtain ⟨t,ht,he⟩ := W.radial_trace i |>.symm ▸ hyf
      have hcut : f i.val t ∈ f i.val '' Icc (W.left i) (W.right i) := ⟨t,ht,rfl⟩
      have hs : (f i.val t).val ∈ W.chart.source := (W.whole_closed i |>.symm ▸ hcut).1.1
      exact ⟨t,Subtype.ext (W.chart.injOn hs hy he)⟩
  have hHorizontalPorts (u v z : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
      (huv : u ≠ v) (hu1 : u 1 = 0) (hv1 : v 1 = 0) (hz : ‖z‖ ≤ 1) :
      z ∈ segment ℝ u 0 ∪ segment ℝ 0 v ↔ z 1 = 0 := by
    have hun : u ≠ 0 := by intro he; simpa [he] using hu
    have hq : u 0 ^ 2 = v 0 ^ 2 := by
      have a := EuclideanSpace.real_norm_sq_eq u
      have b := EuclideanSpace.real_norm_sq_eq v
      simp [hu,hv,hu1,hv1,Fin.sum_univ_two] at a b
      linarith
    have hvu : v = -u := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq with he | he
      · exact (huv (by ext i; fin_cases i; exact he; simpa [hu1,hv1])).elim
      · ext i
        fin_cases i
        · change v 0 = -u 0
          linarith
        · change v 1 = -u 1
          rw [hv1,hu1,neg_zero]
    rw [hvu,segment_symm ℝ u 0]
    constructor
    · rintro (⟨a,b,ha,hb,hab,he⟩ | ⟨a,b,ha,hb,hab,he⟩)
      · have := congrArg (fun z : Plane => z 1) he
        simpa [hu1] using this.symm
      · have := congrArg (fun z : Plane => z 1) he
        simpa [hu1] using this.symm
    · intro hz1
      have hd : Plane.det u z = 0 := by simp [Plane.det,hu1,hz1]
      obtain ⟨s,hs⟩ := (Plane.det_eq_zero_iff_smul u z hun).mp hd
      have hns : |s| ≤ 1 := by
        rw [hs,norm_smul,Real.norm_eq_abs,hu,mul_one] at hz
        exact hz
      rcases le_total 0 s with hp | hm
      · left
        rw [hs]
        exact ⟨1-s,s,sub_nonneg.mpr ((le_abs_self s).trans hns),hp,by ring,by simp⟩
      · right
        have he : z = (-s) • (-u) := by rw [hs]; module
        rw [he]
        exact ⟨1-(-s),-s,sub_nonneg.mpr ((neg_le_abs s).trans hns),
          neg_nonneg.mpr hm,by ring,by simp⟩
  have hFanAxis (p : ↥F) (W : IncidentFanWindow F f V p)
      (i : incidentIndex f p)
      (hi0 : incidentPorts f p W.chart W.left W.right (i,false) 1 = 0)
      (hi1 : incidentPorts f p W.chart W.left W.right (i,true) 1 = 0)
      (y : ↥F) (hy : y.val ∈ W.chart.source)
      (hyball : W.chart y.val ∈ Metric.closedBall (0 : Plane) 1) :
      y ∈ range (f i.val) ↔ W.chart y.val 1 = 0 := by
    apply (hFanTrace p W i y hy hyball).trans
    apply hHorizontalPorts
      (incidentPorts f p W.chart W.left W.right (i,false))
      (incidentPorts f p W.chart W.left W.right (i,true)) (W.chart y.val)
    · simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,false)
    · simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,true)
    · exact fun he => Bool.false_ne_true (congrArg Prod.snd (W.ports_injective he))
    · exact hi0
    · exact hi1
    · simpa only [Metric.mem_closedBall,dist_zero_right] using hyball
  have hRadialContactUnique (a b z : Plane) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
      (hab : a ≠ b) (hza : z ∈ segment ℝ (0 : Plane) a)
      (hzb : z ∈ segment ℝ (0 : Plane) b) : z = 0 := by
    rw [segment_eq_image'] at hza hzb
    obtain ⟨t,ht,he⟩ := hza
    obtain ⟨s,hs,hf⟩ := hzb
    have hte : t • a = z := by simpa using he
    have hse : s • b = z := by simpa using hf
    have hts : t = s := by
      have hn := congrArg norm (hte.trans hse.symm)
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1,
        abs_of_nonneg hs.1,ha,hb,mul_one] using hn
    by_cases ht0 : t = 0
    · simpa [ht0] using hte.symm
    · have hab' : a = b := by
        have heq : t • a = t • b := hte.trans (hts ▸ hse.symm)
        have heq' := congrArg (fun y : Plane => t⁻¹ • y) heq
        simpa [smul_smul,ht0] using heq'
      exact (hab hab').elim
  have hFanContactUnique (p : ↥F) (W : IncidentFanWindow F f V p)
      (i j : incidentIndex f p) (hij : i.val ≠ j.val)
      (y : ↥F) (hy : y.val ∈ W.chart.source)
      (hyball : W.chart y.val ∈ Metric.closedBall (0 : Plane) 1)
      (hyi : y ∈ range (f i.val)) (hyj : y ∈ range (f j.val)) : y = p := by
    have hArm (k : incidentIndex f p) (hyk : y ∈ range (f k.val)) :
        ∃ β : Bool, W.chart y.val ∈ segment ℝ (0 : Plane)
          (incidentPorts f p W.chart W.left W.right (k,β)) := by
      rcases (hFanTrace p W k y hy hyball).mp hyk with hh | hh
      · refine ⟨false,?_⟩
        rwa [segment_symm ℝ _ (0 : Plane)] at hh
      · exact ⟨true,hh⟩
    obtain ⟨β,hβ⟩ := hArm i hyi
    obtain ⟨γ,hγ⟩ := hArm j hyj
    have hz : W.chart y.val = 0 := hRadialContactUnique _ _ _
      (by simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (i,β))
      (by simpa only [Metric.mem_sphere,dist_zero_right] using W.ports_on_sphere (j,γ))
      (fun he => hij (congrArg (fun z : incidentIndex f p × Bool => z.1.val)
        (W.ports_injective he))) hβ hγ
    exact Subtype.ext (W.chart.injOn hy W.contact_in_source (hz.trans W.contact_zero.symm))
  have hFanShrinking (p : ↥F) (W : IncidentFanWindow F f V p)
      (U : Set S) (hU : IsOpen U) (hpU : p.val ∈ U) :
      ∃ η : ℝ, 0 < η ∧ η < 1 ∧
        Metric.closedBall (0 : Plane) η ⊆ W.chart.target ∧
        W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ U := by
    let Q := W.chart '' (W.chart.source ∩ U)
    have hQ : IsOpen Q := W.chart.isOpen_image_source_inter hU
    have hzero : (0 : Plane) ∈ Q := ⟨p.val,⟨W.contact_in_source,hpU⟩,W.contact_zero⟩
    obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hQ 0 hzero
    let η := min ρ 1 / 2
    have hη : 0 < η := half_pos (lt_min hρ zero_lt_one)
    have hηρ : η < ρ := by dsimp [η]; have := min_le_left ρ 1; linarith
    have hη1 : η < 1 := by dsimp [η]; have := min_le_right ρ 1; linarith
    have hηQ : Metric.closedBall (0 : Plane) η ⊆ Q :=
      (Metric.closedBall_subset_ball hηρ).trans hball
    refine ⟨η,hη,hη1,?_,?_⟩
    · intro z hz
      obtain ⟨y,hy,he⟩ := hηQ hz
      exact he ▸ W.chart.map_source hy.1
    · rintro y ⟨z,hz,rfl⟩
      obtain ⟨u,hu,he⟩ := hηQ hz
      rw [← he,W.chart.left_inv hu.1]
      exact hu.2
  have hSignedHalfChoice
      (E Q : OpenPartialHomeomorph S Plane) (p : S)
      (hpQ : p ∈ Q.source) (hQp : Q p = 0) (hEp : E p 1 = 0)
      (η : ℝ) (hη : 0 < η)
      (hBall : Metric.ball (0 : Plane) η ⊆ Q.target)
      (hInvE : Q.symm '' Metric.ball (0 : Plane) η ⊆ E.source)
      (hAxis : ∀ y ∈ Metric.ball (0 : Plane) η,
        E (Q.symm y) 1 = 0 ↔ y 1 = 0)
      (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
      ∃ κ : ℝ, (κ = -1 ∨ κ = 1) ∧
        ∀ y ∈ Metric.ball (0 : Plane) η,
          0 < κ*y 1 → 0 < σ*E (Q.symm y) 1 := by
    have hσsq : σ*σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    let C := Q.source ∩ Q ⁻¹' Metric.ball (0 : Plane) η
    have hC : IsOpen C := Q.isOpen_inter_preimage Metric.isOpen_ball
    have hCE : C ⊆ E.source := by
      intro x hx
      exact hInvE ⟨Q x,hx.2,Q.left_inv hx.1⟩
    have hEC : IsOpen (E '' C) := E.isOpen_image_of_subset_source hC hCE
    have hpEC : E p ∈ E '' C := by
      refine ⟨p,⟨hpQ,?_⟩,rfl⟩
      change Q p ∈ Metric.ball (0 : Plane) η
      rw [hQp]
      simpa using hη
    let v : ℝ → Plane := fun t => E p + Plane.mk 0 (σ*t)
    have hv : Continuous v := by fun_prop
    have hOpen : IsOpen (v ⁻¹' (E '' C)) := hEC.preimage hv
    have h0 : (0 : ℝ) ∈ v ⁻¹' (E '' C) := by
      have hz : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
      simpa [v,hz] using hpEC
    obtain ⟨r,hr,hvr⟩ := Metric.isOpen_iff.mp hOpen 0 h0
    let τ := r/2
    have hτ : 0 < τ := half_pos hr
    obtain ⟨x,hx,hEx⟩ := hvr (show τ ∈ Metric.ball (0 : ℝ) r by
      rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hτ]
      dsimp [τ]
      linarith)
    have hExy : E x 1 = σ*τ := by
      have hh := congrArg (fun z : Plane => z 1) hEx
      change E x 1 = E p 1 + σ*τ at hh
      simpa [hEp] using hh
    let q := Q x
    have hqBall : q ∈ Metric.ball (0 : Plane) η := hx.2
    have hqx : Q.symm q = x := Q.left_inv hx.1
    have hqNe : q 1 ≠ 0 := by
      intro he
      have hz := (hAxis q hqBall).mpr he
      rw [hqx,hExy] at hz
      exact (mul_ne_zero hσne (ne_of_gt hτ)) hz
    let κ : ℝ := if 0 < q 1 then 1 else -1
    have hκ : κ = -1 ∨ κ = 1 := by dsimp [κ]; split_ifs <;> simp
    have hqSign : 0 < κ*q 1 := by
      dsimp [κ]
      split_ifs with hq
      · simpa using hq
      · have hn : q 1 < 0 := lt_of_le_of_ne (le_of_not_gt hq) hqNe
        simpa using neg_pos.mpr hn
    let T : Set Plane := Metric.ball (0 : Plane) η ∩ {y | 0 < κ*y 1}
    have hT : IsPreconnected T := (convex_ball (0 : Plane) η).inter
      (convex_halfSpace_gt (𝕜 := ℝ) (f := fun y : Plane => κ*y 1)
        ⟨by intros x y; change κ*(x 1+y 1)=κ*x 1+κ*y 1; ring,
         by intros a x; change κ*(a*x 1)=a*(κ*x 1); ring⟩ 0) |>.isPreconnected
    let G : T → ℝ := fun y => σ*E (Q.symm y.val) 1
    have hQS : Continuous (fun y : T => Q.symm y.val) :=
      Q.symm.continuousOn.comp_continuous continuous_subtype_val
        (fun y => hBall y.property.1)
    have hEQS : Continuous (fun y : T => E (Q.symm y.val)) :=
      E.continuousOn.comp_continuous hQS
        (fun y => hInvE ⟨y.val,y.property.1,rfl⟩)
    have hG : Continuous G := continuous_const.mul
      ((show Continuous (fun z : Plane => z 1) by fun_prop).comp hEQS)
    have hGNe (y : T) : G y ≠ 0 := by
      apply mul_ne_zero hσne
      intro he
      have hz := (hAxis y.val y.property.1).mp he
      have hp := y.property.2
      change 0 < κ*y.val 1 at hp
      rw [hz,mul_zero] at hp
      exact (lt_irrefl 0) hp
    have hRangeConn : IsPreconnected (range G) := by
      have : PreconnectedSpace T := isPreconnected_iff_preconnectedSpace.mp hT
      exact isPreconnected_range hG
    have hRangeSub : range G ⊆ Ioi 0 ∪ Iio 0 := by
      rintro z ⟨y,rfl⟩
      exact (lt_or_gt_of_ne (hGNe y)).symm
    let qp : T := ⟨q,⟨hqBall,hqSign⟩⟩
    have hqp : 0 < G qp := by
      change 0 < σ*E (Q.symm q) 1
      rw [hqx,hExy,← mul_assoc,hσsq,one_mul]
      exact hτ
    have hPositive : range G ⊆ Ioi 0 :=
      hRangeConn.subset_left_of_subset_union isOpen_Ioi isOpen_Iio
        (disjoint_left.mpr (by intro z hz hz'; change 0 < z at hz; change z < 0 at hz'; linarith))
        hRangeSub ⟨G qp,⟨⟨qp,rfl⟩,hqp⟩⟩
    exact ⟨κ,hκ,fun y hy hys => hPositive ⟨⟨y,⟨hy,hys⟩⟩,rfl⟩⟩
  have hEventAxisFan (p : ↥P) :
      ∃ W : IncidentFanWindow F f V p.val,
        (RegionalChordNormalization.chartPull F W.chart (Metric.closedBall (0 : Plane) 1) ⊆
          RegionalChordNormalization.chartPull F (fan.window ⟨p.val,hPfan p.property⟩).chart
            (Metric.ball (0 : Plane) 1)) ∧
        (incidentPorts f p.val W.chart W.left W.right
          (⟨some w,hsecondWhole p.property.1.1⟩,false) 1 = 0) ∧
        (incidentPorts f p.val W.chart W.left W.right
          (⟨some w,hsecondWhole p.property.1.1⟩,true) 1 = 0) ∧
        (∀ j : incidentIndex f p.val, j.val ≠ some w →
          ((0 < incidentPorts f p.val W.chart W.left W.right (j,false) 1 ∧
            incidentPorts f p.val W.chart W.left W.right (j,true) 1 < 0) ∨
          (incidentPorts f p.val W.chart W.left W.right (j,false) 1 < 0 ∧
            0 < incidentPorts f p.val W.chart W.left W.right (j,true) 1))) ∧
        ∃ η : ℝ, 0 < η ∧ η < 1 ∧
          Metric.closedBall (0 : Plane) η ⊆ W.chart.target ∧
          W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ Eguide.source ∧
          Disjoint (RegionalChordNormalization.chartPull F W.chart (Metric.closedBall (0 : Plane) η))
            (range (f (some v))) := by
    obtain ⟨W,hWsmall,hW0,hW1,hWsign⟩ :=
      fan.selected_axis_fans ⟨p.val,hPfan p.property⟩ (some w) (by simp)
        (hsecondWhole p.property.1.1)
    obtain ⟨η,hη,hη1,hηtarget,hηguide⟩ :=
      hFanShrinking p.val W Eguide.source Eguide.open_source (hsecondSource p.val p.property.1.1)
    refine ⟨W,hWsmall,hW0,hW1,hWsign,η,hη,hη1,hηtarget,hηguide,?_⟩
    apply (W.nonincident_clear (some v) ?_).mono_left
    · intro y hy
      exact ⟨hy.1,Metric.closedBall_subset_closedBall hη1.le hy.2⟩
    · exact fun hp => disjoint_left.mp hPselectedClear p.property hp
  have hSignedRadialPatch {Jp : Type} [Fintype Jp]
      (up down : Jp → Plane) (hup : ∀ j, 0 < up j 1)
      (hdown : ∀ j, down j 1 < 0) (η : ℝ) (hη : 0 < η)
      (κ : ℝ) (hκ : κ = -1 ∨ κ = 1) :
      ∃ δ H : ℝ, 0 < δ ∧ 0 < H ∧
        Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η ∧
        Plane.mk δ 0 ∈ Metric.ball (0 : Plane) η ∧
        ∀ h : ℝ, 0 < h → h < H →
          let C := segment ℝ (Plane.mk (-δ) (κ*h)) (Plane.mk δ (κ*h))
          C ⊆ Metric.ball (0 : Plane) η ∧
          (∀ j, Plane.mk (-δ) (κ*h) ∉ segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j)) ∧
          (∀ j, Plane.mk δ (κ*h) ∉ segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j)) ∧
          Disjoint C {y | y 1 = 0} ∧
          (∀ j, (C ∩ (segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j))).Finite ∧
            (C ∩ (segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j))).ncard ≤ 1) := by
    rcases hκ with rfl | rfl
    · obtain ⟨δ,H,hδ,hH,hleft,hright,hpatch⟩ :=
        actual_uniform_radial_contact_patch (fun j => -down j) (fun j => -up j)
          (fun j => by simpa using neg_pos.mpr (hdown j))
          (fun j => by simpa using neg_neg_of_pos (hup j)) η hη
      have hnegSegment (a b z : Plane) :
          z ∈ segment ℝ a b ↔ -z ∈ segment ℝ (-a) (-b) := by
        let N : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.neg ℝ
        have hi := image_segment ℝ N.toLinearMap.toAffineMap a b
        change N '' segment ℝ a b = segment ℝ (N a) (N b) at hi
        change z ∈ segment ℝ a b ↔ N z ∈ segment ℝ (N a) (N b)
        rw [← hi]
        exact ⟨fun hz => ⟨z,hz,rfl⟩,fun ⟨w,hw,he⟩ => N.injective he ▸ hw⟩
      have hnegStar (j : Jp) (z : Plane) :
          z ∈ segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j) ↔
          -z ∈ segment ℝ (0 : Plane) (-down j) ∪ segment ℝ 0 (-up j) := by
        simp only [mem_union]
        have h1 := hnegSegment 0 (up j) z
        have h2 := hnegSegment 0 (down j) z
        simp only [neg_zero] at h1 h2
        exact (or_congr h1 h2).trans or_comm
      have hnegMk (a b : ℝ) : -Plane.mk a b = Plane.mk (-a) (-b) := by
        ext i
        fin_cases i <;> rfl
      refine ⟨δ,H,hδ,hH,hleft,hright,?_⟩
      intro h hh hhH
      obtain ⟨hC,hL,hR,hAxis,hCounts⟩ := hpatch h hh hhH
      simp only [neg_one_mul]
      let C := segment ℝ (Plane.mk (-δ) (-h)) (Plane.mk δ (-h))
      have hnegC (z : Plane) (hz : z ∈ C) :
          -z ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) := by
        have he := (hnegSegment (Plane.mk (-δ) (-h)) (Plane.mk δ (-h)) z).mp hz
        simpa only [hnegMk,neg_neg,segment_symm ℝ (Plane.mk δ h)] using he
      refine ⟨?_,?_,?_,?_,?_⟩
      · intro z hz
        have hh := hC (hnegC z hz)
        simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hh
      · intro j hj
        have he := (hnegStar j _).mp hj
        simp only [hnegMk,neg_neg] at he
        exact hR j he
      · intro j hj
        have he := (hnegStar j _).mp hj
        simp only [hnegMk,neg_neg] at he
        exact hL j he
      · apply disjoint_left.mpr
        intro z hz hz0
        apply disjoint_left.mp hAxis (hnegC z hz)
        change -z 1 = 0
        exact neg_eq_zero.mpr hz0
      · intro j
        have hSub : (C ∩ (segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j))).Subsingleton := by
          intro z hz y hy
          have hOldSub := (ncard_le_one (hCounts j).1).mp (hCounts j).2
          have he : -z = -y := hOldSub (-z)
            ⟨hnegC z hz.1,(hnegStar j z).mp hz.2⟩ (-y)
            ⟨hnegC y hy.1,(hnegStar j y).mp hy.2⟩
          exact neg_injective he
        exact ⟨hSub.finite,(ncard_le_one hSub.finite).mpr hSub⟩
    · simpa only [one_mul] using
        actual_uniform_radial_contact_patch up down hup hdown η hη
  have hEventPatch (p : ↥P) (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
      ∃ W : IncidentFanWindow F f V p.val, ∃ η δ H κ : ℝ,
        (κ = -1 ∨ κ = 1) ∧
        (RegionalChordNormalization.chartPull F W.chart (Metric.closedBall (0 : Plane) 1) ⊆
          RegionalChordNormalization.chartPull F (fan.window ⟨p.val,hPfan p.property⟩).chart
            (Metric.ball (0 : Plane) 1)) ∧
        0 < η ∧ η < 1 ∧ 0 < δ ∧ 0 < H ∧
        Metric.closedBall (0 : Plane) η ⊆ W.chart.target ∧
        W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ Eguide.source ∧
        Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η ∧
        Plane.mk δ 0 ∈ Metric.ball (0 : Plane) η ∧
        (∀ y : ↥F, y.val ∈ W.chart.source → W.chart y.val ∈ Metric.closedBall 0 η →
          (y ∈ range (f (some w)) ↔ W.chart y.val 1 = 0)) ∧
        (∀ y ∈ Metric.ball (0 : Plane) η,
          0 < κ*y 1 → 0 < σ*Eguide (W.chart.symm y) 1) ∧
        ∀ h : ℝ, 0 < h → h < H →
          let C := segment ℝ (Plane.mk (-δ) (κ*h)) (Plane.mk δ (κ*h))
          C ⊆ Metric.ball (0 : Plane) η ∧
          (∀ y : ↥F, y.val ∈ W.chart.source → W.chart y.val ∈ C →
            y ∉ range (f (some v)) ∧ y ∉ range (f (some w))) ∧
          (∀ y : ↥F, y.val ∈ W.chart.source →
            (W.chart y.val = Plane.mk (-δ) (κ*h) ∨ W.chart y.val = Plane.mk δ (κ*h)) →
            ∀ i : Option ι, y ∉ range (f i)) ∧
          (∀ i : Option ι,
            ({y : ↥F | y.val ∈ W.chart.source ∧ W.chart y.val ∈ C} ∩ range (f i)).Finite ∧
            ({y : ↥F | y.val ∈ W.chart.source ∧ W.chart y.val ∈ C} ∩ range (f i)).ncard ≤
              if p.val ∈ range (f i) then 1 else 0) := by
    obtain ⟨W,hWsmall,hW0,hW1,hWsign,η,hη,hη1,hηtarget,hηguide,hηselected⟩ := hEventAxisFan p
    let Jp := {j : incidentIndex f p.val // j.val ≠ some w}
    letI : Fintype (incidentIndex f p.val) := by unfold incidentIndex; infer_instance
    letI : Fintype Jp := Fintype.ofFinite Jp
    let up : Jp → Plane := fun j =>
      if 0 < incidentPorts f p.val W.chart W.left W.right (j.val,false) 1 then
        incidentPorts f p.val W.chart W.left W.right (j.val,false)
      else incidentPorts f p.val W.chart W.left W.right (j.val,true)
    let down : Jp → Plane := fun j =>
      if 0 < incidentPorts f p.val W.chart W.left W.right (j.val,false) 1 then
        incidentPorts f p.val W.chart W.left W.right (j.val,true)
      else incidentPorts f p.val W.chart W.left W.right (j.val,false)
    have hup : ∀ j, 0 < up j 1 := by
      intro j
      rcases hWsign j.val j.property with h | h
      · simpa only [up,if_pos h.1] using h.1
      · simpa only [up,if_neg (not_lt_of_ge h.1.le)] using h.2
    have hdown : ∀ j, down j 1 < 0 := by
      intro j
      rcases hWsign j.val j.property with h | h
      · simpa only [down,if_pos h.1] using h.2
      · simpa only [down,if_neg (not_lt_of_ge h.1.le)] using h.1
    have hstar (j : Jp) :
        segment ℝ (incidentPorts f p.val W.chart W.left W.right (j.val,false)) 0 ∪
          segment ℝ 0 (incidentPorts f p.val W.chart W.left W.right (j.val,true)) =
        segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j) := by
      dsimp only [up,down]
      split_ifs with h
      · rw [segment_symm ℝ _ 0]
      · rw [segment_symm ℝ _ 0,union_comm]
    have haxis (y : ↥F) (hy : y.val ∈ W.chart.source)
        (hyball : W.chart y.val ∈ Metric.closedBall 0 η) :
        y ∈ range (f (some w)) ↔ W.chart y.val 1 = 0 :=
      hFanAxis p.val W ⟨some w,hsecondWhole p.property.1.1⟩ hW0 hW1 y hy
        (Metric.closedBall_subset_closedBall hη1.le hyball)
    have htransition (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) η) :
        Eguide (W.chart.symm y) 1 = 0 ↔ y 1 = 0 := by
      have hyt := hηtarget (Metric.ball_subset_closedBall hy)
      have hys := W.chart.map_target hyt
      have hyF : W.chart.symm y ∈ F :=
        interior_subset ((W.source_closure (subset_closure hys)).2)
      let z : ↥F := ⟨W.chart.symm y,hyF⟩
      have hzaxis := haxis z hys (by
        change W.chart (W.chart.symm y) ∈ Metric.closedBall 0 η
        rw [W.chart.right_inv hyt]
        exact Metric.ball_subset_closedBall hy)
      have hzg : z.val ∈ Eguide.source :=
        hηguide ⟨y,Metric.ball_subset_closedBall hy,rfl⟩
      have hzcoord : W.chart z.val = y := W.chart.right_inv hyt
      rw [hzcoord] at hzaxis
      constructor
      · intro he
        obtain ⟨t,ht⟩ := (hGuideAxis z.val hzg).mpr he
        exact hzaxis.mp ⟨t,Subtype.ext ht⟩
      · intro he
        obtain ⟨t,ht⟩ := hzaxis.mpr he
        exact (hGuideAxis z.val hzg).mp ⟨t,congrArg Subtype.val ht⟩
    obtain ⟨κ,hκ,hpositive⟩ := hSignedHalfChoice Eguide W.chart p.val.val
      W.contact_in_source W.contact_zero (hsecondZero p.val p.property.1.1) η hη
      (fun y hy => hηtarget (Metric.ball_subset_closedBall hy))
      (fun y hy => by obtain ⟨z,hz,rfl⟩ := hy; exact hηguide ⟨z,Metric.ball_subset_closedBall hz,rfl⟩)
      htransition σ hσ
    obtain ⟨δ,H,hδ,hH,hleft,hright,hpatch⟩ :=
      hSignedRadialPatch up down hup hdown η hη κ hκ
    refine ⟨W,η,δ,H,κ,hκ,hWsmall,hη,hη1,hδ,hH,hηtarget,hηguide,hleft,hright,haxis,hpositive,?_⟩
    intro h hh hhH
    let C := segment ℝ (Plane.mk (-δ) (κ*h)) (Plane.mk δ (κ*h))
    obtain ⟨hCball,hleftClear,hrightClear,hguideClear,hcounts⟩ := hpatch h hh hhH
    have hCclosed : C ⊆ Metric.closedBall 0 η := hCball.trans Metric.ball_subset_closedBall
    have hCunit : C ⊆ Metric.closedBall 0 1 :=
      hCclosed.trans (Metric.closedBall_subset_closedBall hη1.le)
    have hguide (y : ↥F) (hy : y.val ∈ W.chart.source) (hyC : W.chart y.val ∈ C) :
        y ∉ range (f (some w)) := by
      intro hyw
      exact disjoint_left.mp hguideClear hyC ((haxis y hy (hCclosed hyC)).mp hyw)
    refine ⟨hCball,?_,?_,?_⟩
    · intro y hy hyC
      exact ⟨fun hyv => disjoint_left.mp hηselected ⟨hy,hCclosed hyC⟩ hyv,
        hguide y hy hyC⟩
    · intro y hy hyEnd i hyi
      have hyC : W.chart y.val ∈ C := by
        rcases hyEnd with he | he
        · rw [he]
          exact left_mem_segment ℝ _ _
        · rw [he]
          exact right_mem_segment ℝ _ _
      by_cases hpi : p.val ∈ range (f i)
      · by_cases hiw : i = some w
        · subst i
          exact hguide y hy hyC hyi
        · let j : Jp := ⟨⟨i,hpi⟩,hiw⟩
          have hyStar := (hFanTrace p.val W j.val y hy (hCunit hyC)).mp hyi
          rw [hstar j] at hyStar
          rcases hyEnd with he | he
          · rw [he] at hyStar
            exact hleftClear j hyStar
          · rw [he] at hyStar
            exact hrightClear j hyStar
      · exact disjoint_left.mp (W.nonincident_clear i hpi) ⟨hy,hCunit hyC⟩ hyi
    · intro i
      let T : Set ↥F := {y | y.val ∈ W.chart.source ∧ W.chart y.val ∈ C} ∩ range (f i)
      change T.Finite ∧ T.ncard ≤ if p.val ∈ range (f i) then 1 else 0
      by_cases hpi : p.val ∈ range (f i)
      · rw [if_pos hpi]
        by_cases hiw : i = some w
        · have hT : T = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro y hy
            exact hguide y hy.1.1 hy.1.2 (hiw ▸ hy.2)
          rw [hT]
          exact ⟨finite_empty,by simp⟩
        · let j : Jp := ⟨⟨i,hpi⟩,hiw⟩
          let Q := C ∩ (segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j))
          have hQsub : Q.Subsingleton := (ncard_le_one (hcounts j).1).mp (hcounts j).2
          have hTsub : T.Subsingleton := by
            intro y hy z hz
            apply Subtype.ext
            apply W.chart.injOn hy.1.1 hz.1.1
            apply hQsub
            · refine ⟨hy.1.2,?_⟩
              rw [← hstar j]
              exact (hFanTrace p.val W j.val y hy.1.1 (hCunit hy.1.2)).mp hy.2
            · refine ⟨hz.1.2,?_⟩
              rw [← hstar j]
              exact (hFanTrace p.val W j.val z hz.1.1 (hCunit hz.1.2)).mp hz.2
          exact ⟨hTsub.finite,(ncard_le_one hTsub.finite).mpr hTsub⟩
      · rw [if_neg hpi]
        have hT : T = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro y hy
          exact disjoint_left.mp (W.nonincident_clear i hpi) ⟨hy.1.1,hCunit hy.1.2⟩ hy.2
        rw [hT]
        exact ⟨finite_empty,by simp⟩
  have hEventFamily (p : ↥P) (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
      ∃ L R : C(Interval,↥F), ∃ piece : Interval → C(Interval,↥F),
        piece 0 ⟨1/2,by norm_num⟩ = p.val ∧
        (∀ y ∈ range (piece 0), Eguide y.val 1 = 0 ∧
          ∀ i : Option ι, i ≠ some w → y ∈ range (f i) → y = p.val) ∧
        (range (piece 0) ⊆ RegionalChordNormalization.chartPull F
          (fan.window ⟨p.val,hPfan p.property⟩).chart (Metric.ball (0 : Plane) 1)) ∧
        (∀ τ, (L τ).val ∈ Eguide.source ∧ (R τ).val ∈ Eguide.source) ∧
        Eguide (L 0).val 1 = 0 ∧ Eguide (R 0).val 1 = 0 ∧ L 0 ≠ R 0 ∧
        (∀ τ : Interval, 0 < τ.val →
          0 < σ * Eguide (L τ).val 1 ∧ 0 < σ * Eguide (R τ).val 1) ∧
        (∀ τ, IsEmbedding (piece τ) ∧
          range (piece τ) ⊆ {y | y.val ∈ Eguide.source} ∧
          piece τ 0 = L τ ∧ piece τ 1 = R τ) ∧
        ∀ τ : Interval, 0 < τ.val →
          Disjoint (range (piece τ)) (range (f (some v))) ∧
          Disjoint (range (piece τ)) (range (f (some w))) ∧
          (∀ i : Option ι, L τ ∉ range (f i) ∧ R τ ∉ range (f i)) ∧
          (∀ i : Option ι, (range (piece τ) ∩ range (f i)).Finite ∧
            (range (piece τ) ∩ range (f i)).ncard ≤ if p.val ∈ range (f i) then 1 else 0) := by
    obtain ⟨W,η,δ,H,κ,hκ,hWsmall,hη,hη1,hδ,hH,hηtarget,hηguide,hleft,hright,haxis,hpositive,hpatch⟩ := hEventPatch p σ hσ
    let height (τ : Interval) : ℝ := (H/2)*τ.val
    have hheight (τ : Interval) (hτ : 0 < τ.val) : 0 < height τ ∧ height τ < H :=
      ⟨mul_pos (half_pos hH) hτ,by dsimp [height]; nlinarith [τ.property.2]⟩
    let C (τ : Interval) := segment ℝ (Plane.mk (-δ) (κ*height τ)) (Plane.mk δ (κ*height τ))
    have hCball (τ : Interval) : C τ ⊆ Metric.ball (0 : Plane) η := by
      by_cases hτ : τ.val = 0
      · dsimp only [C,height]
        simp only [hτ,mul_zero]
        exact (convex_ball (0 : Plane) η).segment_subset hleft hright
      · exact (hpatch (height τ)
          (hheight τ (lt_of_le_of_ne τ.property.1 (Ne.symm hτ))).1
          (hheight τ (lt_of_le_of_ne τ.property.1 (Ne.symm hτ))).2).1
    let γ (τ s : Interval) : Plane := Plane.mk (-δ+s.val*(2*δ)) (κ*height τ)
    have hγC (τ s : Interval) : γ τ s ∈ C τ := by
      dsimp only [C]
      rw [segment_eq_image']
      refine ⟨s.val,s.property,?_⟩
      ext i
      fin_cases i
      · dsimp [γ,C,Plane.mk]
        ring
      · dsimp [γ,C,Plane.mk]
        ring
    have hγTarget (τ s : Interval) : γ τ s ∈ W.chart.target :=
      hηtarget (Metric.ball_subset_closedBall (hCball τ (hγC τ s)))
    have hγSource (τ s : Interval) : W.chart.symm (γ τ s) ∈ W.chart.source :=
      W.chart.map_target (hγTarget τ s)
    have hγF (τ s : Interval) : W.chart.symm (γ τ s) ∈ F :=
      interior_subset ((W.source_closure (subset_closure (hγSource τ s))).2)
    let piece : Interval → C(Interval,↥F) := fun τ =>
      ⟨fun s => ⟨W.chart.symm (γ τ s),hγF τ s⟩,
        (W.chart.symm.continuousOn.comp_continuous (by fun_prop) (hγTarget τ)).subtype_mk _⟩
    let L : C(Interval,↥F) := ⟨fun τ => piece τ 0,
      (W.chart.symm.continuousOn.comp_continuous
        (by dsimp only [γ,height]; fun_prop) (fun τ => hγTarget τ 0)).subtype_mk _⟩
    let R : C(Interval,↥F) := ⟨fun τ => piece τ 1,
      (W.chart.symm.continuousOn.comp_continuous
        (by dsimp only [γ,height]; fun_prop) (fun τ => hγTarget τ 1)).subtype_mk _⟩
    have hcoord (τ s : Interval) : W.chart (piece τ s).val = γ τ s :=
      W.chart.right_inv (hγTarget τ s)
    have hsource (τ s : Interval) : (piece τ s).val ∈ W.chart.source := hγSource τ s
    have hguide (τ s : Interval) : (piece τ s).val ∈ Eguide.source :=
      hηguide ⟨γ τ s,Metric.ball_subset_closedBall (hCball τ (hγC τ s)),rfl⟩
    have hinj (τ : Interval) : Function.Injective (piece τ) := by
      intro s t hst
      have he := congrArg (fun y : ↥F => W.chart y.val 0) hst
      rw [hcoord,hcoord] at he
      change -δ+s.val*(2*δ) = -δ+t.val*(2*δ) at he
      apply Subtype.ext
      nlinarith
    have hrange (τ : Interval) : range (piece τ) ⊆
        {y : ↥F | y.val ∈ W.chart.source ∧ W.chart y.val ∈ C τ} := by
      rintro y ⟨s,rfl⟩
      exact ⟨hsource τ s,(hcoord τ s).symm ▸ hγC τ s⟩
    have hzeroGuide (s : Interval) : Eguide (piece 0 s).val 1 = 0 := by
      apply (hGuideAxis _ (hguide 0 s)).mp
      have hyw : piece 0 s ∈ range (f (some w)) := by
        apply (haxis (piece 0 s) (hsource 0 s) ?_).mpr
        · rw [hcoord]
          simp [γ,height]
        · rw [hcoord]
          exact Metric.ball_subset_closedBall (hCball 0 (hγC 0 s))
      obtain ⟨t,ht⟩ := hyw
      exact ⟨t,congrArg Subtype.val ht⟩
    have hguideAvoid (τ : Interval) (hτ : 0 < τ.val) (s : Interval) :
        piece τ s ∉ range (f (some w)) :=
      ((hpatch (height τ) (hheight τ hτ).1 (hheight τ hτ).2).2.1
        (piece τ s) (hsource τ s) ((hcoord τ s).symm ▸ hγC τ s)).2
    have hguideNonzero (τ : Interval) (hτ : 0 < τ.val) (s : Interval) :
        Eguide (piece τ s).val 1 ≠ 0 := by
      intro he
      obtain ⟨t,ht⟩ := (hGuideAxis _ (hguide τ s)).mpr he
      exact hguideAvoid τ hτ s ⟨t,Subtype.ext ht⟩
    have hsign (τ s : Interval) (hτ : 0 < τ.val) :
        0 < σ*Eguide (piece τ s).val 1 := by
      apply hpositive (γ τ s) (hCball τ (hγC τ s))
      change 0 < κ*(κ*height τ)
      have hκsq : κ*κ = 1 := by rcases hκ with rfl | rfl <;> norm_num
      rw [← mul_assoc,hκsq,one_mul]
      exact (hheight τ hτ).1
    have hzeroMid : piece 0 ⟨1/2,by norm_num⟩ = p.val := by
      apply Subtype.ext
      change W.chart.symm (γ 0 ⟨1/2,by norm_num⟩) = p.val.val
      have hg : γ 0 ⟨1/2,by norm_num⟩ = (0 : Plane) := by
        ext i
        fin_cases i <;> simp [γ,height,Plane.mk] <;> ring
      rw [hg,← W.contact_zero,W.chart.left_inv W.contact_in_source]
    have hzeroProperties (y : ↥F) (hy : y ∈ range (piece 0)) :
        Eguide y.val 1 = 0 ∧ ∀ i : Option ι, i ≠ some w → y ∈ range (f i) → y = p.val := by
      obtain ⟨s,rfl⟩ := hy
      have hyw : piece 0 s ∈ range (f (some w)) := by
        obtain ⟨t,ht⟩ := (hGuideAxis _ (hguide 0 s)).mpr (hzeroGuide s)
        exact ⟨t,Subtype.ext ht⟩
      have hyunit : W.chart (piece 0 s).val ∈ Metric.closedBall (0 : Plane) 1 := by
        rw [hcoord]
        exact Metric.closedBall_subset_closedBall hη1.le
          (Metric.ball_subset_closedBall (hCball 0 (hγC 0 s)))
      refine ⟨hzeroGuide s,?_⟩
      intro i hi hyi
      by_cases hpi : p.val ∈ range (f i)
      · exact hFanContactUnique p.val W ⟨i,hpi⟩
          ⟨some w,hsecondWhole p.property.1.1⟩ hi (piece 0 s) (hsource 0 s) hyunit hyi hyw
      · exact (disjoint_left.mp (W.nonincident_clear i hpi) ⟨hsource 0 s,hyunit⟩ hyi).elim
    have hzeroSupport : range (piece 0) ⊆
        RegionalChordNormalization.chartPull F (fan.window ⟨p.val,hPfan p.property⟩).chart
          (Metric.ball (0 : Plane) 1) := by
      rintro y ⟨s,rfl⟩
      apply hWsmall
      refine ⟨hsource 0 s,?_⟩
      rw [hcoord]
      exact Metric.closedBall_subset_closedBall hη1.le
        (Metric.ball_subset_closedBall (hCball 0 (hγC 0 s)))
    refine ⟨L,R,piece,hzeroMid,hzeroProperties,hzeroSupport,fun τ => ⟨hguide τ 0,hguide τ 1⟩,
      hzeroGuide 0,hzeroGuide 1,?_,fun τ hτ => ⟨hsign τ 0 hτ,hsign τ 1 hτ⟩,?_,?_⟩
    · intro he
      have h01 := hinj 0 he
      exact zero_ne_one h01
    · intro τ
      exact ⟨((piece τ).continuous.isClosedEmbedding (hinj τ)).isEmbedding,
        fun y hy => by obtain ⟨s,rfl⟩ := hy; exact hguide τ s,rfl,rfl⟩
    · intro τ hτ
      obtain ⟨hC,hvw,hports,hcounts⟩ := hpatch (height τ) (hheight τ hτ).1 (hheight τ hτ).2
      refine ⟨disjoint_left.mpr (fun y hy hyv =>
          (hvw y (hrange τ hy).1 (hrange τ hy).2).1 hyv),
        disjoint_left.mpr (fun y hy hyw =>
          (hvw y (hrange τ hy).1 (hrange τ hy).2).2 hyw),?_,?_⟩
      · intro i
        constructor
        · exact hports (L τ) (hsource τ 0) (Or.inl (by
            change W.chart (piece τ 0).val = _
            rw [hcoord]
            simp [γ])) i
        · exact hports (R τ) (hsource τ 1) (Or.inr (by
            change W.chart (piece τ 1).val = _
            rw [hcoord]
            ext i
            fin_cases i
            · dsimp [γ,Plane.mk]
              ring
            · rfl)) i
      · intro i
        have hsubset := inter_subset_inter_left (range (f i)) (hrange τ)
        exact ⟨(hcounts i).1.subset hsubset,
          (ncard_le_ncard hsubset (hcounts i).1).trans (hcounts i).2⟩
  have hAxisArcOrder (p : ↥F) (arc : C(Interval,↥F))
      (hEmb : IsEmbedding arc) (hSource : ∀ t, (arc t).val ∈ Eguide.source)
      (hZero : ∀ t, Eguide (arc t).val 1 = 0)
      (hMid : arc ⟨1/2,by norm_num⟩ = p) :
      ∃ a b : ℝ, a < Eguide p.val 0 ∧ Eguide p.val 0 < b ∧
        range (fun t => Eguide (arc t).val 0) = Icc a b ∧
        ((a = Eguide (arc 0).val 0 ∧ b = Eguide (arc 1).val 0) ∨
          (a = Eguide (arc 1).val 0 ∧ b = Eguide (arc 0).val 0)) := by
    let φ : Interval → ℝ := fun t => Eguide (arc t).val 0
    have hφ : Continuous φ := (show Continuous (fun z : Plane => z 0) from by fun_prop).comp
      (Eguide.continuousOn.comp_continuous (continuous_subtype_val.comp arc.continuous) hSource)
    have hφinj : Function.Injective φ := by
      intro s t he
      apply hEmb.injective
      apply Subtype.ext
      apply Eguide.injOn (hSource s) (hSource t)
      ext i
      fin_cases i
      · exact he
      · exact (hZero s).trans (hZero t).symm
    have hmid : φ ⟨1/2,by norm_num⟩ = Eguide p.val 0 := congrArg (fun y : ↥F => Eguide y.val 0) hMid
    have h01 : (0 : Interval) < ⟨1/2,by norm_num⟩ := by change (0 : ℝ) < 1/2; norm_num
    have h11 : (⟨1/2,by norm_num⟩ : Interval) < 1 := by change (1/2 : ℝ) < 1; norm_num
    rcases hφ.strictMono_of_inj_boundedOrder' hφinj with hm | hm
    · refine ⟨φ 0,φ 1,hmid ▸ hm h01,hmid ▸ hm h11,?_,Or.inl ⟨rfl,rfl⟩⟩
      ext ξ
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨hm.monotone (show (0 : Interval) ≤ t from t.property.1),
          hm.monotone (show t ≤ (1 : Interval) from t.property.2)⟩
      · intro hξ
        obtain ⟨t,ht,he⟩ := isPreconnected_univ.intermediate_value (mem_univ (0 : Interval))
          (mem_univ (1 : Interval)) hφ.continuousOn hξ
        exact ⟨t,he⟩
    · refine ⟨φ 1,φ 0,hmid ▸ hm h11,hmid ▸ hm h01,?_,Or.inr ⟨rfl,rfl⟩⟩
      ext ξ
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨hm.antitone (show t ≤ (1 : Interval) from t.property.2),
          hm.antitone (show (0 : Interval) ≤ t from t.property.1)⟩
      · intro hξ
        obtain ⟨t,ht,he⟩ := isPreconnected_univ.intermediate_value (mem_univ (1 : Interval))
          (mem_univ (0 : Interval)) hφ.continuousOn hξ
        exact ⟨t,he⟩
  have hOrderedEvent (p : ↥P) (σ : ℝ) (hσ : σ = -1 ∨ σ = 1) :
      ∃ a b : ℝ, ∃ L R : C(Interval,↥F), ∃ piece : Interval → C(Interval,↥F),
        ∃ axisArc : C(Interval,↥F),
        a < Eguide p.val.val 0 ∧ Eguide p.val.val 0 < b ∧
        range (fun t => Eguide (axisArc t).val 0) = Icc a b ∧
        (∀ y ∈ range axisArc, y.val ∈ Eguide.source ∧ Eguide y.val 1 = 0 ∧
          ∀ i : Option ι, i ≠ some w → y ∈ range (f i) → y = p.val) ∧
        (range axisArc ⊆ RegionalChordNormalization.chartPull F
          (fan.window ⟨p.val,hPfan p.property⟩).chart (Metric.ball (0 : Plane) 1)) ∧
        Eguide (L 0).val 0 = a ∧ Eguide (R 0).val 0 = b ∧
        Eguide (L 0).val 1 = 0 ∧ Eguide (R 0).val 1 = 0 ∧
        (∀ τ, (L τ).val ∈ Eguide.source ∧ (R τ).val ∈ Eguide.source) ∧
        (∀ τ : Interval, 0 < τ.val →
          0 < σ*Eguide (L τ).val 1 ∧ 0 < σ*Eguide (R τ).val 1) ∧
        (∀ τ, IsEmbedding (piece τ) ∧
          range (piece τ) ⊆ {y | y.val ∈ Eguide.source} ∧
          piece τ 0 = L τ ∧ piece τ 1 = R τ) ∧
        ∀ τ : Interval, 0 < τ.val →
          Disjoint (range (piece τ)) (range (f (some v))) ∧
          Disjoint (range (piece τ)) (range (f (some w))) ∧
          (∀ i : Option ι, L τ ∉ range (f i) ∧ R τ ∉ range (f i)) ∧
          (∀ i : Option ι, (range (piece τ) ∩ range (f i)).Finite ∧
            (range (piece τ) ∩ range (f i)).ncard ≤ if p.val ∈ range (f i) then 1 else 0) := by
    obtain ⟨L,R,piece,hMid,hZero,hSupport,hSource,hLzero,hRzero,hNe,hSign,hPiece,hPositive⟩ :=
      hEventFamily p σ hσ
    obtain ⟨a,b,ha,hb,hImage,hOrder⟩ := hAxisArcOrder p.val (piece 0) (hPiece 0).1
      (fun t => (hPiece 0).2.1 ⟨t,rfl⟩) (fun t => (hZero _ ⟨t,rfl⟩).1) hMid
    have hData : ∀ y ∈ range (piece 0), y.val ∈ Eguide.source ∧ Eguide y.val 1 = 0 ∧
        ∀ i : Option ι, i ≠ some w → y ∈ range (f i) → y = p.val :=
      fun y hy => ⟨(hPiece 0).2.1 hy,hZero y hy⟩
    have hleft : Eguide (piece 0 0).val 0 = Eguide (L 0).val 0 :=
      congrArg (fun y : ↥F => Eguide y.val 0) (hPiece 0).2.2.1
    have hright : Eguide (piece 0 1).val 0 = Eguide (R 0).val 0 :=
      congrArg (fun y : ↥F => Eguide y.val 0) (hPiece 0).2.2.2
    rcases hOrder with h | h
    · exact ⟨a,b,L,R,piece,piece 0,ha,hb,hImage,hData,hSupport,
        hleft.symm.trans h.1.symm,hright.symm.trans h.2.symm,hLzero,hRzero,hSource,hSign,hPiece,hPositive⟩
    · let rev : Interval → C(Interval,↥F) := fun τ =>
        (piece τ).comp ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
      have hRange (τ : Interval) : range (rev τ) = range (piece τ) :=
        unitInterval.symmHomeomorph.surjective.range_comp (piece τ)
      have hEnds (τ : Interval) : rev τ 0 = R τ ∧ rev τ 1 = L τ := by
        constructor
        · change piece τ (unitInterval.symmHomeomorph 0) = R τ
          simpa only [unitInterval.symmHomeomorph_apply,unitInterval.symm_zero] using (hPiece τ).2.2.2
        · change piece τ (unitInterval.symmHomeomorph 1) = L τ
          simpa only [unitInterval.symmHomeomorph_apply,unitInterval.symm_one] using (hPiece τ).2.2.1
      refine ⟨a,b,R,L,rev,piece 0,ha,hb,hImage,hData,hSupport,
        hright.symm.trans h.1.symm,hleft.symm.trans h.2.symm,hRzero,hLzero,
        fun τ => (hSource τ).symm,fun τ hτ => (hSign τ hτ).symm,?_,?_⟩
      · intro τ
        refine ⟨(hPiece τ).1.comp unitInterval.symmHomeomorph.isEmbedding,?_,hEnds τ⟩
        rw [hRange]
        exact (hPiece τ).2.1
      · intro τ hτ
        obtain ⟨hv,hw,hports,hcounts⟩ := hPositive τ hτ
        rw [hRange]
        exact ⟨hv,hw,fun i => (hports i).symm,hcounts⟩
  have hReflectedFan (p : ↥F) (W : IncidentFanWindow F f V p) :
      ∃ W' : IncidentFanWindow F f V p,
        W'.chart = W.chart.transHomeomorph (ContinuousLinearEquiv.neg ℝ : Plane ≃L[ℝ] Plane).toHomeomorph ∧
        W'.left = W.left ∧ W'.right = W.right := by
    let N : Plane ≃L[ℝ] Plane := ContinuousLinearEquiv.neg ℝ
    let Q := W.chart.transHomeomorph N.toHomeomorph
    have hPullClosed : RegionalChordNormalization.chartPull F Q (Metric.closedBall (0 : Plane) 1) =
        RegionalChordNormalization.chartPull F W.chart (Metric.closedBall (0 : Plane) 1) := by
      ext y
      change (y.val ∈ W.chart.source ∧ -W.chart y.val ∈ Metric.closedBall 0 1) ↔
        (y.val ∈ W.chart.source ∧ W.chart y.val ∈ Metric.closedBall 0 1)
      simp only [Metric.mem_closedBall,dist_zero_right,norm_neg]
    have hPullOpen : RegionalChordNormalization.chartPull F Q (Metric.ball (0 : Plane) 1) =
        RegionalChordNormalization.chartPull F W.chart (Metric.ball (0 : Plane) 1) := by
      ext y
      change (y.val ∈ W.chart.source ∧ -W.chart y.val ∈ Metric.ball 0 1) ↔
        (y.val ∈ W.chart.source ∧ W.chart y.val ∈ Metric.ball 0 1)
      simp only [Metric.mem_ball,dist_zero_right,norm_neg]
    have hImage (a b : Plane) : (fun z : Plane => -z) '' segment ℝ a b =
        segment ℝ (-a) (-b) :=
      image_segment ℝ N.toLinearMap.toAffineMap a b
    let W' : IncidentFanWindow F f V p := {
      chart := Q
      source_closure := W.source_closure
      contact_in_source := W.contact_in_source
      contact_zero := by change -W.chart p.val = 0; rw [W.contact_zero,neg_zero]
      disk_in_target := by
        intro z hz
        change -z ∈ W.chart.target
        apply W.disk_in_target
        simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hz
      left := W.left
      right := W.right
      center := W.center
      cuts := W.cuts
      at_center := W.at_center
      whole_closed := by intro i; rw [hPullClosed]; exact W.whole_closed i
      whole_open := by intro i; rw [hPullOpen]; exact W.whole_open i
      radial_trace := by
        intro i
        have he := congrArg (fun T : Set Plane => (fun z : Plane => -z) '' T) (W.radial_trace i)
        rw [image_union,hImage,hImage,neg_zero,image_image] at he
        exact he
      nonincident_clear := by intro i hi; rw [hPullClosed]; exact W.nonincident_clear i hi
      ports_on_sphere := by
        intro z
        change -incidentPorts f p W.chart W.left W.right z ∈ Metric.sphere (0 : Plane) 1
        simpa only [Metric.mem_sphere,dist_zero_right,norm_neg] using W.ports_on_sphere z
      ports_injective := by
        intro z y he
        apply W.ports_injective
        exact neg_injective he }
    exact ⟨W',rfl,rfl,rfl⟩
  have hCornerPatch (p : ↥F) (W : IncidentFanWindow F f V p)
      (hpv : p ∈ range (f (some v))) (hpw : p ∈ range (f (some w)))
      (hW0 : incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,false) 1 = 0)
      (hW1 : incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,true) 1 = 0)
      (hWsign : ∀ j : incidentIndex f p, j.val ≠ some v →
        ((0 < incidentPorts f p W.chart W.left W.right (j,false) 1 ∧
          incidentPorts f p W.chart W.left W.right (j,true) 1 < 0) ∨
        (incidentPorts f p W.chart W.left W.right (j,false) 1 < 0 ∧
          0 < incidentPorts f p W.chart W.left W.right (j,true) 1)))
      (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 < δ)
      (hηtarget : Metric.closedBall (0 : Plane) η ⊆ W.chart.target)
      (hηguide : W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ Eguide.source)
      (x0 y : ↥F) (hx0 : x0.val ∈ W.chart.source)
      (hstart : W.chart x0.val = Plane.mk (-δ) 0)
      (hstartBall : Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η)
      (hy : y.val ∈ W.chart.source) (hyball : W.chart y.val ∈ Metric.ball (0 : Plane) η)
      (hyw : y ∈ range (f (some w))) (hyy : W.chart y.val 1 ≠ 0) :
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ arc : C(Interval,↥F), IsEmbedding arc ∧
          range arc ⊆ {z | z.val ∈ Eguide.source} ∧ arc 0 = x0 ∧
          (arc 1).val = W.chart.symm (Plane.mk (W.chart y.val 0-ε) (W.chart y.val 1)) ∧
          range arc ∩ range (f (some v)) = {x0} ∧
          Disjoint (range arc) (range (f (some w))) ∧
          (∀ i : Option ι, arc 1 ∉ range (f i)) ∧
          ∀ i : Option ι, i ≠ some v →
            (range arc ∩ range (f i)).Finite ∧
            (range arc ∩ range (f i)).ncard ≤ if p ∈ range (f i) then 1 else 0 := by
    have hyunit := Metric.closedBall_subset_closedBall hη1.le (Metric.ball_subset_closedBall hyball)
    let iw : incidentIndex f p := ⟨some w,hpw⟩
    have hivw : (some w : Option ι) ≠ some v := fun he => hvw (Option.some.inj he).symm
    have hPair : incidentPorts f p W.chart W.left W.right (iw,false) 1 *
        incidentPorts f p W.chart W.left W.right (iw,true) 1 < 0 := by
      rcases hWsign iw hivw with h | h
      · exact mul_neg_of_pos_of_neg h.1 h.2
      · exact mul_neg_of_neg_of_pos h.1 h.2
    have hGermRay : ∃ β : Bool, W.chart y.val ∈ segment ℝ (0 : Plane)
        (incidentPorts f p W.chart W.left W.right (iw,β)) := by
      rcases (hFanTrace p W iw y hy hyunit).mp hyw with hh | hh
      · refine ⟨false,?_⟩
        rwa [segment_symm ℝ _ (0 : Plane)] at hh
      · exact ⟨true,hh⟩
    obtain ⟨β,hβ⟩ := hGermRay
    let bad : Set S := ⋃ i : {i : Option ι // i ≠ some w},
      range (fun t => (f i.val t).val)
    have hbad : IsClosed bad := (isCompact_iUnion (fun i : {i : Option ι // i ≠ some w} =>
      isCompact_range (continuous_subtype_val.comp (f i.val).continuous))).isClosed
    have hyclear : y.val ∉ bad := by
      intro hh
      obtain ⟨i,t,ht⟩ := mem_iUnion.mp hh
      have hyi : y ∈ range (f i.val) := ⟨t,Subtype.ext ht⟩
      by_cases hpi : p ∈ range (f i.val)
      · have he := hFanContactUnique p W ⟨i.val,hpi⟩ iw i.property y hy hyunit hyi hyw
        apply hyy
        rw [he,W.contact_zero]
        rfl
      · exact disjoint_left.mp (W.nonincident_clear i.val hpi) ⟨hy,hyunit⟩ hyi
    let O := W.chart '' (W.chart.source ∩ badᶜ)
    have hO : IsOpen O := W.chart.isOpen_image_source_inter hbad.isOpen_compl
    have hyO : W.chart y.val ∈ O := ⟨y.val,⟨hy,hyclear⟩,rfl⟩
    have hsign : incidentPorts f p W.chart W.left W.right (iw,β) 1 *
        incidentPorts f p W.chart W.left W.right (iw,!β) 1 < 0 := by
      cases β with
      | false => exact hPair
      | true =>
        change incidentPorts f p W.chart W.left W.right (iw,true) 1 *
          incidentPorts f p W.chart W.left W.right (iw,false) 1 < 0
        rw [mul_comm]
        exact hPair
    obtain ⟨ε₀,hε₀,hpatch⟩ := actual_near_entering_ray_corner_family δ η hδ
      (W.chart y.val) (incidentPorts f p W.chart W.left W.right (iw,β))
      (incidentPorts f p W.chart W.left W.right (iw,!β)) hβ hyy hsign O hO hyO hstartBall hyball
    let Ji := {j : incidentIndex f p // j.val ≠ some v}
    let up : Ji → Plane := fun j =>
      if 0 < incidentPorts f p W.chart W.left W.right (j.val,false) 1 then
        incidentPorts f p W.chart W.left W.right (j.val,false)
      else incidentPorts f p W.chart W.left W.right (j.val,true)
    let down : Ji → Plane := fun j =>
      if 0 < incidentPorts f p W.chart W.left W.right (j.val,false) 1 then
        incidentPorts f p W.chart W.left W.right (j.val,true)
      else incidentPorts f p W.chart W.left W.right (j.val,false)
    have hup : ∀ j, 0 < up j 1 := by
      intro j
      rcases hWsign j.val j.property with h | h
      · simpa only [up,if_pos h.1] using h.1
      · simpa only [up,if_neg (not_lt_of_ge h.1.le)] using h.2
    have hdown : ∀ j, down j 1 < 0 := by
      intro j
      rcases hWsign j.val j.property with h | h
      · simpa only [down,if_pos h.1] using h.2
      · simpa only [down,if_neg (not_lt_of_ge h.1.le)] using h.1
    have hstar (j : Ji) :
        segment ℝ (incidentPorts f p W.chart W.left W.right (j.val,false)) 0 ∪
          segment ℝ 0 (incidentPorts f p W.chart W.left W.right (j.val,true)) =
        segment ℝ (0 : Plane) (up j) ∪ segment ℝ 0 (down j) := by
      dsimp only [up,down]
      split_ifs with h
      · rw [segment_symm ℝ _ 0]
      · rw [segment_symm ℝ _ 0,union_comm]
    refine ⟨ε₀,hε₀,?_⟩
    intro ε hε hεsmall
    obtain ⟨hend,hball,havoid⟩ := hpatch ε hε hεsmall
    let C := segment ℝ (Plane.mk (-δ) 0) (Plane.mk (W.chart y.val 0-ε) (W.chart y.val 1))
    have hCtarget : C ⊆ W.chart.target := fun z hz => hηtarget (Metric.ball_subset_closedBall (hball hz))
    have hCunit : C ⊆ Metric.closedBall (0 : Plane) 1 :=
      hball.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hη1.le))
    obtain ⟨a,ha,harange,ha0,ha1,hacoord⟩ := actual_signed_chart_connector_arc W.chart δ
      (W.chart y.val 0-ε) (W.chart y.val 1) hyy hCtarget
    have haF (t : Interval) : a t ∈ F :=
      interior_subset ((W.source_closure (subset_closure (hacoord t).1)).2)
    let arc : C(Interval,↥F) := ⟨fun t => ⟨a t,haF t⟩,a.continuous.subtype_mk _⟩
    have harc : IsEmbedding arc := (arc.continuous.isClosedEmbedding (by
      intro s t hst
      exact ha.injective (congrArg Subtype.val hst))).isEmbedding
    have hrange (z : ↥F) (hz : z ∈ range arc) :
        z.val ∈ W.chart.source ∧ W.chart z.val ∈ C := by
      obtain ⟨t,rfl⟩ := hz
      obtain ⟨q,hq,hqa⟩ := harange ▸ (mem_range_self t)
      refine ⟨(hacoord t).1,?_⟩
      change W.chart (a t) ∈ C
      rw [← hqa,W.chart.right_inv (hCtarget hq)]
      exact hq
    have hstartEq : arc 0 = x0 := by
      apply Subtype.ext
      change a 0 = x0.val
      rw [ha0,← hstart,W.chart.left_inv hx0]
    have hxselected : x0 ∈ range (f (some v)) := by
      apply (hFanAxis p W ⟨some v,hpv⟩ hW0 hW1 x0 hx0 ?_).mpr
      · rw [hstart]
        rfl
      · rw [hstart]
        exact Metric.closedBall_subset_closedBall hη1.le (Metric.ball_subset_closedBall hstartBall)
    have hmeet : range arc ∩ range (f (some v)) = {x0} := by
      ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,ht⟩
        have hz := (hFanAxis p W ⟨some v,hpv⟩ hW0 hW1 (arc t)
          (hrange _ ⟨t,rfl⟩).1 (hCunit (hrange _ ⟨t,rfl⟩).2)).mp ht
        change W.chart (a t) 1 = 0 at hz
        rw [(hacoord t).2] at hz
        change W.chart y.val 1 * t.val = 0 at hz
        have ht0 : t = 0 := Subtype.ext ((mul_eq_zero.mp hz).resolve_left hyy)
        rw [ht0,hstartEq]
        exact mem_singleton _
      · rintro rfl
        exact ⟨⟨0,hstartEq⟩,hxselected⟩
    have hguideClear : Disjoint (range arc) (range (f (some w))) := by
      apply disjoint_left.mpr
      intro z hz hzw
      have hm := (hFanTrace p W iw z (hrange z hz).1 (hCunit (hrange z hz).2)).mp hzw
      have hav : Disjoint C
          (segment ℝ (incidentPorts f p W.chart W.left W.right (iw,false)) 0 ∪
            segment ℝ 0 (incidentPorts f p W.chart W.left W.right (iw,true))) := by
        cases β with
        | false =>
          rw [segment_symm ℝ _ (0 : Plane)]
          exact havoid
        | true =>
          rw [segment_symm ℝ _ (0 : Plane),union_comm]
          exact havoid
      exact disjoint_left.mp hav (hrange z hz).2 hm
    have hendclear : ∀ i : Option ι, arc 1 ∉ range (f i) := by
      intro i hi
      by_cases hiw : i = some w
      · exact disjoint_left.mp hguideClear ⟨1,rfl⟩ (hiw ▸ hi)
      · obtain ⟨z,⟨hz,hzclear⟩,hze⟩ := hend
        have heq : (arc 1).val = z := by
          change a 1 = z
          rw [ha1,← hze,W.chart.left_inv hz]
        apply hzclear
        apply mem_iUnion.mpr
        obtain ⟨t,ht⟩ := hi
        exact ⟨⟨i,hiw⟩,t,(congrArg Subtype.val ht).trans heq⟩
    refine ⟨arc,harc,?_,hstartEq,?_,hmeet,hguideClear,hendclear,?_⟩
    · intro z hz
      obtain ⟨t,rfl⟩ := hz
      obtain ⟨q,hq,heq⟩ := harange ▸ (mem_range_self t)
      exact hηguide ⟨q,Metric.ball_subset_closedBall (hball hq),heq⟩
    · exact ha1
    · intro i hiv
      by_cases hpi : p ∈ range (f i)
      · rw [if_pos hpi]
        let j : Ji := ⟨⟨i,hpi⟩,hiv⟩
        have hc := actual_signed_corner_segment_counts up down hup hdown δ
          (W.chart y.val 0-ε) (W.chart y.val 1) hδ hyy j
        have hSub : (range arc ∩ range (f i)).Subsingleton := by
          intro z hz y' hy'
          apply Subtype.ext
          apply W.chart.injOn (hrange _ hz.1).1 (hrange _ hy'.1).1
          have hSingle := (ncard_le_one hc.1).mp hc.2
          apply hSingle
          · refine ⟨(hrange _ hz.1).2,?_⟩
            rw [← hstar j]
            exact (hFanTrace p W j.val z (hrange _ hz.1).1 (hCunit (hrange _ hz.1).2)).mp hz.2
          · refine ⟨(hrange _ hy'.1).2,?_⟩
            rw [← hstar j]
            exact (hFanTrace p W j.val y' (hrange _ hy'.1).1 (hCunit (hrange _ hy'.1).2)).mp hy'.2
        exact ⟨hSub.finite,(ncard_le_one hSub.finite).mpr hSub⟩
      · rw [if_neg hpi]
        have hd : Disjoint (range arc) (range (f i)) := by
          apply (W.nonincident_clear i hpi).mono_left
          intro z hz
          exact ⟨(hrange z hz).1,hCunit (hrange z hz).2⟩
        rw [disjoint_iff_inter_eq_empty.mp hd]
        exact ⟨finite_empty,by simp⟩
  have hCornerFamilyNegative (p : ↥F) (W : IncidentFanWindow F f V p)
      (hpv : p ∈ range (f (some v))) (hpw : p ∈ range (f (some w)))
      (hW0 : incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,false) 1 = 0)
      (hW1 : incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,true) 1 = 0)
      (hWsign : ∀ j : incidentIndex f p, j.val ≠ some v →
        ((0 < incidentPorts f p W.chart W.left W.right (j,false) 1 ∧
          incidentPorts f p W.chart W.left W.right (j,true) 1 < 0) ∨
        (incidentPorts f p W.chart W.left W.right (j,false) 1 < 0 ∧
          0 < incidentPorts f p W.chart W.left W.right (j,true) 1)))
      (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 < δ)
      (hηtarget : Metric.closedBall (0 : Plane) η ⊆ W.chart.target)
      (hηguide : W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ Eguide.source)
      (x0 y : ↥F) (hx0 : x0.val ∈ W.chart.source)
      (hstart : W.chart x0.val = Plane.mk (-δ) 0)
      (hstartBall : Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η)
      (hy : y.val ∈ W.chart.source) (hyball : W.chart y.val ∈ Metric.ball (0 : Plane) η)
      (hyw : y ∈ range (f (some w))) (hyy : W.chart y.val 1 ≠ 0) :
      ∃ endpoint : C(Interval,↥F), endpoint 0 = y ∧
        (∀ τ, (endpoint τ).val ∈ Eguide.source) ∧
        ∀ τ : Interval, 0 < τ.val →
          ∃ arc : C(Interval,↥F), IsEmbedding arc ∧
            range arc ⊆ {z | z.val ∈ Eguide.source} ∧
            arc 0 = x0 ∧ arc 1 = endpoint τ ∧
            range arc ∩ range (f (some v)) = {x0} ∧
            Disjoint (range arc) (range (f (some w))) ∧
            (∀ i : Option ι, endpoint τ ∉ range (f i)) ∧
            ∀ i : Option ι, i ≠ some v →
              (range arc ∩ range (f i)).Finite ∧
              (range arc ∩ range (f i)).ncard ≤ if p ∈ range (f i) then 1 else 0 := by
    obtain ⟨ε₀,hε₀,hpatch⟩ := hCornerPatch p W hpv hpw hW0 hW1 hWsign η δ hη hη1 hδ
      hηtarget hηguide x0 y hx0 hstart hstartBall hy hyball hyw hyy
    have hyGuide : y.val ∈ Eguide.source :=
      hηguide ⟨W.chart y.val,Metric.ball_subset_closedBall hyball,W.chart.left_inv hy⟩
    obtain ⟨ρ,hρ,hρε,e,he0,he⟩ := actual_corner_endpoint_common_chart_family
      W.chart Eguide y.val hy hyGuide ε₀ hε₀
    let endpoint : C(Interval,↥F) :=
      ⟨fun τ => ⟨e τ,interior_subset (hGuideInterior (he τ).2.1)⟩,e.continuous.subtype_mk _⟩
    refine ⟨endpoint,Subtype.ext he0,fun τ => (he τ).2.1,?_⟩
    intro τ hτ
    have hε : 0 < ρ*τ.val := mul_pos hρ hτ
    have hεsmall : ρ*τ.val < ε₀ :=
      (mul_le_of_le_one_right hρ.le τ.property.2).trans_lt hρε
    obtain ⟨arc,hEmb,hguide,hstartArc,hendArc,hmeet,hclear,hports,hcounts⟩ := hpatch _ hε hεsmall
    have hend : arc 1 = endpoint τ := Subtype.ext (hendArc.trans (he τ).2.2.symm)
    refine ⟨arc,hEmb,hguide,hstartArc,hend,hmeet,hclear,?_,hcounts⟩
    intro i hi
    exact hports i (hend.symm ▸ hi)
  have hCornerFamilyOriented (p : ↥F) (W : IncidentFanWindow F f V p)
      (hpv : p ∈ range (f (some v))) (hpw : p ∈ range (f (some w)))
      (hW0 : incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,false) 1 = 0)
      (hW1 : incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,true) 1 = 0)
      (hWsign : ∀ j : incidentIndex f p, j.val ≠ some v →
        ((0 < incidentPorts f p W.chart W.left W.right (j,false) 1 ∧
          incidentPorts f p W.chart W.left W.right (j,true) 1 < 0) ∨
        (incidentPorts f p W.chart W.left W.right (j,false) 1 < 0 ∧
          0 < incidentPorts f p W.chart W.left W.right (j,true) 1)))
      (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
      (hηtarget : Metric.closedBall (0 : Plane) η ⊆ W.chart.target)
      (hηguide : W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ Eguide.source)
      (x0 y : ↥F) (hx0 : x0.val ∈ W.chart.source)
      (hxBall : W.chart x0.val ∈ Metric.ball (0 : Plane) η)
      (hxAxis : W.chart x0.val 1 = 0) (hxNe : W.chart x0.val 0 ≠ 0)
      (hy : y.val ∈ W.chart.source) (hyball : W.chart y.val ∈ Metric.ball (0 : Plane) η)
      (hyw : y ∈ range (f (some w))) (hyy : W.chart y.val 1 ≠ 0) :
      ∃ endpoint : C(Interval,↥F), endpoint 0 = y ∧
        (∀ τ, (endpoint τ).val ∈ Eguide.source) ∧
        ∀ τ : Interval, 0 < τ.val →
          ∃ arc : C(Interval,↥F), IsEmbedding arc ∧
            range arc ⊆ {z | z.val ∈ Eguide.source} ∧
            arc 0 = x0 ∧ arc 1 = endpoint τ ∧
            range arc ∩ range (f (some v)) = {x0} ∧
            Disjoint (range arc) (range (f (some w))) ∧
            (∀ i : Option ι, endpoint τ ∉ range (f i)) ∧
            ∀ i : Option ι, i ≠ some v →
              (range arc ∩ range (f i)).Finite ∧
              (range arc ∩ range (f i)).ncard ≤ if p ∈ range (f i) then 1 else 0 := by
    rcases lt_or_gt_of_ne hxNe with hxNeg | hxPos
    · have hstart : W.chart x0.val = Plane.mk (- -W.chart x0.val 0) 0 := by
        ext i
        fin_cases i
        · simp only [neg_neg]
          rfl
        · exact hxAxis
      exact hCornerFamilyNegative p W hpv hpw hW0 hW1 hWsign η (-W.chart x0.val 0)
        hη hη1 (neg_pos.mpr hxNeg) hηtarget hηguide x0 y hx0 hstart
        (hstart ▸ hxBall) hy hyball hyw hyy
    · obtain ⟨W',hQ,hleft,hright⟩ := hReflectedFan p W
      have hSource : W'.chart.source = W.chart.source := by rw [hQ]; rfl
      have hFormula (z : S) : W'.chart z = -W.chart z := by rw [hQ]; rfl
      have hInvFormula (z : Plane) : W'.chart.symm z = W.chart.symm (-z) := by rw [hQ]; rfl
      have hPorts (z : incidentIndex f p × Bool) :
          incidentPorts f p W'.chart W'.left W'.right z =
            -incidentPorts f p W.chart W.left W.right z := by
        rw [hQ,hleft,hright]
        rfl
      have hW0' : incidentPorts f p W'.chart W'.left W'.right (⟨some v,hpv⟩,false) 1 = 0 := by
        rw [hPorts]
        change -incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,false) 1 = 0
        rw [hW0,neg_zero]
      have hW1' : incidentPorts f p W'.chart W'.left W'.right (⟨some v,hpv⟩,true) 1 = 0 := by
        rw [hPorts]
        change -incidentPorts f p W.chart W.left W.right (⟨some v,hpv⟩,true) 1 = 0
        rw [hW1,neg_zero]
      have hsign' : ∀ j : incidentIndex f p, j.val ≠ some v →
          ((0 < incidentPorts f p W'.chart W'.left W'.right (j,false) 1 ∧
            incidentPorts f p W'.chart W'.left W'.right (j,true) 1 < 0) ∨
          (incidentPorts f p W'.chart W'.left W'.right (j,false) 1 < 0 ∧
            0 < incidentPorts f p W'.chart W'.left W'.right (j,true) 1)) := by
        intro j hj
        rw [hPorts,hPorts]
        rcases hWsign j hj with h | h
        · exact Or.inr ⟨neg_neg_of_pos h.1,neg_pos.mpr h.2⟩
        · exact Or.inl ⟨neg_pos.mpr h.1,neg_neg_of_pos h.2⟩
      have htarget' : Metric.closedBall (0 : Plane) η ⊆ W'.chart.target := by
        intro z hz
        rw [hQ]
        change -z ∈ W.chart.target
        exact hηtarget (by simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hz)
      have hguide' : W'.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ Eguide.source := by
        rintro z ⟨q,hq,rfl⟩
        rw [hInvFormula]
        exact hηguide ⟨-q,by simpa only [Metric.mem_closedBall,dist_zero_right,norm_neg] using hq,rfl⟩
      have hstart : W'.chart x0.val = Plane.mk (-W.chart x0.val 0) 0 := by
        rw [hFormula]
        ext i
        fin_cases i
        · rfl
        · change -W.chart x0.val 1 = 0
          rw [hxAxis,neg_zero]
      have hstartBall : Plane.mk (-W.chart x0.val 0) 0 ∈ Metric.ball (0 : Plane) η := by
        rw [← hstart,hFormula]
        simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hxBall
      have hyball' : W'.chart y.val ∈ Metric.ball (0 : Plane) η := by
        rw [hFormula]
        simpa only [Metric.mem_ball,dist_zero_right,norm_neg] using hyball
      have hyy' : W'.chart y.val 1 ≠ 0 := by
        rw [hFormula]
        exact neg_ne_zero.mpr hyy
      exact hCornerFamilyNegative p W' hpv hpw hW0' hW1' hsign' η (W.chart x0.val 0)
        hη hη1 hxPos htarget' hguide' x0 y (hSource.symm ▸ hx0) hstart hstartBall
        (hSource.symm ▸ hy) hyball' hyw hyy'
  have hCornerInputs (ca cb : Interval)
      (hca : ca = u ∨ ca = z) (hcb : cb = gu ∨ cb = gz)
      (heq : f (some v) ca = f (some w) cb)
      (U : Set S) (hU : IsOpen U) (hpU : (f (some v) ca).val ∈ U) :
      let p := f (some v) ca
      ∃ W : IncidentFanWindow F f V p, ∃ η : ℝ, ∃ ta tb : Interval,
        0 < η ∧ η < 1 ∧
        Metric.closedBall (0 : Plane) η ⊆ W.chart.target ∧
        W.chart.symm '' Metric.closedBall (0 : Plane) η ⊆ Eguide.source ∧
        (incidentPorts f p W.chart W.left W.right (⟨some v,⟨ca,rfl⟩⟩,false) 1 = 0) ∧
        (incidentPorts f p W.chart W.left W.right (⟨some v,⟨ca,rfl⟩⟩,true) 1 = 0) ∧
        (∀ j : incidentIndex f p, j.val ≠ some v →
          ((0 < incidentPorts f p W.chart W.left W.right (j,false) 1 ∧
            incidentPorts f p W.chart W.left W.right (j,true) 1 < 0) ∨
          (incidentPorts f p W.chart W.left W.right (j,false) 1 < 0 ∧
            0 < incidentPorts f p W.chart W.left W.right (j,true) 1))) ∧
        ((ca = u ∧ ta ∈ Ioo l u) ∨ (ca = z ∧ ta ∈ Ioo z q)) ∧
        tb ∈ Ioo gu gz ∧
        (f (some v) ta).val ∈ W.chart.source ∧
        W.chart (f (some v) ta).val ∈ Metric.ball (0 : Plane) η ∧
        W.chart (f (some v) ta).val 1 = 0 ∧ W.chart (f (some v) ta).val 0 ≠ 0 ∧
        (f (some w) tb).val ∈ W.chart.source ∧
        W.chart (f (some w) tb).val ∈ Metric.ball (0 : Plane) η ∧
        W.chart (f (some w) tb).val 1 ≠ 0 ∧ (f (some w) tb).val ∈ U := by
    let p := f (some v) ca
    have hpfirst : p ∈ range d.first := by
      rw [hfirstRange]
      refine ⟨ca,?_,rfl⟩
      rcases hca with rfl | rfl
      · exact ⟨le_rfl,huz.le⟩
      · exact ⟨huz.le,le_rfl⟩
    have hpsecond : p ∈ range d.second := by
      rw [hsecondRange]
      refine ⟨cb,?_,heq.symm⟩
      rcases hcb with rfl | rfl
      · exact ⟨le_rfl,hgugz.le⟩
      · exact ⟨hgugz.le,le_rfl⟩
    have hpv : p ∈ range (f (some v)) := ⟨ca,rfl⟩
    have hpw : p ∈ range (f (some w)) := ⟨cb,heq.symm⟩
    have hpe : p ∈ fan.events := by
      rw [fan.events_exact]
      exact ⟨hdV (hfirstDisk hpfirst),Or.inl hpfirst,some v,by simp,
        some w,fun h => hvw (Option.some.inj h),hpv,hpw⟩
    obtain ⟨W,hWsmall,hW0,hW1,hWsign⟩ :=
      fan.selected_axis_fans ⟨p,hpe⟩ (some v) (by simp) hpv
    obtain ⟨η,hη,hη1,hηtarget,hηguide⟩ :=
      hFanShrinking p W Eguide.source Eguide.open_source (hsecondSource p hpsecond)
    let Ta : Set Interval := {t | (f (some v) t).val ∈ W.chart.source ∧
      W.chart (f (some v) t).val ∈ Metric.ball (0 : Plane) η}
    have hTa : IsOpen Ta :=
      (W.chart.isOpen_inter_preimage Metric.isOpen_ball).preimage
        (continuous_subtype_val.comp (f (some v)).continuous)
    have hcaT : ca ∈ Ta := by
      refine ⟨W.contact_in_source,?_⟩
      change W.chart p.val ∈ Metric.ball (0 : Plane) η
      rw [W.contact_zero]
      simpa using hη
    have hta : ∃ ta : Interval, ta ∈ Ta ∧
        ((ca = u ∧ ta ∈ Ioo l u) ∨ (ca = z ∧ ta ∈ Ioo z q)) := by
      rcases hca with hc | hc
      · have hcclose : ca ∈ closure (Ioo l u) := by
          rw [closure_Ioo (ne_of_lt hl.2),hc]
          exact ⟨hl.2.le,le_rfl⟩
        obtain ⟨ta,hta,hinside⟩ := mem_closure_iff.mp hcclose Ta hTa hcaT
        exact ⟨ta,hta,Or.inl ⟨hc,hinside⟩⟩
      · have hcclose : ca ∈ closure (Ioo z q) := by
          rw [closure_Ioo (ne_of_lt hq.1),hc]
          exact ⟨le_rfl,hq.1.le⟩
        obtain ⟨ta,hta,hinside⟩ := mem_closure_iff.mp hcclose Ta hTa hcaT
        exact ⟨ta,hta,Or.inr ⟨hc,hinside⟩⟩
    obtain ⟨ta,hta,htaOrder⟩ := hta
    have htaNe : ta ≠ ca := by
      rcases htaOrder with h | h
      · rw [h.1]
        exact ne_of_lt h.2.2
      · rw [h.1]
        exact ne_of_gt h.2.1
    have htaAxis : W.chart (f (some v) ta).val 1 = 0 :=
      (hFanAxis p W ⟨some v,hpv⟩ hW0 hW1 _ hta.1
        (Metric.closedBall_subset_closedBall hη1.le (Metric.ball_subset_closedBall hta.2))).mp ⟨ta,rfl⟩
    have htaX : W.chart (f (some v) ta).val 0 ≠ 0 := by
      intro he
      have hc : W.chart (f (some v) ta).val = W.chart p.val := by
        rw [W.contact_zero]
        ext i
        fin_cases i
        · exact he
        · exact htaAxis
      have hpoint : f (some v) ta = p :=
        Subtype.ext (W.chart.injOn hta.1 W.contact_in_source hc)
      exact htaNe (ha.injective hpoint)
    let Tb : Set Interval := {t | (f (some w) t).val ∈ W.chart.source ∧
      W.chart (f (some w) t).val ∈ Metric.ball (0 : Plane) η}
    have hTb : IsOpen Tb :=
      (W.chart.isOpen_inter_preimage Metric.isOpen_ball).preimage
        (continuous_subtype_val.comp (f (some w)).continuous)
    have hcbT : cb ∈ Tb := by
      change (f (some w) cb).val ∈ W.chart.source ∧ _
      rw [← heq]
      refine ⟨W.contact_in_source,?_⟩
      change W.chart p.val ∈ Metric.ball (0 : Plane) η
      rw [W.contact_zero]
      simpa using hη
    have hcbclose : cb ∈ closure (Ioo gu gz) := by
      rw [closure_Ioo (ne_of_lt hgugz)]
      rcases hcb with rfl | rfl
      · exact ⟨le_rfl,hgugz.le⟩
      · exact ⟨hgugz.le,le_rfl⟩
    let G : Set Interval := Tb ∩ (fun t => (f (some w) t).val) ⁻¹' U
    have hG : IsOpen G := hTb.inter
      (hU.preimage (continuous_subtype_val.comp (f (some w)).continuous))
    have hcbG : cb ∈ G := ⟨hcbT,by change (f (some w) cb).val ∈ U; rw [← heq]; exact hpU⟩
    obtain ⟨tb,htbG,htbOrder⟩ := mem_closure_iff.mp hcbclose G hG hcbG
    have htb := htbG.1
    have htbY : W.chart (f (some w) tb).val 1 ≠ 0 := by
      intro he
      have hvb := (hFanAxis p W ⟨some v,hpv⟩ hW0 hW1 _ htb.1
        (Metric.closedBall_subset_closedBall hη1.le (Metric.ball_subset_closedBall htb.2))).mpr he
      have hbsecond : f (some w) tb ∈ range d.second := hsecondRange.symm ▸
        ⟨tb,⟨htbOrder.1.le,htbOrder.2.le⟩,rfl⟩
      have hbfirst : f (some w) tb ∈ range d.first := d.whole_first ▸
        ⟨hsecondDisk hbsecond,hvb⟩
      have hbcorner : f (some w) tb ∈ C₀ := by
        change f (some w) tb ∈ {d.first 0,d.first 1}
        exact d.sides_inter ▸ ⟨hbfirst,hbsecond⟩
      rw [← hcorners] at hbcorner
      rcases mem_insert_iff.mp hbcorner with hh | hh
      · exact (ne_of_gt htbOrder.1) (hb.injective hh)
      · exact (ne_of_lt htbOrder.2) (hb.injective (mem_singleton_iff.mp hh))
    exact ⟨W,η,ta,tb,hη,hη1,hηtarget,hηguide,hW0,hW1,hWsign,
      htaOrder,htbOrder,hta.1,hta.2,htaAxis,htaX,htb.1,htb.2,htbY,htbG.2⟩
  have hActualCornerFamily (ca cb : Interval)
      (hca : ca = u ∨ ca = z) (hcb : cb = gu ∨ cb = gz)
      (heq : f (some v) ca = f (some w) cb)
      (U : Set S) (hU : IsOpen U) (hpU : (f (some v) ca).val ∈ U) :
      ∃ ta tb : Interval, ∃ endpoint : C(Interval,↥F),
        ((ca = u ∧ ta ∈ Ioo l u) ∨ (ca = z ∧ ta ∈ Ioo z q)) ∧
        tb ∈ Ioo gu gz ∧ (f (some w) tb).val ∈ U ∧
        endpoint 0 = f (some w) tb ∧
        (∀ τ, (endpoint τ).val ∈ Eguide.source) ∧
        ∀ τ : Interval, 0 < τ.val →
          ∃ arc : C(Interval,↥F), IsEmbedding arc ∧
            range arc ⊆ {z | z.val ∈ Eguide.source} ∧
            arc 0 = f (some v) ta ∧ arc 1 = endpoint τ ∧
            range arc ∩ range (f (some v)) = {f (some v) ta} ∧
            Disjoint (range arc) (range (f (some w))) ∧
            (∀ i : Option ι, endpoint τ ∉ range (f i)) ∧
            (∀ s, arc s ∉ range d.disk) ∧
            ∀ i : Option ι, i ≠ some v →
              (range arc ∩ range (f i)).Finite ∧
              (range arc ∩ range (f i)).ncard ≤ if f (some v) ca ∈ range (f i) then 1 else 0 := by
    obtain ⟨W,η,ta,tb,hη,hη1,hηtarget,hηguide,hW0,hW1,hWsign,
      htaOrder,htbOrder,hta,htaBall,htaAxis,htaNe,htb,htbBall,htbY,htbU⟩ :=
      hCornerInputs ca cb hca hcb heq U hU hpU
    obtain ⟨endpoint,he0,heSource,hpieces⟩ := hCornerFamilyOriented
      (f (some v) ca) W ⟨ca,rfl⟩ ⟨cb,heq.symm⟩ hW0 hW1 hWsign η hη hη1
      hηtarget hηguide (f (some v) ta) (f (some w) tb) hta htaBall htaAxis htaNe
      htb htbBall ⟨tb,rfl⟩ htbY
    have hattachFirst : f (some v) ta ∉ range d.first := by
      rw [hfirstRange]
      rintro ⟨t,ht,he⟩
      have hte : t = ta := ha.injective he
      subst t
      rcases htaOrder with h | h
      · exact not_le_of_gt h.2.2 ht.1
      · exact not_le_of_gt h.2.1 ht.2
    have hattachDisk : f (some v) ta ∉ range d.disk := by
      intro hd
      exact hattachFirst (d.whole_first ▸ ⟨hd,⟨ta,rfl⟩⟩)
    refine ⟨ta,tb,endpoint,htaOrder,htbOrder,htbU,he0,heSource,?_⟩
    intro τ hτ
    obtain ⟨arc,hEmb,hguide,hstart,hend,hmeet,hclear,hports,hcounts⟩ := hpieces τ hτ
    have hfirstAvoid : Disjoint (range arc) (range d.first) := by
      apply disjoint_left.mpr
      intro y hy hyf
      have hye : y = f (some v) ta := mem_singleton_iff.mp (hmeet ▸ ⟨hy,hfirstWhole hyf⟩)
      exact hattachFirst (hye ▸ hyf)
    have hstartDisk : arc 0 ∉ range d.disk := hstart.symm ▸ hattachDisk
    exact ⟨arc,hEmb,hguide,hstart,hend,hmeet,hclear,hports,
      hCornerOutsideDisk arc hfirstAvoid hclear hstartDisk,hcounts⟩
  have hGuideInteriorBounds (y : ↥F) (hy : y ∈ range d.second \ C₀) : -1 < Eguide y.val 0 ∧ Eguide y.val 0 < 1 := by
    have hcore : y ∈ f (some w) '' Icc gu gz := hsecondRange ▸ hy.1
    have hpSquare : Eguide y.val ∈ Plane.closedSquare 0 1 :=
      (hGuideTrace.symm ▸ hcore).1.2
    have habs : |Eguide y.val 0| ≤ 1 :=
      (le_max_left _ _).trans (mem_closedSquare_zero_one.mp hpSquare)
    have hnotCorner (t : Interval) (ht : t = gu ∨ t = gz) : y ≠ f (some w) t := by
      intro he
      apply hy.2
      rw [← hcorners,he]
      rcases ht with rfl | rfl
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_singleton _)
    have hnotLeft : Eguide y.val 0 ≠ -1 := by
      intro he
      apply hnotCorner gu (Or.inl rfl)
      apply Subtype.ext
      apply Eguide.injOn (hsecondSource y hy.1)
        (hGuideCore _ ⟨gu,⟨le_rfl,hgugz.le⟩,rfl⟩)
      rw [hGuideZero]
      ext i
      fin_cases i
      · exact he
      · exact hsecondZero y hy.1
    have hnotRight : Eguide y.val 0 ≠ 1 := by
      intro he
      apply hnotCorner gz (Or.inr rfl)
      apply Subtype.ext
      apply Eguide.injOn (hsecondSource y hy.1)
        (hGuideCore _ ⟨gz,⟨hgugz.le,le_rfl⟩,rfl⟩)
      rw [hGuideOne]
      ext i
      fin_cases i
      · exact he
      · exact hsecondZero y hy.1
    exact ⟨lt_of_le_of_ne (abs_le.mp habs).1 hnotLeft.symm,
      lt_of_le_of_ne (abs_le.mp habs).2 hnotRight⟩
  have hPbounds (p : ↥P) : -1 < Eguide p.val.val 0 ∧ Eguide p.val.val 0 < 1 :=
    hGuideInteriorBounds p.val p.property.1
  let contactCoordinates : Finset ℝ := Finset.univ.image (fun p : ↥P => Eguide p.val.val 0)
  have hcoords : ∀ ξ ∈ contactCoordinates, -1 < ξ ∧ ξ < 1 := by
    intro ξ hξ
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hξ
    exact hPbounds p
  obtain ⟨stripL,stripR,hstripL,hstripLR,hstripR,hstripContains⟩ :=
    actual_finite_boundary_coordinate_enclosing_interval (insert 0 contactCoordinates)
      (Finset.insert_nonempty _ _) (by
        intro ξ hξ
        rcases Finset.mem_insert.mp hξ with rfl | hξ
        · norm_num
        · exact hcoords ξ hξ)
  obtain ⟨stripWidth,exteriorSign,hstripWidth,hexteriorSign,hstripSupport,hstripSide⟩ :=
    hExteriorStrip stripL stripR hstripL hstripLR hstripR
  have hstripZero : stripL < 0 ∧ (0 : ℝ) < stripR :=
    hstripContains 0 (Finset.mem_insert_self _ _)
  have hWiderExterior (L R : ℝ) (hL : -1 < L) (hL0 : L < 0)
      (hR0 : 0 < R) (hR : R < 1) :
      ∃ ε : ℝ, 0 < ε ∧
        ∀ z : Plane, L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε → z 1 ≠ 0 →
          (Eguide.symm z ∉ range diskAmbient ↔ 0 < exteriorSign*z 1) := by
    obtain ⟨ε,σ,hε,hσ,hsupport,hside⟩ := hExteriorStrip L R hL (hL0.trans hR0) hR
    let h := min ε stripWidth / 2
    have hh : 0 < h := half_pos (lt_min hε hstripWidth)
    have hhε : h < ε := by dsimp [h]; have := min_le_left ε stripWidth; linarith
    have hhW : h < stripWidth := by dsimp [h]; have := min_le_right ε stripWidth; linarith
    have hiff : (0 < σ*h) ↔ 0 < exteriorSign*h :=
      (hside (Plane.mk 0 h) hL0 hR0 (by change -ε < h; linarith) hhε (ne_of_gt hh)).symm.trans
        (hstripSide (Plane.mk 0 h) hstripZero.1 hstripZero.2
          (by change -stripWidth < h; linarith) hhW (ne_of_gt hh))
    have heq : σ = exteriorSign := by
      rcases hσ with hs | hs <;> rcases hexteriorSign with ht | ht
      · exact hs.trans ht.symm
      · rw [hs,ht] at hiff
        have hn := hiff.mpr (by simpa using hh)
        linarith
      · rw [hs,ht] at hiff
        have hn := hiff.mp (by simpa using hh)
        linarith
      · exact hs.trans ht.symm
    exact ⟨ε,hε,heq ▸ hside⟩
  have hCornerCommonSign (endpoint : C(Interval,↥F))
      (hSource : ∀ τ, (endpoint τ).val ∈ Eguide.source)
      (hZero : endpoint 0 ∈ range d.second \ C₀)
      (hAvoid : ∀ τ : Interval, 0 < τ.val →
        endpoint τ ∉ range d.disk ∧ endpoint τ ∉ range (f (some w))) :
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ : Interval, 0 < τ.val → τ.val < ρ →
        0 < exteriorSign*Eguide (endpoint τ).val 1 := by
    have hξ := hGuideInteriorBounds (endpoint 0) hZero
    obtain ⟨L,hL⟩ := exists_between (lt_min hξ.1 (show (-1 : ℝ) < 0 by norm_num))
    obtain ⟨R,hR⟩ := exists_between (max_lt hξ.2 zero_lt_one)
    have hL0 : L < 0 := hL.2.trans_le (min_le_right _ _)
    have hR0 : 0 < R := (le_max_right _ _).trans_lt hR.1
    have hLξ : L < Eguide (endpoint 0).val 0 := hL.2.trans_le (min_le_left _ _)
    have hξR : Eguide (endpoint 0).val 0 < R := (le_max_left _ _).trans_lt hR.1
    obtain ⟨ε,hε,hside⟩ := hWiderExterior L R hL.1 hL0 hR0 hR.2
    have hmap : Continuous (fun τ : Interval => Eguide (endpoint τ).val) :=
      Eguide.continuousOn.comp_continuous (continuous_subtype_val.comp endpoint.continuous) hSource
    have hx : Continuous (fun τ : Interval => Eguide (endpoint τ).val 0) :=
      (show Continuous (fun z : Plane => z 0) from by fun_prop).comp hmap
    have hy : Continuous (fun τ : Interval => Eguide (endpoint τ).val 1) :=
      (show Continuous (fun z : Plane => z 1) from by fun_prop).comp hmap
    let O : Set Interval := {τ | L < Eguide (endpoint τ).val 0 ∧
      Eguide (endpoint τ).val 0 < R ∧ -ε < Eguide (endpoint τ).val 1 ∧
      Eguide (endpoint τ).val 1 < ε}
    have hO : IsOpen O := (isOpen_lt continuous_const hx).inter
      ((isOpen_lt hx continuous_const).inter
        ((isOpen_lt continuous_const hy).inter (isOpen_lt hy continuous_const)))
    have h0 : (0 : Interval) ∈ O := by
      change L < Eguide (endpoint 0).val 0 ∧ _
      rw [hsecondZero (endpoint 0) hZero.1]
      exact ⟨hLξ,hξR,neg_neg_of_pos hε,hε⟩
    obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hO 0 h0
    refine ⟨ρ,hρ,?_⟩
    intro τ hτ hτρ
    have hrect := hball (show τ ∈ Metric.ball (0 : Interval) ρ by
      simpa [Subtype.dist_eq,Real.dist_eq,abs_of_pos hτ] using hτρ)
    have hnonzero : Eguide (endpoint τ).val 1 ≠ 0 := by
      intro he
      obtain ⟨t,ht⟩ := (hGuideAxis _ (hSource τ)).mpr he
      exact (hAvoid τ hτ).2 ⟨t,Subtype.ext ht⟩
    apply (hside (Eguide (endpoint τ).val) hrect.1 hrect.2.1 hrect.2.2.1 hrect.2.2.2 hnonzero).mp
    rw [Eguide.left_inv (hSource τ),hdiskRange]
    rintro ⟨y,hy,he⟩
    exact (hAvoid τ hτ).1 ((Subtype.ext he : y = endpoint τ) ▸ hy)
  choose eventA eventB eventL eventR eventPiece eventAxis
    hEventA hEventB hEventImage hEventAxisData hEventSupport
    hEventL0 hEventR0 hEventLy0 hEventRy0 hEventSource hEventSign hEventPiece hEventPositive
    using (fun p : ↥P => hOrderedEvent p exteriorSign hexteriorSign)
  have hCornersSelected : C₀ ⊆ range (f (some v)) := by
    intro y hy
    apply hfirstWhole
    change y ∈ {d.first 0,d.first 1} at hy
    rcases mem_insert_iff.mp hy with hh | hh
    · exact ⟨0,hh.symm⟩
    · exact ⟨1,(mem_singleton_iff.mp hh).symm⟩
  have hEventAxisSelectedClear (p : ↥P) (y : ↥F) (hy : y ∈ range (eventAxis p)) :
      y ∉ range (f (some v)) := by
    intro hyv
    have he := (hEventAxisData p y hy).2.2 (some v)
      (fun hh => hvw (Option.some.inj hh)) hyv
    exact disjoint_left.mp hPselectedClear p.property (he ▸ hyv)
  have hEventBounds (p : ↥P) : -1 < eventA p ∧ eventB p < 1 := by
    let φ : Interval → ℝ := fun t => Eguide (eventAxis p t).val 0
    have hφ : Continuous φ := (show Continuous (fun z : Plane => z 0) from by fun_prop).comp
      (Eguide.continuousOn.comp_continuous (continuous_subtype_val.comp (eventAxis p).continuous)
        (fun t => (hEventAxisData p _ ⟨t,rfl⟩).1))
    have hNo (t : Interval) (ht : t = gu ∨ t = gz) (ξ : ℝ)
        (hξ : Eguide (f (some w) t).val = Plane.mk ξ 0) : ξ ∉ range φ := by
      rintro ⟨s,hs⟩
      have htguide : (f (some w) t).val ∈ Eguide.source :=
        hGuideCore _ ⟨t,by rcases ht with rfl | rfl <;> exact ⟨by order,by order⟩,rfl⟩
      have htcorner : f (some w) t ∈ C₀ := by
        rw [← hcorners]
        rcases ht with rfl | rfl
        · exact mem_insert _ _
        · exact mem_insert_of_mem _ (mem_singleton _)
      have he : Eguide (eventAxis p s).val = Eguide (f (some w) t).val := by
        rw [hξ]
        ext i
        fin_cases i
        · exact hs
        · exact (hEventAxisData p _ ⟨s,rfl⟩).2.1
      have hpoint : eventAxis p s = f (some w) t := Subtype.ext
        (Eguide.injOn (hEventAxisData p _ ⟨s,rfl⟩).1 htguide he)
      exact hEventAxisSelectedClear p _ ⟨s,rfl⟩ (hpoint.symm ▸ hCornersSelected htcorner)
    have hBound : range φ ⊆ Ioo (-1 : ℝ) 1 :=
      actual_connected_axis_coordinate_bounds (range φ) (isPreconnected_range hφ) (-1) 1
        (Eguide p.val.val 0) (by
          change Eguide p.val.val 0 ∈ range (fun t => Eguide (eventAxis p t).val 0)
          rw [hEventImage]
          exact ⟨(hEventA p).le,(hEventB p).le⟩)
        (hPbounds p).1 (hPbounds p).2
        (hNo gu (Or.inl rfl) (-1) hGuideZero) (hNo gz (Or.inr rfl) 1 hGuideOne)
    have hab : eventA p ≤ eventB p := (hEventA p).trans (hEventB p) |>.le
    exact ⟨(hBound (hEventImage p ▸ (show eventA p ∈ Icc (eventA p) (eventB p) from ⟨le_rfl,hab⟩))).1,
      (hBound (hEventImage p ▸ (show eventB p ∈ Icc (eventA p) (eventB p) from ⟨hab,le_rfl⟩))).2⟩
  have hEventIntervalsDisjoint (p q : ↥P) (hpq : p ≠ q) :
      Disjoint (Icc (eventA p) (eventB p)) (Icc (eventA q) (eventB q)) := by
    apply disjoint_left.mpr
    intro ξ hξp hξq
    rw [← hEventImage p] at hξp
    rw [← hEventImage q] at hξq
    obtain ⟨s,hs⟩ := hξp
    obtain ⟨t,ht⟩ := hξq
    have he : Eguide (eventAxis p s).val = Eguide (eventAxis q t).val := by
      ext i
      fin_cases i
      · exact hs.trans ht.symm
      · exact (hEventAxisData p _ ⟨s,rfl⟩).2.1.trans
          (hEventAxisData q _ ⟨t,rfl⟩).2.1.symm
    have hpoint : eventAxis p s = eventAxis q t := Subtype.ext
      (Eguide.injOn (hEventAxisData p _ ⟨s,rfl⟩).1 (hEventAxisData q _ ⟨t,rfl⟩).1 he)
    have hdis := fan.windows_disjoint ⟨p.val,hPfan p.property⟩ ⟨q.val,hPfan q.property⟩
      (fun hh => hpq (Subtype.ext (congrArg (fun z : ↥fan.events => z.val) hh)))
    have hp := hEventSupport p ⟨s,rfl⟩
    have hq := hEventSupport q ⟨t,rfl⟩
    rw [← hpoint] at hq
    exact disjoint_left.mp hdis ⟨hp.1,Metric.ball_subset_closedBall hp.2⟩
      ⟨hq.1,Metric.ball_subset_closedBall hq.2⟩
  have hEventIntervalsOrdered (p q : ↥P) (hpq : Eguide p.val.val 0 < Eguide q.val.val 0) :
      eventB p < eventA q := by
    have hdis := hEventIntervalsDisjoint p q (fun he => by rw [he] at hpq; exact lt_irrefl _ hpq)
    by_contra hn
    have hle : eventA q ≤ eventB p := le_of_not_gt hn
    let ξ := max (eventA p) (eventA q)
    have hp : ξ ∈ Icc (eventA p) (eventB p) :=
      ⟨le_max_left _ _,max_le ((hEventA p).trans (hEventB p)).le hle⟩
    have hq : ξ ∈ Icc (eventA q) (eventB q) :=
      ⟨le_max_right _ _,max_le ((hEventA p).trans (hpq.trans (hEventB q))).le
        ((hEventA q).trans (hEventB q)).le⟩
    exact disjoint_left.mp hdis hp hq
  have hContactFreeAxis (ξ : ℝ) (hξ : -1 < ξ ∧ ξ < 1) (hNo : ξ ∉ contactCoordinates) :
      Plane.mk ξ 0 ∈ Eguide.target ∧ ∀ i : Option ι, i ≠ some w →
        Eguide.symm (Plane.mk ξ 0) ∉ Subtype.val '' range (f i) := by
    obtain ⟨y,hySource,hySecond,hyCoord⟩ := hAxisPoint ξ ⟨hξ.1.le,hξ.2.le⟩
    have hyClear : y ∉ range (f (some v)) := by
      obtain ⟨z,hzSource,hzCoord,hzClear⟩ := hAxisSelectedClear ξ hξ.1 hξ.2
      have he : y.val = z := Eguide.injOn hySource hzSource (hyCoord.trans hzCoord.symm)
      exact fun hyv => hzClear ⟨y,hyv,he⟩
    have hyNotCorner : y ∉ C₀ := fun hyc => hyClear (hCornersSelected hyc)
    refine ⟨hyCoord ▸ Eguide.map_source hySource,?_⟩
    intro i hi hmem
    have hinverse : Eguide.symm (Plane.mk ξ 0) = y.val := by rw [← hyCoord,Eguide.left_inv hySource]
    rw [hinverse] at hmem
    obtain ⟨z,hzi,hzy⟩ := hmem
    have hyi : y ∈ range (f i) := (Subtype.ext hzy : z = y) ▸ hzi
    let yp : ↥P := ⟨y,⟨hySecond,hyNotCorner⟩,i,hi,hyi⟩
    apply hNo
    exact Finset.mem_image.mpr ⟨yp,Finset.mem_univ _,congrArg (fun z : Plane => z 0) hyCoord⟩
  let eventEndpoints : Finset ℝ := insert 0 (Finset.univ.image eventA ∪ Finset.univ.image eventB)
  have hEventEndpointBounds : ∀ ξ ∈ eventEndpoints, -1 < ξ ∧ ξ < 1 := by
    intro ξ hξ
    rcases Finset.mem_insert.mp hξ with rfl | hξ
    · norm_num
    · rcases Finset.mem_union.mp hξ with hξ | hξ
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hξ
        exact ⟨(hEventBounds p).1,(hEventA p).trans (hPbounds p).2⟩
      · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hξ
        exact ⟨(hPbounds p).1.trans (hEventB p),(hEventBounds p).2⟩
  obtain ⟨edgeL,edgeR,hedgeL,hedgeLR,hedgeR,hedgeContains⟩ :=
    actual_finite_boundary_coordinate_enclosing_interval eventEndpoints
      (Finset.insert_nonempty _ _) hEventEndpointBounds
  have hedgeA (p : ↥P) : edgeL < eventA p :=
    (hedgeContains _ (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)))).1
  have hedgeB (p : ↥P) : eventB p < edgeR :=
    (hedgeContains _ (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)))).2
  have hselectedCorners : {f (some v) u,f (some v) z} = C₀ := by
    have hzero : d.first 0 = f (some v) d.aStart := by
      simpa [intervalAffine,f,augmented] using d.first_eq 0
    have hone : d.first 1 = f (some v) d.aFinish := by
      simpa [intervalAffine,f,augmented] using d.first_eq 1
    dsimp only [u,z,C₀]
    rw [hzero,hone]
    rcases le_total d.aStart d.aFinish with h | h
    · rw [min_eq_left h,max_eq_right h]
    · rw [min_eq_right h,max_eq_left h]
      exact Set.pair_comm _ _
  obtain ⟨caL,caR,hcaOrder,hcaL,hcaR⟩ :
      ∃ caL caR : Interval, ((caL = u ∧ caR = z) ∨ (caL = z ∧ caR = u)) ∧
        f (some v) caL = f (some w) gu ∧ f (some v) caR = f (some w) gz := by
    rcases pair_eq_pair_iff.mp (hselectedCorners.trans hcorners.symm) with h | h
    · exact ⟨u,z,Or.inl ⟨rfl,rfl⟩,h.1,h.2⟩
    · exact ⟨z,u,Or.inr ⟨rfl,rfl⟩,h.2,h.1⟩
  have hcaLChoice : caL = u ∨ caL = z := hcaOrder.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hcaRChoice : caR = u ∨ caR = z := hcaOrder.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
  let UL : Set S := Eguide.source ∩ Eguide ⁻¹' {z : Plane | z 0 < edgeL}
  let UR : Set S := Eguide.source ∩ Eguide ⁻¹' {z : Plane | edgeR < z 0}
  have hUL : IsOpen UL := Eguide.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)
  have hUR : IsOpen UR := Eguide.isOpen_inter_preimage (isOpen_lt continuous_const (by fun_prop))
  have hpUL : (f (some v) caL).val ∈ UL := by
    rw [hcaL]
    refine ⟨hGuideCore _ ⟨gu,⟨le_rfl,hgugz.le⟩,rfl⟩,?_⟩
    change Eguide (f (some w) gu).val 0 < edgeL
    rw [show Eguide (f (some w) gu).val = Plane.mk (-1) 0 from hGuideZero]
    exact hedgeL
  have hpUR : (f (some v) caR).val ∈ UR := by
    rw [hcaR]
    refine ⟨hGuideCore _ ⟨gz,⟨hgugz.le,le_rfl⟩,rfl⟩,?_⟩
    change edgeR < Eguide (f (some w) gz).val 0
    rw [show Eguide (f (some w) gz).val = Plane.mk 1 0 from hGuideOne]
    exact hedgeR
  obtain ⟨taL,tbL,leftEndpoint,hLeftOrder,hLeftInside,hLeftU,hLeftZero,hLeftSource,hLeftProducer⟩ :=
    hActualCornerFamily caL gu hcaLChoice (Or.inl rfl) hcaL UL hUL hpUL
  obtain ⟨taR,tbR,rightEndpoint,hRightOrder,hRightInside,hRightU,hRightZero,hRightSource,hRightProducer⟩ :=
    hActualCornerFamily caR gz hcaRChoice (Or.inr rfl) hcaR UR hUR hpUR
  have hStrictGuideParam (t : Interval) (ht : t ∈ Ioo gu gz) :
      f (some w) t ∈ range d.second \ C₀ := by
    refine ⟨hsecondRange.symm ▸ ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩,?_⟩
    rw [← hcorners]
    intro hh
    rcases mem_insert_iff.mp hh with hh | hh
    · exact (ne_of_gt ht.1) (hb.injective hh)
    · exact (ne_of_lt ht.2) (hb.injective (mem_singleton_iff.mp hh))
  have hLeftZeroSide : leftEndpoint 0 ∈ range d.second \ C₀ :=
    hLeftZero.symm ▸ hStrictGuideParam tbL hLeftInside
  have hRightZeroSide : rightEndpoint 0 ∈ range d.second \ C₀ :=
    hRightZero.symm ▸ hStrictGuideParam tbR hRightInside
  have hLeftAvoid (τ : Interval) (hτ : 0 < τ.val) :
      leftEndpoint τ ∉ range d.disk ∧ leftEndpoint τ ∉ range (f (some w)) := by
    obtain ⟨arc,hEmb,hGuide,hstart,hend,hmeet,hclear,hports,houtside,hcounts⟩ := hLeftProducer τ hτ
    exact ⟨hend ▸ houtside 1,hports (some w)⟩
  have hRightAvoid (τ : Interval) (hτ : 0 < τ.val) :
      rightEndpoint τ ∉ range d.disk ∧ rightEndpoint τ ∉ range (f (some w)) := by
    obtain ⟨arc,hEmb,hGuide,hstart,hend,hmeet,hclear,hports,houtside,hcounts⟩ := hRightProducer τ hτ
    exact ⟨hend ▸ houtside 1,hports (some w)⟩
  obtain ⟨ρL,hρL,hLeftSign⟩ := hCornerCommonSign leftEndpoint hLeftSource hLeftZeroSide hLeftAvoid
  obtain ⟨ρR,hρR,hRightSign⟩ := hCornerCommonSign rightEndpoint hRightSource hRightZeroSide hRightAvoid
  let ε := min ρL ρR
  have hε : 0 < ε := lt_min hρL hρR
  have hleftAxisBounds : -1 < Eguide (leftEndpoint 0).val 0 ∧
      Eguide (leftEndpoint 0).val 0 < edgeL := by
    refine ⟨(hGuideInteriorBounds _ hLeftZeroSide).1,?_⟩
    rw [hLeftZero]
    exact hLeftU.2
  have hrightAxisBounds : edgeR < Eguide (rightEndpoint 0).val 0 ∧
      Eguide (rightEndpoint 0).val 0 < 1 := by
    refine ⟨?_,(hGuideInteriorBounds _ hRightZeroSide).2⟩
    rw [hRightZero]
    exact hRightU.2
  have hAttachmentOrder :
      (taL ∈ Ioo l u ∧ taR ∈ Ioo z q) ∨ (taR ∈ Ioo l u ∧ taL ∈ Ioo z q) := by
    rcases hcaOrder with h | h
    · rcases hLeftOrder with hL | hL
      · rcases hRightOrder with hR | hR
        · exact ((ne_of_lt huz).symm (h.2.symm.trans hR.1)).elim
        · exact Or.inl ⟨hL.2,hR.2⟩
      · exact (ne_of_lt huz (h.1.symm.trans hL.1)).elim
    · rcases hLeftOrder with hL | hL
      · exact ((ne_of_lt huz).symm (h.1.symm.trans hL.1)).elim
      · rcases hRightOrder with hR | hR
        · exact Or.inr ⟨hR.2,hL.2⟩
        · exact (ne_of_lt huz (h.2.symm.trans hR.1)).elim
  let newL := min taL taR
  let newR := max taL taR
  have hNewCuts : A < newL ∧ newL < u ∧ u < z ∧ z < newR ∧ newR < B := by
    rcases hAttachmentOrder with h | h
    · have hlt : taL < taR := h.1.2.trans (huz.trans h.2.1)
      dsimp only [newL,newR]
      rw [min_eq_left hlt.le,max_eq_right hlt.le]
      exact ⟨hAl.trans h.1.1,h.1.2,huz,h.2.1,h.2.2.trans hqB⟩
    · have hlt : taR < taL := h.1.2.trans (huz.trans h.2.1)
      dsimp only [newL,newR]
      rw [min_eq_right hlt.le,max_eq_left hlt.le]
      exact ⟨hAl.trans h.1.1,h.1.2,huz,h.2.1,h.2.2.trans hqB⟩
  have hNewBounds : l ≤ newL ∧ newR ≤ q := by
    rcases hAttachmentOrder with h | h
    · have hlt : taL < taR := h.1.2.trans (huz.trans h.2.1)
      dsimp only [newL,newR]
      rw [min_eq_left hlt.le,max_eq_right hlt.le]
      exact ⟨h.1.1.le,h.2.2.le⟩
    · have hlt : taR < taL := h.1.2.trans (huz.trans h.2.1)
      dsimp only [newL,newR]
      rw [min_eq_right hlt.le,max_eq_left hlt.le]
      exact ⟨h.1.1.le,h.2.2.le⟩
  have hNewOld : f (some v) '' Icc newL newR ⊆ f (some v) '' Icc l q :=
    image_mono (Icc_subset_Icc hNewBounds.1 hNewBounds.2)
  have hNewOrientation :
      (f (some v) taL = f (some v) newL ∧ f (some v) taR = f (some v) newR) ∨
      (f (some v) taL = f (some v) newR ∧ f (some v) taR = f (some v) newL) := by
    rcases le_total taL taR with h | h
    · left
      simp only [newL,newR,min_eq_left h,max_eq_right h,and_self]
    · right
      simp only [newL,newR,min_eq_right h,max_eq_left h,and_self]
  choose rawCornerL hRawLEmb hRawLGuide hRawLStart hRawLEnd hRawLMeet hRawLClear
    hRawLPorts hRawLOut hRawLCounts using
      (fun τ : {τ : Interval // 0 < τ.val} => hLeftProducer τ.val τ.property)
  choose rawCornerR hRawREmb hRawRGuide hRawRStart hRawREnd hRawRMeet hRawRClear
    hRawRPorts hRawROut hRawRCounts using
      (fun τ : {τ : Interval // 0 < τ.val} => hRightProducer τ.val τ.property)
  let cornerL : Interval → C(Interval,↥F) := fun τ =>
    if h : 0 < τ.val then rawCornerL ⟨τ,h⟩ else ContinuousMap.const _ (f (some v) taL)
  let cornerR : Interval → C(Interval,↥F) := fun τ =>
    if h : 0 < τ.val then
      (rawCornerR ⟨τ,h⟩).comp ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
    else ContinuousMap.const _ (f (some v) taR)
  have hCornerL (τ : Interval) (hτ : 0 < τ.val) :
      IsEmbedding (cornerL τ) ∧ range (cornerL τ) ⊆ {y | y.val ∈ Eguide.source} ∧
      cornerL τ 0 = f (some v) taL ∧ cornerL τ 1 = leftEndpoint τ ∧
      range (cornerL τ) ∩ range (f (some v)) = {f (some v) taL} ∧
      Disjoint (range (cornerL τ)) (range (f (some w))) ∧
      (∀ i : Option ι, leftEndpoint τ ∉ range (f i)) ∧
      ∀ i : Option ι, i ≠ some v → (range (cornerL τ) ∩ range (f i)).Finite ∧
        (range (cornerL τ) ∩ range (f i)).ncard ≤ if f (some w) gu ∈ range (f i) then 1 else 0 := by
    dsimp only [cornerL]
    rw [dif_pos hτ]
    refine ⟨hRawLEmb ⟨τ,hτ⟩,hRawLGuide ⟨τ,hτ⟩,hRawLStart ⟨τ,hτ⟩,
      hRawLEnd ⟨τ,hτ⟩,hRawLMeet ⟨τ,hτ⟩,hRawLClear ⟨τ,hτ⟩,hRawLPorts ⟨τ,hτ⟩,?_⟩
    intro i hi
    rw [← hcaL]
    exact hRawLCounts ⟨τ,hτ⟩ i hi
  have hCornerR (τ : Interval) (hτ : 0 < τ.val) :
      IsEmbedding (cornerR τ) ∧ range (cornerR τ) ⊆ {y | y.val ∈ Eguide.source} ∧
      cornerR τ 0 = rightEndpoint τ ∧ cornerR τ 1 = f (some v) taR ∧
      range (cornerR τ) ∩ range (f (some v)) = {f (some v) taR} ∧
      Disjoint (range (cornerR τ)) (range (f (some w))) ∧
      (∀ i : Option ι, rightEndpoint τ ∉ range (f i)) ∧
      ∀ i : Option ι, i ≠ some v → (range (cornerR τ) ∩ range (f i)).Finite ∧
        (range (cornerR τ) ∩ range (f i)).ncard ≤ if f (some w) gz ∈ range (f i) then 1 else 0 := by
    dsimp only [cornerR]
    rw [dif_pos hτ]
    have hRange : range ((rawCornerR ⟨τ,hτ⟩).comp
        ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩) = range (rawCornerR ⟨τ,hτ⟩) :=
      unitInterval.symmHomeomorph.surjective.range_comp (rawCornerR ⟨τ,hτ⟩)
    refine ⟨(hRawREmb ⟨τ,hτ⟩).comp unitInterval.symmHomeomorph.isEmbedding,?_,?_,?_,?_,?_,hRawRPorts ⟨τ,hτ⟩,?_⟩
    · rw [hRange]
      exact hRawRGuide ⟨τ,hτ⟩
    · simpa only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,
        unitInterval.symmHomeomorph_apply,unitInterval.symm_zero] using hRawREnd ⟨τ,hτ⟩
    · simpa only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,
        unitInterval.symmHomeomorph_apply,unitInterval.symm_one] using hRawRStart ⟨τ,hτ⟩
    · rw [hRange]
      exact hRawRMeet ⟨τ,hτ⟩
    · rw [hRange]
      exact hRawRClear ⟨τ,hτ⟩
    · intro i hi
      rw [hRange,← hcaR]
      exact hRawRCounts ⟨τ,hτ⟩ i hi
  let block (X : Type) (a b : X) (e : Fin m → X) : Fin (m+2) → X :=
    Fin.cases a (Fin.lastCases b e)
  have hblock0 (X : Type) (a b : X) (e : Fin m → X) :
      block X a b e ⟨0,by omega⟩ = a := rfl
  have hblockLast (X : Type) (a b : X) (e : Fin m → X) :
      block X a b e ⟨m+1,by omega⟩ = b := by
    change Fin.lastCases b e (Fin.last m) = b
    exact Fin.lastCases_last
  have hblockEvent (X : Type) (a b : X) (e : Fin m → X) (k : Fin m) :
      block X a b e ⟨k.val+1,by omega⟩ = e k := by
    change Fin.lastCases b e k.castSucc = e k
    exact Fin.lastCases_castSucc k
  have hBlockCases (k : Fin (m+2)) :
      k = ⟨0,Nat.zero_lt_succ (m+1)⟩ ∨ k = ⟨m+1,Nat.lt_succ_self (m+1)⟩ ∨
        ∃ j : Fin m, k = ⟨j.val+1,Nat.add_lt_add_right j.isLt 1 |>.trans (Nat.lt_succ_self (m+1))⟩ := by
    by_cases hk0 : k.val = 0
    · exact Or.inl (Fin.ext hk0)
    · by_cases hklast : k.val = m+1
      · exact Or.inr (Or.inl (Fin.ext hklast))
      · refine Or.inr (Or.inr ⟨⟨k.val-1,by omega⟩,?_⟩)
        apply Fin.ext
        dsimp
        omega
  let Ls := block C(Interval,↥F) (ContinuousMap.const _ (f (some v) taL))
    rightEndpoint (fun k => eventL (label k))
  let Rs := block C(Interval,↥F) leftEndpoint (ContinuousMap.const _ (f (some v) taR))
    (fun k => eventR (label k))
  let pieces := block (Interval → C(Interval,↥F)) cornerL cornerR (fun k => eventPiece (label k))
  let sites := block ↥F (f (some w) gu) (f (some w) gz) (fun k => (label k).val)
  have hGeometry (τ : Interval) (hτ : 0 < τ.val) (k : Fin (m+2)) :
      IsEmbedding (pieces k τ) ∧ range (pieces k τ) ⊆ {y | y.val ∈ Eguide.source} ∧
      (pieces k τ 0 = Ls k τ ∧ pieces k τ 1 = Rs k τ) ∧
      Disjoint (range (pieces k τ)) (range (f (some w))) ∧
      ∀ i : Option ι, i ≠ some v → (range (pieces k τ) ∩ range (f i)).Finite ∧
        (range (pieces k τ) ∩ range (f i)).ncard ≤ if sites k ∈ range (f i) then 1 else 0 := by
    rcases hBlockCases k with rfl | rfl | ⟨j,rfl⟩
    · simp only [pieces,Ls,Rs,sites,hblock0,ContinuousMap.const_apply]
      obtain ⟨hEmb,hGuide,hstart,hend,hmeet,hclear,hports,hcounts⟩ := hCornerL τ hτ
      exact ⟨hEmb,hGuide,⟨hstart,hend⟩,hclear,hcounts⟩
    · simp only [pieces,Ls,Rs,sites,hblockLast,ContinuousMap.const_apply]
      obtain ⟨hEmb,hGuide,hstart,hend,hmeet,hclear,hports,hcounts⟩ := hCornerR τ hτ
      exact ⟨hEmb,hGuide,⟨hstart,hend⟩,hclear,hcounts⟩
    · simp only [pieces,Ls,Rs,sites,hblockEvent]
      have hp := hEventPiece (label j) τ
      have hc := hEventPositive (label j) τ hτ
      exact ⟨hp.1,hp.2.1,hp.2.2,hc.2.1,fun i hi => hc.2.2.2 i⟩
  have hSelectedMeet (τ : Interval) (hτ : 0 < τ.val) :
      range (pieces ⟨0,by omega⟩ τ) ∩ range (f (some v)) = {f (some v) taL} ∧
      range (pieces ⟨m+1,by omega⟩ τ) ∩ range (f (some v)) = {f (some v) taR} ∧
      ∀ k : Fin m, Disjoint (range (pieces ⟨k.val+1,by omega⟩ τ)) (range (f (some v))) := by
    simp only [pieces,hblock0,hblockLast,hblockEvent]
    exact ⟨(hCornerL τ hτ).2.2.2.2.1,(hCornerR τ hτ).2.2.2.2.1,
      fun k => (hEventPositive (label k) τ hτ).1⟩
  let gapLeftFamily : Fin (m+1) → C(Interval,↥F) :=
    Fin.cases leftEndpoint (fun j : Fin m => eventR (label j))
  let gapRightFamily : Fin (m+1) → C(Interval,↥F) :=
    Fin.lastCases rightEndpoint (fun j : Fin m => eventL (label j))
  have hRsGap (k : Fin (m+1)) : Rs ⟨k.val,by omega⟩ = gapLeftFamily k := by
    refine Fin.cases ?_ ?_ k
    · exact hblock0 _ _ _ _
    · intro j
      exact hblockEvent _ _ _ _ j
  have hLsGap (k : Fin (m+1)) : Ls ⟨k.val+1,by omega⟩ = gapRightFamily k := by
    refine Fin.lastCases ?_ ?_ k
    · dsimp only [gapRightFamily]
      rw [Fin.lastCases_last]
      exact hblockLast _ _ _ _
    · intro j
      dsimp only [gapRightFamily]
      rw [Fin.lastCases_castSucc]
      exact hblockEvent _ _ _ _ j
  have hGapLeftData (k : Fin (m+1)) :
      (∀ τ, (gapLeftFamily k τ).val ∈ Eguide.source) ∧
      Eguide (gapLeftFamily k 0).val 1 = 0 ∧
      ∀ τ : Interval, 0 < τ.val → τ.val < ε →
        (∀ i : Option ι, gapLeftFamily k τ ∉ range (f i)) ∧
        0 < exteriorSign*Eguide (gapLeftFamily k τ).val 1 := by
    refine Fin.cases ?_ ?_ k
    · refine ⟨hLeftSource,hsecondZero _ hLeftZeroSide.1,?_⟩
      intro τ hτ hτε
      exact ⟨(hCornerL τ hτ).2.2.2.2.2.2.1,
        hLeftSign τ hτ (hτε.trans_le (min_le_left _ _))⟩
    · intro j
      refine ⟨fun τ => (hEventSource (label j) τ).2,hEventRy0 (label j),?_⟩
      intro τ hτ hτε
      exact ⟨fun i => (hEventPositive (label j) τ hτ).2.2.1 i |>.2,
        (hEventSign (label j) τ hτ).2⟩
  have hGapRightData (k : Fin (m+1)) :
      (∀ τ, (gapRightFamily k τ).val ∈ Eguide.source) ∧
      Eguide (gapRightFamily k 0).val 1 = 0 ∧
      ∀ τ : Interval, 0 < τ.val → τ.val < ε →
        (∀ i : Option ι, gapRightFamily k τ ∉ range (f i)) ∧
        0 < exteriorSign*Eguide (gapRightFamily k τ).val 1 := by
    refine Fin.lastCases ?_ ?_ k
    · dsimp only [gapRightFamily]
      rw [Fin.lastCases_last]
      refine ⟨hRightSource,hsecondZero _ hRightZeroSide.1,?_⟩
      intro τ hτ hτε
      exact ⟨(hCornerR τ hτ).2.2.2.2.2.2.1,
        hRightSign τ hτ (hτε.trans_le (min_le_right _ _))⟩
    · intro j
      dsimp only [gapRightFamily]
      rw [Fin.lastCases_castSucc]
      refine ⟨fun τ => (hEventSource (label j) τ).1,hEventLy0 (label j),?_⟩
      intro τ hτ hτε
      exact ⟨fun i => (hEventPositive (label j) τ hτ).2.2.1 i |>.1,
        (hEventSign (label j) τ hτ).1⟩
  let gapL : Fin (m+1) → ℝ := fun k => Eguide (gapLeftFamily k 0).val 0
  let gapR : Fin (m+1) → ℝ := fun k => Eguide (gapRightFamily k 0).val 0
  have hgapL0 : gapL 0 = Eguide (leftEndpoint 0).val 0 := rfl
  have hgapLSucc (j : Fin m) : gapL j.succ = eventB (label j) := hEventR0 (label j)
  have hgapRLast : gapR (Fin.last m) = Eguide (rightEndpoint 0).val 0 := by
    dsimp only [gapR,gapRightFamily]
    rw [Fin.lastCases_last]
  have hgapRCast (j : Fin m) : gapR j.castSucc = eventA (label j) := by
    dsimp only [gapR,gapRightFamily]
    rw [Fin.lastCases_castSucc]
    exact hEventL0 (label j)
  have hGapBounds (k : Fin (m+1)) : -1 < gapL k ∧ gapR k < 1 := by
    constructor
    · refine Fin.cases ?_ ?_ k
      · exact hleftAxisBounds.1
      · intro j
        rw [hgapLSucc]
        exact (hPbounds (label j)).1.trans (hEventB (label j))
    · refine Fin.lastCases ?_ ?_ k
      · rw [hgapRLast]
        exact hrightAxisBounds.2
      · intro j
        rw [hgapRCast]
        exact (hEventA (label j)).trans (hPbounds (label j)).2
  have hLabelLE (j k : Fin m) (hjk : j ≤ k) :
      Eguide (label j).val.val 0 ≤ Eguide (label k).val.val 0 := by
    rcases lt_or_eq_of_le hjk with h | rfl
    · exact (hlabelOrder j k h).le
    · exact le_rfl
  have hBeforeGap (k : Fin (m+1)) (j : Fin m) (hjk : j.val < k.val) :
      Eguide (label j).val.val 0 < gapL k := by
    revert hjk
    refine Fin.cases ?_ ?_ k
    · intro hjk
      exact (Nat.not_lt_zero _ hjk).elim
    · intro i hjk
      rw [hgapLSucc]
      exact (hLabelLE j i (by change j.val ≤ i.val; simpa only [Fin.val_succ] using Nat.le_of_lt_succ hjk)).trans_lt
        (hEventB (label i))
  have hAfterGap (k : Fin (m+1)) (j : Fin m) (hkj : k.val ≤ j.val) :
      gapR k < Eguide (label j).val.val 0 := by
    revert hkj
    refine Fin.lastCases ?_ ?_ k
    · intro hkj
      exact (not_le_of_gt j.isLt hkj).elim
    · intro i hkj
      rw [hgapRCast]
      exact (hEventA (label i)).trans_le (hLabelLE i j hkj)
  have hGapNoContacts (k : Fin (m+1)) : Disjoint (Icc (gapL k) (gapR k)) (contactCoordinates : Set ℝ) := by
    apply disjoint_left.mpr
    intro ξ hξ hc
    obtain ⟨p,hp,hpc⟩ := Finset.mem_image.mp hc
    obtain ⟨j,rfl⟩ := label.surjective p
    by_cases hjk : j.val < k.val
    · have hh := hBeforeGap k j hjk
      rw [hpc] at hh
      exact not_le_of_gt hh hξ.1
    · have hh := hAfterGap k j (le_of_not_gt hjk)
      rw [hpc] at hh
      exact not_le_of_gt hh hξ.2
  have hGapOrder (k : Fin (m+1)) : gapL k < gapR k := by
    refine Fin.cases ?_ ?_ k
    · rw [hgapL0]
      by_cases hm : 0 < m
      · let j : Fin m := ⟨0,hm⟩
        have he : (0 : Fin (m+1)) = j.castSucc := Fin.ext rfl
        rw [he,hgapRCast]
        exact hleftAxisBounds.2.trans (hedgeA (label j))
      · have he : (0 : Fin (m+1)) = Fin.last m := Fin.ext (by dsimp; omega)
        rw [he,hgapRLast]
        exact hleftAxisBounds.2.trans (hedgeLR.trans hrightAxisBounds.1)
    · intro j
      rw [hgapLSucc]
      by_cases hj : j.val+1 < m
      · let next : Fin m := ⟨j.val+1,hj⟩
        have he : j.succ = next.castSucc := Fin.ext rfl
        rw [he,hgapRCast]
        exact hEventIntervalsOrdered (label j) (label next)
          (hlabelOrder j next (by change j.val < j.val+1; omega))
      · have he : j.succ = Fin.last m := Fin.ext (by dsimp; omega)
        rw [he,hgapRLast]
        exact (hedgeB (label j)).trans hrightAxisBounds.1
  have hEnlargeGap (a b : ℝ) (ha : -1 < a) (hb : b < 1) (hab : a < b)
      (hfree : Disjoint (Icc a b) (contactCoordinates : Set ℝ)) :
      ∃ A B : ℝ, A < a ∧ b < B ∧ ∀ ξ ∈ Icc A B,
        (-1 < ξ ∧ ξ < 1) ∧ ξ ∉ contactCoordinates := by
    let O : Set ℝ := Ioo (-1) 1 \ (contactCoordinates : Set ℝ)
    have hO : IsOpen O := isOpen_Ioo.sdiff contactCoordinates.finite_toSet.isClosed
    have haO : a ∈ O := ⟨⟨ha,hab.trans hb⟩,fun haC => disjoint_left.mp hfree ⟨le_rfl,hab.le⟩ haC⟩
    have hbO : b ∈ O := ⟨⟨ha.trans hab,hb⟩,fun hbC => disjoint_left.mp hfree ⟨hab.le,le_rfl⟩ hbC⟩
    obtain ⟨ra,hra,hraO⟩ := Metric.isOpen_iff.mp hO a haO
    obtain ⟨rb,hrb,hrbO⟩ := Metric.isOpen_iff.mp hO b hbO
    refine ⟨a-ra/2,b+rb/2,by linarith,by linarith,?_⟩
    intro ξ hξ
    by_cases hξa : ξ < a
    · apply hraO
      rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (by linarith)]
      linarith [hξ.1]
    · by_cases hbξ : b < ξ
      · apply hrbO
        rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (by linarith)]
        linarith [hξ.2]
      · exact ⟨⟨ha.trans_le (le_of_not_gt hξa),(le_of_not_gt hbξ).trans_lt hb⟩,
          fun hc => disjoint_left.mp hfree ⟨le_of_not_gt hξa,le_of_not_gt hbξ⟩ hc⟩
  choose gapA gapB hGapA hGapB hGapAxisClear using
    fun k => hEnlargeGap (gapL k) (gapR k) (hGapBounds k).1 (hGapBounds k).2
      (hGapOrder k) (hGapNoContacts k)
  let small : Interval := ⟨min ε 1 / 2,by
    constructor
    · exact (half_pos (lt_min hε zero_lt_one)).le
    · have hh := min_le_right ε (1 : ℝ)
      linarith⟩
  have hsmallPos : 0 < small.val := half_pos (lt_min hε zero_lt_one)
  have hsmallBound : small.val < ε := by
    dsimp only [small]
    have hh := min_le_left ε (1 : ℝ)
    have hp := lt_min hε (zero_lt_one : (0 : ℝ) < 1)
    linarith
  have hAffineContinuous : Continuous (intervalAffine 0 small) := by
    apply Continuous.subtype_mk
    fun_prop
  let rescaledL (k : Fin (m+1)) : C(Interval,↥{y : ↥F | y.val ∈ Eguide.source}) :=
    ⟨fun τ => ⟨gapLeftFamily k (intervalAffine 0 small τ),(hGapLeftData k).1 _⟩,
      ((gapLeftFamily k).continuous.comp hAffineContinuous).subtype_mk _⟩
  let rescaledR (k : Fin (m+1)) : C(Interval,↥{y : ↥F | y.val ∈ Eguide.source}) :=
    ⟨fun τ => ⟨gapRightFamily k (intervalAffine 0 small τ),(hGapRightData k).1 _⟩,
      ((gapRightFamily k).continuous.comp hAffineContinuous).subtype_mk _⟩
  refine ⟨{
    l := newL
    r := newR
    cuts := hNewCuts
    old_in_disk := hNewOld.trans holdDisk
    attachment_clear := ?_
    m := m
    label := label
    label_order := hlabelOrder
    corners := hcorners
    xL := f (some v) taL
    xR := f (some v) taR
    orientation := hNewOrientation
    ε := ε
    epsilon_pos := hε
    L := Ls
    R := Rs
    piece := pieces
    piece_embedded := fun τ hτ _ k => (hGeometry τ hτ k).1
    piece_in_guide := fun τ hτ _ k => (hGeometry τ hτ k).2.1
    piece_endpoints := fun τ hτ _ k => (hGeometry τ hτ k).2.2.1
    attachments := ?_
    guide_clear := fun τ hτ _ k => (hGeometry τ hτ k).2.2.2.1
    selected_meet := fun τ hτ _ => hSelectedMeet τ hτ
    site := sites
    site_left := hblock0 _ _ _ _
    site_right := hblockLast _ _ _ _
    site_event := fun k => hblockEvent _ _ _ _ k
    piece_contacts_finite := fun τ hτ _ k i hi => ((hGeometry τ hτ k).2.2.2.2 i hi).1
    piece_contacts_bound := fun τ hτ _ k i hi _ => ((hGeometry τ hτ k).2.2.2.2 i hi).2
    internal_source := ?_
    internal_clear := ?_
    gapA := gapA
    gapL := gapL
    gapR := gapR
    gapB := gapB
    gap_order := fun k => ⟨hGapA k,hGapOrder k,hGapB k⟩
    gap_zero := ?_
    gap_axis := fun k ξ hξ => hContactFreeAxis ξ (hGapAxisClear k ξ hξ).1 (hGapAxisClear k ξ hξ).2
    σ := exteriorSign
    sign_unit := hexteriorSign
    internal_sign := ?_
    small := small
    small_pos := hsmallPos
    small_bound := hsmallBound
    rescaledL := rescaledL
    rescaledR := rescaledR
    rescale_eq := ?_ }⟩
  · intro i hi
    apply disjoint_left.mpr
    intro y hy hyi
    exact disjoint_left.mp (hattachmentClear i hi) ⟨hNewOld hy.1,hy.2⟩ hyi
  · intro τ hτ hτε
    simp only [Ls,Rs,hblock0,hblockLast,ContinuousMap.const_apply,and_self]
  · intro k τ
    rw [hRsGap,hLsGap]
    exact ⟨(hGapLeftData k).1 τ,(hGapRightData k).1 τ⟩
  · intro τ hτ hτε k i
    rw [hRsGap,hLsGap]
    exact ⟨((hGapLeftData k).2.2 τ hτ hτε).1 i,((hGapRightData k).2.2 τ hτ hτε).1 i⟩
  · intro k
    rw [hRsGap,hLsGap]
    constructor
    · ext i
      fin_cases i
      · rfl
      · exact (hGapLeftData k).2.1
    · ext i
      fin_cases i
      · rfl
      · exact (hGapRightData k).2.1
  · intro τ hτ hτε k
    rw [hRsGap,hLsGap]
    exact ⟨((hGapLeftData k).2.2 τ hτ hτε).2,((hGapRightData k).2.2 τ hτ hτε).2⟩
  · intro k τ
    rw [hRsGap,hLsGap]
    exact ⟨rfl,rfl⟩
