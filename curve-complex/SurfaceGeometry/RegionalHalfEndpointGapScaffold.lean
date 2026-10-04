import RegionalWeightedMovieDefinitions
import RegionalFrontierLocalBasis

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- M2-gap: a relative-open terminal B gap on the supplied boundary side,
with every other family endpoint and both observer endpoints forbidden. -/
theorem regional_half_disk_forbidden_endpoint_gap
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
        Nonempty (BoundaryEndpointGap {y : ↥F | y.val ∈ boundaryCircle} V
          (forbiddenEndpoints (fun i => (r i).val.val) α.val.val v) d.boundarySide) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro ι instι r α hinvariant hcross v w hvw d V hV hdV hclosure
  let forbidden := forbiddenEndpoints (fun i => (r i).val.val) α.val.val v
  have hforbidden : forbidden.Finite := by
    apply ((Set.finite_range (fun j => (r j).val.val 0)).union
      ((Set.finite_range (fun j => (r j).val.val 1)).union
        ((Set.finite_singleton (α.val.val 0)).union (Set.finite_singleton (α.val.val 1))))).subset
    intro p hp
    rcases hp with ⟨j, hj, h0 | h1⟩ | h0 | h1
    · exact Or.inl ⟨j, h0.symm⟩
    · exact Or.inr (Or.inl ⟨j, h1.symm⟩)
    · exact Or.inr (Or.inr (Or.inl h0))
    · exact Or.inr (Or.inr (Or.inr h1))
  let bad : Set Interval := (d.boundarySide ⁻¹' forbidden) ∩ Iio 1
  have hbad : bad.Finite :=
    (hforbidden.preimage d.boundary_embedded.injective.injOn).inter_of_left _
  let cut : Interval := hbad.toFinset.sup id
  have hcut : cut < 1 := by
    apply (Finset.sup_lt_iff (show (⊥ : Interval) < 1 by change (0 : ℝ) < 1; norm_num)).2
    intro t ht
    exact (hbad.mem_toFinset.mp ht).2
  have hgapavoid : Disjoint (d.boundarySide '' Ioo cut 1) forbidden := by
    apply Set.disjoint_left.mpr
    rintro p ⟨t, ht, rfl⟩ hp
    have hmem : t ∈ hbad.toFinset := hbad.mem_toFinset.mpr ⟨hp, ht.2⟩
    exact (not_le_of_gt ht.1) (Finset.le_sup (f := id) hmem)
  have hgapV : d.boundarySide '' Ioo cut 1 ⊆ V := by
    rintro p ⟨t, ht, rfl⟩
    apply hdV
    obtain ⟨z, hz, he⟩ := d.boundary_image.symm ▸
      (show d.boundarySide t ∈ range d.first ∪ range d.second ∪ range d.boundarySide from
        Or.inr (mem_range_self t))
    exact ⟨z, he⟩
  obtain ⟨baseCurve, hbaseCurve⟩ := RegionalEmbeddedFamily.contact_chart_sphere_is_curve
    S (chartAt (EuclideanSpace ℝ (Fin 2)) x)
    ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R hR htarget
  let suffix : C(Interval,S) :=
    ⟨fun t => (d.boundarySide (CurveComplex.BranchedDoubleCover.intervalAffine cut 1 t)).val,
      continuous_subtype_val.comp (d.boundarySide.continuous.comp (by
        unfold CurveComplex.BranchedDoubleCover.intervalAffine
        fun_prop))⟩
  have hsuffix : Topology.IsEmbedding suffix := by
    apply (suffix.continuous.isClosedEmbedding ?_).isEmbedding
    intro t u he
    have hp := congrArg Subtype.val (d.boundary_embedded.injective (Subtype.ext he))
    change (1-(t:ℝ))*(cut:ℝ)+(t:ℝ)*1 = (1-(u:ℝ))*(cut:ℝ)+(u:ℝ)*1 at hp
    apply Subtype.ext
    have hc : (cut:ℝ) < 1 := hcut
    nlinarith
  have hsuffixrange : range suffix ⊆ baseCurve.image := by
    rintro p ⟨t, rfl⟩
    rw [hbaseCurve]
    exact d.boundary_in_B _
  have hsuffixopen := CurveComplex.LocalSurgery.embedded_curve_subarc_interior_isOpen
    baseCurve suffix hsuffix hsuffixrange
  have hsuffiximage : suffix '' Ioo (0 : Interval) 1 =
      Subtype.val '' (d.boundarySide '' Ioo cut 1) := by
    ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨d.boundarySide (CurveComplex.BranchedDoubleCover.intervalAffine cut 1 t), ?_, rfl⟩
      refine ⟨CurveComplex.BranchedDoubleCover.intervalAffine cut 1 t, ?_, rfl⟩
      constructor
      · change (cut:ℝ) < (1-(t:ℝ))*(cut:ℝ)+(t:ℝ)*1
        have ht0 : (0:ℝ) < t := ht.1
        have hc : (cut:ℝ) < 1 := hcut
        nlinarith
      · change (1-(t:ℝ))*(cut:ℝ)+(t:ℝ)*1 < 1
        have ht1 : (t:ℝ) < 1 := ht.2
        have hc : (cut:ℝ) < 1 := hcut
        nlinarith
    · rintro ⟨y, ⟨t, ht, rfl⟩, rfl⟩
      have hc : (cut:ℝ) < 1 := hcut
      have ht0 : (cut:ℝ) < t := ht.1
      have ht1 : (t:ℝ) < 1 := ht.2
      let u : Interval := ⟨((t:ℝ)-(cut:ℝ))/(1-(cut:ℝ)), by
        constructor
        · exact div_nonneg (by linarith) (by linarith)
        · apply (div_le_one (by linarith)).2
          linarith⟩
      have hu : u ∈ Ioo (0 : Interval) 1 := by
        constructor
        · change 0 < ((t:ℝ)-(cut:ℝ))/(1-(cut:ℝ))
          exact div_pos (by linarith) (by linarith)
        · change ((t:ℝ)-(cut:ℝ))/(1-(cut:ℝ)) < 1
          apply (div_lt_one (by linarith)).2
          linarith
      refine ⟨u, hu, ?_⟩
      change (d.boundarySide (CurveComplex.BranchedDoubleCover.intervalAffine cut 1 u)).val = (d.boundarySide t).val
      congr 2
      apply Subtype.ext
      change (1-(((t:ℝ)-(cut:ℝ))/(1-(cut:ℝ))))*(cut:ℝ)+(((t:ℝ)-(cut:ℝ))/(1-(cut:ℝ)))*1 = t
      field_simp [show 1-(cut:ℝ) ≠ 0 from ne_of_gt (sub_pos.mpr hc)]
      <;> ring
  let boundaryToCurve : {y : ↥F | y.val ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R} → baseCurve.image :=
    fun y => ⟨y.val.val, hbaseCurve.symm ▸ y.property⟩
  have hboundaryToCurve : Continuous boundaryToCurve :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hgapopen := hsuffixopen.preimage hboundaryToCurve
  have hgapopen' : IsOpen {y : ↥({y : ↥F | y.val ∈
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}) |
      y.val ∈ d.boundarySide '' Ioo cut 1} := by
    convert hgapopen using 1
    ext y
    change y.val ∈ d.boundarySide '' Ioo cut 1 ↔
      (boundaryToCurve y).val ∈ suffix '' Ioo (0 : Interval) 1
    dsimp only [boundaryToCurve]
    rw [hsuffiximage]
    constructor
    · intro hy
      exact ⟨y.val, hy, rfl⟩
    · rintro ⟨z, hz, he⟩
      exact (Subtype.ext he : z = y.val) ▸ hz
  let chosen : Interval := ⟨((cut:ℝ)+1)/2, by
    constructor
    · linarith [cut.property.1]
    · linarith [cut.property.2]⟩
  have hchosen : chosen ∈ Ioo cut 1 := by
    have hc : (cut:ℝ) < 1 := hcut
    constructor
    · change (cut:ℝ) < ((cut:ℝ)+1)/2
      linarith
    · change ((cut:ℝ)+1)/2 < 1
      linarith
  exact ⟨⟨cut, hcut, hgapopen', hgapV, hgapavoid, chosen, hchosen⟩⟩
