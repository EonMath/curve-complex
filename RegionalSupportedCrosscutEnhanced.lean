import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.RegionalSupportedRestriction
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalFiniteFaceTransport

open CurveComplex Set Topology

/- The canonical square crosscut move gives an actual ambient isotopy of the
   same region, with its full support and frontier behavior retained. -/
theorem regional_square_crosscut_supported_isotopy
    (S : Type) [TopologicalSpace S]
    [ChartedSpace Schoenflies.Plane S] [ClosedSurface S]
    (F : Set S) (E : OpenPartialHomeomorph S Schoenflies.Plane)
    (hSquare : Schoenflies.Plane.closedSquare 0 1 ⊆ E.target)
    (A B : Set Schoenflies.Plane) (u v : Schoenflies.Plane)
    (hA : Schoenflies.IsArcBetween A u v)
    (hB : Schoenflies.IsArcBetween B u v)
    (hu : u ∈ Schoenflies.modelCurve)
    (hv : v ∈ Schoenflies.modelCurve)
    (hAi : A \ {u,v} ⊆ Schoenflies.Plane.openSquare 0 1)
    (hBi : B \ {u,v} ⊆ Schoenflies.Plane.openSquare 0 1)
    (hinside : {y : S | y ∈ E.source ∧
      E y ∈ Schoenflies.Plane.openSquare 0 1} ⊆ interior F) :
    ∃ K : AmbientIsotopy ↥F,
      (∀ t y, y.val ∉ {z : S | z ∈ E.source ∧
        E z ∈ Schoenflies.Plane.openSquare 0 1} → K.map (t,y) = y) ∧
      (∀ t y, y.val ∈ frontier F → K.map (t,y) = y) ∧
      ∃ H : AmbientIsotopy S,
        (∀ t y, (K.map (t,y)).val = H.map (t,y.val)) ∧
        H.finalMap '' {z : S | z ∈ E.source ∧ E z ∈ A} =
          {z : S | z ∈ E.source ∧ E z ∈ B} := by
  let D : Set S := {z | z ∈ E.source ∧
    E z ∈ Schoenflies.Plane.openSquare 0 1}
  have hPull (C : Set Schoenflies.Plane) :
      {z : S | ∃ w : E.source, w.val = z ∧
        (E.toHomeomorphSourceTarget w : Schoenflies.Plane) ∈ C} =
      {z : S | z ∈ E.source ∧ E z ∈ C} := by
    ext z
    constructor
    · rintro ⟨w, rfl, hw⟩
      exact ⟨w.property, hw⟩
    · rintro ⟨hz,hc⟩
      exact ⟨⟨z,hz⟩,rfl,hc⟩
  obtain ⟨H,hmove,hfix⟩ :=
    position_crosscut_surface_square_support S E.source E.target E.open_source
      E.toHomeomorphSourceTarget hSquare A B u v hA hB hu hv hAi hBi
  rw [hPull A, hPull B] at hmove
  rw [hPull (Schoenflies.Plane.openSquare 0 1)] at hfix
  obtain ⟨K,hK,hKfix,hKfront⟩ :=
    regional_ambient_isotopy_restricts_with_support F D hinside H hfix
  exact ⟨K,hKfix,hKfront,H,hK,hmove⟩

#print axioms regional_square_crosscut_supported_isotopy

/- Lift the literal surface trace replacement to the subtype region. -/
theorem regional_lifted_crosscut_trace_transport
    {S : Type} [TopologicalSpace S] (F A B : Set S)
    (hAF : A ⊆ F)
    (H : AmbientIsotopy S) (K : AmbientIsotopy ↥F)
    (hK : ∀ t y, (K.map (t,y)).val = H.map (t,y.val))
    (hmove : H.finalMap '' A = B) :
    K.finalMap '' {y : ↥F | y.val ∈ A} =
      {y : ↥F | y.val ∈ B} := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have hy : y.val ∈ H.finalMap '' A := by
      refine ⟨x.val, hx, ?_⟩
      exact (hK 1 x).symm.trans (congrArg Subtype.val hxy)
    exact hmove ▸ hy
  · intro hy
    have hyB : y.val ∈ H.finalMap '' A := hmove.symm ▸ hy
    obtain ⟨x,hx,hxy⟩ := hyB
    let xf : ↥F := ⟨x,hAF hx⟩
    refine ⟨xf,hx,?_⟩
    apply Subtype.ext
    exact (hK 1 xf).trans hxy

#print axioms regional_lifted_crosscut_trace_transport

/- A boundary-fixed homeomorphism preserves the literal disk-cap obstruction
   used to define an essential proper arc. -/
private theorem regional_boundary_fixed_homeomorph_preserves_essential_arc
    {X : Type} [TopologicalSpace X] (B : Set X)
    (a : C(Interval,X)) (h : X ≃ₜ X)
    (hB : ∀ y, y ∈ B → h y = y)
    (ha : ∀ k : C(Interval,X), Topology.IsEmbedding k →
      (∀ t, k t ∈ B) →
      ∀ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,X),
        Topology.IsEmbedding d →
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ≠
          Set.range a ∪ Set.range k) :
    let ah : C(Interval,X) :=
      ⟨fun t => h (a t), h.continuous.comp a.continuous⟩
    ∀ k : C(Interval,X), Topology.IsEmbedding k →
      (∀ t, k t ∈ B) →
      ∀ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,X),
        Topology.IsEmbedding d →
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ≠
          Set.range ah ∪ Set.range k := by
  dsimp only
  intro k hk hkB d hd hboundary
  let ki : C(Interval,X) :=
    ⟨fun t => h.symm (k t), h.symm.continuous.comp k.continuous⟩
  let di : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,X) :=
    ⟨fun z => h.symm (d z), h.symm.continuous.comp d.continuous⟩
  have hki : Topology.IsEmbedding ki := h.symm.isEmbedding.comp hk
  have hdi : Topology.IsEmbedding di := h.symm.isEmbedding.comp hd
  have hkiB : ∀ t, ki t ∈ B := by
    intro t
    have he : h.symm (k t) = k t := by
      calc
        h.symm (k t) = h.symm (h (k t)) :=
          congrArg h.symm (hB _ (hkB t)).symm
        _ = k t := h.symm_apply_apply _
    change h.symm (k t) ∈ B
    rw [he]
    exact hkB t
  apply ha ki hki hkiB di hdi
  change (h.symm ∘ d) '' _ = Set.range a ∪ Set.range ki
  rw [Set.image_comp, hboundary, Set.image_union,
    ← Set.range_comp, ← Set.range_comp]
  change Set.range (fun t => h.symm (h (a t))) ∪
    Set.range (fun t => h.symm (k t)) = Set.range a ∪ Set.range ki
  simp only [Homeomorph.symm_apply_apply]
  rfl

#print axioms regional_boundary_fixed_homeomorph_preserves_essential_arc

/- Full supported version of the original regional crosscut replacement. -/
theorem regional_proper_crosscut_replacement_with_support
    {S : Type} [TopologicalSpace S]
    [ChartedSpace Schoenflies.Plane S] [ClosedSurface S]
    (F B0 : Set S) (hBfront : B0 ⊆ frontier F)
    (a : C(Interval,↥F)) (ha : Topology.IsEmbedding a)
    (ha0 : (a 0).val ∈ B0) (ha1 : (a 1).val ∈ B0)
    (haI : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
    (haessential : ∀ k : C(Interval,↥F), Topology.IsEmbedding k →
      (∀ t, (k t).val ∈ B0) →
      ∀ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding d →
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ≠
          Set.range a ∪ Set.range k)
    (E : OpenPartialHomeomorph S Schoenflies.Plane)
    (hSquare : Schoenflies.Plane.closedSquare 0 1 ⊆ E.target)
    (A B : Set Schoenflies.Plane) (u v : Schoenflies.Plane)
    (hA : Schoenflies.IsArcBetween A u v)
    (hB : Schoenflies.IsArcBetween B u v)
    (hu : u ∈ Schoenflies.modelCurve) (hv : v ∈ Schoenflies.modelCurve)
    (hAi : A \ {u,v} ⊆ Schoenflies.Plane.openSquare 0 1)
    (hBi : B \ {u,v} ⊆ Schoenflies.Plane.openSquare 0 1)
    (hinside : {y : S | y ∈ E.source ∧ E y ∈ Schoenflies.Plane.openSquare 0 1} ⊆
      interior F)
    (htrace : {y : S | y ∈ E.source ∧ E y ∈ Schoenflies.Plane.closedSquare 0 1} ∩
      Set.range (fun t => (a t).val) =
      {y : S | y ∈ E.source ∧ E y ∈ A}) :
    ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
      b 0 = a 0 ∧ b 1 = a 1 ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
      (∀ k : C(Interval,↥F), Topology.IsEmbedding k →
        (∀ t, (k t).val ∈ B0) →
        ∀ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d →
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ≠
            Set.range b ∪ Set.range k) ∧
      Set.range (fun t => (b t).val) =
        (Set.range (fun t => (a t).val) \ {y : S | y ∈ E.source ∧ E y ∈ A}) ∪
          {y : S | y ∈ E.source ∧ E y ∈ B} ∧
      ∃ K : AmbientIsotopy ↥F,
        (∀ t y, y.val ∈ frontier F → K.map (t,y) = y) ∧
        (∀ t y, y.val ∉ {z : S | z ∈ E.source ∧
          E z ∈ Schoenflies.Plane.openSquare 0 1} → K.map (t,y) = y) ∧
        K.finalMap '' Set.range a = Set.range b := by
  let Ap : Set S := {y | y ∈ E.source ∧ E y ∈ A}
  let Bp : Set S := {y | y ∈ E.source ∧ E y ∈ B}
  let Dp : Set S := {y | y ∈ E.source ∧
    E y ∈ Schoenflies.Plane.openSquare 0 1}
  let as : C(Interval,S) :=
    ⟨fun t => (a t).val, continuous_subtype_val.comp a.continuous⟩
  obtain ⟨K,hKfix,hKfront,H,hK,hmove⟩ :=
    regional_square_crosscut_supported_isotopy S F E hSquare A B u v
      hA hB hu hv hAi hBi hinside
  obtain ⟨h,hh⟩ := K.homeomorphism_at 1
  let b : C(Interval,↥F) :=
    ⟨fun t => h (a t), h.continuous.comp a.continuous⟩
  have hb : Topology.IsEmbedding b := h.isEmbedding.comp ha
  have hb0 : b 0 = a 0 :=
    (hh (a 0)).trans (hKfront 1 (a 0) (hBfront ha0))
  have hb1 : b 1 = a 1 :=
    (hh (a 1)).trans (hKfront 1 (a 1) (hBfront ha1))
  have hbI : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (b t).val ∉ frontier F := by
    intro t ht hbt
    have hefix : h (b t) = b t :=
      (hh (b t)).trans (hKfront 1 (b t) hbt)
    have he : b t = a t := h.injective hefix
    exact haI t ht (he ▸ hbt)
  have hbessential := regional_boundary_fixed_homeomorph_preserves_essential_arc
    {y : ↥F | y.val ∈ B0} a h
    (fun y hy => (hh y).trans (hKfront 1 y (hBfront hy))) haessential
  have hAp : Ap ⊆ Set.range as := by
    intro y hy
    have hz : y ∈ {z : S | z ∈ E.source ∧
        E z ∈ Schoenflies.Plane.closedSquare 0 1} ∩
        Set.range as := htrace.symm ▸ hy
    exact hz.2
  have hDtrace : Dp ∩ Set.range as ⊆ Ap := by
    intro y hy
    change y ∈ {z : S | z ∈ E.source ∧ E z ∈ A}
    rw [← htrace]
    exact ⟨⟨hy.1.1,
      Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hy.1.2⟩,hy.2⟩
  have hrestfix (y : S) (hy : y ∈ Set.range as \ Ap) :
      H.finalMap y = y := by
    have hyF : y ∈ F := by
      obtain ⟨t,ht⟩ := hy.1
      exact ht ▸ (a t).property
    let yf : ↥F := ⟨y,hyF⟩
    have hfixY : K.map (1,yf) = yf :=
      hKfix 1 yf (fun hz => hy.2 (hDtrace ⟨hz,hy.1⟩))
    exact (hK 1 yf).symm.trans (congrArg Subtype.val hfixY)
  have hrest : H.finalMap '' (Set.range as \ Ap) =
      Set.range as \ Ap := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      simpa only [hrestfix z hz] using hz
    · intro hy
      exact ⟨y,hy,hrestfix y hy⟩
  have hbrange : Set.range (fun t => (b t).val) =
      H.finalMap '' Set.range as := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext t
    exact (congrArg Subtype.val (hh (a t))).trans (hK 1 (a t))
  have hrange : Set.range (fun t => (b t).val) =
      (Set.range as \ Ap) ∪ Bp := by
    rw [hbrange]
    calc
      H.finalMap '' Set.range as =
          H.finalMap '' ((Set.range as \ Ap) ∪ Ap) :=
        congrArg (fun U => H.finalMap '' U)
          (Set.sdiff_union_of_subset hAp).symm
      _ = (Set.range as \ Ap) ∪ Bp := by
        rw [Set.image_union,hrest,hmove]
  have hKmove : K.finalMap '' Set.range a = Set.range b := by
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext t
    exact (hh (a t)).symm
  exact ⟨b,hb,hb0,hb1,hbI,hbessential,hrange,
    K,hKfront,hKfix,hKmove⟩

#print axioms regional_proper_crosscut_replacement_with_support

/- One actual chart crosscut surgery on a protected intrinsic face, with the
   square chosen to avoid the other simultaneous representatives. -/
theorem regional_intrinsic_face_crosscut_surgery
    {S : Type} [TopologicalSpace S]
    [ChartedSpace Schoenflies.Plane S] [ClosedSurface S]
    (F B0 : Set S) (hBfront : B0 ⊆ frontier F) :
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ B0 ∧
        (a ⟨1,by norm_num⟩).val ∈ B0 ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ B0) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ B0} =
          {y | y.val ∈ B0}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    ∀ (τ : Finset (Quot intrinsicArcRel))
      (a : ↥τ → IntrinsicEssentialArc) (k : ↥τ),
      (∀ w, Quot.mk intrinsicArcRel (a w) = w.val) →
      (∀ w z, w ≠ z →
        Disjoint (Set.range (a w).val.val) (Set.range (a z).val.val)) →
      ∀ (E : OpenPartialHomeomorph S Schoenflies.Plane)
        (_hSquare : Schoenflies.Plane.closedSquare 0 1 ⊆ E.target)
        (A B : Set Schoenflies.Plane) (u v : Schoenflies.Plane),
      Schoenflies.IsArcBetween A u v →
      Schoenflies.IsArcBetween B u v →
      u ∈ Schoenflies.modelCurve → v ∈ Schoenflies.modelCurve →
      A \ {u,v} ⊆ Schoenflies.Plane.openSquare 0 1 →
      B \ {u,v} ⊆ Schoenflies.Plane.openSquare 0 1 →
      {y : S | y ∈ E.source ∧ E y ∈ Schoenflies.Plane.openSquare 0 1} ⊆
        interior F →
      {y : S | y ∈ E.source ∧ E y ∈ Schoenflies.Plane.closedSquare 0 1} ∩
        Set.range (fun t => ((a k).val.val t).val) =
          {y : S | y ∈ E.source ∧ E y ∈ A} →
      (∀ w, w ≠ k → Disjoint
        {y : ↥F | y.val ∈ {z : S | z ∈ E.source ∧
          E z ∈ Schoenflies.Plane.openSquare 0 1}}
        (Set.range (a w).val.val)) →
      ∃ r : IntrinsicEssentialArc,
        Set.range (fun t => (r.val.val t).val) =
          (Set.range (fun t => ((a k).val.val t).val) \
            {y : S | y ∈ E.source ∧ E y ∈ A}) ∪
            {y : S | y ∈ E.source ∧ E y ∈ B} ∧
        ∃ b : ↥τ → IntrinsicEssentialArc,
          (∀ w, Quot.mk intrinsicArcRel (b w) = w.val) ∧
          (∀ w z, w ≠ z →
            Disjoint (Set.range (b w).val.val) (Set.range (b z).val.val)) ∧
          b k = r := by
  classical
  intro RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel τ a k hclass hdisjoint E hSquare A B u v hA hB
    hu hv hAi hBi hinside htrace havoid
  have hessential : ∀ c : C(Interval,↥F), Topology.IsEmbedding c →
      (∀ t, (c t).val ∈ B0) →
      ∀ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding d →
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ≠
          Set.range (a k).val.val ∪ Set.range c := by
    intro c hc hcB d hd he
    exact (a k).property ⟨c,hc,hcB,d,hd,he⟩
  obtain ⟨rmap,hr,hr0,hr1,hrI,hress,hrange,K,hKfront,hKfix,hKmove⟩ :=
    regional_proper_crosscut_replacement_with_support F B0 hBfront
      (a k).val.val (a k).val.property.1 (a k).val.property.2.1
      (a k).val.property.2.2.1 (a k).val.property.2.2.2
      hessential E hSquare A B u v hA hB hu hv hAi hBi hinside htrace
  let rp : RegionProperArc :=
    ⟨rmap,hr,hr0.symm ▸ (a k).val.property.2.1,
      hr1.symm ▸ (a k).val.property.2.2.1,hrI⟩
  let r : IntrinsicEssentialArc := ⟨rp,by
    rintro ⟨c,hc,hcB,d,hd,he⟩
    exact hress c hc hcB d hd he⟩
  have hpres (P : Set S) (hP : P ⊆ frontier F) (t : Interval) :
      (fun y => K.map (t,y)) '' {y : ↥F | y.val ∈ P} =
        {y : ↥F | y.val ∈ P} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change (K.map (t,z)).val ∈ P
      rw [hKfront t z (hP hz)]
      exact hz
    · intro hy
      exact ⟨y,hy,hKfront t y (hP hy)⟩
  let Dp : Set ↥F := {y | y.val ∈ {z : S | z ∈ E.source ∧
    E z ∈ Schoenflies.Plane.openSquare 0 1}}
  have hface := regional_supported_single_surgery_preserves_finite_face
    F B0 (frontier F) IntrinsicEssentialArc (fun z => z.val.val)
    τ a k r K Dp (hpres B0 hBfront) (hpres (frontier F) Subset.rfl)
    hclass hdisjoint hKmove
    (fun t y hy => hKfix t y hy)
    havoid
  refine ⟨r,hrange,fun w => if w = k then r else a w,
    hface.1,hface.2,?_⟩
  simp

#print axioms regional_intrinsic_face_crosscut_surgery

/- Exact regional-arc contact decrease from the enhanced replacement range
   equation, once the chosen planar branch avoids the anchor. -/
theorem regional_proper_crosscut_contact_descent
    {S : Type} [TopologicalSpace S] {F : Set S}
    (a b : C(Interval,↥F))
    (E : OpenPartialHomeomorph S Schoenflies.Plane)
    (A B : Set Schoenflies.Plane) (anchor : Set S)
    (hrange : Set.range (fun t => (b t).val) =
      (Set.range (fun t => (a t).val) \
        {y : S | y ∈ E.source ∧ E y ∈ A}) ∪
        {y : S | y ∈ E.source ∧ E y ∈ B})
    (hremoved : {y : S | y ∈ E.source ∧ E y ∈ A} ⊆
      Set.range (fun t => (a t).val))
    (hinserted : Disjoint {y : S | y ∈ E.source ∧ E y ∈ B} anchor)
    (hfinite : (Set.range (fun t => (a t).val) ∩ anchor).Finite)
    (p : S) (hp : p ∈ {y : S | y ∈ E.source ∧ E y ∈ A} ∩ anchor) :
    (Set.range (fun t => (b t).val) ∩ anchor).Finite ∧
      (Set.range (fun t => (b t).val) ∩ anchor).ncard <
        (Set.range (fun t => (a t).val) ∩ anchor).ncard := by
  rw [hrange]
  exact regional_crosscut_replacement_strict_contact_decrease
    _ _ _ _ hremoved hinserted hfinite p hp

#print axioms regional_proper_crosscut_contact_descent
