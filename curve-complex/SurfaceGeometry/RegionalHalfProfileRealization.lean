import RegionalHalfGuidingGeometryScaffold
import HalfSignedGuidingChainRecord
import RegionalHalfGuidingCollar
import RegionalHalfProfileExterior
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryRectangle.DisjointFreeBoundaryRectangle
import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.ActualHarerOptionalCollapseGluingProof
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRelativeSupportNeighborhood

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
attribute [local instance] instDecidable_regionalHalfGuidingGeometryScaffold

set_option maxHeartbeats 16000000

/- H4: same-disk and same-chain marked profile strip. -/
theorem regional_half_guiding_chain_profile_realization
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
        ∃ E : C(Interval × Icc (-1 : ℝ) 1,↥F),
          IsEmbedding E ∧
          (∀ t, E (t,⟨0,by norm_num⟩) = (r v).val.val t) ∧
          (∀ u, (E (0,u)).val ∈ boundaryCircle ∧ (E (1,u)).val ∈ boundaryCircle) ∧
          (∀ t ∈ Ioo (0 : Interval) 1, ∀ u, (E (t,u)).val ∈ interior F) ∧
          IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) ∧
          ∃ (ε : C(Interval,ℝ)) (hε : ∀ t, 0 ≤ ε t ∧ ε t < 1),
            range (chain.q ρ) = range (fun t => E
              (t,⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩)) ∧
            (∀ t, ε t ≠ 0 → ∀ u, E (t,u) ∈ V) ∧
            (∀ t ∈ Icc chain.cut (1 : Interval), ε (chain.clock t) = 0) ∧
            ∃ ν : Interval ≃ₜ Interval,
              ν d.aStart = 0 ∧ ν (chain.clock 1) = 1 ∧
              (∀ t, chain.q ρ (ν t) = E
                (t,⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩)) ∧
              ∃ sweep : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
                IsEmbedding sweep ∧ range sweep ⊆ V ∧
                range d.disk ⊆ range sweep ∧
                range sweep ⊆ range d.disk ∪ range chain.oldStrip ∪
                  range chain.guideStrip ∪
                  chartPull F chain.cornerFan.chart (Metric.closedBall (0 : Plane) 1) ∧
                sweep '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
                  ((r v).val.val '' (chain.clock '' Icc (0 : Interval) chain.cut)) ∪
                  (chain.q ρ '' Icc (0 : Interval) (chain.cuts ρ ⟨chain.n,by omega⟩)) ∪
                  range (chain.boundaryExtension ρ) ∧
                range sweep ∩ {y : ↥F | y.val ∈ frontier F} =
                  range (chain.boundaryExtension ρ) := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset hcheap fan gap chain ρ
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
  -- A0: literal guide faces and filled-cell intersections.
  choose G hG hGr hG0 hG1 hGV hGcoord using ruled_guide_cells
  have guide_progress_bounds
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) (t : Interval) :
      chain.guidePortTime i.val.castSucc ≤ chain.guideClock.symm (chain.guideCoordinates ρ i t).1 ∧
      chain.guideClock.symm (chain.guideCoordinates ρ i t).1 ≤ chain.guidePortTime i.val.succ := by
    have h0 := (chain.guideCoordinates_order ρ i).monotone (show (0:Interval) ≤ t from bot_le)
    have h1 := (chain.guideCoordinates_order ρ i).monotone (show t ≤ (1:Interval) from le_top)
    simpa only [chain.guideCoordinates_zero,chain.guideCoordinates_one,
      Homeomorph.symm_apply_apply] using And.intro h0 h1
  have guide_longitudinal_adjacent
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 = j.val.val) (t s : Interval)
      (he : (chain.guideCoordinates ρ i t).1 = (chain.guideCoordinates ρ j s).1) :
      t = 1 ∧ s = 0 := by
    have hp : chain.guidePortTime i.val.succ = chain.guidePortTime j.val.castSucc :=
      congrArg chain.guidePortTime (Fin.ext hij)
    have he' := congrArg chain.guideClock.symm he
    have hi := guide_progress_bounds i t
    have hj := guide_progress_bounds j s
    have ht : t = 1 := (chain.guideCoordinates_order ρ i).injective (by
      rw [chain.guideCoordinates_one,Homeomorph.symm_apply_apply]
      exact le_antisymm hi.2 (by rw [hp,he']; exact hj.1))
    have hs : s = 0 := (chain.guideCoordinates_order ρ j).injective (by
      rw [chain.guideCoordinates_zero,Homeomorph.symm_apply_apply]
      exact le_antisymm (by rw [← hp,← he']; exact hi.2) hj.1)
    exact ⟨ht,hs⟩
  have guide_face_range
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) (t : Interval) :
      range (fun u : Interval => G i (t,u)) = chain.guideStrip ''
        {z | z.1 = (chain.guideCoordinates ρ i t).1 ∧
          0 ≤ z.2.val ∧ z.2.val ≤ (chain.guideCoordinates ρ i t).2.val} := by
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      obtain ⟨z,hz1,hz2,hzG⟩ := hGcoord i t u
      refine ⟨z,⟨hz1,?_,?_⟩,hzG.symm⟩
      · rw [hz2]; exact mul_nonneg u.property.1 (chain.guideCoordinates_width ρ i t).1.le
      · rw [hz2]; exact mul_le_of_le_one_left (chain.guideCoordinates_width ρ i t).1.le u.property.2
    · rintro ⟨z,⟨hz1,hz0,hzle⟩,rfl⟩
      let u : Interval := ⟨z.2.val / (chain.guideCoordinates ρ i t).2.val,
        ⟨div_nonneg hz0 (chain.guideCoordinates_width ρ i t).1.le,
          (div_le_one (chain.guideCoordinates_width ρ i t).1).mpr hzle⟩⟩
      obtain ⟨z',hz'1,hz'2,hz'G⟩ := hGcoord i t u
      refine ⟨u,hz'G.trans (congrArg chain.guideStrip ?_)⟩
      apply Prod.ext
      · exact hz'1.trans hz1.symm
      · apply Subtype.ext
        rw [hz'2]
        exact div_mul_cancel₀ _ (chain.guideCoordinates_width ρ i t).1.ne'
  have guide_full_seam
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 = j.val.val) (u : Interval) : G i (1,u) = G j (0,u) := by
    obtain ⟨z,hz1,hz2,hzG⟩ := hGcoord i 1 u
    obtain ⟨z',hz'1,hz'2,hz'G⟩ := hGcoord j 0 u
    rw [hzG,hz'G]
    apply congrArg chain.guideStrip
    apply Prod.ext
    · rw [hz1,hz'1,guide_coordinate_seam i j hij]
    · apply Subtype.ext
      rw [hz2,hz'2,guide_coordinate_seam i j hij]
  have guide_adjacent_inter
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 = j.val.val) :
      range (G i) ∩ range (G j) = range (fun u : Interval => G i (1,u)) := by
    rw [hGr i,hGr j,guide_face_range i 1]
    ext y
    constructor
    · rintro ⟨⟨z,⟨t,hzt,hz0,hzw⟩,rfl⟩,⟨z',⟨s,hz's,hz'0,hz'w⟩,he⟩⟩
      have hzz := chain.guideStrip_embedded.injective he
      subst z'
      obtain ⟨rfl,rfl⟩ := guide_longitudinal_adjacent i j hij t s (hzt.symm.trans hz's)
      exact ⟨z,⟨hzt,hz0,hzw⟩,rfl⟩
    · rintro ⟨z,⟨hzt,hz0,hzw⟩,rfl⟩
      refine ⟨⟨z,⟨1,hzt,hz0,hzw⟩,rfl⟩,⟨z,⟨0,?_,hz0,?_⟩,rfl⟩⟩
      · rw [← guide_coordinate_seam i j hij]; exact hzt
      · rw [← guide_coordinate_seam i j hij]; exact hzw
  have guide_nonadjacent_disjoint
      (i j : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hij : i.val.val+1 < j.val.val) : Disjoint (range (G i)) (range (G j)) := by
    rw [hGr i,hGr j]
    apply Set.disjoint_left.mpr
    rintro y ⟨z,⟨t,ht,hz0,hzw⟩,rfl⟩ ⟨z',⟨s,hs,hz'0,hz'w⟩,he⟩
    have hzz := chain.guideStrip_embedded.injective he
    subst z'
    have hcs := congrArg chain.guideClock.symm (ht.symm.trans hs)
    have hi := (guide_progress_bounds i t).2
    have hj := (guide_progress_bounds j s).1
    have hp := chain.guidePortTime_order i.val.succ j.val.castSucc hij (Nat.le_of_lt j.property)
    have hh := lt_of_le_of_lt hi (lt_of_lt_of_le hp hj)
    rw [hcs] at hh
    exact (lt_irrefl _) hh
  have corner_cell_chart (z : Interval × Interval) :
      chain.cornerFan.chart (cornerCell z).val = P z := chain.cornerFan.chart.right_inv (hPt z)
  have corner_plane_bottom (t : Interval) : P (t,0) = (1-t.val) • chain.cornerEntry := by
    simp [P]
  have corner_plane_final (u : Interval) : P (1,u) = u.val • Plane.mk (-chain.cornerDelta) 0 := by
    simp [P]
  have corner_plane_entry (u : Interval) :
      P (0,u) = Plane.mk (chain.cornerEntry 0-u.val*chain.cornerEpsilon ρ) (chain.cornerEntry 1) := by
    ext j
    fin_cases j
    · change P (0,u) 0 = _
      rw [hP0]; simp
    · change P (0,u) 1 = _
      rw [hP1]; simp
  have corner_bottom_range : range (fun t : Interval => cornerCell (t,0)) =
      d.second '' Icc chain.guideEntryTime (1:Interval) := by
    rw [← chain.corner_b_axis_segment]
    ext y
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨hPc_source (t,0),?_⟩
      rw [corner_cell_chart,corner_plane_bottom,segment_eq_image]
      refine ⟨1-t.val,⟨by linarith [t.property.2],by linarith [t.property.1]⟩,?_⟩
      simp
    · rintro ⟨hy,hyseg⟩
      rw [segment_eq_image] at hyseg
      obtain ⟨a,ha,he⟩ := hyseg
      let t : Interval := ⟨1-a,⟨by linarith [ha.2],by linarith [ha.1]⟩⟩
      refine ⟨t,?_⟩
      apply Subtype.ext
      change chain.cornerFan.chart.symm (P (t,0)) = y.val
      rw [corner_plane_bottom]
      have hplane : (1-t.val) • chain.cornerEntry = chain.cornerFan.chart y.val := by
        simpa [t] using he
      rw [hplane]
      exact chain.cornerFan.chart.left_inv hy
  have corner_final_range : range (fun u : Interval => cornerCell (1,u)) =
      (r v).val.val '' (chain.clock '' Icc (chain.clock.symm d.aFinish) chain.cut) := by
    rw [← chain.corner_a_axis_segment]
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      refine ⟨hPc_source (1,u),?_⟩
      rw [corner_cell_chart,corner_plane_final,segment_eq_image]
      exact ⟨u.val,u.property,by simp⟩
    · rintro ⟨hy,hyseg⟩
      rw [segment_eq_image] at hyseg
      obtain ⟨a,ha,he⟩ := hyseg
      refine ⟨⟨a,ha⟩,?_⟩
      apply Subtype.ext
      change chain.cornerFan.chart.symm (P (1,⟨a,ha⟩)) = y.val
      rw [corner_plane_final]
      have hplane : a • Plane.mk (-chain.cornerDelta) 0 = chain.cornerFan.chart y.val := by
        simpa using he
      rw [hplane]
      exact chain.cornerFan.chart.left_inv hy
  have guide_corner_full_seam
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hi : i.val.val+1 = chain.cornerIndex.val) (u : Interval) :
      G i (1,u) = cornerCell (0,u) := by
    obtain ⟨z,hz1,hz2,hzG⟩ := hGcoord i 1 u
    have hz0 : 0 ≤ z.2.val := by
      rw [hz2]; exact mul_nonneg u.property.1 (chain.guideCoordinates_width ρ i 1).1.le
    have hzw : z.2.val ≤ (chain.guideCoordinates ρ i 1).2.val := by
      rw [hz2]; exact mul_le_of_le_one_left (chain.guideCoordinates_width ρ i 1).1.le u.property.2
    have ht := chain.guide_corner_width_transition ρ i hi z.2 hz0 hzw
    have hpair : ((chain.guideCoordinates ρ i 1).1,z.2) = z := by
      apply Prod.ext
      · exact hz1.symm
      · rfl
    dsimp only at ht
    rw [hpair] at ht
    apply Subtype.ext
    rw [hzG]
    change (chain.guideStrip z).val = chain.cornerFan.chart.symm (P (0,u))
    rw [← chain.cornerFan.chart.left_inv ht.1]
    apply congrArg chain.cornerFan.chart.symm
    rw [ht.2,corner_plane_entry,hz2]
    simp only [mul_div_cancel_right₀ _ (chain.guideCoordinates_width ρ i 1).1.ne']
  have guide_corner_exact_inter
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) :
      range (G i) ∩ range cornerCell =
        if i.val.val+1 = chain.cornerIndex.val then range (fun u : Interval => G i (1,u)) else ∅ := by
    rw [hGr i,corner_cell_range,chain.guide_corner_inter]
    split_ifs
    · exact (guide_face_range i 1).symm
    · rfl
  have corner_disk_exact_inter : range cornerCell ∩ range d.disk =
      d.second '' Icc chain.guideEntryTime (1:Interval) := by
    rw [corner_cell_range]
    exact chain.corner_disk_inter ρ
  have guide_first_full_face
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hi : i.val.val = 0) (u : Interval) :
      ∃ width : Icc (-1:ℝ) 1, width.val = ρ.val*u.val ∧ G i (0,u) = chain.boundaryLine width := by
    obtain ⟨z,hz1,hz2,hzG⟩ := hGcoord i 0 u
    refine ⟨z.2,?_,?_⟩
    · rw [hz2,chain.guideCoordinates_first_width ρ i hi,mul_comm]
    · rw [hzG,chain.boundaryLine_eq]
      apply congrArg chain.guideStrip
      apply Prod.ext
      · rw [hz1,chain.guideCoordinates_zero]
        have hidx : i.val.castSucc = 0 := Fin.ext hi
        rw [hidx,chain.guidePortTime_zero,chain.guideClock_start]
      · rfl
  have guide_coordinate_selected
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) (t : Interval) :
      (chain.guideCoordinates ρ i t).1 ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) := by
    have hb := guide_progress_bounds i t
    have h0 := chain.guidePortTime_selected i.val.castSucc (Nat.le_of_lt i.property)
    have h1 := chain.guidePortTime_selected i.val.succ (by exact i.property)
    rcases chain.guideClock_increasing with hm | ha
    · have hlo := hm.monotone hb.1
      have hhi := hm.monotone hb.2
      simp only [Homeomorph.apply_symm_apply] at hlo hhi
      exact ⟨h0.1.trans hlo,hhi.trans h1.2⟩
    · have hlo := ha.antitone hb.2
      have hhi := ha.antitone hb.1
      simp only [Homeomorph.apply_symm_apply] at hlo hhi
      exact ⟨h1.1.trans hlo,hhi.trans h0.2⟩
  have selected_b_in_second :
      (r w).val.val '' Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) ⊆ range d.second := by
    rintro y ⟨t,ht,rfl⟩
    have hc : Continuous (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish) :=
      (CurveComplex.BranchedDoubleCover.intervalSegment d.bStart d.bFinish).continuous
    have h0 : d.bStart ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish) :=
      ⟨0,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
    have h1 : d.bFinish ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine d.bStart d.bFinish) :=
      ⟨1,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
    obtain ⟨u,hu⟩ := (isPreconnected_range hc).ordConnected.uIcc_subset h0 h1 ht
    exact ⟨u,(d.second_eq u).trans (congrArg (r w).val.val hu)⟩
  have guide_disk_exact_inter
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) :
      range (G i) ∩ range d.disk = range (fun t : Interval => G i (t,0)) := by
    ext y
    constructor
    · rintro ⟨hy,hD⟩
      rw [hGr i] at hy
      obtain ⟨z,⟨t,ht,hz0,hzw⟩,rfl⟩ := hy
      have hzselected : z.1 ∈ Icc (min d.bStart d.bFinish) (max d.bStart d.bFinish) :=
        ht.symm ▸ guide_coordinate_selected i t
      have hzero : z.2.val = 0 := by
        by_contra hn
        have hzpos : 0 < z.2.val := lt_of_le_of_ne hz0 (Ne.symm hn)
        exact Set.disjoint_left.mp chain.guiding_exterior
          ⟨z,⟨hzselected,hzpos,hzw.trans_lt (chain.guideCoordinates_width ρ i t).2⟩,rfl⟩ hD
      refine ⟨t,(hG0 i t).trans ?_⟩
      rw [← chain.guideStrip_center]
      apply congrArg chain.guideStrip
      apply Prod.ext
      · exact ht.symm
      · exact Subtype.ext hzero.symm
    · rintro ⟨t,rfl⟩
      refine ⟨mem_range_self (t,0),?_⟩
      change G i (t,0) ∈ range d.disk
      rw [hG0]
      have hb := selected_b_in_second ⟨(chain.guideCoordinates ρ i t).1,guide_coordinate_selected i t,rfl⟩
      rw [← d.whole_second] at hb
      exact hb.1
  -- A3a: a literal terminal cap graph in the existing old strip.
  let L : ℝ := chain.cornerEntry 0-chain.cornerEpsilon ρ
  have hden : 0 < L+chain.cornerDelta := by
    have hp := chain.corner_horizontal_progress ρ
    dsimp [L]
    linarith
  let capScale : ℝ := (chain.oldCornerSign*chain.cornerEntry 1) /
    (chain.oldCornerScale*(L+chain.cornerDelta))
  have capScale_pos : 0 < capScale := div_pos chain.oldCornerSign_matches
    (mul_pos chain.oldCornerScale_pos hden)
  let capHeight : C(Interval,ℝ) :=
    ⟨fun t => (chain.oldCornerX t+chain.cornerDelta)*capScale,by fun_prop⟩
  have capHeight_cut : capHeight chain.cut = 0 := by
    simp [capHeight,chain.oldCornerX_cut]
  have cut_in_old_window : chain.cut ∈ chain.oldCornerWindow :=
    chain.oldCornerWindow_padded ⟨chain.corner_before_cut.le,le_rfl⟩
  let capWindow : Set Interval := chain.oldCornerWindow ∩
    (chain.oldCornerX ⁻¹' Iio L) ∩ (capHeight ⁻¹' Iio chain.oldCornerWidth)
  have capWindow_open : IsOpen capWindow :=
    (chain.oldCornerWindow_open.inter (isOpen_Iio.preimage chain.oldCornerX.continuous)).inter
      (isOpen_Iio.preimage capHeight.continuous)
  have cut_in_cap_window : chain.cut ∈ capWindow := by
    refine ⟨⟨cut_in_old_window,?_⟩,?_⟩
    · change chain.oldCornerX chain.cut < L
      rw [chain.oldCornerX_cut]
      linarith
    · change capHeight chain.cut < chain.oldCornerWidth
      rw [capHeight_cut]
      exact chain.oldCornerWidth_pos
  obtain ⟨cl,cr,hclc,hcapnbhd⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨chain.clock.symm d.aFinish,chain.corner_before_cut⟩
      ⟨1,chain.cut_interior.2⟩).mp (capWindow_open.mem_nhds cut_in_cap_window)
  obtain ⟨s,hs⟩ := exists_between (max_lt chain.corner_before_cut hclc.1)
  obtain ⟨rCap,hrCap⟩ := exists_between (lt_min chain.cut_interior.2 hclc.2)
  have hs0 : chain.clock.symm d.aFinish < s := (le_max_left _ _).trans_lt hs.1
  have hsc : s < chain.cut := hs.2
  have hcr : chain.cut < rCap := hrCap.1
  have hr1 : rCap < (1:Interval) := hrCap.2.trans_le (min_le_left _ _)
  have cap_interval_window : Icc s rCap ⊆ capWindow := by
    intro t ht
    apply hcapnbhd
    exact ⟨((le_max_right _ _).trans_lt hs.1).trans_le ht.1,
      ht.2.trans_lt (hrCap.2.trans_le (min_le_right _ _))⟩
  have cap_interval_old_window : Icc s rCap ⊆ chain.oldCornerWindow :=
    fun t ht => (cap_interval_window ht).1.1
  have cap_left_window (t : Icc s chain.cut) : t.val ∈ capWindow :=
    cap_interval_window ⟨t.property.1,t.property.2.trans hcr.le⟩
  have capHeight_nonneg (t : Icc s chain.cut) : 0 ≤ capHeight t.val := by
    have hx := chain.oldCornerX_order.antitoneOn (cap_left_window t).1.1
      cut_in_old_window t.property.2
    rw [chain.oldCornerX_cut] at hx
    exact mul_nonneg (by linarith) capScale_pos.le
  have capHeight_pos (t : Icc s chain.cut) (ht : t.val < chain.cut) : 0 < capHeight t.val := by
    have hx := chain.oldCornerX_order (cap_left_window t).1.1 cut_in_old_window ht
    rw [chain.oldCornerX_cut] at hx
    exact mul_pos (by linarith) capScale_pos
  have capHeight_small (t : Icc s chain.cut) : capHeight t.val < chain.oldCornerWidth :=
    (cap_left_window t).2
  have capHeight_strictAnti : StrictAnti (fun t : Icc s chain.cut => capHeight t.val) := by
    intro t u htu
    have hx := chain.oldCornerX_order (cap_left_window t).1.1 (cap_left_window u).1.1 htu
    exact mul_lt_mul_of_pos_right (by linarith only [hx]) capScale_pos
  let capTau : C(Icc s chain.cut,Interval) :=
    ⟨fun t => ⟨(L-chain.oldCornerX t.val)/(L+chain.cornerDelta),by
      constructor
      · exact div_nonneg (sub_nonneg.mpr (cap_left_window t).1.2.le) hden.le
      · apply (div_le_one hden).mpr
        have hx := chain.oldCornerX_order.antitoneOn (cap_left_window t).1.1 cut_in_old_window t.property.2
        rw [chain.oldCornerX_cut] at hx
        linarith⟩,by fun_prop⟩
  have capTau_pos (t : Icc s chain.cut) : 0 < (capTau t).val :=
    div_pos (sub_pos.mpr (cap_left_window t).1.2) hden
  have capTau_lt_one (t : Icc s chain.cut) (ht : t.val < chain.cut) : (capTau t).val < 1 := by
    apply (div_lt_one hden).mpr
    have hx := chain.oldCornerX_order (cap_left_window t).1.1 cut_in_old_window ht
    rw [chain.oldCornerX_cut] at hx
    linarith
  have capTau_strictMono : StrictMono capTau := by
    intro t u htu
    change (L-chain.oldCornerX t.val)/(L+chain.cornerDelta) <
      (L-chain.oldCornerX u.val)/(L+chain.cornerDelta)
    exact div_lt_div_of_pos_right
      (sub_lt_sub_left (chain.oldCornerX_order (cap_left_window t).1.1 (cap_left_window u).1.1 htu) L) hden
  have capTau_cut : capTau ⟨chain.cut,⟨hsc.le,le_rfl⟩⟩ = 1 := by
    apply Subtype.ext
    change (L-chain.oldCornerX chain.cut)/(L+chain.cornerDelta) = 1
    rw [chain.oldCornerX_cut]
    simpa only [sub_neg_eq_add] using div_self hden.ne'
  let capClock : C(Icc s chain.cut,Interval) :=
    ⟨fun t => CurveComplex.BranchedDoubleCover.intervalAffine
      (chain.cuts ρ chain.cornerIndex.castSucc) (chain.cuts ρ chain.cornerIndex.succ) (capTau t),
      (CurveComplex.BranchedDoubleCover.intervalSegment _ _).continuous.comp capTau.continuous⟩
  have cap_cuts_strict : chain.cuts ρ chain.cornerIndex.castSucc < chain.cuts ρ chain.cornerIndex.succ :=
    chain.cuts_strict ρ (by exact Nat.lt_succ_self chain.cornerIndex.val)
  have capClock_strictMono : StrictMono capClock := by
    intro t u htu
    have hτ := capTau_strictMono htu
    change (capTau t).val < (capTau u).val at hτ
    have hc : (chain.cuts ρ chain.cornerIndex.castSucc).val < (chain.cuts ρ chain.cornerIndex.succ).val := cap_cuts_strict
    change (1-(capTau t).val)*(chain.cuts ρ chain.cornerIndex.castSucc).val +
      (capTau t).val*(chain.cuts ρ chain.cornerIndex.succ).val <
      (1-(capTau u).val)*(chain.cuts ρ chain.cornerIndex.castSucc).val +
      (capTau u).val*(chain.cuts ρ chain.cornerIndex.succ).val
    have hm := mul_pos (sub_pos.mpr hτ) (sub_pos.mpr hc)
    nlinarith only [hm]
  have capClock_cut : capClock ⟨chain.cut,⟨hsc.le,le_rfl⟩⟩ = chain.cuts ρ ⟨chain.n,by omega⟩ := by
    change CurveComplex.BranchedDoubleCover.intervalAffine _ _ (capTau _) = _
    rw [capTau_cut]
    simp only [CurveComplex.BranchedDoubleCover.intervalAffine]
    have he : chain.cornerIndex.succ = (⟨chain.n,by omega⟩ : Fin (chain.n+2)) :=
      Fin.ext chain.corner_position
    simpa using congrArg (chain.cuts ρ) he
  have capClock_start_bounds :
      0 < capClock ⟨s,⟨le_rfl,hsc.le⟩⟩ ∧
      capClock ⟨s,⟨le_rfl,hsc.le⟩⟩ < chain.cuts ρ ⟨chain.n,by omega⟩ := by
    constructor
    · have hτ := capTau_pos ⟨s,⟨le_rfl,hsc.le⟩⟩
      have hc : (chain.cuts ρ chain.cornerIndex.castSucc).val < (chain.cuts ρ chain.cornerIndex.succ).val := cap_cuts_strict
      have hc0 := (chain.cuts ρ chain.cornerIndex.castSucc).property.1
      change 0 < (1-(capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val)*(chain.cuts ρ chain.cornerIndex.castSucc).val +
        (capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val*(chain.cuts ρ chain.cornerIndex.succ).val
      have hm := mul_pos hτ (sub_pos.mpr hc)
      nlinarith only [hm,hc0]
    · rw [← capClock_cut]
      exact capClock_strictMono hsc
  have capTau_x (t : Icc s chain.cut) :
      -chain.cornerDelta+(1-(capTau t).val)*(L+chain.cornerDelta) = chain.oldCornerX t.val := by
    have hτ : (capTau t).val*(L+chain.cornerDelta) = L-chain.oldCornerX t.val :=
      div_mul_cancel₀ _ hden.ne'
    nlinarith only [hτ]
  have cap_height_chart (t : Icc s chain.cut) :
      chain.cornerEntry 1*(1-(capTau t).val) =
        chain.oldCornerSign*chain.oldCornerScale*capHeight t.val := by
    change chain.cornerEntry 1*(1-(L-chain.oldCornerX t.val)/(L+chain.cornerDelta)) =
      chain.oldCornerSign*chain.oldCornerScale*((chain.oldCornerX t.val+chain.cornerDelta)*
        ((chain.oldCornerSign*chain.cornerEntry 1)/(chain.oldCornerScale*(L+chain.cornerDelta))))
    rcases chain.oldCornerSign_unit with hσ | hσ <;> rw [hσ] <;>
      field_simp [chain.oldCornerScale_pos.ne',hden.ne'] <;> ring
  let capWidth : C(Icc s chain.cut,Icc (-1:ℝ) 1) :=
    ⟨fun t => ⟨capHeight t.val,⟨by linarith [capHeight_nonneg t],
      (capHeight_small t).le.trans chain.oldCornerWidth_lt_one.le⟩⟩,by fun_prop⟩
  have cap_graph (t : Icc s chain.cut) :
      chain.q ρ (capClock t) = chain.oldStrip (chain.clock t.val,capWidth t) := by
    change chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine _ _ (capTau t)) = _
    rw [← chain.piece_clock]
    have ht := chain.old_corner_transition t.val (cap_left_window t).1.1 (capWidth t)
      (by change |capHeight t.val| ≤ chain.oldCornerWidth
          rw [abs_of_nonneg (capHeight_nonneg t)]; exact (capHeight_small t).le)
    apply Subtype.ext
    rw [(chain.corner_formula ρ (capTau t)).2]
    rw [← chain.cornerFan.chart.left_inv ht.1]
    apply congrArg chain.cornerFan.chart.symm
    rw [ht.2]
    ext j
    fin_cases j
    · change -chain.cornerDelta+(1-(capTau t).val)*
        (chain.cornerEntry 0-chain.cornerEpsilon ρ+chain.cornerDelta) = chain.oldCornerX t.val
      exact capTau_x t
    · change chain.cornerEntry 1*(1-(capTau t).val) =
        chain.oldCornerSign*chain.oldCornerScale*capHeight t.val
      exact cap_height_chart t
  have cap_plane_upper (t : Icc s chain.cut) :
      P (capTau t,1) = Plane.mk (chain.oldCornerX t.val)
        (chain.oldCornerSign*chain.oldCornerScale*capHeight t.val) := by
    ext j
    fin_cases j
    · change P (capTau t,1) 0 = _
      rw [hP0]
      have hx := capTau_x t
      dsimp [L] at hx
      norm_num
      nlinarith only [hx]
    · change P (capTau t,1) 1 = _
      rw [hP1]
      rw [mul_comm]
      exact cap_height_chart t
  have cap_base_hull (t : Icc s chain.cut) :
      Plane.mk (chain.oldCornerX t.val) 0 ∈
        regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ) := by
    have hA : (r v).val.val (chain.clock t.val) ∈
        chartPull F chain.cornerFan.chart (segment ℝ (0:Plane) (Plane.mk (-chain.cornerDelta) 0)) := by
      rw [chain.corner_a_axis_segment]
      exact ⟨chain.clock t.val,⟨t.val,⟨hs0.le.trans t.property.1,t.property.2⟩,rfl⟩,rfl⟩
    have hc : chain.cornerFan.chart ((r v).val.val (chain.clock t.val)).val =
        Plane.mk (chain.oldCornerX t.val) 0 := by
      simpa only [chain.oldStrip_center,mul_zero] using
        (chain.old_corner_transition t.val (cap_left_window t).1.1 ⟨0,by norm_num⟩
          (by simp only [abs_zero]; exact chain.oldCornerWidth_pos.le)).2
    have hseg := hA.2
    rw [hc] at hseg
    exact segment_subset_convexHull (by simp) (by simp) hseg
  have cap_vertical_in_hull (t : Icc s chain.cut) (u : Icc (-1:ℝ) 1)
      (hu0 : 0 ≤ u.val) (huh : u.val ≤ capHeight t.val) :
      chain.oldStrip (chain.clock t.val,u) ∈ chartPull F chain.cornerFan.chart
        (regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)) := by
    have ht := chain.old_corner_transition t.val (cap_left_window t).1.1 u
      (by rw [abs_of_nonneg hu0]; exact huh.trans (capHeight_small t).le)
    refine ⟨ht.1,?_⟩
    rw [ht.2]
    have hbase := cap_base_hull t
    have htop := hP_hull (capTau t,1)
    rw [cap_plane_upper] at htop
    rcases eq_or_lt_of_le (capHeight_nonneg t) with hz | hp
    · have hu : u.val = 0 := by linarith
      simpa only [hu,mul_zero] using hbase
    · let a : ℝ := u.val/capHeight t.val
      have ha0 : 0 ≤ a := div_nonneg hu0 hp.le
      have ha1 : a ≤ 1 := (div_le_one hp).mpr huh
      have hc := (convex_convexHull ℝ
        ({0,Plane.mk (-chain.cornerDelta) 0,chain.cornerEntry,
          Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1)} : Set Plane))
        hbase htop (by linarith : 0 ≤ 1-a) ha0 (by ring : 1-a+a=1)
      have he : (1-a) • Plane.mk (chain.oldCornerX t.val) 0 +
          a • Plane.mk (chain.oldCornerX t.val) (chain.oldCornerSign*chain.oldCornerScale*capHeight t.val) =
          Plane.mk (chain.oldCornerX t.val) (chain.oldCornerSign*chain.oldCornerScale*u.val) := by
        ext j
        fin_cases j
        · simp
          ring
        · simp
          dsimp [a]
          field_simp [hp.ne']
      rw [he] at hc
      exact hc
  have cap_old_full_fibers_in_V (t : Interval) (ht : t ∈ Icc s rCap) (u : Icc (-1:ℝ) 1) :
      chain.oldStrip (chain.clock t,u) ∈ V :=
    chain.oldStrip_full_active_fibers _
      (chain.oldCornerWindow_active (cap_interval_old_window ht)) u
  have cap_port_margin : ∃ κ : ℝ, 0 < κ ∧ capHeight s+κ < chain.oldCornerWidth := by
    have hsWidth := capHeight_small ⟨s,⟨le_rfl,hsc.le⟩⟩
    refine ⟨(chain.oldCornerWidth-capHeight s)/2,?_,?_⟩ <;> linarith
  have interval_clock_orientation (e : Interval ≃ₜ Interval) :
      (StrictMono e ∧ e 0 = 0 ∧ e 1 = 1) ∨
        (StrictAnti e ∧ e 0 = 1 ∧ e 1 = 0) := by
    rcases e.continuous.strictMono_of_inj_boundedOrder' e.injective with hm | ha
    · left
      refine ⟨hm,?_,?_⟩
      · obtain ⟨t,ht⟩ := e.surjective 0
        apply Subtype.ext
        have hh := hm.monotone (show (0:Interval) ≤ t from bot_le)
        rw [ht] at hh
        exact le_antisymm hh (e 0).property.1
      · obtain ⟨t,ht⟩ := e.surjective 1
        apply Subtype.ext
        have hh := hm.monotone (show t ≤ (1:Interval) from le_top)
        rw [ht] at hh
        exact le_antisymm (e 1).property.2 hh
    · right
      refine ⟨ha,?_,?_⟩
      · obtain ⟨t,ht⟩ := e.surjective 1
        apply Subtype.ext
        have hh := ha.antitone (show (0:Interval) ≤ t from bot_le)
        rw [ht] at hh
        exact le_antisymm (e 0).property.2 hh
      · obtain ⟨t,ht⟩ := e.surjective 0
        apply Subtype.ext
        have hh := ha.antitone (show t ≤ (1:Interval) from le_top)
        rw [ht] at hh
        exact le_antisymm hh (e 1).property.1
  have old_clock_orientation :
      (StrictMono chain.clock ∧ d.aStart = 0 ∧ chain.clock 1 = 1) ∨
        (StrictAnti chain.clock ∧ d.aStart = 1 ∧ chain.clock 1 = 0) := by
    simpa only [chain.clock_start] using interval_clock_orientation chain.clock
  have guiding_clock_orientation :
      (StrictMono chain.guideClock ∧ d.bStart = 0 ∧ chain.guideClock 1 = 1) ∨
        (StrictAnti chain.guideClock ∧ d.bStart = 1 ∧ chain.guideClock 1 = 0) := by
    simpa only [chain.guideClock_start] using interval_clock_orientation chain.guideClock
  have cap_port_positive : 0 < capHeight s := capHeight_pos ⟨s,⟨le_rfl,hsc.le⟩⟩ hsc
  have capTau_start_between : capTau ⟨s,⟨le_rfl,hsc.le⟩⟩ ∈ Ioo (0:Interval) 1 :=
    ⟨capTau_pos _,capTau_lt_one _ hsc⟩
  let boundaryWidth (u : Interval) : Icc (-1:ℝ) 1 :=
    ⟨ρ.val*u.val,⟨by have := mul_nonneg ρ.property.1.le u.property.1; linarith,
      (mul_le_of_le_one_right ρ.property.1.le u.property.2).trans
        (ρ.property.2.trans chain.bound_lt_one).le⟩⟩
  have guide_first_face_literal
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hi : i.val.val = 0) (u : Interval) : G i (0,u) = chain.boundaryLine (boundaryWidth u) := by
    obtain ⟨w,hw,he⟩ := guide_first_full_face i hi u
    have hw' : w = boundaryWidth u := Subtype.ext hw
    simpa only [hw'] using he
  have guide_first_face_in_BV
      (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val})
      (hi : i.val.val = 0) (u : Interval) :
      G i (0,u) ∈ {y : ↥F | y.val ∈ boundaryCircle} ∩ V := by
    rw [guide_first_face_literal i hi u]
    apply chain.boundaryLine_local
    refine ⟨boundaryWidth u,?_,rfl⟩
    change |ρ.val*u.val| < chain.bound
    rw [abs_of_nonneg (mul_nonneg ρ.property.1.le u.property.1)]
    exact (mul_le_of_le_one_right ρ.property.1.le u.property.2).trans_lt ρ.property.2
  -- A2: consume the paid finite collar without reconstructing its cells.
  let guideCarrier : Set ↥F := ⋃ i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val},
    regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i)
  let cornerCarrier : Set ↥F := chartPull F chain.cornerFan.chart
    (regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ))
  let orientedA : C(Interval,↥F) := (r v).val.val.comp ⟨chain.clock,chain.clock.continuous⟩
  let z : Interval := chain.cuts ρ ⟨chain.n,by omega⟩
  let filledCarrier : Set ↥F := range d.disk ∪ guideCarrier ∪ cornerCarrier
  let oldNegative : Set ↥F := regionalHalfOldNegativeBand F chain.oldStrip
    chain.clock chain.cut chain.oldNegativeWidth
  obtain ⟨Hcollar,hHcollar,hHrange,hHV,hHbottom,hHtop,hHleft,hHright,
    hHdisk,hHfrontier,hHbeta,hHcut,hHfinal⟩ :=
    regional_half_guiding_cells_form_embedded_collar S g hg hS x R hR htarget
      F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint
      hfrontier ι r α hinv hcross v w hvw d V hV hdV havoid hcheap fan gap chain ρ
  change range Hcollar = guideCarrier ∪ cornerCarrier at hHrange
  change range (fun t => Hcollar (t,1)) = chain.q ρ '' Icc 0 z at hHtop
  change range (fun u => Hcollar (1,u)) = orientedA '' Icc (chain.clock.symm d.aFinish) chain.cut at hHfinal
  have hfilled_range : range d.disk ∪ range Hcollar = filledCarrier := by
    rw [hHrange]
    exact (union_assoc _ _ _).symm
  have hfilledV : filledCarrier ⊆ V := by
    rw [← hfilled_range]
    exact union_subset hdV hHV
  have hdFilled : range d.disk ⊆ filledCarrier := by
    rw [← hfilled_range]
    exact subset_union_left
  let reverseBoundary : C(Interval,↥F) := d.boundarySide.comp
    ⟨unitInterval.symm,unitInterval.continuous_symm⟩
  have hreverseEmbedding : IsEmbedding reverseBoundary :=
    d.boundary_embedded.comp unitInterval.symmHomeomorph.isEmbedding
  have hreverseRange : range reverseBoundary = range d.boundarySide := by
    change range (d.boundarySide ∘ unitInterval.symm) = _
    exact unitInterval.symm_bijective.2.range_comp _
  have hreverse0 : reverseBoundary 0 = d.second 0 := by
    simpa [reverseBoundary] using d.boundary_one
  have hreverse1 : reverseBoundary 1 = d.first 0 := by
    simpa [reverseBoundary] using d.boundary_zero
  have hreverseMeet : range reverseBoundary ∩ range d.first = {reverseBoundary 1} := by
    rw [hreverseRange,inter_comm,d.first_boundary_inter,hreverse1]
  -- The exact endpoint-preserving concatenation proof is reused locally.
  let pathB : Path (reverseBoundary 0) (reverseBoundary 1) := ⟨reverseBoundary,rfl,rfl⟩
  let pathA : Path (reverseBoundary 1) (d.first 1) := ⟨d.first,hreverse1.symm,rfl⟩
  let complement : C(Interval,↥F) := (pathB.trans pathA).toContinuousMap
  have complement_cross (s t : Interval) (he : reverseBoundary s = d.first t) :
      s = 1 ∧ t = 0 := by
    have hh : reverseBoundary s ∈ range reverseBoundary ∩ range d.first :=
      ⟨mem_range_self _,⟨t,he.symm⟩⟩
    rw [hreverseMeet] at hh
    have hh' := mem_singleton_iff.mp hh
    exact ⟨hreverseEmbedding.injective hh',
      d.first_embedded.injective (he.symm.trans (hh'.trans hreverse1))⟩
  have hComplement : IsEmbedding complement := by
    apply (complement.continuous.isClosedEmbedding ?_).isEmbedding
    intro s t he
    change (pathB.trans pathA) s = (pathB.trans pathA) t at he
    simp only [Path.trans_apply] at he
    split_ifs at he with hs ht ht
    · have hc := congrArg Subtype.val (hreverseEmbedding.injective he)
      apply Subtype.ext
      change 2*(s:ℝ) = 2*(t:ℝ) at hc
      linarith
    · obtain ⟨h1,h0⟩ := complement_cross _ _ he
      have hc0 := congrArg Subtype.val h0
      change 2*(t:ℝ)-1=0 at hc0
      exact False.elim (ht (by linarith))
    · obtain ⟨h1,h0⟩ := complement_cross _ _ he.symm
      have hc0 := congrArg Subtype.val h0
      change 2*(s:ℝ)-1=0 at hc0
      exact False.elim (hs (by linarith))
    · have hc := congrArg Subtype.val (d.first_embedded.injective he)
      apply Subtype.ext
      change 2*(s:ℝ)-1 = 2*(t:ℝ)-1 at hc
      linarith
  have hComplement0 : complement 0 = d.second 0 := (pathB.trans pathA).source.trans hreverse0
  have hComplement1 : complement 1 = d.second 1 := (pathB.trans pathA).target.trans d.corner_eq
  have hComplementRange : range complement = range d.boundarySide ∪ range d.first := by
    exact (pathB.trans_range pathA).trans (by
      change range reverseBoundary ∪ range d.first = _
      rw [hreverseRange])
  have hDiskComplementBoundary :
      d.disk '' {y | y.val ∈ Metric.sphere (0 : Plane) 1} =
        range d.second ∪ range complement := by
    rw [d.boundary_image,hComplementRange]
    ext y
    simp only [mem_union]
    tauto
  have hSecondComplementCollision (s t : Interval) (he : d.second s = complement t) :
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    have hc : d.second s ∈ range complement := ⟨t,he.symm⟩
    rw [hComplementRange] at hc
    rcases hc with hc | hc
    · have hs : s = 0 := d.second_embedded.injective
        (mem_singleton_iff.mp (d.second_boundary_inter ▸ ⟨mem_range_self _,hc⟩))
      exact Or.inl ⟨hs,hComplement.injective (he.symm.trans (hs ▸ hComplement0.symm))⟩
    · have hs : s = 1 := d.second_embedded.injective
        ((mem_singleton_iff.mp (d.sides_inter ▸ ⟨hc,mem_range_self _⟩)).trans d.corner_eq)
      exact Or.inr ⟨hs,hComplement.injective (he.symm.trans (hs ▸ hComplement1.symm))⟩
  have affine_interval_range (s t : Interval) :
      range (CurveComplex.BranchedDoubleCover.intervalAffine s t) = uIcc s t := by
    have hc := (CurveComplex.BranchedDoubleCover.intervalSegment s t).continuous
    have hs : s ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine s t) :=
      ⟨0,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
    have ht : t ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine s t) :=
      ⟨1,by simp [CurveComplex.BranchedDoubleCover.intervalAffine]⟩
    apply Subset.antisymm
    · rintro y ⟨u,rfl⟩
      rcases le_total s t with hst | hts
      · simpa [uIcc_of_le hst] using CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hst u
      · have he : CurveComplex.BranchedDoubleCover.intervalAffine s t u =
            CurveComplex.BranchedDoubleCover.intervalAffine t s (unitInterval.symm u) := by
          apply Subtype.ext
          simp [CurveComplex.BranchedDoubleCover.intervalAffine,unitInterval.symm]
          ring
        rw [he,uIcc_of_ge hts]
        exact CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hts _
    · exact (isPreconnected_range hc).ordConnected.uIcc_subset hs ht
  have clock_initial_image : chain.clock '' Icc (0 : Interval) (chain.clock.symm d.aFinish) =
      uIcc d.aStart d.aFinish := by
    rcases old_clock_orientation with ⟨hm,_,_⟩ | ⟨hm,_,_⟩
    · have ho : d.aStart ≤ d.aFinish := by
        simpa only [chain.clock_start,chain.clock.apply_symm_apply] using
          hm.monotone (show (0:Interval) ≤ chain.clock.symm d.aFinish from bot_le)
      rw [chain.clock.continuous.image_Icc_of_strictMono hm,
        chain.clock_start,chain.clock.apply_symm_apply,uIcc_of_le ho]
    · have ho : d.aFinish ≤ d.aStart := by
        simpa only [chain.clock_start,chain.clock.apply_symm_apply] using
          hm.antitone (show (0:Interval) ≤ chain.clock.symm d.aFinish from bot_le)
      rw [chain.clock.continuous.continuousOn.image_Icc_of_antitoneOn
          (show (0:Interval) ≤ chain.clock.symm d.aFinish from bot_le) (hm.antitone.antitoneOn _),chain.clock_start,chain.clock.apply_symm_apply,uIcc_of_ge ho]
  have first_oriented_range : range d.first =
      orientedA '' Icc (0 : Interval) (chain.clock.symm d.aFinish) := by
    have he : (d.first : Interval → ↥F) =
        (r v).val.val ∘ CurveComplex.BranchedDoubleCover.intervalAffine d.aStart d.aFinish :=
      funext d.first_eq
    rw [he,range_comp,affine_interval_range]
    change _ = ((r v).val.val ∘ chain.clock) '' _
    rw [image_comp,clock_initial_image]
  have first_and_padded : range d.first ∪ orientedA '' Icc (chain.clock.symm d.aFinish) chain.cut =
      orientedA '' Icc (0 : Interval) chain.cut := by
    rw [first_oriented_range,← image_union]
    congr 1
    exact Icc_union_Icc_eq_Icc bot_le chain.corner_before_cut.le
  have negative_guide_disjoint : Disjoint oldNegative guideCarrier := by
    refine disjoint_iUnion_right.mpr ?_
    intro i
    exact chain.old_negative_guide_clear ρ i
  have negative_filled : oldNegative ∩ filledCarrier = orientedA '' Icc (0 : Interval) chain.cut := by
    change oldNegative ∩ (range d.disk ∪ guideCarrier ∪ cornerCarrier) = _
    rw [inter_union_distrib_left,inter_union_distrib_left,
      chain.old_negative_disk_inter,negative_guide_disjoint.inter_eq,union_empty]
    change range d.first ∪ (oldNegative ∩ cornerCarrier) = _
    rw [chain.old_negative_corner_inter]
    change range d.first ∪ (r v).val.val '' (chain.clock '' Icc (chain.clock.symm d.aFinish) chain.cut) = _
    rw [← image_comp]
    exact first_and_padded
  have initial_face_range : range (fun u => Hcollar (0,u)) =
      chain.boundaryLine '' {u | 0 ≤ u.val ∧ u.val ≤ ρ.val} := by
    ext y
    constructor
    · rintro ⟨u,rfl⟩
      change Hcollar (0,u) ∈ _
      rw [hHleft]
      exact ⟨_,⟨mul_nonneg ρ.property.1.le u.property.1,
        mul_le_of_le_one_right ρ.property.1.le u.property.2⟩,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      let t : Interval := ⟨u.val/ρ.val,⟨div_nonneg hu.1 ρ.property.1.le,
        (div_le_one ρ.property.1).mpr hu.2⟩⟩
      refine ⟨t,?_⟩
      change Hcollar (0,t) = chain.boundaryLine u
      rw [hHleft]
      congr 1
      apply Subtype.ext
      change ρ.val * (u.val / ρ.val) = u.val
      field_simp [ne_of_gt ρ.property.1]
  have filled_frontier : filledCarrier ∩ {y : ↥F | y.val ∈ frontier F} =
      range (chain.boundaryExtension ρ) := by
    rw [← hfilled_range,union_inter_distrib_right,d.whole_frontier,hHfrontier,
      initial_face_range,chain.boundaryExtension_range]
  have filled_ceiling : filledCarrier ⊆ range d.disk ∪ range chain.oldStrip ∪
      range chain.guideStrip ∪ chartPull F chain.cornerFan.chart (Metric.closedBall (0 : Plane) 1) := by
    rintro y ((hy | hy) | hy)
    · exact Or.inl (Or.inl (Or.inl hy))
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      obtain ⟨z,hz,rfl⟩ := hi
      exact Or.inl (Or.inr (mem_range_self _))
    · right
      exact ⟨hy.1,Metric.ball_subset_closedBall (chain.cornerHull_open_unit ρ hy.2)⟩
  have attachment_boundary_rewrite :
      range complement ∪ range (fun u => Hcollar (0,u)) ∪
        range (fun u => Hcollar (1,u)) ∪ range (fun t => Hcollar (t,1)) =
      orientedA '' Icc (0 : Interval) chain.cut ∪ chain.q ρ '' Icc (0 : Interval) z ∪
        range (chain.boundaryExtension ρ) := by
    rw [hComplementRange,hHfinal,hHtop,initial_face_range,chain.boundaryExtension_range]
    rw [← first_and_padded]
    ext y
    simp only [mem_union]
    tauto
  have hAinjective : Function.Injective orientedA :=
    (r v).val.property.1.injective.comp chain.clock.injective
  have first0_oriented0 : d.first 0 = orientedA 0 := by
    simpa [orientedA,chain.clock_start,CurveComplex.BranchedDoubleCover.intervalAffine] using d.first_eq 0
  have boundary_side_in_disk : range d.boundarySide ⊆ range d.disk := by
    intro y hy
    apply image_subset_range d.disk _
    rw [d.boundary_image]
    exact Or.inr hy
  have boundary_extension_old_inter : range (chain.boundaryExtension ρ) ∩ range (r v).val.val =
      {orientedA 0} := by
    rw [chain.boundaryExtension_range]
    ext y
    constructor
    · rintro ⟨hy,ha⟩
      rcases hy with hy | hy
      · have hf : y ∈ range d.first := d.whole_first ▸ ⟨boundary_side_in_disk hy,ha⟩
        have hm : y ∈ ({d.first 0} : Set ↥F) := d.first_boundary_inter ▸ ⟨hf,hy⟩
        simpa only [first0_oriented0] using hm
      · obtain ⟨u,hu,rfl⟩ := hy
        have hlu : |u.val| < chain.bound := by
          rw [abs_of_nonneg hu.1]
          exact hu.2.trans_lt ρ.property.2
        exact (disjoint_left.mp (chain.outgoing_clear (some v) (by simpa using hvw))
          ⟨u,hlu,rfl⟩ ha).elim
    · intro hy
      have he := mem_singleton_iff.mp hy
      subst y
      refine ⟨Or.inl ?_,mem_range_self _⟩
      exact ⟨0,d.boundary_zero.trans first0_oriented0⟩
  have end_one_frontier : (orientedA 1).val ∈ frontier F := by
    have hB : (orientedA 1).val ∈ boundaryCircle := by
      rcases old_clock_orientation with ⟨_,_,he⟩ | ⟨_,_,he⟩
      · simpa [orientedA,he] using (r v).val.property.2.2.1
      · simpa [orientedA,he] using (r v).val.property.2.1
    rw [hfrontier]
    exact Or.inl hB
  have end_one_not_filled : orientedA 1 ∉ filledCarrier := by
    intro hfilled
    have hb : orientedA 1 ∈ range (chain.boundaryExtension ρ) :=
      filled_frontier ▸ ⟨hfilled,end_one_frontier⟩
    have he : orientedA 1 = orientedA 0 := mem_singleton_iff.mp
      (boundary_extension_old_inter ▸ ⟨hb,mem_range_self _⟩)
    have := congrArg Subtype.val (hAinjective he)
    norm_num at this
  -- Both A3 caller obligations are about the same actual filled sweep.
  have whole_old_of_actual_sweep
      (sweep : C(Metric.closedBall (0 : Plane) 1,↥F))
      (hsweep : IsEmbedding sweep) (hsweepRange : range sweep = filledCarrier)
      (hsweepSphere : sweep '' {y | y.val ∈ Metric.sphere (0 : Plane) 1} =
        orientedA '' Icc (0 : Interval) chain.cut ∪ chain.q ρ '' Icc (0 : Interval) z ∪
          range (chain.boundaryExtension ρ)) :
      range sweep ∩ range (r v).val.val = orientedA '' Icc (0 : Interval) chain.cut := by
    let ambientSweep : C(Metric.closedBall (0 : Plane) 1,S) :=
      ⟨fun x => (sweep x).val,continuous_subtype_val.comp sweep.continuous⟩
    have hambientSweep : IsEmbedding ambientSweep := IsEmbedding.subtypeVal.comp hsweep
    let tailCarrier : Set S := (fun t : Interval => (orientedA t).val) '' Ioc chain.cut 1
    have htailConnected : IsPreconnected tailCarrier :=
      isPreconnected_Ioc.image _ (continuous_subtype_val.comp orientedA.continuous).continuousOn
    have htailAvoid : Disjoint tailCarrier
        (ambientSweep '' {y | y.val ∈ Metric.sphere (0 : Plane) 1}) := by
      apply disjoint_left.mpr
      rintro y ⟨t,ht,rfl⟩ ⟨u,hu,he⟩
      have he' : sweep u = orientedA t := Subtype.ext he
      have hb : orientedA t ∈ sweep '' {y | y.val ∈ Metric.sphere (0 : Plane) 1} :=
        ⟨u,hu,he'⟩
      rw [hsweepSphere] at hb
      rcases hb with (⟨j,hj,hjEq⟩ | hq) | hb
      · have hejt : j = t := hAinjective hjEq
        exact (not_lt_of_ge (hejt ▸ hj.2)) ht.1
      · have heq : orientedA t = orientedA chain.cut := mem_singleton_iff.mp
          (chain.changed_prefix_meets_a ρ ▸ ⟨hq,mem_range_self _⟩)
        exact (ne_of_gt ht.1) (hAinjective heq)
      · have heq : orientedA t = orientedA 0 := mem_singleton_iff.mp
          (boundary_extension_old_inter ▸ ⟨hb,mem_range_self _⟩)
        exact (ne_of_gt (chain.cut_interior.1.trans ht.1)) (hAinjective heq)
    have htailOutside : tailCarrier ⊆ (range ambientSweep)ᶜ := by
      rcases RegionalEmbeddedFamily.connected_open_set_avoiding_disk_boundary_dichotomy
        tailCarrier htailConnected ambientSweep hambientSweep htailAvoid with hin | hout
      · have h1 : (orientedA 1).val ∈ tailCarrier := ⟨1,⟨chain.cut_interior.2,le_rfl⟩,rfl⟩
        obtain ⟨u,hu⟩ := interior_subset (hin h1)
        have hu' : sweep u = orientedA 1 := Subtype.ext hu
        exact (end_one_not_filled (hsweepRange ▸ ⟨u,hu'⟩)).elim
      · exact hout
    apply Subset.antisymm
    · rintro y ⟨hs,⟨t,ht⟩⟩
      let j : Interval := chain.clock.symm t
      have he : orientedA j = y := by simpa [orientedA,j] using ht
      by_cases hj : j ≤ chain.cut
      · exact ⟨j,⟨bot_le,hj⟩,he⟩
      · obtain ⟨u,hu⟩ := hs
        have htj : (orientedA j).val ∈ tailCarrier := ⟨j,⟨lt_of_not_ge hj,le_top⟩,rfl⟩
        exact (htailOutside htj ⟨u,congrArg Subtype.val (hu.trans he.symm)⟩).elim
    · rintro y ⟨t,ht,rfl⟩
      have hf : orientedA t ∈ filledCarrier :=
        (negative_filled.symm ▸ (show orientedA t ∈ orientedA '' Icc 0 chain.cut from ⟨t,ht,rfl⟩)).2
      exact ⟨hsweepRange.symm ▸ hf,mem_range_self _⟩
  obtain ⟨sweep,hsweep,hsweepRange0,hsweepBoundary0⟩ :=
    ActualHarerDiskGluing.actual_disk_attach_half_collar_with_optional_endpoint_collapse
      d.second complement d.disk d.second_embedded hComplement d.disk_embedded
      hComplement0.symm hComplement1.symm hDiskComplementBoundary hSecondComplementCollision
      Hcollar false false (by simp) hHbottom (by
        intro t u t' u'
        simp only [ActualHarerDiskGluing.collapsedEndpoint,Bool.false_eq_true,
          false_and,false_or,or_false]
        constructor
        · intro he
          exact ⟨congrArg Prod.fst (hHcollar.injective he),
            congrArg Prod.snd (hHcollar.injective he)⟩
        · rintro ⟨rfl,rfl⟩
          rfl) hHdisk
  have hsweepRange : range sweep = filledCarrier := hsweepRange0.trans hfilled_range
  have hsweepV : range sweep ⊆ V := hsweepRange ▸ hfilledV
  have hdSweep : range d.disk ⊆ range sweep := hsweepRange.symm ▸ hdFilled
  have hsweepCeiling : range sweep ⊆ range d.disk ∪ range chain.oldStrip ∪
      range chain.guideStrip ∪ chartPull F chain.cornerFan.chart (Metric.closedBall (0 : Plane) 1) :=
    hsweepRange ▸ filled_ceiling
  have hsweepSphere : sweep '' {y | y.val ∈ Metric.sphere (0 : Plane) 1} =
      orientedA '' Icc (0 : Interval) chain.cut ∪ chain.q ρ '' Icc (0 : Interval) z ∪
        range (chain.boundaryExtension ρ) := hsweepBoundary0.trans attachment_boundary_rewrite
  have hsweepFrontier : range sweep ∩ {y : ↥F | y.val ∈ frontier F} =
      range (chain.boundaryExtension ρ) := by rw [hsweepRange,filled_frontier]
  have hnegativeSweep : oldNegative ∩ range sweep = orientedA '' Icc (0 : Interval) chain.cut := by
    rw [hsweepRange,negative_filled]
  have hwholeOldSweep : range sweep ∩ range (r v).val.val =
      orientedA '' Icc (0 : Interval) chain.cut :=
    whole_old_of_actual_sweep sweep hsweep hsweepRange hsweepSphere
  -- A4: the transverse cap port meets the whole changed prefix only at its top.
  -- This is parameterized by the literal output data of the paid A3 theorem.
  have cap_port_prefix_collision
      (s0 τ0 k0 : Interval) (height0 : ℝ)
      (hs0 : s0 < chain.cut) (hsW : s0 ∈ chain.oldCornerWindow)
      (hτ0 : 0 < τ0 ∧ τ0 < 1)
      (hh0 : 0 < height0 ∧ height0 < chain.oldCornerWidth)
      (hx0 : -chain.cornerDelta+(1-τ0.val)*(L+chain.cornerDelta) = chain.oldCornerX s0)
      (hy0 : chain.cornerEntry 1*(1-τ0.val) = chain.oldCornerSign*chain.oldCornerScale*height0)
      (hk0 : k0 = CurveComplex.BranchedDoubleCover.intervalAffine
        (chain.cuts ρ chain.cornerIndex.castSucc) (chain.cuts ρ chain.cornerIndex.succ) τ0)
      (width0 : Interval → Icc (-1:ℝ) 1) (hwidth0 : ∀ u, (width0 u).val = height0*u.val)
      (hportHull : ∀ u, chain.oldStrip (chain.clock s0,width0 u) ∈ cornerCarrier)
      (j : Interval) (hj : j ∈ Icc (0:Interval) z) (u : Interval)
      (he : chain.q ρ j = chain.oldStrip (chain.clock s0,width0 u)) : j = k0 ∧ u = 1 := by
    have hwu : |(width0 u).val| ≤ chain.oldCornerWidth := by
      rw [hwidth0,abs_of_nonneg (mul_nonneg hh0.1.le u.property.1)]
      exact (mul_le_of_le_one_right hh0.1.le u.property.2).trans hh0.2.le
    have hchart := (chain.old_corner_transition s0 hsW (width0 u) hwu).2
    have hmem : chain.q ρ j ∈ range (chain.q ρ) := mem_range_self _
    rw [chain.q_range] at hmem
    obtain ⟨i,⟨t,ht⟩⟩ := mem_iUnion.mp hmem
    by_cases hi : i.val < chain.cornerIndex.val
    · let ii : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val} := ⟨i,hi⟩
      have hgEq : G ii (t,1) = chain.oldStrip (chain.clock s0,width0 u) :=
        (hG1 ii t).trans (ht.trans he)
      have hm : G ii (t,1) ∈ range (G ii) ∩ range cornerCell := by
        refine ⟨mem_range_self _,?_⟩
        rw [corner_cell_range,hgEq]
        exact hportHull u
      rw [guide_corner_exact_inter] at hm
      split_ifs at hm with hlast
      · obtain ⟨v0,hv0⟩ := hm
        have hcEq : cornerCell (0,v0) = chain.oldStrip (chain.clock s0,width0 u) :=
          (guide_corner_full_seam ii hlast v0).symm.trans (hv0.trans hgEq)
        have hcoords := congrArg (fun y : ↥F => chain.cornerFan.chart y.val 1) hcEq
        rw [corner_cell_chart,hchart] at hcoords
        change P (0,v0) 1 = chain.oldCornerSign*chain.oldCornerScale*(width0 u).val at hcoords
        rw [hP1,hwidth0] at hcoords
        have hmul : chain.cornerEntry 1 * ((1-τ0.val)*u.val-1) = 0 := by
          have hscaled := congrArg (fun x : ℝ => x*u.val) hy0
          norm_num at hcoords
          nlinarith only [hcoords,hscaled]
        have heq := (mul_eq_zero.mp hmul).resolve_left chain.cornerEntry_nonzero_height
        have hτpos : 0 < τ0.val := hτ0.1
        have hτle : 0 ≤ 1-τ0.val := sub_nonneg.mpr τ0.property.2
        have hprod := mul_le_of_le_one_right hτle u.property.2
        nlinarith
      · exact hm.elim
    · by_cases hic : i = chain.cornerIndex
      · subst i
        have hcEq : cornerCell (t,1) = chain.oldStrip (chain.clock s0,width0 u) :=
          (corner_cell_upper t).trans (ht.trans he)
        have hcoords := congrArg (fun y : ↥F => chain.cornerFan.chart y.val) hcEq
        rw [corner_cell_chart,hchart] at hcoords
        have hx := congrArg (fun x : Plane => x 0) hcoords
        rw [hP0] at hx
        change (1-t.val)*(chain.cornerEntry 0-1*chain.cornerEpsilon ρ)-
          t.val*1*chain.cornerDelta = chain.oldCornerX s0 at hx
        have htx : (t.val-τ0.val)*(L+chain.cornerDelta) = 0 := by
          dsimp only [L] at hx0 ⊢
          nlinarith only [hx,hx0]
        have htτ : t = τ0 := Subtype.ext (sub_eq_zero.mp ((mul_eq_zero.mp htx).resolve_right hden.ne'))
        have hjk : j = k0 := (chain.q_embedded ρ).injective (by
          rw [hk0,← chain.piece_clock,← htτ]
          exact ht.symm)
        refine ⟨hjk,?_⟩
        have hy := congrArg (fun x : Plane => x 1) hcoords
        rw [hP1,hwidth0,htτ] at hy
        change (1-τ0.val)*chain.cornerEntry 1 =
          chain.oldCornerSign*chain.oldCornerScale*(height0*u.val) at hy
        have hsig : chain.oldCornerSign ≠ 0 := by
          rcases chain.oldCornerSign_unit with h | h <;> rw [h] <;> norm_num
        have heq : chain.oldCornerSign*chain.oldCornerScale*height0*(1-u.val) = 0 := by
          nlinarith only [hy,hy0]
        have hu := (mul_eq_zero.mp heq).resolve_left
          (mul_ne_zero (mul_ne_zero hsig chain.oldCornerScale_pos.ne') hh0.1.ne')
        apply Subtype.ext
        change u.val = 1
        linarith
      · have hiLast : i = Fin.last chain.n := Fin.ext (by
          change i.val = chain.n
          have hneval : i.val ≠ chain.cornerIndex.val := fun h => hic (Fin.ext h)
          have := chain.corner_position
          have := i.isLt
          omega)
        have ha : chain.q ρ j ∈ range (r v).val.val := by
          rw [← ht,hiLast,chain.retained_formula]
          exact mem_range_self _
        have hcut : chain.q ρ j = orientedA chain.cut := mem_singleton_iff.mp
          (chain.changed_prefix_meets_a ρ ▸ ⟨⟨j,hj,rfl⟩,ha⟩)
        have hstrip : chain.oldStrip (chain.clock s0,width0 u) =
            chain.oldStrip (chain.clock chain.cut,⟨0,by norm_num⟩) := by
          rw [chain.oldStrip_center]
          exact he.symm.trans hcut
        have hsEq := chain.clock.injective (congrArg Prod.fst (chain.oldStrip_embedded.injective hstrip))
        exact (hs0.ne hsEq).elim
  have cap_rectangle_in_actual_sweep
      (s0 τ0 k0 : Interval) (height0 : ℝ)
      (hs0pos : 0 < s0) (hs0 : s0 < chain.cut) (hsW : s0 ∈ chain.oldCornerWindow)
      (hτ0 : 0 < τ0 ∧ τ0 < 1) (hk0pos : 0 < k0) (hk0lt : k0 < z)
      (hh0 : 0 < height0 ∧ height0 < chain.oldCornerWidth)
      (hx0 : -chain.cornerDelta+(1-τ0.val)*(L+chain.cornerDelta) = chain.oldCornerX s0)
      (hy0 : chain.cornerEntry 1*(1-τ0.val) = chain.oldCornerSign*chain.oldCornerScale*height0)
      (hk0 : k0 = CurveComplex.BranchedDoubleCover.intervalAffine
        (chain.cuts ρ chain.cornerIndex.castSucc) (chain.cuts ρ chain.cornerIndex.succ) τ0)
      (width0 : C(Interval,Icc (-1:ℝ) 1)) (hwidth0 : ∀ u, (width0 u).val = height0*u.val)
      (hportHull : ∀ u, chain.oldStrip (chain.clock s0,width0 u) ∈ cornerCarrier)
      (hgraph0 : chain.q ρ k0 = chain.oldStrip (chain.clock s0,width0 1)) :
      ∃ square : C(Interval × Interval,↥F), IsEmbedding square ∧
        (∀ t, square (t,0) = orientedA (CurveComplex.BranchedDoubleCover.intervalAffine 0 s0 t)) ∧
        (∀ t, square (t,1) = chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 k0 t)) ∧
        (∀ u, square (0,u) = chain.boundaryExtension ρ u) ∧
        (∀ u, square (1,u) = chain.oldStrip (chain.clock s0,width0 u)) ∧
        range square ⊆ range sweep := by
    let seg (b : Interval) := CurveComplex.BranchedDoubleCover.intervalSegment 0 b
    have hseg0 (b : Interval) : seg b 0 = 0 := by simp [seg,CurveComplex.BranchedDoubleCover.intervalSegment,CurveComplex.BranchedDoubleCover.intervalAffine]
    have hseg1 (b : Interval) : seg b 1 = b := by simp [seg,CurveComplex.BranchedDoubleCover.intervalSegment,CurveComplex.BranchedDoubleCover.intervalAffine]
    have hsegRange (b : Interval) (t : Interval) : seg b t ∈ Icc (0:Interval) b :=
      CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc bot_le t
    have hsegInjective (b : Interval) (hb : 0 < b) : Function.Injective (seg b) := by
      intro t u he
      have he' := congrArg Subtype.val he
      change (1-t.val)*0+t.val*b.val = (1-u.val)*0+u.val*b.val at he'
      apply Subtype.ext
      simp only [mul_zero,zero_add] at he'
      exact mul_right_cancel₀ (ne_of_gt (show (0:ℝ) < b.val from hb)) he'
    let PP : C(Interval,↥F) := orientedA.comp (seg s0)
    let QQ : C(Interval,↥F) := (chain.q ρ).comp (seg k0)
    let RR : C(Interval,↥F) := chain.oldStrip.comp
      ⟨fun u => (chain.clock s0,width0 u),continuous_const.prodMk width0.continuous⟩
    have hPP : IsEmbedding PP := (PP.continuous.isClosedEmbedding
      (hAinjective.comp (hsegInjective s0 hs0pos))).isEmbedding
    have hQQ : IsEmbedding QQ := (QQ.continuous.isClosedEmbedding
      ((chain.q_embedded ρ).injective.comp (hsegInjective k0 hk0pos))).isEmbedding
    have hRR : IsEmbedding RR := (RR.continuous.isClosedEmbedding (by
      intro t u he
      have hwidth := congrArg (fun y : Interval × Icc (-1:ℝ) 1 => y.2.val)
        (chain.oldStrip_embedded.injective he)
      change (width0 t).val = (width0 u).val at hwidth
      rw [hwidth0,hwidth0] at hwidth
      apply Subtype.ext
      exact (mul_left_cancel₀ hh0.1.ne' hwidth))).isEmbedding
    have hwidthZero : width0 0 = ⟨0,by norm_num⟩ := Subtype.ext (by simpa using hwidth0 0)
    have hPP0 : PP 0 = orientedA 0 := congrArg orientedA (hseg0 s0)
    have hPP1 : PP 1 = orientedA s0 := congrArg orientedA (hseg1 s0)
    have hQQ0 : QQ 0 = chain.beta ρ := (congrArg (chain.q ρ) (hseg0 k0)).trans (chain.q_zero ρ)
    have hQQ1 : QQ 1 = chain.q ρ k0 := congrArg (chain.q ρ) (hseg1 k0)
    have hRR0 : RR 0 = orientedA s0 := by
      change chain.oldStrip (chain.clock s0,width0 0) = _
      rw [hwidthZero,chain.oldStrip_center]
      rfl
    have hPPboundary (t u : Interval) (he : PP t = chain.boundaryExtension ρ u) : t = 0 ∧ u = 0 := by
      have ho : PP t = orientedA 0 := mem_singleton_iff.mp
        (boundary_extension_old_inter ▸ ⟨⟨u,he.symm⟩,mem_range_self _⟩)
      have ht : t = 0 := hPP.injective (ho.trans hPP0.symm)
      refine ⟨ht,(chain.boundaryExtension_embedded ρ).injective ?_⟩
      exact he.symm.trans (ho.trans (first0_oriented0.symm.trans (chain.boundaryExtension_zero ρ).symm))
    have hPPport (t u : Interval) (he : PP t = RR u) : t = 1 ∧ u = 0 := by
      have he' : chain.oldStrip (chain.clock (seg s0 t),⟨0,by norm_num⟩) =
          chain.oldStrip (chain.clock s0,width0 u) := by
        rw [chain.oldStrip_center]
        exact he
      have hp := chain.oldStrip_embedded.injective he'
      have ht : t = 1 := hsegInjective s0 hs0pos
        ((chain.clock.injective (congrArg Prod.fst hp)).trans (hseg1 s0).symm)
      have hu := congrArg (fun y : Interval × Icc (-1:ℝ) 1 => y.2.val) hp
      change 0 = (width0 u).val at hu
      rw [hwidth0] at hu
      refine ⟨ht,Subtype.ext ?_⟩
      change u.val = 0
      exact (mul_eq_zero.mp hu.symm).resolve_left hh0.1.ne'
    have hQQboundary (t u : Interval) (he : QQ t = chain.boundaryExtension ρ u) : t = 0 ∧ u = 1 := by
      have hB : (QQ t).val ∈ boundaryCircle := (chain.boundaryExtension_in_BV ρ ⟨u,he.symm⟩).1
      have hfront : (QQ t).val ∈ frontier F := by rw [hfrontier];exact Or.inl hB
      have ht0 : seg k0 t = 0 := by
        by_contra hn
        have hpos : 0 < seg k0 t := bot_lt_iff_ne_bot.mpr hn
        have hlt : seg k0 t < 1 := (hsegRange k0 t).2.trans_lt (hk0lt.trans_le z.property.2)
        exact chain.q_proper ρ (seg k0 t) ⟨hpos,hlt⟩ hfront
      have ht : t = 0 := hsegInjective k0 hk0pos (ht0.trans (hseg0 k0).symm)
      refine ⟨ht,(chain.boundaryExtension_embedded ρ).injective ?_⟩
      exact he.symm.trans ((congrArg QQ ht).trans (hQQ0.trans (chain.boundaryExtension_one ρ).symm))
    have hQQport (t u : Interval) (he : QQ t = RR u) : t = 1 ∧ u = 1 := by
      have hj : seg k0 t ∈ Icc (0:Interval) z :=
        ⟨(hsegRange k0 t).1,(hsegRange k0 t).2.trans hk0lt.le⟩
      obtain ⟨ht,hu⟩ := cap_port_prefix_collision s0 τ0 k0 height0 hs0 hsW hτ0 hh0 hx0 hy0 hk0
        width0 hwidth0 hportHull (seg k0 t) hj u he
      exact ⟨hsegInjective k0 hk0pos (ht.trans (hseg1 k0).symm),hu⟩
    have hPPQQ : Disjoint (range PP) (range QQ) := by
      apply disjoint_left.mpr
      rintro y ⟨t,rfl⟩ ⟨u,hu⟩
      have hq : PP t ∈ chain.q ρ '' Icc (0:Interval) z :=
        ⟨seg k0 u,⟨(hsegRange k0 u).1,(hsegRange k0 u).2.trans hk0lt.le⟩,hu⟩
      have heq : PP t = orientedA chain.cut := mem_singleton_iff.mp
        (chain.changed_prefix_meets_a ρ ▸ ⟨hq,mem_range_self _⟩)
      have htcut := hAinjective heq
      exact (not_le_of_gt hs0) (htcut ▸ (hsegRange s0 t).2)
    have hBoundaryPort : Disjoint (range (chain.boundaryExtension ρ)) (range RR) := by
      apply disjoint_left.mpr
      rintro y hy ⟨u,rfl⟩
      have hfront : (RR u).val ∈ frontier F := by
        rw [hfrontier]
        exact Or.inl (chain.boundaryExtension_in_BV ρ hy).1
      have hsInterior : chain.clock s0 ∈ Ioo (0:Interval) 1 := by
        rcases old_clock_orientation with ⟨hm,h0,h1⟩ | ⟨hm,h0,h1⟩
        · constructor
          · simpa only [chain.clock_start,h0] using hm hs0pos
          · simpa only [h1] using hm (hs0.trans chain.cut_interior.2)
        · have hclock0 : chain.clock 0 = 1 := chain.clock_start.trans h0
          constructor
          · simpa only [h1] using hm (hs0.trans chain.cut_interior.2)
          · simpa only [hclock0] using hm hs0pos
      exact (disjoint_left.mp disjoint_interior_frontier)
        (chain.oldStrip_interior _ hsInterior (width0 u)) hfront
    have hPPsweep : range PP ⊆ range sweep := by
      rintro y ⟨t,rfl⟩
      apply image_subset_range sweep _
      rw [hsweepSphere]
      exact Or.inl (Or.inl ⟨seg s0 t,⟨(hsegRange s0 t).1,(hsegRange s0 t).2.trans hs0.le⟩,rfl⟩)
    have hQQsweep : range QQ ⊆ range sweep := by
      rintro y ⟨t,rfl⟩
      apply image_subset_range sweep _
      rw [hsweepSphere]
      exact Or.inl (Or.inr ⟨seg k0 t,⟨(hsegRange k0 t).1,(hsegRange k0 t).2.trans hk0lt.le⟩,rfl⟩)
    have hBoundarySweep : range (chain.boundaryExtension ρ) ⊆ range sweep := by
      intro y hy
      exact (hsweepFrontier.symm ▸ hy).1
    have hRRsweep : range RR ⊆ range sweep := by
      rintro y ⟨u,rfl⟩
      rw [hsweepRange]
      exact Or.inr (hportHull u)
    have paid_rectangle := by
      run_tac
        let nm := Lean.Name.str (Lean.Name.str (Lean.Name.str
          (Lean.Name.num (`_private ++ `CurveComplexGenusTwo.Topology.ActualFreeBoundaryRectangle.DisjointFreeBoundaryRectangle) 0)
          "CoherentEndpointMotion") "FreeBoundaryNullGeometry") "four_sides_in_disk_give_prescribed_rectangle"
        Lean.Elab.Tactic.evalTactic (← `(tactic| exact @$(Lean.mkIdent nm)))
    exact paid_rectangle
      PP QQ (chain.boundaryExtension ρ) RR hPP hQQ (chain.boundaryExtension_embedded ρ) hRR
      (hPP0.trans (first0_oriented0.symm.trans (chain.boundaryExtension_zero ρ).symm))
      (hPP1.trans hRR0.symm) (hQQ0.trans (chain.boundaryExtension_one ρ).symm)
      (hQQ1.trans hgraph0) hPPboundary hPPport hQQboundary hQQport hPPQQ hBoundaryPort
      sweep hsweep hPPsweep hQQsweep hBoundarySweep hRRsweep
  have q_at_retained_cut : chain.q ρ z = orientedA chain.cut := by
    have hp := chain.piece_clock ρ (Fin.last chain.n) 0
    have hr := chain.retained_formula ρ 0
    have hi : (Fin.last chain.n).castSucc = (⟨chain.n,by omega⟩ : Fin (chain.n+2)) := Fin.ext rfl
    rw [hi] at hp
    simpa [z,orientedA,CurveComplex.BranchedDoubleCover.intervalAffine] using hp.symm.trans hr
  have cap_rectangle_whole_old
      (s0 k0 : Interval) (hs0 : 0 < s0 ∧ s0 < chain.cut) (hk0 : k0 < z)
      (width0 : C(Interval,Icc (-1:ℝ) 1))
      (square : C(Interval × Interval,↥F)) (hSquare : IsEmbedding square)
      (hbottom : ∀ t, square (t,0) = orientedA (CurveComplex.BranchedDoubleCover.intervalAffine 0 s0 t))
      (htop : ∀ t, square (t,1) = chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 k0 t))
      (hleft : ∀ u, square (0,u) = chain.boundaryExtension ρ u)
      (hright : ∀ u, square (1,u) = chain.oldStrip (chain.clock s0,width0 u))
      (hSquareSweep : range square ⊆ range sweep) :
      range square ∩ range (r v).val.val = orientedA '' Icc (0:Interval) s0 := by
    obtain ⟨ballSquare,hballSquare⟩ := ActualHarerDiskGluing.unit_disk_square_boundary_homeomorph
    let sd : C(Metric.closedBall (0 : Plane) 1,S) :=
      ⟨fun u => (square (ballSquare u)).val,
        continuous_subtype_val.comp (square.continuous.comp ballSquare.continuous)⟩
    have hsd : IsEmbedding sd := IsEmbedding.subtypeVal.comp (hSquare.comp ballSquare.isEmbedding)
    let tailSet : Set S := (fun t : Interval => (orientedA t).val) '' Ioc s0 1
    have htailConnected : IsPreconnected tailSet :=
      isPreconnected_Ioc.image _ (continuous_subtype_val.comp orientedA.continuous).continuousOn
    have htailAvoid : Disjoint tailSet (sd '' {y | y.val ∈ Metric.sphere (0 : Plane) 1}) := by
      apply disjoint_left.mpr
      rintro y ⟨t,ht,rfl⟩ ⟨u,hu,he⟩
      have he' : square (ballSquare u) = orientedA t := Subtype.ext he
      have hb : ballSquare u ∈ ActualHarerDiskGluing.squareBoundary :=
        hballSquare ▸ ⟨u,hu,rfl⟩
      change (ballSquare u).1 = 0 ∨ (ballSquare u).1 = 1 ∨
        (ballSquare u).2 = 0 ∨ (ballSquare u).2 = 1 at hb
      rw [← Prod.eta (ballSquare u)] at he'
      rcases hb with hb | hb | hb | hb
      · rw [hb,hleft] at he'
        have ho : orientedA t = orientedA 0 := mem_singleton_iff.mp
          (boundary_extension_old_inter ▸ ⟨⟨(ballSquare u).2,he'⟩,mem_range_self _⟩)
        exact (ne_of_gt (hs0.1.trans ht.1)) (hAinjective ho)
      · rw [hb,hright] at he'
        have heStrip : chain.oldStrip (chain.clock s0,width0 (ballSquare u).2) =
            chain.oldStrip (chain.clock t,⟨0,by norm_num⟩) := by
          rw [chain.oldStrip_center]
          exact he'
        have hsEq := chain.clock.injective (congrArg Prod.fst (chain.oldStrip_embedded.injective heStrip))
        exact (ne_of_gt ht.1) hsEq.symm
      · rw [hb,hbottom] at he'
        have hj := CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc
          (show (0:Interval) ≤ s0 from bot_le) (ballSquare u).1
        have heq := hAinjective he'
        exact (not_lt_of_ge (heq ▸ hj.2)) ht.1
      · rw [hb,htop] at he'
        let j := CurveComplex.BranchedDoubleCover.intervalAffine 0 k0 (ballSquare u).1
        have hj : j ∈ Icc (0:Interval) k0 :=
          CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc bot_le (ballSquare u).1
        have hq : orientedA t ∈ chain.q ρ '' Icc (0:Interval) z :=
          ⟨j,⟨hj.1,hj.2.trans hk0.le⟩,he'⟩
        have ho : orientedA t = orientedA chain.cut := mem_singleton_iff.mp
          (chain.changed_prefix_meets_a ρ ▸ ⟨hq,mem_range_self _⟩)
        have hjz : j = z := (chain.q_embedded ρ).injective (he'.trans (ho.trans q_at_retained_cut.symm))
        exact (not_le_of_gt hk0) (hjz ▸ hj.2)
    have htailOutside : tailSet ⊆ (range sd)ᶜ := by
      rcases RegionalEmbeddedFamily.connected_open_set_avoiding_disk_boundary_dichotomy
        tailSet htailConnected sd hsd htailAvoid with hin | hout
      · have h1 : (orientedA 1).val ∈ tailSet := ⟨1,⟨hs0.2.trans chain.cut_interior.2,le_rfl⟩,rfl⟩
        obtain ⟨u,hu⟩ := interior_subset (hin h1)
        have hu' : square (ballSquare u) = orientedA 1 := Subtype.ext hu
        exact (end_one_not_filled (hsweepRange ▸ hSquareSweep ⟨ballSquare u,hu'⟩)).elim
      · exact hout
    apply Subset.antisymm
    · rintro y ⟨⟨u,hu⟩,⟨t,ht⟩⟩
      let j : Interval := chain.clock.symm t
      have he : orientedA j = y := by simpa [orientedA,j] using ht
      by_cases hj : j ≤ s0
      · exact ⟨j,⟨bot_le,hj⟩,he⟩
      · have htj : (orientedA j).val ∈ tailSet := ⟨j,⟨lt_of_not_ge hj,le_top⟩,rfl⟩
        apply (htailOutside htj).elim
        refine ⟨ballSquare.symm u,?_⟩
        change (square (ballSquare (ballSquare.symm u))).val = _
        rw [ballSquare.apply_symm_apply]
        exact congrArg Subtype.val (hu.trans he.symm)
    · rintro y ⟨t,ht,rfl⟩
      have ht' : t ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine 0 s0) := by
        rw [affine_interval_range,uIcc_of_le (show (0:Interval) ≤ s0 from bot_le)]
        exact ht
      obtain ⟨u,hu⟩ := ht'
      exact ⟨⟨(u,0),(hbottom u).trans (congrArg orientedA hu)⟩,mem_range_self _⟩
  have transverse_glue_at
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (L R : C(Interval × Interval,↥F)) (hL : IsEmbedding L) (hR : IsEmbedding R)
    (hseam : ∀ t, L (t,1) = R (t,0))
    (hmeet : range L ∩ range R = range (fun t => L (t,1))) :
    ∃ P : C(Interval × Interval,↥F), IsEmbedding P ∧
      (∀ t u, u.val ≤ θ → P (t,u) = L (t,projIcc 0 1 zero_le_one (u.val/θ))) ∧
      (∀ t u, θ ≤ u.val → P (t,u) = R (t,projIcc 0 1 zero_le_one ((u.val-θ)/(1-θ)))) ∧
      range P = range L ∪ range R := by
    let kl (z : Interval × Interval) : Interval × Interval :=
      (z.1,projIcc 0 1 zero_le_one (z.2.val/θ))
    let kr (z : Interval × Interval) : Interval × Interval :=
      (z.1,projIcc 0 1 zero_le_one ((z.2.val-θ)/(1-θ)))
    have hleft (z : Interval × Interval) (hz : z.2.val ≤ θ) :
        (kl z).2.val = z.2.val/θ := by
      exact congrArg Subtype.val (projIcc_of_mem zero_le_one
        ⟨div_nonneg z.2.property.1 hθ.1.le,(div_le_one hθ.1).mpr hz⟩)
    have hright (z : Interval × Interval) (hz : θ ≤ z.2.val) :
        (kr z).2.val = (z.2.val-θ)/(1-θ) := by
      exact congrArg Subtype.val (projIcc_of_mem zero_le_one
        ⟨div_nonneg (sub_nonneg.mpr hz) (by linarith),
         (div_le_one (by linarith : 0 < 1-θ)).mpr (by linarith [z.2.property.2])⟩)
    have hseamL (t : Interval) (u : Interval) (hu : u.val = θ) : kl (t,u) = (t,1) := by
      apply Prod.ext
      · rfl
      apply Subtype.ext
      rw [hleft (t,u) hu.le]
      simp [hu,ne_of_gt hθ.1]
    have hseamR (t : Interval) (u : Interval) (hu : u.val = θ) : kr (t,u) = (t,0) := by
      apply Prod.ext
      · rfl
      apply Subtype.ext
      rw [hright (t,u) hu.ge]
      simp [hu]
    let P : C(Interval × Interval,↥F) :=
      ⟨fun z => if z.2.val ≤ θ then L (kl z) else R (kr z),by
        apply continuous_if_le (by fun_prop) continuous_const
          (L.continuous.comp (show Continuous kl by fun_prop)).continuousOn
          (R.continuous.comp (show Continuous kr by fun_prop)).continuousOn
        intro z hz
        change L (kl (z.1,z.2)) = R (kr (z.1,z.2))
        rw [hseamL z.1 z.2 hz,hseamR z.1 z.2 hz,hseam]⟩
    have hPleft (t u : Interval) (hu : u.val ≤ θ) : P (t,u) = L (kl (t,u)) :=
      ite_eq_left hu
    have hPright (t u : Interval) (hu : θ ≤ u.val) : P (t,u) = R (kr (t,u)) := by
      rcases hu.eq_or_lt with he | he
      · rw [hPleft t u he.ge,hseamL t u he.symm,hseamR t u he.symm,hseam]
      · exact ite_eq_right (not_le_of_gt he)
    have hPinj : Function.Injective P := by
      intro z w he
      change (if z.2.val ≤ θ then L (kl z) else R (kr z)) =
        (if w.2.val ≤ θ then L (kl w) else R (kr w)) at he
      split_ifs at he with hz hw hw
      · have hh := hL.injective he
        apply Prod.ext
        · simpa only [kl] using congrArg Prod.fst hh
        apply Subtype.ext
        have hv := congrArg (fun q : Interval × Interval => q.2.val) hh
        rw [hleft z hz,hleft w hw] at hv
        exact (div_left_inj' (ne_of_gt hθ.1)).mp hv
      · obtain ⟨t,ht⟩ := hmeet ▸ (show L (kl z) ∈ range L ∩ range R from
          ⟨mem_range_self _,⟨kr w,he.symm⟩⟩)
        have hr : R (kr w) = R (t,0) := he.symm.trans (ht.symm.trans (hseam t))
        have hv := congrArg (fun q : Interval × Interval => q.2.val) (hR.injective hr)
        rw [hright w (le_of_not_ge hw)] at hv
        change (w.2.val-θ)/(1-θ) = 0 at hv
        have : w.2.val = θ := sub_eq_zero.mp ((div_eq_zero_iff).mp hv |>.resolve_right (by linarith))
        exact (hw this.le).elim
      · obtain ⟨t,ht⟩ := hmeet ▸ (show L (kl w) ∈ range L ∩ range R from
          ⟨mem_range_self _,⟨kr z,he⟩⟩)
        have hr : R (kr z) = R (t,0) := he.trans (ht.symm.trans (hseam t))
        have hv := congrArg (fun q : Interval × Interval => q.2.val) (hR.injective hr)
        rw [hright z (le_of_not_ge hz)] at hv
        change (z.2.val-θ)/(1-θ) = 0 at hv
        have : z.2.val = θ := sub_eq_zero.mp ((div_eq_zero_iff).mp hv |>.resolve_right (by linarith))
        exact (hz this.le).elim
      · have hh := hR.injective he
        apply Prod.ext
        · simpa only [kr] using congrArg Prod.fst hh
        apply Subtype.ext
        have hv := congrArg (fun q : Interval × Interval => q.2.val) hh
        rw [hright z (le_of_not_ge hz),hright w (le_of_not_ge hw)] at hv
        have := (div_left_inj' (by linarith : 1-θ ≠ 0)).mp hv
        linarith
    refine ⟨P,(P.continuous.isClosedEmbedding hPinj).isEmbedding,hPleft,hPright,?_⟩
    apply Subset.antisymm
    · rintro y ⟨z,rfl⟩
      by_cases hz : z.2.val ≤ θ
      · exact Or.inl ⟨kl z,(hPleft z.1 z.2 hz).symm⟩
      · exact Or.inr ⟨kr z,(hPright z.1 z.2 (le_of_not_ge hz)).symm⟩
    · rintro y (⟨z,rfl⟩ | ⟨z,rfl⟩)
      · let u : Interval := ⟨θ*z.2.val,⟨mul_nonneg hθ.1.le z.2.property.1,
          (mul_le_of_le_one_right hθ.1.le z.2.property.2).trans hθ.2.le⟩⟩
        have hu : u.val ≤ θ := mul_le_of_le_one_right hθ.1.le z.2.property.2
        refine ⟨(z.1,u),(hPleft z.1 u hu).trans ?_⟩
        apply congrArg L
        apply Prod.ext
        · rfl
        apply Subtype.ext
        rw [hleft (z.1,u) hu]
        dsimp [u]
        field_simp [ne_of_gt hθ.1,show 1-θ ≠ 0 by linarith] <;> ring
      · let u : Interval := ⟨θ+(1-θ)*z.2.val,⟨by nlinarith [z.2.property.1],by nlinarith [z.2.property.2]⟩⟩
        have hu : θ ≤ u.val := by dsimp [u]; nlinarith [z.2.property.1]
        refine ⟨(z.1,u),(hPright z.1 u hu).trans ?_⟩
        apply congrArg R
        apply Prod.ext
        · rfl
        apply Subtype.ext
        rw [hright (z.1,u) hu]
        dsimp [u]
        field_simp [ne_of_gt hθ.1,show 1-θ ≠ 0 by linarith] <;> ring
  -- A6 is derived from the oriented marked strip; no clock witness is assumed.
  suffices oriented_marked_strip_remaining :
    ∃ Ehat : C(Interval × Icc (-1 : ℝ) 1,↥F),
      IsEmbedding Ehat ∧
      (∀ t, Ehat (t,⟨0,by norm_num⟩) = orientedA t) ∧
      (∀ u, (Ehat (0,u)).val ∈ boundaryCircle ∧ (Ehat (1,u)).val ∈ boundaryCircle) ∧
      (∀ t ∈ Ioo (0 : Interval) 1, ∀ u, (Ehat (t,u)).val ∈ interior F) ∧
      IsOpen (Ehat '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) ∧
      ∃ (εhat : C(Interval,ℝ)) (hεhat : ∀ t, 0 ≤ εhat t ∧ εhat t < 1),
        range (chain.q ρ) = range (fun t => Ehat
          (t,⟨εhat t,⟨by linarith [(hεhat t).1],(hεhat t).2.le⟩⟩)) ∧
        (∀ t, εhat t ≠ 0 → ∀ u, Ehat (t,u) ∈ V) ∧
        (∀ t ∈ Icc chain.cut (1 : Interval), εhat t = 0) by
    obtain ⟨Ehat,hEhat,hcenter,hends,hinterior,hopen,εhat,hεhat,hrange,hactive,hretained⟩ :=
      oriented_marked_strip_remaining
    let graph : C(Interval,↥F) := ⟨fun t => Ehat
      (t,⟨εhat t,⟨by linarith [(hεhat t).1],(hεhat t).2.le⟩⟩),by fun_prop⟩
    have hgraph : IsEmbedding graph :=
      (graph.continuous.isClosedEmbedding (by
        intro t u he
        exact congrArg Prod.fst (hEhat.injective he))).isEmbedding
    change range (chain.q ρ) = range graph at hrange
    let νhat : Interval ≃ₜ Interval :=
      (hgraph.toHomeomorph.trans (Homeomorph.setCongr hrange.symm)).trans
        (chain.q_embedded ρ).toHomeomorph.symm
    have hνhat (t : Interval) : chain.q ρ (νhat t) = graph t :=
      congrArg Subtype.val ((chain.q_embedded ρ).toHomeomorph.apply_symm_apply
        ((Homeomorph.setCongr hrange.symm) (hgraph.toHomeomorph t)))
    have hεhat1 : εhat 1 = 0 := hretained 1 ⟨le_top,le_rfl⟩
    have hgraph1 : graph 1 = orientedA 1 := by
      change Ehat (1,_) = _
      convert hcenter 1 using 1
      exact congrArg (fun u => Ehat (1,u)) (Subtype.ext hεhat1)
    have hνhat1 : νhat 1 = 1 :=
      (chain.q_embedded ρ).injective ((hνhat 1).trans (hgraph1.trans (chain.q_one ρ).symm))
    have hνhat0 : νhat 0 = 0 := by
      rcases interval_clock_orientation νhat with ⟨_,h0,_⟩ | ⟨_,_,h1⟩
      · exact h0
      · have bad : (0 : Interval) = 1 := h1.symm.trans hνhat1
        norm_num at bad
    let clockProd : (Interval × Icc (-1 : ℝ) 1) ≃ₜ (Interval × Icc (-1 : ℝ) 1) :=
      chain.clock.symm.prodCongr (Homeomorph.refl _)
    let E : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
      ⟨fun z => Ehat (chain.clock.symm z.1,z.2),by fun_prop⟩
    have hE : IsEmbedding E := hEhat.comp clockProd.isEmbedding
    let ε : C(Interval,ℝ) := ⟨fun t => εhat (chain.clock.symm t),by fun_prop⟩
    have hε (t : Interval) : 0 ≤ ε t ∧ ε t < 1 := hεhat (chain.clock.symm t)
    have hEcenter (t : Interval) : E (t,⟨0,by norm_num⟩) = (r v).val.val t := by
      change Ehat (chain.clock.symm t,_) = _
      simpa only [orientedA,ContinuousMap.coe_comp,Function.comp_apply,ContinuousMap.coe_mk,Homeomorph.apply_symm_apply] using
        hcenter (chain.clock.symm t)
    have hEends (u : Icc (-1:ℝ) 1) :
        (E (0,u)).val ∈ boundaryCircle ∧ (E (1,u)).val ∈ boundaryCircle := by
      rcases interval_clock_orientation chain.clock.symm with ⟨_,h0,h1⟩ | ⟨_,h0,h1⟩
      · simpa only [E,ContinuousMap.coe_mk,h0,h1] using hends u
      · simpa only [E,ContinuousMap.coe_mk,h0,h1] using (hends u).symm
    have hEinterior (t : Interval) (ht : t ∈ Ioo (0:Interval) 1) (u : Icc (-1:ℝ) 1) :
        (E (t,u)).val ∈ interior F := by
      apply hinterior
      rcases interval_clock_orientation chain.clock.symm with ⟨hm,h0,h1⟩ | ⟨ha,h0,h1⟩
      · constructor
        · simpa only [h0] using hm ht.1
        · simpa only [h1] using hm ht.2
      · constructor
        · simpa only [h1] using ha ht.2
        · simpa only [h0] using ha ht.1
    have hcore : E '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1} =
        Ehat '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1} := by
      apply Subset.antisymm
      · rintro y ⟨z,hz,rfl⟩
        exact ⟨(chain.clock.symm z.1,z.2),hz,rfl⟩
      · rintro y ⟨z,hz,rfl⟩
        refine ⟨(chain.clock z.1,z.2),hz,?_⟩
        simp only [E,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply]
    have hGraphRange : range (chain.q ρ) = range (fun t => E
        (t,⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩)) := by
      rw [hrange]
      apply Subset.antisymm
      · rintro y ⟨t,rfl⟩
        refine ⟨chain.clock t,?_⟩
        simp only [E,ε,graph,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply]
      · rintro y ⟨t,rfl⟩
        exact ⟨chain.clock.symm t,rfl⟩
    have hActive (t : Interval) (ht : ε t ≠ 0) (u : Icc (-1:ℝ) 1) : E (t,u) ∈ V :=
      hactive (chain.clock.symm t) ht u
    have hRetained (t : Interval) (ht : t ∈ Icc chain.cut (1:Interval)) :
        ε (chain.clock t) = 0 := by
      simpa only [ε,ContinuousMap.coe_mk,Homeomorph.symm_apply_apply] using hretained t ht
    let ν : Interval ≃ₜ Interval := chain.clock.symm.trans νhat
    have hνStart : ν d.aStart = 0 := by
      change νhat (chain.clock.symm d.aStart) = 0
      rw [← chain.clock_start,chain.clock.symm_apply_apply]
      exact hνhat0
    have hνEnd : ν (chain.clock 1) = 1 := by
      change νhat (chain.clock.symm (chain.clock 1)) = 1
      rw [chain.clock.symm_apply_apply]
      exact hνhat1
    have hGraph (t : Interval) : chain.q ρ (ν t) = E
        (t,⟨ε t,⟨by linarith [(hε t).1],(hε t).2.le⟩⟩) := hνhat (chain.clock.symm t)
    refine ⟨E,hE,hEcenter,hEends,hEinterior,hcore ▸ hopen,ε,hε,hGraphRange,hActive,hRetained,
      ν,hνStart,hνEnd,hGraph,sweep,hsweep,hsweepV,hdSweep,hsweepCeiling,?_,hsweepFrontier⟩
    simpa only [orientedA,ContinuousMap.coe_comp,ContinuousMap.coe_mk,image_comp,z] using hsweepSphere
  -- Consume the repaired paid A3 on the very same A2 sweep and both caller obligations.
  obtain ⟨sCap,rCap,hscCap,hsPrev,hcR,hr1,hwindow,τCap,hCap,kCap,hhCap,
    hxCap,hyCap,hτ0,hτ1,hτEnd,hτMono,hkEnd,hkMono,hk0,hklt,hkFormula,
    hcapGraph,hcapEnd,hcapPos,hcapAnti,hcapHull,κ,port,Rplus,hκ,hportTotal,
    hport,hRplus,hRplusV,hRplusBottom,hRplusBoundary,hRplusInterior,hRplusRight,
    hRplusSweep,hRplusNegative,hRplusOld,tGerm,htGerm,hRplusGerm⟩ :=
    regional_half_q_prefix_exterior_collar_with_cap_port S g hg hS x R hR htarget
      F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint
      hfrontier ι r α hinv hcross v w hvw d V hV hdV havoid hcheap fan gap chain ρ
      sweep hsweep hsweepRange hsweepV hdSweep hsweepCeiling hsweepSphere
      hsweepFrontier hnegativeSweep hwholeOldSweep
  let leftCap : Icc sCap chain.cut := ⟨sCap,⟨le_rfl,hscCap.le⟩⟩
  let rightCap : Icc sCap chain.cut := ⟨chain.cut,⟨hscCap.le,le_rfl⟩⟩
  have hsCap0 : 0 < sCap := (show (0:Interval) ≤ chain.clock.symm d.aFinish from bot_le).trans_lt hsPrev
  have hsCapW : sCap ∈ chain.oldCornerWindow := hwindow ⟨le_rfl,hscCap.le.trans hcR.le⟩
  have hhCap0 : 0 < hCap leftCap := hcapPos leftCap hscCap
  have hhCapWidth : hCap leftCap < chain.oldCornerWidth := by linarith
  have hxCap0 : -chain.cornerDelta+(1-(τCap leftCap).val)*(L+chain.cornerDelta) =
      chain.oldCornerX sCap := by
    have hx := hxCap leftCap
    dsimp only [leftCap] at hx
    dsimp only [L]
    nlinarith
  have hsign : chain.oldCornerSign ≠ 0 := by
    rcases chain.oldCornerSign_unit with h | h <;> rw [h] <;> norm_num
  have hyCap0 : chain.cornerEntry 1*(1-(τCap leftCap).val) =
      chain.oldCornerSign*chain.oldCornerScale*hCap leftCap := by
    have hy := (eq_div_iff (mul_ne_zero hsign (ne_of_gt chain.oldCornerScale_pos))).mp (hyCap leftCap)
    nlinarith
  let capPort : C(Interval,Icc (-1:ℝ) 1) :=
    ⟨fun u => ⟨hCap leftCap*u.val,⟨by nlinarith [u.property.1],
      (mul_le_of_le_one_right hhCap0.le u.property.2).trans (hhCap leftCap).2.le⟩⟩,by fun_prop⟩
  have hcapPort (u : Interval) : (capPort u).val = hCap leftCap*u.val := rfl
  have hcapPortHull (u : Interval) : chain.oldStrip (chain.clock sCap,capPort u) ∈ cornerCarrier :=
    hcapHull leftCap (capPort u) (mul_nonneg hhCap0.le u.property.1)
      (mul_le_of_le_one_right hhCap0.le u.property.2)
  have hcapPortGraph : chain.q ρ (kCap leftCap) = chain.oldStrip (chain.clock sCap,capPort 1) := by
    convert hcapGraph leftCap using 1 <;> simp [leftCap,capPort]
  obtain ⟨capSquare,hcapSquare,hcapBottom,hcapTop,hcapLeft,hcapRight,hcapSquareSweep⟩ :=
    cap_rectangle_in_actual_sweep sCap (τCap leftCap) (kCap leftCap) (hCap leftCap)
      hsCap0 hscCap hsCapW ⟨hτ0,hτ1⟩ hk0 hklt ⟨hhCap0,hhCapWidth⟩ hxCap0 hyCap0
      (hkFormula leftCap) capPort hcapPort hcapPortHull hcapPortGraph
  have hcapSquareOld : range capSquare ∩ range (r v).val.val =
      orientedA '' Icc (0:Interval) sCap :=
    cap_rectangle_whole_old sCap (kCap leftCap) ⟨hsCap0,hscCap⟩ hklt capPort capSquare
      hcapSquare hcapBottom hcapTop hcapLeft hcapRight hcapSquareSweep
  have cap_q_prefix_range : range (fun t => capSquare (t,1)) =
      chain.q ρ '' Icc (0:Interval) (kCap leftCap) := by
    simp_rw [hcapTop]
    change range ((chain.q ρ) ∘ CurveComplex.BranchedDoubleCover.intervalAffine 0 (kCap leftCap)) = _
    rw [range_comp,affine_interval_range,uIcc_of_le (show (0:Interval) ≤ kCap leftCap from bot_le)]
  have cap_outer_seam (t : Interval) : capSquare (t,1) = Rplus (t,0) :=
    (hcapTop t).trans (hRplusBottom t).symm
  have cap_outer_inter : range capSquare ∩ range Rplus = range (fun t => capSquare (t,1)) := by
    apply Subset.antisymm
    · rintro y ⟨hS,hP⟩
      rw [cap_q_prefix_range]
      exact hRplusSweep ▸ ⟨hP,hcapSquareSweep hS⟩
    · rintro y ⟨t,rfl⟩
      exact ⟨mem_range_self _,⟨(t,0),(cap_outer_seam t).symm⟩⟩
  let pCap : ℝ := hCap leftCap+κ
  have hpCap0 : 0 < pCap := add_pos hhCap0 hκ
  have hpCap1 : pCap < 1 := hportTotal.trans chain.oldCornerWidth_lt_one
  let θCap : ℝ := hCap leftCap/pCap
  have hθCap : 0 < θCap ∧ θCap < 1 :=
    ⟨div_pos hhCap0 hpCap0,(div_lt_one hpCap0).mpr (by dsimp [pCap]; linarith)⟩
  obtain ⟨Pplus,hPplus,hPplusLower,hPplusUpper,hPplusRange⟩ :=
    transverse_glue_at θCap hθCap capSquare Rplus hcapSquare hRplus cap_outer_seam cap_outer_inter
  have hPplus0 (t : Interval) : Pplus (t,0) =
      orientedA (CurveComplex.BranchedDoubleCover.intervalAffine 0 sCap t) := by
    rw [hPplusLower t 0 hθCap.1.le]
    simpa using hcapBottom t
  have hPplusMarked (t : Interval) : Pplus (t,⟨θCap,hθCap.1.le,hθCap.2.le⟩) =
      chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 (kCap leftCap) t) := by
    rw [hPplusLower t _ le_rfl]
    simpa [ne_of_gt hθCap.1] using hcapTop t
  have hPplusV : range Pplus ⊆ V := by
    rw [hPplusRange]
    exact union_subset (hcapSquareSweep.trans hsweepV) hRplusV
  have hcapSquareBoundary (u : Interval) : (capSquare (0,u)).val ∈ boundaryCircle := by
    rw [hcapLeft]
    exact (chain.boundaryExtension_in_BV ρ (mem_range_self u)).1
  have hcapSquareInterior (t : Interval) (ht : 0 < t) (u : Interval) :
      (capSquare (t,u)).val ∈ interior F := by
    apply (mem_interior_iff_notMem_frontier (capSquare (t,u)).property).mpr
    intro hb
    obtain ⟨w,hw⟩ := hsweepFrontier ▸ (show capSquare (t,u) ∈
        range sweep ∩ {y : ↥F | y.val ∈ frontier F} from
      ⟨hcapSquareSweep (mem_range_self _),hb⟩)
    have he : capSquare (t,u) = capSquare (0,w) := hw.symm.trans (hcapLeft w).symm
    exact ht.ne' (congrArg Prod.fst (hcapSquare.injective he))
  have hPplusBoundary (u : Interval) : (Pplus (0,u)).val ∈ boundaryCircle := by
    by_cases hu : u.val ≤ θCap
    · rw [hPplusLower 0 u hu]
      exact hcapSquareBoundary _
    · rw [hPplusUpper 0 u (le_of_not_ge hu)]
      exact hRplusBoundary _
  have hPplusInterior (t : Interval) (ht : 0 < t) (u : Interval) :
      (Pplus (t,u)).val ∈ interior F := by
    by_cases hu : u.val ≤ θCap
    · rw [hPplusLower t u hu]
      exact hcapSquareInterior t ht _
    · rw [hPplusUpper t u (le_of_not_ge hu)]
      exact hRplusInterior t ht _
  let plusWidth (u : Interval) : Icc (-1:ℝ) 1 :=
    ⟨pCap*u.val,⟨by nlinarith [u.property.1],
      (mul_le_of_le_one_right hpCap0.le u.property.2).trans hpCap1.le⟩⟩
  have hθidentity : θCap*pCap = hCap leftCap := div_mul_cancel₀ _ (ne_of_gt hpCap0)
  have hPplusRight (u : Interval) : Pplus (1,u) = chain.oldStrip (chain.clock sCap,plusWidth u) := by
    by_cases hu : u.val ≤ θCap
    · rw [hPplusLower 1 u hu,hcapRight]
      apply congrArg (fun w => chain.oldStrip (chain.clock sCap,w))
      apply Subtype.ext
      rw [hcapPort,projIcc_of_mem zero_le_one
        ⟨div_nonneg u.property.1 hθCap.1.le,(div_le_one hθCap.1).mpr hu⟩]
      change hCap leftCap*(u.val/θCap) = pCap*u.val
      rw [← mul_div_assoc]
      apply (div_eq_iff (ne_of_gt hθCap.1)).mpr
      nlinarith [hθidentity]
    · rw [hPplusUpper 1 u (le_of_not_ge hu),hRplusRight]
      apply congrArg (fun w => chain.oldStrip (chain.clock sCap,w))
      apply Subtype.ext
      rw [hport,projIcc_of_mem zero_le_one
        ⟨div_nonneg (by linarith) (by linarith),
          (div_le_one (by linarith : 0 < 1-θCap)).mpr (by linarith [u.property.2])⟩]
      change hCap leftCap+κ*((u.val-θCap)/(1-θCap)) = pCap*u.val
      have hp : pCap = hCap leftCap+κ := rfl
      field_simp [show 1-θCap ≠ 0 by linarith]
      nlinarith [hθidentity]
  have hPplusOld : range Pplus ∩ range (r v).val.val = orientedA '' Icc (0:Interval) sCap := by
    rw [hPplusRange,union_inter_distrib_right,hcapSquareOld,hRplusOld.inter_eq,union_empty]
  let ηCap : ℝ := chain.oldNegativeWidth/2
  have hηCap0 : 0 < ηCap := half_pos chain.oldNegativeWidth_pos
  have hηCapWidth : ηCap < chain.oldNegativeWidth := half_lt_self chain.oldNegativeWidth_pos
  have hηCap1 : ηCap < 1 := hηCapWidth.trans
    (chain.oldNegativeWidth_lt_corner.trans chain.oldCornerWidth_lt_one)
  let segCap : C(Interval,Interval) := CurveComplex.BranchedDoubleCover.intervalSegment 0 sCap
  have hsegCap (t : Interval) : (segCap t).val = t.val*sCap.val := by
    change (1-t.val)*0+t.val*sCap.val = _
    ring
  have hsegCapRange : range segCap = Icc (0:Interval) sCap := by
    change range (CurveComplex.BranchedDoubleCover.intervalAffine 0 sCap) = _
    rw [affine_interval_range,uIcc_of_le (show (0:Interval) ≤ sCap from bot_le)]
  have hsegCapInj : Function.Injective segCap := by
    intro t u he
    have he' := congrArg Subtype.val he
    rw [hsegCap,hsegCap] at he'
    exact Subtype.ext (mul_right_cancel₀ (ne_of_gt (show (0:ℝ) < sCap.val from hsCap0)) he')
  let negWidth (u : Interval) : Icc (-1:ℝ) 1 :=
    ⟨ηCap*(u.val-1),⟨by nlinarith [u.property.1],by nlinarith [u.property.2]⟩⟩
  let Nminus : C(Interval × Interval,↥F) :=
    ⟨fun z => chain.oldStrip (chain.clock (segCap z.1),negWidth z.2),by fun_prop⟩
  have hNminus : IsEmbedding Nminus :=
    (Nminus.continuous.isClosedEmbedding (by
      intro z w he
      have hp := chain.oldStrip_embedded.injective he
      apply Prod.ext
      · exact hsegCapInj (chain.clock.injective (congrArg Prod.fst hp))
      · apply Subtype.ext
        have hh := congrArg (fun u : Interval × Icc (-1:ℝ) 1 => u.2.val) hp
        change ηCap*(z.2.val-1) = ηCap*(w.2.val-1) at hh
        nlinarith [hηCap0])).isEmbedding
  have hNminusTop (t : Interval) : Nminus (t,1) = orientedA (segCap t) := by
    have hw : negWidth 1 = ⟨0,by norm_num⟩ := by apply Subtype.ext; simp [negWidth]
    change chain.oldStrip (_,_) = (r v).val.val (chain.clock (segCap t))
    rw [hw,chain.oldStrip_center]
  have hNminusNegative : range Nminus ⊆ oldNegative := by
    rintro y ⟨z,rfl⟩
    refine ⟨(chain.clock (segCap z.1),negWidth z.2),⟨?_,?_,?_⟩,rfl⟩
    · have hseg := hsegCapRange ▸ mem_range_self (f := segCap) z.1
      exact ⟨segCap z.1,⟨hseg.1,hseg.2.trans hscCap.le⟩,rfl⟩
    · change -chain.oldNegativeWidth ≤ ηCap*(z.2.val-1)
      nlinarith [z.2.property.1]
    · change ηCap*(z.2.val-1) ≤ 0
      nlinarith [z.2.property.2]
  have hNminusV : range Nminus ⊆ V := hNminusNegative.trans old_negative_in_V
  have hNminusTopRange : range (fun t => Nminus (t,1)) = orientedA '' Icc (0:Interval) sCap := by
    simp_rw [hNminusTop]
    change range (orientedA ∘ segCap) = _
    rw [range_comp,hsegCapRange]
  have negative_positive_seam (t : Interval) : Nminus (t,1) = Pplus (t,0) :=
    (hNminusTop t).trans (hPplus0 t).symm
  have negative_positive_inter : range Nminus ∩ range Pplus = range (fun t => Nminus (t,1)) := by
    apply Subset.antisymm
    · rintro y ⟨hn,hp⟩
      rw [hPplusRange] at hp
      rcases hp with hs | hr
      · have ha : y ∈ orientedA '' Icc (0:Interval) chain.cut :=
          hnegativeSweep ▸ ⟨hNminusNegative hn,hcapSquareSweep hs⟩
        have haWhole : y ∈ range (r v).val.val := by
          obtain ⟨t,_,ht⟩ := ha
          exact ⟨chain.clock t,ht⟩
        rw [hNminusTopRange]
        exact hcapSquareOld ▸ ⟨hs,haWhole⟩
      · exact (disjoint_left.mp hRplusNegative hr (hNminusNegative hn)).elim
    · rintro y ⟨t,rfl⟩
      exact ⟨mem_range_self _,⟨(t,0),(negative_positive_seam t).symm⟩⟩
  obtain ⟨Punit,hPunit,hPunitLower,hPunitUpper,hPunitRange⟩ :=
    transverse_glue_at (1/2) (by norm_num) Nminus Pplus hNminus hPplus
      negative_positive_seam negative_positive_inter
  let unitWidth (u : Icc (-1:ℝ) 1) : Interval :=
    ⟨(u.val+1)/2,⟨by linarith [u.property.1],by linarith [u.property.2]⟩⟩
  let Pstar : C(Interval × Icc (-1:ℝ) 1,↥F) :=
    ⟨fun z => Punit (z.1,unitWidth z.2),by fun_prop⟩
  have hPstar : IsEmbedding Pstar :=
    (Pstar.continuous.isClosedEmbedding (by
      intro z w he
      have hp := hPunit.injective he
      apply Prod.ext
      · simpa only using congrArg Prod.fst hp
      · apply Subtype.ext
        have hh := congrArg (fun u : Interval × Interval => u.2.val) hp
        change (z.2.val+1)/2 = (w.2.val+1)/2 at hh
        linarith)).isEmbedding
  have hPstarRange : range Pstar = range Nminus ∪ range Pplus := by
    rw [← hPunitRange]
    apply Subset.antisymm
    · rintro y ⟨z,rfl⟩
      exact mem_range_self (z.1,unitWidth z.2)
    · rintro y ⟨z,rfl⟩
      let u : Icc (-1:ℝ) 1 := ⟨2*z.2.val-1,⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩⟩
      refine ⟨(z.1,u),?_⟩
      apply congrArg Punit
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        change (2*z.2.val-1+1)/2 = z.2.val
        ring
  have hPstarV : range Pstar ⊆ V := by
    rw [hPstarRange]
    exact union_subset hNminusV hPplusV
  have hPstarNonneg (t : Interval) (u : Icc (-1:ℝ) 1) (hu : 0 ≤ u.val) :
      Pstar (t,u) = Pplus (t,⟨u.val,hu,u.property.2⟩) := by
    change Punit (t,unitWidth u) = _
    rw [hPunitUpper t (unitWidth u) (by dsimp [unitWidth]; linarith)]
    have he : ((unitWidth u).val-1/2)/(1-1/2) = u.val := by dsimp [unitWidth]; ring
    rw [he,projIcc_of_mem zero_le_one ⟨hu,u.property.2⟩]
  let negActualWidth (u : Icc (-1:ℝ) 1) : Icc (-1:ℝ) 1 :=
    ⟨ηCap*u.val,⟨by nlinarith [u.property.1],by nlinarith [u.property.2]⟩⟩
  have hPstarNonpos (t : Interval) (u : Icc (-1:ℝ) 1) (hu : u.val ≤ 0) :
      Pstar (t,u) = chain.oldStrip (chain.clock (segCap t),negActualWidth u) := by
    change Punit (t,unitWidth u) = _
    rw [hPunitLower t (unitWidth u) (by dsimp [unitWidth]; linarith)]
    have he : (unitWidth u).val/(1/2) = u.val+1 := by dsimp [unitWidth]; ring
    rw [he,projIcc_of_mem zero_le_one ⟨by linarith [u.property.1],by linarith⟩]
    change chain.oldStrip (_,_) = _
    apply congrArg (fun w => chain.oldStrip (chain.clock (segCap t),w))
    apply Subtype.ext
    change ηCap*(u.val+1-1) = ηCap*u.val
    ring
  have hPstarCenter (t : Interval) : Pstar (t,⟨0,by norm_num⟩) = orientedA (segCap t) := by
    rw [hPstarNonneg t _ (by norm_num)]
    exact hPplus0 t
  have hPstarMarked (t : Interval) : Pstar (t,⟨θCap,by constructor <;> linarith [hθCap.1,hθCap.2]⟩) =
      chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 (kCap leftCap) t) := by
    rw [hPstarNonneg t _ hθCap.1.le]
    exact hPplusMarked t
  have hNminusBoundary (u : Interval) : (Nminus (0,u)).val ∈ boundaryCircle := by
    have hs0 : segCap 0 = 0 := by apply Subtype.ext; rw [hsegCap]; simp
    change (chain.oldStrip (chain.clock (segCap 0),negWidth u)).val ∈ _
    rw [hs0]
    rcases old_clock_orientation with ⟨_,h0,_⟩ | ⟨_,h0,_⟩
    · rw [chain.clock_start,h0]
      exact (chain.oldStrip_ends _).1
    · rw [chain.clock_start,h0]
      exact (chain.oldStrip_ends _).2
  have hNminusInterior (t : Interval) (ht : 0 < t) (u : Interval) :
      (Nminus (t,u)).val ∈ interior F := by
    apply chain.oldStrip_interior
    have hs0 : (0:Interval) < segCap t := by
      change (0:ℝ) < (segCap t).val
      rw [hsegCap]
      exact mul_pos ht hsCap0
    have hs1 : segCap t < (1:Interval) :=
      ((hsegCapRange ▸ mem_range_self (f := segCap) t).2).trans_lt (hscCap.trans chain.cut_interior.2)
    rcases old_clock_orientation with ⟨hm,h0,h1⟩ | ⟨ha,h0,h1⟩
    · constructor
      · simpa only [chain.clock_start,h0] using hm hs0
      · simpa only [h1] using hm hs1
    · constructor
      · simpa only [h1] using ha hs1
      · simpa only [chain.clock_start,h0] using ha hs0
  have hPstarBoundary (u : Icc (-1:ℝ) 1) : (Pstar (0,u)).val ∈ boundaryCircle := by
    change (Punit (0,unitWidth u)).val ∈ _
    by_cases hu : (unitWidth u).val ≤ 1/2
    · rw [hPunitLower 0 _ hu]
      exact hNminusBoundary _
    · rw [hPunitUpper 0 _ (le_of_not_ge hu)]
      exact hPplusBoundary _
  have hPstarInterior (t : Interval) (ht : 0 < t) (u : Icc (-1:ℝ) 1) :
      (Pstar (t,u)).val ∈ interior F := by
    change (Punit (t,unitWidth u)).val ∈ _
    by_cases hu : (unitWidth u).val ≤ 1/2
    · rw [hPunitLower t _ hu]
      exact hNminusInterior t ht _
    · rw [hPunitUpper t _ (le_of_not_ge hu)]
      exact hPplusInterior t ht _
  let fullPort (u : Icc (-1:ℝ) 1) : Icc (-1:ℝ) 1 :=
    ⟨if u.val ≤ 0 then ηCap*u.val else pCap*u.val,by
      split_ifs with hu
      · constructor <;> nlinarith [u.property.1,u.property.2]
      · constructor <;> nlinarith [u.property.1,u.property.2]⟩
  have hPstarRight (u : Icc (-1:ℝ) 1) : Pstar (1,u) = chain.oldStrip (chain.clock sCap,fullPort u) := by
    by_cases hu : u.val ≤ 0
    · rw [hPstarNonpos 1 u hu]
      have hs1 : segCap 1 = sCap := by apply Subtype.ext; rw [hsegCap]; simp
      rw [hs1]
      congr 1
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp only [fullPort,negActualWidth,ite_eq_left hu]
    · rw [hPstarNonneg 1 u (le_of_not_ge hu),hPplusRight]
      congr 1
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp only [fullPort,plusWidth,ite_eq_right hu]
  have hNminusOld : range Nminus ∩ range (r v).val.val = orientedA '' Icc (0:Interval) sCap := by
    apply Subset.antisymm
    · rintro y ⟨⟨u,hu⟩,⟨t,ht⟩⟩
      have he : chain.oldStrip (chain.clock (segCap u.1),negWidth u.2) = chain.oldStrip (t,⟨0,by norm_num⟩) :=
        hu.trans (ht.symm.trans (chain.oldStrip_center t).symm)
      have ht' := congrArg Prod.fst (chain.oldStrip_embedded.injective he)
      change chain.clock (segCap u.1) = t at ht'
      refine ⟨segCap u.1,hsegCapRange ▸ mem_range_self _,?_⟩
      change (r v).val.val (chain.clock (segCap u.1)) = y
      rw [ht']
      exact ht
    · rintro y ⟨t,ht,rfl⟩
      obtain ⟨u,hu⟩ := hsegCapRange.symm ▸ ht
      exact ⟨⟨(u,1),(hNminusTop u).trans (congrArg orientedA hu)⟩,mem_range_self _⟩
  have hPstarOld : range Pstar ∩ range (r v).val.val = orientedA '' Icc (0:Interval) sCap := by
    rw [hPstarRange,union_inter_distrib_right,hNminusOld,hPplusOld,union_self]
  -- The entire prescribed cap band, its q graph, retained zero, and full V support.
  have hfullPortContinuous : Continuous fullPort := by
    apply Continuous.subtype_mk
    apply continuous_if_le continuous_subtype_val continuous_const
      (by fun_prop) (by fun_prop)
    intro u hu
    simp only [hu,mul_zero]
  have hfullPortInj : Function.Injective fullPort := by
    intro u w he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    change (if u.val ≤ 0 then ηCap*u.val else pCap*u.val) =
      (if w.val ≤ 0 then ηCap*w.val else pCap*w.val) at he'
    split_ifs at he' with hu hw hw <;> nlinarith [hηCap0,hpCap0]
  let capBand : C(Icc sCap chain.cut × Icc (-1:ℝ) 1,↥F) :=
    ⟨fun z => chain.oldStrip (chain.clock z.1.val,fullPort z.2),
      chain.oldStrip.continuous.comp ((chain.clock.continuous.comp
        (continuous_subtype_val.comp continuous_fst)).prodMk
          (hfullPortContinuous.comp continuous_snd))⟩
  have hcapBand : IsEmbedding capBand :=
    (capBand.continuous.isClosedEmbedding (by
      intro u w he
      have hh := chain.oldStrip_embedded.injective he
      apply Prod.ext
      · exact Subtype.ext (chain.clock.injective (congrArg Prod.fst hh))
      · exact hfullPortInj (congrArg Prod.snd hh))).isEmbedding
  have hcapBandSeam (u : Icc (-1:ℝ) 1) : capBand (leftCap,u) = Pstar (1,u) :=
    (hPstarRight u).symm
  have hcapBandV (t : Icc sCap chain.cut) (u : Icc (-1:ℝ) 1) : capBand (t,u) ∈ V :=
    chain.oldStrip_full_active_fibers (chain.clock t.val)
      (chain.oldCornerWindow_active (hwindow ⟨t.property.1,t.property.2.trans hcR.le⟩)) _
  let εCap : C(Icc sCap chain.cut,ℝ) := ⟨fun t => hCap t/pCap,by fun_prop⟩
  have hεCap (t : Icc sCap chain.cut) : 0 ≤ εCap t ∧ εCap t ≤ θCap := by
    have ht : leftCap ≤ t := t.property.1
    exact ⟨div_nonneg (hhCap t).1 hpCap0.le,
      (div_le_div_iff_of_pos_right hpCap0).mpr (hcapAnti.antitone ht)⟩
  have hεCap_lt (t : Icc sCap chain.cut) : εCap t < 1 := (hεCap t).2.trans_lt hθCap.2
  have hεCapStart : εCap leftCap = θCap := rfl
  have hεCapEnd : εCap rightCap = 0 := by change hCap rightCap/pCap = 0; rw [hcapEnd,zero_div]
  have hεCapWidth (t : Icc sCap chain.cut) :
      fullPort ⟨εCap t,⟨by linarith [(hεCap t).1],(hεCap_lt t).le⟩⟩ =
        ⟨hCap t,⟨by linarith [(hhCap t).1],(hhCap t).2.le⟩⟩ := by
    apply Subtype.ext
    by_cases hz : hCap t = 0
    · simp [fullPort,εCap,hz]
    · have hh : 0 < hCap t := lt_of_le_of_ne (hhCap t).1 (Ne.symm hz)
      have he : 0 < εCap t := div_pos hh hpCap0
      change (if εCap t ≤ 0 then ηCap*εCap t else pCap*εCap t) = _
      rw [ite_eq_right (not_le_of_gt he)]
      change pCap*(hCap t/pCap) = hCap t
      field_simp [ne_of_gt hpCap0]
  have hcapBandGraph (t : Icc sCap chain.cut) : chain.q ρ (kCap t) =
      capBand (t,⟨εCap t,⟨by linarith [(hεCap t).1],(hεCap_lt t).le⟩⟩) := by
    change chain.q ρ (kCap t) = chain.oldStrip (chain.clock t.val,_)
    rw [hεCapWidth]
    exact hcapGraph t
  -- T0: full retained-center and negative-cap clearance in the actual old strip.
  have tail_center_clear (t : Interval) (ht : sCap < t) :
      chain.oldStrip (chain.clock t,⟨0,by norm_num⟩) ∉ range Pstar := by
    rw [chain.oldStrip_center]
    intro h
    obtain ⟨j,hj,he⟩ := hPstarOld ▸ (show orientedA t ∈ range Pstar ∩ range (r v).val.val from
      ⟨h,mem_range_self _⟩)
    exact (not_le_of_gt ht) ((hAinjective he) ▸ hj.2)
  have old_tail_negative_clear (t : Interval) (ht : sCap < t) (htc : t ≤ chain.cut)
      (u : Icc (-1:ℝ) 1) (hu0 : -ηCap ≤ u.val) (hu1 : u.val ≤ 0) :
      chain.oldStrip (chain.clock t,u) ∉ range Pstar := by
    by_cases hz : u.val = 0
    · have hu : u = ⟨0,by norm_num⟩ := Subtype.ext hz
      rw [hu]
      exact tail_center_clear t ht
    have hn : chain.oldStrip (chain.clock t,u) ∈ oldNegative :=
      ⟨(chain.clock t,u),⟨⟨t,⟨bot_le,htc⟩,rfl⟩,by linarith [hηCapWidth],hu1⟩,rfl⟩
    intro hp
    rw [hPstarRange,hPplusRange] at hp
    rcases hp with ⟨z,hz'⟩ | hS | hR
    · have he := chain.clock.injective (congrArg Prod.fst (chain.oldStrip_embedded.injective hz'))
      change segCap z.1 = t at he
      have hj := (hsegCapRange ▸ mem_range_self (f := segCap) z.1).2
      exact (not_le_of_gt ht) (he ▸ hj)
    · have hcent : chain.oldStrip (chain.clock t,u) ∈ orientedA '' Icc (0:Interval) chain.cut :=
        hnegativeSweep ▸ ⟨hn,hcapSquareSweep hS⟩
      obtain ⟨j,_,hj⟩ := hcent
      have he : chain.oldStrip (chain.clock j,⟨0,by norm_num⟩) = chain.oldStrip (chain.clock t,u) :=
        (chain.oldStrip_center _).trans hj
      have hw := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => z.2.val)
        (chain.oldStrip_embedded.injective he)
      exact hz hw.symm
    · exact disjoint_left.mp hRplusNegative hR hn
  have old_after_seam_misses_Nminus (t : Interval) (ht : sCap < t) (u : Icc (-1:ℝ) 1) :
      chain.oldStrip (chain.clock t,u) ∉ range Nminus := by
    rintro ⟨z,hz⟩
    have he := chain.clock.injective (congrArg Prod.fst (chain.oldStrip_embedded.injective hz))
    change segCap z.1 = t at he
    exact (not_le_of_gt ht) (he ▸ (hsegCapRange ▸ mem_range_self (f := segCap) z.1).2)
  have old_cap_fiber_interior (t : Interval) (ht0 : 0 < t) (ht1 : t < 1) (u : Icc (-1:ℝ) 1) :
      (chain.oldStrip (chain.clock t,u)).val ∈ interior F := by
    apply chain.oldStrip_interior
    rcases old_clock_orientation with ⟨hm,h0,h1⟩ | ⟨ha,h0,h1⟩
    · constructor
      · simpa only [chain.clock_start,h0] using hm ht0
      · simpa only [h1] using hm ht1
    · constructor
      · simpa only [h1] using ha ht1
      · simpa only [chain.clock_start,h0] using ha ht0
  have capSquare_in_Pstar : range capSquare ⊆ range Pstar := by
    rw [hPstarRange,hPplusRange]
    exact fun _ h => Or.inr (Or.inl h)
  -- Filled-square exclusion from clearance of the literal top boundary.
  have cap_vertical_square_clear (t : Interval) (ht : sCap < t) (ht1 : t < 1)
      (H : ℝ) (hH : 0 ≤ H ∧ H ≤ 1)
      (hTopClear : ∀ w : Icc (-1:ℝ) 1, 0 ≤ w.val → w.val ≤ H →
        chain.oldStrip (chain.clock t,w) ∉ chain.q ρ '' Icc (0:Interval) (kCap leftCap)) :
      ∀ w : Icc (-1:ℝ) 1, 0 ≤ w.val → w.val ≤ H →
        chain.oldStrip (chain.clock t,w) ∉ range capSquare := by
    by_cases hH0 : H = 0
    · intro w hw0 hwH hmem
      have hw : w = ⟨0,by norm_num⟩ := Subtype.ext (by linarith)
      exact tail_center_clear t ht (hw ▸ capSquare_in_Pstar hmem)
    have hHpos : 0 < H := lt_of_le_of_ne hH.1 (Ne.symm hH0)
    let widthH (u : Interval) : Icc (-1:ℝ) 1 :=
      ⟨H*u.val,⟨by nlinarith [u.property.1],
        (mul_le_of_le_one_right hH.1 u.property.2).trans hH.2⟩⟩
    let verticalH : C(Interval,S) :=
      ⟨fun u => (chain.oldStrip (chain.clock t,widthH u)).val,by fun_prop⟩
    obtain ⟨ballSquare,hballSquare⟩ := ActualHarerDiskGluing.unit_disk_square_boundary_homeomorph
    let sd : C(Metric.closedBall (0 : Plane) 1,S) :=
      ⟨fun u => (capSquare (ballSquare u)).val,
        continuous_subtype_val.comp (capSquare.continuous.comp ballSquare.continuous)⟩
    have hsd : IsEmbedding sd := IsEmbedding.subtypeVal.comp (hcapSquare.comp ballSquare.isEmbedding)
    have hboundary : Disjoint (range verticalH)
        (sd '' {y | y.val ∈ Metric.sphere (0 : Plane) 1}) := by
      apply disjoint_left.mpr
      rintro y ⟨v,rfl⟩ ⟨u,hu,he⟩
      have he' : capSquare (ballSquare u) = chain.oldStrip (chain.clock t,widthH v) := Subtype.ext he
      have hb : ballSquare u ∈ ActualHarerDiskGluing.squareBoundary := hballSquare ▸ ⟨u,hu,rfl⟩
      change (ballSquare u).1 = 0 ∨ (ballSquare u).1 = 1 ∨
        (ballSquare u).2 = 0 ∨ (ballSquare u).2 = 1 at hb
      rw [← Prod.eta (ballSquare u)] at he'
      rcases hb with hb | hb | hb | hb
      · rw [hb,hcapLeft] at he'
        have hbnd := (chain.boundaryExtension_in_BV ρ (mem_range_self (ballSquare u).2)).1
        have hf : (chain.oldStrip (chain.clock t,widthH v)).val ∈ frontier F := by
          have hBsub : boundaryCircle ⊆ frontier F := by
            rw [hfrontier]
            exact subset_union_left
          exact hBsub ((congrArg Subtype.val he') ▸ hbnd)
        exact disjoint_left.mp disjoint_interior_frontier
          (old_cap_fiber_interior t (hsCap0.trans ht) ht1 _) hf
      · rw [hb,hcapRight] at he'
        have heq := chain.clock.injective (congrArg Prod.fst (chain.oldStrip_embedded.injective he'))
        exact ht.ne heq
      · rw [hb,hcapBottom] at he'
        have heStrip : chain.oldStrip
            (chain.clock (CurveComplex.BranchedDoubleCover.intervalAffine 0 sCap (ballSquare u).1),⟨0,by norm_num⟩) =
            chain.oldStrip (chain.clock t,widthH v) := (chain.oldStrip_center _).trans he'
        have heq := chain.clock.injective (congrArg Prod.fst (chain.oldStrip_embedded.injective heStrip))
        have hseg := CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc
          (show (0:Interval) ≤ sCap from bot_le) (ballSquare u).1
        exact (not_le_of_gt ht) (heq ▸ hseg.2)
      · rw [hb,hcapTop] at he'
        exact hTopClear (widthH v) (mul_nonneg hH.1 v.property.1)
          (mul_le_of_le_one_right hH.1 v.property.2)
          ⟨_,CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc bot_le (ballSquare u).1,he'⟩
    have hout : range verticalH ⊆ (range sd)ᶜ := by
      rcases RegionalEmbeddedFamily.connected_open_set_avoiding_disk_boundary_dichotomy
        (range verticalH) (isPreconnected_range verticalH.continuous) sd hsd hboundary with hin | hout
      · obtain ⟨u,hu⟩ := interior_subset (hin (mem_range_self 0))
        have he : capSquare (ballSquare u) = chain.oldStrip (chain.clock t,⟨0,by norm_num⟩) := by
          apply Subtype.ext
          simpa [verticalH,widthH,sd] using hu
        exact (tail_center_clear t ht (capSquare_in_Pstar ⟨ballSquare u,he⟩)).elim
      · exact hout
    intro w hw0 hwH hmem
    let v : Interval := ⟨w.val/H,div_nonneg hw0 hH.1,(div_le_one hHpos).mpr hwH⟩
    have hv : widthH v = w := by
      apply Subtype.ext
      change H*(w.val/H) = w.val
      field_simp [hH0]
    obtain ⟨u,hu⟩ := hmem
    apply hout (mem_range_self v)
    refine ⟨ballSquare.symm u,?_⟩
    change (capSquare (ballSquare (ballSquare.symm u))).val =
      (chain.oldStrip (chain.clock t,widthH v)).val
    rw [ballSquare.apply_symm_apply,hv]
    exact congrArg Subtype.val hu
  have cap_subgraph_misses_q_prefix (t : Icc sCap chain.cut) (ht : sCap < t.val)
      (u : Icc (-1:ℝ) 1) (hu0 : 0 ≤ u.val) (huh : u.val ≤ hCap t) :
      chain.oldStrip (chain.clock t.val,u) ∉ chain.q ρ '' Icc (0:Interval) (kCap leftCap) := by
    by_cases htc : t.val = chain.cut
    · have htr : t = rightCap := Subtype.ext htc
      have hu : u = ⟨0,by norm_num⟩ := Subtype.ext (by rw [htr,hcapEnd] at huh; linarith)
      rw [hu,htc,chain.oldStrip_center]
      rintro ⟨j,hj,he⟩
      have hjz : j = z := (chain.q_embedded ρ).injective (he.trans q_at_retained_cut.symm)
      exact (not_le_of_gt hklt) (calc
        z = j := hjz.symm
        _ ≤ kCap leftCap := hj.2)
    have htc' : t.val < chain.cut := lt_of_le_of_ne t.property.2 htc
    have hh : 0 < hCap t := hcapPos t htc'
    have htleft : leftCap < t := ht
    have htle : leftCap ≤ t := htleft.le
    have hhW : hCap t < chain.oldCornerWidth :=
      (hcapAnti.antitone htle).trans_lt hhCapWidth
    have htW : t.val ∈ chain.oldCornerWindow := hwindow ⟨t.property.1,t.property.2.trans hcR.le⟩
    have hτ : 0 < τCap t ∧ τCap t < 1 := by
      constructor
      · exact hτ0.trans_le (hτMono.monotone htle)
      · have htR : t < rightCap := htc'
        exact (hτMono htR).trans_le (show τCap rightCap = 1 from hτEnd).le
    have hx : -chain.cornerDelta+(1-(τCap t).val)*(L+chain.cornerDelta) = chain.oldCornerX t.val := by
      have hhx := hxCap t
      dsimp only [L]
      nlinarith
    have hy : chain.cornerEntry 1*(1-(τCap t).val) = chain.oldCornerSign*chain.oldCornerScale*hCap t := by
      have hhy := (eq_div_iff (mul_ne_zero hsign (ne_of_gt chain.oldCornerScale_pos))).mp (hyCap t)
      nlinarith
    let width (v : Interval) : Icc (-1:ℝ) 1 :=
      ⟨hCap t*v.val,⟨by nlinarith [v.property.1],
        (mul_le_of_le_one_right hh.le v.property.2).trans (hhCap t).2.le⟩⟩
    let v : Interval := ⟨u.val/hCap t,div_nonneg hu0 hh.le,(div_le_one hh).mpr huh⟩
    have hv : width v = u := by
      apply Subtype.ext
      change hCap t*(u.val/hCap t) = u.val
      field_simp [ne_of_gt hh]
    rintro ⟨j,hj,he⟩
    obtain ⟨hjk,_⟩ := cap_port_prefix_collision t.val (τCap t) (kCap t) (hCap t)
      htc' htW hτ ⟨hh,hhW⟩ hx hy (hkFormula t) width (fun _ => rfl)
      (fun v => hcapHull t (width v) (mul_nonneg hh.le v.property.1)
        (mul_le_of_le_one_right hh.le v.property.2)) j ⟨hj.1,hj.2.trans hklt.le⟩ v (hv.symm ▸ he)
    exact (not_le_of_gt (hkMono htleft)) (hjk ▸ hj.2)
  have cap_subgraph_clear (t : Icc sCap chain.cut) (ht : sCap < t.val)
      (u : Icc (-1:ℝ) 1) (hu0 : 0 ≤ u.val) (huh : u.val ≤ hCap t) :
      chain.oldStrip (chain.clock t.val,u) ∉ range Pstar := by
    intro hp
    rw [hPstarRange,hPplusRange] at hp
    rcases hp with hn | hs | hr
    · exact old_after_seam_misses_Nminus t.val ht u hn
    · exact cap_vertical_square_clear t.val ht (t.property.2.trans_lt chain.cut_interior.2)
        (hCap t) ⟨(hhCap t).1,(hhCap t).2.le⟩ (cap_subgraph_misses_q_prefix t ht) u hu0 huh hs
    · have hHull := hcapHull t u hu0 huh
      have hSweep : chain.oldStrip (chain.clock t.val,u) ∈ range sweep := by
        rw [hsweepRange]
        exact Or.inr hHull
      have hq : chain.oldStrip (chain.clock t.val,u) ∈ chain.q ρ '' Icc (0:Interval) (kCap leftCap) :=
        hRplusSweep ▸ ⟨hr,hSweep⟩
      exact cap_subgraph_misses_q_prefix t ht u hu0 huh hq
  -- T1a: the same q/collar terminal germ lies on the incoming x-side.
  let entryCut : Interval := chain.cuts ρ chain.cornerIndex.castSucc
  let exitCut : Interval := chain.cuts ρ chain.cornerIndex.succ
  have hcutGap : (entryCut:ℝ) < exitCut.val := cap_cuts_strict
  have hkEntry : entryCut < kCap leftCap := by
    have hk := congrArg Subtype.val (hkFormula leftCap)
    change (kCap leftCap).val = (1-(τCap leftCap).val)*entryCut.val+(τCap leftCap).val*exitCut.val at hk
    have hτpos : (0:ℝ) < (τCap leftCap).val := hτ0
    change entryCut.val < (kCap leftCap).val
    nlinarith
  have hkExit : kCap leftCap < exitCut := by
    have hk := congrArg Subtype.val (hkFormula leftCap)
    change (kCap leftCap).val = (1-(τCap leftCap).val)*entryCut.val+(τCap leftCap).val*exitCut.val at hk
    have hτlt : (τCap leftCap).val < (1:ℝ) := hτ1
    change (kCap leftCap).val < exitCut.val
    nlinarith
  have corner_prefix_x_lower (j : Interval) (hja : entryCut ≤ j) (hjk : j ≤ kCap leftCap) :
      (chain.q ρ j).val ∈ chain.cornerFan.chart.source ∧
      chain.oldCornerX sCap ≤ chain.cornerFan.chart (chain.q ρ j).val 0 := by
    have hjRange : j ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine entryCut exitCut) := by
      rw [affine_interval_range,uIcc_of_le cap_cuts_strict.le]
      exact ⟨hja,hjk.trans hkExit.le⟩
    obtain ⟨v,hv⟩ := hjRange
    have hvle : v.val ≤ (τCap leftCap).val := by
      have hv' := congrArg Subtype.val hv
      have hk := congrArg Subtype.val (hkFormula leftCap)
      change (1-v.val)*entryCut.val+v.val*exitCut.val = j.val at hv'
      change (kCap leftCap).val = (1-(τCap leftCap).val)*entryCut.val+(τCap leftCap).val*exitCut.val at hk
      have hjk' : j.val ≤ (kCap leftCap).val := hjk
      nlinarith
    have hp := chain.piece_clock ρ chain.cornerIndex v
    have hq : chain.q ρ j = chain.piece ρ chain.cornerIndex v := by
      rw [← hv]
      exact hp.symm
    rw [hq,(chain.corner_formula ρ v).2]
    refine ⟨chain.cornerFan.chart.map_target (chain.corner_formula ρ v).1,?_⟩
    rw [chain.cornerFan.chart.right_inv (chain.corner_formula ρ v).1]
    change chain.oldCornerX sCap ≤ -chain.cornerDelta+(1-v.val)*(L+chain.cornerDelta)
    rw [← hxCap0]
    nlinarith [hden]
  let entryRatio : Interval := ⟨entryCut.val/(kCap leftCap).val,
    div_nonneg entryCut.property.1 hk0.le,(div_le_one hk0).mpr hkEntry.le⟩
  have hentryRatio : entryRatio < (1:Interval) := by
    change entryCut.val/(kCap leftCap).val < 1
    exact (div_lt_one (show (0:ℝ) < (kCap leftCap).val from hk0)).mpr
      (show entryCut.val < (kCap leftCap).val from hkEntry)
  obtain ⟨germStart,hgermStart⟩ := exists_between (max_lt htGerm hentryRatio)
  have hgermStart1 : germStart < (1:Interval) := hgermStart.2
  have hgermStartG : tGerm < germStart := (le_max_left _ _).trans_lt hgermStart.1
  have hgermStartEntry : entryRatio < germStart := (le_max_right _ _).trans_lt hgermStart.1
  have Rplus_germ_x_lower (t u : Interval) (ht : germStart ≤ t) :
      (Rplus (t,u)).val ∈ chain.cornerFan.chart.source ∧
      chain.oldCornerX sCap ≤ chain.cornerFan.chart (Rplus (t,u)).val 0 := by
    have htG : tGerm ≤ t := hgermStartG.le.trans ht
    have hcoord := hRplusGerm t htG u
    refine ⟨hcoord.1,?_⟩
    have hjLo : entryCut ≤ CurveComplex.BranchedDoubleCover.intervalAffine 0 (kCap leftCap) t := by
      have htEntry : entryRatio.val ≤ t.val := hgermStartEntry.le.trans ht
      have hh : entryCut.val ≤ t.val*(kCap leftCap).val := (div_le_iff₀ hk0).mp htEntry
      change entryCut.val ≤ (1-t.val)*0+t.val*(kCap leftCap).val
      simpa using hh
    have hjHi := (CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc
      (show (0:Interval) ≤ kCap leftCap from bot_le) t).2
    have hq := (corner_prefix_x_lower _ hjLo hjHi).2
    rw [hcoord.2.2]
    simpa using hq
  -- T1b: remote exterior fibers miss every point of the full positive seam.
  have positive_seam_Rplus_collision (t u : Interval) (w : Icc (-1:ℝ) 1)
      (hw0 : 0 ≤ w.val) (hwp : w.val ≤ pCap)
      (he : Rplus (t,u) = chain.oldStrip (chain.clock sCap,w)) : t = 1 := by
    by_cases hwh : w.val ≤ hCap leftCap
    · let v : Interval := ⟨w.val/hCap leftCap,div_nonneg hw0 hhCap0.le,(div_le_one hhCap0).mpr hwh⟩
      have hv : capPort v = w := by
        apply Subtype.ext
        change hCap leftCap*(w.val/hCap leftCap) = w.val
        field_simp [ne_of_gt hhCap0]
      have hS : capSquare (1,v) = chain.oldStrip (chain.clock sCap,w) := by rw [hcapRight,hv]
      have hm : chain.oldStrip (chain.clock sCap,w) ∈ range (fun j => capSquare (j,1)) :=
        cap_outer_inter ▸ ⟨⟨(1,v),hS⟩,⟨(t,u),he⟩⟩
      obtain ⟨j,hj⟩ := hm
      have hj1 : j = 1 := congrArg Prod.fst (hcapSquare.injective (hj.trans hS.symm))
      have hR : Rplus (t,u) = Rplus (1,0) := by
        rw [← hj1]
        exact he.trans (hj.symm.trans (cap_outer_seam j))
      exact congrArg Prod.fst (hRplus.injective hR)
    · let v : Interval := ⟨(w.val-hCap leftCap)/κ,div_nonneg (by linarith) hκ.le,
        (div_le_one hκ).mpr (by dsimp only [pCap] at hwp; linarith)⟩
      have hv : port v = w := by
        apply Subtype.ext
        rw [hport]
        change hCap leftCap+κ*((w.val-hCap leftCap)/κ) = w.val
        field_simp [ne_of_gt hκ]
        ring
      have hR : Rplus (1,v) = chain.oldStrip (chain.clock sCap,w) := by rw [hRplusRight,hv]
      exact congrArg Prod.fst (hRplus.injective (he.trans hR.symm))
  let remoteR : Set ↥F := Rplus '' (Icc (0:Interval) germStart ×ˢ univ)
  have hremoteR : IsCompact remoteR :=
    (isCompact_Icc.prod isCompact_univ).image Rplus.continuous
  have seam_remote_clear (w : Icc (-1:ℝ) 1) (hw0 : 0 ≤ w.val) (hwp : w.val ≤ pCap) :
      chain.oldStrip (chain.clock sCap,w) ∉ remoteR := by
    rintro ⟨⟨t,u⟩,⟨ht,_⟩,he⟩
    have ht1 := positive_seam_Rplus_collision t u w hw0 hwp he
    exact (not_le_of_gt hgermStart1) (ht1 ▸ ht.2)
  -- T1c: uniform remote clearance and actual chart-side comparison for every width.
  let oldPositive : C(Interval × Interval,↥F) :=
    ⟨fun z => chain.oldStrip (chain.clock z.1,plusWidth z.2),by fun_prop⟩
  have hposOpen : IsOpen (oldPositive ⁻¹' remoteRᶜ) := hremoteR.isClosed.isOpen_compl.preimage oldPositive.continuous
  have hposSeam : ({sCap} : Set Interval) ×ˢ univ ⊆ oldPositive ⁻¹' remoteRᶜ := by
    rintro ⟨t,u⟩ ⟨ht,_⟩
    obtain rfl := mem_singleton_iff.mp ht
    exact seam_remote_clear (plusWidth u) (mul_nonneg hpCap0.le u.property.1)
      (mul_le_of_le_one_right hpCap0.le u.property.2)
  obtain ⟨timeU,widthU,htimeU,hwidthU,hsTime,hwidthAll,hproductClear⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hposOpen hposSeam
  obtain ⟨timeLo,timeHi,hsTimes,htimeInterval⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0,hsCap0⟩ ⟨chain.cut,hscCap⟩).mp
      (htimeU.mem_nhds (hsTime (mem_singleton _)))
  obtain ⟨nearCut,hnearCut⟩ := exists_between (lt_min hsTimes.2 hscCap)
  have hnearCutCut : nearCut < chain.cut := hnearCut.2.trans_le (min_le_right _ _)
  have near_positive_Rplus_clear (t : Icc sCap chain.cut) (ht : sCap < t.val) (htNear : t.val ≤ nearCut)
      (w : Icc (-1:ℝ) 1) (hw0 : 0 ≤ w.val) (hwp : w.val ≤ pCap) :
      chain.oldStrip (chain.clock t.val,w) ∉ range Rplus := by
    rintro ⟨⟨j,u⟩,he⟩
    by_cases hj : j ≤ germStart
    · let v : Interval := ⟨w.val/pCap,div_nonneg hw0 hpCap0.le,(div_le_one hpCap0).mpr hwp⟩
      have hv : plusWidth v = w := by
        apply Subtype.ext
        change pCap*(w.val/pCap) = w.val
        field_simp [ne_of_gt hpCap0]
      have htU : t.val ∈ timeU := htimeInterval ⟨hsTimes.1.trans ht,
        htNear.trans_lt (hnearCut.2.trans_le (min_le_left _ _))⟩
      have hclear : oldPositive (t.val,v) ∉ remoteR :=
        hproductClear (show (t.val,v) ∈ timeU ×ˢ widthU from ⟨htU,hwidthAll (mem_univ v)⟩)
      change chain.oldStrip (chain.clock t.val,plusWidth v) ∉ remoteR at hclear
      rw [hv] at hclear
      exact hclear ⟨(j,u),⟨⟨bot_le,hj⟩,mem_univ _⟩,he⟩
    · have hRcoord := Rplus_germ_x_lower j u (le_of_not_ge hj)
      have htW : t.val ∈ chain.oldCornerWindow := hwindow ⟨t.property.1,t.property.2.trans hcR.le⟩
      have hwW : |w.val| ≤ chain.oldCornerWidth := by
        rw [abs_of_nonneg hw0]
        exact hwp.trans hportTotal.le
      have hOcoord := chain.old_corner_transition t.val htW w hwW
      have hX : chain.oldCornerX t.val < chain.oldCornerX sCap :=
        chain.oldCornerX_order hsCapW htW ht
      have heX := congrArg (fun y : ↥F => chain.cornerFan.chart y.val 0) he
      rw [hOcoord.2] at heX
      change chain.cornerFan.chart (Rplus (j,u)).val 0 = chain.oldCornerX t.val at heX
      exact (not_lt_of_ge hRcoord.2) (heX ▸ hX)
  have near_positive_q_prefix_clear (t : Icc sCap chain.cut) (ht : sCap < t.val) (htNear : t.val ≤ nearCut)
      (w : Icc (-1:ℝ) 1) (hw0 : 0 ≤ w.val) (hwp : w.val ≤ pCap) :
      chain.oldStrip (chain.clock t.val,w) ∉ chain.q ρ '' Icc (0:Interval) (kCap leftCap) := by
    rintro ⟨j,hj,he⟩
    have hjr : j ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine 0 (kCap leftCap)) := by
      rw [affine_interval_range,uIcc_of_le (show (0:Interval) ≤ kCap leftCap from bot_le)]
      exact hj
    obtain ⟨v,hv⟩ := hjr
    apply near_positive_Rplus_clear t ht htNear w hw0 hwp
    exact ⟨(v,0),(hRplusBottom v).trans ((congrArg (chain.q ρ) hv).trans he)⟩
  have near_positive_full_clear (t : Icc sCap chain.cut) (ht : sCap < t.val) (htNear : t.val ≤ nearCut)
      (w : Icc (-1:ℝ) 1) (hw0 : 0 ≤ w.val) (hwp : w.val ≤ pCap) :
      chain.oldStrip (chain.clock t.val,w) ∉ range Pstar := by
    intro hp
    rw [hPstarRange,hPplusRange] at hp
    rcases hp with hn | hs | hr
    · exact old_after_seam_misses_Nminus t.val ht w hn
    · exact cap_vertical_square_clear t.val ht (t.property.2.trans_lt chain.cut_interior.2)
        pCap ⟨hpCap0.le,hpCap1.le⟩ (near_positive_q_prefix_clear t ht htNear) w hw0 hwp hs
    · exact near_positive_Rplus_clear t ht htNear w hw0 hwp hr
  have full_cap_band_outgoing_clear :
      ∃ r₀ : Interval, sCap < r₀ ∧ r₀ < chain.cut ∧
        ∀ t : Icc sCap chain.cut, sCap < t.val → t.val ≤ r₀ →
          ∀ u : Icc (-1:ℝ) 1, capBand (t,u) ∉ range Pstar := by
    refine ⟨nearCut,hnearCut.1,hnearCutCut,?_⟩
    intro t ht htNear u
    change chain.oldStrip (chain.clock t.val,fullPort u) ∉ _
    by_cases hu : u.val ≤ 0
    · apply old_tail_negative_clear t.val ht t.property.2 (fullPort u)
      · change -ηCap ≤ if u.val ≤ 0 then ηCap*u.val else pCap*u.val
        rw [ite_eq_left hu]
        nlinarith [u.property.1]
      · change (if u.val ≤ 0 then ηCap*u.val else pCap*u.val) ≤ 0
        rw [ite_eq_left hu]
        exact mul_nonpos_of_nonneg_of_nonpos hηCap0.le hu
    · apply near_positive_full_clear t ht htNear (fullPort u)
      · change 0 ≤ if u.val ≤ 0 then ηCap*u.val else pCap*u.val
        rw [ite_eq_right hu]
        exact mul_nonneg hpCap0.le (le_of_not_ge hu)
      · change (if u.val ≤ 0 then ηCap*u.val else pCap*u.val) ≤ pCap
        rw [ite_eq_right hu]
        exact mul_le_of_le_one_right hpCap0.le u.property.2
  -- T3: a positive cap width with the prescribed full outgoing face.
  let remoteCap : Set (Icc sCap chain.cut) := {t | nearCut ≤ t.val}
  have hremoteCap : IsCompact remoteCap :=
    (isClosed_le continuous_const continuous_subtype_val).isCompact
  let graphThickening : C((Icc sCap chain.cut) × ℝ,↥F) :=
    ⟨fun z => chain.oldStrip (chain.clock z.1.val,
      projIcc (-1:ℝ) 1 (by norm_num) (hCap z.1+z.2)),by fun_prop⟩
  have hPstarClosed : IsClosed (range Pstar) := (isCompact_range Pstar.continuous).isClosed
  have hgraphOpen : IsOpen (graphThickening ⁻¹' (range Pstar)ᶜ) :=
    hPstarClosed.isOpen_compl.preimage graphThickening.continuous
  have hremoteGraph : remoteCap ×ˢ ({0} : Set ℝ) ⊆ graphThickening ⁻¹' (range Pstar)ᶜ := by
    rintro ⟨t,e⟩ ⟨ht,he⟩
    obtain rfl := mem_singleton_iff.mp he
    have hw : projIcc (-1:ℝ) 1 (by norm_num) (hCap t+0) =
        (⟨hCap t,by constructor <;> linarith [(hhCap t).1,(hhCap t).2]⟩ : Icc (-1:ℝ) 1) := by
      apply Subtype.ext
      simp only [add_zero]
      exact congrArg Subtype.val (projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) (by constructor <;> linarith [(hhCap t).1,(hhCap t).2]))
    change chain.oldStrip (chain.clock t.val,_) ∉ range Pstar
    rw [hw]
    exact cap_subgraph_clear t (hnearCut.1.trans_le ht) _ (hhCap t).1 le_rfl
  obtain ⟨capU,marginU,hcapU,hmarginU,hremoteU,hzeroU,hmarginClear⟩ :=
    generalized_tube_lemma hremoteCap isCompact_singleton hgraphOpen hremoteGraph
  obtain ⟨marginRadius,hmarginRadius,hmarginBall⟩ :=
    Metric.mem_nhds_iff.mp (hmarginU.mem_nhds (hzeroU (mem_singleton _)))
  let δCap : ℝ := min (marginRadius/2) ((pCap-hCap leftCap)/2)
  have hδCap0 : 0 < δCap := lt_min (half_pos hmarginRadius) (half_pos (by dsimp [pCap]; linarith))
  have hδCapRadius : δCap < marginRadius := (min_le_left _ _).trans_lt (by linarith)
  have hδCapGap : δCap < pCap-hCap leftCap :=
    (min_le_right _ _).trans_lt (by dsimp only [pCap]; linarith)
  have hcapHeightBound (t : Icc sCap chain.cut) : hCap t ≤ hCap leftCap :=
    hcapAnti.antitone t.property.1
  have hcapMarginBound (t : Icc sCap chain.cut) : hCap t+δCap < pCap := by
    linarith [hcapHeightBound t]
  have cap_margin_clear (t : Icc sCap chain.cut) (ht : nearCut ≤ t.val)
      (w : Icc (-1:ℝ) 1) (hw0 : 0 ≤ w.val) (hwH : w.val ≤ hCap t+δCap) :
      chain.oldStrip (chain.clock t.val,w) ∉ range Pstar := by
    by_cases hw : w.val ≤ hCap t
    · exact cap_subgraph_clear t (hnearCut.1.trans_le ht) w hw0 hw
    · have he0 : 0 ≤ w.val-hCap t := by linarith
      have heU : w.val-hCap t ∈ marginU := hmarginBall (by
        change dist (w.val-hCap t) 0 < marginRadius
        rw [Real.dist_eq,sub_zero,abs_of_nonneg he0]
        exact (show w.val-hCap t ≤ δCap by linarith).trans_lt hδCapRadius)
      have hclear : graphThickening (t,w.val-hCap t) ∉ range Pstar :=
        hmarginClear (show (t,w.val-hCap t) ∈ capU ×ˢ marginU from ⟨hremoteU ht,heU⟩)
      change chain.oldStrip (chain.clock t.val,
        projIcc (-1:ℝ) 1 (by norm_num) (hCap t+(w.val-hCap t))) ∉ range Pstar at hclear
      have hw' : projIcc (-1:ℝ) 1 (by norm_num) (hCap t+(w.val-hCap t)) = w := by
        convert projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) w.property using 1 <;> congr 1 <;> ring
      simpa only [hw'] using hclear
  have hnearGap : (0:ℝ) < nearCut.val-sCap.val := sub_pos.mpr hnearCut.1
  let blendCap : C(Icc sCap chain.cut,ℝ) :=
    ⟨fun t => max 0 ((nearCut.val-t.val.val)/(nearCut.val-sCap.val)),by fun_prop⟩
  have hblendCap (t : Icc sCap chain.cut) : 0 ≤ blendCap t ∧ blendCap t ≤ 1 := by
    refine ⟨le_max_left _ _,max_le (by norm_num) ?_⟩
    apply (div_le_one hnearGap).mpr
    have ht : sCap.val ≤ t.val.val := t.property.1
    linarith
  have hblendCapStart : blendCap leftCap = 1 := by
    change max 0 ((nearCut.val-sCap.val)/(nearCut.val-sCap.val)) = 1
    rw [div_self (ne_of_gt hnearGap)]
    norm_num
  have hblendCapZero (t : Icc sCap chain.cut) (ht : nearCut ≤ t.val) : blendCap t = 0 := by
    apply max_eq_left
    apply div_nonpos_of_nonpos_of_nonneg _ hnearGap.le
    exact sub_nonpos.mpr ht
  let βCap : C(Icc sCap chain.cut,ℝ) :=
    ⟨fun t => blendCap t*pCap+(1-blendCap t)*(hCap t+δCap),by fun_prop⟩
  have hβCapStart : βCap leftCap = pCap := by
    change blendCap leftCap*pCap+(1-blendCap leftCap)*(hCap leftCap+δCap) = pCap
    rw [hblendCapStart]
    ring
  have hβCap (t : Icc sCap chain.cut) : hCap t < βCap t ∧ βCap t ≤ pCap := by
    have hblend := hblendCap t
    have hmargin := hcapMarginBound t
    have hh := hcapHeightBound t
    dsimp only [βCap,ContinuousMap.coe_mk]
    constructor
    · nlinarith [mul_nonneg hblend.1 (show 0 ≤ pCap-(hCap t+δCap) by linarith)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hblend.2) (show 0 ≤ pCap-(hCap t+δCap) by linarith)]
  have cap_width_clear (t : Icc sCap chain.cut) (ht : sCap < t.val)
      (w : Icc (-1:ℝ) 1) (hw0 : 0 ≤ w.val) (hwβ : w.val ≤ βCap t) :
      chain.oldStrip (chain.clock t.val,w) ∉ range Pstar := by
    by_cases hnear : t.val ≤ nearCut
    · exact near_positive_full_clear t ht hnear w hw0 (hwβ.trans (hβCap t).2)
    · apply cap_margin_clear t (le_of_not_ge hnear) w hw0
      simpa only [βCap,ContinuousMap.coe_mk,hblendCapZero t (le_of_not_ge hnear),zero_mul,sub_zero,one_mul,zero_add] using hwβ
  have positive_cap_width :
      ∃ β : C(Icc sCap chain.cut,ℝ), β leftCap = pCap ∧
        (∀ t, hCap t < β t ∧ β t ≤ pCap) ∧
        (∀ t, sCap < t.val → ∀ w : Icc (-1:ℝ) 1,
          0 ≤ w.val → w.val ≤ β t → chain.oldStrip (chain.clock t.val,w) ∉ range Pstar) :=
    ⟨βCap,hβCapStart,hβCap,cap_width_clear⟩
  -- T4a: pay the existing taper's caller at the actual cut, including time 1.
  let reverseRetained : C(Interval,Interval) :=
    (CurveComplex.BranchedDoubleCover.intervalSegment 1 chain.cut).toContinuousMap
  have hreverseRetained (t : Interval) :
      (reverseRetained t).val = 1-(1-chain.cut.val)*t.val := by
    change (1-t.val)*1+t.val*chain.cut.val = _
    ring
  have hreverseRetained1 : reverseRetained 1 = chain.cut := by
    apply Subtype.ext
    rw [hreverseRetained]
    norm_num
  have hreverseRetainedAbove (t : Interval) : chain.cut ≤ reverseRetained t := by
    change chain.cut.val ≤ (reverseRetained t).val
    rw [hreverseRetained]
    nlinarith [t.property.2,chain.cut.property.2]
  let retainedBand : C(Interval × Icc (-1:ℝ) 1,↥F) :=
    ⟨fun z => chain.oldStrip (chain.clock (reverseRetained z.1),z.2),by fun_prop⟩
  have hretainedCenter (t : Interval) :
      retainedBand (t,⟨0,by norm_num⟩) ∉ range Pstar :=
    tail_center_clear _ (hscCap.trans_le (hreverseRetainedAbove t))
  have hretainedTerminal (w : Icc (-1:ℝ) 1)
      (hwMin : -ηCap < w.val) (hwPlus : w.val < βCap rightCap) :
      retainedBand (1,w) ∉ range Pstar := by
    change chain.oldStrip (chain.clock (reverseRetained 1),w) ∉ range Pstar
    rw [hreverseRetained1]
    by_cases hw : w.val ≤ 0
    · exact old_tail_negative_clear chain.cut hscCap le_rfl w hwMin.le hw
    · exact cap_width_clear rightCap hscCap w (le_of_not_ge hw) hwPlus.le
  obtain ⟨βRetPlus,βRetMinus,hβRet,hβRetPlusEnd,hβRetMinusEnd,hβRetClear⟩ :=
    CurveComplex.actual_continuous_longitudinal_width_taper retainedBand (range Pstar)
      hPstarClosed (βCap rightCap) ηCap
      ⟨(hhCap rightCap).1.trans_lt (hβCap rightCap).1,(hβCap rightCap).2.trans hpCap1.le⟩
      ⟨hηCap0,hηCap1.le⟩ hretainedCenter hretainedTerminal
  let capTime : C(Icc sCap (1:Interval),Icc sCap chain.cut) :=
    ⟨fun t => projIcc sCap chain.cut hscCap.le t.val,by fun_prop⟩
  have hcapTime (t : Icc sCap (1:Interval)) (ht : t.val ≤ chain.cut) :
      (capTime t).val = t.val := by
    exact congrArg Subtype.val (projIcc_of_mem hscCap.le ⟨t.property.1,ht⟩)
  let tailCut : Icc sCap (1:Interval) := ⟨chain.cut,hscCap.le,le_top⟩
  let tailStart : Icc sCap (1:Interval) := ⟨sCap,le_rfl,le_top⟩
  have hcapTimeCut : capTime tailCut = rightCap := Subtype.ext (hcapTime tailCut le_rfl)
  have hcapTimeStart : capTime tailStart = leftCap := Subtype.ext (hcapTime tailStart hscCap.le)
  have hcutGap1 : (0:ℝ) < 1-chain.cut.val := sub_pos.mpr chain.cut_interior.2
  let retainedTime : C(Icc sCap (1:Interval),Interval) :=
    ⟨fun t => projIcc 0 1 zero_le_one ((1-t.val.val)/(1-chain.cut.val)),by fun_prop⟩
  have hretainedTime (t : Icc sCap (1:Interval)) (ht : chain.cut ≤ t.val) :
      (retainedTime t).val = (1-t.val.val)/(1-chain.cut.val) := by
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one
      ⟨div_nonneg (sub_nonneg.mpr t.val.property.2) hcutGap1.le,
       (div_le_one hcutGap1).mpr (sub_le_sub_left (show chain.cut.val ≤ t.val.val from ht) (1:ℝ))⟩)
  have hretainedTimeCut : retainedTime tailCut = 1 := by
    apply Subtype.ext
    rw [hretainedTime tailCut le_rfl]
    exact div_self (ne_of_gt hcutGap1)
  have hretainedTimeLt (t : Icc sCap (1:Interval)) (ht : chain.cut < t.val) :
      (retainedTime t).val < 1 := by
    rw [hretainedTime t ht.le]
    apply (div_lt_one hcutGap1).mpr
    exact sub_lt_sub_left (show chain.cut.val < t.val.val from ht) (1:ℝ)
  have hretainedTimeInv (t : Icc sCap (1:Interval)) (ht : chain.cut ≤ t.val) :
      reverseRetained (retainedTime t) = t.val := by
    apply Subtype.ext
    rw [hreverseRetained,hretainedTime t ht]
    field_simp [ne_of_gt hcutGap1]
    ring
  let βMinus : C(Icc sCap (1:Interval),ℝ) :=
    ⟨fun t => if t.val ≤ chain.cut then ηCap else βRetMinus (retainedTime t),by
      apply continuous_if_le continuous_subtype_val continuous_const
        continuous_const.continuousOn (βRetMinus.continuous.comp retainedTime.continuous).continuousOn
      intro t ht
      have he : t = tailCut := Subtype.ext ht
      change ηCap = βRetMinus (retainedTime t)
      rw [he,hretainedTimeCut,hβRetMinusEnd]⟩
  let βPlus : C(Icc sCap (1:Interval),ℝ) :=
    ⟨fun t => if t.val ≤ chain.cut then βCap (capTime t) else βRetPlus (retainedTime t),by
      apply continuous_if_le continuous_subtype_val continuous_const
        (βCap.continuous.comp capTime.continuous).continuousOn
        (βRetPlus.continuous.comp retainedTime.continuous).continuousOn
      intro t ht
      have he : t = tailCut := Subtype.ext ht
      change βCap (capTime t) = βRetPlus (retainedTime t)
      rw [he,hcapTimeCut,hretainedTimeCut,hβRetPlusEnd]⟩
  have hβTail (t : Icc sCap (1:Interval)) :
      (0 < βMinus t ∧ βMinus t ≤ 1) ∧ (0 < βPlus t ∧ βPlus t ≤ 1) := by
    dsimp only [βMinus,βPlus,ContinuousMap.coe_mk]
    split_ifs with ht
    · exact ⟨⟨hηCap0,hηCap1.le⟩,
        ⟨(hhCap (capTime t)).1.trans_lt (hβCap (capTime t)).1,(hβCap (capTime t)).2.trans hpCap1.le⟩⟩
    · exact ⟨(hβRet (retainedTime t)).2,(hβRet (retainedTime t)).1⟩
  have hβMinusStart : βMinus tailStart = ηCap := ite_eq_left hscCap.le
  have hβPlusStart : βPlus tailStart = pCap := by
    change (if tailStart.val ≤ chain.cut then βCap (capTime tailStart) else _) = pCap
    rw [if_pos hscCap.le,hcapTimeStart,hβCapStart]
  have hβTailGraph (t : Icc sCap chain.cut) :
      hCap t < βPlus ⟨t.val,⟨t.property.1,le_top⟩⟩ := by
    change hCap t < if t.val ≤ chain.cut then βCap (capTime ⟨t.val,⟨t.property.1,le_top⟩⟩) else _
    rw [if_pos t.property.2]
    have he : capTime ⟨t.val,⟨t.property.1,le_top⟩⟩ = t :=
      Subtype.ext (hcapTime _ t.property.2)
    rw [he]
    exact (hβCap t).1
  let tailWidth (t : Icc sCap (1:Interval)) (u : Icc (-1:ℝ) 1) : Icc (-1:ℝ) 1 :=
    ⟨if u.val ≤ 0 then βMinus t*u.val else βPlus t*u.val,by
      split_ifs with hu
      · constructor <;> nlinarith [(hβTail t).1.1,(hβTail t).1.2,u.property.1,u.property.2]
      · constructor <;> nlinarith [(hβTail t).2.1,(hβTail t).2.2,u.property.1,u.property.2]⟩
  have htailWidth : Continuous (fun z : (Icc sCap (1:Interval)) × Icc (-1:ℝ) 1 => tailWidth z.1 z.2) := by
    apply Continuous.subtype_mk
    apply continuous_if_le (by fun_prop) continuous_const (by fun_prop) (by fun_prop)
    intro z hz
    simp only [hz,mul_zero]
  let Tail : C((Icc sCap (1:Interval)) × Icc (-1:ℝ) 1,↥F) :=
    ⟨fun z => chain.oldStrip (chain.clock z.1.val,tailWidth z.1 z.2),
      chain.oldStrip.continuous.comp (((chain.clock.continuous.comp continuous_subtype_val).comp
        continuous_fst).prodMk htailWidth)⟩
  have hTailClear (t : Icc sCap (1:Interval)) (ht : sCap < t.val) (u : Icc (-1:ℝ) 1) :
      Tail (t,u) ∉ range Pstar := by
    change chain.oldStrip (chain.clock t.val,tailWidth t u) ∉ range Pstar
    by_cases htc : t.val ≤ chain.cut
    · have hβM : βMinus t = ηCap := ite_eq_left htc
      have hβP : βPlus t = βCap ⟨t.val,⟨t.property.1,htc⟩⟩ := by
        change (if t.val ≤ chain.cut then βCap (capTime t) else _) = _
        rw [if_pos htc]
        exact congrArg βCap (Subtype.ext (hcapTime t htc))
      by_cases hu : u.val ≤ 0
      · apply old_tail_negative_clear t.val ht htc (tailWidth t u)
        · change -ηCap ≤ if u.val ≤ 0 then βMinus t*u.val else βPlus t*u.val
          rw [if_pos hu,hβM]
          nlinarith [u.property.1]
        · change (if u.val ≤ 0 then βMinus t*u.val else βPlus t*u.val) ≤ 0
          rw [if_pos hu,hβM]
          exact mul_nonpos_of_nonneg_of_nonpos hηCap0.le hu
      · apply cap_width_clear ⟨t.val,⟨t.property.1,htc⟩⟩ ht (tailWidth t u)
        · change 0 ≤ if u.val ≤ 0 then βMinus t*u.val else βPlus t*u.val
          rw [if_neg hu]
          exact mul_nonneg (hβTail t).2.1.le (le_of_not_ge hu)
        · change (if u.val ≤ 0 then βMinus t*u.val else βPlus t*u.val) ≤ _
          rw [if_neg hu,hβP]
          exact mul_le_of_le_one_right ((hhCap _).1.trans_lt (hβCap _).1).le u.property.2
    · have hclear := hβRetClear (retainedTime t) (hretainedTimeLt t (lt_of_not_ge htc)) u
      change chain.oldStrip (chain.clock (reverseRetained (retainedTime t)),_) ∉ range Pstar at hclear
      rw [hretainedTimeInv t (le_of_not_ge htc)] at hclear
      simpa only [tailWidth,βMinus,βPlus,ContinuousMap.coe_mk,if_neg htc] using hclear
  have htailWidthStart (u : Icc (-1:ℝ) 1) : tailWidth tailStart u = fullPort u := by
    apply Subtype.ext
    change (if u.val ≤ 0 then βMinus tailStart*u.val else βPlus tailStart*u.val) = _
    rw [hβMinusStart,hβPlusStart]
  have hTailSeam (u : Icc (-1:ℝ) 1) : Tail (tailStart,u) = Pstar (1,u) := by
    change chain.oldStrip (chain.clock sCap,tailWidth tailStart u) = Pstar (1,u)
    rw [htailWidthStart,hPstarRight]
  have hTailIntersect : range Tail ∩ range Pstar = range (fun u => Pstar (1,u)) := by
    apply Subset.antisymm
    · rintro y ⟨⟨⟨t,u⟩,rfl⟩,hy⟩
      have ht : t = tailStart := by
        apply Subtype.ext
        exact le_antisymm (le_of_not_gt (fun hh => hTailClear t hh u hy)) t.property.1
      exact ⟨u,ht ▸ (hTailSeam u).symm⟩
    · rintro y ⟨u,rfl⟩
      exact ⟨⟨(tailStart,u),hTailSeam u⟩,mem_range_self _⟩
  have hTail : IsEmbedding Tail := by
    apply (Tail.continuous.isClosedEmbedding ?_).isEmbedding
    intro z w he
    have hh := chain.oldStrip_embedded.injective he
    have ht : z.1 = w.1 := Subtype.ext (chain.clock.injective (congrArg Prod.fst hh))
    obtain ⟨t,u⟩ := z
    obtain ⟨t',v⟩ := w
    dsimp only at ht
    subst t'
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    have hw := congrArg (fun q : Interval × Icc (-1:ℝ) 1 => q.2.val) hh
    change (if u.val ≤ 0 then βMinus t*u.val else βPlus t*u.val) =
      (if v.val ≤ 0 then βMinus t*v.val else βPlus t*v.val) at hw
    split_ifs at hw with hu hv hv
    · nlinarith [(hβTail t).1.1]
    · nlinarith [(hβTail t).1.1,(hβTail t).2.1]
    · nlinarith [(hβTail t).1.1,(hβTail t).2.1]
    · nlinarith [(hβTail t).2.1]
  -- T5a: literal longitudinal gluing at the original old time sCap.
  let prefixTime : C(Interval,Interval) :=
    ⟨fun t => projIcc 0 1 zero_le_one (t.val/sCap.val),by fun_prop⟩
  have hprefixTime (t : Interval) (ht : t ≤ sCap) : (prefixTime t).val = t.val/sCap.val := by
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one
      ⟨div_nonneg t.property.1 hsCap0.le,(div_le_one hsCap0).mpr ht⟩)
  have hprefixTimeSeam : prefixTime sCap = 1 := by
    apply Subtype.ext
    rw [hprefixTime sCap le_rfl]
    exact div_self (ne_of_gt hsCap0)
  let tailTime : C(Interval,Icc sCap (1:Interval)) :=
    ⟨fun t => projIcc sCap 1 le_top t,by fun_prop⟩
  have htailTime (t : Interval) (ht : sCap ≤ t) : (tailTime t).val = t := by
    exact congrArg Subtype.val (projIcc_of_mem (show sCap ≤ (1:Interval) from le_top) ⟨ht,le_top⟩)
  have htailTimeSeam : tailTime sCap = tailStart := Subtype.ext (htailTime sCap le_rfl)
  let Ehat : C(Interval × Icc (-1:ℝ) 1,↥F) :=
    ⟨fun z => if z.1 ≤ sCap then Pstar (prefixTime z.1,z.2) else Tail (tailTime z.1,z.2),by
      apply continuous_if_le continuous_fst continuous_const
        (Pstar.continuous.comp (prefixTime.continuous.comp continuous_fst |>.prodMk continuous_snd)).continuousOn
        (Tail.continuous.comp (tailTime.continuous.comp continuous_fst |>.prodMk continuous_snd)).continuousOn
      intro z hz
      change Pstar (prefixTime z.1,z.2) = Tail (tailTime z.1,z.2)
      rw [hz,hprefixTimeSeam,htailTimeSeam,hTailSeam]⟩
  have hEhatPrefix (t : Interval) (ht : t ≤ sCap) (u : Icc (-1:ℝ) 1) :
      Ehat (t,u) = Pstar (prefixTime t,u) := ite_eq_left ht
  have hEhatTail (t : Interval) (ht : sCap ≤ t) (u : Icc (-1:ℝ) 1) :
      Ehat (t,u) = Tail (tailTime t,u) := by
    rcases ht.eq_or_lt with ht | ht
    · subst t
      rw [hEhatPrefix sCap le_rfl,hprefixTimeSeam,htailTimeSeam,hTailSeam]
    · exact ite_eq_right (not_le_of_gt ht)
  have hEhat : IsEmbedding Ehat := by
    apply (Ehat.continuous.isClosedEmbedding ?_).isEmbedding
    intro z w he
    change (if z.1 ≤ sCap then Pstar (prefixTime z.1,z.2) else Tail (tailTime z.1,z.2)) =
      (if w.1 ≤ sCap then Pstar (prefixTime w.1,w.2) else Tail (tailTime w.1,w.2)) at he
    split_ifs at he with hz hw hw
    · have hh := hPstar.injective he
      apply Prod.ext
      · apply Subtype.ext
        have ht := congrArg (fun p : Interval × Icc (-1:ℝ) 1 => p.1.val) hh
        rw [hprefixTime z.1 hz,hprefixTime w.1 hw] at ht
        exact (div_left_inj' (ne_of_gt hsCap0)).mp ht
      · have hsnd := congrArg Prod.snd hh
        exact hsnd
    · have hm : Tail (tailTime w.1,w.2) ∈ range (fun u => Pstar (1,u)) :=
        hTailIntersect ▸ ⟨mem_range_self _,⟨(prefixTime z.1,z.2),he⟩⟩
      obtain ⟨u,hu⟩ := hm
      have hh := hTail.injective (hu.symm.trans (hTailSeam u).symm)
      have ht := congrArg (fun p : (Icc sCap (1:Interval)) × Icc (-1:ℝ) 1 => p.1.val) hh
      rw [htailTime w.1 (le_of_not_ge hw)] at ht
      exact (hw ht.le).elim
    · have hm : Tail (tailTime z.1,z.2) ∈ range (fun u => Pstar (1,u)) :=
        hTailIntersect ▸ ⟨mem_range_self _,⟨(prefixTime w.1,w.2),he.symm⟩⟩
      obtain ⟨u,hu⟩ := hm
      have hh := hTail.injective (hu.symm.trans (hTailSeam u).symm)
      have ht := congrArg (fun p : (Icc sCap (1:Interval)) × Icc (-1:ℝ) 1 => p.1.val) hh
      rw [htailTime z.1 (le_of_not_ge hz)] at ht
      exact (hz ht.le).elim
    · have hh := hTail.injective he
      apply Prod.ext
      · have ht := congrArg (fun p : (Icc sCap (1:Interval)) × Icc (-1:ℝ) 1 => p.1.val) hh
        rwa [htailTime z.1 (le_of_not_ge hz),htailTime w.1 (le_of_not_ge hw)] at ht
      · exact congrArg (fun p : (Icc sCap (1:Interval)) × Icc (-1:ℝ) 1 => p.2) hh
  have hprefixCenter (t : Interval) (ht : t ≤ sCap) : segCap (prefixTime t) = t := by
    apply Subtype.ext
    rw [hsegCap,hprefixTime t ht]
    field_simp [ne_of_gt hsCap0]
  have htailWidthZero (t : Icc sCap (1:Interval)) : tailWidth t ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := by
    apply Subtype.ext
    simp [tailWidth]
  have hEhatCenter (t : Interval) : Ehat (t,⟨0,by norm_num⟩) = orientedA t := by
    by_cases ht : t ≤ sCap
    · rw [hEhatPrefix t ht,hPstarCenter,hprefixCenter t ht]
    · rw [hEhatTail t (le_of_not_ge ht)]
      change chain.oldStrip (chain.clock (tailTime t).val,tailWidth (tailTime t) ⟨0,by norm_num⟩) = _
      rw [htailTime t (le_of_not_ge ht),htailWidthZero,chain.oldStrip_center]
      rfl
  have hEhatInterior (t : Interval) (ht : t ∈ Ioo (0:Interval) 1) (u : Icc (-1:ℝ) 1) :
      (Ehat (t,u)).val ∈ interior F := by
    by_cases hs : t ≤ sCap
    · rw [hEhatPrefix t hs]
      apply hPstarInterior
      change (0:ℝ) < (prefixTime t).val
      rw [hprefixTime t hs]
      exact div_pos ht.1 hsCap0
    · rw [hEhatTail t (le_of_not_ge hs)]
      change (chain.oldStrip (chain.clock (tailTime t).val,tailWidth (tailTime t) u)).val ∈ interior F
      rw [htailTime t (le_of_not_ge hs)]
      exact old_cap_fiber_interior t ht.1 ht.2 _
  have hEhatEnds (u : Icc (-1:ℝ) 1) :
      (Ehat (0,u)).val ∈ boundaryCircle ∧ (Ehat (1,u)).val ∈ boundaryCircle := by
    constructor
    · rw [hEhatPrefix 0 bot_le]
      have hzero : prefixTime 0 = 0 := by
        apply Subtype.ext
        rw [hprefixTime 0 bot_le]
        norm_num
      rw [hzero]
      exact hPstarBoundary u
    · rw [hEhatTail 1 le_top]
      change (chain.oldStrip (chain.clock (tailTime 1).val,tailWidth (tailTime 1) u)).val ∈ boundaryCircle
      rw [htailTime 1 le_top]
      rcases old_clock_orientation with ⟨_,_,h1⟩ | ⟨_,_,h1⟩
      · rw [h1]
        exact (chain.oldStrip_ends _).2
      · rw [h1]
        exact (chain.oldStrip_ends _).1
  have hEhatActive (t : Interval) (ht : t ≤ chain.cut) (u : Icc (-1:ℝ) 1) : Ehat (t,u) ∈ V := by
    by_cases hs : t ≤ sCap
    · rw [hEhatPrefix t hs]
      exact hPstarV (mem_range_self _)
    · rw [hEhatTail t (le_of_not_ge hs)]
      change chain.oldStrip (chain.clock (tailTime t).val,tailWidth (tailTime t) u) ∈ V
      rw [htailTime t (le_of_not_ge hs)]
      exact chain.oldStrip_full_active_fibers _
        (chain.activeWindow_prefix ⟨t,⟨bot_le,ht⟩,rfl⟩) _
  let εCapVariable : C(Icc sCap chain.cut,ℝ) :=
    ⟨fun t => hCap t/βCap t,hCap.continuous.div βCap.continuous
      (fun t => ne_of_gt ((hhCap t).1.trans_lt (hβCap t).1))⟩
  have hεCapVariable (t : Icc sCap chain.cut) : 0 ≤ εCapVariable t ∧ εCapVariable t < 1 := by
    exact ⟨div_nonneg (hhCap t).1 ((hhCap t).1.trans_lt (hβCap t).1).le,
      (div_lt_one ((hhCap t).1.trans_lt (hβCap t).1)).mpr (hβCap t).1⟩
  have hεCapVariableStart : εCapVariable leftCap = θCap := by
    change hCap leftCap/βCap leftCap = _
    rw [hβCapStart]
  have hεCapVariableEnd : εCapVariable rightCap = 0 := by
    change hCap rightCap/βCap rightCap = 0
    rw [show hCap rightCap=0 from hcapEnd,zero_div]
  let capClamp : C(Interval,Icc sCap chain.cut) :=
    ⟨fun t => projIcc sCap chain.cut hscCap.le t,by fun_prop⟩
  have hcapClamp (t : Icc sCap chain.cut) : capClamp t.val = t :=
    projIcc_of_mem hscCap.le t.property
  let εAfter : C(Interval,ℝ) :=
    ⟨fun t => if t ≤ chain.cut then εCapVariable (capClamp t) else 0,by
      apply continuous_if_le continuous_id continuous_const
        (εCapVariable.continuous.comp capClamp.continuous).continuousOn continuous_const.continuousOn
      intro t ht
      change t = chain.cut at ht
      change εCapVariable (capClamp t) = 0
      subst t
      rw [show capClamp chain.cut=rightCap from hcapClamp rightCap,hεCapVariableEnd]⟩
  let εhat : C(Interval,ℝ) :=
    ⟨fun t => if t ≤ sCap then θCap else εAfter t,by
      apply continuous_if_le continuous_id continuous_const continuous_const.continuousOn εAfter.continuous.continuousOn
      intro t ht
      change t = sCap at ht
      subst t
      change θCap = if sCap ≤ chain.cut then εCapVariable (capClamp sCap) else 0
      rw [if_pos hscCap.le,show capClamp sCap=leftCap from hcapClamp leftCap,hεCapVariableStart]⟩
  have hεhatPrefix (t : Interval) (ht : t ≤ sCap) : εhat t = θCap := ite_eq_left ht
  have hεhatCap (t : Icc sCap chain.cut) : εhat t.val = εCapVariable t := by
    rcases t.property.1.eq_or_lt with ht | ht
    · have he : t = leftCap := Subtype.ext ht.symm
      rw [he,hεhatPrefix sCap le_rfl,hεCapVariableStart]
    · change (if t.val ≤ sCap then θCap else if t.val ≤ chain.cut then εCapVariable (capClamp t.val) else 0) = _
      rw [if_neg (not_le_of_gt ht),if_pos t.property.2,hcapClamp]
  have hεhatRetained (t : Interval) (ht : chain.cut ≤ t) : εhat t = 0 := by
    rcases ht.eq_or_lt with ht | ht
    · subst t
      exact (hεhatCap rightCap).trans hεCapVariableEnd
    · change (if t ≤ sCap then θCap else if t ≤ chain.cut then εCapVariable (capClamp t) else 0) = 0
      rw [if_neg (not_le_of_gt (hscCap.trans ht)),if_neg (not_le_of_gt ht)]
  have hεhat (t : Interval) : 0 ≤ εhat t ∧ εhat t < 1 := by
    by_cases hs : t ≤ sCap
    · rw [hεhatPrefix t hs]
      exact ⟨hθCap.1.le,hθCap.2⟩
    · by_cases hc : t ≤ chain.cut
      · rw [show εhat t=εCapVariable ⟨t,⟨le_of_not_ge hs,hc⟩⟩ from hεhatCap ⟨t,⟨le_of_not_ge hs,hc⟩⟩]
        exact hεCapVariable _
      · rw [hεhatRetained t (le_of_not_ge hc)]
        norm_num
  have hεhatSupport (t : Interval) (ht : εhat t ≠ 0) (u : Icc (-1:ℝ) 1) : Ehat (t,u) ∈ V := by
    apply hEhatActive t _ u
    exact le_of_not_gt (fun hc => ht (hεhatRetained t hc.le))
  let graphHat : Interval → ↥F := fun t =>
    Ehat (t,⟨εhat t,⟨by linarith [(hεhat t).1],(hεhat t).2.le⟩⟩)
  have hgraphPrefix (t : Interval) (ht : t ≤ sCap) :
      graphHat t = chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 (kCap leftCap) (prefixTime t)) := by
    change Ehat (t,_) = _
    rw [hEhatPrefix t ht]
    have hu : (⟨εhat t,⟨by linarith [(hεhat t).1],(hεhat t).2.le⟩⟩ : Icc (-1:ℝ) 1) =
        ⟨θCap,⟨by linarith [hθCap.1],hθCap.2.le⟩⟩ := Subtype.ext (hεhatPrefix t ht)
    rw [hu,hPstarMarked]
  have hgraphCap (t : Icc sCap chain.cut) : graphHat t.val = chain.q ρ (kCap t) := by
    change Ehat (t.val,_) = _
    rw [hEhatTail t.val t.property.1]
    change chain.oldStrip (chain.clock (tailTime t.val).val,tailWidth (tailTime t.val) _) = _
    rw [htailTime t.val t.property.1]
    have hβP : βPlus (tailTime t.val) = βCap t := by
      change (if (tailTime t.val).val ≤ chain.cut then βCap (capTime (tailTime t.val)) else _) = _
      rw [htailTime t.val t.property.1,if_pos t.property.2]
      apply congrArg βCap
      apply Subtype.ext
      rw [hcapTime _ (by rw [htailTime t.val t.property.1]; exact t.property.2),htailTime t.val t.property.1]
    have hwidth : tailWidth (tailTime t.val)
        ⟨εhat t.val,⟨by linarith [(hεhat t.val).1],(hεhat t.val).2.le⟩⟩ =
        ⟨hCap t,⟨by linarith [(hhCap t).1],(hhCap t).2.le⟩⟩ := by
      apply Subtype.ext
      change (if εhat t.val ≤ 0 then βMinus (tailTime t.val)*εhat t.val
        else βPlus (tailTime t.val)*εhat t.val) = hCap t
      rw [hεhatCap t,hβP]
      by_cases hz : hCap t = 0
      · simp [εCapVariable,hz]
      · have hp : 0 < εCapVariable t := div_pos
          (lt_of_le_of_ne (hhCap t).1 (Ne.symm hz)) ((hhCap t).1.trans_lt (hβCap t).1)
        rw [if_neg (not_le_of_gt hp)]
        change βCap t*(hCap t/βCap t) = hCap t
        field_simp [ne_of_gt ((hhCap t).1.trans_lt (hβCap t).1)]
    rw [hwidth]
    exact (hcapGraph t).symm
  have hgraphRetained (t : Interval) (ht : chain.cut ≤ t) : graphHat t = orientedA t := by
    have hu : (⟨εhat t,⟨by linarith [(hεhat t).1],(hεhat t).2.le⟩⟩ : Icc (-1:ℝ) 1) =
        ⟨0,by norm_num⟩ := Subtype.ext (hεhatRetained t ht)
    change Ehat (t,_) = _
    rw [hu,hEhatCenter]
  have hkCapRange : range kCap = Icc (kCap leftCap) z := by
    have hright : kCap rightCap = z := hkEnd
    rw [← hright]
    apply Subset.antisymm
    · rintro y ⟨t,rfl⟩
      exact ⟨hkMono.monotone t.property.1,hkMono.monotone t.property.2⟩
    · letI : PreconnectedSpace (Icc sCap chain.cut) := Subtype.preconnectedSpace isPreconnected_Icc
      exact (isPreconnected_range kCap.continuous).Icc_subset (mem_range_self _) (mem_range_self _)
  have hretainedClock (t : Interval) :
      chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine z 1 t) =
        orientedA (CurveComplex.BranchedDoubleCover.intervalAffine chain.cut 1 t) := by
    have hp := chain.piece_clock ρ (Fin.last chain.n) t
    have hr := chain.retained_formula ρ t
    have hi : (Fin.last chain.n).castSucc = (⟨chain.n,by omega⟩ : Fin (chain.n+2)) := Fin.ext rfl
    have hj : (Fin.last chain.n).succ = Fin.last (chain.n+1) := Fin.ext rfl
    rw [hi,hj,chain.cuts_one] at hp
    exact hp.symm.trans hr
  have hretainedRange : chain.q ρ '' Icc z (1:Interval) = orientedA '' Icc chain.cut (1:Interval) := by
    have hleft : range (chain.q ρ ∘ CurveComplex.BranchedDoubleCover.intervalAffine z 1) =
        chain.q ρ '' Icc z (1:Interval) := by
      rw [range_comp,affine_interval_range,uIcc_of_le (show z ≤ (1:Interval) from le_top)]
    have hright : range (orientedA ∘ CurveComplex.BranchedDoubleCover.intervalAffine chain.cut 1) =
        orientedA '' Icc chain.cut (1:Interval) := by
      rw [range_comp,affine_interval_range,uIcc_of_le (show chain.cut ≤ (1:Interval) from le_top)]
    rw [← hleft,← hright]
    congr 1
    funext t
    exact hretainedClock t
  have hsegPrefixInv (u : Interval) : prefixTime (segCap u) = u := by
    have ht : segCap u ≤ sCap := (hsegCapRange ▸ mem_range_self u).2
    apply Subtype.ext
    rw [hprefixTime (segCap u) ht,hsegCap]
    field_simp [ne_of_gt hsCap0]
  have hgraphHatRange : range (chain.q ρ) = range graphHat := by
    apply Subset.antisymm
    · rintro y ⟨j,rfl⟩
      by_cases hj : j ≤ kCap leftCap
      · have hjr : j ∈ range (CurveComplex.BranchedDoubleCover.intervalAffine 0 (kCap leftCap)) := by
          rw [affine_interval_range,uIcc_of_le (show (0:Interval) ≤ kCap leftCap from bot_le)]
          exact ⟨bot_le,hj⟩
        obtain ⟨u,hu⟩ := hjr
        refine ⟨segCap u,?_⟩
        rw [hgraphPrefix (segCap u) (hsegCapRange ▸ mem_range_self u).2,hsegPrefixInv,hu]
      · by_cases hjz : j ≤ z
        · obtain ⟨t,ht⟩ := hkCapRange.symm ▸ (show j ∈ Icc (kCap leftCap) z from ⟨le_of_not_ge hj,hjz⟩)
          exact ⟨t.val,(hgraphCap t).trans (congrArg (chain.q ρ) ht)⟩
        · have hy : chain.q ρ j ∈ orientedA '' Icc chain.cut (1:Interval) :=
            hretainedRange ▸ ⟨j,⟨le_of_not_ge hjz,le_top⟩,rfl⟩
          obtain ⟨t,ht,he⟩ := hy
          exact ⟨t,(hgraphRetained t ht.1).trans he⟩
    · rintro y ⟨t,rfl⟩
      by_cases hs : t ≤ sCap
      · rw [hgraphPrefix t hs]
        exact mem_range_self _
      · by_cases hc : t ≤ chain.cut
        · rw [show graphHat t=chain.q ρ (kCap ⟨t,⟨le_of_not_ge hs,hc⟩⟩) from hgraphCap ⟨t,⟨le_of_not_ge hs,hc⟩⟩]
          exact mem_range_self _
        · rw [hgraphRetained t (le_of_not_ge hc)]
          have hy : orientedA t ∈ chain.q ρ '' Icc z (1:Interval) :=
            hretainedRange.symm ▸ ⟨t,⟨le_of_not_ge hc,le_top⟩,rfl⟩
          exact image_subset_range _ _ hy
  -- T6: local adaptation of the paid original-Q band-openness derivation.
  have originalBoundaryBandInitialNeighborhood
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R))
      (hE : Topology.IsEmbedding E)
      (hend : ∀ w, E (0,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R ∧ E (1,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R)
      (w : Set.Icc (-1 : ℝ) 1) (hw : -1 < (w:ℝ) ∧ (w:ℝ) < 1) :
      ∃ N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R), IsOpen N ∧ E (0,w) ∈ N ∧
        N ⊆ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    let b : C(Interval,CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := ⟨fun t => E (t,w),
      E.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have hb : Topology.IsEmbedding b := hE.comp (isEmbedding_prodMkLeft w)
    obtain ⟨U,V,hpU,h,hU,hV,hzero,hother,hdisk,hboundary,haxis⟩ :=
      CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.source_proper_arc_initial_endpoint_attached_axis_chart
        S g hg hS x R hR htarget b hb (hend w).1 (hend w).2
        (fun t ht => hproper t ht w)
    let f : C(Interval × Set.Icc (-1 : ℝ) 1,S) :=
      ⟨fun z => (E z).val,continuous_subtype_val.comp E.continuous⟩
    have hp : f (0,w) ∈ U := hpU
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
      ((hU.preimage f.continuous).mem_nhds hp)
    let a : ℝ := min (r/4) (1/2)
    have ha : 0 < a ∧ a < 1 :=
      ⟨lt_min (by positivity) (by norm_num),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have har : a < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let η : ℝ := min (r/4) (min ((1-(w:ℝ))/2) ((1+(w:ℝ))/2))
    have hη : 0 < η := lt_min (by positivity)
      (lt_min (by linarith [hw.2]) (by linarith [hw.1]))
    have hηr : η < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hηlo : η ≤ (1+(w:ℝ))/2 := (min_le_right _ _).trans (min_le_right _ _)
    have hηhi : η ≤ (1-(w:ℝ))/2 := (min_le_right _ _).trans (min_le_left _ _)
    have hwstrict (u : Set.Icc (-1 : ℝ) 1) : -1 < (w:ℝ)+η*(u:ℝ) ∧
        (w:ℝ)+η*(u:ℝ) < 1 := by
      constructor <;> nlinarith [u.property.1,u.property.2,hw.1,hw.2]
    let k : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
      (⟨a*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,ha.1,ha.2]⟩,
        ⟨(w:ℝ)+η*(z.2:ℝ),⟨(hwstrict z.2).1.le,(hwstrict z.2).2.le⟩⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      intro z v he
      apply Prod.ext
      · apply Subtype.ext
        exact mul_left_cancel₀ ha.1.ne' (congrArg (fun p => (p.1:ℝ)) he)
      · apply Subtype.ext
        have hh := congrArg (fun p => (p.2:ℝ)) he
        change (w:ℝ)+η*(z.2:ℝ) = (w:ℝ)+η*(v.2:ℝ) at hh
        nlinarith
    have hfkU (z) : f (k z) ∈ U := by
      apply hrU
      rw [Metric.mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
      apply max_lt
      · change |a*(z.1:ℝ)-0| < r
        rw [sub_zero,abs_of_nonneg (mul_nonneg ha.1.le z.1.property.1)]
        exact (mul_le_of_le_one_right ha.1.le z.1.property.2).trans_lt har
      · change |((w:ℝ)+η*(z.2:ℝ))-(w:ℝ)| < r
        have he : ((w:ℝ)+η*(z.2:ℝ))-(w:ℝ) = η*(z.2:ℝ) := by ring
        rw [he,abs_mul,abs_of_pos hη]
        exact (mul_le_of_le_one_right hη.le (abs_le.mpr z.2.property)).trans_lt hηr
    have outside_nonneg (y : S) (hy : y ∈ U) (hQ : y ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.openDisk S x R) :
        0 ≤ (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 := by
      by_contra hn
      have hneg : (((h ⟨y,hy⟩ : V) : ℝ × ℝ)).1 < 0 := lt_of_not_ge hn
      obtain ⟨z,hz,he⟩ := (hdisk y hy).mpr hneg.le
      rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlo | heq
      · exact hQ ⟨z,Metric.mem_ball.mpr hlo,he⟩
      · have hB : y ∈ CurveComplexGenusTwo.SourceTopology.EulerThreeArcs.boundary S x R :=
          ⟨z,Metric.mem_sphere.mpr heq,he⟩
        exact hneg.ne ((hboundary y hy).mp hB)
    let coord : U → Schoenflies.Plane := fun y => Schoenflies.Plane.mk
      (((h y : V) : ℝ × ℝ)).1 (((h y : V) : ℝ × ℝ)).2
    have hcoord : Continuous coord := by dsimp [coord]; fun_prop
    have hcoordi : Function.Injective coord := by
      intro y z he
      apply h.injective
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun p : Schoenflies.Plane => p 0) he
      · exact congrArg (fun p : Schoenflies.Plane => p 1) he
    let C : C(Interval × Set.Icc (-1 : ℝ) 1,Schoenflies.Plane) :=
      ⟨fun z => coord ⟨f (k z),hfkU z⟩,
        hcoord.comp ((f.continuous.comp hkc).subtype_mk _)⟩
    have hCi : Function.Injective C := by
      intro z v he
      have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
      have hEk : E (k z) = E (k v) := Subtype.ext hh
      exact hki (hE.injective hEk)
    have hC : Topology.IsEmbedding C := (C.continuous.isClosedEmbedding hCi).isEmbedding
    have hCzero (u : Set.Icc (-1 : ℝ) 1) : C (0,u) 0 = 0 := by
      apply (hboundary (f (k (0,u))) (hfkU (0,u))).mp
      have hk0 : (k (0,u)).1 = 0 := Subtype.ext (by change a*0=0; ring)
      change (E (k (0,u))).val ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryCircle S x R
      have he : k (0,u) = (0,(k (0,u)).2) := Prod.ext hk0 rfl
      rw [he]
      exact (hend _).1
    have hCpos (t : Interval) (ht : 0 < (t:ℝ)) (u : Set.Icc (-1 : ℝ) 1) :
        0 < C (t,u) 0 := by
      have hn := outside_nonneg (f (k (t,u))) (hfkU (t,u)) (E (k (t,u))).property
      apply lt_of_le_of_ne hn
      intro he
      have hB := (hboundary (f (k (t,u))) (hfkU (t,u))).mpr he.symm
      have hti : (k (t,u)).1 ∈ Set.Ioo (0 : Interval) 1 := by
        constructor
        · change 0 < a*(t:ℝ); exact mul_pos ha.1 ht
        · change a*(t:ℝ) < 1
          exact (mul_le_of_le_one_right ha.1.le t.property.2).trans_lt ha.2
      exact hproper _ hti _ hB
    let P : Set {p : Schoenflies.Plane | 0 ≤ p 0} :=
      {y | y.val ∈ C '' {z | (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1}}
    have hP : IsOpen P := CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.halfPlaneBandOpenness C hC hCzero hCpos
    let W : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := Subtype.val ⁻¹' U
    have hW : IsOpen W := hU.preimage continuous_subtype_val
    let J : W → U := fun y => ⟨y.val.val,y.property⟩
    have hJ : Continuous J := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    let H : W → {p : Schoenflies.Plane | 0 ≤ p 0} := fun y =>
      ⟨coord (J y),outside_nonneg y.val.val y.property y.val.property⟩
    have hH : Continuous H := (hcoord.comp hJ).subtype_mk _
    let K : Set W := H ⁻¹' P
    have hK : IsOpen K := hP.preimage hH
    let N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := Subtype.val '' K
    have hN : IsOpen N := hW.isOpenMap_subtype_val K hK
    have hk00 : k (0,⟨0,by norm_num⟩) = (0,w) := by
      apply Prod.ext
      · apply Subtype.ext; change a*0=0; ring
      · apply Subtype.ext; change (w:ℝ)+η*0=(w:ℝ); ring
    have hpN : E (0,w) ∈ N := by
      refine ⟨⟨E (0,w),hp⟩,?_,rfl⟩
      change coord (J ⟨E (0,w),hp⟩) ∈ C '' _
      refine ⟨(0,⟨0,by norm_num⟩),⟨by norm_num,by norm_num,by norm_num⟩,?_⟩
      change coord ⟨f (k (0,⟨0,by norm_num⟩)),hfkU _⟩ =
        coord ⟨(E (0,w)).val,hp⟩
      apply congrArg coord
      apply Subtype.ext
      change (E (k (0,⟨0,by norm_num⟩))).val = (E (0,w)).val
      rw [hk00]
    refine ⟨N,hN,hpN,?_⟩
    rintro y ⟨u,hu,rfl⟩
    change coord (J u) ∈ C '' _ at hu
    obtain ⟨z,hz,he⟩ := hu
    have hh := congrArg (fun y : U => (y:S)) (hcoordi he)
    have hEq : E (k z) = u.val := Subtype.ext hh
    exact ⟨k z,hwstrict z.2,hEq⟩
  /- Relative openness is derived for every actual original-Q embedded proper
  band, including both full boundary width edges. No openness certificate is input. -/
  have source_original_boundary_band_relative_open
      (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R))
      (hE : Topology.IsEmbedding E)
      (hend : ∀ w, E (0,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R ∧ E (1,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R)
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w, E (t,w) ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R) :
      IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    have interiorNeighborhood (t : Interval) (w : Set.Icc (-1 : ℝ) 1)
        (ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1) (hw : -1 < (w:ℝ) ∧ (w:ℝ) < 1) :
        ∃ N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R), IsOpen N ∧ E (t,w) ∈ N ∧
          N ⊆ E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
      let clip : Schoenflies.Plane → Interval × Set.Icc (-1 : ℝ) 1 := fun z =>
        (Set.projIcc 0 1 zero_le_one (z 0),Set.projIcc (-1) 1 (by norm_num) (z 1))
      let F : Schoenflies.Plane → S := fun z => (E (clip z)).val
      have hFc : Continuous F := continuous_subtype_val.comp
        (E.continuous.comp (by dsimp [clip]; fun_prop))
      let O : Set Schoenflies.Plane := {z | 0 < z 0 ∧ z 0 < 1 ∧ -1 < z 1 ∧ z 1 < 1}
      have hO : IsOpen O :=
        (isOpen_lt continuous_const (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop)).inter
        ((isOpen_lt (show Continuous (fun z : Schoenflies.Plane => z 0) by fun_prop) continuous_const).inter
        ((isOpen_lt continuous_const (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop)).inter
        (isOpen_lt (show Continuous (fun z : Schoenflies.Plane => z 1) by fun_prop) continuous_const)))
      have hclip (z : Schoenflies.Plane) (hz : z ∈ O) :
          ((clip z).1:ℝ) = z 0 ∧ ((clip z).2:ℝ) = z 1 := by
        constructor
        · exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ⟨hz.1.le,hz.2.1.le⟩)
        · exact congrArg Subtype.val (Set.projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
            ⟨hz.2.2.1.le,hz.2.2.2.le⟩)
      have hFi : Set.InjOn F O := by
        intro z hz v hv he
        have hEq : E (clip z) = E (clip v) := Subtype.ext he
        have hh := hE.injective hEq
        have h0 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.1:ℝ)) hh
        have h1 := congrArg (fun p : Interval × Set.Icc (-1 : ℝ) 1 => (p.2:ℝ)) hh
        rw [(hclip z hz).1,(hclip v hv).1] at h0
        rw [(hclip z hz).2,(hclip v hv).2] at h1
        ext j
        fin_cases j <;> assumption
      have hFO : IsOpen (F '' O) :=
        surface_invariance_of_domain_probe F O hO hFc.continuousOn hFi
      let N : Set (CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) := Subtype.val ⁻¹' (F '' O)
      have hN : IsOpen N := hFO.preimage continuous_subtype_val
      have htw : Schoenflies.Plane.mk t w ∈ O := ⟨ht.1,ht.2,hw.1,hw.2⟩
      have hcliptw : clip (Schoenflies.Plane.mk t w) = (t,w) := Prod.ext
        (Subtype.ext (hclip _ htw).1) (Subtype.ext (hclip _ htw).2)
      refine ⟨N,hN,?_,?_⟩
      · refine ⟨Schoenflies.Plane.mk t w,htw,?_⟩
        change (E (clip (Schoenflies.Plane.mk t w))).val = (E (t,w)).val
        rw [hcliptw]
      · rintro y ⟨z,hz,he⟩
        refine ⟨clip z,?_,Subtype.ext he⟩
        change -1 < ((clip z).2:ℝ) ∧ ((clip z).2:ℝ) < 1
        rw [(hclip z hz).2]
        exact ⟨hz.2.2.1,hz.2.2.2⟩
    let rev : Interval × Set.Icc (-1 : ℝ) 1 → Interval × Set.Icc (-1 : ℝ) 1 :=
      fun z => (unitInterval.symm z.1,z.2)
    have hrev : Topology.IsEmbedding rev :=
      unitInterval.symmHomeomorph.isEmbedding.prodMap Topology.IsEmbedding.id
    let Er : C(Interval × Set.Icc (-1 : ℝ) 1,CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) :=
      ⟨E ∘ rev,E.continuous.comp hrev.continuous⟩
    have hEr : Topology.IsEmbedding Er := hE.comp hrev
    have hEr0 (w) : Er (0,w) = E (1,w) := by
      apply congrArg E
      apply Prod.ext
      · apply Subtype.ext; norm_num [rev,unitInterval.symm]
      · rfl
    have hEr1 (w) : Er (1,w) = E (0,w) := by
      apply congrArg E
      apply Prod.ext
      · apply Subtype.ext; norm_num [rev,unitInterval.symm]
      · rfl
    have hErend (w) : Er (0,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R ∧ Er (1,w) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R :=
      ⟨hEr0 w ▸ (hend w).2,hEr1 w ▸ (hend w).1⟩
    have hErproper (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1) (w) :
        Er (t,w) ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R := by
      apply hproper (unitInterval.symm t) _ w
      constructor
      · change (0:ℝ) < 1-(t:ℝ)
        have hh : (t:ℝ) < 1 := ht.2
        linarith
      · change 1-(t:ℝ) < (1:ℝ)
        have hh : (0:ℝ) < t := ht.1
        linarith
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨⟨t,w⟩,hw,rfl⟩
    by_cases ht0 : t = 0
    · subst t
      obtain ⟨N,hN,hp,hsub⟩ := originalBoundaryBandInitialNeighborhood
        g hg hS hR htarget E hE hend hproper w hw
      exact ⟨N,hsub,hN,hp⟩
    by_cases ht1 : t = 1
    · subst t
      obtain ⟨N,hN,hp,hsub⟩ := originalBoundaryBandInitialNeighborhood
        g hg hS hR htarget Er hEr hErend hErproper w hw
      refine ⟨N,?_,hN,(hEr0 w) ▸ hp⟩
      intro y hy
      obtain ⟨z,hz,he⟩ := hsub hy
      exact ⟨rev z,hz,he⟩
    · have ht : 0 < (t:ℝ) ∧ (t:ℝ) < 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)),
          lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))⟩
      obtain ⟨N,hN,hp,hsub⟩ := interiorNeighborhood t w ht hw
      exact ⟨N,hsub,hN,hp⟩
  let regionInclusion : ↥F → CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R :=
    fun y => ⟨y.val,houtside y.property⟩
  have hregionInclusion : Continuous regionInclusion := continuous_subtype_val.subtype_mk _
  have hregionInclusionInj : Function.Injective regionInclusion := by
    intro y z he
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  let EQ : C(Interval × Icc (-1:ℝ) 1,CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.Q S x R) :=
    ⟨regionInclusion ∘ Ehat,hregionInclusion.comp Ehat.continuous⟩
  have hEQ : IsEmbedding EQ :=
    (EQ.continuous.isClosedEmbedding (hregionInclusionInj.comp hEhat.injective)).isEmbedding
  have hEQEnds (u : Icc (-1:ℝ) 1) :
      EQ (0,u) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R ∧
      EQ (1,u) ∈ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R := hEhatEnds u
  have hEQProper (t : Interval) (ht : t ∈ Ioo (0:Interval) 1) (u : Icc (-1:ℝ) 1) :
      EQ (t,u) ∉ CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.boundaryQ S x R := by
    intro hb
    have hBsub : boundaryCircle ⊆ frontier F := by
      rw [hfrontier]
      exact subset_union_left
    exact disjoint_interior_frontier.le_bot ⟨hEhatInterior t ht u,hBsub hb⟩
  have hEQOpen := source_original_boundary_band_relative_open g hg hS hR htarget EQ hEQ hEQEnds hEQProper
  have hEhatOpen : IsOpen (Ehat '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1}) := by
    have heq : regionInclusion ⁻¹' (EQ '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1}) =
        Ehat '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1} := by
      ext y
      constructor
      · rintro ⟨z,hz,he⟩
        exact ⟨z,hz,hregionInclusionInj he⟩
      · rintro ⟨z,hz,rfl⟩
        exact ⟨z,hz,rfl⟩
    rw [← heq]
    exact hEQOpen.preimage hregionInclusion
  exact ⟨Ehat,hEhat,hEhatCenter,hEhatEnds,hEhatInterior,hEhatOpen,
    εhat,hεhat,hgraphHatRange,hεhatSupport,fun t ht => hεhatRetained t ht.1⟩
