import RegionalHalfGuidingCollar
import HalfSignedGuidingChainRecord
import CurveComplexGenusTwo.Topology.CapBandGeometry.LocalCapSeam
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualInternalCollarCalibration
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalNullBigon
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalRelativeSupportNeighborhood
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
attribute [local instance] instDecidable_regionalHalfProfile187Supports

set_option maxHeartbeats 3000000

theorem regional_half_q_prefix_exterior_collar_with_cap_port
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
        let filledCarrier : Set ↥F := range d.disk ∪ guideCarrier ∪ cornerCarrier
        let oldNegative : Set ↥F := regionalHalfOldNegativeBand F chain.oldStrip
          chain.clock chain.cut chain.oldNegativeWidth
        ∀ sweep : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          IsEmbedding sweep →
          range sweep = filledCarrier →
          range sweep ⊆ V →
          range d.disk ⊆ range sweep →
          range sweep ⊆ range d.disk ∪ range chain.oldStrip ∪ range chain.guideStrip ∪
            chartPull F chain.cornerFan.chart (Metric.closedBall (0 : Plane) 1) →
          sweep '' {y | y.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            orientedA '' Icc (0 : Interval) chain.cut ∪
              chain.q ρ '' Icc (0 : Interval) z ∪ range (chain.boundaryExtension ρ) →
          range sweep ∩ {y : ↥F | y.val ∈ frontier F} = range (chain.boundaryExtension ρ) →
          oldNegative ∩ range sweep = orientedA '' Icc (0 : Interval) chain.cut →
          range sweep ∩ range (r v).val.val = orientedA '' Icc (0 : Interval) chain.cut →
        ∃ (s rcap : Interval) (hsc : s < chain.cut),
          chain.clock.symm d.aFinish < s ∧ chain.cut < rcap ∧ rcap < 1 ∧
          Icc s rcap ⊆ chain.oldCornerWindow ∧
        ∃ (τ : C(Icc s chain.cut,Interval)) (h : C(Icc s chain.cut,ℝ))
          (k : C(Icc s chain.cut,Interval)),
        let left : Icc s chain.cut := ⟨s,⟨le_rfl,hsc.le⟩⟩
        let right : Icc s chain.cut := ⟨chain.cut,⟨hsc.le,le_rfl⟩⟩
        ∃ hh : ∀ t, 0 ≤ h t ∧ h t < 1,
          (∀ t, (1-(τ t).val)*(chain.cornerEntry 0-chain.cornerEpsilon ρ) -
            (τ t).val*chain.cornerDelta = chain.oldCornerX t.val) ∧
          (∀ t, h t = (1-(τ t).val)*chain.cornerEntry 1 /
            (chain.oldCornerSign*chain.oldCornerScale)) ∧
          0 < τ left ∧ τ left < 1 ∧ τ right = 1 ∧ StrictMono τ ∧
          k right = z ∧ StrictMono k ∧ 0 < k left ∧ k left < z ∧
          (∀ t, k t = CurveComplex.BranchedDoubleCover.intervalAffine
            (chain.cuts ρ chain.cornerIndex.castSucc)
            (chain.cuts ρ chain.cornerIndex.succ) (τ t)) ∧
          (∀ t, chain.q ρ (k t) = chain.oldStrip
            (chain.clock t.val,⟨h t,⟨by linarith [(hh t).1],(hh t).2.le⟩⟩)) ∧
          h right = 0 ∧ (∀ t, t.val < chain.cut → 0 < h t) ∧ StrictAnti h ∧
          (∀ t, ∀ u : Icc (-1 : ℝ) 1, 0 ≤ u.val → u.val ≤ h t →
            chain.oldStrip (chain.clock t.val,u) ∈ cornerCarrier) ∧
        ∃ (κ : ℝ) (port : C(Interval,Icc (-1 : ℝ) 1))
          (Rplus : C(Interval × Interval,↥F)),
          0 < κ ∧ h left+κ < chain.oldCornerWidth ∧
          (∀ u, (port u).val = h left+κ*u.val) ∧
          IsEmbedding Rplus ∧ range Rplus ⊆ V ∧
          (∀ t, Rplus (t,0) = chain.q ρ
            (CurveComplex.BranchedDoubleCover.intervalAffine 0 (k left) t)) ∧
          (∀ u, (Rplus (0,u)).val ∈ boundaryCircle) ∧
          (∀ t : Interval, 0 < t → ∀ u, (Rplus (t,u)).val ∈ interior F) ∧
          (∀ u, Rplus (1,u) = chain.oldStrip (chain.clock s,port u)) ∧
          range Rplus ∩ range sweep = chain.q ρ '' Icc (0 : Interval) (k left) ∧
          Disjoint (range Rplus) oldNegative ∧
          Disjoint (range Rplus) (range (r v).val.val) ∧
          ∃ t₀ : Interval, t₀ < 1 ∧ ∀ t : Interval, t₀ ≤ t → ∀ u : Interval,
            (Rplus (t,u)).val ∈ chain.cornerFan.chart.source ∧
            (chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 (k left) t)).val ∈
              chain.cornerFan.chart.source ∧
            chain.cornerFan.chart (Rplus (t,u)).val =
              chain.cornerFan.chart
                (chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 (k left) t)).val +
                  Plane.mk 0 (chain.oldCornerSign*chain.oldCornerScale*κ*u.val) := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset hcheap fan gap chain ρ
    guideCarrier cornerCarrier orientedA z filledCarrier oldNegative
    sweep hsweep hsweepRange hsweepV hdSweep hsweepCeiling hsweepSphere
    hsweepFrontier hnegativeSweep hwholeOldSweep
  let : ClosedSurface S := Classical.choice hS.2.1
  have sweep_B_relative_interior :
      chain.boundaryExtension ρ '' Ioo (0 : Interval) 1 ⊆ interior (range sweep : Set ↥F) := by
    let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
    let p := E x
    let τ : BandWidth → Interval := fun w =>
      ⟨((w : ℝ) + 1) / 2, by constructor <;> linarith [w.property.1, w.property.2]⟩
    have hτc : Continuous τ := by dsimp [τ]; fun_prop
    have hτi : Function.Injective τ := by
      intro v w h
      apply Subtype.ext
      have hh := congrArg Subtype.val h
      dsimp [τ] at hh
      linarith
    let β : BandWidth → ↥F := fun w => (chain.boundaryExtension ρ) (τ w)
    have hβc : Continuous β := (chain.boundaryExtension ρ).continuous.comp hτc
    have hβi : Function.Injective β := (chain.boundaryExtension_embedded ρ).injective.comp hτi
    have hβsphere (w : BandWidth) : β w ∈
        sweep '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [hsweepSphere]
      exact Or.inr (mem_range_self _)
    let v : BandWidth → CapBandGeometry.CapDisk := fun w =>
      hsweep.toHomeomorph.symm ⟨β w, image_subset_range _ _ (hβsphere w)⟩
    have hvimage (w : BandWidth) : sweep (v w) = β w :=
      congrArg Subtype.val (hsweep.toHomeomorph.apply_symm_apply _)
    have hvnorm (w : BandWidth) : ‖(v w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      obtain ⟨z,hz,hzβ⟩ := hβsphere w
      have hvz : v w = z := hsweep.injective ((hvimage w).trans hzβ.symm)
      rw [hvz]
      simpa [Metric.mem_sphere,dist_zero_right] using hz
    have hvc : Continuous v := hsweep.toHomeomorph.symm.continuous.comp (hβc.subtype_mk _)
    have hvi : Function.Injective v := by
      intro w u h
      apply hβi
      exact (hvimage w).symm.trans ((congrArg sweep h).trans (hvimage u))
    let L : BandWidth × unitInterval → S := fun z =>
      (sweep (CapBandGeometry.diskRadialStrip v hvnorm z)).val
    have hL : IsEmbedding L := IsEmbedding.subtypeVal.comp
      (hsweep.comp (CapBandGeometry.diskRadialStrip_embedded v hvnorm hvc hvi))
    have hLzero (w : BandWidth) : L (w,0) = (β w).val := by
      dsimp only [L]
      rw [CapBandGeometry.diskRadialStrip_zero, hvimage]
    have hβB (w : BandWidth) : (β w).val ∈ E.symm '' Metric.sphere p R :=
      (chain.boundaryExtension_in_BV ρ (mem_range_self _)).1
    have hβsource (w : BandWidth) : (β w).val ∈ E.source := by
      obtain ⟨z,hz,hzβ⟩ := hβB w
      rw [← hzβ]
      exact E.map_target (htarget (Metric.sphere_subset_closedBall hz))
    have hβcoord (w : BandWidth) : E (β w).val ∈ Metric.sphere p R := by
      obtain ⟨z,hz,hzβ⟩ := hβB w
      rw [← hzβ,E.right_inv (htarget (Metric.sphere_subset_closedBall hz))]
      exact hz
    let u : BandWidth → CapBandGeometry.CapDisk := fun w =>
      ⟨R⁻¹ • (E (β w).val - p), by
        rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hR)]
        have hh : ‖E (β w).val - p‖ = R := by
          simpa only [Metric.mem_sphere,dist_eq_norm] using hβcoord w
        rw [hh,inv_mul_cancel₀ hR.ne']⟩
    have hunorm (w : BandWidth) : ‖(u w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
      change ‖R⁻¹ • (E (β w).val - p)‖ = 1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
      have hh : ‖E (β w).val - p‖ = R := by
        simpa only [Metric.mem_sphere,dist_eq_norm] using hβcoord w
      rw [hh,inv_mul_cancel₀ hR.ne']
    have huc : Continuous u := by
      apply Continuous.subtype_mk
      have hc : Continuous (fun w : BandWidth => E (β w).val) :=
        E.continuousOn.comp_continuous
          (continuous_subtype_val.comp hβc) hβsource
      exact (hc.sub continuous_const).const_smul R⁻¹
    have hui : Function.Injective u := by
      intro w z h
      apply hβi
      apply Subtype.ext
      apply E.injOn (hβsource w) (hβsource z)
      have hh := congrArg Subtype.val h
      change R⁻¹ • (E (β w).val - p) = R⁻¹ • (E (β z).val - p) at hh
      exact sub_left_injective ((smul_right_injective _ (inv_ne_zero hR.ne')) hh)
    let d : CapBandGeometry.CapDisk → S := fun z => E.symm (p + R • z.val)
    have hdt (z : CapBandGeometry.CapDisk) : p + R • z.val ∈ E.target := by
      apply htarget
      rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos hR]
      have hz : ‖z.val‖ ≤ 1 := by
        have hh := z.property
        change dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 at hh
        simpa only [dist_zero_right] using hh
      nlinarith
    have hdc : Continuous d := E.continuousOn_symm.comp_continuous (by fun_prop) hdt
    have hdi : Function.Injective d := by
      intro z w h
      apply Subtype.ext
      have hh := E.symm.injOn (hdt z) (hdt w) h
      exact (smul_right_injective _ hR.ne') (add_left_cancel hh)
    have hd : IsEmbedding d := (hdc.isClosedEmbedding hdi).isEmbedding
    have huimage (w : BandWidth) : d (u w) = (β w).val := by
      change E.symm (p + R • (R⁻¹ • (E (β w).val - p))) = (β w).val
      rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel,
        E.left_inv (hβsource w)]
    let T : BandWidth × unitInterval → S :=
      d ∘ CapBandGeometry.diskRadialStrip u hunorm
    have hT : IsEmbedding T := hd.comp
      (CapBandGeometry.diskRadialStrip_embedded u hunorm huc hui)
    have hTzero (w : BandWidth) : T (w,0) = (β w).val := by
      dsimp only [T,Function.comp_apply]
      rw [CapBandGeometry.diskRadialStrip_zero,huimage]
    have hTQ (z : BandWidth × unitInterval) (hz : T z ∈ F) : z.2 = 0 := by
      by_contra hn
      have ht : 0 < (z.2 : ℝ) := lt_of_le_of_ne z.2.property.1
        (fun hh => hn (Subtype.ext hh.symm))
      apply houtside hz
      refine ⟨p + R • (CapBandGeometry.diskRadialStrip u hunorm z).val,?_,rfl⟩
      rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
        Real.norm_eq_abs,abs_of_pos hR]
      change R * ‖(1-(z.2:ℝ)/2) • (u z.1).val‖ < R
      rw [norm_smul,Real.norm_eq_abs,hunorm,mul_one,
        abs_of_pos (by linarith [z.2.property.2] : 0 < 1-(z.2:ℝ)/2)]
      nlinarith
    have hseam (w : BandWidth) : L (w,0) = T (w,0) :=
      (hLzero w).trans (hTzero w).symm
    have hLT : range L ∩ range T = range (fun w => L (w,0)) := by
      ext y
      constructor
      · rintro ⟨⟨z,rfl⟩,w,hw⟩
        have hwQ : T w ∈ F := hw ▸ (sweep (CapBandGeometry.diskRadialStrip v hvnorm z)).property
        have hw0 := hTQ w hwQ
        refine ⟨w.1,?_⟩
        change L (w.1,0) = L z
        rw [hseam]
        exact (congrArg T (show (w.1,0) = w from Prod.ext rfl hw0.symm)).trans hw
      · rintro ⟨w,rfl⟩
        exact ⟨mem_range_self _,⟨(w,0),(hseam w).symm⟩⟩
    have hsub : (Subtype.val : ↥F → S) ⁻¹' (range L ∪ range T) ⊆ range sweep := by
      intro y hy
      rcases hy with ⟨z,hz⟩ | ⟨z,hz⟩
      · exact ⟨CapBandGeometry.diskRadialStrip v hvnorm z,Subtype.ext hz⟩
      · have hz0 := hTQ z (hz ▸ y.property)
        have hyβ : (β z.1).val = y.val := by
          exact (hTzero z.1).symm.trans
            ((congrArg T (show (z.1,0) = z from Prod.ext rfl hz0.symm)).trans hz)
        exact (Subtype.ext hyβ) ▸ image_subset_range _ _ (hβsphere z.1)
    rintro y ⟨t,ht,rfl⟩
    let w : BandWidth := ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.1,t.property.2]⟩
    have hwlo : (-1 : ℝ) < w := by change -1 < 2*(t:ℝ)-1; linarith [show (0 : ℝ) < t from ht.1]
    have hwhi : (w : ℝ) < 1 := by change 2*(t:ℝ)-1 < 1; linarith [show (t : ℝ) < 1 from ht.2]
    have hτw : τ w = t := by apply Subtype.ext; dsimp [τ,w]; ring
    have hi := glued_half_rectangles_seam_interior_probe L T hL hT hseam hLT w hwlo hwhi
    have hβw : β w = (chain.boundaryExtension ρ) t := by dsimp only [β]; rw [hτw]
    rw [hLzero,hβw] at hi
    exact interior_maximal
      ((preimage_mono interior_subset).trans hsub)
      (isOpen_interior.preimage continuous_subtype_val) hi
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
    apply mul_lt_mul_of_pos_right _ capScale_pos
    have hx := chain.oldCornerX_order (cap_left_window t).1.1 (cap_left_window u).1.1 htu
    linarith
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
    change (capClock t).val < (capClock u).val
    change (1-(capTau t).val)*(chain.cuts ρ chain.cornerIndex.castSucc).val +
      (capTau t).val*(chain.cuts ρ chain.cornerIndex.succ).val <
      (1-(capTau u).val)*(chain.cuts ρ chain.cornerIndex.castSucc).val +
      (capTau u).val*(chain.cuts ρ chain.cornerIndex.succ).val
    nlinarith
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
      change 0 < (capClock ⟨s,⟨le_rfl,hsc.le⟩⟩).val
      change 0 < (1-(capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val)*
        (chain.cuts ρ chain.cornerIndex.castSucc).val +
        (capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val*(chain.cuts ρ chain.cornerIndex.succ).val
      nlinarith
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
    have htop : Plane.mk (chain.oldCornerX t.val)
        (chain.oldCornerSign*chain.oldCornerScale*capHeight t.val) ∈
        regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ) := by
      have hconv := convex_convexHull ℝ
        ({0,Plane.mk (-chain.cornerDelta) 0,chain.cornerEntry,
          Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1)} : Set Plane)
      have hb : Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1) ∈
          regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ) :=
        subset_convexHull ℝ _ (by simp)
      have ha : Plane.mk (-chain.cornerDelta) 0 ∈
          regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ) :=
        subset_convexHull ℝ _ (by simp)
      have hc := hconv hb ha (by linarith [(capTau t).property.2] : 0 ≤ 1-(capTau t).val)
        (capTau t).property.1 (by ring : 1-(capTau t).val+(capTau t).val=1)
      have he : (1-(capTau t).val) •
          Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1) +
          (capTau t).val • Plane.mk (-chain.cornerDelta) 0 =
          Plane.mk (chain.oldCornerX t.val)
            (chain.oldCornerSign*chain.oldCornerScale*capHeight t.val) := by
        ext j
        fin_cases j
        · change (1-(capTau t).val)*(chain.cornerEntry 0-chain.cornerEpsilon ρ)+
            (capTau t).val*(-chain.cornerDelta) = chain.oldCornerX t.val
          have hx := capTau_x t
          dsimp [L] at hx
          nlinarith only [hx]
        · simpa [mul_comm] using cap_height_chart t
      rw [he] at hc
      exact hc
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
  let h : C(Icc s chain.cut,ℝ) :=
    ⟨fun t => capHeight t.val, capHeight.continuous.comp continuous_subtype_val⟩
  have hh : ∀ t, 0 ≤ h t ∧ h t < 1 := by
    intro t
    exact ⟨capHeight_nonneg t,(capHeight_small t).trans chain.oldCornerWidth_lt_one⟩
  let ks : Interval := capClock ⟨s,⟨le_rfl,hsc.le⟩⟩
  have hks0 : 0 < ks := capClock_start_bounds.1
  have hksz : ks < z := capClock_start_bounds.2
  have hqz : chain.q ρ z = orientedA chain.cut := by
    change chain.q ρ (chain.cuts ρ ⟨chain.n,by omega⟩) = _
    rw [← capClock_cut,cap_graph]
    have hw : capWidth ⟨chain.cut,⟨hsc.le,le_rfl⟩⟩ = ⟨0,by norm_num⟩ :=
      Subtype.ext capHeight_cut
    rw [hw,chain.oldStrip_center]
  have qprefix_in_sweep : chain.q ρ '' Icc (0 : Interval) ks ⊆ range sweep := by
    intro y hy
    have hy' : y ∈ chain.q ρ '' Icc (0 : Interval) z := by
      rcases hy with ⟨t,ht,rfl⟩
      exact ⟨t,⟨ht.1,ht.2.trans hksz.le⟩,rfl⟩
    have hb : y ∈ sweep '' {y | y.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [hsweepSphere]
      exact Or.inl (Or.inr hy')
    exact image_subset_range _ _ hb
  have qprefix_clear_old : Disjoint (chain.q ρ '' Icc (0 : Interval) ks)
      (range (r v).val.val) := by
    apply disjoint_left.mpr
    intro y hy ha
    have hy' : y ∈ chain.q ρ '' Icc (0 : Interval) z := by
      rcases hy with ⟨t,ht,rfl⟩
      exact ⟨t,⟨ht.1,ht.2.trans hksz.le⟩,rfl⟩
    have he := chain.changed_prefix_meets_a ρ
    have hycut : y = orientedA chain.cut := by
      have : y ∈ ({(r v).val.val (chain.clock chain.cut)} : Set ↥F) := he ▸ ⟨hy',ha⟩
      exact this
    rcases hy with ⟨t,ht,hqt⟩
    have htcut : t = z := (chain.q_embedded ρ).injective ((hqt.trans hycut).trans hqz.symm)
    exact (not_le_of_gt hksz) (htcut ▸ ht.2)
  have qprefix_clear_negative : Disjoint (chain.q ρ '' Icc (0 : Interval) ks) oldNegative := by
    apply disjoint_left.mpr
    intro y hy hn
    have hs : y ∈ orientedA '' Icc (0 : Interval) chain.cut :=
      hnegativeSweep ▸ ⟨hn,qprefix_in_sweep hy⟩
    rcases hs with ⟨t,ht,rfl⟩
    exact disjoint_left.mp qprefix_clear_old hy (mem_range_self _)
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
  have hq0 : ((chain.q ρ) 0).val ∈ boundaryCircle := by
    rw [chain.q_zero,← chain.boundaryExtension_one ρ]
    exact (chain.boundaryExtension_in_BV ρ (mem_range_self _)).1
  have hq1 : ((chain.q ρ) 1).val ∈ boundaryCircle := by
    rw [chain.q_one]
    rcases interval_clock_orientation chain.clock with hm | ha
    · rw [hm.2.2]
      exact (r v).val.property.2.2.1
    · rw [ha.2.2]
      exact (r v).val.property.2.1
  obtain ⟨N,hN,hNc,hNend,hNint,hNopen⟩ :=
    regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget F hFcompact
      hbase houtside J c hbaseDisjoint hfrontier (chain.q ρ) (chain.q_embedded ρ)
      hq0 hq1 (chain.q_proper ρ)
  let prefixClock : C(Interval,Interval) := CurveComplex.BranchedDoubleCover.intervalSegment 0 ks
  have prefixClock_val (t : Interval) : (prefixClock t).val = ks.val*t.val := by
    change (1-t.val)*0+t.val*ks.val = ks.val*t.val
    ring
  have prefixClock_range (t : Interval) : prefixClock t ∈ Icc (0 : Interval) ks := by
    change 0 ≤ (prefixClock t).val ∧ (prefixClock t).val ≤ ks.val
    rw [prefixClock_val]
    exact ⟨mul_nonneg ks.property.1 t.property.1,mul_le_of_le_one_right ks.property.1 t.property.2⟩
  have prefixClock_injective : Function.Injective prefixClock := by
    intro t u he
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    rw [prefixClock_val,prefixClock_val] at hv
    exact mul_left_cancel₀ (show ks.val ≠ 0 from ne_of_gt hks0) hv
  have prefixClock_interior (t : Interval) (ht : 0 < t) : prefixClock t ∈ Ioo (0 : Interval) 1 := by
    constructor
    · change 0 < (prefixClock t).val
      rw [prefixClock_val]
      exact mul_pos hks0 ht
    · exact (prefixClock_range t).2.trans_lt (hksz.trans_le z.property.2)
  let Nprefix : C(Interval × Icc (-1 : ℝ) 1,↥F) :=
    ⟨fun p => N (prefixClock p.1,p.2),
      N.continuous.comp ((prefixClock.continuous.comp continuous_fst).prodMk continuous_snd)⟩
  have hNprefix : IsEmbedding Nprefix := by
    apply (Nprefix.continuous.isClosedEmbedding _).isEmbedding
    intro p q he
    have hp := hN.injective he
    have hfirst : prefixClock p.1 = prefixClock q.1 := congrArg Prod.fst hp
    injection hp with hf hs
    exact Prod.ext (prefixClock_injective hf) hs
  have hNprefix_center (t : Interval) : Nprefix (t,⟨0,by norm_num⟩) = chain.q ρ (prefixClock t) := hNc _
  have hNprefix_start (u : Icc (-1 : ℝ) 1) : (Nprefix (0,u)).val ∈ boundaryCircle := by
    have hz : prefixClock 0 = 0 := Subtype.ext (by rw [prefixClock_val]; simp)
    change (N (prefixClock 0,u)).val ∈ _
    rw [hz]
    exact (hNend u).1
  have hNprefix_interior (t : Interval) (ht : 0 < t) (u : Icc (-1 : ℝ) 1) :
      (Nprefix (t,u)).val ∈ interior F := hNint _ (prefixClock_interior t ht) u
  have hnegativeCompact : IsCompact oldNegative := by
    apply IsCompact.image _ chain.oldStrip.continuous
    apply IsClosed.isCompact
    change IsClosed {p : Interval × Icc (-1 : ℝ) 1 |
      p.1 ∈ chain.clock '' Icc (0 : Interval) chain.cut ∧ -chain.oldNegativeWidth ≤ p.2.val ∧ p.2.val ≤ 0}
    exact ((isCompact_Icc.image chain.clock.continuous).isClosed.preimage continuous_fst).inter
      ((isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd)).inter
        (isClosed_le (continuous_subtype_val.comp continuous_snd) continuous_const))
  let Uclear : Set ↥F := V \ (oldNegative ∪ range (r v).val.val)
  have hUclear : IsOpen Uclear := IsOpen.inter hV
    (hnegativeCompact.isClosed.union (isCompact_range (r v).val.val.continuous).isClosed).isOpen_compl
  have hNprefix_center_U (t : Interval) : Nprefix (t,⟨0,by norm_num⟩) ∈ Uclear := by
    rw [hNprefix_center]
    have hp : chain.q ρ (prefixClock t) ∈ chain.q ρ '' Icc (0 : Interval) ks :=
      ⟨prefixClock t,prefixClock_range t,rfl⟩
    exact ⟨hsweepV (qprefix_in_sweep hp),fun hbad => hbad.elim
      (disjoint_left.mp qprefix_clear_negative hp) (disjoint_left.mp qprefix_clear_old hp)⟩
  obtain ⟨δ,hδ,Narrow,hNarrow,hNarrowU,hNarrowFormula,hNarrowCenter⟩ :=
    source_shrink_embedded_strip_in_open Nprefix hNprefix Uclear hUclear hNprefix_center_U
  let narrowPrefix : C(Interval × Icc (-1 : ℝ) 1,↥F) := ⟨Narrow,hNarrow.continuous⟩
  have narrowPrefix_center (t : Interval) : narrowPrefix (t,⟨0,by norm_num⟩) =
      chain.q ρ (CurveComplex.BranchedDoubleCover.intervalAffine 0 ks t) := by
    exact (hNarrowCenter t).trans (hNprefix_center t)
  have narrowPrefix_in_V : range narrowPrefix ⊆ V := fun y hy => (hNarrowU hy).1
  have narrowPrefix_start (u : Icc (-1 : ℝ) 1) : (narrowPrefix (0,u)).val ∈ boundaryCircle := by
    rw [show narrowPrefix (0,u) = Nprefix (0,⟨δ*u.val,by
      constructor <;> nlinarith [u.property.1,u.property.2,hδ.1,hδ.2]⟩) from hNarrowFormula _]
    exact hNprefix_start _
  have narrowPrefix_interior (t : Interval) (ht : 0 < t) (u : Icc (-1 : ℝ) 1) :
      (narrowPrefix (t,u)).val ∈ interior F := by
    rw [show narrowPrefix (t,u) = Nprefix (t,⟨δ*u.val,by
      constructor <;> nlinarith [u.property.1,u.property.2,hδ.1,hδ.2]⟩) from hNarrowFormula _]
    exact hNprefix_interior t ht _
  have narrowPrefix_clear_negative : Disjoint (range narrowPrefix) oldNegative := by
    apply disjoint_left.mpr
    intro y hy hn
    exact (hNarrowU hy).2 (Or.inl hn)
  have narrowPrefix_clear_old : Disjoint (range narrowPrefix) (range (r v).val.val) := by
    apply disjoint_left.mpr
    intro y hy ha
    exact (hNarrowU hy).2 (Or.inr ha)
  let squarePrefix : C(Interval × Interval,↥F) :=
    ⟨fun p => narrowPrefix (p.1,⟨p.2.val,⟨by linarith [p.2.property.1],p.2.property.2⟩⟩),
      by fun_prop⟩
  have squarePrefix_embedded : IsEmbedding squarePrefix := by
    apply (squarePrefix.continuous.isClosedEmbedding _).isEmbedding
    intro p q he
    have hp := hNarrow.injective he
    have hp0 := congrArg Prod.fst hp
    have hp1 := congrArg (fun a : Interval × Icc (-1 : ℝ) 1 => a.2.val) hp
    exact Prod.ext hp0 (Subtype.ext hp1)
  have squarePrefix_in_V : range squarePrefix ⊆ V := by
    rintro y ⟨p,rfl⟩
    exact narrowPrefix_in_V (mem_range_self _)
  have squarePrefix_center (t : Interval) : squarePrefix (t,0) = chain.q ρ
      (CurveComplex.BranchedDoubleCover.intervalAffine 0 ks t) := narrowPrefix_center t
  have squarePrefix_start (u : Interval) : (squarePrefix (0,u)).val ∈ boundaryCircle :=
    narrowPrefix_start _
  have squarePrefix_interior (t : Interval) (ht : 0 < t) (u : Interval) :
      (squarePrefix (t,u)).val ∈ interior F := narrowPrefix_interior t ht _
  have squarePrefix_clear_negative : Disjoint (range squarePrefix) oldNegative := by
    apply disjoint_left.mpr
    rintro y ⟨p,rfl⟩ hn
    exact disjoint_left.mp narrowPrefix_clear_negative (mem_range_self _) hn
  have squarePrefix_clear_old : Disjoint (range squarePrefix) (range (r v).val.val) := by
    apply disjoint_left.mpr
    rintro y ⟨p,rfl⟩ ha
    exact disjoint_left.mp narrowPrefix_clear_old (mem_range_self _) ha
  have affinePort (κ : ℝ) (hκ : 0 < κ) (hκwidth : capHeight s+κ < chain.oldCornerWidth) :
      ∃ port : C(Interval,Icc (-1 : ℝ) 1),
        (∀ u, (port u).val = capHeight s+κ*u.val) ∧
        (∀ u, (chain.oldStrip (chain.clock s,port u)).val ∈ chain.cornerFan.chart.source ∧
          chain.cornerFan.chart (chain.oldStrip (chain.clock s,port u)).val =
            Plane.mk (chain.oldCornerX s) (chain.oldCornerSign*chain.oldCornerScale*(capHeight s+κ*u.val))) := by
    have hsnonneg := capHeight_nonneg ⟨s,⟨le_rfl,hsc.le⟩⟩
    let port : C(Interval,Icc (-1 : ℝ) 1) :=
      ⟨fun u => ⟨capHeight s+κ*u.val,by
        constructor
        · nlinarith [u.property.1]
        · have hle := mul_le_of_le_one_right hκ.le u.property.2
          linarith [chain.oldCornerWidth_lt_one]⟩,by fun_prop⟩
    refine ⟨port,(fun _ => rfl),?_⟩
    intro u
    exact chain.old_corner_transition s (cap_left_window ⟨s,⟨le_rfl,hsc.le⟩⟩).1.1 (port u) (by
      have hpn : 0 ≤ (port u).val := by
        change 0 ≤ capHeight s+κ*u.val
        exact add_nonneg hsnonneg (mul_nonneg hκ.le u.property.1)
      rw [abs_of_nonneg hpn]
      change capHeight s+κ*u.val ≤ chain.oldCornerWidth
      have hle := mul_le_of_le_one_right hκ.le u.property.2
      linarith)
  -- E1: the actual cap graph and its supporting affine halfspace.
  have cap_sign_nonzero : chain.oldCornerSign ≠ 0 := by
    rcases chain.oldCornerSign_unit with hσ | hσ <;> rw [hσ] <;> norm_num
  have cap_sign_square : chain.oldCornerSign * chain.oldCornerSign = 1 := by
    rcases chain.oldCornerSign_unit with hσ | hσ <;> rw [hσ] <;> norm_num
  have cap_signed_scale_nonzero : chain.oldCornerSign*chain.oldCornerScale ≠ 0 :=
    mul_ne_zero cap_sign_nonzero chain.oldCornerScale_pos.ne'
  have cap_entry_height_nonzero : chain.cornerEntry 1 ≠ 0 := by
    intro he
    have hp := chain.oldCornerSign_matches
    rw [he,mul_zero] at hp
    exact lt_irrefl _ hp
  let capFunctional : Plane → ℝ := fun p => chain.oldCornerSign *
    ((L+chain.cornerDelta)*p 1-chain.cornerEntry 1*(p 0+chain.cornerDelta))
  have capFunctional_convex : Convex ℝ {p : Plane | capFunctional p ≤ 0} := by
    intro p hp q hq a b ha hb hab
    have hf : capFunctional (a • p+b • q) = a*capFunctional p+b*capFunctional q := by
      have he : b = 1-a := by linarith
      rw [he]
      dsimp [capFunctional]
      change chain.oldCornerSign*((L+chain.cornerDelta)*
        (a*p 1+(1-a)*q 1)-chain.cornerEntry 1*(a*p 0+(1-a)*q 0+chain.cornerDelta)) =
        a*(chain.oldCornerSign*((L+chain.cornerDelta)*p 1-chain.cornerEntry 1*(p 0+chain.cornerDelta)))+
          (1-a)*(chain.oldCornerSign*((L+chain.cornerDelta)*q 1-chain.cornerEntry 1*(q 0+chain.cornerDelta)))
      ring
    change capFunctional (a • p+b • q) ≤ 0
    rw [hf]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hp)
      (mul_nonpos_of_nonneg_of_nonpos hb hq)
  have capFunctional_hull (p : Plane)
      (hp : p ∈ regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)) :
      capFunctional p ≤ 0 := by
    apply convexHull_min (s := ({0,Plane.mk (-chain.cornerDelta) 0,chain.cornerEntry,
      Plane.mk (chain.cornerEntry 0-chain.cornerEpsilon ρ) (chain.cornerEntry 1)} : Set Plane))
      (t := {p : Plane | capFunctional p ≤ 0}) ?_ capFunctional_convex hp
    intro p hp
    simp only [mem_insert_iff,mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · change chain.oldCornerSign*((L+chain.cornerDelta)*0-chain.cornerEntry 1*(0+chain.cornerDelta)) ≤ 0
      nlinarith [mul_pos chain.oldCornerSign_matches chain.cornerDelta_pos]
    · change chain.oldCornerSign*((L+chain.cornerDelta)*0-chain.cornerEntry 1*(-chain.cornerDelta+chain.cornerDelta)) ≤ 0
      ring_nf
      norm_num
    · change chain.oldCornerSign*((L+chain.cornerDelta)*chain.cornerEntry 1-
        chain.cornerEntry 1*(chain.cornerEntry 0+chain.cornerDelta)) ≤ 0
      dsimp [L]
      nlinarith [mul_pos chain.oldCornerSign_matches (chain.cornerEpsilon_pos ρ)]
    · change chain.oldCornerSign*((L+chain.cornerDelta)*chain.cornerEntry 1-
        chain.cornerEntry 1*(chain.cornerEntry 0-chain.cornerEpsilon ρ+chain.cornerDelta)) ≤ 0
      dsimp [L]
      ring_nf
      norm_num
  let capAffine : Plane ≃ₜ Plane := {
    toFun := fun p => Plane.mk (p 0-chain.oldCornerX s)
      ((p 1-chain.cornerEntry 1*(p 0+chain.cornerDelta)/(L+chain.cornerDelta))/
        (chain.oldCornerSign*chain.oldCornerScale))
    invFun := fun p => Plane.mk (p 0+chain.oldCornerX s)
      (chain.oldCornerSign*chain.oldCornerScale*p 1+
        chain.cornerEntry 1*(p 0+chain.oldCornerX s+chain.cornerDelta)/(L+chain.cornerDelta))
    left_inv := by
      intro p
      ext i
      fin_cases i
      · dsimp [Plane.mk]; ring
      · change chain.oldCornerSign*chain.oldCornerScale*
          ((p 1-chain.cornerEntry 1*(p 0+chain.cornerDelta)/(L+chain.cornerDelta))/
            (chain.oldCornerSign*chain.oldCornerScale))+
          chain.cornerEntry 1*(p 0-chain.oldCornerX s+chain.oldCornerX s+chain.cornerDelta)/(L+chain.cornerDelta) = p 1
        field_simp [cap_signed_scale_nonzero,cap_sign_nonzero,chain.oldCornerScale_pos.ne',hden.ne']
        <;> ring
    right_inv := by
      intro p
      ext i
      fin_cases i
      · dsimp [Plane.mk]; ring
      · change (chain.oldCornerSign*chain.oldCornerScale*p 1+
          chain.cornerEntry 1*(p 0+chain.oldCornerX s+chain.cornerDelta)/(L+chain.cornerDelta)-
          chain.cornerEntry 1*(p 0+chain.oldCornerX s+chain.cornerDelta)/(L+chain.cornerDelta))/
            (chain.oldCornerSign*chain.oldCornerScale) = p 1
        field_simp [cap_signed_scale_nonzero,cap_sign_nonzero,chain.oldCornerScale_pos.ne',hden.ne']
        <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have capAffine_second (p : Plane) : capAffine p 1 =
      capFunctional p/(chain.oldCornerScale*(L+chain.cornerDelta)) := by
    change (p 1-chain.cornerEntry 1*(p 0+chain.cornerDelta)/(L+chain.cornerDelta))/
      (chain.oldCornerSign*chain.oldCornerScale) = _
    dsimp [capFunctional]
    rcases chain.oldCornerSign_unit with hσ | hσ <;> rw [hσ] <;>
      field_simp [chain.oldCornerScale_pos.ne',hden.ne'] <;> ring
  have capAffine_hull_nonpositive (p : Plane)
      (hp : p ∈ regionalHalfCornerHull chain.cornerDelta chain.cornerEntry (chain.cornerEpsilon ρ)) :
      capAffine p 1 ≤ 0 := by
    rw [capAffine_second]
    exact div_nonpos_of_nonpos_of_nonneg (capFunctional_hull p hp)
      (mul_pos chain.oldCornerScale_pos hden).le
  have cap_ks_piece : chain.q ρ ks = chain.piece ρ chain.cornerIndex (capTau ⟨s,⟨le_rfl,hsc.le⟩⟩) :=
    (chain.piece_clock ρ chain.cornerIndex _).symm
  have cap_ks_in_hull : chain.q ρ ks ∈ cornerCarrier := by
    rw [show chain.q ρ ks = chain.oldStrip (chain.clock s,capWidth ⟨s,⟨le_rfl,hsc.le⟩⟩) from cap_graph _]
    exact cap_vertical_in_hull ⟨s,⟨le_rfl,hsc.le⟩⟩
      (capWidth ⟨s,⟨le_rfl,hsc.le⟩⟩) (capHeight_nonneg _) (by rfl)
  have cap_ks_chart : (chain.q ρ ks).val ∈ chain.cornerFan.chart.source ∧
      chain.cornerFan.chart (chain.q ρ ks).val =
        Plane.mk (chain.oldCornerX s) (chain.oldCornerSign*chain.oldCornerScale*capHeight s) := by
    rw [show chain.q ρ ks = chain.oldStrip (chain.clock s,capWidth ⟨s,⟨le_rfl,hsc.le⟩⟩) from cap_graph _]
    exact chain.old_corner_transition s (cap_left_window ⟨s,⟨le_rfl,hsc.le⟩⟩).1.1 _ (by
      change |capHeight s| ≤ chain.oldCornerWidth
      rw [abs_of_nonneg (capHeight_nonneg ⟨s,⟨le_rfl,hsc.le⟩⟩)]
      exact (capHeight_small ⟨s,⟨le_rfl,hsc.le⟩⟩).le)
  have cap_ks_clear_b : chain.q ρ ks ∉ range (r w).val.val := by
    apply disjoint_left.mp (chain.changed_misses_b ρ chain.cornerIndex ?_)
      (cap_ks_piece ▸ mem_range_self _)
    have he := (chain.corner_kind chain.cornerIndex).2 rfl
    rw [he]
    decide
  have cap_ks_clear_disk : chain.q ρ ks ∉ range d.disk := by
    intro hd
    have hm : chain.q ρ ks ∈ d.second '' Icc chain.guideEntryTime (1 : Interval) :=
      chain.corner_disk_inter ρ ▸ ⟨cap_ks_in_hull,hd⟩
    rcases hm with ⟨t,ht,he⟩
    apply cap_ks_clear_b
    rw [← he]
    rw [d.second_eq]
    exact mem_range_self _
  have cap_ks_clear_guide : chain.q ρ ks ∉ guideCarrier := by
    intro hg
    obtain ⟨i,hi⟩ := mem_iUnion.mp hg
    have hmeet := chain.guide_corner_inter ρ i
    have hm := hmeet ▸ (show chain.q ρ ks ∈
      regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i) ∩ cornerCarrier
      from ⟨hi,cap_ks_in_hull⟩)
    split_ifs at hm with hlast
    · obtain ⟨p,hp,hpy⟩ := hm
      have ht := chain.guide_corner_width_transition ρ i hlast p.2 hp.2.1 hp.2.2
      have he : chain.guideStrip ((chain.guideCoordinates ρ i 1).1,p.2) = chain.q ρ ks := by
        simpa only [← hp.1] using hpy
      have hheight := congrArg (fun p : Plane => p 1) (ht.2.symm.trans (congrArg chain.cornerFan.chart (congrArg Subtype.val he)))
      have hheight' := congrArg (fun p : Plane => p 1) cap_ks_chart.2
      have hcap := cap_height_chart ⟨s,⟨le_rfl,hsc.le⟩⟩
      change chain.cornerEntry 1 = chain.cornerFan.chart (chain.q ρ ks).val 1 at hheight
      change chain.cornerFan.chart (chain.q ρ ks).val 1 =
        chain.oldCornerSign*chain.oldCornerScale*capHeight s at hheight'
      have hz : chain.cornerEntry 1*(capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val = 0 := by
        nlinarith only [hheight,hheight',hcap]
      exact (mul_ne_zero cap_entry_height_nonzero (capTau_pos ⟨s,⟨le_rfl,hsc.le⟩⟩).ne') hz
    · exact hm
  have cap_ks_clock_in_corner : ks ∈ Ioo
      (chain.cuts ρ chain.cornerIndex.castSucc) (chain.cuts ρ chain.cornerIndex.succ) := by
    have ht0 := capTau_pos ⟨s,⟨le_rfl,hsc.le⟩⟩
    have ht1 := capTau_lt_one ⟨s,⟨le_rfl,hsc.le⟩⟩ hsc
    have hc : (chain.cuts ρ chain.cornerIndex.castSucc).val <
      (chain.cuts ρ chain.cornerIndex.succ).val := cap_cuts_strict
    change (chain.cuts ρ chain.cornerIndex.castSucc).val < ks.val ∧
      ks.val < (chain.cuts ρ chain.cornerIndex.succ).val
    change _ < (1-(capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val)*(chain.cuts ρ chain.cornerIndex.castSucc).val+
      (capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val*(chain.cuts ρ chain.cornerIndex.succ).val ∧
      (1-(capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val)*(chain.cuts ρ chain.cornerIndex.castSucc).val+
        (capTau ⟨s,⟨le_rfl,hsc.le⟩⟩).val*(chain.cuts ρ chain.cornerIndex.succ).val < _
    constructor <;> nlinarith
  have cap_slab_compact (i : {i : Fin (chain.n+1) // i.val < chain.cornerIndex.val}) :
      IsCompact (regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i)) := by
    let K : Set (Interval × (Interval × Icc (-1 : ℝ) 1)) := {p |
      p.2.1 = (chain.guideCoordinates ρ i p.1).1 ∧
      0 ≤ p.2.2.val ∧ p.2.2.val ≤ (chain.guideCoordinates ρ i p.1).2.val}
    have hK : IsClosed K := by
      exact (isClosed_eq (continuous_fst.comp continuous_snd)
        (continuous_fst.comp ((chain.guideCoordinates ρ i).continuous.comp continuous_fst))).inter
        ((isClosed_le continuous_const (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).inter
          (isClosed_le (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
            (continuous_subtype_val.comp (continuous_snd.comp ((chain.guideCoordinates ρ i).continuous.comp continuous_fst)))))
    have he : regionalHalfGuideSlab F chain.guideStrip (chain.guideCoordinates ρ i) =
        (fun p : Interval × (Interval × Icc (-1 : ℝ) 1) => chain.guideStrip p.2) '' K := by
      ext y
      constructor
      · rintro ⟨p,⟨t,hpt,hp0,hp1⟩,rfl⟩
        exact ⟨(t,p),⟨hpt,hp0,hp1⟩,rfl⟩
      · rintro ⟨⟨t,p⟩,⟨hpt,hp0,hp1⟩,rfl⟩
        exact ⟨p,⟨t,hpt,hp0,hp1⟩,rfl⟩
    rw [he]
    exact hK.isCompact.image (chain.guideStrip.continuous.comp continuous_snd)
  have cap_guide_compact : IsCompact guideCarrier := isCompact_iUnion cap_slab_compact
  let qOutsideCorner : Set ↥F := chain.q ρ ''
    (Iic (chain.cuts ρ chain.cornerIndex.castSucc) ∪ Ici (chain.cuts ρ chain.cornerIndex.succ))
  have qOutsideCorner_compact : IsCompact qOutsideCorner :=
    (isClosed_Iic.union isClosed_Ici).isCompact.image (chain.q ρ).continuous
  have cap_ks_not_outside : chain.q ρ ks ∉ qOutsideCorner := by
    rintro ⟨t,ht,he⟩
    have htks := (chain.q_embedded ρ).injective he
    subst t
    exact ht.elim (not_le_of_gt cap_ks_clock_in_corner.1) (not_le_of_gt cap_ks_clock_in_corner.2)
  obtain ⟨Wclear,hWclear,hWpre⟩ := isOpen_induced_iff.mp hUclear
  let capForbidden : Set S := (Subtype.val : ↥F → S) '' range d.disk ∪
    (Subtype.val : ↥F → S) '' guideCarrier ∪ (Subtype.val : ↥F → S) '' qOutsideCorner
  have capForbidden_closed : IsClosed capForbidden :=
    (((isCompact_range d.disk.continuous).image continuous_subtype_val).union
      (cap_guide_compact.image continuous_subtype_val)).union
        (qOutsideCorner_compact.image continuous_subtype_val) |>.isClosed
  let capSupport : Set S := Wclear ∩ interior F ∩ capForbiddenᶜ
  have capSupport_open : IsOpen capSupport := (hWclear.inter isOpen_interior).inter capForbidden_closed.isOpen_compl
  have cap_ks_interior : (chain.q ρ ks).val ∈ interior F := by
    rw [← hNc ks]
    exact hNint ks ⟨hks0,show ks.val < 1 from hksz.trans_le (show z ≤ (1 : Interval) from z.property.2)⟩ _
  have cap_ks_support : (chain.q ρ ks).val ∈ capSupport := by
    refine ⟨⟨?_,cap_ks_interior⟩,?_⟩
    · have hh := hNprefix_center_U (0 : Interval)
      have hx : chain.q ρ ks ∈ Uclear := by
        refine ⟨hsweepV (qprefix_in_sweep ⟨ks,⟨hks0.le,le_rfl⟩,rfl⟩),?_⟩
        intro hb
        exact hb.elim (disjoint_left.mp qprefix_clear_negative ⟨ks,⟨hks0.le,le_rfl⟩,rfl⟩)
          (disjoint_left.mp qprefix_clear_old ⟨ks,⟨hks0.le,le_rfl⟩,rfl⟩)
      exact show chain.q ρ ks ∈ (Subtype.val : ↥F → S) ⁻¹' Wclear from hWpre.symm ▸ hx
    · intro hbad
      rcases hbad with (hd | hg) | hq
      · obtain ⟨y,hy,he⟩ := hd
        exact cap_ks_clear_disk ((Subtype.ext he : y = chain.q ρ ks) ▸ hy)
      · obtain ⟨y,hy,he⟩ := hg
        exact cap_ks_clear_guide ((Subtype.ext he : y = chain.q ρ ks) ▸ hy)
      · obtain ⟨y,hy,he⟩ := hq
        exact cap_ks_not_outside ((Subtype.ext he : y = chain.q ρ ks) ▸ hy)
  let capChart : OpenPartialHomeomorph S Plane :=
    (chain.cornerFan.chart.restr capSupport).transHomeomorph capAffine
  have capChart_source : capChart.source = chain.cornerFan.chart.source ∩ capSupport :=
    chain.cornerFan.chart.restr_source' capSupport capSupport_open
  have capChart_apply (y : S) : capChart y = capAffine (chain.cornerFan.chart y) := rfl
  have capChart_ks_source : (chain.q ρ ks).val ∈ capChart.source := by
    rw [capChart_source]
    exact ⟨cap_ks_chart.1,cap_ks_support⟩
  have capChart_ks_zero : capChart (chain.q ρ ks).val = 0 := by
    rw [capChart_apply,cap_ks_chart.2]
    ext j
    fin_cases j
    · change chain.oldCornerX s-chain.oldCornerX s = 0
      ring
    · change (chain.oldCornerSign*chain.oldCornerScale*capHeight s-
        chain.cornerEntry 1*(chain.oldCornerX s+chain.cornerDelta)/(L+chain.cornerDelta))/
          (chain.oldCornerSign*chain.oldCornerScale) = 0
      have hx := capTau_x ⟨s,⟨le_rfl,hsc.le⟩⟩
      have hh := cap_height_chart ⟨s,⟨le_rfl,hsc.le⟩⟩
      apply (div_eq_zero_iff).2 (Or.inl ?_)
      apply (sub_eq_zero).2
      apply (eq_div_iff hden.ne').2
      rw [← hh,← hx]
      ring
  have capChart_axis (t : Interval) (ht : (chain.q ρ t).val ∈ capChart.source) :
      capChart (chain.q ρ t).val 1 = 0 := by
    have htSupport := (capChart_source ▸ ht).2
    have hnot : chain.q ρ t ∉ qOutsideCorner := by
      intro hb
      exact htSupport.2 (Or.inr ⟨chain.q ρ t,hb,rfl⟩)
    have hclock : t ∈ Ioo (chain.cuts ρ chain.cornerIndex.castSucc) (chain.cuts ρ chain.cornerIndex.succ) := by
      constructor
      · by_contra hn
        exact hnot ⟨t,Or.inl (le_of_not_gt hn),rfl⟩
      · by_contra hn
        exact hnot ⟨t,Or.inr (le_of_not_gt hn),rfl⟩
    have hcutsReal : (chain.cuts ρ chain.cornerIndex.castSucc).val <
      (chain.cuts ρ chain.cornerIndex.succ).val := cap_cuts_strict
    let ξ : Interval := ⟨(t.val-(chain.cuts ρ chain.cornerIndex.castSucc).val)/
      ((chain.cuts ρ chain.cornerIndex.succ).val-(chain.cuts ρ chain.cornerIndex.castSucc).val),by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hclock.1.le) (sub_pos.mpr hcutsReal).le
      · apply (div_le_one (sub_pos.mpr hcutsReal)).2
        exact sub_le_sub_right (show t.val ≤ (chain.cuts ρ chain.cornerIndex.succ).val from hclock.2.le) _⟩
    have hξ : CurveComplex.BranchedDoubleCover.intervalAffine
        (chain.cuts ρ chain.cornerIndex.castSucc) (chain.cuts ρ chain.cornerIndex.succ) ξ = t := by
      apply Subtype.ext
      change (1-ξ.val)*(chain.cuts ρ chain.cornerIndex.castSucc).val+
        ξ.val*(chain.cuts ρ chain.cornerIndex.succ).val = t.val
      dsimp [ξ]
      field_simp [(sub_pos.mpr hcutsReal).ne']
      <;> ring
    have he : chain.q ρ t = chain.piece ρ chain.cornerIndex ξ := by
      rw [chain.piece_clock,hξ]
    have hf := chain.corner_formula ρ ξ
    rw [capChart_apply,he,hf.2,chain.cornerFan.chart.right_inv hf.1]
    change (chain.cornerEntry 1*(1-ξ.val)-chain.cornerEntry 1*
      ((-chain.cornerDelta+(1-ξ.val)*(chain.cornerEntry 0-chain.cornerEpsilon ρ+chain.cornerDelta))+chain.cornerDelta)/
        (L+chain.cornerDelta))/(chain.oldCornerSign*chain.oldCornerScale) = 0
    change (chain.cornerEntry 1*(1-ξ.val)-chain.cornerEntry 1*
      ((-chain.cornerDelta+(1-ξ.val)*(L+chain.cornerDelta))+chain.cornerDelta)/
        (L+chain.cornerDelta))/(chain.oldCornerSign*chain.oldCornerScale) = 0
    apply div_eq_zero_iff.mpr (Or.inl ?_)
    apply sub_eq_zero.mpr
    apply (eq_div_iff hden.ne').mpr
    ring
  have capChart_positive_exterior (y : ↥F) (hy : y.val ∈ capChart.source)
      (hpos : 0 < capChart y.val 1) : y ∉ range sweep := by
    intro hD
    have hySupport := (capChart_source ▸ hy).2
    rw [hsweepRange] at hD
    rcases hD with (hd | hg) | hk
    · exact hySupport.2 (Or.inl (Or.inl ⟨y,hd,rfl⟩))
    · exact hySupport.2 (Or.inl (Or.inr ⟨y,hg,rfl⟩))
    · have hh := capAffine_hull_nonpositive (chain.cornerFan.chart y.val) hk.2
      rw [capChart_apply] at hpos
      exact (not_lt_of_ge hh) hpos
  let Vcal : Set S := capChart.source
  have Vcal_open : IsOpen Vcal := capChart.open_source
  have Vcal_interior : Vcal ⊆ interior F := by
    intro y hy
    change y ∈ capChart.source at hy
    exact (capChart_source ▸ hy).2.1.2
  have Vcal_clear (y : ↥F) (hy : y.val ∈ Vcal) : y ∈ Uclear := by
    change y.val ∈ capChart.source at hy
    have hh : y ∈ (Subtype.val : ↥F → S) ⁻¹' Wclear := (capChart_source ▸ hy).2.1.1
    exact hWpre ▸ hh
  -- E2: calibrate the whole proper-q strip at its original interior clock.
  let Nwhole : C(Interval × Icc (-1 : ℝ) 1,↥F) := ⟨fun p =>
    N (p.1,⟨δ*p.2.val,by constructor <;> nlinarith [p.2.property.1,p.2.property.2,hδ.1,hδ.2]⟩),by fun_prop⟩
  have Nwhole_embedded : IsEmbedding Nwhole := by
    apply (Nwhole.continuous.isClosedEmbedding ?_).isEmbedding
    intro p q he
    have hh := hN.injective he
    apply Prod.ext
    · have hf := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.1) hh
      exact hf
    · apply Subtype.ext
      have hw := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => p.2.val) hh
      change δ*p.2.val = δ*q.2.val at hw
      exact mul_left_cancel₀ hδ.1.ne' hw
  have Nwhole_center (t : Interval) : Nwhole (t,⟨0,by norm_num⟩) = chain.q ρ t := by
    change N (t,⟨δ*0,_⟩) = _
    simpa using hNc t
  have Nwhole_prefix (t : Interval) (w : Icc (-1 : ℝ) 1) :
      Nwhole (prefixClock t,w) = narrowPrefix (t,w) := (hNarrowFormula (t,w)).symm
  let qAmbient : C(Interval,S) :=
    ⟨fun t => (chain.q ρ t).val,continuous_subtype_val.comp (chain.q ρ).continuous⟩
  let NwholeAmbient : Interval × Icc (-1 : ℝ) 1 → S := fun p => (Nwhole p).val
  have NwholeAmbient_embedded : IsEmbedding NwholeAmbient := IsEmbedding.subtypeVal.comp Nwhole_embedded
  obtain ⟨ω,hω,ε,δcal,η,Ψ,hε,hδcal,hη,hΨq,hΨoutside,hΨcal⟩ :=
    source_internal_collar_calibration qAmbient
      (IsEmbedding.subtypeVal.comp (chain.q_embedded ρ)) NwholeAmbient NwholeAmbient_embedded
      (fun t => congrArg Subtype.val (Nwhole_center t)) ks ⟨hks0,show ks.val < 1 from hksz.trans_le (show z ≤ (1 : Interval) from z.property.2)⟩
      capChart capChart_ks_source capChart_ks_zero capChart_axis
      univ Vcal isOpen_univ Vcal_open (subset_univ _) capChart_ks_source (subset_univ _)
  have Ψ_preserves (P : Set S) (hVP : Vcal ⊆ P) (y : S) : Ψ y ∈ P ↔ y ∈ P := by
    constructor
    · intro hy
      by_contra hn
      have hv : y ∉ Vcal := fun h => hn (hVP h)
      rw [hΨoutside y hv] at hy
      exact hn hy
    · intro hy
      by_contra hn
      have hv : Ψ y ∉ Vcal := fun h => hn (hVP h)
      have he : Ψ y = y := Ψ.injective (hΨoutside (Ψ y) hv)
      rw [he] at hn
      exact hn hy
  have Ψ_preserves_F (y : S) : Ψ y ∈ F ↔ y ∈ F :=
    Ψ_preserves F (Vcal_interior.trans interior_subset) y
  have Ψ_preserves_interior (y : S) : Ψ y ∈ interior F ↔ y ∈ interior F :=
    Ψ_preserves (interior F) Vcal_interior y
  have Vcal_Wclear : Vcal ⊆ Wclear := by
    intro y hy
    change y ∈ capChart.source at hy
    exact (capChart_source ▸ hy).2.1.1
  have Ψ_preserves_clear (y : S) : Ψ y ∈ Wclear ↔ y ∈ Wclear :=
    Ψ_preserves Wclear Vcal_Wclear y
  have Ψ_fixes_boundary (y : S) (hy : y ∈ boundaryCircle) : Ψ y = y := by
    apply hΨoutside
    intro hVcal
    have hf : y ∈ frontier F := by
      rw [hfrontier]
      exact Or.inl hy
    exact hf.2 (Vcal_interior hVcal)
  let CalWhole : C(Interval × Icc (-1 : ℝ) 1,↥F) := ⟨fun p =>
    ⟨Ψ (Nwhole (p.1,⟨ω*p.2.val,by constructor <;> nlinarith [p.2.property.1,p.2.property.2,hω.1,hω.2]⟩)).val,
      (Ψ_preserves_F _).2 (Nwhole _).property⟩,by
    apply Continuous.subtype_mk
    exact Ψ.continuous.comp (continuous_subtype_val.comp
      (Nwhole.continuous.comp (by fun_prop)))⟩
  have CalWhole_embedded : IsEmbedding CalWhole := by
    apply (CalWhole.continuous.isClosedEmbedding ?_).isEmbedding
    intro p q he
    have hh := Nwhole_embedded.injective (Subtype.ext (Ψ.injective (congrArg Subtype.val he)))
    apply Prod.ext
    · have hf := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.1) hh
      exact hf
    · apply Subtype.ext
      have hw := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => p.2.val) hh
      change ω*p.2.val = ω*q.2.val at hw
      exact mul_left_cancel₀ hω.1.ne' hw
  have CalWhole_center (t : Interval) : CalWhole (t,⟨0,by norm_num⟩) = chain.q ρ t := by
    apply Subtype.ext
    change Ψ (Nwhole (t,⟨ω*0,_⟩)).val = _
    simp only [mul_zero,Nwhole_center]
    exact hΨq t
  have CalWhole_cal (t : Interval) (w : Icc (-1 : ℝ) 1) (ht : |t.val-ks.val| < η) :
      (CalWhole (t,w)).val ∈ capChart.source ∧
      capChart (CalWhole (t,w)).val = Plane.mk (capChart (chain.q ρ t).val 0) (ε*δcal*w.val) :=
    hΨcal t w ht
  have CalWhole_prefix_clear (t : Interval) (w : Icc (-1 : ℝ) 1) :
      CalWhole (prefixClock t,w) ∈ Uclear := by
    have hn : Nwhole (prefixClock t,⟨ω*w.val,by constructor <;> nlinarith [w.property.1,w.property.2,hω.1,hω.2]⟩) ∈ Uclear := by
      rw [Nwhole_prefix]
      exact hNarrowU (mem_range_self _)
    have hw : (Nwhole (prefixClock t,⟨ω*w.val,by constructor <;> nlinarith [w.property.1,w.property.2,hω.1,hω.2]⟩)).val ∈ Wclear :=
      show Nwhole _ ∈ (Subtype.val : ↥F → S) ⁻¹' Wclear from hWpre.symm ▸ hn
    have hp : CalWhole (prefixClock t,w) ∈ (Subtype.val : ↥F → S) ⁻¹' Wclear :=
      (Ψ_preserves_clear _).2 hw
    exact hWpre ▸ hp
  have CalWhole_prefix_start (w : Icc (-1 : ℝ) 1) :
      (CalWhole (prefixClock 0,w)).val ∈ boundaryCircle := by
    change Ψ (Nwhole (prefixClock 0,⟨ω*w.val,_⟩)).val ∈ boundaryCircle
    rw [Nwhole_prefix]
    have hb := narrowPrefix_start ⟨ω*w.val,by constructor <;> nlinarith [w.property.1,w.property.2,hω.1,hω.2]⟩
    rw [Ψ_fixes_boundary _ hb]
    exact hb
  have CalWhole_prefix_interior (t : Interval) (ht : 0 < t) (w : Icc (-1 : ℝ) 1) :
      (CalWhole (prefixClock t,w)).val ∈ interior F := by
    change Ψ (Nwhole (prefixClock t,⟨ω*w.val,_⟩)).val ∈ interior F
    apply (Ψ_preserves_interior _).2
    rw [Nwhole_prefix]
    exact narrowPrefix_interior t ht _
  have cap_margin_pos : 0 < chain.oldCornerWidth-capHeight s := by
    have hm := capHeight_small ⟨s,⟨le_rfl,hsc.le⟩⟩
    linarith
  let lamWidth : ℝ := min 1 ((chain.oldCornerWidth-capHeight s)/(2*δcal))
  have hlamWidth : 0 < lamWidth ∧ lamWidth ≤ 1 :=
    ⟨lt_min (by norm_num) (div_pos cap_margin_pos (mul_pos (by norm_num) hδcal)),min_le_left _ _⟩
  let κ : ℝ := δcal*lamWidth
  have hκ : 0 < κ := mul_pos hδcal hlamWidth.1
  have hκwidth : capHeight s+κ < chain.oldCornerWidth := by
    have hle := min_le_right (1 : ℝ) ((chain.oldCornerWidth-capHeight s)/(2*δcal))
    have hm : lamWidth*(2*δcal) ≤ chain.oldCornerWidth-capHeight s :=
      (le_div_iff₀ (mul_pos (by norm_num) hδcal)).mp hle
    change capHeight s+δcal*lamWidth < _
    linarith
  have ε_nonzero : ε ≠ 0 := by
    rcases hε with he | he <;> rw [he] <;> norm_num
  have ε_square : ε*ε = 1 := by
    rcases hε with he | he <;> rw [he] <;> norm_num
  let Rhalf : C(Interval × Interval,↥F) := ⟨fun p =>
    CalWhole (prefixClock p.1,⟨ε*lamWidth*p.2.val,by
      rcases hε with he | he <;> rw [he] <;>
        constructor <;> nlinarith [p.2.property.1,p.2.property.2,hlamWidth.1,hlamWidth.2]⟩),by fun_prop⟩
  have Rhalf_embedded : IsEmbedding Rhalf := by
    apply (Rhalf.continuous.isClosedEmbedding ?_).isEmbedding
    intro p q he
    have hh := CalWhole_embedded.injective he
    apply Prod.ext
    · exact prefixClock_injective (congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.1) hh)
    · apply Subtype.ext
      have hw := congrArg (fun z : Interval × Icc (-1 : ℝ) 1 => z.2.val) hh
      change ε*lamWidth*p.2.val = ε*lamWidth*q.2.val at hw
      exact mul_left_cancel₀ (mul_ne_zero ε_nonzero hlamWidth.1.ne') hw
  have Rhalf_clear (t u : Interval) : Rhalf (t,u) ∈ Uclear := CalWhole_prefix_clear t _
  have Rhalf_V : range Rhalf ⊆ V := by
    rintro y ⟨⟨t,u⟩,rfl⟩
    exact (Rhalf_clear t u).1
  have Rhalf_center (t : Interval) : Rhalf (t,0) = chain.q ρ (prefixClock t) := by
    change CalWhole (prefixClock t,⟨ε*lamWidth*0,_⟩) = _
    simpa only [mul_zero] using CalWhole_center (prefixClock t)
  have Rhalf_start (u : Interval) : (Rhalf (0,u)).val ∈ boundaryCircle := CalWhole_prefix_start _
  have Rhalf_interior (t : Interval) (ht : 0 < t) (u : Interval) :
      (Rhalf (t,u)).val ∈ interior F := CalWhole_prefix_interior t ht _
  have Rhalf_clear_negative : Disjoint (range Rhalf) oldNegative := by
    apply disjoint_left.mpr
    rintro y ⟨⟨t,u⟩,rfl⟩ hn
    exact (Rhalf_clear t u).2 (Or.inl hn)
  have Rhalf_clear_old : Disjoint (range Rhalf) (range (r v).val.val) := by
    apply disjoint_left.mpr
    rintro y ⟨⟨t,u⟩,rfl⟩ ha
    exact (Rhalf_clear t u).2 (Or.inr ha)
  let terminalSize : ℝ := min (1/2) (η/(2*ks.val))
  have terminalSize_pos : 0 < terminalSize :=
    lt_min (by norm_num) (div_pos hη (mul_pos (by norm_num) hks0))
  have terminalSize_le : terminalSize ≤ 1/2 := min_le_left _ _
  have terminalSize_bound : terminalSize*(2*ks.val) ≤ η :=
    (le_div_iff₀ (mul_pos (by norm_num) hks0)).mp (min_le_right _ _)
  let t₀ : Interval := ⟨1-terminalSize,by
    constructor <;> linarith only [terminalSize_pos,terminalSize_le]⟩
  have ht₀ : t₀ < 1 := by change 1-terminalSize < 1; linarith
  have ks_real_positive : (0 : ℝ) < ks.val := hks0
  have prefix_near_cap (t : Interval) (ht : t₀ ≤ t) : |(prefixClock t).val-ks.val| < η := by
    rw [prefixClock_val,abs_of_nonpos (by nlinarith only [t.property.2,ks_real_positive] : ks.val*t.val-ks.val ≤ 0)]
    have htt : 1-terminalSize ≤ t.val := ht
    nlinarith only [htt,terminalSize_bound,hη,ks_real_positive]
  have capAffine_vertical (p : Plane) (v : ℝ) :
      capAffine (p+Plane.mk 0 (chain.oldCornerSign*chain.oldCornerScale*v)) = capAffine p+Plane.mk 0 v := by
    ext j
    fin_cases j
    · change p 0+0-chain.oldCornerX s = (p 0-chain.oldCornerX s)+0
      ring
    · change (p 1+chain.oldCornerSign*chain.oldCornerScale*v-
        chain.cornerEntry 1*(p 0+0+chain.cornerDelta)/(L+chain.cornerDelta))/
          (chain.oldCornerSign*chain.oldCornerScale) =
        (p 1-chain.cornerEntry 1*(p 0+chain.cornerDelta)/(L+chain.cornerDelta))/
          (chain.oldCornerSign*chain.oldCornerScale)+v
      field_simp [cap_sign_nonzero,chain.oldCornerScale_pos.ne',hden.ne']
      <;> ring
  have Rhalf_germ (t : Interval) (ht : t₀ ≤ t) (u : Interval) :
      (Rhalf (t,u)).val ∈ chain.cornerFan.chart.source ∧
      (chain.q ρ (prefixClock t)).val ∈ chain.cornerFan.chart.source ∧
      chain.cornerFan.chart (Rhalf (t,u)).val =
        chain.cornerFan.chart (chain.q ρ (prefixClock t)).val+
          Plane.mk 0 (chain.oldCornerSign*chain.oldCornerScale*κ*u.val) := by
    have hnear := prefix_near_cap t ht
    have hcal := CalWhole_cal (prefixClock t)
      ⟨ε*lamWidth*u.val,by rcases hε with he | he <;> rw [he] <;>
        constructor <;> nlinarith [u.property.1,u.property.2,hlamWidth.1,hlamWidth.2]⟩ hnear
    have hzero := CalWhole_cal (prefixClock t) ⟨0,by norm_num⟩ hnear
    rw [CalWhole_center] at hzero
    have hr : (Rhalf (t,u)).val ∈ capChart.source := hcal.1
    have hq : (chain.q ρ (prefixClock t)).val ∈ capChart.source := hzero.1
    refine ⟨(capChart_source ▸ hr).1,(capChart_source ▸ hq).1,?_⟩
    apply capAffine.injective
    have hv := capAffine_vertical (chain.cornerFan.chart (chain.q ρ (prefixClock t)).val) (κ*u.val)
    simp only [mul_assoc] at hv ⊢
    rw [hv]
    have hχ : capChart (Rhalf (t,u)).val = capChart (chain.q ρ (prefixClock t)).val+Plane.mk 0 (κ*u.val) := by
      rw [show capChart (Rhalf (t,u)).val =
        Plane.mk (capChart (chain.q ρ (prefixClock t)).val 0) (ε*δcal*(ε*lamWidth*u.val)) from hcal.2]
      ext j
      fin_cases j
      · change capChart (chain.q ρ (prefixClock t)).val 0 = capChart (chain.q ρ (prefixClock t)).val 0+0
        ring
      · change ε*δcal*(ε*lamWidth*u.val) = capChart (chain.q ρ (prefixClock t)).val 1+κ*u.val
        rw [capChart_axis _ hq]
        dsimp [κ]
        calc ε*δcal*(ε*lamWidth*u.val) = (ε*ε)*(δcal*lamWidth*u.val) := by ring
             _ = 0+δcal*lamWidth*u.val := by rw [ε_square]; ring
    simpa only [capChart_apply,mul_assoc] using hχ
  obtain ⟨port,hport,hportChart⟩ := affinePort κ hκ hκwidth
  have Rhalf_terminal (u : Interval) : Rhalf (1,u) = chain.oldStrip (chain.clock s,port u) := by
    have hg := Rhalf_germ 1 ht₀.le u
    have hc : prefixClock 1 = ks := by apply Subtype.ext; rw [prefixClock_val]; simp
    rw [hc] at hg
    apply Subtype.ext
    apply chain.cornerFan.chart.injOn hg.1 (hportChart u).1
    rw [hg.2.2,cap_ks_chart.2,(hportChart u).2]
    ext j
    fin_cases j
    · change chain.oldCornerX s+0 = chain.oldCornerX s
      ring
    · change chain.oldCornerSign*chain.oldCornerScale*capHeight s+
        chain.oldCornerSign*chain.oldCornerScale*κ*u.val =
        chain.oldCornerSign*chain.oldCornerScale*(capHeight s+κ*u.val)
      ring
  -- E3: select the exterior of the unchanged actual sweep by the calibrated cap seed.
  have Rhalf_off_q (t u : Interval) (hu : 0 < u) : Rhalf (t,u) ∉ range (chain.q ρ) := by
    rintro ⟨k,hk⟩
    have he : CalWhole (prefixClock t,⟨ε*lamWidth*u.val,by
        rcases hε with he | he <;> rw [he] <;>
          constructor <;> nlinarith [u.property.1,u.property.2,hlamWidth.1,hlamWidth.2]⟩) =
        CalWhole (k,⟨0,by norm_num⟩) := hk.symm.trans (CalWhole_center k).symm
    have hh := CalWhole_embedded.injective he
    have hw := congrArg (fun p : Interval × Icc (-1 : ℝ) 1 => p.2.val) hh
    change ε*lamWidth*u.val = 0 at hw
    exact (mul_ne_zero (mul_ne_zero ε_nonzero hlamWidth.1.ne') (show u.val ≠ 0 from (show (0 : ℝ) < u.val from hu).ne')) hw
  let positiveProduct : Set (Interval × Interval) := Ioc (0 : Interval) 1 ×ˢ Ioc (0 : Interval) 1
  let Rambient : C(Interval × Interval,S) :=
    ⟨fun p => (Rhalf p).val,continuous_subtype_val.comp Rhalf.continuous⟩
  let positiveImage : Set S := Rambient '' positiveProduct
  have positiveImage_preconnected : IsPreconnected positiveImage :=
    (isPreconnected_Ioc.prod isPreconnected_Ioc).image Rambient Rambient.continuous.continuousOn
  let sweepAmbient : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
    ⟨fun p => (sweep p).val,continuous_subtype_val.comp sweep.continuous⟩
  have sweepAmbient_embedded : IsEmbedding sweepAmbient := IsEmbedding.subtypeVal.comp hsweep
  have positiveImage_sphere_clear : Disjoint positiveImage
      (sweepAmbient '' {y | y.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    apply disjoint_left.mpr
    rintro y ⟨⟨t,u⟩,⟨ht,hu⟩,rfl⟩ ⟨p,hp,he⟩
    have hR : Rhalf (t,u) ∈ sweep '' {y | y.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
      ⟨p,hp,Subtype.ext he⟩
    rw [hsweepSphere] at hR
    rcases hR with (ha | hq) | hβ
    · apply disjoint_left.mp Rhalf_clear_old (mem_range_self _) 
      rcases ha with ⟨k,hk,he⟩
      exact ⟨chain.clock k,he⟩
    · exact Rhalf_off_q t u hu.1 (image_subset_range _ _ hq)
    · have hB := (chain.boundaryExtension_in_BV ρ hβ).1
      have hf : (Rhalf (t,u)).val ∈ frontier F := by
        rw [hfrontier]
        exact Or.inl hB
      exact hf.2 (Rhalf_interior t ht.1 u)
  let halfPoint : Interval := ⟨1/2,by norm_num⟩
  have halfPoint_pos : 0 < halfPoint := by change (0:ℝ) < 1/2; norm_num
  have Rhalf_cap_seed : Rhalf (1,halfPoint) ∉ range sweep := by
    have hc : prefixClock 1 = ks := by apply Subtype.ext; rw [prefixClock_val]; simp
    have hcal := CalWhole_cal (prefixClock 1)
      ⟨ε*lamWidth*halfPoint.val,by rcases hε with he | he <;> rw [he] <;>
        constructor <;> nlinarith [halfPoint.property.1,halfPoint.property.2,hlamWidth.1,hlamWidth.2]⟩
      (prefix_near_cap 1 ht₀.le)
    apply capChart_positive_exterior (Rhalf (1,halfPoint)) hcal.1
    rw [show capChart (Rhalf (1,halfPoint)).val =
      Plane.mk (capChart (chain.q ρ (prefixClock 1)).val 0) (ε*δcal*(ε*lamWidth*halfPoint.val)) from hcal.2]
    change 0 < ε*δcal*(ε*lamWidth*halfPoint.val)
    have he : ε*δcal*(ε*lamWidth*halfPoint.val) = κ*halfPoint.val := by
      dsimp [κ]
      calc ε*δcal*(ε*lamWidth*halfPoint.val) = (ε*ε)*(δcal*lamWidth*halfPoint.val) := by ring
           _ = δcal*lamWidth*halfPoint.val := by rw [ε_square]; ring
    rw [he]
    exact mul_pos hκ halfPoint_pos
  have positiveImage_exterior : positiveImage ⊆ (range sweepAmbient)ᶜ := by
    rcases RegionalEmbeddedFamily.connected_open_set_avoiding_disk_boundary_dichotomy
      positiveImage positiveImage_preconnected sweepAmbient sweepAmbient_embedded positiveImage_sphere_clear with hi | ho
    · exfalso
      have hp : Rambient (1,halfPoint) ∈ positiveImage :=
        ⟨(1,halfPoint),⟨⟨by norm_num,le_rfl⟩,⟨halfPoint_pos,halfPoint.property.2⟩⟩,rfl⟩
      have hh := interior_subset (hi hp)
      obtain ⟨p,he⟩ := hh
      exact Rhalf_cap_seed ⟨p,Subtype.ext he⟩
    · exact ho
  have Rhalf_positive_exterior (t u : Interval) (ht : 0 < t) (hu : 0 < u) : Rhalf (t,u) ∉ range sweep := by
    intro hd
    have hp : Rambient (t,u) ∈ positiveImage :=
      ⟨(t,u),⟨⟨ht,t.property.2⟩,⟨hu,u.property.2⟩⟩,rfl⟩
    apply positiveImage_exterior hp
    rcases hd with ⟨p,he⟩
    exact ⟨p,congrArg Subtype.val he⟩
  have Rhalf_start_exterior (u : Interval) (hu : 0 < u) : Rhalf (0,u) ∉ range sweep := by
    intro hd
    have hf : (Rhalf (0,u)).val ∈ frontier F := by
      rw [hfrontier]
      exact Or.inl (Rhalf_start u)
    have hβ : Rhalf (0,u) ∈ range (chain.boundaryExtension ρ) := hsweepFrontier ▸ ⟨hd,hf⟩
    obtain ⟨b,hb⟩ := hβ
    have hb0 : b ≠ 0 := by
      intro he
      apply disjoint_left.mp Rhalf_clear_old (mem_range_self _)
      rw [he,chain.boundaryExtension_zero] at hb
      rw [← hb,d.first_eq]
      exact mem_range_self _
    have hb1 : b ≠ 1 := by
      intro he
      have hp0 : prefixClock 0 = 0 := by apply Subtype.ext; rw [prefixClock_val]; simp
      have hz : Rhalf (0,0) = chain.boundaryExtension ρ 1 := by
        rw [Rhalf_center,hp0,chain.q_zero,chain.boundaryExtension_one]
      have hEq : Rhalf (0,u) = Rhalf (0,0) := by rw [← hb,he,← hz]
      have hw := congrArg Prod.snd (Rhalf_embedded.injective hEq)
      exact hu.ne' hw
    have hbStrict : b ∈ Ioo (0 : Interval) 1 :=
      ⟨lt_of_le_of_ne b.property.1 (Ne.symm hb0),lt_of_le_of_ne b.property.2 hb1⟩
    have hInside : Rhalf (0,u) ∈ interior (range sweep : Set ↥F) :=
      sweep_B_relative_interior ⟨b,hbStrict,hb⟩
    let Utime : Set Interval := (fun t : Interval => Rhalf (t,u)) ⁻¹' interior (range sweep : Set ↥F)
    have hUtime : IsOpen Utime := isOpen_interior.preimage (Rhalf.continuous.comp (by fun_prop))
    have hzTime : (0 : Interval) ∈ Utime := hInside
    have hzCl : (0 : Interval) ∈ closure (Ioc (0 : Interval) 1) := by
      rw [closure_Ioc (by norm_num : (0 : Interval) ≠ 1)]
      exact ⟨le_rfl,by norm_num⟩
    obtain ⟨t,htU,htPos⟩ := mem_closure_iff.mp hzCl Utime hUtime hzTime
    exact Rhalf_positive_exterior t u htPos.1 hu (interior_subset htU)
  have Rhalf_nonzero_exterior (t u : Interval) (hu : 0 < u) : Rhalf (t,u) ∉ range sweep := by
    by_cases ht : 0 < t
    · exact Rhalf_positive_exterior t u ht hu
    · have hz : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt ht) t.property.1)
      rw [hz]
      exact Rhalf_start_exterior u hu
  have prefixClock_surjective (k : Interval) (hk : k ∈ Icc (0 : Interval) ks) : ∃ t, prefixClock t = k := by
    let t : Interval := ⟨k.val/ks.val,by
      constructor
      · exact div_nonneg k.property.1 hks0.le
      · exact (div_le_one hks0).mpr hk.2⟩
    refine ⟨t,Subtype.ext ?_⟩
    rw [prefixClock_val]
    change ks.val*(k.val/ks.val) = k.val
    field_simp [ks_real_positive.ne']
  have Rhalf_sweep_inter : range Rhalf ∩ range sweep = chain.q ρ '' Icc (0 : Interval) ks := by
    ext y
    constructor
    · rintro ⟨⟨⟨t,u⟩,rfl⟩,hd⟩
      have hu : u = 0 := by
        by_contra hn
        have hp : 0 < u := lt_of_le_of_ne u.property.1 (Ne.symm hn)
        exact Rhalf_nonzero_exterior t u hp hd
      rw [hu,Rhalf_center]
      exact ⟨prefixClock t,prefixClock_range t,rfl⟩
    · intro hy
      refine ⟨?_,qprefix_in_sweep hy⟩
      obtain ⟨k,hk,rfl⟩ := hy
      obtain ⟨t,ht⟩ := prefixClock_surjective k hk
      exact ⟨(t,0),by rw [Rhalf_center,ht]⟩
  refine ⟨s,rCap,hsc,hs0,hcr,hr1,cap_interval_old_window,capTau,h,capClock,hh,?_,?_,
    capTau_pos _,capTau_lt_one _ hsc,capTau_cut,capTau_strictMono,capClock_cut,
    capClock_strictMono,capClock_start_bounds.1,capClock_start_bounds.2,(fun _ => rfl),?_,
    capHeight_cut,capHeight_pos,capHeight_strictAnti,cap_vertical_in_hull,?_⟩
  · intro t
    have hx := capTau_x t
    dsimp [L] at hx
    nlinarith only [hx]
  · intro t
    have he := cap_height_chart t
    have hnonzero : chain.oldCornerSign*chain.oldCornerScale ≠ 0 := by
      rcases chain.oldCornerSign_unit with hs | hs <;> rw [hs] <;>
        simpa using chain.oldCornerScale_pos.ne'
    apply (eq_div_iff hnonzero).mpr
    change capHeight t.val * (chain.oldCornerSign*chain.oldCornerScale) = _
    nlinarith only [he]
  · intro t
    exact cap_graph t
  · refine ⟨κ,port,Rhalf,hκ,hκwidth,hport,Rhalf_embedded,Rhalf_V,Rhalf_center,
      Rhalf_start,Rhalf_interior,Rhalf_terminal,Rhalf_sweep_inter,Rhalf_clear_negative,Rhalf_clear_old,t₀,ht₀,?_⟩
    exact Rhalf_germ
