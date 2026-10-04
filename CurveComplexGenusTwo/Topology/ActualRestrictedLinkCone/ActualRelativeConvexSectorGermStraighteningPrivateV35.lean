import CurveComplexGenusTwo.Filtration.Geometry.ActualSupportCrosscutAlignment
import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import CurveComplexGenusTwo.Topology.Smoothing.FirstExitPrefixHeader
import CurveComplexGenusTwo.Topology.Smoothing.ConvexSectorChartHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
import CurveComplexGenusTwo.Topology.Smoothing.RadialSectorSplitHeader
import CurveComplexGenusTwo.Topology.Smoothing.SectorBoundaryInvariantHeader
import CurveComplexGenusTwo.Topology.Smoothing.SectorSplitNonemptyHeader
import Mathlib.Topology.Algebra.Module.FiniteDimension
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedTrimmedCrosscutAssembly
import CurveComplexGenusTwo.Topology.ActualMain14FinitePreparation.Main14ActualRelativeTransverseCrosscutRedrawingLocalNamedPROVED
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import CurveComplexGenusTwo.Topology.WeightedSurgery.IsolatedArcNeighborhood
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof
import CurveComplexGenusTwo.Topology.GeometricPosition.IntervalSubdivision
import CurveComplexGenusTwo.Topology.PositionExtension.FlatBumpTranslation
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization
import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import CurveComplexGenusTwo.Topology.Smoothing.FirstExitPrefixHeader
import CurveComplexGenusTwo.Topology.Smoothing.ConvexSectorChartHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
import CurveComplexGenusTwo.Topology.Smoothing.RadialSectorSplitHeader
import CurveComplexGenusTwo.Topology.Smoothing.SectorBoundaryInvariantHeader
import CurveComplexGenusTwo.Topology.Smoothing.SectorSplitNonemptyHeader
import Mathlib.Topology.Algebra.Module.FiniteDimension
open Set Metric Schoenflies CurveComplex.FiniteStarGeometry CurveComplex Bornology
set_option maxHeartbeats 2200000

private theorem actual_relative_convex_sector_germ_straightening_private {J K : Type} (Q : K → Set Plane) (v : J → Plane)
    (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0:Plane) ∈ Q k)
    (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
    (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ ⋃ j, segment ℝ (0:Plane) (v j))
    (hcellne : ∀ k, (interior (Q k)).Nonempty)
    (hcenter : ∀ k, (0:Plane) ∈ frontier (Q k))
    (hfan : ∀ k, Disjoint (interior (Q k)) (⋃ j, segment ℝ (0:Plane) (v j)))
    (hv : ∀ j, ‖v j‖ = R)
    {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
    (ha : a ∉ closedBall (0:Plane) R)
    (havoid : ∀ t : I, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
    ∃ (F : Plane ≃ₜ Plane) (c : I) (k : K),
      0 < c.val ∧ c.val < 1 ∧ ‖α c‖ = R ∧
      α c ∈ frontier (Q k) ∧
      segment ℝ (0:Plane) (α c) \ {0,α c} ⊆ interior (Q k) ∧
      F '' (α '' Icc 0 c) = segment ℝ (0:Plane) (α c) ∧
      F 0 = 0 ∧ (∀ x, x ∉ interior (Q k) → F x = x) ∧
      (∀ x, x ∉ ball (0:Plane) R → F x = x) ∧
      (∀ x ∈ ⋃ j, segment ℝ (0:Plane) (v j), F x = x) := by
  have firstExit {J K : Type} (Q : K → Set Plane) (v : J → Plane)
      (R : ℝ) (hR : 0 < R)
      (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
      (hzero : ∀ k, (0:Plane) ∈ Q k)
      (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
      (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
      (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
      (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ ⋃ j, segment ℝ (0:Plane) (v j))
      (hv : ∀ j, ‖v j‖ = R)
      {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
      (ha : a ∉ closedBall (0:Plane) R)
      (havoid : ∀ t : I, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
      ∃ (c : I) (k : K), 0 < c.val ∧ c.val < 1 ∧
        ‖α c‖ = R ∧ α c ∈ frontier (Q k) ∧
        IsArcBetween (α '' Icc 0 c) 0 (α c) ∧
        (α '' Icc 0 c) \ {0,α c} ⊆ interior (Q k) ∧
        segment ℝ (0:Plane) (α c) \ {0,α c} ⊆ interior (Q k) := by
    classical
    have select (U : K → Set Plane) (hU : ∀ k, IsOpen (U k))
        (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
        (c t₀ : I) (ht₀ : t₀ ∈ Ioo zeroI c)
        (hc : ∀ t ∈ Ioo zeroI c, α t ∈ ⋃ k, U k) :
        ∃ k, ∀ t ∈ Ioo zeroI c, α t ∈ U k := by
      obtain ⟨k,hk⟩ := mem_iUnion.mp (hc t₀ ht₀)
      let W := ⋃ (j : K) (_ : j ≠ k), U j
      have hW : IsOpen W := isOpen_iUnion (fun j => isOpen_iUnion (fun _ => hU j))
      have hdW : Disjoint (U k) W := by
        apply Set.disjoint_left.mpr
        intro x hx hxW
        obtain ⟨j,hj⟩ := mem_iUnion.mp hxW
        obtain ⟨hne,hxj⟩ := mem_iUnion.mp hj
        exact Set.disjoint_left.mp (hd hne.symm) hx hxj
      have hp : α '' Ioo zeroI c ⊆ U k ∪ W := by
        rintro x ⟨t,ht,rfl⟩
        obtain ⟨j,hj⟩ := mem_iUnion.mp (hc t ht)
        by_cases he : j = k
        · exact Or.inl (he ▸ hj)
        · exact Or.inr (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨he,hj⟩⟩)
      have hsel : α '' Ioo zeroI c ⊆ U k :=
        (isPreconnected_Ioo.image α α.continuous.continuousOn).subset_left_of_subset_union
          (hU k) hW hdW hp ⟨α t₀,⟨⟨t₀,ht₀,rfl⟩,hk⟩⟩
      exact ⟨k,fun t ht => hsel ⟨t,ht,rfl⟩⟩
    have nonsphere {x : Plane} (hb : x ∈ ball (0:Plane) R) : x ∉ sphere (0:Plane) R := by
      simp only [mem_ball,mem_sphere,dist_zero_right] at *
      exact ne_of_lt hb
    have haopen : a ∉ ball (0:Plane) R := fun hm => ha (ball_subset_closedBall hm)
    obtain ⟨c,hc,γ,hex,hγ,himage,hbefore⟩ :=
      CurveComplex.SeedProbeHeaders.embedded_first_exit_prefix α hα
        (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
    have heR : ‖α c‖ = R := by
      rw [frontier_ball (0:Plane) (ne_of_gt hR)] at hex
      simpa only [mem_sphere,dist_zero_right] using hex
    have hc1 : c < 1 := by
      apply lt_of_le_of_ne c.property.2
      intro he
      apply ha
      rw [show c = 1 from Subtype.ext he] at heR
      simpa only [α.target,mem_closedBall,dist_zero_right] using heR.le
    have hrawbefore : ∀ t : I, t < c → α t ∈ ball (0:Plane) R := by
      obtain ⟨d,hd,hdf,hdb⟩ := CurveComplex.path_first_exit_frontier α
        (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
      have hdle : d ≤ c := by
        by_contra hn
        have hm := hdb c (lt_of_not_ge hn)
        exact (show α c ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hex.2) hm
      have hcd : c ≤ d := by
        by_contra hn
        have hdγ : α d ∈ range γ := by
          rw [himage]
          exact ⟨d,⟨d.property.1,(lt_of_not_ge hn).le⟩,rfl⟩
        obtain ⟨s,hs⟩ := hdγ
        have hs1 : s < 1 := by
          apply lt_of_le_of_ne s.property.2
          intro he
          have hsone : s = 1 := Subtype.ext he
          have hdc : d = c := hα (hs.symm.trans (hsone ▸ γ.target))
          exact (ne_of_lt (lt_of_not_ge hn)) hdc
        have hm := hbefore s hs1
        rw [hs] at hm
        exact (show α d ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hdf.2) hm
      exact fun t ht => hdb t (ht.trans_le hcd)
    have hcellcover : ∀ t ∈ Ioo zeroI c, α t ∈ ⋃ k, interior (Q k) := by
      intro t ht
      have hb := hrawbefore t ht.2
      obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover (ball_subset_closedBall hb))
      refine mem_iUnion.mpr ⟨k,?_⟩
      by_contra hn
      have hfr : α t ∈ frontier (Q k) := by
        rw [(hclosed k).frontier_eq]
        exact ⟨hk,hn⟩
      rcases hfront k hfr with hs | hf
      · exact (nonsphere hb) hs
      · exact havoid t ht.1 hf
    let t₀ : I := ⟨c.val/2,by constructor <;> nlinarith [c.property.1,c.property.2]⟩
    have ht₀ : t₀ ∈ Ioo zeroI c := by
      have hcr : 0 < c.val := hc
      constructor
      · change 0 < c.val/2
        linarith
      · change c.val/2 < c.val
        linarith
    obtain ⟨k,hk⟩ := select (fun k => interior (Q k)) (fun _ => isOpen_interior)
      hdisj c t₀ ht₀ hcellcover
    have heQ : α c ∈ Q k := by
      have hcc : c ∈ closure (Ioo zeroI c : Set I) := by
        rw [closure_Ioo (show zeroI ≠ c from ne_of_lt hc)]
        exact ⟨hc.le,le_rfl⟩
      have hsub : Ioo zeroI c ⊆ α ⁻¹' Q k := by
        intro t ht
        change α t ∈ Q k
        exact interior_subset (hk t ht)
      exact ((hclosed k).preimage α.continuous).closure_subset_iff.mpr hsub hcc
    have hefront : α c ∈ frontier (Q k) := by
      rw [(hclosed k).frontier_eq]
      refine ⟨heQ,?_⟩
      intro hm
      have hb : α c ∈ interior (closedBall (0:Plane) R) := interior_mono (hinside k) hm
      rw [interior_closedBall (0:Plane) (ne_of_gt hR)] at hb
      exact (nonsphere hb) (by simpa only [mem_sphere,dist_zero_right] using heR)
    have hArc : IsArcBetween (α '' Icc 0 c) 0 (α c) := by
      refine ⟨γ.extend,γ.continuous_extend.continuousOn,?_,?_,γ.extend_zero,γ.extend_one⟩
      · intro s hs t ht he
        rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
        exact congrArg Subtype.val (hγ he)
      · exact (γ.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans himage
    refine ⟨c,k,hc,hc1,heR,hefront,hArc,?_,?_⟩
    · rintro x ⟨⟨t,ht,rfl⟩,hne⟩
      have ht0 : zeroI < t := by
        apply lt_of_le_of_ne t.property.1
        intro he
        have he0 : t = 0 := Subtype.ext he.symm
        exact hne (by simp [he0,α.source])
      have htc : t < c := by
        apply lt_of_le_of_ne ht.2
        intro he
        exact hne (by simp [he])
      exact hk t ⟨ht0,htc⟩
    · intro x hx
      have hxQ : x ∈ Q k := (hconvex k).segment_subset (hzero k) heQ hx.1
      have hxne0 : x ≠ 0 := by intro he; exact hx.2 (by simp [he])
      have hxnee : x ≠ α c := by intro he; exact hx.2 (by simp [he])
      have hxo : x ∈ openSegment ℝ (0:Plane) (α c) :=
        mem_openSegment_of_ne_left_right hxne0.symm hxnee.symm hx.1
      obtain ⟨a,b,ha,hb,hab,hxb⟩ := hxo
      have hxb' : x = b • α c := by simpa using hxb.symm
      have hxball : x ∈ ball (0:Plane) R := by
        rw [mem_ball,dist_zero_right,hxb',norm_smul,Real.norm_eq_abs,abs_of_pos hb,heR]
        have hb1 : b < 1 := by linarith
        nlinarith
      by_contra hn
      have hxfr : x ∈ frontier (Q k) := by
        rw [(hclosed k).frontier_eq]
        exact ⟨hxQ,hn⟩
      rcases hfront k hxfr with hs | hf
      · exact (nonsphere hxball) hs
      · obtain ⟨j,hj⟩ := mem_iUnion.mp hf
        have hejne : α c ≠ v j := by
          intro he
          apply havoid c hc
          exact mem_iUnion.mpr ⟨j,he ▸ right_mem_segment ℝ 0 (v j)⟩
        have hmeet := LeanEval.Topology.ClassificationOfSurfaces.Moise.radial_segments_inter
          (center := (0:Plane)) (p := α c) (q := v j) (radius := R) hR
          (by simpa only [dist_zero_right] using heR)
          (by simpa only [dist_zero_right] using hv j) hejne
        have hxzero : x ∈ ({0} : Set Plane) := hmeet ▸ ⟨hx.1,hj⟩
        exact hxne0 hxzero
  obtain ⟨c,k,hc,hc1,heR,hefront,hA,hAi,hBi⟩ :=
    firstExit Q v R hR hclosed hconvex hzero hinside hcover hdisj hfront hv α hα ha havoid
  have hbounded : Bornology.IsBounded (Q k) :=
    isBounded_closedBall.subset (hinside k)
  obtain ⟨E,hEi,hEQ,hEf,hJ⟩ := convex_sector_ambient_square_chart (Q k) (hconvex k) (hclosed k) (hcellne k) hbounded
  have hclint : closure (interior (Q k)) = Q k := by
    exact ((hconvex k).closure_interior_eq_closure_of_nonempty_interior (hcellne k)).trans (hclosed k).closure_eq
  have hfrontint : frontier (interior (Q k)) = frontier (Q k) := by
    simp only [frontier,isOpen_interior.interior_eq,hclint,(hclosed k).closure_eq]
  have hinsideEq : interior (Q k) = inside (frontier (Q k)) :=
    bounded_jordan_frontier_region_eq_inside hJ isOpen_interior ((hconvex k).interior.isConnected (hcellne k))
      (hbounded.subset interior_subset) hfrontint
  have hene : (0:Plane) ≠ α c := by
    intro he
    rw [← he,norm_zero] at heR
    linarith
  have hB : IsArcBetween (segment ℝ (0:Plane) (α c)) 0 (α c) := isArcBetween_segment hene
  obtain ⟨aMap⟩ := exists_arcHomeo hA hB
  obtain ⟨F,hpoint,himage,hfix⟩ := jordan_sector_prescribed_crosscut_ambient_extension hJ (hcenter k) hefront hA hB
    (by simpa only [← hinsideEq] using hAi)
    (by simpa only [← hinsideEq] using hBi) aMap
  have hfixQ : ∀ x, x ∉ interior (Q k) → F x = x := by
    simpa only [← hinsideEq] using hfix
  refine ⟨F,c,k,hc,hc1,heR,hefront,hBi,himage,?_,hfixQ,?_,?_⟩
  · apply hfixQ
    have hz : (0:Plane) ∈ Q k \ interior (Q k) := (hclosed k).frontier_eq ▸ hcenter k
    exact hz.2
  · intro x hx
    apply hfixQ
    intro hi
    have hb : x ∈ interior (closedBall (0:Plane) R) := interior_mono (hinside k) hi
    rw [interior_closedBall (0:Plane) (ne_of_gt hR)] at hb
    exact hx hb
  · intro x hx
    apply hfixQ
    intro hi
    exact Set.disjoint_left.mp (hfan k) hi hx



private theorem actual_radially_closed_fixed_set_alexander_isotopy_private (R : ℝ) (hR : 0 < R) (F : Plane ≃ₜ Plane)
    (hFfix : ∀ x, R ≤ ‖x‖ → F x = x) (hFzero : F 0 = 0)
    (P : Set Plane) (hPscale : ∀ x ∈ P, ∀ c : ℝ, 1 ≤ c → c • x ∈ P)
    (hPfix : ∀ x ∈ P, F x = x) :
    ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
      (∀ t x, R ≤ ‖x‖ → H.map (t,x) = x) ∧
    (∀ t, H.map (t,0) = 0) ∧ ∀ t x, x ∈ P → H.map (t,x) = x := by
  have hFbound (x : Plane) (hx : ‖x‖ ≤ R) : ‖F x‖ ≤ R := by
    by_contra hn
    have heq : F x = x := F.injective (hFfix (F x) (le_of_not_ge hn))
    exact hn (by rw [heq]; exact hx)
  have hdisp (x : Plane) : ‖F x - x‖ ≤ 2 * R := by
    by_cases hx : ‖x‖ ≤ R
    · exact (norm_sub_le _ _).trans (by linarith [hFbound x hx])
    · rw [hFfix x (le_of_not_ge hx), sub_self, norm_zero]
      linarith
  let G : Interval × Plane → Plane := fun z =>
    if (z.1 : ℝ) = 0 then z.2 else (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2)
  have hGbound (z : Interval × Plane) :
      dist (G z) z.2 ≤ (2 * R) * (z.1 : ℝ) := by
    by_cases ht : (z.1 : ℝ) = 0
    · simp only [G, ht, ite_true, dist_self, mul_zero, le_refl]
    · dsimp only [G]
      rw [if_neg ht, dist_eq_norm]
      have heq : (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2) - z.2 =
          (z.1 : ℝ) • (F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2) := by
        rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.property.1]
      calc
        (z.1 : ℝ) * ‖F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2‖ ≤
            (z.1 : ℝ) * (2 * R) :=
          mul_le_mul_of_nonneg_left (hdisp _) z.1.property.1
        _ = (2 * R) * (z.1 : ℝ) := mul_comm _ _
  have hGc : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases ht : (z.1 : ℝ) = 0
    · have hGz : G z = z.2 := by simp only [G, ht, ite_true]
      change Filter.Tendsto G (nhds z) (nhds (G z))
      rw [hGz, tendsto_iff_dist_tendsto_zero]
      have hlim : Filter.Tendsto
          (fun w : Interval × Plane => (2 * R) * (w.1 : ℝ) + dist w.2 z.2)
          (nhds z) (nhds 0) := by
        have hc : Continuous (fun w : Interval × Plane =>
            (2 * R) * (w.1 : ℝ) + dist w.2 z.2) := by fun_prop
        simpa only [ContinuousAt, ht, mul_zero, dist_self, add_zero] using hc.continuousAt (x := z)
      exact squeeze_zero (fun w => dist_nonneg) (fun w =>
        (dist_triangle (G w) w.2 z.2).trans (add_le_add (hGbound w) le_rfl)) hlim
    · have hc : ContinuousAt
          (fun w : Interval × Plane => (w.1 : ℝ) • F ((w.1 : ℝ)⁻¹ • w.2)) z := by
        fun_prop (disch := assumption)
      apply hc.congr_of_eventuallyEq
      have hevent : ∀ᶠ w : Interval × Plane in nhds z, (w.1 : ℝ) ≠ 0 :=
        (continuous_subtype_val.comp continuous_fst).continuousAt.eventually_ne ht
      exact hevent.mono (fun w hw => if_neg hw)
  refine ⟨{ map := ⟨G, hGc⟩, homeomorphism_at := ?_, at_zero := ?_ }, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : (t : ℝ) = 0
    · exact ⟨Homeomorph.refl _, fun x => by
        change x = G (t, x)
        simp only [G, ht, ite_true]⟩
    · let u : ℝˣ := Units.mk0 (t : ℝ) ht
      let e := ((Homeomorph.smul u⁻¹).trans F).trans (Homeomorph.smul u)
      refine ⟨e, ?_⟩
      intro x
      change (t : ℝ) • F ((t : ℝ)⁻¹ • x) = G (t, x)
      dsimp only [G]
      rw [if_neg ht]
  · intro x
    simp [G]
  · funext x
    simp [AmbientIsotopy.finalMap, G]
  · intro t x hx
    change G (t, x) = x
    by_cases ht : (t : ℝ) = 0
    · simp only [G, ht, ite_true]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have hlarge : R ≤ ‖(t : ℝ)⁻¹ • x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), inv_mul_eq_div]
        apply (le_div_iff₀ htpos).mpr
        nlinarith [t.property.2]
      simp only [G, if_neg ht, hFfix _ hlarge, smul_smul, mul_inv_cancel₀ ht, one_smul]
  · intro t
    change G (t,0) = 0
    by_cases ht : (t:ℝ) = 0
    · simp only [G,ht,ite_true]
    · simp only [G,if_neg ht,smul_zero,hFzero]
  · intro t x hx
    change G (t,x) = x
    by_cases ht : (t : ℝ) = 0
    · simp only [G,ht,ite_true]
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have hlarge : 1 ≤ (t : ℝ)⁻¹ := (one_le_inv₀ htpos).mpr t.property.2
      have hp := hPfix _ (hPscale x hx _ hlarge)
      simp only [G,if_neg ht,hp,smul_smul,mul_inv_cancel₀ ht,one_smul]

#print axioms actual_relative_convex_sector_germ_straightening_private
#print axioms actual_radially_closed_fixed_set_alexander_isotopy_private

private theorem actual_relative_convex_sector_germ_supported_isotopy_private {J K : Type} (Q : K → Set Plane) (v : J → Plane)
    (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0:Plane) ∈ Q k)
    (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
    (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ ⋃ j, segment ℝ (0:Plane) (v j))
    (hcellne : ∀ k, (interior (Q k)).Nonempty)
    (hcenter : ∀ k, (0:Plane) ∈ frontier (Q k))
    (hfan : ∀ k, Disjoint (interior (Q k)) (⋃ j, segment ℝ (0:Plane) (v j)))
    (hv : ∀ j, ‖v j‖ = R)
    {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
    (ha : a ∉ closedBall (0:Plane) R)
    (havoid : ∀ t : I, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
    ∃ (H : AmbientIsotopy Plane) (c : I) (k : K),
      0 < c.val ∧ c.val < 1 ∧ ‖α c‖ = R ∧
      H.finalMap '' (α '' Icc 0 c) = segment ℝ (0:Plane) (α c) ∧
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ interior (Q k) → H.map (t,x) = x) ∧
      (∀ t x, x ∉ ball (0:Plane) R → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, segment ℝ (0:Plane) (v j) → H.map (t,x) = x) := by
  obtain ⟨F,c,k,hc,hc1,heR,_,_,himage,hF0,hfix,hball,hfanfix⟩ :=
    actual_relative_convex_sector_germ_straightening_private Q v R hR hclosed hconvex
      hzero hinside hcover hdisj hfront hcellne hcenter hfan hv α hα ha havoid
  have hscale : ∀ x ∈ (interior (Q k))ᶜ, ∀ d : ℝ, 1 ≤ d →
      d • x ∈ (interior (Q k))ᶜ := by
    intro x hx d hd hi
    have hdpos : 0 < d := by linarith
    have hdi : 0 < d⁻¹ := inv_pos.mpr hdpos
    have hdi1 : d⁻¹ ≤ 1 := (inv_le_one₀ hdpos).mpr hd
    have hh := (hconvex k).combo_interior_self_mem_interior hi (hzero k)
      hdi (show 0 ≤ 1-d⁻¹ by linarith) (show d⁻¹+(1-d⁻¹)=1 by ring)
    simp only [smul_zero,add_zero,smul_smul,inv_mul_cancel₀ (ne_of_gt hdpos),one_smul] at hh
    exact hx hh
  obtain ⟨H,hHF,hHball,hH0,hHQ⟩ :=
    actual_radially_closed_fixed_set_alexander_isotopy_private R hR F
      (fun x hx => hball x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx))
      hF0 (interior (Q k))ᶜ hscale hfix
  refine ⟨H,c,k,hc,hc1,heR,?_,hH0,hHQ,?_,?_⟩
  · rw [hHF]; exact himage
  · intro t x hx
    exact hHball t x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx)
  · intro t x hx
    apply hHQ t x
    intro hi
    exact Set.disjoint_left.mp (hfan k) hi hx

#print axioms actual_relative_convex_sector_germ_supported_isotopy_private

private theorem actual_radial_sector_split_preserves_literal_background_private {K : Type} (Q : K → Set Plane) (F : Set Plane)
    (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0:Plane) ∈ Q k) (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
    (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ F)
    (hcellne : ∀ k, (interior (Q k)).Nonempty)
    (hcenter : ∀ k, (0:Plane) ∈ frontier (Q k))
    (hfan : ∀ k, Disjoint (interior (Q k)) F)
    (hsupport : ∀ k, ∃ L : Plane →L[ℝ] ℝ,
      (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ F))
    (k₀ : K) (e : Plane) (heQ : e ∈ Q k₀) (heR : ‖e‖ = R) (heF : e ∉ F)
    (hproper : segment ℝ (0:Plane) e \ {0,e} ⊆ interior (Q k₀)) :
    ∃ (K' : Type) (Q' : K' → Set Plane),
      (∀ k, IsClosed (Q' k)) ∧ (∀ k, Convex ℝ (Q' k)) ∧
      (∀ k, (0:Plane) ∈ Q' k) ∧ (∀ k, Q' k ⊆ closedBall (0:Plane) R) ∧
      (closedBall (0:Plane) R ⊆ ⋃ k, Q' k) ∧
      (Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l)))) ∧
      (∀ k, frontier (Q' k) ⊆ sphere (0:Plane) R ∪ (F ∪ segment ℝ (0:Plane) e)) ∧
      (∀ k, (interior (Q' k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q' k)) ∧
      (∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e)) ∧
      (∀ k, ∃ L : Plane →L[ℝ] ℝ,
        (∀ x ∈ Q' k, 0 ≤ L x) ∧
        (∀ x ∈ Q' k, L x = 0 → x ∈ F ∪ segment ℝ (0:Plane) e)) := by
  classical
  have halfInt (e : Plane) (he : e ≠ 0) :
      interior {x : Plane | 0 ≤ Plane.det e x} = {x | 0 < Plane.det e x} ∧
      interior {x : Plane | Plane.det e x ≤ 0} = {x | Plane.det e x < 0} := by
    let D : Plane →ₗ[ℝ] ℝ := {
      toFun := fun x => Plane.det e x
      map_add' := Plane.det_add_right e
      map_smul' := fun r x => Plane.det_smul_right r e x }
    have hcont : Continuous D := by
      change Continuous (fun x : Plane => Plane.det e x)
      unfold Plane.det
      exact (continuous_const.mul (Plane.continuous_coord 1)).sub
        (continuous_const.mul (Plane.continuous_coord 0))
    have hnorm : ‖e‖^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr he))
    have hsurj : Function.Surjective D := by
      intro r
      refine ⟨(r / ‖e‖^2) • Plane.perp e,?_⟩
      change Plane.det e ((r / ‖e‖^2) • Plane.perp e) = r
      rw [Plane.det_smul_right,Plane.det_perp_self]
      exact div_mul_cancel₀ r hnorm
    have hopen : IsOpenMap D := D.isOpenMap_of_finiteDimensional hsurj
    constructor
    · change interior (D ⁻¹' Ici (0:ℝ)) = D ⁻¹' Ioi (0:ℝ)
      rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Ici]
    · change interior (D ⁻¹' Iic (0:ℝ)) = D ⁻¹' Iio (0:ℝ)
      rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Iic]
  have hen : e ≠ 0 := by intro he; simp [he] at heR; linarith
  obtain ⟨L,hL,hker⟩ := hsupport k₀
  have heL : 0 < L e := lt_of_le_of_ne (hL e heQ) (fun hz => heF (hker e heQ hz.symm))
  let A := Q k₀ ∩ {x | 0 ≤ Plane.det e x}
  let B := Q k₀ ∩ {x | Plane.det e x ≤ 0}
  obtain ⟨hab,hinter,hca,hcb⟩ := radial_sector_determinant_split
    (Q k₀) (hconvex k₀) R hR (hinside k₀) (hzero k₀) e heQ heR L hL heL
  have hcont : Continuous (fun x : Plane => Plane.det e x) := by
    unfold Plane.det
    exact (continuous_const.mul (Plane.continuous_coord 1)).sub
      (continuous_const.mul (Plane.continuous_coord 0))
  have haClosed : IsClosed A := (hclosed k₀).inter (isClosed_le continuous_const hcont)
  have hbClosed : IsClosed B := (hclosed k₀).inter (isClosed_le hcont continuous_const)
  obtain ⟨hfa,hfb,hdab⟩ := sector_split_frontier_invariant (Q k₀) (hclosed k₀) e hen hinter
  have hhalf : (1/2:ℝ) • e ∈ segment ℝ (0:Plane) e \ {0,e} := by
    refine ⟨⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by simp⟩,?_⟩
    intro hh
    have hh' : (1/2:ℝ) • e = 0 ∨ (1/2:ℝ) • e = e := by simpa using hh
    rcases hh' with hh|hh
    · exact hen ((smul_eq_zero.mp hh).resolve_left (by norm_num))
    · have hz : (-1/2:ℝ) • e = 0 := by calc
        (-1/2:ℝ) • e = (1/2:ℝ) • e - e := by module
        _ = 0 := by rw [hh,sub_self]
      exact hen ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  obtain ⟨hneA,hneB⟩ := sector_split_interiors_nonempty (Q k₀) ((1/2:ℝ) • e) e
    (hproper hhalf) hen (by simp)
  let K' := Sum {k : K // k ≠ k₀} Bool
  let Q' : K' → Set Plane := Sum.elim (fun k => Q k.val) (fun b => if b then B else A)
  have hnewclosed : ∀ k, IsClosed (Q' k) := by
    intro k
    cases k with
    | inl k => exact hclosed k.val
    | inr b => cases b; exact haClosed; exact hbClosed
  have hmona : interior A ⊆ interior (Q k₀) := interior_mono inter_subset_left
  have hmonb : interior B ⊆ interior (Q k₀) := interior_mono inter_subset_left
  have hnewzero : ∀ k, (0:Plane) ∈ Q' k := by
    intro k
    cases k with
    | inl k => exact hzero k.val
    | inr b => cases b <;> exact ⟨hzero k₀,by simp [Plane.det]⟩
  have newSubsetOld : ∀ k : K', ∃ j : K, Q' k ⊆ Q j := by
    intro k
    cases k with
    | inl k => exact ⟨k.val,Subset.refl _⟩
    | inr b => cases b <;> exact ⟨k₀,inter_subset_left⟩
  have hnewinside : ∀ k, Q' k ⊆ closedBall (0:Plane) R := by
    intro k
    obtain ⟨j,hj⟩ := newSubsetOld k
    exact hj.trans (hinside j)
  have hnewcenter : ∀ k, (0:Plane) ∈ frontier (Q' k) := by
    intro k
    rw [(hnewclosed k).frontier_eq]
    refine ⟨hnewzero k,?_⟩
    intro hi
    obtain ⟨j,hj⟩ := newSubsetOld k
    have hj0 : (0:Plane) ∉ interior (Q j) := by
      have hh : (0:Plane) ∈ Q j \ interior (Q j) := (hclosed j).frontier_eq ▸ hcenter j
      exact hh.2
    exact hj0 (interior_mono hj hi)
  have hnewdisj : Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l))) := by
    intro k l hkl
    cases k with
    | inl k =>
      cases l with
      | inl l => exact hdisj (fun he => hkl (congrArg Sum.inl (Subtype.ext he)))
      | inr b => cases b; exact (hdisj k.property).mono_right hmona; exact (hdisj k.property).mono_right hmonb
    | inr b =>
      cases l with
      | inl l => cases b; exact (hdisj l.property.symm).mono_left hmona; exact (hdisj l.property.symm).mono_left hmonb
      | inr c => cases b <;> cases c
                 · exact False.elim (hkl rfl)
                 · exact hdab
                 · exact hdab.symm
                 · exact False.elim (hkl rfl)
  have hnewfan : ∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e) := by
    intro k
    apply Set.disjoint_left.mpr
    intro x hi hx
    obtain ⟨j,hj⟩ := newSubsetOld k
    rcases hx with hf|hr
    · exact Set.disjoint_left.mp (hfan j) (interior_mono hj hi) hf
    · have hd : Plane.det e x = 0 := by
        obtain ⟨a,b,ha,hb,hab,hx⟩ := hr
        rw [← hx]
        simp
      cases k with
      | inl k =>
        by_cases hx0 : x = 0
        · have hh : x ∈ frontier (Q' (.inl k)) := hx0.symm ▸ hnewcenter (.inl k)
          have hh' : x ∈ Q' (.inl k) \ interior (Q' (.inl k)) := (hnewclosed _).frontier_eq ▸ hh
          exact hh'.2 hi
        by_cases hxe : x = e
        · have hb : e ∈ ball (0:Plane) R := by
            have hh := interior_mono (hinside k.val) (show x ∈ interior (Q k.val) from hi)
            rw [interior_closedBall (0:Plane) (ne_of_gt hR),hxe] at hh
            exact hh
          have hh : ‖e‖ < R := by simpa only [mem_ball,dist_zero_right] using hb
          exact (ne_of_lt hh) heR
        have hip : x ∈ interior (Q k₀) := hproper ⟨hr,by simpa using And.intro hx0 hxe⟩
        exact Set.disjoint_left.mp (hdisj k.property) hi hip
      | inr b =>
        cases b
        · have hp := interior_mono (show A ⊆ {x | 0 ≤ Plane.det e x} from inter_subset_right) hi
          rw [(halfInt e hen).1] at hp
          exact (ne_of_gt (show 0 < Plane.det e x from hp)) hd
        · have hn := interior_mono (show B ⊆ {x | Plane.det e x ≤ 0} from inter_subset_right) hi
          rw [(halfInt e hen).2] at hn
          exact (ne_of_lt (show Plane.det e x < 0 from hn)) hd
  refine ⟨K',Q',hnewclosed,?_,hnewzero,hnewinside,?_,hnewdisj,?_,?_,hnewcenter,hnewfan,?_⟩
  · intro k
    cases k with
    | inl k => exact hconvex k.val
    | inr b => cases b; exact hca; exact hcb
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hje : j = k₀
    · subst j
      have hxAB : x ∈ A ∪ B := hab.symm ▸ hj
      rcases hxAB with hxA|hxB
      · exact mem_iUnion.mpr ⟨.inr false,hxA⟩
      · exact mem_iUnion.mpr ⟨.inr true,hxB⟩
    · exact mem_iUnion.mpr ⟨.inl ⟨j,hje⟩,hj⟩
  · intro k x hx
    cases k with
    | inl k =>
      rcases hfront k.val hx with hs|hf
      · exact Or.inl hs
      · exact Or.inr (Or.inl hf)
    | inr b =>
      have hh : x ∈ frontier (Q k₀) ∪ segment ℝ (0:Plane) e := by
        cases b; exact hfa hx; exact hfb hx
      rcases hh with hfr|hr
      · rcases hfront k₀ hfr with hs|hf
        · exact Or.inl hs
        · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr hr)
  · intro k
    cases k with
    | inl k => exact hcellne k.val
    | inr b => cases b; exact hneA; exact hneB
  · intro k
    obtain ⟨j,hj⟩ := newSubsetOld k
    obtain ⟨Lj,hLj,hkj⟩ := hsupport j
    exact ⟨Lj,fun x hx => hLj x (hj hx),fun x hx he => Or.inl (hkj x (hj hx) he)⟩
#print axioms actual_radial_sector_split_preserves_literal_background_private

private theorem actual_finite_star_completion_with_actual_sector_cells_private {J : Type} [Fintype J] (γ : J → I → Plane)
    (hγ : ∀ j, Topology.IsClosedEmbedding (γ j)) (hstart : ∀ j, γ j zeroI = 0)
    (hmeet : ∀ i j, i ≠ j → range (γ i) ∩ range (γ j) = {0})
    (R R₀ : ℝ) (hR : 0 < R) (hRR₀ : R ≤ R₀) :
    let fan : Finset J → (J → Plane) → Set Plane := fun S w => ⋃ j, ⋃ (_ : j ∈ S), segment ℝ (0:Plane) (w j)
    let Cells : Finset J → (J → Plane) → Prop := fun S w =>
      ∃ (K : Type) (Q : K → Set Plane),
        (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
        (∀ k, (0:Plane) ∈ Q k) ∧ (∀ k, Q k ⊆ closedBall (0:Plane) R) ∧
        (closedBall (0:Plane) R ⊆ ⋃ k, Q k) ∧
        (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
        (∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ fan S w) ∧
        (∀ k, (interior (Q k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q k)) ∧
        (∀ k, Disjoint (interior (Q k)) (fan S w)) ∧
        (∀ k, ∃ L : Plane →L[ℝ] ℝ,
          (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ fan S w))
    ∀ (S₀ : Finset J) (H₀ : Plane ≃ₜ Plane) (c₀ : J → I) (w₀ : J → Plane),
      H₀ 0 = 0 → (∀ x, x ∉ ball (0:Plane) R₀ → H₀ x = x) →
      (∀ j, H₀ (γ j oneI) ∉ closedBall (0:Plane) R) →
      (∀ j ∈ S₀, 0 < (c₀ j).val ∧ (c₀ j).val < 1 ∧ ‖w₀ j‖ = R ∧
        H₀ '' (γ j '' Icc 0 (c₀ j)) = segment ℝ (0:Plane) (w₀ j)) →
      Cells S₀ w₀ →
      ∃ (H : Plane ≃ₜ Plane) (c : J → I) (w : J → Plane),
        H 0 = 0 ∧ (∀ x, x ∉ ball (0:Plane) R₀ → H x = x) ∧
        (∀ j, 0 < (c j).val ∧ (c j).val < 1 ∧ ‖w j‖ = R ∧
          H '' (γ j '' Icc 0 (c j)) = segment ℝ (0:Plane) (w j)) ∧
        (∀ j ∈ S₀, w j = w₀ j) ∧ Cells Finset.univ w ∧
      (∀ j ∈ S₀, ∀ x ∈ γ j '' Icc 0 (c₀ j), H x = H₀ x) := by
  classical
  intro fan Cells S₀ H₀ c₀ w₀ hH₀ hfix₀ hend₀ hprefix₀ hCells₀
  let State : Finset J → Prop := fun S =>
    ∃ (H : Plane ≃ₜ Plane) (c : J → I) (w : J → Plane),
      H 0 = 0 ∧ (∀ x, x ∉ ball (0:Plane) R₀ → H x = x) ∧
      (∀ j, H (γ j oneI) ∉ closedBall (0:Plane) R) ∧
      (∀ j ∈ S, 0 < (c j).val ∧ (c j).val < 1 ∧ ‖w j‖ = R ∧
        H '' (γ j '' Icc 0 (c j)) = segment ℝ (0:Plane) (w j)) ∧ Cells S w ∧ (∀ j ∈ S₀, w j = w₀ j) ∧
      (∀ j ∈ S₀, ∀ x ∈ γ j '' Icc 0 (c₀ j), H x = H₀ x)
  have hbase : State S₀ := ⟨H₀,c₀,w₀,hH₀,hfix₀,hend₀,hprefix₀,hCells₀,(fun j _ => rfl),fun j hj x hx => rfl⟩
  have fanSubtype (S : Finset J) (w : J → Plane) :
      fan S w = ⋃ i : {i : J // i ∈ S}, segment ℝ (0:Plane) (w i.val) := by
    ext x
    simp [fan]
  have step (S : Finset J) (hseed : S₀ ⊆ S) (hS : State S) (j : J) (hj : j ∉ S) : State (insert j S) := by
    obtain ⟨H,c,w,hH,hfix,hend,hprefix,hCells,hpres,hfixed⟩ := hS
    obtain ⟨K,Q,hclosed,hconvex,hzero,hinside,hcover,hdisj,hfront,hcellne,hcenter,hfan,hsupport⟩ := hCells
    have hzeroI : (0:I) = zeroI := by apply Subtype.ext; rfl
    let α : Path (0:Plane) (H (γ j oneI)) := {
      toFun := H ∘ γ j
      continuous_toFun := H.continuous.comp (hγ j).continuous
      source' := by
        change H (γ j 0) = 0
        rw [hzeroI,hstart j,hH]
      target' := rfl }
    have hα : Function.Injective α := H.injective.comp (hγ j).injective
    have havoid : ∀ t : I, 0 < t.val → α t ∉ fan S w := by
      intro t ht hm
      obtain ⟨i,hm⟩ := mem_iUnion.mp hm
      obtain ⟨hi,hmi⟩ := mem_iUnion.mp hm
      rw [← (hprefix i hi).2.2.2] at hmi
      obtain ⟨x,⟨s,hs,rfl⟩,he⟩ := hmi
      have he' : γ j t = γ i s := (H.injective he).symm
      have hji : j ≠ i := by intro he; exact hj (he.symm ▸ hi)
      have hz : γ j t = 0 := by
        have hp : γ j t ∈ range (γ j) ∩ range (γ i) := ⟨⟨t,rfl⟩,⟨s,he'.symm⟩⟩
        rw [hmeet j i hji] at hp
        exact hp
      have htzero : t = zeroI := (hγ j).injective (hz.trans (hstart j).symm)
      have hh : t.val = 0 := congrArg Subtype.val htzero
      linarith
    obtain ⟨T,d,k,hd,hd1,heR,hefront,hproper,himage,hT,hTQ,hTR,hTF⟩ :=
      actual_relative_convex_sector_germ_straightening_private Q (fun i : {i : J // i ∈ S} => w i.val) R hR
        hclosed hconvex hzero hinside hcover hdisj
        (by simpa only [← fanSubtype S w] using hfront) hcellne hcenter
        (by simpa only [← fanSubtype S w] using hfan)
        (fun i => (hprefix i.val i.property).2.2.1) α hα (hend j)
        (by simpa only [← fanSubtype S w] using havoid)
    have hTF' : ∀ x ∈ fan S w, T x = x := by
      simpa only [← fanSubtype S w] using hTF
    have heQ : α d ∈ Q k := (hclosed k).closure_eq ▸ frontier_subset_closure hefront
    have heF : α d ∉ fan S w := havoid d hd
    obtain ⟨K',Q',hclosed',hconvex',hzero',hinside',hcover',hdisj',hfront',hcellne',hcenter',hfan',hsupport'⟩ :=
      actual_radial_sector_split_preserves_literal_background_private Q (fan S w) R hR hclosed hconvex hzero hinside hcover hdisj
        hfront hcellne hcenter hfan hsupport k (α d) heQ heR heF hproper
    let H' := H.trans T
    let c' : J → I := Function.update c j d
    let w' : J → Plane := Function.update w j (α d)
    have hfanEq : fan (insert j S) w' = fan S w ∪ segment ℝ (0:Plane) (α d) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i,hx⟩ := mem_iUnion.mp hx
        obtain ⟨hi,hxi⟩ := mem_iUnion.mp hx
        rcases Finset.mem_insert.mp hi with he|hi
        · subst i
          exact Or.inr (by simpa [w'] using hxi)
        · have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
          exact Or.inl (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,by simpa [w',Function.update_of_ne hij] using hxi⟩⟩)
      · rintro (hx|hx)
        · obtain ⟨i,hx⟩ := mem_iUnion.mp hx
          obtain ⟨hi,hxi⟩ := mem_iUnion.mp hx
          have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
          exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hi,by simpa [w',Function.update_of_ne hij] using hxi⟩⟩
        · exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,by simpa [w'] using hx⟩⟩
    refine ⟨H',c',w',?_,?_,?_,?_,?_,?_,?_⟩
    · change T (H 0) = 0
      rw [hH,hT]
    · intro x hx
      have hxR : x ∉ ball (0:Plane) R := fun hh => hx ((ball_subset_ball hRR₀) hh)
      change T (H x) = x
      rw [hfix x hx,hTR x hxR]
    · intro i
      change T (H (γ i oneI)) ∉ closedBall (0:Plane) R
      rw [hTR _ (fun hh => hend i (ball_subset_closedBall hh))]
      exact hend i
    · intro i hi
      rcases Finset.mem_insert.mp hi with he|hi
      · subst i
        refine ⟨by simpa [c'] using hd,by simpa [c'] using hd1,by simpa [w'] using heR,?_⟩
        simp only [c',w',Function.update_self]
        change (T ∘ H) '' (γ j '' Icc 0 d) = segment ℝ 0 (α d)
        rw [image_comp]
        have hαimage : H '' (γ j '' Icc 0 d) = α '' Icc 0 d := (image_comp H (γ j) _).symm
        rw [hαimage]
        exact himage
      · have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
        have hcEq : c' i = c i := Function.update_of_ne hij _ _
        have hwEq : w' i = w i := Function.update_of_ne hij _ _
        obtain ⟨hip,hi1,hin,hiim⟩ := hprefix i hi
        refine ⟨by simpa only [hcEq] using hip,by simpa only [hcEq] using hi1,
          by simpa only [hwEq] using hin,?_⟩
        rw [hcEq,hwEq]
        change (T ∘ H) '' (γ i '' Icc 0 (c i)) = segment ℝ 0 (w i)
        rw [image_comp,hiim]
        have hEq : EqOn T id (segment ℝ (0:Plane) (w i)) := by
          intro x hx
          exact hTF' x (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩)
        simpa only [image_id] using hEq.image_eq
    · refine ⟨K',Q',hclosed',hconvex',hzero',hinside',hcover',hdisj',?_,hcellne',hcenter',?_,?_⟩
      · simpa only [hfanEq] using hfront'
      · simpa only [hfanEq] using hfan'
      · simpa only [hfanEq] using hsupport'
    · intro i hi
      have hij : i ≠ j := by intro he; exact hj (he ▸ hseed hi)
      exact (Function.update_of_ne hij _ _).trans (hpres i hi)
    · intro i hi x hx
      change T (H x) = H₀ x
      rw [hfixed i hi x hx]
      apply hTF'
      apply mem_iUnion.mpr
      refine ⟨i,mem_iUnion.mpr ⟨hseed hi,?_⟩⟩
      rw [hpres i hi,← (hprefix₀ i hi).2.2.2]
      exact ⟨x,hx,rfl⟩
  have finish (T : Finset J) : State (S₀ ∪ T) := by
    induction T using Finset.induction_on with
    | empty => simpa using hbase
    | @insert j T hjT ih =>
      by_cases hjS : j ∈ S₀ ∪ T
      · have heq : S₀ ∪ insert j T = S₀ ∪ T := by
          ext i
          simp only [Finset.mem_union,Finset.mem_insert]
          grind
        exact heq.symm ▸ ih
      · have heq : S₀ ∪ insert j T = insert j (S₀ ∪ T) := by
          ext i
          simp only [Finset.mem_union,Finset.mem_insert]
          tauto
        exact heq.symm ▸ step (S₀ ∪ T) Finset.subset_union_left ih j hjS
  obtain ⟨H,c,w,hH,hfix,hend,hprefix,hCells,hpres,hfixed⟩ := finish Finset.univ
  refine ⟨H,c,w,hH,hfix,(fun j => hprefix j (by simp)),hpres,(by
    have heq : S₀ ∪ Finset.univ = Finset.univ := by ext j; simp
    exact heq ▸ hCells),hfixed⟩
#print axioms actual_finite_star_completion_with_actual_sector_cells_private

private theorem actual_supported_radial_prefix_homeomorphism_to_graph_fixed_motion_private
    {J : Type} (v : J → Plane) (R : ℝ) (hR : 0 < R)
    (hv : ∀ j, ‖v j‖ = R) (F : Plane ≃ₜ Plane)
    (hF0 : F 0 = 0) (hFball : ∀ x, x ∉ ball (0:Plane) R → F x = x)
    (hFfan : ∀ j x, x ∈ segment ℝ (0:Plane) (v j) → F x = x) :
    ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ ball (0:Plane) R → H.map (t,x) = x) ∧
      (∀ t j (d : ℝ), 0 ≤ d → H.map (t,d • v j) = d • v j) := by
  let P : Set Plane := {x | ∃ j, ∃ d : ℝ, 0 ≤ d ∧ x = d • v j}
  have hPscale : ∀ x ∈ P, ∀ d : ℝ, 1 ≤ d → d • x ∈ P := by
    rintro x ⟨j,c,hc,rfl⟩ d hd
    exact ⟨j,d*c,mul_nonneg (by linarith) hc,smul_smul d c (v j)⟩
  have hPfix : ∀ x ∈ P, F x = x := by
    rintro x ⟨j,d,hd,rfl⟩
    by_cases hdi : d ≤ 1
    · apply hFfan j
      rw [segment_eq_image]
      refine ⟨d,⟨hd,hdi⟩,?_⟩
      simp
    · apply hFball
      simp only [mem_ball,dist_zero_right,not_lt,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hd,hv]
      nlinarith
  obtain ⟨H,hHF,hball,hzero,hP⟩ :=
    actual_radially_closed_fixed_set_alexander_isotopy_private R hR F
      (fun x hx => hFball x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx))
      hF0 P hPscale hPfix
  refine ⟨H,hHF,hzero,?_,?_⟩
  · intro t x hx
    exact hball t x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx)
  · intro t j d hd
    exact hP t _ ⟨j,d,hd,rfl⟩

#print axioms actual_supported_radial_prefix_homeomorphism_to_graph_fixed_motion_private

private theorem actual_finite_star_radialization_entire_background_ray_fixed_private {J : Type} [Fintype J] (γ : J → I → Plane)
    (hγ : ∀ j, Topology.IsClosedEmbedding (γ j)) (hstart : ∀ j, γ j zeroI = 0)
    (hmeet : ∀ i j, i ≠ j → range (γ i) ∩ range (γ j) = {0})
    (R : ℝ) (hR : 0 < R) :
    let fan : Finset J → (J → Plane) → Set Plane := fun S w => ⋃ j, ⋃ (_ : j ∈ S), segment ℝ (0:Plane) (w j)
    let Cells : Finset J → (J → Plane) → Prop := fun S w =>
      ∃ (K : Type) (Q : K → Set Plane),
        (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
        (∀ k, (0:Plane) ∈ Q k) ∧ (∀ k, Q k ⊆ closedBall (0:Plane) R) ∧
        (closedBall (0:Plane) R ⊆ ⋃ k, Q k) ∧
        (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
        (∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ fan S w) ∧
        (∀ k, (interior (Q k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q k)) ∧
        (∀ k, Disjoint (interior (Q k)) (fan S w)) ∧
        (∀ k, ∃ L : Plane →L[ℝ] ℝ,
          (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ fan S w))
    ∀ (S₀ : Finset J) (c₀ : J → I) (w₀ : J → Plane),
      (∀ j, γ j oneI ∉ closedBall (0:Plane) R) →
      (∀ j ∈ S₀, 0 < (c₀ j).val ∧ (c₀ j).val < 1 ∧ ‖w₀ j‖ = R ∧
        γ j '' Icc 0 (c₀ j) = segment ℝ (0:Plane) (w₀ j)) →
      Cells S₀ w₀ →
      ∃ (H : AmbientIsotopy Plane) (c : J → I) (w : J → Plane),
        (∀ t, H.map (t,0) = 0) ∧
        (∀ t x, x ∉ ball (0:Plane) R → H.map (t,x) = x) ∧
        (∀ t j, j ∈ S₀ → ∀ d : ℝ, 0 ≤ d → H.map (t,d • w₀ j) = d • w₀ j) ∧
        (∀ j, 0 < (c j).val ∧ (c j).val < 1 ∧ ‖w j‖ = R ∧
          H.finalMap '' (γ j '' Icc 0 (c j)) = segment ℝ (0:Plane) (w j)) ∧
        (∀ j ∈ S₀, w j = w₀ j) := by
  classical
  intro fan Cells S₀ c₀ w₀ hend₀ hprefix₀ hCells₀
  obtain ⟨F,c,w,hF0,hFball,hprefix,hpres,hCells,hfixed⟩ :=
    actual_finite_star_completion_with_actual_sector_cells_private γ hγ hstart hmeet
      R R hR le_rfl S₀ (Homeomorph.refl _) c₀ w₀ rfl (fun _ _ => rfl) hend₀
      (fun j hj => ⟨(hprefix₀ j hj).1,(hprefix₀ j hj).2.1,(hprefix₀ j hj).2.2.1,
        by simpa only [Homeomorph.refl_apply,image_id] using (hprefix₀ j hj).2.2.2⟩) hCells₀
  let v : {j : J // j ∈ S₀} → Plane := fun j => w₀ j.val
  have hv : ∀ j, ‖v j‖ = R := fun j => (hprefix₀ j.val j.property).2.2.1
  have hFfan : ∀ j x, x ∈ segment ℝ (0:Plane) (v j) → F x = x := by
    intro j x hx
    have hx' : x ∈ γ j.val '' Icc 0 (c₀ j.val) :=
      (hprefix₀ j.val j.property).2.2.2.symm ▸ hx
    exact hfixed j.val j.property x hx'
  obtain ⟨H,hHF,hH0,hHball,hHfan⟩ :=
    actual_supported_radial_prefix_homeomorphism_to_graph_fixed_motion_private v R hR
      hv F hF0 hFball hFfan
  refine ⟨H,c,w,hH0,hHball,?_,?_,hpres⟩
  · intro t j hj d hd
    exact hHfan t ⟨j,hj⟩ d hd
  · intro j
    rw [hHF]
    exact hprefix j

#print axioms actual_finite_star_radialization_entire_background_ray_fixed_private

open Lean Elab Term in
elab "checkedRecovery20actualInjectivePathIsArc" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualInjectivePathIsArc
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualSourcePrefixPullback" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualSourcePrefixPullback
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualGermSegmentAvoidingNoncollinearRay" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualGermSegmentAvoidingNoncollinearRay
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualJoinedSourceArmsArePointedArc" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualJoinedSourceArmsArePointedArc
  discard <| getConstInfo n
  return mkConst n

private theorem actual_open_sector_point_avoiding_finite_directions_private
    {K : Type} [Fintype K] (v : K → Plane)
    {U : Set Plane} (hU : IsOpen U) {x : Plane} (hx : x ∈ U) (hx1 : x 1 ≠ 0) :
    ∃ q ∈ U, q 1 = x 1 ∧ ∀ (k : K) (r : ℝ), q ≠ r • v k := by
  classical
  let f : ℝ → Plane := fun t => Plane.mk t (x 1)
  have hfc : Continuous f := by fun_prop
  let T : Set ℝ := range (fun k => (v k 0 / v k 1) * x 1)
  have hT : T.Finite := finite_range _
  have hxEq : f (x 0) = x := by
    ext i
    fin_cases i <;> simp [f]
  have hW : IsOpen (f ⁻¹' U) := hU.preimage hfc
  have hWne : (f ⁻¹' U).Nonempty := ⟨x 0, by simpa only [mem_preimage, hxEq] using hx⟩
  obtain ⟨t, htNot, htU⟩ := (hT.countable.dense_compl ℝ).exists_mem_open hW hWne
  refine ⟨f t, htU, rfl, ?_⟩
  intro k r he
  have he0 : t = r * v k 0 := by
    have hh := congrArg (fun z : Plane => z 0) he
    simpa [f] using hh
  have he1 : x 1 = r * v k 1 := by
    have hh := congrArg (fun z : Plane => z 1) he
    simpa [f] using hh
  have hv1 : v k 1 ≠ 0 := by intro hh; simp [hh] at he1; exact hx1 he1
  have htSlope : t = (v k 0 / v k 1) * x 1 := by
    rw [he0, he1]
    field_simp [hv1]
  apply htNot
  exact ⟨k, htSlope.symm⟩

/-- Genuine source prefix replacement inside an actual convex fan cell. It fixes
all cell-exterior points and chooses its new straight germ away from indexed old rays. -/
private theorem actual_old_avoiding_graph_sector_source_prefix_private
    {K : Type} [Fintype K] (v : K → Plane)
    (Q : Set Plane) (hclosed : IsClosed Q) (hconv : Convex ℝ Q)
    (hne : (interior Q).Nonempty) (hbounded : Bornology.IsBounded Q)
    (h0front : (0 : Plane) ∈ frontier Q)
    {a : Plane} (α : Path (0 : Plane) a) (hα : Function.Injective α)
    (ha : a ∉ Q) (c₀ : CurveComplex.Interval) (hc₀ : 0 < c₀)
    (hAArc : IsArcBetween (α '' Icc 0 c₀) 0 (α c₀))
    (hbfront : α c₀ ∈ frontier Q)
    (hAi : (α '' Icc 0 c₀) \ {0, α c₀} ⊆ interior Q) :
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧
      (∀ x, x ∉ interior Q → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          ∀ k, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v k} = {0} := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hne : (interior Q).Nonempty := ⟨x, hx⟩
  let g : ℝ → Plane := fun t => Plane.mk (x 0) t
  have hgc : Continuous g := by fun_prop
  have hgx : g (x 1) = x := by ext i; fin_cases i <;> simp [g]
  have hG : IsOpen (g ⁻¹' interior Q) := isOpen_interior.preimage hgc
  have hGne : (g ⁻¹' interior Q).Nonempty := ⟨x 1,by simpa only [mem_preimage,hgx] using hx⟩
  obtain ⟨t,ht0,htQ⟩ := ((finite_singleton (0:ℝ)).countable.dense_compl ℝ).exists_mem_open hG hGne
  have htne : t ≠ 0 := by simpa only [mem_compl_iff,mem_singleton_iff] using ht0
  let x' := g t
  have hx' : x' ∈ interior Q := htQ
  have hx1 : x' 1 ≠ 0 := htne
  let b := α c₀
  let allv : Option K → Plane := fun k => Option.casesOn k b v
  obtain ⟨q, hqi, hq1, hqv⟩ := actual_open_sector_point_avoiding_finite_directions_private
    allv isOpen_interior hx' hx1
  have hq0 : q ≠ 0 := by
    intro he
    apply hx1
    simpa [he] using hq1.symm
  have hb0 : b ≠ 0 := by
    intro he
    have ht0 : c₀ = 0 := hα (he.trans α.source.symm)
    exact (ne_of_gt hc₀) ht0
  have hqb : q ≠ b := by simpa [allv] using hqv none 1
  have hind : ∀ r t : ℝ, r • q = t • b → r = 0 ∧ t = 0 := by
    intro r t he
    by_cases hr : r = 0
    · refine ⟨hr, ?_⟩
      have ht : t • b = 0 := by simpa [hr] using he.symm
      exact (smul_eq_zero.mp ht).resolve_right hb0
    · exfalso
      apply hqv none (r⁻¹ * t)
      have hh := congrArg (fun z : Plane => r⁻¹ • z) he
      simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hh
  have hinter : segment ℝ (0 : Plane) q ∩ segment ℝ q b = {q} := by
    apply Subset.antisymm
    · rintro z ⟨⟨r,t,hr,ht,hrt,hzt⟩,⟨u,w,hu,hw,huw,hzw⟩⟩
      have he : (t - u) • q = w • b := by
        calc
          (t-u) • q = (r • (0 : Plane) + t • q) - u • q := by module
          _ = w • b := by rw [hzt, ← hzw]; module
      have hw0 := (hind _ _ he).2
      have hu1 : u = 1 := by linarith
      have hzq : z = q := by rw [← hzw, hw0, hu1]; simp
      exact hzq
    · intro z hz
      have he : z = q := hz
      subst z
      exact ⟨right_mem_segment ℝ 0 q, left_mem_segment ℝ q b⟩
  obtain ⟨hNArc, _⟩ := checkedRecovery20actualJoinedSourceArmsArePointedArc
    (Path.segment (0 : Plane) q) (Path.segment q b)
    (Path.segment_injective_of_ne hq0.symm)
    (Path.segment_injective_of_ne hqb)
    (by simpa only [Path.range_segment] using hinter)
  simp only [Path.range_segment] at hNArc
  let N := segment ℝ (0 : Plane) q ∪ segment ℝ q b
  change IsArcBetween N 0 b at hNArc
  have h0Q : (0 : Plane) ∈ Q := hclosed.frontier_subset h0front
  have hbQ : b ∈ Q := hclosed.frontier_subset hbfront
  have hNi : N \ {0,b} ⊆ interior Q := by
    intro z hz
    have hz0 : z ≠ 0 := fun he => hz.2 (by simp [he])
    have hzb : z ≠ b := fun he => hz.2 (by simp [he])
    by_cases hzq : z = q
    · simpa only [hzq] using hqi
    · rcases hz.1 with hz | hz
      · exact hconv.openSegment_self_interior_subset_interior h0Q hqi
          (mem_openSegment_of_ne_left_right (Ne.symm hz0) (Ne.symm hzq) hz)
      · exact hconv.openSegment_interior_self_subset_interior hqi hbQ
          (mem_openSegment_of_ne_left_right (Ne.symm hzq) hzb.symm hz)
  obtain ⟨E, hEi, hEQ, hEf, hJ⟩ := convex_sector_ambient_square_chart Q hconv hclosed hne hbounded
  have hclInt : closure (interior Q) = Q :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hne).trans hclosed.closure_eq
  have hfront : frontier (interior Q) = frontier Q := by
    simp only [frontier, isOpen_interior.interior_eq, hclInt, hclosed.closure_eq]
  have hInside : interior Q = inside (frontier Q) :=
    bounded_jordan_frontier_region_eq_inside hJ isOpen_interior
      (hconv.interior.isConnected hne) (hbounded.subset interior_subset) hfront
  obtain ⟨e⟩ := exists_arcHomeo hAArc hNArc
  obtain ⟨F, hpoint, hFN, hfix⟩ :=
    jordan_sector_prescribed_crosscut_ambient_extension hJ h0front hbfront hAArc hNArc
      (by simpa only [← hInside] using hAi)
      (by simpa only [← hInside] using hNi) e
  have hfixQ : ∀ x, x ∉ interior Q → F x = x := by simpa only [← hInside] using hfix
  have hF0 : F 0 = 0 := hfixQ 0 ((hclosed.frontier_eq ▸ h0front).2)
  have hFa : F a = a := hfixQ a (fun hh => ha (interior_subset hh))
  have hqFa : q ≠ F a := by
    rw [hFa]
    intro he
    exact ha (he ▸ interior_subset hqi)
  have hfullArc : IsArcBetween (F '' range α) 0 (F a) := by
    have hh := (checkedRecovery20actualInjectivePathIsArc α hα).image_of_injOn
      (S := Set.univ) (subset_univ _) F.continuous.continuousOn F.injective.injOn
    simpa only [hF0] using hh
  have hsub : segment ℝ (0 : Plane) q ⊆ F '' range α := by
    apply (show segment ℝ (0 : Plane) q ⊆ N from subset_union_left).trans
    rw [← hFN]
    exact image_mono (image_subset_range _ _)
  obtain ⟨c, hc, hc1, hcim⟩ := checkedRecovery20actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) (F '' range α) hfullArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    Subset.rfl hsub (hsub (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFa
  exact ⟨F, hF0, hfixQ, c, hc, hc1, q, hq0, hcim,
    fun k => checkedRecovery20actualGermSegmentAvoidingNoncollinearRay (hqv (some k))⟩


#print axioms actual_old_avoiding_graph_sector_source_prefix_private

private theorem actual_old_avoiding_graph_sector_source_prefix_supported_motion_private
    {K : Type} [Fintype K] (v : K → Plane)
    (Q : Set Plane) (hclosed : IsClosed Q) (hconv : Convex ℝ Q)
    (hne : (interior Q).Nonempty) (hbounded : Bornology.IsBounded Q)
    (h0front : (0 : Plane) ∈ frontier Q)
    {a : Plane} (α : Path (0 : Plane) a) (hα : Function.Injective α)
    (ha : a ∉ Q) (c₀ : CurveComplex.Interval) (hc₀ : 0 < c₀)
    (hAArc : IsArcBetween (α '' Icc 0 c₀) 0 (α c₀))
    (hbfront : α c₀ ∈ frontier Q)
    (hAi : (α '' Icc 0 c₀) \ {0, α c₀} ⊆ interior Q) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ interior Q → H.map (t,x) = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ H.finalMap '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          ∀ k, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v k} = {0} := by
  obtain ⟨F,hF0,hfix,c,hc,hc1,q,hq,himage,havoid⟩ :=
    actual_old_avoiding_graph_sector_source_prefix_private v Q hclosed hconv hne
      hbounded h0front α hα ha c₀ hc₀ hAArc hbfront hAi
  obtain ⟨R,hR,hQR⟩ := hbounded.subset_ball_lt 0 (0:Plane)
  have hFball : ∀ x, R ≤ ‖x‖ → F x = x := by
    intro x hx
    apply hfix
    intro hi
    have hh := hQR (interior_subset hi)
    simp only [mem_ball,dist_zero_right] at hh
    exact (not_lt.mpr hx) hh
  have h0Q : (0:Plane) ∈ Q :=
    hclosed.closure_eq ▸ frontier_subset_closure h0front
  have hscale : ∀ x ∈ (interior Q)ᶜ, ∀ d : ℝ, 1 ≤ d →
      d • x ∈ (interior Q)ᶜ := by
    intro x hx d hd hi
    have hdpos : 0 < d := by linarith
    have hdi : 0 < d⁻¹ := inv_pos.mpr hdpos
    have hdi1 : d⁻¹ ≤ 1 := (inv_le_one₀ hdpos).mpr hd
    have hh := hconv.combo_interior_self_mem_interior hi h0Q
      hdi (show 0 ≤ 1-d⁻¹ by linarith) (show d⁻¹+(1-d⁻¹)=1 by ring)
    simp only [smul_zero,add_zero,smul_smul,inv_mul_cancel₀ (ne_of_gt hdpos),one_smul] at hh
    exact hx hh
  obtain ⟨H,hHF,_,hH0,hHQ⟩ :=
    actual_radially_closed_fixed_set_alexander_isotopy_private R hR F hFball hF0
      (interior Q)ᶜ hscale hfix
  refine ⟨H,hH0,hHQ,c,hc,hc1,q,hq,?_,havoid⟩
  rw [hHF]
  exact himage

#print axioms actual_old_avoiding_graph_sector_source_prefix_supported_motion_private

namespace CurveComplex.HyperellipticModel
private theorem actual_graph_fixed_terminal_chart_motion_lift_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (p : S)
    (e : OpenPartialHomeomorph S Plane) (hpe : p ∈ e.source) (he0 : e p = 0)
    (hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = p)
    (R : ℝ) (hRT : closedBall (0:Plane) R ⊆ e.target)
    (P : Set S) (H : AmbientIsotopy Plane)
    (hH0 : ∀ t, H.map (t,0) = 0)
    (hHout : ∀ t z, z ∉ ball (0:Plane) R → H.map (t,z) = z)
    (hHP : ∀ t x, x ∈ P → x ∈ e.source → H.map (t,e x) = e x) :
    ∃ K : AmbientIsotopy S,
      (∀ t x, x ∈ M.cover.branch → K.map (t,x) = x) ∧
      (∀ t x, x ∈ P → K.map (t,x) = x) ∧
      (∀ t x, x ∉ e.source → K.map (t,x) = x) ∧
      (∀ t x, x ∈ e.source → K.map (t,x) ∈ e.source) ∧
      ∀ t x, x ∈ e.source → e (K.map (t,x)) = H.map (t,e x) := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨L,K,hL,hK,houtside⟩ := position_surface_chart_lift S e.source e.target
    e.open_source e.toHomeomorphSourceTarget (closedBall (0:Plane) R)
    (isCompact_closedBall (0:Plane) R) hRT H
    (fun t z hz => hHout t z (fun hb => hz (ball_subset_closedBall hb)))
  have hstay (t : Interval) (x : S) (hx : x ∈ e.source) :
      K.map (t,x) ∈ e.source := by
    rw [hK t ⟨x,hx⟩]
    exact (L.map (t,⟨x,hx⟩)).property
  have hcoord (t : Interval) (x : S) (hx : x ∈ e.source) :
      e (K.map (t,x)) = H.map (t,e x) := by
    rw [hK t ⟨x,hx⟩]
    exact hL t ⟨x,hx⟩
  refine ⟨K,?_,?_,houtside,hstay,hcoord⟩
  · intro t x hx
    by_cases hxs : x ∈ e.source
    · have hxp := hemarks x hxs hx
      subst x
      apply e.injOn (hstay t p hpe) hpe
      rw [hcoord t p hpe,he0,hH0]
    · exact houtside t x hxs
  · intro t x hx
    by_cases hxs : x ∈ e.source
    · apply e.injOn (hstay t x hxs) hxs
      rw [hcoord t x hxs,hHP t x hx hxs]
    · exact houtside t x hxs
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_graph_fixed_terminal_chart_motion_lift_private

private theorem actual_common_arm_pointwise_fixed_prescribed_crosscut_replacement_private
    {K L N : Set Plane} {a p b : Plane}
    (hK : IsArcBetween K a p) (hL : IsArcBetween L p b) (hN : IsArcBetween N p b)
    (hKL : K ∩ L = {p}) (hKN : K ∩ N = {p})
    (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
    (hAi : (K ∪ L) \ {a,b} ⊆ Plane.openSquare 0 1)
    (hBi : (K ∪ N) \ {a,b} ⊆ Plane.openSquare 0 1) :
    ∃ F : Plane ≃ₜ Plane,
      (∀ x ∈ K, F x = x) ∧ F '' L = N ∧
      ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
  classical
  obtain ⟨h⟩ := exists_arcHomeo hL hN
  have hId : IsHomeoOn id id K K :=
    ⟨fun _ hx => hx,fun _ hx => hx,continuous_id.continuousOn,
      continuous_id.continuousOn,⟨fun _ _ => rfl,fun _ _ => rfl⟩⟩
  have hLN : IsHomeoOn h.toFun h.invFun L N :=
    ⟨h.mapsTo,h.mapsTo_invFun,h.continuousOn_toFun,h.continuousOn_invFun,
      ⟨h.leftInvOn,h.rightInvOn⟩⟩
  obtain ⟨f,g,hfg,hfK,hfL⟩ := glue_closed_homeoOn hK.isArc.isClosed hL.isArc.isClosed
    hK.isArc.isClosed hN.isArc.isClosed hId hLN
    (fun x hx => by have he : x = p := Set.mem_singleton_iff.mp (hKL ▸ hx); subst x; exact h.map_left.symm)
    (by simpa only [image_id,hKL,hKN])
  have hA : IsArcBetween (K ∪ L) a b := hK.concatenate hL
    (fun x hxK hxL => Set.mem_singleton_iff.mp (hKL ▸ (show x ∈ K ∩ L from ⟨hxK,hxL⟩)))
  have hB : IsArcBetween (K ∪ N) a b := hK.concatenate hN
    (fun x hxK hxN => Set.mem_singleton_iff.mp (hKN ▸ (show x ∈ K ∩ N from ⟨hxK,hxN⟩)))
  let e : ArcHomeo (K ∪ L) (K ∪ N) a b a b := {
    toFun := f, invFun := g, continuousOn_toFun := hfg.continuousOn,
    continuousOn_invFun := hfg.continuousOn_inv, leftInvOn := hfg.invOn.1,
    rightInvOn := hfg.invOn.2, image_eq := hfg.image_eq,
    map_left := hfK a hK.left_mem,
    map_right := (hfL b hL.right_mem).trans h.map_right }
  obtain ⟨F,hpoint,_,hfix⟩ := prescribed_relative_crosscut_replacement
    (K ∪ L) (K ∪ N) a b hA hB ha hb hAi hBi e
  refine ⟨F,?_,?_,hfix⟩
  · intro x hx
    exact (hpoint x (Or.inl hx)).trans (hfK x hx)
  · have heq : EqOn F h.toFun L := fun x hx =>
      (hpoint x (Or.inr hx)).trans (hfL x hx)
    exact heq.image_eq.trans h.image_eq

#print axioms actual_common_arm_pointwise_fixed_prescribed_crosscut_replacement_private

open Lean Elab Term in
elab "checkedRecovery20actualArcBetweenHasInjectivePath" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualArcBetweenHasInjectivePath
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualFixedArmIntersectsReferenceAvoidingSource" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualFixedArmIntersectsReferenceAvoidingSource
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualPositiveReferenceSquareArm" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualPositiveReferenceSquareArm
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualScaledTargetGermDirection" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualScaledTargetGermDirection
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualSimpleTwoSegmentSourceTarget" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualSimpleTwoSegmentSourceTarget
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualTwoSegmentTargetAvoidsReference" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualTwoSegmentTargetAvoidsReference
  discard <| getConstInfo n
  return mkConst n

private theorem actual_positive_ray_pointwise_fixed_one_source_square_private
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (hb : b ∈ modelCurve)
    (hαi : ∀ t : CurveComplex.Interval, t < 1 → α t ∈ Plane.openSquare 0 1)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0}) :
    let reference : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧ (∀ x ∈ reference, F x = x) ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ (j : J) (r : ℝ), q ≠ r • v j := by
  let a : Plane := Plane.mk 1 0
  let R : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
  let K := segment ℝ (0 : Plane) a
  obtain ⟨ha, hKArc, hKR, hlocal, hKi⟩ := checkedRecovery20actualPositiveReferenceSquareArm
  change a ∈ modelCurve at ha
  change IsArcBetween K a 0 at hKArc
  change K ⊆ R at hKR
  change R ∩ Plane.openSquare 0 1 ⊆ K at hlocal
  change K \ {a} ⊆ Plane.openSquare 0 1 at hKi
  have h0K : (0 : Plane) ∈ K := left_mem_segment ℝ 0 a
  have hbR : b ∉ R := by
    change b ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0}
    simpa only [α.target] using havoid 1 (by norm_num)
  have hb0 : b ≠ 0 := by
    intro he
    apply hbR
    simp [R, he]
  obtain ⟨q, hqi, hq0, hqup, hqlo, hind, hqv⟩ :=
    checkedRecovery20actualScaledTargetGermDirection v hb0
  let N := segment ℝ (0 : Plane) q ∪ segment ℝ q b
  obtain ⟨hNArc, hNi⟩ := checkedRecovery20actualSimpleTwoSegmentSourceTarget hb hqi hq0 hind
  change IsArcBetween N 0 b at hNArc
  change N \ {0,b} ⊆ Plane.openSquare 0 1 at hNi
  have hNR : N ∩ R = {0} := by
    simpa [N, R] using checkedRecovery20actualTwoSegmentTargetAvoidsReference false
      (by simpa [R] using hbR) hqup hqlo
  have hKN : K ∩ N = {0} :=
    checkedRecovery20actualFixedArmIntersectsReferenceAvoidingSource hKR h0K hNR
  have hαR : range α ∩ R = {0} := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, rfl⟩, htR⟩
      by_cases ht : t = 0
      · simpa [ht, α.source]
      · exfalso
        exact havoid t (lt_of_le_of_ne t.property.1 (Ne.symm ht)) htR
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      exact ⟨⟨0, α.source⟩, by simp [R]⟩
  have hKα : K ∩ range α = {0} :=
    checkedRecovery20actualFixedArmIntersectsReferenceAvoidingSource hKR h0K hαR
  obtain ⟨κ, hκ, hκK⟩ := checkedRecovery20actualArcBetweenHasInjectivePath hKArc
  obtain ⟨ν, hν, hνN⟩ := checkedRecovery20actualArcBetweenHasInjectivePath hNArc
  obtain ⟨hA, hpA⟩ := checkedRecovery20actualJoinedSourceArmsArePointedArc κ α hκ hα
    (by simpa [hκK] using hKα)
  obtain ⟨hB, hpB⟩ := checkedRecovery20actualJoinedSourceArmsArePointedArc κ ν hκ hν
    (by simpa [hκK, hνN] using hKN)
  rw [hκK] at hA hpA
  rw [hκK, hνN] at hB hpB
  have hAi : (K ∪ range α) \ {a,b} ⊆ Plane.openSquare 0 1 := by
    intro z hz
    have hza : z ≠ a := fun he => hz.2 (by simp [he])
    have hzb : z ≠ b := fun he => hz.2 (by simp [he])
    rcases hz.1 with hzK | hzα
    · apply hKi
      exact ⟨hzK, by simpa using hza⟩
    · obtain ⟨t, rfl⟩ := hzα
      apply hαi
      apply lt_of_le_of_ne t.property.2
      intro he
      have heI : t = (1 : CurveComplex.Interval) := Subtype.ext he
      apply hz.2
      simp [heI, α.target]
  have hBi : (K ∪ N) \ {a,b} ⊆ Plane.openSquare 0 1 := by
    intro z hz
    have hza : z ≠ a := fun he => hz.2 (by simp [he])
    have hzb : z ≠ b := fun he => hz.2 (by simp [he])
    rcases hz.1 with hzK | hzN
    · exact hKi ⟨hzK, by simpa using hza⟩
    · by_cases hz0 : z = 0
      · rw [hz0, mem_openSquare_zero_one]
        simp [Plane.supNorm]
      · apply hNi
        exact ⟨hzN, by simpa using ⟨hz0, hzb⟩⟩
  obtain ⟨F,hFK,hFα,hfix⟩ :=
    actual_common_arm_pointwise_fixed_prescribed_crosscut_replacement_private hKArc
      (checkedRecovery20actualInjectivePathIsArc α hα) hNArc hKα hKN ha hb hAi hBi
  have hF0 : F 0 = 0 := hFK 0 h0K
  have hFR : ∀ x ∈ R, F x = x := by
    intro x hx
    by_cases hxS : x ∈ Plane.openSquare 0 1
    · exact hFK x (hlocal ⟨hx,hxS⟩)
    · exact hfix x hxS
  have hFb : F b = b := by
    apply hfix
    intro hh
    have hlt := mem_openSquare_zero_one.mp hh
    rw [show Plane.supNorm b = 1 from hb] at hlt
    exact (lt_irrefl 1) hlt
  have hqFb : q ≠ F b := by
    rw [hFb]
    intro he
    have hlt := mem_openSquare_zero_one.mp hqi
    rw [he, show Plane.supNorm b = 1 from hb] at hlt
    exact (lt_irrefl 1) hlt
  obtain ⟨c, hc, hc1, hcim⟩ := checkedRecovery20actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) N hNArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    (by rw [hFα]) subset_union_left
    (by rw [hFα]; exact Or.inl (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFb
  refine ⟨F, hF0, hFR, hfix, c, hc, hc1, q, hq0, hcim, ?_, hqv⟩
  apply Subset.antisymm
  · intro z hz
    rw [← hNR]
    exact ⟨Or.inl hz.1, hz.2⟩
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    exact ⟨left_mem_segment ℝ 0 q, by simp [R]⟩


#print axioms actual_positive_ray_pointwise_fixed_one_source_square_private

open Lean Elab Term in
elab "checkedRecovery20actualReferenceAvoidingFirstExitSourceArm" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualReferenceAvoidingFirstExitSourceArm
  discard <| getConstInfo n
  return mkConst n

private theorem actual_positive_ray_pointwise_fixed_original_arm_square_private
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (hb : b ∉ Plane.closedSquare 0 1)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0}) :
    let reference : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
    ∃ F : Plane ≃ₜ Plane, F 0 = 0 ∧ (∀ x ∈ reference, F x = x) ∧
      (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ (j : J) (r : ℝ), q ≠ r • v j := by
  obtain ⟨d, hd, hd1, δ, hδ, hδb, hδi, hδavoid, hδrange⟩ :=
    checkedRecovery20actualReferenceAvoidingFirstExitSourceArm α hα havoid hb
  let allv : Option J → Plane := fun j => Option.casesOn j b v
  obtain ⟨F, hF0, hFR, hfix, cδ, hcδ, hcδ1, q, hq0, hqim, hqR, hqv⟩ :=
    actual_positive_ray_pointwise_fixed_one_source_square_private allv δ hδ hδb hδi hδavoid
  have hfullArc : IsArcBetween (F '' range α) 0 (F b) := by
    have hh := (checkedRecovery20actualInjectivePathIsArc α hα).image_of_injOn
      (S := Set.univ) (subset_univ _) F.continuous.continuousOn F.injective.injOn
    simpa only [hF0] using hh
  have hsub : segment ℝ (0 : Plane) q ⊆ F '' range α := by
    rw [← hqim]
    apply (image_mono (image_subset_range _ _)).trans
    apply image_mono
    rw [hδrange]
    exact image_subset_range _ _
  have hFb : F b = b := by
    apply hfix
    intro hh
    apply hb
    exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hh).le
  have hqFb : q ≠ F b := by
    rw [hFb]
    simpa [allv] using hqv none 1
  obtain ⟨c, hc, hc1, hcim⟩ := checkedRecovery20actualSourcePrefixPullback α hα F
    (segment ℝ (0 : Plane) q) (F '' range α) hfullArc
    (by simpa only [hF0] using isArcBetween_segment hq0.symm)
    Subset.rfl hsub (hsub (right_mem_segment ℝ 0 q))
    (by simpa only [hF0] using hq0) hqFb
  exact ⟨F, hF0, hFR, hfix, c, hc, hc1, q, hq0, hcim, hqR,
    fun j r => hqv (some j) r⟩

private theorem actualRelativeSquareWindow (o a b : Plane) (ha : a ≠ o) (hb : b ≠ o)
    (V : Set Plane) (hV : IsOpen V) (hoV : o ∈ V) :
    ∃ (E : Plane ≃ₜ Plane) (R scale : ℝ), 0 < R ∧ 0 < scale ∧
      closedBall o R ⊆ V ∧ E o = 0 ∧
      E a ∉ Plane.closedSquare 0 1 ∧ E b ∉ Plane.closedSquare 0 1 ∧
      (∀ x, E x ∈ Plane.openSquare 0 1 → x ∈ ball o R) ∧
      ∀ y, E.symm y = scale • y + o := by
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hoV)
  have pos (x : Plane) (hx : x ≠ o) : 0 < Plane.supNorm (x-o) := by
    have hnorm : 0 < ‖x-o‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    have hbound := Plane.norm_le_sqrt_two_mul_supNorm (x-o)
    by_contra hn
    have hprod : Real.sqrt 2 * Plane.supNorm (x-o) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (not_lt.mp hn)
    linarith
  let R := ε/2
  let scale := min (R/4) (min (Plane.supNorm (a-o)) (Plane.supNorm (b-o))) / 2
  have hR : 0 < R := half_pos hε
  have hscale : 0 < scale := half_pos (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))
  have hscaleR : scale < R/4 :=
    (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le (min_le_left _ _)
  have hscalea : scale < Plane.supNorm (a-o) :=
    (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hscaleb : scale < Plane.supNorm (b-o) :=
    (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  let E : Plane ≃ₜ Plane := {
    toEquiv := {
      toFun := fun x => scale⁻¹ • (x-o)
      invFun := fun y => scale • y + o
      left_inv := by
        intro x
        dsimp only
        rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hscale),one_smul]
        abel
      right_inv := by
        intro y
        dsimp only
        rw [add_sub_cancel_right,smul_smul,inv_mul_cancel₀ (ne_of_gt hscale),one_smul] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hEo : E o = 0 := by simp [E]
  have houtside (x : Plane) (hx : scale < Plane.supNorm (x-o)) : E x ∉ Plane.closedSquare 0 1 := by
    intro hm
    have hn := mem_closedSquare_zero_one.mp hm
    change Plane.supNorm (scale⁻¹ • (x-o)) ≤ 1 at hn
    rw [Plane.supNorm_smul,abs_of_pos (inv_pos.mpr hscale)] at hn
    have hh : Plane.supNorm (x-o) ≤ scale := by
      have ht := mul_le_mul_of_nonneg_left hn hscale.le
      rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hscale),one_mul,mul_one] at ht
      exact ht
    exact not_le_of_gt hx hh
  have hinside (x : Plane) (hx : E x ∈ Plane.openSquare 0 1) : x ∈ ball o R := by
    have hsup := mem_openSquare_zero_one.mp hx
    have hsqrt : Real.sqrt 2 < 2 := by
      have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have hp := Real.sqrt_nonneg (2:ℝ)
      nlinarith
    have hn : ‖E x‖ < 2 := by
      have hbound := Plane.norm_le_sqrt_two_mul_supNorm (E x)
      have hp := Plane.supNorm_nonneg (E x)
      nlinarith [Real.sqrt_nonneg (2:ℝ)]
    have hxe : x-o = scale • E x := by
      have hh := E.symm_apply_apply x
      change scale • E x + o = x at hh
      have hs := congrArg (fun y : Plane => y-o) hh
      simpa only [add_sub_cancel_right] using hs.symm
    rw [mem_ball,dist_eq_norm,hxe,norm_smul,Real.norm_eq_abs,abs_of_pos hscale]
    exact (mul_lt_mul_of_pos_left hn hscale).trans (by linarith)
  refine ⟨E,R,scale,hR,hscale,?_,hEo,houtside a hscalea,houtside b hscaleb,hinside,fun _ => rfl⟩
  exact (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεV

private theorem actualPositiveScaleReferenceMembership
    (anchorLoop : Bool) {s : ℝ} (hs : 0 < s) (z : Plane) :
    (s • z) ∈ {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} ↔
      z ∈ {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} := by
  change (s * z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ s * z 0)) ↔
    (z 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ z 0))
  constructor
  · rintro ⟨hy, hh | hx⟩
    · exact ⟨(mul_eq_zero.mp hy).resolve_left (ne_of_gt hs), Or.inl hh⟩
    · exact ⟨(mul_eq_zero.mp hy).resolve_left (ne_of_gt hs),
        Or.inr (nonneg_of_mul_nonneg_right hx hs)⟩
  · rintro ⟨hy, hh | hx⟩
    · exact ⟨by rw [hy, mul_zero], Or.inl hh⟩
    · exact ⟨by rw [hy, mul_zero], Or.inr (mul_nonneg hs.le hx)⟩

private theorem actualPositiveScaleReferenceImage
    (anchorLoop : Bool) {s : ℝ} (hs : 0 < s) :
    (fun z : Plane => s • z) ''
      {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} =
      {x : Plane | x 1 = 0 ∧ (anchorLoop = true ∨ 0 ≤ x 0)} := by
  apply Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    exact (actualPositiveScaleReferenceMembership anchorLoop hs x).mpr hx
  · intro z hz
    refine ⟨s⁻¹ • z,
      (actualPositiveScaleReferenceMembership anchorLoop (inv_pos.mpr hs) z).mpr hz, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]

private theorem actualGermSegmentAvoidingNoncollinearRay
    {q v : Plane} (h : ∀ r : ℝ, q ≠ r • v) :
    segment ℝ (0 : Plane) q ∩ {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v} = {0} := by
  apply Subset.antisymm
  · rintro z ⟨hz, r, hr, hzr⟩
    rw [segment_eq_image] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have htq : t • q = z := by simpa using htz
    by_cases ht0 : t = 0
    · simpa [ht0] using htq.symm
    · exfalso
      apply h (t⁻¹ * r)
      have he := congrArg (fun x : Plane => t⁻¹ • x) (htq.trans hzr)
      simpa only [smul_smul, inv_mul_cancel₀ ht0, one_smul] using he
  · intro z hz
    have hz0 : z = 0 := hz
    subst z
    exact ⟨left_mem_segment ℝ 0 q, 0, le_refl 0, by simp⟩

/-- Actual one-arm producer in any prescribed neighborhood, preserving the
literal positive anchor ray through scaling and conjugation. -/
private theorem actual_positive_ray_pointwise_fixed_one_source_private
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0 : Plane) b) (hα : Function.Injective α)
    (havoid : ∀ t : CurveComplex.Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0})
    (V : Set Plane) (hV : IsOpen V) (h0V : (0 : Plane) ∈ V) :
    let reference : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
    ∃ F : Plane ≃ₜ Plane, ∃ R : ℝ, 0 < R ∧ closedBall (0 : Plane) R ⊆ V ∧
      F 0 = 0 ∧ (∀ x, x ∉ ball (0 : Plane) R → F x = x) ∧
      (∀ x ∈ reference, F x = x) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ F '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ reference = {0} ∧
          ∀ j, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v j} = {0} := by
  let ref : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
  have hb0 : b ≠ 0 := by
    intro he
    have h10 : (1 : CurveComplex.Interval) = 0 :=
      hα (α.target.trans (he.trans α.source.symm))
    exact one_ne_zero h10
  obtain ⟨E, R, scale, hR, hs, hRV, hE0, hEb, _, hinside, hinv⟩ :=
    actualRelativeSquareWindow 0 b b hb0 hb0 V hV h0V
  have hinv' : ∀ y, E.symm y = scale • y := by
    intro y
    simpa using hinv y
  have hE : ∀ x, E x = scale⁻¹ • x := by
    intro x
    have hh := E.symm_apply_apply x
    rw [hinv'] at hh
    have he := congrArg (fun z : Plane => scale⁻¹ • z) hh
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] using he
  have hER : E '' ref = ref := by
    have hh := actualPositiveScaleReferenceImage false (inv_pos.mpr hs)
    simpa [ref, hE] using hh
  have hEinvR : E.symm '' ref = ref := by
    have hh := actualPositiveScaleReferenceImage false hs
    simpa [ref, hinv'] using hh
  let α' : Path (0 : Plane) (E b) := {
    toFun := E ∘ α
    continuous_toFun := E.continuous.comp α.continuous
    source' := (congrArg E α.source).trans hE0
    target' := congrArg E α.target }
  have hα' : Function.Injective α' := fun s t he => hα (E.injective he)
  have havoid' : ∀ t : CurveComplex.Interval, 0 < t → α' t ∉ ref := by
    intro t ht he
    apply havoid t ht
    have hh : scale⁻¹ • α t ∈ ref := by simpa [α', hE] using he
    have hc := (actualPositiveScaleReferenceMembership false (inv_pos.mpr hs) (α t)).mp
      (by simpa [ref] using hh)
    simpa using hc
  obtain ⟨G, hG0, hGR, hGfix, c, hc, hc1, q, hq0, hqim, hqR, hqv⟩ :=
    actual_positive_ray_pointwise_fixed_original_arm_square_private v α' hα' hEb havoid'
  let F : Plane ≃ₜ Plane := (E.trans G).trans E.symm
  have hF0 : F 0 = 0 := by
    change E.symm (G (E 0)) = 0
    rw [hE0, hG0, hinv']
    simp
  have hfix : ∀ x, x ∉ ball (0 : Plane) R → F x = x := by
    intro x hx
    change E.symm (G (E x)) = x
    rw [hGfix (E x) (fun he => hx (hinside x he)), E.symm_apply_apply]
  have himage (A : Set Plane) : F '' A = E.symm '' (G '' (E '' A)) := by
    rw [← image_comp, ← image_comp]
    rfl
  have hFR : ∀ x ∈ ref, F x = x := by
    intro x hx
    change E.symm (G (E x)) = x
    have hEx : E x ∈ ref := by rw [← hER]; exact ⟨x,hx,rfl⟩
    rw [hGR (E x) hEx,E.symm_apply_apply]
  let A : Plane →ᵃ[ℝ] Plane := {
    toFun := fun y => scale • y
    linear := scale • LinearMap.id
    map_vadd' := by intro x y; change scale • (y+x) = scale • y + scale • x; module }
  have hA : (E.symm : Plane → Plane) = (A : Plane → Plane) := funext hinv'
  have hseg : E.symm '' segment ℝ (0 : Plane) q = segment ℝ 0 (scale • q) := by
    rw [hA, image_segment]
    simp [A]
  have hprefix : F '' (α '' Icc 0 c) = segment ℝ 0 (scale • q) := by
    have hαprefix : α' '' Icc 0 c = E '' (α '' Icc 0 c) := image_comp E α _
    rw [himage, ← hαprefix, hqim, hseg]
  have hscaledRef : segment ℝ 0 (scale • q) ∩ ref = {0} := by
    rw [← hseg, ← hEinvR, ← image_inter E.symm.injective, hqR, image_singleton, hinv']
    simp
  refine ⟨F, R, hR, hRV, hF0, hfix, hFR, c, hc, hc1, scale • q,
    smul_ne_zero (ne_of_gt hs) hq0, hprefix, hscaledRef, ?_⟩
  intro j
  apply actualGermSegmentAvoidingNoncollinearRay
  intro r he
  apply hqv j (scale⁻¹ * r)
  have hh := congrArg (fun x : Plane => scale⁻¹ • x) he
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul] using hh


#print axioms actual_positive_ray_pointwise_fixed_one_source_private

private theorem actual_positive_ray_graph_fixed_old_avoiding_source_motion_private
    {J : Type} [Fintype J] (v : J → Plane) {b : Plane}
    (α : Path (0:Plane) b) (hα : Function.Injective α)
    (havoid : ∀ t : Interval, 0 < t →
      α t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0})
    (V : Set Plane) (hV : IsOpen V) (h0V : (0:Plane) ∈ V) :
    ∃ H : AmbientIsotopy Plane, ∃ R : ℝ,
      0 < R ∧ closedBall (0:Plane) R ⊆ V ∧
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ ball (0:Plane) R → H.map (t,x) = x) ∧
      (∀ t x, x 1 = 0 → 0 ≤ x 0 → H.map (t,x) = x) ∧
      ∃ c : Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ H.finalMap '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          segment ℝ 0 q ∩ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0} = {0} ∧
          ∀ j, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • v j} = {0} := by
  obtain ⟨F,R,hR,hRV,hF0,hFball,hFref,c,hc,hc1,q,hq,himage,hqref,hqold⟩ :=
    actual_positive_ray_pointwise_fixed_one_source_private v α hα havoid V hV h0V
  let P : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
  have hscale : ∀ x ∈ P, ∀ d : ℝ, 1 ≤ d → d • x ∈ P := by
    intro x hx d hd
    constructor
    · change d * x 1 = 0
      rw [hx.1,mul_zero]
    · change 0 ≤ d * x 0
      exact mul_nonneg (by linarith) hx.2
  obtain ⟨H,hHF,hHball,hH0,hHP⟩ :=
    actual_radially_closed_fixed_set_alexander_isotopy_private R hR F
      (fun x hx => hFball x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx))
      hF0 P hscale hFref
  refine ⟨H,R,hR,hRV,hH0,?_,?_,c,hc,hc1,q,hq,?_,hqref,hqold⟩
  · intro t x hx
    exact hHball t x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx)
  · intro t x hx1 hx0
    exact hHP t x ⟨hx1,hx0⟩
  · rw [hHF]; exact himage

#print axioms actual_positive_ray_graph_fixed_old_avoiding_source_motion_private

private theorem actual_short_support_full_radial_arms_fixed_motion_private
    {J : Type} (v : J → Plane) (R : ℝ) (hR : 0 < R)
    (hv : ∀ j, R ≤ ‖v j‖) (F : Plane ≃ₜ Plane)
    (hF0 : F 0 = 0) (hFball : ∀ x, x ∉ ball (0:Plane) R → F x = x)
    (hFfan : ∀ j x, x ∈ segment ℝ (0:Plane) (v j) → F x = x) :
    ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ ball (0:Plane) R → H.map (t,x) = x) ∧
      (∀ t j (d : ℝ), 0 ≤ d → H.map (t,d • v j) = d • v j) := by
  let P : Set Plane := {x | ∃ j, ∃ d : ℝ, 0 ≤ d ∧ x = d • v j}
  have hPscale : ∀ x ∈ P, ∀ d : ℝ, 1 ≤ d → d • x ∈ P := by
    rintro x ⟨j,c,hc,rfl⟩ d hd
    exact ⟨j,d*c,mul_nonneg (by linarith) hc,smul_smul d c (v j)⟩
  have hPfix : ∀ x ∈ P, F x = x := by
    rintro x ⟨j,d,hd,rfl⟩
    by_cases hdi : d ≤ 1
    · apply hFfan j
      rw [segment_eq_image]
      refine ⟨d,⟨hd,hdi⟩,?_⟩
      simp
    · apply hFball
      simp only [mem_ball,dist_zero_right,not_lt,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg hd]
      have hnorm := hv j
      nlinarith
  obtain ⟨H,hHF,hball,hzero,hP⟩ :=
    actual_radially_closed_fixed_set_alexander_isotopy_private R hR F
      (fun x hx => hFball x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx))
      hF0 P hPscale hPfix
  refine ⟨H,hHF,hzero,?_,?_⟩
  · intro t x hx
    exact hball t x (by simpa only [mem_ball,dist_zero_right,not_lt] using hx)
  · intro t j d hd
    exact hP t _ ⟨j,d,hd,rfl⟩


#print axioms actual_short_support_full_radial_arms_fixed_motion_private

private theorem actual_new_source_arm_entire_two_radial_arms_fixed_motion_private
    {K : Type} [Fintype K]
    (v : Fin 2 → Plane) (hv : ∀ j, v j ≠ 0)
    (hfan : segment ℝ (0:Plane) (v 0) ∩ segment ℝ (0:Plane) (v 1) = {0})
    (γ : Interval → Plane) (hγ : Topology.IsClosedEmbedding γ) (hzero : γ 0 = 0)
    (havoid : ∀ t : Interval, 0 < t.val → γ t ∉
      segment ℝ (0:Plane) (v 0) ∪ segment ℝ (0:Plane) (v 1))
    (old : K → Plane) (hold : ∀ k, old k ≠ 0)
    (V : Set Plane) (hV : IsOpen V) (h0V : (0:Plane) ∈ V) :
    ∃ H : AmbientIsotopy Plane, ∃ R : ℝ,
      0 < R ∧ closedBall (0:Plane) R ⊆ V ∧
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ ball (0:Plane) R → H.map (t,x) = x) ∧
      (∀ t j (d : ℝ), 0 ≤ d → H.map (t,d • v j) = d • v j) ∧
      ∃ cut : Interval, ∃ vector : Plane,
        0 < cut.val ∧ cut.val < 1 ∧ vector ≠ 0 ∧
        H.finalMap '' (γ '' Icc 0 cut) = segment ℝ 0 vector ∧
        segment ℝ 0 vector ∩
          (segment ℝ (0:Plane) (v 0) ∪ segment ℝ (0:Plane) (v 1)) = {0} ∧
        ∀ k, segment ℝ 0 vector ∩
          {z | ∃ d : ℝ, 0 ≤ d ∧ z = d • old k} = {0} := by
  obtain ⟨F,R,hR,hRV,hRv0,hRv1,hF0,hFball,hFfan,cut,q,hcut,hcut1,hq,
      himage,hqfan,hqold⟩ := actual_new_source_arm_relative_to_two_fixed_segments
    v hv hfan γ hγ hzero havoid old hold V hV h0V
  have hRv : ∀ j : Fin 2, R ≤ ‖v j‖ := by
    intro j
    fin_cases j
    · exact hRv0.le
    · exact hRv1.le
  have hFF : ∀ j x, x ∈ segment ℝ (0:Plane) (v j) → F x = x := by
    intro j x hx
    fin_cases j
    · exact hFfan x (Or.inl hx)
    · exact hFfan x (Or.inr hx)
  obtain ⟨H,hHF,hH0,hHball,hHfan⟩ :=
    actual_short_support_full_radial_arms_fixed_motion_private v R hR hRv F hF0 hFball hFF
  refine ⟨H,R,hR,hRV,hH0,hHball,hHfan,cut,q,hcut,hcut1,hq,?_,hqfan,hqold⟩
  rw [hHF]; exact himage

#print axioms actual_new_source_arm_entire_two_radial_arms_fixed_motion_private

open Lean Elab Term in
elab "checkedRecovery20actualTransportedSourceAvoidsLiteralReference" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualTransportedSourceAvoidsLiteralReference
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20actualSecondSourceAvoidsFirstRadialPrefix" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualSecondSourceAvoidsFirstRadialPrefix
  discard <| getConstInfo n
  return mkConst n


private theorem actual_two_loop_germs_positive_ray_graph_fixed_old_avoiding_motion_private
    {K : Type} [Fintype K] (old : K → Plane) (hold : ∀ k, old k ≠ 0)
    (γ : Fin 2 → Interval → Plane)
    (hγ : ∀ j, Topology.IsClosedEmbedding (γ j)) (hzero : ∀ j, γ j 0 = 0)
    (hmeet : range (γ 0) ∩ range (γ 1) = {0})
    (havoid : ∀ j (t : Interval), 0 < t →
      γ j t ∉ {z : Plane | z 1 = 0 ∧ 0 ≤ z 0})
    (V : Set Plane) (hV : IsOpen V) (h0V : (0:Plane) ∈ V) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ V → H.map (t,x) = x) ∧
      (∀ t x, x 1 = 0 → 0 ≤ x 0 → H.map (t,x) = x) ∧
      ∃ cut : Fin 2 → Interval, ∃ vector : Fin 2 → Plane,
        (∀ j, 0 < (cut j).val ∧ (cut j).val < 1 ∧ vector j ≠ 0 ∧
          H.finalMap '' (γ j '' Icc 0 (cut j)) = segment ℝ 0 (vector j)) ∧
        ∀ j k, segment ℝ 0 (vector j) ∩
          {z | ∃ d : ℝ, 0 ≤ d ∧ z = d • old k} = {0} := by
  classical
  let α : Path (0:Plane) (γ 0 1) := {
    toFun := γ 0, continuous_toFun := (hγ 0).continuous,
    source' := hzero 0, target' := rfl }
  obtain ⟨H,R,hR,hRV,hH0,hHout,hHref,c,hc,hc1,q,hq,himage,hqref,hqold⟩ :=
    actual_positive_ray_graph_fixed_old_avoiding_source_motion_private old α
      (hγ 0).injective (havoid 0) V hV h0V
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:Interval)
  have hHg : H.finalMap = g := funext (fun x => (hg x).symm)
  have hg0 : g 0 = 0 := by rw [←hHg]; exact hH0 1
  let ref : Set Plane := {z | z 1 = 0 ∧ 0 ≤ z 0}
  have hgRefFix : ∀ x ∈ ref, g x = x := fun x hx => by
    rw [←hHg]; exact hHref 1 x hx.1 hx.2
  have hgRef : g '' ref = ref := (show EqOn g id ref from hgRefFix).image_eq.trans (image_id ref)
  let η : Interval → Plane := g ∘ γ 1
  have hη : Topology.IsClosedEmbedding η := g.isClosedEmbedding.comp (hγ 1)
  have hη0 : η 0 = 0 := by change g (γ 1 0) = 0; rw [hzero 1,hg0]
  have hηRef : ∀ t : Interval, 0 < t → η t ∉ ref :=
    checkedRecovery20actualTransportedSourceAvoidsLiteralReference g hgRef (γ 1) (havoid 1)
  have hgimage : g '' (γ 0 '' Icc 0 c) = segment ℝ 0 q := by
    rw [←hHg]; exact himage
  have hηq : ∀ t : Interval, 0 < t → η t ∉ segment ℝ 0 q :=
    checkedRecovery20actualSecondSourceAvoidsFirstRadialPrefix g (γ 0) (γ 1)
      (hγ 1).injective (hzero 1) hmeet c q hgimage
  let a : Plane := Plane.mk 1 0
  have ha : a ≠ 0 := by intro he; have hh := congrArg (fun z : Plane => z 0) he; norm_num [a] at hh
  let v : Fin 2 → Plane := fun j => if j = 0 then a else q
  have hv : ∀ j, v j ≠ 0 := by intro j; fin_cases j <;> simp [v,ha,hq]
  have haRef : segment ℝ (0:Plane) a ⊆ ref := by
    intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨d,hd,rfl⟩ := hx
    simp only [smul_zero,add_zero] at *
    constructor
    · simp [a]
    · simpa [a] using hd.1
  have hfan : segment ℝ (0:Plane) (v 0) ∩ segment ℝ (0:Plane) (v 1) = {0} := by
    apply Subset.antisymm
    · intro x hx
      apply Set.mem_singleton_iff.mp (show x ∈ ({0}:Set Plane) from ?_)
      rw [←hqref]
      exact ⟨by simpa [v] using hx.2,haRef (by simpa [v] using hx.1)⟩
    · intro x hx; have he : x = 0 := hx; subst x
      exact ⟨left_mem_segment ℝ 0 _,left_mem_segment ℝ 0 _⟩
  have hηavoid : ∀ t : Interval, 0 < t.val → η t ∉
      segment ℝ (0:Plane) (v 0) ∪ segment ℝ (0:Plane) (v 1) := by
    intro t ht hx
    rcases hx with hx|hx
    · exact hηRef t ht (haRef (by simpa [v] using hx))
    · exact hηq t ht (by simpa [v] using hx)
  obtain ⟨L,R',hR',hRV',hL0,hLout,hLfan,d,w,hd,hd1,hw,himL,_,hwold⟩ :=
    actual_new_source_arm_entire_two_radial_arms_fixed_motion_private v hv hfan η hη hη0
      hηavoid old hold V hV h0V
  have hLa (t : Interval) (x : Plane) (hx1 : x 1 = 0) (hx0 : 0 ≤ x 0) : L.map (t,x) = x := by
    have he : x = (x 0) • a := by ext i; fin_cases i <;> simp [a,hx1]
    rw [he]
    simpa [v] using hLfan t 0 (x 0) hx0
  have hLq (t : Interval) : EqOn (fun x => L.map (t,x)) id (segment ℝ (0:Plane) q) := by
    intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    simpa [v] using hLfan t 1 z hz.1
  let cuts : Fin 2 → Interval := fun j => if j = 0 then c else d
  let vectors : Fin 2 → Plane := fun j => if j = 0 then q else w
  refine ⟨H.compose L,?_,?_,?_,cuts,vectors,?_,?_⟩
  · intro t; change L.map (t,H.map (t,0)) = 0; rw [hH0,hL0]
  · intro t x hx
    change L.map (t,H.map (t,x)) = x
    rw [hHout t x (fun hb => hx (hRV (ball_subset_closedBall hb))),
      hLout t x (fun hb => hx (hRV' (ball_subset_closedBall hb)))]
  · intro t x hx1 hx0
    change L.map (t,H.map (t,x)) = x
    rw [hHref t x hx1 hx0,hLa t x hx1 hx0]
  · intro j
    fin_cases j
    · refine ⟨hc,hc1,hq,?_⟩
      change (H.compose L).finalMap '' (γ 0 '' Icc 0 c) = segment ℝ 0 q
      rw [AmbientIsotopy.compose_finalMap,image_comp,hHg,hgimage]
      exact (hLq 1).image_eq.trans (image_id _)
    · refine ⟨hd,hd1,hw,?_⟩
      change (H.compose L).finalMap '' (γ 1 '' Icc 0 d) = segment ℝ 0 w
      rw [AmbientIsotopy.compose_finalMap,image_comp,hHg,←image_comp g (γ 1) (Icc 0 d)]
      change L.finalMap '' (η '' Icc 0 d) = segment ℝ 0 w
      exact himL
  · intro j k; fin_cases j <;> simpa [vectors] using (by first | exact hqold k | exact hwold k)

#print axioms actual_two_loop_germs_positive_ray_graph_fixed_old_avoiding_motion_private

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_loop_two_terminal_germs_chart_source_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M)
    (hloop : b.val.map 0 = b.val.map 1)
    (e : OpenPartialHomeomorph S Plane) (he0 : e (b.val.map 0) = 0)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (hsource : ∀ terminal t, b.val.map
      (endpointGermParameter terminal r hr (by linarith) t) ∈ e.source) :
    let γ : Fin 2 → Interval → Plane := fun j t => e (b.val.map
      (endpointGermParameter (j = 1) r hr (by linarith) t))
    (∀ j, Topology.IsClosedEmbedding (γ j)) ∧
    (∀ j, γ j 0 = 0) ∧ range (γ 0) ∩ range (γ 1) = {0} := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  intro γ
  have emb (terminal : Bool) : Topology.IsClosedEmbedding (fun t => e (b.val.map
      (endpointGermParameter terminal r hr (by linarith) t))) := by
    have hc := actual_endpoint_germ_embedding M b terminal r hr (by linarith)
    have hec : Continuous (fun t => e (b.val.map
        (endpointGermParameter terminal r hr (by linarith) t))) := by
      exact continuousOn_univ.mp (e.continuousOn.comp hc.continuous.continuousOn
        (fun t _ => hsource terminal t))
    apply hec.isClosedEmbedding
    intro t u he
    apply hc.injective
    exact e.injOn (hsource terminal t) (hsource terminal u) he
  have hγ0 (j : Fin 2) : γ j 0 = 0 := by
    fin_cases j
    · simpa [γ,endpointGermParameter] using he0
    · simpa [γ,endpointGermParameter,←hloop] using he0
  refine ⟨fun j => emb (j = 1),hγ0,?_⟩
  apply Subset.antisymm
  · rintro z ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
    have he : b.val.map (endpointGermParameter false r hr (by linarith) t) =
        b.val.map (endpointGermParameter true r hr (by linarith) u) := by
      apply e.injOn (hsource false t) (hsource true u)
      exact hu.symm
    rcases b.val.injective_except_loop_closure _ _ he with hs|hs|hs
    · have hv := congrArg Subtype.val hs
      dsimp [endpointGermParameter] at hv
      nlinarith [t.property.2,u.property.2]
    · have he0t : endpointGermParameter false r hr (by linarith) t = 0 := hs.1
      change e (b.val.map (endpointGermParameter false r hr (by linarith) t)) ∈ ({0}:Set Plane)
      rw [he0t,he0]
      exact mem_singleton 0
    · have hv := congrArg Subtype.val hs.1
      dsimp [endpointGermParameter] at hv
      nlinarith [t.property.2]
  · intro z hz
    have he : z = 0 := hz
    subst z
    exact ⟨⟨0,hγ0 0⟩,⟨0,hγ0 1⟩⟩
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_loop_two_terminal_germs_chart_source_private

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_loop_graph_fixed_both_terminal_collars_single_graph_ray_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hloop : b.val.map 0 = b.val.map 1)
    (e : OpenPartialHomeomorph S Plane) (hpe : b.val.map 0 ∈ e.source)
    (he0 : e (b.val.map 0) = 0)
    (hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = b.val.map 0)
    (P : Set S)
    (hgraph : ∀ x, x ∈ e.source → (x ∈ P ↔ e x 1 = 0 ∧ 0 ≤ e x 0))
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 → b.val.map t ∉ P)
    {K : Type} [Fintype K] (old : K → Plane) (hold : ∀ k, old k ≠ 0)
    (haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k)
    (R : ℝ) (hR : 0 < R) (hRT : closedBall (0:Plane) R ⊆ e.target)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (hsource : ∀ terminal t, b.val.map
      (endpointGermParameter terminal r hr (by linarith) t) ∈ e.source) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ P → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let γ : Fin 2 → Interval → Plane := fun j t => e (b.val.map
    (endpointGermParameter (j = 1) r hr (by linarith) t))
  obtain ⟨hγ,hγ0,hmeet⟩ :=
    actual_marked_loop_two_terminal_germs_chart_source_private M b hloop e he0 r hr hrhalf hsource
  have havoid : ∀ j (t : Interval), 0 < t → γ j t ∉
      {z : Plane | z 1 = 0 ∧ 0 ≤ z 0} := by
    intro j t ht hx
    have htp : 0 < t.val := ht
    have hb := (hgraph _ (hsource (j=1) t)).mpr hx
    apply hbP _ ?_ ?_ hb
    · fin_cases j <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2,htp]
    · fin_cases j <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2,htp]
  obtain ⟨L,hL0,hLout,hLref,cut,v,hcut,hvOld⟩ :=
    actual_two_loop_germs_positive_ray_graph_fixed_old_avoiding_motion_private old hold
      γ hγ hγ0 hmeet havoid (ball (0:Plane) R) isOpen_ball (by simpa using hR)
  obtain ⟨H,hHmarks,hHP,hHout,hHstay,hHcoord⟩ :=
    actual_graph_fixed_terminal_chart_motion_lift_private M (b.val.map 0) e hpe he0 hemarks
      R hRT P L hL0 hLout
      (fun t x hx hxs => hLref t (e x) ((hgraph x hxs).mp hx).1 ((hgraph x hxs).mp hx).2)
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:Interval)
  have hHg : H.finalMap = g := funext (fun x => (hg x).symm)
  have hgmarks : ∀ x, x ∈ M.cover.branch → g x = x := fun x hx => by
    rw [←hHg]; exact hHmarks 1 x hx
  let c := b.transport g hgmarks
  have hcmap (t : Interval) : c.val.map t = H.finalMap (b.val.map t) := by
    change g (b.val.map t) = H.finalMap (b.val.map t)
    rw [hHg]
  have hclass : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hHmarks,?_⟩
    rw [hHg]
    exact (MarkedArc.transport_image b.val g hgmarks).symm
  let δ := r * min (cut 0).val (cut 1).val / 2
  have hmin : 0 < min (cut 0).val (cut 1).val := lt_min (hcut 0).1 (hcut 1).1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ ≤ r := by
    have hm : min (cut 0).val (cut 1).val ≤ 1 := (min_le_left _ _).trans (cut 0).property.2
    dsimp [δ]
    nlinarith
  have hδhalf : δ < 1/2 := hδr.trans_lt hrhalf
  have hδcut (j : Fin 2) : δ ≤ r * (cut j).val := by
    have hm : min (cut 0).val (cut 1).val ≤ (cut j).val := by
      fin_cases j
      · exact min_le_left _ _
      · exact min_le_right _ _
    dsimp [δ]
    nlinarith [(cut j).property.1]
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hHmarks,hHP,hcmap,?_⟩
  intro t ht0 ht1 htδ hcontact
  obtain ⟨j,u,hu,htu⟩ : ∃ (j : Fin 2) (u : Interval),
      u ∈ Icc 0 (cut j) ∧
      endpointGermParameter (j=1) r hr (by linarith) u = t := by
    rcases htδ with htδ|htδ
    · let u : Interval := ⟨t.val/r,⟨div_nonneg t.property.1 hr.le,
        (div_le_one hr).mpr (htδ.trans hδr)⟩⟩
      refine ⟨0,u,⟨u.property.1,?_⟩,?_⟩
      · change t.val/r ≤ (cut 0).val
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans (hδcut 0))
      · apply Subtype.ext
        change r*(t.val/r) = t.val
        field_simp
    · let u : Interval := ⟨(1-t.val)/r,⟨div_nonneg (by linarith) hr.le,
        (div_le_one hr).mpr (htδ.trans hδr)⟩⟩
      refine ⟨1,u,⟨u.property.1,?_⟩,?_⟩
      · change (1-t.val)/r ≤ (cut 1).val
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans (hδcut 1))
      · apply Subtype.ext
        change 1-r*((1-t.val)/r) = t.val
        field_simp
        ring
  have hbt : b.val.map t ∈ e.source := htu ▸ hsource (j=1) u
  have hct : c.val.map t ∈ e.source := by rw [hcmap]; exact hHstay 1 _ hbt
  have hseg : e (c.val.map t) ∈ segment ℝ (0:Plane) (v j) := by
    rw [hcmap]
    change e (H.map (1,b.val.map t)) ∈ segment ℝ (0:Plane) (v j)
    rw [hHcoord 1 _ hbt]
    change L.finalMap (e (b.val.map t)) ∈ segment ℝ (0:Plane) (v j)
    rw [←(hcut j).2.2.2]
    refine ⟨γ j u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg L.finalMap (congrArg e (congrArg b.val.map htu))
  obtain ⟨k,d,hd,heold⟩ := haOld _ hcontact hct
  have hz : e (c.val.map t) = 0 := by
    apply Set.mem_singleton_iff.mp
    rw [←hvOld j k]
    exact ⟨hseg,⟨d,hd,heold⟩⟩
  have hcp : c.val.map t = b.val.map 0 := e.injOn hct hpe (hz.trans he0.symm)
  have hm : c.val.map t ∈ M.cover.branch := hcp.symm ▸ b.val.start_marked
  exact (c.val.marked_only_at_ends t hm).elim
    (fun h => by have hh := congrArg Subtype.val h; change t.val=0 at hh; linarith)
    (fun h => by have hh := congrArg Subtype.val h; change t.val=1 at hh; linarith)
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_loop_graph_fixed_both_terminal_collars_single_graph_ray_private

open Lean Elab Term in
elab "checkedRecovery20endpoint_germs_from_finite_contacts" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart 0).append
    `CurveComplex.HyperellipticModel.endpoint_germs_from_finite_contacts
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRecovery20radialized_prefix_common_cut" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart 0).append
    `CurveComplex.HyperellipticModel.radialized_prefix_common_cut
  discard <| getConstInfo n
  return mkConst n


namespace CurveComplex.HyperellipticModel
open CurveComplex.FiniteStarGeometry
private theorem actual_marked_source_fan_two_prescribed_incidences_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (a : J → EssentialMarkedArc M)
    (hfinite : ∀ i j, i ≠ j → (ArcSurgery.crossings M (a i) (a j)).Finite)
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
    (g₀ g₁ : J × Bool)
    (hg₀ : (if g₀.2 then (a g₀.1).val.map 1 else (a g₀.1).val.map 0) = p)
    (hg₁ : (if g₁.2 then (a g₁.1).val.map 1 else (a g₁.1).val.map 0) = p)
    (hne : g₀ ≠ g₁) :
    let incident : J × Bool → Prop := fun g =>
      (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p = 0 ∧ F.source ⊆ W ∧
      F.source ∩ (M.cover.branch : Set S) = {p} ∧
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
    ∃ v : J × Bool → Plane,
      (∀ g, incident g → v g ≠ 0) ∧
      (∃ ell : ℝ, 0 < ell ∧ v g₁ = -ell • v g₀) ∧
      (∀ g k, incident g → incident k → g ≠ k →
        segment ℝ (0 : Plane) (v g) ∩ segment ℝ (0 : Plane) (v k) = {0}) ∧
      (∀ g, incident g →
        Set.range ((a g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) ⊆ F.source ∧
        Set.range (F ∘ (a g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) =
          segment ℝ (0 : Plane) (v g)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let C := actualSphereSmoothAtlas M
  letI := C.charts
  obtain ⟨U,hU,hpU,hUchart,hmarks,hcentral,hnoninc,rOld,hrOld,hrOldHalf,hOldGerms⟩ :=
    actual_endpoint_star_in_smooth_chart M C J a p hp
  let D := U ∩ W
  have hD : IsOpen D := hU.inter hW
  have hpD : p ∈ D := ⟨hpU,hpW⟩
  let e0 := chartAt Plane p
  let e : OpenPartialHomeomorph S Plane :=
    (e0.restr D).trans (Homeomorph.addRight (-e0 p)).toOpenPartialHomeomorph
  have heSource : e.source = e0.source ∩ D := by simp [e,hD.interior_eq]
  have hep : p ∈ e.source := heSource.symm ▸ ⟨mem_chart_source _ _,hpD⟩
  have heval (x : S) : e x = e0 x - e0 p := by simp [e,sub_eq_add_neg]
  have hezero : e p = 0 := by simp [heval]
  obtain ⟨r₀,hr₀,hr₀half,hgermSource,hgermMeet⟩ :=
    checkedRecovery20endpoint_germs_from_finite_contacts M a hfinite p hp D hD hpD
  have hr₀1 : r₀ < 1 := by linarith
  let incident : J × Bool → Prop := fun g =>
    (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p
  let α : J × Bool → Interval → S := fun g =>
    (a g.1).val.map ∘ endpointGermParameter g.2 r₀ hr₀ hr₀1
  let L := {g : J × Bool // incident g}
  let γ : L → Interval → Plane := fun g => e ∘ α g.val
  have hsource (g : L) (t : Interval) : α g.val t ∈ e.source := by
    rw [heSource]
    have hd := hgermSource g.val g.property t
    exact ⟨hUchart hd.1,hd⟩
  have hαzero (g : L) : α g.val zeroI = p := by
    cases hb : g.val.2 <;> simpa [α,endpointGermParameter,zeroI,hb,incident] using g.property
  have hγ (g : L) : Topology.IsClosedEmbedding (γ g) := by
    have hα := actual_endpoint_germ_embedding M (a g.val.1) g.val.2 r₀ hr₀ hr₀1
    have hc : Continuous (γ g) := e.continuousOn.comp_continuous hα.continuous (hsource g)
    exact hc.isClosedEmbedding (fun s t he => hα.injective (e.injOn (hsource g s) (hsource g t) he))
  have hstart (g : L) : γ g zeroI = 0 := by simp only [γ,Function.comp_apply,hαzero,hezero]
  have hmeet (i j : L) (hij : i ≠ j) : range (γ i) ∩ range (γ j) = {0} := by
    have hreal := hgermMeet i.val j.val (fun he => hij (Subtype.ext he)) i.property j.property
    ext x
    constructor
    · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
      have he : α i.val s = α j.val t := e.injOn (hsource i s) (hsource j t) (hs.trans ht.symm)
      have hz : α i.val s = p := by
        have hh : α i.val s ∈ range (α i.val) ∩ range (α j.val) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
        rw [hreal] at hh
        exact hh
      exact mem_singleton_iff.mpr (hs.symm.trans ((congrArg e hz).trans hezero))
    · intro hx
      have hx0 : x = 0 := hx
      subst x
      exact ⟨⟨zeroI,hstart i⟩,⟨zeroI,hstart j⟩⟩
  let l₀ : L := ⟨g₀,hg₀⟩
  let l₁ : L := ⟨g₁,hg₁⟩
  have htarget0 : (0:Plane) ∈ e.target := hezero ▸ e.map_source hep
  have hlne : l₀ ≠ l₁ := fun he => hne (congrArg Subtype.val he)
  obtain ⟨star,hpair⟩ := prescribed_pair_finite_actual_star_radialization_zero γ hγ hstart hmeet
    l₀ l₁ hlne e.target e.open_target htarget0
  have small (s : Finset L) : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∀ g ∈ s, d < (star.cut g).val := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1/2,by norm_num,by norm_num,by simp⟩
    | @insert g s hg ih =>
      obtain ⟨d,hd,hd1,hds⟩ := ih
      refine ⟨min d ((star.cut g).val/2),lt_min hd (half_pos (star.cut_pos g)),
        (min_le_left _ _).trans_lt hd1,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (min_le_right _ _).trans_lt (by linarith [star.cut_pos k])
      · exact (min_le_left _ _).trans_lt (hds k hk)
  obtain ⟨d,hd,hd1,hds⟩ := small Finset.univ
  let q : Interval := ⟨d,⟨hd.le,hd1.le⟩⟩
  let r := r₀*d
  have hr : 0 < r := mul_pos hr₀ hd
  have hrhalf : r < 1/2 := by
    have hh : r₀*d < r₀ := by nlinarith
    exact hh.trans hr₀half
  let F : OpenPartialHomeomorph S Plane := e.trans star.H.toOpenPartialHomeomorph
  have hFsource : F.source = e.source := by simp [F]
  have hFval (x : S) : F x = star.H (e x) := rfl
  let v : J × Bool → Plane := fun g => if hi : incident g then star.H (γ ⟨g,hi⟩ q) else 0
  have hv (g : L) : v g.val = star.H (γ g q) := by simp only [v,dif_pos g.property]; rfl
  have hprefix (g : L) :
      star.H '' armPrefix γ g q = segment ℝ (0 : Plane) (v g.val) ∧ v g.val ≠ 0 := by
    obtain ⟨hs,hn⟩ := checkedRecovery20radialized_prefix_common_cut (γ g) (hγ g) 0 (hstart g) star.H star.fixes_center
      (star.cut g) q hd (hds g (Finset.mem_univ _)).le (star.vector g) (star.vector_nonzero g)
      (by simpa only [zero_add,armPrefix] using star.prefix_image g)
    simpa only [hv,armPrefix] using And.intro hs hn
  let k : Interval → Interval := fun t => ⟨d*t.val,by
    constructor
    · exact mul_nonneg hd.le t.property.1
    · nlinarith [t.property.2]⟩
  have hkRange : range k = {t : Interval | t.val ≤ d} := by
    ext t
    constructor
    · rintro ⟨u,rfl⟩
      change d*u.val ≤ d
      nlinarith [u.property.2]
    · intro ht
      let u : Interval := ⟨t.val/d,⟨div_nonneg t.property.1 hd.le,(div_le_one hd).mpr ht⟩⟩
      refine ⟨u,?_⟩
      apply Subtype.ext
      change d*(t.val/d) = t.val
      field_simp
  have hparam (g : L) : (a g.val.1).val.map ∘ endpointGermParameter g.val.2 r hr (by linarith) = α g.val ∘ k := by
    funext t
    change (a g.val.1).val.map _ = (a g.val.1).val.map _
    congr 1
    apply Subtype.ext
    cases hb : g.val.2 <;> dsimp [endpointGermParameter,α,k,r] <;> ring
  have himage (g : L) :
      range (F ∘ (a g.val.1).val.map ∘ endpointGermParameter g.val.2 r hr (by linarith)) =
        segment ℝ (0 : Plane) (v g.val) := by
    rw [← (hprefix g).1]
    change range (F ∘ ((a g.val.1).val.map ∘ endpointGermParameter g.val.2 r hr (by linarith))) = _
    rw [hparam]
    change range ((star.H ∘ γ g) ∘ k) = _
    rw [range_comp,hkRange]
    exact Set.image_comp star.H (γ g) {t : Interval | t.val ≤ d}
  refine ⟨F,hFsource.symm ▸ hep,?_,?_,?_,r,hr,hrhalf,v,?_,?_,?_,?_⟩
  · rw [hFval,hezero,star.fixes_center]
  · intro x hx
    exact (heSource ▸ (hFsource ▸ hx)).2.2
  · ext x
    constructor
    · rintro ⟨hx,hm⟩
      exact hmarks x hm (heSource ▸ (hFsource ▸ hx)).2.1
    · intro hx
      have hx0 : x = p := hx
      subst x
      exact ⟨hFsource.symm ▸ hep,hp⟩
  · intro g hi
    exact (hprefix ⟨g,hi⟩).2
  ·
    have hmember (g : L) : v g.val ∈ segment ℝ (0 : Plane) (star.vector g) := by
      rw [← zero_add (star.vector g),← star.prefix_image g]
      exact ⟨γ g q,⟨q,(hds g (Finset.mem_univ _)).le,rfl⟩,by rw [hv]⟩
    have hmem0 := hmember l₀
    have hmem1 := hmember l₁
    rw [hpair] at hmem1
    rw [segment_eq_image_lineMap] at hmem0 hmem1
    obtain ⟨t,ht,htv⟩ := hmem0
    obtain ⟨s,hs,hsv⟩ := hmem1
    have ht0 : 0 < t := by
      have hn : t ≠ 0 := by
        intro he
        apply (hprefix l₀).2
        simpa [AffineMap.lineMap_apply_module,he] using htv.symm
      exact lt_of_le_of_ne ht.1 (Ne.symm hn)
    have hs0 : 0 < s := by
      have hn : s ≠ 0 := by
        intro he
        apply (hprefix l₁).2
        simpa [AffineMap.lineMap_apply_module,he] using hsv.symm
      exact lt_of_le_of_ne hs.1 (Ne.symm hn)
    refine ⟨s/t,div_pos hs0 ht0,?_⟩
    have htEq : v g₀ = t • star.vector l₀ := by simpa [AffineMap.lineMap_apply_module] using htv.symm
    have hsEq : v g₁ = -s • star.vector l₀ := by simpa [AffineMap.lineMap_apply_module,smul_neg,neg_smul] using hsv.symm
    rw [htEq,hsEq,smul_smul]
    congr 1
    field_simp
  · intro g j hi hj hgj
    let l : L := ⟨g,hi⟩
    let m : L := ⟨j,hj⟩
    rw [← (hprefix l).1,← (hprefix m).1]
    ext x
    constructor
    · rintro ⟨⟨_,⟨s,hs,rfl⟩,hxs⟩,⟨_,⟨t,ht,rfl⟩,hxt⟩⟩
      have he : γ l s = γ m t := star.H.injective (hxs.trans hxt.symm)
      have hz : γ l s = 0 := by
        have hh : γ l s ∈ range (γ l) ∩ range (γ m) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
        rw [hmeet l m (fun hh => hgj (congrArg Subtype.val hh))] at hh
        exact hh
      apply mem_singleton_iff.mpr
      exact hxs.symm.trans ((congrArg star.H hz).trans star.fixes_center)
    · intro hx
      have hx0 : x = 0 := hx
      subst x
      exact ⟨⟨γ l zeroI,⟨zeroI,hd.le,rfl⟩,(congrArg star.H (hstart l)).trans star.fixes_center⟩,
        ⟨γ m zeroI,⟨zeroI,hd.le,rfl⟩,(congrArg star.H (hstart m)).trans star.fixes_center⟩⟩
  · intro g hi
    let l : L := ⟨g,hi⟩
    refine ⟨?_,himage l⟩
    rw [hparam l]
    rintro _ ⟨t,rfl⟩
    exact hFsource.symm ▸ hsource l (k t)

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_source_fan_two_prescribed_incidences_private

namespace CurveComplex.HyperellipticModel
noncomputable local instance recovery20FanDecidableEq (S : Type) : DecidableEq S := Classical.decEq S
private theorem actual_marked_whole_trace_fan_two_prescribed_incidences_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (c : I → EssentialMarkedArc M)
    (hfinite : ∀ i j, i ≠ j → (ArcSurgery.crossings M (c i) (c j)).Finite)
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
    (g₀ g₁ : I × Bool)
    (hg₀ : (if g₀.2 then (c g₀.1).val.map 1 else (c g₀.1).val.map 0) = p)
    (hg₁ : (if g₁.2 then (c g₁.1).val.map 1 else (c g₁.1).val.map 0) = p)
    (hne : g₀ ≠ g₁) :
    let incident : I × Bool → Prop := fun g =>
      (if g.2 then (c g.1).val.map 1 else (c g.1).val.map 0) = p
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p = 0 ∧ F.source ⊆ W ∧
      F.source ∩ (M.cover.branch : Set S) = {p} ∧
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
    ∃ v : I × Bool → Plane,
      (∀ g, incident g → v g ≠ 0) ∧
      v g₀ = Plane.mk 1 0 ∧
      (v g₁ = Plane.mk (-1) 0) ∧
      (∀ g, incident g → g ≠ g₀ → v g 1 = 0 → v g 0 ≤ 0) ∧
      (∀ g k, incident g → incident k → g ≠ k →
        segment ℝ (0 : Plane) (v g) ∩ segment ℝ (0 : Plane) (v k) = {0}) ∧
      (∀ g, incident g →
        Set.range ((c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) ⊆ F.source ∧
        Set.range (F ∘ (c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) =
          segment ℝ (0 : Plane) (v g)) ∧
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (0 : Plane) δ ⊆ F.target ∧
      (∀ g, incident g → δ < ‖v g‖) ∧
      (∀ i y, y ∈ F.source → F y ∈ Metric.ball (0 : Plane) δ →
        (y ∈ (c i).val.image ↔
          ∃ b : Bool, incident (i,b) ∧ F y ∈ segment ℝ (0 : Plane) (v (i,b)))) ∧
      (∀ i, ∃ K : Set S, IsCompact K ∧ p ∉ K ∧
        (c i).val.image = K ∪
          ⋃ b : Bool, if incident (i,b) then
            Set.range ((c i).val.map ∘ endpointGermParameter b r hr (by linarith)) else ∅) := by
  classical
  dsimp only
  let incident : I × Bool → Prop := fun g =>
    (if g.2 then (c g.1).val.map 1 else (c g.1).val.map 0) = p
  obtain ⟨e,hpe,hep,heW,hemarks,r,hr,hrhalf,v,hvn,hopp,hmeet,hgerms⟩ :=
    actual_marked_source_fan_two_prescribed_incidences_private M c hfinite p hp W hW hpW g₀ g₁ hg₀ hg₁ hne
  obtain ⟨ell,hell,hop⟩ := hopp
  obtain ⟨N,hNzero,hNunit,hNopp,hNsmul⟩ :=
    plane_selected_opposite_ray_normalization (v g₀) (hvn g₀ hg₀) ell hell
  let F : OpenPartialHomeomorph S Plane := e.trans N.toOpenPartialHomeomorph
  let w : I × Bool → Plane := N ∘ v
  have hFs : F.source = e.source := by simp [F]
  have hFval (x : S) : F x = N (e x) := rfl
  have hw0 : w g₀ = Plane.mk 1 0 := hNunit
  have hwn (g : I × Bool) (hi : incident g) : w g ≠ 0 := by
    intro he
    exact hvn g hi (N.injective (he.trans hNzero.symm))
  have hseg (g : I × Bool) : N '' segment ℝ (0 : Plane) (v g) = segment ℝ (0 : Plane) (w g) :=
    homogeneous_homeomorph_segment_image N hNzero hNsmul (v g)
  have hwmeet (g k : I × Bool) (hg : incident g) (hk : incident k) (hne : g ≠ k) :
      segment ℝ (0 : Plane) (w g) ∩ segment ℝ (0 : Plane) (w k) = {0} := by
    rw [← hseg g,← hseg k,← Set.image_inter N.injective,hmeet g k hg hk hne]
    simp [hNzero]
  have hwhole (g : I × Bool) (hi : incident g) :
      Set.range ((c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) ⊆ F.source ∧
      Set.range (F ∘ (c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) =
        segment ℝ (0 : Plane) (w g) := by
    refine ⟨fun x hx => hFs.symm ▸ (hgerms g hi).1 hx,?_⟩
    change range (N ∘ (e ∘ (c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith))) = _
    rw [Set.range_comp,(hgerms g hi).2,hseg]
  have hwhorizontal (g : I × Bool) (hi : incident g) (hne : g ≠ g₀)
      (hy : w g 1 = 0) : w g 0 ≤ 0 := by
    by_contra hn
    have hx : 0 < w g 0 := lt_of_not_ge hn
    let t := min (w g 0) 1 / 2
    have ht : 0 < t := half_pos (lt_min hx (by norm_num))
    have htg : t ≤ w g 0 := by dsimp [t]; linarith [min_le_left (w g 0) 1]
    have ht1 : t ≤ 1 := by dsimp [t]; linarith [min_le_right (w g 0) 1]
    let z : Plane := Plane.mk t 0
    have hzunit : z ∈ segment ℝ (0 : Plane) (w g₀) := by
      rw [hw0,segment_eq_image_lineMap]
      refine ⟨t,⟨ht.le,ht1⟩,?_⟩
      ext j
      fin_cases j <;> simp [z,Plane.mk,AffineMap.lineMap_apply_module]
    have hzg : z ∈ segment ℝ (0 : Plane) (w g) := by
      rw [segment_eq_image_lineMap]
      refine ⟨t / w g 0,⟨div_nonneg ht.le hx.le,(div_le_one hx).mpr htg⟩,?_⟩
      ext j
      fin_cases j
      · simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add]
        change (t / w g 0) * w g 0 = t
        field_simp
      · simp [z,Plane.mk,AffineMap.lineMap_apply_module,hy]
    have hzero : z = 0 := by
      have hz : z ∈ segment ℝ (0 : Plane) (w g) ∩ segment ℝ (0 : Plane) (w g₀) := ⟨hzg,hzunit⟩
      rw [hwmeet g g₀ hi hg₀ hne] at hz
      exact hz
    have htzero : t = 0 := congrArg (fun x : Plane => x 0) hzero
    exact (ne_of_gt ht) htzero
  obtain ⟨δ,hδ,hball,hδv,hinc⟩ := marked_endpoint_whole_trace_ball M c p hp F
    (hFs.symm ▸ hpe) (by rw [hFval,hep,hNzero]) r hr hrhalf w hwn
    (fun g hi => (hwhole g hi).1) (fun g hi => (hwhole g hi).2)
  refine ⟨F,hFs.symm ▸ hpe,?_,?_,?_,r,hr,hrhalf,w,hwn,hw0,?_,hwhorizontal,
    hwmeet,hwhole,δ,hδ,hball,hδv,hinc,?_⟩
  · rw [hFval,hep,hNzero]
  · exact hFs ▸ heW
  · rw [hFs]; exact hemarks
  · change N (v g₁) = _
    rw [hop,hNopp]
  · intro i
    exact marked_endpoint_compact_whole_remainder M (c i) p hp r hr hrhalf

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_whole_trace_fan_two_prescribed_incidences_private

namespace CurveComplex.HyperellipticModel
private theorem actual_single_incident_graph_original_loop_terminal_collars_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (hloop : b.val.map 0 = b.val.map 1)
    (j₀ : G) (terminal₀ : Bool)
    (hincident : (if terminal₀ then (graph j₀).val.map 1 else (graph j₀).val.map 0) = b.val.map 0)
    (honly : ∀ j terminal,
      ((if terminal then (graph j).val.map 1 else (graph j).val.map 0) = b.val.map 0 ↔
        j = j₀ ∧ terminal = terminal₀))
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let p := b.val.map 0
  let family : Option G → EssentialMarkedArc M := fun i => Option.elim i a graph
  obtain ⟨F,hpF,hFp,_,hmarks,r₀,hr₀,hr₀half,v,hvn,hv0,_,_,_,_,ε,hε,hεT,hεv,htrace,_⟩ :=
    actual_marked_endpoint_source_fan_chart M family hfinite p b.val.start_marked
      univ isOpen_univ (mem_univ _) (some j₀,terminal₀) hincident
  let U : Set S := F.source ∩ F ⁻¹' ball (0:Plane) (ε/2)
  have hU : IsOpen U := F.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hpF,by simpa [hFp] using half_pos hε⟩
  let e := F.restr U
  have hes : e.source = F.source ∩ U := by
    rw [OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have heval (x : S) : e x = F x := rfl
  have hpe : p ∈ e.source := hes.symm ▸ ⟨hpF,hpU⟩
  have he0 : e p = 0 := hFp
  have hxF (x : S) (hx : x ∈ e.source) : x ∈ F.source := (hes ▸ hx).1
  have hxBall (x : S) (hx : x ∈ e.source) : F x ∈ ball (0:Plane) ε :=
    (ball_subset_ball (by linarith : ε/2 ≤ ε)) ((hes ▸ hx).2.2)
  have hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = p := by
    intro x hx hm
    exact Set.mem_singleton_iff.mp (hmarks ▸ (show x ∈ F.source ∩ (M.cover.branch:Set S) from ⟨hxF x hx,hm⟩))
  have hR : 0 < ε/4 := by positivity
  have hRT : closedBall (0:Plane) (ε/4) ⊆ e.target := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ε/4 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hzε : z ∈ ball (0:Plane) ε := by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε by linarith)
    have hzF : z ∈ F.target := hεT hzε
    have hx : F.symm z ∈ e.source := by
      rw [hes]
      refine ⟨F.map_target hzF,⟨F.map_target hzF,?_⟩⟩
      rw [mem_preimage,F.right_inv hzF]
      simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε/2 by linarith)
    have hh := e.map_source hx
    change F (F.symm z) ∈ e.target at hh
    rw [F.right_inv hzF] at hh
    exact hh
  have hgraph : ∀ x, x ∈ e.source →
      (x ∈ ⋃ j, (graph j).val.image ↔ e x 1 = 0 ∧ 0 ≤ e x 0) := by
    intro x hx
    constructor
    · intro hp
      obtain ⟨j,hj⟩ := mem_iUnion.mp hp
      obtain ⟨terminal,hi,hs⟩ := (htrace (some j) x (hxF x hx) (hxBall x hx)).mp hj
      obtain ⟨hj0,ht0⟩ := (honly j terminal).mp hi
      subst j; subst terminal
      rw [hv0] at hs
      rw [segment_eq_image] at hs
      obtain ⟨d,hd,hde⟩ := hs
      have heq : e x = d • Plane.mk 1 0 := by simpa only [heval,smul_zero,add_zero,zero_add] using hde.symm
      rw [heq]
      constructor
      · simp
      · simpa using hd.1
    · intro hxaxis
      have hε1 : ε < 1 := by
        have hh := hεv (some j₀,terminal₀) hincident
        rw [hv0] at hh
        simpa [Plane.mk,EuclideanSpace.norm_eq] using hh
      have hx0 : e x 0 ≤ 1 := by
        have hh : |e x 0| ≤ ‖e x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e x) 0
        have hn : ‖e x‖ < ε := by simpa only [heval,mem_ball,dist_zero_right] using hxBall x hx
        exact (le_abs_self _).trans (hh.trans (hn.le.trans hε1.le))
      have hs : e x ∈ segment ℝ (0:Plane) (Plane.mk 1 0) := by
        rw [segment_eq_image]
        refine ⟨e x 0,⟨hxaxis.2,hx0⟩,?_⟩
        ext i
        fin_cases i <;> simp [hxaxis.1]
      apply mem_iUnion.mpr
      refine ⟨j₀,(htrace (some j₀) x (hxF x hx) (hxBall x hx)).mpr ?_⟩
      exact ⟨terminal₀,hincident,by simpa only [heval,hv0] using hs⟩
  let Old : Type := {terminal : Bool // (if terminal then a.val.map 1 else a.val.map 0) = p}
  let old : Old → Plane := fun k => v (none,k.val)
  have hold : ∀ k, old k ≠ 0 := fun k => hvn (none,k.val) k.property
  have haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k : Old, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k := by
    intro x hx hxs
    obtain ⟨terminal,hi,hs⟩ := (htrace none x (hxF x hxs) (hxBall x hxs)).mp hx
    rw [segment_eq_image] at hs
    obtain ⟨d,hd,hde⟩ := hs
    exact ⟨⟨terminal,hi⟩,d,hd.1,by simpa only [heval,smul_zero,add_zero,zero_add,old] using hde.symm⟩
  obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => b) p
    e.source e.open_source hpe
  have hsource : ∀ terminal t, b.val.map
      (endpointGermParameter terminal r hr (by linarith) t) ∈ e.source := by
    intro terminal t
    cases terminal
    · apply hstart PUnit.unit rfl
      change r*t.val ≤ r
      nlinarith [t.property.2]
    · apply hend PUnit.unit hloop.symm
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  exact actual_marked_loop_graph_fixed_both_terminal_collars_single_graph_ray_private M a b hloop e
    hpe he0 hemarks (⋃ j,(graph j).val.image) hgraph hbP old hold haOld
    (ε/4) hR hRT r hr hrhalf hsource
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_single_incident_graph_original_loop_terminal_collars_private

namespace CurveComplex.HyperellipticModel
private theorem actual_disjoint_family_single_incident_graph_loop_terminal_collars_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {I : Type} (r : I → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (J : Finset I) (u : I) (hu : u ∉ J) (b : EssentialMarkedArc M)
    (hloop : b.val.map 0 = b.val.map 1)
    (j₀ : {j // j ∈ J}) (terminal₀ : Bool)
    (hincident : (if terminal₀ then (r j₀.val).val.map 1 else (r j₀.val).val.map 0) = b.val.map 0)
    (honly : ∀ j : {j // j ∈ J}, ∀ terminal,
      ((if terminal then (r j.val).val.map 1 else (r j.val).val.map 0) = b.val.map 0 ↔
        j = j₀ ∧ terminal = terminal₀))
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j : {j // j ∈ J}, (r j.val).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j : {j // j ∈ J}, (r j.val).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ (r u).val.image := by
  classical
  let G := {j // j ∈ J}
  let f : Option G → I := fun i => Option.elim i u (fun j => j.val)
  have hf : Function.Injective f := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        exfalso
        have he' : u = j.val := he
        exact hu (he'.symm ▸ j.property)
    | some i =>
      cases j with
      | none =>
        exfalso
        have he' : i.val = u := he
        exact hu (he' ▸ i.property)
      | some j => exact congrArg some (Subtype.ext he)
  have hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i (r u) (fun j : G => r j.val))
        (Option.elim j (r u) (fun j : G => r j.val))).Finite := by
    intro i j hij
    have hdis := hd (f i) (f j) (fun he => hij (hf he))
    have hfamily (i : Option G) : Option.elim i (r u) (fun j : G => r j.val) = r (f i) := by
      cases i <;> rfl
    have hzero : ArcSurgery.crossings M (r (f i)) (r (f j)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact Set.disjoint_left.mp hdis hx.1 hx.2
    rw [hfamily i,hfamily j,hzero]
    exact Set.finite_empty
  exact actual_single_incident_graph_original_loop_terminal_collars_private M
    (fun j : G => r j.val) (r u) b hfinite hloop j₀ terminal₀ hincident honly hbP
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_disjoint_family_single_incident_graph_loop_terminal_collars_private

namespace CurveComplex.HyperellipticModel
private theorem actual_aligned_disjoint_families_single_incident_graph_loop_terminal_collars_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {I : Type} (r : I → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (J : Finset I) (u : I) (hu : u ∉ J) (s : I → EssentialMarkedArc M)
    (hsd : ∀ i j, i ≠ j → Disjoint (arcInterior M (s i)) (arcInterior M (s j)))
    (haligned : ∀ j ∈ J, (s j).val.image = (r j).val.image)
    (b : EssentialMarkedArc M) (hb : b = s u)
    (hloop : b.val.map 0 = b.val.map 1)
    (j₀ : {j // j ∈ J}) (terminal₀ : Bool)
    (hincident : (if terminal₀ then (r j₀.val).val.map 1 else (r j₀.val).val.map 0) = b.val.map 0)
    (honly : ∀ j : {j // j ∈ J}, ∀ terminal,
      ((if terminal then (r j.val).val.map 1 else (r j.val).val.map 0) = b.val.map 0 ↔
        j = j₀ ∧ terminal = terminal₀))
 :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j : {j // j ∈ J}, (r j.val).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ (r u).val.image := by
  classical
  have hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j : {j // j ∈ J}, (r j.val).val.image := by
    intro t ht0 ht1 hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    have hnotmark : b.val.map t ∉ M.cover.branch := by
      intro hm
      rcases b.val.marked_only_at_ends t hm with he|he
      · have hv := congrArg Subtype.val he
        change t.val = 0 at hv
        linarith
      · have hv := congrArg Subtype.val he
        change t.val = 1 at hv
        linarith
    have hsu : b.val.map t ∈ arcInterior M (s u) := by
      subst b
      exact ⟨mem_range_self t,hnotmark⟩
    have hsj : b.val.map t ∈ arcInterior M (s j.val) :=
      ⟨(haligned j.val j.property).symm ▸ hj,hnotmark⟩
    exact Set.disjoint_left.mp (hsd u j.val (fun he => hu (he.symm ▸ j.property))) hsu hsj
  exact actual_disjoint_family_single_incident_graph_loop_terminal_collars_private
    M r hd J u hu b hloop j₀ terminal₀ hincident honly hbP
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_aligned_disjoint_families_single_incident_graph_loop_terminal_collars_private


namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Every interior point of the old disjoint system has a genuine source
crosscut chart supported away from all marks and all other complete arcs. -/
private theorem actual_loop_capable_disjoint_system_interior_crosscut_chart
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (i : ι)
    (p : S) (hp : p ∈ arcInterior M (r i)) :
    ∃ Echart : OpenPartialHomeomorph S Plane,
      p ∈ Echart.source ∧ Disjoint Echart.source (M.cover.branch : Set S) ∧
      (∀ j, j ≠ i → Disjoint Echart.source (r j).val.image) ∧
      (∀ x ∈ Echart.source, x ∈ (r i).val.image ↔ Echart x 1 = 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨τ,hτ⟩ := hp.1
  have hτ0 : 0 < τ.val := by
    apply lt_of_le_of_ne τ.property.1
    intro h
    have ht : τ = (⟨0,by norm_num⟩ : Interval) := Subtype.ext h.symm
    subst τ
    exact hp.2 (hτ ▸ (r i).val.start_marked)
  have hτ1 : τ.val < 1 := by
    apply lt_of_le_of_ne τ.property.2
    intro h
    have ht : τ = (⟨1,by norm_num⟩ : Interval) := Subtype.ext h
    subst τ
    exact hp.2 (hτ ▸ (r i).val.end_marked)
  letI := (actualSphereSmoothAtlas M).charts
  let e : OpenPartialHomeomorph S Plane := chartAt Plane p
  obtain ⟨W₀,hW₀,hpW₀,hmarks₀,hothers₀⟩ := finite_arc_system_isolated_neighborhood M r hd i p hp
  let W := W₀ ∩ e.source
  have hW : IsOpen W := hW₀.inter e.open_source
  have hpoint : (r i).val.map τ ∈ W := by
    rw [hτ]
    exact ⟨hpW₀,mem_chart_source Plane p⟩
  have he : ∀ z ∈ W,z ∈ e.source := fun z hz => hz.2
  have hmarks : Disjoint W (M.cover.branch:Set S) := hmarks₀.mono_left inter_subset_left
  have hothers : ∀ j,j≠i → Disjoint W (r j).val.image :=
    fun j hj => (hothers₀ j hj).mono_left inter_subset_left
  let g : ℝ → S := (r i).val.map ∘ Set.projIcc 0 1 zero_le_one
  have hg : Continuous g := (r i).val.continuous.comp continuous_projIcc
  have hgτ : g τ.val = (r i).val.map τ := by
    dsimp [g]
    rw [Set.projIcc_val]
  have hnear : g ⁻¹' W ∈ nhds τ.val := hg.continuousAt.preimage_mem_nhds
    (by rw [hgτ]; exact hW.mem_nhds hpoint)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := min δ (min τ.val (1-τ.val)) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ (min τ.val (1-τ.val))]
  have hετ : ε < τ.val := by
    have hh := (min_le_right δ (min τ.val (1-τ.val))).trans (min_le_left _ _)
    dsimp [ε]; linarith
  have hε1 : ε < 1-τ.val := by
    have hh := (min_le_right δ (min τ.val (1-τ.val))).trans (min_le_right _ _)
    dsimp [ε]; linarith
  let l := τ.val-ε
  let u := τ.val+ε
  have hl : 0 < l := by dsimp [l]; linarith
  have hlu : l < u := by dsimp [l,u]; linarith
  have hu : u < 1 := by dsimp [u]; linarith
  have hsub : g '' Icc l u ⊆ W ∩ e.source := by
    rintro _ ⟨t,ht,rfl⟩
    have htW : g t ∈ W := by
      apply hball
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      dsimp [l,u] at ht
      constructor <;> linarith [ht.1,ht.2]
    exact ⟨htW,htW.2⟩
  obtain ⟨Echart,hE,_,hseg,_,_,hflat,_⟩ :=
    actual_interval_subarc_crosscut_chart (r i).val.map (r i).val.continuous
      (r i).val.injective_except_loop_closure l u hl hlu hu e W hW hsub
  have hpseg : p ∈ g '' Icc l u := by
    refine ⟨τ.val,?_,hgτ.trans hτ⟩
    dsimp [l,u]
    constructor <;> linarith
  refine ⟨Echart,hseg hpseg,hmarks.mono (fun _ hx => (hE hx).1) (Subset.refl _),?_,hflat⟩
  intro j hj
  exact (hothers j hj).mono (fun _ hx => (hE hx).1) (Subset.refl _)


private theorem actual_loop_capable_disjoint_system_prepared_interior_cover
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    ∀ p : S, p ∉ M.cover.branch →
      ∃ e : OpenPartialHomeomorph S Plane,
        p ∈ e.source ∧ Disjoint e.source (M.cover.branch : Set S) ∧
        ∃ label : Option ι, ∀ j x, x ∈ e.source →
          (x ∈ (r j).val.image ↔ label = some j ∧ e x 0 = 0) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI := (actualSphereSmoothAtlas M).charts
  let L : Plane ≃ₜ ℝ × ℝ := ((EuclideanSpace.equiv (Fin 2) ℝ).trans
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let flip : Plane ≃ₜ Plane := (L.trans (Homeomorph.prodComm ℝ ℝ)).trans L.symm
  have hflip (z : Plane) : flip z 0 = z 1 := rfl
  intro p hp
  by_cases hex : ∃ i, p ∈ (r i).val.image
  · obtain ⟨i,hpi⟩ := hex
    obtain ⟨E0,hpE0,hmarks,hothers,hflat⟩ :=
      actual_loop_capable_disjoint_system_interior_crosscut_chart M r hd i p ⟨hpi,hp⟩
    let e := E0.trans flip.toOpenPartialHomeomorph
    have heSource : e.source = E0.source := by
      ext x; simp [e,OpenPartialHomeomorph.trans_source]
    refine ⟨e,heSource.symm ▸ hpE0,?_,some i,?_⟩
    · simpa only [heSource] using hmarks
    · intro j x hx
      have hx0 : x ∈ E0.source := heSource ▸ hx
      have hcoord : e x 0 = E0 x 1 := hflip (E0 x)
      by_cases hij : i = j
      · subst j
        simpa only [Option.some.injEq,eq_self,true_and,hcoord] using hflat x hx0
      · have hxnot : x ∉ (r j).val.image := fun hj =>
          Set.disjoint_left.mp (hothers j (Ne.symm hij)) hx0 hj
        simp only [Option.some.injEq,hij,false_and,iff_false]
        exact hxnot
  · let forbidden : Set S := (⋃ j, (r j).val.image) ∪ (M.cover.branch : Set S)
    have hclosed : IsClosed forbidden :=
      (markedFamily_graph_compact (fun j => (r j).val)).isClosed.union
        M.cover.branch.finite_toSet.isClosed
    let E0 := chartAt Plane p
    let e := E0.restr forbiddenᶜ
    have heSource : e.source = E0.source ∩ forbiddenᶜ := by
      rw [OpenPartialHomeomorph.restr_source,hclosed.isOpen_compl.interior_eq]
    have hpF : p ∉ forbidden := by
      rintro (h | h)
      · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
        exact hex ⟨j,hj⟩
      · exact hp h
    refine ⟨e,heSource.symm ▸ ⟨mem_chart_source _ _,hpF⟩,?_,none,?_⟩
    · exact Set.disjoint_left.mpr (fun x hx hm => (heSource.le hx).2 (Or.inr hm))
    · intro j x hx
      constructor
      · intro hj
        exact False.elim ((heSource.le hx).2 (Or.inl (Set.mem_iUnion.mpr ⟨j,hj⟩)))
      · rintro ⟨h,_⟩
        cases h


private theorem actual_loop_capable_new_arc_compact_interior_chart_subdivision
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (a : EssentialMarkedArc M)
    (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1) :
    ∃ η : C(Interval,S),
      (∀ t, η t = a.val.map ⟨l+(u-l)*t.val, by
        constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
      Topology.IsClosedEmbedding η ∧
      ∃ n : ℕ, 0 < n ∧
        ∃ (chart : Fin n → OpenPartialHomeomorph S Plane) (label : Fin n → Option ι),
          (∀ k, Disjoint (chart k).source (M.cover.branch : Set S)) ∧
          (∀ k j x, x ∈ (chart k).source →
            (x ∈ (r j).val.image ↔ label k = some j ∧ chart k x 0 = 0)) ∧
          ∀ k (t : Interval), (k.val:ℝ)/n ≤ t.val →
            t.val ≤ (k.val+1:ℝ)/n → η t ∈ (chart k).source := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let η : C(Interval,S) := ⟨fun t => a.val.map ⟨l+(u-l)*t.val, by
    constructor <;> nlinarith [t.property.1,t.property.2]⟩,
    by
      have hc : Continuous (fun t : Interval => (⟨l+(u-l)*t.val, by
        constructor <;> nlinarith [t.property.1,t.property.2]⟩ : Interval)) := by fun_prop
      exact a.val.continuous.comp hc⟩
  have hemb : Topology.IsClosedEmbedding η := η.continuous.isClosedEmbedding (by
    intro t s heq
    rcases a.val.injective_except_loop_closure _ _ heq with h | h | h
    · have h := congrArg Subtype.val h
      apply Subtype.ext
      change l+(u-l)*t.val = l+(u-l)*s.val at h
      nlinarith
    · have h := congrArg Subtype.val h.1
      change l+(u-l)*t.val=0 at h
      nlinarith [t.property.1]
    · have h := congrArg Subtype.val h.1
      change l+(u-l)*t.val=1 at h
      nlinarith [t.property.2])
  have hclean (t : Interval) : η t ∉ M.cover.branch := by
    intro hm
    rcases a.val.marked_only_at_ends _ hm with h | h
    · have hh := congrArg Subtype.val h
      change l+(u-l)*t.val = 0 at hh
      nlinarith [t.property.1,t.property.2]
    · have hh := congrArg Subtype.val h
      change l+(u-l)*t.val = 1 at hh
      nlinarith [t.property.1,t.property.2]
  have hlocal (t : Interval) := actual_loop_capable_disjoint_system_prepared_interior_cover
    M r hd (η t) (hclean t)
  choose e hpoint hmarks label hlabel using hlocal
  obtain ⟨n,hn,choice,hsub⟩ := position_interval_subdivision η
    (fun t => (e t).source) (fun t => (e t).open_source) (fun t => ⟨t,hpoint t⟩)
  exact ⟨η,fun _ => rfl,hemb,n,hn,fun k => e (choice k),fun k => label (choice k),
    fun k => hmarks (choice k),fun k => hlabel (choice k),hsub⟩


private theorem actual_loop_capable_compact_interior_subdivision_in_prescribed_open_private
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (a : EssentialMarkedArc M)
    (V : Set S) (hV : IsOpen V)
    (haV : arcInterior M a ⊆ V)
    (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1) :
    ∃ η : C(Interval,S),
      (∀ t, η t = a.val.map ⟨l+(u-l)*t.val, by
        constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
      Topology.IsClosedEmbedding η ∧
      ∃ n : ℕ, 0 < n ∧
        ∃ (chart : Fin n → OpenPartialHomeomorph S Plane) (label : Fin n → Option ι),
          (∀ k, (chart k).source ⊆ V) ∧
          (∀ k, Disjoint (chart k).source (M.cover.branch : Set S)) ∧
          (∀ k j x, x ∈ (chart k).source →
            (x ∈ (r j).val.image ↔ label k = some j ∧ chart k x 0 = 0)) ∧
          ∀ k (t : Interval), (k.val:ℝ)/n ≤ t.val →
            t.val ≤ (k.val+1:ℝ)/n → η t ∈ (chart k).source := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let η : C(Interval,S) := ⟨fun t => a.val.map ⟨l+(u-l)*t.val, by
    constructor <;> nlinarith [t.property.1,t.property.2]⟩,
    by
      have hc : Continuous (fun t : Interval => (⟨l+(u-l)*t.val, by
        constructor <;> nlinarith [t.property.1,t.property.2]⟩ : Interval)) := by fun_prop
      exact a.val.continuous.comp hc⟩
  have hemb : Topology.IsClosedEmbedding η := η.continuous.isClosedEmbedding (by
    intro t s heq
    rcases a.val.injective_except_loop_closure _ _ heq with h | h | h
    · have h := congrArg Subtype.val h
      apply Subtype.ext
      change l+(u-l)*t.val = l+(u-l)*s.val at h
      nlinarith
    · have h := congrArg Subtype.val h.1
      change l+(u-l)*t.val=0 at h
      nlinarith [t.property.1]
    · have h := congrArg Subtype.val h.1
      change l+(u-l)*t.val=1 at h
      nlinarith [t.property.2])
  have hclean (t : Interval) : η t ∉ M.cover.branch := by
    intro hm
    rcases a.val.marked_only_at_ends _ hm with h | h
    · have hh := congrArg Subtype.val h
      change l+(u-l)*t.val = 0 at hh
      nlinarith [t.property.1,t.property.2]
    · have hh := congrArg Subtype.val h
      change l+(u-l)*t.val = 1 at hh
      nlinarith [t.property.1,t.property.2]
  have hlocal (t : Interval) := actual_loop_capable_disjoint_system_prepared_interior_cover
    M r hd (η t) (hclean t)
  choose e₀ hpoint₀ hmarks₀ label hlabel₀ using hlocal
  let e (t : Interval) := (e₀ t).restr V
  have hsource (t : Interval) : (e t).source=(e₀ t).source ∩ V := by
    rw [OpenPartialHomeomorph.restr_source,hV.interior_eq]
  have hpoint (t : Interval) : η t ∈ (e t).source := by
    rw [hsource]
    exact ⟨hpoint₀ t,haV ⟨Set.mem_range_self _,hclean t⟩⟩
  have hmarks (t : Interval) : Disjoint (e t).source (M.cover.branch:Set S) :=
    (hmarks₀ t).mono_left ((hsource t).le.trans inter_subset_left)
  have hlabel (t : Interval) (j : ι) (x : S) (hx : x ∈ (e t).source) :
      x ∈ (r j).val.image ↔ label t=some j ∧ e t x 0=0 :=
    hlabel₀ t j x ((hsource t).le hx).1
  obtain ⟨n,hn,choice,hsub⟩ := position_interval_subdivision η
    (fun t => (e t).source) (fun t => (e t).open_source) (fun t => ⟨t,hpoint t⟩)
  exact ⟨η,fun _ => rfl,hemb,n,hn,fun k => e (choice k),fun k => label (choice k),
    (fun k => (hsource (choice k)).le.trans inter_subset_right),
    fun k => hmarks (choice k),fun k => hlabel (choice k),hsub⟩



private theorem actual_point_off_disjoint_arc_system_loop_capable_private
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (p : S) (hp : p ∉ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ H : AmbientIsotopy S,
      (∀ j, H.finalMap p ∉ (r j).val.image) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      ∀ t x, x ∉ W → H.map (t,x) = x := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  by_cases hnone : ∀ j, p ∉ (r j).val.image
  · exact ⟨AmbientIsotopy.identity S,hnone,fun _ _ _ => rfl,fun _ _ _ => rfl⟩
  push_neg at hnone
  obtain ⟨i,hpi⟩ := hnone
  obtain ⟨E0,hpE0,hmarks,label,hlabel⟩ :=
    actual_loop_capable_disjoint_system_prepared_interior_cover M r hd p hp
  have hlabeli := (hlabel i p hpE0).mp hpi
  have hpaxis : E0 p 0 = 0 := hlabeli.2
  let U : Set S := W ∩ (M.cover.branch : Set S)ᶜ
  have hU : IsOpen U := hW.inter M.cover.branch.finite_toSet.isClosed.isOpen_compl
  let e : OpenPartialHomeomorph S Plane :=
    (E0.restr U).trans (Homeomorph.addRight (-(E0 p))).toOpenPartialHomeomorph
  have heSource : e.source = E0.source ∩ U := by
    ext x
    simp [e,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have hpe : p ∈ e.source := heSource.symm ▸ ⟨hpE0,hpW,hp⟩
  have he (x : S) : e x = E0 x-E0 p := by simp [e,sub_eq_add_neg]
  have hep : e p = 0 := by simp [he]
  have hzero : (0:Plane) ∈ e.target := hep ▸ e.map_source hpe
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hzero)
  let R : ℝ := ε/2
  have hR : 0 < R := by dsimp [R]; positivity
  have htarget : closedBall (0:Plane) R ⊆ e.target := by
    intro z hz
    apply hball
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by dsimp [R]; linarith))
  let unit : Plane := Plane.mk 1 0
  have hunit : ‖unit‖ = 1 := by
    norm_num [unit,EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk]
  let v : Plane := (R/4) • unit
  have hv : ‖v‖ < R/2 := by
    dsimp [v]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),hunit]
    linarith
  obtain ⟨P,hinner,houter⟩ := CurveComplex.GenusOrientationCandidate.plane_flat_bump_translation R hR v hv
  obtain ⟨K,H,hcoord,hHK,hout⟩ := position_surface_chart_lift S e.source e.target
    e.open_source e.toHomeomorphSourceTarget (closedBall (0:Plane) R)
    (isCompact_closedBall _ _) htarget P houter
  have hstay (t : Interval) : H.map (t,p) ∈ e.source := by
    rw [hHK t ⟨p,hpe⟩]
    exact (K.map (t,⟨p,hpe⟩)).property
  have hmove : e (H.finalMap p) = v := by
    rw [show H.finalMap p = (K.map (⟨1,by norm_num⟩,⟨p,hpe⟩)).val from
      hHK ⟨1,by norm_num⟩ ⟨p,hpe⟩]
    change (e.toHomeomorphSourceTarget (K.map (⟨1,by norm_num⟩,⟨p,hpe⟩))).val = v
    rw [hcoord]
    change P.map (⟨1,by norm_num⟩,e p) = v
    rw [hep,hinner _ _ (by change (0:Plane) ∈ closedBall 0 (R/2); exact mem_closedBall_self (by positivity))]
    simp
  have hmovedaxis : E0 (H.finalMap p) 0 ≠ 0 := by
    have hh := congrArg (fun z : Plane => z 0) hmove
    simp only [he,PiLp.sub_apply,hpaxis,sub_zero] at hh
    have hv0 : v 0 = R/4 := by simp [v,unit,Plane.mk]
    rw [hv0] at hh
    rw [hh]
    positivity
  refine ⟨H,?_,?_,?_⟩
  · intro j hm
    have hx0 : H.finalMap p ∈ E0.source := (heSource.le (hstay ⟨1,by norm_num⟩)).1
    exact hmovedaxis ((hlabel j (H.finalMap p) hx0).mp hm).2
  · intro t x hm
    exact hout t x (fun hx => (heSource.le hx).2.2 hm)
  · intro t x hx
    exact hout t x (fun he => hx (heSource.le he).2.1)


private theorem actual_localized_marked_seam_repair_loop_capable_private
    (M : HyperellipticModel E S) {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (p : κ → S) (hpi : Function.Injective p)
    (hpmark : ∀ k, p k ∉ M.cover.branch)
    (arc : μ → C(Interval,S)) (e : μ → OpenPartialHomeomorph S Plane)
    (hchart : ∀ i, Set.range (arc i) ⊆ (e i).source)
    (W : κ → Set S) (hW : ∀ k, IsOpen (W k)) (hpW : ∀ k, p k ∈ W k) :
    ∃ U : κ → Set S, ∃ H : AmbientIsotopy S,
      (∀ k, IsOpen (U k)) ∧ (∀ k, p k ∈ U k) ∧
      (∀ k, U k ⊆ W k) ∧ (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
      (∀ k j, H.finalMap (p k) ∉ (r j).val.image) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∉ ⋃ k, U k → H.map (t,x) = x) ∧
      (∀ i t, (fun x => H.map (t,x)) '' Set.range (arc i) ⊆ (e i).source) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hclosed (i : μ) : IsClosed (Set.range (arc i)) :=
    (isCompact_range (arc i).continuous).isClosed
  let V : κ → μ → Set S := fun k i =>
    if p k ∈ Set.range (arc i) then (e i).source else (Set.range (arc i))ᶜ
  have hVopen (k i) : IsOpen (V k i) := by
    dsimp [V]; split
    · exact (e i).open_source
    · exact (hclosed i).isOpen_compl
  have hpV (k i) : p k ∈ V k i := by
    dsimp [V]; split
    · rename_i hi; exact hchart i hi
    · assumption
  obtain ⟨D,hD,hDdis⟩ := (Set.finite_range p).t2_separation
  let U : κ → Set S := fun k => W k ∩ (D (p k) ∩ ⋂ i, V k i)
  have hU (k) : IsOpen (U k) :=
    (hW k).inter ((hD (p k)).2.inter (isOpen_iInter_of_finite (hVopen k)))
  have hpU (k) : p k ∈ U k :=
    ⟨hpW k,(hD (p k)).1,Set.mem_iInter.mpr (hpV k)⟩
  have hdis (k l) (hkl : k ≠ l) : Disjoint (U k) (U l) :=
    (hDdis (Set.mem_range_self k) (Set.mem_range_self l)
      (fun hh => hkl (hpi hh))).mono (fun _ hx => hx.2.1) (fun _ hx => hx.2.1)
  have hmove (k) := actual_point_off_disjoint_arc_system_loop_capable_private M r hd
    (p k) (hpmark k) (U k) (hU k) (hpU k)
  choose moves hoff hmarks hfix using hmove
  obtain ⟨H,hout,hinside⟩ := finite_supported_patch_assembly U hdis moves hfix
  have hstay (t : Interval) (k : κ) (x : S) (hx : x ∈ U k) : H.map (t,x) ∈ U k := by
    rw [hinside k t x hx]
    by_contra hn
    obtain ⟨g,hg⟩ := (moves k).homeomorphism_at t
    have hfixed : (moves k).map (t,(moves k).map (t,x)) = (moves k).map (t,x) :=
      hfix k t _ hn
    have heq : (moves k).map (t,x) = x := g.injective (by simpa only [hg] using hfixed)
    exact hn (heq.symm ▸ hx)
  refine ⟨U,H,hU,hpU,(fun _ => inter_subset_left),hdis,?_,?_,hout,?_⟩
  · intro k j
    change H.map (⟨1,by norm_num⟩,p k) ∉ _
    rw [hinside k ⟨1,by norm_num⟩ (p k) (hpU k)]
    exact hoff k j
  · intro t x hx
    by_cases hi : x ∈ ⋃ k, U k
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hi
      rw [hinside k t x hk]; exact hmarks k t x hx
    · exact hout t x hi
  · intro i t y hy
    obtain ⟨x,hx,rfl⟩ := hy
    by_cases hi : x ∈ ⋃ k, U k
    · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hi
      have hpC : p k ∈ Set.range (arc i) := by
        by_contra hn
        have hv := Set.mem_iInter.mp hk.2.2 i
        exact (show x ∉ Set.range (arc i) by simpa only [V,if_neg hn,Set.mem_compl_iff] using hv) hx
      have hv := Set.mem_iInter.mp (hstay t k x hk).2.2 i
      simpa only [V,if_pos hpC] using hv
    · change H.map (t,x) ∈ (e i).source
      rw [hout t x hi]; exact hchart i hx


open CurveComplex.ArcFinitePosition

private theorem actual_loop_capable_graph_relative_internal_mesh_seam_repair_private
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M)
    (V : Set S) (hV : IsOpen V) (haV : arcInterior M a ⊆ V)
    (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1) :
    ∃ η : C(Interval,S),
      (∀ t, η t = a.val.map ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
      Topology.IsClosedEmbedding η ∧
      ∃ n : ℕ, ∃ hn : 0 < n,
      ∃ e : Fin n → OpenPartialHomeomorph S Plane, ∃ label : Fin n → Option ι,
      ∃ H : AmbientIsotopy S, ∃ b : EssentialMarkedArc M,
        (∀ t x,x ∈ M.cover.branch → H.map (t,x)=x) ∧
        (∀ t x,x ∉ V → H.map (t,x)=x) ∧
        (∀ k, (e k).source ⊆ V) ∧
        (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
        (∀ k j x, x ∈ (e k).source →
          (x ∈ (old j).val.image ↔ label k = some j ∧ e k x 0 = 0)) ∧
        Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
        (∀ t, b.val.map t = H.finalMap (a.val.map t)) ∧
        (∀ t : Interval, (t:ℝ) ≤ l ∨ u ≤ (t:ℝ) → b.val.map t = a.val.map t) ∧
        (∀ k t, H.finalMap (η (intervalMeshParameter n hn k t)) ∈ (e k).source) ∧
        ∀ k : Fin (n-1), ∀ j,
          H.finalMap (η ⟨((k.val:ℝ)+1)/n,by
            have hnR : (0:ℝ) < n := by exact_mod_cast hn
            constructor
            · positivity
            · apply (div_le_one hnR).mpr
              have hk : k.val+1 ≤ n := by omega
              exact_mod_cast hk⟩) ∉ (old j).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨η,hη,hi,n,hn,e,label,heV,hemarks,hlabel,hchart⟩ :=
    actual_loop_capable_compact_interior_subdivision_in_prescribed_open_private M old hd a V hV haV l u hl hlu hu
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let σ : Fin (n-1) → Interval := fun k => ⟨((k.val:ℝ)+1)/n,by
    constructor
    · positivity
    · apply (div_le_one hnR).mpr
      have hk : k.val+1 ≤ n := by omega
      exact_mod_cast hk⟩
  have hσ0 (k : Fin (n-1)) : 0 < (σ k:ℝ) := div_pos (by positivity) hnR
  have hσ1 (k : Fin (n-1)) : (σ k:ℝ) < 1 := by
    apply (div_lt_one hnR).mpr
    have hk : k.val+1 < n := by omega
    exact_mod_cast hk
  let p : Fin (n-1) → S := fun k => η (σ k)
  have hpi : Function.Injective p := by
    intro k j he
    have hh := congrArg Subtype.val (hi.injective he)
    change ((k.val:ℝ)+1)/n = ((j.val:ℝ)+1)/n at hh
    have hh' := (div_left_inj' hnR.ne').mp hh
    apply Fin.ext
    exact Nat.cast_injective (by linarith : (k.val:ℝ) = j.val)
  have hpm (k : Fin (n-1)) : p k ∉ M.cover.branch := by
    rw [show p k = η (σ k) from rfl,hη]
    intro hm
    rcases a.val.marked_only_at_ends _ hm with he | he
    · have hh := congrArg Subtype.val he
      change l+(u-l)*(σ k:ℝ) = 0 at hh
      nlinarith [hσ0 k]
    · have hh := congrArg Subtype.val he
      change l+(u-l)*(σ k:ℝ) = 1 at hh
      nlinarith [hσ1 k]
  let tailParameters : Set Interval := {t | (t:ℝ) ≤ l ∨ u ≤ (t:ℝ)}
  let tails : Set S := a.val.map '' tailParameters
  have htailClosed : IsClosed tailParameters :=
    (isClosed_le continuous_subtype_val continuous_const).union
      (isClosed_le continuous_const continuous_subtype_val)
  have htails : IsClosed tails := (htailClosed.isCompact.image a.val.continuous).isClosed
  have hpTail (k : Fin (n-1)) : p k ∉ tails := by
    rintro ⟨t,ht,he⟩
    rw [show p k = η (σ k) from rfl,hη] at he
    rcases a.val.injective_except_loop_closure _ _ he with he | he | he
    · have heq := congrArg Subtype.val he
      change (t:ℝ) = l+(u-l)*(σ k:ℝ) at heq
      rcases ht with ht | ht <;> nlinarith [hσ0 k,hσ1 k]
    · have heq := congrArg Subtype.val he.2
      change l+(u-l)*(σ k:ℝ)=1 at heq
      nlinarith [hσ1 k]
    · have heq := congrArg Subtype.val he.2
      change l+(u-l)*(σ k:ℝ)=0 at heq
      nlinarith [hσ0 k]
  let arc : Fin n → C(Interval,S) := fun k =>
    ⟨η ∘ intervalMeshParameter n hn k,η.continuous.comp (intervalMeshParameter_continuous n hn k)⟩
  have hpiece (k : Fin n) : Set.range (arc k) ⊆ (e k).source := by
    rintro x ⟨t,rfl⟩
    apply hchart k
    · change (k.val:ℝ)/n ≤ ((k.val:ℝ)+(t:ℝ))/n
      exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [t.property.1])
    · change ((k.val:ℝ)+(t:ℝ))/n ≤ (k.val+1:ℝ)/n
      exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [t.property.2])
  obtain ⟨U,H,_,_,hUW,_,havoid,hmarks,hout,hpreserve⟩ :=
    actual_localized_marked_seam_repair_loop_capable_private M old hd p hpi hpm arc e hpiece
      (fun _ => tailsᶜ ∩ V) (fun _ => htails.isOpen_compl.inter hV)
      (fun k => ⟨hpTail k,haV ⟨⟨_,(hη (σ k)).symm⟩,hpm k⟩⟩)
  have htailfix (t : Interval) (x : S) (hx : x ∈ tails) : H.map (t,x) = x := by
    apply hout t x
    intro hh
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
    exact (hUW k hk).1 hx
  have hVfix : ∀ t x,x ∉ V → H.map (t,x)=x := by
    intro t x hx
    apply hout t x
    intro hi
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hi
    exact hx (hUW k hk).2
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
  let b := a.transport g hfix
  refine ⟨η,hη,hi,n,hn,e,label,H,b,hmarks,hVfix,heV,hemarks,hlabel,?_,?_,?_,?_,havoid⟩
  · apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image a.val g hfix).symm
  · intro t; change g (a.val.map t) = H.finalMap (a.val.map t); rw [hfinal]
  · intro t ht
    change g (a.val.map t) = a.val.map t
    rw [← hfinal]
    exact htailfix 1 _ ⟨t,ht,rfl⟩
  · intro k t
    exact hpreserve k 1 ⟨η (intervalMeshParameter n hn k t),Set.mem_range_self t,rfl⟩


private theorem actual_loop_capable_graph_relative_finite_position_from_actual_clear_collars_private
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hd : ∀ i j,i≠j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) (V : Set S) (hV : IsOpen V) (haV : arcInterior M a ⊆ V)
    (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (houter : ∀ t : Interval,0 < (t:ℝ) → (t:ℝ) < 1 →
      (t:ℝ) ≤ l ∨ u ≤ (t:ℝ) → ∀ j,a.val.map t ∉ (old j).val.image) :
    ∃ b : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      Quotient.mk (essentialArcSetoid M) b=Quotient.mk (essentialArcSetoid M) a ∧
      H.finalMap '' a.val.image=b.val.image ∧
      (∀ t x,x ∈ M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x,x ∉ V → H.map (t,x)=x) ∧
      ∀ j,(arcInterior M b ∩ (old j).val.image).Finite ∧
        ∀ q ∈ arcInterior M b ∩ (old j).val.image,ArcSurgery.CrossesInDisk M (old j) b q := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨η,hη,hi,n,hn,e,label,K,a₁,hmarksK,houtK,heV,hemarks,hlabel,hclassK,hmapK,htails,hpiece,hseam⟩ :=
    actual_loop_capable_graph_relative_internal_mesh_seam_repair_private M old hd a V hV haV l u hl hlu hu
  obtain ⟨g,hg⟩ := K.homeomorphism_at (1:Interval)
  have hfinal : K.finalMap=g := funext (fun x => (hg x).symm)
  let ν : C(Interval,S) := ⟨g ∘ η,g.continuous.comp η.continuous⟩
  have hν (t : Interval) : ν t=K.finalMap (η t) := by change g (η t)=_;rw [hfinal]
  have hνliteral (t : Interval) : ν t=a₁.val.map ⟨l+(u-l)*t.val,by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩ := by rw [hν,hη,hmapK]
  have hνinj : Function.Injective ν := g.injective.comp hi.injective
  have hends := actual_interval_mesh_all_ends_off η K (fun i => (old i).val.image) n hn
    (by
      intro i
      have hη0 : η 0=a.val.map ⟨l,⟨hl.le,by linarith⟩⟩ := by simpa using hη 0
      rw [hη0,←hmapK,htails _ (Or.inl le_rfl)]
      exact houter _ hl (by linarith) (Or.inl le_rfl) i)
    (by
      intro i
      have hη1 : η 1=a.val.map ⟨u,⟨by linarith,hu.le⟩⟩ := by
        rw [hη]; apply congrArg a.val.map; apply Subtype.ext; simp
      rw [hη1,←hmapK,htails _ (Or.inr le_rfl)]
      exact houter _ (by linarith) hu (Or.inr le_rfl) i) hseam
  have houter₁ : ∀ t : Interval,0 < (t:ℝ) → (t:ℝ) < 1 →
      (t:ℝ) ≤ l ∨ u ≤ (t:ℝ) → ∀ j,a₁.val.map t ∉ (old j).val.image := by
    intro t ht0 ht1 ht j
    rw [htails t ht]
    exact houter t ht0 ht1 ht j
  obtain ⟨α,β,F,hbounds,hFsub,hFdis,hFmarks,hFsq,hFends,hFcurve,hFslice,hFendsOff,houtside⟩ :=
    actual_trimmed_marked_crosscut_assembly M old a₁ l u hl hlu hu ν hνliteral hνinj n hn e hemarks
      (fun k t => (hν _).symm ▸ hpiece k t)
      (fun k j => by simpa only [hν] using hends k j) houter₁
  have hcentral (k : Fin n) :
      (a₁.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Icc (α k) (β k) ⊆ (F k).source := by
    rw [←hFslice k]
    exact fun z hz => hz.1.1
  obtain ⟨b,L,hclassL,himageL,hmarksL,houtL,hfinL⟩ :=
    actual_relative_finite_transverse_crosscut_redrawing M old a₁ e F label α β hbounds V
      (fun k => (hFsub k).trans (heV k)) hFsub hFdis hFmarks hFsq hcentral hFends hFcurve hFslice
      hlabel hFendsOff houtside
  have hmapImage : K.finalMap '' a.val.image=a₁.val.image := by
    change K.finalMap '' range a.val.map=range a₁.val.map
    rw [←range_comp]
    exact congrArg range (funext (fun t => (hmapK t).symm))
  refine ⟨b,K.compose L,hclassL.trans hclassK,?_,?_,?_,hfinL⟩
  · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hmapImage]
    exact himageL.symm
  · intro t x hx
    change L.map (t,K.map (t,x))=x
    rw [hmarksK t x hx,hmarksL t x hx]
  · intro t x hx
    change L.map (t,K.map (t,x))=x
    rw [houtK t x hx,houtL t x hx]

#print axioms actual_loop_capable_graph_relative_finite_position_from_actual_clear_collars_private
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
private theorem actual_graph_fixed_terminal_collars_consume_interior_preparation_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (a b c : EssentialMarkedArc M)
    (P : Set S) (hP : IsClosed P)
    (hbP : arcInterior M b ⊆ Pᶜ)
    (K : AmbientIsotopy S) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1/2)
    (hclass : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b)
    (hmarks : ∀ t x, x ∈ M.cover.branch → K.map (t,x) = x)
    (hgraph : ∀ t x, x ∈ P → K.map (t,x) = x)
    (hmap : ∀ t, c.val.map t = K.finalMap (b.val.map t))
    (htails : ∀ t : Interval, 0 < t.val → t.val < 1 →
      t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image) :
    ∃ d : EssentialMarkedArc M, ∃ H : AmbientIsotopy S,
      Quotient.mk (essentialArcSetoid M) d = Quotient.mk (essentialArcSetoid M) b ∧
      H.finalMap '' b.val.image = d.val.image ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ P → H.map (t,x) = x) ∧
      (ArcSurgery.crossings M a d).Finite ∧
      ∀ q ∈ ArcSurgery.crossings M a d, ArcSurgery.CrossesInDisk M a d q := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let V := ((M.cover.branch : Set S) ∪ P)ᶜ
  have hV : IsOpen V := (M.cover.branch.finite_toSet.isClosed.union hP).isOpen_compl
  obtain ⟨g,hg⟩ := K.homeomorphism_at (1:Interval)
  have hfinal : K.finalMap = g := funext (fun x => (hg x).symm)
  have hcV : arcInterior M c ⊆ V := by
    rintro x ⟨⟨t,rfl⟩,hxmark⟩
    change c.val.map t ∉ ((M.cover.branch : Set S) ∪ P)
    intro hxUnion
    rcases hxUnion with hxM|hxP
    · exact hxmark hxM
    have hxP := hxP
    have hbi : b.val.map t ∈ arcInterior M b := by
      refine ⟨mem_range_self t,?_⟩
      intro hm
      apply hxmark
      rw [hmap,hfinal]
      have hh : K.finalMap (b.val.map t) = b.val.map t := hmarks (1:Interval) (b.val.map t) hm
      rw [←hfinal,hh]
      exact hm
    have he : g (b.val.map t) = g (c.val.map t) := by
      rw [←hfinal,←hmap]
      exact (hgraph (1:Interval) (c.val.map t) hxP).symm
    exact hbP hbi (g.injective he ▸ hxP)
  obtain ⟨d,L,hclassL,himageL,hmarksL,houtL,hfinL⟩ :=
    actual_loop_capable_graph_relative_finite_position_from_actual_clear_collars_private
      M (fun _ : PUnit => a) (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
      c V hV hcV δ (1-δ) hδ (by linarith) (by linarith)
      (by intro t ht0 ht1 ht j; apply htails t ht0 ht1; rcases ht with ht|ht
          · exact Or.inl ht
          · exact Or.inr (by linarith))
  have himageK : K.finalMap '' b.val.image = c.val.image := by
    change K.finalMap '' range b.val.map = range c.val.map
    rw [←range_comp]
    exact congrArg range (funext (fun t => (hmap t).symm))
  refine ⟨d,K.compose L,hclassL.trans hclass,?_,?_,?_,?_,?_⟩
  · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,himageK]
    exact himageL
  · intro t x hx
    change L.map (t,K.map (t,x)) = x
    rw [hmarks t x hx,hmarksL t x hx]
  · intro t x hx
    change L.map (t,K.map (t,x)) = x
    rw [hgraph t x hx]
    apply houtL t x
    exact fun hv => hv (Or.inr hx)
  · exact (hfinL PUnit.unit).1.subset (fun x hx => ⟨hx.2,hx.1.1⟩)
  · intro q hq
    exact (hfinL PUnit.unit).2 q ⟨hq.2,hq.1.1⟩
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_graph_fixed_terminal_collars_consume_interior_preparation_private

private theorem actual_sector_source_motion_entire_literal_radial_graph_fixed_private
    {J K : Type} [Fintype K] (old : K → Plane) (v : J → Plane)
    (R : ℝ) (hR : 0 < R) (hv : ∀ j, ‖v j‖ = R)
    (Q : Set Plane) (hclosed : IsClosed Q) (hconv : Convex ℝ Q)
    (hne : (interior Q).Nonempty) (hinside : Q ⊆ closedBall (0:Plane) R)
    (hdisj : Disjoint (interior Q) (⋃ j, segment ℝ (0:Plane) (v j)))
    (h0front : (0:Plane) ∈ frontier Q)
    {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
    (ha : a ∉ Q) (c₀ : CurveComplex.Interval) (hc₀ : 0 < c₀)
    (hAArc : IsArcBetween (α '' Icc 0 c₀) 0 (α c₀))
    (hbfront : α c₀ ∈ frontier Q)
    (hAi : (α '' Icc 0 c₀) \ {0,α c₀} ⊆ interior Q) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ interior Q → H.map (t,x) = x) ∧
      (∀ t j (d : ℝ), 0 ≤ d → H.map (t,d • v j) = d • v j) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ H.finalMap '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          ∀ k, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • old k} = {0} := by
  obtain ⟨H,hH0,hHfix,hrest⟩ :=
    actual_old_avoiding_graph_sector_source_prefix_supported_motion_private old Q
      hclosed hconv hne (isBounded_closedBall.subset hinside) h0front
      α hα ha c₀ hc₀ hAArc hbfront hAi
  refine ⟨H,hH0,hHfix,?_,hrest⟩
  intro t j d hd
  apply hHfix
  intro hi
  by_cases hd1 : d ≤ 1
  · apply Set.disjoint_left.mp hdisj hi
    apply mem_iUnion.mpr
    refine ⟨j,?_⟩
    rw [segment_eq_image]
    refine ⟨d,⟨hd,hd1⟩,?_⟩
    simp
  · have hn := hinside (interior_subset hi)
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd,hv] at hn
    nlinarith [hR]
#print axioms actual_sector_source_motion_entire_literal_radial_graph_fixed_private

/- Actual convex-cell subdivision for a stationary finite radial fan.
Extracts canonical first-exit/sector-split geometry; no homeomorphism moves the fan. -/
open Set Metric Schoenflies CurveComplex Bornology
set_option maxHeartbeats 2600000
set_option linter.unnecessarySimpa false
namespace CurveComplex.FiniteStarGeometry

private theorem firstExit {J K : Type} (Q : K → Set Plane) (v : J → Plane)
    (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0:Plane) ∈ Q k)
    (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
    (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ ⋃ j, segment ℝ (0:Plane) (v j))
    (hv : ∀ j, ‖v j‖ = R)
    {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
    (ha : a ∉ closedBall (0:Plane) R)
    (havoid : ∀ t : I, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
    ∃ (c : I) (k : K), 0 < c.val ∧ c.val < 1 ∧
      ‖α c‖ = R ∧ α c ∈ frontier (Q k) ∧
      IsArcBetween (α '' Icc 0 c) 0 (α c) ∧
      (α '' Icc 0 c) \ {0,α c} ⊆ interior (Q k) ∧
      segment ℝ (0:Plane) (α c) \ {0,α c} ⊆ interior (Q k) := by
  classical
  have select (U : K → Set Plane) (hU : ∀ k, IsOpen (U k))
      (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
      (c t₀ : I) (ht₀ : t₀ ∈ Ioo zeroI c)
      (hc : ∀ t ∈ Ioo zeroI c, α t ∈ ⋃ k, U k) :
      ∃ k, ∀ t ∈ Ioo zeroI c, α t ∈ U k := by
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hc t₀ ht₀)
    let W := ⋃ (j : K) (_ : j ≠ k), U j
    have hW : IsOpen W := isOpen_iUnion (fun j => isOpen_iUnion (fun _ => hU j))
    have hdW : Disjoint (U k) W := by
      apply Set.disjoint_left.mpr
      intro x hx hxW
      obtain ⟨j,hj⟩ := mem_iUnion.mp hxW
      obtain ⟨hne,hxj⟩ := mem_iUnion.mp hj
      exact Set.disjoint_left.mp (hd hne.symm) hx hxj
    have hp : α '' Ioo zeroI c ⊆ U k ∪ W := by
      rintro x ⟨t,ht,rfl⟩
      obtain ⟨j,hj⟩ := mem_iUnion.mp (hc t ht)
      by_cases he : j = k
      · exact Or.inl (he ▸ hj)
      · exact Or.inr (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨he,hj⟩⟩)
    have hsel : α '' Ioo zeroI c ⊆ U k :=
      (isPreconnected_Ioo.image α α.continuous.continuousOn).subset_left_of_subset_union
        (hU k) hW hdW hp ⟨α t₀,⟨⟨t₀,ht₀,rfl⟩,hk⟩⟩
    exact ⟨k,fun t ht => hsel ⟨t,ht,rfl⟩⟩
  have nonsphere {x : Plane} (hb : x ∈ ball (0:Plane) R) : x ∉ sphere (0:Plane) R := by
    simp only [mem_ball,mem_sphere,dist_zero_right] at *
    exact ne_of_lt hb
  have haopen : a ∉ ball (0:Plane) R := fun hm => ha (ball_subset_closedBall hm)
  obtain ⟨c,hc,γ,hex,hγ,himage,hbefore⟩ :=
    CurveComplex.SeedProbeHeaders.embedded_first_exit_prefix α hα
      (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
  have heR : ‖α c‖ = R := by
    rw [frontier_ball (0:Plane) (ne_of_gt hR)] at hex
    simpa only [mem_sphere,dist_zero_right] using hex
  have hc1 : c < 1 := by
    apply lt_of_le_of_ne c.property.2
    intro he
    apply ha
    rw [show c = 1 from Subtype.ext he] at heR
    simpa only [α.target,mem_closedBall,dist_zero_right] using heR.le
  have hrawbefore : ∀ t : I, t < c → α t ∈ ball (0:Plane) R := by
    obtain ⟨d,hd,hdf,hdb⟩ := CurveComplex.path_first_exit_frontier α
      (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
    have hdle : d ≤ c := by
      by_contra hn
      have hm := hdb c (lt_of_not_ge hn)
      exact (show α c ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hex.2) hm
    have hcd : c ≤ d := by
      by_contra hn
      have hdγ : α d ∈ range γ := by
        rw [himage]
        exact ⟨d,⟨d.property.1,(lt_of_not_ge hn).le⟩,rfl⟩
      obtain ⟨s,hs⟩ := hdγ
      have hs1 : s < 1 := by
        apply lt_of_le_of_ne s.property.2
        intro he
        have hsone : s = 1 := Subtype.ext he
        have hdc : d = c := hα (hs.symm.trans (hsone ▸ γ.target))
        exact (ne_of_lt (lt_of_not_ge hn)) hdc
      have hm := hbefore s hs1
      rw [hs] at hm
      exact (show α d ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hdf.2) hm
    exact fun t ht => hdb t (ht.trans_le hcd)
  have hcellcover : ∀ t ∈ Ioo zeroI c, α t ∈ ⋃ k, interior (Q k) := by
    intro t ht
    have hb := hrawbefore t ht.2
    obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover (ball_subset_closedBall hb))
    refine mem_iUnion.mpr ⟨k,?_⟩
    by_contra hn
    have hfr : α t ∈ frontier (Q k) := by
      rw [(hclosed k).frontier_eq]
      exact ⟨hk,hn⟩
    rcases hfront k hfr with hs | hf
    · exact (nonsphere hb) hs
    · exact havoid t ht.1 hf
  let t₀ : I := ⟨c.val/2,by constructor <;> nlinarith [c.property.1,c.property.2]⟩
  have ht₀ : t₀ ∈ Ioo zeroI c := by
    have hcr : 0 < c.val := hc
    constructor
    · change 0 < c.val/2
      linarith
    · change c.val/2 < c.val
      linarith
  obtain ⟨k,hk⟩ := select (fun k => interior (Q k)) (fun _ => isOpen_interior)
    hdisj c t₀ ht₀ hcellcover
  have heQ : α c ∈ Q k := by
    have hcc : c ∈ closure (Ioo zeroI c : Set I) := by
      rw [closure_Ioo (show zeroI ≠ c from ne_of_lt hc)]
      exact ⟨hc.le,le_rfl⟩
    have hsub : Ioo zeroI c ⊆ α ⁻¹' Q k := by
      intro t ht
      change α t ∈ Q k
      exact interior_subset (hk t ht)
    exact ((hclosed k).preimage α.continuous).closure_subset_iff.mpr hsub hcc
  have hefront : α c ∈ frontier (Q k) := by
    rw [(hclosed k).frontier_eq]
    refine ⟨heQ,?_⟩
    intro hm
    have hb : α c ∈ interior (closedBall (0:Plane) R) := interior_mono (hinside k) hm
    rw [interior_closedBall (0:Plane) (ne_of_gt hR)] at hb
    exact (nonsphere hb) (by simpa only [mem_sphere,dist_zero_right] using heR)
  have hArc : IsArcBetween (α '' Icc 0 c) 0 (α c) := by
    refine ⟨γ.extend,γ.continuous_extend.continuousOn,?_,?_,γ.extend_zero,γ.extend_one⟩
    · intro s hs t ht he
      rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
      exact congrArg Subtype.val (hγ he)
    · exact (γ.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans himage
  refine ⟨c,k,hc,hc1,heR,hefront,hArc,?_,?_⟩
  · rintro x ⟨⟨t,ht,rfl⟩,hne⟩
    have ht0 : zeroI < t := by
      apply lt_of_le_of_ne t.property.1
      intro he
      have he0 : t = 0 := Subtype.ext he.symm
      exact hne (by simp [he0,α.source])
    have htc : t < c := by
      apply lt_of_le_of_ne ht.2
      intro he
      exact hne (by simp [he])
    exact hk t ⟨ht0,htc⟩
  · intro x hx
    have hxQ : x ∈ Q k := (hconvex k).segment_subset (hzero k) heQ hx.1
    have hxne0 : x ≠ 0 := by intro he; exact hx.2 (by simp [he])
    have hxnee : x ≠ α c := by intro he; exact hx.2 (by simp [he])
    have hxo : x ∈ openSegment ℝ (0:Plane) (α c) :=
      mem_openSegment_of_ne_left_right hxne0.symm hxnee.symm hx.1
    obtain ⟨a,b,ha,hb,hab,hxb⟩ := hxo
    have hxb' : x = b • α c := by simpa using hxb.symm
    have hxball : x ∈ ball (0:Plane) R := by
      rw [mem_ball,dist_zero_right,hxb',norm_smul,Real.norm_eq_abs,abs_of_pos hb,heR]
      have hb1 : b < 1 := by linarith
      nlinarith
    by_contra hn
    have hxfr : x ∈ frontier (Q k) := by
      rw [(hclosed k).frontier_eq]
      exact ⟨hxQ,hn⟩
    rcases hfront k hxfr with hs | hf
    · exact (nonsphere hxball) hs
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hf
      have hejne : α c ≠ v j := by
        intro he
        apply havoid c hc
        exact mem_iUnion.mpr ⟨j,he ▸ right_mem_segment ℝ 0 (v j)⟩
      have hmeet := LeanEval.Topology.ClassificationOfSurfaces.Moise.radial_segments_inter
        (center := (0:Plane)) (p := α c) (q := v j) (radius := R) hR
        (by simpa only [dist_zero_right] using heR)
        (by simpa only [dist_zero_right] using hv j) hejne
      have hxzero : x ∈ ({0} : Set Plane) := hmeet ▸ ⟨hx.1,hj⟩
      exact hxne0 hxzero
private theorem insertCells {K : Type} (Q : K → Set Plane) (F : Set Plane)
    (R : ℝ) (hR : 0 < R)
    (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
    (hzero : ∀ k, (0:Plane) ∈ Q k) (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
    (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
    (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
    (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ F)
    (hcellne : ∀ k, (interior (Q k)).Nonempty)
    (hcenter : ∀ k, (0:Plane) ∈ frontier (Q k))
    (hfan : ∀ k, Disjoint (interior (Q k)) F)
    (hsupport : ∀ k, ∃ L : Plane →L[ℝ] ℝ,
      (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ F))
    (k₀ : K) (e : Plane) (heQ : e ∈ Q k₀) (heR : ‖e‖ = R) (heF : e ∉ F)
    (hproper : segment ℝ (0:Plane) e \ {0,e} ⊆ interior (Q k₀)) :
    ∃ (K' : Type) (Q' : K' → Set Plane),
      (∀ k, IsClosed (Q' k)) ∧ (∀ k, Convex ℝ (Q' k)) ∧
      (∀ k, (0:Plane) ∈ Q' k) ∧ (∀ k, Q' k ⊆ closedBall (0:Plane) R) ∧
      (closedBall (0:Plane) R ⊆ ⋃ k, Q' k) ∧
      (Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l)))) ∧
      (∀ k, frontier (Q' k) ⊆ sphere (0:Plane) R ∪ (F ∪ segment ℝ (0:Plane) e)) ∧
      (∀ k, (interior (Q' k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q' k)) ∧
      (∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e)) ∧
      (∀ k, ∃ L : Plane →L[ℝ] ℝ,
        (∀ x ∈ Q' k, 0 ≤ L x) ∧
        (∀ x ∈ Q' k, L x = 0 → x ∈ F ∪ segment ℝ (0:Plane) e)) := by
  classical
  have halfInt (e : Plane) (he : e ≠ 0) :
      interior {x : Plane | 0 ≤ Plane.det e x} = {x | 0 < Plane.det e x} ∧
      interior {x : Plane | Plane.det e x ≤ 0} = {x | Plane.det e x < 0} := by
    let D : Plane →ₗ[ℝ] ℝ := {
      toFun := fun x => Plane.det e x
      map_add' := Plane.det_add_right e
      map_smul' := fun r x => Plane.det_smul_right r e x }
    have hcont : Continuous D := by
      change Continuous (fun x : Plane => Plane.det e x)
      unfold Plane.det
      exact (continuous_const.mul (Plane.continuous_coord 1)).sub
        (continuous_const.mul (Plane.continuous_coord 0))
    have hnorm : ‖e‖^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr he))
    have hsurj : Function.Surjective D := by
      intro r
      refine ⟨(r / ‖e‖^2) • Plane.perp e,?_⟩
      change Plane.det e ((r / ‖e‖^2) • Plane.perp e) = r
      rw [Plane.det_smul_right,Plane.det_perp_self]
      exact div_mul_cancel₀ r hnorm
    have hopen : IsOpenMap D := D.isOpenMap_of_finiteDimensional hsurj
    constructor
    · change interior (D ⁻¹' Ici (0:ℝ)) = D ⁻¹' Ioi (0:ℝ)
      rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Ici]
    · change interior (D ⁻¹' Iic (0:ℝ)) = D ⁻¹' Iio (0:ℝ)
      rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Iic]
  have hen : e ≠ 0 := by intro he; simp [he] at heR; linarith
  obtain ⟨L,hL,hker⟩ := hsupport k₀
  have heL : 0 < L e := lt_of_le_of_ne (hL e heQ) (fun hz => heF (hker e heQ hz.symm))
  let A := Q k₀ ∩ {x | 0 ≤ Plane.det e x}
  let B := Q k₀ ∩ {x | Plane.det e x ≤ 0}
  obtain ⟨hab,hinter,hca,hcb⟩ := radial_sector_determinant_split
    (Q k₀) (hconvex k₀) R hR (hinside k₀) (hzero k₀) e heQ heR L hL heL
  have hcont : Continuous (fun x : Plane => Plane.det e x) := by
    unfold Plane.det
    exact (continuous_const.mul (Plane.continuous_coord 1)).sub
      (continuous_const.mul (Plane.continuous_coord 0))
  have haClosed : IsClosed A := (hclosed k₀).inter (isClosed_le continuous_const hcont)
  have hbClosed : IsClosed B := (hclosed k₀).inter (isClosed_le hcont continuous_const)
  obtain ⟨hfa,hfb,hdab⟩ := sector_split_frontier_invariant (Q k₀) (hclosed k₀) e hen hinter
  have hhalf : (1/2:ℝ) • e ∈ segment ℝ (0:Plane) e \ {0,e} := by
    refine ⟨⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by simp⟩,?_⟩
    intro hh
    have hh' : (1/2:ℝ) • e = 0 ∨ (1/2:ℝ) • e = e := by simpa using hh
    rcases hh' with hh|hh
    · exact hen ((smul_eq_zero.mp hh).resolve_left (by norm_num))
    · have hz : (-1/2:ℝ) • e = 0 := by calc
        (-1/2:ℝ) • e = (1/2:ℝ) • e - e := by module
        _ = 0 := by rw [hh,sub_self]
      exact hen ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  obtain ⟨hneA,hneB⟩ := sector_split_interiors_nonempty (Q k₀) ((1/2:ℝ) • e) e
    (hproper hhalf) hen (by simp)
  let K' := Sum {k : K // k ≠ k₀} Bool
  let Q' : K' → Set Plane := Sum.elim (fun k => Q k.val) (fun b => if b then B else A)
  have hnewclosed : ∀ k, IsClosed (Q' k) := by
    intro k
    cases k with
    | inl k => exact hclosed k.val
    | inr b => cases b; exact haClosed; exact hbClosed
  have hmona : interior A ⊆ interior (Q k₀) := interior_mono inter_subset_left
  have hmonb : interior B ⊆ interior (Q k₀) := interior_mono inter_subset_left
  have hnewzero : ∀ k, (0:Plane) ∈ Q' k := by
    intro k
    cases k with
    | inl k => exact hzero k.val
    | inr b => cases b <;> exact ⟨hzero k₀,by simp [Plane.det]⟩
  have newSubsetOld : ∀ k : K', ∃ j : K, Q' k ⊆ Q j := by
    intro k
    cases k with
    | inl k => exact ⟨k.val,Subset.refl _⟩
    | inr b => cases b <;> exact ⟨k₀,inter_subset_left⟩
  have hnewinside : ∀ k, Q' k ⊆ closedBall (0:Plane) R := by
    intro k
    obtain ⟨j,hj⟩ := newSubsetOld k
    exact hj.trans (hinside j)
  have hnewcenter : ∀ k, (0:Plane) ∈ frontier (Q' k) := by
    intro k
    rw [(hnewclosed k).frontier_eq]
    refine ⟨hnewzero k,?_⟩
    intro hi
    obtain ⟨j,hj⟩ := newSubsetOld k
    have hj0 : (0:Plane) ∉ interior (Q j) := by
      have hh : (0:Plane) ∈ Q j \ interior (Q j) := (hclosed j).frontier_eq ▸ hcenter j
      exact hh.2
    exact hj0 (interior_mono hj hi)
  have hnewdisj : Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l))) := by
    intro k l hkl
    cases k with
    | inl k =>
      cases l with
      | inl l => exact hdisj (fun he => hkl (congrArg Sum.inl (Subtype.ext he)))
      | inr b => cases b; exact (hdisj k.property).mono_right hmona; exact (hdisj k.property).mono_right hmonb
    | inr b =>
      cases l with
      | inl l => cases b; exact (hdisj l.property.symm).mono_left hmona; exact (hdisj l.property.symm).mono_left hmonb
      | inr c => cases b <;> cases c
                 · exact False.elim (hkl rfl)
                 · exact hdab
                 · exact hdab.symm
                 · exact False.elim (hkl rfl)
  have hnewfan : ∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e) := by
    intro k
    apply Set.disjoint_left.mpr
    intro x hi hx
    obtain ⟨j,hj⟩ := newSubsetOld k
    rcases hx with hf|hr
    · exact Set.disjoint_left.mp (hfan j) (interior_mono hj hi) hf
    · have hd : Plane.det e x = 0 := by
        obtain ⟨a,b,ha,hb,hab,hx⟩ := hr
        rw [← hx]
        simp
      cases k with
      | inl k =>
        by_cases hx0 : x = 0
        · have hh : x ∈ frontier (Q' (.inl k)) := hx0.symm ▸ hnewcenter (.inl k)
          have hh' : x ∈ Q' (.inl k) \ interior (Q' (.inl k)) := (hnewclosed _).frontier_eq ▸ hh
          exact hh'.2 hi
        by_cases hxe : x = e
        · have hb : e ∈ ball (0:Plane) R := by
            have hh := interior_mono (hinside k.val) (show x ∈ interior (Q k.val) from hi)
            rw [interior_closedBall (0:Plane) (ne_of_gt hR),hxe] at hh
            exact hh
          have hh : ‖e‖ < R := by simpa only [mem_ball,dist_zero_right] using hb
          exact (ne_of_lt hh) heR
        have hip : x ∈ interior (Q k₀) := hproper ⟨hr,by simpa using And.intro hx0 hxe⟩
        exact Set.disjoint_left.mp (hdisj k.property) hi hip
      | inr b =>
        cases b
        · have hp := interior_mono (show A ⊆ {x | 0 ≤ Plane.det e x} from inter_subset_right) hi
          rw [(halfInt e hen).1] at hp
          exact (ne_of_gt (show 0 < Plane.det e x from hp)) hd
        · have hn := interior_mono (show B ⊆ {x | Plane.det e x ≤ 0} from inter_subset_right) hi
          rw [(halfInt e hen).2] at hn
          exact (ne_of_lt (show Plane.det e x < 0 from hn)) hd
  refine ⟨K',Q',hnewclosed,?_,hnewzero,hnewinside,?_,hnewdisj,?_,?_,hnewcenter,hnewfan,?_⟩
  · intro k
    cases k with
    | inl k => exact hconvex k.val
    | inr b => cases b; exact hca; exact hcb
  · intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hx)
    by_cases hje : j = k₀
    · subst j
      have hxAB : x ∈ A ∪ B := hab.symm ▸ hj
      rcases hxAB with hxA|hxB
      · exact mem_iUnion.mpr ⟨.inr false,hxA⟩
      · exact mem_iUnion.mpr ⟨.inr true,hxB⟩
    · exact mem_iUnion.mpr ⟨.inl ⟨j,hje⟩,hj⟩
  · intro k x hx
    cases k with
    | inl k =>
      rcases hfront k.val hx with hs|hf
      · exact Or.inl hs
      · exact Or.inr (Or.inl hf)
    | inr b =>
      have hh : x ∈ frontier (Q k₀) ∪ segment ℝ (0:Plane) e := by
        cases b; exact hfa hx; exact hfb hx
      rcases hh with hfr|hr
      · rcases hfront k₀ hfr with hs|hf
        · exact Or.inl hs
        · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr hr)
  · intro k
    cases k with
    | inl k => exact hcellne k.val
    | inr b => cases b; exact hneA; exact hneB
  · intro k
    obtain ⟨j,hj⟩ := newSubsetOld k
    obtain ⟨Lj,hLj,hkj⟩ := hsupport j
    exact ⟨Lj,fun x hx => hLj x (hj hx),fun x hx he => Or.inl (hkj x (hj hx) he)⟩
private theorem halfCells (v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ = R) :
    ∃ Q : Bool → Set Plane,
      (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
      (∀ k, (0:Plane) ∈ Q k) ∧ (∀ k, Q k ⊆ closedBall (0:Plane) R) ∧
      (closedBall (0:Plane) R ⊆ ⋃ k, Q k) ∧
      (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
      (∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪
        (segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) ∧
      (∀ k, (interior (Q k)).Nonempty) ∧
      (∀ k, (0:Plane) ∈ frontier (Q k)) ∧
      (∀ k, Disjoint (interior (Q k))
        (segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) ∧
      (∀ k, ∃ L : Plane →L[ℝ] ℝ,
        (∀ x ∈ Q k, 0 ≤ L x) ∧
        (∀ x ∈ Q k, L x = 0 → x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) := by
  have hvne : v ≠ 0 := by intro he; simp [he] at hv; linarith
  let D : Plane →ₗ[ℝ] ℝ := {
    toFun := fun x => Plane.det v x
    map_add' := Plane.det_add_right v
    map_smul' := fun r x => Plane.det_smul_right r v x }
  let L : Bool → Plane →L[ℝ] ℝ := fun b => if b then -D.toContinuousLinearMap else D.toContinuousLinearMap
  let Q : Bool → Set Plane := fun b => closedBall (0:Plane) R ∩ {x | 0 ≤ L b x}
  have hclosed : ∀ b, IsClosed (Q b) := fun b =>
    isClosed_closedBall.inter (isClosed_le continuous_const (L b).continuous)
  have hconvex : ∀ b, Convex ℝ (Q b) := by
    intro b
    apply (convex_closedBall (0:Plane) R).inter
    intro x hx y hy a b ha hb hab
    change 0 ≤ L _ (a • x + b • y)
    simp only [map_add,map_smul,smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hzero : ∀ b, (0:Plane) ∈ Q b := by
    intro b
    exact ⟨by simpa using hR.le,by simp⟩
  have hinside : ∀ b, Q b ⊆ closedBall (0:Plane) R := fun _ => inter_subset_left
  have hlinearInt : ∀ b, interior {x | 0 ≤ L b x} = {x | 0 < L b x} := by
    intro b
    have hsurj : Function.Surjective (L b) := by
      intro r
      cases b
      · refine ⟨(r / ‖v‖^2) • Plane.perp v,?_⟩
        change Plane.det v ((r / ‖v‖^2) • Plane.perp v) = r
        rw [Plane.det_smul_right,Plane.det_perp_self]
        exact div_mul_cancel₀ r (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hvne)))
      · refine ⟨(-r / ‖v‖^2) • Plane.perp v,?_⟩
        change -Plane.det v ((-r / ‖v‖^2) • Plane.perp v) = r
        rw [Plane.det_smul_right,Plane.det_perp_self,div_mul_cancel₀ _
          (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hvne))),neg_neg]
    have hopen := (L b).toLinearMap.isOpenMap_of_finiteDimensional hsurj
    change IsOpenMap (L b) at hopen
    change interior ((L b) ⁻¹' Ici (0:ℝ)) = (L b) ⁻¹' Ioi (0:ℝ)
    rw [← hopen.preimage_interior_eq_interior_preimage (L b).continuous,interior_Ici]
  have hInt : ∀ b, interior (Q b) = ball (0:Plane) R ∩ {x | 0 < L b x} := by
    intro b
    rw [interior_inter,interior_closedBall (0:Plane) (ne_of_gt hR),hlinearInt]
  have kernelFan {x : Plane} (hx : x ∈ closedBall (0:Plane) R)
      (hdet : Plane.det v x = 0) : x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v) := by
    obtain ⟨r,hr⟩ := (Plane.det_eq_zero_iff_smul v x hvne).mp hdet
    have hnr : |r| ≤ 1 := by
      have hh : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
      rw [hr,norm_smul,Real.norm_eq_abs,hv] at hh
      nlinarith
    rcases le_total 0 r with hp|hn
    · apply Or.inl
      rw [hr]
      have hr1 : r ≤ 1 := le_trans (le_abs_self r) hnr
      exact ⟨1-r,r,sub_nonneg.mpr hr1,hp,by ring,by simp⟩
    · apply Or.inr
      have hr1 : -r ≤ 1 := le_trans (neg_le_abs r) hnr
      have hxneg : x = (-r) • (-v) := by rw [hr]; module
      rw [hxneg]
      exact ⟨1-(-r),-r,sub_nonneg.mpr hr1,neg_nonneg.mpr hn,by ring,by simp⟩
  have hker : ∀ b x, L b x = 0 → Plane.det v x = 0 := by
    intro b x hx
    cases b
    · exact hx
    · change -Plane.det v x = 0 at hx
      exact neg_eq_zero.mp hx
  have hfanD : ∀ x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v), Plane.det v x = 0 := by
    intro x hx
    rcases hx with hx|hx <;> obtain ⟨a,b,ha,hb,hab,hx⟩ := hx <;> rw [← hx] <;> simp [Plane.det] <;> ring
  refine ⟨Q,hclosed,hconvex,hzero,hinside,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    rcases le_total 0 (Plane.det v x) with hp|hn
    · exact mem_iUnion.mpr ⟨false,hx,hp⟩
    · exact mem_iUnion.mpr ⟨true,hx,by change 0 ≤ -Plane.det v x; linarith⟩
  · intro b c hbc
    apply Set.disjoint_left.mpr
    intro x hxb hxc
    rw [hInt b] at hxb
    rw [hInt c] at hxc
    cases b <;> cases c
    · exact hbc rfl
    · have hp : 0 < Plane.det v x := hxb.2
      have hn : 0 < -Plane.det v x := hxc.2
      linarith
    · have hn : 0 < -Plane.det v x := hxb.2
      have hp : 0 < Plane.det v x := hxc.2
      linarith
    · exact hbc rfl
  · intro b x hx
    rcases frontier_inter_subset (closedBall (0:Plane) R) {x | 0 ≤ L b x} hx with hball|hline
    · exact Or.inl ((frontier_closedBall (0:Plane) (ne_of_gt hR)) ▸ hball.1)
    · apply Or.inr
      have hxQ : x ∈ Q b := (hclosed b).closure_eq ▸ frontier_subset_closure hx
      exact kernelFan hxQ.1 (hker b x (frontier_le_subset_eq continuous_const (L b).continuous hline.2).symm)
  · intro b
    cases b
    · refine ⟨(1/2:ℝ) • Plane.perp v,?_⟩
      rw [hInt]
      constructor
      · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),Plane.norm_perp,hv]
        linarith
      · change 0 < Plane.det v ((1/2:ℝ) • Plane.perp v)
        rw [Plane.det_smul_right,Plane.det_perp_self]
        exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hvne))
    · refine ⟨(-1/2:ℝ) • Plane.perp v,?_⟩
      rw [hInt]
      constructor
      · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_neg (by norm_num : (-1/2:ℝ)<0),Plane.norm_perp,hv]
        linarith
      · change 0 < -Plane.det v ((-1/2:ℝ) • Plane.perp v)
        rw [Plane.det_smul_right,Plane.det_perp_self]
        nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hvne)]
  · intro b
    rw [(hclosed b).frontier_eq]
    refine ⟨hzero b,?_⟩
    rw [hInt b]
    rintro ⟨_,hh⟩
    simpa using hh
  · intro b
    apply Set.disjoint_left.mpr
    intro x hx hf
    rw [hInt b] at hx
    have hd := hfanD x hf
    cases b
    · have hp : 0 < Plane.det v x := hx.2
      linarith
    · have hn : 0 < -Plane.det v x := hx.2
      linarith
  · intro b
    refine ⟨L b,fun x hx => hx.2,?_⟩
    intro x hx hd
    exact kernelFan hx.1 (hker b x hd)


private theorem stationaryOppositeFanCells {J : Type} [Fintype J]
    (v : J → Plane) (R : ℝ) (hR : 0 < R) (hv : ∀ j, ‖v j‖ = R)
    (hinj : Function.Injective v) (j₀ j₁ : J) (hopposite : v j₁ = -v j₀) :
    let Cells : Finset J → Prop := fun S =>
      ∃ (K : Type) (Q : K → Set Plane),
          (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
          (∀ k, (0:Plane) ∈ Q k) ∧ (∀ k, Q k ⊆ closedBall (0:Plane) R) ∧
          (closedBall (0:Plane) R ⊆ ⋃ k, Q k) ∧
          (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
          (∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ (⋃ j, ⋃ (_ : j ∈ S), segment ℝ (0:Plane) (v j))) ∧
          (∀ k, (interior (Q k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q k)) ∧
          (∀ k, Disjoint (interior (Q k)) ((⋃ j, ⋃ (_ : j ∈ S), segment ℝ (0:Plane) (v j)))) ∧
          (∀ k, ∃ L : Plane →L[ℝ] ℝ,
            (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ (⋃ j, ⋃ (_ : j ∈ S), segment ℝ (0:Plane) (v j))))
    Cells Finset.univ := by
  classical
  intro Cells
  let fan : Finset J → Set Plane := fun S => ⋃ j, ⋃ (_ : j ∈ S), segment ℝ (0:Plane) (v j)
  let S₀ : Finset J := {j₀,j₁}
  have hfan₀ : fan S₀ = segment ℝ (0:Plane) (v j₀) ∪ segment ℝ (0:Plane) (-v j₀) := by
    simp [fan,S₀,hopposite]
  have hbase : Cells S₀ := by
    obtain ⟨Q,hcl,hcv,hz,hi,hco,hd,hfr,hne,hce,hf,hs⟩ := halfCells (v j₀) R hR (hv j₀)
    refine ⟨Bool,Q,hcl,hcv,hz,hi,hco,hd,?_,hne,hce,?_,?_⟩
    · change ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ fan S₀
      simpa only [hfan₀] using hfr
    · change ∀ k, Disjoint (interior (Q k)) (fan S₀)
      simpa only [hfan₀] using hf
    · change ∀ k, ∃ L : Plane →L[ℝ] ℝ,
        (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x=0 → x ∈ fan S₀)
      simpa only [hfan₀] using hs
  have hstep (S : Finset J) (hS : Cells S) (j : J) (hj : j ∉ S) : Cells (insert j S) := by
    obtain ⟨K,Q,hcl,hcv,hz,hi,hco,hd,hfr,hne,hce,hf,hs⟩ := hS
    have hvne : v j ≠ 0 := by intro he; have hh := hv j; simp [he] at hh; linarith
    let α : Path (0:Plane) ((2:ℝ) • v j) := {
      toFun := fun t => (2*t.val) • v j
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
    have hα : Function.Injective α := by
      intro s t he
      have hh : (2*s.val) = (2*t.val) := (smul_left_injective ℝ hvne) he
      apply Subtype.ext
      linarith
    have ha : (2:ℝ) • v j ∉ closedBall (0:Plane) R := by
      simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2),hv j]
      linarith
    have hav : ∀ t : I, 0 < t.val → α t ∉ fan S := by
      intro t ht hm
      obtain ⟨i,hm⟩ := mem_iUnion.mp hm
      obtain ⟨hi,hm⟩ := mem_iUnion.mp hm
      obtain ⟨a,b,ha,hb,hab,he⟩ := hm
      have he' : b • v i = (2*t.val) • v j := by simpa [α] using he
      have hn := congrArg norm he'
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hb,
        abs_of_nonneg (by positivity : 0 ≤ 2*t.val),hv i,hv j] at hn
      have hb' : b = 2*t.val := by nlinarith
      have hvi : v i = v j := (smul_right_injective _ (by positivity : (2*t.val:ℝ) ≠ 0)) (hb' ▸ he')
      exact hj (hinj hvi ▸ hi)
    have hfanSubtype : fan S = ⋃ i : {i : J // i ∈ S}, segment ℝ (0:Plane) (v i.val) := by
      ext x
      simp [fan]
    obtain ⟨c,k,hc,hc1,hcR,hcf,hArc,hAi,hBi⟩ := firstExit Q
      (fun i : {i : J // i ∈ S} => v i.val) R hR hcl hcv hz hi hco hd
      (by simpa only [← hfanSubtype] using hfr) (fun i => hv i.val) α hα ha
      (by simpa only [← hfanSubtype] using hav)
    have hc2 : 2*c.val=1 := by
      change ‖(2*c.val) • v j‖=R at hcR
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),hv j] at hcR
      nlinarith
    have he : α c = v j := by change (2*c.val) • v j=v j; rw [hc2,one_smul]
    have heQ : v j ∈ Q k := he ▸ ((hcl k).closure_eq ▸ frontier_subset_closure hcf)
    have heF : v j ∉ fan S := he ▸ hav c hc
    obtain ⟨K',Q',hcl',hcv',hz',hi',hco',hd',hfr',hne',hce',hf',hs'⟩ :=
      insertCells Q (fan S) R hR hcl hcv hz hi hco hd hfr hne hce hf hs
        k (v j) heQ (hv j) heF (by simpa only [he] using hBi)
    have hfe : fan (insert j S) = fan S ∪ segment ℝ (0:Plane) (v j) := by
      ext x
      simp [fan,or_comm]
    refine ⟨K',Q',hcl',hcv',hz',hi',hco',hd',?_,hne',hce',?_,?_⟩
    · change ∀ k, frontier (Q' k) ⊆ sphere (0:Plane) R ∪ fan (insert j S)
      simpa only [hfe] using hfr'
    · change ∀ k, Disjoint (interior (Q' k)) (fan (insert j S))
      simpa only [hfe] using hf'
    · change ∀ k, ∃ L : Plane →L[ℝ] ℝ,
        (∀ x ∈ Q' k, 0 ≤ L x) ∧ (∀ x ∈ Q' k, L x=0 → x ∈ fan (insert j S))
      simpa only [hfe] using hs'
  have finish (T : Finset J) : Cells (S₀ ∪ T) := by
    induction T using Finset.induction_on with
    | empty => simpa using hbase
    | @insert j T hj ih =>
      by_cases hjS : j ∈ S₀ ∪ T
      · have he : S₀ ∪ insert j T = S₀ ∪ T := by ext i; simp only [Finset.mem_union,Finset.mem_insert]; grind
        exact he.symm ▸ ih
      · have he : S₀ ∪ insert j T = insert j (S₀ ∪ T) := by ext i; simp only [Finset.mem_union,Finset.mem_insert]; tauto
        exact he.symm ▸ hstep (S₀ ∪ T) ih j hjS
  have he : S₀ ∪ Finset.univ = Finset.univ := by ext i; simp
  exact he ▸ finish Finset.univ



end CurveComplex.FiniteStarGeometry

open Set Metric Schoenflies

/-- Finite equal-radius rays, including an opposite pair, admit convex radial
cells whose boundaries use the original rays. -/
theorem actual_finite_radial_fan_cells_private {J : Type} [Fintype J]
    (v : J → Schoenflies.Plane) (R : ℝ) (hR : 0 < R)
    (hnorm : ∀ j, ‖v j‖ = R)
    (hmeet : ∀ i j, i ≠ j →
      segment ℝ (0 : Schoenflies.Plane) (v i) ∩
        segment ℝ (0 : Schoenflies.Plane) (v j) = {0})
    (i0 i1 : J) (hne : i0 ≠ i1) (hopp : v i1 = -v i0) :
    ∃ (K : Type) (Q : K → Set Schoenflies.Plane),
      (∀ k, IsClosed (Q k)) ∧
      (∀ k, Convex ℝ (Q k)) ∧
      (∀ k, (0 : Schoenflies.Plane) ∈ Q k) ∧
      (∀ k, Q k ⊆ Metric.closedBall (0 : Schoenflies.Plane) R) ∧
      (Metric.closedBall (0 : Schoenflies.Plane) R ⊆ ⋃ k, Q k) ∧
      (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
      (∀ k, frontier (Q k) ⊆ Metric.sphere (0 : Schoenflies.Plane) R ∪
        ⋃ j, segment ℝ (0 : Schoenflies.Plane) (v j)) ∧
      (∀ k, (interior (Q k)).Nonempty) ∧
      (∀ k, (0 : Schoenflies.Plane) ∈ frontier (Q k)) ∧
      (∀ k, Disjoint (interior (Q k))
        (⋃ j, segment ℝ (0 : Schoenflies.Plane) (v j))) ∧
      (∀ k, ∃ L : Schoenflies.Plane →L[ℝ] ℝ,
        (∀ x ∈ Q k, 0 ≤ L x) ∧
        (∀ x ∈ Q k, L x = 0 →
          x ∈ ⋃ j, segment ℝ (0 : Schoenflies.Plane) (v j))) := by
  classical
  have hinj : Function.Injective v := by
    intro i j he
    by_contra hij
    have hvzero : v i ∈ ({0} : Set Schoenflies.Plane) := by
      rw [← hmeet i j hij]
      exact ⟨right_mem_segment ℝ 0 (v i), by simpa [he] using (right_mem_segment ℝ 0 (v j))⟩
    have hh := hnorm i
    have hvi : v i = 0 := by simpa using hvzero
    rw [hvi, norm_zero] at hh
    linarith
  have hcells := CurveComplex.FiniteStarGeometry.stationaryOppositeFanCells
    v R hR hnorm hinj i0 i1 hopp
  simpa [Finset.mem_univ] using hcells

private theorem actual_literal_finite_graph_old_avoiding_source_motion_private
    {J K : Type} [Fintype J] [Fintype K] (v : J → Plane) (old : K → Plane)
    (R : ℝ) (hR : 0 < R) (hv : ∀ j, ‖v j‖ = R)
    (hmeet : ∀ i j, i ≠ j → segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (v j) = {0})
    (i0 i1 : J) (hne : i0 ≠ i1) (hopp : v i1 = -v i0)
    {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
    (ha : a ∉ closedBall (0:Plane) R)
    (havoid : ∀ t : I, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ ball (0:Plane) R → H.map (t,x) = x) ∧
      (∀ t j (d : ℝ), 0 ≤ d → H.map (t,d • v j) = d • v j) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ H.finalMap '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          ∀ k, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • old k} = {0} := by
  obtain ⟨L,Q,hclosed,hconv,hzero,hinside,hcover,hdisjoint,hfront,hint,h0front,hfan,hlinear⟩ :=
    actual_finite_radial_fan_cells_private v R hR hv hmeet i0 i1 hne hopp
  obtain ⟨c₀,k,hc₀,hc₀1,hcR,hbfront,hAArc,hAi,hBi⟩ :=
    CurveComplex.FiniteStarGeometry.firstExit Q v R hR hclosed hconv hzero hinside hcover
      hdisjoint hfront hv α hα ha havoid
  obtain ⟨H,hH0,hHfix,hHgraph,hrest⟩ :=
    actual_sector_source_motion_entire_literal_radial_graph_fixed_private old v R hR hv
      (Q k) (hclosed k) (hconv k) (hint k) (hinside k) (hfan k) (h0front k)
      α hα (fun hx => ha (hinside k hx)) c₀ hc₀ hAArc hbfront hAi
  refine ⟨H,hH0,?_,hHgraph,hrest⟩
  intro t x hx
  apply hHfix
  intro hi
  apply hx
  have hh : interior (Q k) ⊆ ball (0:Plane) R := by
    have hs := interior_mono (hinside k)
    simpa only [interior_closedBall (0:Plane) (ne_of_gt hR)] using hs
  exact hh hi
#print axioms actual_literal_finite_graph_old_avoiding_source_motion_private

private theorem actual_literal_radial_graph_arbitrary_open_support_source_motion_private
    {J K : Type} [Fintype J] [Fintype K] (v : J → Plane) (old : K → Plane)
    (hv : ∀ j, ‖v j‖ = 1)
    (hmeet : ∀ i j, i ≠ j → segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (v j) = {0})
    (i0 i1 : J) (hne : i0 ≠ i1) (hopp : v i1 = -v i0)
    {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
    (havoid : ∀ t : I, 0 < t.val → ∀ j, α t ∉ {z : Plane | ∃ d : ℝ, 0 ≤ d ∧ z = d • v j})
    (V : Set Plane) (hV : IsOpen V) (h0V : (0:Plane) ∈ V) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t, H.map (t,0) = 0) ∧
      (∀ t x, x ∉ V → H.map (t,x) = x) ∧
      (∀ t j (d : ℝ), 0 ≤ d → H.map (t,d • v j) = d • v j) ∧
      ∃ c : CurveComplex.Interval, 0 < c ∧ c < 1 ∧
        ∃ q : Plane, q ≠ 0 ∧ H.finalMap '' (α '' Icc 0 c) = segment ℝ 0 q ∧
          ∀ k, segment ℝ 0 q ∩
            {z : Plane | ∃ r : ℝ, 0 ≤ r ∧ z = r • old k} = {0} := by
  classical
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have ha0 : a ≠ 0 := by
    intro he
    have ht : (1:I) = 0 := hα (by simpa [he] using α.target.trans α.source.symm)
    have hh := congrArg Subtype.val ht
    norm_num at hh
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  let R := min ε ‖a‖ / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRe : R < ε := by dsimp [R]; linarith [min_le_left ε ‖a‖]
  have hRa : R < ‖a‖ := by dsimp [R]; linarith [min_le_right ε ‖a‖]
  let w : J → Plane := fun j => R • v j
  have hw : ∀ j, ‖w j‖ = R := by
    intro j
    simp [w,norm_smul,Real.norm_eq_abs,abs_of_pos hR,hv]
  have hscale (j : J) {x : Plane} (hx : x ∈ segment ℝ (0:Plane) (w j)) :
      R⁻¹ • x ∈ segment ℝ (0:Plane) (v j) := by
    rw [segment_eq_image] at hx ⊢
    obtain ⟨d,hd,hde⟩ := hx
    refine ⟨d,hd,?_⟩
    simp only [smul_zero,add_zero,zero_add,w] at hde ⊢
    rw [←hde]
    simp only [smul_smul]
    congr 1
    field_simp
  have hwmeet : ∀ i j, i ≠ j → segment ℝ (0:Plane) (w i) ∩ segment ℝ (0:Plane) (w j) = {0} := by
    intro i j hij
    apply Set.Subset.antisymm
    · intro x hx
      have hem : R⁻¹ • x ∈ ({0}:Set Plane) := (hmeet i j hij) ▸ ⟨hscale i hx.1,hscale j hx.2⟩
      have he : R⁻¹ • x = (0:Plane) := hem
      have hh := congrArg (fun z : Plane => R • z) he
      simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt hR),one_smul,smul_zero,Set.mem_singleton_iff] using hh
    · intro x hx
      have he : x = 0 := hx
      subst x
      exact ⟨left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
  obtain ⟨H,hH0,hHout,hHgraph,hrest⟩ :=
    actual_literal_finite_graph_old_avoiding_source_motion_private w old R hR hw hwmeet i0 i1 hne
      (by simp [w,hopp]) α hα (by simpa only [mem_closedBall,dist_zero_right] using not_le.mpr hRa)
      (by
        intro t ht hx
        obtain ⟨j,hj⟩ := mem_iUnion.mp hx
        rw [segment_eq_image] at hj
        obtain ⟨d,hd,hde⟩ := hj
        apply havoid t ht j
        refine ⟨d*R,mul_nonneg hd.1 hR.le,?_⟩
        simpa only [w,smul_zero,add_zero,zero_add,smul_smul] using hde.symm)
  refine ⟨H,hH0,?_,?_,hrest⟩
  · intro t x hx
    apply hHout t x
    intro hi
    apply hx
    apply hball
    simp only [mem_ball,dist_zero_right] at hi ⊢
    exact hi.trans hRe
  · intro t j d hd
    have hh := hHgraph t j (d/R) (div_nonneg hd hR.le)
    simpa only [w,smul_smul,div_mul_cancel₀ _ (ne_of_gt hR)] using hh
#print axioms actual_literal_radial_graph_arbitrary_open_support_source_motion_private

private theorem actual_old_avoiding_segment_entire_ray_separation_private
    (q v : Plane) (hq : q ≠ 0)
    (havoid : segment ℝ (0:Plane) q ∩ {z : Plane | ∃ d : ℝ,0 ≤ d ∧ z=d • v} = {0})
    (d c : ℝ) (hd : 0 < d) (hc : 0 ≤ c) : d • q ≠ c • v := by
  intro he
  have hqe : q = (d⁻¹*c) • v := by
    have hh := congrArg (fun x : Plane => d⁻¹ • x) he
    simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt hd),one_smul] using hh
  have hzero : q ∈ ({0}:Set Plane) := havoid ▸
    ⟨right_mem_segment ℝ 0 q,⟨d⁻¹*c,mul_nonneg (inv_nonneg.mpr hd.le) hc,hqe⟩⟩
  exact hq hzero

private theorem actual_old_avoiding_inserted_unit_direction_literal_fan_private
    {J : Type} (v : J → Plane) (hv : ∀ j,‖v j‖=1)
    (hmeet : ∀ i j,i≠j → segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (v j)={0})
    (q : Plane) (hq : q ≠ 0)
    (havoid : ∀ j,segment ℝ (0:Plane) q ∩
      {z : Plane | ∃ d : ℝ,0 ≤ d ∧ z=d • v j}={0}) :
    let w : Option J → Plane := fun j => Option.elim j (‖q‖⁻¹ • q) v
    (∀ j,‖w j‖=1) ∧
    ∀ i j,i≠j → segment ℝ (0:Plane) (w i) ∩ segment ℝ (0:Plane) (w j)={0} := by
  classical
  intro w
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hmixed (j : J) : segment ℝ (0:Plane) (‖q‖⁻¹ • q) ∩ segment ℝ (0:Plane) (v j)={0} := by
    apply Set.Subset.antisymm
    · intro x hx
      simp only [segment_eq_image] at hx
      obtain ⟨d,hd,hde⟩ := hx.1
      obtain ⟨c,hc,hce⟩ := hx.2
      simp only [smul_zero,zero_add,smul_smul] at hde hce
      by_cases hd0 : d=0
      · have he : x=0 := by simpa only [hd0,zero_mul,zero_smul] using hde.symm
        exact he
      · have hdp : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm hd0)
        exact False.elim ((actual_old_avoiding_segment_entire_ray_separation_private q (v j) hq
          (havoid j) (d*‖q‖⁻¹) c (mul_pos hdp (inv_pos.mpr hqn)) hc.1) (hde.trans hce.symm))
    · intro x hx
      have he : x=0 := hx
      subst x
      exact ⟨left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
  refine ⟨?_,?_⟩
  · intro j
    cases j
    · simp [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hqn),inv_mul_cancel₀ (ne_of_gt hqn)]
    · exact hv _
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some j => exact hmixed j
    | some i =>
      cases j with
      | none =>
        change segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (‖q‖⁻¹ • q) = {0}
        rw [Set.inter_comm]
        exact hmixed i
      | some j => exact hmeet i j (fun he => hij (congrArg some he))
#print axioms actual_old_avoiding_segment_entire_ray_separation_private
#print axioms actual_old_avoiding_inserted_unit_direction_literal_fan_private

private theorem actual_second_source_short_clock_avoids_entire_first_radial_ray_private
    (η : CurveComplex.Interval → Plane) (hη : Topology.IsClosedEmbedding η)
    (hη0 : η 0 = 0) (q : Plane) (hq : q ≠ 0)
    (havoid : ∀ t : CurveComplex.Interval,0 < t.val → η t ∉ segment ℝ (0:Plane) q) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1),
      let ν : CurveComplex.Interval → Plane := fun t => η ⟨ρ*t.val,by
        constructor <;> nlinarith [t.property.1,t.property.2]⟩
      Topology.IsClosedEmbedding ν ∧ ν 0 = 0 ∧
      ∀ t : CurveComplex.Interval,0 < t.val →
        ν t ∉ {z : Plane | ∃ d : ℝ,0 ≤ d ∧ z=d • q} := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hn : η ⁻¹' ball (0:Plane) ‖q‖ ∈ nhds (0:CurveComplex.Interval) :=
    hη.continuous.continuousAt.preimage_mem_nhds (by rw [hη0];exact isOpen_ball.mem_nhds (by simpa using hqn))
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
  let ρ := min ε 1 / 2
  have hρ : 0 < ρ := by dsimp [ρ];positivity
  have hρε : ρ < ε := by dsimp [ρ];linarith [min_le_left ε 1]
  have hρ1 : ρ < 1 := by dsimp [ρ];linarith [min_le_right ε 1]
  let clock : CurveComplex.Interval → CurveComplex.Interval := fun t => ⟨ρ*t.val,by
    constructor <;> nlinarith [t.property.1,t.property.2]⟩
  have hc : Continuous clock := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have hi : Function.Injective clock := by
    intro t u he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    dsimp [clock] at hh
    nlinarith
  refine ⟨ρ,hρ,hρ1,?_,?_,?_⟩
  · exact hη.comp (hc.isClosedEmbedding hi)
  · simpa [clock] using hη0
  · intro t ht hx
    obtain ⟨d,hd,he⟩ := hx
    have hb : η (clock t) ∈ ball (0:Plane) ‖q‖ := by
      apply hball
      change dist (clock t) (0:CurveComplex.Interval) < ε
      change |ρ*t.val-0| < ε
      rw [sub_zero,abs_of_nonneg (mul_nonneg hρ.le t.property.1)]
      nlinarith [t.property.2]
    have he' : η (clock t) = d • q := he
    have hd1 : d < 1 := by
      rw [he'] at hb
      simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd] at hb
      nlinarith [hqn]
    apply havoid (clock t) (mul_pos hρ ht)
    rw [segment_eq_image]
    refine ⟨d,⟨hd,hd1.le⟩,?_⟩
    simpa only [smul_zero,zero_add] using he.symm
#print axioms actual_second_source_short_clock_avoids_entire_first_radial_ray_private

private theorem actual_short_terminal_clock_preserves_literal_prefix_image_private
    {X : Type} (η : CurveComplex.Interval → X) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (d : CurveComplex.Interval) :
    let clock : CurveComplex.Interval → CurveComplex.Interval := fun t => ⟨ρ*t.val,by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩
    let cut : CurveComplex.Interval := ⟨ρ*d.val,by
      constructor <;> nlinarith [d.property.1,d.property.2]⟩
    (η ∘ clock) '' Icc 0 d = η '' Icc 0 cut := by
  intro clock cut
  rw [Set.image_comp]
  congr 1
  apply Set.Subset.antisymm
  · rintro t ⟨u,hu,rfl⟩
    constructor
    · change 0 ≤ ρ*u.val
      exact mul_nonneg hρ.le u.property.1
    · change ρ*u.val ≤ ρ*d.val
      exact mul_le_mul_of_nonneg_left hu.2 hρ.le
  · intro t ht
    let u : CurveComplex.Interval := ⟨t.val/ρ,by
      constructor
      · exact div_nonneg t.property.1 hρ.le
      · apply (div_le_one₀ hρ).mpr
        have hh : t.val ≤ ρ*d.val := ht.2
        nlinarith [d.property.2]⟩
    refine ⟨u,⟨?_,?_⟩,?_⟩
    · exact u.property.1
    · change t.val/ρ ≤ d.val
      apply (div_le_iff₀ hρ).mpr
      have hh : t.val ≤ ρ*d.val := ht.2
      simpa only [mul_comm] using hh
    · apply Subtype.ext
      change ρ*(t.val/ρ)=t.val
      field_simp
#print axioms actual_short_terminal_clock_preserves_literal_prefix_image_private

private theorem actual_two_loop_germs_entire_literal_radial_graph_fixed_motion_private
    {J K : Type} [Fintype J] [Fintype K] (v : J → Plane) (old : K → Plane)
    (hv : ∀ j, ‖v j‖=1)
    (hfan : ∀ i j,i≠j → segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (v j)={0})
    (i0 i1 : J) (hne : i0≠i1) (hopp : v i1 = -v i0)
    (γ : Fin 2 → CurveComplex.Interval → Plane)
    (hγ : ∀ j,Topology.IsClosedEmbedding (γ j)) (hzero : ∀ j,γ j 0=0)
    (hmeet : range (γ 0) ∩ range (γ 1)={0})
    (havoid : ∀ j (t : CurveComplex.Interval),0 < t.val → ∀ k,
      γ j t ∉ {z : Plane | ∃ d : ℝ,0 ≤ d ∧ z=d • v k})
    (V : Set Plane) (hV : IsOpen V) (h0V : (0:Plane)∈V) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t,H.map (t,0)=0) ∧
      (∀ t x,x∉V → H.map (t,x)=x) ∧
      (∀ t j (d : ℝ),0≤d → H.map (t,d • v j)=d • v j) ∧
      ∃ cut : Fin 2 → CurveComplex.Interval,∃ vector : Fin 2 → Plane,
        (∀ j,0 < (cut j).val ∧ (cut j).val < 1 ∧ vector j≠0 ∧
          H.finalMap '' (γ j '' Icc 0 (cut j))=segment ℝ 0 (vector j)) ∧
        ∀ j k,segment ℝ 0 (vector j) ∩
          {z : Plane | ∃ d : ℝ,0≤d ∧ z=d • old k}={0} := by
  classical
  let α : Path (0:Plane) (γ 0 1) := {
    toFun := γ 0,continuous_toFun := (hγ 0).continuous,source' := hzero 0,target' := rfl }
  let compare : K ⊕ J → Plane := Sum.elim old v
  obtain ⟨H,hH0,hHout,hHgraph,c,hc,hc1,q,hq,himage,hqavoid⟩ :=
    actual_literal_radial_graph_arbitrary_open_support_source_motion_private v compare hv hfan
      i0 i1 hne hopp α (hγ 0).injective (havoid 0) V hV h0V
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:CurveComplex.Interval)
  have hHg : H.finalMap=g := funext (fun x => (hg x).symm)
  have hg0 : g 0=0 := by rw [←hHg];exact hH0 1
  let η : CurveComplex.Interval → Plane := g ∘ γ 1
  have hη : Topology.IsClosedEmbedding η := g.isClosedEmbedding.comp (hγ 1)
  have hη0 : η 0=0 := by change g (γ 1 0)=0;rw [hzero 1,hg0]
  have hηgraph : ∀ t : CurveComplex.Interval,0<t.val → ∀ j,
      η t ∉ {z : Plane | ∃ d : ℝ,0≤d ∧ z=d • v j} := by
    intro t ht j hx
    obtain ⟨d,hd,he⟩ := hx
    apply havoid 1 t ht j
    refine ⟨d,hd,?_⟩
    apply g.injective
    change η t=g (d • v j)
    rw [he,←hHg]
    exact (hHgraph 1 j d hd).symm
  have hgimage : g '' (γ 0 '' Icc 0 c)=segment ℝ 0 q := by
    rw [←hHg];exact himage
  have hηq : ∀ t : CurveComplex.Interval,0<t.val → η t∉segment ℝ 0 q :=
    checkedRecovery20actualSecondSourceAvoidsFirstRadialPrefix g (γ 0) (γ 1)
      (hγ 1).injective (hzero 1) hmeet c q hgimage
  obtain ⟨ρ,hρ,hρ1,hν,hν0,hνq⟩ :=
    actual_second_source_short_clock_avoids_entire_first_radial_ray_private η hη hη0 q hq hηq
  let clock : CurveComplex.Interval → CurveComplex.Interval := fun t => ⟨ρ*t.val,by
    constructor <;> nlinarith [t.property.1,t.property.2]⟩
  let ν : CurveComplex.Interval → Plane := η ∘ clock
  let w : Option J → Plane := fun j => Option.elim j (‖q‖⁻¹ • q) v
  obtain ⟨hw,hwmeet⟩ := actual_old_avoiding_inserted_unit_direction_literal_fan_private
    v hv hfan q hq (fun j => hqavoid (Sum.inr j))
  let β : Path (0:Plane) (ν 1) := {
    toFun := ν,continuous_toFun := hν.continuous,source' := hν0,target' := rfl }
  have hνavoid : ∀ t : CurveComplex.Interval,0<t.val → ∀ j,
      ν t ∉ {z : Plane | ∃ d : ℝ,0≤d ∧ z=d • w j} := by
    intro t ht j hx
    cases j with
    | none =>
      obtain ⟨d,hd,he⟩ := hx
      apply hνq t ht
      refine ⟨d*‖q‖⁻¹,mul_nonneg hd (inv_nonneg.mpr (norm_nonneg _)),?_⟩
      simpa only [w,Option.elim,smul_smul,ν,Function.comp_apply,clock] using he
    | some j => exact hηgraph (clock t) (mul_pos hρ ht) j hx
  obtain ⟨L,hL0,hLout,hLgraph,d,hd,hd1,z,hz,himL,hzold⟩ :=
    actual_literal_radial_graph_arbitrary_open_support_source_motion_private w old hw hwmeet
      (some i0) (some i1) (fun he => hne (Option.some.inj he)) (by exact hopp)
      β hν.injective hνavoid V hV h0V
  let d' : CurveComplex.Interval := ⟨ρ*d.val,by
    constructor <;> nlinarith [d.property.1,d.property.2]⟩
  have hd' : 0 < d'.val := mul_pos hρ hd
  have hd'1 : d'.val < 1 := by change ρ*d.val<1;nlinarith [d.property.2]
  have hLq (t : CurveComplex.Interval) : EqOn (fun x => L.map (t,x)) id (segment ℝ (0:Plane) q) := by
    intro x hx
    rw [segment_eq_image] at hx
    obtain ⟨r,hr,hre⟩ := hx
    simp only [smul_zero,zero_add] at hre
    rw [←hre]
    have hh := hLgraph t none (r*‖q‖) (mul_nonneg hr.1 (norm_nonneg _))
    have hqn : ‖q‖≠0 := norm_ne_zero_iff.mpr hq
    simpa only [w,Option.elim,smul_smul,mul_assoc,mul_inv_cancel₀ hqn,mul_one,id_eq] using hh
  let cuts : Fin 2 → CurveComplex.Interval := fun j => if j=0 then c else d'
  let vectors : Fin 2 → Plane := fun j => if j=0 then q else z
  refine ⟨H.compose L,?_,?_,?_,cuts,vectors,?_,?_⟩
  · intro t;change L.map (t,H.map (t,0))=0;rw [hH0,hL0]
  · intro t x hx;change L.map (t,H.map (t,x))=x;rw [hHout t x hx,hLout t x hx]
  · intro t j r hr
    change L.map (t,H.map (t,r • v j))=r • v j
    rw [hHgraph t j r hr]
    exact hLgraph t (some j) r hr
  · intro j
    fin_cases j
    · refine ⟨hc,hc1,hq,?_⟩
      change (H.compose L).finalMap '' (γ 0 '' Icc 0 c)=segment ℝ 0 q
      rw [AmbientIsotopy.compose_finalMap,image_comp,hHg,hgimage]
      exact (hLq 1).image_eq.trans (image_id _)
    · refine ⟨hd',hd'1,hz,?_⟩
      change (H.compose L).finalMap '' (γ 1 '' Icc 0 d')=segment ℝ 0 z
      rw [AmbientIsotopy.compose_finalMap,image_comp,hHg,←image_comp g (γ 1) (Icc 0 d')]
      change L.finalMap '' (η '' Icc 0 d')=segment ℝ 0 z
      rw [←actual_short_terminal_clock_preserves_literal_prefix_image_private η ρ hρ hρ1 d]
      exact himL
  · intro j k
    fin_cases j
    · exact hqavoid (Sum.inl k)
    · exact hzold k
#print axioms actual_two_loop_germs_entire_literal_radial_graph_fixed_motion_private

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_loop_graph_fixed_both_terminal_collars_literal_finite_graph_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hloop : b.val.map 0 = b.val.map 1)
    (e : OpenPartialHomeomorph S Plane) (hpe : b.val.map 0 ∈ e.source)
    (he0 : e (b.val.map 0) = 0)
    (hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = b.val.map 0)
    (P : Set S)
    {G : Type} [Fintype G] (graphVector : G → Plane)
    (hgraphNorm : ∀ j,‖graphVector j‖=1)
    (hgraphMeet : ∀ i j,i≠j → segment ℝ (0:Plane) (graphVector i) ∩
      segment ℝ (0:Plane) (graphVector j)={0})
    (i0 i1 : G) (hne : i0≠i1) (hopp : graphVector i1 = -graphVector i0)
    (hgraph : ∀ x, x ∈ e.source → (x ∈ P ↔
      ∃ j, ∃ d : ℝ,0≤d ∧ e x=d • graphVector j))
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 → b.val.map t ∉ P)
    {K : Type} [Fintype K] (old : K → Plane) (hold : ∀ k, old k ≠ 0)
    (haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k)
    (R : ℝ) (hR : 0 < R) (hRT : closedBall (0:Plane) R ⊆ e.target)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (hsource : ∀ terminal t, b.val.map
      (endpointGermParameter terminal r hr (by linarith) t) ∈ e.source) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ P → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let γ : Fin 2 → Interval → Plane := fun j t => e (b.val.map
    (endpointGermParameter (j = 1) r hr (by linarith) t))
  obtain ⟨hγ,hγ0,hmeet⟩ :=
    actual_marked_loop_two_terminal_germs_chart_source_private M b hloop e he0 r hr hrhalf hsource
  have havoid : ∀ j (t : Interval),0<t.val → ∀ k,
      γ j t ∉ {z : Plane | ∃ d : ℝ,0≤d ∧ z=d • graphVector k} := by
    intro j t ht k hx
    have hb := (hgraph _ (hsource (j=1) t)).mpr ⟨k,hx⟩
    apply hbP _ ?_ ?_ hb
    · fin_cases j <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2]
    · fin_cases j <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2]
  obtain ⟨L,hL0,hLout,hLref,cut,v,hcut,hvOld⟩ :=
    actual_two_loop_germs_entire_literal_radial_graph_fixed_motion_private graphVector old
      hgraphNorm hgraphMeet i0 i1 hne hopp γ hγ hγ0 hmeet havoid
      (ball (0:Plane) R) isOpen_ball (by simpa using hR)
  obtain ⟨H,hHmarks,hHP,hHout,hHstay,hHcoord⟩ :=
    actual_graph_fixed_terminal_chart_motion_lift_private M (b.val.map 0) e hpe he0 hemarks
      R hRT P L hL0 hLout
      (by
        intro t x hx hxs
        obtain ⟨j,d,hd,he⟩ := (hgraph x hxs).mp hx
        rw [he]
        exact hLref t j d hd)
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:Interval)
  have hHg : H.finalMap = g := funext (fun x => (hg x).symm)
  have hgmarks : ∀ x, x ∈ M.cover.branch → g x = x := fun x hx => by
    rw [←hHg]; exact hHmarks 1 x hx
  let c := b.transport g hgmarks
  have hcmap (t : Interval) : c.val.map t = H.finalMap (b.val.map t) := by
    change g (b.val.map t) = H.finalMap (b.val.map t)
    rw [hHg]
  have hclass : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hHmarks,?_⟩
    rw [hHg]
    exact (MarkedArc.transport_image b.val g hgmarks).symm
  let δ := r * min (cut 0).val (cut 1).val / 2
  have hmin : 0 < min (cut 0).val (cut 1).val := lt_min (hcut 0).1 (hcut 1).1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ ≤ r := by
    have hm : min (cut 0).val (cut 1).val ≤ 1 := (min_le_left _ _).trans (cut 0).property.2
    dsimp [δ]
    nlinarith
  have hδhalf : δ < 1/2 := hδr.trans_lt hrhalf
  have hδcut (j : Fin 2) : δ ≤ r * (cut j).val := by
    have hm : min (cut 0).val (cut 1).val ≤ (cut j).val := by
      fin_cases j
      · exact min_le_left _ _
      · exact min_le_right _ _
    dsimp [δ]
    nlinarith [(cut j).property.1]
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hHmarks,hHP,hcmap,?_⟩
  intro t ht0 ht1 htδ hcontact
  obtain ⟨j,u,hu,htu⟩ : ∃ (j : Fin 2) (u : Interval),
      u ∈ Icc 0 (cut j) ∧
      endpointGermParameter (j=1) r hr (by linarith) u = t := by
    rcases htδ with htδ|htδ
    · let u : Interval := ⟨t.val/r,⟨div_nonneg t.property.1 hr.le,
        (div_le_one hr).mpr (htδ.trans hδr)⟩⟩
      refine ⟨0,u,⟨u.property.1,?_⟩,?_⟩
      · change t.val/r ≤ (cut 0).val
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans (hδcut 0))
      · apply Subtype.ext
        change r*(t.val/r) = t.val
        field_simp
    · let u : Interval := ⟨(1-t.val)/r,⟨div_nonneg (by linarith) hr.le,
        (div_le_one hr).mpr (htδ.trans hδr)⟩⟩
      refine ⟨1,u,⟨u.property.1,?_⟩,?_⟩
      · change (1-t.val)/r ≤ (cut 1).val
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans (hδcut 1))
      · apply Subtype.ext
        change 1-r*((1-t.val)/r) = t.val
        field_simp
        ring
  have hbt : b.val.map t ∈ e.source := htu ▸ hsource (j=1) u
  have hct : c.val.map t ∈ e.source := by rw [hcmap]; exact hHstay 1 _ hbt
  have hseg : e (c.val.map t) ∈ segment ℝ (0:Plane) (v j) := by
    rw [hcmap]
    change e (H.map (1,b.val.map t)) ∈ segment ℝ (0:Plane) (v j)
    rw [hHcoord 1 _ hbt]
    change L.finalMap (e (b.val.map t)) ∈ segment ℝ (0:Plane) (v j)
    rw [←(hcut j).2.2.2]
    refine ⟨γ j u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg L.finalMap (congrArg e (congrArg b.val.map htu))
  obtain ⟨k,d,hd,heold⟩ := haOld _ hcontact hct
  have hz : e (c.val.map t) = 0 := by
    apply Set.mem_singleton_iff.mp
    rw [←hvOld j k]
    exact ⟨hseg,⟨d,hd,heold⟩⟩
  have hcp : c.val.map t = b.val.map 0 := e.injOn hct hpe (hz.trans he0.symm)
  have hm : c.val.map t ∈ M.cover.branch := hcp.symm ▸ b.val.start_marked
  exact (c.val.marked_only_at_ends t hm).elim
    (fun h => by have hh := congrArg Subtype.val h; change t.val=0 at hh; linarith)
    (fun h => by have hh := congrArg Subtype.val h; change t.val=1 at hh; linarith)
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_loop_graph_fixed_both_terminal_collars_literal_finite_graph_private

private theorem actual_literal_fan_direction_normalization_preserves_ray_separation_private
    {J : Type} (v : J → Plane) (hv : ∀ j,v j≠0)
    (hmeet : ∀ i j,i≠j → segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (v j)={0}) :
    let w : J → Plane := fun j => ‖v j‖⁻¹ • v j
    (∀ j,‖w j‖=1) ∧
    (∀ i j,i≠j → segment ℝ (0:Plane) (w i) ∩ segment ℝ (0:Plane) (w j)={0}) ∧
    ∀ j x,(∃ d : ℝ,0≤d ∧ x=d • v j) ↔ (∃ d : ℝ,0≤d ∧ x=d • w j) := by
  intro w
  have hn (j : J) : 0<‖v j‖ := norm_pos_iff.mpr (hv j)
  refine ⟨?_,?_,?_⟩
  · intro j
    simp [w,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hn j)),inv_mul_cancel₀ (ne_of_gt (hn j))]
  · intro i j hij
    apply Set.Subset.antisymm
    · intro x hx
      simp only [segment_eq_image] at hx
      obtain ⟨d,hd,hde⟩ := hx.1
      obtain ⟨c,hc,hce⟩ := hx.2
      simp only [w,smul_zero,zero_add,smul_smul] at hde hce
      let scale := min ‖v i‖ ‖v j‖
      have hscale : 0<scale := lt_min (hn i) (hn j)
      have hcoeff (k : J) (e : ℝ) (he : e∈Icc 0 1) (hscalek : scale≤‖v k‖) :
          scale*(e*‖v k‖⁻¹)∈Icc (0:ℝ) 1 := by
        constructor
        · exact mul_nonneg hscale.le (mul_nonneg he.1 (inv_nonneg.mpr (norm_nonneg _)))
        · have hratio : scale/‖v k‖≤1 := (div_le_one₀ (hn k)).mpr hscalek
          have heq : scale*(e*‖v k‖⁻¹)=e*(scale/‖v k‖) := by ring
          rw [heq]
          exact (mul_le_mul_of_nonneg_left hratio he.1).trans (by simpa using he.2)
      have hxFan : scale • x∈segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (v j) := by
        constructor
        · rw [segment_eq_image]
          refine ⟨scale*(d*‖v i‖⁻¹),hcoeff i d hd (min_le_left _ _),?_⟩
          simp only [smul_zero,zero_add]
          rw [←hde,smul_smul]
        · rw [segment_eq_image]
          refine ⟨scale*(c*‖v j‖⁻¹),hcoeff j c hc (min_le_right _ _),?_⟩
          simp only [smul_zero,zero_add]
          rw [←hce,smul_smul]
      have hzm : scale • x∈({0}:Set Plane) := (hmeet i j hij) ▸ hxFan
      have hz : scale • x=(0:Plane) := hzm
      have hh := congrArg (fun y : Plane => scale⁻¹ • y) hz
      simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt hscale),one_smul,smul_zero,Set.mem_singleton_iff] using hh
    · intro x hx
      have he : x=0 := hx
      subst x
      exact ⟨left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
  · intro j x
    constructor
    · rintro ⟨d,hd,he⟩
      refine ⟨d*‖v j‖,mul_nonneg hd (norm_nonneg _),?_⟩
      simpa only [w,smul_smul,mul_assoc,mul_inv_cancel₀ (ne_of_gt (hn j)),mul_one] using he
    · rintro ⟨d,hd,he⟩
      refine ⟨d*‖v j‖⁻¹,mul_nonneg hd (inv_nonneg.mpr (norm_nonneg _)),?_⟩
      simpa only [w,smul_smul] using he
#print axioms actual_literal_fan_direction_normalization_preserves_ray_separation_private

namespace CurveComplex.HyperellipticModel
private theorem actual_multiple_incident_graph_original_loop_terminal_collars_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (hloop : b.val.map 0 = b.val.map 1)
    (g₀ g₁ : G × Bool)
    (hg₀ : (if g₀.2 then (graph g₀.1).val.map 1 else (graph g₀.1).val.map 0) = b.val.map 0)
    (hg₁ : (if g₁.2 then (graph g₁.1).val.map 1 else (graph g₁.1).val.map 0) = b.val.map 0)
    (hne : g₀≠g₁)
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let p := b.val.map 0
  let family : Option G → EssentialMarkedArc M := fun i => Option.elim i a graph
  have hchosen : (some g₀.1,g₀.2) ≠ (some g₁.1,g₁.2) := by
    intro he
    apply hne
    exact Prod.ext (Option.some.inj (congrArg Prod.fst he)) (congrArg (fun z : Option G × Bool => z.2) he)
  obtain ⟨F,hpF,hFp,_,hmarks,r₀,hr₀,hr₀half,v,hvn,hv0,hv1,_,hvmeet,_,ε,hε,hεT,hεv,htrace,_⟩ :=
    actual_marked_whole_trace_fan_two_prescribed_incidences_private M family hfinite p b.val.start_marked
      univ isOpen_univ (mem_univ _) (some g₀.1,g₀.2) (some g₁.1,g₁.2) hg₀ hg₁ hchosen
  let U : Set S := F.source ∩ F ⁻¹' ball (0:Plane) (ε/2)
  have hU : IsOpen U := F.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hpF,by simpa [hFp] using half_pos hε⟩
  let e := F.restr U
  have hes : e.source = F.source ∩ U := by
    rw [OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have heval (x : S) : e x = F x := rfl
  have hpe : p ∈ e.source := hes.symm ▸ ⟨hpF,hpU⟩
  have he0 : e p = 0 := hFp
  have hxF (x : S) (hx : x ∈ e.source) : x ∈ F.source := (hes ▸ hx).1
  have hxBall (x : S) (hx : x ∈ e.source) : F x ∈ ball (0:Plane) ε :=
    (ball_subset_ball (by linarith : ε/2 ≤ ε)) ((hes ▸ hx).2.2)
  have hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = p := by
    intro x hx hm
    exact Set.mem_singleton_iff.mp (hmarks ▸ (show x ∈ F.source ∩ (M.cover.branch:Set S) from ⟨hxF x hx,hm⟩))
  have hR : 0 < ε/4 := by positivity
  have hRT : closedBall (0:Plane) (ε/4) ⊆ e.target := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ε/4 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hzε : z ∈ ball (0:Plane) ε := by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε by linarith)
    have hzF : z ∈ F.target := hεT hzε
    have hx : F.symm z ∈ e.source := by
      rw [hes]
      refine ⟨F.map_target hzF,⟨F.map_target hzF,?_⟩⟩
      rw [mem_preimage,F.right_inv hzF]
      simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε/2 by linarith)
    have hh := e.map_source hx
    change F (F.symm z) ∈ e.target at hh
    rw [F.right_inv hzF] at hh
    exact hh
  let D := {g : G × Bool // (if g.2 then (graph g.1).val.map 1 else (graph g.1).val.map 0) = p}
  let raw : D → Plane := fun g => v (some g.val.1,g.val.2)
  let unit : D → Plane := fun g => ‖raw g‖⁻¹ • raw g
  have hraw (g : D) : raw g≠0 := hvn (some g.val.1,g.val.2) g.property
  have hrawmeet : ∀ i j : D,i≠j → segment ℝ (0:Plane) (raw i) ∩ segment ℝ (0:Plane) (raw j)={0} := by
    intro i j hij
    apply hvmeet _ _ i.property j.property
    intro he
    apply hij
    apply Subtype.ext
    exact Prod.ext (Option.some.inj (congrArg (fun z => z.1) he)) (congrArg (fun z => z.2) he)
  obtain ⟨hunit,hunitmeet,hrays⟩ :=
    actual_literal_fan_direction_normalization_preserves_ray_separation_private raw hraw hrawmeet
  let d₀ : D := ⟨g₀,hg₀⟩
  let d₁ : D := ⟨g₁,hg₁⟩
  have hdne : d₀≠d₁ := fun he => hne (congrArg Subtype.val he)
  have hunitopp : unit d₁ = -unit d₀ := by
    have hn0 : ‖Plane.mk 1 0‖=(1:ℝ) := by simp [Plane.mk,EuclideanSpace.norm_eq]
    have hn1 : ‖Plane.mk (-1) 0‖=(1:ℝ) := by simp [Plane.mk,EuclideanSpace.norm_eq]
    simp only [unit,raw,d₀,d₁,hv0,hv1,hn0,hn1,inv_one,one_smul]
    ext i;fin_cases i <;> simp [Plane.mk]
  have hgraph : ∀ x,x∈e.source → (x∈⋃ j,(graph j).val.image ↔
      ∃ g : D, ∃ d : ℝ,0≤d ∧ e x=d • unit g) := by
    intro x hx
    constructor
    · intro hxP
      obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
      obtain ⟨terminal,hi,hs⟩ := (htrace (some j) x (hxF x hx) (hxBall x hx)).mp hj
      rw [segment_eq_image] at hs
      obtain ⟨d,hd,hde⟩ := hs
      let g : D := ⟨(j,terminal),hi⟩
      refine ⟨g,?_⟩
      apply (hrays g (e x)).mp
      refine ⟨d,hd.1,?_⟩
      simpa only [heval,smul_zero,zero_add,raw,g] using hde.symm
    · rintro ⟨g,d,hd,he⟩
      obtain ⟨c,hc,hce⟩ := (hrays g (e x)).mpr ⟨d,hd,he⟩
      have hn : ‖e x‖<ε := by simpa only [heval,mem_ball,dist_zero_right] using hxBall x hx
      have hvbound : ε < ‖raw g‖ := hεv (some g.val.1,g.val.2) g.property
      have hc1 : c≤1 := by
        rw [hce,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc] at hn
        have hpos := norm_pos_iff.mpr (hraw g)
        nlinarith
      apply mem_iUnion.mpr
      refine ⟨g.val.1,(htrace (some g.val.1) x (hxF x hx) (hxBall x hx)).mpr ⟨g.val.2,g.property,?_⟩⟩
      rw [segment_eq_image]
      refine ⟨c,⟨hc,hc1⟩,?_⟩
      simpa only [heval,smul_zero,zero_add,raw] using hce.symm
  let Old : Type := {terminal : Bool // (if terminal then a.val.map 1 else a.val.map 0) = p}
  let old : Old → Plane := fun k => v (none,k.val)
  have hold : ∀ k, old k ≠ 0 := fun k => hvn (none,k.val) k.property
  have haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k : Old, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k := by
    intro x hx hxs
    obtain ⟨terminal,hi,hs⟩ := (htrace none x (hxF x hxs) (hxBall x hxs)).mp hx
    rw [segment_eq_image] at hs
    obtain ⟨d,hd,hde⟩ := hs
    exact ⟨⟨terminal,hi⟩,d,hd.1,by simpa only [heval,smul_zero,add_zero,zero_add,old] using hde.symm⟩
  obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => b) p
    e.source e.open_source hpe
  have hsource : ∀ terminal t, b.val.map
      (endpointGermParameter terminal r hr (by linarith) t) ∈ e.source := by
    intro terminal t
    cases terminal
    · apply hstart PUnit.unit rfl
      change r*t.val ≤ r
      nlinarith [t.property.2]
    · apply hend PUnit.unit hloop.symm
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  exact actual_marked_loop_graph_fixed_both_terminal_collars_literal_finite_graph_private M a b hloop e
    hpe he0 hemarks (⋃ j,(graph j).val.image) unit hunit hunitmeet d₀ d₁ hdne hunitopp hgraph
    hbP old hold haOld (ε/4) hR hRT r hr hrhalf hsource
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_multiple_incident_graph_original_loop_terminal_collars_private

open Lean Elab Term in
elab "checkedRecovery20actualOldAvoidingFreeSourceStarRadialization" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualOriginalEndpointPosition.ActualAnchorRelativeEndpointRadialization 0).append
    `CurveComplex.HyperellipticModel.actualOldAvoidingFreeSourceStarRadialization
  discard <| getConstInfo n
  return mkConst n

private theorem actual_old_avoiding_free_source_star_supported_motion_private
    {J K : Type} [Fintype J] [Fintype K]
    (γ : J → CurveComplex.Interval → Plane)
    (hγ : ∀ j,Topology.IsClosedEmbedding (γ j)) (hzero : ∀ j,γ j 0=0)
    (hmeet : ∀ j k,j≠k → range (γ j) ∩ range (γ k)={0})
    (old : K → Plane) (hold : ∀ k,old k≠0)
    (V : Set Plane) (hV : IsOpen V) (h0V : (0:Plane)∈V) :
    ∃ H : AmbientIsotopy Plane,
      (∀ t,H.map (t,0)=0) ∧ (∀ t x,x∉V → H.map (t,x)=x) ∧
      ∃ cut : J → CurveComplex.Interval,∃ vector : J → Plane,
        (∀ j,0<(cut j).val ∧ (cut j).val<1 ∧ vector j≠0 ∧
          H.finalMap '' (γ j '' Icc 0 (cut j))=segment ℝ 0 (vector j)) ∧
        ∀ j k,segment ℝ 0 (vector j) ∩
          {z : Plane | ∃ d : ℝ,0≤d ∧ z=d • old k}={0} := by
  obtain ⟨F,R,hR,hRV,hF0,hFout,cut,vector,hcut,havoid⟩ :=
    checkedRecovery20actualOldAvoidingFreeSourceStarRadialization γ hγ hzero hmeet old hold V hV h0V
  obtain ⟨H,hHF,hHout,hH0,_⟩ :=
    actual_radially_closed_fixed_set_alexander_isotopy_private R hR F
      (by intro x hx;apply hFout;simpa only [mem_ball,dist_zero_right] using not_lt.mpr hx)
      hF0 (∅:Set Plane) (by simp) (by simp)
  refine ⟨H,hH0,?_,cut,vector,?_,havoid⟩
  · intro t x hx
    apply hHout t x
    apply le_of_not_gt
    intro hi
    apply hx
    apply hRV
    simpa only [mem_closedBall,dist_zero_right] using hi.le
  · intro j
    simpa only [hHF] using hcut j
#print axioms actual_old_avoiding_free_source_star_supported_motion_private

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_loop_both_terminal_collars_chart_disjoint_graph_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hloop : b.val.map 0 = b.val.map 1)
    (e : OpenPartialHomeomorph S Plane) (hpe : b.val.map 0 ∈ e.source)
    (he0 : e (b.val.map 0) = 0)
    (hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = b.val.map 0)
    (P : Set S)
    (hgraph : Disjoint e.source P)
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 → b.val.map t ∉ P)
    {K : Type} [Fintype K] (old : K → Plane) (hold : ∀ k, old k ≠ 0)
    (haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k)
    (R : ℝ) (hR : 0 < R) (hRT : closedBall (0:Plane) R ⊆ e.target)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (hsource : ∀ terminal t, b.val.map
      (endpointGermParameter terminal r hr (by linarith) t) ∈ e.source) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ P → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let γ : Fin 2 → Interval → Plane := fun j t => e (b.val.map
    (endpointGermParameter (j = 1) r hr (by linarith) t))
  obtain ⟨hγ,hγ0,hmeet⟩ :=
    actual_marked_loop_two_terminal_germs_chart_source_private M b hloop e he0 r hr hrhalf hsource
  have hmeetAll : ∀ i j : Fin 2,i≠j → range (γ i) ∩ range (γ j)={0} := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · exact hmeet
    · rw [Set.inter_comm];exact hmeet
    · exact False.elim (hij rfl)
  obtain ⟨L,hL0,hLout,cut,v,hcut,hvOld⟩ :=
    actual_old_avoiding_free_source_star_supported_motion_private γ hγ hγ0 hmeetAll old hold
      (ball (0:Plane) R) isOpen_ball (by simpa using hR)
  obtain ⟨H,hHmarks,hHP,hHout,hHstay,hHcoord⟩ :=
    actual_graph_fixed_terminal_chart_motion_lift_private M (b.val.map 0) e hpe he0 hemarks
      R hRT P L hL0 hLout
      (by intro t x hx hxs;exact False.elim (Set.disjoint_left.mp hgraph hxs hx))
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:Interval)
  have hHg : H.finalMap = g := funext (fun x => (hg x).symm)
  have hgmarks : ∀ x, x ∈ M.cover.branch → g x = x := fun x hx => by
    rw [←hHg]; exact hHmarks 1 x hx
  let c := b.transport g hgmarks
  have hcmap (t : Interval) : c.val.map t = H.finalMap (b.val.map t) := by
    change g (b.val.map t) = H.finalMap (b.val.map t)
    rw [hHg]
  have hclass : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hHmarks,?_⟩
    rw [hHg]
    exact (MarkedArc.transport_image b.val g hgmarks).symm
  let δ := r * min (cut 0).val (cut 1).val / 2
  have hmin : 0 < min (cut 0).val (cut 1).val := lt_min (hcut 0).1 (hcut 1).1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ ≤ r := by
    have hm : min (cut 0).val (cut 1).val ≤ 1 := (min_le_left _ _).trans (cut 0).property.2
    dsimp [δ]
    nlinarith
  have hδhalf : δ < 1/2 := hδr.trans_lt hrhalf
  have hδcut (j : Fin 2) : δ ≤ r * (cut j).val := by
    have hm : min (cut 0).val (cut 1).val ≤ (cut j).val := by
      fin_cases j
      · exact min_le_left _ _
      · exact min_le_right _ _
    dsimp [δ]
    nlinarith [(cut j).property.1]
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hHmarks,hHP,hcmap,?_⟩
  intro t ht0 ht1 htδ hcontact
  obtain ⟨j,u,hu,htu⟩ : ∃ (j : Fin 2) (u : Interval),
      u ∈ Icc 0 (cut j) ∧
      endpointGermParameter (j=1) r hr (by linarith) u = t := by
    rcases htδ with htδ|htδ
    · let u : Interval := ⟨t.val/r,⟨div_nonneg t.property.1 hr.le,
        (div_le_one hr).mpr (htδ.trans hδr)⟩⟩
      refine ⟨0,u,⟨u.property.1,?_⟩,?_⟩
      · change t.val/r ≤ (cut 0).val
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans (hδcut 0))
      · apply Subtype.ext
        change r*(t.val/r) = t.val
        field_simp
    · let u : Interval := ⟨(1-t.val)/r,⟨div_nonneg (by linarith) hr.le,
        (div_le_one hr).mpr (htδ.trans hδr)⟩⟩
      refine ⟨1,u,⟨u.property.1,?_⟩,?_⟩
      · change (1-t.val)/r ≤ (cut 1).val
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans (hδcut 1))
      · apply Subtype.ext
        change 1-r*((1-t.val)/r) = t.val
        field_simp
        ring
  have hbt : b.val.map t ∈ e.source := htu ▸ hsource (j=1) u
  have hct : c.val.map t ∈ e.source := by rw [hcmap]; exact hHstay 1 _ hbt
  have hseg : e (c.val.map t) ∈ segment ℝ (0:Plane) (v j) := by
    rw [hcmap]
    change e (H.map (1,b.val.map t)) ∈ segment ℝ (0:Plane) (v j)
    rw [hHcoord 1 _ hbt]
    change L.finalMap (e (b.val.map t)) ∈ segment ℝ (0:Plane) (v j)
    rw [←(hcut j).2.2.2]
    refine ⟨γ j u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg L.finalMap (congrArg e (congrArg b.val.map htu))
  obtain ⟨k,d,hd,heold⟩ := haOld _ hcontact hct
  have hz : e (c.val.map t) = 0 := by
    apply Set.mem_singleton_iff.mp
    rw [←hvOld j k]
    exact ⟨hseg,⟨d,hd,heold⟩⟩
  have hcp : c.val.map t = b.val.map 0 := e.injOn hct hpe (hz.trans he0.symm)
  have hm : c.val.map t ∈ M.cover.branch := hcp.symm ▸ b.val.start_marked
  exact (c.val.marked_only_at_ends t hm).elim
    (fun h => by have hh := congrArg Subtype.val h; change t.val=0 at hh; linarith)
    (fun h => by have hh := congrArg Subtype.val h; change t.val=1 at hh; linarith)
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_loop_both_terminal_collars_chart_disjoint_graph_private

namespace CurveComplex.HyperellipticModel
private theorem actual_no_incident_graph_original_loop_terminal_collars_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (hloop : b.val.map 0 = b.val.map 1)
    (terminal : Bool)
    (haIncident : (if terminal then a.val.map 1 else a.val.map 0) = b.val.map 0)
    (hno : ∀ j (terminal : Bool),(if terminal then (graph j).val.map 1 else (graph j).val.map 0) ≠ b.val.map 0)
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let p := b.val.map 0
  let family : Option G → EssentialMarkedArc M := fun i => Option.elim i a graph
  obtain ⟨F,hpF,hFp,_,hmarks,r₀,hr₀,hr₀half,v,hvn,hv0,_,_,_,_,ε,hε,hεT,hεv,htrace,_⟩ :=
    actual_marked_endpoint_source_fan_chart M family hfinite p b.val.start_marked
      univ isOpen_univ (mem_univ _) (none,terminal) haIncident
  let U : Set S := F.source ∩ F ⁻¹' ball (0:Plane) (ε/2)
  have hU : IsOpen U := F.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hpF,by simpa [hFp] using half_pos hε⟩
  let e := F.restr U
  have hes : e.source = F.source ∩ U := by
    rw [OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have heval (x : S) : e x = F x := rfl
  have hpe : p ∈ e.source := hes.symm ▸ ⟨hpF,hpU⟩
  have he0 : e p = 0 := hFp
  have hxF (x : S) (hx : x ∈ e.source) : x ∈ F.source := (hes ▸ hx).1
  have hxBall (x : S) (hx : x ∈ e.source) : F x ∈ ball (0:Plane) ε :=
    (ball_subset_ball (by linarith : ε/2 ≤ ε)) ((hes ▸ hx).2.2)
  have hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = p := by
    intro x hx hm
    exact Set.mem_singleton_iff.mp (hmarks ▸ (show x ∈ F.source ∩ (M.cover.branch:Set S) from ⟨hxF x hx,hm⟩))
  have hR : 0 < ε/4 := by positivity
  have hRT : closedBall (0:Plane) (ε/4) ⊆ e.target := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ε/4 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hzε : z ∈ ball (0:Plane) ε := by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε by linarith)
    have hzF : z ∈ F.target := hεT hzε
    have hx : F.symm z ∈ e.source := by
      rw [hes]
      refine ⟨F.map_target hzF,⟨F.map_target hzF,?_⟩⟩
      rw [mem_preimage,F.right_inv hzF]
      simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε/2 by linarith)
    have hh := e.map_source hx
    change F (F.symm z) ∈ e.target at hh
    rw [F.right_inv hzF] at hh
    exact hh
  have hgraph : Disjoint e.source (⋃ j,(graph j).val.image) := by
    apply Set.disjoint_left.mpr
    intro x hx hxP
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
    obtain ⟨terminal,hi,_⟩ := (htrace (some j) x (hxF x hx) (hxBall x hx)).mp hj
    exact hno j terminal hi
  let Old : Type := {terminal : Bool // (if terminal then a.val.map 1 else a.val.map 0) = p}
  let old : Old → Plane := fun k => v (none,k.val)
  have hold : ∀ k, old k ≠ 0 := fun k => hvn (none,k.val) k.property
  have haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k : Old, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k := by
    intro x hx hxs
    obtain ⟨terminal,hi,hs⟩ := (htrace none x (hxF x hxs) (hxBall x hxs)).mp hx
    rw [segment_eq_image] at hs
    obtain ⟨d,hd,hde⟩ := hs
    exact ⟨⟨terminal,hi⟩,d,hd.1,by simpa only [heval,smul_zero,add_zero,zero_add,old] using hde.symm⟩
  obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => b) p
    e.source e.open_source hpe
  have hsource : ∀ terminal t, b.val.map
      (endpointGermParameter terminal r hr (by linarith) t) ∈ e.source := by
    intro terminal t
    cases terminal
    · apply hstart PUnit.unit rfl
      change r*t.val ≤ r
      nlinarith [t.property.2]
    · apply hend PUnit.unit hloop.symm
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  exact actual_marked_loop_both_terminal_collars_chart_disjoint_graph_private M a b hloop e
    hpe he0 hemarks (⋃ j,(graph j).val.image) hgraph hbP old hold haOld
    (ε/4) hR hRT r hr hrhalf hsource
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_no_incident_graph_original_loop_terminal_collars_private

namespace CurveComplex.HyperellipticModel
private theorem actual_arbitrary_graph_original_loop_terminal_collars_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (hloop : b.val.map 0 = b.val.map 1)
    (terminal : Bool)
    (haIncident : (if terminal then a.val.map 1 else a.val.map 0) = b.val.map 0)
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        t.val ≤ δ ∨ 1-t.val ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let incident : G × Bool → Prop := fun g =>
    (if g.2 then (graph g.1).val.map 1 else (graph g.1).val.map 0) = b.val.map 0
  by_cases hsome : ∃ g,incident g
  · obtain ⟨g₀,hg₀⟩ := hsome
    by_cases htwo : ∃ g₁,incident g₁ ∧ g₁≠g₀
    · obtain ⟨g₁,hg₁,hne⟩ := htwo
      exact actual_multiple_incident_graph_original_loop_terminal_collars_private M graph a b hfinite
        hloop g₀ g₁ hg₀ hg₁ hne.symm hbP
    · have honly : ∀ j terminal,
          ((if terminal then (graph j).val.map 1 else (graph j).val.map 0) = b.val.map 0 ↔
            j=g₀.1 ∧ terminal=g₀.2) := by
        intro j terminal
        constructor
        · intro hi
          have he : (j,terminal)=g₀ := by
            by_contra hn
            exact htwo ⟨(j,terminal),hi,hn⟩
          exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
        · rintro ⟨rfl,rfl⟩
          exact hg₀
      exact actual_single_incident_graph_original_loop_terminal_collars_private M graph a b hfinite
        hloop g₀.1 g₀.2 hg₀ honly hbP
  · exact actual_no_incident_graph_original_loop_terminal_collars_private M graph a b hfinite hloop
      terminal haIncident (by intro j terminal hi;exact hsome ⟨(j,terminal),hi⟩) hbP
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_arbitrary_graph_original_loop_terminal_collars_private

namespace CurveComplex.HyperellipticModel
private theorem actual_original_aligned_disjoint_families_loop_relative_finite_preparation_private
    {E S I : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (r s : I → EssentialMarkedArc M)
    (hd : ∀ i j,i≠j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hsd : ∀ i j,i≠j → Disjoint (arcInterior M (s i)) (arcInterior M (s j)))
    (J : Finset I) (u : I) (hu : u∉J)
    (haligned : ∀ j∈J,(s j).val.image=(r j).val.image)
    (hloop : (s u).val.map 0=(s u).val.map 1)
    (terminal : Bool)
    (haIncident : (if terminal then (r u).val.map 1 else (r u).val.map 0)=(s u).val.map 0) :
    ∃ d : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      Quotient.mk (essentialArcSetoid M) d=Quotient.mk (essentialArcSetoid M) (s u) ∧
      H.finalMap '' (s u).val.image=d.val.image ∧
      (∀ t x,x∈M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x,x∈⋃ j : {j//j∈J},(r j.val).val.image → H.map (t,x)=x) ∧
      (ArcSurgery.crossings M (r u) d).Finite ∧
      ∀ q∈ArcSurgery.crossings M (r u) d,ArcSurgery.CrossesInDisk M (r u) d q := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let G := {j//j∈J}
  let P : Set S := ⋃ j : G,(r j.val).val.image
  have hP : IsClosed P := isClosed_iUnion_of_finite (fun j => (isCompact_range (r j.val).val.continuous).isClosed)
  have hbP : arcInterior M (s u)⊆Pᶜ := by
    intro x hx hxP
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
    have hs : x∈arcInterior M (s j.val) := ⟨(haligned j.val j.property).symm ▸ hj,hx.2⟩
    exact Set.disjoint_left.mp (hsd u j.val (fun he => hu (he.symm ▸ j.property))) hx hs
  have hbClock : ∀ t : Interval,0<t.val → t.val<1 → (s u).val.map t∉P := by
    intro t ht0 ht1
    apply hbP
    refine ⟨mem_range_self t,?_⟩
    intro hm
    rcases (s u).val.marked_only_at_ends t hm with he|he
    · have hh := congrArg Subtype.val he
      change t.val=0 at hh
      linarith
    · have hh := congrArg Subtype.val he
      change t.val=1 at hh
      linarith
  let f : Option G → I := fun i => Option.elim i u (fun j => j.val)
  have hf : Function.Injective f := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        exfalso
        have he' : u=j.val := he
        exact hu (he'.symm ▸ j.property)
    | some i =>
      cases j with
      | none =>
        exfalso
        have he' : i.val=u := he
        exact hu (he' ▸ i.property)
      | some j => exact congrArg some (Subtype.ext he)
  have hfinite : ∀ i j : Option G,i≠j →
      (ArcSurgery.crossings M (Option.elim i (r u) (fun j : G => r j.val))
        (Option.elim j (r u) (fun j : G => r j.val))).Finite := by
    intro i j hij
    have hfamily (i : Option G) : Option.elim i (r u) (fun j : G => r j.val)=r (f i) := by cases i <;> rfl
    have hz : ArcSurgery.crossings M (r (f i)) (r (f j))=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact Set.disjoint_left.mp (hd (f i) (f j) (fun he => hij (hf he))) hx.1 hx.2
    rw [hfamily i,hfamily j,hz]
    exact Set.finite_empty
  obtain ⟨c,H,δ,hδ,hδhalf,hclass,hmarks,hgraph,hmap,htails⟩ :=
    actual_arbitrary_graph_original_loop_terminal_collars_private M (fun j : G => r j.val)
      (r u) (s u) hfinite hloop terminal haIncident hbClock
  exact actual_graph_fixed_terminal_collars_consume_interior_preparation_private M (r u) (s u) c P
    hP hbP H δ hδ hδhalf hclass hmarks hgraph hmap htails
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_original_aligned_disjoint_families_loop_relative_finite_preparation_private

namespace CurveComplex.HyperellipticModel
private theorem actual_original_graph_fixed_motion_transports_full_target_family_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (F T J : Finset (EssentialArcClass M))
    (hTF : T⊆F) (hJT : J⊆T)
    (r r0 : {w//w∈F} → EssentialMarkedArc M)
    (rT : {w//w∈T} → EssentialMarkedArc M)
    (hrT : ∀ w,Quotient.mk (essentialArcSetoid M) (rT w)=w.val)
    (hdT : ∀ w z,w≠z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (haligned0 : ∀ w : {w//w∈T},w.val∈J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (H : AmbientIsotopy S)
    (hm : ∀ t x,x∈M.cover.branch → H.map (t,x)=x)
    (hG : ∀ t x,x∈actualObjectTrace M r J → H.map (t,x)=x) :
    ∃ s : {w//w∈T} → EssentialMarkedArc M,
      (∀ w,Quotient.mk (essentialArcSetoid M) (s w)=w.val) ∧
      (∀ w z,w≠z → Disjoint (arcInterior M (s w)) (arcInterior M (s z))) ∧
      (∀ w : {w//w∈T},w.val∈J → r0 ⟨w.val,hTF w.property⟩=s w) ∧
      ∀ w,(s w).val.image=H.finalMap '' (rT w).val.image := by
  classical
  obtain ⟨s,hsclass,hsimage,hsd,hspreserve⟩ :=
    actual_marked_family_transport_fixing_graph M rT hdT H hm (actualObjectTrace M r J) hG
  have hslabel (w) : Quotient.mk (essentialArcSetoid M) (s w)=w.val := (hsclass w).trans (hrT w)
  let target : {w//w∈J} → EssentialMarkedArc M := fun w => rT ⟨w.val,hJT w.property⟩
  have htarget (w) : Quotient.mk (essentialArcSetoid M) (target w)=w.val := hrT _
  have hsourceImage : ∀ w : {w//w∈J},(s ⟨w.val,hJT w.property⟩).val.image=(target w).val.image := by
    intro w
    apply hspreserve
    intro x hx
    rw [←hgraph]
    refine mem_iUnion.mpr ⟨⟨w.val,hTF (hJT w.property)⟩,mem_iUnion.mpr ⟨w.property,?_⟩⟩
    rw [haligned0 ⟨w.val,hJT w.property⟩ w.property]
    exact hx
  obtain ⟨z,hzclass,hzd,hzrestrict,hzimage⟩ :=
    actual_family_literal_restriction_of_aligned_images M J T hJT s hslabel hsd target htarget hsourceImage
  refine ⟨z,hzclass,hzd,?_,?_⟩
  · intro w hw
    have heT : (⟨w.val,hJT hw⟩ : {w//w∈T})=w := Subtype.ext rfl
    have hz := hzrestrict ⟨w.val,hw⟩
    have hzw : z w=rT w := by simpa only [heT,target] using hz
    rw [hzw]
    exact haligned0 w hw
  · intro w
    exact (hzimage w).trans (hsimage w)
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_original_graph_fixed_motion_transports_full_target_family_private
