import CurveComplexGenusTwo.Intersection.SphereRegionTransport
import ClassificationSchoenflies.PolyhedralDiskNeighborhoods
import CurveComplexGenusTwo.Topology.ArcCounts.ActualNumericDegree
import CurveComplexGenusTwo.Filtration.Geometry.ActualBigonMarkNamedHeader
import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Topology.Smoothing.IncidentCircleRadialCoreStatement
import CurveComplexGenusTwo.Topology.Smoothing.PointedPlaneIsotopyProof
import CurveComplexGenusTwo.Topology.Smoothing.ConvexSectorChartHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Topology.Smoothing.SeedMarkedArcDependency
import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import Schoenflies.SkeletonAccess
import Schoenflies.SkeletonLocal
import CurveComplexGenusTwo.Filtration.Geometry.NonloopPuncture
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CurveComplexGenusTwo.Filtration.Geometry.ActualFaceMarksHeader
open Set Metric
open LeanEval.Topology.ClassificationOfSurfaces.Moise
namespace ClassificationSchoenflies
theorem exists_compact_connected_superset_in_open_connected
    (U : Set Plane) (hU : IsOpen U) (hcU : IsConnected U) {K : Set Plane}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKinside : K ⊆ U) :
    ∃ C : Set Plane,
      K ⊆ C ∧ IsCompact C ∧ IsConnected C ∧ C ⊆ U := by
  classical
  obtain ⟨delta, hdelta, hthick⟩ :=
    hKcompact.exists_cthickening_subset_open hU hKinside
  obtain ⟨centers, hcentersK, hcentersFinite, hcover⟩ :=
    hKcompact.finite_cover_balls (show 0 < delta / 4 by positivity)
  letI : Fintype centers := hcentersFinite.fintype
  let a : Plane := hKnonempty.some
  have haK : a ∈ K := hKnonempty.some_mem
  have haInside : a ∈ U := hKinside haK
  have hpathConnected : IsPathConnected U :=
    hU.isConnected_iff_isPathConnected.mp hcU
  let path (x : centers) : Path a x :=
    (hpathConnected.joinedIn a haInside x
      (hKinside (hcentersK x.2))).somePath
  let piece : Option centers → Set Plane
    | none => {a}
    | some x => range (path x) ∪ Metric.closedBall x (delta / 2)
  let C : Set Plane := ⋃ i : Option centers, piece i
  have hpieceCompact : ∀ i, IsCompact (piece i) := by
    intro i
    cases i with
    | none => exact isCompact_singleton
    | some x =>
        exact (isCompact_range (path x).continuous).union
          (isCompact_closedBall (x : Plane) (delta / 2))
  have hpieceConnected : ∀ i, IsConnected (piece i) := by
    intro i
    cases i with
    | none => exact isConnected_singleton
    | some x =>
        have hrange : IsConnected (range (path x)) :=
          isConnected_range (path x).continuous
        have hball : IsConnected (Metric.closedBall (x : Plane) (delta / 2)) :=
          (convex_closedBall (x : Plane) (delta / 2)).isConnected
            ⟨x, Metric.mem_closedBall_self (by positivity)⟩
        apply IsConnected.union
          (s := range (path x)) (t := Metric.closedBall x (delta / 2))
          (Hs := hrange) (Ht := hball)
        exact ⟨x, Path.target_mem_range (path x),
          Metric.mem_closedBall_self (by positivity)⟩
  have haPiece : ∀ i, a ∈ piece i := by
    intro i
    cases i with
    | none => exact Set.mem_singleton a
    | some x => exact Or.inl (Path.source_mem_range (path x))
  have hCcompact : IsCompact C := by
    exact isCompact_iUnion hpieceCompact
  have hCconnected : IsConnected C := by
    refine ⟨⟨a, Set.mem_iUnion.mpr ⟨none, haPiece none⟩⟩, ?_⟩
    apply isPreconnected_iUnion
    · exact ⟨a, Set.mem_iInter.mpr haPiece⟩
    · exact fun i => (hpieceConnected i).isPreconnected
  have hCinside : C ⊆ U := by
    intro y hy
    obtain ⟨i, hyPiece⟩ := Set.mem_iUnion.mp hy
    cases i with
    | none =>
        have hya : y = a := by simpa [piece] using hyPiece
        simpa [hya] using haInside
    | some x =>
        rcases hyPiece with hyPath | hyBall
        · obtain ⟨t, rfl⟩ := hyPath
          exact (hpathConnected.joinedIn a haInside x
            (hKinside (hcentersK x.2))).somePath_mem t
        · apply hthick
          apply Metric.closedBall_subset_cthickening (hcentersK x.2) delta
          exact Metric.closedBall_subset_closedBall (by nlinarith) hyBall
  have hKC : K ⊆ C := by
    intro x hxK
    have hxCover := hcover hxK
    obtain ⟨c, hcCenters, hxc⟩ := Set.mem_iUnion₂.mp hxCover
    let c' : centers := ⟨c, hcCenters⟩
    apply Set.mem_iUnion.mpr
    refine ⟨some c', ?_⟩
    apply Or.inr
    rw [Metric.mem_closedBall]
    have hdist := Metric.mem_ball.mp hxc
    nlinarith
  exact ⟨C, hKC, hCcompact, hCconnected, hCinside⟩

end ClassificationSchoenflies


namespace ClassificationSchoenflies
open Set Real
/-- Literal conversion of the classification circle parametrization to the
vendor's closed interval Jordan-loop parametrization. -/
theorem forest_jordan_circle_vendor_jordan (J : JordanCircle) :
    Schoenflies.IsJordanCurve J.carrier := by
  let f : ℝ → Schoenflies.Plane := fun t => J.parametrization (ClassificationJordanCurve.Arcs.param (2 * π * t))
  have hc : Continuous f := J.continuous.comp (ClassificationJordanCurve.Arcs.continuous_param.comp (by fun_prop))
  have hloop : Schoenflies.IsLoop f := by
    refine ⟨hc.continuousOn,?_,?_⟩
    · change J.parametrization (ClassificationJordanCurve.Arcs.param (2 * π * 0)) =
        J.parametrization (ClassificationJordanCurve.Arcs.param (2 * π * 1))
      simp only [mul_zero,mul_one]
      exact congrArg J.parametrization ((ClassificationJordanCurve.Arcs.param_periodic 0).symm.trans (by simp))
    · intro t ht u hu he
      have h := J.injective he
      obtain ⟨m,hm⟩ := ClassificationJordanCurve.Arcs.param_eq_iff.mp h
      have hp : (0 : ℝ) < 2 * π := by positivity
      have heq : t - u = (m : ℝ) := by nlinarith [hm]
      have hmlo : (-1 : ℝ) < m := by linarith [ht.1,ht.2,hu.1,hu.2]
      have hmhi : (m : ℝ) < 1 := by linarith [ht.1,ht.2,hu.1,hu.2]
      have hm0 : m = 0 := by
        have h1 : (-1 : ℤ) < m := by exact_mod_cast hmlo
        have h2 : m < (1 : ℤ) := by exact_mod_cast hmhi
        omega
      simp only [hm0,Int.cast_zero] at heq
      linarith
  refine ⟨f,hloop,?_⟩
  have himage : ClassificationJordanCurve.Arcs.param '' Set.Icc (0 : ℝ) (2 * π) = Set.univ := by
    simpa [ClassificationJordanCurve.Arcs.param_surjective.range_eq] using
      ClassificationJordanCurve.Arcs.param_periodic.image_Icc (by positivity : (0 : ℝ) < 2 * π) 0
  ext x
  constructor
  · rintro ⟨t,ht,rfl⟩
    exact Set.mem_range_self _
  · rintro ⟨z,rfl⟩
    have hz : z ∈ ClassificationJordanCurve.Arcs.param '' Set.Icc (0 : ℝ) (2 * π) := by rw [himage]; exact Set.mem_univ z
    obtain ⟨t,ht,he⟩ := hz
    refine ⟨t / (2 * π),?_,?_⟩
    · constructor
      · exact div_nonneg ht.1 (by positivity)
      · exact (div_le_one (by positivity : (0 : ℝ) < 2 * π)).2 ht.2
    · dsimp [f]
      rw [mul_div_cancel₀ _ (by positivity : (2 * π : ℝ) ≠ 0),he]

theorem forest_jordan_circle_vendor_regions (J : JordanCircle) :
    Schoenflies.inside J.carrier = J.inside ∧ Schoenflies.outside J.carrier = J.outside := by
  have heq (x : Schoenflies.Plane) (hx : x ∈ J.inside) : connectedComponentIn J.carrierᶜ x = J.inside :=
    (connectedComponentIn_eq hx).symm
  have heqO (x : Schoenflies.Plane) (hx : x ∈ J.outside) : connectedComponentIn J.carrierᶜ x = J.outside :=
    (connectedComponentIn_eq hx).symm
  have hi : Schoenflies.inside J.carrier = J.inside := by
    ext x
    constructor
    · intro hx
      rcases J.mem_inside_or_outside hx.1 with hxI | hxO
      · exact hxI
      · have hbounded := hx.2
        rw [heqO x hxO] at hbounded
        exact False.elim (J.outside_unbounded hbounded)
    · intro hx
      exact ⟨J.inside_subset_compl hx,by rw [heq x hx]; exact J.inside_bounded⟩
  refine ⟨hi,?_⟩
  ext x
  constructor
  · intro hx
    rcases J.mem_inside_or_outside hx.1 with hxI | hxO
    · exact False.elim (hx.2 (by rw [heq x hxI]; exact J.inside_bounded))
    · exact hxO
  · intro hx
    exact ⟨J.outside_subset_compl hx,by rw [heqO x hx]; exact J.outside_unbounded⟩
end ClassificationSchoenflies
namespace CurveComplex.HyperellipticModel
open Set
theorem forest_plane_open_puncture_connected {U : Set Schoenflies.Plane} (hU : IsOpen U)
      (hcU : IsConnected U) (p : Schoenflies.Plane) : IsConnected (U \ {p}) := by
    have hlocal : ∀ {U N : Set Schoenflies.Plane} {p : Schoenflies.Plane}, IsOpen U → IsConnected U →
              IsOpen N → p ∈ N → N ⊆ U → IsConnected (N \ {p}) → IsConnected (U \ {p}) := by
            intro U N p hU hcU hN hpN hNU hcN
            obtain ⟨x,hx⟩ := hcN.nonempty
            let C := connectedComponentIn (U \ {p}) x
            have hxU : x ∈ U \ {p} := ⟨hNU hx.1,hx.2⟩
            have hcC : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxU
            have hNC : N \ {p} ⊆ C := hcN.isPreconnected.subset_connectedComponentIn hx
              (fun y hy => ⟨hNU hy.1,hy.2⟩)
            have hCsub : C ⊆ U \ {p} := connectedComponentIn_subset _ _
            have hcomp : IsComplementComponent (Uᶜ ∪ {p}) C := by
              apply complementComponent_iff_componentIn.mpr
              refine ⟨x,?_,?_⟩
              · simpa only [mem_compl_iff,mem_union,not_or,not_not,mem_sdiff] using hxU
              · change connectedComponentIn (U \ {p}) x = _
                congr 1
                ext y
                simp [and_comm]
            have hclosed : IsClosed (Uᶜ ∪ {p}) := hU.isClosed_compl.union isClosed_singleton
            have hCopen : IsOpen C := complementComponent_open hclosed hcomp
            have heq : C ∪ {p} = C ∪ N := by
              ext y
              constructor
              · rintro (hy|hy)
                · exact Or.inl hy
                · exact Or.inr ((mem_singleton_iff.mp hy) ▸ hpN)
              · rintro (hy|hy)
                · exact Or.inl hy
                · by_cases hyp : y = p
                  · exact Or.inr (mem_singleton_iff.mpr hyp)
                  · exact Or.inl (hNC ⟨hy,hyp⟩)
            have hopen : IsOpen (C ∪ {p}) := heq ▸ hCopen.union hN
            have hfront : frontier C ⊆ Uᶜ ∪ {p} := complementComponent_frontier_subset hclosed hcomp
            have hall : U ⊆ C ∪ {p} := hcU.isPreconnected.subset_of_closure_inter_subset hopen
              ⟨x,hxU.1,Or.inl (mem_connectedComponentIn hxU)⟩ (by
                rintro y ⟨hy,hyU⟩
                rw [closure_union,isClosed_singleton.closure_eq] at hy
                rcases hy with hy|hy
                · by_cases hyC : y ∈ C
                  · exact Or.inl hyC
                  · have hf : y ∈ frontier C := by
                      rw [frontier,hCopen.interior_eq]
                      exact ⟨hy,hyC⟩
                    rcases hfront hf with hn|hp
                    · exact False.elim (hn hyU)
                    · exact Or.inr hp
                · exact Or.inr hy)
            have he : U \ {p} = C := by
              apply Subset.antisymm
              · intro y hy
                exact (hall hy.1).resolve_right hy.2
              · exact hCsub
            exact he.symm ▸ hcC
  
    by_cases hp : p ∈ U
    · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU p hp
      exact hlocal hU hcU Metric.isOpen_ball (Metric.mem_ball_self hr) hsub
        (Schoenflies.isConnected_ball_diff_singleton hr)
    · have he : U \ {p} = U := by
        ext x
        constructor
        · exact fun hx => hx.1
        · intro hx
          refine ⟨hx, ?_⟩
          intro he
          exact hp ((Set.mem_singleton_iff.mp he) ▸ hx)
      exact he.symm ▸ hcU
theorem forest_open_domain_jordan_exterior_connected (D0 K : Set Schoenflies.Plane)
      (hD0 : IsOpen D0) (hcD0 : IsConnected D0)
      (hK : Schoenflies.IsJordanCurve K) (hKin : K ⊆ D0)
      (hinside : Schoenflies.inside K ⊆ D0)
      (y : Schoenflies.Plane) (hyI : y ∈ D0) (hyO : y ∈ Schoenflies.outside K) :
      IsConnected (D0 ∩ Schoenflies.outside K) := by
    have hKs := Schoenflies.jordan_curve_theorem hK
    obtain ⟨f, hf, hfim⟩ := hK
    have hbaseK : f 0 ∈ K := hfim ▸ (show f 0 ∈ f '' (Set.Icc (0 : ℝ) 1) from
      ⟨0, Schoenflies.zero_mem_I, rfl⟩)
    let D : Set Schoenflies.Plane := D0 \ {f 0}
    have hDopen : IsOpen D := hD0.sdiff isClosed_singleton
    have hDconn : IsConnected D := forest_plane_open_puncture_connected hD0 hcD0 (f 0)
    have hbaseD : f 0 ∉ D := fun h => h.2 (Set.mem_singleton _)
    have hmiddle : f '' Set.Ioo (0 : ℝ) 1 ⊆ D := by
      rintro z ⟨t, ht, rfl⟩
      refine ⟨hKin (hfim ▸ (show f t ∈ f '' (Set.Icc (0 : ℝ) 1) from ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)), ?_⟩
      intro he
      have ht0 : t = 0 := hf.injOn ⟨ht.1.le, ht.2⟩ ⟨le_rfl, zero_lt_one⟩
        (Set.mem_singleton_iff.mp he)
      exact (ne_of_gt ht.1) ht0
    have hcut : D \ (f '' (Set.Icc (0 : ℝ) 1)) = D0 \ K := by
      rw [hfim]
      ext z
      constructor
      · exact fun hz => ⟨hz.1.1, hz.2⟩
      · intro hz
        refine ⟨⟨hz.1, ?_⟩, hz.2⟩
        intro he
        exact hz.2 ((Set.mem_singleton_iff.mp he).symm ▸ hbaseK)
    obtain ⟨zL, hzL, zR, hzR, hcov⟩ :=
      Schoenflies.actual_loop_domain_atMostTwo hf hDopen hDconn.isPreconnected hbaseD hmiddle
    rw [hcut] at hzL hzR hcov
    let A : Set Schoenflies.Plane := D0 \ K
    obtain ⟨x, hxI⟩ := hKs.isConnected_inside.nonempty
    have hxA : x ∈ A := ⟨hinside hxI, Schoenflies.inside_subset_compl hxI⟩
    have hyA : y ∈ A := ⟨hyI, Schoenflies.outside_subset_compl hyO⟩
    have hxi : connectedComponentIn A x ⊆ Schoenflies.inside K := by
      have hs : connectedComponentIn A x ⊆ connectedComponentIn Kᶜ x :=
        (isConnected_connectedComponentIn_iff.mpr hxA).isPreconnected.subset_connectedComponentIn
          (mem_connectedComponentIn hxA) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
      rwa [hKs.connectedComponentIn_eq_inside hxI] at hs
    have hyo : connectedComponentIn A y ⊆ Schoenflies.outside K := by
      have hs : connectedComponentIn A y ⊆ connectedComponentIn Kᶜ y :=
        (isConnected_connectedComponentIn_iff.mpr hyA).isPreconnected.subset_connectedComponentIn
          (mem_connectedComponentIn hyA) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
      rwa [hKs.connectedComponentIn_eq_outside hyO] at hs
    have hne : connectedComponentIn A x ≠ connectedComponentIn A y := by
      intro he
      exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
        (hxi (he.symm ▸ mem_connectedComponentIn hyA)) hyO
    have hcover := Schoenflies.covered_by_two_components_of_ne hcov hxA hyA hne
    have heq : D0 ∩ Schoenflies.outside K = connectedComponentIn A y := by
      apply Set.Subset.antisymm
      · intro z hz
        have hzA : z ∈ A := ⟨hz.1, Schoenflies.outside_subset_compl hz.2⟩
        rcases hcover z hzA with hzX | hzY
        · exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside (hxi hzX) hz.2)
        · exact hzY
      · intro z hz
        exact ⟨(connectedComponentIn_subset _ _ hz).1, hyo hz⟩
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr hyA


/-- A compact planar enclosure whose boundary avoids a connected actual site
also avoids its whole filled region when the chart puncture belongs to the site. -/
theorem forest_chart_enclosure_avoids_site
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (C : Set S) (hc : IsConnected C)
    (p : S) (hpC : p ∈ C) (K : Set Schoenflies.Plane) (hK : IsCompact K)
    (hbound : Disjoint (M.planeToSphere p '' frontier K) C) :
    Disjoint (M.planeToSphere p '' K) C := by
  letI : T2Space S := M.sphere.symm.t2Space
  let L := M.planeToSphere p '' K
  have hLc : IsClosed L := (hK.image (M.planeToSphere_isOpenEmbedding p).continuous).isClosed
  have hpL : p ∉ L := by
    rintro ⟨x,hx,he⟩
    exact M.planeToSphere_ne_p p x he
  have hfr : Disjoint (frontier L) C := by
    change Disjoint (frontier (M.planeToSphere p '' K)) C
    rw [← M.planeToSphere_image_frontier_of_compact p hK]
    exact hbound
  have hCout : C ⊆ Lᶜ := hc.isPreconnected.subset_of_closure_inter_subset hLc.isOpen_compl
    ⟨p,hpC,hpL⟩ (by
      intro x hx
      by_contra hn
      have hxf : x ∈ frontier Lᶜ := by
        rw [hLc.isOpen_compl.frontier_eq]
        exact ⟨hx.1,hn⟩
      rw [frontier_compl] at hxf
      exact Set.disjoint_left.mp hfr hxf hx.2)
  exact Set.disjoint_left.mpr (fun x hx hxC => hCout hxC hx)


/-- A literal compact subset of an actual complementary gap has a polygonal
filled enclosure wholly in that gap when the chart puncture is on the site. -/
theorem forest_actual_site_gap_enclosure
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (C D K : Set S) (hcC : IsConnected C)
    (hCc : IsCompact C) (hD : IsComplementComponent C D)
    (p : S) (hpC : p ∈ C) (hKc : IsCompact K) (hKn : K.Nonempty) (hKD : K ⊆ D) :
    ∃ Q : PolygonalCircle, K ⊆ M.planeToSphere p '' interior Q.closedRegion ∧
      M.planeToSphere p '' Q.closedRegion ⊆ D := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  let f := M.planeToSphere p
  have hf := M.planeToSphere_isOpenEmbedding p
  have hDrange : D ⊆ range f := by
    intro x hx
    have hxp : x ≠ p := fun he => hD.2.2.1 hx (he.symm ▸ hpC)
    refine ⟨M.puncturedPlane p ⟨x,hxp⟩,?_⟩
    exact congrArg Subtype.val ((M.puncturedPlane p).symm_apply_apply ⟨x,hxp⟩)
  have hKrange : K ⊆ range f := hKD.trans hDrange
  have hDpopen : IsOpen (f ⁻¹' D) := (complementComponent_open hCc.isClosed hD).preimage hf.continuous
  have hDpconn : IsConnected (f ⁻¹' D) := hD.2.1.preimage_of_isOpenMap hf.injective hf.isOpenMap hDrange
  have hKpc : IsCompact (f ⁻¹' K) := hf.isEmbedding.isInducing.isCompact_preimage' hKc hKrange
  have hKpn : (f ⁻¹' K).Nonempty := hKn.preimage' hKrange
  obtain ⟨B,hKB,hBc,hBconn,hBD⟩ := ClassificationSchoenflies.exists_compact_connected_superset_in_open_connected
    (f ⁻¹' D) hDpopen hDpconn hKpc hKpn (Set.preimage_mono hKD)
  let N : ClassificationSchoenflies.JordanCircle.FinitePolyhedralNeighborhood B (f ⁻¹' D) :=
    Classical.choice (ClassificationSchoenflies.JordanCircle.exists_finitePolyhedralNeighborhood hBc hDpopen hBD)
  obtain ⟨Q,_hf,hQambient,hCore,_hFrame⟩ := N.exists_outerBoundaryPolygonalCircle_of_connected hBconn
  have hBin : B ⊆ interior Q.closedRegion := by
    rw [Q.interior_closedRegion]
    exact (N.core_subset_coreComponent hBconn).trans hCore
  have hbound : Disjoint (f '' frontier Q.closedRegion) C := by
    rw [Q.frontier_closedRegion]
    apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hxC
    exact hD.2.2.1 (hQambient hz) hxC
  have hQavoid : Disjoint (f '' Q.closedRegion) C :=
    forest_chart_enclosure_avoids_site M C hcC p hpC Q.closedRegion Q.isCompact_closedRegion hbound
  have hQconn : IsConnected (f '' Q.closedRegion) :=
    Q.isConnected_closedRegion.image f hf.continuous.continuousOn
  have hKinside : K ⊆ f '' interior Q.closedRegion := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := hKrange hx
    exact ⟨z,hBin (hKB hx),rfl⟩
  obtain ⟨x,hxK⟩ := hKn
  have hxQ : x ∈ f '' Q.closedRegion := Set.image_mono interior_subset (hKinside hxK)
  have hQD : f '' Q.closedRegion ⊆ D := by
    have hh := hQconn.isPreconnected.subset_connectedComponentIn hxQ
      (fun y hy h => Set.disjoint_left.mp hQavoid hy h)
    change f '' Q.closedRegion ⊆ connectedComponentIn Cᶜ x at hh
    obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hD
    have hxcomp := he ▸ hKD hxK
    rw [← connectedComponentIn_eq hxcomp,← he] at hh
    exact hh
  exact ⟨Q,hKinside,hQD⟩


/-- Within a literal component gap, a filled polygonal enclosure of all graph
points leaves a connected exterior meeting every full face touching the site. -/
theorem forest_unique_full_face_in_site_gap
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (G C D U V : Set S)
    (hcC : IsConnected C) (hCc : IsCompact C) (hCG : C ⊆ G)
    (hD : IsComplementComponent C D) (hGc : IsClosed G)
    (hKc : IsCompact (G ∩ D))
    (hU : IsComplementComponent G U) (hV : IsComplementComponent G V)
    (hUD : U ⊆ D) (hVD : V ⊆ D)
    (htU : (frontier U ∩ C).Nonempty) (htV : (frontier V ∩ C).Nonempty) : U = V := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  by_cases hKn : (G ∩ D).Nonempty
  · obtain ⟨p,hpC⟩ := hcC.nonempty
    obtain ⟨Q,hKQ,hQD⟩ := forest_actual_site_gap_enclosure M C D (G ∩ D) hcC hCc hD p hpC hKc hKn Set.inter_subset_right
    let f := M.planeToSphere p
    have hf := M.planeToSphere_isOpenEmbedding p
    let K := f '' Q.closedRegion
    have hKclosed : IsClosed K := (Q.isCompact_closedRegion.image hf.continuous).isClosed
    have hKC : Disjoint K C := Set.disjoint_left.mpr (fun x hx hxC => hD.2.2.1 (hQD hx) hxC)
    have hDopen : IsOpen D := complementComponent_open hCc.isClosed hD
    have hDrange : D ⊆ range f := by
      intro x hx
      have hxp : x ≠ p := fun he => hD.2.2.1 hx (he.symm ▸ hpC)
      exact ⟨M.puncturedPlane p ⟨x,hxp⟩,congrArg Subtype.val
        ((M.puncturedPlane p).symm_apply_apply ⟨x,hxp⟩)⟩
    have hDpconn : IsConnected (f ⁻¹' D) := hD.2.1.preimage_of_isOpenMap hf.injective hf.isOpenMap hDrange
    have hDpop : IsOpen (f ⁻¹' D) := hDopen.preimage hf.continuous
    have houterMeet : ∀ W, IsComplementComponent G W → W ⊆ D →
        (frontier W ∩ C).Nonempty → (W ∩ Kᶜ).Nonempty := by
      intro W hW hWD htouch
      obtain ⟨z,hzF,hzC⟩ := htouch
      have hzK : z ∈ Kᶜ := fun h => Set.disjoint_left.mp hKC h hzC
      obtain ⟨x,hxK,hxW⟩ := Set.Nonempty.of_closure
        ⟨z,hKclosed.isOpen_compl.inter_closure ⟨hzK,frontier_subset_closure hzF⟩⟩
      exact ⟨x,hxW,hxK⟩
    obtain ⟨x,hxU,hxK⟩ := houterMeet U hU hUD htU
    obtain ⟨y,hyEq⟩ := hDrange (hUD hxU)
    have hyD : y ∈ f ⁻¹' D := by
      change f y ∈ D
      rw [hyEq]
      exact hUD hxU
    have hxUplane : f y ∈ U := hyEq.symm ▸ hxU
    have hxKplane : f y ∉ K := hyEq.symm ▸ hxK
    have hyOut : y ∈ Schoenflies.outside Q.carrier := by
      have hn : y ∉ Q.closedRegion := fun h => hxKplane ⟨y,h,rfl⟩
      rw [Q.closedRegion_eq_union] at hn
      have hyExt : y ∈ Q.exteriorRegion := by
        have hyc : y ∉ Q.carrier := fun h => hn (Or.inr h)
        have hh : y ∈ Q.interiorRegion ∪ Q.exteriorRegion := Q.interior_union_exterior.symm ▸ hyc
        exact hh.resolve_left (fun h => hn (Or.inl h))
      simpa only [← Q.outside_toJordanCircle,← (ClassificationSchoenflies.forest_jordan_circle_vendor_regions Q.toJordanCircle).2,Q.carrier_toJordanCircle] using hyExt
    have hcurve : Schoenflies.IsJordanCurve Q.carrier := by
      exact by simpa only [Q.carrier_toJordanCircle] using ClassificationSchoenflies.forest_jordan_circle_vendor_jordan Q.toJordanCircle
    have hinside : Schoenflies.inside Q.carrier ⊆ f ⁻¹' D := by
      intro z hz
      have hzQ : z ∈ Q.closedRegion := by
        rw [Q.closedRegion_eq_union]
        left
        have hh : z ∈ Schoenflies.inside Q.toJordanCircle.carrier := by simpa only [Q.carrier_toJordanCircle] using hz
        rw [(ClassificationSchoenflies.forest_jordan_circle_vendor_regions Q.toJordanCircle).1,Q.inside_toJordanCircle] at hh
        exact hh
      exact hQD ⟨z,hzQ,rfl⟩
    have hcurvein : Q.carrier ⊆ f ⁻¹' D := fun z hz => hQD ⟨z,by rw [Q.closedRegion_eq_union]; exact Or.inr hz,rfl⟩
    have hOc := forest_open_domain_jordan_exterior_connected (f ⁻¹' D) Q.carrier
      hDpop hDpconn hcurve hcurvein hinside y hyD hyOut
    let O := f '' ((f ⁻¹' D) ∩ Schoenflies.outside Q.carrier)
    have hOconn : IsConnected O := hOc.image f hf.continuous.continuousOn
    have hOeq : O = D \ K := by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        refine ⟨hw.1,?_⟩
        rintro ⟨t,ht,he⟩
        have htw := hf.injective he
        subst t
        have hExt : w ∈ Q.exteriorRegion := by
          have hh : w ∈ Schoenflies.outside Q.toJordanCircle.carrier := by simpa only [Q.carrier_toJordanCircle] using hw.2
          rw [(ClassificationSchoenflies.forest_jordan_circle_vendor_regions Q.toJordanCircle).2,Q.outside_toJordanCircle] at hh
          exact hh
        rw [Q.closedRegion_eq_union] at ht
        rcases ht with ht | ht
        · exact Set.disjoint_left.mp Q.disjoint_interior_exterior ht hExt
        · have hnc : w ∉ Q.carrier := by
            change w ∈ Q.carrierᶜ
            rw [← Q.interior_union_exterior]
            exact Or.inr hExt
          exact hnc ht
      · rintro ⟨hzD,hzK⟩
        obtain ⟨w,hwEq⟩ := hDrange hzD
        refine ⟨w,⟨?_,?_⟩,hwEq⟩
        · change f w ∈ D
          rw [hwEq]
          exact hzD
        have hwK : f w ∉ K := hwEq.symm ▸ hzK
        have hn : w ∉ Q.closedRegion := fun h => hwK ⟨w,h,rfl⟩
        have hext : w ∈ Q.exteriorRegion := by
          rw [Q.closedRegion_eq_union] at hn
          have hc : w ∉ Q.carrier := fun h => hn (Or.inr h)
          have hh : w ∈ Q.interiorRegion ∪ Q.exteriorRegion := Q.interior_union_exterior.symm ▸ hc
          exact hh.resolve_left (fun h => hn (Or.inl h))
        simpa only [← Q.outside_toJordanCircle,← (ClassificationSchoenflies.forest_jordan_circle_vendor_regions Q.toJordanCircle).2,Q.carrier_toJordanCircle] using hext
    have hOG : O ⊆ Gᶜ := by
      rw [hOeq]
      intro z hz hzg
      exact hz.2 (Set.image_mono interior_subset (hKQ ⟨hzg,hz.1⟩))
    have hxO : f y ∈ O := hOeq.symm ▸ (show f y ∈ D \ K from ⟨hUD hxUplane,hxKplane⟩)
    have hOU : O ⊆ U := by
      have hh := hOconn.isPreconnected.subset_connectedComponentIn hxO hOG
      obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hU
      have hxu := he ▸ hxUplane
      rw [← connectedComponentIn_eq hxu,← he] at hh
      exact hh
    obtain ⟨z,hzV,hzK⟩ := houterMeet V hV hVD htV
    have hzO : z ∈ O := hOeq.symm ▸ (show z ∈ D \ K from ⟨hVD hzV,hzK⟩)
    by_contra hne
    exact Set.disjoint_left.mp (complementComponents_disjoint hU hV hne) (hOU hzO) hzV
  · have hDG : D ⊆ Gᶜ := by
      intro x hx hxG
      exact hKn ⟨x,hxG,hx⟩
    have hUeq : U = D := by
      apply Set.Subset.antisymm hUD
      obtain ⟨x,hxU⟩ := hU.1
      have hh := hD.2.1.isPreconnected.subset_connectedComponentIn (hUD hxU) hDG
      obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hU
      have hx := he ▸ hxU
      rw [← connectedComponentIn_eq hx,← he] at hh
      exact hh
    have hVeq : V = D := by
      apply Set.Subset.antisymm hVD
      obtain ⟨x,hxV⟩ := hV.1
      have hh := hD.2.1.isPreconnected.subset_connectedComponentIn (hVD hxV) hDG
      obtain ⟨w,hw,he⟩ := complementComponent_iff_componentIn.mp hV
      have hx := he ▸ hxV
      rw [← connectedComponentIn_eq hx,← he] at hh
      exact hh
    exact hUeq.trans hVeq.symm

end CurveComplex.HyperellipticModel
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Actual faces contacting different connected graph components consume at
most componentCount - 1 holes. The component membership is geometric;
no injection, incidence count, Euler relation, or charge budget is assumed. -/
theorem actual_cross_component_faces_card_le_components_sub_one
    (M : HyperellipticModel E S) (σ : Finset (EssentialArcClass M))
    (hσ : σ.Nonempty)
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (F : Finset (Set S))
    (hF : ∀ U ∈ F, IsComplementComponent (⋃ i, (r i).val.image) U)
    (hcross : ∀ U ∈ F, ∃ i j : {v // v ∈ σ},
      connectedComponentIn (⋃ k, (r k).val.image) ((r i).val.map 0) ≠
        connectedComponentIn (⋃ k, (r k).val.image) ((r j).val.map 0) ∧
      (frontier U ∩ (r i).val.image).Nonempty ∧
      (frontier U ∩ (r j).val.image).Nonempty) :
    F.card ≤ (Finset.univ.image (fun i : {v // v ∈ σ} =>
      connectedComponentIn (⋃ k, (r k).val.image) ((r i).val.map 0))).card - 1 := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  let G := ⋃ k, (r k).val.image
  let components : Finset (Set S) := Finset.univ.image (fun i : {v // v ∈ σ} =>
    connectedComponentIn G ((r i).val.map 0))
  let Comp := {C // C ∈ components}
  let Face := {U // U ∈ F}
  let Rel : Comp ⊕ Face → Comp ⊕ Face → Prop := fun x y =>
    match x, y with
    | Sum.inl C, Sum.inr U => (frontier U.val ∩ C.val).Nonempty
    | _, _ => False
  let H := SimpleGraph.fromRel Rel
  have hAdj (C : Comp) (U : Face) :
      H.Adj (Sum.inl C) (Sum.inr U) ↔ (frontier U.val ∩ C.val).Nonempty := by
    simp [H, Rel]
  have hwhole (i : {v // v ∈ σ}) :
      (r i).val.image ⊆ connectedComponentIn G ((r i).val.map 0) :=
    (markedArc_image_connected (r i).val).isPreconnected.subset_connectedComponentIn
      (Set.mem_range_self 0) (fun z hz => Set.mem_iUnion.mpr ⟨i, hz⟩)
  have htwo : ∀ U : Face, ∃ C D : Comp, C ≠ D ∧
      H.Adj (Sum.inl C) (Sum.inr U) ∧ H.Adj (Sum.inl D) (Sum.inr U) := by
    intro U
    obtain ⟨i, j, hne, hi, hj⟩ := hcross U.val U.property
    let C : Comp := ⟨connectedComponentIn G ((r i).val.map 0),
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    let D : Comp := ⟨connectedComponentIn G ((r j).val.map 0),
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    refine ⟨C, D, (fun he => hne (congrArg Subtype.val he)), ?_, ?_⟩
    · apply (hAdj C U).mpr
      obtain ⟨z, hzU, hzi⟩ := hi
      exact ⟨z, hzU, hwhole i hzi⟩
    · apply (hAdj D U).mpr
      obtain ⟨z, hzU, hzj⟩ := hj
      exact ⟨z, hzU, hwhole j hzj⟩
  have hsites : ∀ C : Comp, IsConnected C.val ∧ IsCompact C.val ∧ C.val ⊆ G := by
    intro C
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp C.property
    have hstart : (r v).val.map 0 ∈ G := Set.mem_iUnion.mpr ⟨v, Set.mem_range_self 0⟩
    have hconn : IsConnected C.val := hv ▸ isConnected_connectedComponentIn_iff.mpr hstart
    have hsub : C.val ⊆ G := hv ▸ connectedComponentIn_subset G ((r v).val.map 0)
    let I := Finset.univ.filter (fun i : {v // v ∈ σ} => (r i).val.map 0 ∈ C.val)
    have htrace : C.val = ⋃ i ∈ I, (r i).val.image := by
      apply Set.Subset.antisymm
      · intro z hz
        obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (hsub hz)
        have hpath := (markedArc_image_connected (r i).val).isPreconnected.subset_connectedComponentIn
          hzi (show (r i).val.image ⊆ G from fun w hw => Set.mem_iUnion.mpr ⟨i, hw⟩)
        have hsame : connectedComponentIn G z = C.val := by
          rw [← hv]
          exact (connectedComponentIn_eq (hv.symm ▸ hz)).symm
        have histart : (r i).val.map 0 ∈ C.val := by
          rw [← hsame]
          exact hpath (Set.mem_range_self 0)
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, histart⟩, hzi⟩⟩
      · intro z hz
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
        obtain ⟨hiI, hzi⟩ := Set.mem_iUnion.mp hi
        have histart := (Finset.mem_filter.mp hiI).2
        have hsame : connectedComponentIn G ((r i).val.map 0) = C.val := by
          rw [← hv]
          exact (connectedComponentIn_eq (hv.symm ▸ histart)).symm
        exact hsame ▸ hwhole i hzi
    have hcompact : IsCompact C.val := by
      rw [htrace]
      exact I.finite_toSet.isCompact_biUnion (fun i _ => markedArc_image_compact (r i).val)
    exact ⟨hconn, hcompact, hsub⟩
  have hsites_disjoint : ∀ C D : Comp, C ≠ D → Disjoint C.val D.val := by
    intro C D hne
    apply Set.disjoint_left.mpr
    intro x hxC hxD
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp C.property
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp D.property
    have hVC := connectedComponentIn_eq (hv.symm ▸ hxC)
    have hWD := connectedComponentIn_eq (hw.symm ▸ hxD)
    exact hne (Subtype.ext (hv.symm.trans (hVC.trans (hWD.symm.trans hw))))
  have hsites_cover : G = ⋃ C : Comp, C.val := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hx
      let C : Comp := ⟨connectedComponentIn G ((r i).val.map 0),
        Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
      exact Set.mem_iUnion.mpr ⟨C,hwhole i hxi⟩
    · intro x hx
      obtain ⟨C,hxC⟩ := Set.mem_iUnion.mp hx
      exact (hsites C).2.2 hxC
  have hGclosed : IsClosed G := isClosed_iUnion_of_finite
    (fun i => (markedArc_image_compact (r i).val).isClosed)
  have hface_frontier_sites (U : Face) : frontier U.val ⊆ ⋃ C : Comp, C.val := by
    rw [← hsites_cover]
    exact complementComponent_frontier_subset hGclosed (hF U.val U.property)
  have hface_open (U : Face) : IsOpen U.val :=
    complementComponent_open hGclosed (hF U.val U.property)
  have hface_in_site_gap (C : Comp) (U : Face) (x : S) (hx : x ∈ U.val) :
      U.val ⊆ connectedComponentIn C.valᶜ x := by
    exact (hF U.val U.property).2.1.isPreconnected.subset_connectedComponentIn hx
      (fun z hz h => (hF U.val U.property).2.2.1 hz ((hsites C).2.2 h))
  have hcomponent_closed (C : Comp) : IsClosed C.val := (hsites C).2.1.isClosed
  have hsite_face_disjoint (C : Comp) (U : Face) : Disjoint C.val U.val := by
    apply Set.disjoint_left.mpr
    intro x hxC hxU
    exact (hF U.val U.property).2.2.1 hxU ((hsites C).2.2 hxC)
  have hface_contact_closure (C : Comp) (U : Face) :
      (frontier U.val ∩ C.val).Nonempty ↔ (closure U.val ∩ C.val).Nonempty := by
    constructor
    · rintro ⟨x,hxF,hxC⟩
      exact ⟨x,frontier_subset_closure hxF,hxC⟩
    · rintro ⟨x,hxCl,hxC⟩
      refine ⟨x,?_,hxC⟩
      rw [(hface_open U).frontier_eq]
      exact ⟨hxCl,fun hx => Set.disjoint_left.mp (hsite_face_disjoint C U) hxC hx⟩
  have hsite_in_other_gap (C D : Comp) (hCD : C ≠ D) (x : S) (hx : x ∈ D.val) :
      D.val ⊆ connectedComponentIn C.valᶜ x := by
    exact (hsites D).1.isPreconnected.subset_connectedComponentIn hx
      (fun z hz hc => Set.disjoint_left.mp (hsites_disjoint C D hCD) hc hz)
  have hgap_contact_transport (C D : Comp) (hCD : C ≠ D) (U : Face)
      (hcontact : (frontier U.val ∩ D.val).Nonempty)
      (x : S) (hx : x ∈ D.val) :
      U.val ⊆ connectedComponentIn C.valᶜ x := by
    obtain ⟨z,hzU,hzD⟩ := hcontact
    let W := connectedComponentIn C.valᶜ x
    have hxC : x ∈ C.valᶜ := fun h => Set.disjoint_left.mp (hsites_disjoint C D hCD) h hx
    have hW : IsComplementComponent C.val W := complementComponent_iff_componentIn.mpr ⟨x,hxC,rfl⟩
    have hWopen : IsOpen W := complementComponent_open (hcomponent_closed C) hW
    have hzW : z ∈ W := hsite_in_other_gap C D hCD x hx hzD
    obtain ⟨y,hyW,hyU⟩ := Set.Nonempty.of_closure
      ⟨z,hWopen.inter_closure ⟨hzW,frontier_subset_closure hzU⟩⟩
    have hh := hface_in_site_gap C U y hyU
    have he : connectedComponentIn C.valᶜ y = W := by
      exact (connectedComponentIn_eq hyW).symm
    change U.val ⊆ W
    exact he ▸ hh
  have hface_closure_remove_site_connected (C : Comp) (U : Face) :
      IsConnected (closure U.val \ C.val) := by
    apply (hF U.val U.property).2.1.subset_closure
    · intro x hx
      exact ⟨subset_closure hx,fun h => Set.disjoint_left.mp (hsite_face_disjoint C U) h hx⟩
    · exact Set.sdiff_subset
  have hcontact_connected_union_avoids_site (C D : Comp) (hCD : C ≠ D) (U : Face)
      (hcontact : (frontier U.val ∩ D.val).Nonempty) :
      IsConnected (D.val ∪ (closure U.val \ C.val)) ∧
      D.val ∪ (closure U.val \ C.val) ⊆ C.valᶜ := by
    obtain ⟨z,hzU,hzD⟩ := hcontact
    have hznot : z ∉ C.val := fun h => Set.disjoint_left.mp (hsites_disjoint C D hCD) h hzD
    refine ⟨(hsites D).1.union ⟨z,hzD,frontier_subset_closure hzU,hznot⟩
      (hface_closure_remove_site_connected C U),?_⟩
    rintro x (hx | hx)
    · exact fun h => Set.disjoint_left.mp (hsites_disjoint C D hCD) h hx
    · exact hx.2
  have hgap_graph_compact (C : Comp) (D : Set S) (hD : IsComplementComponent C.val D) :
      IsCompact (G ∩ D) := by
    let I := Finset.univ.filter (fun B : Comp => B.val ⊆ D)
    have heq : G ∩ D = ⋃ B ∈ I, B.val := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨B,hxB⟩ := Set.mem_iUnion.mp (hsites_cover ▸ hx.1)
        have hBC : B ≠ C := by
          intro he
          exact hD.2.2.1 hx.2 (he ▸ hxB)
        have hBD : B.val ⊆ D := by
          have hh := hsite_in_other_gap C B hBC.symm x hxB
          obtain ⟨w,hw,hd⟩ := complementComponent_iff_componentIn.mp hD
          have hxcomp := hd ▸ hx.2
          rw [← connectedComponentIn_eq hxcomp,← hd] at hh
          exact hh
        exact Set.mem_iUnion.mpr ⟨B,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBD⟩,hxB⟩⟩
      · intro x hx
        obtain ⟨B,hx⟩ := Set.mem_iUnion.mp hx
        obtain ⟨hBI,hxB⟩ := Set.mem_iUnion.mp hx
        exact ⟨(hsites B).2.2 hxB,(Finset.mem_filter.mp hBI).2 hxB⟩
    rw [heq]
    exact I.finite_toSet.isCompact_biUnion (fun B _ => (hsites B).2.1)
  have hgap_face_unique (C : Comp) (D : Set S) (hD : IsComplementComponent C.val D)
      (U V : Face) (hUD : U.val ⊆ D) (hVD : V.val ⊆ D)
      (htU : (frontier U.val ∩ C.val).Nonempty) (htV : (frontier V.val ∩ C.val).Nonempty) : U = V := by
    apply Subtype.ext
    exact forest_unique_full_face_in_site_gap M G C.val D U.val V.val (hsites C).1 (hsites C).2.1
      (hsites C).2.2 hD hGclosed (hgap_graph_compact C D hD)
      (hF U.val U.property) (hF V.val V.property) hUD hVD htU htV
  have hpuncture_plane {U : Set Schoenflies.Plane} (hU : IsOpen U)
      (hcU : IsConnected U) (p : Schoenflies.Plane) : IsConnected (U \ {p}) := by
    have hlocal : ∀ {U N : Set Schoenflies.Plane} {p : Schoenflies.Plane}, IsOpen U → IsConnected U →
              IsOpen N → p ∈ N → N ⊆ U → IsConnected (N \ {p}) → IsConnected (U \ {p}) := by
            intro U N p hU hcU hN hpN hNU hcN
            obtain ⟨x,hx⟩ := hcN.nonempty
            let C := connectedComponentIn (U \ {p}) x
            have hxU : x ∈ U \ {p} := ⟨hNU hx.1,hx.2⟩
            have hcC : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxU
            have hNC : N \ {p} ⊆ C := hcN.isPreconnected.subset_connectedComponentIn hx
              (fun y hy => ⟨hNU hy.1,hy.2⟩)
            have hCsub : C ⊆ U \ {p} := connectedComponentIn_subset _ _
            have hcomp : IsComplementComponent (Uᶜ ∪ {p}) C := by
              apply complementComponent_iff_componentIn.mpr
              refine ⟨x,?_,?_⟩
              · simpa only [mem_compl_iff,mem_union,not_or,not_not,mem_sdiff] using hxU
              · change connectedComponentIn (U \ {p}) x = _
                congr 1
                ext y
                simp [and_comm]
            have hclosed : IsClosed (Uᶜ ∪ {p}) := hU.isClosed_compl.union isClosed_singleton
            have hCopen : IsOpen C := complementComponent_open hclosed hcomp
            have heq : C ∪ {p} = C ∪ N := by
              ext y
              constructor
              · rintro (hy|hy)
                · exact Or.inl hy
                · exact Or.inr ((mem_singleton_iff.mp hy) ▸ hpN)
              · rintro (hy|hy)
                · exact Or.inl hy
                · by_cases hyp : y = p
                  · exact Or.inr (mem_singleton_iff.mpr hyp)
                  · exact Or.inl (hNC ⟨hy,hyp⟩)
            have hopen : IsOpen (C ∪ {p}) := heq ▸ hCopen.union hN
            have hfront : frontier C ⊆ Uᶜ ∪ {p} := complementComponent_frontier_subset hclosed hcomp
            have hall : U ⊆ C ∪ {p} := hcU.isPreconnected.subset_of_closure_inter_subset hopen
              ⟨x,hxU.1,Or.inl (mem_connectedComponentIn hxU)⟩ (by
                rintro y ⟨hy,hyU⟩
                rw [closure_union,isClosed_singleton.closure_eq] at hy
                rcases hy with hy|hy
                · by_cases hyC : y ∈ C
                  · exact Or.inl hyC
                  · have hf : y ∈ frontier C := by
                      rw [frontier,hCopen.interior_eq]
                      exact ⟨hy,hyC⟩
                    rcases hfront hf with hn|hp
                    · exact False.elim (hn hyU)
                    · exact Or.inr hp
                · exact Or.inr hy)
            have he : U \ {p} = C := by
              apply Subset.antisymm
              · intro y hy
                exact (hall hy.1).resolve_right hy.2
              · exact hCsub
            exact he.symm ▸ hcC
  
    by_cases hp : p ∈ U
    · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU p hp
      exact hlocal hU hcU Metric.isOpen_ball (Metric.mem_ball_self hr) hsub
        (Schoenflies.isConnected_ball_diff_singleton hr)
    · have he : U \ {p} = U := by
        ext x
        constructor
        · exact fun hx => hx.1
        · intro hx
          refine ⟨hx, ?_⟩
          intro he
          exact hp ((Set.mem_singleton_iff.mp he) ▸ hx)
      exact he.symm ▸ hcU
  have hnested_annulus (C K : Set Schoenflies.Plane)
      (hC : Schoenflies.IsJordanCurve C) (hK : Schoenflies.IsJordanCurve K)
      (hKin : K ⊆ Schoenflies.inside C) :
      IsConnected (Schoenflies.inside C ∩ Schoenflies.outside K) := by
    have hCs := Schoenflies.jordan_curve_theorem hC
    have hKs := Schoenflies.jordan_curve_theorem hK
    have hinside : Schoenflies.inside K ⊆ Schoenflies.inside C :=
      CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside hCs hKs
        (fun z hz => Or.inl (hKin hz))
    obtain ⟨f, hf, hfim⟩ := hK
    have hbaseK : f 0 ∈ K := hfim ▸ (show f 0 ∈ f '' (Set.Icc (0 : ℝ) 1) from
      ⟨0, Schoenflies.zero_mem_I, rfl⟩)
    let D : Set Schoenflies.Plane := Schoenflies.inside C \ {f 0}
    have hDopen : IsOpen D := hCs.isOpen_inside.sdiff isClosed_singleton
    have hDconn : IsConnected D := hpuncture_plane hCs.isOpen_inside hCs.isConnected_inside (f 0)
    have hbaseD : f 0 ∉ D := fun h => h.2 (Set.mem_singleton _)
    have hmiddle : f '' Set.Ioo (0 : ℝ) 1 ⊆ D := by
      rintro z ⟨t, ht, rfl⟩
      refine ⟨hKin (hfim ▸ (show f t ∈ f '' (Set.Icc (0 : ℝ) 1) from ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)), ?_⟩
      intro he
      have ht0 : t = 0 := hf.injOn ⟨ht.1.le, ht.2⟩ ⟨le_rfl, zero_lt_one⟩
        (Set.mem_singleton_iff.mp he)
      exact (ne_of_gt ht.1) ht0
    have hcut : D \ (f '' (Set.Icc (0 : ℝ) 1)) = Schoenflies.inside C \ K := by
      rw [hfim]
      ext z
      constructor
      · exact fun hz => ⟨hz.1.1, hz.2⟩
      · intro hz
        refine ⟨⟨hz.1, ?_⟩, hz.2⟩
        intro he
        exact hz.2 ((Set.mem_singleton_iff.mp he).symm ▸ hbaseK)
    obtain ⟨zL, hzL, zR, hzR, hcov⟩ :=
      Schoenflies.actual_loop_domain_atMostTwo hf hDopen hDconn.isPreconnected hbaseD hmiddle
    rw [hcut] at hzL hzR hcov
    let A : Set Schoenflies.Plane := Schoenflies.inside C \ K
    obtain ⟨x, hxI⟩ := hKs.isConnected_inside.nonempty
    have hxA : x ∈ A := ⟨hinside hxI, Schoenflies.inside_subset_compl hxI⟩
    obtain ⟨q, hqC⟩ := hC.nonempty
    have hqnotK : q ∉ K := fun he => Schoenflies.inside_subset_compl (hKin he) hqC
    have hqnotI : q ∉ Schoenflies.inside K := fun he => Schoenflies.inside_subset_compl (hinside he) hqC
    have hqO : q ∈ Schoenflies.outside K := by
      have hcover : q ∈ Schoenflies.inside K ∪ Schoenflies.outside K := by
        rw [Schoenflies.inside_union_outside]
        exact hqnotK
      exact hcover.resolve_left hqnotI
    have hqcl : q ∈ closure (Schoenflies.inside C) := by
      apply frontier_subset_closure
      rw [hCs.frontier_inside]
      exact hqC
    obtain ⟨y, hyO, hyI⟩ := mem_closure_iff.mp hqcl (Schoenflies.outside K) hKs.isOpen_outside hqO
    have hyA : y ∈ A := ⟨hyI, Schoenflies.outside_subset_compl hyO⟩
    have hxi : connectedComponentIn A x ⊆ Schoenflies.inside K := by
      have hs : connectedComponentIn A x ⊆ connectedComponentIn Kᶜ x :=
        (isConnected_connectedComponentIn_iff.mpr hxA).isPreconnected.subset_connectedComponentIn
          (mem_connectedComponentIn hxA) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
      rwa [hKs.connectedComponentIn_eq_inside hxI] at hs
    have hyo : connectedComponentIn A y ⊆ Schoenflies.outside K := by
      have hs : connectedComponentIn A y ⊆ connectedComponentIn Kᶜ y :=
        (isConnected_connectedComponentIn_iff.mpr hyA).isPreconnected.subset_connectedComponentIn
          (mem_connectedComponentIn hyA) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
      rwa [hKs.connectedComponentIn_eq_outside hyO] at hs
    have hne : connectedComponentIn A x ≠ connectedComponentIn A y := by
      intro he
      exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
        (hxi (he.symm ▸ mem_connectedComponentIn hyA)) hyO
    have hcover := Schoenflies.covered_by_two_components_of_ne hcov hxA hyA hne
    have heq : Schoenflies.inside C ∩ Schoenflies.outside K = connectedComponentIn A y := by
      apply Set.Subset.antisymm
      · intro z hz
        have hzA : z ∈ A := ⟨hz.1, Schoenflies.outside_subset_compl hz.2⟩
        rcases hcover z hzA with hzX | hzY
        · exact False.elim (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside (hxi hzX) hz.2)
        · exact hzY
      · intro z hz
        exact ⟨(connectedComponentIn_subset _ _ hz).1, hyo hz⟩
    rw [heq]
    exact isConnected_connectedComponentIn_iff.mpr hyA
  let sitePoint (C : Comp) : S := (hsites C).1.nonempty.some
  have hsitePoint (C : Comp) : sitePoint C ∈ C.val := (hsites C).1.nonempty.some_mem
  let facePoint (U : Face) : S := (hF U.val U.property).1.some
  have hfacePoint (U : Face) : facePoint U ∈ U.val := (hF U.val U.property).1.some_mem
  let point : Comp ⊕ Face → S := Sum.elim sitePoint facePoint
  let gap (C : Comp) (v : Comp ⊕ Face) := connectedComponentIn C.valᶜ (point v)
  have hgap_adj (C : Comp) (v w : Comp ⊕ Face) (hv : v ≠ Sum.inl C)
      (hw : w ≠ Sum.inl C) (hvw : H.Adj v w) : gap C v = gap C w := by
    have hforward (D : Comp) (U : Face) (hDC : D ≠ C)
        (hadj : H.Adj (Sum.inl D) (Sum.inr U)) : gap C (Sum.inl D) = gap C (Sum.inr U) := by
      have hc := (hAdj D U).mp hadj
      have hsub := hgap_contact_transport C D hDC.symm U hc (sitePoint D) (hsitePoint D)
      have hp := hsub (hfacePoint U)
      exact connectedComponentIn_eq hp
    cases v with
    | inl D =>
      cases w with
      | inl B => simp [H,Rel] at hvw
      | inr U => exact hforward D U (fun he => hv (congrArg Sum.inl he)) hvw
    | inr U =>
      cases w with
      | inl D => exact (hforward D U (fun he => hw (congrArg Sum.inl he)) hvw.symm).symm
      | inr V => simp [H,Rel] at hvw
  have hgap_walk (C : Comp) {v w : Comp ⊕ Face} (p : H.Walk v w)
      (havoid : Sum.inl C ∉ p.support) : gap C v = gap C w := by
    induction p with
    | nil => rfl
    | @cons v u w hadj p ih =>
      have hv : v ≠ Sum.inl C := by intro he; apply havoid; simp [he]
      have hp : Sum.inl C ∉ p.support := by intro h; apply havoid; simp [h]
      have hu : u ≠ Sum.inl C := by intro he; apply hp; exact he ▸ p.start_mem_support
      exact (hgap_adj C v u hv hu hadj).trans (ih hp)
  have hgap_neighbors_unique (C : Comp) (U V : Face)
      (hCU : H.Adj (Sum.inl C) (Sum.inr U)) (hCV : H.Adj (Sum.inl C) (Sum.inr V))
      (he : gap C (Sum.inr U) = gap C (Sum.inr V)) : U = V := by
    let D := gap C (Sum.inr U)
    have hpC : facePoint U ∈ C.valᶜ := fun h => Set.disjoint_left.mp (hsite_face_disjoint C U) h (hfacePoint U)
    have hD : IsComplementComponent C.val D := complementComponent_iff_componentIn.mpr ⟨facePoint U,hpC,rfl⟩
    have hUD : U.val ⊆ D := hface_in_site_gap C U (facePoint U) (hfacePoint U)
    have hVD : V.val ⊆ D := by
      change V.val ⊆ gap C (Sum.inr U)
      rw [he]
      exact hface_in_site_gap C V (facePoint V) (hfacePoint V)
    exact hgap_face_unique C D hD U V hUD hVD ((hAdj C U).mp hCU) ((hAdj C V).mp hCV)
  have hroot_no_cycle (C : Comp) (cycle : H.Walk (Sum.inl C) (Sum.inl C))
      (hcycle : cycle.IsCycle) : False := by
    cases cycle with
    | nil => exact hcycle.not_nil SimpleGraph.Walk.nil_nil
    | @cons _ first _ hfirst p =>
      cases first with
      | inl B => simp [H,Rel] at hfirst
      | inr U =>
        have hinfo := SimpleGraph.Walk.cons_isCycle_iff p hfirst |>.mp hcycle
        have hpn : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_isCycle_cons hcycle
        cases hr : p.reverse with
        | @cons _ last _ hlast q =>
          cases last with
          | inl B => simp [H,Rel] at hlast
          | inr V =>
            have hrevpath := hinfo.1.reverse
            rw [hr] at hrevpath
            have havoid : Sum.inl C ∉ q.support :=
              (SimpleGraph.Walk.cons_isPath_iff hlast q).mp hrevpath |>.2
            have hgapEq := hgap_walk C q havoid
            have hVU : V = U := hgap_neighbors_unique C V U hlast hfirst hgapEq
            subst V
            have hemem : s(Sum.inl C,Sum.inr U) ∈ p.reverse.edges := by
              rw [hr]
              simp
            have heorig : s(Sum.inl C,Sum.inr U) ∈ p.edges := by simpa using hemem
            exact hinfo.2 heorig
  have hforest : H.IsAcyclic := by
    intro v p hp
    cases v with
    | inl C => exact hroot_no_cycle C p hp
    | inr U =>
      cases p with
      | nil => exact hp.not_nil SimpleGraph.Walk.nil_nil
      | @cons _ first _ hfirst q =>
        cases first with
        | inr V => simp [H,Rel] at hfirst
        | inl C =>
          have hmem : Sum.inl C ∈ (SimpleGraph.Walk.cons hfirst q).support := by simp
          exact hroot_no_cycle C _ (hp.rotate hmem)
  choose C D hne hC hD using htwo
  let pick (U : Face) (k : Fin 2) : Comp := if k = 0 then C U else D U
  have hpick (U : Face) : Function.Injective (pick U) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact False.elim (hne U (by simpa [pick] using hkl))
    · exact False.elim (hne U (by simpa [pick] using hkl.symm))
    · rfl
  have hpickadj (U : Face) (k : Fin 2) : H.Adj (Sum.inl (pick U k)) (Sum.inr U) := by
    dsimp [pick]
    split_ifs <;> first | exact hC U | exact hD U
  let edge : Face × Fin 2 → H.edgeSet := fun z =>
    ⟨s(Sum.inl (pick z.1 z.2), Sum.inr z.1), by
      exact (H.mem_edgeSet).mpr (hpickadj z.1 z.2)⟩
  have heinj : Function.Injective edge := by
    intro z w heq
    have he := congrArg Subtype.val heq
    change s(Sum.inl (pick z.1 z.2), Sum.inr z.1) =
      s(Sum.inl (pick w.1 w.2), Sum.inr w.1) at he
    rcases Sym2.eq_iff.mp he with h | h
    · have hU : z.1 = w.1 := Sum.inr.inj h.2
      apply Prod.ext hU
      apply hpick w.1
      have hp := Sum.inl.inj h.1
      rw [hU] at hp
      exact hp
    · cases h.1
  letI : Fintype H.edgeSet := Fintype.ofFinite _
  have hside := Fintype.card_le_of_injective edge heinj
  have hforestcount {V : Type} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    Nat.card G.edgeSet + Nat.card G.ConnectedComponent = Fintype.card V := by
    classical
    letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
    have hedges :
      Nat.card G.edgeSet = ∑ c : G.ConnectedComponent, Nat.card c.toSimpleGraph.edgeSet := by
    
      classical
      letI : Fintype G.edgeSet := Fintype.ofFinite _
      letI (c : G.ConnectedComponent) : Fintype c.toSimpleGraph.edgeSet := Fintype.ofFinite _
      let f : (Σ c : G.ConnectedComponent, c.toSimpleGraph.edgeSet) → G.edgeSet :=
        fun z => ⟨z.2.val.map Subtype.val,z.1.toSimpleGraph_hom.map_mem_edgeSet z.2.property⟩
      have hf : Function.Bijective f := by
        constructor
        · intro z w h
          obtain ⟨c,e⟩ := z
          obtain ⟨d,k⟩ := w
          let x := e.val.out.1
          let y := e.val.out.2
          let u := k.val.out.1
          let v := k.val.out.2
          have he : s(x,y) = e.val := e.val.out_eq
          have hk : s(u,v) = k.val := k.val.out_eq
          have hp : s(x.val,y.val) = s(u.val,v.val) := by
            simpa only [f,← he,← hk,Sym2.map_mk] using congrArg Subtype.val h
          have hcd : c = d := by
            rcases Sym2.eq_iff.mp hp with h|h
            · exact x.property.symm.trans ((congrArg G.connectedComponentMk h.1).trans u.property)
            · exact x.property.symm.trans ((congrArg G.connectedComponentMk h.1).trans v.property)
          subst d
          have hek : e = k := Subtype.ext (Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h))
          cases hek
          rfl
        · intro e
          let x := e.val.out.1
          let y := e.val.out.2
          have he : s(x,y) = e.val := e.val.out_eq
          have hxy : G.Adj x y := G.mem_edgeSet.mp (he.symm ▸ e.property)
          let c := G.connectedComponentMk x
          have hx : x ∈ c.supp := rfl
          have hy : y ∈ c.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy.symm
          let k : c.toSimpleGraph.edgeSet := ⟨s(⟨x,hx⟩,⟨y,hy⟩),c.toSimpleGraph.mem_edgeSet.mpr hxy⟩
          refine ⟨⟨c,k⟩,?_⟩
          apply Subtype.ext
          exact he
      rw [Nat.card_eq_fintype_card,← Fintype.card_congr (Equiv.ofBijective f hf)]
      simp only [Fintype.card_sigma,Nat.card_eq_fintype_card]
    have hcomponents :
      (∑ c : G.ConnectedComponent, Nat.card c.toSimpleGraph.edgeSet) +
        Nat.card G.ConnectedComponent = Fintype.card V := by
    
      classical
      letI (c : G.ConnectedComponent) : Fintype c := Fintype.ofFinite _
      letI (c : G.ConnectedComponent) : Fintype c.toSimpleGraph.edgeSet := Fintype.ofFinite _
      have hc (c : G.ConnectedComponent) : Nat.card c.toSimpleGraph.edgeSet + 1 = Fintype.card c := by
        rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
        exact (hG.isTree_connectedComponent c).card_edgeFinset
      have hv : (∑ c : G.ConnectedComponent, Fintype.card c) = Fintype.card V := by
        calc
          _ = Fintype.card (Σ c : G.ConnectedComponent, c) := Fintype.card_sigma.symm
          _ = Fintype.card V := Fintype.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
      simpa only [← hv, ← hc, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_one, Nat.card_eq_fintype_card]
    rw [hedges]
    exact hcomponents
  obtain ⟨i, hi⟩ := hσ
  let C0 : Comp := ⟨connectedComponentIn G ((r ⟨i, hi⟩).val.map 0),
    Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩⟩
  letI : Nonempty H.ConnectedComponent := ⟨H.connectedComponentMk (Sum.inl C0)⟩
  have hcpos : 0 < Nat.card H.ConnectedComponent := Nat.card_pos
  have hcount := hforestcount H hforest
  have hcardedge : Nat.card H.edgeSet = Fintype.card H.edgeSet := Nat.card_eq_fintype_card
  have hvertices : Fintype.card (Comp ⊕ Face) = components.card + F.card := by
    simp [Comp, Face]
  have hfaces : Fintype.card (Face × Fin 2) = 2 * F.card := by
    simp [Face, Nat.mul_comm]
  rw [hfaces] at hside
  rw [hcardedge, hvertices] at hcount
  change F.card ≤ components.card - 1
  omega
end CurveComplex.HyperellipticModel
