import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSurfaceEndpointCap
import Schoenflies.BoundaryContinuity2
import Schoenflies.FaceCyclesProof
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1ArbitraryCrosscutAlternationPROVED
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopPreparedMovieBoundary
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopFiniteCoreSupport
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteBoundaryAvoidingPhase
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopBoundarySafeMoviePreparation
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopWholeGridAffineEdgeMoviesInRange
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellLiteralSharedEdgeDegree
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformVerticalSeamEndpointCount
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformHorizontalSeamEndpointCount
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformInitialBoundaryEndpointCount
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLocalBoundaryNormalRootDegree
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualExactStripTransverseNormalSigns
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellFourEdgeCoordinates
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellGenuineContactMovie
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteProperContactBoundaryVertices
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellSourceFiniteContactFamily
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedGridGenuineSurfaceBoundaryDegreeMovie
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopPreparedMovieCornerBoundaryScaffold
import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualOriginalMarkFreeContactPathInteriorParameters
import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualScaledLogarithmicContactCornerFamily
import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualMarkedContactSectorEmbeddedBoundaryWord
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import Mathlib.Topology.Subpath
import Mathlib.Analysis.Convex.Contractible
set_option maxHeartbeats 6000000
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Review-only exact ORIGINAL same-class loop subpath selection obligation.
No selected movie, component, corner word, graph or disk is an input. -/
theorem actual_same_class_loop_original_subpaths_punctured_homotopic
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (htransverse : ∀ q ∈ ArcSurgery.crossings M a b,
      ArcSurgery.CrossesInDisk M a b q)
    (p : S) (hp : p ∈ ArcSurgery.crossings M a b) :
    ∃ (f g : C(Interval,S)) (u v : S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0 = u ∧ g 0 = u ∧ f 1 = v ∧ g 1 = v ∧ u ≠ v ∧
      range f ∩ range g = {u,v} ∧
      v ∈ ArcSurgery.crossings M a b ∧
      (u ∈ ArcSurgery.crossings M a b ∨
        (u ∈ a.val.image ∩ b.val.image ∧ u ∈ (M.cover.branch : Set S))) ∧
      ∃ (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩),
        (∀ t : Interval, (α t : S) = f t) ∧
        (∀ t : Interval, (β t : S) = g t) ∧ α.Homotopic β := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨K,hzero,hcollision,hbase,hmarks,htop,U,V,hU,e,hCV,hUmarks,haxis,
    ε,hε,hεhalf,l,r,hl,hr,hin,htails,L,R,hL,hR,hzeroCharts,hnz,hLaxis,hRaxis,
    Λ₀,Λ₁,hΛ₀,hΛ₁,n₀₀,n₀₁,n₁₀,n₁₁,hn₀₀,hn₀₁,hn₁₀,hn₁₁,
    levels₀,levels₁,γ₀,γ₁,hp₀,hp₁,he₀,he₁,hd₀,hd₁,hc₀,hc₁,
    d₀,d₁,hdpos₀,hh₀,hdpos₁,hh₁,c₀,c₁,cp₀,cp₁,hcscale₀,hcscale₁,hcpscale₀,hcpscale₁,
    P₀,P₁,hPzero,hPstart,hPouter,hPboundary,hPV,hPinner,hPcontacts,hPnz,
    J₀,J₁,hJU,hcoord,hJbase,hJmarks,hJstart,hJouter,hJcontacts,hJboundary,
    A,B,hAeq,hBeq,hA,hB,hAB,q₀,q₁,hq₀,hq₁,W,hwleft,hwright,hwmiddle,
    hwstart,hwbase,hwmarks,hwbottom,hwtop,hWinner₀,hWinner₁,
    r₀,r₁,hr₀eq,hr₁eq,hr₀,horder,hr₁,φ,hφ,hφeq,G,hGeq,hGmarks,hGtop,hfiniteLeft,hfiniteRight,
    BC,hBC,hBCmarks,hBCaxis,T,hT,hGT,Q,hQ,ψ,hψ,hψbounds,hψzero,hψtop⟩ :=
      actual_same_class_loop_patched_central_contact_core M a b ha hclass hfinite p hp
  have hφbounds := actual_affine_window_strict_interior r₀ r₁ hr₀ horder hr₁ φ hφeq
  have hGbottom (t : Interval) : G (0,t)=b.val.map (φ t) := by
    as_aux_lemma =>
      rw [hGeq,hwbottom]
  obtain ⟨hbottomEmbedding,hfiniteBottom⟩ := actual_literal_window_bottom_contact_finite
    M a b K G hzero (hcollision 0) φ hφ hφbounds hGbottom (fun t => hGmarks (0,t)) hfinite
  have hfiniteTop : {t : Interval | G (1,t) ∈ a.val.image}.Finite := by
    as_aux_lemma =>
      apply Set.finite_empty.subset
      intro t ht
      exact False.elim (hGtop (1,t) rfl ht)
  have hr₀ε : r₀<ε := by
    as_aux_lemma =>
      rw [hr₀eq,hAeq]
      exact actual_small_weighted_quarter_margin ε d₀ hε hh₀
  have hεr₁ : 1-ε<r₁ := by
    as_aux_lemma =>
      rw [hr₁eq,hBeq]
      have hh := actual_small_weighted_quarter_margin ε d₁ hε hh₁
      linarith only [hh]
  have hcapture (t : Interval) (ht : b.val.map t ∈ crossings M a b) : ∃ s,φ s=t := by
    as_aux_lemma =>
      have hlo : ε<(t:ℝ) := lt_of_not_ge (fun hh => htails t (Or.inl hh) ht)
      have hhi : (t:ℝ)<1-ε := lt_of_not_ge (fun hh => htails t (Or.inr hh) ht)
      exact actual_affine_window_contains_middle r₀ r₁ ε horder hr₀ε hεr₁ φ hφeq t hlo hhi
  have hcorner := actual_original_crossing_free_tail_corner_geometry
    M a b ε r₀ r₁ htails hr₀ε.le hεr₁.le φ hφeq G hGbottom hGmarks
  have hSourceMovieMarks := hmarks
  have hSourceMovieTop := htop
  have hbottom := hGbottom
  have hbottomEmbed := hbottomEmbedding
  have hmarks := hGmarks
  have hcorner0 := hcorner.1
  have hcorner1 := hcorner.2
  have htop (t : Interval) := hGtop (1,t) rfl
  have hcontacts := hGT
  let originalSourceRightCoordinates := R
  have hlzero : l 0=0 := by apply Subtype.ext; rw [hl]; simp
  have hbU : a.val.map 0 ∈ U := by
    have he : K (0,l 0)=a.val.map 0 := by rw [hlzero,(hbase 0).1]
    exact he ▸ (hin 0 0).1
  have hbcoord : (e ⟨a.val.map 0,hbU⟩).val=0 := by
    have he : (⟨K (0,l 0),(hin 0 0).1⟩ : U)=⟨a.val.map 0,hbU⟩ := by
      apply Subtype.ext
      change K (0,l 0)=a.val.map 0
      rw [hlzero,(hbase 0).1]
    have hv := congrArg (fun q : U => (e q).val) he
    exact hv.symm.trans ((hL 0 0 (hin 0 0).1).symm.trans (hzeroCharts 0).1)
  have hczero₀ : c₀ 0=0 := by apply Subtype.ext; rw [hcscale₀]; change d₀*0=0; simp
  have hczero₁ : c₁ 0=0 := by apply Subtype.ext; rw [hcscale₁]; change d₁*0=0; simp
  have hcompat₀ (t : Ioc (0:ℝ) 1) :
      (⟨(cp₀ t).val,(cp₀ t).property.1.le,(cp₀ t).property.2⟩ : Interval)=
        c₀ ⟨t.val,t.property.1.le,t.property.2⟩ := by
    apply Subtype.ext
    change (cp₀ t).val=(c₀ ⟨t.val,t.property.1.le,t.property.2⟩:ℝ)
    rw [hcpscale₀,hcscale₀]
  have hcompat₁ (t : Ioc (0:ℝ) 1) :
      (⟨(cp₁ t).val,(cp₁ t).property.1.le,(cp₁ t).property.2⟩ : Interval)=
        c₁ ⟨t.val,t.property.1.le,t.property.2⟩ := by
    apply Subtype.ext
    change (cp₁ t).val=(c₁ ⟨t.val,t.property.1.le,t.property.2⟩:ℝ)
    rw [hcpscale₁,hcscale₁]
  obtain ⟨κ₀,hκ₀,time₀,htime₀,F₀,hFU₀,hFzero₀,hFmarks₀,hFtop₀,hFstart₀,hFcoord₀⟩ :=
    actual_scaled_logarithmic_contact_corner_family M a U V e hUmarks hbU hbcoord haxis
      L (fun τ => (hzeroCharts τ).1) c₀ cp₀ hczero₀ hcompat₀ Λ₀ hΛ₀ γ₀
      (fun k t => (hc₀ (cp₀ t) (γ₀ k (cp₀ t))).mpr ⟨k,rfl⟩)
      P₀ (fun z => (hPV z).1) (fun τ t ht hh => (hPinner τ t ht hh).1)
  obtain ⟨κ₁,hκ₁,time₁,htime₁,F₁,hFU₁,hFzero₁,hFmarks₁,hFtop₁,hFstart₁,hFcoord₁⟩ :=
    actual_scaled_logarithmic_contact_corner_family M a U V e hUmarks hbU hbcoord haxis
      originalSourceRightCoordinates (fun τ => (hzeroCharts τ).2) c₁ cp₁ hczero₁ hcompat₁ Λ₁ hΛ₁ γ₁
      (fun k t => (hc₁ (cp₁ t) (γ₁ k (cp₁ t))).mpr ⟨k,rfl⟩)
      P₁ (fun z => (hPV z).2) (fun τ t ht hh => (hPinner τ t ht hh).2)
  let actualSourceHalfParameter : C(Icc (0:ℝ) (1/2),Icc (0:ℝ) (1/2)) :=
    ⟨fun t => ⟨t.val/2,div_nonneg t.property.1 (by norm_num),by linarith [t.property.2]⟩,by fun_prop⟩
  have hActualSourceHalfZero : actualSourceHalfParameter ⟨0,le_rfl,by norm_num⟩=
      ⟨0,le_rfl,by norm_num⟩ := by
    apply Subtype.ext
    change (0:ℝ)/2=0
    norm_num
  let actualLeftCornerSector (k : ↑levels₀) : C(Interval × Icc (0:ℝ) (1/2),S) :=
    ⟨fun z => F₀ k (z.1,actualSourceHalfParameter z.2),by fun_prop⟩
  let actualRightCornerSector (k : ↑levels₁) : C(Interval × Icc (0:ℝ) (1/2),S) :=
    ⟨fun z => F₁ k (z.1,actualSourceHalfParameter z.2),by fun_prop⟩
  have hActualLeftCornerBoundaryWord (k : ↑levels₀) :=
    actual_marked_contact_sector_embedded_boundary_word M a U V e hUmarks haxis hbU hbcoord
      (actualLeftCornerSector k) (fun z => hFU₀ k (z.1,actualSourceHalfParameter z.2))
      (fun σ => by change F₀ k (σ,actualSourceHalfParameter ⟨0,le_rfl,by norm_num⟩)=_; rw [hActualSourceHalfZero]; exact hFzero₀ k σ)
      (fun z hz => hFmarks₀ k z.1 (actualSourceHalfParameter z.2) (div_pos hz (by norm_num)))
      (fun t => hFtop₀ k (actualSourceHalfParameter t))
  have hActualRightCornerBoundaryWord (k : ↑levels₁) :=
    actual_marked_contact_sector_embedded_boundary_word M a U V e hUmarks haxis hbU hbcoord
      (actualRightCornerSector k) (fun z => hFU₁ k (z.1,actualSourceHalfParameter z.2))
      (fun σ => by change F₁ k (σ,actualSourceHalfParameter ⟨0,le_rfl,by norm_num⟩)=_; rw [hActualSourceHalfZero]; exact hFzero₁ k σ)
      (fun z hz => hFmarks₁ k z.1 (actualSourceHalfParameter z.2) (div_pos hz (by norm_num)))
      (fun t => hFtop₁ k (actualSourceHalfParameter t))
  let sourceQuarter : Interval := ⟨1/4,by norm_num⟩
  let sectorQuarter : Icc (0:ℝ) (1/2) := ⟨1/4,by norm_num⟩
  let phaseQuarter : Ioc (0:ℝ) (1/2) := ⟨1/4,by norm_num⟩
  have hSourcePhiZero : (φ 0:ℝ)=r₀ := by rw [hφeq]; norm_num
  have hSourcePhiOne : (φ 1:ℝ)=r₁ := by rw [hφeq]; norm_num
  have hSourceLeftQuarter : q₀ (φ 0)=sourceQuarter := by
    apply Subtype.ext
    rw [hq₀,hSourcePhiZero,hr₀eq]
    have hh : (A/4)/A=(1/4:ℝ) := by field_simp [ne_of_gt hA]
    rw [hh]
    norm_num [sourceQuarter]
  have hSourceRightQuarter : q₁ (φ 1)=sourceQuarter := by
    apply Subtype.ext
    rw [hq₁,hSourcePhiOne,hr₁eq]
    have hh : (1-(1-B/4))/B=(1/4:ℝ) := by field_simp [ne_of_gt hB]; ring
    rw [hh]
    norm_num [sourceQuarter]
  have hSourceLeftBoundaryLiteral (τ : Interval) :
      G (τ,0)=J₀ ((1,τ),sourceQuarter) := by
    have hle : (φ 0:ℝ)≤A := by rw [hSourcePhiZero,hr₀eq]; linarith only [hA]
    rw [hGeq,hwleft 1 τ (φ 0) hle,hSourceLeftQuarter]
  have hSourceRightBoundaryLiteral (τ : Interval) :
      G (τ,1)=J₁ ((1,τ),sourceQuarter) := by
    have hle : 1-B≤(φ 1:ℝ) := by rw [hSourcePhiOne,hr₁eq]; linarith only [hB]
    rw [hGeq,hwright 1 τ (φ 1) hle,hSourceRightQuarter]
  have hSameSourceLeftBoundaryContact (τ : Interval) (ht : G (τ,0)∈a.val.image) :
      ∃ k : ↑levels₀,κ₀ k phaseQuarter=τ ∧ F₀ k (1,sectorQuarter)=G (τ,0) := by
    have hJcontact : J₀ ((1,τ),sourceQuarter)∈a.val.image := hSourceLeftBoundaryLiteral τ ▸ ht
    obtain ⟨k,hτ⟩ := ((hJcontacts τ sourceQuarter (by norm_num [sourceQuarter])
      (by norm_num [sourceQuarter])).1).mp hJcontact
    have hSameChosenPhase : κ₀ k phaseQuarter=τ := by
      rw [hκ₀]
      simpa [phaseQuarter,sourceQuarter] using hτ.symm
    have htime : time₀ k (1,phaseQuarter)=τ := by
      apply Subtype.ext
      rw [htime₀,hκ₀]
      simpa [phaseQuarter,sourceQuarter] using congrArg Subtype.val hτ.symm
    have hFcoord := hFcoord₀ k 1 sectorQuarter (by norm_num [sectorQuarter])
      (hFU₀ k (1,sectorQuarter))
    have hJU0 := (hJU ((1,τ),sourceQuarter)).1
    have hJU1 := (hJU ((1,τ),sourceQuarter)).2
    have he : e ⟨F₀ k (1,sectorQuarter),hFU₀ k (1,sectorQuarter)⟩=
        e ⟨J₀ ((1,τ),sourceQuarter),hJU0⟩ := by
      apply Subtype.ext
      rw [hFcoord,htime]
      exact ((hcoord ((1,τ),sourceQuarter) hJU0 hJU1).1).symm
    refine ⟨k,hSameChosenPhase,?_⟩
    exact (congrArg Subtype.val (e.injective he)).trans (hSourceLeftBoundaryLiteral τ).symm
  have hSameSourceRightBoundaryContact (τ : Interval) (ht : G (τ,1)∈a.val.image) :
      ∃ k : ↑levels₁,κ₁ k phaseQuarter=τ ∧ F₁ k (1,sectorQuarter)=G (τ,1) := by
    have hJcontact : J₁ ((1,τ),sourceQuarter)∈a.val.image := hSourceRightBoundaryLiteral τ ▸ ht
    obtain ⟨k,hτ⟩ := ((hJcontacts τ sourceQuarter (by norm_num [sourceQuarter])
      (by norm_num [sourceQuarter])).2).mp hJcontact
    have hSameChosenPhase : κ₁ k phaseQuarter=τ := by
      rw [hκ₁]
      simpa [phaseQuarter,sourceQuarter] using hτ.symm
    have htime : time₁ k (1,phaseQuarter)=τ := by
      apply Subtype.ext
      rw [htime₁,hκ₁]
      simpa [phaseQuarter,sourceQuarter] using congrArg Subtype.val hτ.symm
    have hFcoord := hFcoord₁ k 1 sectorQuarter (by norm_num [sectorQuarter])
      (hFU₁ k (1,sectorQuarter))
    have hJU0 := (hJU ((1,τ),sourceQuarter)).1
    have hJU1 := (hJU ((1,τ),sourceQuarter)).2
    have he : e ⟨F₁ k (1,sectorQuarter),hFU₁ k (1,sectorQuarter)⟩=
        e ⟨J₁ ((1,τ),sourceQuarter),hJU1⟩ := by
      apply Subtype.ext
      rw [hFcoord,htime]
      exact ((hcoord ((1,τ),sourceQuarter) hJU0 hJU1).2).symm
    refine ⟨k,hSameChosenPhase,?_⟩
    exact (congrArg Subtype.val (e.injective he)).trans (hSourceRightBoundaryLiteral τ).symm
  have hSameRawSourceLeftInitialLiteral (k : ↑levels₀) (t : Icc (0:ℝ) (1/2)) :
      F₀ k (0,t)=b.val.map (l (c₀ ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)) := by
    let v : Interval := ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩
    have hK := (hin 0 (c₀ v)).1
    have he : e ⟨F₀ k (0,t),hFU₀ k (0,t)⟩=e ⟨K (0,l (c₀ v)),hK⟩ := by
      apply Subtype.ext
      exact (hFstart₀ k t (hFU₀ k (0,t))).trans (hL 0 (c₀ v) hK)
    exact (congrArg Subtype.val (e.injective he)).trans (hzero _)
  have hSameRawSourceLeftQuarterRightLiteral (k : ↑levels₀) (σ : Interval) :
      F₀ k (σ,sectorQuarter)=G (time₀ k (σ,phaseQuarter),0) := by
    let τ := time₀ k (σ,phaseQuarter)
    have hJ0 := (hJU ((1,τ),sourceQuarter)).1
    have hJ1 := (hJU ((1,τ),sourceQuarter)).2
    have he : e ⟨F₀ k (σ,sectorQuarter),hFU₀ k (σ,sectorQuarter)⟩=
        e ⟨J₀ ((1,τ),sourceQuarter),hJ0⟩ := by
      apply Subtype.ext
      rw [hFcoord₀ k σ sectorQuarter (by norm_num [sectorQuarter]) (hFU₀ k (σ,sectorQuarter))]
      exact ((hcoord ((1,τ),sourceQuarter) hJ0 hJ1).1).symm
    exact (congrArg Subtype.val (e.injective he)).trans (hSourceLeftBoundaryLiteral τ).symm
  have hSameRawSourceRightInitialLiteral (k : ↑levels₁) (t : Icc (0:ℝ) (1/2)) :
      F₁ k (0,t)=b.val.map (r (c₁ ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩)) := by
    let v : Interval := ⟨t.val,t.property.1,t.property.2.trans (by norm_num)⟩
    have hK := (hin 0 (c₁ v)).2
    have he : e ⟨F₁ k (0,t),hFU₁ k (0,t)⟩=e ⟨K (0,r (c₁ v)),hK⟩ := by
      apply Subtype.ext
      exact (hFstart₁ k t (hFU₁ k (0,t))).trans (hR 0 (c₁ v) hK)
    exact (congrArg Subtype.val (e.injective he)).trans (hzero _)
  have hSameRawSourceRightQuarterRightLiteral (k : ↑levels₁) (σ : Interval) :
      F₁ k (σ,sectorQuarter)=G (time₁ k (σ,phaseQuarter),1) := by
    let τ := time₁ k (σ,phaseQuarter)
    have hJ0 := (hJU ((1,τ),sourceQuarter)).1
    have hJ1 := (hJU ((1,τ),sourceQuarter)).2
    have he : e ⟨F₁ k (σ,sectorQuarter),hFU₁ k (σ,sectorQuarter)⟩=
        e ⟨J₁ ((1,τ),sourceQuarter),hJ1⟩ := by
      apply Subtype.ext
      rw [hFcoord₁ k σ sectorQuarter (by norm_num [sectorQuarter]) (hFU₁ k (σ,sectorQuarter))]
      exact ((hcoord ((1,τ),sourceQuarter) hJ0 hJ1).2).symm
    exact (congrArg Subtype.val (e.injective he)).trans (hSourceRightBoundaryLiteral τ).symm
  let actualRawSourceQuarterParameter : C(Interval,Icc (0:ℝ) (1/2)) :=
    ⟨fun t => ⟨(t:ℝ)/4,div_nonneg t.property.1 (by norm_num),by
      have ht := t.property.2
      linarith⟩,by fun_prop⟩
  have hRawQuarterOne : actualRawSourceQuarterParameter 1=sectorQuarter :=
    Subtype.ext (by norm_num [actualRawSourceQuarterParameter,sectorQuarter])
  have hRawQuarterZero : actualRawSourceQuarterParameter 0=⟨0,le_rfl,by norm_num⟩ :=
    Subtype.ext (by norm_num [actualRawSourceQuarterParameter])
  let actualRawLeftCornerSquare (k : ↑levels₀) : C(Interval × Interval,S) :=
    ⟨fun z => F₀ k (z.1,actualRawSourceQuarterParameter z.2),by fun_prop⟩
  let actualRawRightCornerSquare (k : ↑levels₁) : C(Interval × Interval,S) :=
    ⟨fun z => F₁ k (z.1,actualRawSourceQuarterParameter z.2),by fun_prop⟩
  have hRawLeftCornerCarrier (k : ↑levels₀) (z : Interval × Interval) :
      actualRawLeftCornerSquare k z∉((M.cover.branch : Set S)\{a.val.map 0}) :=
    Set.disjoint_left.mp hUmarks (hFU₀ k (z.1,actualRawSourceQuarterParameter z.2))
  have hRawRightCornerCarrier (k : ↑levels₁) (z : Interval × Interval) :
      actualRawRightCornerSquare k z∉((M.cover.branch : Set S)\{a.val.map 0}) :=
    Set.disjoint_left.mp hUmarks (hFU₁ k (z.1,actualRawSourceQuarterParameter z.2))
  have hRawLeftCornerBoundaryWord (k : ↑levels₀) :=
    actual_one_corner_square_boundary_homotopy M (a.val.map 0) (actualRawLeftCornerSquare k)
      (hRawLeftCornerCarrier k)
  have hRawRightCornerBoundaryWord (k : ↑levels₁) :=
    actual_one_corner_square_boundary_homotopy M (a.val.map 0) (actualRawRightCornerSquare k)
      (hRawRightCornerCarrier k)
  have hRawLeftCornerRightLiteral (k : ↑levels₀) (σ : Interval) :
      actualRawLeftCornerSquare k (σ,1)=G (time₀ k (σ,phaseQuarter),0) := by
    change F₀ k (σ,actualRawSourceQuarterParameter 1)=_
    rw [hRawQuarterOne]
    exact hSameRawSourceLeftQuarterRightLiteral k σ
  have hRawRightCornerRightLiteral (k : ↑levels₁) (σ : Interval) :
      actualRawRightCornerSquare k (σ,1)=G (time₁ k (σ,phaseQuarter),1) := by
    change F₁ k (σ,actualRawSourceQuarterParameter 1)=_
    rw [hRawQuarterOne]
    exact hSameRawSourceRightQuarterRightLiteral k σ
  let actualRawSourceQuarterClosedParameter : C(Interval,Interval) :=
    ⟨fun t => ⟨(actualRawSourceQuarterParameter t).val,(actualRawSourceQuarterParameter t).property.1,
      (actualRawSourceQuarterParameter t).property.2.trans (by norm_num)⟩,by fun_prop⟩
  let actualRawLeftOriginalComparisonParameter : C(Interval,Interval) :=
    l.comp (c₀.comp actualRawSourceQuarterClosedParameter)
  let actualRawRightOriginalComparisonParameter : C(Interval,Interval) :=
    r.comp (c₁.comp actualRawSourceQuarterClosedParameter)
  have hRawLeftOriginalComparisonCoefficient (t : Interval) :
      (actualRawLeftOriginalComparisonParameter t:ℝ)=r₀*(t:ℝ) := by
    change (l (c₀ (actualRawSourceQuarterClosedParameter t)):ℝ)=r₀*(t:ℝ)
    rw [hl,hcscale₀,hr₀eq,hAeq]
    change ε*(d₀*((t:ℝ)/4))=(ε*d₀/4)*(t:ℝ)
    ring
  have hRawRightOriginalComparisonCoefficient (t : Interval) :
      (actualRawRightOriginalComparisonParameter t:ℝ)=1-(1-r₁)*(t:ℝ) := by
    change (r (c₁ (actualRawSourceQuarterClosedParameter t)):ℝ)=1-(1-r₁)*(t:ℝ)
    rw [hr,hcscale₁,hr₁eq,hBeq]
    change 1-ε*(d₁*((t:ℝ)/4))=1-(1-(1-ε*d₁/4))*(t:ℝ)
    ring
  have hRawLeftInitialOriginalComparisonLiteral (k : ↑levels₀) (t : Interval) :
      actualRawLeftCornerSquare k (0,t)=b.val.map (actualRawLeftOriginalComparisonParameter t) :=
    hSameRawSourceLeftInitialLiteral k (actualRawSourceQuarterParameter t)
  have hRawRightInitialOriginalComparisonLiteral (k : ↑levels₁) (t : Interval) :
      actualRawRightCornerSquare k (0,t)=b.val.map (actualRawRightOriginalComparisonParameter t) :=
    hSameRawSourceRightInitialLiteral k (actualRawSourceQuarterParameter t)
  have hRawLeftComparisonSource : actualRawLeftOriginalComparisonParameter 0=0 := by
    apply Subtype.ext
    rw [hRawLeftOriginalComparisonCoefficient]
    norm_num
  have hRawRightComparisonSource : actualRawRightOriginalComparisonParameter 0=1 := by
    apply Subtype.ext
    rw [hRawRightOriginalComparisonCoefficient]
    norm_num
  have hRawLeftComparisonTarget : actualRawLeftOriginalComparisonParameter 1=φ 0 := by
    apply Subtype.ext
    rw [hRawLeftOriginalComparisonCoefficient,hSourcePhiZero]
    norm_num
  have hRawRightComparisonTarget : actualRawRightOriginalComparisonParameter 1=φ 1 := by
    apply Subtype.ext
    rw [hRawRightOriginalComparisonCoefficient,hSourcePhiOne]
    norm_num
  have hRawLeftComparisonInterior (t : Interval) (ht : 0<(t:ℝ)) :
      0<(actualRawLeftOriginalComparisonParameter t:ℝ) ∧ (actualRawLeftOriginalComparisonParameter t:ℝ)<1 := by
    rw [hRawLeftOriginalComparisonCoefficient]
    have hr₀one : r₀<1 := horder.trans hr₁
    constructor <;> nlinarith only [hr₀,hr₀one,ht,t.property.1,t.property.2]
  have hRawRightComparisonInterior (t : Interval) (ht : 0<(t:ℝ)) :
      0<(actualRawRightOriginalComparisonParameter t:ℝ) ∧ (actualRawRightOriginalComparisonParameter t:ℝ)<1 := by
    rw [hRawRightOriginalComparisonCoefficient]
    have hr₁pos : 0<r₁ := hr₀.trans horder
    constructor <;> nlinarith only [hr₁pos,hr₁,ht,t.property.1,t.property.2]
  have hDrawing :
      ∃ G' : C(Interval × Interval,S),
      ∃ R : C((Interval × Interval) × Interval,S),
        (∀ z,R ((0,z.1),z.2)=G z) ∧
        (∀ z,R ((1,z.1),z.2)=G' z) ∧
        (∀ σ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → R ((σ,z.1),z.2)=G z) ∧
        (∀ z,R z ∉ (M.cover.branch : Set S)) ∧
      ∃ vertices : Finset (Interval × Interval),
      ∃ edges : Finset ℕ, ∃ arc : ↑edges → C(Interval,Interval × Interval),
        (∀ e,IsEmbedding (arc e)) ∧
        (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
        (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
        (∀ e f t u,arc e t=arc f u →
          (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
        (∀ z,G' z ∈ a.val.image ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) ∧
        (∀ z,G' z ∈ a.val.image → z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z ∈ vertices) ∧
        (∀ v : ↑vertices,0<(v.val.1:ℝ) → (v.val.1:ℝ)<1 →
          0<(v.val.2:ℝ) → (v.val.2:ℝ)<1 →
          {q : ↑edges × Fin 2 | arc q.1 (if q.2=0 then 0 else 1)=v.val}.ncard=2) ∧
        (∀ t,G' (0,t) ∈ a.val.image →
          {q : ↑edges × Fin 2 | arc q.1 (if q.2=0 then 0 else 1)=(0,t)}.ncard=1) := by
    classical
    let : T2Space S := M.sphere.symm.t2Space
    obtain ⟨preparedN,hpreparedN,hpreparedNodes,preparedCell,hpreparedCell,
      hpreparedCellClosed,hpreparedCover,preparedLabel,hpreparedCellT,hpreparedCellOff,
      preparedMovie,hpreparedStart,hpreparedBoundary,hpreparedMarks,
      hpreparedCellRange,hpreparedContacts,hpreparedOff,hpreparedClear⟩ :=
      actual_prepared_loop_boundary_safe_movie_preparation M a G hmarks
        hfiniteBottom hfiniteTop hfiniteLeft hfiniteRight BC hBC hBCmarks hBCaxis
        T hT hcontacts Q hQ ψ hψ
        (fun z => ⟨(hψbounds z).2.2.1,(hψbounds z).2.2.2⟩) hψzero
    have hpreparedVertices := actual_prepared_uniform_mesh_vertex_clear
      a.val.image G preparedN hpreparedN preparedMovie hpreparedBoundary hpreparedNodes hpreparedClear
    have hpreparedOffGrid (k) (hk : preparedLabel k=false)
        (z : Interval × Interval) (σ : Interval) :
        preparedMovie ((ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.1 z.1,
          ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.2 z.2),σ) ∉ a.val.image := by
      have hz : (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.1 z.1,
          ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.2 z.2) ∈ preparedCell k := by
        rw [hpreparedCell k]
        exact mem_range_self z
      rw [hpreparedOff k hk _ hz σ]
      exact hpreparedCellOff k hk _ hz
    have hbR (t : Interval) : preparedMovie ((t,0),1)=G (t,0) :=
      hpreparedBoundary (t,0) 1 (Or.inr (Or.inr (Or.inl rfl)))
    have hrR (t : Interval) : preparedMovie ((1,t),1)=G (1,t) :=
      hpreparedBoundary (1,t) 1 (Or.inr (Or.inl rfl))
    have htR (t : Interval) : preparedMovie ((t,1),1)=G (t,1) :=
      hpreparedBoundary (t,1) 1 (Or.inr (Or.inr (Or.inr rfl)))
    have hlR (t : Interval) : preparedMovie ((0,t),1)=G (0,t) :=
      hpreparedBoundary (0,t) 1 (Or.inl rfl)
    have hbFinite : {t : Interval | preparedMovie ((t,0),1) ∈ a.val.image}.Finite := by
      simpa only [hbR] using hfiniteLeft
    have hrFinite : {t : Interval | preparedMovie ((1,t),1) ∈ a.val.image}.Finite := by
      simpa only [hrR] using hfiniteTop
    have htFinite : {t : Interval | preparedMovie ((t,1),1) ∈ a.val.image}.Finite := by
      simpa only [htR] using hfiniteRight
    have hlFinite : {t : Interval | preparedMovie ((0,t),1) ∈ a.val.image}.Finite := by
      simpa only [hlR] using hfiniteBottom
    obtain ⟨gridMovies,hGridStart,hGridEnds,hGridMarks,hGridFinite,hGridRange,
      hGridOff,hGridOuter,hGridSigns,gridBoundary,hGridBoundary⟩ :=
      actual_prepared_loop_whole_grid_affine_edge_movies_in_range M a BC hBC hBCmarks hBCaxis
        preparedMovie preparedN hpreparedN preparedCell hpreparedCell preparedLabel hpreparedCellRange
        hpreparedVertices hpreparedMarks hpreparedOffGrid hbFinite hrFinite htFinite hlFinite
    obtain ⟨actualCellFinal,actualGridSurfaceMovie,hActualGridStart,hActualGridFinal,
      hActualGridMarks,hActualGridOuter,hActualOffLiteral,hActualCellFinalSides,hActualOffFree,hActualSelectedContacts⟩ :=
      actual_prepared_grid_genuine_surface_boundary_degree_movie BC hBC (M.cover.branch : Set S) hBCmarks
        a.val.image hBCaxis preparedMovie hpreparedMarks preparedN hpreparedN
        preparedCell hpreparedCell preparedLabel hpreparedCellRange
        (fun k hk z => hpreparedOffGrid k hk z 1)
        gridMovies hGridStart hGridEnds hGridFinite hGridRange hGridOff hGridOuter
        gridBoundary hGridBoundary
    have hActualGridBoundary (z : Interval × Interval) (σ : Interval)
        (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) : actualGridSurfaceMovie (z,σ)=G z := by
      obtain ⟨side,i,t,he⟩ := actual_outer_grid_boundary_cover preparedN hpreparedN z hz
      calc
        actualGridSurfaceMovie (z,σ)=preparedMovie (z,1) := by rw [←he,hActualGridOuter]
        _=G z := hpreparedBoundary z 1 hz
    let preparedFinal : C(Interval × Interval,S) := ⟨fun z => preparedMovie (z,1),by fun_prop⟩
    let actualFinal : C(Interval × Interval,S) := ⟨fun z => actualGridSurfaceMovie (z,1),by fun_prop⟩
    let before : G.Homotopy preparedFinal :=
      { toFun := fun q => preparedMovie (q.2,q.1)
        continuous_toFun := preparedMovie.continuous.comp (continuous_snd.prodMk continuous_fst)
        map_zero_left := hpreparedStart
        map_one_left := fun _ => rfl }
    let after : preparedFinal.Homotopy actualFinal :=
      { toFun := fun q => actualGridSurfaceMovie (q.2,q.1)
        continuous_toFun := actualGridSurfaceMovie.continuous.comp (continuous_snd.prodMk continuous_fst)
        map_zero_left := hActualGridStart
        map_one_left := fun _ => rfl }
    let joined := before.trans after
    have hJoinedMarks := actual_homotopy_concatenation_avoidance before after
      (M.cover.branch : Set S) (fun σ z => hpreparedMarks (z,σ))
        (fun σ z => hActualGridMarks (z,σ))
    have hJoinedBoundary (σ : Interval) (z : Interval × Interval)
        (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) : joined (σ,z)=G z := by
      rw [ContinuousMap.Homotopy.trans_apply]
      split_ifs
      · exact hpreparedBoundary z _ hz
      · exact hActualGridBoundary z _ hz
    let actualRelativeMovie : C((Interval × Interval) × Interval,S) :=
      ⟨fun q => joined (q.1.1,(q.1.2,q.2)),
        joined.continuous.comp (((continuous_fst.comp continuous_fst).prodMk
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))⟩
    refine ⟨actualFinal,actualRelativeMovie,?_,?_,?_,?_,?_⟩
    · intro z
      exact joined.map_zero_left z
    · intro z
      exact joined.map_one_left z
    · intro σ z hz
      exact hJoinedBoundary σ z hz
    · intro z
      exact hJoinedMarks z.1.1 (z.1.2,z.2)
    · have hLocalFamily (k : Fin preparedN × Fin preparedN) : ∃ vertices : Finset (Interval × Interval),
      ∃ A : Type,∃ _hA : Finite A,∃ arc : A → C(Interval,Interval × Interval),
        (∀ e,arc e 0 ∈ vertices ∧ arc e 1 ∈ vertices) ∧
        (∀ e d t u,arc e t=arc d u → (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
        (∀ e t,t≠0 → t≠1 → arc e t ∉ vertices) ∧
        (∀ e,IsEmbedding (arc e)) ∧
        (∀ e t,0<t.val → t.val<1 →
          0<(arc e t).1.val ∧ (arc e t).1.val<1 ∧ 0<(arc e t).2.val ∧ (arc e t).2.val<1) ∧
        (∀ z,actualCellFinal k z ∈ a.val.image ↔ z ∈ vertices ∨ ∃ e t,arc e t=z) ∧
        (∀ v : ↑vertices,0<v.val.1.val → v.val.1.val < 1 →
          0<v.val.2.val → v.val.2.val < 1 →
          {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=v.val}.ncard=2) ∧
        (preparedLabel k=true →
        ∃ coordinate : C(Interval × Interval,Interval × Icc (-1:ℝ) 1),
          (∀ z,BC (coordinate z)=actualCellFinal k z) ∧
        (∀ (i : Fin 4) (u : Interval),0<u.val → u.val < 1 →
          (coordinate (actualLiteralCellSide i u)).2.val=0 →
          ∀ δ : ℝ,0<δ →
          (∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
            (coordinate (actualLiteralCellSide i v)).2.val/(1/2:ℝ)≠0 ∧
            (coordinate (actualLiteralCellSide i w)).2.val/(1/2:ℝ)≠0 ∧
            ((0<(coordinate (actualLiteralCellSide i v)).2.val/(1/2:ℝ)) ↔
              ¬(0<(coordinate (actualLiteralCellSide i w)).2.val/(1/2:ℝ)))) →
          {r : A × Fin 2 | arc r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide i u}.ncard=1)) := by
        by_cases hk : preparedLabel k=true
        · obtain ⟨v,A,hA,arc,he,hc,hcl,hemb,hin,hcov,hdeg,hcoord⟩ := hActualSelectedContacts k hk
          exact ⟨v,A,hA,arc,he,hc,hcl,hemb,hin,hcov,hdeg,fun _ => hcoord⟩
        · have hf : preparedLabel k=false := Bool.eq_false_of_not_eq_true hk
          refine ⟨∅,Empty,inferInstance,(fun e => nomatch e),?_,?_,?_,?_,?_,?_,?_,?_⟩
          · intro e
            cases e
          · intro e
            cases e
          · intro e
            cases e
          · intro e
            cases e
          · intro e
            cases e
          · intro z
            simp only [Finset.notMem_empty, false_or]
            constructor
            · intro hz
              exact False.elim (hActualOffFree k hf z hz)
            · rintro ⟨e,t,he⟩
              cases e
          · intro v
            exact False.elim (Finset.notMem_empty _ v.property)
          · intro htrue
            exact False.elim (hk htrue)
      choose localVertices localA localFinite localArc hLocalEnds hLocalCollision hLocalClear
        hLocalEmbed hLocalInterior hLocalCoverage hLocalDegree hLocalBoundaryDegree using hLocalFamily
      have : ∀ k,Finite (localA k) := localFinite
      obtain ⟨globalVertices,globalArcs,hGlobalEmbed,hGlobalEnds,hGlobalClear,
        hGlobalCollision,hGlobalCoverage,hGlobalInterior,hGlobalArcParameter,hGlobalVertices,hGlobalCellCount⟩ :=
        actual_uniform_cell_source_finite_contact_family preparedN hpreparedN actualFinal a.val.image
          actualCellFinal hActualGridFinal localVertices localA localArc hLocalEnds hLocalCollision
            hLocalClear hLocalEmbed hLocalInterior hLocalCoverage
      have hGlobalBoundary := actual_finite_proper_contact_boundary_vertices actualFinal a.val.image
        globalVertices globalArcs hGlobalEnds hGlobalCoverage hGlobalInterior
      have hGlobalCellInteriorDegree (k : Fin preparedN × Fin preparedN)
          (v : ↑(localVertices k)) (hv0 : 0<v.val.1.val) (hv1 : v.val.1.val < 1)
          (hv2 : 0<v.val.2.val) (hv3 : v.val.2.val < 1) :
          {r : (Σ l,localA l) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=
              (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.1 v.val.1,
                ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.2 v.val.2)}.ncard=2 := by
        rw [hGlobalCellCount k v.val hv0 hv1 hv2 hv3]
        exact hLocalDegree k v hv0 hv1 hv2 hv3
      have hLocalSharedEdgeDegree (k : Fin preparedN × Fin preparedN)
          (side : Fin 4) (u : Interval) (hu0 : 0<u.val) (hu1 : u.val < 1)
          (hinternal : (actualUniformCellGridSide preparedN k side).elim
            (fun q => 0<q.2.val ∧ q.2.val<preparedN)
            (fun q => 0<q.1.val ∧ q.1.val<preparedN))
          (hcontact : gridMovies (actualUniformCellGridSide preparedN k side) (1,u)∈a.val.image) :
          {r : localA k × Fin 2 |
            localArc k r.1 (if r.2=0 then 0 else 1)=actualLiteralCellSide side u}.ncard=1 := by
        have hselected : preparedLabel k=true := by
          by_contra hn
          have hf := Bool.eq_false_of_not_eq_true hn
          exact hActualOffFree k hf _ ((hActualCellFinalSides k side u).symm ▸ hcontact)
        obtain ⟨coordinate,hdecode,hdegree⟩ := hLocalBoundaryDegree k hselected
        obtain ⟨Qe,hQe,hflip⟩ := hGridSigns (actualUniformCellGridSide preparedN k side) hinternal u hcontact
        let edge : C(Interval,S) := ⟨fun t => gridMovies (actualUniformCellGridSide preparedN k side) (1,t),by fun_prop⟩
        have hroot : (hBC.toHomeomorph.symm (Qe u)).2.val=0 := by
          apply (hBCaxis _).mp
          have hq : BC (hBC.toHomeomorph.symm (Qe u))=edge u :=
            (congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Qe u))).trans (hQe u)
          rw [hq]
          exact hcontact
        exact actual_selected_cell_literal_shared_edge_degree_one BC hBC (actualCellFinal k)
          coordinate hdecode (localA k) (localArc k) hdegree side edge
            (hActualCellFinalSides k side) Qe hQe u hu0 hu1 hroot hflip
      have hGlobalVerticalSeamDegree (node : Fin (preparedN+1))
          (hnode : 0<node.val ∧ node.val<preparedN) (i : Fin preparedN)
          (u : Interval) (hu0 : 0<u.val) (hu1 : u.val < 1)
          (hcontact : gridMovies (Sum.inr (node,i)) (1,u)∈a.val.image) :
          {r : (Σ k,localA k) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=
            (actualHalfMeshParameter preparedN hpreparedN ⟨2*node.val,by omega⟩,
              ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u)}.ncard=2 := by
        let L : Fin preparedN × Fin preparedN := (⟨node.val-1,by omega⟩,i)
        let R : Fin preparedN × Fin preparedN := (⟨node.val,hnode.2⟩,i)
        have heL : actualUniformCellGridSide preparedN L 1=Sum.inr (node,i) := by
          change Sum.inr (L.1.succ,L.2)=Sum.inr (node,i)
          apply congrArg Sum.inr
          apply Prod.ext
          · apply Fin.ext
            change node.val-1+1=node.val
            omega
          · rfl
        have heR : actualUniformCellGridSide preparedN R 3=Sum.inr (node,i) := by
          change Sum.inr (R.1.castSucc,R.2)=Sum.inr (node,i)
          apply congrArg Sum.inr
          exact Prod.ext (Fin.ext rfl) rfl
        have hcL := hLocalSharedEdgeDegree L 1 u hu0 hu1
          (by rw [heL]; exact hnode) (by rw [heL]; exact hcontact)
        have hcR := hLocalSharedEdgeDegree R 3 u hu0 hu1
          (by rw [heR]; exact hnode) (by rw [heR]; exact hcontact)
        have hs : {r : (Σ k,localA k) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=
            (actualHalfMeshParameter preparedN hpreparedN ⟨2*node.val,by omega⟩,
              ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u)}=
            {r : (Σ k,localA k) × Fin 2 |
              (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN r.1.1.1
                (localArc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).1,
               ArcFinitePosition.intervalMeshParameter preparedN hpreparedN r.1.1.2
                (localArc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).2)=
              (actualHalfMeshParameter preparedN hpreparedN ⟨2*node.val,by omega⟩,
                ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u)} := by
          ext r
          simp only [Set.mem_ofPred_eq]
          rw [hGlobalArcParameter]
        rw [hs,actual_uniform_vertical_seam_endpoint_count preparedN hpreparedN localA localArc node hnode i u ⟨hu0,hu1⟩]
        change _+_=2
        change {r : localA L × Fin 2 | localArc L r.1 (if r.2=0 then 0 else 1)=(1,u)}.ncard=1 at hcL
        change {r : localA R × Fin 2 | localArc R r.1 (if r.2=0 then 0 else 1)=(0,u)}.ncard=1 at hcR
        exact (congrArg₂ Nat.add hcL hcR).trans (by norm_num)
      have hGlobalHorizontalSeamDegree (node : Fin (preparedN+1))
          (hnode : 0<node.val ∧ node.val<preparedN) (i : Fin preparedN)
          (u : Interval) (hu0 : 0<u.val) (hu1 : u.val < 1)
          (hcontact : gridMovies (Sum.inl (i,node)) (1,u)∈a.val.image) :
          {r : (Σ k,localA k) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=
            (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u,
              actualHalfMeshParameter preparedN hpreparedN ⟨2*node.val,by omega⟩)}.ncard=2 := by
        let L : Fin preparedN × Fin preparedN := (i,⟨node.val-1,by omega⟩)
        let R : Fin preparedN × Fin preparedN := (i,⟨node.val,hnode.2⟩)
        have heL : actualUniformCellGridSide preparedN L 2=Sum.inl (i,node) := by
          change Sum.inl (L.1,L.2.succ)=Sum.inl (i,node)
          apply congrArg Sum.inl
          apply Prod.ext
          · rfl
          · apply Fin.ext
            change node.val-1+1=node.val
            omega
        have heR : actualUniformCellGridSide preparedN R 0=Sum.inl (i,node) := by
          change Sum.inl (R.1,R.2.castSucc)=Sum.inl (i,node)
          apply congrArg Sum.inl
          exact Prod.ext rfl (Fin.ext rfl)
        have hcL := hLocalSharedEdgeDegree L 2 u hu0 hu1
          (by rw [heL]; exact hnode) (by rw [heL]; exact hcontact)
        have hcR := hLocalSharedEdgeDegree R 0 u hu0 hu1
          (by rw [heR]; exact hnode) (by rw [heR]; exact hcontact)
        have hs : {r : (Σ k,localA k) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=
            (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u,
              actualHalfMeshParameter preparedN hpreparedN ⟨2*node.val,by omega⟩)}=
            {r : (Σ k,localA k) × Fin 2 |
              (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN r.1.1.1
                (localArc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).1,
               ArcFinitePosition.intervalMeshParameter preparedN hpreparedN r.1.1.2
                (localArc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).2)=
              (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u,
                actualHalfMeshParameter preparedN hpreparedN ⟨2*node.val,by omega⟩)} := by
          ext r
          simp only [Set.mem_ofPred_eq]
          rw [hGlobalArcParameter]
        rw [hs,actual_uniform_horizontal_seam_endpoint_count preparedN hpreparedN localA localArc node hnode i u ⟨hu0,hu1⟩]
        change _+_=2
        change {r : localA L × Fin 2 | localArc L r.1 (if r.2=0 then 0 else 1)=(u,1)}.ncard=1 at hcL
        change {r : localA R × Fin 2 | localArc R r.1 (if r.2=0 then 0 else 1)=(u,0)}.ncard=1 at hcR
        exact (congrArg₂ Nat.add hcL hcR).trans (by norm_num)
      have hCellCornerLiteral (k : Fin preparedN × Fin preparedN) (z : Interval × Interval)
          (hx : z.1=0 ∨ z.1=1) (hy : z.2=0 ∨ z.2=1) :
          actualCellFinal k z=preparedMovie
            ((ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.1 z.1,
              ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.2 z.2),1) := by
        rcases hx with hx | hx
        · have he : z=actualLiteralCellSide 3 z.2 := by change z=(0,z.2); exact Prod.ext hx rfl
          rw [he,hActualCellFinalSides,hGridEnds _ 1 z.2 hy,
            ← actual_literal_cell_side_grid_parameter]
          rfl
        · have he : z=actualLiteralCellSide 1 z.2 := by change z=(1,z.2); exact Prod.ext hx rfl
          rw [he,hActualCellFinalSides,hGridEnds _ 1 z.2 hy,
            ← actual_literal_cell_side_grid_parameter]
          rfl
      have hGlobalInteriorDegree (v : ↑globalVertices) (hv0 : 0<v.val.1.val)
          (hv1 : v.val.1.val < 1) (hv2 : 0<v.val.2.val) (hv3 : v.val.2.val < 1) :
          {r : (Σ k,localA k) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=v.val}.ncard=2 := by
        obtain ⟨k,w,hw,he⟩ := (hGlobalVertices v.val).mp v.property
        have hcontact : actualCellFinal k w∈a.val.image := (hLocalCoverage k w).mpr (Or.inl hw)
        have hnR : (0:ℝ)<preparedN := by exact_mod_cast hpreparedN
        have hnotCorner : ¬((w.1=0 ∨ w.1=1) ∧ (w.2=0 ∨ w.2=1)) := by
          rintro ⟨hx,hy⟩
          let ix : Fin (preparedN+1) := if w.1=0 then k.1.castSucc else k.1.succ
          let iy : Fin (preparedN+1) := if w.2=0 then k.2.castSucc else k.2.succ
          have hxnode : ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.1 w.1=
              actualHalfMeshParameter preparedN hpreparedN ⟨2*ix.val,by omega⟩ := by
            rcases hx with h | h
            · simpa [ix,h] using (actual_uniform_mesh_node_as_cell_start preparedN hpreparedN k.1).symm
            · simpa [ix,h] using (actual_uniform_mesh_node_as_cell_end preparedN hpreparedN k.1).symm
          have hynode : ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.2 w.2=
              actualHalfMeshParameter preparedN hpreparedN ⟨2*iy.val,by omega⟩ := by
            rcases hy with h | h
            · simpa [iy,h] using (actual_uniform_mesh_node_as_cell_start preparedN hpreparedN k.2).symm
            · simpa [iy,h] using (actual_uniform_mesh_node_as_cell_end preparedN hpreparedN k.2).symm
          have hix : 0 < ix.val ∧ ix.val < preparedN := by
            have hh0 := hv0
            have hh1 := hv1
            rw [← he,hxnode] at hh0 hh1
            rw [actual_half_mesh_parameter_vertex] at hh0 hh1
            have hi0 : (0:ℝ) < ix.val := (div_pos_iff_of_pos_right hnR).mp hh0
            have hi1 : (ix.val:ℝ) < preparedN := (div_lt_one hnR).mp hh1
            exact ⟨by exact_mod_cast hi0,by exact_mod_cast hi1⟩
          have hclear := hpreparedVertices ix iy (Or.inl hix)
          rw [← hxnode,← hynode,← hCellCornerLiteral k w hx hy] at hclear
          exact hclear hcontact
        have pos0 (x : Interval) (hx : x≠0) : 0<x.val :=
          lt_of_le_of_ne x.property.1 (fun he => hx (Subtype.ext he.symm))
        have pos1 (x : Interval) (hx : x≠1) : x.val < 1 :=
          lt_of_le_of_ne x.property.2 (fun he => hx (Subtype.ext he))
        by_cases hx0 : w.1=0
        · have hy0 : w.2≠0 := fun h => hnotCorner ⟨Or.inl hx0,Or.inl h⟩
          have hy1 : w.2≠1 := fun h => hnotCorner ⟨Or.inl hx0,Or.inr h⟩
          have hi : 0<k.1.val := by
            have hh := hv0
            rw [← he] at hh
            change 0<((k.1.val:ℝ)+w.1.val)/preparedN at hh
            rw [hx0] at hh
            change 0<((k.1.val:ℝ)+0)/preparedN at hh
            simp only [add_zero] at hh
            exact_mod_cast (div_pos_iff_of_pos_right hnR).mp hh
          have hc : gridMovies (Sum.inr (k.1.castSucc,k.2)) (1,w.2)∈a.val.image := by
            have hz : w=actualLiteralCellSide 3 w.2 := by change w=(0,w.2); exact Prod.ext hx0 rfl
            rw [hz,hActualCellFinalSides] at hcontact
            exact hcontact
          have hd := hGlobalVerticalSeamDegree k.1.castSucc ⟨hi,k.1.isLt⟩ k.2 w.2 (pos0 _ hy0) (pos1 _ hy1) hc
          have hg : (actualHalfMeshParameter preparedN hpreparedN ⟨2*k.1.castSucc.val,by omega⟩,
              ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.2 w.2)=v.val := by
            change (actualHalfMeshParameter preparedN hpreparedN ⟨2*k.1.val,by omega⟩,_) = _
            rw [actual_uniform_mesh_node_as_cell_start preparedN hpreparedN k.1]
            simpa only [hx0] using he
          rw [hg] at hd
          exact hd
        · by_cases hx1 : w.1=1
          · have hy0 : w.2≠0 := fun h => hnotCorner ⟨Or.inr hx1,Or.inl h⟩
            have hy1 : w.2≠1 := fun h => hnotCorner ⟨Or.inr hx1,Or.inr h⟩
            have hi : k.1.val+1<preparedN := by
              have hh := hv1
              rw [← he] at hh
              change ((k.1.val:ℝ)+w.1.val)/preparedN<1 at hh
              rw [hx1] at hh
              have hiR := (div_lt_one hnR).mp hh
              change (k.1.val:ℝ)+1<(preparedN:ℝ) at hiR
              exact_mod_cast hiR
            have hc : gridMovies (Sum.inr (k.1.succ,k.2)) (1,w.2)∈a.val.image := by
              have hz : w=actualLiteralCellSide 1 w.2 := by change w=(1,w.2); exact Prod.ext hx1 rfl
              rw [hz,hActualCellFinalSides] at hcontact
              exact hcontact
            have hd := hGlobalVerticalSeamDegree k.1.succ ⟨by change 0<k.1.val+1; omega,hi⟩ k.2 w.2 (pos0 _ hy0) (pos1 _ hy1) hc
            have hg : (actualHalfMeshParameter preparedN hpreparedN ⟨2*k.1.succ.val,by omega⟩,
                ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.2 w.2)=v.val := by
              rw [actual_uniform_mesh_node_as_cell_end preparedN hpreparedN k.1]
              simpa only [hx1] using he
            rw [hg] at hd
            exact hd
          · by_cases hy0 : w.2=0
            · have hi : 0<k.2.val := by
                have hh := hv2
                rw [← he] at hh
                change 0<((k.2.val:ℝ)+w.2.val)/preparedN at hh
                rw [hy0] at hh
                change 0<((k.2.val:ℝ)+0)/preparedN at hh
                simp only [add_zero] at hh
                exact_mod_cast (div_pos_iff_of_pos_right hnR).mp hh
              have hc : gridMovies (Sum.inl (k.1,k.2.castSucc)) (1,w.1)∈a.val.image := by
                have hz : w=actualLiteralCellSide 0 w.1 := by change w=(w.1,0); exact Prod.ext rfl hy0
                rw [hz,hActualCellFinalSides] at hcontact
                exact hcontact
              have hd := hGlobalHorizontalSeamDegree k.2.castSucc ⟨hi,k.2.isLt⟩ k.1 w.1 (pos0 _ hx0) (pos1 _ hx1) hc
              have hg : (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.1 w.1,
                  actualHalfMeshParameter preparedN hpreparedN ⟨2*k.2.castSucc.val,by omega⟩)=v.val := by
                change (_,actualHalfMeshParameter preparedN hpreparedN ⟨2*k.2.val,by omega⟩) = _
                rw [actual_uniform_mesh_node_as_cell_start preparedN hpreparedN k.2]
                simpa only [hy0] using he
              rw [hg] at hd
              exact hd
            · by_cases hy1 : w.2=1
              · have hi : k.2.val+1<preparedN := by
                  have hh := hv3
                  rw [← he] at hh
                  change ((k.2.val:ℝ)+w.2.val)/preparedN<1 at hh
                  rw [hy1] at hh
                  have hiR := (div_lt_one hnR).mp hh
                  change (k.2.val:ℝ)+1<(preparedN:ℝ) at hiR
                  exact_mod_cast hiR
                have hc : gridMovies (Sum.inl (k.1,k.2.succ)) (1,w.1)∈a.val.image := by
                  have hz : w=actualLiteralCellSide 2 w.1 := by change w=(w.1,1); exact Prod.ext rfl hy1
                  rw [hz,hActualCellFinalSides] at hcontact
                  exact hcontact
                have hd := hGlobalHorizontalSeamDegree k.2.succ ⟨by change 0<k.2.val+1; omega,hi⟩ k.1 w.1 (pos0 _ hx0) (pos1 _ hx1) hc
                have hg : (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN k.1 w.1,
                    actualHalfMeshParameter preparedN hpreparedN ⟨2*k.2.succ.val,by omega⟩)=v.val := by
                  rw [actual_uniform_mesh_node_as_cell_end preparedN hpreparedN k.2]
                  simpa only [hy1] using he
                rw [hg] at hd
                exact hd
              · have hd := hGlobalCellInteriorDegree k ⟨w,hw⟩ (pos0 _ hx0) (pos1 _ hx1) (pos0 _ hy0) (pos1 _ hy1)
                rw [he] at hd
                exact hd
      have hInitialCellLiteral (i : Fin preparedN) (t : Interval) :
          actualCellFinal (⟨0,hpreparedN⟩,i) (0,t)=
            G (0,ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i t) := by
        have hh := hActualGridFinal (⟨0,hpreparedN⟩,i) (0,t)
        have hz : ArcFinitePosition.intervalMeshParameter preparedN hpreparedN ⟨0,hpreparedN⟩ 0=0 := by
          apply Subtype.ext
          simp [ArcFinitePosition.intervalMeshParameter]
        rw [hz,hActualGridBoundary _ 1 (Or.inl rfl)] at hh
        exact hh.symm
      have hLocalOriginalBottomDegree (i : Fin preparedN) (u : Interval)
          (hu : 0<u.val ∧ u.val < 1)
          (hcontact : actualCellFinal (⟨0,hpreparedN⟩,i) (0,u)∈a.val.image) :
          {r : localA (⟨0,hpreparedN⟩,i) × Fin 2 |
            localArc (⟨0,hpreparedN⟩,i) r.1 (if r.2=0 then 0 else 1)=(0,u)}.ncard=1 := by
        let k : Fin preparedN × Fin preparedN := (⟨0,hpreparedN⟩,i)
        have hk : preparedLabel k=true := by
          by_contra hn
          exact hActualOffFree k (Bool.eq_false_of_not_eq_true hn) (0,u) hcontact
        obtain ⟨coordinate,hdecode,hdegree⟩ := hLocalBoundaryDegree k hk
        let γ : C(Interval,S) := (actualCellFinal k).comp (actualLiteralCellSide 3)
        have hγ (t : Interval) : γ t=G (0,ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i t) := hInitialCellLiteral i t
        have hinj : InjOn γ (Ioo 0 1) := by
          intro t ht v hv he
          rw [hγ,hγ] at he
          have hh := congrArg Subtype.val (hbottomEmbed.injective he)
          have hnR : (preparedN:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hpreparedN
          have hp : (i.val:ℝ)+t.val=(i.val:ℝ)+v.val := (div_left_inj' hnR).mp hh
          exact Subtype.ext (by linarith only [hp])
        have himage : range γ⊆b.val.image := by
          rintro x ⟨t,rfl⟩
          rw [hγ,hbottom]
          exact mem_range_self _
        have hmarksγ (t) : γ t∉(M.cover.branch : Set S) := by rw [hγ]; exact hmarks _
        have hcross : CrossesInDisk M a b (γ u) := htransverse (γ u)
          ⟨⟨hcontact,hmarksγ u⟩,⟨himage (mem_range_self u),hmarksγ u⟩⟩
        let embed : C(Interval,Interval × Interval) :=
          ⟨fun t => (0,ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i t),
            continuous_const.prodMk (ArcFinitePosition.intervalMeshParameter_continuous preparedN hpreparedN i)⟩
        let T0 : Set Interval := embed ⁻¹' T
        have hT0 : IsOpen T0 := hT.preimage embed.continuous
        have huT : u∈T0 := by
          apply hcontacts
          change G (0,ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u)∈a.val.image
          rw [← hγ u]
          exact hcontact
        let lift : C(T0,T) := ⟨fun t => ⟨embed t.val,t.property⟩,by fun_prop⟩
        let Q0 : C(T0,range BC) := Q.comp lift
        let normal : C(T0,ℝ) :=
          ⟨fun t => (coordinate (actualLiteralCellSide 3 t.val)).2.val,by fun_prop⟩
        have hnormal (t : T0) : normal t=((hBC.toHomeomorph.symm (Q0 t)).2:ℝ) := by
          have he : coordinate (actualLiteralCellSide 3 t.val)=hBC.toHomeomorph.symm (Q0 t) := by
            apply hBC.injective
            exact ((hdecode _).trans (hγ t.val)).trans
              ((congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Q0 t))).trans (hQ (lift t))).symm
          exact congrArg (fun z => z.2.val) he
        have hQ0 (t : T0) : (Q0 t).val=γ t.val := (hQ (lift t)).trans (hγ t.val).symm
        obtain ⟨δ,hδ,hflip⟩ := actual_exact_strip_transverse_normal_signs_flip
          M a b γ hinj himage u hu hcross BC hBC hBCaxis T0 hT0 huT Q0 hQ0 normal hnormal
            (by intro t; rw [hnormal t]; simpa only [Q0,ContinuousMap.comp_apply,hψ (lift t)] using hψbounds (lift t))
        have hzero : (coordinate (actualLiteralCellSide 3 u)).2.val=0 :=
          (hBCaxis _).mp ((hdecode _).symm ▸ hcontact)
        have hd := actual_local_boundary_normal_root_degree_one coordinate (localA k) (localArc k)
          hdegree 3 u hu hzero δ hδ (by
            intro v w hvl hvh hwl hwh
            obtain ⟨hvT,hwT,hf⟩ := hflip v w hvl hvh hwl hwh
            exact hf)
        exact hd
      have hOriginalBottomNodeClear (j : Fin (preparedN+1))
          (ht0 : 0<(actualHalfMeshParameter preparedN hpreparedN ⟨2*j.val,Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt))⟩).val)
          (ht1 : (actualHalfMeshParameter preparedN hpreparedN ⟨2*j.val,Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt))⟩).val < 1) :
          G (0,actualHalfMeshParameter preparedN hpreparedN ⟨2*j.val,Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt))⟩)∉a.val.image := by
        have hnR : (0:ℝ)<preparedN := by exact_mod_cast hpreparedN
        have hj : 0<j.val ∧ j.val<preparedN := by
          rw [actual_half_mesh_parameter_vertex] at ht0 ht1
          exact ⟨by exact_mod_cast (div_pos_iff_of_pos_right hnR).mp ht0,
            by exact_mod_cast (div_lt_one hnR).mp ht1⟩
        have hc := hpreparedVertices 0 j (Or.inr hj)
        have hzero : actualHalfMeshParameter preparedN hpreparedN ⟨2*(0:Fin (preparedN+1)).val,by omega⟩=0 := by
          apply Subtype.ext
          rw [actual_half_mesh_parameter_vertex]
          norm_num
        have he := hpreparedBoundary (0,actualHalfMeshParameter preparedN hpreparedN ⟨2*j.val,Nat.lt_succ_of_le (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt))⟩) 1 (Or.inl rfl)
        intro hmem
        apply hc
        simpa only [hzero] using he.symm ▸ hmem
      have hGlobalOpenBottomDegree (t : Interval) (ht0 : 0<t.val) (ht1 : t.val < 1)
          (hcontact : actualFinal (0,t)∈a.val.image) :
          {r : (Σ k,localA k) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=(0,t)}.ncard=1 := by
        have hOriginalContact : G (0,t)∈a.val.image := by
          have hlit := hActualGridBoundary (0,t) 1 (Or.inl rfl)
          exact hlit ▸ hcontact
        obtain ⟨i,u,he⟩ := ArcFinitePosition.intervalMeshParameter_cover preparedN hpreparedN t
        have hu0 : u≠0 := by
          intro hu
          have hnode : actualHalfMeshParameter preparedN hpreparedN ⟨2*i.castSucc.val,by omega⟩=t := by
            change actualHalfMeshParameter preparedN hpreparedN ⟨2*i.val,by omega⟩=t
            rw [actual_uniform_mesh_node_as_cell_start preparedN hpreparedN i,← hu]
            exact he
          exact hOriginalBottomNodeClear i.castSucc (by rw [hnode]; exact ht0)
            (by rw [hnode]; exact ht1) (hnode.symm ▸ hOriginalContact)
        have hu1 : u≠1 := by
          intro hu
          have hnode : actualHalfMeshParameter preparedN hpreparedN ⟨2*i.succ.val,by omega⟩=t := by
            rw [actual_uniform_mesh_node_as_cell_end preparedN hpreparedN i,← hu]
            exact he
          exact hOriginalBottomNodeClear i.succ (by rw [hnode]; exact ht0)
            (by rw [hnode]; exact ht1) (hnode.symm ▸ hOriginalContact)
        have hupos : 0<u.val ∧ u.val < 1 :=
          ⟨lt_of_le_of_ne u.property.1 (fun h => hu0 (Subtype.ext h.symm)),
            lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))⟩
        have hcellContact : actualCellFinal (⟨0,hpreparedN⟩,i) (0,u)∈a.val.image := by
          rw [hInitialCellLiteral,he]
          exact hOriginalContact
        have hd := hLocalOriginalBottomDegree i u hupos hcellContact
        have hs : {r : (Σ k,localA k) × Fin 2 |
            globalArcs r.1 (if r.2=0 then 0 else 1)=(0,t)}=
            {r : (Σ k,localA k) × Fin 2 |
              (ArcFinitePosition.intervalMeshParameter preparedN hpreparedN r.1.1.1
                (localArc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).1,
               ArcFinitePosition.intervalMeshParameter preparedN hpreparedN r.1.1.2
                (localArc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).2)=
              (0,ArcFinitePosition.intervalMeshParameter preparedN hpreparedN i u)} := by
          ext r
          simp only [Set.mem_ofPred_eq]
          rw [hGlobalArcParameter,he]
        rw [hs,actual_uniform_initial_boundary_endpoint_count preparedN hpreparedN localA localArc i u hupos]
        exact hd
      let Index := Σ k,localA k
      let _ : Fintype Index := Fintype.ofFinite Index
      let enc : Index ≃ Fin (Fintype.card Index) := Fintype.equivFin Index
      let edges : Finset ℕ := Finset.range (Fintype.card Index)
      let lift : ↑edges → Index := fun e => enc.symm ⟨e.val,Finset.mem_range.mp e.property⟩
      have hLiftInjective : Function.Injective lift := by
        intro e f he
        have hh := congrArg enc he
        change enc (enc.symm ⟨e.val,_⟩)=enc (enc.symm ⟨f.val,_⟩) at hh
        simp only [enc.apply_symm_apply] at hh
        exact Subtype.ext (congrArg Fin.val hh)
      have hLiftSurjective (e : Index) : ∃ f : ↑edges,lift f=e := by
        refine ⟨⟨(enc e).val,Finset.mem_range.mpr (enc e).isLt⟩,?_⟩
        exact enc.symm_apply_apply e
      let arcs : ↑edges → C(Interval,Interval × Interval) := fun e => globalArcs (lift e)
      have hArcsCoverage (z : Interval × Interval) : actualFinal z ∈ a.val.image ↔
          z ∈ globalVertices ∨ ∃ e t,arcs e t=z := by
        rw [hGlobalCoverage]
        constructor
        · rintro (hv | ⟨e,t,he⟩)
          · exact Or.inl hv
          · obtain ⟨f,hf⟩ := hLiftSurjective e
            exact Or.inr ⟨f,t,by change globalArcs (lift f) t=z; rw [hf]; exact he⟩
        · rintro (hv | ⟨e,t,he⟩)
          · exact Or.inl hv
          · exact Or.inr ⟨lift e,t,he⟩
      have hArcsEndpointCount (z : Interval × Interval) :
          {r : ↑edges × Fin 2 | arcs r.1 (if r.2=0 then 0 else 1)=z}.ncard=
          {r : Index × Fin 2 | globalArcs r.1 (if r.2=0 then 0 else 1)=z}.ncard := by
        apply Set.ncard_congr (fun r _ => (lift r.1,r.2))
        · intro r hr
          exact hr
        · intro r q hr hq he
          have ha : r.1=q.1 := hLiftInjective (congrArg Prod.fst he)
          have hb : r.2=q.2 := congrArg (fun x : Index × Fin 2 => x.2) he
          exact Prod.ext ha hb
        · rintro ⟨e,bit⟩ he
          obtain ⟨f,hf⟩ := hLiftSurjective e
          refine ⟨(f,bit),?_,Prod.ext hf rfl⟩
          change globalArcs (lift f) (if bit=0 then 0 else 1)=z
          rw [hf]
          exact he
      refine ⟨globalVertices,edges,arcs,(fun e => hGlobalEmbed (lift e)),
        (fun e => hGlobalEnds (lift e)),(fun e t => hGlobalClear (lift e) t),
        ?_,hArcsCoverage,hGlobalBoundary,?_⟩
      · intro e f t u he
        rcases hGlobalCollision (lift e) (lift f) t u he with ⟨hef,htu⟩ | hh
        · exact Or.inl ⟨hLiftInjective hef,htu⟩
        · exact Or.inr hh
      · constructor
        · intro v hv0 hv1 hv2 hv3
          rw [hArcsEndpointCount]
          exact hGlobalInteriorDegree v hv0 hv1 hv2 hv3
        · have hBottomCornerDegree : ∀ t : Interval,t=0 ∨ t=1 → actualFinal (0,t)∈a.val.image →
              {r : ↑edges × Fin 2 | arcs r.1 (if r.2=0 then 0 else 1)=(0,t)}.ncard=1 := by
            intro t ht hcontact
            have hlit := hActualGridBoundary (0,t) 1 (Or.inl rfl)
            change actualGridSurfaceMovie ((0,t),1) ∈ a.val.image at hcontact
            rw [hlit] at hcontact
            rcases ht with ht | ht
            · subst t
              exact (hcorner0 hcontact).elim
            · subst t
              exact (hcorner1 hcontact).elim
          intro t ht
          by_cases ht0 : t=0
          · exact hBottomCornerDegree t (Or.inl ht0) ht
          · by_cases ht1 : t=1
            · exact hBottomCornerDegree t (Or.inr ht1) ht
            · rw [hArcsEndpointCount]
              exact hGlobalOpenBottomDegree t
                (lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm)))
                (lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))) ht
  obtain ⟨G',R,hRstart,hRend,hRboundary,hRmarks,vertices,edges,arc,
    hEmbed,hEnds,hClear,hCollision,hCoverage,hBoundary,hInterior,hBottomDegree⟩ := hDrawing
  have hFinalBoundary (z : Interval × Interval)
      (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) : G' z=G z := by
    rw [← hRend z]
    exact hRboundary 1 z hz
  have hFinalBottom (t : Interval) : G' (0,t)=b.val.map (φ t) := by
    rw [hFinalBoundary (0,t) (Or.inl rfl)]
    exact hbottom t
  have hFinalMarks (z : Interval × Interval) : G' z ∉ (M.cover.branch : Set S) := by
    rw [← hRend z]
    exact hRmarks ((1,z.1),z.2)
  have hFinalTop (t : Interval) : G' (1,t) ∉ a.val.image := by
    rw [hFinalBoundary (1,t) (Or.inr (Or.inl rfl))]
    exact htop t
  -- The original K/J0/J1/W/phi/G and this same relative R are retained locally.
  -- No independently chosen movie or component is identified with them.
  let actualContactVertices : Set (Interval × Interval) := vertices
  have hActualContactVerticesFinite : actualContactVertices.Finite := vertices.finite_toSet
  let actualGlobalContactArcs : (↑edges) → C(Interval,Interval × Interval) := arc
  let actualFiniteConeSweep := G'
  have hActualFiniteConeSweepMarks := hFinalMarks
  have hActualGlobalContactArcEmbedding := hEmbed
  have hActualContactArcStartInVertices (e : (↑edges)) :
      actualGlobalContactArcs e 0∈actualContactVertices := (hEnds e).1
  have hActualContactArcEndInVertices (e : (↑edges)) :
      actualGlobalContactArcs e 1∈actualContactVertices := (hEnds e).2
  have hActualContactVerticesImage (v : actualContactVertices) :
      actualFiniteConeSweep v.val∈a.val.image := (hCoverage v.val).mpr (Or.inl v.property)
  have hActualGlobalContactArcImage (e : (↑edges)) (t : Interval) :
      actualFiniteConeSweep (actualGlobalContactArcs e t)∈a.val.image :=
    (hCoverage _).mpr (Or.inr ⟨e,t,rfl⟩)
  have hActualContactArcCollisionClassification := hCollision
  have hActualGlobalContactArcInteriorAvoidVertices (e : (↑edges))
      (t : Interval) (ht : t∈Set.Ioo (0 : Interval) 1) :
      actualGlobalContactArcs e t∉actualContactVertices := hClear e t (ne_of_gt ht.1) (ne_of_lt ht.2)
  have hActualGlobalContactArcInteriorsDisjoint (e f : (↑edges)) (t u : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) (hu : u∈Set.Ioo (0 : Interval) 1)
      (he : actualGlobalContactArcs e t=actualGlobalContactArcs f u) : e=f := by
    rcases hCollision e f t u he with h | h
    · exact h.1
    · exact False.elim (h.1.elim (ne_of_gt ht.1) (ne_of_lt ht.2))
  let actualIntervalSegment (x y : Interval) : C(Interval,Interval) := {
    toFun := fun t => ⟨(1-t.val)*x.val+t.val*y.val,by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property.1)
          (mul_nonneg t.property.1 y.property.1)
      · nlinarith only [t.property.1,t.property.2,x.property.2,y.property.2]⟩
    continuous_toFun := by fun_prop }
  have actualIntervalSegmentInjective (x y : Interval) (hxy : x<y) :
      Function.Injective (actualIntervalSegment x y) := by
    as_aux_lemma =>
      intro t u he
      have hh := congrArg Subtype.val he
      change (1-t.val)*x.val+t.val*y.val=(1-u.val)*x.val+u.val*y.val at hh
      have hxyR : x.val<y.val := hxy
      apply Subtype.ext
      nlinarith only [hh,hxyR]
  have actualIntervalSegmentBounds (x y : Interval) (hxy : x<y) (t : Interval) :
      x≤actualIntervalSegment x y t ∧ actualIntervalSegment x y t≤y := by
    as_aux_lemma =>
      have hxyR : x.val<y.val := hxy
      change x.val≤(1-t.val)*x.val+t.val*y.val ∧ (1-t.val)*x.val+t.val*y.val≤y.val
      constructor <;> nlinarith only [hxyR,t.property.1,t.property.2]
  let actualPairSchoenflies : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let actualParameterSquarePlane : C(Interval × Interval,Schoenflies.Plane) :=
    ⟨fun z => actualPairSchoenflies (z.1.val,z.2.val),by fun_prop⟩
  have hActualParameterSquarePlaneInjective : Function.Injective actualParameterSquarePlane := by
    as_aux_lemma =>
      intro z w he
      have hh := actualPairSchoenflies.injective he
      exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  have hActualParameterSquarePlaneEmbedding : IsEmbedding actualParameterSquarePlane :=
    (actualParameterSquarePlane.continuous.isClosedEmbedding hActualParameterSquarePlaneInjective).isEmbedding
  let actualContactPlaneArc (e : (↑edges)) : C(Interval,Schoenflies.Plane) :=
    actualParameterSquarePlane.comp (actualGlobalContactArcs e)
  have hActualContactPlaneArcEmbedding (e : (↑edges)) :
      IsEmbedding (actualContactPlaneArc e) :=
    hActualParameterSquarePlaneEmbedding.comp (hActualGlobalContactArcEmbedding e)
  let actualContactPlaneVertices : Set Schoenflies.Plane :=
    actualParameterSquarePlane '' actualContactVertices
  have hActualContactPlaneVerticesFinite : actualContactPlaneVertices.Finite :=
    hActualContactVerticesFinite.image actualParameterSquarePlane
  have hActualContactPlaneStart (e : (↑edges)) :
      actualContactPlaneArc e 0∈actualContactPlaneVertices :=
    ⟨actualGlobalContactArcs e 0,hActualContactArcStartInVertices e,rfl⟩
  have hActualContactPlaneEnd (e : (↑edges)) :
      actualContactPlaneArc e 1∈actualContactPlaneVertices :=
    ⟨actualGlobalContactArcs e 1,hActualContactArcEndInVertices e,rfl⟩
  have hActualContactPlaneArcInteriorAvoidVertices (e : (↑edges)) (t : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) :
      actualContactPlaneArc e t∉actualContactPlaneVertices := by
    as_aux_lemma =>
      rintro ⟨v,hv,he⟩
      have hpoint : v=actualGlobalContactArcs e t :=
        hActualParameterSquarePlaneInjective he
      exact hActualGlobalContactArcInteriorAvoidVertices e t ht (hpoint ▸ hv)
  have hActualContactPlaneArcCollisionClassification (e f : (↑edges))
      (t u : Interval) (he : actualContactPlaneArc e t=actualContactPlaneArc f u) :
      (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) :=
    hActualContactArcCollisionClassification e f t u (hActualParameterSquarePlaneInjective he)
  let actualContactPlanePath (e : (↑edges)) :
      Path (actualContactPlaneArc e 0) (actualContactPlaneArc e 1) := {
    toFun := actualContactPlaneArc e
    continuous_toFun := (actualContactPlaneArc e).continuous
    source' := rfl
    target' := rfl }
  have hActualContactPlanePathEmbedding (e : (↑edges)) :
      IsEmbedding (actualContactPlanePath e) := hActualContactPlaneArcEmbedding e
  have hActualContactPlanePathEndpointsDistinct (e : (↑edges)) :
      actualContactPlanePath e 0≠actualContactPlanePath e 1 := by
    as_aux_lemma =>
      intro he
      have h := (hActualContactPlanePathEmbedding e).injective he
      exact zero_ne_one (congrArg Subtype.val h)
  letI : Fintype (↑edges) := Fintype.ofFinite _
  letI : Fintype actualContactVertices := hActualContactVerticesFinite.fintype
  let zeroVertex := Sum actualContactVertices ((↑edges) × Fin 2)
  letI : Fintype zeroVertex := Fintype.ofFinite zeroVertex
  let zeroLeftVertex (e : (↑edges)) : zeroVertex :=
    Sum.inl ⟨actualGlobalContactArcs e 0,hActualContactArcStartInVertices e⟩
  let zeroRightVertex (e : (↑edges)) : zeroVertex :=
    Sum.inl ⟨actualGlobalContactArcs e 1,hActualContactArcEndInVertices e⟩
  let zeroDirectedIncidence : zeroVertex → zeroVertex → Prop := fun v w => ∃ e : (↑edges),
    (v = zeroLeftVertex e ∧ w = Sum.inr (e,0)) ∨
    (v = Sum.inr (e,0) ∧ w = Sum.inr (e,1)) ∨
    (v = Sum.inr (e,1) ∧ w = zeroRightVertex e)
  let actualZeroGraph : SimpleGraph zeroVertex := SimpleGraph.fromRel zeroDirectedIncidence
  letI : DecidableRel actualZeroGraph.Adj := Classical.decRel _
  have zeroGraphLeftAdj (e : (↑edges)) :
      actualZeroGraph.Adj (zeroLeftVertex e) (Sum.inr (e,0)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inl ⟨rfl,rfl⟩⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  have zeroGraphMiddleAdj (e : (↑edges)) :
      actualZeroGraph.Adj (Sum.inr (e,0)) (Sum.inr (e,1)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩⟩
    intro he
    have hh := congrArg Prod.snd (Sum.inr.inj he)
    norm_num at hh
  have zeroGraphRightAdj (e : (↑edges)) :
      actualZeroGraph.Adj (Sum.inr (e,1)) (zeroRightVertex e) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  have zeroSubdivisionNeighborsLeft (e : (↑edges)) :
      actualZeroGraph.neighborFinset (Sum.inr (e,0)) =
        {zeroLeftVertex e,Sum.inr (e,1)} := by
    as_aux_lemma =>
      ext v
      rcases v with p | ⟨e',j⟩
      · simp [-Subtype.exists,SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
      · fin_cases j <;>
          simp [-Subtype.exists,SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
            zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  have zeroSubdivisionNeighborsRight (e : (↑edges)) :
      actualZeroGraph.neighborFinset (Sum.inr (e,1)) =
        {Sum.inr (e,0),zeroRightVertex e} := by
    as_aux_lemma =>
      ext v
      rcases v with p | ⟨e',j⟩
      · simp [-Subtype.exists,SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
      · fin_cases j <;>
          simp [-Subtype.exists,SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
            zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  let leftIncidentEdges (p : actualContactVertices) : Finset (↑edges) :=
    Finset.univ.filter (fun e => Sum.inl p = zeroLeftVertex e)
  let rightIncidentEdges (p : actualContactVertices) : Finset (↑edges) :=
    Finset.univ.filter (fun e => Sum.inl p = zeroRightVertex e)
  have zeroEndpointNeighbors (p : actualContactVertices) :
      actualZeroGraph.neighborFinset (Sum.inl p) =
        (leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) ∪
        (rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
    as_aux_lemma =>
      ext v
      rcases v with q | ⟨e,j⟩
      · simp [-Subtype.exists,SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,leftIncidentEdges,rightIncidentEdges,
          zeroLeftVertex,zeroRightVertex,zeroVertex]
      · fin_cases j <;>
          simp [-Subtype.exists,SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
            zeroDirectedIncidence,leftIncidentEdges,rightIncidentEdges,
            zeroLeftVertex,zeroRightVertex,zeroVertex,
            Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq]
  have zeroEndpointDegreeExact (p : actualContactVertices) :
      actualZeroGraph.degree (Sum.inl p) =
        (leftIncidentEdges p).card + (rightIncidentEdges p).card := by
    as_aux_lemma =>
      change (actualZeroGraph.neighborFinset (Sum.inl p)).card = _
      rw [zeroEndpointNeighbors]
      have hd : Disjoint
          ((leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)))
          ((rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex))) := by
        apply Finset.disjoint_left.mpr
        intro v hv hw
        obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨f,hf,h⟩ := Finset.mem_image.mp hw
        have hh := congrArg (fun v : (↑edges) × Fin 2 => v.2) (Sum.inr.inj h)
        norm_num at hh
      rw [Finset.card_union_of_disjoint hd]
      have hi0 : Function.Injective (fun e : (↑edges) => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) := by
        intro e f h
        exact congrArg Prod.fst (Sum.inr.inj h)
      have hi1 : Function.Injective (fun e : (↑edges) => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
        intro e f h
        exact congrArg Prod.fst (Sum.inr.inj h)
      rw [Finset.card_image_of_injective _ hi0,Finset.card_image_of_injective _ hi1]
  have zeroSubdivisionDegrees (e : (↑edges)) :
      actualZeroGraph.degree (Sum.inr (e,0)) = 2 ∧
      actualZeroGraph.degree (Sum.inr (e,1)) = 2 := by
    as_aux_lemma =>
      change (actualZeroGraph.neighborFinset (Sum.inr (e,0))).card = 2 ∧
        (actualZeroGraph.neighborFinset (Sum.inr (e,1))).card = 2
      rw [zeroSubdivisionNeighborsLeft,zeroSubdivisionNeighborsRight]
      simp [zeroLeftVertex,zeroRightVertex]
  let privateParameter : Fin 2 → Interval := fun j =>
    if j=0 then ⟨1/3,by norm_num⟩ else ⟨2/3,by norm_num⟩
  have privateParameterInterior (j : Fin 2) :
      privateParameter j∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      change 0<(privateParameter j).val ∧ (privateParameter j).val<1
      fin_cases j <;> norm_num [privateParameter]
  have privateParameterInjective : Function.Injective privateParameter := by
    as_aux_lemma =>
      intro j k he
      have hh := congrArg Subtype.val he
      fin_cases j <;> fin_cases k <;> first | rfl | (norm_num [privateParameter] at hh)
  let zeroVertexPosition : zeroVertex → Interval × Interval := fun v =>
    match v with
    | Sum.inl p => p.val
    | Sum.inr (e,j) => actualGlobalContactArcs e (privateParameter j)
  have zeroVertexPositionInjective : Function.Injective zeroVertexPosition := by
    as_aux_lemma =>
      intro v w he
      rcases v with p | ⟨e,j⟩ <;> rcases w with q | ⟨f,k⟩
      · exact congrArg Sum.inl (Subtype.ext he)
      · change p.val=actualGlobalContactArcs f (privateParameter k) at he
        have hh : actualGlobalContactArcs f (privateParameter k)∈actualContactVertices :=
          he ▸ p.property
        exact False.elim (hActualGlobalContactArcInteriorAvoidVertices f _ (privateParameterInterior k) hh)
      · change actualGlobalContactArcs e (privateParameter j)=q.val at he
        have hh : actualGlobalContactArcs e (privateParameter j)∈actualContactVertices :=
          he.symm ▸ q.property
        exact False.elim (hActualGlobalContactArcInteriorAvoidVertices e _ (privateParameterInterior j) hh)
      · have hef : e=f := hActualGlobalContactArcInteriorsDisjoint e f _ _
          (privateParameterInterior j) (privateParameterInterior k) he
        subst f
        have hjk := privateParameterInjective ((hActualGlobalContactArcEmbedding e).injective he)
        subst k
        rfl
  let actualPlanarVertexPosition (v : zeroVertex) : Schoenflies.Plane :=
    actualParameterSquarePlane (zeroVertexPosition v)
  have actualPlanarVertexPositionInjective : Function.Injective actualPlanarVertexPosition :=
    hActualParameterSquarePlaneInjective.comp zeroVertexPositionInjective
  have hActualContactGraphVertexImage (v : zeroVertex) :
      actualFiniteConeSweep (zeroVertexPosition v)∈a.val.image := by
    as_aux_lemma =>
      rcases v with p | ⟨e,j⟩
      · exact hActualContactVerticesImage p
      · exact hActualGlobalContactArcImage e _
  have hActualContactGraphVertexMarks (v : zeroVertex) :
      actualFiniteConeSweep (zeroVertexPosition v)∉(M.cover.branch : Set S) :=
    hActualFiniteConeSweepMarks _
  have actualPrivateParametersOrdered :
      (0 : Interval)<privateParameter 0 ∧ privateParameter 0<privateParameter 1 ∧
        privateParameter 1<(1 : Interval) := by
    as_aux_lemma =>
      change 0<(privateParameter 0).val ∧ (privateParameter 0).val<(privateParameter 1).val ∧
        (privateParameter 1).val<1
      norm_num [privateParameter]
  let actualSegmentStartParameter (q : (↑edges) × Fin 3) : Interval :=
    if q.2=0 then 0 else if q.2=1 then privateParameter 0 else privateParameter 1
  let actualSegmentEndParameter (q : (↑edges) × Fin 3) : Interval :=
    if q.2=0 then privateParameter 0 else if q.2=1 then privateParameter 1 else 1
  let actualSegmentStartVertex (q : (↑edges) × Fin 3) : zeroVertex :=
    if q.2=0 then zeroLeftVertex q.1 else if q.2=1 then Sum.inr (q.1,0) else Sum.inr (q.1,1)
  let actualSegmentEndVertex (q : (↑edges) × Fin 3) : zeroVertex :=
    if q.2=0 then Sum.inr (q.1,0) else if q.2=1 then Sum.inr (q.1,1) else zeroRightVertex q.1
  have actualSegmentParameterOrder (q : (↑edges) × Fin 3) :
      actualSegmentStartParameter q<actualSegmentEndParameter q := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j
      · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.1
      · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.1
      · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.2
  let actualSegmentSquarePath (q : (↑edges) × Fin 3) :
      Path (actualGlobalContactArcs q.1 (actualSegmentStartParameter q))
        (actualGlobalContactArcs q.1 (actualSegmentEndParameter q)) := {
    toFun := fun t => actualGlobalContactArcs q.1
      (actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q) t)
    continuous_toFun := (actualGlobalContactArcs q.1).continuous.comp
      (actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q)).continuous
    source' := by
      apply congrArg (actualGlobalContactArcs q.1)
      apply Subtype.ext
      change (1-(0 : ℝ))*(actualSegmentStartParameter q).val+0*(actualSegmentEndParameter q).val=
        (actualSegmentStartParameter q).val
      ring
    target' := by
      apply congrArg (actualGlobalContactArcs q.1)
      apply Subtype.ext
      change (1-(1 : ℝ))*(actualSegmentStartParameter q).val+1*(actualSegmentEndParameter q).val=
        (actualSegmentEndParameter q).val
      ring }
  have actualSegmentSquarePathEmbedding (q : (↑edges) × Fin 3) :
      IsEmbedding (actualSegmentSquarePath q) :=
    (hActualGlobalContactArcEmbedding q.1).comp
      (((actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q)).continuous.isClosedEmbedding (actualIntervalSegmentInjective _ _ (actualSegmentParameterOrder q))).isEmbedding)
  have actualSegmentSquarePathRange (q : (↑edges) × Fin 3) :
      Set.range (actualSegmentSquarePath q)⊆actualGlobalContactArcs q.1 ''
        Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q) := by
    as_aux_lemma =>
      rintro z ⟨t,rfl⟩
      refine ⟨actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q) t,?_,rfl⟩
      exact actualIntervalSegmentBounds _ _ (actualSegmentParameterOrder q) t
  have actualSegmentStartPosition (q : (↑edges) × Fin 3) :
      zeroVertexPosition (actualSegmentStartVertex q)=
        actualGlobalContactArcs q.1 (actualSegmentStartParameter q) := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> simp [actualSegmentStartVertex,actualSegmentStartParameter,
        zeroVertexPosition,zeroLeftVertex] <;> rfl
  have actualSegmentEndPosition (q : (↑edges) × Fin 3) :
      zeroVertexPosition (actualSegmentEndVertex q)=
        actualGlobalContactArcs q.1 (actualSegmentEndParameter q) := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> simp [actualSegmentEndVertex,actualSegmentEndParameter,
        zeroVertexPosition,zeroRightVertex] <;> rfl
  let actualSegmentPlanarPath (q : (↑edges) × Fin 3) :
      Path (actualParameterSquarePlane (actualGlobalContactArcs q.1 (actualSegmentStartParameter q)))
        (actualParameterSquarePlane (actualGlobalContactArcs q.1 (actualSegmentEndParameter q))) :=
    (actualSegmentSquarePath q).map actualParameterSquarePlane.continuous
  have actualSegmentPlanarPathEmbedding (q : (↑edges) × Fin 3) :
      IsEmbedding (actualSegmentPlanarPath q) :=
    hActualParameterSquarePlaneEmbedding.comp (actualSegmentSquarePathEmbedding q)
  have actualSegmentPlanarSource (q : (↑edges) × Fin 3) :
      actualSegmentPlanarPath q 0=actualPlanarVertexPosition (actualSegmentStartVertex q) := by
    as_aux_lemma =>
      rw [Path.source]
      exact congrArg actualParameterSquarePlane (actualSegmentStartPosition q).symm
  have actualSegmentPlanarTarget (q : (↑edges) × Fin 3) :
      actualSegmentPlanarPath q 1=actualPlanarVertexPosition (actualSegmentEndVertex q) := by
    as_aux_lemma =>
      rw [Path.target]
      exact congrArg actualParameterSquarePlane (actualSegmentEndPosition q).symm
  let actualPlanarGraph : Graph Schoenflies.Plane ((↑edges) × Fin 3) := {
    vertexSet := Set.range actualPlanarVertexPosition
    edgeSet := Set.univ
    IsLink := fun q x y =>
      (x = actualSegmentPlanarPath q 0 ∧ y = actualSegmentPlanarPath q 1) ∨
      (x = actualSegmentPlanarPath q 1 ∧ y = actualSegmentPlanarPath q 0)
    isLink_symm := by
      intro q hq
      constructor
      intro x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inr ⟨hy,hx⟩
      · exact Or.inl ⟨hy,hx⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro q x y z w hx hz
      rcases hx with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;>
        rcases hz with ⟨hz,hw⟩ | ⟨hz,hw⟩
      · exact Or.inl (hx.trans hz.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inl (hx.trans hz.symm)
    edge_mem_iff_exists_isLink := by
      intro q
      constructor
      · intro hq
        exact ⟨actualSegmentPlanarPath q 0,actualSegmentPlanarPath q 1,Or.inl ⟨rfl,rfl⟩⟩
      · intro hq
        exact Set.mem_univ _
    left_mem_of_isLink := by
      intro q x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact ⟨actualSegmentStartVertex q,(actualSegmentPlanarSource q).symm.trans hx.symm⟩
      · exact ⟨actualSegmentEndVertex q,(actualSegmentPlanarTarget q).symm.trans hx.symm⟩ }
  let actualPlanarDrawing (q : (↑edges) × Fin 3) : ℝ → Schoenflies.Plane :=
    (actualSegmentPlanarPath q).extend
  have actualPlanarEdgeParameter (q : (↑edges) × Fin 3) :
      ContinuousOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      actualPlanarGraph.IsLink q (actualPlanarDrawing q 0) (actualPlanarDrawing q 1) := by
    as_aux_lemma =>
      refine ⟨(actualSegmentPlanarPath q).continuous_extend.continuousOn,?_,?_⟩
      · intro s hs t ht he
        change (actualSegmentPlanarPath q).extend s = (actualSegmentPlanarPath q).extend t at he
        rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
        exact congrArg Subtype.val ((actualSegmentPlanarPathEmbedding q).injective he)
      · change (actualPlanarDrawing q 0 = actualSegmentPlanarPath q 0 ∧
          actualPlanarDrawing q 1 = actualSegmentPlanarPath q 1) ∨ _
        exact Or.inl ⟨by simp [actualPlanarDrawing],by simp [actualPlanarDrawing]⟩
  have actualZeroVertexOnEdgeBreakpoint (v : zeroVertex) (e : (↑edges))
      (t : Interval) (he : zeroVertexPosition v=actualGlobalContactArcs e t) :
      t=0 ∨ t=privateParameter 0 ∨ t=privateParameter 1 ∨ t=1 := by
    as_aux_lemma =>
      rcases v with p | ⟨f,j⟩
      · by_cases ht0 : t=0
        · exact Or.inl ht0
        by_cases ht1 : t=1
        · exact Or.inr (Or.inr (Or.inr ht1))
        have ht : t∈Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
        change p.val=actualGlobalContactArcs e t at he
        exact False.elim (hActualGlobalContactArcInteriorAvoidVertices e t ht (he ▸ p.property))
      · change actualGlobalContactArcs f (privateParameter j)=actualGlobalContactArcs e t at he
        rcases hActualContactArcCollisionClassification f e _ t he with ⟨hfe,ht⟩ | ⟨hf,ht⟩
        · fin_cases j
          · exact Or.inr (Or.inl ht.symm)
          · exact Or.inr (Or.inr (Or.inl ht.symm))
        · rcases hf with hf | hf
          · exact False.elim ((ne_of_gt (privateParameterInterior j).1) hf)
          · exact False.elim ((ne_of_lt (privateParameterInterior j).2) hf)
  have actualSegmentStartValue (q : (↑edges) × Fin 3) :
      (actualSegmentStartParameter q).val=CurveComplex.LocalSurgery.actualThreeSegmentStart q.2 := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> norm_num [actualSegmentStartParameter,privateParameter,
        CurveComplex.LocalSurgery.actualThreeSegmentStart]
  have actualSegmentEndValue (q : (↑edges) × Fin 3) :
      (actualSegmentEndParameter q).val=CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2 := by
    as_aux_lemma =>
      rcases q with ⟨e,j⟩
      fin_cases j <;> norm_num [actualSegmentEndParameter,privateParameter,
        CurveComplex.LocalSurgery.actualThreeSegmentEnd]
  have actualSegmentBreakpointIsEndpoint (q : (↑edges) × Fin 3) (u : Interval)
      (hu : u∈Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hb : u=0 ∨ u=privateParameter 0 ∨ u=privateParameter 1 ∨ u=1) :
      u=actualSegmentStartParameter q ∨ u=actualSegmentEndParameter q := by
    as_aux_lemma =>
      have hreal : u.val∈Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart q.2)
          (CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2) := by
        rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
        exact hu
      have hbReal : u.val=0 ∨ u.val=1/3 ∨ u.val=2/3 ∨ u.val=1 := by
        rcases hb with rfl | rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (by norm_num [privateParameter]))
        · exact Or.inr (Or.inr (Or.inl (by norm_num [privateParameter])))
        · exact Or.inr (Or.inr (Or.inr rfl))
      rcases CurveComplex.LocalSurgery.actualThreeSegment_breakpoint_is_endpoint q.2 u.val hreal hbReal with h | h
      · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
      · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
  have actualDistinctSegmentParameterIntersection (q r : (↑edges) × Fin 3)
      (hj : q.2 ≠ r.2) (u : Interval)
      (hu : u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hv : u ∈ Set.Icc (actualSegmentStartParameter r) (actualSegmentEndParameter r)) :
      (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
        (u = actualSegmentStartParameter r ∨ u = actualSegmentEndParameter r) := by
    as_aux_lemma =>
      have huReal : u.val ∈ Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart q.2) (CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2) := by
        rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
        exact hu
      have hvReal : u.val ∈ Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart r.2) (CurveComplex.LocalSurgery.actualThreeSegmentEnd r.2) := by
        rw [←actualSegmentStartValue r,←actualSegmentEndValue r]
        exact hv
      obtain ⟨hq,hr⟩ := CurveComplex.LocalSurgery.actualThreeSegment_distinct_intersection q.2 r.2 hj u.val huReal hvReal
      constructor
      · rcases hq with h | h
        · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
        · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
      · rcases hr with h | h
        · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue r).symm))
        · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue r).symm))
  have actualPlanarEdgeArcParameter (q : (↑edges) × Fin 3) (z : Schoenflies.Plane)
      (hz : z ∈ Graph.edgeArc actualPlanarDrawing q) :
      ∃ u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q),
        actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = z := by
    as_aux_lemma =>
      obtain ⟨s,hs,he⟩ := hz
      change (actualSegmentPlanarPath q).extend s = z at he
      rw [Path.extend_apply _ hs] at he
      obtain ⟨u,hu,hup⟩ := actualSegmentSquarePathRange q ⟨⟨s,hs⟩,rfl⟩
      exact ⟨u,hu,(congrArg actualParameterSquarePlane hup).trans he⟩
  have actualSegmentEndpointPlanarPosition (q : (↑edges) × Fin 3) (u : Interval)
      (hu : u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) :
      actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = actualSegmentPlanarPath q 0 ∨
        actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = actualSegmentPlanarPath q 1 := by
    as_aux_lemma =>
      rcases hu with rfl | rfl
      · exact Or.inl (Path.source _).symm
      · exact Or.inr (Path.target _).symm
  have actualSegmentVertexOnArcIsEndpoint (q : (↑edges) × Fin 3) (v : zeroVertex)
      (hv : actualPlanarVertexPosition v ∈ Graph.edgeArc actualPlanarDrawing q) :
      actualPlanarVertexPosition v = actualSegmentPlanarPath q 0 ∨
        actualPlanarVertexPosition v = actualSegmentPlanarPath q 1 := by
    as_aux_lemma =>
      obtain ⟨u,hu,he⟩ := actualPlanarEdgeArcParameter q _ hv
      have hpoint : zeroVertexPosition v = actualGlobalContactArcs q.1 u :=
        (hActualParameterSquarePlaneInjective he).symm
      have hb := actualZeroVertexOnEdgeBreakpoint v q.1 u hpoint
      have hend := actualSegmentBreakpointIsEndpoint q u hu hb
      rw [←he]
      exact actualSegmentEndpointPlanarPosition q u hend
  have actualDistinctSegmentArcIntersection (q r : (↑edges) × Fin 3)
      (hqr : q ≠ r) (z : Schoenflies.Plane)
      (hq : z ∈ Graph.edgeArc actualPlanarDrawing q)
      (hr : z ∈ Graph.edgeArc actualPlanarDrawing r) :
      (z = actualSegmentPlanarPath q 0 ∨ z = actualSegmentPlanarPath q 1) ∧
        (z = actualSegmentPlanarPath r 0 ∨ z = actualSegmentPlanarPath r 1) := by
    as_aux_lemma =>
      obtain ⟨u,hu,hup⟩ := actualPlanarEdgeArcParameter q z hq
      obtain ⟨v,hv,hvp⟩ := actualPlanarEdgeArcParameter r z hr
      have he : actualGlobalContactArcs q.1 u = actualGlobalContactArcs r.1 v :=
        hActualParameterSquarePlaneInjective (hup.trans hvp.symm)
      have hends : (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
          (v = actualSegmentStartParameter r ∨ v = actualSegmentEndParameter r) := by
        rcases hActualContactArcCollisionClassification q.1 r.1 u v he with ⟨hedge,huv⟩ | ⟨hu0,hv0⟩
        · have hj : q.2 ≠ r.2 := by
            intro hj
            exact hqr (Prod.ext hedge hj)
          subst v
          exact actualDistinctSegmentParameterIntersection q r hj u hu hv
        · have hbu : u = 0 ∨ u = privateParameter 0 ∨ u = privateParameter 1 ∨ u = 1 := by
            rcases hu0 with h0 | h1
            · exact Or.inl h0
            · exact Or.inr (Or.inr (Or.inr h1))
          have hbv : v = 0 ∨ v = privateParameter 0 ∨ v = privateParameter 1 ∨ v = 1 := by
            rcases hv0 with h0 | h1
            · exact Or.inl h0
            · exact Or.inr (Or.inr (Or.inr h1))
          exact ⟨actualSegmentBreakpointIsEndpoint q u hu hbu,
            actualSegmentBreakpointIsEndpoint r v hv hbv⟩
      constructor
      · rw [←hup]
        exact actualSegmentEndpointPlanarPosition q u hends.1
      · rw [←hvp]
        exact actualSegmentEndpointPlanarPosition r v hends.2
  have actualPlanarDrawingIsDrawing : Graph.IsDrawing actualPlanarGraph actualPlanarDrawing := by
    as_aux_lemma =>
      refine ⟨?_,?_,?_⟩
      · intro q hq
        exact actualPlanarEdgeParameter q
      · intro q x y z hlink hz hze
        obtain ⟨v,rfl⟩ := hz
        have hend := actualSegmentVertexOnArcIsEndpoint q v hze
        change (_ = actualSegmentPlanarPath q 0 ∧ _ = actualSegmentPlanarPath q 1) ∨
          (_ = actualSegmentPlanarPath q 1 ∧ _ = actualSegmentPlanarPath q 0) at hlink
        rcases hlink with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hend
        · exact hend.elim Or.inr Or.inl
      · intro q r hq hr hqr z hze hzr
        obtain ⟨hqend,hrend⟩ := actualDistinctSegmentArcIntersection q r hqr z hze hzr
        have hver : z ∈ actualPlanarGraph.vertexSet := by
          rcases hqend with h0 | h1
          · exact ⟨actualSegmentStartVertex q,(actualSegmentPlanarSource q).symm.trans h0.symm⟩
          · exact ⟨actualSegmentEndVertex q,(actualSegmentPlanarTarget q).symm.trans h1.symm⟩
        refine ⟨hver,?_,?_⟩
        · rcases hqend with h0 | h1
          · exact ⟨actualSegmentPlanarPath q 1,Or.inl ⟨h0,rfl⟩⟩
          · exact ⟨actualSegmentPlanarPath q 0,Or.inr ⟨h1,rfl⟩⟩
        · rcases hrend with h0 | h1
          · exact ⟨actualSegmentPlanarPath r 1,Or.inl ⟨h0,rfl⟩⟩
          · exact ⟨actualSegmentPlanarPath r 0,Or.inr ⟨h1,rfl⟩⟩
  have hOriginalEndpointNeighbor (v : actualContactVertices) (q : ↑edges × Fin 2) :
      (Sum.inr q : zeroVertex)∈actualZeroGraph.neighborSet (Sum.inl v) ↔
        actualGlobalContactArcs q.1 (if q.2=0 then 0 else 1)=v.val := by
    change actualZeroGraph.Adj (Sum.inl v) (Sum.inr q) ↔ _
    rw [← SimpleGraph.mem_neighborFinset,zeroEndpointNeighbors]
    constructor
    · intro hh
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hh
        have hq : (f,(0 : Fin 2))=q := Sum.inr.inj he
        rw [← hq]
        have hvf := (Finset.mem_filter.mp hf).2
        exact (congrArg Subtype.val (Sum.inl.inj hvf)).symm
      · obtain ⟨f,hf,he⟩ := Finset.mem_image.mp hh
        have hq : (f,(1 : Fin 2))=q := Sum.inr.inj he
        rw [← hq]
        have hvf := (Finset.mem_filter.mp hf).2
        exact (congrArg Subtype.val (Sum.inl.inj hvf)).symm
    · intro hh
      by_cases hbit : q.2=0
      · rw [if_pos hbit] at hh
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_image.mpr
        refine ⟨q.1,?_,?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,?_⟩
          apply congrArg Sum.inl
          exact Subtype.ext hh.symm
        · exact congrArg Sum.inr (Prod.ext rfl hbit.symm)
      · rw [if_neg hbit] at hh
        have hbit1 : q.2=1 := by
          apply Fin.ext
          have hz : q.2.val≠0 := fun h => hbit (Fin.ext h)
          have ht := q.2.isLt
          change q.2.val=1
          omega
        apply Finset.mem_union.mpr
        right
        apply Finset.mem_image.mpr
        refine ⟨q.1,?_,?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _,?_⟩
          apply congrArg Sum.inl
          exact Subtype.ext hh.symm
        · exact congrArg Sum.inr (Prod.ext rfl hbit1.symm)
  have hActualGraphDegreeFromOriginalEndpointCount (v : actualContactVertices) :
      actualZeroGraph.degree (Sum.inl v)=
        {q : ↑edges × Fin 2 | actualGlobalContactArcs q.1
          (if q.2=0 then 0 else 1)=v.val}.ncard := by
    have hc : {q : ↑edges × Fin 2 | actualGlobalContactArcs q.1
          (if q.2=0 then 0 else 1)=v.val}.ncard=
        (actualZeroGraph.neighborSet (Sum.inl v)).ncard := by
      apply Set.ncard_congr (fun q _ => (Sum.inr q : zeroVertex))
      · intro q hq
        exact (hOriginalEndpointNeighbor v q).mpr hq
      · intro q r hq hr he
        exact Sum.inr.inj he
      · intro u hu
        rcases u with w | q
        · have hh : Sum.inl w∈actualZeroGraph.neighborFinset (Sum.inl v) := by
            rw [SimpleGraph.mem_neighborFinset]
            exact hu
          rw [zeroEndpointNeighbors] at hh
          simp at hh
        · exact ⟨q,(hOriginalEndpointNeighbor v q).mp hu,rfl⟩
    simpa only [SimpleGraph.ncard_neighborSet] using hc.symm
  have hActualEveryOriginalCrossingProducesDegreeOne (t : Interval)
      (ht : b.val.map t∈crossings M a b) :
      ∃ w : actualContactVertices,actualFiniteConeSweep w.val=b.val.map t ∧
        w.val.1=0 ∧ actualZeroGraph.degree (Sum.inl w)=1 := by
    obtain ⟨s,hs⟩ := hcapture t ht
    have hcontact : G' (0,s)∈a.val.image := by
      rw [hFinalBottom,hs]
      exact ht.1.1
    have hd := hBottomDegree s hcontact
    obtain ⟨q,hq⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<
      {q : ↑edges × Fin 2 | arc q.1 (if q.2=0 then 0 else 1)=(0,s)}.ncard by rw [hd]; omega)
    have hv : (0,s)∈vertices := by
      by_cases hbit : q.2=0
      · have hh := (hEnds q.1).1
        change arc q.1 (if q.2=0 then 0 else 1)=(0,s) at hq
        rw [if_pos hbit] at hq
        exact hq ▸ hh
      · have hh := (hEnds q.1).2
        change arc q.1 (if q.2=0 then 0 else 1)=(0,s) at hq
        rw [if_neg hbit] at hq
        exact hq ▸ hh
    let w : actualContactVertices := ⟨(0,s),hv⟩
    refine ⟨w,?_,rfl,?_⟩
    · exact (hFinalBottom s).trans (congrArg b.val.map hs)
    · rw [hActualGraphDegreeFromOriginalEndpointCount]
      exact hd
  have hActualSpecifiedOriginalCrossingProducesOddVertex :
      ∃ w : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧
        Odd (actualZeroGraph.degree (Sum.inl w)) := by
    obtain ⟨t,ht⟩ := hp.2.1
    have hcross : b.val.map t∈crossings M a b := ht.symm ▸ hp
    obtain ⟨w,hw,hboundary,hdegree⟩ := hActualEveryOriginalCrossingProducesDegreeOne t hcross
    refine ⟨w,hw.trans ht,hboundary,?_⟩
    rw [hdegree]
    norm_num
  have hActualSpecifiedOriginalCrossingHasActualOddContactPartner :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ W : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),W.IsPath := by
    obtain ⟨w,hw,hboundary,hodd⟩ := hActualSpecifiedOriginalCrossingProducesOddVertex
    obtain ⟨v,hvw,hvodd,W,hW⟩ := CurveComplex.LocalSurgery.actual_odd_vertex_has_distinct_path_partner
      actualZeroGraph (Sum.inl w) hodd
    rcases v with z | ⟨e,j⟩
    · refine ⟨w,z,hw,hboundary,?_,hvodd,W,hW⟩
      intro he
      exact hvw (congrArg Sum.inl he)
    · fin_cases j
      · change Odd (actualZeroGraph.degree (Sum.inr (e,(0 : Fin 2)))) at hvodd
        rw [(zeroSubdivisionDegrees e).1] at hvodd
        norm_num at hvodd
      · change Odd (actualZeroGraph.degree (Sum.inr (e,(1 : Fin 2)))) at hvodd
        rw [(zeroSubdivisionDegrees e).2] at hvodd
        norm_num at hvodd
  have hActualPlanarSubedgeLink (q : (↑edges) × Fin 3) :
      actualPlanarGraph.IsLink q (actualPlanarVertexPosition (actualSegmentStartVertex q))
        (actualPlanarVertexPosition (actualSegmentEndVertex q)) :=
    Or.inl ⟨(actualSegmentPlanarSource q).symm,(actualSegmentPlanarTarget q).symm⟩
  have hActualDirectedContactIncidenceProducesPlanarLink (v w : zeroVertex)
      (h : zeroDirectedIncidence v w) :
      ∃ q,actualPlanarGraph.IsLink q (actualPlanarVertexPosition v) (actualPlanarVertexPosition w) := by
    as_aux_lemma =>
      rcases h with ⟨e,h⟩
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · refine ⟨(e,0),?_⟩
        simpa only [actualSegmentStartVertex,actualSegmentEndVertex,if_pos rfl] using hActualPlanarSubedgeLink (e,0)
      · refine ⟨(e,1),?_⟩
        simpa [actualSegmentStartVertex,actualSegmentEndVertex] using hActualPlanarSubedgeLink (e,1)
      · refine ⟨(e,2),?_⟩
        simpa [actualSegmentStartVertex,actualSegmentEndVertex] using hActualPlanarSubedgeLink (e,2)
  have hActualContactGraphAdjacencyProducesPlanarLink {v w : zeroVertex}
      (h : actualZeroGraph.Adj v w) :
      ∃ q,actualPlanarGraph.IsLink q (actualPlanarVertexPosition v) (actualPlanarVertexPosition w) := by
    as_aux_lemma =>
      rcases h.2 with h | h
      · exact hActualDirectedContactIncidenceProducesPlanarLink v w h
      · obtain ⟨q,hq⟩ := hActualDirectedContactIncidenceProducesPlanarLink w v h
        exact ⟨q,hq.symm⟩
  have hActualSpecifiedCrossingProducesEmbeddedPlanarContactCarrier :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          ∃ W : List ((↑edges) × Fin 3),W≠[] ∧
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
              (actualPlanarVertexPosition (Sum.inl z)) ∧
            actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
              actualPlanarVertexPosition '' {r | r∈P.support} ∧
            Schoenflies.IsArcBetween (Graph.edgesCover actualPlanarDrawing W)
              (actualPlanarVertexPosition (Sum.inl w)) (actualPlanarVertexPosition (Sum.inl z)) := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP⟩ := hActualSpecifiedOriginalCrossingHasActualOddContactPartner
      obtain ⟨W,hW,hvertices⟩ := CurveComplex.LocalSurgery.actual_simple_graph_path_to_labeled_graph_with_vertices
        actualZeroGraph actualPlanarGraph actualPlanarVertexPosition actualPlanarVertexPositionInjective
        (fun r => ⟨r,rfl⟩) (fun h => hActualContactGraphAdjacencyProducesPlanarLink h) P hP
      have hne : W≠[] := by
        intro hn
        rw [hn] at hW
        have he : (Sum.inl w : zeroVertex)=Sum.inl z := actualPlanarVertexPositionInjective hW.isWalk.eq_of_nil
        exact hzw (Sum.inl.inj he).symm
      exact ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,
        actualPlanarDrawingIsDrawing.path_isArcBetween hW hne⟩
  have hActualPlanarArcLiftsToEmbeddedParameterSquarePath
      (A : Set Schoenflies.Plane) (x y : Interval × Interval)
      (hA : Schoenflies.IsArcBetween A (actualParameterSquarePlane x) (actualParameterSquarePlane y))
      (hRange : A⊆Set.range actualParameterSquarePlane) :
      ∃ q : Path x y,IsEmbedding q ∧ actualParameterSquarePlane '' Set.range q=A := by
    as_aux_lemma =>
      obtain ⟨γ,hγc,hγi,hγA,hγ₀,hγ₁⟩ := hA
      let R := Set.range actualParameterSquarePlane
      let rx : R := ⟨actualParameterSquarePlane x,⟨x,rfl⟩⟩
      let ry : R := ⟨actualParameterSquarePlane y,⟨y,rfl⟩⟩
      have hγR (t : Interval) : γ t.val∈R := hRange (hγA ▸ ⟨t.val,t.property,rfl⟩)
      let r : Path rx ry := {
        toFun := fun t => ⟨γ t.val,hγR t⟩
        continuous_toFun := (continuousOn_iff_continuous_restrict.mp hγc).subtype_mk _
        source' := by apply Subtype.ext;exact hγ₀
        target' := by apply Subtype.ext;exact hγ₁ }
      let E := hActualParameterSquarePlaneEmbedding.toHomeomorph
      have hback (z : R) : actualParameterSquarePlane (E.symm z)=z.val :=
        congrArg Subtype.val (E.apply_symm_apply z)
      have hrx : E.symm rx=x := hActualParameterSquarePlaneInjective (hback rx)
      have hry : E.symm ry=y := hActualParameterSquarePlaneInjective (hback ry)
      let q : Path x y := (r.map E.symm.continuous).cast hrx.symm hry.symm
      have hq : IsEmbedding q := by
        apply (q.continuous.isClosedEmbedding ?_).isEmbedding
        intro t u he
        have hr : r t=r u := E.symm.injective he
        exact Subtype.ext (hγi t.property u.property (congrArg Subtype.val hr))
      have hpoint (t : Interval) : actualParameterSquarePlane (q t)=γ t.val := hback (r t)
      refine ⟨q,hq,?_⟩
      ext z
      constructor
      · rintro ⟨v,⟨t,rfl⟩,rfl⟩
        rw [hpoint]
        exact hγA ▸ ⟨t.val,t.property,rfl⟩
      · intro hz
        obtain ⟨t,ht,he⟩ := (show z∈γ '' Set.Icc (0 : ℝ) 1 from hγA.symm ▸ hz)
        exact ⟨q ⟨t,ht⟩,⟨⟨t,ht⟩,rfl⟩,(hpoint ⟨t,ht⟩).trans he⟩
  have hActualSpecifiedCrossingProducesEmbeddedSquareContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          ∃ W : List ((↑edges) × Fin 3),W≠[] ∧
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
              (actualPlanarVertexPosition (Sum.inl z)) ∧
            ∃ q : Path w.val z.val,IsEmbedding q ∧
              actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W ∧
              (∀ t,actualFiniteConeSweep (q t)∈a.val.image) ∧
              (∀ t,actualFiniteConeSweep (q t)∉(M.cover.branch : Set S)) := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,hArc⟩ :=
        hActualSpecifiedCrossingProducesEmbeddedPlanarContactCarrier
      have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
        intro x hx
        obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
        obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
        exact ⟨actualGlobalContactArcs e.1 u,hpoint⟩
      obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
        obtain ⟨u,hu,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
        have hqu : actualGlobalContactArcs e.1 u=q t := hActualParameterSquarePlaneInjective hpoint
        rw [←hqu]
        exact hActualGlobalContactArcImage e.1 u
      exact ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,q,hq,himage,hcontact,
        fun t => hActualFiniteConeSweepMarks _⟩
  have hActualOldArcContactPathHasOriginalInteriorParameters
      (x y : Interval × Interval) (q : Path x y)
      (hcontact : ∀ t,actualFiniteConeSweep (q t)∈a.val.image)
      (hmarks : ∀ t,actualFiniteConeSweep (q t)∉(M.cover.branch : Set S)) :
      ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
        ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    obtain ⟨κ,hκ,hinside⟩ := actual_original_mark_free_contact_path_interior_parameters
      M a (actualFiniteConeSweep.comp q.toContinuousMap) hcontact hmarks
    exact ⟨κ,hκ,hinside⟩
  have hActualSpecifiedCrossingProducesOriginalParameterContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
            ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,q,hq,himage,hcontact,hmarks⟩ :=
        hActualSpecifiedCrossingProducesEmbeddedSquareContactPath
      obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact hmarks
      exact ⟨w,z,hw,hleft,hzw,hodd,q,hq,κ,hκ,hinside⟩
  have hActualOriginalInteriorMapEmbedding (d : EssentialMarkedArc M)
      (c : C(Interval,Interval)) (hci : ∀ t,0<(c t:ℝ) ∧ (c t:ℝ)<1)
      (hc : Function.Injective c) : IsEmbedding (fun t => d.val.map (c t)) := by
    as_aux_lemma =>
      have hi : Function.Injective (fun t => d.val.map (c t)) := by
        intro t u he
        rcases d.val.injective_except_loop_closure (c t) (c u) he with hh | hh | hh
        · exact hc hh
        · have hv := congrArg Subtype.val hh.1
          exact False.elim ((ne_of_gt (hci t).1) hv)
        · have hv := congrArg Subtype.val hh.1
          exact False.elim ((ne_of_lt (hci t).2) hv)
      exact ((d.val.continuous.comp c.continuous).isClosedEmbedding hi).isEmbedding
  have hActualFinalBottomEmbedding : IsEmbedding (fun t : Interval => actualFiniteConeSweep (0,t)) := by
    have he : (fun t : Interval => actualFiniteConeSweep (0,t))=(fun t => b.val.map (φ t)) :=
      funext hFinalBottom
    rw [he]
    exact hActualOriginalInteriorMapEmbedding b φ hφbounds hφ.injective
  have hActualEveryInitialContactVertexDegreeOne (v : actualContactVertices)
      (hv : v.val.1=0) : actualZeroGraph.degree (Sum.inl v)=1 := by
    rw [hActualGraphDegreeFromOriginalEndpointCount]
    have he : v.val=(0,v.val.2) := Prod.ext hv rfl
    rw [he]
    exact hBottomDegree v.val.2 (he ▸ hActualContactVerticesImage v)
  have hActualOddVertexOnActualOuterSides (v : actualContactVertices)
      (hodd : Odd (actualZeroGraph.degree (Sum.inl v))) :
      v.val.1=0 ∨ v.val.2=0 ∨ v.val.2=1 := by
    have htopoff : v.val.1≠1 := by
      intro he
      have hp : v.val=(1,v.val.2) := Prod.ext he rfl
      exact hFinalTop v.val.2 (hp ▸ hActualContactVerticesImage v)
    by_cases hx : v.val.1=0
    · exact Or.inl hx
    by_cases hy : v.val.2=0
    · exact Or.inr (Or.inl hy)
    by_cases hy1 : v.val.2=1
    · exact Or.inr (Or.inr hy1)
    have hd : actualZeroGraph.degree (Sum.inl v)=2 := by
      rw [hActualGraphDegreeFromOriginalEndpointCount]
      exact hInterior v
        (lt_of_le_of_ne v.val.1.property.1 (fun h => hx (Subtype.ext h.symm)))
        (lt_of_le_of_ne v.val.1.property.2 (fun h => htopoff (Subtype.ext h)))
        (lt_of_le_of_ne v.val.2.property.1 (fun h => hy (Subtype.ext h.symm)))
        (lt_of_le_of_ne v.val.2.property.2 (fun h => hy1 (Subtype.ext h)))
    rw [hd] at hodd
    norm_num at hodd
  have hActualOriginalInitialContactPathSupportOnlyEndpoints
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (v : actualContactVertices) (hv : v.val.1=0)
      (hsupport : Sum.inl v∈P.support) : v=w ∨ v=z := by
    as_aux_lemma =>
      have he := CurveComplex.LocalSurgery.actual_degree_one_path_support_is_endpoint
        actualZeroGraph P hP hsupport (hActualEveryInitialContactVertexDegreeOne v hv)
      exact he.elim (fun h => Or.inl (Sum.inl.inj h)) (fun h => Or.inr (Sum.inl.inj h))
  have hRawLeftCornerBase (k : ↑levels₀) (σ : Interval) :
      actualRawLeftCornerSquare k (σ,0)=a.val.map 0 := by
    change F₀ k (σ,actualRawSourceQuarterParameter 0)=_
    rw [hRawQuarterZero]
    exact hFzero₀ k σ
  have hRawLeftCornerOld (k : ↑levels₀) (t : Interval) :
      actualRawLeftCornerSquare k (1,t)∈a.val.image :=
    hFtop₀ k (actualRawSourceQuarterParameter t)
  have hRawLeftCornerPositiveMarks (k : ↑levels₀) (t : Interval) (ht : 0<(t:ℝ)) :
      actualRawLeftCornerSquare k (1,t)∉(M.cover.branch : Set S) :=
    hFmarks₀ k 1 (actualRawSourceQuarterParameter t) (div_pos ht (by norm_num))
  have hRawRightCornerBase (k : ↑levels₁) (σ : Interval) :
      actualRawRightCornerSquare k (σ,0)=a.val.map 0 := by
    change F₁ k (σ,actualRawSourceQuarterParameter 0)=_
    rw [hRawQuarterZero]
    exact hFzero₁ k σ
  have hRawRightCornerOld (k : ↑levels₁) (t : Interval) :
      actualRawRightCornerSquare k (1,t)∈a.val.image :=
    hFtop₁ k (actualRawSourceQuarterParameter t)
  have hRawRightCornerPositiveMarks (k : ↑levels₁) (t : Interval) (ht : 0<(t:ℝ)) :
      actualRawRightCornerSquare k (1,t)∉(M.cover.branch : Set S) :=
    hFmarks₁ k 1 (actualRawSourceQuarterParameter t) (div_pos ht (by norm_num))
  have hActualRawCornerBoundaryWordWithLiteralBase
      (H : C(Interval × Interval,S)) (hbase : ∀ σ,H (σ,0)=a.val.map 0)
      (hmarks : ∀ z,H z∉((M.cover.branch : Set S)\{a.val.map 0})) :
      ∃ (h00 : H (0,0)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (h01 : H (0,1)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (h11 : H (1,1)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (bottom : Path (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) ⟨H (0,1),h01⟩)
        (right : Path (⟨H (0,1),h01⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) ⟨H (1,1),h11⟩)
        (top : Path (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) ⟨H (1,1),h11⟩),
        (∀ t,(bottom t:S)=H (0,t)) ∧ (∀ t,(right t:S)=H (t,1)) ∧
        (∀ t,(top t:S)=H (1,t)) ∧ (bottom.trans right).Homotopic top := by
    as_aux_lemma =>
      obtain ⟨h00,h01,h10,h11,bottom,right,left,top,hbottom,hright,hleft,htop,hword⟩ :=
        actual_one_corner_square_boundary_homotopy M (a.val.map 0) H hmarks
      have he : (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ)=⟨H (1,0),h10⟩ :=
        Subtype.ext ((hbase 0).trans (hbase 1).symm)
      let actualTop := top.cast he rfl
      let actualLeft := left.cast rfl he
      have hleftRefl : actualLeft=Path.refl (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) := by
        ext t
        exact (hleft t).trans ((hbase t).trans (hbase 0).symm)
      have hWordLiteral : (left.trans top)=actualLeft.trans actualTop := by
        ext t
        rfl
      rw [hWordLiteral,hleftRefl] at hword
      refine ⟨h00,h01,h11,bottom,right,actualTop,hbottom,hright,htop,?_⟩
      exact hword.trans ⟨Path.Homotopy.reflTrans actualTop⟩
  have hActualRawCornerWordPastesWithSameSourceSquare
      (H G : C(Interval × Interval,S)) (hbase : ∀ σ,H (σ,0)=a.val.map 0)
      (hHmarks : ∀ z,H z∉((M.cover.branch : Set S)\{a.val.map 0}))
      (hGmarks : ∀ z,G z∉(M.cover.branch : Set S))
      {x y z : Interval × Interval} (boundary : Path z y) (q : Path x y) (initial : Path z x)
      (hLiteral : ∀ t,H (t,1)=G (boundary t)) :
      ∃ (h00 : H (0,0)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (h01 : H (0,1)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (h11 : H (1,1)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (hx : G x∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (bottom : Path (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) ⟨H (0,1),h01⟩)
        (top : Path (⟨H (0,0),h00⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) ⟨H (1,1),h11⟩)
        (reverse : Path (⟨H (1,1),h11⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) ⟨G x,hx⟩)
        (returnPath : Path (⟨H (0,1),h01⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ) ⟨G x,hx⟩),
        (∀ t,(bottom t:S)=H (0,t)) ∧ (∀ t,(top t:S)=H (1,t)) ∧
        (∀ t,(reverse t:S)=G (q.symm t)) ∧ (∀ t,(returnPath t:S)=G (initial t)) ∧
        (top.trans reverse).Homotopic (bottom.trans returnPath) := by
    as_aux_lemma =>
      obtain ⟨h00,h01,h11,bottom,right,top,hbottom,hright,htop,hword⟩ :=
        hActualRawCornerBoundaryWordWithLiteralBase H hbase hHmarks
      let T := ((M.cover.branch : Set S)\{a.val.map 0})ᶜ
      have hG (v : Interval × Interval) : G v∈T := fun hv => hGmarks v hv.1
      let A : C(Interval × Interval,T) := ⟨fun v => ⟨G v,hG v⟩,G.continuous.subtype_mk _⟩
      have h0 : (⟨H (0,1),h01⟩ : T)=A z :=
        Subtype.ext ((hLiteral 0).trans (congrArg G boundary.source))
      have h1 : (⟨H (1,1),h11⟩ : T)=A y :=
        Subtype.ext ((hLiteral 1).trans (congrArg G boundary.target))
      let actualBoundary := (boundary.map A.continuous).cast h0 h1
      let reverse := (q.symm.map A.continuous).cast h1 rfl
      let returnPath := (initial.map A.continuous).cast h0 rfl
      have hBoundaryLiteral : actualBoundary=right := by
        ext t
        exact (hLiteral t).symm.trans (hright t).symm
      letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
      have hCentral := (SimplyConnectedSpace.paths_homotopic (boundary.trans q.symm) initial).map A
      rw [Path.map_trans] at hCentral
      have hCentralCast := hCentral.pathCast h0 rfl
      change (actualBoundary.trans reverse).Homotopic returnPath at hCentralCast
      rw [hBoundaryLiteral] at hCentralCast
      have hFirst : (top.trans reverse).Homotopic ((bottom.trans right).trans reverse) :=
        (hword.hcomp (Path.Homotopic.refl reverse)).symm
      have hAssoc : ((bottom.trans right).trans reverse).Homotopic (bottom.trans (right.trans reverse)) :=
        ⟨Path.Homotopy.transAssoc bottom right reverse⟩
      refine ⟨h00,h01,h11,hG x,bottom,top,reverse,returnPath,hbottom,htop,
        (fun _ => rfl),(fun _ => rfl),?_⟩
      exact hFirst.trans (hAssoc.trans ((Path.Homotopic.refl bottom).hcomp hCentralCast))
  have hActualSourceSquarePathsHomotopicInSelectedPuncturedCarrier
      (u : S) {x y : Interval × Interval} (q r : Path x y) :
      ∃ (hx : actualFiniteConeSweep x∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : actualFiniteConeSweep y∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨actualFiniteConeSweep x,hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨actualFiniteConeSweep y,hy⟩),
        (∀ t,(α t : S)=actualFiniteConeSweep (q t)) ∧
        (∀ t,(β t : S)=actualFiniteConeSweep (r t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let T := ((M.cover.branch : Set S)\{u})ᶜ
      have havoid (z : Interval × Interval) : actualFiniteConeSweep z∈T := by
        intro hz
        exact hActualFiniteConeSweepMarks z hz.1
      let A : C(Interval × Interval,T) := ⟨fun z => ⟨actualFiniteConeSweep z,havoid z⟩,
        actualFiniteConeSweep.continuous.subtype_mk _⟩
      letI : ContractibleSpace Interval := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
      have hhom : q.Homotopic r := SimplyConnectedSpace.paths_homotopic q r
      exact ⟨havoid x,havoid y,q.map A.continuous,r.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualBottomEndpointsContactPathHomotopicToOriginalBoundary
      (u : S) {x y : Interval × Interval} (q : Path x y)
      (hx₀ : x.1=0) (hy₀ : y.1=0) :
      ∃ (hx : actualFiniteConeSweep x∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : actualFiniteConeSweep y∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨actualFiniteConeSweep x,hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨actualFiniteConeSweep y,hy⟩),
        (∀ t,(α t : S)=actualFiniteConeSweep (q t)) ∧
        (∀ t,(β t : S)=b.val.map (φ (actualIntervalSegment x.2 y.2 t))) ∧
        α.Homotopic β := by
    as_aux_lemma =>
      let r₀ : Path ((0 : Interval),x.2) ((0 : Interval),y.2) := {
        toFun := fun t => (0,actualIntervalSegment x.2 y.2 t)
        continuous_toFun := continuous_const.prodMk (actualIntervalSegment x.2 y.2).continuous
        source' := by apply Prod.ext; rfl; apply Subtype.ext; change (1-(0 : ℝ))*x.2.val+0*y.2.val=x.2.val; ring
        target' := by apply Prod.ext; rfl; apply Subtype.ext; change (1-(1 : ℝ))*x.2.val+1*y.2.val=y.2.val; ring }
      have hx : x=((0 : Interval),x.2) := Prod.ext hx₀ rfl
      have hy : y=((0 : Interval),y.2) := Prod.ext hy₀ rfl
      let r : Path x y := r₀.cast hx hy
      obtain ⟨hxm,hym,α,β,hα,hβ,hhom⟩ :=
        hActualSourceSquarePathsHomotopicInSelectedPuncturedCarrier u q r
      refine ⟨hxm,hym,α,β,hα,?_,hhom⟩
      intro t
      rw [hβ t]
      change actualFiniteConeSweep (0,actualIntervalSegment x.2 y.2 t)=_
      rw [hFinalBottom]
  have hActualMarkedArcInteriorParametersStraightenInSelectedCarrier
      (d : EssentialMarkedArc M) (κ : C(Interval,Interval)) (hκ : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) (u : S) :
      ∃ (hx : d.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : d.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨d.val.map (κ 1),hy⟩),
        (∀ t,(α t : S)=d.val.map (κ t)) ∧
        (∀ t,(β t : S)=d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let J := Set.Ioo (0 : ℝ) 1
      let x : J := ⟨(κ 0).val,hκ 0⟩
      let y : J := ⟨(κ 1).val,hκ 1⟩
      let r : Path x y := {
        toFun := fun t => ⟨(κ t).val,hκ t⟩
        continuous_toFun := (continuous_subtype_val.comp κ.continuous).subtype_mk hκ
        source' := rfl
        target' := rfl }
      have hseg (t : Interval) : (actualIntervalSegment (κ 0) (κ 1) t).val∈J := by
        have hx₀ : 0<(κ 0).val := (hκ 0).1
        have hx₁ : (κ 0).val<1 := (hκ 0).2
        have hy₀ : 0<(κ 1).val := (hκ 1).1
        have hy₁ : (κ 1).val<1 := (hκ 1).2
        change 0<(1-t.val)*(κ 0).val+t.val*(κ 1).val ∧
          (1-t.val)*(κ 0).val+t.val*(κ 1).val<1
        simpa only [smul_eq_mul,Set.mem_Ioo] using (convex_Ioo (0 : ℝ) 1) (show (κ 0).val∈Set.Ioo (0 : ℝ) 1 from ⟨hx₀,hx₁⟩) (show (κ 1).val∈Set.Ioo (0 : ℝ) 1 from ⟨hy₀,hy₁⟩) (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-t.val)+t.val=1)
      let s : Path x y := {
        toFun := fun t => ⟨(actualIntervalSegment (κ 0) (κ 1) t).val,hseg t⟩
        continuous_toFun := (continuous_subtype_val.comp (actualIntervalSegment (κ 0) (κ 1)).continuous).subtype_mk hseg
        source' := by apply Subtype.ext;change (1-(0 : ℝ))*(κ 0).val+0*(κ 1).val=(κ 0).val;ring
        target' := by apply Subtype.ext;change (1-(1 : ℝ))*(κ 0).val+1*(κ 1).val=(κ 1).val;ring }
      let inc : C(J,Interval) := ⟨fun t => ⟨t.val,t.property.1.le,t.property.2.le⟩,
        continuous_subtype_val.subtype_mk (fun t => ⟨t.property.1.le,t.property.2.le⟩)⟩
      have havoid (t : J) : d.val.map (inc t)∉(M.cover.branch : Set S) := by
        intro hm
        rcases d.val.marked_only_at_ends (inc t) hm with he | he
        · have hv := congrArg Subtype.val he
          exact (ne_of_gt t.property.1) hv
        · have hv := congrArg Subtype.val he
          exact (ne_of_lt t.property.2) hv
      let T := ((M.cover.branch : Set S)\{u})ᶜ
      have htarget (t : J) : d.val.map (inc t)∈T := by
        intro hm
        exact havoid t hm.1
      let A : C(J,T) := ⟨fun t => ⟨d.val.map (inc t),htarget t⟩,
        (d.val.continuous.comp inc.continuous).subtype_mk htarget⟩
      letI : ContractibleSpace J := (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨x,x.property⟩
      have hhom : r.Homotopic s := SimplyConnectedSpace.paths_homotopic r s
      exact ⟨htarget x,htarget y,r.map A.continuous,s.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualOriginalBottomBoundaryParametersStraightenInSelectedCarrier
      (x y : Interval) (u : S) :
      let ρ := φ.comp (actualIntervalSegment x y)
      ∃ (hx : b.val.map (ρ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : b.val.map (ρ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨b.val.map (ρ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨b.val.map (ρ 1),hy⟩),
        (∀ t,(α t : S)=b.val.map (φ (actualIntervalSegment x y t))) ∧
        (∀ t,(β t : S)=b.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let ρ := φ.comp (actualIntervalSegment x y)
      have hρ (t : Interval) : ρ t∈Set.Ioo (0 : Interval) 1 :=
        hφbounds (actualIntervalSegment x y t)
      exact hActualMarkedArcInteriorParametersStraightenInSelectedCarrier b ρ hρ u
  have hActualOriginalBottomToBottomSubpathsPuncturedHomotopic
      (u : S) {x y : Interval × Interval} (q : Path x y)
      (hx₀ : x.1=0) (hy₀ : y.1=0)
      (κ : C(Interval,Interval)) (hκ : ∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t))
      (hinside : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) :
      ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨a.val.map (κ 1),hy⟩),
        (∀ t,(α t : S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        (∀ t,(β t : S)=b.val.map (actualIntervalSegment
          (φ x.2) (φ y.2) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      obtain ⟨hx,hy,A₀,A₁,hA₀,hA₁,hA⟩ :=
        hActualMarkedArcInteriorParametersStraightenInSelectedCarrier a κ hinside u
      obtain ⟨hx',hy',Q₀,Q₁,hQ₀,hQ₁,hQ⟩ :=
        hActualBottomEndpointsContactPathHomotopicToOriginalBoundary u q hx₀ hy₀
      have ex : (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=⟨actualFiniteConeSweep x,hx'⟩ :=
        Subtype.ext (by simpa only [q.source] using hκ 0)
      have ey : (⟨a.val.map (κ 1),hy⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=⟨actualFiniteConeSweep y,hy'⟩ :=
        Subtype.ext (by simpa only [q.target] using hκ 1)
      have hAQ : A₀=Q₀.cast ex ey := by
        ext t
        exact (hA₀ t).trans ((hκ t).trans (hQ₀ t).symm)
      obtain ⟨hx'',hy'',B₀,B₁,hB₀,hB₁,hB⟩ :=
        hActualOriginalBottomBoundaryParametersStraightenInSelectedCarrier x.2 y.2 u
      have exb : (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=
          ⟨b.val.map ((φ.comp (actualIntervalSegment x.2 y.2)) 0),hx''⟩ := by
        apply Subtype.ext
        exact (congrArg Subtype.val ex).trans ((congrArg Subtype.val Q₁.source).symm.trans (hQ₁ 0))
      have eyb : (⟨a.val.map (κ 1),hy⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)=
          ⟨b.val.map ((φ.comp (actualIntervalSegment x.2 y.2)) 1),hy''⟩ := by
        apply Subtype.ext
        exact (congrArg Subtype.val ey).trans ((congrArg Subtype.val Q₁.target).symm.trans (hQ₁ 1))
      have hQB : Q₁.cast ex ey=B₀.cast exb eyb := by
        ext t
        exact (hQ₁ t).trans (hB₀ t).symm
      have hfirst : A₁.Homotopic (Q₁.cast ex ey) := by
        exact hA.symm.trans (hAQ ▸ hQ.pathCast ex ey)
      have hlast : A₁.Homotopic (B₁.cast exb eyb) :=
        hfirst.trans (hQB ▸ hB.pathCast exb eyb)
      refine ⟨hx,hy,A₁,B₁.cast exb eyb,hA₁,?_,hlast⟩
      have hs₀ : actualIntervalSegment x.2 y.2 0=x.2 := by
        apply Subtype.ext
        change (1-(0 : ℝ))*x.2.val+0*y.2.val=x.2.val
        ring
      have hs₁ : actualIntervalSegment x.2 y.2 1=y.2 := by
        apply Subtype.ext
        change (1-(1 : ℝ))*x.2.val+1*y.2.val=y.2.val
        ring
      intro t
      change (B₁ t : S)=_
      simpa only [ContinuousMap.comp_apply,hs₀,hs₁] using hB₁ t
  have hActualInitialBoundaryVertex (z : Interval × Interval)
      (hcontact : actualFiniteConeSweep z∈a.val.image) (hz : z.1=0) :
      z∈actualContactVertices := by
    have he : z=(0,z.2) := Prod.ext hz rfl
    have hd := hBottomDegree z.2 (he ▸ hcontact)
    obtain ⟨q,hq⟩ := (Set.ncard_pos (Set.toFinite _)).mp (show 0<
      {q : ↑edges × Fin 2 | arc q.1 (if q.2=0 then 0 else 1)=(0,z.2)}.ncard by rw [hd]; omega)
    rw [he]
    change arc q.1 (if q.2=0 then 0 else 1)=(0,z.2) at hq
    by_cases hbit : q.2=0
    · rw [if_pos hbit] at hq
      exact hq ▸ (hEnds q.1).1
    · rw [if_neg hbit] at hq
      exact hq ▸ (hEnds q.1).2
  have hActualContactVertexOnSameCarrierIsOnGraphSupport
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (W : List ((↑edges) × Fin 3))
      (hvertices : actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (v : actualContactVertices)
      (hcarrier : actualPlanarVertexPosition (Sum.inl v)∈Graph.edgesCover actualPlanarDrawing W) :
      (Sum.inl v : zeroVertex)∈P.support := by
    as_aux_lemma =>
      obtain ⟨e,he,hve⟩ := Graph.mem_edgesCover_iff.mp hcarrier
      have hvvertex : actualPlanarVertexPosition (Sum.inl v)∈actualPlanarGraph.vertexSet :=
        ⟨Sum.inl v,rfl⟩
      have hend := actualPlanarDrawingIsDrawing.vertex_mem_edgeArc
        (hActualPlanarSubedgeLink e) hvvertex hve
      have hinc : actualPlanarGraph.Inc e (actualPlanarVertexPosition (Sum.inl v)) := by
        rcases hend with h | h
        · exact h ▸ (hActualPlanarSubedgeLink e).inc_left
        · exact h ▸ (hActualPlanarSubedgeLink e).inc_right
      have hwalk : actualPlanarVertexPosition (Sum.inl v)∈
          actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W :=
        Graph.mem_walkVertices_of_mem_covered (Graph.mem_coveredVertices he hinc)
      rw [hvertices] at hwalk
      obtain ⟨r,hr,heq⟩ := hwalk
      have hrv : r=Sum.inl v := actualPlanarVertexPositionInjective heq
      exact hrv ▸ hr
  have hActualInitialContactPlanarCarrierOnlyEndpoints
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (W : List ((↑edges) × Fin 3))
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
        (actualPlanarVertexPosition (Sum.inl z)))
      (hvertices : actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (v : actualContactVertices) (hv : v.val.1=0)
      (hcarrier : actualPlanarVertexPosition (Sum.inl v)∈Graph.edgesCover actualPlanarDrawing W) :
      v=w ∨ v=z := by
    exact hActualOriginalInitialContactPathSupportOnlyEndpoints P hP v hv
      (hActualContactVertexOnSameCarrierIsOnGraphSupport P W hvertices v hcarrier)
  have hActualEmbeddedSquareContactPathMeetsInitialBoundaryOnlyAtEnds
      {w z : actualContactVertices} (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z))
      (hP : P.IsPath) (W : List ((↑edges) × Fin 3))
      (hW : actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
        (actualPlanarVertexPosition (Sum.inl z)))
      (hvertices : actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (q : Path w.val z.val) (hq : IsEmbedding q)
      (himage : actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W)
      (t : Interval) (ht : (q t).1=0) : t=0 ∨ t=1 := by
    as_aux_lemma =>
      have hcarrier : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
        himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
      obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hcarrier
      obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
      have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
      have hqrinitial : actualGlobalContactArcs e.1 r=(0,(q t).2) :=
        hqr.trans (Prod.ext ht rfl)
      have hrend : r=0 ∨ r=1 := by
          by_cases hr0 : r=0
          · exact Or.inl hr0
          by_cases hr1 : r=1
          · exact Or.inr hr1
          have hmem : actualGlobalContactArcs e.1 r∈actualContactVertices := by
            have hh := hActualGlobalContactArcImage e.1 r
            rw [hqr] at hh
            -- In the actual full consumer this is literal boundary-vertex retention.
            rw [hqr]
            exact hActualInitialBoundaryVertex (q t) hh ht
          exact False.elim (hActualGlobalContactArcInteriorAvoidVertices e.1 r
            ⟨lt_of_le_of_ne r.property.1 (Ne.symm hr0),lt_of_le_of_ne r.property.2 hr1⟩ hmem)
      have hv : q t∈actualContactVertices := by
        rcases hrend with rfl | rfl
        · exact hqr ▸ hActualContactArcStartInVertices e.1
        · exact hqr ▸ hActualContactArcEndInVertices e.1
      let v : actualContactVertices := ⟨q t,hv⟩
      have hvposition : actualPlanarVertexPosition (Sum.inl v)=actualParameterSquarePlane (q t) := rfl
      have hend : v=w ∨ v=z := hActualInitialContactPlanarCarrierOnlyEndpoints P hP W hW
        hvertices v ht (hvposition.symm ▸ hcarrier)
      rcases hend with h | h
      · have hpoint : q t=w.val := congrArg Subtype.val h
        exact Or.inl (hq.injective (hpoint.trans q.source.symm))
      · have hpoint : q t=z.val := congrArg Subtype.val h
        exact Or.inr (hq.injective (hpoint.trans q.target.symm))
  have hActualSpecifiedCrossingProducesBottomProperOriginalContactPath :
      ∃ w z : actualContactVertices,actualFiniteConeSweep w.val=p ∧ w.val.1=0 ∧ z≠w ∧
        Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ q : Path w.val z.val,IsEmbedding q ∧ (∀ t,(q t).1=0 → t=0 ∨ t=1) ∧
          ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
            ∃ W : List ((↑edges) × Fin 3),W≠[] ∧
              actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
                (actualPlanarVertexPosition (Sum.inl z)) ∧
              actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
                actualPlanarVertexPosition '' {r | r∈P.support} ∧
              actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W ∧
          ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
            ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨w,z,hw,hleft,hzw,hodd,P,hP,W,hne,hW,hvertices,hArc⟩ :=
        hActualSpecifiedCrossingProducesEmbeddedPlanarContactCarrier
      have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
        intro x hx
        obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
        exact ⟨actualGlobalContactArcs e.1 r,hpoint⟩
      obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
        have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
        rw [←hqr]
        exact hActualGlobalContactArcImage e.1 r
      obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact
        (fun t => hActualFiniteConeSweepMarks (q t))
      exact ⟨w,z,hw,hleft,hzw,hodd,q,hq,
        fun t ht => hActualEmbeddedSquareContactPathMeetsInitialBoundaryOnlyAtEnds P hP W hW
          hvertices q hq himage t ht,P,hP,W,hne,hW,hvertices,himage,κ,hκ,hinside⟩
  have actualIntervalSegmentInjectiveOfNe (x y : Interval) (hxy : x≠y) :
      Function.Injective (actualIntervalSegment x y) := by
    as_aux_lemma =>
      intro t s he
      have hv := congrArg Subtype.val he
      change (1-t.val)*x.val+t.val*y.val=(1-s.val)*x.val+s.val*y.val at hv
      have hprod : (y.val-x.val)*(t.val-s.val)=0 := by nlinarith only [hv]
      rcases mul_eq_zero.mp hprod with hbad | hts
      · exact False.elim (hxy (Subtype.ext (sub_eq_zero.mp hbad).symm))
      · exact Subtype.ext (sub_eq_zero.mp hts)
  have hActualOriginalSegmentInterior (x y : Interval)
      (hx : 0<(x:ℝ) ∧ (x:ℝ)<1) (hy : 0<(y:ℝ) ∧ (y:ℝ)<1) (t : Interval) :
      0<(actualIntervalSegment x y t:ℝ) ∧ (actualIntervalSegment x y t:ℝ)<1 := by
    change 0<(1-t.val)*x.val+t.val*y.val ∧ (1-t.val)*x.val+t.val*y.val<1
    simpa only [smul_eq_mul,Set.mem_Ioo] using (convex_Ioo (0 : ℝ) 1) hx hy
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-t.val)+t.val=1)
  have hActualOriginalBottomContactSubpathPairBothEmbedded
      (w z : actualContactVertices) (hw : w.val.1=0) (hz : z.val.1=0) (hzw : z≠w)
      (q : Path w.val z.val) (κ : C(Interval,Interval))
      (hκ : ∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t))
      (hinside : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) :
      IsEmbedding (fun t : Interval => a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
      IsEmbedding (fun t : Interval => b.val.map (actualIntervalSegment (φ w.val.2) (φ z.val.2) t)) := by
    have hwpoint : w.val=(0,w.val.2) := Prod.ext hw rfl
    have hzpoint : z.val=(0,z.val.2) := Prod.ext hz rfl
    have hcoord : w.val.2≠z.val.2 := by
      intro he
      have hepair : ((0 : Interval),z.val.2)=(0,w.val.2) := Prod.ext rfl he.symm
      exact hzw (Subtype.ext (hzpoint.trans (hepair.trans hwpoint.symm)))
    have hends : κ 0≠κ 1 := by
      intro he
      have hpoint : actualFiniteConeSweep w.val=actualFiniteConeSweep z.val := by
        simpa only [q.source,q.target] using (hκ 0).symm.trans ((congrArg a.val.map he).trans (hκ 1))
      rw [hwpoint,hzpoint] at hpoint
      exact hcoord (hActualFinalBottomEmbedding.injective hpoint)
    have hφends : φ w.val.2≠φ z.val.2 := fun h => hcoord (hφ.injective h)
    constructor
    · exact hActualOriginalInteriorMapEmbedding a (actualIntervalSegment (κ 0) (κ 1))
        (hActualOriginalSegmentInterior _ _ (hinside 0) (hinside 1))
        (actualIntervalSegmentInjectiveOfNe _ _ hends)
    · exact hActualOriginalInteriorMapEmbedding b (actualIntervalSegment (φ w.val.2) (φ z.val.2))
        (hActualOriginalSegmentInterior _ _ (hφbounds _) (hφbounds _))
        (actualIntervalSegmentInjectiveOfNe _ _ hφends)
  have hActualOriginalInitialWindowPathLift
      (d : EssentialMarkedArc M) (γ : C(Interval,S))
      (hcontact : ∀ t,γ t∈d.val.image)
      (hmarks : ∀ t : Interval,0<(t:ℝ) → γ t∉(M.cover.branch : Set S))
      (δ : Interval) (hδ : 0<(δ:ℝ))
      (c : C(Interval,Interval)) (he : IsEmbedding (fun t => d.val.map (c t)))
      (hcap : ∀ t : Interval,t≤δ → γ t∈range (fun u => d.val.map (c u))) :
      ∃ κ : C(Interval,Interval),∀ t,d.val.map (κ t)=γ t := by
    as_aux_lemma =>
      let coreMap : C(Interval,S) := ⟨fun t => d.val.map (c t),d.val.continuous.comp c.continuous⟩
      let E := he.toHomeomorph
      let earlySource : C(Interval,range coreMap) :=
        ⟨fun t => ⟨γ (actualIntervalSegment 0 δ t),hcap _
          (actualIntervalSegmentBounds 0 δ hδ t).2⟩,by fun_prop⟩
      let rate : C(Interval,Interval) :=
        ⟨fun t => Set.projIcc 0 1 zero_le_one ((t:ℝ)/(δ:ℝ)),by fun_prop⟩
      let earlyParameter : C(Interval,Interval) :=
        ⟨fun t => c (E.symm (earlySource (rate t))),by fun_prop⟩
      have hEarlyIdentity (t : Interval) (ht : t≤δ) : d.val.map (earlyParameter t)=γ t := by
        have hrate : (rate t:ℝ)=(t:ℝ)/(δ:ℝ) := by
          dsimp [rate]
          rw [Set.projIcc_of_mem zero_le_one
            ⟨div_nonneg t.property.1 hδ.le,(div_le_one hδ).mpr ht⟩]
        have hscaled : actualIntervalSegment 0 δ (rate t)=t := by
          apply Subtype.ext
          change (1-(rate t:ℝ))*0+(rate t:ℝ)*(δ:ℝ)=(t:ℝ)
          rw [hrate]
          field_simp [ne_of_gt hδ]
          ring
        have hh := congrArg Subtype.val (E.apply_symm_apply (earlySource (rate t)))
        change d.val.map (earlyParameter t)=γ (actualIntervalSegment 0 δ (rate t)) at hh
        rw [hscaled] at hh
        exact hh
      let laterDomain : C(Interval,Interval) := ⟨fun t => max δ t,by fun_prop⟩
      have hLaterPositive (t : Interval) : 0<(laterDomain t:ℝ) :=
        lt_of_lt_of_le hδ (le_max_left _ _)
      obtain ⟨laterParameter,hLaterIdentity',hLaterInside⟩ :=
        actual_original_mark_free_contact_path_interior_parameters M d (γ.comp laterDomain)
          (fun t => hcontact (laterDomain t)) (fun t => hmarks (laterDomain t) (hLaterPositive t))
      have hLaterIdentity (t : Interval) (ht : δ≤t) : d.val.map (laterParameter t)=γ t := by
        simpa only [ContinuousMap.comp_apply,laterDomain,ContinuousMap.coe_mk,max_eq_right ht]
          using hLaterIdentity' t
      have hJoin : earlyParameter δ=laterParameter δ := by
        have hh := (hEarlyIdentity δ le_rfl).trans (hLaterIdentity δ le_rfl).symm
        rcases d.val.injective_except_loop_closure _ _ hh with h | h | h
        · exact h
        · have hv := congrArg Subtype.val h.2
          exact False.elim ((ne_of_lt (hLaterInside δ).2) hv)
        · have hv := congrArg Subtype.val h.2
          exact False.elim ((ne_of_gt (hLaterInside δ).1) hv)
      let κ : C(Interval,Interval) :=
        ⟨fun t => if (t:ℝ)≤(δ:ℝ) then earlyParameter t else laterParameter t,
          earlyParameter.continuous.if_le laterParameter.continuous continuous_subtype_val
            continuous_const (by
              intro t ht
              have heq : t=δ := Subtype.ext ht
              subst t
              exact hJoin)⟩
      refine ⟨κ,?_⟩
      intro t
      change d.val.map (if (t:ℝ)≤(δ:ℝ) then earlyParameter t else laterParameter t)=γ t
      split_ifs with ht
      · exact hEarlyIdentity t ht
      · exact hLaterIdentity t (le_of_not_ge ht)
  have hActualOriginalProperWindowEmbedding (d : EssentialMarkedArc M)
      (x y : Interval) (hxy : x<y) (hproper : 0<(x:ℝ) ∨ (y:ℝ)<1) :
      IsEmbedding (fun t => d.val.map (actualIntervalSegment x y t)) := by
    as_aux_lemma =>
      have hi : Function.Injective (fun t => d.val.map (actualIntervalSegment x y t)) := by
        intro t u he
        rcases d.val.injective_except_loop_closure _ _ he with hh | hh | hh
        · exact actualIntervalSegmentInjective x y hxy hh
        · rcases hproper with hx | hy
          · have hbound := (actualIntervalSegmentBounds x y hxy t).1
            have hz := congrArg Subtype.val hh.1
            change (x:ℝ)≤(actualIntervalSegment x y t:ℝ) at hbound
            change (actualIntervalSegment x y t:ℝ)=0 at hz
            linarith
          · have hbound := (actualIntervalSegmentBounds x y hxy u).2
            have hz := congrArg Subtype.val hh.2
            change (actualIntervalSegment x y u:ℝ)≤(y:ℝ) at hbound
            change (actualIntervalSegment x y u:ℝ)=1 at hz
            linarith
        · rcases hproper with hx | hy
          · have hbound := (actualIntervalSegmentBounds x y hxy u).1
            have hz := congrArg Subtype.val hh.2
            change (x:ℝ)≤(actualIntervalSegment x y u:ℝ) at hbound
            change (actualIntervalSegment x y u:ℝ)=0 at hz
            linarith
          · have hbound := (actualIntervalSegmentBounds x y hxy t).2
            have hz := congrArg Subtype.val hh.1
            change (actualIntervalSegment x y t:ℝ)≤(y:ℝ) at hbound
            change (actualIntervalSegment x y t:ℝ)=1 at hz
            linarith
      exact ((d.val.continuous.comp (actualIntervalSegment x y).continuous).isClosedEmbedding hi).isEmbedding
  have hActualOriginalProperWindowParameterSurjective (x y : Interval) (hxy : x<y)
      (t : Interval) (ht : x≤t ∧ t≤y) : ∃ u : Interval,actualIntervalSegment x y u=t := by
    as_aux_lemma =>
      have hd : 0<(y:ℝ)-(x:ℝ) := sub_pos.mpr hxy
      let u : Interval := ⟨((t:ℝ)-(x:ℝ))/((y:ℝ)-(x:ℝ)),
        div_nonneg (sub_nonneg.mpr ht.1) hd.le,
        (div_le_one hd).mpr (sub_le_sub_right (show (t:ℝ)≤(y:ℝ) from ht.2) _)⟩
      refine ⟨u,Subtype.ext ?_⟩
      change (1-((t:ℝ)-(x:ℝ))/((y:ℝ)-(x:ℝ)))*(x:ℝ)+
        (((t:ℝ)-(x:ℝ))/((y:ℝ)-(x:ℝ)))*(y:ℝ)=(t:ℝ)
      field_simp [ne_of_gt hd]
      ring
  have hActualOriginalInitialWindowSide (d : EssentialMarkedArc M)
      (γ : C(Interval,S)) (hcontact : ∀ t,γ t∈d.val.image)
      (hmarks : ∀ t : Interval,0<(t:ℝ) → γ t∉(M.cover.branch : Set S))
      (δ : Interval) (hδ : 0<(δ:ℝ))
      (m : Interval) (hm : 0<(m:ℝ) ∧ (m:ℝ)<1)
      (havoid : ∀ t : Interval,t≤δ → γ t≠d.val.map m) :
      (∀ t : Ioc (0 : Interval) δ,
        openAnchorInterval ((anchorInteriorCoordinates M d).symm
          ⟨γ t.val,⟨hcontact t.val,hmarks t.val t.property.1⟩⟩) > m) ∨
      (∀ t : Ioc (0 : Interval) δ,
        openAnchorInterval ((anchorInteriorCoordinates M d).symm
          ⟨γ t.val,⟨hcontact t.val,hmarks t.val t.property.1⟩⟩) < m) := by
    as_aux_lemma =>
      letI : PreconnectedSpace (Ioc (0 : Interval) δ) :=
        Subtype.preconnectedSpace isPreconnected_Ioc
      let contact : C(Ioc (0 : Interval) δ,arcInterior M d) :=
        ⟨fun t => ⟨γ t.val,⟨hcontact t.val,hmarks t.val t.property.1⟩⟩,by fun_prop⟩
      let κ : C(Ioc (0 : Interval) δ,Interval) :=
        ⟨fun t => openAnchorInterval ((anchorInteriorCoordinates M d).symm (contact t)),
          openAnchorInterval_continuous.comp
            ((anchorInteriorCoordinates M d).symm.continuous.comp contact.continuous)⟩
      have hκ (t : Ioc (0 : Interval) δ) : d.val.map (κ t)=γ t.val := by
        change d.val.map (openAnchorInterval ((anchorInteriorCoordinates M d).symm (contact t)))=γ t.val
        rw [← anchorInteriorCoordinates_apply M d]
        exact congrArg Subtype.val ((anchorInteriorCoordinates M d).apply_symm_apply (contact t))
      have hne (t : Ioc (0 : Interval) δ) : κ t≠m := by
        intro he
        exact havoid t.val t.property.2 ((hκ t).symm.trans (congrArg d.val.map he))
      have hs := (isPreconnected_range κ.continuous).mapsTo_Ioi_or_Iio
        (f := fun t : Interval => t) (b := m) continuous_id.continuousOn
        (by rintro t ⟨u,rfl⟩; exact hne u)
      rcases hs with hs | hs
      · exact Or.inl (fun t => hs ⟨t,rfl⟩)
      · exact Or.inr (fun t => hs ⟨t,rfl⟩)
  have hActualOriginalMarkedBasePathParameters (d : EssentialMarkedArc M)
      (hd : d.val.map 0=d.val.map 1) (γ : C(Interval,S))
      (hbase : γ 0=d.val.map 0) (hcontact : ∀ t,γ t∈d.val.image)
      (hmarks : ∀ t : Interval,0<(t:ℝ) → γ t∉(M.cover.branch : Set S)) :
      ∃ κ : C(Interval,Interval),(∀ t,d.val.map (κ t)=γ t) ∧
        (κ 0=0 ∨ κ 0=1) ∧ ∀ t : Interval,0<(t:ℝ) → 0<(κ t:ℝ) ∧ (κ t:ℝ)<1 := by
    as_aux_lemma =>
      let m : Interval := ⟨1/2,by norm_num⟩
      have hm : 0<(m:ℝ) ∧ (m:ℝ)<1 := by norm_num [m]
      have hmid : γ 0≠d.val.map m := by
        rw [hbase]
        intro he
        rcases d.val.injective_except_loop_closure 0 m he with hh | hh | hh
        · have hv := congrArg Subtype.val hh
          norm_num [m] at hv
        · have hv := congrArg Subtype.val hh.2
          norm_num [m] at hv
        · have hv := congrArg Subtype.val hh.1
          norm_num at hv
      have hopen : IsOpen {t : Interval | γ t≠d.val.map m} :=
        isOpen_compl_singleton.preimage γ.continuous
      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmid)
      let δ : Interval := ⟨min (ε/2) (1/2),
        le_of_lt (lt_min (by positivity) (by norm_num)),
        (min_le_right _ _).trans (by norm_num)⟩
      have hδ : 0<(δ:ℝ) := lt_min (by positivity) (by norm_num)
      have havoid (t : Interval) (ht : t≤δ) : γ t≠d.val.map m := by
        apply hball
        change dist t (0 : Interval)<ε
        rw [Subtype.dist_eq,Real.dist_eq]
        change |(t:ℝ)-(0:ℝ)|<ε
        rw [sub_zero,abs_of_nonneg t.property.1]
        have hb : (δ:ℝ)≤ε/2 := min_le_left _ _
        have htt : (t:ℝ)≤(δ:ℝ) := ht
        linarith
      obtain hside | hside := hActualOriginalInitialWindowSide d γ hcontact hmarks δ hδ m hm havoid
      all_goals
        let contact : C(Ioc (0 : Interval) δ,arcInterior M d) :=
          ⟨fun t => ⟨γ t.val,⟨hcontact t.val,hmarks t.val t.property.1⟩⟩,by fun_prop⟩
        let parameter : C(Ioc (0 : Interval) δ,Interval) :=
          ⟨fun t => openAnchorInterval ((anchorInteriorCoordinates M d).symm (contact t)),
            openAnchorInterval_continuous.comp
              ((anchorInteriorCoordinates M d).symm.continuous.comp contact.continuous)⟩
        have hparam (t : Ioc (0 : Interval) δ) : d.val.map (parameter t)=γ t.val := by
          change d.val.map (openAnchorInterval ((anchorInteriorCoordinates M d).symm (contact t)))=γ t.val
          rw [← anchorInteriorCoordinates_apply M d]
          exact congrArg Subtype.val ((anchorInteriorCoordinates M d).apply_symm_apply (contact t))
      · have hcap (t : Interval) (ht : t≤δ) :
            γ t∈range (fun u => d.val.map (actualIntervalSegment m 1 u)) := by
          by_cases hz : t=0
          · subst t
            refine ⟨1,?_⟩
            have hs : actualIntervalSegment m 1 1=1 := Subtype.ext (by simp [actualIntervalSegment])
            change d.val.map (actualIntervalSegment m 1 1)=γ 0
            rw [hs,← hd,← hbase]
          · let tp : Ioc (0 : Interval) δ := ⟨t,lt_of_le_of_ne t.property.1 (Ne.symm hz),ht⟩
            have hlt : m<parameter tp := hside tp
            obtain ⟨u,hu⟩ := hActualOriginalProperWindowParameterSurjective m 1 hm.2 (parameter tp)
              ⟨hlt.le,(parameter tp).property.2⟩
            exact ⟨u,by change d.val.map (actualIntervalSegment _ _ u)=γ t; rw [hu]; exact hparam tp⟩
        obtain ⟨κ,hκ⟩ := hActualOriginalInitialWindowPathLift d γ hcontact hmarks δ hδ
          (actualIntervalSegment m 1) (hActualOriginalProperWindowEmbedding d m 1 hm.2 (Or.inl hm.1)) hcap
        refine ⟨κ,hκ,?_,?_⟩
        · have hh := (hκ 0).trans hbase
          rcases d.val.injective_except_loop_closure _ _ hh with hh | hh | hh
          · exact Or.inl hh
          · exact False.elim (zero_ne_one hh.2)
          · exact Or.inr hh.1
        · intro t ht
          have hn0 : κ t≠0 := by
            intro hz
            exact hmarks t ht ((hκ t).symm ▸ (hz ▸ d.val.start_marked))
          have hn1 : κ t≠1 := by
            intro hz
            exact hmarks t ht ((hκ t).symm ▸ (hz ▸ d.val.end_marked))
          exact ⟨lt_of_le_of_ne (κ t).property.1 (Ne.symm (fun he => hn0 (Subtype.ext he))),
            lt_of_le_of_ne (κ t).property.2 (fun he => hn1 (Subtype.ext he))⟩
      · have hcap (t : Interval) (ht : t≤δ) :
            γ t∈range (fun u => d.val.map (actualIntervalSegment 0 m u)) := by
          by_cases hz : t=0
          · subst t
            refine ⟨0,?_⟩
            have hs : actualIntervalSegment 0 m 0=0 := Subtype.ext (by simp [actualIntervalSegment])
            change d.val.map (actualIntervalSegment 0 m 0)=γ 0
            rw [hs,← hbase]
          · let tp : Ioc (0 : Interval) δ := ⟨t,lt_of_le_of_ne t.property.1 (Ne.symm hz),ht⟩
            have hlt : parameter tp < m := hside tp
            obtain ⟨u,hu⟩ := hActualOriginalProperWindowParameterSurjective 0 m hm.1 (parameter tp)
              ⟨(parameter tp).property.1,hlt.le⟩
            exact ⟨u,by change d.val.map (actualIntervalSegment _ _ u)=γ t; rw [hu]; exact hparam tp⟩
        obtain ⟨κ,hκ⟩ := hActualOriginalInitialWindowPathLift d γ hcontact hmarks δ hδ
          (actualIntervalSegment 0 m) (hActualOriginalProperWindowEmbedding d 0 m hm.1 (Or.inr hm.2)) hcap
        refine ⟨κ,hκ,?_,?_⟩
        · have hh := (hκ 0).trans hbase
          rcases d.val.injective_except_loop_closure _ _ hh with hh | hh | hh
          · exact Or.inl hh
          · exact False.elim (zero_ne_one hh.2)
          · exact Or.inr hh.1
        · intro t ht
          have hn0 : κ t≠0 := by
            intro hz
            exact hmarks t ht ((hκ t).symm ▸ (hz ▸ d.val.start_marked))
          have hn1 : κ t≠1 := by
            intro hz
            exact hmarks t ht ((hκ t).symm ▸ (hz ▸ d.val.end_marked))
          exact ⟨lt_of_le_of_ne (κ t).property.1 (Ne.symm (fun he => hn0 (Subtype.ext he))),
            lt_of_le_of_ne (κ t).property.2 (fun he => hn1 (Subtype.ext he))⟩
  have hActualOriginalConvexParameterCarrierStraightening
      (d : EssentialMarkedArc M) (κ : C(Interval,Interval)) (u : S)
      (J : Set ℝ) (hJ : Convex ℝ J) (hκ : ∀ t,(κ t:ℝ)∈J)
      (hunit : J⊆Set.Icc (0:ℝ) 1)
      (hcarrier : ∀ (r : ℝ) (hr : r∈J),d.val.map ⟨r,hunit hr⟩∈((M.cover.branch : Set S)\{u})ᶜ) :
      ∃ (hx : d.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : d.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨d.val.map (κ 1),hy⟩),
        (∀ t,(α t:S)=d.val.map (κ t)) ∧
        (∀ t,(β t:S)=d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let x : J := ⟨(κ 0).val,hκ 0⟩
      let y : J := ⟨(κ 1).val,hκ 1⟩
      let r : Path x y := {
        toFun := fun t => ⟨(κ t).val,hκ t⟩
        continuous_toFun := (continuous_subtype_val.comp κ.continuous).subtype_mk hκ
        source' := rfl
        target' := rfl }
      have hseg (t : Interval) : (actualIntervalSegment (κ 0) (κ 1) t).val∈J := by
        change (1-t.val)*(κ 0).val+t.val*(κ 1).val∈J
        simpa only [smul_eq_mul] using hJ (hκ 0) (hκ 1)
          (sub_nonneg.mpr t.property.2) t.property.1 (by ring : (1-t.val)+t.val=1)
      let s : Path x y := {
        toFun := fun t => ⟨(actualIntervalSegment (κ 0) (κ 1) t).val,hseg t⟩
        continuous_toFun := (continuous_subtype_val.comp (actualIntervalSegment (κ 0) (κ 1)).continuous).subtype_mk hseg
        source' := by apply Subtype.ext; change (1-(0:ℝ))*(κ 0).val+0*(κ 1).val=(κ 0).val; ring
        target' := by apply Subtype.ext; change (1-(1:ℝ))*(κ 0).val+1*(κ 1).val=(κ 1).val; ring }
      let inc : C(J,Interval) := ⟨fun t => ⟨t.val,hunit t.property⟩,by fun_prop⟩
      let T := ((M.cover.branch : Set S)\{u})ᶜ
      let A : C(J,T) := ⟨fun t => ⟨d.val.map (inc t),hcarrier t.val t.property⟩,
        (d.val.continuous.comp inc.continuous).subtype_mk (fun t => hcarrier t.val t.property)⟩
      letI : ContractibleSpace J := hJ.contractibleSpace ⟨x,x.property⟩
      have hhom : r.Homotopic s := SimplyConnectedSpace.paths_homotopic r s
      exact ⟨hcarrier x.val x.property,hcarrier y.val y.property,r.map A.continuous,s.map A.continuous,
        (fun _ => rfl),(fun _ => rfl),hhom.map A⟩
  have hActualOriginalMarkedBaseParametersStraighten
      (d : EssentialMarkedArc M) (hd : d.val.map 0=d.val.map 1)
      (κ : C(Interval,Interval)) (hzero : κ 0=0 ∨ κ 0=1)
      (hpositive : ∀ t : Interval,0<(t:ℝ) → 0<(κ t:ℝ) ∧ (κ t:ℝ)<1) :
      ∃ (hx : d.val.map (κ 0)∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
        (hy : d.val.map (κ 1)∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
        (α β : Path (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
          ⟨d.val.map (κ 1),hy⟩),
        (∀ t,(α t:S)=d.val.map (κ t)) ∧
        (∀ t,(β t:S)=d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      rcases hzero with hz | hz
      · have hκJ (t : Interval) : (κ t:ℝ)∈Set.Ico (0:ℝ) 1 := by
          refine ⟨(κ t).property.1,?_⟩
          by_cases ht : t=0
          · rw [ht,hz]; norm_num
          · exact (hpositive t (lt_of_le_of_ne t.property.1 (Ne.symm (fun he => ht (Subtype.ext he))))).2
        have hunit : Set.Ico (0:ℝ) 1⊆Set.Icc (0:ℝ) 1 := fun _ hr => ⟨hr.1,hr.2.le⟩
        have hcarrier (r : ℝ) (hr : r∈Set.Ico (0:ℝ) 1) :
            d.val.map ⟨r,hunit hr⟩∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ := by
          intro hm
          rcases d.val.marked_only_at_ends ⟨r,hunit hr⟩ hm.1 with he | he
          · have hh : d.val.map ⟨r,hunit hr⟩=d.val.map 0 := congrArg d.val.map he
            exact hm.2 (Set.mem_singleton_iff.mpr hh)
          · have hh := congrArg Subtype.val he
            exact (ne_of_lt hr.2) hh
        exact hActualOriginalConvexParameterCarrierStraightening d κ (d.val.map 0)
          (Set.Ico (0:ℝ) 1) (convex_Ico (0:ℝ) 1) hκJ hunit hcarrier
      · have hκJ (t : Interval) : (κ t:ℝ)∈Set.Ioc (0:ℝ) 1 := by
          refine ⟨?_,(κ t).property.2⟩
          by_cases ht : t=0
          · rw [ht,hz]; norm_num
          · exact (hpositive t (lt_of_le_of_ne t.property.1 (Ne.symm (fun he => ht (Subtype.ext he))))).1
        have hunit : Set.Ioc (0:ℝ) 1⊆Set.Icc (0:ℝ) 1 := fun _ hr => ⟨hr.1.le,hr.2⟩
        have hcarrier (r : ℝ) (hr : r∈Set.Ioc (0:ℝ) 1) :
            d.val.map ⟨r,hunit hr⟩∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ := by
          intro hm
          rcases d.val.marked_only_at_ends ⟨r,hunit hr⟩ hm.1 with he | he
          · have hh := congrArg Subtype.val he
            exact (ne_of_gt hr.1) hh
          · have hh : d.val.map ⟨r,hunit hr⟩=d.val.map 0 := (congrArg d.val.map he).trans hd.symm
            exact hm.2 (Set.mem_singleton_iff.mpr hh)
        exact hActualOriginalConvexParameterCarrierStraightening d κ (d.val.map 0)
          (Set.Ioc (0:ℝ) 1) (convex_Ioc (0:ℝ) 1) hκJ hunit hcarrier
  have hActualOriginalOneMarkedBaseAffineSubpathEmbedding
      (d : EssentialMarkedArc M) (x y : Interval) (hx : x=0 ∨ x=1)
      (hy : 0<(y:ℝ) ∧ (y:ℝ)<1) :
      IsEmbedding (fun t => d.val.map (actualIntervalSegment x y t)) := by
    as_aux_lemma =>
      have hne : x≠y := by
        rcases hx with hx | hx
        · intro he
          have hh : (y:ℝ)=0 := congrArg Subtype.val (he.symm.trans hx)
          exact (ne_of_gt hy.1) hh
        · intro he
          have hh : (y:ℝ)=1 := congrArg Subtype.val (he.symm.trans hx)
          exact (ne_of_lt hy.2) hh
      have hbound : (∀ t : Interval,(actualIntervalSegment x y t:ℝ)<1) ∨
          (∀ t : Interval,0<(actualIntervalSegment x y t:ℝ)) := by
        rcases hx with hx | hx
        · left
          intro t
          change (1-t.val)*x.val+t.val*y.val<1
          have hxr : (x:ℝ)=0 := congrArg Subtype.val hx
          rw [hxr]
          nlinarith only [hy.1,hy.2,t.property.1,t.property.2]
        · right
          intro t
          change 0<(1-t.val)*x.val+t.val*y.val
          have hxr : (x:ℝ)=1 := congrArg Subtype.val hx
          rw [hxr]
          nlinarith only [hy.1,hy.2,t.property.1,t.property.2]
      have hi : Function.Injective (fun t => d.val.map (actualIntervalSegment x y t)) := by
        intro t u he
        rcases d.val.injective_except_loop_closure _ _ he with hh | hh | hh
        · exact actualIntervalSegmentInjectiveOfNe x y hne hh
        · rcases hbound with hb | hb
          · have hz : (actualIntervalSegment x y u:ℝ)=1 := congrArg Subtype.val hh.2
            exact False.elim ((ne_of_lt (hb u)) hz)
          · have hz : (actualIntervalSegment x y t:ℝ)=0 := congrArg Subtype.val hh.1
            exact False.elim ((ne_of_gt (hb t)) hz)
        · rcases hbound with hb | hb
          · have hz : (actualIntervalSegment x y t:ℝ)=1 := congrArg Subtype.val hh.1
            exact False.elim ((ne_of_lt (hb t)) hz)
          · have hz : (actualIntervalSegment x y u:ℝ)=0 := congrArg Subtype.val hh.2
            exact False.elim ((ne_of_gt (hb u)) hz)
      exact ((d.val.continuous.comp (actualIntervalSegment x y).continuous).isClosedEmbedding hi).isEmbedding
  have hActualOriginalMarkedBaseContactPathProducesEmbeddedSubpath
      (d : EssentialMarkedArc M) (hd : d.val.map 0=d.val.map 1)
      (γ : C(Interval,S)) (hbase : γ 0=d.val.map 0)
      (hcontact : ∀ t,γ t∈d.val.image)
      (hmarks : ∀ t : Interval,0<(t:ℝ) → γ t∉(M.cover.branch : Set S)) :
      ∃ κ : C(Interval,Interval),(∀ t,d.val.map (κ t)=γ t) ∧
        (κ 0=0 ∨ κ 0=1) ∧
        (∀ t : Interval,0<(t:ℝ) → 0<(κ t:ℝ) ∧ (κ t:ℝ)<1) ∧
        IsEmbedding (fun t => d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
      ∃ (hx : d.val.map (κ 0)∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
        (hy : d.val.map (κ 1)∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
        (α β : Path (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
          ⟨d.val.map (κ 1),hy⟩),
        (∀ t,(α t:S)=γ t) ∧
        (∀ t,(β t:S)=d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧ α.Homotopic β := by
    as_aux_lemma =>
      obtain ⟨κ,hκ,hzero,hpositive⟩ := hActualOriginalMarkedBasePathParameters d hd γ hbase hcontact hmarks
      have he := hActualOriginalOneMarkedBaseAffineSubpathEmbedding d (κ 0) (κ 1) hzero
        (hpositive 1 (by norm_num))
      obtain ⟨hx,hy,α,β,hα,hβ,hhom⟩ := hActualOriginalMarkedBaseParametersStraighten d hd κ hzero hpositive
      exact ⟨κ,hκ,hzero,hpositive,he,hx,hy,α,β,(fun t => (hα t).trans (hκ t)),hβ,hhom⟩
  have hActualOriginalMarkedCornerContactConcatenationParameters
      (d : EssentialMarkedArc M) (hd : d.val.map 0=d.val.map 1)
      (c v : S) (α : Path (d.val.map 0) c) (β : Path c v)
      (hα : ∀ t,α t∈d.val.image) (hβ : ∀ t,β t∈d.val.image)
      (hαmarks : ∀ t : Interval,0<(t:ℝ) → α t∉(M.cover.branch : Set S))
      (hβmarks : ∀ t : Interval,β t∉(M.cover.branch : Set S)) :
      ∃ κ : C(Interval,Interval),(∀ t,d.val.map (κ t)=(α.trans β) t) ∧
        (κ 0=0 ∨ κ 0=1) ∧ ∀ t : Interval,0<(t:ℝ) → 0<(κ t:ℝ) ∧ (κ t:ℝ)<1 := by
    as_aux_lemma =>
      have hcontact (t : Interval) : (α.trans β) t∈d.val.image := by
        rw [Path.trans_apply]
        split_ifs with ht
        · exact hα _
        · exact hβ _
      have hmarks (t : Interval) (ht : 0<(t:ℝ)) : (α.trans β) t∉(M.cover.branch : Set S) := by
        rw [Path.trans_apply]
        split_ifs with htt
        · exact hαmarks _ (by change 0<2*(t:ℝ); positivity)
        · exact hβmarks _
      exact hActualOriginalMarkedBasePathParameters d hd (α.trans β).toContinuousMap
        (α.trans β).source hcontact hmarks
  have hActualTwoOriginalMarkedBaseWordsStraightenKeepingHomotopy
      (d e : EssentialMarkedArc M) (hd : d.val.map 0=d.val.map 1)
      (he : e.val.map 0=e.val.map 1) (hbase : e.val.map 0=d.val.map 0)
      {u v : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ}
      (α β : Path u v) (hword : α.Homotopic β) (hstart : (u:S)=d.val.map 0)
      (hαcontact : ∀ t,(α t:S)∈d.val.image) (hβcontact : ∀ t,(β t:S)∈e.val.image)
      (hαmarks : ∀ t : Interval,0<(t:ℝ) → (α t:S)∉(M.cover.branch : Set S))
      (hβmarks : ∀ t : Interval,0<(t:ℝ) → (β t:S)∉(M.cover.branch : Set S)) :
      ∃ κ ρ : C(Interval,Interval),
        (∀ t,d.val.map (κ t)=(α t:S)) ∧ (∀ t,e.val.map (ρ t)=(β t:S)) ∧
        (κ 0=0 ∨ κ 0=1) ∧ (ρ 0=0 ∨ ρ 0=1) ∧
        (∀ t : Interval,0<(t:ℝ) → 0<(κ t:ℝ) ∧ (κ t:ℝ)<1) ∧
        (∀ t : Interval,0<(t:ℝ) → 0<(ρ t:ℝ) ∧ (ρ t:ℝ)<1) ∧
        IsEmbedding (fun t => d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        IsEmbedding (fun t => e.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)) ∧
        ∃ (hx : d.val.map (κ 0)∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
          (hy : d.val.map (κ 1)∈((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
          (f g : Path (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ)
            ⟨d.val.map (κ 1),hy⟩),
          (∀ t,(f t:S)=d.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
          (∀ t,(g t:S)=e.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)) ∧ f.Homotopic g := by
    as_aux_lemma =>
      let valMap : C(↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ,S) :=
        ⟨Subtype.val,continuous_subtype_val⟩
      let γ := valMap.comp α.toContinuousMap
      let δ := valMap.comp β.toContinuousMap
      have hγbase : γ 0=d.val.map 0 := (congrArg Subtype.val α.source).trans hstart
      have hδbase : δ 0=e.val.map 0 :=
        (congrArg Subtype.val β.source).trans (hstart.trans hbase.symm)
      obtain ⟨κ,hκ,hκbase,hκpositive,hκembedding,hx,hy,A₀,A₁,hA₀,hA₁,hA⟩ :=
        hActualOriginalMarkedBaseContactPathProducesEmbeddedSubpath d hd γ hγbase hαcontact hαmarks
      have hBPackage := hActualOriginalMarkedBaseContactPathProducesEmbeddedSubpath e he δ
        hδbase hβcontact hβmarks
      rw [hbase] at hBPackage
      obtain ⟨ρ,hρ,hρbase,hρpositive,hρembedding,hx',hy',B₀,B₁,hB₀,hB₁,hB⟩ := hBPackage
      have ex : (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ)=u :=
        Subtype.ext ((hκ 0).trans (congrArg Subtype.val α.source))
      have ey : (⟨d.val.map (κ 1),hy⟩ : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ)=v :=
        Subtype.ext ((hκ 1).trans (congrArg Subtype.val α.target))
      have exb : (⟨d.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ)=⟨e.val.map (ρ 0),hx'⟩ :=
        Subtype.ext ((congrArg Subtype.val ex).trans ((congrArg Subtype.val β.source).symm.trans (hρ 0).symm))
      have eyb : (⟨d.val.map (κ 1),hy⟩ : ↑((M.cover.branch : Set S)\{d.val.map 0})ᶜ)=⟨e.val.map (ρ 1),hy'⟩ :=
        Subtype.ext ((congrArg Subtype.val ey).trans ((congrArg Subtype.val β.target).symm.trans (hρ 1).symm))
      have hAα : A₀=α.cast ex ey := by
        ext t
        exact hA₀ t
      have hβB : β.cast ex ey=B₀.cast exb eyb := by
        ext t
        exact (hB₀ t).symm
      have hfirst : A₁.Homotopic (β.cast ex ey) :=
        hA.symm.trans (hAα ▸ hword.pathCast ex ey)
      refine ⟨κ,ρ,hκ,hρ,hκbase,hρbase,hκpositive,hρpositive,hκembedding,hρembedding,hx,hy,A₁,B₁.cast exb eyb,hA₁,hB₁,?_⟩
      exact hfirst.trans (hβB ▸ hB.pathCast exb eyb)
  have hActualFiniteContactPathFirstOuterBoundaryParameter
      (w z : Interval × Interval) (q : Path w z) (hq : IsEmbedding q)
      (V : Finset (Interval × Interval))
      (hcontactBoundary : ∀ t : Interval,
        (q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1 → q t∈V)
      (hend : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
      ∃ t : Interval,0<(t:ℝ) ∧
        ((q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1) ∧
        ∀ r : Interval,0<(r:ℝ) → r<t →
          0<((q r).1:ℝ) ∧ ((q r).1:ℝ)<1 ∧
            0<((q r).2:ℝ) ∧ ((q r).2:ℝ)<1 := by
    as_aux_lemma =>
      let events : Set Interval := {t | t≠0 ∧
        ((q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1)}
      have hpre : (q ⁻¹' (V : Set (Interval × Interval))).Finite :=
        Set.Finite.preimage hq.injective.injOn V.finite_toSet
      have hfinite : events.Finite := hpre.subset (fun t ht => hcontactBoundary t ht.2)
      have hone : (1 : Interval)∈events := by
        refine ⟨by norm_num,?_⟩
        simpa only [q.target] using hend
      obtain ⟨t,ht,hmin⟩ := Set.exists_min_image events (fun t : Interval => t) hfinite ⟨1,hone⟩
      have hpos : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (fun he => ht.1 (Subtype.ext he.symm))
      refine ⟨t,hpos,ht.2,?_⟩
      intro r hr hrt
      have hnot : ¬((q r).1=0 ∨ (q r).1=1 ∨ (q r).2=0 ∨ (q r).2=1) := by
        intro hb
        have hr0 : r≠0 := fun he => (ne_of_gt hr) (congrArg Subtype.val he)
        exact (not_le_of_gt hrt) (hmin r ⟨hr0,hb⟩)
      refine ⟨lt_of_le_of_ne (q r).1.property.1 ?_,lt_of_le_of_ne (q r).1.property.2 ?_,
        lt_of_le_of_ne (q r).2.property.1 ?_,lt_of_le_of_ne (q r).2.property.2 ?_⟩
      · intro he
        exact hnot (Or.inl (Subtype.ext he.symm))
      · intro he
        exact hnot (Or.inr (Or.inl (Subtype.ext he)))
      · intro he
        exact hnot (Or.inr (Or.inr (Or.inl (Subtype.ext he.symm))))
      · intro he
        exact hnot (Or.inr (Or.inr (Or.inr (Subtype.ext he))))
  have hActualFiniteContactPathFirstOuterBoundaryProperPrefix
      (w z : Interval × Interval) (q : Path w z) (hq : IsEmbedding q)
      (V : Finset (Interval × Interval))
      (hcontactBoundary : ∀ t : Interval,
        (q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1 → q t∈V)
      (hend : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
      ∃ t : Interval,0<(t:ℝ) ∧
        ((q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1) ∧
        ∃ r : Path w (q t),IsEmbedding r ∧
          (∀ u,r u=q (actualIntervalSegment 0 t u)) ∧
          ∀ u : Interval,0<(u:ℝ) → (u:ℝ)<1 →
            0<((r u).1:ℝ) ∧ ((r u).1:ℝ)<1 ∧
              0<((r u).2:ℝ) ∧ ((r u).2:ℝ)<1 := by
    as_aux_lemma =>
      obtain ⟨t,ht,hbound,hinterior⟩ :=
        hActualFiniteContactPathFirstOuterBoundaryParameter w z q hq V hcontactBoundary hend
      have hstart : actualIntervalSegment 0 t 0=0 := Subtype.ext (by simp [actualIntervalSegment])
      have hend' : actualIntervalSegment 0 t 1=t := Subtype.ext (by simp [actualIntervalSegment])
      let r : Path w (q t) := {
        toFun := fun u => q (actualIntervalSegment 0 t u)
        continuous_toFun := q.continuous.comp (actualIntervalSegment 0 t).continuous
        source' := by rw [hstart,q.source]
        target' := by rw [hend'] }
      have he : IsEmbedding r := ((q.continuous.comp (actualIntervalSegment 0 t).continuous).isClosedEmbedding
        (hq.injective.comp (actualIntervalSegmentInjective 0 t ht))).isEmbedding
      refine ⟨t,ht,hbound,r,he,(fun _ => rfl),?_⟩
      intro u hu0 hu1
      have hs0 : 0<(actualIntervalSegment 0 t u:ℝ) := by
        change 0<(1-u.val)*0+u.val*t.val
        nlinarith only [hu0,ht]
      have hst : actualIntervalSegment 0 t u<t := by
        change (1-u.val)*0+u.val*t.val<t.val
        nlinarith only [hu1,ht]
      exact hinterior _ hs0 hst
  have hActualEveryBottomContactHasActualGraphPathPartner
      (w : actualContactVertices) (hw : w.val.1=0) :
      ∃ z : actualContactVertices,z≠w ∧ Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath := by
    as_aux_lemma =>
      have hodd : Odd (actualZeroGraph.degree (Sum.inl w)) := by
        rw [hActualEveryInitialContactVertexDegreeOne w hw]
        norm_num
      obtain ⟨v,hvw,hvodd,P,hP⟩ := CurveComplex.LocalSurgery.actual_odd_vertex_has_distinct_path_partner
        actualZeroGraph (Sum.inl w) hodd
      rcases v with z | ⟨e,j⟩
      · refine ⟨z,?_,hvodd,P,hP⟩
        intro he
        exact hvw (congrArg Sum.inl he)
      · fin_cases j
        · change Odd (actualZeroGraph.degree (Sum.inr (e,(0 : Fin 2)))) at hvodd
          rw [(zeroSubdivisionDegrees e).1] at hvodd
          norm_num at hvodd
        · change Odd (actualZeroGraph.degree (Sum.inr (e,(1 : Fin 2)))) at hvodd
          rw [(zeroSubdivisionDegrees e).2] at hvodd
          norm_num at hvodd
  have hActualEveryBottomContactProducesEmbeddedSquarePathWithSameGraphWitness
      (w : actualContactVertices) (hw : w.val.1=0) :
      ∃ z : actualContactVertices,z≠w ∧ Odd (actualZeroGraph.degree (Sum.inl z)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          ∃ W : List ((↑edges) × Fin 3),W≠[] ∧
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
              (actualPlanarVertexPosition (Sum.inl z)) ∧
            actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
              actualPlanarVertexPosition '' {r | r∈P.support} ∧
            ∃ q : Path w.val z.val,IsEmbedding q ∧
              actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W ∧
              ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
                ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨z,hzw,hodd,P,hP⟩ := hActualEveryBottomContactHasActualGraphPathPartner w hw
      obtain ⟨W,hW,hvertices⟩ := CurveComplex.LocalSurgery.actual_simple_graph_path_to_labeled_graph_with_vertices
        actualZeroGraph actualPlanarGraph actualPlanarVertexPosition actualPlanarVertexPositionInjective
        (fun r => ⟨r,rfl⟩) (fun h => hActualContactGraphAdjacencyProducesPlanarLink h) P hP
      have hne : W≠[] := by
        intro hn
        rw [hn] at hW
        have he : (Sum.inl w : zeroVertex)=Sum.inl z := actualPlanarVertexPositionInjective hW.isWalk.eq_of_nil
        exact hzw (Sum.inl.inj he).symm
      have hArc := actualPlanarDrawingIsDrawing.path_isArcBetween hW hne
      have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
        intro x hx
        obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
        exact ⟨actualGlobalContactArcs e.1 r,hpoint⟩
      obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
        have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
        rw [←hqr]
        exact hActualGlobalContactArcImage e.1 r
      obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact
        (fun t => hActualFiniteConeSweepMarks (q t))
      exact ⟨z,hzw,hodd,P,hP,W,hne,hW,hvertices,q,hq,himage,κ,hκ,hinside⟩
  have hActualDegreeTwoInternalPathNeighborsStayOnSupport
      {v w z r : zeroVertex} (P : actualZeroGraph.Walk v w) (hP : P.IsPath)
      (hz : z∈P.support) (hzv : z≠v) (hzw : z≠w)
      (hdegree : actualZeroGraph.degree z=2) (hr : actualZeroGraph.Adj z r) : r∈P.support := by
    as_aux_lemma =>
      obtain ⟨n,hnz,hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
      have hn0 : 0<n := by
        by_contra h
        have he : n=0 := by omega
        rw [he] at hnz
        exact hzv (by simpa using hnz.symm)
      have hnlt : n<P.length := by
        by_contra h
        have he : n=P.length := by omega
        rw [he,SimpleGraph.Walk.getVert_length] at hnz
        exact hzw hnz.symm
      have hprev : actualZeroGraph.Adj z (P.getVert (n-1)) := by
        have h := (P.adj_getVert_succ (i := n-1) (by omega)).symm
        have he : n-1+1=n := by omega
        rwa [he,hnz] at h
      have hnext : actualZeroGraph.Adj z (P.getVert (n+1)) := by
        simpa only [hnz] using P.adj_getVert_succ hnlt
      have hne : P.getVert (n-1)≠P.getVert (n+1) := by
        intro he
        have hh := hP.getVert_injOn (show n-1≤P.length by omega) (show n+1≤P.length by omega) he
        omega
      have hpair : ({P.getVert (n-1),P.getVert (n+1)} : Finset zeroVertex)⊆actualZeroGraph.neighborFinset z := by
        intro u hu
        simp only [Finset.mem_insert,Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact (actualZeroGraph.mem_neighborFinset z _).mpr hprev
        · exact (actualZeroGraph.mem_neighborFinset z _).mpr hnext
      have hcard : ({P.getVert (n-1),P.getVert (n+1)} : Finset zeroVertex).card=2 := by simp [hne]
      have heq : ({P.getVert (n-1),P.getVert (n+1)} : Finset zeroVertex)=actualZeroGraph.neighborFinset z :=
        Finset.eq_of_subset_of_card_le hpair (by
          change actualZeroGraph.degree z≤({P.getVert (n-1),P.getVert (n+1)} : Finset zeroVertex).card
          rw [hdegree,hcard])
      have hrmem : r∈actualZeroGraph.neighborFinset z := (actualZeroGraph.mem_neighborFinset z r).mpr hr
      rw [←heq] at hrmem
      simp only [Finset.mem_insert,Finset.mem_singleton] at hrmem
      rcases hrmem with rfl | rfl
      · exact P.getVert_mem_support _
      · exact P.getVert_mem_support _
  have hActualPathDegreeTwoPreventsInteriorEntry
      {v w x y : zeroVertex} (P : actualZeroGraph.Walk v w) (hP : P.IsPath)
      (hdegree : ∀ z,z∈P.support → z≠v → z≠w → actualZeroGraph.degree z=2)
      (Q : actualZeroGraph.Walk x y) (hQ : Q.IsPath) (hx : x∉P.support)
      (havoid : ∀ z,z∈Q.support → z≠y → z≠v ∧ z≠w) :
      ∀ z,z∈Q.support → z≠y → z∉P.support := by
    as_aux_lemma =>
      have hindices : ∀ n : ℕ,n<Q.length → Q.getVert n∉P.support := by
        intro n
        induction n with
        | zero =>
          intro hn
          simpa using hx
        | succ n ih =>
          intro hn
          have hnprev : n<Q.length := by omega
          have hprev := ih hnprev
          have hny : Q.getVert (n+1)≠y := by
            intro he
            have hi := hQ.getVert_injOn (show n+1≤Q.length by omega) (le_refl Q.length)
              (he.trans Q.getVert_length.symm)
            omega
          have hends := havoid _ (Q.getVert_mem_support (n+1)) hny
          intro hz
          have hadj := (Q.adj_getVert_succ hnprev).symm
          exact hprev (hActualDegreeTwoInternalPathNeighborsStayOnSupport P hP hz hends.1 hends.2
            (hdegree _ hz hends.1 hends.2) hadj)
      intro z hz hzy
      obtain ⟨n,hnz,hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
      have hnlt : n<Q.length := by
        by_contra h
        have he : n=Q.length := by omega
        rw [he,SimpleGraph.Walk.getVert_length] at hnz
        exact hzy hnz.symm
      exact hnz ▸ hindices n hnlt
  have hActualSimpleWalkFirstPositiveBoundaryPrefix
      {V : Type} (G : SimpleGraph V) {v w : V} (P : G.Walk v w)
      (hP : P.IsPath) (hne : v≠w) (B : V→Prop) (hw : B w) :
      ∃ z : V,B z ∧ z≠v ∧ ∃ Q : G.Walk v z,Q.IsPath ∧
        (∀ r,r∈Q.support → r≠v → r≠z → ¬B r) := by
    as_aux_lemma =>
      have hlen : 0<P.length := Nat.pos_of_ne_zero (fun h => hne (SimpleGraph.Walk.eq_of_length_eq_zero h))
      have hex : ∃ n : ℕ,0<n ∧ n≤P.length ∧ B (P.getVert n) :=
        ⟨P.length,hlen,le_refl _,by simpa using hw⟩
      let n := Nat.find hex
      have hn := Nat.find_spec hex
      change 0<n ∧ n≤P.length ∧ B (P.getVert n) at hn
      have hzv : P.getVert n≠v := by
        intro h
        have he := hP.getVert_injOn hn.2.1 (show 0≤P.length by omega) (h.trans P.getVert_zero.symm)
        omega
      refine ⟨P.getVert n,hn.2.2,hzv,P.take n,hP.take n,?_⟩
      intro r hr hrv hrz hBr
      obtain ⟨m,hmr,hm⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hr
      have hmn : m≤n := by
        simpa only [SimpleGraph.Walk.take_length,Nat.min_eq_left hn.2.1] using hm
      have hmr' : P.getVert m=r := by
        simpa only [SimpleGraph.Walk.take_getVert,Nat.min_eq_right hmn] using hmr
      have hmpos : 0 < m := by
        by_contra h
        have hm0 : m=0 := by omega
        rw [hm0,SimpleGraph.Walk.getVert_zero] at hmr'
        exact hrv hmr'.symm
      have hmlt : m < n := lt_of_le_of_ne hmn (fun he => hrz (hmr'.symm.trans (congrArg P.getVert he)))
      have hnm := Nat.find_min' hex ⟨hmpos,hmn.trans hn.2.1,hmr'.symm ▸ hBr⟩
      omega
  let actualContactGraphOuterBoundary : zeroVertex→Prop := fun r =>
    match r with
    | Sum.inl v => v.val.1=0 ∨ v.val.1=1 ∨ v.val.2=0 ∨ v.val.2=1
    | Sum.inr _ => False
  have hActualBoundaryProperGraphPathLiftsToProperOriginalContactPath
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      {w z : actualContactVertices} (hzw : z≠w)
      (Q : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z)) (hQ : Q.IsPath)
      (hQBoundary : ∀ r,r∈Q.support → r≠Sum.inl w → r≠Sum.inl z → ¬actualContactGraphOuterBoundary r) :
          ∃ W : List ((↑edges) × Fin 3),
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
              (actualPlanarVertexPosition (Sum.inl z)) ∧
            actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
              actualPlanarVertexPosition '' {r | r∈Q.support} ∧
            ∃ q : Path w.val z.val,IsEmbedding q ∧
              actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W ∧
              (∀ t : Interval,0<(t:ℝ) → (t:ℝ)<1 →
                0<((q t).1:ℝ) ∧ ((q t).1:ℝ)<1 ∧ 0<((q t).2:ℝ) ∧ ((q t).2:ℝ)<1) ∧
              ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
                ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨W,hW,hvertices⟩ := CurveComplex.LocalSurgery.actual_simple_graph_path_to_labeled_graph_with_vertices
        actualZeroGraph actualPlanarGraph actualPlanarVertexPosition actualPlanarVertexPositionInjective
        (fun r => ⟨r,rfl⟩) (fun h => hActualContactGraphAdjacencyProducesPlanarLink h) Q hQ
      have hWne : W≠[] := by
        intro he
        rw [he] at hW
        have he' : (Sum.inl w : zeroVertex)=Sum.inl z :=
          actualPlanarVertexPositionInjective hW.isWalk.eq_of_nil
        exact hzw (Sum.inl.inj he').symm
      have hArc := actualPlanarDrawingIsDrawing.path_isArcBetween hW hWne
      have hRange : Graph.edgesCover actualPlanarDrawing W⊆Set.range actualParameterSquarePlane := by
        intro x hx
        obtain ⟨e,he,hxe⟩ := Graph.mem_edgesCover_iff.mp hx
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e x hxe
        exact ⟨actualGlobalContactArcs e.1 r,hpoint⟩
      obtain ⟨q,hq,himage⟩ := hActualPlanarArcLiftsToEmbeddedParameterSquarePath _ w.val z.val hArc hRange
      have hcontact (t : Interval) : actualFiniteConeSweep (q t)∈a.val.image := by
        have hqpoint : actualParameterSquarePlane (q t)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        obtain ⟨e,he,hqe⟩ := Graph.mem_edgesCover_iff.mp hqpoint
        obtain ⟨r,hr,hpoint⟩ := actualPlanarEdgeArcParameter e _ hqe
        have hqr : actualGlobalContactArcs e.1 r=q t := hActualParameterSquarePlaneInjective hpoint
        rw [←hqr]
        exact hActualGlobalContactArcImage e.1 r
      have hBoundaryOnlyEnds (t : Interval)
          (ht : (q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1) : t=0 ∨ t=1 := by
        have hv : q t∈actualContactVertices := hBoundary _ (hcontact t) ht
        let v : actualContactVertices := ⟨q t,hv⟩
        have hcarrier : actualPlanarVertexPosition (Sum.inl v)∈Graph.edgesCover actualPlanarDrawing W :=
          himage ▸ ⟨q t,⟨t,rfl⟩,rfl⟩
        have hsupport := hActualContactVertexOnSameCarrierIsOnGraphSupport Q W hvertices v hcarrier
        have he : v=w ∨ v=z := by
          by_contra h
          have hvw : (Sum.inl v : zeroVertex)≠Sum.inl w := fun he => h (Or.inl (Sum.inl.inj he))
          have hvz : (Sum.inl v : zeroVertex)≠Sum.inl z := fun he => h (Or.inr (Sum.inl.inj he))
          exact hQBoundary _ hsupport hvw hvz ht
        rcases he with he | he
        · exact Or.inl (hq.injective ((congrArg Subtype.val he).trans q.source.symm))
        · exact Or.inr (hq.injective ((congrArg Subtype.val he).trans q.target.symm))
      have hproper (t : Interval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) :
          0<((q t).1:ℝ) ∧ ((q t).1:ℝ)<1 ∧ 0<((q t).2:ℝ) ∧ ((q t).2:ℝ)<1 := by
        have hnot : ¬((q t).1=0 ∨ (q t).1=1 ∨ (q t).2=0 ∨ (q t).2=1) := by
          intro h
          rcases hBoundaryOnlyEnds t h with he | he
          · exact (ne_of_gt ht0) (congrArg Subtype.val he)
          · exact (ne_of_lt ht1) (congrArg Subtype.val he)
        refine ⟨lt_of_le_of_ne (q t).1.property.1 ?_,lt_of_le_of_ne (q t).1.property.2 ?_,
          lt_of_le_of_ne (q t).2.property.1 ?_,lt_of_le_of_ne (q t).2.property.2 ?_⟩
        · exact fun he => hnot (Or.inl (Subtype.ext he.symm))
        · exact fun he => hnot (Or.inr (Or.inl (Subtype.ext he)))
        · exact fun he => hnot (Or.inr (Or.inr (Or.inl (Subtype.ext he.symm))))
        · exact fun he => hnot (Or.inr (Or.inr (Or.inr (Subtype.ext he))))
      obtain ⟨κ,hκ,hinside⟩ := hActualOldArcContactPathHasOriginalInteriorParameters _ _ q hcontact
        (fun t => hActualFiniteConeSweepMarks (q t))
      exact ⟨W,hW,hvertices,q,hq,himage,hproper,κ,hκ,hinside⟩
  have hActualEveryBottomContactHasGraphFirstBoundaryProperOriginalContactPath
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (w : actualContactVertices) (hw : w.val.1=0) :
      ∃ z : actualContactVertices,z≠w ∧ (z.val.1=0 ∨ z.val.2=0 ∨ z.val.2=1) ∧
        ∃ Q : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),Q.IsPath ∧
          (∀ r,r∈Q.support → r≠Sum.inl w → r≠Sum.inl z → actualZeroGraph.degree r=2) ∧
          (∀ r,r∈Q.support → r≠Sum.inl w → r≠Sum.inl z → ¬actualContactGraphOuterBoundary r) ∧
          ∃ W : List ((↑edges) × Fin 3),
            actualPlanarGraph.IsPath (actualPlanarVertexPosition (Sum.inl w)) W
              (actualPlanarVertexPosition (Sum.inl z)) ∧
            actualPlanarGraph.walkVertices (actualPlanarVertexPosition (Sum.inl w)) W=
              actualPlanarVertexPosition '' {r | r∈Q.support} ∧
            ∃ q : Path w.val z.val,IsEmbedding q ∧
              actualParameterSquarePlane '' Set.range q=Graph.edgesCover actualPlanarDrawing W ∧
              (∀ t : Interval,0<(t:ℝ) → (t:ℝ)<1 →
                0<((q t).1:ℝ) ∧ ((q t).1:ℝ)<1 ∧ 0<((q t).2:ℝ) ∧ ((q t).2:ℝ)<1) ∧
              ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
                ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    as_aux_lemma =>
      obtain ⟨z,hzw,hodd,P,hP⟩ := hActualEveryBottomContactHasActualGraphPathPartner w hw
      have hPB : actualContactGraphOuterBoundary (Sum.inl z) := by
        rcases hActualOddVertexOnActualOuterSides z hodd with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      have hne : (Sum.inl w : zeroVertex)≠Sum.inl z := fun he => hzw (Sum.inl.inj he).symm
      obtain ⟨r,hB,hrw,Q,hQ,hQBoundary⟩ := hActualSimpleWalkFirstPositiveBoundaryPrefix
        actualZeroGraph P hP hne actualContactGraphOuterBoundary hPB
      rcases r with z | r
      swap
      · exact False.elim hB
      have hzw : z≠w := fun h => hrw (congrArg Sum.inl h)
      have htopoff : z.val.1≠1 := by
        intro ht
        have he : z.val=(1,z.val.2) := Prod.ext ht rfl
        exact hFinalTop z.val.2 (he ▸ hActualContactVerticesImage z)
      have hside : z.val.1=0 ∨ z.val.2=0 ∨ z.val.2=1 := by
        change z.val.1=0 ∨ z.val.1=1 ∨ z.val.2=0 ∨ z.val.2=1 at hB
        rcases hB with h | h | h | h
        · exact Or.inl h
        · exact False.elim (htopoff h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hQdegree (r : zeroVertex) (hr : r∈Q.support) (hrw : r≠Sum.inl w) (hrz : r≠Sum.inl z) :
          actualZeroGraph.degree r=2 := by
        rcases r with v | ⟨e,j⟩
        · have hnot := hQBoundary (Sum.inl v) hr hrw hrz
          change ¬(v.val.1=0 ∨ v.val.1=1 ∨ v.val.2=0 ∨ v.val.2=1) at hnot
          rw [hActualGraphDegreeFromOriginalEndpointCount]
          apply hInterior v
          · exact lt_of_le_of_ne v.val.1.property.1 (fun he => hnot (Or.inl (Subtype.ext he.symm)))
          · exact lt_of_le_of_ne v.val.1.property.2 (fun he => hnot (Or.inr (Or.inl (Subtype.ext he))))
          · exact lt_of_le_of_ne v.val.2.property.1 (fun he => hnot (Or.inr (Or.inr (Or.inl (Subtype.ext he.symm)))))
          · exact lt_of_le_of_ne v.val.2.property.2 (fun he => hnot (Or.inr (Or.inr (Or.inr (Subtype.ext he)))))
        · fin_cases j
          · exact (zeroSubdivisionDegrees e).1
          · exact (zeroSubdivisionDegrees e).2
      obtain ⟨W,hW,hvertices,q,hq,himage,hproper,κ,hκ,hinside⟩ :=
        hActualBoundaryProperGraphPathLiftsToProperOriginalContactPath hBoundary hzw Q hQ hQBoundary
      exact ⟨z,hzw,hside,Q,hQ,hQdegree,hQBoundary,W,hW,hvertices,q,hq,himage,hproper,κ,hκ,hinside⟩

  have hActualBoundaryProperDegreeTwoPathsWithDisjointEndsHaveDisjointSupport
      {v w x y : zeroVertex} (P : actualZeroGraph.Walk v w) (hP : P.IsPath)
      (Q : actualZeroGraph.Walk x y) (hQ : Q.IsPath)
      (B : zeroVertex→Prop) (hBv : B v) (hBw : B w) (hBx : B x) (hBy : B y)
      (hPB : ∀ r,r∈P.support → r≠v → r≠w → ¬B r)
      (hQB : ∀ r,r∈Q.support → r≠x → r≠y → ¬B r)
      (hdegree : ∀ r,r∈P.support → r≠v → r≠w → actualZeroGraph.degree r=2)
      (hxv : x≠v) (hxw : x≠w) (hyv : y≠v) (hyw : y≠w) :
      ∀ r,r∈Q.support → r∉P.support := by
    as_aux_lemma =>
      have hx : x∉P.support := fun h => hPB x h hxv hxw hBx
      have hy : y∉P.support := fun h => hPB y h hyv hyw hBy
      have hQAvoid (r : zeroVertex) (hr : r∈Q.support) : r≠v ∧ r≠w := by
        constructor
        · intro he
          have hrx : r≠x := fun h => hxv (h.symm.trans he)
          have hry : r≠y := fun h => hyv (h.symm.trans he)
          exact hQB r hr hrx hry (he ▸ hBv)
        · intro he
          have hrx : r≠x := fun h => hxw (h.symm.trans he)
          have hry : r≠y := fun h => hyw (h.symm.trans he)
          exact hQB r hr hrx hry (he ▸ hBw)
      have hInterior := hActualPathDegreeTwoPreventsInteriorEntry P hP hdegree Q hQ hx
        (fun r hr _ => hQAvoid r hr)
      intro r hr
      by_cases he : r=y
      · exact he ▸ hy
      · exact hInterior r hr he
  have hActualDisjointContactGraphSupportsGiveDisjointPlanarCarriers
      {v w x y : zeroVertex} (P : actualZeroGraph.Walk v w) (Q : actualZeroGraph.Walk x y)
      (WP WQ : List ((↑edges) × Fin 3))
      (hWP : actualPlanarGraph.IsPath (actualPlanarVertexPosition v) WP (actualPlanarVertexPosition w))
      (hWQ : actualPlanarGraph.IsPath (actualPlanarVertexPosition x) WQ (actualPlanarVertexPosition y))
      (hPV : actualPlanarGraph.walkVertices (actualPlanarVertexPosition v) WP=
        actualPlanarVertexPosition '' {r | r∈P.support})
      (hQV : actualPlanarGraph.walkVertices (actualPlanarVertexPosition x) WQ=
        actualPlanarVertexPosition '' {r | r∈Q.support})
      (hdisjoint : ∀ r,r∈Q.support → r∉P.support) :
      Disjoint (Graph.edgesCover actualPlanarDrawing WP) (Graph.edgesCover actualPlanarDrawing WQ) := by
    as_aux_lemma =>
      have hVertexDisjoint : Disjoint (actualPlanarGraph.walkVertices (actualPlanarVertexPosition v) WP)
          (actualPlanarGraph.walkVertices (actualPlanarVertexPosition x) WQ) := by
        apply Set.disjoint_left.mpr
        intro z hzP hzQ
        rw [hPV] at hzP
        rw [hQV] at hzQ
        obtain ⟨p,hp,hpz⟩ := hzP
        obtain ⟨q,hq,hqz⟩ := hzQ
        have he : p=q := actualPlanarVertexPositionInjective (hpz.trans hqz.symm)
        exact hdisjoint q hq (he ▸ hp)
      have hEdgeDisjoint (e : (↑edges) × Fin 3) (he : e∈WP) : e∉WQ := by
        intro hf
        have hvP := Graph.mem_walkVertices_of_mem_covered (u := actualPlanarVertexPosition v)
          (Graph.mem_coveredVertices he (hActualPlanarSubedgeLink e).inc_left)
        have hvQ := Graph.mem_walkVertices_of_mem_covered (u := actualPlanarVertexPosition x)
          (Graph.mem_coveredVertices hf (hActualPlanarSubedgeLink e).inc_left)
        exact Set.disjoint_left.mp hVertexDisjoint hvP hvQ
      apply Set.disjoint_left.mpr
      intro z hzP hzQ
      obtain ⟨e,he,hze⟩ := Graph.mem_edgesCover_iff.mp hzP
      obtain ⟨f,hf,hzf⟩ := Graph.mem_edgesCover_iff.mp hzQ
      have hef : e≠f := fun h => hEdgeDisjoint e he (h.symm ▸ hf)
      obtain ⟨hv,hincE,hincF⟩ := actualPlanarDrawingIsDrawing.edge_inter
        (hWP.edge_mem he) (hWQ.edge_mem hf) hef hze hzf
      exact Set.disjoint_left.mp hVertexDisjoint
        (Graph.mem_walkVertices_of_mem_covered (Graph.mem_coveredVertices he hincE))
        (Graph.mem_walkVertices_of_mem_covered (Graph.mem_coveredVertices hf hincF))
  have hActualDegreeOnePathEndpointNeighborsStayOnSupport
      {v w z r : zeroVertex} (P : actualZeroGraph.Walk v w) (hne : v≠w)
      (hz : z=v ∨ z=w) (hdegree : actualZeroGraph.degree z=1)
      (hadj : actualZeroGraph.Adj z r) : r∈P.support := by
    as_aux_lemma =>
      have hlen : 0<P.length := Nat.pos_of_ne_zero (fun h => hne (SimpleGraph.Walk.eq_of_length_eq_zero h))
      obtain ⟨neighbor,hneighbor,hunique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegree
      rcases hz with rfl | rfl
      · have hfirst : actualZeroGraph.Adj z (P.getVert 1) := by
          simpa using P.adj_getVert_succ hlen
        have he : r=P.getVert 1 := (hunique r hadj).trans (hunique _ hfirst).symm
        exact he.symm ▸ P.getVert_mem_support 1
      · have hlast : actualZeroGraph.Adj z (P.getVert (P.length-1)) := by
          have hh := (P.adj_getVert_succ (i:=P.length-1) (by omega)).symm
          have he : P.length-1+1=P.length := by omega
          simpa only [he,P.getVert_length] using hh
        have he : r=P.getVert (P.length-1) := (hunique r hadj).trans (hunique _ hlast).symm
        exact he.symm ▸ P.getVert_mem_support (P.length-1)
  have hActualDegreeOneEndedDegreeTwoInternalPathIsAnEntireGraphComponent
      {v w x y : zeroVertex} (P : actualZeroGraph.Walk v w) (hP : P.IsPath) (hne : v≠w)
      (hv : actualZeroGraph.degree v=1) (hw : actualZeroGraph.degree w=1)
      (hdegree : ∀ z,z∈P.support → z≠v → z≠w → actualZeroGraph.degree z=2)
      (Q : actualZeroGraph.Walk x y) (hx : x∉P.support) :
      ∀ z,z∈Q.support → z∉P.support := by
    as_aux_lemma =>
      have hclosed (z r : zeroVertex) (hz : z∈P.support) (hr : actualZeroGraph.Adj z r) : r∈P.support := by
        by_cases hzv : z=v
        · exact hActualDegreeOnePathEndpointNeighborsStayOnSupport P hne (Or.inl hzv) (hzv.symm ▸ hv) hr
        by_cases hzw : z=w
        · exact hActualDegreeOnePathEndpointNeighborsStayOnSupport P hne (Or.inr hzw) (hzw.symm ▸ hw) hr
        exact hActualDegreeTwoInternalPathNeighborsStayOnSupport P hP hz hzv hzw (hdegree z hz hzv hzw) hr
      have hindices : ∀ n : ℕ,n≤Q.length → Q.getVert n∉P.support := by
        intro n
        induction n with
        | zero =>
          intro hn
          simpa using hx
        | succ n ih =>
          intro hn
          have hnprev : n<Q.length := by omega
          have hprev := ih (show n≤Q.length by omega)
          intro hz
          exact hprev (hclosed _ _ hz (Q.adj_getVert_succ hnprev).symm)
      intro z hz
      obtain ⟨n,hnz,hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
      exact hnz ▸ hindices n hn
  have hActualDegreeOneStartProperDegreeTwoPathsHaveSameFirstBoundaryEndpoint
      {v w y : zeroVertex} (P : actualZeroGraph.Walk v w) (hP : P.IsPath) (hvw : v≠w)
      (Q : actualZeroGraph.Walk v y) (hvy : v≠y) (B : zeroVertex→Prop)
      (hv : actualZeroGraph.degree v=1) (hBw : B w) (hBy : B y)
      (hPB : ∀ r,r∈P.support → r≠v → r≠w → ¬B r)
      (hQB : ∀ r,r∈Q.support → r≠v → r≠y → ¬B r)
      (hdegree : ∀ r,r∈P.support → r≠v → r≠w → actualZeroGraph.degree r=2) : w=y := by
    as_aux_lemma =>
      by_contra hwy
      have hQavoid (r : zeroVertex) (hr : r∈Q.support) : r≠w := by
        intro he
        have hrv : r≠v := fun hh => hvw (hh.symm.trans he)
        have hry : r≠y := fun hh => hwy (he.symm.trans hh)
        exact hQB r hr hrv hry (he ▸ hBw)
      have hStep (z r : zeroVertex) (hz : z∈P.support) (hzw : z≠w)
          (hr : actualZeroGraph.Adj z r) : r∈P.support := by
        by_cases hzv : z=v
        · exact hActualDegreeOnePathEndpointNeighborsStayOnSupport P hvw (Or.inl hzv) (hzv.symm ▸ hv) hr
        · exact hActualDegreeTwoInternalPathNeighborsStayOnSupport P hP hz hzv hzw (hdegree z hz hzv hzw) hr
      have hindices : ∀ n : ℕ,n≤Q.length → Q.getVert n∈P.support := by
        intro n
        induction n with
        | zero =>
          intro hn
          simpa using P.getVert_mem_support 0
        | succ n ih =>
          intro hn
          have hnprev : n<Q.length := by omega
          exact hStep _ _ (ih (show n≤Q.length by omega))
            (hQavoid _ (Q.getVert_mem_support n)) (Q.adj_getVert_succ hnprev)
      have hy : y∈P.support := by
        simpa using hindices Q.length (le_refl _)
      exact hPB y hy hvy.symm (Ne.symm hwy) hBy

  let actualSourceSquareModel : C(Interval × Interval,Plane) :=
    ⟨fun z => Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1),by fun_prop⟩
  have hActualSourceSquareModelInjective : Function.Injective actualSourceSquareModel := by
    intro z w he
    have hx := congrArg (fun p : Plane => p 0) he
    have hy := congrArg (fun p : Plane => p 1) he
    change 2*(z.1:ℝ)-1=2*(w.1:ℝ)-1 at hx
    change 2*(z.2:ℝ)-1=2*(w.2:ℝ)-1 at hy
    apply Prod.ext <;> apply Subtype.ext <;> linarith
  have hActualSourceSquareModelEmbedding : IsEmbedding actualSourceSquareModel :=
    (actualSourceSquareModel.continuous.isClosedEmbedding hActualSourceSquareModelInjective).isEmbedding
  have hActualSourceSquareModelBoundary (z : Interval × Interval) :
      actualSourceSquareModel z∈modelCurve ↔ z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 := by
    have hx : |2*(z.1:ℝ)-1|≤1 := abs_le.mpr ⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩
    have hy : |2*(z.2:ℝ)-1|≤1 := abs_le.mpr ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩
    change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1|=1 ↔ _
    constructor
    · intro h
      have he : |2*(z.1:ℝ)-1|=1 ∨ |2*(z.2:ℝ)-1|=1 := by
        by_cases he : |2*(z.1:ℝ)-1|=1
        · exact Or.inl he
        · have hlt := lt_of_le_of_ne hx he
          have hy' : |2*(z.2:ℝ)-1|=1 := by
            by_contra hne
            have hh := max_lt hlt (lt_of_le_of_ne hy hne)
            rw [h] at hh
            exact (lt_irrefl (1:ℝ)) hh
          exact Or.inr hy'
      rcases he with he | he
      · rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp he with he | he
        · exact Or.inr (Or.inl (Subtype.ext (show (z.1:ℝ)=1 by linarith)))
        · exact Or.inl (Subtype.ext (show (z.1:ℝ)=0 by linarith))
      · rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp he with he | he
        · exact Or.inr (Or.inr (Or.inr (Subtype.ext (show (z.2:ℝ)=1 by linarith))))
        · exact Or.inr (Or.inr (Or.inl (Subtype.ext (show (z.2:ℝ)=0 by linarith))))
    · intro h
      rcases h with h | h | h | h
      · rw [h]; norm_num; exact hy
      · rw [h]; norm_num; exact hy
      · rw [h]; norm_num; exact hx
      · rw [h]; norm_num; exact hx
  have hActualSourceSquareModelStrictInterior (z : Interval × Interval)
      (hx0 : 0<(z.1:ℝ)) (hx1 : (z.1:ℝ)<1)
      (hy0 : 0<(z.2:ℝ)) (hy1 : (z.2:ℝ)<1) :
      actualSourceSquareModel z∈inside modelCurve := by
    rw [inside_modelCurve,mem_openSquare_zero_one]
    change max |2*(z.1:ℝ)-1| |2*(z.2:ℝ)-1|<1
    apply max_lt
    · exact abs_lt.mpr ⟨by linarith,by linarith⟩
    · exact abs_lt.mpr ⟨by linarith,by linarith⟩
  have hActualSourceProperSquarePathBecomesModelCrosscut
      {x y : Interval × Interval} (q : Path x y) (hq : IsEmbedding q)
      (hx : x.1=0 ∨ x.1=1 ∨ x.2=0 ∨ x.2=1)
      (hy : y.1=0 ∨ y.1=1 ∨ y.2=0 ∨ y.2=1)
      (hproper : ∀ t : Interval,0<(t:ℝ) → (t:ℝ)<1 →
        0<((q t).1:ℝ) ∧ ((q t).1:ℝ)<1 ∧ 0<((q t).2:ℝ) ∧ ((q t).2:ℝ)<1) :
      let γ := actualSourceSquareModel.comp q.toContinuousMap
      IsEmbedding γ ∧ γ 0∈modelCurve ∧ γ 1∈modelCurve ∧
        γ '' Set.Ioo (0 : Interval) 1⊆inside modelCurve ∧
        IsArcBetween (Set.range γ) (γ 0) (γ 1) := by
    as_aux_lemma =>
      let γ := actualSourceSquareModel.comp q.toContinuousMap
      have hγ : IsEmbedding γ := hActualSourceSquareModelEmbedding.comp hq
      have hγ0 : γ 0∈modelCurve := by
        change actualSourceSquareModel (q 0)∈modelCurve
        rw [q.source]
        exact (hActualSourceSquareModelBoundary x).mpr hx
      have hγ1 : γ 1∈modelCurve := by
        change actualSourceSquareModel (q 1)∈modelCurve
        rw [q.target]
        exact (hActualSourceSquareModelBoundary y).mpr hy
      have hi : γ '' Set.Ioo (0 : Interval) 1⊆inside modelCurve := by
        rintro z ⟨t,ht,rfl⟩
        obtain ⟨hx0,hx1,hy0,hy1⟩ := hproper t ht.1 ht.2
        exact hActualSourceSquareModelStrictInterior (q t) hx0 hx1 hy0 hy1
      exact ⟨hγ,hγ0,hγ1,hi,CurveComplex.source_planar_interval_isArcBetween γ hγ⟩
  have hActualSpecifiedEmbeddedBoundaryArcIsAnActualCutSide
      {C : Set Plane} (hC : IsJordanCurve C) (γ : C(Interval,Plane))
      (hγ : IsEmbedding γ) (hγC : Set.range γ⊆C) :
      ∃ T : Set Plane,IsCutPair C (γ 0) (γ 1) (Set.range γ) T := by
    as_aux_lemma =>
      have hne : γ 0≠γ 1 := fun he => by
        have hh := hγ.injective he
        norm_num at hh
      obtain ⟨A,B,hcut⟩ := exists_isCutPair hC (hγC (mem_range_self 0)) (hγC (mem_range_self 1)) hne
      let U := γ '' Set.Ioo (0 : Interval) 1
      have hUconn : IsPreconnected U := isPreconnected_Ioo.image γ γ.continuous.continuousOn
      have hUcover : U⊆A∪B := by
        rintro x ⟨t,ht,rfl⟩
        rw [hcut.union_eq]
        exact hγC (mem_range_self _)
      have hUavoid (x : Plane) (hx : x∈U) : x∉({γ 0,γ 1} : Set Plane) := by
        obtain ⟨t,ht,rfl⟩ := hx
        intro he
        rcases he with he | he
        · exact (ne_of_gt ht.1) (hγ.injective he)
        · exact (ne_of_lt ht.2) (hγ.injective (Set.mem_singleton_iff.mp he))
      have hAclosed : IsClosed A := hcut.fst.isArc.isCompact.isClosed
      have hBclosed : IsClosed B := hcut.snd.isArc.isCompact.isClosed
      have hSide : U⊆A ∨ U⊆B := by
        by_cases hUA : (U∩A).Nonempty
        · apply Or.inl
          intro x hx
          rcases hUcover hx with hA | hB
          · exact hA
          · have hUB : (U∩B).Nonempty := ⟨x,hx,hB⟩
            obtain ⟨p,hpU,hpAB⟩ := isPreconnected_closed_iff.mp hUconn A B hAclosed hBclosed hUcover hUA hUB
            rw [hcut.inter_eq] at hpAB
            exact False.elim (hUavoid p hpU hpAB)
        · apply Or.inr
          intro x hx
          rcases hUcover hx with hA | hB
          · exact False.elim (hUA ⟨x,hx,hA⟩)
          · exact hB
      have hClosureRange : Set.range γ⊆closure U := by
        rintro x ⟨t,rfl⟩
        have ht : t∈closure (Set.Ioo (0 : Interval) 1) := by
          rw [closure_Ioo (by norm_num : (0 : Interval)≠1)]
          exact ⟨t.property.1,t.property.2⟩
        exact mem_closure_image γ.continuous.continuousAt ht
      have hγArc := CurveComplex.source_planar_interval_isArcBetween γ hγ
      rcases hSide with hUA | hUB
      · have hRange : Set.range γ⊆A := hClosureRange.trans (closure_minimal hUA hAclosed)
        have he : Set.range γ=A := hcut.fst.eq_of_subset hγArc hRange
        exact ⟨B,he.symm ▸ hcut⟩
      · have hRange : Set.range γ⊆B := hClosureRange.trans (closure_minimal hUB hBclosed)
        have he : Set.range γ=B := hcut.snd.eq_of_subset hγArc hRange
        exact ⟨A,he.symm ▸ hcut.symm⟩
  have hActualDisjointProperCrosscutEndpointsStayOnSpecifiedBoundarySide
      {C A B : Set Plane} (hC : IsJordanCurve C)
      (η γ : C(Interval,Plane)) (hη : IsEmbedding η) (hγ : IsEmbedding γ)
      (hη0 : η 0∈C) (hη1 : η 1∈C)
      (hηinside : η '' Set.Ioo (0 : Interval) 1⊆inside C)
      (hγ0 : γ 0∈C) (hγ1 : γ 1∈C)
      (hγinside : γ '' Set.Ioo (0 : Interval) 1⊆inside C)
      (hcut : IsCutPair C (η 0) (η 1) A B)
      (hdisjoint : Disjoint (Set.range η) (Set.range γ)) (hstart : γ 0∈A) : γ 1∈A := by
    as_aux_lemma =>
      have hPairRange : ({η 0,η 1} : Set Plane)⊆Set.range η := by
        intro x hx
        rcases hx with hx | hx
        · exact hx ▸ mem_range_self 0
        · exact (Set.mem_singleton_iff.mp hx) ▸ mem_range_self 1
      have hStartNotB : γ 0∉B := by
        intro hB
        have hPair : γ 0∈({η 0,η 1} : Set Plane) := hcut.inter_eq ▸ ⟨hstart,hB⟩
        exact Set.disjoint_left.mp hdisjoint (hPairRange hPair) (mem_range_self 0)
      have hηProper : Set.range η\{η 0,η 1}⊆inside C := by
        rintro x ⟨⟨t,rfl⟩,ht⟩
        have ht0 : t≠0 := fun h => ht (Or.inl (congrArg η h))
        have ht1 : t≠1 := fun h => ht (Or.inr (Set.mem_singleton_iff.mpr (congrArg η h)))
        exact hηinside ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩
      have hηBoundary : Set.range η∩C={η 0,η 1} := by
        apply Set.Subset.antisymm
        · intro x hx
          by_contra hp
          exact inside_subset_compl (hηProper ⟨hx.1,hp⟩) hx.2
        · intro x hx
          refine ⟨hPairRange hx,?_⟩
          rcases hx with hx | hx
          · exact hx ▸ hη0
          · exact (Set.mem_singleton_iff.mp hx) ▸ hη1
      let U := γ '' Set.Ioo (0 : Interval) 1
      have hUconnected : IsPreconnected U := isPreconnected_Ioo.image γ γ.continuous.continuousOn
      have hEndClosure (t : Interval) : γ t∈closure U := by
        have ht : t∈closure (Set.Ioo (0 : Interval) 1) := by
          rw [closure_Ioo (by norm_num : (0 : Interval)≠1)]
          exact ⟨t.property.1,t.property.2⟩
        exact mem_closure_image γ.continuous.continuousAt ht
      by_contra hnot
      have hEndB : γ 1∈B := by
        have hcover : γ 1∈A∪B := hcut.union_eq.symm ▸ hγ1
        exact hcover.resolve_left hnot
      obtain ⟨x,hxU,hxη⟩ := arbitrary_jordan_crosscut_alternating_inter_nonempty hC
        (CurveComplex.source_planar_interval_isArcBetween η hη) hcut hηBoundary hηProper
        hUconnected hγinside (hEndClosure 0) (hEndClosure 1) hstart hStartNotB hEndB hnot
      have hxγ : x∈Set.range γ := by
        obtain ⟨t,ht,rfl⟩ := hxU
        exact mem_range_self t
      exact Set.disjoint_left.mp hdisjoint hxη hxγ
  have hActualSpecifiedBoundaryArcCarrierIsAnActualCutSide
      {C A : Set Plane} {p q : Plane} (hC : IsJordanCurve C)
      (hA : IsArcBetween A p q) (hAC : A⊆C) :
      ∃ T : Set Plane,IsCutPair C p q A T := by
    as_aux_lemma =>
      obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
      let γ : C(Interval,Plane) := ⟨fun t => f t.val,hf.restrict⟩
      have hγ : IsEmbedding γ := (γ.continuous.isClosedEmbedding (fun t u he =>
        Subtype.ext (hi t.property u.property he))).isEmbedding
      have hRange : Set.range γ=A := by
        ext x
        constructor
        · rintro ⟨t,rfl⟩
          rw [←himage]
          exact ⟨t,t.property,rfl⟩
        · intro hx
          rw [←himage] at hx
          obtain ⟨t,ht,rfl⟩ := hx
          exact ⟨⟨t,ht⟩,rfl⟩
      obtain ⟨T,hcut⟩ := hActualSpecifiedEmbeddedBoundaryArcIsAnActualCutSide hC γ hγ
        (hRange ▸ hAC)
      have h0 : γ 0=p := hf0
      have h1 : γ 1=q := hf1
      rw [h0,h1,hRange] at hcut
      exact ⟨T,hcut⟩
  let actualModelInitialBoundarySegment (s t : Interval) : Set Plane :=
    segment ℝ (actualSourceSquareModel (0,s)) (actualSourceSquareModel (0,t))
  have hActualModelInitialBoundarySegmentMembership (s t : Interval) (hst : s<t)
      (z : Interval × Interval) :
      actualSourceSquareModel z∈actualModelInitialBoundarySegment s t ↔
        z.1=0 ∧ s≤z.2 ∧ z.2≤t := by
    change Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1)∈
      segment ℝ (Plane.mk (2*(0:ℝ)-1) (2*(s:ℝ)-1)) (Plane.mk (2*(0:ℝ)-1) (2*(t:ℝ)-1)) ↔ _
    norm_num only [mul_zero,zero_sub]
    rw [mem_segment_vert,segment_eq_Icc (show 2*(s:ℝ)-1≤2*(t:ℝ)-1 by
      have hh : (s:ℝ)<(t:ℝ) := hst
      linarith)]
    change (2*(z.1:ℝ)-1= -1 ∧ 2*(s:ℝ)-1≤2*(z.2:ℝ)-1 ∧
      2*(z.2:ℝ)-1≤2*(t:ℝ)-1) ↔ z.1=0 ∧ s≤z.2 ∧ z.2≤t
    constructor
    · rintro ⟨hx,hy0,hy1⟩
      refine ⟨Subtype.ext (show (z.1:ℝ)=0 by linarith),?_,?_⟩
      · change (s:ℝ)≤(z.2:ℝ)
        linarith
      · change (z.2:ℝ)≤(t:ℝ)
        linarith
    · rintro ⟨hx,hy0,hy1⟩
      rw [hx]
      refine ⟨by norm_num,?_,?_⟩
      · have hh : (s:ℝ)≤(z.2:ℝ) := hy0
        linarith
      · have hh : (z.2:ℝ)≤(t:ℝ) := hy1
        linarith
  have hActualModelInitialBoundarySegmentIsActualCutSide (s t : Interval) (hst : s<t) :
      ∃ B : Set Plane,IsCutPair modelCurve (actualSourceSquareModel (0,s))
        (actualSourceSquareModel (0,t)) (actualModelInitialBoundarySegment s t) B := by
    as_aux_lemma =>
      have hne : actualSourceSquareModel (0,s)≠actualSourceSquareModel (0,t) := by
        intro he
        have hh : s=t := congrArg Prod.snd (hActualSourceSquareModelInjective he)
        exact (ne_of_lt hst) hh
      have hArc : IsArcBetween (actualModelInitialBoundarySegment s t)
          (actualSourceSquareModel (0,s)) (actualSourceSquareModel (0,t)) := isArcBetween_segment hne
      have hSubset : actualModelInitialBoundarySegment s t⊆modelCurve := by
        intro x hx
        change x∈segment ℝ (Plane.mk (2*(0:ℝ)-1) (2*(s:ℝ)-1)) (Plane.mk (2*(0:ℝ)-1) (2*(t:ℝ)-1)) at hx
        norm_num only [mul_zero,zero_sub] at hx
        rw [mem_segment_vert,segment_eq_Icc (show 2*(s:ℝ)-1≤2*(t:ℝ)-1 by
          have hh : (s:ℝ)<(t:ℝ) := hst
          linarith)] at hx
        have habs : |x 1|≤1 := abs_le.mpr ⟨by linarith [s.property.1,hx.2.1],by linarith [t.property.2,hx.2.2]⟩
        change max |x 0| |x 1|=1
        rw [hx.1]
        norm_num
        exact habs
      exact hActualSpecifiedBoundaryArcCarrierIsAnActualCutSide isJordanCurve_modelCurve hArc hSubset
  have hActualBottomReturnTrapsEveryDisjointProperContactPathEndpoint
      (s t u : Interval) (hst : s<t) (hu : s<u ∧ u<t)
      {z : Interval × Interval} (η : Path ((0 : Interval),s) (0,t))
      (γ : Path ((0 : Interval),u) z) (hη : IsEmbedding η) (hγ : IsEmbedding γ)
      (hηproper : ∀ r : Interval,0<(r:ℝ) → (r:ℝ)<1 →
        0<((η r).1:ℝ) ∧ ((η r).1:ℝ)<1 ∧ 0<((η r).2:ℝ) ∧ ((η r).2:ℝ)<1)
      (hγproper : ∀ r : Interval,0<(r:ℝ) → (r:ℝ)<1 →
        0<((γ r).1:ℝ) ∧ ((γ r).1:ℝ)<1 ∧ 0<((γ r).2:ℝ) ∧ ((γ r).2:ℝ)<1)
      (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1)
      (hdisjoint : Disjoint (Set.range η) (Set.range γ)) :
      z.1=0 ∧ s<z.2 ∧ z.2<t := by
    as_aux_lemma =>
      let ηM := actualSourceSquareModel.comp η.toContinuousMap
      let γM := actualSourceSquareModel.comp γ.toContinuousMap
      obtain ⟨hηM,hηM0,hηM1,hηMi,hηArc⟩ := hActualSourceProperSquarePathBecomesModelCrosscut
        η hη (Or.inl rfl) (Or.inl rfl) hηproper
      obtain ⟨hγM,hγM0,hγM1,hγMi,hγArc⟩ := hActualSourceProperSquarePathBecomesModelCrosscut
        γ hγ (Or.inl rfl) hz hγproper
      have hη0 : ηM 0=actualSourceSquareModel (0,s) := congrArg actualSourceSquareModel η.source
      have hη1 : ηM 1=actualSourceSquareModel (0,t) := congrArg actualSourceSquareModel η.target
      have hγ0 : γM 0=actualSourceSquareModel (0,u) := congrArg actualSourceSquareModel γ.source
      have hγ1 : γM 1=actualSourceSquareModel z := congrArg actualSourceSquareModel γ.target
      obtain ⟨B,hcut⟩ := hActualModelInitialBoundarySegmentIsActualCutSide s t hst
      have hCut : IsCutPair modelCurve (ηM 0) (ηM 1) (actualModelInitialBoundarySegment s t) B := by
        rw [hη0,hη1]
        exact hcut
      have hStart : γM 0∈actualModelInitialBoundarySegment s t := by
        rw [hγ0]
        exact (hActualModelInitialBoundarySegmentMembership s t hst (0,u)).mpr ⟨rfl,hu.1.le,hu.2.le⟩
      have hModelDisjoint : Disjoint (Set.range ηM) (Set.range γM) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨r,hr⟩ ⟨v,hv⟩
        have he : η r=γ v := hActualSourceSquareModelInjective (hr.trans hv.symm)
        exact Set.disjoint_left.mp hdisjoint (mem_range_self r) ⟨v,he.symm⟩
      have hEnd := hActualDisjointProperCrosscutEndpointsStayOnSpecifiedBoundarySide isJordanCurve_modelCurve
        ηM γM hηM hγM hηM0 hηM1 hηMi hγM0 hγM1 hγMi hCut hModelDisjoint hStart
      rw [hγ1] at hEnd
      have hBounds := (hActualModelInitialBoundarySegmentMembership s t hst z).mp hEnd
      have hzs : z≠(0,s) := by
        intro he
        exact Set.disjoint_left.mp hdisjoint ⟨0,η.source⟩ ⟨1,γ.target.trans he⟩
      have hzt : z≠(0,t) := by
        intro he
        exact Set.disjoint_left.mp hdisjoint ⟨1,η.target⟩ ⟨1,γ.target.trans he⟩
      exact ⟨hBounds.1,lt_of_le_of_ne hBounds.2.1 (fun he => hzs (Prod.ext hBounds.1 he.symm)),
        lt_of_le_of_ne hBounds.2.2 (fun he => hzt (Prod.ext hBounds.1 he))⟩
  have hActualModelInitialPointLiteral (t : Interval) :
      actualSourceSquareModel (0,t)=Plane.mk (-1) (2*(t:ℝ)-1) := by
    ext i
    fin_cases i <;> norm_num [actualSourceSquareModel]
  have hActualModelLowerSidePointLiteral (t : Interval) :
      actualSourceSquareModel (t,0)=Plane.mk (2*(t:ℝ)-1) (-1) := by
    ext i
    fin_cases i <;> norm_num [actualSourceSquareModel]
  have hActualModelUpperSidePointLiteral (t : Interval) :
      actualSourceSquareModel (t,1)=Plane.mk (2*(t:ℝ)-1) 1 := by
    ext i
    fin_cases i <;> norm_num [actualSourceSquareModel]
  have hActualModelLeftThenTopBoundaryIsSpecifiedCutSide
      (s r : Interval) (hs : (s:ℝ)<1) (hr : 0<(r:ℝ)) :
      ∃ A B : Set Plane,IsCutPair modelCurve (actualSourceSquareModel (0,s))
        (actualSourceSquareModel (r,1)) A B ∧
        (∀ t : Interval,s≤t → actualSourceSquareModel (0,t)∈A) ∧
        (∀ v : Interval,0<(v:ℝ) → actualSourceSquareModel (v,0)∉A) := by
    as_aux_lemma =>
      let p := Plane.mk (-1) (2*(s:ℝ)-1)
      let q := Plane.mk (2*(r:ℝ)-1) 1
      let c := cornerNW
      let A₁ := segment ℝ p c
      let A₂ := segment ℝ c q
      let A := A₁∪A₂
      have hp : p≠c := by
        intro he
        have h := congrArg (fun z : Plane => z 1) he
        change 2*(s:ℝ)-1=1 at h
        linarith
      have hq : c≠q := by
        intro he
        have h := congrArg (fun z : Plane => z 0) he
        change -1=2*(r:ℝ)-1 at h
        linarith
      have hA₁ : IsArcBetween A₁ p c := isArcBetween_segment hp
      have hA₂ : IsArcBetween A₂ c q := isArcBetween_segment hq
      have hA₁coords (x : Plane) (hx : x∈A₁) :
          x 0= -1 ∧ 2*(s:ℝ)-1≤x 1 ∧ x 1≤1 := by
        change x∈segment ℝ (Plane.mk (-1) (2*(s:ℝ)-1)) (Plane.mk (-1) 1) at hx
        rw [mem_segment_vert,segment_eq_Icc (show 2*(s:ℝ)-1≤1 by linarith)] at hx
        exact hx
      have hA₂coords (x : Plane) (hx : x∈A₂) :
          x 1=1 ∧ -1≤x 0 ∧ x 0≤2*(r:ℝ)-1 := by
        change x∈segment ℝ (Plane.mk (-1) 1) (Plane.mk (2*(r:ℝ)-1) 1) at hx
        rw [mem_segment_horiz,segment_eq_Icc (show -1≤2*(r:ℝ)-1 by linarith)] at hx
        exact hx
      have hMeet : A₁∩A₂={c} := by
        ext x
        constructor
        · intro hx
          have hx0 := (hA₁coords x hx.1).1
          have hx1 := (hA₂coords x hx.2).1
          apply Set.mem_singleton_iff.mpr
          ext i
          fin_cases i
          · exact hx0
          · exact hx1
        · intro hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact ⟨hA₁.right_mem,hA₂.left_mem⟩
      have hArc : IsArcBetween A p q := hA₁.concatenate hA₂ (fun z hz₁ hz₂ => Set.mem_singleton_iff.mp (hMeet ▸ ⟨hz₁,hz₂⟩))
      have hASubset : A⊆modelCurve := by
        intro x hx
        rcases hx with hx | hx
        · obtain ⟨hx0,hxlo,hxhi⟩ := hA₁coords x hx
          have habs : |x 1|≤1 := abs_le.mpr ⟨by linarith [s.property.1],hxhi⟩
          change max |x 0| |x 1|=1
          rw [hx0]
          norm_num
          exact habs
        · obtain ⟨hx1,hxlo,hxhi⟩ := hA₂coords x hx
          have habs : |x 0|≤1 := abs_le.mpr ⟨hxlo,by linarith [r.property.2]⟩
          change max |x 0| |x 1|=1
          rw [hx1]
          norm_num
          exact habs
      obtain ⟨B,hCut⟩ := hActualSpecifiedBoundaryArcCarrierIsAnActualCutSide isJordanCurve_modelCurve hArc hASubset
      have hCutLiteral : IsCutPair modelCurve (actualSourceSquareModel (0,s))
          (actualSourceSquareModel (r,1)) A B := by
        rw [hActualModelInitialPointLiteral,hActualModelUpperSidePointLiteral]
        exact hCut
      refine ⟨A,B,hCutLiteral,?_,?_⟩
      · intro t ht
        apply Or.inl
        rw [hActualModelInitialPointLiteral]
        change Plane.mk (-1) (2*(t:ℝ)-1)∈segment ℝ
          (Plane.mk (-1) (2*(s:ℝ)-1)) (Plane.mk (-1) 1)
        rw [mem_segment_vert,segment_eq_Icc (show 2*(s:ℝ)-1≤1 by linarith)]
        change -1= -1 ∧ 2*(s:ℝ)-1≤2*(t:ℝ)-1 ∧ 2*(t:ℝ)-1≤1
        have hst : (s:ℝ)≤(t:ℝ) := ht
        exact ⟨rfl,by linarith,by linarith [t.property.2]⟩
      · intro v hv hA
        rw [hActualModelLowerSidePointLiteral] at hA
        rcases hA with hA | hA
        · have hx := (hA₁coords _ hA).1
          change 2*(v:ℝ)-1= -1 at hx
          linarith
        · have hx := (hA₂coords _ hA).1
          change -1=1 at hx
          norm_num at hx

  have hActualOrderedBottomToOppositeSideProperCrosscutsMustMeet
      (s t r v : Interval) (hst : s<t) (hr : 0<(r:ℝ)) (hv : 0<(v:ℝ))
      (η : Path ((0 : Interval),s) (r,1)) (γ : Path ((0 : Interval),t) (v,0))
      (hη : IsEmbedding η) (hγ : IsEmbedding γ)
      (hηproper : ∀ a : Interval,0<(a:ℝ) → (a:ℝ)<1 →
        0<((η a).1:ℝ) ∧ ((η a).1:ℝ)<1 ∧ 0<((η a).2:ℝ) ∧ ((η a).2:ℝ)<1)
      (hγproper : ∀ a : Interval,0<(a:ℝ) → (a:ℝ)<1 →
        0<((γ a).1:ℝ) ∧ ((γ a).1:ℝ)<1 ∧ 0<((γ a).2:ℝ) ∧ ((γ a).2:ℝ)<1) :
      ¬Disjoint (Set.range η) (Set.range γ) := by
    as_aux_lemma =>
      intro hdisjoint
      let ηM := actualSourceSquareModel.comp η.toContinuousMap
      let γM := actualSourceSquareModel.comp γ.toContinuousMap
      obtain ⟨hηM,hηM0,hηM1,hηMi,hηArc⟩ := hActualSourceProperSquarePathBecomesModelCrosscut
        η hη (Or.inl rfl) (Or.inr (Or.inr (Or.inr rfl))) hηproper
      obtain ⟨hγM,hγM0,hγM1,hγMi,hγArc⟩ := hActualSourceProperSquarePathBecomesModelCrosscut
        γ hγ (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) hγproper
      have hη0 : ηM 0=actualSourceSquareModel (0,s) := congrArg actualSourceSquareModel η.source
      have hη1 : ηM 1=actualSourceSquareModel (r,1) := congrArg actualSourceSquareModel η.target
      have hγ0 : γM 0=actualSourceSquareModel (0,t) := congrArg actualSourceSquareModel γ.source
      have hγ1 : γM 1=actualSourceSquareModel (v,0) := congrArg actualSourceSquareModel γ.target
      have hs : (s:ℝ)<1 := by
        have hh : (s:ℝ)<(t:ℝ) := hst
        linarith [t.property.2]
      obtain ⟨A,B,hcut,hHigher,hLowerFree⟩ := hActualModelLeftThenTopBoundaryIsSpecifiedCutSide s r hs hr
      have hCut : IsCutPair modelCurve (ηM 0) (ηM 1) A B := by
        rw [hη0,hη1]
        exact hcut
      have hStart : γM 0∈A := by
        rw [hγ0]
        exact hHigher t hst.le
      have hModelDisjoint : Disjoint (Set.range ηM) (Set.range γM) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨a,ha⟩ ⟨b,hb⟩
        have he : η a=γ b := hActualSourceSquareModelInjective (ha.trans hb.symm)
        exact Set.disjoint_left.mp hdisjoint (mem_range_self a) ⟨b,he.symm⟩
      have hEnd := hActualDisjointProperCrosscutEndpointsStayOnSpecifiedBoundarySide isJordanCurve_modelCurve
        ηM γM hηM hγM hηM0 hηM1 hηMi hγM0 hγM1 hγMi hCut hModelDisjoint hStart
      rw [hγ1] at hEnd
      exact hLowerFree v hv hEnd

  have hActualBottomReturnProducesStrictlyNestedChildPath
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (w z r : actualContactVertices) (hw : w.val.1=0) (hz : z.val.1=0)
      (hr : r.val.1=0) (hwr : w.val.2<r.val.2) (hrz : r.val.2<z.val.2)
      (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z)) (hP : P.IsPath)
      (hdegree : ∀ v,v∈P.support → v≠Sum.inl w → v≠Sum.inl z → actualZeroGraph.degree v=2)
      (hproper : ∀ v,v∈P.support → v≠Sum.inl w → v≠Sum.inl z → ¬actualContactGraphOuterBoundary v) :
      ∃ c : actualContactVertices,c≠r ∧ c.val.1=0 ∧ w.val.2<c.val.2 ∧ c.val.2<z.val.2 ∧
        ∃ Q : actualZeroGraph.Walk (Sum.inl r) (Sum.inl c),Q.IsPath ∧
          (∀ v,v∈Q.support → v≠Sum.inl r → v≠Sum.inl c → actualZeroGraph.degree v=2) ∧
          (∀ v,v∈Q.support → v≠Sum.inl r → v≠Sum.inl c → ¬actualContactGraphOuterBoundary v) := by
    as_aux_lemma =>
      have hwz : w.val.2<z.val.2 := lt_trans hwr hrz
      have hzw : z≠w := by
        intro he
        exact (ne_of_lt hwz) (congrArg (fun v : actualContactVertices => v.val.2) he).symm
      have hrw : (Sum.inl r : zeroVertex)≠Sum.inl w := by
        intro he
        exact (ne_of_lt hwr) (congrArg (fun v : actualContactVertices => v.val.2) (Sum.inl.inj he)).symm
      have hrz' : (Sum.inl r : zeroVertex)≠Sum.inl z := by
        intro he
        exact (ne_of_lt hrz) (congrArg (fun v : actualContactVertices => v.val.2) (Sum.inl.inj he))
      have hroutside : (Sum.inl r : zeroVertex)∉P.support := by
        intro h
        exact hproper _ h hrw hrz' (Or.inl hr)
      obtain ⟨WP,hWP,hPV,η,hη,hηimage,hηproper,κ,hκ,hκinside⟩ :=
        hActualBoundaryProperGraphPathLiftsToProperOriginalContactPath hBoundary hzw P hP hproper
      obtain ⟨c,hcr,hcside,Q,hQ,hQdegree,hQboundary,WQ,hWQ,hQV,γ,hγ,hγimage,hγproper,ρ,hρ,hρinside⟩ :=
        hActualEveryBottomContactHasGraphFirstBoundaryProperOriginalContactPath hBoundary r hr
      have hsupport := hActualDegreeOneEndedDegreeTwoInternalPathIsAnEntireGraphComponent P hP
        (fun he => hzw (Sum.inl.inj he).symm)
        (hActualEveryInitialContactVertexDegreeOne w hw)
        (hActualEveryInitialContactVertexDegreeOne z hz) hdegree Q hroutside
      have hcarriers := hActualDisjointContactGraphSupportsGiveDisjointPlanarCarriers P Q WP WQ
        hWP hWQ hPV hQV hsupport
      have hranges : Disjoint (Set.range η) (Set.range γ) := by
        apply Set.disjoint_left.mpr
        intro x hx hy
        have hxP : actualParameterSquarePlane x∈Graph.edgesCover actualPlanarDrawing WP := by
          rw [←hηimage]
          exact ⟨x,hx,rfl⟩
        have hxQ : actualParameterSquarePlane x∈Graph.edgesCover actualPlanarDrawing WQ := by
          rw [←hγimage]
          exact ⟨x,hy,rfl⟩
        exact Set.disjoint_left.mp hcarriers hxP hxQ
      let η' : Path ((0 : Interval),w.val.2) (0,z.val.2) :=
        η.cast (Prod.ext hw.symm rfl) (Prod.ext hz.symm rfl)
      let γ' : Path ((0 : Interval),r.val.2) c.val :=
        γ.cast (Prod.ext hr.symm rfl) rfl
      have htrap := hActualBottomReturnTrapsEveryDisjointProperContactPathEndpoint
        w.val.2 z.val.2 r.val.2 hwz ⟨hwr,hrz⟩ η' γ' hη hγ hηproper hγproper
        (by rcases hcside with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))) hranges
      exact ⟨c,hcr,htrap.1,htrap.2.1,htrap.2.2,Q,hQ,hQdegree,hQboundary⟩

  let actualBottomReturnGraphPair (w z : actualContactVertices) : Prop :=
    w.val.1=0 ∧ z.val.1=0 ∧ w.val.2<z.val.2 ∧
      ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
        (∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → actualZeroGraph.degree r=2) ∧
        (∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → ¬actualContactGraphOuterBoundary r)
  have hActualBottomProperGraphPathHasAnOrderedReturn
      (w z : actualContactVertices) (hw : w.val.1=0) (hz : z.val.1=0) (hzw : z≠w)
      (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z)) (hP : P.IsPath)
      (hdegree : ∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → actualZeroGraph.degree r=2)
      (hproper : ∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → ¬actualContactGraphOuterBoundary r) :
      actualBottomReturnGraphPair w z ∨ actualBottomReturnGraphPair z w := by
    as_aux_lemma =>
      have hheight : w.val.2≠z.val.2 := by
        intro he
        exact hzw (Subtype.ext (Prod.ext (hz.trans hw.symm) he.symm))
      rcases lt_or_gt_of_ne hheight with h | h
      · exact Or.inl ⟨hw,hz,h,P,hP,hdegree,hproper⟩
      · apply Or.inr
        refine ⟨hz,hw,h,P.reverse,hP.reverse,?_,?_⟩
        · intro r hr hrz hrw
          exact hdegree r (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hr) hrw hrz
        · intro r hr hrz hrw
          exact hproper r (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hr) hrw hrz

  have hActualAnyBottomReturnWithInteriorContactHasSmallerNestedReturn
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (w z : actualContactVertices) (hreturn : actualBottomReturnGraphPair w z)
      (hinside : ∃ r : actualContactVertices,r.val.1=0 ∧ w.val.2<r.val.2 ∧ r.val.2<z.val.2) :
      ∃ u v : actualContactVertices,actualBottomReturnGraphPair u v ∧
        w.val.2<u.val.2 ∧ v.val.2<z.val.2 := by
    as_aux_lemma =>
      obtain ⟨hw,hz,hwz,P,hP,hdegree,hproper⟩ := hreturn
      obtain ⟨r,hr,hwr,hrz⟩ := hinside
      obtain ⟨c,hcr,hc,hwc,hcz,Q,hQ,hQdegree,hQproper⟩ :=
        hActualBottomReturnProducesStrictlyNestedChildPath hBoundary w z r hw hz hr hwr hrz P hP hdegree hproper
      rcases hActualBottomProperGraphPathHasAnOrderedReturn r c hr hc hcr Q hQ hQdegree hQproper with h | h
      · exact ⟨r,c,h,hwr,hcz⟩
      · exact ⟨c,r,h,hwc,hrz⟩
  have hActualFiniteContactGraphHasInnermostOriginalBottomReturn
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hex : ∃ w z : actualContactVertices,actualBottomReturnGraphPair w z) :
      ∃ w z : actualContactVertices,actualBottomReturnGraphPair w z ∧
        ¬∃ r : actualContactVertices,r.val.1=0 ∧ w.val.2<r.val.2 ∧ r.val.2<z.val.2 := by
    as_aux_lemma =>
      classical
      let count (w z : actualContactVertices) :=
        (Finset.univ.filter (fun r : actualContactVertices =>
          r.val.1=0 ∧ w.val.2≤r.val.2 ∧ r.val.2≤z.val.2)).card
      have hn : ∃ n,∃ w z : actualContactVertices,actualBottomReturnGraphPair w z ∧ count w z=n := by
        obtain ⟨w,z,h⟩ := hex
        exact ⟨count w z,w,z,h,rfl⟩
      obtain ⟨w,z,hreturn,hcount⟩ := Nat.find_spec hn
      refine ⟨w,z,hreturn,?_⟩
      intro hinterior
      obtain ⟨u,v,hchild,hwu,hvz⟩ :=
        hActualAnyBottomReturnWithInteriorContactHasSmallerNestedReturn hBoundary w z hreturn hinterior
      have hminimum : count w z≤count u v := by
        rw [hcount]
        exact Nat.find_min' hn ⟨u,v,hchild,rfl⟩
      have hstrict : count u v<count w z := by
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        constructor
        · intro r hr
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hr ⊢
          exact ⟨hr.1,le_trans (le_of_lt hwu) hr.2.1,le_trans hr.2.2 (le_of_lt hvz)⟩
        · intro he
          have hm : w∈Finset.univ.filter (fun r : actualContactVertices =>
              r.val.1=0 ∧ w.val.2≤r.val.2 ∧ r.val.2≤z.val.2) := by
            simp only [Finset.mem_filter,Finset.mem_univ,true_and]
            exact ⟨hreturn.1,le_rfl,le_of_lt hreturn.2.2.1⟩
          rw [←he] at hm
          simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hm
          exact (not_le_of_gt hwu) hm.2.1
      exact (not_lt_of_ge hminimum) hstrict

  have hActualOrderedBottomOppositeSideContactGraphPathsAreImpossible
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (w z u v : actualContactVertices) (hw : w.val.1=0) (hu : u.val.1=0)
      (horder : w.val.2≤u.val.2) (hz : z.val.2=1) (hv : v.val.2=0)
      (hzoff : z.val.1≠0) (hvoff : v.val.1≠0)
      (P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z)) (hP : P.IsPath)
      (Q : actualZeroGraph.Walk (Sum.inl u) (Sum.inl v)) (hQ : Q.IsPath)
      (hdegree : ∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → actualZeroGraph.degree r=2)
      (hPB : ∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → ¬actualContactGraphOuterBoundary r)
      (hQB : ∀ r,r∈Q.support → r≠Sum.inl u → r≠Sum.inl v → ¬actualContactGraphOuterBoundary r) : False := by
    as_aux_lemma =>
      have hzNeBottom (r : actualContactVertices) (hr : r.val.1=0) : z≠r := by
        intro he
        exact hzoff ((congrArg (fun v : actualContactVertices => v.val.1) he).trans hr)
      have hvNeBottom (r : actualContactVertices) (hr : r.val.1=0) : v≠r := by
        intro he
        exact hvoff ((congrArg (fun v : actualContactVertices => v.val.1) he).trans hr)
      have hvz : v≠z := by
        intro he
        have hh := (congrArg (fun v : actualContactVertices => v.val.2) he)
        rw [hv,hz] at hh
        exact zero_ne_one hh
      have hzw := hzNeBottom w hw
      have hvu := hvNeBottom u hu
      by_cases hwu : w=u
      · subst u
        have he := hActualDegreeOneStartProperDegreeTwoPathsHaveSameFirstBoundaryEndpoint P hP
          (fun he => hzw (Sum.inl.inj he).symm) Q
          (fun he => hvu (Sum.inl.inj he).symm) actualContactGraphOuterBoundary
          (hActualEveryInitialContactVertexDegreeOne w hw)
          (Or.inr (Or.inr (Or.inr hz))) (Or.inr (Or.inr (Or.inl hv))) hPB hQB hdegree
        exact hvz (Sum.inl.inj he).symm
      have hstrict : w.val.2<u.val.2 := lt_of_le_of_ne horder (by
        intro he
        exact hwu (Subtype.ext (Prod.ext (hw.trans hu.symm) he)))
      have hsupport := hActualBoundaryProperDegreeTwoPathsWithDisjointEndsHaveDisjointSupport
        P hP Q hQ actualContactGraphOuterBoundary (Or.inl hw) (Or.inr (Or.inr (Or.inr hz)))
        (Or.inl hu) (Or.inr (Or.inr (Or.inl hv))) hPB hQB hdegree
        (fun he => hwu (Sum.inl.inj he).symm)
        (fun he => hzNeBottom u hu (Sum.inl.inj he).symm)
        (fun he => hvNeBottom w hw (Sum.inl.inj he)) (fun he => hvz (Sum.inl.inj he))
      obtain ⟨WP,hWP,hPV,η,hη,hηimage,hηproper,κ,hκ,hκinside⟩ :=
        hActualBoundaryProperGraphPathLiftsToProperOriginalContactPath hBoundary hzw P hP hPB
      obtain ⟨WQ,hWQ,hQV,γ,hγ,hγimage,hγproper,ρ,hρ,hρinside⟩ :=
        hActualBoundaryProperGraphPathLiftsToProperOriginalContactPath hBoundary hvu Q hQ hQB
      have hcarriers := hActualDisjointContactGraphSupportsGiveDisjointPlanarCarriers P Q WP WQ
        hWP hWQ hPV hQV hsupport
      have hranges : Disjoint (Set.range η) (Set.range γ) := by
        apply Set.disjoint_left.mpr
        intro x hx hy
        have hxP : actualParameterSquarePlane x∈Graph.edgesCover actualPlanarDrawing WP := by
          rw [←hηimage]
          exact ⟨x,hx,rfl⟩
        have hxQ : actualParameterSquarePlane x∈Graph.edgesCover actualPlanarDrawing WQ := by
          rw [←hγimage]
          exact ⟨x,hy,rfl⟩
        exact Set.disjoint_left.mp hcarriers hxP hxQ
      let η' : Path ((0 : Interval),w.val.2) (z.val.1,1) :=
        η.cast (Prod.ext hw.symm rfl) (Prod.ext rfl hz.symm)
      let γ' : Path ((0 : Interval),u.val.2) (v.val.1,0) :=
        γ.cast (Prod.ext hu.symm rfl) (Prod.ext rfl hv.symm)
      exact hActualOrderedBottomToOppositeSideProperCrosscutsMustMeet w.val.2 u.val.2 z.val.1 v.val.1
        hstrict (lt_of_le_of_ne z.val.1.property.1 (fun he => hzoff (Subtype.ext he.symm)))
        (lt_of_le_of_ne v.val.1.property.1 (fun he => hvoff (Subtype.ext he.symm)))
        η' γ' hη hγ hηproper hγproper hranges

  have hActualNoBottomReturnGraphHasAnExtremeSideContactPath
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hbottom : ∃ w : actualContactVertices,w.val.1=0)
      (hno : ¬∃ w z : actualContactVertices,actualBottomReturnGraphPair w z) :
      ∃ w z : actualContactVertices,z≠w ∧ w.val.1=0 ∧
        ((z.val.2=0 ∧ ∀ r : actualContactVertices,r.val.1=0 → w.val.2≤r.val.2) ∨
         (z.val.2=1 ∧ ∀ r : actualContactVertices,r.val.1=0 → r.val.2≤w.val.2)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          (∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → actualZeroGraph.degree r=2) ∧
          (∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → ¬actualContactGraphOuterBoundary r) := by
    as_aux_lemma =>
      classical
      let bottoms := Finset.univ.filter (fun w : actualContactVertices => w.val.1=0)
      have hnonempty : bottoms.Nonempty := by
        obtain ⟨w,hw⟩ := hbottom
        exact ⟨w,by simp [bottoms,hw]⟩
      obtain ⟨w,hwmem,hmin⟩ := bottoms.exists_min_image (fun r => r.val.2) hnonempty
      obtain ⟨u,humem,hmax⟩ := bottoms.exists_max_image (fun r => r.val.2) hnonempty
      have hw : w.val.1=0 := (Finset.mem_filter.mp hwmem).2
      have hu : u.val.1=0 := (Finset.mem_filter.mp humem).2
      have hminimum (r : actualContactVertices) (hr : r.val.1=0) : w.val.2≤r.val.2 :=
        hmin r (by simp [bottoms,hr])
      have hmaximum (r : actualContactVertices) (hr : r.val.1=0) : r.val.2≤u.val.2 :=
        hmax r (by simp [bottoms,hr])
      obtain ⟨z,hzw,hzside,P,hP,hPdegree,hPB,WP,hWP,hPV,η,hη,hηimage,hηproper,κ,hκ,hκinside⟩ :=
        hActualEveryBottomContactHasGraphFirstBoundaryProperOriginalContactPath hBoundary w hw
      obtain ⟨v,hvu,hvside,Q,hQ,hQdegree,hQB,WQ,hWQ,hQV,γ,hγ,hγimage,hγproper,ρ,hρ,hρinside⟩ :=
        hActualEveryBottomContactHasGraphFirstBoundaryProperOriginalContactPath hBoundary u hu
      have hzoff : z.val.1≠0 := by
        intro hz
        rcases hActualBottomProperGraphPathHasAnOrderedReturn w z hw hz hzw P hP hPdegree hPB with h | h
        · exact hno ⟨w,z,h⟩
        · exact hno ⟨z,w,h⟩
      have hvoff : v.val.1≠0 := by
        intro hv
        rcases hActualBottomProperGraphPathHasAnOrderedReturn u v hu hv hvu Q hQ hQdegree hQB with h | h
        · exact hno ⟨u,v,h⟩
        · exact hno ⟨v,u,h⟩
      by_cases hzleft : z.val.2=0
      · exact ⟨w,z,hzw,hw,Or.inl ⟨hzleft,hminimum⟩,P,hP,hPdegree,hPB⟩
      by_cases hvright : v.val.2=1
      · exact ⟨u,v,hvu,hu,Or.inr ⟨hvright,hmaximum⟩,Q,hQ,hQdegree,hQB⟩
      have hzright : z.val.2=1 := by
        rcases hzside with h | h | h
        · exact False.elim (hzoff h)
        · exact False.elim (hzleft h)
        · exact h
      have hvleft : v.val.2=0 := by
        rcases hvside with h | h | h
        · exact False.elim (hvoff h)
        · exact h
        · exact False.elim (hvright h)
      exact False.elim (hActualOrderedBottomOppositeSideContactGraphPathsAreImpossible hBoundary w z u v
        hw hu (hminimum u hu) hzright hvleft hzoff hvoff P hP Q hQ hPdegree hPB hQB)

  have hActualFiniteSameSourceGraphProducesCleanOriginalContactPath
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hbottom : ∃ w : actualContactVertices,w.val.1=0) :
      ∃ w z : actualContactVertices,z≠w ∧ w.val.1=0 ∧
        ((z.val.1=0 ∧ w.val.2<z.val.2 ∧
            ¬∃ r : actualContactVertices,r.val.1=0 ∧ w.val.2<r.val.2 ∧ r.val.2<z.val.2) ∨
         (z.val.2=0 ∧ ∀ r : actualContactVertices,r.val.1=0 → w.val.2≤r.val.2) ∨
         (z.val.2=1 ∧ ∀ r : actualContactVertices,r.val.1=0 → r.val.2≤w.val.2)) ∧
        ∃ P : actualZeroGraph.Walk (Sum.inl w) (Sum.inl z),P.IsPath ∧
          (∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → actualZeroGraph.degree r=2) ∧
          (∀ r,r∈P.support → r≠Sum.inl w → r≠Sum.inl z → ¬actualContactGraphOuterBoundary r) := by
    as_aux_lemma =>
      classical
      by_cases hex : ∃ w z : actualContactVertices,actualBottomReturnGraphPair w z
      · obtain ⟨w,z,hreturn,hclean⟩ := hActualFiniteContactGraphHasInnermostOriginalBottomReturn hBoundary hex
        obtain ⟨hw,hz,hwz,P,hP,hdegree,hproper⟩ := hreturn
        have hzw : z≠w := by
          intro he
          exact (ne_of_lt hwz) (congrArg (fun v : actualContactVertices => v.val.2) he).symm
        exact ⟨w,z,hzw,hw,Or.inl ⟨hz,hwz,hclean⟩,P,hP,hdegree,hproper⟩
      · obtain ⟨w,z,hzw,hw,hside,P,hP,hdegree,hproper⟩ :=
          hActualNoBottomReturnGraphHasAnExtremeSideContactPath hBoundary hbottom hex
        exact ⟨w,z,hzw,hw,Or.inr hside,P,hP,hdegree,hproper⟩

  have hActualSourcePhiStrictMono : StrictMono φ := by
    as_aux_lemma =>
      intro x y hxy
      change (φ x:ℝ)<(φ y:ℝ)
      rw [hφeq,hφeq]
      have hxy' : (x:ℝ)<(y:ℝ) := hxy
      nlinarith only [hxy',horder]
  have hActualOriginalCrossingRetainsItsSameBottomVertex
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (t : Interval)
      (ht : b.val.map t∈crossings M a b) :
      ∃ v : actualContactVertices,v.val.1=0 ∧ φ v.val.2=t := by
    as_aux_lemma =>
      obtain ⟨s,hs⟩ := hcapture t ht
      have hc : actualFiniteConeSweep (0,s)∈a.val.image := by
        rw [hFinalBottom,hs]
        exact ht.1.1
      have hv : (0,s)∈actualContactVertices := hBoundary (0,s) hc (Or.inl rfl)
      exact ⟨⟨(0,s),hv⟩,rfl,hs⟩
  have hActualAdjacentBottomReturnHasNoOriginalComparisonCrossingBetween
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hActualSourcePhiStrictMono : StrictMono φ)
      (w z : actualContactVertices) (hclean : ¬∃ v : actualContactVertices,
        v.val.1=0 ∧ w.val.2<v.val.2 ∧ v.val.2<z.val.2)
      (t : Interval) (ht : φ w.val.2<t ∧ t<φ z.val.2) :
      b.val.map t∉crossings M a b := by
    as_aux_lemma =>
      intro hcross
      obtain ⟨v,hv,hparameter⟩ := hActualOriginalCrossingRetainsItsSameBottomVertex hBoundary t hcross
      apply hclean
      refine ⟨v,hv,?_,?_⟩
      · exact hActualSourcePhiStrictMono.lt_iff_lt.mp (hparameter.symm ▸ ht.1)
      · exact hActualSourcePhiStrictMono.lt_iff_lt.mp (hparameter.symm ▸ ht.2)
  have hActualMinimumBottomContactHasNoOriginalPrefixCrossing
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hActualSourcePhiStrictMono : StrictMono φ)
      (w : actualContactVertices)
      (hmin : ∀ v : actualContactVertices,v.val.1=0 → w.val.2≤v.val.2)
      (t : Interval) (ht : t<φ w.val.2) : b.val.map t∉crossings M a b := by
    as_aux_lemma =>
      intro hcross
      obtain ⟨v,hv,hparameter⟩ := hActualOriginalCrossingRetainsItsSameBottomVertex hBoundary t hcross
      have hle := hActualSourcePhiStrictMono.monotone (hmin v hv)
      rw [hparameter] at hle
      exact (not_le_of_gt ht) hle
  have hActualMaximumBottomContactHasNoOriginalSuffixCrossing
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hActualSourcePhiStrictMono : StrictMono φ)
      (w : actualContactVertices)
      (hmax : ∀ v : actualContactVertices,v.val.1=0 → v.val.2≤w.val.2)
      (t : Interval) (ht : φ w.val.2<t) : b.val.map t∉crossings M a b := by
    as_aux_lemma =>
      intro hcross
      obtain ⟨v,hv,hparameter⟩ := hActualOriginalCrossingRetainsItsSameBottomVertex hBoundary t hcross
      have hle := hActualSourcePhiStrictMono.monotone (hmax v hv)
      rw [hparameter] at hle
      exact (not_le_of_gt ht) hle
  have hActualOriginalSidesExactIntersectionFromCleanComparisonInterior
      (f g : C(Interval,S)) (u v : S)
      (hfa : Set.range f⊆a.val.image)
      (hf0 : f 0=u) (hg0 : g 0=u) (hf1 : f 1=v) (hg1 : g 1=v)
      (hclean : ∀ t : Interval,0<(t:ℝ) → (t:ℝ)<1 → g t∉a.val.image) :
      Set.range f∩Set.range g={u,v} := by
    as_aux_lemma =>
      apply Set.Subset.antisymm
      · rintro x ⟨hxf,t,rfl⟩
        by_cases ht0 : t=0
        · subst t
          simp only [hg0,Set.mem_insert_iff,Set.mem_singleton_iff]
          exact Or.inl trivial
        by_cases ht1 : t=1
        · subst t
          simp only [hg1,Set.mem_insert_iff,Set.mem_singleton_iff]
          exact Or.inr trivial
        have htpos : 0<(t:ℝ) := lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
        have htlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
        exact False.elim (hclean t htpos htlt (hfa hxf))
      · intro x hx
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨⟨0,hf0⟩,⟨0,hg0⟩⟩
        · exact ⟨⟨1,hf1⟩,⟨1,hg1⟩⟩
  have hActualCleanBottomReturnClosesOriginalSubpathTarget
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hActualSourcePhiStrictMono : StrictMono φ)
      (w z : actualContactVertices) (hw : w.val.1=0) (hz : z.val.1=0) (hzw : z≠w)
      (horder : w.val.2<z.val.2)
      (hclean : ¬∃ v : actualContactVertices,v.val.1=0 ∧ w.val.2<v.val.2 ∧ v.val.2<z.val.2)
      (q : Path w.val z.val) (κ : C(Interval,Interval))
      (hκ : ∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t))
      (hinside : ∀ t,κ t∈Set.Ioo (0 : Interval) 1) :
    ∃ (f g : C(Interval,S)) (u v : S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0 = u ∧ g 0 = u ∧ f 1 = v ∧ g 1 = v ∧ u ≠ v ∧
      range f ∩ range g = {u,v} ∧
      v ∈ ArcSurgery.crossings M a b ∧
      (u ∈ ArcSurgery.crossings M a b ∨
        (u ∈ a.val.image ∩ b.val.image ∧ u ∈ (M.cover.branch : Set S))) ∧
      ∃ (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩),
        (∀ t : Interval, (α t : S) = f t) ∧
        (∀ t : Interval, (β t : S) = g t) ∧ α.Homotopic β := by
    as_aux_lemma =>
      let u := a.val.map (κ 0)
      let v := a.val.map (κ 1)
      obtain ⟨hFembed,hGembed⟩ := hActualOriginalBottomContactSubpathPairBothEmbedded w z hw hz hzw q κ hκ hinside
      obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ :=
        hActualOriginalBottomToBottomSubpathsPuncturedHomotopic u q hw hz κ hκ hinside
      let f : C(Interval,S) := ⟨fun t => (α t:S),by fun_prop⟩
      let g : C(Interval,S) := ⟨fun t => (β t:S),by fun_prop⟩
      have hF (t : Interval) : f t=a.val.map (actualIntervalSegment (κ 0) (κ 1) t) := hα t
      have hG (t : Interval) : g t=b.val.map (actualIntervalSegment (φ w.val.2) (φ z.val.2) t) := hβ t
      have hf : IsEmbedding f := by
        change IsEmbedding (fun t => f t)
        rw [show (fun t => f t)=(fun t => a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) from funext hF]
        exact hFembed
      have hg : IsEmbedding g := by
        change IsEmbedding (fun t => g t)
        rw [show (fun t => g t)=(fun t => b.val.map (actualIntervalSegment (φ w.val.2) (φ z.val.2) t)) from funext hG]
        exact hGembed
      have hfa : Set.range f⊆a.val.image := by
        rintro x ⟨t,rfl⟩
        rw [hF]
        exact mem_range_self _
      have hgb : Set.range g⊆b.val.image := by
        rintro x ⟨t,rfl⟩
        rw [hG]
        exact mem_range_self _
      have hf0 : f 0=u := congrArg Subtype.val α.source
      have hg0 : g 0=u := congrArg Subtype.val β.source
      have hf1 : f 1=v := congrArg Subtype.val α.target
      have hg1 : g 1=v := congrArg Subtype.val β.target
      have huv : u≠v := fun he => zero_ne_one (hf.injective (hf0.trans (he.trans hf1.symm)))
      have hcomparisonClean (t : Interval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) : g t∉a.val.image := by
        intro hcontact
        let θ := actualIntervalSegment (φ w.val.2) (φ z.val.2) t
        have hθ : φ w.val.2<θ ∧ θ<φ z.val.2 := by
          have hord : (φ w.val.2:ℝ)<(φ z.val.2:ℝ) := hActualSourcePhiStrictMono horder
          change (φ w.val.2:ℝ)<(1-(t:ℝ))*(φ w.val.2:ℝ)+(t:ℝ)*(φ z.val.2:ℝ) ∧
            (1-(t:ℝ))*(φ w.val.2:ℝ)+(t:ℝ)*(φ z.val.2:ℝ)<(φ z.val.2:ℝ)
          constructor <;> nlinarith only [hord,ht0,ht1]
        have hm : b.val.map θ∉(M.cover.branch : Set S) := by
          intro hm
          rcases b.val.marked_only_at_ends θ hm with h | h
          · have hpos : 0<(θ:ℝ) := lt_trans (hφbounds w.val.2).1 (show (φ w.val.2:ℝ)<(θ:ℝ) from hθ.1)
            exact (ne_of_gt hpos) (congrArg Subtype.val h)
          · have hlt : (θ:ℝ)<1 := lt_trans (show (θ:ℝ)<(φ z.val.2:ℝ) from hθ.2) (hφbounds z.val.2).2
            exact (ne_of_lt hlt) (congrArg Subtype.val h)
        exact hActualAdjacentBottomReturnHasNoOriginalComparisonCrossingBetween hBoundary
          hActualSourcePhiStrictMono w z hclean θ hθ ⟨⟨(hG t) ▸ hcontact,hm⟩,mem_range_self θ,hm⟩
      have hintersection := hActualOriginalSidesExactIntersectionFromCleanComparisonInterior f g u v hfa hf0 hg0 hf1 hg1 hcomparisonClean
      have hunmarked : u∉(M.cover.branch : Set S) := by
        intro hm
        rcases a.val.marked_only_at_ends (κ 0) hm with h | h
        · exact (ne_of_gt (hinside 0).1) h
        · exact (ne_of_lt (hinside 0).2) h
      have hvunmarked : v∉(M.cover.branch : Set S) := by
        intro hm
        rcases a.val.marked_only_at_ends (κ 1) hm with h | h
        · exact (ne_of_gt (hinside 1).1) h
        · exact (ne_of_lt (hinside 1).2) h
      have hucross : u∈crossings M a b := ⟨⟨hf0 ▸ hfa ⟨0,rfl⟩,hunmarked⟩,hg0 ▸ hgb ⟨0,rfl⟩,hunmarked⟩
      have hvcross : v∈crossings M a b := ⟨⟨hf1 ▸ hfa ⟨1,rfl⟩,hvunmarked⟩,hg1 ▸ hgb ⟨1,rfl⟩,hvunmarked⟩
      exact ⟨f,g,u,v,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,huv,hintersection,hvcross,Or.inl hucross,
        hu,hv,α,β,(fun _ => rfl),(fun _ => rfl),hhom⟩
  have hActualCleanExtremeSideClosesOriginalSubpathTarget
      (hBoundary : ∀ z : Interval × Interval,actualFiniteConeSweep z∈a.val.image →
        z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → z∈actualContactVertices)
      (hActualSourcePhiStrictMono : StrictMono φ)
      (w : actualContactVertices) (κ ρ : C(Interval,Interval))
      (hκzero : κ 0=0 ∨ κ 0=1)
      (hκpositive : ∀ t : Interval,0<(t:ℝ) → 0<(κ t:ℝ) ∧ (κ t:ℝ)<1)
      (hρend : ρ 1=φ w.val.2)
      (hside : (ρ 0=0 ∧ ∀ r : actualContactVertices,r.val.1=0 → w.val.2≤r.val.2) ∨
        (ρ 0=1 ∧ ∀ r : actualContactVertices,r.val.1=0 → r.val.2≤w.val.2))
      (hFembed : IsEmbedding (fun t => a.val.map (actualIntervalSegment (κ 0) (κ 1) t)))
      (hGembed : IsEmbedding (fun t => b.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)))
      (hpackage : ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
        (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{a.val.map 0})ᶜ)
          ⟨a.val.map (κ 1),hy⟩),
        (∀ t,(α t:S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        (∀ t,(β t:S)=b.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)) ∧ α.Homotopic β) :
    ∃ (f g : C(Interval,S)) (u v : S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0 = u ∧ g 0 = u ∧ f 1 = v ∧ g 1 = v ∧ u ≠ v ∧
      range f ∩ range g = {u,v} ∧
      v ∈ ArcSurgery.crossings M a b ∧
      (u ∈ ArcSurgery.crossings M a b ∨
        (u ∈ a.val.image ∩ b.val.image ∧ u ∈ (M.cover.branch : Set S))) ∧
      ∃ (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
        (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩),
        (∀ t : Interval, (α t : S) = f t) ∧
        (∀ t : Interval, (β t : S) = g t) ∧ α.Homotopic β := by
    as_aux_lemma =>
      have hbaseκ : a.val.map (κ 0)=a.val.map 0 := by
        rcases hκzero with h | h
        · rw [h]
        · rw [h,←ha]
      let u := a.val.map (κ 0)
      let v := a.val.map (κ 1)
      have hpackage' : ∃ (hx : a.val.map (κ 0)∈((M.cover.branch : Set S)\{u})ᶜ)
        (hy : a.val.map (κ 1)∈((M.cover.branch : Set S)\{u})ᶜ)
        (α β : Path (⟨a.val.map (κ 0),hx⟩ : ↑((M.cover.branch : Set S)\{u})ᶜ)
          ⟨a.val.map (κ 1),hy⟩),
        (∀ t,(α t:S)=a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) ∧
        (∀ t,(β t:S)=b.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)) ∧ α.Homotopic β := by
          have hcarrierEq : ((M.cover.branch : Set S)\{a.val.map 0})ᶜ=
              ((M.cover.branch : Set S)\{u})ᶜ := by
            change ((M.cover.branch : Set S)\{a.val.map 0})ᶜ=
              ((M.cover.branch : Set S)\{a.val.map (κ 0)})ᶜ
            rw [hbaseκ]
          rw [←hcarrierEq]
          exact hpackage
      obtain ⟨hu,hv,α,β,hα,hβ,hhom⟩ := hpackage'
      let f : C(Interval,S) := ⟨fun t => (α t:S),by fun_prop⟩
      let g : C(Interval,S) := ⟨fun t => (β t:S),by fun_prop⟩
      have hF (t : Interval) : f t=a.val.map (actualIntervalSegment (κ 0) (κ 1) t) := hα t
      have hG (t : Interval) : g t=b.val.map (actualIntervalSegment (ρ 0) (ρ 1) t) := hβ t
      have hf : IsEmbedding f := by
        change IsEmbedding (fun t => f t)
        rw [show (fun t => f t)=(fun t => a.val.map (actualIntervalSegment (κ 0) (κ 1) t)) from funext hF]
        exact hFembed
      have hg : IsEmbedding g := by
        change IsEmbedding (fun t => g t)
        rw [show (fun t => g t)=(fun t => b.val.map (actualIntervalSegment (ρ 0) (ρ 1) t)) from funext hG]
        exact hGembed
      have hfa : Set.range f⊆a.val.image := by
        rintro x ⟨t,rfl⟩
        rw [hF]
        exact mem_range_self _
      have hgb : Set.range g⊆b.val.image := by
        rintro x ⟨t,rfl⟩
        rw [hG]
        exact mem_range_self _
      have hf0 : f 0=u := congrArg Subtype.val α.source
      have hg0 : g 0=u := congrArg Subtype.val β.source
      have hf1 : f 1=v := congrArg Subtype.val α.target
      have hg1 : g 1=v := congrArg Subtype.val β.target
      have huv : u≠v := fun he => zero_ne_one (hf.injective (hf0.trans (he.trans hf1.symm)))
      have hcomparisonClean (t : Interval) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) : g t∉a.val.image := by
        intro hcontact
        let θ := actualIntervalSegment (ρ 0) (ρ 1) t
        have hθbounds : 0<(θ:ℝ) ∧ (θ:ℝ)<1 := by
          rcases hside with h | h
          · change 0<(1-(t:ℝ))*(ρ 0:ℝ)+(t:ℝ)*(ρ 1:ℝ) ∧
              (1-(t:ℝ))*(ρ 0:ℝ)+(t:ℝ)*(ρ 1:ℝ)<1
            rw [h.1,hρend]
            norm_num
            constructor <;> nlinarith only [ht0,ht1,(hφbounds w.val.2).1,(hφbounds w.val.2).2]
          · change 0<(1-(t:ℝ))*(ρ 0:ℝ)+(t:ℝ)*(ρ 1:ℝ) ∧
              (1-(t:ℝ))*(ρ 0:ℝ)+(t:ℝ)*(ρ 1:ℝ)<1
            rw [h.1,hρend]
            norm_num
            constructor <;> nlinarith only [ht0,ht1,(hφbounds w.val.2).1,(hφbounds w.val.2).2]
        have hm : b.val.map θ∉(M.cover.branch : Set S) := by
          intro hm
          rcases b.val.marked_only_at_ends θ hm with h | h
          · exact (ne_of_gt hθbounds.1) (congrArg Subtype.val h)
          · exact (ne_of_lt hθbounds.2) (congrArg Subtype.val h)
        have hcross : b.val.map θ∈crossings M a b := ⟨⟨(hG t) ▸ hcontact,hm⟩,mem_range_self θ,hm⟩
        rcases hside with h | h
        · apply hActualMinimumBottomContactHasNoOriginalPrefixCrossing hBoundary hActualSourcePhiStrictMono w h.2 θ _ hcross
          change (1-(t:ℝ))*(ρ 0:ℝ)+(t:ℝ)*(ρ 1:ℝ)<(φ w.val.2:ℝ)
          rw [h.1,hρend]
          norm_num
          nlinarith only [ht1,(hφbounds w.val.2).1]
        · apply hActualMaximumBottomContactHasNoOriginalSuffixCrossing hBoundary hActualSourcePhiStrictMono w h.2 θ _ hcross
          change (φ w.val.2:ℝ)<(1-(t:ℝ))*(ρ 0:ℝ)+(t:ℝ)*(ρ 1:ℝ)
          rw [h.1,hρend]
          norm_num
          nlinarith only [ht1,(hφbounds w.val.2).2]
      have hintersection := hActualOriginalSidesExactIntersectionFromCleanComparisonInterior f g u v hfa hf0 hg0 hf1 hg1 hcomparisonClean
      have humarked : u∈(M.cover.branch : Set S) := by
        change a.val.map (κ 0)∈(M.cover.branch : Set S)
        rw [hbaseκ]
        exact a.val.start_marked
      have hvunmarked : v∉(M.cover.branch : Set S) := by
        intro hm
        rcases a.val.marked_only_at_ends (κ 1) hm with h | h
        · exact (ne_of_gt (hκpositive 1 (by norm_num)).1) (congrArg Subtype.val h)
        · exact (ne_of_lt (hκpositive 1 (by norm_num)).2) (congrArg Subtype.val h)
      have hvcross : v∈crossings M a b := ⟨⟨hf1 ▸ hfa ⟨1,rfl⟩,hvunmarked⟩,hg1 ▸ hgb ⟨1,rfl⟩,hvunmarked⟩
      exact ⟨f,g,u,v,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,huv,hintersection,hvcross,
        Or.inr ⟨⟨hf0 ▸ hfa ⟨0,rfl⟩,hg0 ▸ hgb ⟨0,rfl⟩⟩,humarked⟩,
        hu,hv,α,β,(fun _ => rfl),(fun _ => rfl),hhom⟩
  have hActualOriginalPositiveParameterLiftUnique
      (d : EssentialMarkedArc M) (κ ρ : C(Interval,Interval))
      (hκ : ∀ t : Interval,0<(t:ℝ) → 0<(κ t:ℝ) ∧ (κ t:ℝ)<1)
      (heq : ∀ t,d.val.map (κ t)=d.val.map (ρ t)) : κ=ρ := by
    as_aux_lemma =>
      have hdense : Dense (Set.Ioi (0 : Interval)) := by
        rw [dense_iff_closure_eq,closure_Ioi' (show (Set.Ioi (0 : Interval)).Nonempty from ⟨1,by norm_num⟩)]
        ext t
        simp only [Set.mem_Ici,Set.mem_univ,iff_true]
        exact t.property.1
      apply ContinuousMap.coe_injective
      exact Continuous.ext_on hdense κ.continuous ρ.continuous (by
        intro t ht
        have ht' : 0<(t:ℝ) := ht
        rcases d.val.injective_except_loop_closure _ _ (heq t) with h | h | h
        · exact h
        · exact False.elim ((ne_of_gt (hκ t ht').1) (congrArg Subtype.val h.1))
        · exact False.elim ((ne_of_lt (hκ t ht').2) (congrArg Subtype.val h.1)))
  have hActualOriginalComparisonWordParameterEndpoints
      (d : EssentialMarkedArc M) (ρ : C(Interval,Interval))
      {l r : Interval} (δ : Path l r) (γ : C(Interval,S))
      (hρpositive : ∀ t : Interval,0<(t:ℝ) → 0<(ρ t:ℝ) ∧ (ρ t:ℝ)<1)
      (hρ : ∀ t,d.val.map (ρ t)=γ t)
      (hδ : ∀ t,d.val.map (δ t)=γ t) : ρ 0=l ∧ ρ 1=r := by
    as_aux_lemma =>
      have he := hActualOriginalPositiveParameterLiftUnique d ρ δ.toContinuousMap hρpositive
        (fun t => (hρ t).trans (hδ t).symm)
      constructor
      · exact (congrArg (fun f : C(Interval,Interval) => f 0) he).trans δ.source
      · exact (congrArg (fun f : C(Interval,Interval) => f 1) he).trans δ.target
  have hActualOriginalComparisonCommonBase : b.val.map 0=a.val.map 0 :=
    (hzero 0).symm.trans (hbase 0).1
  have hActualOriginalComparisonOtherBase : b.val.map 1=a.val.map 0 :=
    (hzero 1).symm.trans (hbase 0).2
  have hActualOriginalComparisonLoopClosure : b.val.map 0=b.val.map 1 :=
    hActualOriginalComparisonCommonBase.trans hActualOriginalComparisonOtherBase.symm
  have hActualSourceBottomContactNonempty : ∃ w : actualContactVertices,w.val.1=0 := by
    obtain ⟨w,hw,hB,hdegree⟩ := hActualSpecifiedOriginalCrossingProducesOddVertex
    exact ⟨w,hB⟩
  obtain ⟨selectedStart,selectedEnd,hEndDistinct,hStartBottom,hSelectedCleanChoice,
    actualSelectedFirstBoundaryGraphPath,hActualSelectedFirstBoundaryGraphPath,
    hActualSelectedFirstBoundaryGraphDegree,hActualSelectedFirstBoundaryGraphBoundary⟩ :=
    hActualFiniteSameSourceGraphProducesCleanOriginalContactPath
      (fun z hc hb => hBoundary z hc hb) hActualSourceBottomContactNonempty
  have hSelectedPartnerBoundary : selectedEnd.val.1=0 ∨ selectedEnd.val.2=0 ∨ selectedEnd.val.2=1 := by
    rcases hSelectedCleanChoice with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1)
  obtain ⟨actualSelectedFirstBoundaryPlanarLabels,hActualSelectedFirstBoundaryPlanarPath,
    hActualSelectedFirstBoundaryPlanarVertices,selectedContactPath,hSelectedEmbedding,
    hActualSelectedFirstBoundaryCarrierImage,hSelectedProper,
    originalParameterPath,hOriginalParameterIdentity,hOriginalParameterInterior⟩ :=
    hActualBoundaryProperGraphPathLiftsToProperOriginalContactPath
      (fun z hc hb => hBoundary z hc hb) hEndDistinct actualSelectedFirstBoundaryGraphPath
      hActualSelectedFirstBoundaryGraphPath hActualSelectedFirstBoundaryGraphBoundary
  -- The selected Q/W/q are one graph-first proper prefix of THIS actual source graph.
  -- Its internal graph degrees are two and its boundary vertices are only its endpoints.
  -- Source corner labels below are reconstructed at THIS selected endpoint in the retained movie.
  by_cases hEndBottom : selectedEnd.val.1=0
  · have hcornerClear (v : actualContactVertices) (hv : v.val.1=0) : v.val.2≠0 ∧ v.val.2≠1 := by
      constructor
      · intro hv0
        have he : v.val=(0,0) := Prod.ext hv hv0
        have hc : G (0,0)∈a.val.image := by
          rw [←hFinalBoundary (0,0) (Or.inl rfl)]
          exact he ▸ hActualContactVerticesImage v
        exact hcorner0 hc
      · intro hv1
        have he : v.val=(0,1) := Prod.ext hv hv1
        have hc : G (0,1)∈a.val.image := by
          rw [←hFinalBoundary (0,1) (Or.inl rfl)]
          exact he ▸ hActualContactVerticesImage v
        exact hcorner1 hc
    rcases hSelectedCleanChoice with h | h | h
    · exact hActualCleanBottomReturnClosesOriginalSubpathTarget
        (fun z hc hb => hBoundary z hc hb) hActualSourcePhiStrictMono
        selectedStart selectedEnd hStartBottom hEndBottom hEndDistinct h.2.1 h.2.2
        selectedContactPath originalParameterPath hOriginalParameterIdentity hOriginalParameterInterior
    · exact False.elim ((hcornerClear selectedEnd hEndBottom).1 h.1)
    · exact False.elim ((hcornerClear selectedEnd hEndBottom).2 h.1)
  · rcases hSelectedPartnerBoundary with hEndBottom' | hEndLeft | hEndRight
    · exact False.elim (hEndBottom hEndBottom')
    · have hActualLeftSideAgreement : G' selectedEnd.val=G selectedEnd.val :=
        hFinalBoundary selectedEnd.val (Or.inr (Or.inr (Or.inl hEndLeft)))
      have hPoint : selectedEnd.val=(selectedEnd.val.1,0) := Prod.ext rfl hEndLeft
      have hContact : G (selectedEnd.val.1,0)∈a.val.image := by
        rw [← hPoint,← hActualLeftSideAgreement]
        exact hActualContactVerticesImage selectedEnd
      obtain ⟨actualSelectedLeftLevel,hSelectedLeftPhase,hSelectedLeftEndpoint⟩ :=
        hSameSourceLeftBoundaryContact selectedEnd.val.1 hContact
      let actualCornerH := actualRawLeftCornerSquare actualSelectedLeftLevel
      have hCornerHBase := hRawLeftCornerBase actualSelectedLeftLevel
      have hCornerHOld := hRawLeftCornerOld actualSelectedLeftLevel
      have hActualMatchedCornerEndpoint : actualCornerH (1,1)=G' selectedEnd.val := by
        change F₀ actualSelectedLeftLevel (1,actualRawSourceQuarterParameter 1)=_
        rw [hRawQuarterOne,hSelectedLeftEndpoint,←hPoint]
        exact hActualLeftSideAgreement.symm
      let actualMatchedCornerPhasePath : Path ((0 : Interval),(0 : Interval)) selectedEnd.val := {
        toFun := fun t => (time₀ actualSelectedLeftLevel (t,phaseQuarter),0)
        continuous_toFun := by fun_prop
        source' := by
          apply Prod.ext
          · apply Subtype.ext
            rw [htime₀]
            norm_num
          · rfl
        target' := by
          apply Prod.ext
          · apply Subtype.ext
            rw [htime₀,hSelectedLeftPhase]
            norm_num
          · exact hEndLeft.symm }
      let actualMatchedCornerInitialPath : Path ((0 : Interval),(0 : Interval)) selectedStart.val := {
        toFun := fun t => (0,actualIntervalSegment 0 selectedStart.val.2 t)
        continuous_toFun := by fun_prop
        source' := by
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            norm_num [actualIntervalSegment]
        target' := by
          apply Prod.ext
          · exact hStartBottom.symm
          · apply Subtype.ext
            norm_num [actualIntervalSegment] }
      have hActualRawCornerPhaseMatchesSameFinalMovie (t : Interval) :
          actualCornerH (t,1)=G' (actualMatchedCornerPhasePath t) := by
        rw [hRawLeftCornerRightLiteral]
        exact (hFinalBoundary _ (Or.inr (Or.inr (Or.inl rfl)))).symm
      obtain ⟨hActualRaw00,hActualRaw01,hActualRaw11,hActualSelectedStartCarrier,
        actualRawComparisonPrefix,actualRawOldTerminalSide,actualRawReverseContactSide,
        actualRawInitialBoundaryReturn,hRawComparisonPrefixLiteral,hRawOldTerminalLiteral,
        hRawReverseContactLiteral,hRawInitialBoundaryReturnLiteral,hActualRawCornerAndContactPastedWord⟩ :=
        hActualRawCornerWordPastesWithSameSourceSquare actualCornerH G' hCornerHBase
          (hRawLeftCornerCarrier actualSelectedLeftLevel) hActualFiniteConeSweepMarks
          actualMatchedCornerPhasePath selectedContactPath actualMatchedCornerInitialPath
          hActualRawCornerPhaseMatchesSameFinalMovie
      have hActualPastedOldWordContact (t : Interval) :
          ((actualRawOldTerminalSide.trans actualRawReverseContactSide) t:S)∈a.val.image := by
        rw [Path.trans_apply]
        split_ifs with ht
        · rw [hRawOldTerminalLiteral]
          exact hCornerHOld _
        · rw [hRawReverseContactLiteral]
          change actualFiniteConeSweep (selectedContactPath _)∈a.val.image
          rw [←hOriginalParameterIdentity]
          exact mem_range_self _
      have hActualPastedComparisonWordContact (t : Interval) :
          ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S)∈b.val.image := by
        rw [Path.trans_apply]
        split_ifs with ht
        · rw [hRawComparisonPrefixLiteral,hRawLeftInitialOriginalComparisonLiteral]
          exact mem_range_self _
        · rw [hRawInitialBoundaryReturnLiteral]
          change G' (0,actualIntervalSegment 0 selectedStart.val.2 _)∈b.val.image
          rw [hFinalBottom]
          exact mem_range_self _
      have hActualPastedOldWordPositiveMarks (t : Interval) (ht : 0<(t:ℝ)) :
          ((actualRawOldTerminalSide.trans actualRawReverseContactSide) t:S)∉(M.cover.branch : Set S) := by
        rw [Path.trans_apply]
        split_ifs with hh
        · rw [hRawOldTerminalLiteral]
          exact hRawLeftCornerPositiveMarks actualSelectedLeftLevel _ (by change 0<2*(t:ℝ); positivity)
        · rw [hRawReverseContactLiteral]
          exact hActualFiniteConeSweepMarks _
      have hActualPastedComparisonWordPositiveMarks (t : Interval) (ht : 0<(t:ℝ)) :
          ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S)∉(M.cover.branch : Set S) := by
        rw [Path.trans_apply]
        split_ifs with hh
        · rw [hRawComparisonPrefixLiteral]
          change F₀ actualSelectedLeftLevel (0,actualRawSourceQuarterParameter _)∉(M.cover.branch : Set S)
          exact hFmarks₀ actualSelectedLeftLevel 0 _ (by change 0<(2*(t:ℝ))/4; positivity)
        · rw [hRawInitialBoundaryReturnLiteral]
          exact hActualFiniteConeSweepMarks _
      obtain ⟨actualOriginalOldParameters,actualOriginalComparisonParameters,
        hActualOriginalOldWordCoordinates,hActualOriginalComparisonWordCoordinates,
        hActualOldOriginalStartEndpointChoice,hActualComparisonOriginalStartEndpointChoice,
        hActualOldPositiveParameters,hActualComparisonPositiveParameters,
        hActualOriginalOldEmbedding,hActualOriginalComparisonEmbedding,
        hActualOriginalPairSourceCarrier,hActualOriginalPairTargetCarrier,
        actualOriginalOldSubpath,actualOriginalComparisonSubpath,
        hActualOriginalOldSubpathLiteral,hActualOriginalComparisonSubpathLiteral,
        hActualOriginalSameSourcePuncturedSubpathHomotopy⟩ :=
        hActualTwoOriginalMarkedBaseWordsStraightenKeepingHomotopy a b ha
          hActualOriginalComparisonLoopClosure hActualOriginalComparisonCommonBase
          (actualRawOldTerminalSide.trans actualRawReverseContactSide)
          (actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn)
          hActualRawCornerAndContactPastedWord (hCornerHBase 0)
          hActualPastedOldWordContact hActualPastedComparisonWordContact
          hActualPastedOldWordPositiveMarks hActualPastedComparisonWordPositiveMarks
      let actualOriginalComparisonPrefixParameters : Path (0 : Interval) (φ 0) := {
        toFun := actualRawLeftOriginalComparisonParameter
        continuous_toFun := actualRawLeftOriginalComparisonParameter.continuous
        source' := hRawLeftComparisonSource
        target' := hRawLeftComparisonTarget }
      let actualOriginalComparisonReturnParameters : Path (φ (0 : Interval)) (φ selectedStart.val.2) := {
        toFun := fun t => φ (actualIntervalSegment 0 selectedStart.val.2 t)
        continuous_toFun := by fun_prop
        source' := by
          have he : actualIntervalSegment 0 selectedStart.val.2 0=0 := by
            apply Subtype.ext
            norm_num [actualIntervalSegment]
          rw [he]
        target' := by
          have he : actualIntervalSegment 0 selectedStart.val.2 1=selectedStart.val.2 := by
            apply Subtype.ext
            norm_num [actualIntervalSegment]
          rw [he] }
      let actualOriginalComparisonWordParameters :=
        actualOriginalComparisonPrefixParameters.trans actualOriginalComparisonReturnParameters
      have hActualComparisonWordParameterCoordinates (t : Interval) :
          b.val.map (actualOriginalComparisonWordParameters t)=
            ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S) := by
        rw [Path.trans_apply,Path.trans_apply]
        split_ifs with ht
        · change b.val.map (actualRawLeftOriginalComparisonParameter _)=_
          rw [hRawComparisonPrefixLiteral,hRawLeftInitialOriginalComparisonLiteral]
        · change b.val.map (φ (actualIntervalSegment 0 selectedStart.val.2 _))=_
          rw [hRawInitialBoundaryReturnLiteral]
          change _=G' (0,actualIntervalSegment 0 selectedStart.val.2 _)
          rw [hFinalBottom]
      obtain ⟨hActualComparisonOriginalStartLiteral,hActualComparisonOriginalEndLiteral⟩ :=
        hActualOriginalComparisonWordParameterEndpoints b actualOriginalComparisonParameters
          actualOriginalComparisonWordParameters
          ⟨fun t => ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S),by fun_prop⟩
          hActualComparisonPositiveParameters hActualOriginalComparisonWordCoordinates
          hActualComparisonWordParameterCoordinates
      have hActualSelectedMinimumBottomContact : ∀ r : actualContactVertices,
          r.val.1=0 → selectedStart.val.2≤r.val.2 := by
        rcases hSelectedCleanChoice with h | h | h
        · exact False.elim (hEndBottom h.1)
        · exact h.2
        · exact False.elim (zero_ne_one (hEndLeft.symm.trans h.1))
      exact hActualCleanExtremeSideClosesOriginalSubpathTarget
        (fun z hc hb => hBoundary z hc hb) hActualSourcePhiStrictMono selectedStart
        actualOriginalOldParameters actualOriginalComparisonParameters
        hActualOldOriginalStartEndpointChoice hActualOldPositiveParameters
        hActualComparisonOriginalEndLiteral (Or.inl ⟨hActualComparisonOriginalStartLiteral,hActualSelectedMinimumBottomContact⟩)
        hActualOriginalOldEmbedding hActualOriginalComparisonEmbedding
        ⟨hActualOriginalPairSourceCarrier,hActualOriginalPairTargetCarrier,
          actualOriginalOldSubpath,actualOriginalComparisonSubpath,
          hActualOriginalOldSubpathLiteral,hActualOriginalComparisonSubpathLiteral,
          hActualOriginalSameSourcePuncturedSubpathHomotopy⟩
    · have hActualRightSideAgreement : G' selectedEnd.val=G selectedEnd.val :=
        hFinalBoundary selectedEnd.val (Or.inr (Or.inr (Or.inr hEndRight)))
      have hPoint : selectedEnd.val=(selectedEnd.val.1,1) := Prod.ext rfl hEndRight
      have hContact : G (selectedEnd.val.1,1)∈a.val.image := by
        rw [← hPoint,← hActualRightSideAgreement]
        exact hActualContactVerticesImage selectedEnd
      obtain ⟨actualSelectedRightLevel,hSelectedRightPhase,hSelectedRightEndpoint⟩ :=
        hSameSourceRightBoundaryContact selectedEnd.val.1 hContact
      let actualCornerH := actualRawRightCornerSquare actualSelectedRightLevel
      have hCornerHBase := hRawRightCornerBase actualSelectedRightLevel
      have hCornerHOld := hRawRightCornerOld actualSelectedRightLevel
      have hActualMatchedCornerEndpoint : actualCornerH (1,1)=G' selectedEnd.val := by
        change F₁ actualSelectedRightLevel (1,actualRawSourceQuarterParameter 1)=_
        rw [hRawQuarterOne,hSelectedRightEndpoint,←hPoint]
        exact hActualRightSideAgreement.symm
      let actualMatchedCornerPhasePath : Path ((0 : Interval),(1 : Interval)) selectedEnd.val := {
        toFun := fun t => (time₁ actualSelectedRightLevel (t,phaseQuarter),1)
        continuous_toFun := by fun_prop
        source' := by
          apply Prod.ext
          · apply Subtype.ext
            rw [htime₁]
            norm_num
          · rfl
        target' := by
          apply Prod.ext
          · apply Subtype.ext
            rw [htime₁,hSelectedRightPhase]
            norm_num
          · exact hEndRight.symm }
      let actualMatchedCornerInitialPath : Path ((0 : Interval),(1 : Interval)) selectedStart.val := {
        toFun := fun t => (0,actualIntervalSegment 1 selectedStart.val.2 t)
        continuous_toFun := by fun_prop
        source' := by
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            norm_num [actualIntervalSegment]
        target' := by
          apply Prod.ext
          · exact hStartBottom.symm
          · apply Subtype.ext
            norm_num [actualIntervalSegment] }
      have hActualRawCornerPhaseMatchesSameFinalMovie (t : Interval) :
          actualCornerH (t,1)=G' (actualMatchedCornerPhasePath t) := by
        rw [hRawRightCornerRightLiteral]
        exact (hFinalBoundary _ (Or.inr (Or.inr (Or.inr rfl)))).symm
      obtain ⟨hActualRaw00,hActualRaw01,hActualRaw11,hActualSelectedStartCarrier,
        actualRawComparisonPrefix,actualRawOldTerminalSide,actualRawReverseContactSide,
        actualRawInitialBoundaryReturn,hRawComparisonPrefixLiteral,hRawOldTerminalLiteral,
        hRawReverseContactLiteral,hRawInitialBoundaryReturnLiteral,hActualRawCornerAndContactPastedWord⟩ :=
        hActualRawCornerWordPastesWithSameSourceSquare actualCornerH G' hCornerHBase
          (hRawRightCornerCarrier actualSelectedRightLevel) hActualFiniteConeSweepMarks
          actualMatchedCornerPhasePath selectedContactPath actualMatchedCornerInitialPath
          hActualRawCornerPhaseMatchesSameFinalMovie
      have hActualPastedOldWordContact (t : Interval) :
          ((actualRawOldTerminalSide.trans actualRawReverseContactSide) t:S)∈a.val.image := by
        rw [Path.trans_apply]
        split_ifs with ht
        · rw [hRawOldTerminalLiteral]
          exact hCornerHOld _
        · rw [hRawReverseContactLiteral]
          change actualFiniteConeSweep (selectedContactPath _)∈a.val.image
          rw [←hOriginalParameterIdentity]
          exact mem_range_self _
      have hActualPastedComparisonWordContact (t : Interval) :
          ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S)∈b.val.image := by
        rw [Path.trans_apply]
        split_ifs with ht
        · rw [hRawComparisonPrefixLiteral,hRawRightInitialOriginalComparisonLiteral]
          exact mem_range_self _
        · rw [hRawInitialBoundaryReturnLiteral]
          change G' (0,actualIntervalSegment 1 selectedStart.val.2 _)∈b.val.image
          rw [hFinalBottom]
          exact mem_range_self _
      have hActualPastedOldWordPositiveMarks (t : Interval) (ht : 0<(t:ℝ)) :
          ((actualRawOldTerminalSide.trans actualRawReverseContactSide) t:S)∉(M.cover.branch : Set S) := by
        rw [Path.trans_apply]
        split_ifs with hh
        · rw [hRawOldTerminalLiteral]
          exact hRawRightCornerPositiveMarks actualSelectedRightLevel _ (by change 0<2*(t:ℝ); positivity)
        · rw [hRawReverseContactLiteral]
          exact hActualFiniteConeSweepMarks _
      have hActualPastedComparisonWordPositiveMarks (t : Interval) (ht : 0<(t:ℝ)) :
          ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S)∉(M.cover.branch : Set S) := by
        rw [Path.trans_apply]
        split_ifs with hh
        · rw [hRawComparisonPrefixLiteral]
          change F₁ actualSelectedRightLevel (0,actualRawSourceQuarterParameter _)∉(M.cover.branch : Set S)
          exact hFmarks₁ actualSelectedRightLevel 0 _ (by change 0<(2*(t:ℝ))/4; positivity)
        · rw [hRawInitialBoundaryReturnLiteral]
          exact hActualFiniteConeSweepMarks _
      obtain ⟨actualOriginalOldParameters,actualOriginalComparisonParameters,
        hActualOriginalOldWordCoordinates,hActualOriginalComparisonWordCoordinates,
        hActualOldOriginalStartEndpointChoice,hActualComparisonOriginalStartEndpointChoice,
        hActualOldPositiveParameters,hActualComparisonPositiveParameters,
        hActualOriginalOldEmbedding,hActualOriginalComparisonEmbedding,
        hActualOriginalPairSourceCarrier,hActualOriginalPairTargetCarrier,
        actualOriginalOldSubpath,actualOriginalComparisonSubpath,
        hActualOriginalOldSubpathLiteral,hActualOriginalComparisonSubpathLiteral,
        hActualOriginalSameSourcePuncturedSubpathHomotopy⟩ :=
        hActualTwoOriginalMarkedBaseWordsStraightenKeepingHomotopy a b ha
          hActualOriginalComparisonLoopClosure hActualOriginalComparisonCommonBase
          (actualRawOldTerminalSide.trans actualRawReverseContactSide)
          (actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn)
          hActualRawCornerAndContactPastedWord (hCornerHBase 0)
          hActualPastedOldWordContact hActualPastedComparisonWordContact
          hActualPastedOldWordPositiveMarks hActualPastedComparisonWordPositiveMarks
      let actualOriginalComparisonPrefixParameters : Path (1 : Interval) (φ 1) := {
        toFun := actualRawRightOriginalComparisonParameter
        continuous_toFun := actualRawRightOriginalComparisonParameter.continuous
        source' := hRawRightComparisonSource
        target' := hRawRightComparisonTarget }
      let actualOriginalComparisonReturnParameters : Path (φ (1 : Interval)) (φ selectedStart.val.2) := {
        toFun := fun t => φ (actualIntervalSegment 1 selectedStart.val.2 t)
        continuous_toFun := by fun_prop
        source' := by
          have he : actualIntervalSegment 1 selectedStart.val.2 0=1 := by
            apply Subtype.ext
            norm_num [actualIntervalSegment]
          rw [he]
        target' := by
          have he : actualIntervalSegment 1 selectedStart.val.2 1=selectedStart.val.2 := by
            apply Subtype.ext
            norm_num [actualIntervalSegment]
          rw [he] }
      let actualOriginalComparisonWordParameters :=
        actualOriginalComparisonPrefixParameters.trans actualOriginalComparisonReturnParameters
      have hActualComparisonWordParameterCoordinates (t : Interval) :
          b.val.map (actualOriginalComparisonWordParameters t)=
            ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S) := by
        rw [Path.trans_apply,Path.trans_apply]
        split_ifs with ht
        · change b.val.map (actualRawRightOriginalComparisonParameter _)=_
          rw [hRawComparisonPrefixLiteral,hRawRightInitialOriginalComparisonLiteral]
        · change b.val.map (φ (actualIntervalSegment 1 selectedStart.val.2 _))=_
          rw [hRawInitialBoundaryReturnLiteral]
          change _=G' (0,actualIntervalSegment 1 selectedStart.val.2 _)
          rw [hFinalBottom]
      obtain ⟨hActualComparisonOriginalStartLiteral,hActualComparisonOriginalEndLiteral⟩ :=
        hActualOriginalComparisonWordParameterEndpoints b actualOriginalComparisonParameters
          actualOriginalComparisonWordParameters
          ⟨fun t => ((actualRawComparisonPrefix.trans actualRawInitialBoundaryReturn) t:S),by fun_prop⟩
          hActualComparisonPositiveParameters hActualOriginalComparisonWordCoordinates
          hActualComparisonWordParameterCoordinates
      have hActualSelectedMaximumBottomContact : ∀ r : actualContactVertices,
          r.val.1=0 → r.val.2 ≤ selectedStart.val.2 := by
        rcases hSelectedCleanChoice with h | h | h
        · exact False.elim (hEndBottom h.1)
        · exact False.elim (zero_ne_one (h.1.symm.trans hEndRight))
        · exact h.2
      exact hActualCleanExtremeSideClosesOriginalSubpathTarget
        (fun z hc hb => hBoundary z hc hb) hActualSourcePhiStrictMono selectedStart
        actualOriginalOldParameters actualOriginalComparisonParameters
        hActualOldOriginalStartEndpointChoice hActualOldPositiveParameters
        hActualComparisonOriginalEndLiteral (Or.inr ⟨hActualComparisonOriginalStartLiteral,hActualSelectedMaximumBottomContact⟩)
        hActualOriginalOldEmbedding hActualOriginalComparisonEmbedding
        ⟨hActualOriginalPairSourceCarrier,hActualOriginalPairTargetCarrier,
          actualOriginalOldSubpath,actualOriginalComparisonSubpath,
          hActualOriginalOldSubpathLiteral,hActualOriginalComparisonSubpathLiteral,
          hActualOriginalSameSourcePuncturedSubpathHomotopy⟩
end CurveComplex.HyperellipticModel

