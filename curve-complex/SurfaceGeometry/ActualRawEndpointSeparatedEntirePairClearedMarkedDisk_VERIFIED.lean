import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkFreeMovieExactContactCore
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
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSurfaceEndpointCap
import Schoenflies.BoundaryContinuity2
import Schoenflies.FaceCyclesProof
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1ArbitraryCrosscutAlternationPROVED
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassLoopPreparedMovieCornerBoundaryScaffold
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorInteriorCoordinates
import CurveComplexGenusTwo.Filtration.Geometry.ActualPuncturedJordanConversion
import CurveComplexGenusTwo.Dictionary.JordanDiscHelper
import RawClearanceAligned_RelativeBigonSelfIntrusionSubdisk
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialMarkedDiskCrosscut
import CurveComplexGenusTwo.Topology.IntersectionParity.CurveImageInclusion
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies Metric ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096
noncomputable local instance (M : HyperellipticModel E S) : DecidableEq (EssentialArcClass M) := Classical.decEq _
private theorem actualRawCompatiblePairRepresentatives
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b}) :
    ∃ a₀ b₀ : EssentialMarkedArc M,
      Quotient.mk (essentialArcSetoid M) a₀ = ArcSurgery.vertex M a ∧
      Quotient.mk (essentialArcSetoid M) b₀ = ArcSurgery.vertex M b ∧
      MarkedIsotopyRel M a.val.image a₀.val.image ∧
      MarkedIsotopyRel M b.val.image b₀.val.image ∧
      Disjoint (arcInterior M a₀) (arcInterior M b₀) := by
  classical
  obtain ⟨r,hr,hd⟩ := hc
  let va : {v // v ∈ ({ArcSurgery.vertex M a, ArcSurgery.vertex M b} : Finset _)} :=
    ⟨ArcSurgery.vertex M a, by simp⟩
  let vb : {v // v ∈ ({ArcSurgery.vertex M a, ArcSurgery.vertex M b} : Finset _)} :=
    ⟨ArcSurgery.vertex M b, by simp⟩
  have hab : va ≠ vb := fun h => hne (congrArg Subtype.val h)
  refine ⟨r va,r vb,hr va,hr vb,?_,?_,hd va vb hab⟩
  · exact Quotient.exact (hr va).symm
  · exact Quotient.exact (hr vb).symm
private theorem actualRawCompatibleFixedArcCompetitor
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b}) :
    ∃ c : EssentialMarkedArc M,
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      Disjoint (arcInterior M a) (arcInterior M c) := by
  obtain ⟨α,β,hα,hβ,_,_,hd⟩ := actualRawCompatiblePairRepresentatives M a b hne hc
  obtain ⟨H,hmarks,himage⟩ := Quotient.exact hα
  obtain ⟨g,hg⟩ := H.homeomorphism_at 1
  have hfix : ∀ p,p ∈ M.cover.branch → g p = p := fun p hp =>
    (hg p).trans (hmarks 1 p hp)
  let c := β.transport g hfix
  have hc : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) β := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    change H.finalMap '' β.val.image = (β.val.transport g hfix).image
    rw [MarkedArc.transport_image]
    congr 1
    exact funext (fun p => (hg p).symm)
  have hαimage : (α.transport g hfix).val.image = a.val.image := by
    change (α.val.transport g hfix).image = a.val.image
    rw [MarkedArc.transport_image]
    change g '' α.val.image = a.val.image
    have hmap : g = H.finalMap := funext hg
    rw [hmap]
    exact himage
  have hαinterior : arcInterior M (α.transport g hfix) = arcInterior M a := by
    change (α.transport g hfix).val.image \ (M.cover.branch : Set S) = _
    rw [hαimage]
    rfl
  have hd' := arcInterior_transport_disjoint α β g hfix hd
  rw [hαinterior] at hd'
  exact ⟨c,hc.trans hβ,hd'⟩


private theorem actualRawCompatibleLoopInclusiveSweep
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b}) :
    ∃ F : C(Interval × Interval,S),
      (∀ t, F (0,t) = b.val.map t) ∧
      (∀ τ t u, F (τ,t) = F (τ,u) →
        t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0)) ∧
      (∀ τ, F (τ,0) = b.val.map 0 ∧ F (τ,1) = b.val.map 1) ∧
      (∀ τ t, t ≠ 0 → t ≠ 1 → F (τ,t) ∉ (M.cover.branch : Set S)) ∧
      (∀ t, t ≠ 0 → t ≠ 1 → F (1,t) ∉ arcInterior M a) := by
  classical
  obtain ⟨c,hc,hdis⟩ := actualRawCompatibleFixedArcCompetitor M a b hne hc
  obtain ⟨H,hmarks,himage⟩ := (markedIsotopy_equivalence M).symm (Quotient.exact hc)
  let F : C(Interval × Interval,S) :=
    ⟨fun z => H.map (z.1,b.val.map z.2),
      H.map.continuous.comp (continuous_fst.prodMk (b.val.continuous.comp continuous_snd))⟩
  have hnotmark (τ t : Interval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
      F (τ,t) ∉ (M.cover.branch : Set S) := by
    intro hm
    obtain ⟨g,hg⟩ := H.homeomorphism_at τ
    have hfix : g (F (τ,t)) = F (τ,t) := (hg _).trans (hmarks τ _ hm)
    have hsame : b.val.map t = F (τ,t) :=
      g.injective ((hg (b.val.map t)).trans hfix.symm)
    have hbmark : b.val.map t ∈ M.cover.branch := hsame.symm ▸ hm
    exact (b.val.marked_only_at_ends t hbmark).elim ht0 ht1
  refine ⟨F,?_,?_,?_,hnotmark,?_⟩
  · intro t
    exact H.at_zero _
  · intro τ t u he
    obtain ⟨g,hg⟩ := H.homeomorphism_at τ
    exact b.val.injective_except_loop_closure t u
      (g.injective ((hg _).trans (he.trans (hg _).symm)))
  · intro τ
    exact ⟨hmarks τ _ b.val.start_marked,hmarks τ _ b.val.end_marked⟩
  · intro t ht0 ht1 hpa
    have hpc : F (1,t) ∈ c.val.image := by
      rw [← himage]
      exact ⟨b.val.map t,⟨t,rfl⟩,rfl⟩
    exact disjoint_left.mp hdis hpa ⟨hpc,hnotmark 1 t ht0 ht1⟩

private theorem actualRawCompatibleFiniteCentralSweep
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b})
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (hcontact : (ArcSurgery.crossings M a b).Nonempty) :
    ∃ ε : ℝ, 0<ε ∧ ε<1/2 ∧
    ∃ φ : C(Interval,Interval), Function.Injective φ ∧
      (∀ t, ε<(φ t:ℝ) ∧ (φ t:ℝ)<1-ε) ∧
    ∃ G : C(Interval × Interval,S),
      (∀ t, G (0,t)=b.val.map (φ t)) ∧
      (∀ τ, Function.Injective (fun t => G (τ,t))) ∧
      (∀ z, G z ∉ (M.cover.branch : Set S)) ∧
      (∀ t, G (1,t) ∉ a.val.image) ∧
      (ArcSurgery.crossings M a b ⊆ range (fun t => G (0,t))) ∧
      {t : Interval | G (0,t) ∈ a.val.image}.Finite := by
  classical
  obtain ⟨F,hzero,hcollision,hends,hmarks,htop⟩ :=
    actualRawCompatibleLoopInclusiveSweep M a b hne hc
  let K : Set Interval := {t | b.val.map t ∈ ArcSurgery.crossings M a b}
  have hKfinite : K.Finite := hfinite.preimage (by
    intro t ht s hs he
    rcases b.val.injective_except_loop_closure t s he with he | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact he
    · exact False.elim (ht.2.2 b.val.start_marked)
    · exact False.elim (ht.2.2 b.val.end_marked))
  have hKnonempty : K.Nonempty := by
    obtain ⟨p,hp⟩ := hcontact
    obtain ⟨t,ht⟩ := hp.2.1
    refine ⟨t,?_⟩
    change b.val.map t ∈ ArcSurgery.crossings M a b
    rw [ht]
    exact hp
  obtain ⟨l,hl,hlmin⟩ := hKfinite.isCompact.exists_isLeast hKnonempty
  obtain ⟨u,hu,humax⟩ := hKfinite.isCompact.exists_isGreatest hKnonempty
  have hlpos : (0:ℝ)<(l:ℝ) := by
    apply lt_of_le_of_ne l.property.1
    intro h
    have he : l=(0:Interval) := Subtype.ext h.symm
    exact hl.2.2 (he ▸ b.val.start_marked)
  have hult : (u:ℝ)<(1:ℝ) := by
    apply lt_of_le_of_ne u.property.2
    intro h
    have he : u=(1:Interval) := Subtype.ext h
    exact hu.2.2 (he ▸ b.val.end_marked)
  let δ : ℝ := min (l:ℝ) (1-(u:ℝ))/2
  have hδpos : 0<δ := by dsimp [δ]; positivity
  have hδhalf : δ<1/2 := by
    have hlo : (l:ℝ)≤u := hlmin hu
    have h₁ := min_le_left (l:ℝ) (1-(u:ℝ))
    have h₂ := min_le_right (l:ℝ) (1-(u:ℝ))
    dsimp [δ]; linarith
  have hcontactwindow (t : Interval) (ht : t∈K) : δ<(t:ℝ) ∧ (t:ℝ)<1-δ := by
    have hlo : (l:ℝ)≤t := hlmin ht
    have hhi : (t:ℝ)≤u := humax ht
    have h₁ := min_le_left (l:ℝ) (1-(u:ℝ))
    have h₂ := min_le_right (l:ℝ) (1-(u:ℝ))
    dsimp [δ]; constructor <;> linarith
  let φ : C(Interval,Interval) := {
    toFun := fun t => ⟨δ+(1-2*δ)*(t:ℝ),by
      have ht0 := t.property.1
      have ht1 := t.property.2
      constructor <;> nlinarith⟩
    continuous_toFun := by fun_prop }
  have hφval (t : Interval) : (φ t:ℝ)=δ+(1-2*δ)*(t:ℝ) := rfl
  have hφinj : Function.Injective φ := by
    intro t s he
    have hh := congrArg Subtype.val he
    rw [hφval,hφval] at hh
    apply Subtype.ext
    nlinarith [hδhalf]
  have hφbounds (t : Interval) : 0<(φ t:ℝ) ∧ (φ t:ℝ)<1 := by
    rw [hφval]
    have ht0 := t.property.1
    have ht1 := t.property.2
    constructor <;> nlinarith
  have hφsurj (t : Interval) (ht : t∈K) : ∃ s : Interval,φ s=t := by
    obtain ⟨hlo,hhi⟩ := hcontactwindow t ht
    have hden : 0<1-2*δ := by linarith
    let s : Interval := ⟨((t:ℝ)-δ)/(1-2*δ),by
      constructor
      · exact (div_nonneg (by linarith) hden.le)
      · apply (div_le_one hden).mpr
        linarith⟩
    refine ⟨s,Subtype.ext ?_⟩
    rw [hφval]
    change δ+(1-2*δ)*(((t:ℝ)-δ)/(1-2*δ))=(t:ℝ)
    rw [mul_div_cancel₀ _ (ne_of_gt hden)]
    ring
  let G : C(Interval × Interval,S) :=
    F.comp ⟨fun z => (z.1,φ z.2),continuous_fst.prodMk (φ.continuous.comp continuous_snd)⟩
  have hGmarks (z : Interval × Interval) : G z ∉ (M.cover.branch : Set S) := by
    apply hmarks z.1 (φ z.2)
    · intro he
      have hh := congrArg Subtype.val he
      exact (hφbounds z.2).1.ne' hh
    · intro he
      have hh := congrArg Subtype.val he
      exact (hφbounds z.2).2.ne hh
  have hGzero (t : Interval) : G (0,t)=b.val.map (φ t) := hzero (φ t)
  refine ⟨δ/2,by positivity,by linarith,φ,hφinj,?_,G,hGzero,?_,hGmarks,?_,?_,?_⟩
  · intro t
    rw [hφval]
    have ht0 := t.property.1
    have ht1 := t.property.2
    constructor <;> nlinarith
  · intro τ t s he
    rcases hcollision τ (φ t) (φ s) he with hh | ⟨hh,_⟩ | ⟨hh,_⟩
    · exact hφinj hh
    · have h := congrArg Subtype.val hh
      exact False.elim ((hφbounds t).1.ne' h)
    · have h := congrArg Subtype.val hh
      exact False.elim ((hφbounds t).2.ne h)
  · intro t ha
    apply htop (φ t)
    · intro he
      exact (hφbounds t).1.ne' (congrArg Subtype.val he)
    · intro he
      exact (hφbounds t).2.ne (congrArg Subtype.val he)
    · exact ⟨ha,hGmarks (1,t)⟩
  · intro p hp
    obtain ⟨t,ht⟩ := hp.2.1
    have htK : t∈K := by
      change b.val.map t ∈ ArcSurgery.crossings M a b
      rw [ht]
      exact hp
    obtain ⟨s,hs⟩ := hφsurj t htK
    exact ⟨s,(hGzero s).trans (congrArg b.val.map hs |>.trans ht)⟩
  · apply (hKfinite.preimage hφinj.injOn).subset
    intro t ht
    change φ t ∈ K
    exact ⟨⟨hGzero t ▸ ht,hGzero t ▸ hGmarks (0,t)⟩,
      ⟨mem_range_self _,hGzero t ▸ hGmarks (0,t)⟩⟩

private theorem actualRawCompatibleOriginalCentralAxisCore
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b})
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (hcontact : (ArcSurgery.crossings M a b).Nonempty) :
    ∃ φ : C(Interval,Interval), Function.Injective φ ∧
      (∀ t, 0<(φ t:ℝ) ∧ (φ t:ℝ)<1) ∧
    ∃ G : C(Interval × Interval,S),
      (∀ t, G (0,t)=b.val.map (φ t)) ∧
      (∀ τ, Function.Injective (fun t => G (τ,t))) ∧
      (∀ z, G z ∉ (M.cover.branch : Set S)) ∧
      (∀ t, G (1,t) ∉ a.val.image) ∧
      (ArcSurgery.crossings M a b ⊆ range (fun t => G (0,t))) ∧
      {t : Interval | G (0,t) ∈ a.val.image}.Finite ∧
    ∃ B : Interval × Set.Icc (-1:ℝ) 1 → S, ∃ hB : IsEmbedding B,
      (∀ z, B z ∉ (M.cover.branch : Set S)) ∧
      (∀ z, B z ∈ a.val.image ↔ z.2.val=0) ∧
    ∃ T : Set (Interval × Interval), IsOpen T ∧ G ⁻¹' a.val.image ⊆ T ∧
    ∃ L : C(T,Set.range B), (∀ z : T, (L z).val=G z.val) ∧
    ∃ ψ : C(T,ℝ),
      (∀ z : T, ψ z=((hB.toHomeomorph.symm (L z)).2:ℝ)) ∧
      (∀ z : T, 0<((hB.toHomeomorph.symm (L z)).1:ℝ) ∧
        ((hB.toHomeomorph.symm (L z)).1:ℝ)<1 ∧ -1<ψ z ∧ ψ z<1) ∧
      (∀ z : T, ψ z=0 ↔ G z.val ∈ a.val.image) ∧
      (∀ z : T, z.val.1=1 → ψ z≠0) := by
  obtain ⟨ε,hε,hεhalf,φ,hφ,hφbounds,G,hGzero,hGinject,hGmarks,hGtop,hGcontact,hGfinite⟩ :=
    actualRawCompatibleFiniteCentralSweep M a b hne hc hfinite hcontact
  have htop' : ∀ z : Interval × Interval,z.1=1 → G z ∉ a.val.image := by
    rintro ⟨τ,t⟩ hτ
    dsimp at hτ
    subst τ
    exact hGtop t
  obtain ⟨B,hB,hBmarks,hBaxis,T,hT,hGT,L,hL,ψ,hψ,hbounds,haxis,htopψ⟩ :=
    actual_mark_free_movie_exact_contact_core M a G hGmarks htop'
  refine ⟨φ,hφ,?_,G,hGzero,hGinject,hGmarks,hGtop,hGcontact,hGfinite,
    B,hB,hBmarks,hBaxis,T,hT,hGT,L,hL,ψ,hψ,hbounds,haxis,htopψ⟩
  intro t
  obtain ⟨hlo,hhi⟩ := hφbounds t
  constructor <;> linarith

private theorem actualRawCompatibleEndpointSeparatedCentralSweep
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b})
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (hcontact : (ArcSurgery.crossings M a b).Nonempty)
    (hseparated : ∀ c : Interval,c=0 ∨ c=1 → b.val.map c ∉ a.val.image) :
    ∃ ε : ℝ, 0<ε ∧ ε<1/2 ∧
    ∃ φ : C(Interval,Interval), Function.Injective φ ∧ StrictMono φ ∧
      (∀ t, ε<(φ t:ℝ) ∧ (φ t:ℝ)<1-ε) ∧
    ∃ G : C(Interval × Interval,S),
      (∀ t, G (0,t)=b.val.map (φ t)) ∧
      (∀ τ, Function.Injective (fun t => G (τ,t))) ∧
      (∀ z, G z ∉ (M.cover.branch : Set S)) ∧
      (∀ t, G (1,t) ∉ a.val.image) ∧
      (∀ τ,G (τ,0) ∉ a.val.image ∧ G (τ,1) ∉ a.val.image) ∧
      (ArcSurgery.crossings M a b ⊆ range (fun t => G (0,t))) ∧
      {t : Interval | G (0,t) ∈ a.val.image}.Finite := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨F,hzero,hcollision,hends,hmarks,htop⟩ :=
    actualRawCompatibleLoopInclusiveSweep M a b hne hc
  have htailAvoidance (c : Interval) (hc : c=0 ∨ c=1)
      (hcOff : b.val.map c ∉ a.val.image) :
      ∃ V : Set Interval, IsOpen V ∧ c ∈ V ∧
        ∀ τ t : Interval, t ∈ V → F (τ,t) ∉ a.val.image := by
    as_aux_lemma =>
      let N : Set (Interval × Interval) := F ⁻¹' a.val.imageᶜ
      have hN : IsOpen N := (isCompact_range a.val.continuous).isClosed.isOpen_compl.preimage
        F.continuous
      have hsafe : (Set.univ : Set Interval) ×ˢ {c} ⊆ N := by
        rintro ⟨τ,t⟩ ⟨_,ht⟩
        have htEq : t = c := mem_singleton_iff.mp ht
        subst t
        change F (τ,c) ∉ a.val.image
        rcases hc with rfl | rfl
        · simpa only [(hends τ).1] using hcOff
        · simpa only [(hends τ).2] using hcOff
      obtain ⟨U,V,hU,hV,hUall,hVc,hUV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton hN hsafe
      exact ⟨V,hV,hVc (mem_singleton c),fun τ t ht => hUV ⟨hUall (mem_univ τ),ht⟩⟩
  have htailMargin (c : Interval) (hc : c=0 ∨ c=1) :
      ∃ δ : ℝ, 0 < δ ∧ (b.val.map c ∉ a.val.image →
        ∀ τ t : Interval, dist t c < δ → F (τ,t) ∉ a.val.image) := by
    as_aux_lemma =>
      by_cases hcOff : b.val.map c ∉ a.val.image
      · obtain ⟨V,hV,hcV,havoid⟩ := htailAvoidance c hc hcOff
        obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hcV)
        exact ⟨δ,hδ,fun _ τ t ht => havoid τ t (hball ht)⟩
      · exact ⟨1,by norm_num,fun h => False.elim (hcOff h)⟩
  obtain ⟨δ₀,hδ₀,htail₀⟩ := htailMargin 0 (Or.inl rfl)
  obtain ⟨δ₁,hδ₁,htail₁⟩ := htailMargin 1 (Or.inr rfl)
  let K : Set Interval := {t | b.val.map t ∈ ArcSurgery.crossings M a b}
  have hKfinite : K.Finite := hfinite.preimage (by
    intro t ht s hs he
    rcases b.val.injective_except_loop_closure t s he with he | ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact he
    · exact False.elim (ht.2.2 b.val.start_marked)
    · exact False.elim (ht.2.2 b.val.end_marked))
  have hKnonempty : K.Nonempty := by
    obtain ⟨p,hp⟩ := hcontact
    obtain ⟨t,ht⟩ := hp.2.1
    refine ⟨t,?_⟩
    change b.val.map t ∈ ArcSurgery.crossings M a b
    rw [ht]
    exact hp
  obtain ⟨l,hl,hlmin⟩ := hKfinite.isCompact.exists_isLeast hKnonempty
  obtain ⟨u,hu,humax⟩ := hKfinite.isCompact.exists_isGreatest hKnonempty
  have hlpos : (0:ℝ)<(l:ℝ) := by
    apply lt_of_le_of_ne l.property.1
    intro h
    have he : l=(0:Interval) := Subtype.ext h.symm
    exact hl.2.2 (he ▸ b.val.start_marked)
  have hult : (u:ℝ)<(1:ℝ) := by
    apply lt_of_le_of_ne u.property.2
    intro h
    have he : u=(1:Interval) := Subtype.ext h
    exact hu.2.2 (he ▸ b.val.end_marked)
  let δ : ℝ := min (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)/2
  have hδpos : 0<δ := by dsimp [δ]; positivity
  have hδhalf : δ<1/2 := by
    have hlo : (l:ℝ)≤u := hlmin hu
    have h₁ := (min_le_left (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_left (l:ℝ) (1-(u:ℝ)))
    have h₂ := (min_le_left (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_right (l:ℝ) (1-(u:ℝ)))
    dsimp [δ]; linarith
  have hcontactwindow (t : Interval) (ht : t∈K) : δ<(t:ℝ) ∧ (t:ℝ)<1-δ := by
    have hlo : (l:ℝ)≤t := hlmin ht
    have hhi : (t:ℝ)≤u := humax ht
    have h₁ := (min_le_left (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_left (l:ℝ) (1-(u:ℝ)))
    have h₂ := (min_le_left (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_right (l:ℝ) (1-(u:ℝ)))
    dsimp [δ]; constructor <;> linarith
  let φ : C(Interval,Interval) := {
    toFun := fun t => ⟨δ+(1-2*δ)*(t:ℝ),by
      have ht0 := t.property.1
      have ht1 := t.property.2
      constructor <;> nlinarith⟩
    continuous_toFun := by fun_prop }
  have hφval (t : Interval) : (φ t:ℝ)=δ+(1-2*δ)*(t:ℝ) := rfl
  have hφinj : Function.Injective φ := by
    intro t s he
    have hh := congrArg Subtype.val he
    rw [hφval,hφval] at hh
    apply Subtype.ext
    nlinarith [hδhalf]
  have hφmono : StrictMono φ := by
    intro t s hts
    change (φ t:ℝ)<(φ s:ℝ)
    rw [hφval,hφval]
    have he : (t:ℝ)<(s:ℝ) := hts
    nlinarith
  have hφbounds (t : Interval) : 0<(φ t:ℝ) ∧ (φ t:ℝ)<1 := by
    rw [hφval]
    have ht0 := t.property.1
    have ht1 := t.property.2
    constructor <;> nlinarith
  have hφsurj (t : Interval) (ht : t∈K) : ∃ s : Interval,φ s=t := by
    obtain ⟨hlo,hhi⟩ := hcontactwindow t ht
    have hden : 0<1-2*δ := by linarith
    let s : Interval := ⟨((t:ℝ)-δ)/(1-2*δ),by
      constructor
      · exact (div_nonneg (by linarith) hden.le)
      · apply (div_le_one hden).mpr
        linarith⟩
    refine ⟨s,Subtype.ext ?_⟩
    rw [hφval]
    change δ+(1-2*δ)*(((t:ℝ)-δ)/(1-2*δ))=(t:ℝ)
    rw [mul_div_cancel₀ _ (ne_of_gt hden)]
    ring
  let G : C(Interval × Interval,S) :=
    F.comp ⟨fun z => (z.1,φ z.2),continuous_fst.prodMk (φ.continuous.comp continuous_snd)⟩
  have hGmarks (z : Interval × Interval) : G z ∉ (M.cover.branch : Set S) := by
    apply hmarks z.1 (φ z.2)
    · intro he
      have hh := congrArg Subtype.val he
      exact (hφbounds z.2).1.ne' hh
    · intro he
      have hh := congrArg Subtype.val he
      exact (hφbounds z.2).2.ne hh
  have hδ₀bound : δ<δ₀ := by
    have hh := (min_le_right (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_left δ₀ δ₁)
    dsimp [δ]; linarith
  have hδ₁bound : δ<δ₁ := by
    have hh := (min_le_right (min (l:ℝ) (1-(u:ℝ))) (min δ₀ δ₁)).trans (min_le_right δ₀ δ₁)
    dsimp [δ]; linarith
  have hGsides (τ : Interval) : G (τ,0) ∉ a.val.image ∧ G (τ,1) ∉ a.val.image := by
    constructor
    · apply htail₀ (hseparated 0 (Or.inl rfl)) τ (φ 0)
      change dist (φ 0:ℝ) 0<δ₀
      simp only [Real.dist_eq,sub_zero,hφval,Set.Icc.coe_zero,mul_zero,add_zero,
        abs_of_pos hδpos]
      exact hδ₀bound
    · apply htail₁ (hseparated 1 (Or.inr rfl)) τ (φ 1)
      change dist (φ 1:ℝ) 1<δ₁
      rw [Real.dist_eq,hφval]
      simp only [Set.Icc.coe_one,mul_one]
      rw [abs_of_neg (by linarith : δ+(1-2*δ)-1<0)]
      linarith
  have hGzero (t : Interval) : G (0,t)=b.val.map (φ t) := hzero (φ t)
  refine ⟨δ/2,by positivity,by linarith,φ,hφinj,hφmono,?_,G,hGzero,?_,hGmarks,?_,hGsides,?_,?_⟩
  · intro t
    rw [hφval]
    have ht0 := t.property.1
    have ht1 := t.property.2
    constructor <;> nlinarith
  · intro τ t s he
    rcases hcollision τ (φ t) (φ s) he with hh | ⟨hh,_⟩ | ⟨hh,_⟩
    · exact hφinj hh
    · have h := congrArg Subtype.val hh
      exact False.elim ((hφbounds t).1.ne' h)
    · have h := congrArg Subtype.val hh
      exact False.elim ((hφbounds t).2.ne h)
  · intro t ha
    apply htop (φ t)
    · intro he
      exact (hφbounds t).1.ne' (congrArg Subtype.val he)
    · intro he
      exact (hφbounds t).2.ne (congrArg Subtype.val he)
    · exact ⟨ha,hGmarks (1,t)⟩
  · intro p hp
    obtain ⟨t,ht⟩ := hp.2.1
    have htK : t∈K := by
      change b.val.map t ∈ ArcSurgery.crossings M a b
      rw [ht]
      exact hp
    obtain ⟨s,hs⟩ := hφsurj t htK
    exact ⟨s,(hGzero s).trans (congrArg b.val.map hs |>.trans ht)⟩
  · apply (hKfinite.preimage hφinj.injOn).subset
    intro t ht
    change φ t ∈ K
    exact ⟨⟨hGzero t ▸ ht,hGzero t ▸ hGmarks (0,t)⟩,
      ⟨mem_range_self _,hGzero t ▸ hGmarks (0,t)⟩⟩



private theorem actualRawEndpointSeparatedPreparedContactDrawing
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hfinite : (crossings M a b).Finite)
    (htransverse : ∀ p,p ∈ crossings M a b → CrossesInDisk M a b p)
    (p : S) (hp : p ∈ crossings M a b)
    (φ : C(Interval,Interval)) (hφ : IsEmbedding φ)
    (hφbounds : ∀ t,0<(φ t:ℝ) ∧ (φ t:ℝ)<1)
    (hcapture : ∀ t,b.val.map t ∈ crossings M a b → ∃ s,φ s=t)
    (G : C(Interval × Interval,S))
    (hbottom : ∀ t,G (0,t)=b.val.map (φ t))
    (hbottomEmbed : IsEmbedding (fun t => G (0,t)))
    (hmarks : ∀ z,G z ∉ (M.cover.branch : Set S))
    (htop : ∀ t,G (1,t) ∉ a.val.image)
    (hseams : ∀ τ,G (τ,0) ∉ a.val.image ∧ G (τ,1) ∉ a.val.image)
    (hfiniteBottom : {t : Interval | G (0,t) ∈ a.val.image}.Finite)
    (hfiniteTop : {t : Interval | G (1,t) ∈ a.val.image}.Finite)
    (hfiniteLeft : {τ : Interval | G (τ,0) ∈ a.val.image}.Finite)
    (hfiniteRight : {τ : Interval | G (τ,1) ∈ a.val.image}.Finite)
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (hBCmarks : ∀ z,BC z ∉ (M.cover.branch : Set S))
    (hBCaxis : ∀ z,BC z ∈ a.val.image ↔ z.2.val=0)
    (T : Set (Interval × Interval)) (hT : IsOpen T) (hcontacts : G ⁻¹' a.val.image ⊆ T)
    (Q : C(T,range BC)) (hQ : ∀ z : T,(Q z).val=G z.val)
    (ψ : C(T,ℝ)) (hψ : ∀ z : T,ψ z=((hBC.toHomeomorph.symm (Q z)).2:ℝ))
    (hψbounds : ∀ z : T,0<((hBC.toHomeomorph.symm (Q z)).1:ℝ) ∧
      ((hBC.toHomeomorph.symm (Q z)).1:ℝ)<1 ∧ -1<ψ z ∧ ψ z<1)
    (hψzero : ∀ z : T,ψ z=0 ↔ G z.val ∈ a.val.image)
    (hψtop : ∀ z : T,z.val.1=1 → ψ z≠0) :
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
          have hc : G (0,t)∈a.val.image := by
            change actualGridSurfaceMovie ((0,t),1)∈a.val.image at hcontact
            rw [hActualGridBoundary _ 1 (Or.inl rfl)] at hcontact
            exact hcontact
          rcases ht with rfl | rfl
          · exact False.elim ((hseams 0).1 hc)
          · exact False.elim ((hseams 0).2 hc)
        intro t ht
        by_cases ht0 : t=0
        · exact hBottomCornerDegree t (Or.inl ht0) ht
        · by_cases ht1 : t=1
          · exact hBottomCornerDegree t (Or.inr ht1) ht
          · rw [hArcsEndpointCount]
            exact hGlobalOpenBottomDegree t
              (lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm)))
              (lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))) ht

private theorem actualRawEndpointSeparatedDrawingSelectsOriginalSubpaths
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (p : S) (hp : p ∈ crossings M a b)
    (φ : C(Interval,Interval)) (hφ : IsEmbedding φ)
    (hφbounds : ∀ t,0<(φ t:ℝ) ∧ (φ t:ℝ)<1)
    (hcapture : ∀ t,b.val.map t ∈ crossings M a b → ∃ s,φ s=t)
    (hActualSourcePhiStrictMono : StrictMono φ)
    (G : C(Interval × Interval,S))
    (hbottom : ∀ t,G (0,t)=b.val.map (φ t))
    (htop : ∀ t,G (1,t) ∉ a.val.image)
    (hseams : ∀ τ,G (τ,0) ∉ a.val.image ∧ G (τ,1) ∉ a.val.image)
    (hDrawing :
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
        {q : ↑edges × Fin 2 | arc q.1 (if q.2=0 then 0 else 1)=(0,t)}.ncard=1)) :
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
  have hActualOldArcContactPathHasOriginalInteriorParameters
      (x y : Interval × Interval) (q : Path x y)
      (hcontact : ∀ t,actualFiniteConeSweep (q t)∈a.val.image)
      (hmarks : ∀ t,actualFiniteConeSweep (q t)∉(M.cover.branch : Set S)) :
      ∃ κ : C(Interval,Interval),(∀ t,a.val.map (κ t)=actualFiniteConeSweep (q t)) ∧
        ∀ t,κ t∈Set.Ioo (0 : Interval) 1 := by
    let contact : C(Interval,arcInterior M a) :=
      ⟨fun t => ⟨actualFiniteConeSweep (q t),⟨hcontact t,hmarks t⟩⟩,
        (actualFiniteConeSweep.continuous.comp q.continuous).subtype_mk _⟩
    let coordinates := anchorInteriorCoordinates M a
    let κ : C(Interval,Interval) :=
      ⟨fun t => openAnchorInterval (coordinates.symm (contact t)),
        openAnchorInterval_continuous.comp (coordinates.symm.continuous.comp contact.continuous)⟩
    refine ⟨κ,?_,?_⟩
    · intro t
      exact congrArg Subtype.val (coordinates.apply_symm_apply (contact t))
    · intro t
      exact (coordinates.symm (contact t)).property
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
  have hActualSourceBottomContactNonempty : ∃ w : actualContactVertices,w.val.1=0 := by
    obtain ⟨w,hw,hB,hdegree⟩ := hActualSpecifiedOriginalCrossingProducesOddVertex
    exact ⟨w,hB⟩
  obtain ⟨selectedStart,selectedEnd,hEndDistinct,hStartBottom,hSelectedCleanChoice,
    actualSelectedFirstBoundaryGraphPath,hActualSelectedFirstBoundaryGraphPath,
    hActualSelectedFirstBoundaryGraphDegree,hActualSelectedFirstBoundaryGraphBoundary⟩ :=
    hActualFiniteSameSourceGraphProducesCleanOriginalContactPath
      (fun z hc hb => hBoundary z hc hb) hActualSourceBottomContactNonempty
  obtain ⟨actualSelectedFirstBoundaryPlanarLabels,hActualSelectedFirstBoundaryPlanarPath,
    hActualSelectedFirstBoundaryPlanarVertices,selectedContactPath,hSelectedEmbedding,
    hActualSelectedFirstBoundaryCarrierImage,hSelectedProper,
    originalParameterPath,hOriginalParameterIdentity,hOriginalParameterInterior⟩ :=
    hActualBoundaryProperGraphPathLiftsToProperOriginalContactPath
      (fun z hc hb => hBoundary z hc hb) hEndDistinct actualSelectedFirstBoundaryGraphPath
      hActualSelectedFirstBoundaryGraphPath hActualSelectedFirstBoundaryGraphBoundary
  rcases hSelectedCleanChoice with h | h | h
  · exact hActualCleanBottomReturnClosesOriginalSubpathTarget
      (fun z hc hb => hBoundary z hc hb) hActualSourcePhiStrictMono
      selectedStart selectedEnd hStartBottom h.1 hEndDistinct h.2.1 h.2.2
      selectedContactPath originalParameterPath hOriginalParameterIdentity hOriginalParameterInterior
  · have he : selectedEnd.val=(selectedEnd.val.1,0) := Prod.ext rfl h.1
    have hc := hActualContactVerticesImage selectedEnd
    rw [he,hFinalBoundary _ (Or.inr (Or.inr (Or.inl rfl)))] at hc
    exact False.elim ((hseams selectedEnd.val.1).1 hc)
  · have he : selectedEnd.val=(selectedEnd.val.1,1) := Prod.ext rfl h.1
    have hc := hActualContactVerticesImage selectedEnd
    rw [he,hFinalBoundary _ (Or.inr (Or.inr (Or.inr rfl)))] at hc
    exact False.elim ((hseams selectedEnd.val.1).2 hc)

private theorem actualChartedOriginalJordanDiskRealization
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (en : OpenPartialHomeomorph S Plane) (hentarget : en.target=univ)
    (C₂ : Set Plane) (hC₂ : IsJordanCurve C₂)
    (f g : C(Interval,S)) (u v : S)
    (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfa : range f ⊆ a.val.image) (hgb : range g ⊆ b.val.image)
    (hf0 : f 0=u) (hg0 : g 0=u) (hf1 : f 1=v) (hg1 : g 1=v)
    (hinter : range f ∩ range g={u,v})
    (Ω : Set S) (hfrontier : frontier Ω=range f ∪ range g)
    (hfree : Disjoint Ω (M.cover.branch : Set S))
    (hmarks : ∀ z ∈ range f ∪ range g, z ∈ M.cover.branch → z=u)
    (hclpull : en.symm '' closure (inside C₂)=closure Ω)
    (hinpull : en.symm '' inside C₂=Ω)
    (hcpull : en.symm '' C₂=range f ∪ range g) :
    ∃ D : ActualMarkedTwoSideDisk M a b,
      D.firstSide=f ∧ D.secondSide=g ∧ D.firstCorner=u ∧ D.secondCorner=v ∧
      D.openInterior=Ω ∧ range D.disk=closure Ω := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hinv : IsOpenEmbedding en.symm := en.symm.isOpenEmbedding hentarget
  obtain ⟨η,hηboundary,hηinside⟩ := CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary C₂ hC₂
  let d : C(closedBall (0:Plane) 1,S) :=
    ⟨fun x => en.symm (η x : Plane),hinv.continuous.comp (continuous_subtype_val.comp η.continuous)⟩
  have hdi : Function.Injective d := by
    as_aux_lemma =>
      intro x y he
      apply η.injective
      exact Subtype.ext (hinv.injective he)
  have hd : IsEmbedding d := (d.continuous.isClosedEmbedding hdi).isEmbedding
  have hdrange : range d=closure Ω := by
    as_aux_lemma =>
      rw [← hclpull]
      ext z
      constructor
      · rintro ⟨x,rfl⟩; exact ⟨η x,(η x).property,rfl⟩
      · rintro ⟨w,hw,rfl⟩
        exact ⟨η.symm ⟨w,hw⟩,congrArg (fun t : closure (inside C₂) => en.symm t) (η.apply_symm_apply _)⟩
  have hboundary : d '' {x | x.val ∈ Metric.sphere (0:Plane) 1}=range f ∪ range g := by
    as_aux_lemma =>
      rw [← hcpull]
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        have hxn : ‖(x:Plane)‖=1 := by simpa only [mem_setOf_eq,mem_sphere,dist_zero_right] using hx
        exact ⟨η x,(hηboundary x).mpr hxn,rfl⟩
      · rintro ⟨w,hw,rfl⟩
        have hwcl : w ∈ closure (inside C₂) := by
          apply frontier_subset_closure
          rw [(jordan_curve_theorem hC₂).frontier_inside]
          exact hw
        let x := η.symm ⟨w,hwcl⟩
        have hxw : (η x:Plane)=w := congrArg Subtype.val (η.apply_symm_apply _)
        refine ⟨x,?_,congrArg en.symm hxw⟩
        have hxn : ‖(x:Plane)‖=1 := (hηboundary x).mp (hxw.symm ▸ hw)
        simpa only [mem_setOf_eq,mem_sphere,dist_zero_right] using hxn
  have hinterior : d '' {x | x.val ∈ ball (0:Plane) 1}=Ω := by
    as_aux_lemma =>
      rw [← hinpull]
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        have hxn : ‖(x:Plane)‖<1 := by simpa only [mem_setOf_eq,mem_ball,dist_zero_right] using hx
        exact ⟨η x,(hηinside x).mpr hxn,rfl⟩
      · rintro ⟨w,hw,rfl⟩
        let x := η.symm ⟨w,subset_closure hw⟩
        have hxw : (η x:Plane)=w := congrArg Subtype.val (η.apply_symm_apply _)
        refine ⟨x,?_,congrArg en.symm hxw⟩
        have hxn : ‖(x:Plane)‖<1 := (hηinside x).mp (hxw.symm ▸ hw)
        simpa only [mem_setOf_eq,mem_ball,dist_zero_right] using hxn
  let D : ActualMarkedTwoSideDisk M a b := {
    firstCorner := u
    secondCorner := v
    firstSide := f
    secondSide := g
    first_embedded := hf
    second_embedded := hg
    first_zero := hf0
    first_one := hf1
    second_zero := hg0
    second_one := hg1
    first_on_curve := hfa
    second_on_curve := hgb
    sides_inter := hinter
    disk := d
    disk_embedded := hd
    boundary_eq := hboundary
    marks_are_corners := by
      intro z hz hzm
      have hzcl : z ∈ closure Ω := hdrange ▸ hz
      rw [closure_eq_self_union_frontier,hfrontier] at hzcl
      rcases hzcl with hzΩ | hzbd
      · exact False.elim (disjoint_left.mp hfree hzΩ hzm)
      · exact Or.inl (hmarks z hzbd hzm) }
  exact ⟨D,rfl,rfl,rfl,rfl,hinterior,hdrange⟩

private theorem actualOriginalJordanRegionDiskRealization
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (f g : C(Interval,S)) (u v : S)
    (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfa : range f ⊆ a.val.image) (hgb : range g ⊆ b.val.image)
    (hf0 : f 0=u) (hg0 : g 0=u) (hf1 : f 1=v) (hg1 : g 1=v)
    (hne : u≠v) (hinter : range f ∩ range g={u,v})
    (Ω : Set S) (hΩ : IsComplementComponent (range f ∪ range g) Ω)
    (hfrontier : frontier Ω=range f ∪ range g)
    (hfree : Disjoint Ω (M.cover.branch : Set S))
    (hmarks : ∀ z ∈ range f ∪ range g, z ∈ M.cover.branch → z=u) :
    ∃ D : ActualMarkedTwoSideDisk M a b,
      D.firstSide=f ∧ D.secondSide=g ∧ D.firstCorner=u ∧ D.secondCorner=v ∧
      D.openInterior=Ω ∧ range D.disk=closure Ω := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hcollision : ∀ s t : Interval, f s = g t →
      (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t h
    have hx : f s ∈ ({u,v} : Set S) := by
      rw [← hinter]
      exact ⟨mem_range_self s, ⟨t,h.symm⟩⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨hf.injective (hx.trans hf0.symm),
        hg.injective (h.symm.trans (hx.trans hg0.symm))⟩
    · exact Or.inr ⟨hf.injective (hx.trans hf1.symm),
        hg.injective (h.symm.trans (hx.trans hg1.symm))⟩
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hf.injective hg.injective
    (hf0.trans hg0.symm) (hf1.trans hg1.symm) hcollision
  obtain ⟨J,hJ⟩ := actualCurve_sphereJordan M c
  have hcard : ({u} : Finset S).card < M.cover.branch.card := by
    as_aux_lemma =>
      rw [M.cover.branch_card]; simp
  obtain ⟨q₂,hqmark,hqu⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hqcurve : q₂ ∉ range f ∪ range g := fun hz => hqu (by simpa using hmarks q₂ hz hqmark)
  have hqJ : M.sphere q₂ ∉ J.image := by
    as_aux_lemma =>
      rw [hJ,hc]
      rintro ⟨z,hz,he⟩
      exact hqcurve (M.sphere.injective he ▸ hz)
  let P₂ : CurveComplex.SpherePort.Chart J := {
    puncture := M.sphere q₂
    avoids := hqJ
    plane := puncturedSpherePlane (M.sphere q₂) }
  let C₂ := P₂.planeImage J
  have hC₂ : IsJordanCurve C₂ := CurveComplex.SpherePort.chart_image_jordan J P₂
  have hback : M.sphere.symm '' J.image=range f ∪ range g := by
    as_aux_lemma =>
      rw [hJ,hc,← image_comp,M.sphere.symm_comp_self,image_id]
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2+1) := ⟨by simp⟩
  let en : OpenPartialHomeomorph S Plane :=
    M.sphere.toOpenPartialHomeomorph.trans (stereographic' 2 (M.sphere q₂))
  have hensource : en.source={q₂}ᶜ := by
    as_aux_lemma =>
      ext x; simp [en,OpenPartialHomeomorph.trans_source]
  have hentarget : en.target=univ := by simp [en,OpenPartialHomeomorph.trans_target]
  have hopen : IsOpen Ω := complementComponent_open
    ((isCompact_range f.continuous).isClosed.union (isCompact_range g.continuous).isClosed) hΩ
  have hclosure : closure Ω ⊆ en.source := by
    as_aux_lemma =>
      rw [hensource,closure_eq_self_union_frontier,hfrontier]
      rintro x (hx | hx) he
      · exact disjoint_left.mp hfree hx (he.symm ▸ hqmark)
      · exact hqcurve (he ▸ hx)
  have hcurveSource : (range f ∪ range g) ⊆ en.source :=
    fun x hx => hclosure (frontier_subset_closure (hfrontier.symm ▸ hx))
  have hC₂image : en '' (range f ∪ range g) = C₂ := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨⟨M.sphere x, ?_⟩, ?_, ?_⟩
        · intro he
          have hs := hcurveSource hx
          rw [hensource] at hs
          exact hs (M.sphere.injective he)
        · rw [hJ,hc]
          exact ⟨x,hx,rfl⟩
        · rfl
      · rintro ⟨x,hx,rfl⟩
        refine ⟨M.sphere.symm x, ?_, ?_⟩
        · rw [← hback]
          exact ⟨x,hx,rfl⟩
        · change (stereographic' 2 (M.sphere q₂)) (M.sphere (M.sphere.symm x)) = _
          rw [M.sphere.apply_symm_apply]
          rfl
  let Uplane := en '' Ω
  have hUplaneOpen : IsOpen Uplane := en.isOpen_image_of_subset_source hopen
    (Set.Subset.trans subset_closure hclosure)
  have hUplaneConn : IsConnected Uplane := hΩ.2.1.image en
    (en.continuousOn.mono (Set.Subset.trans subset_closure hclosure))
  have hUplaneBounded : Bornology.IsBounded Uplane := by
    as_aux_lemma =>
      have hk : IsCompact (closure Ω) := isClosed_closure.isCompact
      exact (hk.image_of_continuousOn (en.continuousOn.mono hclosure)).isBounded.subset
        (Set.image_mono subset_closure)
  have hUisImage : en.IsImage Ω Uplane := by
    as_aux_lemma =>
      intro x hx
      constructor
      · rintro ⟨y,hy,he⟩
        exact en.injOn (hclosure (subset_closure hy)) hx he ▸ hy
      · intro hy
        exact ⟨x,hy,rfl⟩
  have hUplaneFrontier : frontier Uplane = C₂ := by
    as_aux_lemma =>
      have he := hUisImage.frontier.image_eq
      have hfs : frontier Ω ⊆ en.source :=
        fun x hx => hclosure (frontier_subset_closure hx)
      rw [Set.inter_eq_right.mpr hfs, hentarget, Set.univ_inter, hfrontier,
        hC₂image] at he
      exact he.symm
  have hUplaneInside : Uplane = Schoenflies.inside C₂ :=
    bounded_jordan_frontier_region_eq_inside hC₂ hUplaneOpen hUplaneConn
      hUplaneBounded hUplaneFrontier

  have hpull (A : Set S) (hA : A ⊆ en.source) : en.symm '' (en '' A)=A := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨w,⟨t,ht,rfl⟩,rfl⟩
        exact (en.left_inv (hA ht)).symm ▸ ht
      · intro hz
        exact ⟨en z,⟨z,hz,rfl⟩,en.left_inv (hA hz)⟩
  have hclpull : en.symm '' closure (inside C₂)=closure Ω := by
    as_aux_lemma =>
      have he := hUisImage.closure.symm_image_eq
      rw [hentarget,univ_inter,inter_eq_right.mpr hclosure,hUplaneInside] at he
      exact he
  have hinpull : en.symm '' inside C₂=Ω := by
    as_aux_lemma =>
      rw [← hUplaneInside]
      exact hpull Ω (Subset.trans subset_closure hclosure)
  have hcpull : en.symm '' C₂=range f ∪ range g := by
    as_aux_lemma =>
      rw [← hC₂image]
      exact hpull _ hcurveSource
  exact actualChartedOriginalJordanDiskRealization M a b en hentarget C₂ hC₂
    f g u v hf hg hfa hgb hf0 hg0 hf1 hg1 hinter Ω hfrontier hfree hmarks
    hclpull hinpull hcpull
private theorem actualOriginalPuncturedSidesDiskRealization
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (f g : C(Interval,S)) (u v : S)
    (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hfa : range f ⊆ a.val.image) (hgb : range g ⊆ b.val.image)
    (hf0 : f 0=u) (hg0 : g 0=u) (hf1 : f 1=v) (hg1 : g 1=v)
    (hne : u≠v) (hinter : range f ∩ range g={u,v})
    (hu : u ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
    (hv : v ∈ ((M.cover.branch : Set S) \ {u})ᶜ)
    (α β : Path (⟨u,hu⟩ : ↑((M.cover.branch : Set S) \ {u})ᶜ) ⟨v,hv⟩)
    (hα : ∀ t : Interval, (α t : S)=f t)
    (hβ : ∀ t : Interval, (β t : S)=g t)
    (hhom : α.Homotopic β) :
    ∃ D : ActualMarkedTwoSideDisk M a b,
      D.firstSide=f ∧ D.secondSide=g ∧ D.firstCorner=u ∧ D.secondCorner=v := by
  obtain ⟨Ω,hΩne,hΩconn,hΩsub,hΩmax,hfrontier,hfree⟩ :=
    actual_punctured_homotopic_jordan_sides_have_empty_region M f g u v hf hg
      hf0 hg0 hf1 hg1 hne hinter hu hv α β hα hβ hhom
  have hmarks : ∀ z ∈ range f ∪ range g, z ∈ M.cover.branch → z=u := by
    intro z hz hzm
    rcases hz with ⟨t,rfl⟩ | ⟨t,rfl⟩
    · by_contra hn
      have ht := (α t).property
      rw [hα] at ht
      exact ht ⟨hzm,hn⟩
    · by_contra hn
      have ht := (β t).property
      rw [hβ] at ht
      exact ht ⟨hzm,hn⟩
  obtain ⟨D,hfD,hgD,huD,hvD,_,_⟩ :=
    actualOriginalJordanRegionDiskRealization M a b f g u v hf hg hfa hgb
      hf0 hg0 hf1 hg1 hne hinter Ω ⟨hΩne,hΩconn,hΩsub,hΩmax⟩ hfrontier hfree hmarks
  exact ⟨D,hfD,hgD,huD,hvD⟩


private theorem actualRawEndpointSeparatedProducesOriginalMarkedDisk
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a, ArcSurgery.vertex M b})
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (htransverse : ∀ p ∈ ArcSurgery.crossings M a b,ArcSurgery.CrossesInDisk M a b p)
    (hcontact : (ArcSurgery.crossings M a b).Nonempty)
    (hseparated : ∀ c : Interval,c=0 ∨ c=1 → b.val.map c ∉ a.val.image) :
    ∃ D : ActualMarkedTwoSideDisk M a b,
      D.firstCorner ∈ ArcSurgery.crossings M a b ∨ D.secondCorner ∈ ArcSurgery.crossings M a b := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨ε,hε,hεhalf,φ,hφ,hφmono,hφwindow,G,hbottom,hGinject,hmarks,htop,hseams,hcapturePhysical,hfiniteBottom⟩ :=
    actualRawCompatibleEndpointSeparatedCentralSweep M a b hne hc hfinite hcontact hseparated
  have hφbounds (t : Interval) : 0<(φ t:ℝ) ∧ (φ t:ℝ)<1 := by
    obtain ⟨hlo,hhi⟩ := hφwindow t
    constructor <;> linarith
  have hcapture : ∀ t,b.val.map t ∈ ArcSurgery.crossings M a b → ∃ s,φ s=t := by
    intro t ht
    obtain ⟨s,hs⟩ := hcapturePhysical ht
    have he : b.val.map (φ s)=b.val.map t := (hbottom s).symm.trans hs
    rcases b.val.injective_except_loop_closure _ _ he with he | ⟨he,_⟩ | ⟨he,_⟩
    · exact ⟨s,he⟩
    · exact False.elim ((hφbounds s).1.ne' (congrArg Subtype.val he))
    · exact False.elim ((hφbounds s).2.ne (congrArg Subtype.val he))
  have hφEmbed : IsEmbedding φ := (φ.continuous.isClosedEmbedding hφ).isEmbedding
  have hbottomContinuous : Continuous (fun t : Interval => G (0,t)) :=
    G.continuous.comp (continuous_const.prodMk continuous_id)
  have hbottomEmbed : IsEmbedding (fun t : Interval => G (0,t)) :=
    (hbottomContinuous.isClosedEmbedding (hGinject 0)).isEmbedding
  have htop' : ∀ z : Interval × Interval,z.1=1 → G z ∉ a.val.image := by
    rintro ⟨τ,t⟩ hτ
    dsimp at hτ
    subst τ
    exact htop t
  obtain ⟨BC,hBC,hBCmarks,hBCaxis,T,hT,hGT,Q,hQ,ψ,hψ,hbounds,hψzero,hψtop⟩ :=
    actual_mark_free_movie_exact_contact_core M a G hmarks htop'
  have hfiniteTop : {t : Interval | G (1,t) ∈ a.val.image}.Finite := by
    apply Set.finite_empty.subset
    intro t ht
    exact False.elim (htop t ht)
  have hfiniteLeft : {τ : Interval | G (τ,0) ∈ a.val.image}.Finite := by
    apply Set.finite_empty.subset
    intro τ hτ
    exact False.elim ((hseams τ).1 hτ)
  have hfiniteRight : {τ : Interval | G (τ,1) ∈ a.val.image}.Finite := by
    apply Set.finite_empty.subset
    intro τ hτ
    exact False.elim ((hseams τ).2 hτ)
  obtain ⟨p,hp⟩ := hcontact
  have hDrawing := actualRawEndpointSeparatedPreparedContactDrawing M a b hfinite htransverse p hp
    φ hφEmbed hφbounds hcapture G hbottom hbottomEmbed hmarks htop hseams
    hfiniteBottom hfiniteTop hfiniteLeft hfiniteRight BC hBC hBCmarks hBCaxis
    T hT hGT Q hQ ψ hψ hbounds hψzero hψtop
  obtain ⟨f,g,u,v,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,huv,hinter,hvcross,hucontact,
    hu,hv,α,β,hα,hβ,hhom⟩ := actualRawEndpointSeparatedDrawingSelectsOriginalSubpaths
    M a b p hp φ hφEmbed hφbounds hcapture hφmono G hbottom htop hseams hDrawing
  obtain ⟨D,hDf,hDg,hDu,hDv⟩ := actualOriginalPuncturedSidesDiskRealization
    M a b f g u v hf hg hfa hgb hf0 hg0 hf1 hg1 huv hinter hu hv α β hα hβ hhom
  exact ⟨D,Or.inr (hDv.symm ▸ hvcross)⟩


private theorem curve_crosscut_endpoint_on_other_side
    {X : Type} [TopologicalSpace X]
    (a : Curve X) (f g q : C(Interval,X)) (hf : IsEmbedding f)
    (hfa : range f ⊆ a.image) (hqa : range q ⊆ a.image)
    (hf0 : f 0 = g 0) (hf1 : f 1 = g 1)
    (U : Set X) (hfree : Disjoint U (range f ∪ range g))
    (hqin : q '' Ioo (0:Interval) 1 ⊆ U)
    (e : Interval) (hqe : q e ∈ range f ∪ range g) : q e ∈ range g := by
  by_contra hnot
  have hefirst : q e ∈ range f := hqe.resolve_right hnot
  obtain ⟨v,hv⟩ := hefirst
  have hv0 : v ≠ 0 := by
    intro h
    exact hnot ⟨0,hf0.symm.trans ((congrArg f h).symm.trans hv)⟩
  have hv1 : v ≠ 1 := by
    intro h
    exact hnot ⟨1,hf1.symm.trans ((congrArg f h).symm.trans hv)⟩
  have hvI : v ∈ Ioo (0:Interval) 1 :=
    ⟨lt_of_le_of_ne v.property.1 (Ne.symm hv0),lt_of_le_of_ne v.property.2 hv1⟩
  let qa : C(Interval,a.image) := ⟨fun t => ⟨q t,hqa (mem_range_self t)⟩,
    q.continuous.subtype_mk _⟩
  let V : Set Interval := qa ⁻¹' {x : a.image | (x:X) ∈ f '' Ioo (0:Interval) 1}
  have hVo : IsOpen V :=
    (CurveComplex.LocalSurgery.embedded_curve_subarc_interior_isOpen a f hf hfa).preimage
      qa.continuous
  have heV : e ∈ V := ⟨v,hvI,hv⟩
  have hecl : e ∈ closure (Ioo (0:Interval) 1) := by
    rw [closure_Ioo (by norm_num : (0:Interval) ≠ 1)]
    exact e.property
  obtain ⟨t,htV,htI⟩ := mem_closure_iff_nhds.mp hecl V (hVo.mem_nhds heV)
  have htU : q t ∈ U := hqin (mem_image_of_mem q htI)
  obtain ⟨w,hwI,hw⟩ := htV
  exact Set.disjoint_left.mp hfree htU (Or.inl ⟨w,hw⟩)

private theorem loop_crosscut_with_companion_impossible
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hloop : a.val.map (0 : Interval) = a.val.map (1 : Interval))
    (B : ActualMarkedTwoSideDisk M a b)
    (q f : C(Interval,S)) (hq : IsEmbedding q) (hf : IsEmbedding f)
    (hqa : range q ⊆ a.val.image)
    (hff : range f ⊆ range B.firstSide)
    (hf0 : f 0 = q 0) (hf1 : f 1 = q 1)
    (hqin : q '' Ioo (0:Interval) 1 ⊆ B.openInterior)
    (hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide)) : False := by
  let : T2Space S := M.sphere.symm.t2Space
  have hcross (t u : Interval) (he : q t = f u) :
      (t = 0 ∧ u = 0) ∨ (t = 1 ∧ u = 1) := by
    by_cases ht0 : t = 0
    · exact Or.inl ⟨ht0,hf.injective (by rw [hf0,← he,ht0])⟩
    by_cases ht1 : t = 1
    · exact Or.inr ⟨ht1,hf.injective (by rw [hf1,← he,ht1])⟩
    have htI : t ∈ Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
    exact False.elim (Set.disjoint_left.mp hfree (hqin ⟨t,htI,rfl⟩)
      (Or.inl (he.symm ▸ hff (mem_range_self u))))
  obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs q f hq.injective hf.injective
    hf0.symm hf1.symm hcross
  obtain ⟨ac,hac⟩ := actual_curve_of_marked_interval_loop
    (⟨a.val.map,a.val.continuous⟩ : C(Interval,S)) hloop
    a.val.injective_except_loop_closure
  have hcA : c.image ⊆ ac.image := by
    rw [hc,hac]
    exact union_subset hqa (hff.trans B.first_on_curve)
  have heq : c.image = a.val.image :=
    (CurveComplex.LocalSurgery.curve_image_eq_of_subset ac c hcA).trans hac
  have hqDisk : range q ⊆ range B.disk := by
    rintro z ⟨t,rfl⟩
    by_cases ht0 : t = 0
    · subst t
      exact image_subset_range _ _ (B.boundary_eq.symm ▸
        (show q 0 ∈ range B.firstSide ∪ range B.secondSide from
          Or.inl (hff ⟨0,hf0⟩)))
    by_cases ht1 : t = 1
    · subst t
      exact image_subset_range _ _ (B.boundary_eq.symm ▸
        (show q 1 ∈ range B.firstSide ∪ range B.secondSide from
          Or.inl (hff ⟨1,hf1⟩)))
    exact image_subset_range _ _ (hqin ⟨t,
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
        lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
  have haDisk : a.val.image ⊆ range B.disk := by
    rw [← heq,hc]
    exact union_subset hqDisk (fun z hz => image_subset_range _ _
      (B.boundary_eq.symm ▸ (show z ∈ range B.firstSide ∪ range B.secondSide from
        Or.inl (hff hz))))
  exact actual_essential_loop_not_in_interior_free_disk M a hloop B.disk B.disk_embedded
    (relative_selected_bigon_open_interior_mark_free M a b B) haDisk

private theorem actual_loop_first_intrusion_crosscut
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hloop : a.val.map (0 : Interval) = a.val.map (1 : Interval))
    (B : ActualMarkedTwoSideDisk M a b)
    (hin : (a.val.image ∩ B.openInterior).Nonempty) :
    ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ a.val.image ∧
      q 0 ∈ range B.secondSide ∧ q 1 ∈ range B.secondSide ∧
      q '' Ioo (0:Interval) 1 ⊆ B.openInterior ∧
      ¬ (q 0 ∈ ({B.firstCorner,B.secondCorner}:Set S) ∧
        q 1 ∈ ({B.firstCorner,B.secondCorner}:Set S)) := by
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨q,hq,hqa,hq0,hq1,hqin⟩ :=
    actual_essential_marked_arc_entering_interior_free_disk_has_crosscut
      M a B.disk B.disk_embedded
      (relative_selected_bigon_open_interior_mark_free M a b B) hin
  obtain ⟨ac,hac⟩ := actual_curve_of_marked_interval_loop
    (⟨a.val.map,a.val.continuous⟩ : C(Interval,S)) hloop
    a.val.injective_except_loop_closure
  have hfa : range B.firstSide ⊆ ac.image := by
    rw [hac]
    exact B.first_on_curve
  have hqa' : range q ⊆ ac.image := by rwa [hac]
  have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
    rw [← B.boundary_eq]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := B.disk_embedded.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have hqe (e : Interval) (he : q e ∈ range B.firstSide ∪ range B.secondSide) :
      q e ∈ range B.secondSide :=
    curve_crosscut_endpoint_on_other_side ac B.firstSide B.secondSide q
      B.first_embedded hfa hqa'
      (B.first_zero.trans B.second_zero.symm)
      (B.first_one.trans B.second_one.symm)
      B.openInterior hfree hqin e he
  have hq0' : q 0 ∈ range B.secondSide := hqe 0 (B.boundary_eq ▸ hq0)
  have hq1' : q 1 ∈ range B.secondSide := hqe 1 (B.boundary_eq ▸ hq1)
  refine ⟨q,hq,hqa,hq0',hq1',hqin,?_⟩
  rintro ⟨hc0,hc1⟩
  have hqne : q 0 ≠ q 1 := by
    intro he
    exact zero_ne_one (hq.injective he)
  rcases mem_insert_iff.mp hc0 with hc0 | hc0
  · rcases mem_insert_iff.mp hc1 with hc1 | hc1
    · exact hqne (hc0.trans hc1.symm)
    · apply loop_crosscut_with_companion_impossible M a b hloop B q B.firstSide
        hq B.first_embedded hqa (fun z hz => hz) ?_ ?_ hqin hfree
      · exact B.first_zero.trans hc0.symm
      · exact B.first_one.trans (mem_singleton_iff.mp hc1).symm
  · rcases mem_insert_iff.mp hc1 with hc1 | hc1
    · let rev : C(Interval,Interval) :=
        ⟨fun t => ⟨1-t.val,by
          constructor <;> linarith [t.property.1,t.property.2]⟩,by fun_prop⟩
      let f : C(Interval,S) := B.firstSide.comp rev
      have hfi : Function.Injective f := by
        intro t u he
        have he' := congrArg Subtype.val (B.first_embedded.injective he)
        apply Subtype.ext
        change 1-t.val=1-u.val at he'
        linarith
      have hf : IsEmbedding f := (f.continuous.isClosedEmbedding hfi).isEmbedding
      have hff : range f ⊆ range B.firstSide := by
        rintro z ⟨t,rfl⟩
        exact ⟨rev t,rfl⟩
      have hrev0 : rev 0 = 1 := by apply Subtype.ext; norm_num [rev]
      have hrev1 : rev 1 = 0 := by apply Subtype.ext; norm_num [rev]
      apply loop_crosscut_with_companion_impossible M a b hloop B q f
        hq hf hqa hff ?_ ?_ hqin hfree
      · change B.firstSide (rev 0)=q 0
        rw [hrev0,B.first_one]
        exact (mem_singleton_iff.mp hc0).symm
      · change B.firstSide (rev 1)=q 1
        rw [hrev1,B.first_zero]
        exact hc1.symm
    · exact hqne (mem_singleton_iff.mp hc0 |>.trans (mem_singleton_iff.mp hc1).symm)

private theorem actual_any_first_intrusion_crosscut
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (B : ActualMarkedTwoSideDisk M a b)
    (hin : (a.val.image ∩ B.openInterior).Nonempty) :
    ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ a.val.image ∧
      q 0 ∈ range B.secondSide ∧ q 1 ∈ range B.secondSide ∧
      q '' Ioo (0:Interval) 1 ⊆ B.openInterior ∧
      ¬ (q 0 ∈ ({B.firstCorner,B.secondCorner}:Set S) ∧
        q 1 ∈ ({B.firstCorner,B.secondCorner}:Set S)) := by
  by_cases hloop : a.val.map (0 : Interval) = a.val.map (1 : Interval)
  · exact actual_loop_first_intrusion_crosscut M a b hloop B hin
  let : T2Space S := M.sphere.symm.t2Space
  let an : NonLoopArc M := ⟨a.val,hloop⟩
  let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have hA : IsEmbedding A := (A.continuous.isClosedEmbedding an.injective).isEmbedding
  obtain ⟨q,hq,hqa,hq0,hq1,hqin⟩ :=
    actual_essential_marked_arc_entering_interior_free_disk_has_crosscut
      M a B.disk B.disk_embedded
      (relative_selected_bigon_open_interior_mark_free M a b B) hin
  have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
    rw [← B.boundary_eq]
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
    have huv := B.disk_embedded.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have hqe (e : Interval) (he : q e ∈ range B.firstSide ∪ range B.secondSide) :
      q e ∈ range B.secondSide :=
    CurveComplex.LocalSurgery.raw_self_intrusion_crosscut_endpoint_on_other_side
      A B.firstSide B.secondSide q hA B.first_embedded B.first_on_curve hqa
      (B.first_zero.trans B.second_zero.symm)
      (B.first_one.trans B.second_one.symm)
      B.openInterior hfree hqin e he
  refine ⟨q,hq,hqa,hqe 0 (B.boundary_eq ▸ hq0),hqe 1 (B.boundary_eq ▸ hq1),hqin,?_⟩
  rintro ⟨hc0,hc1⟩
  have hcorner (x : S) (hx : x ∈ ({B.firstCorner,B.secondCorner}:Set S)) :
      x ∈ range B.firstSide := by
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · exact ⟨0,B.first_zero.trans hx.symm⟩
    · exact ⟨1,B.first_one.trans (Set.mem_singleton_iff.mp hx).symm⟩
  have hqf : range q ⊆ range B.firstSide :=
    CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem
      A B.firstSide q hA hq B.first_on_curve hqa
      (hcorner _ hc0) (hcorner _ hc1)
  let t : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have ht : t ∈ Ioo (0:Interval) 1 := by
    constructor
    · change (0:ℝ) < 1/2
      norm_num
    · change (1/2:ℝ) < 1
      norm_num
  exact Set.disjoint_left.mp hfree (hqin (Set.mem_image_of_mem q ht))
    (Or.inl (hqf (mem_range_self t)))

private theorem actualInnermostOriginalTwoSideDiskClearance_of_strict_step
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (D : ActualMarkedTwoSideDisk M a b)
    (hcontact : D.firstCorner ∈ ArcSurgery.crossings M a b ∨
      D.secondCorner ∈ ArcSurgery.crossings M a b)
    (hstep : ∀ B : ActualMarkedTwoSideDisk M a b,
      ((a.val.image ∪ b.val.image) ∩ B.openInterior).Nonempty →
      ∃ F : ActualMarkedTwoSideDisk M a b,
        range F.disk ⊆ range B.disk ∧
        (∃ z ∈ ({B.firstCorner,B.secondCorner}:Set S), z ∉ range F.disk) ∧
        (F.firstCorner ∈ ArcSurgery.crossings M a b ∨
          F.secondCorner ∈ ArcSurgery.crossings M a b)) :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      range B.disk ⊆ range D.disk ∧
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner ∈ ArcSurgery.crossings M a b ∨
        B.secondCorner ∈ ArcSurgery.crossings M a b) := by
  classical
  let C : Set S := a.val.image ∩ b.val.image
  have hCf : C.Finite :=
    (hfinite.union (Set.toFinite ({a.val.map 0,a.val.map 1}:Set S))).subset (by
      intro x hx
      by_cases hxmark : x ∈ M.cover.branch
      · right
        obtain ⟨t,ht⟩ := hx.1
        rcases a.val.marked_only_at_ends t (ht ▸ hxmark) with ht0 | ht1
        · exact Or.inl ((congrArg a.val.map ht0).symm.trans ht).symm
        · exact Or.inr ((congrArg a.val.map ht1).symm.trans ht).symm
      · exact Or.inl ⟨⟨hx.1,hxmark⟩,hx.2,hxmark⟩)
  let energy (B : ActualMarkedTwoSideDisk M a b) : ℕ :=
    (C ∩ range B.disk).ncard
  let P : ℕ → Prop := fun n =>
    ∃ B : ActualMarkedTwoSideDisk M a b,
      range B.disk ⊆ range D.disk ∧
      (B.firstCorner ∈ ArcSurgery.crossings M a b ∨
        B.secondCorner ∈ ArcSurgery.crossings M a b) ∧ energy B = n
  have hex : ∃ n, P n := ⟨energy D,D,Subset.rfl,hcontact,rfl⟩
  obtain ⟨B,hBD,hBcontact,hBenergy⟩ := Nat.find_spec hex
  refine ⟨B,hBD,?_,hBcontact⟩
  apply Set.disjoint_left.mpr
  intro x hxDisk hxArc
  obtain ⟨F,hFB,⟨z,hzcorner,hznotF⟩,hFcontact⟩ :=
    hstep B ⟨x,hxArc,hxDisk⟩
  have hzC : z ∈ C := by
    rcases mem_insert_iff.mp hzcorner with hz | hz
    · exact ⟨B.first_on_curve ⟨0,B.first_zero.trans hz.symm⟩,
        B.second_on_curve ⟨0,B.second_zero.trans hz.symm⟩⟩
    · have hz' := mem_singleton_iff.mp hz
      exact ⟨B.first_on_curve ⟨1,B.first_one.trans hz'.symm⟩,
        B.second_on_curve ⟨1,B.second_one.trans hz'.symm⟩⟩
  have hzB : z ∈ range B.disk := image_subset_range _ _ (B.boundary_eq.symm ▸
    (show z ∈ range B.firstSide ∪ range B.secondSide from
      Or.inl (by
        rcases mem_insert_iff.mp hzcorner with hz | hz
        · exact ⟨0,B.first_zero.trans hz.symm⟩
        · exact ⟨1,B.first_one.trans (mem_singleton_iff.mp hz).symm⟩)))
  have hlt : energy F < energy B := Set.ncard_lt_ncard
    (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_inter_right C hFB,by
      intro he
      have hzF : z ∈ C ∩ range F.disk := he.symm ▸ (show z ∈ C ∩ range B.disk from ⟨hzC,hzB⟩)
      exact hznotF hzF.2⟩) (hCf.inter_of_left _)
  exact Nat.find_min hex (hlt.trans_eq hBenergy)
    ⟨F,hFB.trans hBD,hFcontact,rfl⟩

private theorem actualInnermostOriginalTwoSideDiskClearance
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (_htransverse : ∀ p ∈ ArcSurgery.crossings M a b,
      ArcSurgery.CrossesInDisk M a b p)
    (D : ActualMarkedTwoSideDisk M a b)
    (hcontact : D.firstCorner ∈ ArcSurgery.crossings M a b ∨
      D.secondCorner ∈ ArcSurgery.crossings M a b) :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      range B.disk ⊆ range D.disk ∧
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner ∈ ArcSurgery.crossings M a b ∨
        B.secondCorner ∈ ArcSurgery.crossings M a b) := by
  classical
  have actual_selected_intrusion_crosscut_produces_smaller_disk
      (a b : EssentialMarkedArc M) (B : ActualMarkedTwoSideDisk M a b)
      (hbranch : Disjoint B.openInterior (M.cover.branch : Set S))
      (q : C(Interval,S)) (hq : IsEmbedding q) (hqa : range q ⊆ a.val.image)
      (hq0 : q 0 ∈ range B.secondSide) (hq1 : q 1 ∈ range B.secondSide)
      (hqin : q '' Ioo (0:Interval) 1 ⊆ B.openInterior)
      (hnotboth : ¬ (q 0 ∈ ({B.firstCorner,B.secondCorner}:Set S) ∧
        q 1 ∈ ({B.firstCorner,B.secondCorner}:Set S))) :
      ∃ D : ActualMarkedTwoSideDisk M a b,
        range D.disk ⊆ range B.disk ∧
        (∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S),x ∉ range D.disk) ∧
        (D.firstCorner ∈ ArcSurgery.crossings M a b ∨
          D.secondCorner ∈ ArcSurgery.crossings M a b) := by
    classical
    let : T2Space S := M.sphere.symm.t2Space
    let : CompactSpace S := M.sphere.symm.compactSpace
    let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Subtype.connectedSpace (isConnected_sphere
        (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
        0 (by norm_num))
    let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
    let := (actualSphereSmoothAtlas M).charts
    let := (actualSphereSmoothAtlas M).manifold
    let : ClosedSurface S := {}
    have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
      rw [← B.boundary_eq]
      apply Set.disjoint_left.mpr
      rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
      have huv := B.disk_embedded.injective (hux.trans hvx.symm)
      subst v
      have hu' : ‖u.val‖ < 1 := by
        simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using hu
      have hv' : ‖u.val‖ = 1 := by
        simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hv
      linarith
    obtain ⟨r,hr⟩ := hq0
    obtain ⟨s,hs⟩ := hq1
    have hrs : r ≠ s := by
      intro he
      have h01 : (0:Interval) = 1 := hq.injective (hr.symm.trans ((congrArg B.secondSide he).trans hs))
      exact zero_ne_one h01
    let affine : Interval → Interval := fun t =>
      ⟨(1-t.val)*r.val+t.val*s.val,by
        constructor <;> nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,
          s.property.1,s.property.2]⟩
    let g : C(Interval,S) := ⟨B.secondSide ∘ affine,B.secondSide.continuous.comp (by fun_prop)⟩
    have hg0 : g 0 = q 0 := by simpa [g,affine] using hr
    have hg1 : g 1 = q 1 := by simpa [g,affine] using hs
    have hgi : Function.Injective g := by
      intro t u he
      have hv := congrArg Subtype.val (B.second_embedded.injective he)
      apply Subtype.ext
      have hne : r.val ≠ s.val := fun he => hrs (Subtype.ext he)
      dsimp [affine] at hv
      have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact sub_eq_zero.mp hz
      · exact False.elim (hne (sub_eq_zero.mp hz).symm)
    have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
    have hgg : range g ⊆ range B.secondSide := by
      rintro x ⟨t,rfl⟩
      exact mem_range_self (affine t)
    have hcross (t u : Interval) (he : q t = g u) :
        (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
      by_cases ht0 : t=0
      · exact Or.inl ⟨ht0,hgi (by rw [hg0,← he,ht0])⟩
      by_cases ht1 : t=1
      · exact Or.inr ⟨ht1,hgi (by rw [hg1,← he,ht1])⟩
      have htI : t ∈ Ioo (0:Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
      exact False.elim (Set.disjoint_left.mp hfree (hqin ⟨t,htI,rfl⟩)
        (Or.inr (he.symm ▸ hgg (mem_range_self u))))
    obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs q g hq.injective hgi hg0.symm hg1.symm hcross
    have hcB : c.image ⊆ range B.disk := by
      rw [hc]
      apply union_subset
      · rintro x ⟨t,rfl⟩
        by_cases ht0 : t=0
        · subst t
          exact image_subset_range _ _ (B.boundary_eq.symm ▸
            (show q 0 ∈ range B.firstSide ∪ range B.secondSide from Or.inr ⟨r,hr⟩))
        by_cases ht1 : t=1
        · subst t
          exact image_subset_range _ _ (B.boundary_eq.symm ▸
            (show q 1 ∈ range B.firstSide ∪ range B.secondSide from Or.inr ⟨s,hs⟩))
        exact image_subset_range _ _ (hqin ⟨t,
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
      · exact fun x hx => image_subset_range _ _ (B.boundary_eq.symm ▸
          (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hgg hx)))
    obtain ⟨d,hd,hdb,hdB⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
      c B.disk B.disk_embedded hcB
    have hdin : d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ B.openInterior := by
      change d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
        B.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
      rw [← CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq B.disk B.disk_embedded]
      exact (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen d hd).subset_interior_iff.mpr
        ((image_subset_range _ _).trans hdB)
    have hmarks : ∀ x ∈ range d, x ∈ M.cover.branch → x ∈ ({q 0,q 1}:Set S) := by
      intro x hx hxmark
      obtain ⟨u,hu⟩ := hx
      have hnorm : ‖u.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
      have hne : ¬ ‖u.val‖ < 1 := by
        intro h
        have hxU := hdin ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right] using h,hu⟩
        exact Set.disjoint_left.mp hbranch hxU hxmark
      have hxc : x ∈ c.image := hdb ▸ (show x ∈ d ''
          {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} from
        ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
          using le_antisymm hnorm (not_lt.mp hne),hu⟩)
      rw [hc] at hxc
      rcases hxc with ⟨t,ht⟩ | ⟨t,ht⟩
      · have htend : t=0 ∨ t=1 := by
          by_cases ht0 : t=0
          · exact Or.inl ht0
          by_cases ht1 : t=1
          · exact Or.inr ht1
          have hti : t ∈ Ioo (0:Interval) 1 :=
            ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
          exact False.elim (Set.disjoint_left.mp hbranch (hqin ⟨t,hti,rfl⟩) (ht.symm ▸ hxmark))
        rcases htend with ht0 | ht1
        · exact Or.inl ((congrArg q ht0).symm.trans ht).symm
        · exact Or.inr ((congrArg q ht1).symm.trans ht).symm
      · have hxB : x ∈ range B.disk := hdB ⟨u,hu⟩
        have hcorn := B.marks_are_corners x hxB hxmark
        have he : g t=B.secondSide 0 ∨ g t=B.secondSide 1 := by
          rcases mem_insert_iff.mp hcorn with hc0 | hc1
          · exact Or.inl (ht.trans (hc0.trans B.second_zero.symm))
          · exact Or.inr (ht.trans ((mem_singleton_iff.mp hc1).trans B.second_one.symm))
        rcases actual_embedded_side_source_endpoint B.secondSide g B.second_embedded hg hgg t he with ht0 | ht1
        · exact Or.inl ((hg0.symm.trans ((congrArg g ht0).symm.trans ht))).symm
        · exact Or.inr ((hg1.symm.trans ((congrArg g ht1).symm.trans ht))).symm
    have hsides : range q ∩ range g = {q 0,q 1} := by
      ext x
      constructor
      · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
        rcases hcross t u (ht.trans hu.symm) with ⟨ht0,_⟩ | ⟨ht1,_⟩
        · exact Or.inl ((congrArg q ht0).symm.trans ht).symm
        · exact Or.inr ((congrArg q ht1).symm.trans ht).symm
      · intro hx
        rcases mem_insert_iff.mp hx with hx | hx
        · exact hx ▸ ⟨⟨0,rfl⟩,⟨0,hg0⟩⟩
        · exact mem_singleton_iff.mp hx ▸ ⟨⟨1,rfl⟩,⟨1,hg1⟩⟩
    let D : ActualMarkedTwoSideDisk M a b := {
      firstCorner := q 0, secondCorner := q 1,
      firstSide := q, secondSide := g, first_embedded := hq, second_embedded := hg,
      first_zero := rfl,first_one := rfl,second_zero := hg0,second_one := hg1,
      first_on_curve := hqa, second_on_curve := hgg.trans B.second_on_curve,
      sides_inter := hsides,disk := d,disk_embedded := hd,boundary_eq := hdb.trans hc,
      marks_are_corners := hmarks }
    have hmissing : ∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S), x ∉ range D.disk := by
      have hn01 : ¬ (r=0 ∧ s=1) := by
        rintro ⟨rfl,rfl⟩
        apply hnotboth
        rw [← hr,← hs,B.second_zero,B.second_one]
        exact ⟨Or.inl rfl,Or.inr rfl⟩
      have hn10 : ¬ (r=1 ∧ s=0) := by
        rintro ⟨rfl,rfl⟩
        apply hnotboth
        rw [← hr,← hs,B.second_one,B.second_zero]
        exact ⟨Or.inr rfl,Or.inl rfl⟩
      have hend : ∃ v : Interval, (v=0 ∨ v=1) ∧ r≠v ∧ s≠v := by
        by_cases hr0 : r=0
        · refine ⟨1,Or.inr rfl,?_,fun hs1 => hn01 ⟨hr0,hs1⟩⟩
          rw [hr0]
          exact zero_ne_one
        by_cases hs0 : s=0
        · refine ⟨1,Or.inr rfl,fun hr1 => hn10 ⟨hr1,hs0⟩,?_⟩
          rw [hs0]
          exact zero_ne_one
        exact ⟨0,Or.inl rfl,hr0,hs0⟩
      obtain ⟨v,hv,hrv,hsv⟩ := hend
      let x : S := B.secondSide v
      have hxcorner : x ∈ ({B.firstCorner,B.secondCorner}:Set S) := by
        rcases hv with hv | hv
        · exact Or.inl ((congrArg B.secondSide hv).trans B.second_zero)
        · exact Or.inr ((congrArg B.secondSide hv).trans B.second_one)
      have hxB : x ∈ range B.firstSide ∪ range B.secondSide := Or.inr (mem_range_self v)
      have hxnotq : x ∉ range q := by
        rintro ⟨t,ht⟩
        by_cases ht0 : t=0
        · apply hrv
          apply B.second_embedded.injective
          exact hr.trans ((congrArg q ht0).symm.trans ht)
        by_cases ht1 : t=1
        · apply hsv
          apply B.second_embedded.injective
          exact hs.trans ((congrArg q ht1).symm.trans ht)
        exact Set.disjoint_left.mp hfree (ht ▸ hqin ⟨t,
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩) hxB
      have hxnotg : x ∉ range g := by
        rintro ⟨t,ht⟩
        have he : g t = B.secondSide 0 ∨ g t = B.secondSide 1 := by
          rcases hv with hv | hv
          · exact Or.inl (ht.trans (congrArg B.secondSide hv))
          · exact Or.inr (ht.trans (congrArg B.secondSide hv))
        rcases actual_embedded_side_source_endpoint B.secondSide g B.second_embedded hg hgg t he
          with ht0 | ht1
        · exact hxnotq ⟨0,hg0.symm.trans ((congrArg g ht0).symm.trans ht)⟩
        · exact hxnotq ⟨1,hg1.symm.trans ((congrArg g ht1).symm.trans ht)⟩
      have hxnotc : x ∉ c.image := by
        rw [hc]
        exact fun h => h.elim hxnotq hxnotg
      refine ⟨x,hxcorner,?_⟩
      rintro ⟨u,hu⟩
      have hnorm : ‖u.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
      have hne : ‖u.val‖ ≠ 1 := by
        intro he
        apply hxnotc
        rw [← hdb]
        exact ⟨u,by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using he,hu⟩
      have hxinside : x ∈ B.openInterior := hdin ⟨u,
        by simpa only [Set.mem_ofPred_eq,Metric.mem_ball,dist_zero_right]
          using lt_of_le_of_ne hnorm hne,hu⟩
      exact Set.disjoint_left.mp hfree hxinside hxB
    have hcontact : D.firstCorner ∈ ArcSurgery.crossings M a b ∨
        D.secondCorner ∈ ArcSurgery.crossings M a b := by
      by_cases h0mark : q 0 ∈ M.cover.branch
      · right
        have h1not : q 1 ∉ M.cover.branch := by
          intro h1mark
          exact hnotboth ⟨B.marks_are_corners _ (hcB (hc.symm ▸ Or.inl (mem_range_self 0))) h0mark,
            B.marks_are_corners _ (hcB (hc.symm ▸ Or.inl (mem_range_self 1))) h1mark⟩
        exact ⟨⟨hqa (mem_range_self 1),h1not⟩,B.second_on_curve ⟨s,hs⟩,h1not⟩
      · left
        exact ⟨⟨hqa (mem_range_self 0),h0mark⟩,B.second_on_curve ⟨r,hr⟩,h0mark⟩
    exact ⟨D,hdB,hmissing,hcontact⟩
  have hstep : ∀ B : ActualMarkedTwoSideDisk M a b,
      ((a.val.image ∪ b.val.image) ∩ B.openInterior).Nonempty →
      ∃ F : ActualMarkedTwoSideDisk M a b,
        range F.disk ⊆ range B.disk ∧
        (∃ z ∈ ({B.firstCorner,B.secondCorner}:Set S), z ∉ range F.disk) ∧
        (F.firstCorner ∈ ArcSurgery.crossings M a b ∨
          F.secondCorner ∈ ArcSurgery.crossings M a b) := by
    intro B hin
    rcases hin with ⟨x,hxa | hxb,hxB⟩
    · obtain ⟨q,hq,hqa,hq0,hq1,hqin,hnotboth⟩ :=
        actual_any_first_intrusion_crosscut M a b B ⟨x,hxa,hxB⟩
      exact actual_selected_intrusion_crosscut_produces_smaller_disk
        a b B (relative_selected_bigon_open_interior_mark_free M a b B)
        q hq hqa hq0 hq1 hqin hnotboth
    · let swap {c d : EssentialMarkedArc M} (K : ActualMarkedTwoSideDisk M c d) :
          ActualMarkedTwoSideDisk M d c := {
        firstCorner := K.firstCorner,secondCorner := K.secondCorner,
        firstSide := K.secondSide,secondSide := K.firstSide,
        first_embedded := K.second_embedded,second_embedded := K.first_embedded,
        first_zero := K.second_zero,first_one := K.second_one,
        second_zero := K.first_zero,second_one := K.first_one,
        first_on_curve := K.second_on_curve,second_on_curve := K.first_on_curve,
        sides_inter := by rw [Set.inter_comm,K.sides_inter],
        disk := K.disk,disk_embedded := K.disk_embedded,
        boundary_eq := K.boundary_eq.trans (Set.union_comm _ _),
        marks_are_corners := K.marks_are_corners }
      obtain ⟨q,hq,hqa,hq0,hq1,hqin,hnotboth⟩ :=
        actual_any_first_intrusion_crosscut M b a (swap B) ⟨x,hxb,hxB⟩
      obtain ⟨F,hsub,hmissing,hpositive⟩ :=
        actual_selected_intrusion_crosscut_produces_smaller_disk
          b a (swap B) (relative_selected_bigon_open_interior_mark_free M b a (swap B))
          q hq hqa hq0 hq1 hqin hnotboth
      refine ⟨swap F,hsub,hmissing,?_⟩
      simpa only [ArcSurgery.crossings,Set.inter_comm] using hpositive
  exact actualInnermostOriginalTwoSideDiskClearance_of_strict_step
    M a b hfinite D hcontact hstep



private theorem actualRawEndpointSeparatedProducesEntirePairClearedMarkedDisk
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a,ArcSurgery.vertex M b})
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (htransverse : ∀ p ∈ ArcSurgery.crossings M a b,ArcSurgery.CrossesInDisk M a b p)
    (hcontact : (ArcSurgery.crossings M a b).Nonempty)
    (hseparated : ∀ c : Interval,c=0 ∨ c=1 → b.val.map c∉a.val.image) :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner∈ArcSurgery.crossings M a b ∨ B.secondCorner∈ArcSurgery.crossings M a b) := by
  obtain ⟨D,hD⟩ := actualRawEndpointSeparatedProducesOriginalMarkedDisk M a b hne hc hfinite htransverse hcontact hseparated
  obtain ⟨B,_,hfree,hB⟩ := actualInnermostOriginalTwoSideDiskClearance M a b hfinite htransverse D hD
  exact ⟨B,hfree,hB⟩

end CurveComplex.HyperellipticModel
