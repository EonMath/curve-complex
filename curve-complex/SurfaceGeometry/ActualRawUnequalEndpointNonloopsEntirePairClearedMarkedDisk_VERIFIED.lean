import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualOriginalSelector
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
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



private theorem actualRawUnequalEndpointNonloopsProduceEntirePairClearedMarkedDisk
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hne : ArcSurgery.vertex M a ≠ ArcSurgery.vertex M b)
    (hc : IsArcSimplex M {ArcSurgery.vertex M a,ArcSurgery.vertex M b})
    (ha : a.val.map 0≠a.val.map 1) (hb : b.val.map 0≠b.val.map 1)
    (hendpoints : classEndpoints M (ArcSurgery.vertex M a)≠classEndpoints M (ArcSurgery.vertex M b))
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (htransverse : ∀ p ∈ ArcSurgery.crossings M a b,ArcSurgery.CrossesInDisk M a b p)
    (hcontact : (ArcSurgery.crossings M a b).Nonempty) :
    ∃ B : ActualMarkedTwoSideDisk M a b,
      Disjoint B.openInterior (a.val.image ∪ b.val.image) ∧
      (B.firstCorner∈ArcSurgery.crossings M a b ∨ B.secondCorner∈ArcSurgery.crossings M a b) := by
  classical
  obtain ⟨a₀,b₀,ha₀,hb₀,_,_,hdis⟩ := actualRawCompatiblePairRepresentatives M a b hne hc
  have hnonloop (d : EssentialMarkedArc M) (hd : d.val.map 0≠d.val.map 1) :
      ¬ (actualArcLabels M).isLoop (ArcSurgery.vertex M d) := by
    change ¬ (arcEndpoints M d).card=1
    change ¬ ({d.val.map 0,d.val.map 1} : Finset S).card=1
    simp [hd]
  have hadj : ArcAdjacent M (ArcSurgery.vertex M a) (ArcSurgery.vertex M b) :=
    ⟨hne,hnonloop a ha,hnonloop b hb,hendpoints,a₀,b₀,ha₀,hb₀,hdis⟩
  obtain ⟨p,hp⟩ := hcontact
  obtain ⟨f,g,u,v,hf,hg,hfa,hgb,hf0,hg0,hf1,hg1,huv,hinter,hvcross,hucontact,
    hu,hv,α,β,hα,hβ,hhom⟩ := actual_adjacent_original_subpaths_punctured_homotopic
    M a b hadj hfinite htransverse p hp
  obtain ⟨D,hDf,hDg,hDu,hDv⟩ := actualOriginalPuncturedSidesDiskRealization
    M a b f g u v hf hg hfa hgb hf0 hg0 hf1 hg1 huv hinter hu hv α β hα hβ hhom
  have hDcontact : D.firstCorner∈crossings M a b ∨ D.secondCorner∈crossings M a b :=
    Or.inr (hDv.symm ▸ hvcross)
  obtain ⟨B,_,hfree,hB⟩ := actualInnermostOriginalTwoSideDiskClearance M a b hfinite htransverse D hDcontact
  exact ⟨B,hfree,hB⟩

end CurveComplex.HyperellipticModel
