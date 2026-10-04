import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualJordanDiskTools
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import Mathlib.Analysis.Convex.Contractible
import CurveComplexGenusTwo.Filtration.Geometry.ActualPuncturedJordanConversion
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroRawSupportedCrosscutMove
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroDiskBigonChartProducer
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteInteriorAxisFraming
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedArcReverse
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroEmptyDiskCleanSides
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopPrefixParameters
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopPaddedRemainder
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopBaseVanishingTracks
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.NonloopClosedPieceDescent
import CurveComplexGenusTwo.Topology.IntersectionParity.EmptyDiskSidesStatement
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedTwoSideDisk
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingAfterClosedReplacement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
set_option maxHeartbeats 4000000
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_retained_nonloop_jordan_region_produces_supporting_disk
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a))
    (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1)
    (g : C(Interval,S)) (hg : IsEmbedding g)
    (hg0 : g 0=a.val.map 0)
    (hg1 : g 1=a.val.map (projIcc 0 1 zero_le_one hi))
    (hgmeet : range g ∩ a.val.image = {a.val.map 0,g 1})
    (Ω : Set S) (hΩne : Ω.Nonempty) (hΩ : IsConnected Ω)
    (hΩfree : Ω ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ)
    (hΩmax : ∀ V : Set S, IsConnected V → Ω ⊆ V →
      V ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ → V=Ω)
    (hfrontier : frontier Ω = ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)
    (hΩmarks : Disjoint Ω (M.cover.branch : Set S)) :
    ∃ disk : C(Metric.closedBall (0 : Plane) 1,S), IsEmbedding disk ∧
      disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} =
        ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g ∧
      disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}=Ω := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : ClosedSurface S := {}
  have embedded_side_isArcBetween (f : C(Interval,Plane))
      (hf : IsEmbedding f) : IsArcBetween (range f) (f 0) (f 1) := by
    let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
    have hfc : Continuous fc := f.continuous.comp continuous_projIcc
    have he (t : Interval) : fc t = f t := by
      simp [fc,Set.projIcc_of_mem zero_le_one t.property]
    refine ⟨fc,hfc.continuousOn,?_,?_,he 0,he 1⟩
    · intro t ht u hu h
      exact congrArg Subtype.val (hf.injective (by
        simpa only [← he] using h : f ⟨t,ht⟩ = f ⟨u,hu⟩))
    · ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
      · rintro ⟨t,rfl⟩
        exact ⟨t,t.property,he t⟩
  
  have hActualPuncturedCorePath (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1) :
      ∃ (hp : a.val.map 0 ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ)
        (hq : a.val.map (projIcc 0 1 zero_le_one hi) ∈ ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ),
      ∃ γ : Path (⟨a.val.map 0,hp⟩ : ↑(((M.cover.branch : Set S) \ {a.val.map 0})ᶜ))
          ⟨a.val.map (projIcc 0 1 zero_le_one hi),hq⟩,
        IsEmbedding (fun t => (γ t:S)) ∧
        range (fun t => (γ t:S)) = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi := by
    let X : Set S := ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ
    let q : Interval → Interval := fun t => ⟨hi*(t:ℝ),
      ⟨mul_nonneg hhi0.le t.property.1,
        (mul_le_of_le_one_right hhi0.le t.property.2).trans hhi1.le⟩⟩
    have hqcont : Continuous q := by dsimp [q]; fun_prop
    have hX (t : Interval) : a.val.map (q t) ∈ X := by
      rintro ⟨hm,hn⟩
      rcases a.val.marked_only_at_ends (q t) hm with he | he
      · exact hn (congrArg a.val.map he)
      · have hh : hi*(t:ℝ)=1 := congrArg Subtype.val he
        have hle := mul_le_of_le_one_right hhi0.le t.property.2
        linarith
    let c : C(Interval,X) := ⟨fun t => ⟨a.val.map (q t),hX t⟩,
      (a.val.continuous.comp hqcont).subtype_mk _⟩
    have hp : a.val.map 0 ∈ X := by simp [X]
    have hq0 : q 0=0 := by apply Subtype.ext; dsimp [q]; norm_num
    have hq1 : q 1=projIcc 0 1 zero_le_one hi := by
      apply Subtype.ext
      rw [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi1.le⟩]
      dsimp [q]; norm_num
    have hq : a.val.map (projIcc 0 1 zero_le_one hi) ∈ X := hq1 ▸ hX 1
    let γ : Path (⟨a.val.map 0,hp⟩ : X) ⟨a.val.map (projIcc 0 1 zero_le_one hi),hq⟩ :=
      ⟨c,Subtype.ext (congrArg a.val.map hq0),Subtype.ext (congrArg a.val.map hq1)⟩
    have hc : IsEmbedding (fun t => (γ t:S)) :=
      ((a.val.continuous.comp hqcont).isClosedEmbedding (by
        intro t u he
        have hh := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩ he
        apply Subtype.ext
        exact mul_left_cancel₀ (ne_of_gt hhi0) (congrArg Subtype.val hh))).isEmbedding
    refine ⟨hp,hq,γ,hc,?_⟩
    apply Subset.antisymm
    · rintro y ⟨t,rfl⟩
      refine ⟨hi*(t:ℝ),⟨mul_nonneg hhi0.le t.property.1,
        mul_le_of_le_one_right hhi0.le t.property.2⟩,?_⟩
      rw [Function.comp_apply,projIcc_of_mem zero_le_one (q t).property]
      rfl
    · rintro y ⟨x,hx,rfl⟩
      let tx : Interval := ⟨x/hi,⟨div_nonneg hx.1 hhi0.le,(div_le_one hhi0).mpr hx.2⟩⟩
      refine ⟨tx,?_⟩
      change a.val.map (q tx)=a.val.map (projIcc 0 1 zero_le_one x)
      congr 1; apply Subtype.ext
      rw [projIcc_of_mem zero_le_one ⟨hx.1,hx.2.trans hhi1.le⟩]
      change hi*(x/hi)=x
      field_simp
  have hPlanarJordanDisk (C : Set Plane) (hC : Schoenflies.IsJordanCurve C) :
      ∃ d : C(Metric.closedBall (0 : Plane) 1,Plane), IsEmbedding d ∧
        d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=C ∧
        d '' {x | x.val ∈ Metric.ball (0 : Plane) 1}=Schoenflies.inside C := by
    classical
    obtain ⟨square,hSquare,hBoundary⟩ := exists_embedded_square_disc_of_jordan hC
    obtain ⟨h,hi,hcl,hfront⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Plane.convex_closedSquare 0 1)
      (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
      (Plane.isBounded_closedSquare 0 1)
    have hcl' : h '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
      simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hcl
    have hfront' : h '' Schoenflies.modelCurve = Metric.sphere (0 : Plane) 1 := by
      simpa only [← Schoenflies.modelCurve_eq_frontier] using hfront
    let e : Plane.closedSquare 0 1 ≃ₜ Metric.closedBall (0 : Plane) 1 :=
      (h.image (Plane.closedSquare 0 1)).trans (Homeomorph.setCongr hcl')
    have he (x : Plane.closedSquare 0 1) : (e x).val = h x.val := rfl
    have heB : e.symm '' {x : Metric.closedBall (0 : Plane) 1 | x.val ∈ Metric.sphere (0 : Plane) 1} =
        {x : Plane.closedSquare 0 1 | x.val ∈ Schoenflies.modelCurve} := by
      ext x
      constructor
      · rintro ⟨y,hy,hxy⟩
        have hy' : (e x).val ∈ Metric.sphere (0 : Plane) 1 := by
          rw [←hxy,e.apply_symm_apply]; exact hy
        rw [he,←hfront'] at hy'
        obtain ⟨z,hz,hzx⟩ := hy'
        change x.val ∈ Schoenflies.modelCurve
        rw [←h.injective hzx]
        exact hz
      · intro hx
        refine ⟨e x,?_,e.symm_apply_apply x⟩
        change (e x).val ∈ Metric.sphere (0 : Plane) 1
        rw [he,←hfront']
        exact Set.mem_image_of_mem h hx
    let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
      ⟨fun x => square (e.symm x),square.continuous.comp e.symm.continuous⟩
    have hd : Topology.IsEmbedding d := hSquare.comp e.symm.isEmbedding
    have hdB : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = C := by
      change (square ∘ e.symm) '' _ = C
      rw [Set.image_comp,heB]
      exact hBoundary
    have hrange : range d=Schoenflies.inside C ∪ C :=
      CurveComplex.embedded_disc_range_eq_closed_inside d hd C hC hdB
    refine ⟨d,hd,hdB,?_⟩
    apply Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      have hyrange : d x ∈ range d := mem_range_self x
      rw [hrange] at hyrange
      rcases hyrange with hy | hy
      · exact hy
      · obtain ⟨z,hz,he⟩ := hdB.symm ▸ hy
        have hxz : z=x := hd.injective he
        subst z
        have hxeq : dist x.val 0=(1:ℝ) := hz
        exact False.elim (ne_of_lt hx hxeq)
    · intro y hy
      have hyrange : y ∈ range d := hrange.symm ▸ Or.inl hy
      obtain ⟨x,hx⟩ := hyrange
      refine ⟨x,?_,hx⟩
      have hxle : dist x.val 0 ≤ (1:ℝ) := x.property
      apply lt_of_le_of_ne hxle
      intro he
      have hyC : y ∈ C := hdB ▸ ⟨x,he,hx⟩
      exact Set.disjoint_right.mp (disjoint_curve_inside C) hy hyC
  have hRetainedJordanRegionDisk (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1)
      (g : C(Interval,S)) (hg : IsEmbedding g) (hg0 : g 0=a.val.map 0)
      (hg1 : g 1=a.val.map (projIcc 0 1 zero_le_one hi))
      (hgmeet : range g ∩ a.val.image = {a.val.map 0,g 1})
      (Ω : Set S) (hΩne : Ω.Nonempty) (hΩ : IsConnected Ω)
      (hΩfree : Ω ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ)
      (hΩmax : ∀ V : Set S, IsConnected V → Ω ⊆ V →
        V ⊆ (((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)ᶜ → V=Ω)
      (hfrontier : frontier Ω = ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g)
      (hΩmarks : Disjoint Ω (M.cover.branch : Set S)) :
      ∃ disk : C(Metric.closedBall (0 : Plane) 1,S), IsEmbedding disk ∧
        disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} =
          ((a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi) ∪ range g ∧
        disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}=Ω := by
    obtain ⟨hp,hz,core,hcore,hcoreRange⟩ := hActualPuncturedCorePath hi hhi0 hhi1
    let f : C(Interval,S) := ⟨fun t => (core t:S),continuous_subtype_val.comp core.continuous⟩
    have hf0 : f 0=a.val.map 0 := congrArg Subtype.val core.source
    have hf1 : f 1=a.val.map (projIcc 0 1 zero_le_one hi) := congrArg Subtype.val core.target
    have hfRange : range f=(a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi := hcoreRange
    let Γ : Set S := range f ∪ range g
    let w := a.val.map 1
    have hwΓ : w ∉ Γ := by
      intro hw
      have hinj := NonLoopArc.injective ⟨a.val,actualRepresentative_nonloop M a ha⟩
      rcases hw with hw | hw
      · obtain ⟨t,ht,he⟩ := hfRange ▸ hw
        have hh := congrArg Subtype.val (hinj he)
        have ht1 : t=1 := by
          simpa only [Function.comp_apply,projIcc_of_mem zero_le_one ⟨ht.1,ht.2.trans hhi1.le⟩,
            show ((1:Interval):ℝ)=1 from rfl] using hh
        exact not_le_of_gt hhi1 (ht1 ▸ ht.2)
      · have he : w ∈ ({a.val.map 0,g 1} : Set S) :=
          hgmeet ▸ (show w ∈ range g ∩ a.val.image from ⟨hw,mem_range_self 1⟩)
        rcases mem_insert_iff.mp he with he | he
        · have hh := congrArg Subtype.val (hinj he)
          norm_num at hh
        · have hh := congrArg Subtype.val (hinj ((mem_singleton_iff.mp he).trans hg1))
          have hh' : (1:ℝ)=hi := by
            simpa only [projIcc_of_mem zero_le_one ⟨hhi0.le,hhi1.le⟩,
              show ((1:Interval):ℝ)=1 from rfl] using hh
          linarith
    have hwΩ : w ∉ Ω := fun hw => Set.disjoint_left.mp hΩmarks hw a.val.end_marked
    let e := M.puncturedPlane w
    have hPlaneRange : range (M.planeToSphere w)={w}ᶜ := by
      apply Subset.antisymm
      · rintro y ⟨x,rfl⟩
        exact M.planeToSphere_ne_p w x
      · intro y hy
        refine ⟨e ⟨y,hy⟩,?_⟩
        exact congrArg Subtype.val (e.symm_apply_apply ⟨y,hy⟩)
    let en : OpenPartialHomeomorph S Plane :=
      ((M.planeToSphere_isOpenEmbedding w).toOpenPartialHomeomorph (M.planeToSphere w)).symm
    have hensource : en.source={w}ᶜ := by
      simp only [en,OpenPartialHomeomorph.symm_source,
        IsOpenEmbedding.toOpenPartialHomeomorph_target,hPlaneRange]
    have hentarget : en.target=univ := by
      simp [en]
    have hΓsource : Γ ⊆ en.source := by
      intro y hy
      rw [hensource]
      intro he
      exact hwΓ (he ▸ hy)
    have hen (y : S) (hy : y ≠ w) : en y=e ⟨y,hy⟩ := by
      have he : M.planeToSphere w (e ⟨y,hy⟩)=y := congrArg Subtype.val (e.symm_apply_apply _)
      exact (congrArg en he.symm).trans
        ((M.planeToSphere_isOpenEmbedding w).toOpenPartialHomeomorph_left_inv _)
    let F : C(Interval,Plane) := ⟨fun t => e ⟨f t,fun he => hwΓ (he ▸ Or.inl (mem_range_self t))⟩,by fun_prop⟩
    let G : C(Interval,Plane) := ⟨fun t => e ⟨g t,fun he => hwΓ (he ▸ Or.inr (mem_range_self t))⟩,by fun_prop⟩
    have hF : IsEmbedding F := (F.continuous.isClosedEmbedding (by
      intro t u he
      have hh : f t=f u := congrArg (Subtype.val : {z : S // z ≠ w} → S) (e.injective he)
      exact hcore.injective hh)).isEmbedding
    have hG : IsEmbedding G := (G.continuous.isClosedEmbedding (by
      intro t u he
      exact hg.injective (congrArg Subtype.val (e.injective he)))).isEmbedding
    have hF0 : F 0=G 0 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf0.trans hg0.symm
    have hF1 : F 1=G 1 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf1.trans hg1.symm
    have hfa : range f ⊆ a.val.image := by
      rw [hfRange]
      rintro y ⟨t,ht,rfl⟩
      exact mem_range_self _
    have hinter : range f ∩ range g={a.val.map 0,g 1} := by
      apply Subset.antisymm
      · intro y hy
        exact hgmeet ▸ (show y ∈ range g ∩ a.val.image from ⟨hy.2,hfa hy.1⟩)
      · intro y hy
        rcases mem_insert_iff.mp hy with he | he
        · exact ⟨⟨0,hf0.trans he.symm⟩,⟨0,hg0.trans he.symm⟩⟩
        · exact ⟨⟨1,hf1.trans (hg1.symm.trans (mem_singleton_iff.mp he).symm)⟩,
            ⟨1,(mem_singleton_iff.mp he).symm⟩⟩
    have hC : IsJordanCurve (range F ∪ range G) :=
      IsJordanCurve.of_two_arcs (embedded_side_isArcBetween F hF)
        (by rw [hF0,hF1]; exact (embedded_side_isArcBetween G hG).reverse) (by
          rintro y ⟨t,ht⟩ ⟨u,hu⟩
          have he : f t=g u := congrArg Subtype.val (e.injective (ht.trans hu.symm))
          have hm : f t ∈ ({a.val.map 0,g 1} : Set S) :=
            hinter ▸ (show f t ∈ range f ∩ range g from ⟨mem_range_self t,⟨u,he.symm⟩⟩)
          rcases mem_insert_iff.mp hm with hm | hm
          · have ht0 : t=0 := hcore.injective (hm.trans hf0.symm)
            subst t
            exact Or.inl ht.symm
          · have ht1 : t=1 := hcore.injective ((mem_singleton_iff.mp hm).trans (hg1.trans hf1.symm))
            subst t
            exact Or.inr ht.symm)
    have hCimage : en '' Γ=range F ∪ range G := by
      rw [image_union]
      congr 1
      · rw [← range_comp]
        exact congrArg range (funext (fun t => hen (f t) (fun he => hwΓ (he ▸ Or.inl (mem_range_self t)))))
      · rw [← range_comp]
        exact congrArg range (funext (fun t => hen (g t) (fun he => hwΓ (he ▸ Or.inr (mem_range_self t)))))
    have hΓclosed : IsClosed Γ := by
      have hfc : IsClosed (range f) := by
        simpa only [image_univ] using (isCompact_univ.image f.continuous).isClosed
      have hgc : IsClosed (range g) := by
        simpa only [image_univ] using (isCompact_univ.image g.continuous).isClosed
      exact hfc.union hgc
    letI : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
    have hΩopen : IsOpen Ω := complementComponent_open hΓclosed
      ⟨hΩne,hΩ,by simpa only [Γ,hfRange] using hΩfree,
        by simpa only [Γ,hfRange] using hΩmax⟩
    have hclosure : closure Ω ⊆ en.source := by
      rw [hensource,closure_eq_self_union_frontier,hfrontier,← hfRange]
      rintro y (hy | hy) he
      · exact hwΩ (he ▸ hy)
      · exact hwΓ (he ▸ hy)
    let Ωplane := en '' Ω
    have hΩplaneOpen : IsOpen Ωplane := en.isOpen_image_of_subset_source hΩopen
      (subset_closure.trans hclosure)
    have hΩplaneConn : IsConnected Ωplane := hΩ.image en
      (en.continuousOn.mono (subset_closure.trans hclosure))
    have hΩplaneBounded : Bornology.IsBounded Ωplane :=
      ((isClosed_closure.isCompact : IsCompact (closure Ω)).image_of_continuousOn
        (en.continuousOn.mono hclosure)).isBounded.subset (image_mono subset_closure)
    have hΩIsImage : en.IsImage Ω Ωplane := by
      intro y hy
      constructor
      · rintro ⟨x,hx,he⟩
        exact en.injOn (hclosure (subset_closure hx)) hy he ▸ hx
      · intro hyΩ
        exact ⟨y,hyΩ,rfl⟩
    have hΩplaneFrontier : frontier Ωplane=range F ∪ range G := by
      have hh := hΩIsImage.frontier.image_eq
      have hfrSource : frontier Ω ⊆ en.source := frontier_subset_closure.trans hclosure
      rw [inter_eq_right.mpr hfrSource,hentarget,univ_inter,hfrontier,← hfRange,hCimage] at hh
      exact hh.symm
    have hΩinside : Ωplane=inside (range F ∪ range G) :=
      bounded_jordan_frontier_region_eq_inside hC hΩplaneOpen hΩplaneConn hΩplaneBounded hΩplaneFrontier
    obtain ⟨d,hd,hdB,hdI⟩ := hPlanarJordanDisk (range F ∪ range G) hC
    let disk : C(Metric.closedBall (0 : Plane) 1,S) :=
      ⟨fun x => M.planeToSphere w (d x),(M.planeToSphere_isOpenEmbedding w).continuous.comp d.continuous⟩
    have hDisk : IsEmbedding disk := (M.planeToSphere_isOpenEmbedding w).isEmbedding.comp hd
    have hcancel (K : Set S) (hK : K ⊆ en.source) : en.symm '' (en '' K)=K := by
      apply Subset.antisymm
      · rintro y ⟨z,⟨x,hx,rfl⟩,rfl⟩
        rw [en.left_inv (hK hx)]
        exact hx
      · intro y hy
        exact ⟨en y,⟨y,hy,rfl⟩,en.left_inv (hK hy)⟩
    refine ⟨disk,hDisk,?_,?_⟩
    · change (en.symm ∘ d) '' _ = _
      rw [image_comp,hdB,← hCimage,hcancel Γ hΓsource]
      exact congrArg (fun K : Set S => K ∪ range g) hfRange
    · change (en.symm ∘ d) '' _ = _
      rw [image_comp,hdI,← hΩinside]
      exact hcancel Ω (subset_closure.trans hclosure)
  exact hRetainedJordanRegionDisk hi hhi0 hhi1 g hg hg0 hg1 hgmeet Ω hΩne hΩ hΩfree hΩmax hfrontier hΩmarks

end CurveComplex.HyperellipticModel
