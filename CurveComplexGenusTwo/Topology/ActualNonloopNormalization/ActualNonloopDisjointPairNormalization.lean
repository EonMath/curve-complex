import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Intersection.FiniteCount
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort

import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import CurveComplexGenusTwo.Topology.Smoothing.UniformActualGerms
import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.LocalSquareLiftProof

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.FiniteStarGeometry
set_option maxHeartbeats 5000000
variable {S B : Type} [TopologicalSpace S] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  (M : HyperellipticModel S B)

/-- Source Lemma 5.3 in topological canonical-map form. Two actual non-loop
arcs with disjoint interiors can be replaced in their literal marked classes
by a pair with disjoint interiors whose literal full inverse-image essential
curves are topologically transverse. No smooth atlas is prescribed. -/
theorem actual_nonloop_disjoint_pair_transverse_full_preimages
    (a b : NonLoopArc M)
    (hd : Disjoint (arcInterior M a.toEssential) (arcInterior M b.toEssential)) :
    ∃ p q : NonLoopArc M,
      Quotient.mk (nonLoopArcSetoid M) p = Quotient.mk (nonLoopArcSetoid M) a ∧
      Quotient.mk (nonLoopArcSetoid M) q = Quotient.mk (nonLoopArcSetoid M) b ∧
      Disjoint (arcInterior M p.toEssential) (arcInterior M q.toEssential) ∧
      Transverse (nonloop_arc_essential_preimage M p).val
        (nonloop_arc_essential_preimage M q).val := by
  classical
  have hshared : a.image ∩ b.image ⊆ (M.cover.branch : Set B) := by
    intro z hz
    by_contra hmark
    exact Set.disjoint_left.mp hd ⟨hz.1, hmark⟩ ⟨hz.2, hmark⟩
  have hbranchInjective : Set.InjOn M.cover.projection
      (M.cover.projection ⁻¹' (M.cover.branch : Set B)) := by
    intro x hx y _ hxy
    obtain ⟨w, _, huniq⟩ := M.cover.branch_fiber_unique hx
    exact (huniq x rfl).trans (huniq y hxy.symm).symm
  have hramFinite :
      (M.cover.projection ⁻¹' (M.cover.branch : Set B)).Finite :=
    M.cover.branch.finite_toSet.preimage hbranchInjective
  have hfinite :
      ((nonloop_arc_essential_preimage M a).val.image ∩
        (nonloop_arc_essential_preimage M b).val.image).Finite := by
    rw [nonloop_arc_essential_preimage_image,
      nonloop_arc_essential_preimage_image, ← Set.preimage_inter]
    exact hramFinite.subset (Set.preimage_mono hshared)
  refine ⟨a, b, rfl, rfl, hd, hfinite, ?_⟩
  intro w hw
  have hπa : M.cover.projection w ∈ a.image := by
    simpa only [nonloop_arc_essential_preimage_image, Set.mem_preimage] using hw.1
  have hπb : M.cover.projection w ∈ b.image := by
    simpa only [nonloop_arc_essential_preimage_image, Set.mem_preimage] using hw.2
  have hπbranch : M.cover.projection w ∈ M.cover.branch :=
    hshared ⟨hπa, hπb⟩
  have haend : M.cover.projection w ∈
      ({a.val.map 0, a.val.map 1} : Set B) := by
    have hz : M.cover.projection w ∈ a.val.image ∩ (M.cover.branch : Set B) := ⟨hπa, hπbranch⟩
    rw [a.image_inter_branch] at hz
    exact hz
  have hbend : M.cover.projection w ∈
      ({b.val.map 0, b.val.map 1} : Set B) := by
    have hz : M.cover.projection w ∈ b.val.image ∩ (M.cover.branch : Set B) := ⟨hπb, hπbranch⟩
    rw [b.image_inter_branch] at hz
    exact hz
  let p : B := M.cover.projection w
  let c := M.cover.branch_chart w hπbranch
  let P := ArcFinitePosition.planeComplexLinearEquiv
  let e : OpenPartialHomeomorph B Plane :=
    c.downstairs.trans P.symm.toHomeomorph.toOpenPartialHomeomorph
  have hep : p ∈ e.source := by simpa [e,p] using c.downstairs_mem
  have hezero : e p = 0 := by
    change P.symm (c.downstairs p) = 0
    rw [c.downstairs_center, P.symm.map_zero]
  let d : Bool → NonLoopArc M := fun i => if i then b else a
  let ds : Bool → EssentialMarkedArc M := fun i => (d i).toEssential
  have hdFamily : ∀ i j : Bool, i ≠ j →
      Disjoint (arcInterior M (ds i)) (arcInterior M (ds j)) := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hd
    · exact hd.symm
    · exact (hij rfl).elim
  have hEnd : ∀ i : Bool, ∃ k : Bool,
      (if k then (d i).val.map 1 else (d i).val.map 0) = p := by
    intro i
    have hi : p ∈ ({(d i).val.map 0, (d i).val.map 1} : Set B) := by
      cases i
      · exact haend
      · exact hbend
    rcases Set.mem_insert_iff.mp hi with h | h
    · exact ⟨false, h.symm⟩
    · exact ⟨true, (Set.mem_singleton_iff.mp h).symm⟩
  choose k hk using hEnd
  obtain ⟨r,hr,hrhalf,hstart,hfinish⟩ :=
    uniform_actual_endpoint_germs M Bool ds p e.source e.open_source hep
  have hr1 : r < 1 := by linarith
  let η : Bool → Interval → B := fun i =>
    (ds i).val.map ∘ endpointGermParameter (k i) r hr hr1
  have hηsource : ∀ i t, η i t ∈ e.source := by
    intro i t
    have hki := hk i
    cases h : k i
    · have hm : (ds i).val.map 0 = p := by simpa [ds,h,NonLoopArc.toEssential] using hki
      apply hstart i hm
      simp only [endpointGermParameter,h,Bool.false_eq_true,ite_false]
      nlinarith [t.property.2]
    · have hm : (ds i).val.map 1 = p := by simpa [ds,h,NonLoopArc.toEssential] using hki
      apply hfinish i hm
      simp only [endpointGermParameter,h,ite_true]
      nlinarith [t.property.2]
  have hηzero : ∀ i, η i 0 = p := by
    intro i
    cases h : k i <;> simpa [η,endpointGermParameter,h,ds,NonLoopArc.toEssential] using hk i
  let γ : Bool → Interval → Plane := fun i => e ∘ η i
  have hγ : ∀ i, Topology.IsClosedEmbedding (γ i) := by
    intro i
    have hη := actual_endpoint_germ_embedding M (ds i) (k i) r hr hr1
    have hc : Continuous (γ i) := continuousOn_univ.mp
      (e.continuousOn.comp hη.continuous.continuousOn (fun t _ => hηsource i t))
    apply hc.isClosedEmbedding
    intro t u htu
    exact hη.injective (e.injOn (hηsource i t) (hηsource i u) htu)
  have hγzero : ∀ i, γ i 0 = 0 := by
    intro i
    change e (η i 0) = 0
    rw [hηzero,hezero]
  have hmeet : ∀ i j : Bool, i ≠ j → range (γ i) ∩ range (γ j) = {0} := by
    intro i j hij
    have hij' : (i,k i) ≠ (j,k j) := fun he => hij (congrArg Prod.fst he)
    have hηmeet := actual_normalized_star_intersection M ds hdFamily p r hr hrhalf
      (i,k i) (j,k j) hij' (hηzero i) (hηzero j)
    ext z
    constructor
    · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
      have htu : η i t = η j u :=
        e.injOn (hηsource i t) (hηsource j u) (ht.trans hu.symm)
      have hm : η i t ∈ range (η i) ∩ range (η j) :=
        ⟨⟨t,rfl⟩,⟨u,htu.symm⟩⟩
      rw [hηmeet] at hm
      have htp : η i t = p := Set.mem_singleton_iff.mp hm
      exact Set.mem_singleton_iff.mpr (ht.symm.trans (by change e (η i t)=0; rw [htp,hezero]))
    · intro hz
      have hz0 : z = 0 := hz
      subst z
      exact ⟨⟨0,hγzero i⟩,⟨0,hγzero j⟩⟩
  obtain ⟨R,hopposite⟩ := pointed_one_or_two_arm_relative_seed γ 0 hγ hγzero hmeet
    (Or.inr (by decide)) Set.univ isOpen_univ (Set.mem_univ _)
  obtain ⟨ell,hell,hellEq⟩ := hopposite false true (by decide)
  obtain ⟨N,hN0,hNfirst,hNsecond,hNsmul⟩ :=
    plane_selected_opposite_ray_normalization (R.vector false) (R.vector_nonzero false) ell hell
  have hNvec : ∀ i : Bool, N (R.vector i) = Plane.mk (if i then -1 else 1) 0 := by
    intro i
    cases i
    · exact hNfirst
    · rw [hellEq]
      exact hNsecond
  let F : OpenPartialHomeomorph B Plane :=
    e.trans ((R.H.trans N).toOpenPartialHomeomorph)
  have hFs : F.source = e.source := by simp [F]
  have hFval (y : B) : F y = N (R.H (e y)) := rfl
  have hpF : p ∈ F.source := hFs.symm ▸ hep
  have hFp : F p = 0 := by rw [hFval,hezero,R.fixes_center,hN0]
  have hprefix (i : Bool) :
      (N ∘ R.H) '' armPrefix γ i (R.cut i) =
        segment ℝ (0 : Plane) (Plane.mk (if i then -1 else 1) 0) := by
    rw [Set.image_comp, R.prefix_image]
    simp only [zero_add]
    rw [homogeneous_homeomorph_segment_image N hN0 hNsmul, hNvec]
  have hIncidentUnique (i terminal : Bool)
      (hi : (if terminal then (ds i).val.map 1 else (ds i).val.map 0) = p) :
      terminal = k i := by
    by_contra hn
    have hki := hk i
    cases ht : terminal <;> cases hki' : k i
    · exact hn (ht.trans hki'.symm)
    · have hz : (d i).val.map 0 = p := by simpa [ht,ds,NonLoopArc.toEssential] using hi
      have ho : (d i).val.map 1 = p := by simpa [hki'] using hki
      exact (d i).property (hz.trans ho.symm)
    · have ho : (d i).val.map 1 = p := by simpa [ht,ds,NonLoopArc.toEssential] using hi
      have hz : (d i).val.map 0 = p := by simpa [hki'] using hki
      exact (d i).property (hz.trans ho.symm)
    · exact hn (ht.trans hki'.symm)
  have hremainder := fun i : Bool =>
    marked_endpoint_compact_whole_remainder M (ds i) p hπbranch r hr hrhalf
  choose K hKcompact hpK hKimage using hremainder
  let bad : Set B := K false ∪ K true
  have hbadClosed : IsClosed bad := by
    let : T2Space B := M.sphere.symm.t2Space
    exact (hKcompact false).isClosed.union (hKcompact true).isClosed
  have hpbad : p ∉ bad := by simp only [bad,Set.mem_union,not_or]; exact ⟨hpK false,hpK true⟩
  let W : Set B := e.source ∩ badᶜ ∩
    (e ⁻¹' (R.H ⁻¹' Metric.ball (0 : Plane) R.coreRadius)) ∩
    (F ⁻¹' Metric.ball (0 : Plane) 1)
  have hW : IsOpen W := by
    have hball : IsOpen (R.H ⁻¹' Metric.ball (0 : Plane) R.coreRadius) :=
      R.H.continuous.isOpen_preimage _ Metric.isOpen_ball
    have heball : IsOpen (e.source ∩ (e ⁻¹' (R.H ⁻¹' Metric.ball (0 : Plane) R.coreRadius))) :=
      e.isOpen_inter_preimage hball
    have hFball := F.isOpen_inter_preimage (Metric.isOpen_ball (x := (0 : Plane)) (ε := 1))
    have hWeq : W = ((e.source ∩ badᶜ) ∩
        (e.source ∩ e ⁻¹' (R.H ⁻¹' Metric.ball (0 : Plane) R.coreRadius))) ∩
        (F.source ∩ F ⁻¹' Metric.ball (0 : Plane) 1) := by
      rw [hFs]
      ext y
      simp only [W,Set.mem_inter_iff]
      tauto
    rw [hWeq]
    exact ((e.open_source.inter hbadClosed.isOpen_compl).inter heball).inter hFball
  have hpW : p ∈ W := by
    refine ⟨⟨⟨hep,hpbad⟩,?_⟩,?_⟩
    · change R.H (e p) ∈ Metric.ball (0 : Plane) R.coreRadius
      rw [hezero,R.fixes_center]
      exact Metric.mem_ball_self R.core_pos
    · change F p ∈ Metric.ball (0 : Plane) 1
      rw [hFp]
      exact Metric.mem_ball_self (by norm_num)
  have hlocal (i : Bool) (y : B) (hy : y ∈ W) :
      y ∈ (ds i).val.image ↔
        F y ∈ segment ℝ (0 : Plane) (Plane.mk (if i then -1 else 1) 0) := by
    constructor
    · intro hya
      rw [hKimage i] at hya
      have hyK : y ∉ K i := by
        cases i
        · exact fun h => hy.1.1.2 (Or.inl h)
        · exact fun h => hy.1.1.2 (Or.inr h)
      rcases hya with hK | hgerm
      · exact (hyK hK).elim
      · obtain ⟨terminal,hterminal⟩ := Set.mem_iUnion.mp hgerm
        by_cases hi : (if terminal then (ds i).val.map 1 else (ds i).val.map 0) = p
        · rw [ite_eq_left hi] at hterminal
          have htk := hIncidentUnique i terminal hi
          subst terminal
          obtain ⟨t,ht⟩ := hterminal
          have hγval : γ i t = e y := by change e (η i t) = e y; exact congrArg e ht
          have hcut : t.val ≤ (R.cut i).val := by
            by_contra hn
            have htail : R.H (e y) ∈ R.H '' tail γ i (R.cut i) :=
              ⟨γ i t,⟨t,(lt_of_not_ge hn).le,rfl⟩,congrArg R.H hγval⟩
            have hball : R.H (e y) ∈ Metric.closedBall (0 : Plane) R.coreRadius :=
              Metric.ball_subset_closedBall hy.1.2
            exact Set.disjoint_left.mp (R.excludes_tails i) htail hball
          rw [← hprefix i]
          refine ⟨γ i t,⟨t,hcut,rfl⟩,?_⟩
          change N (R.H (γ i t)) = F y
          rw [hγval,hFval]
        · rw [ite_eq_right hi] at hterminal
          exact hterminal.elim
    · intro hseg
      rw [← hprefix i] at hseg
      obtain ⟨z,⟨t,ht,rfl⟩,hz⟩ := hseg
      have hEy : e (η i t) = e y := by
        apply R.H.injective
        apply N.injective
        exact hz
      have hηy : η i t = y := e.injOn (hηsource i t) hy.1.1.1 hEy
      exact ⟨endpointGermParameter (k i) r hr hr1 t,hηy⟩
  have hsegmentChar (i : Bool) (z : Plane) (hz : ‖z‖ < 1) :
      z ∈ segment ℝ (0 : Plane) (Plane.mk (if i then -1 else 1) 0) ↔
        z 1 = 0 ∧ (if i then z 0 ≤ 0 else 0 ≤ z 0) := by
    rw [segment_eq_image_lineMap]
    have habs : |z 0| < 1 := lt_of_le_of_lt (PiLp.norm_apply_le z 0) hz
    constructor
    · rintro ⟨t,ht,rfl⟩
      cases i <;> simp [AffineMap.lineMap_apply_module,Plane.mk] <;> linarith [ht.1]
    · rintro ⟨hz1,hz0⟩
      cases i
      · refine ⟨z 0,⟨hz0,(abs_lt.mp habs).2.le⟩,?_⟩
        ext j
        fin_cases j <;> simp [AffineMap.lineMap_apply_module,Plane.mk,hz1]
      · refine ⟨-z 0,⟨by simpa using neg_nonneg.mpr hz0,(by linarith [(abs_lt.mp habs).1])⟩,?_⟩
        ext j
        fin_cases j <;> simp [AffineMap.lineMap_apply_module,Plane.mk,hz1]
  have hlocalAxes (i : Bool) (y : B) (hy : y ∈ W) :
      y ∈ (ds i).val.image ↔
        (F y) 1 = 0 ∧ (if i then (F y) 0 ≤ 0 else 0 ≤ (F y) 0) := by
    rw [hlocal i y hy]
    exact hsegmentChar i (F y) (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hy.2)
  let F0 := F.restrOpen W hW
  let D : OpenPartialHomeomorph B ℂ :=
    F0.trans P.toHomeomorph.toOpenPartialHomeomorph
  have hDsource : D.source = W := by
    simp only [D,F0,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
    change F.source ∩ W = W
    apply Set.inter_eq_right.mpr
    intro y hy
    exact hFs.symm ▸ hy.1.1.1
  have hDvalue (y : B) : D y = P (F y) := rfl
  have hcdown0 : c.downstairs.symm 0 = p := by
    rw [← c.downstairs_center]
    exact c.downstairs.left_inv c.downstairs_mem
  have hcdownTarget0 : (0 : ℂ) ∈ c.downstairs.target := by
    rw [← c.downstairs_center]
    exact c.downstairs.map_source c.downstairs_mem
  let h : OpenPartialHomeomorph ℂ ℂ := c.downstairs.symm.trans D
  have hh0 : (0 : ℂ) ∈ h.source := by
    change (0 : ℂ) ∈ c.downstairs.target ∧ c.downstairs.symm 0 ∈ D.source
    exact ⟨hcdownTarget0, hDsource.symm ▸ (hcdown0.symm ▸ hpW)⟩
  have hhzero : h 0 = 0 := by
    change D (c.downstairs.symm 0) = 0
    rw [hcdown0,hDvalue,hFp,P.map_zero]
  obtain ⟨g,hgsource,hgzero,hgsquare,_⟩ :=
    CurveComplex.Hyperbolic.local_plane_homeomorphism_square_lift h hh0 hhzero
  let G : OpenPartialHomeomorph S ℂ := c.upstairs.trans g
  have hwG : w ∈ G.source := by
    change w ∈ c.upstairs.source ∧ c.upstairs w ∈ g.source
    exact ⟨c.upstairs_mem,c.upstairs_center.symm ▸ hgsource⟩
  have hGzero : G w = 0 := by
    change g (c.upstairs w) = 0
    rw [c.upstairs_center,hgzero]
  have hProjectionW (x : S) (hx : x ∈ G.source) :
      M.cover.projection x ∈ W ∧ P (F (M.cover.projection x)) = (G x)^2 := by
    have hxUp : x ∈ c.upstairs.source := hx.1
    have hxG : c.upstairs x ∈ g.source := hx.2
    obtain ⟨hxsquare,hgeq⟩ := hgsquare (c.upstairs x) hxG
    have heq : c.downstairs.symm ((c.upstairs x)^2) = M.cover.projection x := by
      rw [← c.square x hxUp]
      exact c.downstairs.left_inv (c.image_mem x hxUp)
    have hπD : M.cover.projection x ∈ D.source := by
      have ht : c.downstairs.symm ((c.upstairs x)^2) ∈ D.source := hxsquare.2
      exact heq ▸ ht
    refine ⟨hDsource ▸ hπD,?_⟩
    change P (F (M.cover.projection x)) = (g (c.upstairs x))^2
    rw [hgeq]
    change P (F (M.cover.projection x)) = D (c.downstairs.symm ((c.upstairs x)^2))
    rw [heq,hDvalue]
  have hsquarePositive (z : ℂ) :
      (z^2).im = 0 ∧ 0 ≤ (z^2).re ↔ z.im = 0 := by
    simp only [pow_two,Complex.mul_im,Complex.mul_re]
    constructor
    · rintro ⟨him,hre⟩
      have hprod : z.re * z.im = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with hr | hi
      · nlinarith [sq_nonneg z.im]
      · exact hi
    · intro hi
      constructor
      · simp [hi]
      · nlinarith [sq_nonneg z.re]
  have hsquareNegative (z : ℂ) :
      (z^2).im = 0 ∧ (z^2).re ≤ 0 ↔ z.re = 0 := by
    simp only [pow_two,Complex.mul_im,Complex.mul_re]
    constructor
    · rintro ⟨him,hre⟩
      have hprod : z.re * z.im = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with hr | hi
      · exact hr
      · nlinarith [sq_nonneg z.re]
    · intro hr
      constructor
      · simp [hr]
      · nlinarith [sq_nonneg z.im]
  have hAxes (x : S) (hx : x ∈ G.source) :
      (x ∈ (nonloop_arc_essential_preimage M a).val.image ↔ (G x).im = 0) ∧
      (x ∈ (nonloop_arc_essential_preimage M b).val.image ↔ (G x).re = 0) := by
    obtain ⟨hπW,hsquare⟩ := hProjectionW x hx
    constructor
    · rw [nonloop_arc_essential_preimage_image,Set.mem_preimage]
      change M.cover.projection x ∈ (ds false).val.image ↔ _
      rw [hlocalAxes false (M.cover.projection x) hπW]
      change (P (F (M.cover.projection x))).im = 0 ∧
        0 ≤ (P (F (M.cover.projection x))).re ↔ _
      rw [hsquare]
      exact hsquarePositive (G x)
    · rw [nonloop_arc_essential_preimage_image,Set.mem_preimage]
      change M.cover.projection x ∈ (ds true).val.image ↔ _
      rw [hlocalAxes true (M.cover.projection x) hπW]
      change (P (F (M.cover.projection x))).im = 0 ∧
        (P (F (M.cover.projection x))).re ≤ 0 ↔ _
      rw [hsquare]
      exact hsquareNegative (G x)
  let L : ℂ ≃ₜ ℝ × ℝ :=
    Complex.equivRealProdCLM.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ)
  let J : OpenPartialHomeomorph S (ℝ × ℝ) := G.trans L.toOpenPartialHomeomorph
  have hJs : J.source = G.source := by simp [J]
  have hwJ : w ∈ J.source := hJs.symm ▸ hwG
  refine ⟨J.source,J.target,hwJ,J.toHomeomorphSourceTarget,
    J.open_source,J.open_target,?_,?_⟩
  · change L (G w) = (0,0)
    rw [hGzero]
    rfl
  · intro x hx
    change (x ∈ (nonloop_arc_essential_preimage M a).val.image ↔ (L (G x)).1 = 0) ∧
      (x ∈ (nonloop_arc_essential_preimage M b).val.image ↔ (L (G x)).2 = 0)
    exact hAxes x (hJs ▸ hx)

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonloop_disjoint_pair_transverse_full_preimages
