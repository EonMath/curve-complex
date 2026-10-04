import CurveComplexGenusTwo.Topology.WeightedSurgery.IsolatedArcNeighborhood
import CurveComplexGenusTwo.Topology.Smoothing.SphereAtlasProof
import CurveComplexGenusTwo.Topology.GeometricPosition.IntervalSubdivision
import CurveComplexGenusTwo.Topology.PositionExtension.FlatBumpTranslation
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Every interior point of the old disjoint system has a genuine source
crosscut chart supported away from all marks and all other complete arcs. -/
theorem actual_disjoint_system_interior_crosscut_chart
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (i : ι) (hne : (r i).val.map 0 ≠ (r i).val.map 1)
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
  obtain ⟨e,W,he,hW,hpoint,hmarks,hothers,_⟩ :=
    actual_disjoint_system_interior_star M r hd i hne τ hτ0 hτ1
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
    refine ⟨hball ?_,he _⟩
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [l,u] at ht
    constructor <;> linarith [ht.1,ht.2]
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

/-- Prepared old-family coordinates at every unmarked point, the marked-arc
analogue of `position_prepared_family_cover`. No seam-avoidance move is needed
because the supplied old system already has disjoint interiors. -/
theorem actual_disjoint_system_prepared_interior_cover
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
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
      actual_disjoint_system_interior_crosscut_chart M r hd i (hne i) p ⟨hpi,hp⟩
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

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The new arbitrary non-loop arc's compact interior is subdivided into
finitely many prepared old-family patches. Both the patches and their labels
are outputs; no finite-position data or finite intersection assumption is used. -/
theorem actual_new_arc_compact_interior_chart_subdivision
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (a : EssentialMarkedArc M) (ha : a.val.map 0 ≠ a.val.map 1)
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
    have h := congrArg Subtype.val (NonLoopArc.injective ⟨a.val,ha⟩ heq)
    apply Subtype.ext
    change l+(u-l)*t.val = l+(u-l)*s.val at h
    nlinarith)
  have hclean (t : Interval) : η t ∉ M.cover.branch := by
    intro hm
    rcases a.val.marked_only_at_ends _ hm with h | h
    · have hh := congrArg Subtype.val h
      change l+(u-l)*t.val = 0 at hh
      nlinarith [t.property.1,t.property.2]
    · have hh := congrArg Subtype.val h
      change l+(u-l)*t.val = 1 at hh
      nlinarith [t.property.1,t.property.2]
  have hlocal (t : Interval) := actual_disjoint_system_prepared_interior_cover
    M r hne hd (η t) (hclean t)
  choose e hpoint hmarks label hlabel using hlocal
  obtain ⟨n,hn,choice,hsub⟩ := position_interval_subdivision η
    (fun t => (e t).source) (fun t => (e t).open_source) (fun t => ⟨t,hpoint t⟩)
  exact ⟨η,fun _ => rfl,hemb,n,hn,fun k => e (choice k),fun k => label (choice k),
    fun k => hmarks (choice k),fun k => hlabel (choice k),hsub⟩

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual marked seam-repair move: an unmarked point can be moved off the
entire disjoint old system by a marked-fixing isotopy in any prescribed support. -/
theorem actual_point_off_disjoint_arc_system
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
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
    actual_disjoint_system_prepared_interior_cover M r hne hd p hp
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

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- All finitely many unmarked seam points are repaired in one actual ambient
isotopy, using disjoint supports constructed by finite Hausdorff separation. -/
theorem actual_finite_points_off_disjoint_arc_system
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (F : Finset S) (hF : ∀ p ∈ F, p ∉ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hFW : (F : Set S) ⊆ W) :
    ∃ H : AmbientIsotopy S,
      (∀ p ∈ F, ∀ j, H.finalMap p ∉ (r j).val.image) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      ∀ t x, x ∉ W → H.map (t,x) = x := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨D,hD,hDdis⟩ := F.finite_toSet.t2_separation
  let U : {p // p ∈ F} → Set S := fun p => W ∩ D p.val
  have hU (p : {p // p ∈ F}) : IsOpen (U p) := hW.inter (hD p.val).2
  have hpU (p : {p // p ∈ F}) : p.val ∈ U p := ⟨hFW p.property,(hD p.val).1⟩
  have hUdis (p q : {p // p ∈ F}) (hpq : p ≠ q) : Disjoint (U p) (U q) := by
    exact (hDdis p.property q.property (fun h => hpq (Subtype.ext h))).mono
      inter_subset_right inter_subset_right
  have hmoves (p : {p // p ∈ F}) := actual_point_off_disjoint_arc_system
    M r hne hd p.val (hF p.val p.property) (U p) (hU p) (hpU p)
  choose moves hoff hmarks hfix using hmoves
  obtain ⟨H,hout,hinside⟩ := finite_supported_patch_assembly U hUdis moves hfix
  refine ⟨H,?_,?_,?_⟩
  · intro p hp j
    change H.map (⟨1,by norm_num⟩,p) ∉ (r j).val.image
    rw [hinside ⟨p,hp⟩ ⟨1,by norm_num⟩ p (hpU ⟨p,hp⟩)]
    exact hoff ⟨p,hp⟩ j
  · intro t x hx
    by_cases hxin : x ∈ ⋃ p, U p
    · obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hxin
      rw [hinside p t x hp]
      exact hmarks p t x hx
    · exact hout t x hxin
  · intro t x hx
    apply hout t x
    intro hi
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hi
    exact hx hp.1

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Localize marked seam repair so every assigned compact piece remains in its
chart throughout the motion. All supports are constructed from the actual pieces. -/
theorem actual_localized_marked_seam_repair
    (M : HyperellipticModel E S) {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
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
  have hmove (k) := actual_point_off_disjoint_arc_system M r hne hd
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

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Metric
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- After genuine seam repair, one uniform positive collar on every compact
piece avoids the complete old arc system. The collar width is constructed. -/
theorem actual_uniform_piece_off_system_collars
    (M : HyperellipticModel E S) {ι κ : Type} [Fintype ι] [Fintype κ]
    (r : ι → EssentialMarkedArc M) (arc : κ → C(Interval,S))
    (hends : ∀ k j, arc k 0 ∉ (r j).val.image ∧ arc k 1 ∉ (r j).val.image) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧
      ∀ k (t : Interval), (t:ℝ) ≤ ε ∨ 1-ε ≤ (t:ℝ) → ∀ j, arc k t ∉ (r j).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let bad : Set Interval := ⋃ k, ⋃ j, (arc k) ⁻¹' (r j).val.image
  have hbad : IsClosed bad := isClosed_iUnion_of_finite (fun k =>
    isClosed_iUnion_of_finite (fun j =>
      ((isCompact_range (r j).val.continuous).isClosed).preimage (arc k).continuous))
  have hzero : (0:Interval) ∈ badᶜ := by
    intro h
    obtain ⟨k,j,hkj⟩ := Set.mem_iUnion₂.mp h
    exact (hends k j).1 hkj
  have hone : (1:Interval) ∈ badᶜ := by
    intro h
    obtain ⟨k,j,hkj⟩ := Set.mem_iUnion₂.mp h
    exact (hends k j).2 hkj
  obtain ⟨δ₀,hδ₀,hball₀⟩ := Metric.isOpen_iff.mp hbad.isOpen_compl 0 hzero
  obtain ⟨δ₁,hδ₁,hball₁⟩ := Metric.isOpen_iff.mp hbad.isOpen_compl 1 hone
  let ε : ℝ := min (1/4) (min δ₀ δ₁) / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεhalf : ε < 1/2 := by
    have := min_le_left (1/4:ℝ) (min δ₀ δ₁)
    dsimp [ε]; linarith
  have hεδ₀ : ε < δ₀ := by
    have := (min_le_right (1/4:ℝ) (min δ₀ δ₁)).trans (min_le_left δ₀ δ₁)
    dsimp [ε]; linarith
  have hεδ₁ : ε < δ₁ := by
    have := (min_le_right (1/4:ℝ) (min δ₀ δ₁)).trans (min_le_right δ₀ δ₁)
    dsimp [ε]; linarith
  refine ⟨ε,hε,hεhalf,?_⟩
  intro k t ht j hj
  have htgood : t ∈ badᶜ := by
    rcases ht with ht | ht
    · apply hball₀
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |(t:ℝ)-0| < δ₀
      rw [sub_zero,abs_of_nonneg t.property.1]
      exact ht.trans_lt hεδ₀
    · apply hball₁
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |(t:ℝ)-1| < δ₁
      rw [abs_of_nonpos (by linarith [t.property.2])]
      linarith
  exact htgood (Set.mem_iUnion₂.mpr ⟨k,j,hj⟩)

end CurveComplex.HyperellipticModel
