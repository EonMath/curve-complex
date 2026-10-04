import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalDiskConstructionHeaders
import CurveComplexGenusTwo.Topology.CapBandGeometry.DiskOpen
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.Preorder.Finite
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import CurveComplexGenusTwo.Foundations.SurfaceCoverTransfer
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology CurveComplex
namespace CurveComplex.LocalSurgery

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 2000000 in
/-- A nullhomotopic embedded circle bounds an actual embedded disk downstairs
when the base has a genuine spherical quotient covering. -/
theorem boundsDisc_of_nullhomotopic_spherical_quotient_cover_complete
    {G S : Type*} [Group G] [TopologicalSpace S] [T2Space S]
    [MulAction G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)]
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → S)
    (hp : IsQuotientCoveringMap p G) (c : Curve S)
    (hc : (⟨c.map,c.embedded.continuous⟩ : C(Circle,S)).Nullhomotopic) : BoundsDisc c := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let P := EuclideanSpace ℝ (Fin 2)
  let Q := Metric.sphere (0 : E) 1
  letI : Fact (Module.finrank ℝ E = 2 + 1) := ⟨by simp [E]⟩
  letI : ConnectedSpace Q := Subtype.connectedSpace (isConnected_sphere (by
    apply Module.one_lt_rank_of_one_lt_finrank
    simp [E]) (0 : E) (by norm_num : (0 : ℝ) ≤ 1))
  have homit {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (r : C(Circle,S)) (hr : IsEmbedding r) : ¬Function.Surjective r := by
    classical
    have hgeneral {F : Set S} (hF : F.Finite)
        (hlocal : ∀ p ∈ F, ∃ U : Set S,
          IsOpen U ∧ p ∈ U ∧ IsPathConnected (U \ F)) : IsConnected Fᶜ := by
      classical
      by_cases hFempty : F = ∅
      · simpa [hFempty] using
          (isConnected_univ : IsConnected (Set.univ : Set S))
      have hcomplNonempty : Fᶜ.Nonempty := by
        obtain ⟨p, hpF⟩ := Set.nonempty_iff_ne_empty.mpr hFempty
        obtain ⟨U, _hUopen, _hpU, hpath⟩ := hlocal p hpF
        obtain ⟨x, _hxU, hxF⟩ := hpath.nonempty
        exact ⟨x, hxF⟩
      refine ⟨hcomplNonempty, ?_⟩
      intro u v hu hv hcover hUne hVne
      by_contra hinter
      let A : Set S := Fᶜ ∩ u
      let B : Set S := Fᶜ ∩ v
      have hAopen : IsOpen A := hF.isClosed.isOpen_compl.inter hu
      have hBopen : IsOpen B := hF.isClosed.isOpen_compl.inter hv
      have hABcover : Fᶜ ⊆ A ∪ B := by
        intro x hx
        rcases hcover hx with hxu | hxv
        · exact Or.inl ⟨hx, hxu⟩
        · exact Or.inr ⟨hx, hxv⟩
      have hABdisjoint : Disjoint A B := by
        rw [Set.disjoint_left]
        intro x hxA hxB
        exact hinter ⟨x, hxA.1, hxA.2, hxB.2⟩
      choose U hUopen hpU hUpath using
        fun p : F ↦ hlocal p.1 p.2
      have hside (p : F) :
          U p \ F ⊆ A ∨ U p \ F ⊆ B := by
        obtain ⟨x, hx⟩ := (hUpath p).nonempty
        rcases hABcover hx.2 with hxA | hxB
        · left
          exact (hUpath p).isConnected.isPreconnected.subset_left_of_subset_union
            hAopen hBopen hABdisjoint
            (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxA⟩
        · right
          exact (hUpath p).isConnected.isPreconnected.subset_right_of_subset_union
            hAopen hBopen hABdisjoint
            (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxB⟩
      let Left (p : F) : Prop := U p \ F ⊆ A
      have hright (p : F) (hp : ¬Left p) :
          U p \ F ⊆ B :=
        (hside p).resolve_left hp
      let W (p : F) : Set S := U p \ (F \ {p.1})
      have hWopen (p : F) : IsOpen (W p) := by
        exact (hUopen p).inter (hF.sdiff |>.isClosed.isOpen_compl)
      have hpW (p : F) : p.1 ∈ W p := by
        refine ⟨hpU p, ?_⟩
        rintro ⟨_, hpne⟩
        exact hpne rfl
      have eq_center_of_mem_W_of_mem_F (p : F) {x : S}
          (hxW : x ∈ W p) (hxF : x ∈ F) :
          x = p.1 := by
        by_contra hxp
        apply hxW.2
        exact ⟨hxF, by simpa using hxp⟩
      let L : Set S := {x | ∃ p : F, Left p ∧ x = p.1}
      let R : Set S := {x | ∃ p : F, ¬Left p ∧ x = p.1}
      let A' : Set S := A ∪ L
      let B' : Set S := B ∪ R
      have hA'open : IsOpen A' := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        rcases hx with hxA | ⟨p, hpLeft, rfl⟩
        · exact ⟨A, Set.subset_union_left, hAopen, hxA⟩
        · refine ⟨W p, ?_, hWopen p, hpW p⟩
          intro y hyW
          by_cases hyF : y ∈ F
          · right
            exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
          · left
            exact hpLeft ⟨hyW.1, hyF⟩
      have hB'open : IsOpen B' := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        rcases hx with hxB | ⟨p, hpLeft, rfl⟩
        · exact ⟨B, Set.subset_union_left, hBopen, hxB⟩
        · refine ⟨W p, ?_, hWopen p, hpW p⟩
          intro y hyW
          by_cases hyF : y ∈ F
          · right
            exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
          · left
            exact hright p hpLeft ⟨hyW.1, hyF⟩
      have hA'B'disjoint : Disjoint A' B' := by
        rw [Set.disjoint_left]
        intro x hxA' hxB'
        rcases hxA' with hxA | ⟨p, hpLeft, hp⟩
        · rcases hxB' with hxB | ⟨q, _hqLeft, hq⟩
          · exact Set.disjoint_left.mp hABdisjoint hxA hxB
          · exact hxA.1 (hq ▸ q.2)
        · rcases hxB' with hxB | ⟨q, hqLeft, hq⟩
          · exact hxB.1 (hp ▸ p.2)
          · apply hqLeft
            have hpq : p = q := by
              apply Subtype.ext
              exact hp.symm.trans hq
            simpa [hpq] using hpLeft
      have hA'B'cover : (Set.univ : Set S) ⊆ A' ∪ B' := by
        intro x _
        by_cases hxF : x ∈ F
        · let p : F := ⟨x, hxF⟩
          by_cases hpLeft : Left p
          · exact Or.inl (Or.inr ⟨p, hpLeft, rfl⟩)
          · exact Or.inr (Or.inr ⟨p, hpLeft, rfl⟩)
        · rcases hABcover hxF with hxA | hxB
          · exact Or.inl (Or.inl hxA)
          · exact Or.inr (Or.inl hxB)
      have hA'ne : ((Set.univ : Set S) ∩ A').Nonempty := by
        obtain ⟨x, hxF, hxu⟩ := hUne
        exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxu⟩⟩
      have hB'ne : ((Set.univ : Set S) ∩ B').Nonempty := by
        obtain ⟨x, hxF, hxv⟩ := hVne
        exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxv⟩⟩
      obtain ⟨x, _, hxA', hxB'⟩ := isPreconnected_univ
        A' B' hA'open hB'open hA'B'cover hA'ne hB'ne
      exact Set.disjoint_left.mp hA'B'disjoint hxA' hxB'
    have hplane (x : S) : ∃ U : Set S, x ∈ U ∧ IsOpen U ∧
        Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) := by
      let P := EuclideanSpace ℝ (Fin 2)
      let e := chartAt P x
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x)
        (e.map_source (mem_chart_source P x))
      let U := e.symm '' Metric.ball (e x) r
      have hsub : Metric.ball (e x) r ⊆ e.symm.source := hball
      have hopen : IsOpen U := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub
      have hx : x ∈ U := ⟨e x, Metric.mem_ball_self hr, e.left_inv (mem_chart_source P x)⟩
      let b := OpenPartialHomeomorph.univBall (e x) r
      have hmap : b '' (Set.univ : Set P) = Metric.ball (e x) r := by
        simpa only [b, OpenPartialHomeomorph.univBall_source,
          OpenPartialHomeomorph.univBall_target (e x) hr] using b.image_source_eq_target
      let g : P ≃ₜ Metric.ball (e x) r :=
        (Homeomorph.Set.univ P).symm.trans
          (b.homeomorphOfImageSubsetSource (by simp [b]) hmap)
      let f : Metric.ball (e x) r ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hsub rfl
      exact ⟨U, hx, hopen, ⟨g.trans f⟩⟩
    have hfinite (F : Set S) (hF : F.Finite) : IsConnected Fᶜ := by
      apply hgeneral hF
      intro x hxF
      obtain ⟨U, hxU, hU, ⟨g⟩⟩ := hplane x
      let f : EuclideanSpace ℝ (Fin 2) → S := fun z => (g z : S)
      have hfin : (f ⁻¹' F).Finite := hF.preimage (by
        intro a _ b _ hab
        exact g.injective (Subtype.ext hab))
      have hp : IsPathConnected (f ⁻¹' F)ᶜ :=
        hfin.countable.isPathConnected_compl_of_one_lt_rank (by
          apply Module.one_lt_rank_of_one_lt_finrank
          simp)
      have himage : f '' (f ⁻¹' F)ᶜ = U \ F := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨(g z).property, hz⟩
        · rintro ⟨hyU, hyF⟩
          obtain ⟨z, hz⟩ := g.surjective ⟨y, hyU⟩
          refine ⟨z, ?_, congrArg Subtype.val hz⟩
          change f z ∉ F
          simpa [f, hz] using hyF
      refine ⟨U, hU, hxU, ?_⟩
      rw [← himage]
      exact hp.image (continuous_subtype_val.comp g.continuous)
    intro hsurj
    let h : Circle ≃ₜ S := hr.toHomeomorphOfSurjective hsurj
    have hp : IsPreconnected (r ⁻¹' ({r 1, r (-1)} : Set S)ᶜ) :=
      h.isPreconnected_preimage.mpr (hfinite _ ((Set.finite_singleton _).insert _)).isPreconnected
    have heq : r ⁻¹' ({r 1, r (-1)} : Set S)ᶜ = ({1, -1} : Set Circle)ᶜ := by
      ext z
      simp only [mem_preimage, mem_compl_iff, mem_insert_iff, mem_singleton_iff]
      rw [hr.injective.eq_iff, hr.injective.eq_iff]
    rw [heq] at hp
    exact Circle.not_isPreconnected_compl_pair (Circle.neg_ne_self (1 : Circle)).symm hp
  have hpuncture [Finite G]
    (K : G → Set Q) (hclosed : ∀ i, IsClosed (K i))
    (hpair : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (i₀ : G) (hne : (K i₀).Nonempty) (hproper : K i₀ ≠ Set.univ) :
    ∃ x : Q, ∀ i, x ∉ K i := by
    classical
    by_contra h
    have hcover : ⋃ i, K i = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      by_contra hx
      apply h
      refine ⟨x, fun i hi => hx ?_⟩
      exact mem_iUnion.mpr ⟨i,hi⟩
    have hcomp : (K i₀)ᶜ = ⋃ i : {j : G // j ≠ i₀}, K i.val := by
      ext x
      constructor
      · intro hx
        have hxall : x ∈ ⋃ i, K i := by rw [hcover]; trivial
        obtain ⟨i,hi⟩ := mem_iUnion.mp hxall
        have hneq : i ≠ i₀ := fun he => hx (he ▸ hi)
        exact mem_iUnion.mpr ⟨⟨i,hneq⟩,hi⟩
      · intro hx
        obtain ⟨i,hi⟩ := mem_iUnion.mp hx
        exact fun hx₀ => Set.disjoint_left.mp (hpair i.val i₀ i.property) hi hx₀
    have hopen : IsOpen (K i₀) := by
      rw [← isClosed_compl_iff, hcomp]
      exact isClosed_iUnion_of_finite fun i => hclosed i.val
    have hclopen : IsClopen (K i₀) := ⟨hclosed i₀,hopen⟩
    exact hproper (hclopen.eq_univ hne)
  have hinner [Finite G]
    (C : G → Set Schoenflies.Plane)
    (hC : ∀ i, Schoenflies.IsJordanCurve (C i))
    (hdis : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    ∃ i, ∀ j, j ≠ i →
      Disjoint (Schoenflies.inside (C i) ∪ C i) (C j) := by
    classical
    let R : G → Set Schoenflies.Plane := fun i => Schoenflies.inside (C i) ∪ C i
    obtain ⟨i, hi⟩ := Set.Finite.exists_minimalFor R Set.univ (Set.toFinite _)
      (Set.univ_nonempty : (Set.univ : Set G).Nonempty)
    have hsep (i : G) := Schoenflies.jordan_curve_theorem (hC i)
    refine ⟨i, ?_⟩
    intro j hji
    have hdisij := hdis i j hji.symm
    rcases jordan_boundary_subset_inside_or_outside (hsep i) (hsep j) hdisij with hinside | houtside
    · have hm : Schoenflies.inside (C j) ⊆ Schoenflies.inside (C i) :=
        jordan_inside_mono_of_boundary_subset_closed_inside (hsep i) (hsep j)
          (fun _ hx => Or.inl (hinside hx))
      have hRji : R j ⊆ R i := by
        rintro x (hx | hx)
        · exact Or.inl (hm hx)
        · exact Or.inl (hinside hx)
      have hRij : R i ⊆ R j := hi.2 (mem_univ j) hRji
      obtain ⟨x,hx⟩ := (hC i).nonempty
      have hxj : x ∈ Schoenflies.inside (C j) := by
        rcases hRij (Or.inr hx) with hy | hy
        · exact hy
        · exact False.elim (Set.disjoint_left.mp hdisij hx hy)
      exact False.elim (Schoenflies.inside_subset_compl (hm hxj) hx)
    · exact Set.disjoint_left.mpr fun x hx hy => by
        rcases hx with hx | hx
        · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hx (houtside hy)
        · exact Set.disjoint_left.mp hdisij hx hy
  have hdescent (p : Q → S) (hp : IsQuotientCoveringMap p G)
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Q))
    (hd : IsEmbedding d)
    (havoid : ∀ g : G, g ≠ 1 → Disjoint (Set.range d)
      ((g • ·) '' (d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}))) :
    Set.InjOn p (Set.range d) := by
    classical
    let P := EuclideanSpace ℝ (Fin 2)
    let K := Metric.closedBall (0 : P) 1
    letI : ConnectedSpace K := Subtype.connectedSpace
      ((convex_closedBall (0 : P) 1).isConnected (by
        exact ⟨0, by simp⟩))
    have hconn : IsConnected (Set.range d) := isConnected_range d.continuous
    have hBrouwer : ∀ u : C(K,K), ∃ x, u x = x := fun u =>
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.BrouwerFixedPoint.brouwer_fixed_point
        u u.continuous
    apply projection_injective_on_disc_of_jordan_trichotomy p hp d hd hBrouwer
    intro g hg
    let t : Q ≃ₜ Q := {
      toFun := fun x => g • x
      invFun := fun x => g⁻¹ • x
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      continuous_toFun := hp.continuous_const_smul g
      continuous_invFun := hp.continuous_const_smul g⁻¹ }
    let dg : C(K,Q) := ⟨fun x => g • d x, (hp.continuous_const_smul g).comp d.continuous⟩
    have hdg : IsEmbedding dg := t.isEmbedding.comp hd
    have hrange : Set.range dg = (g • ·) '' Set.range d := by
      rw [← Set.range_comp]
      rfl
    have hfront : frontier (Set.range dg) ⊆
        (g • ·) '' (d '' {x : K | x.val ∈ Metric.sphere (0:P) 1}) := by
      have hi : dg '' {x : K | x.val ∈ Metric.sphere (0:P) 1} =
          (g • ·) '' (d '' {x : K | x.val ∈ Metric.sphere (0:P) 1}) := by
        rw [← Set.image_comp]
        rfl
      rw [← hi]
      exact embedded_disk_frontier_subset_boundary dg hdg
    have hclosed : IsClosed (Set.range dg) := (isCompact_range dg.continuous).isClosed
    have hdisfront : Disjoint (Set.range d) (frontier (Set.range dg)) :=
      (havoid g hg).mono_right hfront
    have hcover : Set.range d ⊆ interior (Set.range dg) ∪ (Set.range dg)ᶜ := by
      intro x hx
      by_cases hxm : x ∈ Set.range dg
      · left
        by_contra hxi
        have hxf : x ∈ frontier (Set.range dg) := by
          rw [frontier, hclosed.closure_eq]
          exact ⟨hxm,hxi⟩
        exact Set.disjoint_left.mp hdisfront hx hxf
      · exact Or.inr hxm
    have hdis : Disjoint (interior (Set.range dg)) (Set.range dg)ᶜ :=
      Set.disjoint_left.mpr fun _ hx hy => hy (interior_subset hx)
    rcases hconn.isPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hdis hcover with hi | ho
    · exact Or.inr (Or.inl (hi.trans (interior_subset.trans (by rw [hrange]))))
    · left
      rw [← hrange]
      exact Set.disjoint_left.mpr fun _ hx hy => ho hx hy
  have hcov : IsCoveringMap p := hp.isCoveringMap
  obtain ⟨r,hpr,hr,hrnull⟩ := exists_embedded_nullhomotopic_lift_of_covering
    p hcov hp.surjective c hc
  have hprpt (z : Circle) : p (r z) = c.map z := congrArg (fun f : C(Circle,S) => f z) hpr
  let F := p ⁻¹' {p (r 1)}
  have hF : IsClosed F := isClosed_singleton.preimage hcov.continuous
  letI : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  letI : DiscreteTopology F := (hcov (p (r 1))).discreteTopology_fiber
  letI : Finite F := finite_of_compact_of_discrete
  letI : Finite G := Finite.of_equiv F (hp.fiberEquivGroup ⟨r 1,rfl⟩)
  let K : G → Set Q := fun g => (g • ·) '' Set.range r
  have hKclosed (g : G) : IsClosed (K g) :=
    ((isCompact_range r.continuous).image (hp.continuous_const_smul g)).isClosed
  have hKpair (g h : G) (hne : g ≠ h) : Disjoint (K g) (K h) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨a,⟨u,rfl⟩,ha⟩ ⟨b,⟨v,rfl⟩,hb⟩
    have huv : u = v := c.embedded.injective (by
      rw [← hprpt u, ← hprpt v]
      exact (hp.map_smul g).symm.trans
        ((congrArg p (ha.trans hb.symm)).trans (hp.map_smul h)))
    subst v
    exact hne (hp.isCancelSMul.right_cancel g h (r u) (ha.trans hb.symm))
  have hKone : K 1 = Set.range r := by simp [K]
  have hKproper : K 1 ≠ Set.univ := by
    rw [hKone]
    intro hrange
    apply homit r hr
    intro y
    have hy : y ∈ Set.range r := by rw [hrange]; trivial
    exact hy
  have hKne : (K 1).Nonempty := by
    rw [hKone]
    exact ⟨r 1,⟨1,rfl⟩⟩
  obtain ⟨x,hx⟩ := hpuncture K hKclosed hKpair 1 hKne hKproper
  let e := stereographic' 2 x
  have hsource (g : G) (z : Circle) : g • r z ∈ e.source := by
    simp only [e,stereographic'_source,mem_compl_iff,mem_singleton_iff]
    exact fun he => hx g ⟨r z,⟨z,rfl⟩,he⟩
  let v : G → C(Circle,P) := fun g =>
    ⟨fun z => e (g • r z), e.continuousOn.comp_continuous
      ((hp.continuous_const_smul g).comp r.continuous) (hsource g)⟩
  have hv (g : G) : IsEmbedding (v g) := by
    have hi : Function.Injective (v g) := by
      intro a b hab
      have he := e.injOn (hsource g a) (hsource g b) hab
      have hrsame : r a = r b := by
        have hh := congrArg (fun y : Q => g⁻¹ • y) he
        simpa using hh
      exact hr.injective hrsame
    exact ((v g).continuous.isClosedEmbedding hi).isEmbedding
  let C : G → Set P := fun g => Set.range (v g)
  have hJ (g : G) : Schoenflies.IsJordanCurve (C g) :=
    isJordanCurve_range_of_isEmbedding_circle (v g) (hv g)
  have hCpair (g h : G) (hne : g ≠ h) : Disjoint (C g) (C h) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨a,ha⟩ ⟨b,hb⟩
    have he : g • r a = h • r b := e.injOn (hsource g a) (hsource h b) (ha.trans hb.symm)
    exact Set.disjoint_left.mp (hKpair g h hne) ⟨r a,⟨a,rfl⟩,rfl⟩ ⟨r b,⟨b,rfl⟩,he.symm⟩
  obtain ⟨g₀,hg₀⟩ := hinner C hJ hCpair
  let c₀ : Curve P := ⟨v g₀,hv g₀⟩
  obtain ⟨d,hd,hbd⟩ := jordan_curve_bounds_disc c₀ (hJ g₀)
  have hregion : Set.range d = Schoenflies.inside (C g₀) ∪ C g₀ :=
    embedded_disc_range_eq_closed_inside d hd (C g₀) (hJ g₀) hbd
  have he : IsOpenEmbedding e.symm := e.symm.isOpenEmbedding (by simp [e])
  let D : C(Metric.closedBall (0:P) 1,Q) :=
    ⟨fun z => e.symm (d z), he.continuous.comp d.continuous⟩
  have hD : IsEmbedding D := he.isEmbedding.comp hd
  have hDb : D '' {z | z.val ∈ Metric.sphere (0:P) 1} = K g₀ := by
    change (e.symm ∘ (d : Metric.closedBall (0:P) 1 → P)) '' _ = K g₀
    rw [Set.image_comp,hbd]
    ext y
    constructor
    · rintro ⟨z,⟨a,rfl⟩,rfl⟩
      exact ⟨r a,⟨a,rfl⟩,(e.left_inv (hsource g₀ a)).symm⟩
    · rintro ⟨z,⟨a,rfl⟩,rfl⟩
      exact ⟨v g₀ a,⟨a,rfl⟩,e.left_inv (hsource g₀ a)⟩
  have hDavoid (g : G) (hgg : g ≠ g₀) : Disjoint (Set.range D) (K g) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨z,hz⟩ ⟨w,⟨a,rfl⟩,ha⟩
    have hsame : d z = v g a := by
      change d z = e (g • r a)
      have hy : e.symm (d z) = g • r a := hz.trans ha.symm
      have hh := congrArg (fun t : Q => e t) hy
      simpa only [e.right_inv (by simp [e])] using hh
    have hdz : d z ∈ Schoenflies.inside (C g₀) ∪ C g₀ :=
      hregion ▸ (show d z ∈ Set.range d from ⟨z,rfl⟩)
    exact Set.disjoint_left.mp (hg₀ g hgg) hdz ⟨a,hsame.symm⟩
  have hinj : Set.InjOn p (Set.range D) := hdescent p hp D hD (by
    intro h hh
    rw [hDb]
    have hKg : (h • ·) '' K g₀ = K (h * g₀) := by
      rw [Set.image_image]
      apply Set.image_congr
      intro y hy
      exact (mul_smul h g₀ y).symm
    rw [hKg]
    apply hDavoid
    intro heq
    have hmul : h * g₀ = 1 * g₀ := by simpa using heq
    exact hh (mul_right_cancel hmul))
  let f : C(Metric.closedBall (0:P) 1,S) := ⟨fun z => p (D z), hcov.continuous.comp D.continuous⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact hD.injective (hinj ⟨a,rfl⟩ ⟨b,rfl⟩ hab)
  refine ⟨f,(f.continuous.isClosedEmbedding hf).isEmbedding,?_⟩
  change (p ∘ (D : Metric.closedBall (0:P) 1 → Q)) '' _ = Set.range c.map
  rw [Set.image_comp,hDb]
  ext y
  constructor
  · rintro ⟨z,⟨w,⟨a,rfl⟩,rfl⟩,rfl⟩
    exact ⟨a,(congrArg (fun f : C(Circle,S) => f a) hpr).symm.trans (hp.map_smul g₀).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨g₀ • r a,⟨r a,⟨a,rfl⟩,rfl⟩,(hp.map_smul g₀).trans
      (congrArg (fun f : C(Circle,S) => f a) hpr)⟩


end CurveComplex.LocalSurgery
