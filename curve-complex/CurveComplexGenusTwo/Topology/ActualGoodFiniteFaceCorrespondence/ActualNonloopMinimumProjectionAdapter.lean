import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Intersection.FiniteCount
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Foundations.SourceNonseparating
import CurveComplexGenusTwo.Topology.ActualGoodFiniteFaceCorrespondence.Main12OriginalRegularArcNeighborhood
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14OriginalCircle24DescentConsume
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalBoundaryPairCanonicalNamedConsumeProof
import CurveComplexGenusTwo.Topology.ActualMain14OriginalD.Main14OriginalDiskSupportedCancellationConsumePROVED
import CurveComplexGenusTwo.Dictionary.Circle24.ClosedTwoMarkSideAdapter

import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential
import CurveComplexGenusTwo.Topology.ActualCurveMinimum.OriginalFiniteMinimalActualReturningConsumer

namespace CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal
open CurveComplex CurveComplex.HyperellipticModel
open Set _root_.Topology Schoenflies
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
variable {S B : Type} [TopologicalSpace S] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  (M : HyperellipticModel S B)

private theorem marked_descent (a b : HyperellipticModel.NonLoopArc M)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' a.image)
      (M.cover.projection ⁻¹' b.image)) :
    HyperellipticModel.MarkedIsotopyRel M a.image b.image := by
  have hBoundaryDiskTransport (a b : NonLoopArc M)
      (Na : ArcNeighborhood a) (Nb : ArcNeighborhood b)
      (H : AmbientIsotopy B)
      (hfix : ∀ t x, x ∈ M.cover.branch → H.map (t,x)=x)
      (hboundary : H.finalMap '' Na.boundary.image=Nb.boundary.image) :
      H.finalMap '' Na.closedSet=Nb.closedSet ∧
        ∃ aT : NonLoopArc M,
          MarkedIsotopyRel M a.image aT.image ∧ aT.image ⊆ interior Nb.closedSet ∧
          ({aT.val.map 0,aT.val.map 1}:Set B)={b.val.map 0,b.val.map 1} := by
    classical
    letI : T2Space B := M.sphere.symm.t2Space
    have uniqueSide (c : Circle24 M) (D F : Set B)
        (hD : IsClosed D) (hF : IsClosed F)
        (hd : frontier D=c.val.image) (hf : frontier F=c.val.image)
        (hcD : (by classical exact (M.cover.branch.filter (· ∈ interior D)).card=2))
        (hcF : (by classical exact (M.cover.branch.filter (· ∈ interior F)).card=2)) : D=F := by
      classical
      obtain ⟨U,V,hU,hV,hUc,hVc,hUV,hcover,rest⟩ := M.puncturedCircle_closedSides c.val
      have hpart (K : Set B) (hK : IsClosed K) (hk : frontier K=c.val.image)
          (hcount : (M.cover.branch.filter (· ∈ interior K)).card=2) :
          interior K=U ∨ interior K=V := by
        obtain ⟨W,d,ho,hconn,hw,hwhole,hboundary,hinside⟩ :=
          M.arbitrary_two_mark_closed_side_adapter c K hK hk hcount
        have hconn' : IsConnected (interior K) := hw ▸ hconn
        have hsub : interior K ⊆ U ∪ V := by
          rw [hcover,← hk]
          exact fun x hx => Set.disjoint_left.mp disjoint_interior_frontier hx
        have hsep : interior K ∪ Kᶜ=c.val.imageᶜ := by
          rw [← hk]
          ext x
          simp only [frontier,hK.closure_eq,mem_sdiff,mem_union,mem_compl_iff]
          tauto
        have hn : (interior K).Nonempty := hconn'.nonempty
        have hforce (A : Set B) (hAc : IsConnected A) (hAs : A ⊆ c.val.imageᶜ)
            (hi : interior K ⊆ A) : interior K=A := by
          have ha := hAc.isPreconnected.subset_or_subset isOpen_interior hK.isOpen_compl
            (Set.disjoint_left.mpr (fun _ hxi hxo => hxo (interior_subset hxi)))
            (hsep.symm ▸ hAs)
          rcases ha with ha | ha
          · exact Subset.antisymm hi ha
          · obtain ⟨x,hx⟩ := hn
            exact False.elim (ha (hi hx) (interior_subset hx))
        rcases hconn'.isPreconnected.subset_or_subset hU hV hUV hsub with hi | hi
        · exact Or.inl (hforce U hUc (by rw [← hcover]; exact subset_union_left) hi)
        · exact Or.inr (hforce V hVc (by rw [← hcover]; exact subset_union_right) hi)
      have hsum : (M.cover.branch.filter (· ∈ U)).card+
          (M.cover.branch.filter (· ∈ V)).card=6 := by
        have hdis : Disjoint (M.cover.branch.filter (· ∈ U)) (M.cover.branch.filter (· ∈ V)) := by
          apply Finset.disjoint_left.mpr
          intro x hx hy
          exact Set.disjoint_left.mp hUV (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
        have he : M.cover.branch.filter (· ∈ U) ∪ M.cover.branch.filter (· ∈ V)=M.cover.branch := by
          ext x
          simp only [Finset.mem_union,Finset.mem_filter]
          constructor
          · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx
          · intro hx
            have hxc : x ∈ c.val.imageᶜ := fun he => Set.disjoint_left.mp c.val.avoids_branch he hx
            rcases (show x ∈ U ∪ V from hcover.symm ▸ hxc) with hu | hv
            · exact Or.inl ⟨hx,hu⟩
            · exact Or.inr ⟨hx,hv⟩
        rw [← Finset.card_union_of_disjoint hdis,he,M.cover.branch_card]
      have hint : interior D=interior F := by
        rcases hpart D hD hd hcD with hDu | hDv <;>
          rcases hpart F hF hf hcF with hFu | hFv
        · exact hDu.trans hFu.symm
        · rw [hDu] at hcD; rw [hFv] at hcF
          omega
        · rw [hDv] at hcD; rw [hFu] at hcF
          omega
        · exact hDv.trans hFv.symm
      have hdecomp (K : Set B) (hK : IsClosed K) : K=interior K ∪ frontier K := by
        rw [frontier,hK.closure_eq]
        ext x
        simp only [mem_union,mem_sdiff]
        exact ⟨fun hx => by by_cases hi : x ∈ interior K <;> aesop,
          fun h => h.elim (fun hi => interior_subset hi) And.left⟩
      rw [hdecomp D hD,hdecomp F hF,hd,hf,hint]
    have hclosed (c : NonLoopArc M) (N : ArcNeighborhood c) : IsClosed N.closedSet := by
      have hr : range (fun z => (N.disk z : B))=N.closedSet := by
        ext x
        constructor
        · rintro ⟨z,rfl⟩; exact (N.disk z).property
        · intro hx; exact ⟨N.disk.symm ⟨x,hx⟩,congrArg Subtype.val (N.disk.apply_symm_apply ⟨x,hx⟩)⟩
      rw [← hr]
      exact (isCompact_range (continuous_subtype_val.comp N.disk.continuous)).isClosed
    have hcount (c : NonLoopArc M) (N : ArcNeighborhood c) :
        (M.cover.branch.filter (· ∈ interior N.closedSet)).card=2 := by
      have he : (M.cover.branch.filter (· ∈ interior N.closedSet):Set B)=
          (M.cover.branch:Set B) ∩ interior N.closedSet := by ext x; simp
      rw [← Set.ncard_coe_finset,he]
      exact M.actual_arc_neighborhood_interior_marked_count c N
    obtain ⟨e,he⟩ := H.homeomorphism_at 1
    have hfinal : H.finalMap=e := funext (fun x => (he x).symm)
    have efix : ∀ x, x ∈ M.cover.branch → e x=x :=
      fun x hx => (he x).trans (hfix 1 x hx)
    have hfilter : M.cover.branch.filter (· ∈ interior (e '' Na.closedSet))=
        M.cover.branch.filter (· ∈ interior Na.closedSet) := by
      apply Finset.filter_congr
      intro x hx
      rw [← e.image_interior]
      constructor
      · rintro ⟨y,hy,hyx⟩
        have hy' : y=x := e.injective (hyx.trans (efix x hx).symm)
        exact hy' ▸ hy
      · intro hxN
        exact ⟨x,hxN,efix x hx⟩
    let c : Circle24 M := ⟨Nb.boundary,M.actual_arc_neighborhood_boundary_type b Nb⟩
    have hdisk : e '' Na.closedSet=Nb.closedSet := uniqueSide c _ _
      (e.isClosedMap _ (hclosed a Na)) (hclosed b Nb)
      (by rw [← e.image_frontier,← Na.boundary_eq_frontier,← hfinal]; exact hboundary)
      Nb.boundary_eq_frontier.symm
      (by rw [hfilter]; exact hcount a Na) (hcount b Nb)
    have hmarks : (M.cover.branch:Set B) ∩ (e '' Na.closedSet)=
        (M.cover.branch:Set B) ∩ Na.closedSet := by
      ext x
      constructor
      · rintro ⟨hm,⟨y,hy,hyx⟩⟩
        have hy' : y=x := e.injective (hyx.trans (efix x hm).symm)
        exact ⟨hm,hy' ▸ hy⟩
      · rintro ⟨hm,hx⟩
        exact ⟨hm,x,hx,efix x hm⟩
    have hends : ({a.val.map 0,a.val.map 1}:Set B)={b.val.map 0,b.val.map 1} := by
      have hm := hmarks
      rw [hdisk,Na.marked_inside,Nb.marked_inside] at hm
      convert hm.symm using 1
    let aT : NonLoopArc M := ⟨a.val.transport e efix,by
      change e (a.val.map ⟨0,by norm_num⟩) ≠ e (a.val.map ⟨1,by norm_num⟩)
      exact e.injective.ne a.property⟩
    have hat : aT.image=e '' a.image := MarkedArc.transport_image a.val e efix
    have ha0 : aT.val.map 0=a.val.map 0 := efix _ a.val.start_marked
    have ha1 : aT.val.map 1=a.val.map 1 := efix _ a.val.end_marked
    refine ⟨hfinal ▸ hdisk,aT,?_,?_,?_⟩
    · exact ⟨H,hfix,by rw [hfinal,hat]⟩
    · rw [hat,← hdisk,← e.image_interior]
      exact Set.image_mono Na.arc_inside
    · rw [ha0,ha1]
      exact hends
  obtain ⟨Na,pa,hpa⟩ := M.actual_nonloop_regular_arc_neighborhood a
  obtain ⟨Nb,pb,hpb⟩ := M.actual_nonloop_regular_arc_neighborhood b
  have hNa := M.actual_arc_neighborhood_boundary_type a Na
  have hNb := M.actual_arc_neighborhood_boundary_type b Nb
  obtain ⟨HA,hHAcore,hHA⟩ :=
    M.actual_nonloop_regular_neighborhood_lift_core_annulus a Na pa hpa
  obtain ⟨HB,hHBcore,hHB⟩ :=
    M.actual_nonloop_regular_neighborhood_lift_core_annulus b Nb pb hpb
  let ca : Circle24 M := ⟨Na.boundary,hNa⟩
  let cb : Circle24 M := ⟨Nb.boundary,hNb⟩
  have hboundUp : AmbientIsotopy.Rel
      (M.cover.projection ⁻¹' Na.boundary.image)
      (M.cover.projection ⁻¹' Nb.boundary.image) := by
    exact M.actual_nonloop_regular_neighborhood_boundaries_isotopic_of_cores
      a b Na Nb pa pb hpa hpb hup
  have hboundDown : MarkedIsotopyRel M Na.boundary.image Nb.boundary.image := by
    exact M.circle24_full_preimage_isotopy_descends_marked ca cb hboundUp
  obtain ⟨H,hHfix,hHboundary⟩ := hboundDown
  obtain ⟨hdisk,aIn,hmove,hinside,hends⟩ :=
    hBoundaryDiskTransport a b Na Nb H hHfix hHboundary
  let NIn : ArcNeighborhood aIn := {
    closedSet := Nb.closedSet
    disk := Nb.disk
    arc_inside := hinside
    marked_inside := by
      have he : (M.cover.branch:Set B) ∩ Nb.closedSet=
          ({b.val.map 0,b.val.map 1}:Set B) := by convert Nb.marked_inside using 1
      convert he.trans hends.symm using 1
    boundary := Nb.boundary
    boundary_eq_frontier := Nb.boundary_eq_frontier }
  obtain ⟨HD,hDoutside,hDmarked,hDimage⟩ :=
    M.actual_two_mark_disk_arcs_supported_marked_isotopy aIn b NIn Nb.arc_inside hends
  have hlocal : MarkedIsotopyRel M aIn.image b.image :=
    ⟨HD,hDmarked,hDimage⟩
  exact (markedIsotopy_equivalence M).trans hmove hlocal

private theorem vertex_map_injective : Function.Injective (nonloop_arc_vertex_map M) := by
  intro a b hab
  induction a, b using Quotient.inductionOn₂ with
  | h a b =>
    apply Quotient.sound
    apply marked_descent M a b
    have hraw := Quotient.exact hab
    change AmbientIsotopy.Rel
      (nonloop_arc_essential_preimage M a).val.image
      (nonloop_arc_essential_preimage M b).val.image at hraw
    rw [nonloop_arc_essential_preimage_image,
      nonloop_arc_essential_preimage_image] at hraw
    exact hraw

/-- This is a definition and class-identity reduction, not a geometry producer.
The representative already supplied here must be literally deck invariant. -/
private theorem project_named_nonloop_class
    (a : NonLoopArcClass M) (c : EssentialCurve S)
    (hc : Quotient.mk (essentialCurveSetoid S) c = nonloop_arc_vertex_map M a)
    (hinv : M.cover.deck '' c.val.image = c.val.image) :
    ∃ p : NonLoopArc M,
      Quotient.mk (nonLoopArcSetoid M) p = a ∧
      (nonloop_arc_essential_preimage M p).val.image = c.val.image := by
  classical
  have hconn : IsConnected c.val.imageᶜ := by
    induction a using Quotient.inductionOn with
    | h a =>
      have hrel := Quotient.exact hc
      change (essentialCurveSetoid S).r c (nonloop_arc_essential_preimage M a) at hrel
      exact (nonseparating_isotopy_invariant hrel).mpr
        (nonloop_arc_essential_preimage_complement_connected M a)
  rcases M.invariant_essential_curve_projects_dictionary c hinv with hp | hd
  · obtain ⟨p, hp⟩ := hp
    have himage : (nonloop_arc_essential_preimage M p).val.image = c.val.image :=
      (nonloop_arc_essential_preimage_image M p).trans hp.symm
    have hclass : nonloop_arc_vertex_map M (Quotient.mk (nonLoopArcSetoid M) p) =
        nonloop_arc_vertex_map M a := by
      rw [nonloop_arc_vertex_map_mk]
      apply Eq.trans _ hc
      apply Quotient.sound
      change AmbientIsotopy.Rel _ _
      rw [himage]
      exact (ambientIsotopy_equivalence (S := S)).refl _
    exact ⟨p, vertex_map_injective M hclass, himage⟩
  · obtain ⟨d, hd⟩ := hd
    exact False.elim ((M.circle33_preimage_complement_not_connected d)
      (hd ▸ hconn))

/-- Exact image equality transfers every part of the original topological
transversality predicate, including the common local crossing charts. -/
private theorem transverse_of_same_images
    (c d p q : Curve S) (hp : p.image = c.image) (hq : q.image = d.image)
    (ht : Transverse c d) : Transverse p q := by
  simpa only [Transverse, CrossesAt, hp, hq] using ht

/-- A purely logical adapter for an already produced invariant minimum pair.
Neither deck invariance nor attainment is established by this adapter. -/
theorem minimum_of_invariant_pair
    (a b : NonLoopArcClass M) (c d : EssentialCurve S)
    (hc : Quotient.mk (essentialCurveSetoid S) c = nonloop_arc_vertex_map M a)
    (hd : Quotient.mk (essentialCurveSetoid S) d = nonloop_arc_vertex_map M b)
    (hcinv : M.cover.deck '' c.val.image = c.val.image)
    (hdinv : M.cover.deck '' d.val.image = d.val.image)
    (ht : Transverse c.val d.val)
    (hcount : (c.val.image ∩ d.val.image).ncard =
      geometricIntersection (nonloop_arc_vertex_map M a) (nonloop_arc_vertex_map M b)) :
    ∃ p q : NonLoopArc M,
      Quotient.mk (nonLoopArcSetoid M) p = a ∧
      Quotient.mk (nonLoopArcSetoid M) q = b ∧
      Transverse (nonloop_arc_essential_preimage M p).val
        (nonloop_arc_essential_preimage M q).val ∧
      ((nonloop_arc_essential_preimage M p).val.image ∩
        (nonloop_arc_essential_preimage M q).val.image).ncard =
          geometricIntersection (nonloop_arc_vertex_map M a)
            (nonloop_arc_vertex_map M b) := by
  obtain ⟨p, hp, hpimage⟩ := project_named_nonloop_class M a c hc hcinv
  obtain ⟨q, hq, hqimage⟩ := project_named_nonloop_class M b d hd hdinv
  refine ⟨p, q, hp, hq,
    transverse_of_same_images c.val d.val _ _ hpimage hqimage ht, ?_⟩
  simpa only [hpimage, hqimage] using hcount

theorem vertex_map_injective_release : Function.Injective (nonloop_arc_vertex_map M) :=
  vertex_map_injective M

/-- Specialize the paid original finite-family minimum to the two literal
upstairs classes. This supplies no invariant representatives. -/
theorem ordinary_minimum_pair (a b : NonLoopArcClass M) (hab : a ≠ b) :
    ∃ c d : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) c = nonloop_arc_vertex_map M a ∧
      Quotient.mk (essentialCurveSetoid S) d = nonloop_arc_vertex_map M b ∧
      Transverse c.val d.val ∧
      (c.val.image ∩ d.val.image).ncard =
        geometricIntersection (nonloop_arc_vertex_map M a) (nonloop_arc_vertex_map M b) := by
  classical
  let A := nonloop_arc_vertex_map M a
  let B := nonloop_arc_vertex_map M b
  have hAB : A ≠ B := (vertex_map_injective M).ne hab
  let σ : Finset (Vertex S) := {A, B}
  have hA : A ∈ σ := by simp [σ]
  have hB : B ∈ σ := by simp [σ]
  obtain ⟨r, hr, ht⟩ := exists_finite_simultaneous_minimal_representatives
    S 2 (by omega) M.genusTwo σ
  obtain ⟨htrans, hcount⟩ := ht A hA B hB hAB
  refine ⟨r A hA, r B hB, hr A hA, hr B hB, htrans, ?_⟩
  exact (Set.ncard_eq_toFinset_card _ htrans.1).trans hcount

/-- Literal full inverse images are already preserved by the actual deck map. -/
theorem preimage_deck_invariant (p : NonLoopArc M) :
    M.cover.deck '' (nonloop_arc_essential_preimage M p).val.image =
      (nonloop_arc_essential_preimage M p).val.image := by
  rw [nonloop_arc_essential_preimage_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change M.cover.projection (M.cover.deck y) ∈ p.image
    rwa [M.cover.projection_deck]
  · intro hx
    refine ⟨M.cover.deck x, ?_, M.cover.deck_involution x⟩
    change M.cover.projection (M.cover.deck x) ∈ p.image
    rwa [M.cover.projection_deck]

private theorem image_relation_transport (e : S ≃ₜ S) (A D : Set S)
    (hAD : AmbientIsotopy.Rel A D) : AmbientIsotopy.Rel (e '' A) (e '' D) := by
  obtain ⟨H, hH⟩ := hAD
  let K : AmbientIsotopy S := {
    map := ⟨fun p => e (H.map (p.1, e.symm p.2)),
      e.continuous.comp (H.map.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨g, hg⟩ := H.homeomorphism_at t
      refine ⟨(e.symm.trans g).trans e, fun x => ?_⟩
      exact congrArg e (hg (e.symm x))
    at_zero := by
      intro x
      change e (H.map (⟨0, by norm_num⟩, e.symm x)) = x
      rw [H.at_zero, e.apply_symm_apply] }
  refine ⟨K, ?_⟩
  have he : K.finalMap ∘ e = e ∘ H.finalMap := by
    funext x
    change e (H.map (⟨1, by norm_num⟩, e.symm (e x))) = e (H.finalMap x)
    rw [e.symm_apply_apply]
    rfl
  rw [Set.image_image]
  change (K.finalMap ∘ e) '' A = e '' D
  rw [he, Set.image_comp, hH]

/-- A named nonloop image class is fixed by deck even when this particular
representative has no invariant image. This does not create such an image. -/
theorem deck_fixes_named_class_relation (a : NonLoopArcClass M) (c : EssentialCurve S)
    (hc : Quotient.mk (essentialCurveSetoid S) c = nonloop_arc_vertex_map M a) :
    AmbientIsotopy.Rel (M.cover.deck '' c.val.image) c.val.image := by
  induction a using Quotient.inductionOn with
  | h a =>
    have hrel := Quotient.exact hc
    change AmbientIsotopy.Rel c.val.image (nonloop_arc_essential_preimage M a).val.image at hrel
    have hdeck := image_relation_transport M.cover.deck _ _ hrel
    rw [preimage_deck_invariant M a] at hdeck
    exact (ambientIsotopy_equivalence (S := S)).trans hdeck
      ((ambientIsotopy_equivalence (S := S)).symm hrel)

/-- The completely disjoint representative case of the exact minimum goal
needs no transversality perturbation: there are no crossing points. -/
theorem minimum_of_disjoint_images (a b : NonLoopArcClass M) (p q : NonLoopArc M)
    (hp : Quotient.mk (nonLoopArcSetoid M) p = a)
    (hq : Quotient.mk (nonLoopArcSetoid M) q = b)
    (hd : Disjoint p.image q.image) :
    Transverse (nonloop_arc_essential_preimage M p).val
      (nonloop_arc_essential_preimage M q).val ∧
    ((nonloop_arc_essential_preimage M p).val.image ∩
      (nonloop_arc_essential_preimage M q).val.image).ncard =
        geometricIntersection (nonloop_arc_vertex_map M a) (nonloop_arc_vertex_map M b) := by
  classical
  have hempty : (nonloop_arc_essential_preimage M p).val.image ∩
      (nonloop_arc_essential_preimage M q).val.image = ∅ := by
    rw [nonloop_arc_essential_preimage_image, nonloop_arc_essential_preimage_image,
      ← Set.preimage_inter, Set.disjoint_iff_inter_eq_empty.mp hd, Set.preimage_empty]
  have ht : Transverse (nonloop_arc_essential_preimage M p).val
      (nonloop_arc_essential_preimage M q).val := by
    refine ⟨hempty ▸ Set.finite_empty, ?_⟩
    intro x hx
    simpa only [hempty, Set.mem_empty_iff_false] using hx
  have hz : geometricIntersection (nonloop_arc_vertex_map M a)
      (nonloop_arc_vertex_map M b) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    refine ⟨nonloop_arc_essential_preimage M p, nonloop_arc_essential_preimage M q,
      ?_, ?_, ht, ?_⟩
    · rw [← nonloop_arc_vertex_map_mk, hp]
    · rw [← nonloop_arc_vertex_map_mk, hq]
    · rw [← Set.ncard_eq_toFinset_card _ ht.1, hempty, Set.ncard_empty]
  refine ⟨ht, ?_⟩
  rw [hempty, Set.ncard_empty, hz]

end CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal

#print axioms CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal.minimum_of_invariant_pair
#print axioms CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal.vertex_map_injective_release
#print axioms CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal.ordinary_minimum_pair
#print axioms CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal.preimage_deck_invariant
#print axioms CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal.deck_fixes_named_class_relation
#print axioms CurveComplexGenusTwo.SourceTopology.MinimumProjectionInternal.minimum_of_disjoint_images
