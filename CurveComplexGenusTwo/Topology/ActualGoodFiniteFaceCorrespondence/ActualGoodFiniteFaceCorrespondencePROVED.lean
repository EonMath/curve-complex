import CurveComplexGenusTwo.Topology.ActualNonloopNormalization.ActualGoodActiveNonloopIdentification
import CurveComplexGenusTwo.Topology.ActualNonloopNormalization.ActualNonloopDisjointPairNormalization
import CurveComplexGenusTwo.Topology.ActualGoodFiniteFaceCorrespondence.ActualNonloopPairMinimumFullPreimagesPROVED
import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Intersection.FiniteCount
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Foundations.SourceNonseparating
import CurveComplexGenusTwo.Foundations.SingularComparison
import CurveComplexGenusTwo.Filtration.ActualFiltrationEndpointProgress
import CurveComplexGenusTwo.Filtration.OriginalEndpoints.OriginalActualXSubcomplexActualA
import CurveComplexGenusTwo.Topology.ActualGoodFiniteFaceCorrespondence.Main12OriginalRegularArcNeighborhood
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14OriginalCircle24DescentConsume
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalBoundaryPairCanonicalNamedConsumeProof
import CurveComplexGenusTwo.Topology.ActualMain14OriginalD.Main14OriginalDiskSupportedCancellationConsumePROVED
import CurveComplexGenusTwo.Dictionary.Circle24.ClosedTwoMarkSideAdapter

/-!
Source: curve-complex-genus-two.pdf, Corollary 5.7, Proposition 6.1,
and Lemma 8.5(iii). This file isolates the finite-face conjunct of
Main12CanonicalBCDNonloopDescentConsumerV11.lean, lines 209--211.

The complexes, quotient classes, endpoint labels and full-preimage map below
are the existing canonical definitions. The original finite-face statements are preserved verbatim.
The `eArc` equation retains the literal class identification; a bare arbitrary
equivalence between the two vertex types does not retain that identification.
-/

open Lean Elab Tactic in
elab "audit_actual_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in actual subproof from {c}: {ax}"
  logInfo m!"Actual isolated subproof axiom audit: {found.toList}"

namespace CurveComplexGenusTwo.SourceTopology

open CurveComplex CurveComplex.HyperellipticModel CurveGenusTwo.Filtration
open Set _root_.Topology Schoenflies
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

variable {S B : Type} [TopologicalSpace S] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  (M : HyperellipticModel S B)

noncomputable local instance : DecidableEq {a : Vertex S // nonseparatingVertex a} :=
  Classical.decEq _

/-- Corollary 5.7 in the graph notation of Definition 2.5, with the literal
canonical full-preimage map on the source's non-loop marked isotopy classes.
No simultaneous-family or minimum certificate is supplied as a hypothesis. -/
theorem actual_nonloop_preimage_adjacent_iff
    (a b : NonLoopArcClass M) (hab : a ≠ b) :
    ArcAdjacent M (nonloopToEssentialClass M a) (nonloopToEssentialClass M b) ↔
      geometricIntersection (nonloop_arc_vertex_map M a)
        (nonloop_arc_vertex_map M b) ≤ 1 := by
  classical
  have hπ : CurveComplex.Intersection.HasBranchFiberCounts
      M.cover.projection (M.cover.branch : Set B) := by
    audit_actual_base3
     constructor
     · intro x hx
       obtain ⟨w, hw⟩ := M.cover.projection_surjective x
       have hfixed : M.cover.deck w = w :=
         (M.cover.fixed_iff_branch w).mpr (hw ▸ hx)
       have hfiber : M.cover.projection ⁻¹' ({x} : Set B) = {w} := by
         ext y
         constructor
         · intro hy
           have hwy : M.cover.projection w = M.cover.projection y :=
             hw.trans (Set.mem_singleton_iff.mp hy).symm
           rcases (M.cover.fiber_pair w y).mp hwy with h | h
           · exact Set.mem_singleton_iff.mpr h
           · exact Set.mem_singleton_iff.mpr (h.trans hfixed)
         · intro hy
           simpa [Set.mem_singleton_iff.mp hy, hw]
       rw [hfiber, Set.ncard_singleton]
     · intro x hx
       obtain ⟨w, hw⟩ := M.cover.projection_surjective x
       have hne : w ≠ M.cover.deck w := by
         intro he
         have hbranch := (M.cover.fixed_iff_branch w).mp he.symm
         exact hx (hw ▸ hbranch)
       have hfiber : M.cover.projection ⁻¹' ({x} : Set B) =
           {w, M.cover.deck w} := by
         ext y
         constructor
         · intro hy
           have hwy : M.cover.projection w = M.cover.projection y :=
             hw.trans (Set.mem_singleton_iff.mp hy).symm
           rcases (M.cover.fiber_pair w y).mp hwy with h | h
           · exact Set.mem_insert_iff.mpr (Or.inl h)
           · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))
         · intro hy
           rcases Set.mem_insert_iff.mp hy with rfl | hy
           · simpa [hw]
           · have : y = M.cover.deck w := Set.mem_singleton_iff.mp hy
             subst y
             simpa [M.cover.projection_deck, hw]
       rw [hfiber, Set.ncard_pair hne]

  have hcount (x y : NonLoopArc M) (hfinite : (x.image ∩ y.image).Finite) :
      ((M.cover.projection ⁻¹' x.image) ∩
        (M.cover.projection ⁻¹' y.image)).ncard =
      2 * (arcInterior M x.toEssential ∩ arcInterior M y.toEssential).ncard +
        (arcEndpoints M x.toEssential ∩ arcEndpoints M y.toEssential).card := by
    audit_actual_base3
     have hm (c : NonLoopArc M) (z : B) (hz : z ∈ M.cover.branch) :
         z ∈ c.image ↔ z ∈ arcEndpoints M c.toEssential := by
       constructor
       · rintro ⟨t, ht⟩
         rcases c.val.marked_only_at_ends t (ht ▸ hz) with rfl | rfl <;>
           change _ ∈ ({c.val.map ⟨0, by norm_num⟩, c.val.map ⟨1, by norm_num⟩} : Finset B) <;>
           simp [← ht]
       · intro he
         change z ∈ ({c.val.map ⟨0, by norm_num⟩, c.val.map ⟨1, by norm_num⟩} : Finset B) at he
         rcases Finset.mem_insert.mp he with he | he
         · exact ⟨⟨0, by norm_num⟩, he.symm⟩
         · exact ⟨⟨1, by norm_num⟩, (Finset.mem_singleton.mp he).symm⟩
     have hemark (c : NonLoopArc M) (z : B)
         (hz : z ∈ arcEndpoints M c.toEssential) : z ∈ M.cover.branch := by
       change z ∈ ({c.val.map ⟨0, by norm_num⟩, c.val.map ⟨1, by norm_num⟩} : Finset B) at hz
       rcases Finset.mem_insert.mp hz with hz | hz
       · exact hz.symm ▸ c.val.start_marked
       · exact (Finset.mem_singleton.mp hz).symm ▸ c.val.end_marked
     have hdecomp : x.image ∩ y.image =
         (arcInterior M x.toEssential ∩ arcInterior M y.toEssential) ∪
           (x.image ∩ y.image ∩ (M.cover.branch : Set B)) := by
       ext z
       constructor
       · rintro ⟨hx, hy⟩
         by_cases hz : z ∈ M.cover.branch
         · exact Or.inr ⟨⟨hx, hy⟩, hz⟩
         · exact Or.inl ⟨⟨hx, hz⟩, ⟨hy, hz⟩⟩
       · rintro (⟨hx, hy⟩ | ⟨⟨hx, hy⟩, _⟩)
         · exact ⟨hx.1, hy.1⟩
         · exact ⟨hx, hy⟩
     have hdis : Disjoint (arcInterior M x.toEssential ∩ arcInterior M y.toEssential)
         (M.cover.branch : Set B) := Set.disjoint_left.mpr (fun _ hz hb => hz.1.2 hb)
     have hmarks : x.image ∩ y.image ∩ (M.cover.branch : Set B) =
         ((arcEndpoints M x.toEssential ∩ arcEndpoints M y.toEssential : Finset B) : Set B) := by
       ext z
       simp only [Finset.mem_coe, Finset.mem_inter]
       constructor
       · rintro ⟨⟨hx, hy⟩, hz⟩
         exact ⟨(hm x z hz).mp hx, (hm y z hz).mp hy⟩
       · rintro ⟨hx, hy⟩
         have hz := hemark x z hx
         exact ⟨⟨(hm x z hz).mpr hx, (hm y z hz).mpr hy⟩, hz⟩
     have hc := CurveComplex.Intersection.local_count_of_fibers
       M.cover.projection (M.cover.branch : Set B) x.image y.image
       (arcInterior M x.toEssential) (arcInterior M y.toEssential)
       hfinite hdecomp hdis hπ
     simpa only [hmarks, Set.ncard_coe_finset] using hc
  have hcard (x : NonLoopArc M) : (arcEndpoints M x.toEssential).card = 2 := by
    change ({x.val.map ⟨0, by norm_num⟩, x.val.map ⟨1, by norm_num⟩} : Finset B).card = 2
    exact Finset.card_pair x.property
  have hnormalize (x y : NonLoopArc M)
      (hd : Disjoint (arcInterior M x.toEssential) (arcInterior M y.toEssential)) :
      ∃ p q : NonLoopArc M,
        Quotient.mk (nonLoopArcSetoid M) p = Quotient.mk (nonLoopArcSetoid M) x ∧
        Quotient.mk (nonLoopArcSetoid M) q = Quotient.mk (nonLoopArcSetoid M) y ∧
        Disjoint (arcInterior M p.toEssential) (arcInterior M q.toEssential) ∧
        Transverse (nonloop_arc_essential_preimage M p).val
          (nonloop_arc_essential_preimage M q).val := by
    exact actual_nonloop_disjoint_pair_transverse_full_preimages M x y hd
  have hminimum : ∃ p q : NonLoopArc M,
      Quotient.mk (nonLoopArcSetoid M) p = a ∧
      Quotient.mk (nonLoopArcSetoid M) q = b ∧
      Transverse (nonloop_arc_essential_preimage M p).val
        (nonloop_arc_essential_preimage M q).val ∧
      ((nonloop_arc_essential_preimage M p).val.image ∩
        (nonloop_arc_essential_preimage M q).val.image).ncard =
          geometricIntersection (nonloop_arc_vertex_map M a)
            (nonloop_arc_vertex_map M b) := by
    exact actual_nonloop_pair_minimum_full_preimages M a b hab
  have hnonloop (x : NonLoopArcClass M) :
      ¬ (actualArcLabels M).isLoop (nonloopToEssentialClass M x) := by
    induction x using Quotient.inductionOn with
    | h x =>
      change ¬ (arcEndpoints M x.toEssential).card = 1
      rw [hcard]; norm_num
  constructor
  · rintro ⟨_, _, _, hendpoints, x, y, hx, hy, hdis⟩
    have hn (z : EssentialMarkedArc M) (w : NonLoopArcClass M)
        (hz : Quotient.mk (essentialArcSetoid M) z = nonloopToEssentialClass M w) :
        z.val.map ⟨0, by norm_num⟩ ≠ z.val.map ⟨1, by norm_num⟩ := by
      intro heq
      apply hnonloop w
      change (classEndpoints M (nonloopToEssentialClass M w)).card = 1
      rw [← hz]
      change (arcEndpoints M z).card = 1
      change ({z.val.map ⟨0, by norm_num⟩, z.val.map ⟨1, by norm_num⟩} : Finset B).card = 1
      rw [heq]
      simp
    let x' : NonLoopArc M := ⟨x.val, hn x a hx⟩
    let y' : NonLoopArc M := ⟨y.val, hn y b hy⟩
    have hx' : Quotient.mk (nonLoopArcSetoid M) x' = a := by
      apply nonloopToEssentialClass_injective M
      exact hx
    have hy' : Quotient.mk (nonLoopArcSetoid M) y' = b := by
      apply nonloopToEssentialClass_injective M
      exact hy
    obtain ⟨p, q, hp, hq, hd, ht⟩ := hnormalize x' y' hdis
    have hpclass : Quotient.mk (nonLoopArcSetoid M) p = a := hp.trans hx'
    have hqclass : Quotient.mk (nonLoopArcSetoid M) q = b := hq.trans hy'
    have hpends : arcEndpoints M p.toEssential = classEndpoints M (nonloopToEssentialClass M a) := by
      rw [← hpclass]; rfl
    have hqends : arcEndpoints M q.toEssential = classEndpoints M (nonloopToEssentialClass M b) := by
      rw [← hqclass]; rfl
    have hfin : (p.image ∩ q.image).Finite := by
      have hff := ht.1.image M.cover.projection
      rw [nonloop_arc_essential_preimage_image, nonloop_arc_essential_preimage_image] at hff
      have he : M.cover.projection '' ((M.cover.projection ⁻¹' p.image) ∩
          (M.cover.projection ⁻¹' q.image)) = p.image ∩ q.image := by
        rw [← Set.preimage_inter]
        exact Set.image_preimage_eq _ M.cover.projection_surjective
      rwa [he] at hff
    have hc := hcount p q hfin
    have hd0 : arcInterior M p.toEssential ∩ arcInterior M q.toEssential = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hd
    rw [hd0, Set.ncard_empty, mul_zero, zero_add] at hc
    have hbound : (arcEndpoints M p.toEssential ∩ arcEndpoints M q.toEssential).card ≤ 1 :=
      (CurveComplex.Intersection.endpoint_count_le_one_iff_ne _ _ (hcard p) (hcard q)).mpr
        (by rw [hpends, hqends]; exact hendpoints)
    have hcountle : ht.1.toFinset.card ≤ 1 := by
      rw [← Set.ncard_eq_toFinset_card _ ht.1,
        nonloop_arc_essential_preimage_image, nonloop_arc_essential_preimage_image,
        hc]
      exact hbound
    have hmem : ht.1.toFinset.card ∈ intersectionCounts
        (nonloop_arc_vertex_map M a) (nonloop_arc_vertex_map M b) := by
      refine ⟨nonloop_arc_essential_preimage M p, nonloop_arc_essential_preimage M q, ?_, ?_, ht, rfl⟩
      · rw [← hpclass, nonloop_arc_vertex_map_mk]
      · rw [← hqclass, nonloop_arc_vertex_map_mk]
    exact (Nat.sInf_le hmem).trans hcountle
  · intro hle
    obtain ⟨p, q, hp, hq, ht, hmin⟩ := hminimum
    have hfin : (p.image ∩ q.image).Finite := by
      have hff := ht.1.image M.cover.projection
      rw [nonloop_arc_essential_preimage_image, nonloop_arc_essential_preimage_image] at hff
      have he : M.cover.projection '' ((M.cover.projection ⁻¹' p.image) ∩
          (M.cover.projection ⁻¹' q.image)) = p.image ∩ q.image := by
        rw [← Set.preimage_inter]
        exact Set.image_preimage_eq _ M.cover.projection_surjective
      rwa [he] at hff
    have hc := hcount p q hfin
    have hmin' := hmin
    rw [nonloop_arc_essential_preimage_image, nonloop_arc_essential_preimage_image] at hmin'
    have hn : (arcInterior M p.toEssential ∩ arcInterior M q.toEssential).ncard = 0 := by omega
    have he : (arcEndpoints M p.toEssential ∩ arcEndpoints M q.toEssential).card ≤ 1 := by omega
    have hifin : (arcInterior M p.toEssential ∩ arcInterior M q.toEssential).Finite :=
      hfin.subset (fun _ hz => ⟨hz.1.1, hz.2.1⟩)
    have hd : Disjoint (arcInterior M p.toEssential) (arcInterior M q.toEssential) :=
      Set.disjoint_iff_inter_eq_empty.mpr ((Set.ncard_eq_zero hifin).mp hn)
    have hends : arcEndpoints M p.toEssential ≠ arcEndpoints M q.toEssential :=
      (CurveComplex.Intersection.endpoint_count_le_one_iff_ne _ _ (hcard p) (hcard q)).mp he
    refine ⟨(nonloopToEssentialClass_injective M).ne hab, hnonloop a, hnonloop b, ?_,
      p.toEssential, q.toEssential, ?_, ?_, hd⟩
    · rw [← hp, ← hq]
      exact hends
    · rw [← hp]; rfl
    · rw [← hq]; rfl

variable [LinearOrder (EssentialArcClass M)]

/-- Proposition 6.1 combined with Lemma 8.5(iii): for every finite set of
active good vertices, its membership in the geometric good complex is
equivalent to membership of its literal full-preimage image in the actual
nonseparating curve complex.

`heArc` pins the coordinate equivalence to the already existing class map.
`hpreimage_nonseparating` is the already derived subtype proof used by Main12;
it imposes no intersection or simultaneous-representative assumption.
No bijection, intersection formula, invariant-representative theorem, or
desired finite-face property is taken as a premise. -/
theorem actual_good_finite_face_correspondence
    (eArc :
      ActiveVertex (goodSubcomplex (actualA M) (actualArcLabels M)) ≃
        NonLoopArcClass M)
    (heArc : ∀ a, nonloopToEssentialClass M (eArc a) = a.val)
    (hpreimage_nonseparating : ∀ a : NonLoopArcClass M,
      nonseparatingVertex (nonloop_arc_vertex_map M a)) :
    ∀ σ : Finset (ActiveVertex (goodSubcomplex (actualA M) (actualArcLabels M))),
      σ ∈ (geometricComplex (goodSubcomplex (actualA M) (actualArcLabels M))).faces ↔
        σ.image (fun a =>
          (⟨nonloop_arc_vertex_map M (eArc a), hpreimage_nonseparating (eArc a)⟩ :
            {a : Vertex S // nonseparatingVertex a})) ∈
              (nonseparatingComplex S).faces := by
  classical
  let : DecidableEq (EssentialArcClass M) := LinearOrder.toDecidableEq
  let : DecidableEq B := Classical.decEq B
  have hDesc (a b : HyperellipticModel.NonLoopArc M)
      (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' a.image)
        (M.cover.projection ⁻¹' b.image)) :
      HyperellipticModel.MarkedIsotopyRel M a.image b.image := by
    audit_actual_base3
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
  have hi : Function.Injective (nonloop_arc_vertex_map M) := by
    intro a b hab
    induction a, b using Quotient.inductionOn₂ with
    | h a b =>
      apply Quotient.sound
      apply hDesc a b
      have hraw := Quotient.exact hab
      change AmbientIsotopy.Rel
        (nonloop_arc_essential_preimage M a).val.image
        (nonloop_arc_essential_preimage M b).val.image at hraw
      rw [nonloop_arc_essential_preimage_image,
        nonloop_arc_essential_preimage_image] at hraw
      exact hraw
  let f : ActiveVertex (goodSubcomplex (actualA M) (actualArcLabels M)) →
      {a : Vertex S // nonseparatingVertex a} :=
    fun a => ⟨nonloop_arc_vertex_map M (eArc a), hpreimage_nonseparating (eArc a)⟩
  have hf : Function.Injective (fun a => (f a).val) := by
    intro a b hab
    exact eArc.injective (hi hab)
  have hnonloop (a : ActiveVertex (goodSubcomplex (actualA M) (actualArcLabels M))) :
      ¬ (actualArcLabels M).isLoop a.val := by
    have h := a.property
    change ({a.val} : Finset _) ∈ actualA M ∧
      (badVertices (actualArcLabels M) {a.val}).card ≤ (0 : ℤ) at h
    intro hl
    have hm : a.val ∈ badVertices (actualArcLabels M) {a.val} :=
      Finset.mem_filter.mpr ⟨Finset.mem_singleton_self _, Or.inl hl⟩
    have hp := Finset.card_pos.mpr ⟨_, hm⟩
    omega
  intro σ
  change (σ.Nonempty ∧ σ.image Subtype.val ∈
      goodSubcomplex (actualA M) (actualArcLabels M)) ↔
    ((σ.image f).image Subtype.val).Nonempty ∧
      ∀ v ∈ (σ.image f).image Subtype.val,
        ∀ w ∈ (σ.image f).image Subtype.val,
          v ≠ w → geometricIntersection v w ≤ 1
  have hσnon : ((σ.image f).image Subtype.val).Nonempty ↔ σ.Nonempty := by
    simp only [Finset.image_nonempty]
  constructor
  · rintro ⟨hσnonempty, hσgood⟩
    have hX : σ.image Subtype.val ∈ actualX M := by
      change σ.image Subtype.val ∈ actualA M ∧
        (badVertices (actualArcLabels M) (σ.image Subtype.val)).card ≤ (0 : ℤ) at hσgood
      have hbad : badVertices (actualArcLabels M) (σ.image Subtype.val) = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      have hnotbad (v) : v ∉ badVertices (actualArcLabels M) (σ.image Subtype.val) := by
        rw [hbad]; simp
      change IsXSimplex M (σ.image Subtype.val)
      refine ⟨?_, ?_⟩
      · intro v hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        exact hnonloop a
      · intro v hv w hw hvw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
        refine ⟨hvw, hnonloop a, hnonloop b, ?_, ?_⟩
        · intro heq
          exact hnotbad a.val (Finset.mem_filter.mpr
            ⟨Finset.mem_image.mpr ⟨a, ha, rfl⟩,
              Or.inr ⟨b.val, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
                hvw.symm, hnonloop a, hnonloop b, heq.symm⟩⟩)
        · obtain ⟨r, hr, hd⟩ := hσgood.1
          refine ⟨r ⟨a.val, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩,
            r ⟨b.val, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩,
            hr _, hr _, hd _ _ ?_⟩
          intro heq
          exact hvw (congrArg (fun z : {v // v ∈ σ.image Subtype.val} => z.val) heq)
    refine ⟨hσnon.mpr hσnonempty, ?_⟩
    intro v hv w hw hvw
    obtain ⟨av, hav, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨bv, hbv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hav
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hbv
    have hab : a ≠ b := fun heq => hvw (heq ▸ rfl)
    apply (actual_nonloop_preimage_adjacent_iff M (eArc a) (eArc b)
      (eArc.injective.ne hab)).mp
    rw [heArc, heArc]
    exact hX.2 a.val (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
      b.val (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      (fun heq => hab (Subtype.ext heq))
  · rintro ⟨hσnonempty, hcurve⟩
    have hX : σ.image Subtype.val ∈ actualX M := by
      change IsXSimplex M (σ.image Subtype.val)
      refine ⟨?_, ?_⟩
      · intro v hv
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        exact hnonloop a
      · intro v hv w hw hvw
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
        have hab : a ≠ b := fun heq => hvw (congrArg Subtype.val heq)
        have hle := hcurve (f a).val
          (Finset.mem_image.mpr ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, rfl⟩)
          (f b).val
          (Finset.mem_image.mpr ⟨f b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, rfl⟩)
          (hf.ne hab)
        have hadj := (actual_nonloop_preimage_adjacent_iff M (eArc a) (eArc b)
          (eArc.injective.ne hab)).mpr hle
        rwa [heArc, heArc] at hadj
    refine ⟨hσnon.mp hσnonempty, ?_⟩
    change σ.image Subtype.val ∈ actualA M ∧
      (badVertices (actualArcLabels M) (σ.image Subtype.val)).card ≤ (0 : ℤ)
    refine ⟨actualX_subcomplex_actualA M _ hX, ?_⟩
    have hbad : badVertices (actualArcLabels M) (σ.image Subtype.val) = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      rcases Finset.mem_filter.mp hv with ⟨hvσ, hl | ⟨w, hwσ, hwv, _, _, heq⟩⟩
      · exact hX.1 v hvσ hl
      · exact (hX.2 v hvσ w hwσ hwv.symm).2.2.2.1 heq.symm
    rw [hbad]
    simp

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonloop_preimage_adjacent_iff
#print axioms CurveComplexGenusTwo.SourceTopology.actual_good_active_nonloop_identification_exists
#print axioms CurveComplexGenusTwo.SourceTopology.actual_good_finite_face_correspondence
