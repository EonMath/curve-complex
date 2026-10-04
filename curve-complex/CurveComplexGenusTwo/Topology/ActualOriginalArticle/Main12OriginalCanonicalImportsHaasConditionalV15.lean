import CurveComplexGenusTwo.Hyperbolic.InvariantRepresentative.InvariantRepresentativeComplete85
import CurveComplexGenusTwo.Topology.ActualAcyclicity.ActualAOriginalAcyclicProof
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualConeOriginalSourceAlignmentCompleteCandidate
import CurveComplexGenusTwo.Topology.ActualNonloopNormalization.ActualGoodActiveNonloopIdentification
import CurveComplexGenusTwo.Topology.ActualGoodFiniteFaceCorrespondence.ActualGoodFiniteFaceCorrespondencePROVED
import CurveComplexGenusTwo.Topology.ActualGoodFiniteFaceCorrespondence.Main12OriginalRegularArcNeighborhood
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14OriginalCircle24DescentConsume
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalBoundaryPairCanonicalNamedConsumeProof
import CurveComplexGenusTwo.Topology.ActualMain14OriginalD.Main14OriginalDiskSupportedCancellationConsumePROVED
import CurveComplexGenusTwo.Dictionary.Circle24.ClosedTwoMarkSideAdapter
import CurveComplexGenusTwo.Topology.ActualMarkedAnnulus.Main14ActualMarkedAnnulusPackage
import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential
import CurveComplexGenusTwo.Dictionary.CircleVertexAPI
import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Foundations.VertexEquiv
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.GenusTwoActualAlternatingTotalRecognition
import CurveComplexGenusTwo.Filtration.ActualPositiveComparison.OriginalPositiveComparison
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers
import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12FullConnectivity
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.ConeChains
import CurveComplexGenusTwo.Filtration.GoodSubcomplexAcyclic
import CurveComplexGenusTwo.Topology.ActualAlternatingModelTransfer
import CurveComplexGenusTwo.Topology.ArcCounts.ActualFullACard12
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalClassificationStatements
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import Mathlib.Topology.Connected.Clopen
import CurveComplexGenusTwo.Topology.ActualSeparatingNonadjacency.OriginalSeparatingNonadjacencyProof
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardTorusSurface
import CurveComplexGenusTwo.Topology.CapBandGeometry.DiskOpen
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualIntegerBasisTorusHomeomorph
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualLiftedAxisChart
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.OriginalGenusTwoSeparatingActualCut
import CurveComplexGenusTwo.Topology.ActualCutRecognition.SharedActualCut
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTranslatedPrimitiveSource
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleProjectionEssential
import CurveComplexGenusTwo.Foundations.NonseparatingRealizationBridge
import CurveComplexGenusTwo.Topology.FareyDictionaryStarDeletionConsumer
import CurveComplexGenusTwo.Topology.ActualSDR.OriginalSourceSDRPROVED
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped Simplicial
namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CurveComplex.HyperellipticModel
open CurveComplexGenusTwo.Topology
open scoped Manifold ContDiff
open Set Topology Schoenflies
set_option maxHeartbeats 30000000

open ContinuousMap

theorem c1_acyclic_genusTwo
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hS : IsGenus S 2) :
    IsAcyclicIntegral (curveComplexRealization S 1) := by
  -- The source theorem header and all its contexts are unchanged.
  constructor
  · intro n hn
    let X := TopCat.of (curveComplexRealization S 1)
    -- Pending actual geometric producer: every genuine singular cycle fills.
    -- This is a proof obligation, not an added theorem hypothesis.
    have hfill_actual_curve_cycles :
        ∀ z : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ,
          z ∈ CurveComplexGenusTwo.CWHurewicz.absoluteSingularCycles X n →
          ∃ b : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ,
            CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp X n b = z := by
      classical
      -- Recover the original actual model from the paid recognition theorem.
      let B := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
      have hmodel : Nonempty (HyperellipticModel S B) := by
        -- Original homological genus-two S is homeomorphic to the actual
        -- canonical alternating six-branch total by the paid recognition.
        have hsurface_homeomorph : Nonempty (S ≃ₜ AlternatingSphereCover.Total) := by
          exact genusTwo_homeomorphic_actual_alternating_total S hS
        exact actual_alternating_model_transfer S hS
          (Classical.choice hsurface_homeomorph)
      let M := Classical.choice hmodel
      letI : LinearOrder (HyperellipticModel.EssentialArcClass M) :=
        linearOrderOfSTO WellOrderingRel
      letI main12DecidableEq : DecidableEq (HyperellipticModel.EssentialArcClass M) :=
        LinearOrder.toDecidableEq
      let K := HyperellipticModel.actualA M
      let a := HyperellipticModel.actualArcLabels M
      -- Full A-simplex cardinal bound, including loop classes.
      have hcard : ∀ σ : Finset (HyperellipticModel.EssentialArcClass M),
          σ ∈ K → σ.card ≤ 12 := by
        intro σ hσ
        exact HyperellipticModel.actualA_card_le_twelve M σ hσ
      -- Canonical original all-integer A acyclicity, accepted at 1b4bbea.
      have hA : ∀ q : ℤ, -1 ≤ q →
          Subsingleton (CurveGenusTwo.Filtration.reducedHomology K q) := by
        intro q _
        exact HyperellipticModel.actualA_reducedHomology_zero M q
      -- Universal positive-stratum cones, not merely an aligned two-mark piece.
      have hcones : ∀ p : ℕ, 1 ≤ p →
          ∀ T : CurveGenusTwo.Filtration.strata K a p,
            CurveGenusTwo.Filtration.IsNonemptyCone
              (CurveGenusTwo.Filtration.restrictedLink K a T) := by
        intro p hp T
        have hdec : main12DecidableEq =
            HyperellipticModel.integrationLocalInstance_ActualArcFiltrationV3_1 M :=
          Subsingleton.elim _ _
        have hconeDec : main12DecidableEq =
            HyperellipticModel.instDecidableEqEssentialArcClass_8 M :=
          Subsingleton.elim _ _
        let T' : HyperellipticModel.ActualStratum M p :=
          ⟨T.val, by simpa (config := { instances := true }) only [K, a, ← hdec] using T.property⟩
        simpa (config := { instances := true }) [CurveGenusTwo.Filtration.IsNonemptyCone,
          HyperellipticModel.actualRestrictedLink, CurveGenusTwo.Filtration.restrictedLink,
          CurveGenusTwo.Filtration.restrictedLinkSet,
          CurveGenusTwo.Filtration.badVertices, K, a, T', ← hdec, ← hconeDec] using
          (HyperellipticModel.actualRestrictedLink_cone M p hp T')
      have hlinks : ∀ p : ℕ, 1 ≤ p →
          ∀ T : CurveGenusTwo.Filtration.strata K a p, ∀ q : ℤ,
            -1 ≤ q → Subsingleton (CurveGenusTwo.Filtration.reducedHomology
              (CurveGenusTwo.Filtration.restrictedLink K a T) q) := by
        intro p hp T q hq
        exact CurveGenusTwo.Filtration.nonemptyCone_reducedHomology _
          (hcones p hp T) q hq
      have hgood := CurveGenusTwo.Filtration.goodSubcomplex_acyclic K a hcard hA hlinks
      -- Original filtration, positive comparison and SDR are paid.
      -- The literal finite-face geometry is paid; the dictionary needs Haas.
      have hactual_curve_transport :
          Subsingleton (CurveGenusTwo.Filtration.reducedHomology
            (CurveGenusTwo.Filtration.goodSubcomplex K a) (n : ℤ)) →
          ∀ z : (TopCat.toSSet.obj X) _⦋n⦌ →₀ ℤ,
            z ∈ CurveComplexGenusTwo.CWHurewicz.absoluteSingularCycles X n →
            ∃ b : (TopCat.toSSet.obj X) _⦋n + 1⦌ →₀ ℤ,
              CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp X n b = z := by
        let G := CurveGenusTwo.Filtration.goodSubcomplex K a
        have hactual_realization_transport : Nonempty
            (ContinuousMap.HomotopyEquiv
              (CurveGenusTwo.Filtration.geometricRealization G)
              (curveComplexRealization S 1)) := by
          have hfinite_face_dictionary : ∃ v :
              CurveGenusTwo.Filtration.ActiveVertex G ≃
                {a : Vertex S // nonseparatingVertex a},
              ∀ σ : Finset (CurveGenusTwo.Filtration.ActiveVertex G),
                σ ∈ (CurveGenusTwo.Filtration.geometricComplex G).faces ↔
                  σ.image v ∈ (nonseparatingComplex S).faces := by
            -- Retain the SAME coordinate witness and its literal class equation.
            obtain ⟨eArc, heArc⟩ := actual_good_active_nonloop_identification_exists M
            have hpreimage_nonseparating : ∀ a : HyperellipticModel.NonLoopArcClass M,
                nonseparatingVertex (HyperellipticModel.nonloop_arc_vertex_map M a) := by
              intro a
              induction a using Quotient.inductionOn with
              | h a =>
                change IsConnected (HyperellipticModel.nonloop_arc_essential_preimage M a).val.imageᶜ
                exact HyperellipticModel.nonloop_arc_essential_preimage_complement_connected M a
            let fArc : HyperellipticModel.NonLoopArcClass M →
                {a : Vertex S // nonseparatingVertex a} :=
              fun a => ⟨HyperellipticModel.nonloop_arc_vertex_map M a, hpreimage_nonseparating a⟩
            have hactual_nonloop_dictionary : Function.Bijective fArc ∧
                ∀ σ : Finset (CurveGenusTwo.Filtration.ActiveVertex G),
                  σ ∈ (CurveGenusTwo.Filtration.geometricComplex G).faces ↔
                    σ.image (fun a => fArc (eArc a)) ∈ (nonseparatingComplex S).faces := by
              -- Exact original Haas producer; analytic deck identity remains open.
              have hInv : ∀ c : EssentialCurve S, ∃ d : EssentialCurve S,
                  (essentialCurveSetoid S).r c d ∧
                  M.cover.deck '' d.val.image = d.val.image := by
                intro c
                exact HyperellipticModel.essential_curve_has_deck_invariant_representative M c
              -- Paid all-finite-face theorem on the SAME literal coordinate map.
              have hfaceDec :
                  (inferInstance : DecidableEq {a : Vertex S // nonseparatingVertex a}) =
                    instDecidableEqSubtypeVertexNonseparatingVertex_1 :=
                Subsingleton.elim _ _
              have hf : ∀ σ : Finset (CurveGenusTwo.Filtration.ActiveVertex G),
                  σ ∈ (CurveGenusTwo.Filtration.geometricComplex G).faces ↔
                    σ.image (fun a => fArc (eArc a)) ∈ (nonseparatingComplex S).faces := by
                simpa (config := { instances := true }) only [← hfaceDec, fArc] using
                  (actual_good_finite_face_correspondence M eArc heArc hpreimage_nonseparating)
              have hDesc (a b : HyperellipticModel.NonLoopArc M)
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
              have hi : Function.Injective fArc := by
                intro a b hab
                have hv : HyperellipticModel.nonloop_arc_vertex_map M a =
                    HyperellipticModel.nonloop_arc_vertex_map M b := congrArg Subtype.val hab
                induction a, b using Quotient.inductionOn₂ with
                | h a b =>
                  apply Quotient.sound
                  apply hDesc a b
                  have hraw := Quotient.exact hv
                  change AmbientIsotopy.Rel
                    (HyperellipticModel.nonloop_arc_essential_preimage M a).val.image
                    (HyperellipticModel.nonloop_arc_essential_preimage M b).val.image at hraw
                  rw [HyperellipticModel.nonloop_arc_essential_preimage_image,
                    HyperellipticModel.nonloop_arc_essential_preimage_image] at hraw
                  exact hraw
              have hsurj : ∀ v : {v : Vertex S // nonseparatingVertex v},
                  ∃ a : HyperellipticModel.NonLoopArcClass M,
                    HyperellipticModel.nonloop_arc_vertex_map M a = v.val := by
                intro v
                obtain ⟨c, hc⟩ := Quotient.exists_rep v.val
                obtain ⟨d, hcd, hdeck⟩ := hInv c
                have hconnc : Nonseparating c.val := by
                  have hv := v.property
                  rw [← hc] at hv
                  exact hv
                have hconnd : IsConnected d.val.imageᶜ :=
                  (nonseparating_isotopy_invariant hcd).mp hconnc
                obtain (⟨a, ha⟩ | ⟨a, ha⟩) := HyperellipticModel.invariant_essential_curve_projects_dictionary M d hdeck
                · refine ⟨Quotient.mk (HyperellipticModel.nonLoopArcSetoid M) a, ?_⟩
                  rw [HyperellipticModel.nonloop_arc_vertex_map_mk]
                  have hd : Quotient.mk (essentialCurveSetoid S) d =
                      Quotient.mk (essentialCurveSetoid S) (HyperellipticModel.nonloop_arc_essential_preimage M a) := by
                    apply Quotient.sound
                    change AmbientIsotopy.Rel d.val.image (HyperellipticModel.nonloop_arc_essential_preimage M a).val.image
                    rw [ha, HyperellipticModel.nonloop_arc_essential_preimage_image]
                    exact ambientIsotopy_equivalence.refl _
                  exact hd.symm.trans ((Quotient.sound hcd).symm.trans hc)
                · exact False.elim ((HyperellipticModel.circle33_preimage_complement_not_connected M a)
                    (ha ▸ hconnd))
              have hs : Function.Surjective fArc := by
                intro v
                obtain ⟨a, ha⟩ := hsurj v
                exact ⟨a, Subtype.ext ha⟩
              exact ⟨⟨hi, hs⟩, hf⟩
            obtain ⟨hb, hf⟩ := hactual_nonloop_dictionary
            exact ⟨eArc.trans (Equiv.ofBijective fArc hb), hf⟩
          obtain ⟨v, hface⟩ := hfinite_face_dictionary
          have hSDR := nonseparating_strongDeformationRetract_genusTwo S hS
          have h : Nonempty ((NonseparatingLocus S) ≃ₕ curveComplexRealization S 1) := by
            obtain ⟨H, hzero, hone, hfix⟩ := hSDR
            let i : C(NonseparatingLocus S,curveComplexRealization S 1) := ⟨Subtype.val, continuous_subtype_val⟩
            let r : C(curveComplexRealization S 1,NonseparatingLocus S) := ⟨fun x => ⟨H (x,timeOne),hone x⟩,
              (H.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk _⟩
            have hr : r.comp i = ContinuousMap.id (NonseparatingLocus S) := by
              apply ContinuousMap.ext
              intro x
              apply Subtype.ext
              exact hfix x.val x.property timeOne
            let F : ContinuousMap.Homotopy (ContinuousMap.id (curveComplexRealization S 1)) (i.comp r) := {
              toFun := fun tx => H (tx.2,tx.1)
              continuous_toFun := H.continuous.comp (continuous_snd.prodMk continuous_fst)
              map_zero_left := hzero
              map_one_left := fun _ => rfl }
            exact ⟨{toFun := i
                    invFun := r
                    left_inv := by rw [hr]
                    right_inv := ⟨F.symm⟩}⟩
          obtain ⟨r⟩ := h
          let e := (realizationHomeomorphOfVertexEquiv (CurveGenusTwo.Filtration.geometricComplex G)
            (nonseparatingComplex S) v hface).trans (nonseparatingRealizationHomeomorph S)
          exact ⟨e.toHomotopyEquiv.trans r⟩
        let e := Classical.choice hactual_realization_transport
        intro hzero z hz
        letI := hzero
        obtain ⟨c⟩ := CurveGenusTwo.Filtration.augmented_singular_comparison_positive G n hn
        have hfinite : CategoryTheory.Limits.IsZero (CurveComplex.integralHomology (CurveGenusTwo.Filtration.geometricRealization G) n) :=
          (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (CurveGenusTwo.Filtration.reducedHomology G (n : ℤ)))).of_iso c.symm
        have hY : CategoryTheory.Limits.IsZero (CurveComplex.integralHomology (curveComplexRealization S 1) n) :=
          hfinite.of_iso (CircleHomologyComputation.homotopyHomologyIso e n).symm
        have hraw : CategoryTheory.Limits.IsZero ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).homology n) :=
          hY.of_iso (CurveComplexGenusTwo.CWHurewicz.singularHomologyRepresentation X n)
        have hexact := (HomologicalComplex.exactAt_iff_isZero_homology _ n).mpr hraw
        rw [HomologicalComplex.exactAt_iff, CategoryTheory.ShortComplex.moduleCat_exact_iff] at hexact
        change ∀ x, ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).d n
          ((ComplexShape.down ℕ).next n)).hom x = 0 →
          ∃ b, ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).d
            ((ComplexShape.down ℕ).prev n) n).hom b = x at hexact
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        rw [ChainComplex.next_nat_succ, ChainComplex.prev] at hexact
        have hz' : CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp X k z = 0 := hz
        have hker : ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).d (k+1) k).hom z = 0 := by
          simpa only [CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex, ChainComplex.of_d, ModuleCat.hom_ofHom] using hz'
        obtain ⟨b, hb⟩ := hexact z hker
        refine ⟨b, ?_⟩
        simpa only [CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex, ChainComplex.of_d, ModuleCat.hom_ofHom] using hb
      exact hactual_curve_transport (hgood n (by omega))
    have hexact : (CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).ExactAt n := by
      rw [HomologicalComplex.exactAt_iff]
      rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_ker_sub_range]
      intro z hz
      have hcycle : z ∈ CurveComplexGenusTwo.CWHurewicz.absoluteSingularCycles X n := by
        have hg := LinearMap.mem_ker.mp hz
        change (CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).d n
          ((ComplexShape.down ℕ).next n) z = 0 at hg
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
        rw [ChainComplex.next_nat_succ] at hg
        change CurveComplexGenusTwo.CWHurewicz.singularBoundaryFinsupp X k z = 0
        change (CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).d (k + 1) k z = 0 at hg
        change ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).d (k + 1) k).hom z = 0 at hg
        simpa only [CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex,
          ChainComplex.of_d, ModuleCat.hom_ofHom] using hg
      obtain ⟨b, hb⟩ := hfill_actual_curve_cycles z hcycle
      change z ∈ LinearMap.range
        ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).d
          ((ComplexShape.down ℕ).prev n) n).hom
      rw [ChainComplex.prev]
      simp only [CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex, ChainComplex.of_d]
      exact ⟨b, hb⟩
    exact hexact.isZero_homology.of_iso
      (CurveComplexGenusTwo.CWHurewicz.singularHomologyRepresentation X n).symm
  · -- Paid actual full-C1 connectivity supplies the augmented H0 condition.
    have hpath_actual_curve_realization : PathConnectedSpace (curveComplexRealization S 1) := by
      exact source_genus_two_full_curve_realization_pathConnected S hS
    letI := hpath_actual_curve_realization
    infer_instance

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.c1_acyclic_genusTwo
