import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedDiskFreeDescent
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.MarkedDescentCandidate
import CurveComplexGenusTwo.Topology.ActualMain14CNext.actual_given_paired_component_reference_returning_diskNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.ActualRelativeFiniteCancellationComplete
import CurveComplexGenusTwo.Topology.ActualMain14FinitePreparation.Main14ActualOriginalDiskRelativeFinitePreparationNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.ActualOriginalDisjointDiskArcsSupportedTerminalAlignment
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskActualCoverAssemblyProved
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalBoundaryPairCanonicalNamedConsumeProof
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenToConstructedCommonPairLocal
import CurveComplexGenusTwo.Topology.ActualMarkedAnnulus.Main14ActualMarkedAnnulusPackage
import CurveComplexGenusTwo.Dictionary.Circle24.ClosedTwoMarkSideAdapter
import CurveComplexGenusTwo.Topology.WeightedSurgery.EssentialArcHomeomorphismHeaders
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.ActualTwoEndpointPuncturedJordan
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteTransverseNewArc
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualTwoMarkDiskComparisonRegion
import CurveComplexGenusTwo.Filtration.Geometry.ActualEmptyBigonUnorderedClassNamedHeader
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Topology.ActualGoodFiniteFaceCorrespondence.Main12OriginalRegularArcNeighborhood
import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ClosedAssignment
import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14Circle33InitialTransversePreparation
import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14Circle33ActualReturningCriterion
import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential

import CurveComplexGenusTwo.Hyperbolic.InvariantRepresentative.InvariantRepresentativeComplete85

namespace CurveComplex.HyperellipticModel

open Set Topology Schoenflies
set_option maxHeartbeats 30000000

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The induced full-preimage correspondence of Theorem 1.4. -/
theorem headline_hyperelliptic_dictionary (M : HyperellipticModel E S) :
    ∃! f : (NonLoopArcClass M ⊕ Circle33Class M) ≃ Vertex E,
      (∀ a : NonLoopArc M,
        ∃ c : EssentialCurve E,
          c.val.image = M.cover.projection ⁻¹' a.image ∧
          f (Sum.inl (Quotient.mk (nonLoopArcSetoid M) a)) =
            Quotient.mk (essentialCurveSetoid E) c ∧
          IsConnected c.val.imageᶜ) ∧
      (∀ a : Circle33 M,
        ∃ c : EssentialCurve E,
          c.val.image = M.cover.projection ⁻¹' a.val.image ∧
          f (Sum.inr (Quotient.mk (circle33Setoid M) a)) =
            Quotient.mk (essentialCurveSetoid E) c ∧
          ¬ IsConnected c.val.imageᶜ) := by
  classical
  have hOriginalC
      (c d : Circle24 M)
      (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
        (M.cover.projection ⁻¹' d.val.image)) :
      MarkedIsotopyRel M c.val.image d.val.image := by
    classical
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have hDiskFree := M.actual_original_circle24_paired_four_crosspair_disk_free_preparation c d hup
    obtain ⟨c',d',hci,hdi,htbase,a0,a1,b0,b1,H,ha,hb,hAd,hBd,hDA,hDB,hH0,hH1,hap0,hap1,hbp0,hbp1,hAc0,hAc1,hBc0,hBc1,ht00,ht01,ht10,ht11,hfree00,hfree01,hfree10,hfree11⟩ := hDiskFree
    have hp0 : b0.val.image ⊆ M.cover.projection ⁻¹' d'.val.image := by
      intro x hx
      have hh : x ∈ b0.val.image ∪ b1.val.image := Or.inl hx
      rw [hb] at hh
      exact hh
    have hp1 : b1.val.image ⊆ M.cover.projection ⁻¹' d'.val.image := by
      intro x hx
      have hh : x ∈ b0.val.image ∪ b1.val.image := Or.inr hx
      rw [hb] at hh
      exact hh
    have hiso0 : AmbientIsotopy.Rel a0.val.image b0.val.image := ⟨H,hH0⟩
    have hiso1 : AmbientIsotopy.Rel a1.val.image b1.val.image := ⟨H,hH1⟩
    have hdisjoint : Disjoint c'.val.image d'.val.image := by
      apply Set.disjoint_left.mpr
      intro y hyc hyd
      obtain ⟨x,rfl⟩ := M.cover.projection_surjective y
      have hxa : x ∈ a0.val.image ∪ a1.val.image := by rw [ha]; exact hyc
      have hxb : x ∈ b0.val.image ∪ b1.val.image := by rw [hb]; exact hyd
      rcases hxa with hx0 | hx1 <;> rcases hxb with hy0 | hy1
      · exact hfree00.false (M.actual_given_paired_component_reference_returning_disk a0 b0 b0 d'.val hp0 hp0 ht00 hiso0 ⟨x,hx0,hy0⟩).some
      · exact hfree01.false (M.actual_given_paired_component_reference_returning_disk a0 b0 b1 d'.val hp0 hp1 ht01 hiso0 ⟨x,hx0,hy1⟩).some
      · exact hfree10.false (M.actual_given_paired_component_reference_returning_disk a1 b1 b0 d'.val hp1 hp0 ht10 hiso1 ⟨x,hx1,hy0⟩).some
      · exact hfree11.false (M.actual_given_paired_component_reference_returning_disk a1 b1 b1 d'.val hp1 hp1 ht11 hiso1 ⟨x,hx1,hy1⟩).some
    have hup' : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c'.val.image) (M.cover.projection ⁻¹' d'.val.image) := by
      refine ⟨H,?_⟩
      rw [←ha,←hb,Set.image_union,hH0,hH1]
    have hTerminal := M.actual_original_disjoint_circle24_full_preimage_isotopy_descends_marked c' d' hup' hdisjoint
    exact (markedIsotopy_equivalence M).trans hci
      ((markedIsotopy_equivalence M).trans hTerminal ((markedIsotopy_equivalence M).symm hdi))
  have hSupportedOriginalD
      (a b : NonLoopArc M)
      (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
      (hends : ({a.val.map 0,a.val.map 1} : Set S) = {b.val.map 0,b.val.map 1}) :
      ∃ H : AmbientIsotopy S,
        (∀ t x, x ∉ interior N.closedSet → H.map (t,x) = x) ∧
        (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
        H.finalMap '' a.image = b.image := by
    classical
    let Q : Set S := (interior N.closedSet)ᶜ ∪ (M.cover.branch:Set S)
    let R : Set S → Set S → Prop := fun A B => ∃ H : AmbientIsotopy S,
      (∀ t x, x ∈ Q → H.map (t,x)=x) ∧ H.finalMap '' A=B
    have hEquiv : Equivalence R := by
        let zero : Interval := ⟨0, by norm_num⟩
        let one : Interval := ⟨1, by norm_num⟩
        let reverse : Interval → Interval := fun t =>
          ⟨1 - (t : ℝ), by
            rcases t.property with ⟨h0, h1⟩
            constructor <;> linarith⟩
        have reverse_cont : Continuous reverse :=
          (continuous_const.sub continuous_subtype_val).subtype_mk (fun t => (reverse t).property)
        let first : Interval → Interval := fun t =>
          ⟨min (2 * (t : ℝ)) 1, by
            rcases t.property with ⟨h0, h1⟩
            exact ⟨le_min (by linarith) (by norm_num), min_le_right _ _⟩⟩
        let second : Interval → Interval := fun t =>
          ⟨max (2 * (t : ℝ) - 1) 0, by
            rcases t.property with ⟨h0, h1⟩
            exact ⟨le_max_right _ _, max_le (by linarith) (by norm_num)⟩⟩
        have first_cont : Continuous first :=
          ((continuous_const.mul continuous_subtype_val).min continuous_const).subtype_mk
            (fun t => (first t).property)
        have second_cont : Continuous second :=
          (((continuous_const.mul continuous_subtype_val).sub continuous_const).max
            continuous_const).subtype_mk (fun t => (second t).property)
        have reverse_zero : reverse zero = one := Subtype.ext (by norm_num [reverse, zero, one])
        have reverse_one : reverse one = zero := Subtype.ext (by norm_num [reverse, zero, one])
        have first_zero : first zero = zero := Subtype.ext (by norm_num [first, zero])
        have first_one : first one = one := Subtype.ext (by norm_num [first, one])
        have second_zero : second zero = zero := Subtype.ext (by norm_num [second, zero])
        have second_one : second one = one := Subtype.ext (by norm_num [second, one])
        constructor
        · intro a
          refine ⟨{ map := ⟨fun p => p.2, continuous_snd⟩
                    homeomorphism_at := ?_
                    at_zero := by intro x; rfl }, ?_, ?_⟩
          · intro t
            exact ⟨Homeomorph.refl S, fun x => rfl⟩
          · intro t x hx; rfl
          · change (id : S → S) '' a = a
            exact Set.image_id a
        · intro a b hab
          obtain ⟨H, hfixH, hH⟩ := hab
          obtain ⟨h, hh⟩ := H.homeomorphism_at one
          have hfinal : ∀ x, h x = H.finalMap x := hh
          let K : AmbientIsotopy S := {
            map := ⟨fun p => H.map (reverse p.1, h.symm p.2), by
              exact H.map.continuous.comp
                ((reverse_cont.comp continuous_fst).prodMk
                  (h.symm.continuous.comp continuous_snd))⟩
            homeomorphism_at := by
              intro t
              obtain ⟨g, hg⟩ := H.homeomorphism_at (reverse t)
              exact ⟨h.symm.trans g, fun x => by
                simpa [Homeomorph.trans_apply] using (hg (h.symm x))⟩
            at_zero := by
              intro x
              change H.map (reverse zero, h.symm x) = x
              rw [reverse_zero]
              rw [← hh]
              exact h.apply_symm_apply x }
          refine ⟨K, ?_, ?_⟩
          · intro t x hx
            have hf : h x = x := by rw [hh]; exact hfixH one x hx
            have hi : h.symm x = x := (congrArg h.symm hf.symm).trans (h.symm_apply_apply x)
            change H.map (reverse t, h.symm x)=x
            rw [hi]
            exact hfixH (reverse t) x hx
          · have hKfinal : ∀ x, K.finalMap x = h.symm x := by
              intro x
              change H.map (reverse one, h.symm x) = h.symm x
              rw [reverse_one]
              exact H.at_zero _
            simp_rw [hKfinal]
            have himage : h '' a = b := by
              simpa only [← hfinal] using hH
            rw [← himage]
            simp [Set.image_image]
        · intro a b c hab hbc
          obtain ⟨H, hfixH, hH⟩ := hab
          obtain ⟨K, hfixK, hK⟩ := hbc
          let L : AmbientIsotopy S := {
            map := ⟨fun p => K.map (second p.1, H.map (first p.1, p.2)), by
              exact K.map.continuous.comp
                ((second_cont.comp continuous_fst).prodMk
                  (H.map.continuous.comp
                    ((first_cont.comp continuous_fst).prodMk continuous_snd)))⟩
            homeomorphism_at := by
              intro t
              obtain ⟨h, hh⟩ := H.homeomorphism_at (first t)
              obtain ⟨k, hk⟩ := K.homeomorphism_at (second t)
              exact ⟨h.trans k, fun x => by simp [Homeomorph.trans_apply, hh, hk]⟩
            at_zero := by
              intro x
              change K.map (second zero, H.map (first zero, x)) = x
              rw [first_zero, second_zero]
              rw [H.at_zero, K.at_zero] }
          refine ⟨L, ?_, ?_⟩
          · intro t x hx
            change K.map (second t, H.map (first t,x))=x
            rw [hfixH (first t) x hx,hfixK (second t) x hx]
          · have hLfinal : ∀ x, L.finalMap x = K.finalMap (H.finalMap x) := by
              intro x
              change K.map (second one, H.map (first one, x)) =
                K.map (one, H.map (one, x))
              rw [first_one, second_one]
            simp_rw [hLfinal]
            change (K.finalMap ∘ H.finalMap) '' a = c
            rw [Set.image_comp, hH, hK]
        
    have hEnds (u v : NonLoopArc M) (H : AmbientIsotopy S)
        (hfix : ∀ t x, x ∈ M.cover.branch → H.map (t,x)=x)
        (himage : H.finalMap '' u.image=v.image) :
        ({u.val.map 0,u.val.map 1}:Set S)={v.val.map 0,v.val.map 1} := by
      have hE : (markedArcEndset u.val:Set S)=(markedArcEndset v.val:Set S) := by
        rw [←markedArc_image_inter_branch,←markedArc_image_inter_branch]
        obtain ⟨f,hf⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
        have hi : Function.Injective H.finalMap := by
          intro x y h; exact f.injective (by simpa only [hf,AmbientIsotopy.finalMap] using h)
        ext x
        constructor
        · rintro ⟨hu,hx⟩
          refine ⟨?_,hx⟩
          change x ∈ v.image
          rw [←himage]
          exact ⟨x,hu,hfix _ x hx⟩
        · rintro ⟨hv,hx⟩
          change x ∈ v.image at hv
          rw [←himage] at hv
          obtain ⟨y,hy,he⟩ := hv
          have hyx : y=x := hi (he.trans (hfix _ x hx).symm)
          exact ⟨hyx ▸ hy,hx⟩
      simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton] at hE
      convert hE using 1
    obtain ⟨a',b',H,K,hHo,hKo,hHm,hKm,hHi,hKi,ha',hb',hfinite,hcross⟩ :=
      M.actual_two_mark_disk_relative_finite_transverse_preparation a b N hb hends
    have hea := hEnds a a' H hHm hHi
    have heb := hEnds b b' K hKm hKi
    have heab : ({a'.val.map 0,a'.val.map 1}:Set S)={b'.val.map 0,b'.val.map 1} :=
      hea.symm.trans (hends.trans heb)
    let N' : ArcNeighborhood a' := {
      closedSet := N.closedSet
      disk := N.disk
      arc_inside := ha'
      marked_inside := N.marked_inside.trans hea
      boundary := N.boundary
      boundary_eq_frontier := N.boundary_eq_frontier }
    have hCancellation : ∃ b'' : NonLoopArc M, ∃ L : AmbientIsotopy S,
        (∀ t x, x ∉ interior N'.closedSet → L.map (t,x)=x) ∧
        (∀ t x, x ∈ M.cover.branch → L.map (t,x)=x) ∧
        L.finalMap '' b'.image=b''.image ∧ b''.image ⊆ interior N'.closedSet ∧
        Disjoint (a'.image \ (M.cover.branch:Set S))
          (b''.image \ (M.cover.branch:Set S)) := by
      exact M.actual_two_mark_disk_relative_finite_cancellation a' b' N' hb' heab hfinite hcross
    obtain ⟨b'',L,hLo,hLm,hLi,hb'',hd⟩ := hCancellation
    have heab'' := heab.trans (hEnds b' b'' L hLm hLi)
    have hmeet : a'.image ∩ b''.image={a'.val.map 0,a'.val.map 1} := by
      change a'.val.image ∩ b''.val.image=_
      change Disjoint (a'.val.image \ (M.cover.branch:Set S)) (b''.val.image \ (M.cover.branch:Set S)) at hd
      rw [markedArc_disjoint_interiors_inter_image a'.val b''.val hd]
      simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton]
      have hh : (markedArcEndset a'.val:Set S)=(markedArcEndset b''.val:Set S) := by
        simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton]
        convert heab'' using 1
      simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton] at hh
      rw [←hh]
      convert Set.inter_self ({a'.val.map 0,a'.val.map 1}:Set S) using 1
  
    obtain ⟨T,hTo,hTm,hTi⟩ :=
      M.actual_original_disjoint_disk_arcs_supported_terminal_alignment a' b'' N' hb'' heab'' hmeet
    have fixed (F : AmbientIsotopy S)
        (ho : ∀ t x, x ∉ interior N.closedSet → F.map (t,x)=x)
        (hm : ∀ t x, x ∈ M.cover.branch → F.map (t,x)=x) :
        ∀ t x, x ∈ Q → F.map (t,x)=x := by
      intro t x hx
      rcases hx with hx | hx
      · exact ho t x hx
      · exact hm t x hx
    have hrH : R a.image a'.image := ⟨H,fixed H hHo hHm,hHi⟩
    have hrK : R b.image b'.image := ⟨K,fixed K hKo hKm,hKi⟩
    have hrL : R b'.image b''.image := ⟨L,fixed L hLo hLm,hLi⟩
    have hrT : R a'.image b''.image := ⟨T,fixed T hTo hTm,hTi⟩
    obtain ⟨F,hFfix,hFi⟩ := hEquiv.trans hrH
      (hEquiv.trans hrT (hEquiv.trans (hEquiv.symm hrL) (hEquiv.symm hrK)))
    exact ⟨F,(fun t x hx => hFfix t x (Or.inl hx)),
      (fun t x hx => hFfix t x (Or.inr hx)),hFi⟩
  have hArcFinitePreparation (a b : NonLoopArc M)
      (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' a.image)
        (M.cover.projection ⁻¹' b.image)) :
      ∃ a' b' : NonLoopArc M,
        MarkedIsotopyRel M a'.image a.image ∧
        MarkedIsotopyRel M b'.image b.image ∧
        AmbientIsotopy.Rel (M.cover.projection ⁻¹' a'.image)
          (M.cover.projection ⁻¹' b'.image) ∧
        (ArcSurgery.crossings M a'.toEssential b'.toEssential).Finite ∧
        ∀ p ∈ ArcSurgery.crossings M a'.toEssential b'.toEssential,
          ArcSurgery.CrossesInDisk M a'.toEssential b'.toEssential p := by
    classical
    have hn (c : NonLoopArc M) :
        ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) c.toEssential) := by
      change ({c.val.map ⟨0,by norm_num⟩,c.val.map ⟨1,by norm_num⟩}:Finset S).card ≠ 1
      have hc : c.val.map 0 ≠ c.val.map 1 := by convert c.property using 1
      change ({c.val.map 0,c.val.map 1}:Finset S).card ≠ 1
      rw [Finset.card_pair hc]
      norm_num
    obtain ⟨old',b0,hold,hdis,hb,hfinite⟩ :=
      M.actual_finite_transverse_arc_insertion (fun _ : Unit => a.toEssential)
        (fun _ => hn a) (fun i j hij => False.elim (hij (Subsingleton.elim _ _)))
        b.toEssential (hn b)
    have hna : ¬ (actualArcLabels M).isLoop
        (Quotient.mk (essentialArcSetoid M) (old' ())) := by rw [hold ()]; exact hn a
    have hnb : ¬ (actualArcLabels M).isLoop
        (Quotient.mk (essentialArcSetoid M) b0) := by rw [hb]; exact hn b
    let a' : NonLoopArc M := ⟨(old' ()).val,M.actualRepresentative_nonloop (old' ()) hna⟩
    let b' : NonLoopArc M := ⟨b0.val,M.actualRepresentative_nonloop b0 hnb⟩
    have ha' : MarkedIsotopyRel M a'.image a.image := Quotient.exact (hold ())
    have hb' : MarkedIsotopyRel M b'.image b.image := Quotient.exact hb
    have hu' : AmbientIsotopy.Rel (M.cover.projection ⁻¹' a'.image)
        (M.cover.projection ⁻¹' b'.image) :=
      ambientIsotopy_equivalence.trans (M.marked_isotopy_preimage ha')
        (ambientIsotopy_equivalence.trans hup
          (ambientIsotopy_equivalence.symm (M.marked_isotopy_preimage hb')))
    exact ⟨a',b',ha',hb',hu',(hfinite ()).1,(hfinite ()).2⟩
  have hBoundaryDiskTransport (a b : NonLoopArc M)
      (Na : ArcNeighborhood a) (Nb : ArcNeighborhood b)
      (H : AmbientIsotopy S)
      (hfix : ∀ t x, x ∈ M.cover.branch → H.map (t,x)=x)
      (hboundary : H.finalMap '' Na.boundary.image=Nb.boundary.image) :
      H.finalMap '' Na.closedSet=Nb.closedSet ∧
        ∃ aT : NonLoopArc M,
          MarkedIsotopyRel M a.image aT.image ∧ aT.image ⊆ interior Nb.closedSet ∧
          ({aT.val.map 0,aT.val.map 1}:Set S)={b.val.map 0,b.val.map 1} := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    have uniqueSide (c : Circle24 M) (D F : Set S)
        (hD : IsClosed D) (hF : IsClosed F)
        (hd : frontier D=c.val.image) (hf : frontier F=c.val.image)
        (hcD : (by classical exact (M.cover.branch.filter (· ∈ interior D)).card=2))
        (hcF : (by classical exact (M.cover.branch.filter (· ∈ interior F)).card=2)) : D=F := by
      classical
      obtain ⟨U,V,hU,hV,hUc,hVc,hUV,hcover,rest⟩ := M.puncturedCircle_closedSides c.val
      have hpart (K : Set S) (hK : IsClosed K) (hk : frontier K=c.val.image)
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
        have hforce (A : Set S) (hAc : IsConnected A) (hAs : A ⊆ c.val.imageᶜ)
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
      have hdecomp (K : Set S) (hK : IsClosed K) : K=interior K ∪ frontier K := by
        rw [frontier,hK.closure_eq]
        ext x
        simp only [mem_union,mem_sdiff]
        exact ⟨fun hx => by by_cases hi : x ∈ interior K <;> aesop,
          fun h => h.elim (fun hi => interior_subset hi) And.left⟩
      rw [hdecomp D hD,hdecomp F hF,hd,hf,hint]
    have hclosed (c : NonLoopArc M) (N : ArcNeighborhood c) : IsClosed N.closedSet := by
      have hr : range (fun z => (N.disk z : S))=N.closedSet := by
        ext x
        constructor
        · rintro ⟨z,rfl⟩; exact (N.disk z).property
        · intro hx; exact ⟨N.disk.symm ⟨x,hx⟩,congrArg Subtype.val (N.disk.apply_symm_apply ⟨x,hx⟩)⟩
      rw [← hr]
      exact (isCompact_range (continuous_subtype_val.comp N.disk.continuous)).isClosed
    have hcount (c : NonLoopArc M) (N : ArcNeighborhood c) :
        (M.cover.branch.filter (· ∈ interior N.closedSet)).card=2 := by
      have he : (M.cover.branch.filter (· ∈ interior N.closedSet):Set S)=
          (M.cover.branch:Set S) ∩ interior N.closedSet := by ext x; simp
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
    have hmarks : (M.cover.branch:Set S) ∩ (e '' Na.closedSet)=
        (M.cover.branch:Set S) ∩ Na.closedSet := by
      ext x
      constructor
      · rintro ⟨hm,⟨y,hy,hyx⟩⟩
        have hy' : y=x := e.injective (hyx.trans (efix x hm).symm)
        exact ⟨hm,hy' ▸ hy⟩
      · rintro ⟨hm,hx⟩
        exact ⟨hm,x,hx,efix x hm⟩
    have hends : ({a.val.map 0,a.val.map 1}:Set S)={b.val.map 0,b.val.map 1} := by
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
  have harcinj : Function.Injective M.nonloop_arc_vertex_map := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        apply Quotient.sound
        have hup := Quotient.exact hab
        change AmbientIsotopy.Rel (M.nonloop_arc_essential_preimage a).val.image
          (M.nonloop_arc_essential_preimage b).val.image at hup
        rw [M.nonloop_arc_essential_preimage_image,M.nonloop_arc_essential_preimage_image] at hup
        have hdown : MarkedIsotopyRel M a.image b.image := by
          obtain ⟨a',b',ha',hb',hup',hfinite,hcross⟩ := hArcFinitePreparation a b hup
          have hpreparedDown : MarkedIsotopyRel M a'.image b'.image := by
            obtain ⟨Na,pa,hpa⟩ := M.actual_nonloop_regular_arc_neighborhood a'
            obtain ⟨Nb,pb,hpb⟩ := M.actual_nonloop_regular_arc_neighborhood b'
            have hNa := M.actual_arc_neighborhood_boundary_type a' Na
            have hNb := M.actual_arc_neighborhood_boundary_type b' Nb
            obtain ⟨HA,hHAcore,hHA⟩ :=
              M.actual_nonloop_regular_neighborhood_lift_core_annulus a' Na pa hpa
            obtain ⟨HB,hHBcore,hHB⟩ :=
              M.actual_nonloop_regular_neighborhood_lift_core_annulus b' Nb pb hpb
            let ca : Circle24 M := ⟨Na.boundary,hNa⟩
            let cb : Circle24 M := ⟨Nb.boundary,hNb⟩
            have hboundUp : AmbientIsotopy.Rel
                (M.cover.projection ⁻¹' Na.boundary.image)
                (M.cover.projection ⁻¹' Nb.boundary.image) := by
              exact M.actual_nonloop_regular_neighborhood_boundaries_isotopic_of_cores
                a' b' Na Nb pa pb hpa hpb hup'
            have hboundDown : MarkedIsotopyRel M Na.boundary.image Nb.boundary.image := by
              exact hOriginalC ca cb hboundUp
            obtain ⟨H,hHfix,hHboundary⟩ := hboundDown
            obtain ⟨hdisk,aIn,hmove,hinside,hends⟩ :=
              hBoundaryDiskTransport a' b' Na Nb H hHfix hHboundary
            let NIn : ArcNeighborhood aIn := {
              closedSet := Nb.closedSet
              disk := Nb.disk
              arc_inside := hinside
              marked_inside := by
                have he : (M.cover.branch:Set S) ∩ Nb.closedSet=
                    ({b'.val.map 0,b'.val.map 1}:Set S) := by convert Nb.marked_inside using 1
                convert he.trans hends.symm using 1
              boundary := Nb.boundary
              boundary_eq_frontier := Nb.boundary_eq_frontier }
            obtain ⟨HD,hDoutside,hDmarked,hDimage⟩ :=
              hSupportedOriginalD aIn b' NIn Nb.arc_inside hends
            have hlocal : MarkedIsotopyRel M aIn.image b'.image :=
              ⟨HD,hDmarked,hDimage⟩
            exact (markedIsotopy_equivalence M).trans hmove hlocal
          exact (markedIsotopy_equivalence M).trans
            ((markedIsotopy_equivalence M).symm ha')
            ((markedIsotopy_equivalence M).trans hpreparedDown hb')
        exact hdown
  have hcircleinj : Function.Injective M.circle33_vertex_map := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ a =>
      induction b using Quotient.inductionOn with
      | _ b =>
        apply Quotient.sound
        have hup := Quotient.exact hab
        change AmbientIsotopy.Rel (M.circle33_essential_preimage a).val.image
          (M.circle33_essential_preimage b).val.image at hup
        rw [M.circle33_essential_preimage_image,M.circle33_essential_preimage_image] at hup
        have hdown : MarkedIsotopyRel M a.val.image b.val.image := by
          obtain ⟨a',b',c',d',ha',hb',hci,hdi,hiso',ht',htbase',hfree⟩ :=
            M.circle33_original_isotopy_actual_disk_free_reduction a b hup
          have hdisjointUp : Disjoint a'.val.image b'.val.image := by
            apply Set.disjoint_left.mpr
            intro x hxa hxb
            obtain ⟨u,v,huv,hu,hv,f,g,hf,hfa,hgb,hclean,hhom⟩ :=
              M.circle33_actual_isotopic_intersection_has_returning_subarc
                a' b' d' hb' ht' hiso' ⟨x,hxa,hxb⟩
            have hDisk : Nonempty (LocalSurgery.TwoCurveDisk a'.val b'.val) := by
              letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
              exact LocalSurgery.actual_original_returning_subarc_produces_two_curve_disk
                E 2 (by omega) M.genusTwo a' b' ht' u v huv f g hf hfa hgb hclean hhom
            exact hfree.false hDisk.some
          have hdisjointDown : Disjoint c'.val.image d'.val.image := by
            apply Set.disjoint_left.mpr
            intro y hyc hyd
            obtain ⟨x,rfl⟩ := M.cover.projection_surjective y
            have hxa : x ∈ a'.val.image := by rw [ha']; exact hyc
            have hxb : x ∈ b'.val.image := by rw [hb']; exact hyd
            exact Set.disjoint_left.mp hdisjointUp hxa hxb
          have hend : MarkedIsotopyRel M c'.val.image d'.val.image := by
            exact M.circle33_disjoint_isotopic_full_preimages_marked_isotopy
              a' b' c' d' ha' hb' hiso' hdisjointDown
          exact (markedIsotopy_equivalence M).trans hci
            ((markedIsotopy_equivalence M).trans hend ((markedIsotopy_equivalence M).symm hdi))
        exact hdown
  have hinj : Function.Injective M.full_preimage_vertex_map := by
    rw [full_preimage_vertex_map,Sum.elim_injective]
    exact ⟨harcinj,hcircleinj,M.full_preimage_vertex_map_summands_disjoint⟩
  have hsurj : Function.Surjective M.full_preimage_vertex_map := by
    intro v
    induction v using Quotient.inductionOn with
    | _ c =>
      have hrep : ∃ d : EssentialCurve E, (essentialCurveSetoid E).r c d ∧
          M.cover.deck '' d.val.image = d.val.image := by
        exact M.essential_curve_has_deck_invariant_representative c
      obtain ⟨d,hiso,hinv⟩ := hrep
      rcases M.invariant_essential_curve_projects_dictionary d hinv with h | h
      · obtain ⟨a,ha⟩ := h
        refine ⟨Sum.inl (Quotient.mk (nonLoopArcSetoid M) a),?_⟩
        rw [M.full_preimage_vertex_map_inl]
        apply Quotient.sound
        have hsame : (essentialCurveSetoid E).r (M.nonloop_arc_essential_preimage a) d := by
          change AmbientIsotopy.Rel (M.nonloop_arc_essential_preimage a).val.image d.val.image
          rw [M.nonloop_arc_essential_preimage_image,ha]
          exact ambientIsotopy_equivalence.refl _
        exact (essentialCurveSetoid E).iseqv.trans hsame ((essentialCurveSetoid E).iseqv.symm hiso)
      · obtain ⟨a,ha⟩ := h
        refine ⟨Sum.inr (Quotient.mk (circle33Setoid M) a),?_⟩
        rw [M.full_preimage_vertex_map_inr]
        apply Quotient.sound
        have hsame : (essentialCurveSetoid E).r (M.circle33_essential_preimage a) d := by
          change AmbientIsotopy.Rel (M.circle33_essential_preimage a).val.image d.val.image
          rw [M.circle33_essential_preimage_image,ha]
          exact ambientIsotopy_equivalence.refl _
        exact (essentialCurveSetoid E).iseqv.trans hsame ((essentialCurveSetoid E).iseqv.symm hiso)
  let f : (NonLoopArcClass M ⊕ Circle33Class M) ≃ Vertex E :=
    Equiv.ofBijective M.full_preimage_vertex_map ⟨hinj,hsurj⟩
  have hf : DictionaryFullPreimageSpec M f := M.full_preimage_vertex_map_geometric_spec
  refine ⟨f,hf,?_⟩
  intro g hg
  exact M.full_preimage_equivalence_unique g f hg hf

end CurveComplex.HyperellipticModel
