import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
import CurveComplexGenusTwo.Topology.ActualMain14FinitePreparation.Main14ActualCircle24GivenUnionComponentPairingLocalNamedPROVED
import CurveComplexGenusTwo.Topology.ActualMain14CNext.actual_circle24_components_nonseparatingNamedPROVED
import CurveComplexGenusTwo.Dictionary.Circle24.ActualGivenDiskAnnulus
import CurveComplexGenusTwo.Topology.ActualFourLiftExterior.AnnulusComplementComponentReuse
import CurveComplexGenusTwo.Topology.ActualFourLiftExterior.G3ExactReuseProbe
import CurveComplexGenusTwo.Topology.ActualFourLiftExterior.CollaredAnnulusPairSeparates
import CurveComplexGenusTwo.Topology.ActualMain14CNext.actual_given_circle24_components_essentialNamedPROVED
import CurveComplexGenusTwo.Topology.ActualFourLiftExterior.AnnulusOneBoundaryConnected
import CurveComplexGenusTwo.Topology.ActualFourLiftExterior.ConnectedAttachBoundary

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
noncomputable local instance fourLiftPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
set_option maxHeartbeats 10000000

theorem actual_circle24_parallel_four_lifts_two_annuli_exterior_disconnected
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
      (M.cover.projection ⁻¹' d.val.image))
    (hdisjoint : Disjoint c.val.image d.val.image)
    (Uc Ud : Set S)
    (hc : IsOpen Uc ∧ IsConnected Uc ∧
      closure Uc = Uc ∪ c.val.image ∧
      (M.cover.branch.filter (· ∈ Uc)).card = 2)
    (hd : IsOpen Ud ∧ IsConnected Ud ∧
      closure Ud = Ud ∪ d.val.image ∧
      (M.cover.branch.filter (· ∈ Ud)).card = 2)
    (hdisj : Disjoint (closure Uc) (closure Ud)) :
    ¬ IsConnected
      ((M.cover.projection ⁻¹' closure Uc ∪
        M.cover.projection ⁻¹' closure Ud)ᶜ) := by
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  have hTwoMarkSideAvoidsCircle (p : Circle24 M) (U : Set S)
      (hUopen : IsOpen U) (hUcl : closure U = U ∪ p.val.image)
      (hcount : (M.cover.branch.filter (· ∈ U)).card = 2) :
      Disjoint U p.val.image := by
    obtain ⟨X,Y,hXopen,hYopen,hXconn,hYconn,hXY,hXYcover,
      fX,fY,hXboundary,hYboundary,hXinterior,hYinterior,hXcl,hYcl⟩ :=
      M.puncturedCircle_closedSides p.val
    have hXavoid : X ⊆ p.val.imageᶜ := by
      rw [← hXYcover]
      exact subset_union_left
    have hYavoid : Y ⊆ p.val.imageᶜ := by
      rw [← hXYcover]
      exact subset_union_right
    have hside (Z : Set S) (hZconn : IsConnected Z)
        (hZavoid : Z ⊆ p.val.imageᶜ)
        (hZmeet : (Z ∩ U).Nonempty) : Z ⊆ U := by
      have hZsplit : Z ⊆ U ∪ (closure U)ᶜ := by
        intro x hx
        by_cases hxU : x ∈ U
        · exact Or.inl hxU
        · right
          rw [hUcl]
          intro hxu
          rcases hxu with hxU' | hxP
          · exact hxU hxU'
          · exact hZavoid hx hxP
      have hdis : Disjoint U (closure U)ᶜ :=
        Set.disjoint_left.mpr (fun x hxU hxCl => hxCl (subset_closure hxU))
      rcases hZconn.isPreconnected.subset_or_subset hUopen
        isClosed_closure.isOpen_compl hdis hZsplit with hZU | hZout
      · exact hZU
      · obtain ⟨x,hxZ,hxU⟩ := hZmeet
        exact False.elim (hZout hxZ (subset_closure hxU))
    apply Set.disjoint_left.mpr
    intro z hzU hzP
    have hzXcl : z ∈ closure X := hXcl.symm ▸ Or.inr hzP
    have hzYcl : z ∈ closure Y := hYcl.symm ▸ Or.inr hzP
    obtain ⟨x,hxU,hxX⟩ := mem_closure_iff.mp hzXcl U hUopen hzU
    obtain ⟨y,hyU,hyY⟩ := mem_closure_iff.mp hzYcl U hUopen hzU
    have hXU : X ⊆ U := hside X hXconn hXavoid ⟨x,hxX,hxU⟩
    have hYU : Y ⊆ U := hside Y hYconn hYavoid ⟨y,hyY,hyU⟩
    have hfilter : M.cover.branch.filter (· ∈ U) = M.cover.branch := by
      apply Finset.filter_eq_self.mpr
      intro b hb
      have hbOff : b ∈ p.val.imageᶜ := by
        intro hbp
        exact Set.disjoint_left.mp p.val.avoids_branch hbp hb
      rcases hXYcover.symm ▸ hbOff with hbX | hbY
      · exact hXU hbX
      · exact hYU hbY
    have hh := hcount
    rw [hfilter,M.cover.branch_card] at hh
    omega
  have hUcAvoid : Disjoint Uc c.val.image :=
    hTwoMarkSideAvoidsCircle c Uc hc.1 hc.2.2.1 hc.2.2.2
  have hUdAvoid : Disjoint Ud d.val.image :=
    hTwoMarkSideAvoidsCircle d Ud hd.1 hd.2.2.1 hd.2.2.2
  have hOtherSide (p : Circle24 M) (U : Set S)
      (hUOpen : IsOpen U) (hUConnected : IsConnected U)
      (hUCl : closure U = U ∪ p.val.image)
      (hUAvoid : Disjoint U p.val.image) (hUNonempty : U.Nonempty) :
      ∃ V : Set S, IsOpen V ∧ IsConnected V ∧ Disjoint U V ∧
        U ∪ V = p.val.imageᶜ ∧ closure V = V ∪ p.val.image := by
    obtain ⟨X,Y,hXOpen,hYOpen,hXConnected,hYConnected,hXY,hXYCover,
      dX,dY,hXBoundary,hYBoundary,hXInterior,hYInterior,hXCl,hYCl⟩ :=
      M.puncturedCircle_closedSides p.val
    have hUsub : U ⊆ X ∪ Y := by
      rw [hXYCover]
      intro x hxU hxP
      exact Set.disjoint_left.mp hUAvoid hxU hxP
    have hforce (A : Set S) (hAOpen : IsOpen A)
        (hAConnected : IsConnected A) (hAsub : A ⊆ p.val.imageᶜ)
        (hUSubA : U ⊆ A) : U = A := by
      have hAsubSplit : A ⊆ U ∪ (closure U)ᶜ := by
        intro x hxA
        by_cases hxU : x ∈ U
        · exact Or.inl hxU
        · right
          rw [hUCl]
          intro hxCl
          rcases hxCl with hxU' | hxP
          · exact hxU hxU'
          · exact hAsub hxA hxP
      have hdis : Disjoint U (closure U)ᶜ :=
        Set.disjoint_left.mpr (fun x hxU hxCl => hxCl (subset_closure hxU))
      have hAcontained := hAConnected.isPreconnected.subset_or_subset
        hUOpen isClosed_closure.isOpen_compl hdis hAsubSplit
      rcases hAcontained with hAU | hAOutside
      · exact Set.Subset.antisymm hUSubA hAU
      · obtain ⟨x,hxU⟩ := hUNonempty
        exact False.elim (hAOutside (hUSubA hxU) (subset_closure hxU))
    rcases hUConnected.isPreconnected.subset_or_subset
      hXOpen hYOpen hXY hUsub with hUX | hUY
    · have he : U = X := hforce X hXOpen hXConnected
        (by rw [←hXYCover]; exact subset_union_left) hUX
      subst X
      exact ⟨Y,hYOpen,hYConnected,hXY,hXYCover,hYCl⟩
    · have he : U = Y := hforce Y hYOpen hYConnected
        (by rw [←hXYCover]; exact subset_union_right) hUY
      subst Y
      exact ⟨X,hXOpen,hXConnected,hXY.symm,
        (Set.union_comm U X).trans hXYCover,hXCl⟩
  have hUcNonempty : Uc.Nonempty := by
    obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Uc)).Nonempty :=
      Finset.card_pos.mp (by rw [hc.2.2.2]; norm_num)
    exact ⟨b,(Finset.mem_filter.mp hb).2⟩
  have hUdNonempty : Ud.Nonempty := by
    obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Ud)).Nonempty :=
      Finset.card_pos.mp (by rw [hd.2.2.2]; norm_num)
    exact ⟨b,(Finset.mem_filter.mp hb).2⟩
  obtain ⟨Vc,hVcOpen,hVcConnected,hUcVcDisjoint,hUcVcCover,hVcClosure⟩ :=
    hOtherSide c Uc hc.1 hc.2.1 hc.2.2.1 hUcAvoid hUcNonempty
  obtain ⟨Vd,hVdOpen,hVdConnected,hUdVdDisjoint,hUdVdCover,hVdClosure⟩ :=
    hOtherSide d Ud hd.1 hd.2.1 hd.2.2.1 hUdAvoid hUdNonempty
  have hClosedSideFrontier (U V C : Set S)
      (hUV : Disjoint U V) (hcover : U ∪ V = Cᶜ)
      (hclU : closure U = U ∪ C) (hclV : closure V = V ∪ C) :
      interior (closure U) = U ∧ frontier (closure U) = C := by
    have hdisUC : Disjoint U C := by
      apply Set.disjoint_left.mpr
      intro x hxU hxC
      have hh : x ∈ Cᶜ := hcover ▸ Or.inl hxU
      exact hh hxC
    have hdisVC : Disjoint V C := by
      apply Set.disjoint_left.mpr
      intro x hxV hxC
      have hh : x ∈ Cᶜ := hcover ▸ Or.inr hxV
      exact hh hxC
    have hcompU : (closure U)ᶜ = V := by
      rw [hclU]
      ext x
      constructor
      · intro hx
        have hxC : x ∈ Cᶜ := by intro hc; exact hx (Or.inr hc)
        rcases hcover.symm ▸ hxC with hxU | hxV
        · exact False.elim (hx (Or.inl hxU))
        · exact hxV
      · intro hxV hx
        rcases hx with hxU | hxC
        · exact Set.disjoint_left.mp hUV hxU hxV
        · exact Set.disjoint_left.mp hdisVC hxV hxC
    have hcompV : (closure V)ᶜ = U := by
      rw [hclV]
      ext x
      constructor
      · intro hx
        have hxC : x ∈ Cᶜ := by intro hc; exact hx (Or.inr hc)
        rcases hcover.symm ▸ hxC with hxU | hxV
        · exact hxU
        · exact False.elim (hx (Or.inl hxV))
      · intro hxU hx
        rcases hx with hxV | hxC
        · exact Set.disjoint_left.mp hUV hxU hxV
        · exact Set.disjoint_left.mp hdisUC hxU hxC
    have hint : interior (closure U) = U := by
      rw [interior_eq_compl_closure_compl,hcompU,hcompV]
    constructor
    · exact hint
    · rw [frontier, isClosed_closure.closure_eq,hint,hclU]
      ext x
      constructor
      · rintro ⟨hx,hnotU⟩
        rcases hx with hxU | hxC
        · exact False.elim (hnotU hxU)
        · exact hxC
      · intro hxC
        exact ⟨Or.inr hxC,fun hxU => Set.disjoint_left.mp hdisUC hxU hxC⟩
  have ⟨hUcInterior,hUcFrontier⟩ :=
    hClosedSideFrontier Uc Vc c.val.image hUcVcDisjoint hUcVcCover
      hc.2.2.1 hVcClosure
  have ⟨hUdInterior,hUdFrontier⟩ :=
    hClosedSideFrontier Ud Vd d.val.image hUdVdDisjoint hUdVdCover
      hd.2.2.1 hVdClosure
  obtain ⟨Hc,hcEnds⟩ := M.circle24_disk_lift_annulus_given_closed_set
    c (closure Uc) isClosed_closure hUcFrontier (by simpa [hUcInterior] using hc.2.2.2)
  obtain ⟨Hd,hdEnds⟩ := M.circle24_disk_lift_annulus_given_closed_set
    d (closure Ud) isClosed_closure hUdFrontier (by simpa [hUdInterior] using hd.2.2.2)
  obtain ⟨a0,a1,b0,b1,H,ha,hb,had,hbd,hadeck,hbdeck,hHa0,hHa1,
    hap0,hap1,hbp0,hbp1⟩ := M.actual_circle24_given_union_component_pairing c d hup
  have hcross (a b : Curve E)
      (hpa : a.image ⊆ M.cover.projection ⁻¹' c.val.image)
      (hpb : b.image ⊆ M.cover.projection ⁻¹' d.val.image) :
      Disjoint a.image b.image := by
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    exact Set.disjoint_left.mp hdisjoint (hpa hxa) (hpb hxb)
  have ha0 : a0.image ⊆ M.cover.projection ⁻¹' c.val.image := by
    rw [← ha]; exact subset_union_left
  have ha1 : a1.image ⊆ M.cover.projection ⁻¹' c.val.image := by
    rw [← ha]; exact subset_union_right
  have hb0 : b0.image ⊆ M.cover.projection ⁻¹' d.val.image := by
    rw [← hb]; exact subset_union_left
  have hb1 : b1.image ⊆ M.cover.projection ⁻¹' d.val.image := by
    rw [← hb]; exact subset_union_right
  have hd00 : Disjoint a0.image b0.image := hcross a0 b0 ha0 hb0
  have hd01 : Disjoint a0.image b1.image := hcross a0 b1 ha0 hb1
  have hd10 : Disjoint a1.image b0.image := hcross a1 b0 ha1 hb0
  have hd11 : Disjoint a1.image b1.image := hcross a1 b1 ha1 hb1
  have hAcEnds :
      Set.range (fun z : Circle => (Hc (z,0)).val) ∪
        Set.range (fun z : Circle => (Hc (z,1)).val) =
        a0.image ∪ a1.image := hcEnds.trans ha.symm
  have hAdEnds :
      Set.range (fun z : Circle => (Hd (z,0)).val) ∪
        Set.range (fun z : Circle => (Hd (z,1)).val) =
        b0.image ∪ b1.image := hdEnds.trans hb.symm
  have hEndpointMatch (D : Set S) (Hdisk : Circle × Interval ≃ₜ
      M.cover.projection ⁻¹' D) (u v : Curve E)
      (hUV : Disjoint u.image v.image)
      (hends : Set.range (fun z : Circle => (Hdisk (z,0)).val) ∪
        Set.range (fun z : Circle => (Hdisk (z,1)).val) =
          u.image ∪ v.image) :
      (Set.range (fun z : Circle => (Hdisk (z,0)).val) = u.image ∧
        Set.range (fun z : Circle => (Hdisk (z,1)).val) = v.image) ∨
      (Set.range (fun z : Circle => (Hdisk (z,0)).val) = v.image ∧
        Set.range (fun z : Circle => (Hdisk (z,1)).val) = u.image) := by
    let F : C(Circle × Interval,E) :=
      ⟨fun p => (Hdisk p).val,continuous_subtype_val.comp Hdisk.continuous⟩
    have hF : Topology.IsEmbedding F :=
      Topology.IsEmbedding.subtypeVal.comp Hdisk.isEmbedding
    have hF0 : Topology.IsEmbedding (fun z : Circle => F (z,0)) :=
      ((F.continuous.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
        (fun z w he => congrArg Prod.fst (hF.injective he))).isEmbedding
    have hF1 : Topology.IsEmbedding (fun z : Circle => F (z,1)) :=
      ((F.continuous.comp (continuous_id.prodMk continuous_const)).isClosedEmbedding
        (fun z w he => congrArg Prod.fst (hF.injective he))).isEmbedding
    let e0 : Curve E := ⟨fun z => F (z,0),hF0⟩
    let e1 : Curve E := ⟨fun z => F (z,1),hF1⟩
    have hlevels : e0.image ∪ e1.image = u.image ∪ v.image := hends
    have hlevelsDisj : Disjoint e0.image e1.image := by
      apply Set.disjoint_left.mpr
      intro x hx0 hx1
      obtain ⟨z,hz⟩ := hx0
      obtain ⟨w,hw⟩ := hx1
      have he : (z, (0 : Interval)) = (w, (1 : Interval)) :=
        hF.injective (hz.trans hw.symm)
      have hf := congrArg (fun p : Circle × Interval => (p.2 : ℝ)) he
      norm_num at hf
    have hchoose : e0.image = u.image ∨ e0.image = v.image := by
      let z : Circle := Classical.choice inferInstance
      have hz : e0.map z ∈ e0.image := Set.mem_range_self _
      have hpoint : e0.map z ∈ u.image ∪ v.image := hlevels ▸ Or.inl hz
      rcases hpoint with hu | hv
      · left
        have hleft := disjoint_curve_connectedComponentIn e0 e1 hlevelsDisj
          (e0.map z) hz
        have hright := disjoint_curve_connectedComponentIn u v hUV
          (e0.map z) hu
        have hh := congrArg (fun T => connectedComponentIn T (e0.map z)) hlevels
        rwa [hleft,hright] at hh
      · right
        have hleft := disjoint_curve_connectedComponentIn e0 e1 hlevelsDisj
          (e0.map z) hz
        have hright := disjoint_curve_connectedComponentIn v u hUV.symm
          (e0.map z) hv
        have hh := congrArg (fun T => connectedComponentIn T (e0.map z))
          (hlevels.trans (Set.union_comm _ _))
        rwa [hleft,hright] at hh
    have hremaining (A B C D : Set E)
        (hAB : A ∪ B = C ∪ D) (hdAB : Disjoint A B)
        (hdCD : Disjoint C D) (hAC : A = C) : B = D := by
      ext x
      constructor
      · intro hxB
        have hx : x ∈ C ∪ D := hAB ▸ Or.inr hxB
        rcases hx with hxC | hxD
        · exact False.elim (Set.disjoint_left.mp hdAB (hAC.symm ▸ hxC) hxB)
        · exact hxD
      · intro hxD
        have hx : x ∈ A ∪ B := hAB.symm ▸ Or.inr hxD
        rcases hx with hxA | hxB
        · exact False.elim (Set.disjoint_left.mp hdCD (hAC ▸ hxA) hxD)
        · exact hxB
    rcases hchoose with h0 | h0
    · have h1 := hremaining e0.image e1.image u.image v.image
        hlevels hlevelsDisj hUV h0
      exact Or.inl ⟨h0,h1⟩
    · have h1 := hremaining e0.image e1.image v.image u.image
        (hlevels.trans (Set.union_comm _ _)) hlevelsDisj hUV.symm h0
      exact Or.inr ⟨h0,h1⟩
  have hAcPair := hEndpointMatch (closure Uc) Hc a0 a1 had hAcEnds
  have hAdPair := hEndpointMatch (closure Ud) Hd b0 b1 hbd hAdEnds
  have hDeckClosed (T : Set S) :
      M.cover.deck '' (M.cover.projection ⁻¹' T) =
        M.cover.projection ⁻¹' T := by
    apply Set.Subset.antisymm
    · rintro y ⟨x,hx,rfl⟩
      simpa only [Set.mem_preimage,M.cover.projection_deck] using hx
    · intro x hx
      exact ⟨M.cover.deck x,
        by simpa only [Set.mem_preimage,M.cover.projection_deck] using hx,
        M.cover.deck_involution x⟩
  have hAcDeck : M.cover.deck ''
      (M.cover.projection ⁻¹' closure Uc) =
      M.cover.projection ⁻¹' closure Uc := hDeckClosed _
  have hAdDeck : M.cover.deck ''
      (M.cover.projection ⁻¹' closure Ud) =
      M.cover.projection ⁻¹' closure Ud := hDeckClosed _
  have hRel0 : AmbientIsotopy.Rel a0.image b0.image := ⟨H,hHa0⟩
  have hRel1 : AmbientIsotopy.Rel a1.image b1.image := ⟨H,hHa1⟩
  have hNonsep (p : Circle24 M) (u v : Curve E)
      (huv : u.image ∪ v.image = M.cover.projection ⁻¹' p.val.image)
      (hdisj : Disjoint u.image v.image) :
      IsConnected u.imageᶜ ∧ IsConnected v.imageᶜ := by
    let : ClosedSurface E := Classical.choice M.genusTwo.2.1
    obtain ⟨r,s,hrs,hrd,_,_,_,hrnc,hsnc⟩ :=
      M.actual_circle24_components_nonseparating p
    have hchoose (x y : Curve E)
        (hxy : x.image ∪ y.image = M.cover.projection ⁻¹' p.val.image)
        (hxd : Disjoint x.image y.image) :
        x.image = r.image ∨ x.image = s.image := by
      let z : Circle := Classical.choice inferInstance
      have hx : x.map z ∈ x.image := Set.mem_range_self _
      have hpoint : x.map z ∈ r.image ∪ s.image := by
        rw [hrs,← hxy]
        exact Or.inl hx
      rcases hpoint with hr | hs
      · left
        have hxComp := disjoint_curve_connectedComponentIn x y hxd (x.map z) hx
        have hrComp := disjoint_curve_connectedComponentIn r s hrd (x.map z) hr
        have heq : x.image ∪ y.image = r.image ∪ s.image := hxy.trans hrs.symm
        have hh := congrArg (fun T => connectedComponentIn T (x.map z)) heq
        rwa [hxComp,hrComp] at hh
      · right
        have hxComp := disjoint_curve_connectedComponentIn x y hxd (x.map z) hx
        have hsComp := disjoint_curve_connectedComponentIn s r hrd.symm (x.map z) hs
        have heq : x.image ∪ y.image = s.image ∪ r.image :=
          (hxy.trans hrs.symm).trans (Set.union_comm _ _)
        have hh := congrArg (fun T => connectedComponentIn T (x.map z)) heq
        rwa [hxComp,hsComp] at hh
    constructor
    · rcases hchoose u v huv hdisj with h | h
      · simpa only [h] using hrnc
      · simpa only [h] using hsnc
    · rcases hchoose v u ((Set.union_comm _ _).trans huv) hdisj.symm with h | h
      · simpa only [h] using hrnc
      · simpa only [h] using hsnc
  have ⟨hNca0,hNca1⟩ := hNonsep c a0 a1 ha had
  have ⟨hNdb0,hNdb1⟩ := hNonsep d b0 b1 hb hbd
  have hdeckreverse (T V : Set E)
      (hTV : M.cover.deck '' T = V) : M.cover.deck '' V = T := by
    rw [← hTV,Set.image_image]
    have hdouble : (fun x : E => M.cover.deck (M.cover.deck x)) = id :=
      funext M.cover.deck_involution
    rw [hdouble,Set.image_id]
  have hadeck1 : M.cover.deck '' a1.image = a0.image :=
    hdeckreverse a0.image a1.image hadeck
  have hbdeck1 : M.cover.deck '' b1.image = b0.image :=
    hdeckreverse b0.image b1.image hbdeck
  have hLiftClosedDisjoint :
      Disjoint (M.cover.projection ⁻¹' closure Uc)
        (M.cover.projection ⁻¹' closure Ud) :=
    Set.disjoint_left.mpr (fun x hx hy =>
      Set.disjoint_left.mp hdisj hx hy)
  have hOppositeSideComplement (U V C : Set S)
      (hcover : U ∪ V = Cᶜ) (hcl : closure U = U ∪ C)
      (hUV : Disjoint U V) : V = (closure U)ᶜ := by
    ext x
    constructor
    · intro hxV hxCl
      rw [hcl] at hxCl
      rcases hxCl with hxU | hxC
      · exact Set.disjoint_left.mp hUV hxU hxV
      · have hxNotC : x ∈ Cᶜ := hcover ▸ Or.inr hxV
        exact hxNotC hxC
    · intro hxNot
      have hxNotC : x ∈ Cᶜ := by
        intro hxC
        exact hxNot (hcl.symm ▸ Or.inr hxC)
      rcases hcover.symm ▸ hxNotC with hxU | hxV
      · exact False.elim (hxNot (subset_closure hxU))
      · exact hxV
  have hVcComp : Vc = (closure Uc)ᶜ :=
    hOppositeSideComplement Uc Vc c.val.image hUcVcCover hc.2.2.1 hUcVcDisjoint
  have hVdComp : Vd = (closure Ud)ᶜ :=
    hOppositeSideComplement Ud Vd d.val.image hUdVdCover hd.2.2.1 hUdVdDisjoint
  have hExteriorEq :
      ((M.cover.projection ⁻¹' closure Uc ∪
        M.cover.projection ⁻¹' closure Ud)ᶜ) =
        M.cover.projection ⁻¹' (Vc ∩ Vd) := by
    rw [hVcComp,hVdComp]
    ext x
    change (M.cover.projection x ∉ closure Uc ∪ closure Ud) ↔
      M.cover.projection x ∈ (closure Uc)ᶜ ∩ (closure Ud)ᶜ
    simp
  have hProjectionOpen : IsOpenMap M.cover.projection := by
    letI : T2Space S := M.sphere.symm.t2Space
    have hcl : IsClosedMap M.cover.projection :=
      M.cover.projection_continuous.isClosedMap
    have hq := hcl.isQuotientMap M.cover.projection_continuous
      M.cover.projection_surjective
    intro U hU
    rw [← hq.isCoinducing.isOpen_preimage]
    have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
        U ∪ M.cover.deck ⁻¹' U := by
      ext x
      constructor
      · rintro ⟨y,hy,hxy⟩
        rcases (M.cover.fiber_pair x y).mp hxy.symm with h | h
        · exact Or.inl (h ▸ hy)
        · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [h] using hy)
      · rintro (hx | hx)
        · exact ⟨x,hx,rfl⟩
        · exact ⟨M.cover.deck x,hx,M.cover.projection_deck x⟩
    rw [heq]
    exact hU.union (hU.preimage M.cover.deck.continuous)
  have hSphereBoundaryClosure :
      c.val.image ∪ d.val.image ⊆ closure (Vc ∩ Vd) := by
    rintro x (hxc | hxd)
    · have hxClUc : x ∈ closure Uc := hc.2.2.1.symm ▸ Or.inr hxc
      have hxVd : x ∈ Vd := by
        rw [hVdComp]
        exact fun hxClUd => Set.disjoint_left.mp hdisj hxClUc hxClUd
      exact hVdOpen.closure_inter ⟨hVcClosure.symm ▸ Or.inr hxc,hxVd⟩
    · have hxClUd : x ∈ closure Ud := hd.2.2.1.symm ▸ Or.inr hxd
      have hxVc : x ∈ Vc := by
        rw [hVcComp]
        exact fun hxClUc => Set.disjoint_left.mp hdisj hxClUc hxClUd
      have hh : x ∈ closure (Vd ∩ Vc) :=
        hVcOpen.closure_inter ⟨hVdClosure.symm ▸ Or.inr hxd,hxVc⟩
      simpa only [Set.inter_comm] using hh
  have hLiftBoundaryClosure :
      M.cover.projection ⁻¹' (c.val.image ∪ d.val.image) ⊆
        closure ((M.cover.projection ⁻¹' closure Uc ∪
          M.cover.projection ⁻¹' closure Ud)ᶜ) := by
    intro x hx
    rw [hExteriorEq]
    exact hProjectionOpen.preimage_closure_subset_closure_preimage
      (hSphereBoundaryClosure hx)
  have hLiftAnnulusComponent (D : Set S)
      (F : Circle × Interval ≃ₜ M.cover.projection ⁻¹' D)
      (u v : Curve E)
      (hends : Set.range (fun z : Circle => (F (z,0)).val) ∪
        Set.range (fun z : Circle => (F (z,1)).val) =
          u.image ∪ v.image) :
      IsComplementComponent (u.image ∪ v.image)
        ((fun p : Circle × Interval => (F p).val) ''
          {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
    let q : C(Circle × Interval,E) :=
      ⟨fun p => (F p).val,continuous_subtype_val.comp F.continuous⟩
    have hq : Topology.IsEmbedding q :=
      Topology.IsEmbedding.subtypeVal.comp F.isEmbedding
    have hcomp := embedded_annulus_inner_complement_component q hq
    change IsComplementComponent
      (Set.range (fun z : Circle => (F (z,0)).val) ∪
        Set.range (fun z : Circle => (F (z,1)).val))
      ((fun p : Circle × Interval => (F p).val) ''
        {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) at hcomp
    rw [hends] at hcomp
    exact hcomp
  have hAcComponent := hLiftAnnulusComponent (closure Uc) Hc a0 a1 hAcEnds
  have hAdComponent := hLiftAnnulusComponent (closure Ud) Hd b0 b1 hAdEnds
  have ⟨hEssA0,hEssA1,_,_⟩ :=
    M.actual_given_circle24_components_essential c a0 a1 ha had
  have ⟨hEssB0,hEssB1,_,_⟩ :=
    M.actual_given_circle24_components_essential d b0 b1 hb hbd
  obtain ⟨B,hB,hBa,hBb,hBopen⟩ :=
    actual_model_ambient_isotopic_essential_pair_collared_annulus
      M a0 b0 hEssA0 hEssB0 hRel0 hd00
  have hCrossPairDisconnect : ¬ IsConnected (a0.image ∪ b0.image)ᶜ := by
    rw [← hBa,← hBb]
    exact collared_annulus_level_pair_separates B hB hBopen
  have hAcMinus : IsConnected
      ((M.cover.projection ⁻¹' closure Uc) \ a0.image) := by
    rcases hAcPair with h | h
    · rw [← h.1]
      exact annulus_except_zero_boundary_connected _ Hc
    · rw [← h.2]
      exact annulus_except_one_boundary_connected _ Hc
  have hAdMinus : IsConnected
      ((M.cover.projection ⁻¹' closure Ud) \ b0.image) := by
    rcases hAdPair with h | h
    · rw [← h.1]
      exact annulus_except_zero_boundary_connected _ Hd
    · rw [← h.2]
      exact annulus_except_one_boundary_connected _ Hd
  let R : Set E := ((M.cover.projection ⁻¹' closure Uc ∪
    M.cover.projection ⁻¹' closure Ud)ᶜ)
  have hA1Contact : ∃ x ∈ (M.cover.projection ⁻¹' closure Uc) \ a0.image,
      x ∈ closure R := by
    let x := a1.map (Classical.choice inferInstance : Circle)
    have hxA1 : x ∈ a1.image := Set.mem_range_self _
    have hxC : M.cover.projection x ∈ c.val.image := ha1 hxA1
    refine ⟨x,⟨?_,?_⟩,?_⟩
    · exact hc.2.2.1.symm ▸ Or.inr hxC
    · exact fun hxA0 => Set.disjoint_left.mp had hxA0 hxA1
    · exact hLiftBoundaryClosure (Or.inl hxC)
  have hB1Contact : ∃ x ∈ (M.cover.projection ⁻¹' closure Ud) \ b0.image,
      x ∈ closure R := by
    let x := b1.map (Classical.choice inferInstance : Circle)
    have hxB1 : x ∈ b1.image := Set.mem_range_self _
    have hxD : M.cover.projection x ∈ d.val.image := hb1 hxB1
    refine ⟨x,⟨?_,?_⟩,?_⟩
    · exact hd.2.2.1.symm ▸ Or.inr hxD
    · exact fun hxB0 => Set.disjoint_left.mp hbd hxB0 hxB1
    · exact hLiftBoundaryClosure (Or.inr hxD)
  have hA0InAc : a0.image ⊆ M.cover.projection ⁻¹' closure Uc := by
    intro x hx
    exact hc.2.2.1.symm ▸ Or.inr (ha0 hx)
  have hB0InAd : b0.image ⊆ M.cover.projection ⁻¹' closure Ud := by
    intro x hx
    exact hd.2.2.1.symm ▸ Or.inr (hb0 hx)
  have hCrossComplementCover :
      (a0.image ∪ b0.image)ᶜ =
        (R ∪ ((M.cover.projection ⁻¹' closure Uc) \ a0.image)) ∪
          ((M.cover.projection ⁻¹' closure Ud) \ b0.image) := by
    ext x
    constructor
    · intro hx
      have hxA0 : x ∉ a0.image := fun h => hx (Or.inl h)
      have hxB0 : x ∉ b0.image := fun h => hx (Or.inr h)
      by_cases hxAc : x ∈ M.cover.projection ⁻¹' closure Uc
      · exact Or.inl (Or.inr ⟨hxAc,hxA0⟩)
      by_cases hxAd : x ∈ M.cover.projection ⁻¹' closure Ud
      · exact Or.inr ⟨hxAd,hxB0⟩
      · exact Or.inl (Or.inl (by
          change x ∉ M.cover.projection ⁻¹' closure Uc ∪
            M.cover.projection ⁻¹' closure Ud
          exact fun h => h.elim hxAc hxAd))
    · rintro ((hxR | ⟨hxAc,hxA0⟩) | ⟨hxAd,hxB0⟩) h
      · change x ∉ M.cover.projection ⁻¹' closure Uc ∪
          M.cover.projection ⁻¹' closure Ud at hxR
        rcases h with hxA0 | hxB0
        · exact hxR (Or.inl (hA0InAc hxA0))
        · exact hxR (Or.inr (hB0InAd hxB0))
      · rcases h with hxA0' | hxB0
        · exact hxA0 hxA0'
        · exact Set.disjoint_left.mp hLiftClosedDisjoint hxAc (hB0InAd hxB0)
      · rcases h with hxA0 | hxB0'
        · exact Set.disjoint_left.mp hLiftClosedDisjoint (hA0InAc hxA0) hxAd
        · exact hxB0 hxB0'
  -- The two actual disk lifts are annuli. Lemma 4.6 orders their four
  -- parallel nonseparating boundary curves around the genus-one piece.
  have hFourOrder :
      ¬ IsConnected
        ((M.cover.projection ⁻¹' closure Uc ∪
          M.cover.projection ⁻¹' closure Ud)ᶜ) := by
    intro hR
    obtain ⟨xA,hxA,hxRA⟩ := hA1Contact
    have hRA := connected_union_of_boundary_attachment R
      ((M.cover.projection ⁻¹' closure Uc) \ a0.image)
      hR hAcMinus xA hxA hxRA
    obtain ⟨xB,hxB,hxRB⟩ := hB1Contact
    have hxRAB : xB ∈ closure
        (R ∪ ((M.cover.projection ⁻¹' closure Uc) \ a0.image)) :=
      closure_mono subset_union_left hxRB
    have hRAB := connected_union_of_boundary_attachment
      (R ∪ ((M.cover.projection ⁻¹' closure Uc) \ a0.image))
      ((M.cover.projection ⁻¹' closure Ud) \ b0.image)
      hRA hAdMinus xB hxB hxRAB
    exact hCrossPairDisconnect (hCrossComplementCover ▸ hRAB)
  exact hFourOrder
end CurveComplex.HyperellipticModel
