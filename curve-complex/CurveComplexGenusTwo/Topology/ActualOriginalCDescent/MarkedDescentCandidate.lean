import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalBoundaryPairCanonicalNamedConsumeProof
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14MarkedCircleTransverseExtension
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualMarkedCircleTransport
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualMarkedCircleParallel
import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
import CurveComplexGenusTwo.Dictionary.ArcGeometry
import CurveComplexGenusTwo.Dictionary.ActualDictionaryEssential
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalFirstDiskActualCoverAssemblyProved
import Mathlib.Topology.Homeomorph.Lemmas
import CurveComplexGenusTwo.Topology.ActualSphereExterior.SphereExteriorCandidate
import CurveComplexGenusTwo.Topology.ActualFourLiftExterior.FourLiftExteriorCandidate
import CurveComplexGenusTwo.Topology.ActualSphereExterior.SpherePairAnnulus
import CurveComplexGenusTwo.Topology.ActualSphereExterior.SphereAnnulusPartition
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.TrimExtendedAnnulus
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 10000000
theorem actual_original_disjoint_circle24_full_preimage_isotopy_descends_marked
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
      (M.cover.projection ⁻¹' d.val.image))
    (hdisjoint : Disjoint c.val.image d.val.image) :
    MarkedIsotopyRel M c.val.image d.val.image := by
  -- Source: Main14Circle24OriginalActualPairedGeometryConsumeCheckpoint, hTerminal.
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨a0,a1,ha,had,hadeck,hap0,hap1,hac0,hac1⟩ :=
    M.actual_circle24_components_project_bijectively c
  obtain ⟨b0,b1,hb,hbd,hbdeck,hbp0,hbp1,hbc0,hbc1⟩ :=
    M.actual_circle24_components_project_bijectively d
  let z0 : Circle := Classical.choice inferInstance
  obtain ⟨H,hH⟩ := hup
  obtain ⟨e,he⟩ := H.homeomorphism_at 1
  have hef : H.finalMap = e := funext (fun x => (he x).symm)
  have hunion : e '' (a0.image ∪ a1.image) = b0.image ∪ b1.image := by
    rw [ha,hb,← hef]; exact hH
  have hpair (u0 u1 v0 v1 : Curve E)
      (hu : Disjoint u0.image u1.image) (hv : Disjoint v0.image v1.image)
      (hunion : e '' (u0.image ∪ u1.image) = v0.image ∪ v1.image)
      (hfirst : e '' u0.image = v0.image) : e '' u1.image = v1.image := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      have hx : e y ∈ v0.image ∪ v1.image := hunion ▸ ⟨y,Or.inr hy,rfl⟩
      rcases hx with hx | hx
      · obtain ⟨z,hz,hzy⟩ := hfirst.symm ▸ hx
        exact False.elim (Set.disjoint_left.mp hu hz ((e.injective hzy).symm ▸ hy))
      · exact hx
    · intro hx
      have hxpre : x ∈ e '' (u0.image ∪ u1.image) := by
        rw [hunion]; exact Or.inr hx
      obtain ⟨y,hy,hyx⟩ := hxpre
      rcases hy with hy | hy
      · have hxb : x ∈ v0.image := hfirst ▸ ⟨y,hy,hyx⟩
        exact False.elim (Set.disjoint_left.mp hv hxb hx)
      · exact ⟨y,hy,hyx⟩
  have hImageComp (v0 v1 : Curve E) (hv : Disjoint v0.image v1.image)
      (hunion : e '' (a0.image ∪ a1.image) = v0.image ∪ v1.image)
      (hx : e (a0.map z0) ∈ v0.image) : e '' a0.image = v0.image := by
    have hsource : a0.map z0 ∈ a0.image := Set.mem_range_self _
    have hs := disjoint_curve_connectedComponentIn a0 a1 had (a0.map z0) hsource
    have ht := disjoint_curve_connectedComponentIn v0 v1 hv (e (a0.map z0)) hx
    have hh := e.image_connectedComponentIn (s := a0.image ∪ a1.image)
      (x := a0.map z0) (by exact Or.inl hsource)
    rw [hs,hunion,ht] at hh
    exact hh
  have hpaired :
      ∃ v0 v1 : Curve E,
        v0.image ∪ v1.image = M.cover.projection ⁻¹' d.val.image ∧
        Disjoint v0.image v1.image ∧
        M.cover.deck '' v0.image = v1.image ∧
        H.finalMap '' a0.image = v0.image ∧
        H.finalMap '' a1.image = v1.image ∧
        Set.BijOn M.cover.projection v0.image d.val.image ∧
        Set.BijOn M.cover.projection v1.image d.val.image := by
    have hx : e (a0.map z0) ∈ b0.image ∪ b1.image :=
      hunion ▸ ⟨a0.map z0,Or.inl (Set.mem_range_self _),rfl⟩
    rcases hx with hx | hx
    · have h0 := hImageComp b0 b1 hbd hunion hx
      have h1 := hpair a0 a1 b0 b1 had hbd hunion h0
      exact ⟨b0,b1,hb,hbd,hbdeck,by rw [hef];exact h0,
        by rw [hef];exact h1,hbp0,hbp1⟩
    · have hunion' : e '' (a0.image ∪ a1.image) = b1.image ∪ b0.image :=
        hunion.trans (Set.union_comm _ _)
      have h0 := hImageComp b1 b0 hbd.symm hunion' hx
      have h1 := hpair a0 a1 b1 b0 had hbd.symm hunion' h0
      have hbdeck' : M.cover.deck '' b1.image = b0.image := by
        rw [← hbdeck,Set.image_image]
        have hi : (fun x : E => M.cover.deck (M.cover.deck x)) = id :=
          funext M.cover.deck_involution
        rw [hi,Set.image_id]
      exact ⟨b1,b0,(Set.union_comm _ _).trans hb,hbd.symm,hbdeck',
        by rw [hef];exact h0,by rw [hef];exact h1,hbp1,hbp0⟩
  obtain ⟨Uc,fc,hUcOpen,hUcConnected,hUcClosure,hfcBoundary,hfcInterior,hUcMarks⟩ :=
    M.actual_circle24_two_mark_closed_side c
  obtain ⟨Ud,fd,hUdOpen,hUdConnected,hUdClosure,hfdBoundary,hfdInterior,hUdMarks⟩ :=
    M.actual_circle24_two_mark_closed_side d
  have hConnectedPreimage (D : Set S) (hD : IsConnected D)
      (b : S) (hb : b ∈ M.cover.branch) (hbD : b ∈ D) :
      IsConnected (M.cover.projection ⁻¹' D) := by
    letI : T2Space S := M.sphere.symm.t2Space
    have hopen : IsOpenMap M.cover.projection := by
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
    have hclosed : IsClosedMap M.cover.projection :=
      M.cover.projection_continuous.isClosedMap
    let f := D.restrictPreimage M.cover.projection
    have hfopen : IsOpenMap f := hopen.restrictPreimage D
    have hfclosed : IsClosedMap f := hclosed.restrictPreimage D
    letI : ConnectedSpace D := isConnected_iff_connectedSpace.mp hD
    obtain ⟨w,hw,huniq⟩ := M.cover.branch_fiber_unique hb
    have hwD : w ∈ M.cover.projection ⁻¹' D := by
      change M.cover.projection w ∈ D
      rw [hw]
      exact hbD
    letI : Nonempty (M.cover.projection ⁻¹' D) := ⟨⟨w,hwD⟩⟩
    apply isConnected_iff_connectedSpace.mpr
    apply connectedSpace_iff_univ.mpr
    refine ⟨Set.univ_nonempty,?_⟩
    by_contra h
    obtain ⟨U,V,hU,hV,hnU,hnV,hd,huv⟩ :=
      isClopen_univ.not_isPreconnected_iff.mp h
    have hUi : f '' U = Set.univ :=
      IsClopen.eq_univ ⟨hfclosed U hU.isClosed,hfopen U hU.isOpen⟩
        (hnU.image f)
    have hVi : f '' V = Set.univ :=
      IsClopen.eq_univ ⟨hfclosed V hV.isClosed,hfopen V hV.isOpen⟩
        (hnV.image f)
    obtain ⟨u,hu,hueq⟩ := (hUi.symm ▸ Set.mem_univ (⟨b,hbD⟩ : D))
    obtain ⟨v,hv,hveq⟩ := (hVi.symm ▸ Set.mem_univ (⟨b,hbD⟩ : D))
    have huval : (u : E) = w := huniq u.val (congrArg Subtype.val hueq)
    have hvval : (v : E) = w := huniq v.val (congrArg Subtype.val hveq)
    have huv' : u = v := Subtype.ext (huval.trans hvval.symm)
    exact Set.disjoint_left.mp hd hu (huv' ▸ hv)
  have hPreUcConnected : IsConnected (M.cover.projection ⁻¹' Uc) := by
    obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Uc)).Nonempty :=
      Finset.card_pos.mp (by rw [hUcMarks]; norm_num)
    exact hConnectedPreimage Uc hUcConnected b
      (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
  have hPreUdConnected : IsConnected (M.cover.projection ⁻¹' Ud) := by
    obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Ud)).Nonempty :=
      Finset.card_pos.mp (by rw [hUdMarks]; norm_num)
    exact hConnectedPreimage Ud hUdConnected b
      (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
  have hUcAvoid : Disjoint Uc c.val.image := by
    apply Set.disjoint_left.mpr
    intro x hxU hxC
    have hxCl : x ∈ closure Uc := subset_closure hxU
    let z := fc.symm ⟨x,hxCl⟩
    have hzEq : (fc z : S) = x :=
      congrArg Subtype.val (fc.apply_symm_apply ⟨x,hxCl⟩)
    have hzi : ‖z.val‖ < 1 := (hfcInterior z).mp (hzEq ▸ hxU)
    have hzb : ‖z.val‖ = 1 := (hfcBoundary z).mp (hzEq ▸ hxC)
    linarith
  have hUdAvoid : Disjoint Ud d.val.image := by
    apply Set.disjoint_left.mpr
    intro x hxU hxD
    have hxCl : x ∈ closure Ud := subset_closure hxU
    let z := fd.symm ⟨x,hxCl⟩
    have hzEq : (fd z : S) = x :=
      congrArg Subtype.val (fd.apply_symm_apply ⟨x,hxCl⟩)
    have hzi : ‖z.val‖ < 1 := (hfdInterior z).mp (hzEq ▸ hxU)
    have hzb : ‖z.val‖ = 1 := (hfdBoundary z).mp (hzEq ▸ hxD)
    linarith
  have hEfull : e '' (M.cover.projection ⁻¹' c.val.image) =
      M.cover.projection ⁻¹' d.val.image := by
    rw [←hef]
    exact hH
  have hImageUcConnected : IsConnected (e '' (M.cover.projection ⁻¹' Uc)) :=
    hPreUcConnected.image e e.continuous.continuousOn
  have hImageUcOpen : IsOpen (e '' (M.cover.projection ⁻¹' Uc)) :=
    e.isOpenMap _ (hUcOpen.preimage M.cover.projection_continuous)
  have hImageUcAvoid :
      Disjoint (e '' (M.cover.projection ⁻¹' Uc))
        (M.cover.projection ⁻¹' d.val.image) := by
    apply Set.disjoint_left.mpr
    intro z hz hzD
    obtain ⟨x,hx,hxz⟩ := hz
    obtain ⟨y,hy,hyz⟩ : z ∈ e '' (M.cover.projection ⁻¹' c.val.image) :=
      hEfull.symm ▸ hzD
    have hxy : x = y := e.injective (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp hUcAvoid hx (hxy ▸ hy)
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
      Finset.card_pos.mp (by rw [hUcMarks]; norm_num)
    exact ⟨b,(Finset.mem_filter.mp hb).2⟩
  have hUdNonempty : Ud.Nonempty := by
    obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Ud)).Nonempty :=
      Finset.card_pos.mp (by rw [hUdMarks]; norm_num)
    exact ⟨b,(Finset.mem_filter.mp hb).2⟩
  obtain ⟨Vc,hVcOpen,hVcConnected,hUcVcDisjoint,hUcVcCover,hVcClosure⟩ :=
    hOtherSide c Uc hUcOpen hUcConnected hUcClosure hUcAvoid hUcNonempty
  obtain ⟨Vd,hVdOpen,hVdConnected,hUdVdDisjoint,hUdVdCover,hVdClosure⟩ :=
    hOtherSide d Ud hUdOpen hUdConnected hUdClosure hUdAvoid hUdNonempty
  have hdCircleSide : d.val.image ⊆ Uc ∨ d.val.image ⊆ Vc := by
    have hsub : d.val.image ⊆ Uc ∪ Vc := by
      rw [hUcVcCover]
      intro x hxD hxC
      exact Set.disjoint_left.mp hdisjoint hxC hxD
    exact (isConnected_range d.val.curve.embedded.continuous).isPreconnected
      |>.subset_or_subset hUcOpen hVcOpen hUcVcDisjoint hsub
  have hcCircleSide : c.val.image ⊆ Ud ∨ c.val.image ⊆ Vd := by
    have hsub : c.val.image ⊆ Ud ∪ Vd := by
      rw [hUdVdCover]
      intro x hxC hxD
      exact Set.disjoint_left.mp hdisjoint hxC hxD
    exact (isConnected_range c.val.curve.embedded.continuous).isPreconnected
      |>.subset_or_subset hUdOpen hVdOpen hUdVdDisjoint hsub
  have hOppositeMarks (p : Circle24 M) (U V : Set S)
      (hUV : Disjoint U V) (hcover : U ∪ V = p.val.imageᶜ)
      (hUmarks : (M.cover.branch.filter (· ∈ U)).card = 2) :
      (M.cover.branch.filter (· ∈ V)).card = 4 := by
    have hdis : Disjoint (M.cover.branch.filter (· ∈ U))
        (M.cover.branch.filter (· ∈ V)) :=
      Finset.disjoint_left.mpr (fun x hxU hxV =>
        Set.disjoint_left.mp hUV (Finset.mem_filter.mp hxU).2
          (Finset.mem_filter.mp hxV).2)
    have hunion : M.cover.branch.filter (· ∈ U) ∪
        M.cover.branch.filter (· ∈ V) = M.cover.branch := by
      ext x
      simp only [Finset.mem_union,Finset.mem_filter]
      constructor
      · rintro (⟨hx,_⟩ | ⟨hx,_⟩) <;> exact hx
      · intro hx
        have hxP : x ∈ p.val.imageᶜ := by
          intro hxImage
          exact Set.disjoint_left.mp p.val.avoids_branch hxImage hx
        rcases (hcover.symm ▸ hxP) with hxU | hxV
        · exact Or.inl ⟨hx,hxU⟩
        · exact Or.inr ⟨hx,hxV⟩
    have hsum : (M.cover.branch.filter (· ∈ U)).card +
        (M.cover.branch.filter (· ∈ V)).card = 6 := by
      rw [← Finset.card_union_of_disjoint hdis,hunion,M.cover.branch_card]
    omega
  have hVcMarks : (M.cover.branch.filter (· ∈ Vc)).card = 4 :=
    hOppositeMarks c Uc Vc hUcVcDisjoint hUcVcCover hUcMarks
  have hVdMarks : (M.cover.branch.filter (· ∈ Vd)).card = 4 :=
    hOppositeMarks d Ud Vd hUdVdDisjoint hUdVdCover hUdMarks
  have hNestedTwoMarkSides (hdInside : d.val.image ⊆ Uc) :
      Ud ⊆ Uc ∧ c.val.image ⊆ Vd := by
    have hVcSub : Vc ⊆ Ud ∪ Vd := by
      rw [hUdVdCover]
      intro x hxVc hxD
      exact Set.disjoint_left.mp hUcVcDisjoint (hdInside hxD) hxVc
    have hVcVd : Vc ⊆ Vd := by
      rcases hVcConnected.isPreconnected.subset_or_subset
        hUdOpen hVdOpen hUdVdDisjoint hVcSub with hVcUd | hVcVd
      · have hfilter : M.cover.branch.filter (· ∈ Vc) ⊆
            M.cover.branch.filter (· ∈ Ud) := by
          intro x hx
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hx).1,hVcUd (Finset.mem_filter.mp hx).2⟩
        have hle := Finset.card_le_card hfilter
        omega
      · exact hVcVd
    have hcVd : c.val.image ⊆ Vd := by
      intro x hxC
      have hxCl : x ∈ closure Vc := by rw [hVcClosure]; exact Or.inr hxC
      have hxClD : x ∈ closure Vd := closure_mono hVcVd hxCl
      rw [hVdClosure] at hxClD
      rcases hxClD with hxVd | hxD
      · exact hxVd
      · exact False.elim (Set.disjoint_left.mp hdisjoint hxC hxD)
    have hUdSub : Ud ⊆ Uc ∪ Vc := by
      rw [hUcVcCover]
      intro x hxUd hxC
      exact Set.disjoint_left.mp hUdVdDisjoint hxUd (hcVd hxC)
    rcases hUdConnected.isPreconnected.subset_or_subset
      hUcOpen hVcOpen hUcVcDisjoint hUdSub with hUdUc | hUdVc
    · exact ⟨hUdUc,hcVd⟩
    · let z : Circle := Classical.choice inferInstance
      have hzD : d.val.curve.map z ∈ d.val.image := Set.mem_range_self _
      have hzCl : d.val.curve.map z ∈ closure Ud := by
        rw [hUdClosure]; exact Or.inr hzD
      have hzVc : d.val.curve.map z ∈ closure Vc := closure_mono hUdVc hzCl
      rw [hVcClosure] at hzVc
      rcases hzVc with hzVc | hzC
      · exact False.elim (Set.disjoint_left.mp hUcVcDisjoint (hdInside hzD) hzVc)
      · exact False.elim (Set.disjoint_left.mp hdisjoint hzC hzD)
  have hNestedMarks (hdInside : d.val.image ⊆ Uc) :
      M.cover.branch.filter (· ∈ Ud) = M.cover.branch.filter (· ∈ Uc) := by
    have hsub : M.cover.branch.filter (· ∈ Ud) ⊆
        M.cover.branch.filter (· ∈ Uc) := by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1,
          (hNestedTwoMarkSides hdInside).1 (Finset.mem_filter.mp hx).2⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hUdMarks,hUcMarks])
  have hReverseNestedTwoMarkSides (hcInside : c.val.image ⊆ Ud) :
      Uc ⊆ Ud ∧ d.val.image ⊆ Vc := by
    have hVdSub : Vd ⊆ Uc ∪ Vc := by
      rw [hUcVcCover]
      intro x hxVd hxC
      exact Set.disjoint_left.mp hUdVdDisjoint (hcInside hxC) hxVd
    have hVdVc : Vd ⊆ Vc := by
      rcases hVdConnected.isPreconnected.subset_or_subset
        hUcOpen hVcOpen hUcVcDisjoint hVdSub with hVdUc | hVdVc
      · have hfilter : M.cover.branch.filter (· ∈ Vd) ⊆
            M.cover.branch.filter (· ∈ Uc) := by
          intro x hx
          exact Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp hx).1,hVdUc (Finset.mem_filter.mp hx).2⟩
        have hle := Finset.card_le_card hfilter
        omega
      · exact hVdVc
    have hdVc : d.val.image ⊆ Vc := by
      intro x hxD
      have hxCl : x ∈ closure Vd := by rw [hVdClosure]; exact Or.inr hxD
      have hxClC : x ∈ closure Vc := closure_mono hVdVc hxCl
      rw [hVcClosure] at hxClC
      rcases hxClC with hxVc | hxC
      · exact hxVc
      · exact False.elim (Set.disjoint_left.mp hdisjoint hxC hxD)
    have hUcSub : Uc ⊆ Ud ∪ Vd := by
      rw [hUdVdCover]
      intro x hxUc hxD
      exact Set.disjoint_left.mp hUcVcDisjoint hxUc (hdVc hxD)
    rcases hUcConnected.isPreconnected.subset_or_subset
      hUdOpen hVdOpen hUdVdDisjoint hUcSub with hUcUd | hUcVd
    · exact ⟨hUcUd,hdVc⟩
    · let z : Circle := Classical.choice inferInstance
      have hzC : c.val.curve.map z ∈ c.val.image := Set.mem_range_self _
      have hzCl : c.val.curve.map z ∈ closure Uc := by
        rw [hUcClosure]; exact Or.inr hzC
      have hzVd : c.val.curve.map z ∈ closure Vd := closure_mono hUcVd hzCl
      rw [hVdClosure] at hzVd
      rcases hzVd with hzVd | hzD
      · exact False.elim (Set.disjoint_left.mp hUdVdDisjoint (hcInside hzC) hzVd)
      · exact False.elim (Set.disjoint_left.mp hdisjoint hzC hzD)
  have hReverseNestedMarks (hcInside : c.val.image ⊆ Ud) :
      M.cover.branch.filter (· ∈ Ud) = M.cover.branch.filter (· ∈ Uc) := by
    have hsub : M.cover.branch.filter (· ∈ Uc) ⊆
        M.cover.branch.filter (· ∈ Ud) := by
      intro x hx
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hx).1,
          (hReverseNestedTwoMarkSides hcInside).1 (Finset.mem_filter.mp hx).2⟩
    exact (Finset.eq_of_subset_of_card_le hsub
      (by rw [hUcMarks,hUdMarks])).symm
  have hMutuallyExteriorDisksDisjoint
      (hdOutside : d.val.image ⊆ Vc)
      (hcOutside : c.val.image ⊆ Vd) : Disjoint Uc Ud := by
    have hUcSub : Uc ⊆ Ud ∪ Vd := by
      rw [hUdVdCover]
      intro x hxUc hxD
      exact Set.disjoint_left.mp hUcVcDisjoint hxUc (hdOutside hxD)
    have hUcVd : Uc ⊆ Vd := by
      rcases hUcConnected.isPreconnected.subset_or_subset
        hUdOpen hVdOpen hUdVdDisjoint hUcSub with hUcUd | hUcVd
      · let z : Circle := Classical.choice inferInstance
        have hzC : c.val.curve.map z ∈ c.val.image := Set.mem_range_self _
        have hzCl : c.val.curve.map z ∈ closure Uc := by
          rw [hUcClosure]; exact Or.inr hzC
        have hzUd : c.val.curve.map z ∈ closure Ud := closure_mono hUcUd hzCl
        rw [hUdClosure] at hzUd
        rcases hzUd with hzUd | hzD
        · exact False.elim
            (Set.disjoint_left.mp hUdVdDisjoint hzUd (hcOutside hzC))
        · exact False.elim (Set.disjoint_left.mp hdisjoint hzC hzD)
      · exact hUcVd
    exact Set.disjoint_left.mpr (fun x hxUc hxUd =>
      Set.disjoint_left.mp hUdVdDisjoint hxUd (hUcVd hxUc))
  have hPosition :
      M.cover.branch.filter (· ∈ Ud) = M.cover.branch.filter (· ∈ Uc) ∨
      Disjoint Uc Ud := by
    rcases hdCircleSide with hdInside | hdOutside
    · exact Or.inl (hNestedMarks hdInside)
    · rcases hcCircleSide with hcInside | hcOutside
      · exact Or.inl (hReverseNestedMarks hcInside)
      · exact Or.inr (hMutuallyExteriorDisksDisjoint hdOutside hcOutside)
  have hSeparateClosedDisks (hUdisj : Disjoint Uc Ud) :
      Disjoint (closure Uc) (closure Ud) := by
    have hdOutside : d.val.image ⊆ Vc := by
      rcases hdCircleSide with hdInside | hdOutside
      · have hsub := (hNestedTwoMarkSides hdInside).1
        obtain ⟨x,hx⟩ := hUdNonempty
        exact False.elim (Set.disjoint_left.mp hUdisj (hsub hx) hx)
      · exact hdOutside
    have hcOutside : c.val.image ⊆ Vd := by
      rcases hcCircleSide with hcInside | hcOutside
      · have hsub := (hReverseNestedTwoMarkSides hcInside).1
        obtain ⟨x,hx⟩ := hUcNonempty
        exact False.elim (Set.disjoint_left.mp hUdisj hx (hsub hx))
      · exact hcOutside
    have hUcSub : Uc ⊆ Ud ∪ Vd := by
      rw [hUdVdCover]
      intro x hxUc hxD
      exact Set.disjoint_left.mp hUcVcDisjoint hxUc (hdOutside hxD)
    have hUcVd : Uc ⊆ Vd := by
      rcases hUcConnected.isPreconnected.subset_or_subset
        hUdOpen hVdOpen hUdVdDisjoint hUcSub with hUcUd | hUcVd
      · obtain ⟨x,hx⟩ := hUcNonempty
        exact False.elim (Set.disjoint_left.mp hUdisj hx (hUcUd hx))
      · exact hUcVd
    have hClUcVd : closure Uc ⊆ Vd := by
      rw [hUcClosure]
      rintro x (hxU | hxC)
      · exact hUcVd hxU
      · exact hcOutside hxC
    apply Set.disjoint_left.mpr
    intro x hxUc hxUd
    have hxVd : x ∈ Vd := hClUcVd hxUc
    rw [hUdClosure] at hxUd
    rcases hxUd with hxUd | hxD
    · exact Set.disjoint_left.mp hUdVdDisjoint hxUd hxVd
    · have hxComp : x ∈ d.val.imageᶜ := by
        rw [←hUdVdCover]; exact Or.inr hxVd
      exact hxComp hxD
  have hSeparateLiftedClosedAnnuli (hUdisj : Disjoint Uc Ud) :
      Disjoint (M.cover.projection ⁻¹' closure Uc)
        (M.cover.projection ⁻¹' closure Ud) :=
    Set.disjoint_left.mpr (fun x hx hy =>
      Set.disjoint_left.mp (hSeparateClosedDisks hUdisj) hx hy)
  have hFixedOutsideBothAnnuli (hUdisj : Disjoint Uc Ud) :
      ∃ w : E, M.cover.deck w = w ∧
        w ∉ M.cover.projection ⁻¹' closure Uc ∧
        w ∉ M.cover.projection ⁻¹' closure Ud := by
    let Bc := M.cover.branch.filter (· ∈ Uc)
    let Bd := M.cover.branch.filter (· ∈ Ud)
    have hBdisj : Disjoint Bc Bd :=
      Finset.disjoint_left.mpr (fun x hx hy =>
        Set.disjoint_left.mp hUdisj
          (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2)
    have hBcard : (Bc ∪ Bd).card = 4 := by
      rw [Finset.card_union_of_disjoint hBdisj,hUcMarks,hUdMarks]
    have hBsub : Bc ∪ Bd ⊆ M.cover.branch := by
      intro b hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (Finset.mem_filter.mp hb).1
      · exact (Finset.mem_filter.mp hb).1
    have hOutside : ∃ b ∈ M.cover.branch, b ∉ Uc ∧ b ∉ Ud := by
      by_contra hnone
      have hreverse : M.cover.branch ⊆ Bc ∪ Bd := by
        intro b hb
        by_contra hbnot
        apply hnone
        refine ⟨b,hb,?_,?_⟩
        · intro hbUc
          exact hbnot (Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨hb,hbUc⟩)))
        · intro hbUd
          exact hbnot (Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨hb,hbUd⟩)))
      have hle := Finset.card_le_card hreverse
      rw [M.cover.branch_card,hBcard] at hle
      omega
    obtain ⟨b,hb,hbUc,hbUd⟩ := hOutside
    obtain ⟨w,hw,_⟩ := M.cover.branch_fiber_unique hb
    have hfixed : M.cover.deck w = w :=
      (M.cover.fixed_iff_branch w).mpr (by rw [hw]; exact hb)
    refine ⟨w,hfixed,?_,?_⟩
    · intro hcl
      change M.cover.projection w ∈ closure Uc at hcl
      rw [hw,hUcClosure] at hcl
      rcases hcl with hU | hC
      · exact hbUc hU
      · exact Set.disjoint_left.mp c.val.avoids_branch hC hb
    · intro hcl
      change M.cover.projection w ∈ closure Ud at hcl
      rw [hw,hUdClosure] at hcl
      rcases hcl with hU | hD
      · exact hbUd hU
      · exact Set.disjoint_left.mp d.val.avoids_branch hD hb
  have hComplementPreimageConnected (hUdisj : Disjoint Uc Ud)
      (hBaseConnected : IsConnected ((closure Uc ∪ closure Ud)ᶜ)) :
      IsConnected
        ((M.cover.projection ⁻¹' closure Uc ∪
          M.cover.projection ⁻¹' closure Ud)ᶜ) := by
    obtain ⟨w,hwfixed,hwc,hwd⟩ := hFixedOutsideBothAnnuli hUdisj
    have hb : M.cover.projection w ∈ M.cover.branch :=
      (M.cover.fixed_iff_branch w).mp hwfixed
    have hbOutside : M.cover.projection w ∈ (closure Uc ∪ closure Ud)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_union, not_or]
      exact ⟨hwc,hwd⟩
    convert hConnectedPreimage ((closure Uc ∪ closure Ud)ᶜ)
      hBaseConnected (M.cover.projection w) hb hbOutside using 1
    simp only [Set.preimage_compl,Set.preimage_union]
  have hBaseConnected (hUdisj : Disjoint Uc Ud) :
      IsConnected ((closure Uc ∪ closure Ud)ᶜ) :=
    actual_two_disjoint_circle24_closed_disks_exterior_connected M c d
      Uc Ud fc fd hfcBoundary hfdBoundary hfcInterior hfdInterior
      (hSeparateClosedDisks hUdisj)
  have hSameMarksOfComplementOrder
      (hBaseConnected : Disjoint Uc Ud →
        IsConnected ((closure Uc ∪ closure Ud)ᶜ))
      (hLiftDisconnected : Disjoint Uc Ud →
        ¬ IsConnected
          ((M.cover.projection ⁻¹' closure Uc ∪
            M.cover.projection ⁻¹' closure Ud)ᶜ)) :
      M.cover.branch.filter (· ∈ Ud) =
        M.cover.branch.filter (· ∈ Uc) := by
    rcases hPosition with heq | hdisj
    · exact heq
    · exact False.elim
        (hLiftDisconnected hdisj
          (hComplementPreimageConnected hdisj (hBaseConnected hdisj)))
  have hActualSameMarks :
      M.cover.branch.filter (· ∈ Ud) =
        M.cover.branch.filter (· ∈ Uc) :=
    hSameMarksOfComplementOrder hBaseConnected (fun hUdisj =>
      actual_circle24_parallel_four_lifts_two_annuli_exterior_disconnected
        M c d ⟨H,hH⟩ hdisjoint Uc Ud
        ⟨hUcOpen,hUcConnected,hUcClosure,hUcMarks⟩
        ⟨hUdOpen,hUdConnected,hUdClosure,hUdMarks⟩
        (hSeparateClosedDisks hUdisj))
  have hNestedCirclePosition :
      d.val.image ⊆ Uc ∨ c.val.image ⊆ Ud := by
    rcases hdCircleSide with hdInside | hdOutside
    · exact Or.inl hdInside
    · rcases hcCircleSide with hcInside | hcOutside
      · exact Or.inr hcInside
      · have hUdisj := hMutuallyExteriorDisksDisjoint hdOutside hcOutside
        obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Uc)).Nonempty :=
          Finset.card_pos.mp (by rw [hUcMarks]; norm_num)
        have hbUc := (Finset.mem_filter.mp hb).2
        have hbUd : b ∈ Ud :=
          (Finset.mem_filter.mp (hActualSameMarks ▸ hb)).2
        exact False.elim (Set.disjoint_left.mp hUdisj hbUc hbUd)
  have hPreVcConnected : IsConnected (M.cover.projection ⁻¹' Vc) := by
    obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Vc)).Nonempty :=
      Finset.card_pos.mp (by rw [hVcMarks]; norm_num)
    exact hConnectedPreimage Vc hVcConnected b
      (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
  have hPreVdConnected : IsConnected (M.cover.projection ⁻¹' Vd) := by
    obtain ⟨b,hb⟩ : (M.cover.branch.filter (· ∈ Vd)).Nonempty :=
      Finset.card_pos.mp (by rw [hVdMarks]; norm_num)
    exact hConnectedPreimage Vd hVdConnected b
      (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hb).2
  have hSideTransport :
      e '' (M.cover.projection ⁻¹' Uc) = M.cover.projection ⁻¹' Ud ∨
      e '' (M.cover.projection ⁻¹' Uc) = M.cover.projection ⁻¹' Vd := by
    let A : Set E := e '' (M.cover.projection ⁻¹' Uc)
    let B : Set E := e '' (M.cover.projection ⁻¹' Vc)
    let P : Set E := M.cover.projection ⁻¹' Ud
    let Q : Set E := M.cover.projection ⁻¹' Vd
    have hABOpen : IsOpen A ∧ IsOpen B :=
      ⟨hImageUcOpen,e.isOpenMap _ (hVcOpen.preimage M.cover.projection_continuous)⟩
    have hABDisjoint : Disjoint A B := by
      apply Set.disjoint_left.mpr
      intro z hzA hzB
      obtain ⟨x,hx,hxz⟩ := hzA
      obtain ⟨y,hy,hyz⟩ := hzB
      have hxy : x = y := e.injective (hxz.trans hyz.symm)
      exact Set.disjoint_left.mp hUcVcDisjoint hx (hxy ▸ hy)
    have hABCover : A ∪ B = P ∪ Q := by
      change e '' (M.cover.projection ⁻¹' Uc) ∪
        e '' (M.cover.projection ⁻¹' Vc) =
        M.cover.projection ⁻¹' Ud ∪ M.cover.projection ⁻¹' Vd
      rw [← Set.image_union,← Set.preimage_union,hUcVcCover,
        Set.preimage_compl,e.image_compl,hEfull,
        ← Set.preimage_union,hUdVdCover,Set.preimage_compl]
    have hPQOpen : IsOpen P ∧ IsOpen Q :=
      ⟨hUdOpen.preimage M.cover.projection_continuous,
        hVdOpen.preimage M.cover.projection_continuous⟩
    have hPQDisjoint : Disjoint P Q :=
      Set.disjoint_left.mpr (fun x hxP hxQ =>
        Set.disjoint_left.mp hUdVdDisjoint hxP hxQ)
    have hANonempty : A.Nonempty := hImageUcConnected.nonempty
    have hforce (T : Set E) (hTConnected : IsConnected T)
        (hTsub : T ⊆ A ∪ B) (hAsub : A ⊆ T) : A = T := by
      have hTchoice := hTConnected.isPreconnected.subset_or_subset
        hABOpen.1 hABOpen.2 hABDisjoint hTsub
      rcases hTchoice with hTA | hTB
      · exact Set.Subset.antisymm hAsub hTA
      · obtain ⟨x,hxA⟩ := hANonempty
        exact False.elim (Set.disjoint_left.mp hABDisjoint hxA
          (hTB (hAsub hxA)))
    have hAsub : A ⊆ P ∪ Q := by rw [← hABCover]; exact subset_union_left
    rcases hImageUcConnected.isPreconnected.subset_or_subset
      hPQOpen.1 hPQOpen.2 hPQDisjoint hAsub with hAP | hAQ
    · left
      exact hforce P hPreUdConnected
        (by rw [hABCover]; exact subset_union_left) hAP
    · right
      exact hforce Q hPreVdConnected
        (by rw [hABCover]; exact subset_union_right) hAQ
  obtain ⟨v0,v1,hvfull,hvdisj,hvdeck,hv0,hv1,hvproj0,hvproj1⟩ := hpaired
  have hRel0 : AmbientIsotopy.Rel a0.image v0.image := ⟨H,hv0⟩
  have hRel1 : AmbientIsotopy.Rel a1.image v1.image := ⟨H,hv1⟩
  -- The missing paired step must select the inter-circle band and exclude all marks.
  have hgeom :
      ∃ g : C(Circle × Set.Icc (-2 : ℝ) 3, S),
        Topology.IsEmbedding g ∧
        Set.range (fun z : Circle => g (z, ⟨0, by norm_num⟩)) = c.val.image ∧
        Set.range (fun z : Circle => g (z, ⟨1, by norm_num⟩)) = d.val.image ∧
        Disjoint (Set.range g) (M.cover.branch : Set S) := by
    obtain ⟨w,hw⟩ : (M.cover.branch.filter (· ∈ Uc)).Nonempty :=
      Finset.card_pos.mp (by rw [hUcMarks]; norm_num)
    have hwmark : w ∈ M.cover.branch := (Finset.mem_filter.mp hw).1
    have hwc : w ∉ c.val.image := by
      intro h
      exact Set.disjoint_left.mp c.val.avoids_branch h hwmark
    have hwd : w ∉ d.val.image := by
      intro h
      exact Set.disjoint_left.mp d.val.avoids_branch h hwmark
    obtain ⟨q,hq,hqc,hqd,hqcomponent⟩ :=
      scratch_sphere_pair_annulus M c.val.curve d.val.curve w hwc hwd hdisjoint
    obtain ⟨U,V,W,Z,hUopen,hVopen,hWopen,hZopen,hUconnected,hVconnected,
      hWconnected,hZconnected,hUVdisjoint,hWZdisjoint,hVZdisjoint,
      hUVcover,hWZcover,hUclosure,hVclosure,hWclosure,hZclosure,
      hdInU,hcInW,hqDisjointV,hqDisjointZ,hqPartition,
      g,hg,hgCentral⟩ :=
      scratch_sphere_annulus_partition M c.val.curve d.val.curve
        hdisjoint q hq hqc hqd hqcomponent
    have hMatchSides (C A B P Q : Set S)
        (hAopen : IsOpen A) (hBopen : IsOpen B)
        (hPopen : IsOpen P) (hQopen : IsOpen Q)
        (hAconn : IsConnected A) (hPconn : IsConnected P)
        (hABdisj : Disjoint A B) (hPQdisj : Disjoint P Q)
        (hABcover : A ∪ B = Cᶜ) (hPQcover : P ∪ Q = Cᶜ)
        (x : S) (hxA : x ∈ A) (hxP : x ∈ P) :
        A = P ∧ B = Q := by
      have hAsub : A ⊆ P ∪ Q := by rw [hPQcover,← hABcover]; exact subset_union_left
      have hPsub : P ⊆ A ∪ B := by rw [hABcover,← hPQcover]; exact subset_union_left
      have hAP : A ⊆ P := by
        rcases hAconn.isPreconnected.subset_or_subset
          hPopen hQopen hPQdisj hAsub with hAP | hAQ
        · exact hAP
        · exact False.elim (Set.disjoint_left.mp hPQdisj hxP (hAQ hxA))
      have hPA : P ⊆ A := by
        rcases hPconn.isPreconnected.subset_or_subset
          hAopen hBopen hABdisj hPsub with hPA | hPB
        · exact hPA
        · exact False.elim (Set.disjoint_left.mp hABdisj hxA (hPB hxP))
      have hAeqP : A = P := Set.Subset.antisymm hAP hPA
      constructor
      · exact hAeqP
      · ext y
        constructor
        · intro hyB
          have hyC : y ∈ Cᶜ := hABcover ▸ Or.inr hyB
          rcases hPQcover.symm ▸ hyC with hyP | hyQ
          · exact False.elim
              (Set.disjoint_left.mp hABdisj (hAeqP.symm ▸ hyP) hyB)
          · exact hyQ
        · intro hyQ
          have hyC : y ∈ Cᶜ := hPQcover ▸ Or.inr hyQ
          rcases hABcover.symm ▸ hyC with hyA | hyB
          · exact False.elim
              (Set.disjoint_left.mp hPQdisj (hAeqP ▸ hyA) hyQ)
          · exact hyB
    have hqMarks : Disjoint (Set.range q) (M.cover.branch : Set S) := by
      apply Set.disjoint_left.mpr
      intro x hxq hxmark
      rcases hNestedCirclePosition with hdInside | hcInside
      · have ⟨hUcU,hVcV⟩ := hMatchSides c.val.image Uc Vc U V
          hUcOpen hVcOpen hUopen hVopen hUcConnected hUconnected
          hUcVcDisjoint hUVdisjoint hUcVcCover hUVcover
          (d.val.curve.map z0) (hdInside (Set.mem_range_self _))
          (hdInU (Set.mem_range_self _))
        have ⟨hVdW,hUdZ⟩ := hMatchSides d.val.image Vd Ud W Z
          hVdOpen hUdOpen hWopen hZopen hVdConnected hWconnected
          hUdVdDisjoint.symm hWZdisjoint
          ((Set.union_comm Vd Ud).trans hUdVdCover) hWZcover
          (c.val.curve.map z0)
          ((hNestedTwoMarkSides hdInside).2 (Set.mem_range_self _))
          (hcInW (Set.mem_range_self _))
        have hxNotVc : x ∉ Vc :=
          fun hx => Set.disjoint_left.mp hqDisjointV hxq (hVcV ▸ hx)
        have hxNotUd : x ∉ Ud :=
          fun hx => Set.disjoint_left.mp hqDisjointZ hxq (hUdZ ▸ hx)
        have hxNotC : x ∉ c.val.image :=
          fun hx => Set.disjoint_left.mp c.val.avoids_branch hx hxmark
        have hxUc : x ∈ Uc := by
          rcases hUcVcCover.symm ▸ (show x ∈ c.val.imageᶜ from hxNotC) with hxUc | hxVc
          · exact hxUc
          · exact False.elim (hxNotVc hxVc)
        have hxUd : x ∈ Ud :=
          (Finset.mem_filter.mp (hActualSameMarks ▸
            (Finset.mem_filter.mpr ⟨hxmark,hxUc⟩))).2
        exact hxNotUd hxUd
      · have ⟨hVcU,hUcV⟩ := hMatchSides c.val.image Vc Uc U V
          hVcOpen hUcOpen hUopen hVopen hVcConnected hUconnected
          hUcVcDisjoint.symm hUVdisjoint
          ((Set.union_comm Vc Uc).trans hUcVcCover) hUVcover
          (d.val.curve.map z0)
          ((hReverseNestedTwoMarkSides hcInside).2 (Set.mem_range_self _))
          (hdInU (Set.mem_range_self _))
        have ⟨hUdW,hVdZ⟩ := hMatchSides d.val.image Ud Vd W Z
          hUdOpen hVdOpen hWopen hZopen hUdConnected hWconnected
          hUdVdDisjoint hWZdisjoint hUdVdCover hWZcover
          (c.val.curve.map z0) (hcInside (Set.mem_range_self _))
          (hcInW (Set.mem_range_self _))
        have hxNotUc : x ∉ Uc :=
          fun hx => Set.disjoint_left.mp hqDisjointV hxq (hUcV ▸ hx)
        have hxNotVd : x ∉ Vd :=
          fun hx => Set.disjoint_left.mp hqDisjointZ hxq (hVdZ ▸ hx)
        have hxNotD : x ∉ d.val.image :=
          fun hx => Set.disjoint_left.mp d.val.avoids_branch hx hxmark
        have hxUd : x ∈ Ud := by
          rcases hUdVdCover.symm ▸ (show x ∈ d.val.imageᶜ from hxNotD) with hxUd | hxVd
          · exact hxUd
          · exact False.elim (hxNotVd hxVd)
        have hxUc : x ∈ Uc :=
          (Finset.mem_filter.mp (hActualSameMarks.symm ▸
            (Finset.mem_filter.mpr ⟨hxmark,hxUd⟩))).2
        exact hxNotUc hxUc
    letI : T2Space S := M.sphere.symm.t2Space
    have hBranchClosed : IsClosed (M.cover.branch : Set S) :=
      M.cover.branch.finite_toSet.isClosed
    have hgCentralAvoid (z : Circle) (t : Set.Icc (-2:ℝ) 3)
        (ht0 : 0 ≤ (t:ℝ)) (ht1 : (t:ℝ) ≤ 1) :
        g (z,t) ∉ (M.cover.branch : Set S) := by
      rw [hgCentral (z,t) ht0 ht1]
      exact fun hb => Set.disjoint_left.mp hqMarks (Set.mem_range_self _) hb
    obtain ⟨g',hg',hg'0,hg'1,hg'marks⟩ :=
      trim_extended_annulus_away_from_closed_set
        (M.cover.branch : Set S) hBranchClosed g hg hgCentralAvoid
    refine ⟨g',hg',?_,?_,hg'marks⟩
    · calc
        Set.range (fun z : Circle => g' (z,⟨0,by norm_num⟩)) =
            Set.range (fun z : Circle => q (z,0)) := by
          congr 1
          funext z
          rw [hg'0 z]
          exact hgCentral (z,⟨0,by norm_num⟩) (by norm_num) (by norm_num)
        _ = c.val.image := by simpa only [PuncturedCircle.image] using hqc
    · calc
        Set.range (fun z : Circle => g' (z,⟨1,by norm_num⟩)) =
            Set.range (fun z : Circle => q (z,1)) := by
          congr 1
          funext z
          rw [hg'1 z]
          exact hgCentral (z,⟨1,by norm_num⟩) (by norm_num) (by norm_num)
        _ = d.val.image := by simpa only [PuncturedCircle.image] using hqd
  obtain ⟨g,hg,hgc,hgd,hmarks⟩ := hgeom
  obtain ⟨H,_,hfix,hlevels⟩ :=
    actual_extended_mark_free_annulus_ambient_isotopy M g hg hmarks
  exact ⟨H,hfix,by simpa only [hgc,hgd] using hlevels⟩
end CurveComplex.HyperellipticModel
