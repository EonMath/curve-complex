import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Filtration.Geometry.ActualJordanRegionsHeader
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
import CurveComplexGenusTwo.Topology.ArcStraightening
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Filtration.Geometry.MarkedCrosscutSurface
namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_bigon_face_contains_mark (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 ≠ a.val.map 1) (hb : b.val.map 0 ≠ b.val.map 1)
    (hends : markedArcEndset a.val = markedArcEndset b.val)
    (hd : Disjoint (a.val.image \ (M.cover.branch : Set S)) (b.val.image \ (M.cover.branch : Set S)))
    (hne : Quotient.mk (essentialArcSetoid M) a ≠ Quotient.mk (essentialArcSetoid M) b)
    (G U : Set S) (hG : IsClosed G)
    (haG : a.val.image ⊆ G) (hbG : b.val.image ⊆ G)
    (hU : IsComplementComponent G U)
    (hboundary : frontier U ⊆ a.val.image ∪ b.val.image) :
    ∃ z ∈ M.cover.branch, z ∈ U := by
  have hempty (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
      (ha : a.val.map 0 ≠ a.val.map 1) (hb : b.val.map 0 ≠ b.val.map 1)
      (hends : markedArcEndset a.val = markedArcEndset b.val)
      (hd : Disjoint (a.val.image \ (M.cover.branch : Set S)) (b.val.image \ (M.cover.branch : Set S)))
      (U : Set S) (hU : IsComplementComponent (a.val.image ∪ b.val.image) U)
      (hfree : ∀ z, z ∈ M.cover.branch → z ∉ U) :
      Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b := by
    have hnormalize (M : HyperellipticModel E S) (a b : NonLoopArc M)
        (hends : markedArcEndset a.val = markedArcEndset b.val)
        (hd : Disjoint (a.val.image \ (M.cover.branch : Set S)) (b.val.image \ (M.cover.branch : Set S)))
        (U : Set S) (hU : IsComplementComponent (a.val.image ∪ b.val.image) U)
        (hfree : ∀ z, z ∈ M.cover.branch → z ∉ U) :
        ∃ p ∈ M.cover.branch, ∃ hp : p ∉ a.val.image ∪ b.val.image,
          let e := M.puncturedPlane p
          let gA : Interval → Plane := fun t => e ⟨a.val.map t, fun he => hp (Or.inl (he ▸ Set.mem_range_self t))⟩
          let gB : Interval → Plane := fun t => e ⟨b.val.map t, fun he => hp (Or.inr (he ▸ Set.mem_range_self t))⟩
          ∃ F : Plane ≃ₜ Plane,
            F (gA 0) = cornerNE ∧ F (gA 1) = cornerSW ∧
            F '' (Set.range gA ∪ Set.range gB) = modelCurve ∧
            F '' ((fun z : Plane => (e.symm z).val) ⁻¹' U) = Plane.openSquare 0 1 := by
      have hchart (M : HyperellipticModel E S) (a b : NonLoopArc M)
          (hends : markedArcEndset a.val = markedArcEndset b.val)
          (hd : Disjoint (a.val.image \ (M.cover.branch : Set S)) (b.val.image \ (M.cover.branch : Set S)))
          (U : Set S) (hU : IsComplementComponent (a.val.image ∪ b.val.image) U)
          (hfree : ∀ z, z ∈ M.cover.branch → z ∉ U) :
          ∃ p ∈ M.cover.branch, p ∉ a.val.image ∪ b.val.image ∧ p ∉ closure U ∧
            let e := M.puncturedPlane p
            let f : Plane → S := fun z => (e.symm z).val
            IsOpen (f ⁻¹' U) ∧ IsConnected (f ⁻¹' U) ∧ Bornology.IsBounded (f ⁻¹' U) ∧
              frontier (f ⁻¹' U) = f ⁻¹' (a.val.image ∪ b.val.image) := by
        have hfront (M : HyperellipticModel E S) (a b : NonLoopArc M)
            (hends : markedArcEndset a.val = markedArcEndset b.val)
            (hd : Disjoint (a.val.image \ (M.cover.branch : Set S))
              (b.val.image \ (M.cover.branch : Set S))) :
            ∀ W : Set S, IsComplementComponent (a.val.image ∪ b.val.image) W →
              frontier W = a.val.image ∪ b.val.image := by
          classical
          have hcomponent : ∀ (g : CurveComplex.SpherePort.Sphere ≃ₜ S)
              {A U : Set CurveComplex.SpherePort.Sphere},
              IsComplementComponent A U → IsComplementComponent (g '' A) (g '' U) := by
            intro g A U hU
            rcases hU with ⟨hne, hconn, hsub, hmax⟩
            refine ⟨hne.image g, hconn.image g g.continuous.continuousOn, ?_, ?_⟩
            · rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
              exact hsub hx (g.injective heq ▸ hy)
            · intro V hV hUV hVA
              have hUV' : U ⊆ g.symm '' V := by
                intro x hx
                exact ⟨g x, hUV ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩
              have hVA' : g.symm '' V ⊆ Aᶜ := by
                rintro _ ⟨x, hx, rfl⟩ ha
                exact hVA hx ⟨g.symm x, ha, g.apply_symm_apply x⟩
              have hEq := hmax (g.symm '' V) (hV.image g.symm g.symm.continuous.continuousOn)
                hUV' hVA'
              calc
                V = g '' (g.symm '' V) := by
                  ext x
                  simp only [Set.mem_image]
                  constructor
                  · intro hx; exact ⟨g.symm x, ⟨x, hx, rfl⟩, g.apply_symm_apply x⟩
                  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simpa using hz
                _ = g '' U := congrArg (fun W : Set CurveComplex.SpherePort.Sphere => g '' W) hEq
        
        
          obtain ⟨c,hc⟩ := actual_parallel_pair_curve_unordered M a b hends hd
          obtain ⟨J,hJ⟩ := actualCurve_sphereJordan M c
          have hecard : (markedArcEndset a.val).card < M.cover.branch.card := by
            rw [M.cover.branch_card]
            have h : (markedArcEndset a.val).card ≤ 2 := Finset.card_le_two
            omega
          obtain ⟨p,hpmark,hpends⟩ := Finset.exists_mem_notMem_of_card_lt_card hecard
          have hpJ : M.sphere p ∉ J.image := by
            rw [hJ,hc]
            rintro ⟨x,hx,hxp⟩
            have he : x = p := M.sphere.injective hxp
            subst x
            rcases hx with ha | hb
            · apply hpends
              have h : p ∈ a.val.image ∩ (M.cover.branch : Set S) := ⟨ha,hpmark⟩
              rwa [markedArc_image_inter_branch] at h
            · apply hpends
              have h : p ∈ b.val.image ∩ (M.cover.branch : Set S) := ⟨hb,hpmark⟩
              rw [markedArc_image_inter_branch, ← hends] at h
              exact h
          let P : CurveComplex.SpherePort.Chart J := {
            puncture := M.sphere p
            avoids := hpJ
            plane := puncturedSpherePlane (M.sphere p) }
          obtain ⟨U,V,hU,hV,_,_,hdisj,hne,hcover,hfrU,hfrV⟩ := sphereJordan_two_regions J P
          have hback : M.sphere.symm '' J.image = (a.val.image ∪ b.val.image) := by
            rw [hJ, hc, ← image_comp, M.sphere.symm_comp_self, image_id]
          have hcU := hcomponent M.sphere.symm hU
          have hcV := hcomponent M.sphere.symm hV
          rw [hback] at hcU hcV
          let A := M.sphere.symm '' U
          let B := M.sphere.symm '' V
          have hneAB : A ≠ B := fun he => hne ((Set.image_injective.mpr M.sphere.symm.injective) he)
          have hAB : A ∪ B = (a.val.image ∪ b.val.image)ᶜ := by
            rw [← Set.image_union, hcover, M.sphere.symm.image_compl, hback]
          have hfrA : frontier A = a.val.image ∪ b.val.image := by
            rw [← M.sphere.symm.image_frontier,hfrU,hback]
          have hfrB : frontier B = a.val.image ∪ b.val.image := by
            rw [← M.sphere.symm.image_frontier,hfrV,hback]
          intro W hW
          obtain ⟨x,hx⟩ := hW.1
          have hxAB : x ∈ A ∪ B := by rw [hAB]; exact hW.2.2.1 hx
          rcases hxAB with hxA|hxB
          · have he : W = A := by
              by_contra hn
              exact Set.disjoint_left.mp (complementComponents_disjoint hW hcU hn) hx hxA
            exact he.symm ▸ hfrA
          · have he : W = B := by
              by_contra hn
              exact Set.disjoint_left.mp (complementComponents_disjoint hW hcV hn) hx hxB
            exact he.symm ▸ hfrB
        classical
        letI : T2Space S := M.sphere.symm.t2Space
        letI : CompactSpace S := M.sphere.symm.compactSpace
        letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
        have hfr : frontier U = a.val.image ∪ b.val.image := hfront M a b hends hd U hU
        have hcl : IsClosed (a.val.image ∪ b.val.image) := a.image_isCompact.isClosed.union b.image_isCompact.isClosed
        have hopen : IsOpen U := complementComponent_open hcl hU
        have hecard : (markedArcEndset a.val).card < M.cover.branch.card := by
          rw [M.cover.branch_card]
          have h : (markedArcEndset a.val).card ≤ 2 := Finset.card_le_two
          omega
        obtain ⟨p,hpm,hpe⟩ := Finset.exists_mem_notMem_of_card_lt_card hecard
        have hpC : p ∉ a.val.image ∪ b.val.image := by
          rintro (hpa|hpb)
          · have hpends : p ∈ (markedArcEndset a.val : Set S) := by
              rw [← markedArc_image_inter_branch]; exact ⟨hpa,hpm⟩
            exact hpe hpends
          · have hpends : p ∈ (markedArcEndset b.val : Set S) := by
              rw [← markedArc_image_inter_branch]; exact ⟨hpb,hpm⟩
            exact hpe (hends.symm ▸ hpends)
        have hpcl : p ∉ closure U := by
          intro hp
          have hpU := hfree p hpm
          have hpfr : p ∈ frontier U := by rw [hopen.frontier_eq]; exact ⟨hp,hpU⟩
          exact hpC (hfr ▸ hpfr)
        refine ⟨p,hpm,hpC,hpcl,?_⟩
        intro e f
        have hf : Topology.IsOpenEmbedding f :=
          isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
        have hconn : IsConnected (f ⁻¹' U) := hU.2.1.preimage_of_isOpenMap hf.injective hf.isOpenMap (by
          intro z hz
          have hznp : z ≠ p := fun he => hpcl (he ▸ subset_closure hz)
          exact ⟨e ⟨z,hznp⟩,congrArg Subtype.val (e.symm_apply_apply _)⟩)
        letI : CompactSpace (closure U) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
        have hcompact : IsCompact (Set.range (fun z : closure U => e ⟨z.val,by
            intro he; exact hpcl (he ▸ z.property)⟩)) :=
          isCompact_range (e.continuous.comp (Continuous.subtype_mk continuous_subtype_val _))
        have hsub : f ⁻¹' U ⊆ Set.range (fun z : closure U => e ⟨z.val,by
            intro he; exact hpcl (he ▸ z.property)⟩) := by
          intro z hz
          refine ⟨⟨f z,subset_closure hz⟩,?_⟩
          exact e.apply_symm_apply z
        refine ⟨hopen.preimage hf.continuous,hconn,hcompact.isBounded.subset hsub,?_⟩
        rw [← hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous U,hfr]
      have hstraight
          {A P : Set Plane} {a b : Plane}
          (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
          (hmeet : A ∩ P = {a, b})
          (hJ : IsJordanCurve (A ∪ P)) :
          ∃ F : Plane ≃ₜ Plane, F '' P = sideBottom ∪ sideRight ∧
            F a = cornerNE ∧ F b = cornerSW ∧
            F '' (A ∪ P) = modelCurve ∧ F '' inside (A ∪ P) = Plane.openSquare 0 1 := by
        let B : Set Plane := sideTop ∪ sideLeft
        let Q : Set Plane := sideBottom ∪ sideRight
        have hB : IsArcBetween B cornerNE cornerSW := by
          simpa [B] using isArcBetween_upperSides
        have hQ : IsArcBetween Q cornerNE cornerSW := by
          simpa [Q] using isArcBetween_lowerSides.reverse
        have hmeetTarget : B ∩ Q = {cornerNE, cornerSW} := by
          apply Subset.antisymm
          · intro z hz
            have hmem : z ∈ sideTop ∪ sideLeft ∧ z ∈ sideBottom ∪ sideRight := by
              simpa [B, Q] using hz
            rcases upperSides_meet_lowerSides z hmem.1 hmem.2 with rfl | rfl
            · simp
            · simp
          · intro z hz
            have hz' : z = cornerNE ∨ z = cornerSW := by simpa using hz
            rcases hz' with rfl | rfl
            · exact ⟨hB.left_mem, hQ.left_mem⟩
            · exact ⟨hB.right_mem, hQ.right_mem⟩
        obtain ⟨e, hArcImage, hleft, hright⟩ :=
          exists_homeomorph_union_arcs_preserving_second hA hP hB hQ hmeet hmeetTarget
        have hModel : B ∪ Q = modelCurve := by
          dsimp [B, Q]
          exact modelCurve_eq_sides.symm
        let eModel : ↥(A ∪ P) ≃ₜ ↥modelCurve := e.trans (Homeomorph.setCongr hModel)
        obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hJ isJordanCurve_modelCurve eModel
        have hImage : F '' P = Q := by
          ext y
          constructor
          · rintro ⟨x, hxP, rfl⟩
            have hxJ : x ∈ A ∪ P := Or.inr hxP
            have hxArc : (e ⟨x, hxJ⟩ : Plane) ∈ Q := by
              have hmem : (e ⟨x, hxJ⟩ : ↥(B ∪ Q)) ∈ e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P} :=
                ⟨⟨x, hxJ⟩, hxP, rfl⟩
              have hval : (e ⟨x, hxJ⟩ : Plane) ∈ Subtype.val ''
                  (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := Set.mem_image_of_mem _ hmem
              rw [hArcImage] at hval
              exact hval
            have hfx : F x = (eModel ⟨x, hxJ⟩ : Plane) := hF ⟨x, hxJ⟩
            have hEmodel : (eModel ⟨x, hxJ⟩ : Plane) = (e ⟨x, hxJ⟩ : Plane) := by rfl
            rw [hfx, hEmodel]
            simpa [Q] using hxArc
          · intro hy
            have hyQ : y ∈ Q := by simpa [Q] using hy
            have hyImage : y ∈ Subtype.val ''
                (e '' {z : ↥(A ∪ P) | (z : Plane) ∈ P}) := by rw [hArcImage]; exact hyQ
            obtain ⟨z, hzImage, hzy⟩ := hyImage
            obtain ⟨x, hxP, hzx⟩ := hzImage
            have hxJ : (x : Plane) ∈ A ∪ P := x.property
            refine ⟨(x : Plane), hxP, ?_⟩
            have hFz : F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) :=
              hF ⟨(x : Plane), hxJ⟩
            have hEmodel : (eModel ⟨(x : Plane), hxJ⟩ : Plane) =
                (e ⟨(x : Plane), hxJ⟩ : Plane) := rfl
            have hzx' : (e ⟨(x : Plane), hxJ⟩ : Plane) = (z : Plane) :=
              congrArg Subtype.val hzx
            calc
              F (x : Plane) = (eModel ⟨(x : Plane), hxJ⟩ : Plane) := hFz
              _ = (e ⟨(x : Plane), hxJ⟩ : Plane) := hEmodel
              _ = (z : Plane) := hzx'
              _ = y := hzy
        have hFa : F a = cornerNE := by
          let x : ↥(A ∪ P) := ⟨a, Or.inl hA.left_mem⟩
          have hxF : F (x : Plane) = (eModel x : Plane) := hF x
          have hxE : (eModel x : Plane) = (e x : Plane) := rfl
          have hxe : (e x : Plane) = cornerNE := by
            have h := congrArg Subtype.val hleft
            exact h
          calc
            F a = F (x : Plane) := rfl
            _ = (eModel x : Plane) := hxF
            _ = (e x : Plane) := hxE
            _ = cornerNE := hxe
        have hFb : F b = cornerSW := by
          let x : ↥(A ∪ P) := ⟨b, Or.inl hA.right_mem⟩
          have hxF : F (x : Plane) = (eModel x : Plane) := hF x
          have hxE : (eModel x : Plane) = (e x : Plane) := rfl
          have hxe : (e x : Plane) = cornerSW := by
            have h := congrArg Subtype.val hright
            exact h
          calc
            F b = F (x : Plane) := rfl
            _ = (eModel x : Plane) := hxF
            _ = (e x : Plane) := hxE
            _ = cornerSW := hxe
        have hFC : F '' (A ∪ P) = modelCurve := by
          ext y
          constructor
          · rintro ⟨x,hx,rfl⟩
            rw [hF ⟨x,hx⟩]
            exact (eModel ⟨x,hx⟩).property
          · intro hy
            let x := eModel.symm ⟨y,hy⟩
            refine ⟨x.val,x.property,?_⟩
            rw [hF x]
            exact congrArg Subtype.val (eModel.apply_symm_apply _)
        have hsep := jordan_curve_theorem hJ
        have hcompact : IsCompact (closure (inside (A ∪ P))) :=
          Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
        have hbounded : Bornology.IsBounded (F '' inside (A ∪ P)) :=
          (hcompact.image F.continuous).isBounded.subset (image_mono subset_closure)
        have hfront : frontier (F '' inside (A ∪ P)) = modelCurve := by
          rw [← F.image_frontier,hsep.frontier_inside,hFC]
        have hFI : F '' inside (A ∪ P) = Plane.openSquare 0 1 := by
          rw [bounded_jordan_frontier_region_eq_inside isJordanCurve_modelCurve
            (F.isOpenMap _ hsep.isOpen_inside)
            (hsep.isConnected_inside.image F F.continuous.continuousOn) hbounded hfront,
            inside_modelCurve]
        exact ⟨F,hImage,hFa,hFb,hFC,hFI⟩
      classical
      obtain ⟨p,hpm,hp,hpcl,hopen,hconn,hbounded,hfront⟩ := hchart M a b hends hd U hU hfree
      refine ⟨p,hpm,hp,?_⟩
      intro e gA gB
      let f : Plane → S := fun z => (e.symm z).val
      have hf : Function.Injective f := fun _ _ h => e.symm.injective (Subtype.ext h)
      have hgA (t : Interval) : f (gA t) = a.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
      have hgB (t : Interval) : f (gB t) = b.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
      have hA : IsArcBetween (Set.range gA) (gA 0) (gA 1) := a.plane_isArcBetween p (fun h => hp (Or.inl h))
      have hB : IsArcBetween (Set.range gB) (gA 0) (gA 1) := by
        have hmem0 : a.val.map 0 = b.val.map 0 ∨ a.val.map 0 = b.val.map 1 := by
          have h : a.val.map 0 ∈ markedArcEndset b.val := hends ▸ (by change a.val.map 0 ∈ ({a.val.map 0,a.val.map 1} : Finset S); simp)
          change a.val.map 0 ∈ ({b.val.map 0,b.val.map 1} : Finset S) at h
          simpa using h
        have hmem1 : a.val.map 1 = b.val.map 0 ∨ a.val.map 1 = b.val.map 1 := by
          have h : a.val.map 1 ∈ markedArcEndset b.val := hends ▸ (by change a.val.map 1 ∈ ({a.val.map 0,a.val.map 1} : Finset S); simp)
          change a.val.map 1 ∈ ({b.val.map 0,b.val.map 1} : Finset S) at h
          simpa using h
        rcases hmem0 with h0|h0
        · have h1 : a.val.map 1 = b.val.map 1 := hmem1.resolve_left (fun he => a.property (h0.trans he.symm))
          have he0 : gA 0 = gB 0 := hf (by rw [hgA,hgB,h0])
          have he1 : gA 1 = gB 1 := hf (by rw [hgA,hgB,h1])
          rw [he0,he1]
          exact b.plane_isArcBetween p (fun h => hp (Or.inr h))
        · have h1 : a.val.map 1 = b.val.map 0 := hmem1.resolve_right (fun he => a.property (h0.trans he.symm))
          have he0 : gA 0 = gB 1 := hf (by rw [hgA,hgB,h0])
          have he1 : gA 1 = gB 0 := hf (by rw [hgA,hgB,h1])
          rw [he0,he1]
          exact (b.plane_isArcBetween p (fun h => hp (Or.inr h))).reverse
      have hmeet : Set.range gA ∩ Set.range gB = {gA 0,gA 1} := by
        apply Set.Subset.antisymm
        · rintro z ⟨⟨t,rfl⟩,⟨s,hs⟩⟩
          have he : a.val.map t = b.val.map s := by
            rw [← hgA,← hgB,hs]
          have hm : a.val.map t ∈ M.cover.branch := by
            by_contra hn
            exact Set.disjoint_left.mp hd ⟨Set.mem_range_self t,hn⟩
              ⟨he ▸ Set.mem_range_self s,hn⟩
          rcases a.val.marked_only_at_ends t hm with ht|ht
          · subst t; simp
          · subst t; simp
        · intro z hz
          rcases Set.mem_insert_iff.mp hz with rfl|hz
          · exact ⟨Set.mem_range_self 0,hB.left_mem⟩
          · have hz1 : z = gA 1 := Set.mem_singleton_iff.mp hz
            subst z
            exact ⟨Set.mem_range_self 1,hB.right_mem⟩
      have hJ : IsJordanCurve (Set.range gA ∪ Set.range gB) := isJordanCurve_union hA hB (by
        intro z hzA hzB
        have hz := hmeet ▸ (show z ∈ Set.range gA ∩ Set.range gB from ⟨hzA,hzB⟩)
        simpa using hz)
      have hC : f ⁻¹' (a.val.image ∪ b.val.image) = Set.range gA ∪ Set.range gB := by
        ext z
        constructor
        · rintro (⟨t,ht⟩|⟨t,ht⟩)
          · exact Or.inl ⟨t,hf (by rw [hgA]; exact ht)⟩
          · exact Or.inr ⟨t,hf (by rw [hgB]; exact ht)⟩
        · rintro (⟨t,rfl⟩|⟨t,rfl⟩)
          · exact Or.inl (hgA t ▸ Set.mem_range_self t)
          · exact Or.inr (hgB t ▸ Set.mem_range_self t)
      have hD : f ⁻¹' U = inside (Set.range gA ∪ Set.range gB) :=
        bounded_jordan_frontier_region_eq_inside hJ hopen hconn hbounded (hfront.trans hC)
      obtain ⟨F,hFB,hF0,hF1,hFC,hFI⟩ := hstraight hA hB hmeet hJ
      exact ⟨F,hF0,hF1,hFC,by rw [hD]; exact hFI⟩
    have hlens (ell : ℝ) (hell : 0 < ell) :
        ∃ H : Plane ≃ₜ Plane, ∀ z : Plane,
          H z = Plane.mk ((z 0 + z 1)/2 + ell*(z 0-z 1)/2)
            ((z 0+z 1)/2 - ell*(z 0-z 1)/2) := by
      let F : Plane → Plane := fun z =>
        Plane.mk ((z 0 + z 1)/2 + ell*(z 0-z 1)/2)
          ((z 0+z 1)/2 - ell*(z 0-z 1)/2)
      let K : Plane → Plane := fun z =>
        Plane.mk ((z 0+z 1)/2+(z 0-z 1)/(2*ell)) ((z 0+z 1)/2-(z 0-z 1)/(2*ell))
      have hn : ell ≠ 0 := ne_of_gt hell
      let H : Plane ≃ₜ Plane := {
        toFun := F
        invFun := K
        left_inv := by
          intro z
          ext i
          fin_cases i <;> dsimp [F,K] <;> field_simp <;> ring
        right_inv := by
          intro z
          ext i
          fin_cases i <;> dsimp [F,K] <;> field_simp <;> ring
        continuous_toFun := by dsimp [F]; fun_prop
        continuous_invFun := by dsimp [K]; fun_prop }
      exact ⟨H,fun z => rfl⟩
    have hinterior (ell : ℝ) (hpos : 0 < ell) (hlt : ell < 1) {z : Plane}
        (hz : z ∈ modelCurve) (hne : z ≠ cornerNE) (hsw : z ≠ cornerSW) :
        Plane.mk ((z 0+z 1)/2+ell*(z 0-z 1)/2)
          ((z 0+z 1)/2-ell*(z 0-z 1)/2) ∈ Plane.openSquare 0 1 := by
      have hweight : ∀ u v a b : ℝ, -1 ≤ u → u ≤ 1 → -1 ≤ v → v ≤ 1 →
          ¬ (u = 1 ∧ v = 1) → ¬ (u = -1 ∧ v = -1) →
          0 < a → 0 < b → a+b = 1 → -1 < a*u+b*v ∧ a*u+b*v < 1 := by
        intro u v a b huL huR hvL hvR hnotR hnotL ha hb hab
        constructor
        · by_cases hu : u = -1
          · have hv : -1 < v := lt_of_le_of_ne hvL (fun he => hnotL ⟨hu,he.symm⟩)
            have h := mul_pos hb (show 0 < v+1 by linarith)
            nlinarith
          · have hu' : -1 < u := lt_of_le_of_ne huL (Ne.symm hu)
            have h := mul_pos ha (show 0 < u+1 by linarith)
            have h' := mul_nonneg hb.le (show 0 ≤ v+1 by linarith)
            nlinarith
        · by_cases hu : u = 1
          · have hv : v < 1 := lt_of_le_of_ne hvR (fun he => hnotR ⟨hu,he⟩)
            have h := mul_pos hb (show 0 < 1-v by linarith)
            nlinarith
          · have hu' : u < 1 := lt_of_le_of_ne huR hu
            have h := mul_pos ha (show 0 < 1-u by linarith)
            have h' := mul_nonneg hb.le (show 0 ≤ 1-v by linarith)
            nlinarith
      have hzN : Plane.supNorm z = 1 := hz
      have h0 : |z 0| ≤ 1 := (Plane.abs_zero_le_supNorm z).trans hzN.le
      have h1 : |z 1| ≤ 1 := (Plane.abs_one_le_supNorm z).trans hzN.le
      have hnR : ¬ (z 0 = 1 ∧ z 1 = 1) := by
        rintro ⟨h0,h1⟩
        apply hne
        ext i
        fin_cases i <;> simp [cornerNE,h0,h1]
      have hnL : ¬ (z 0 = -1 ∧ z 1 = -1) := by
        rintro ⟨h0,h1⟩
        apply hsw
        ext i
        fin_cases i <;> simp [cornerSW,h0,h1]
      have ha : 0 < (1+ell)/2 := by linarith
      have hb : 0 < (1-ell)/2 := by linarith
      have hab : (1+ell)/2+(1-ell)/2 = 1 := by ring
      have hc0 := hweight (z 0) (z 1) ((1+ell)/2) ((1-ell)/2)
        (abs_le.mp h0).1 (abs_le.mp h0).2 (abs_le.mp h1).1 (abs_le.mp h1).2 hnR hnL ha hb hab
      have hc1 := hweight (z 0) (z 1) ((1-ell)/2) ((1+ell)/2)
        (abs_le.mp h0).1 (abs_le.mp h0).2 (abs_le.mp h1).1 (abs_le.mp h1).2 hnR hnL hb ha (by linarith)
      apply mem_openSquare_zero_one.mpr
      rw [Plane.supNorm,max_lt_iff]
      constructor
      · apply abs_lt.mpr
        dsimp
        constructor <;> nlinarith [hc0.1,hc0.2]
      · apply abs_lt.mpr
        dsimp
        constructor <;> nlinarith [hc1.1,hc1.2]
    have hfinite (T : Finset Plane) (hT : ∀ z ∈ T, z ∉ Plane.closedSquare 0 1) :
        ∃ ell : ℝ, 0 < ell ∧ ell < 1 ∧ ∀ z ∈ T,
          Plane.mk ((z 0+z 1)/2+ell*(z 0-z 1)/2)
            ((z 0+z 1)/2-ell*(z 0-z 1)/2) ∉ Plane.closedSquare 0 1 := by
      let L : ℝ → Plane → Plane := fun ell z =>
        Plane.mk ((z 0+z 1)/2+ell*(z 0-z 1)/2)
          ((z 0+z 1)/2-ell*(z 0-z 1)/2)
      have hL1 : ∀ z, L 1 z = z := by
        intro z
        ext i
        fin_cases i <;> dsimp [L] <;> ring
      let V := ⋂ z : {z // z ∈ T}, (fun ell => L ell z.val) ⁻¹' (Plane.closedSquare 0 1)ᶜ
      have hV : IsOpen V := isOpen_iInter_of_finite (fun z =>
        (Plane.isClosed_closedSquare 0 1).isOpen_compl.preimage (by dsimp [L]; fun_prop))
      have h1 : (1 : ℝ) ∈ V := by
        apply mem_iInter.mpr
        intro z
        change L 1 z.val ∉ Plane.closedSquare 0 1
        rw [hL1]
        exact hT z.val z.property
      obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hV 1 h1
      let d := min (eps/2) (1/2)
      have hd : 0 < d := lt_min (by linarith) (by norm_num)
      have hde : d < eps := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hdh : d ≤ 1/2 := min_le_right _ _
      have hell : 0 < 1-d := by linarith
      have hell1 : 1-d < 1 := by linarith
      have hmem : 1-d ∈ V := hball (by
        rw [mem_ball,Real.dist_eq]
        have he : |(1-d)-1| = d := by rw [show (1-d)-1 = -d by ring,abs_neg,abs_of_pos hd]
        rw [he]; exact hde)
      refine ⟨1-d,hell,hell1,?_⟩
      intro z hz
      exact mem_iInter.mp hmem ⟨z,hz⟩
    have hcross (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
        (U : Set S) (V : Set Plane) (hU : IsOpen U)
        (e : U ≃ₜ V) (hSquare : Plane.closedSquare 0 1 ⊆ V)
        (A B : Set Plane) (p q : Plane)
        (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
        (hp : p ∈ modelCurve) (hq : q ∈ modelCurve)
        (hAi : A \ {p, q} ⊆ Plane.openSquare 0 1)
        (hBi : B \ {p, q} ⊆ Plane.openSquare 0 1)
        (haImage : a.val.image = {x : S | ∃ u : U, u.val = x ∧ (e u : Plane) ∈ A})
        (hbImage : b.val.image = {x : S | ∃ u : U, u.val = x ∧ (e u : Plane) ∈ B})
        (hfree : ∀ u : U, u.val ∈ M.cover.branch →
          (e u : Plane) ∉ Plane.openSquare 0 1) :
        Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b := by
      letI : T2Space S := M.sphere.symm.t2Space
      letI : CompactSpace S := M.sphere.symm.compactSpace
      obtain ⟨G, himage, houtside, hcoordinate⟩ :=
        CurveComplex.marked_crosscut_surface_replacement S U V hU e hSquare
          A B p q hA hB hp hq hAi hBi
      apply Quotient.sound
      refine ⟨G, ?_, ?_⟩
      · intro t x hx
        by_cases hxU : x ∈ U
        · exact hcoordinate t ⟨x, hxU⟩ (hfree ⟨x, hxU⟩ hx)
        · exact houtside t x hxU
      · rw [haImage, hbImage]
        exact himage
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let na : NonLoopArc M := ⟨a.val,ha⟩
    let nb : NonLoopArc M := ⟨b.val,hb⟩
    obtain ⟨p,hpm,hp,F,hF0,hF1,hFC,hFI⟩ := hnormalize M na nb hends hd U hU hfree
    let e := M.puncturedPlane p
    let f : Plane → S := fun z => (e.symm z).val
    let gA : Interval → Plane := fun t => e ⟨a.val.map t,fun he => hp (Or.inl (he ▸ Set.mem_range_self t))⟩
    let gB : Interval → Plane := fun t => e ⟨b.val.map t,fun he => hp (Or.inr (he ▸ Set.mem_range_self t))⟩
    have hf : Function.Injective f := fun _ _ he => e.symm.injective (Subtype.ext he)
    have hfe (z : {z : S // z ≠ p}) : f (e z) = z.val := congrArg Subtype.val (e.symm_apply_apply z)
    have hgA (t : Interval) : f (gA t) = a.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
    have hgB (t : Interval) : f (gB t) = b.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
    have hA : IsArcBetween (Set.range gA) (gA 0) (gA 1) := na.plane_isArcBetween p (fun h => hp (Or.inl h))
    have hB : IsArcBetween (Set.range gB) (gA 0) (gA 1) := by
      have hmem0 : a.val.map 0 = b.val.map 0 ∨ a.val.map 0 = b.val.map 1 := by
        have h : a.val.map 0 ∈ markedArcEndset b.val := hends ▸ (by change a.val.map 0 ∈ ({a.val.map 0,a.val.map 1} : Finset S); simp)
        change a.val.map 0 ∈ ({b.val.map 0,b.val.map 1} : Finset S) at h
        simpa using h
      have hmem1 : a.val.map 1 = b.val.map 0 ∨ a.val.map 1 = b.val.map 1 := by
        have h : a.val.map 1 ∈ markedArcEndset b.val := hends ▸ (by change a.val.map 1 ∈ ({a.val.map 0,a.val.map 1} : Finset S); simp)
        change a.val.map 1 ∈ ({b.val.map 0,b.val.map 1} : Finset S) at h
        simpa using h
      rcases hmem0 with h0|h0
      · have h1 : a.val.map 1 = b.val.map 1 := hmem1.resolve_left (fun he => ha (h0.trans he.symm))
        have he0 : gA 0 = gB 0 := hf (by rw [hgA,hgB,h0])
        have he1 : gA 1 = gB 1 := hf (by rw [hgA,hgB,h1])
        rw [he0,he1]
        exact nb.plane_isArcBetween p (fun h => hp (Or.inr h))
      · have h1 : a.val.map 1 = b.val.map 0 := hmem1.resolve_right (fun he => ha (h0.trans he.symm))
        have he0 : gA 0 = gB 1 := hf (by rw [hgA,hgB,h0])
        have he1 : gA 1 = gB 0 := hf (by rw [hgA,hgB,h1])
        rw [he0,he1]
        exact (nb.plane_isArcBetween p (fun h => hp (Or.inr h))).reverse
    have hFmarked (z : {z : S // z ≠ p}) (hz : z.val ∈ M.cover.branch)
        (hz0 : z.val ≠ a.val.map 0) (hz1 : z.val ≠ a.val.map 1) :
        F (e z) ∉ Plane.closedSquare 0 1 := by
      have hnotC : F (e z) ∉ modelCurve := by
        rw [← hFC]
        rintro ⟨w,hw,hew⟩
        have hew' : w = e z := F.injective hew
        subst w
        have hza : z.val ∈ a.val.image ∪ b.val.image := by
          rcases hw with ⟨t,ht⟩|⟨t,ht⟩
          · exact Or.inl ⟨t,by
              change gA t = e z at ht
              have he := congrArg f ht
              rwa [hgA,hfe] at he⟩
          · exact Or.inr ⟨t,by
              change gB t = e z at ht
              have he := congrArg f ht
              rwa [hgB,hfe] at he⟩
        have he : z.val ∈ markedArcEndset a.val := by
          rcases hza with hza|hzb
          · have hzA : z.val ∈ a.val.image ∩ (M.cover.branch : Set S) := ⟨hza,hz⟩
            rwa [markedArc_image_inter_branch] at hzA
          · have hzB : z.val ∈ b.val.image ∩ (M.cover.branch : Set S) := ⟨hzb,hz⟩
            rw [markedArc_image_inter_branch,← hends] at hzB
            exact hzB
        change z.val ∈ ({a.val.map 0,a.val.map 1} : Finset S) at he
        have he' : z.val = a.val.map 0 ∨ z.val = a.val.map 1 := by simpa using he
        exact he'.elim hz0 hz1
      have hnotI : F (e z) ∉ Plane.openSquare 0 1 := by
        rw [← hFI]
        rintro ⟨w,hw,hew⟩
        have hew' : w = e z := F.injective hew
        subst w
        have hzU : z.val ∈ U := by
          change f (e z) ∈ U at hw
          rwa [hfe] at hw
        exact hfree z.val hz hzU
      intro hclosed
      have hle : Plane.supNorm (F (e z)) ≤ 1 := mem_closedSquare_zero_one.mp hclosed
      rcases lt_or_eq_of_le hle with hlt|heq
      · exact hnotI (mem_openSquare_zero_one.mpr hlt)
      · exact hnotC heq
    let Z : Finset S := M.cover.branch.filter (fun z => z ≠ p ∧ z ≠ a.val.map 0 ∧ z ≠ a.val.map 1)
    let T : Finset Plane := Z.attach.image (fun z => F (e ⟨z.val,(Finset.mem_filter.mp z.property).2.1⟩))
    have hT : ∀ w ∈ T, w ∉ Plane.closedSquare 0 1 := by
      intro w hw
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
      have hz' := Finset.mem_filter.mp z.property
      exact hFmarked _ hz'.1 hz'.2.2.1 hz'.2.2.2
    obtain ⟨ell,hell,hell1,havoid⟩ := hfinite T hT
    obtain ⟨H,hH⟩ := hlens ell hell
    have hH0 : H cornerNE = cornerNE := by
      rw [hH]; ext i; fin_cases i <;> simp [cornerNE] <;> ring
    have hH1 : H cornerSW = cornerSW := by
      rw [hH]; ext i; fin_cases i <;> simp [cornerSW] <;> ring
    let K : Plane ≃ₜ Plane := F.trans H
    have hK0 : K (gA 0) = cornerNE := by change H (F (gA 0)) = _; rw [hF0,hH0]
    have hK1 : K (gA 1) = cornerSW := by change H (F (gA 1)) = _; rw [hF1,hH1]
    let A := K '' Set.range gA
    let B := K '' Set.range gB
    have hArcA : IsArcBetween A cornerNE cornerSW := by
      have h := hA.image_of_injOn (Set.subset_univ _) K.continuous.continuousOn K.injective.injOn
      simpa only [hK0,hK1] using h
    have hArcB : IsArcBetween B cornerNE cornerSW := by
      have h := hB.image_of_injOn (Set.subset_univ _) K.continuous.continuousOn K.injective.injOn
      simpa only [hK0,hK1] using h
    have hproper (C : Set Plane) (hC : C ⊆ Set.range gA ∪ Set.range gB) :
        (K '' C) \ {cornerNE,cornerSW} ⊆ Plane.openSquare 0 1 := by
      rintro z ⟨⟨w,hw,rfl⟩,hz⟩
      have hwcurve : F w ∈ modelCurve := by rw [← hFC]; exact Set.mem_image_of_mem F (hC hw)
      have hwNE : F w ≠ cornerNE := by
        intro he
        apply hz
        change H (F w) ∈ _
        rw [he,hH0]
        simp
      have hwSW : F w ≠ cornerSW := by
        intro he
        apply hz
        change H (F w) ∈ _
        rw [he,hH1]
        simp
      change H (F w) ∈ _
      rw [hH]
      exact hinterior ell hell hell1 hwcurve hwNE hwSW
    let U0 : Set S := {z | z ≠ p}
    let V : Set Plane := Set.univ
    let chart : U0 ≃ₜ V := (e.trans K).trans (Homeomorph.Set.univ Plane).symm
    have hchartval (u : U0) : (chart u : Plane) = K (e u) := rfl
    have hImageA : a.val.image = {z : S | ∃ u : U0, u.val = z ∧ (chart u : Plane) ∈ A} := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        refine ⟨⟨a.val.map t,fun he => hp (Or.inl (he ▸ Set.mem_range_self t))⟩,rfl,?_⟩
        exact Set.mem_image_of_mem K (Set.mem_range_self t)
      · rintro ⟨u,rfl,w,⟨t,rfl⟩,he⟩
        have he' : gA t = e u := K.injective he
        exact ⟨t,by have h := congrArg f he'; rwa [hgA,hfe] at h⟩
    have hImageB : b.val.image = {z : S | ∃ u : U0, u.val = z ∧ (chart u : Plane) ∈ B} := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        refine ⟨⟨b.val.map t,fun he => hp (Or.inr (he ▸ Set.mem_range_self t))⟩,rfl,?_⟩
        exact Set.mem_image_of_mem K (Set.mem_range_self t)
      · rintro ⟨u,rfl,w,⟨t,rfl⟩,he⟩
        have he' : gB t = e u := K.injective he
        exact ⟨t,by have h := congrArg f he'; rwa [hgB,hfe] at h⟩
    have hchartfree : ∀ u : U0, u.val ∈ M.cover.branch → (chart u : Plane) ∉ Plane.openSquare 0 1 := by
      intro u hu
      rw [hchartval]
      by_cases hu0 : u.val = a.val.map 0
      · have he : e u = gA 0 := congrArg e (Subtype.ext hu0)
        rw [he,hK0]
        intro h
        have hn := mem_openSquare_zero_one.mp h
        norm_num [Plane.supNorm,cornerNE] at hn
      by_cases hu1 : u.val = a.val.map 1
      · have he : e u = gA 1 := congrArg e (Subtype.ext hu1)
        rw [he,hK1]
        intro h
        have hn := mem_openSquare_zero_one.mp h
        norm_num [Plane.supNorm,cornerSW] at hn
      have huZ : u.val ∈ Z := Finset.mem_filter.mpr ⟨hu,u.property,hu0,hu1⟩
      have huT : F (e u) ∈ T := by
        apply Finset.mem_image.mpr
        refine ⟨⟨u.val,huZ⟩,Finset.mem_attach _ _,rfl⟩
      have hnot := havoid (F (e u)) huT
      change H (F (e u)) ∉ _
      rw [← hH] at hnot
      exact fun h => hnot ((mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp h).le))
    exact hcross M a b U0 V isOpen_compl_singleton chart
      (Set.subset_univ _) A B cornerNE cornerSW hArcA hArcB
      (by norm_num [modelCurve,Plane.supNorm,cornerNE])
      (by norm_num [modelCurve,Plane.supNorm,cornerSW])
      (hproper _ Set.subset_union_left) (hproper _ Set.subset_union_right)
      hImageA hImageB hchartfree
  classical
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hopen : IsOpen U := complementComponent_open hG hU
  have hUA : U ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro x hx hxa
    rcases hxa with hxA|hxB
    · exact hU.2.2.1 hx (haG hxA)
    · exact hU.2.2.1 hx (hbG hxB)
  have hcomp : IsComplementComponent (a.val.image ∪ b.val.image) U := by
    refine ⟨hU.1,hU.2.1,hUA,?_⟩
    intro V hV hUV hVA
    have hcl : closure U ∩ V ⊆ U := by
      intro x hx
      by_contra hn
      have hxf : x ∈ frontier U := by
        rw [hopen.frontier_eq]
        exact ⟨hx.1,hn⟩
      exact hVA hx.2 (hboundary hxf)
    have hVU : V ⊆ U := hV.isPreconnected.subset_of_closure_inter_subset hopen
      (by obtain ⟨x,hx⟩ := hU.1; exact ⟨x,hUV hx,hx⟩) hcl
    exact Set.Subset.antisymm hVU hUV
  by_contra hnomark
  have hfree : ∀ z, z ∈ M.cover.branch → z ∉ U := by
    intro z hzm hzU
    exact hnomark ⟨z,hzm,hzU⟩
  exact hne (hempty M a b ha hb hends hd U hcomp hfree)
end CurveComplex.HyperellipticModel
