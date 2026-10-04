import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualTwoMarkDiskComparisonRegion
import CurveComplexGenusTwo.Filtration.Geometry.ActualEmptyBigonUnorderedClassNamedHeader
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEndpointBigonRelativeAlignment
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion

open Lean Elab Tactic in
elab "audit_main14_original_terminal_supported_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in actual original supported terminal alignment: {ax}"
  logInfo m!"Actual original supported terminal alignment proof axiom audit: {found.toList}"
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1000000
open Metric Schoenflies
set_option maxHeartbeats 2000000
theorem actual_original_disjoint_disk_arcs_supported_terminal_alignment (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
    (hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1})
    (hmeet : a.image ∩ b.image = {a.val.map 0,a.val.map 1}) :
    ∃ H : AmbientIsotopy S,
      (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
      H.finalMap '' a.image=b.image := by
  audit_main14_original_terminal_supported_base3
    have hExterior (M : HyperellipticModel E S) (a : NonLoopArc M) (N : ArcNeighborhood a) :
        IsConnected (interior N.closedSet)ᶜ ∧ ∃ p : S, p ∈ M.cover.branch ∧ p ∉ N.closedSet := by
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      have hzero : (0 : Interval) = ⟨0,by norm_num⟩ := by apply Subtype.ext; norm_num
      have hone : (1 : Interval) = ⟨1,by norm_num⟩ := by apply Subtype.ext; norm_num
      have hKcompact : IsCompact N.closedSet := by
        have h := isCompact_range N.disk.continuous
        have hr : range (fun z => (N.disk z : S)) = N.closedSet := by
          ext x; constructor
          · rintro ⟨z,rfl⟩; exact (N.disk z).property
          · intro hx; exact ⟨N.disk.symm ⟨x,hx⟩,congrArg Subtype.val (N.disk.apply_symm_apply ⟨x,hx⟩)⟩
        rw [← hr]
        exact isCompact_range (continuous_subtype_val.comp N.disk.continuous)
      have hKclosed := hKcompact.isClosed
      obtain ⟨U,V,hU,hV,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
        M.puncturedCircle_closedSides N.boundary
      have hpart (W : Set S) (hW : IsConnected W) (hWc : W ⊆ N.boundary.imageᶜ) :
          W ⊆ interior N.closedSet ∨ W ⊆ N.closedSetᶜ := by
        apply hW.isPreconnected.subset_or_subset isOpen_interior hKclosed.isOpen_compl
          (Set.disjoint_left.mpr (fun _ hi ho => ho (interior_subset hi)))
        intro x hx
        by_cases hxK : x ∈ N.closedSet
        · left
          by_contra hxi
          have hxf : x ∈ frontier N.closedSet := (mem_frontier_iff_notMem_interior hxK).mpr hxi
          exact hWc hx (N.boundary_eq_frontier.symm ▸ hxf)
        · exact Or.inr hxK
      have hUcomp : U ⊆ N.boundary.imageᶜ := by rw [← hcover]; exact subset_union_left
      have hVcomp : V ⊆ N.boundary.imageᶜ := by rw [← hcover]; exact subset_union_right
      have hstart : a.val.map 0 ∈ interior N.closedSet := N.arc_inside (mem_range_self 0)
      have hstartc : a.val.map 0 ∉ N.boundary.image := by
        rw [N.boundary_eq_frontier]
        exact Set.disjoint_left.mp disjoint_interior_frontier hstart
      have houtside : ∃ x, x ∈ M.cover.branch ∧ x ∉ N.closedSet := by
        let F : Finset S := {a.val.map 0,a.val.map 1}
        have hF : F.card < M.cover.branch.card := by
          rw [M.cover.branch_card]
          have hh := Finset.card_insert_le (a.val.map 0) ({a.val.map 1}:Finset S)
          simp only [Finset.card_singleton] at hh
          change ({a.val.map 0,a.val.map 1}:Finset S).card < 6
          omega
        obtain ⟨x,hx,hxn⟩ := Finset.exists_mem_notMem_of_card_lt_card hF
        refine ⟨x,hx,?_⟩
        intro hxK
        have he : x ∈ ({a.val.map 0,a.val.map 1}:Set S) := by
          have hh : x ∈ (M.cover.branch:Set S) ∩ N.closedSet := ⟨hx,hxK⟩
          have hh' := N.marked_inside ▸ hh
          convert hh' using 1
        exact hxn (by simpa [F] using he)
      have hmake (W Z : Set S) (hWc : IsConnected W) (hZc : IsConnected Z)
          (hWZ : Disjoint W Z) (hWZcover : W ∪ Z = N.boundary.imageᶜ)
          (hWin : W ⊆ interior N.closedSet) (hZout : Z ⊆ N.closedSetᶜ)
          (hclZ : closure Z=Z ∪ N.boundary.image) : IsConnected (interior N.closedSet)ᶜ := by
        have hWint : W = interior N.closedSet := by
          apply Set.Subset.antisymm hWin
          intro x hx
          have hxc : x ∉ N.boundary.image := by
            rw [N.boundary_eq_frontier]
            exact Set.disjoint_left.mp disjoint_interior_frontier hx
          rcases (show x ∈ W ∪ Z from by rw [hWZcover]; exact hxc) with hw | hz
          · exact hw
          · exact False.elim (hZout hz (interior_subset hx))
        have he : Wᶜ=closure Z := by
          rw [hclZ]
          ext x
          constructor
          · intro hx
            by_cases hxb : x ∈ N.boundary.image
            · exact Or.inr hxb
            · rcases (show x ∈ W ∪ Z from by rw [hWZcover]; exact hxb) with hw | hz
              · exact False.elim (hx hw)
              · exact Or.inl hz
          · rintro (hz | hb) hw
            · exact Set.disjoint_left.mp hWZ hw hz
            · have hc : x ∈ N.boundary.imageᶜ := by rw [←hWZcover]; exact Or.inl hw
              exact hc hb
        rw [←hWint,he]
        exact hZc.closure
      rcases hpart U hUc hUcomp with hUin | hUout <;>
        rcases hpart V hVc hVcomp with hVin | hVout
      · obtain ⟨x,hxB,hxK⟩ := houtside
        have hxc : x ∉ N.boundary.image := fun hc => hxK (hKclosed.frontier_subset (N.boundary_eq_frontier ▸ hc))
        rcases (show x ∈ U ∪ V from by rw [hcover]; exact hxc) with hu | hv
        · exact False.elim (hxK (interior_subset (hUin hu)))
        · exact False.elim (hxK (interior_subset (hVin hv)))
      · exact ⟨hmake U V hUc hVc hUV hcover hUin hVout hclV,houtside⟩
      · exact ⟨hmake V U hVc hUc hUV.symm ((union_comm V U).trans hcover) hVin hUout hclU,houtside⟩
      · rcases (show a.val.map 0 ∈ U ∪ V from by rw [hcover]; exact hstartc) with hu | hv
        · exact False.elim (hUout hu (interior_subset hstart))
        · exact False.elim (hVout hv (interior_subset hstart))
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
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    have ha : a.val.map 0 ≠ a.val.map 1 := by convert a.property using 1
    have hbn : b.val.map 0 ≠ b.val.map 1 := by convert b.property using 1
    have hendsFin : markedArcEndset a.val=markedArcEndset b.val := by
      apply Finset.coe_injective
      simp only [markedArcEndset,Finset.coe_insert,Finset.coe_singleton]
      convert hends using 1
    have hd : Disjoint (a.val.image \ (M.cover.branch:Set S)) (b.val.image \ (M.cover.branch:Set S)) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have he : x ∈ ({a.val.map 0,a.val.map 1}:Set S) := hmeet ▸ ⟨hx.1,hy.1⟩
      rcases he with he | he
      · exact hx.2 (he ▸ a.val.start_marked)
      · exact hx.2 ((Set.mem_singleton_iff.mp he) ▸ a.val.end_marked)
    obtain ⟨Ω,hn,hconn,hsub,hmax,hfront,hfree⟩ :=
      M.actual_two_mark_disk_disjoint_arcs_comparison_region a b N hb hends hmeet
    obtain ⟨hExteriorConn,p,hp,hpN⟩ := hExterior M a N
    let P : Set S := (interior N.closedSet)ᶜ
    have hPsub : P ⊆ (a.image ∪ b.image)ᶜ := by
      intro x hx hg
      exact hx (hg.elim (fun hxA => N.arc_inside hxA) (fun hxB => hb hxB))
    have hΩN : Ω ⊆ interior N.closedSet := by
      intro x hx
      by_contra hh
      have hmeet : (Ω ∩ P).Nonempty := ⟨x,hx,hh⟩
      have hc : IsConnected (Ω ∪ P) := hconn.union hmeet hExteriorConn
      have he : Ω ∪ P=Ω := hmax _ hc Set.subset_union_left (by rintro x (hx | hx); exact hsub hx; exact hPsub hx)
      have hpP : p ∈ P := fun hi => hpN (interior_subset hi)
      have hpΩ : p ∈ Ω := by rw [←he]; exact Or.inr hpP
      exact Set.disjoint_left.mp hfree hpΩ hp
    obtain ⟨p,hpm,hp,F,hF0,hF1,hFC,hFI⟩ := hnormalize M a b hendsFin hd Ω
      ⟨hn,hconn,hsub,hmax⟩ (fun z hz hΩ => Set.disjoint_left.mp hfree hΩ hz)
    let e := M.puncturedPlane p
    let f : Plane → S := fun z => (e.symm z).val
    let gA : Interval → Plane := fun t => e ⟨a.val.map t,fun he => hp (Or.inl (he ▸ Set.mem_range_self t))⟩
    let gB : Interval → Plane := fun t => e ⟨b.val.map t,fun he => hp (Or.inr (he ▸ Set.mem_range_self t))⟩
    have hf : Function.Injective f := fun _ _ he => e.symm.injective (Subtype.ext he)
    have hfe (z : {z : S // z ≠ p}) : f (e z) = z.val := congrArg Subtype.val (e.symm_apply_apply z)
    have hgA (t : Interval) : f (gA t) = a.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
    have hgB (t : Interval) : f (gB t) = b.val.map t := congrArg Subtype.val (e.symm_apply_apply _)
    have hA : IsArcBetween (Set.range gA) (gA 0) (gA 1) := a.plane_isArcBetween p (fun h => hp (Or.inl h))
    have hB : IsArcBetween (Set.range gB) (gA 0) (gA 1) := by
      have hmem0 : a.val.map 0 = b.val.map 0 ∨ a.val.map 0 = b.val.map 1 := by
        have h : a.val.map 0 ∈ markedArcEndset b.val := hendsFin ▸ (by change a.val.map 0 ∈ ({a.val.map 0,a.val.map 1} : Finset S); simp)
        change a.val.map 0 ∈ ({b.val.map 0,b.val.map 1} : Finset S) at h
        simpa using h
      have hmem1 : a.val.map 1 = b.val.map 0 ∨ a.val.map 1 = b.val.map 1 := by
        have h : a.val.map 1 ∈ markedArcEndset b.val := hendsFin ▸ (by change a.val.map 1 ∈ ({a.val.map 0,a.val.map 1} : Finset S); simp)
        change a.val.map 1 ∈ ({b.val.map 0,b.val.map 1} : Finset S) at h
        simpa using h
      rcases hmem0 with h0|h0
      · have h1 : a.val.map 1 = b.val.map 1 := hmem1.resolve_left (fun he => ha (h0.trans he.symm))
        have he0 : gA 0 = gB 0 := hf (by rw [hgA,hgB,h0])
        have he1 : gA 1 = gB 1 := hf (by rw [hgA,hgB,h1])
        rw [he0,he1]
        exact b.plane_isArcBetween p (fun h => hp (Or.inr h))
      · have h1 : a.val.map 1 = b.val.map 0 := hmem1.resolve_right (fun he => ha (h0.trans he.symm))
        have he0 : gA 0 = gB 1 := hf (by rw [hgA,hgB,h0])
        have he1 : gA 1 = gB 0 := hf (by rw [hgA,hgB,h1])
        rw [he0,he1]
        exact (b.plane_isArcBetween p (fun h => hp (Or.inr h))).reverse
    let fN : Plane → S := f ∘ F.symm
    have hfN : Topology.IsOpenEmbedding fN :=
      (isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding).comp F.symm.isOpenEmbedding
    let A : Set Plane := F '' Set.range gA
    let B : Set Plane := F '' Set.range gB
    have hF0new : F (gA 0)=cornerNE := hF0
    have hF1new : F (gA 1)=cornerSW := hF1
    have hArcA : IsArcBetween A cornerNE cornerSW := by
      have h := hA.image_of_injOn (Set.subset_univ _) F.continuous.continuousOn F.injective.injOn
      simpa only [hF0new,hF1new] using h
    have hArcB : IsArcBetween B cornerNE cornerSW := by
      have h := hB.image_of_injOn (Set.subset_univ _) F.continuous.continuousOn F.injective.injOn
      simpa only [hF0new,hF1new] using h
    have hwhole : A ∪ B=modelCurve := by rw [←Set.image_union]; exact hFC
    have hfN0 : fN cornerNE=a.val.map 0 := by change f (F.symm cornerNE)=_; rw [←hF0,F.symm_apply_apply,hgA]
    have hfN1 : fN cornerSW=a.val.map 1 := by change f (F.symm cornerSW)=_; rw [←hF1,F.symm_apply_apply,hgA]
    have hImageA : a.image=fN '' A := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨F (gA t),Set.mem_image_of_mem F (Set.mem_range_self t),by change f (F.symm (F (gA t)))=_; rw [F.symm_apply_apply,hgA]⟩
      · rintro ⟨x,⟨y,⟨t,rfl⟩,rfl⟩,rfl⟩
        exact ⟨t,by change a.val.map t=f (F.symm (F (gA t))); rw [F.symm_apply_apply,hgA]⟩
    have hImageB : b.image=fN '' B := by
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨F (gB t),Set.mem_image_of_mem F (Set.mem_range_self t),by change f (F.symm (F (gB t)))=_; rw [F.symm_apply_apply,hgB]⟩
      · rintro ⟨x,⟨y,⟨t,rfl⟩,rfl⟩,rfl⟩
        exact ⟨t,by change b.val.map t=f (F.symm (F (gB t))); rw [F.symm_apply_apply,hgB]⟩
    have hboundary (z : Plane) (hz : z ∈ modelCurve) (hm : fN z ∈ M.cover.branch) : z=cornerNE ∨ z=cornerSW := by
      have hmodel : fN '' modelCurve=a.image ∪ b.image := by rw [←hwhole,Set.image_union,←hImageA,←hImageB]
      have hmem : fN z ∈ a.image ∪ b.image := hmodel ▸ Set.mem_image_of_mem fN hz
      have he : fN z ∈ ({a.val.map 0,a.val.map 1}:Set S) := by
        rcases hmem with ha | hb
        · exact a.image_inter_branch ▸ ⟨ha,hm⟩
        · rw [hends]; exact b.image_inter_branch ▸ ⟨hb,hm⟩
      rcases he with h0 | h1
      · exact Or.inl (hfN.injective (h0.trans hfN0.symm))
      · exact Or.inr (hfN.injective ((Set.mem_singleton_iff.mp h1).trans hfN1.symm))
    have hinside (z : Plane) (hz : z ∈ Plane.openSquare 0 1) : fN z ∉ M.cover.branch ∧ fN z ∉ P := by
      have hz' : z ∈ F '' (f ⁻¹' Ω) := hFI.symm ▸ hz
      obtain ⟨w,hw,he⟩ := hz'
      have hw' : w=F.symm z := by apply F.injective; rw [F.apply_symm_apply]; exact he
      have hΩ : fN z ∈ Ω := by change f (F.symm z) ∈ Ω; rw [←hw']; exact hw
      exact ⟨fun hm => Set.disjoint_left.mp hfree hΩ hm,fun hp => hp (hΩN hΩ)⟩
    obtain ⟨H,hmarks,hP,hmove⟩ := M.actual_endpoint_bigon_relative_alignment a.toEssential b.toEssential
      P isOpen_interior.isClosed_compl
      (Set.disjoint_left.mpr (fun x hx hp => hp (N.arc_inside hx.1)))
      (Set.disjoint_left.mpr (fun x hx hp => hp (hb hx.1)))
      fN hfN A B cornerNE cornerSW hArcA hArcB hwhole hImageA hImageB
      (hfN0.symm ▸ a.val.start_marked) (hfN1.symm ▸ a.val.end_marked) hboundary hinside
    exact ⟨H,hP,hmarks,hmove⟩

end CurveComplex.HyperellipticModel
