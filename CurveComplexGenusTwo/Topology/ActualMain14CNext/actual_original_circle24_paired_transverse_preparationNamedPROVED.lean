import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14MarkedCircleTransverseExtension
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14ActualMarkedCircleTransport
import CurveComplexGenusTwo.Topology.ActualMain14CNext.Providers.Main14TransverseImageEquality
import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchCharts
import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
import CurveComplexGenusTwo.Dictionary.ArcGeometry

open Lean Elab Tactic in
elab "audit_main14_original_circle24_prep_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in original Circle24 paired preparation: {ax}"
  logInfo m!"Original Circle24 paired preparation proof axiom audit: {found.toList}"
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
open scoped Manifold ContDiff
set_option maxHeartbeats 5000000
theorem actual_original_circle24_paired_transverse_preparation (M : HyperellipticModel E S) (c d : Circle24 M)
    (hiso : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image) (M.cover.projection ⁻¹' d.val.image)) :
    ∃ d' : Circle24 M, MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse c.val.curve d'.val.curve ∧
      ∃ a0 a1 b0 b1 : EssentialCurve E, ∃ H : AmbientIsotopy E,
        a0.val.image ∪ a1.val.image=M.cover.projection ⁻¹' c.val.image ∧
        b0.val.image ∪ b1.val.image=M.cover.projection ⁻¹' d'.val.image ∧
        Disjoint a0.val.image a1.val.image ∧ Disjoint b0.val.image b1.val.image ∧
        M.cover.deck '' a0.val.image=a1.val.image ∧ M.cover.deck '' b0.val.image=b1.val.image ∧
        H.finalMap '' a0.val.image=b0.val.image ∧ H.finalMap '' a1.val.image=b1.val.image ∧
        Set.BijOn M.cover.projection a0.val.image c.val.image ∧
        Set.BijOn M.cover.projection a1.val.image c.val.image ∧
        Set.BijOn M.cover.projection b0.val.image d'.val.image ∧
        Set.BijOn M.cover.projection b1.val.image d'.val.image ∧
        IsConnected a0.val.imageᶜ ∧ IsConnected a1.val.imageᶜ ∧
        IsConnected b0.val.imageᶜ ∧ IsConnected b1.val.imageᶜ ∧
        Transverse a0.val b0.val ∧ Transverse a0.val b1.val ∧
        Transverse a1.val b0.val ∧ Transverse a1.val b1.val := by
  audit_main14_original_circle24_prep_base3
    classical
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have hPair (M : HyperellipticModel E S) (c d : Circle24 M)
        (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
          (M.cover.projection ⁻¹' d.val.image)) :
        ∃ a0 a1 b0 b1 : Curve E, ∃ H : AmbientIsotopy E,
          a0.image ∪ a1.image = M.cover.projection ⁻¹' c.val.image ∧
          b0.image ∪ b1.image = M.cover.projection ⁻¹' d.val.image ∧
          Disjoint a0.image a1.image ∧ Disjoint b0.image b1.image ∧
          M.cover.deck '' a0.image = a1.image ∧ M.cover.deck '' b0.image = b1.image ∧
          H.finalMap '' a0.image = b0.image ∧ H.finalMap '' a1.image = b1.image ∧
          Set.BijOn M.cover.projection a0.image c.val.image ∧
          Set.BijOn M.cover.projection a1.image c.val.image ∧
          Set.BijOn M.cover.projection b0.image d.val.image ∧
          Set.BijOn M.cover.projection b1.image d.val.image := by
      classical
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      obtain ⟨a0,a1,ha,had,hadeck,hap0,hap1,hac0,hac1⟩ := M.actual_circle24_components_project_bijectively c
      obtain ⟨b0,b1,hb,hbd,hbdeck,hbp0,hbp1,hbc0,hbc1⟩ := M.actual_circle24_components_project_bijectively d
      let z0 : Circle := Classical.choice inferInstance
      obtain ⟨H,hH⟩ := hup
      obtain ⟨e,he⟩ := H.homeomorphism_at 1
      have hef : H.finalMap = e := funext (fun x => (he x).symm)
      have hunion : e '' (a0.image ∪ a1.image) = b0.image ∪ b1.image := by
        rw [ha,hb,← hef]; exact hH
      have hpair (a0 a1 b0 b1 : Curve E)
          (had : Disjoint a0.image a1.image) (hbd : Disjoint b0.image b1.image)
          (hunion : e '' (a0.image ∪ a1.image) = b0.image ∪ b1.image)
          (hfirst : e '' a0.image = b0.image) : e '' a1.image = b1.image := by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          have hx : e y ∈ b0.image ∪ b1.image := hunion ▸ ⟨y,Or.inr hy,rfl⟩
          rcases hx with hx | hx
          · obtain ⟨z,hz,hzy⟩ := hfirst.symm ▸ hx
            exact False.elim (Set.disjoint_left.mp had hz ((e.injective hzy).symm ▸ hy))
          · exact hx
        · intro hx
          have hxpre : x ∈ e '' (a0.image ∪ a1.image) := by
            rw [hunion]; exact Or.inr hx
          obtain ⟨y,hy,hyx⟩ := hxpre
          rcases hy with hy | hy
          · have hxb : x ∈ b0.image := hfirst ▸ ⟨y,hy,hyx⟩
            exact False.elim (Set.disjoint_left.mp hbd hxb hx)
          · exact ⟨y,hy,hyx⟩
      have hImageComp (b0 b1 : Curve E) (hbd : Disjoint b0.image b1.image)
          (hunion : e '' (a0.image ∪ a1.image) = b0.image ∪ b1.image)
          (hx : e (a0.map z0) ∈ b0.image) : e '' a0.image = b0.image := by
        have hsource : a0.map z0 ∈ a0.image := Set.mem_range_self _
        have hs := disjoint_curve_connectedComponentIn a0 a1 had (a0.map z0) hsource
        have ht := disjoint_curve_connectedComponentIn b0 b1 hbd (e (a0.map z0)) hx
        have hh := e.image_connectedComponentIn (s := a0.image ∪ a1.image)
          (x := a0.map z0) (by exact Or.inl hsource)
        rw [hs,hunion,ht] at hh
        exact hh
      have hx : e (a0.map z0) ∈ b0.image ∪ b1.image :=
        hunion ▸ ⟨a0.map z0,Or.inl (Set.mem_range_self _),rfl⟩
      rcases hx with hx | hx
      · have h0 := hImageComp b0 b1 hbd hunion hx
        have h1 := hpair a0 a1 b0 b1 had hbd hunion h0
        exact ⟨a0,a1,b0,b1,H,ha,hb,had,hbd,hadeck,hbdeck,by rw [hef];exact h0,by rw [hef];exact h1,hap0,hap1,hbp0,hbp1⟩
      · have hunion' : e '' (a0.image ∪ a1.image) = b1.image ∪ b0.image :=
          hunion.trans (Set.union_comm _ _)
        have h0 := hImageComp b1 b0 hbd.symm hunion' hx
        have h1 := hpair a0 a1 b1 b0 had hbd.symm hunion' h0
        have hbdeck' : M.cover.deck '' b1.image = b0.image := by
          rw [← hbdeck,Set.image_image]
          have hi : (fun x : E => M.cover.deck (M.cover.deck x)) = id := funext M.cover.deck_involution
          rw [hi,Set.image_id]
        exact ⟨a0,a1,b1,b0,H,ha,(Set.union_comm _ _).trans hb,had,hbd.symm,hadeck,hbdeck',
          by rw [hef];exact h0,by rw [hef];exact h1,hap0,hap1,hbp1,hbp0⟩
    have hEss (M : HyperellipticModel E S) (c : Circle24 M) (a0 a1 : Curve E)
        (ha : a0.image ∪ a1.image = M.cover.projection ⁻¹' c.val.image)
        (had : Disjoint a0.image a1.image) :
        Essential a0 ∧ Essential a1 ∧ IsConnected a0.imageᶜ ∧ IsConnected a1.imageᶜ := by
      have hSides (M : HyperellipticModel E S) (a : Circle24 M) :
          ∃ U V : Set S, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = a.val.imageᶜ ∧
            closure U = U ∪ a.val.image ∧ closure V = V ∪ a.val.image ∧
            IsConnected (M.cover.projection ⁻¹' U) ∧ IsConnected (M.cover.projection ⁻¹' V) := by
        have hConnected (M : HyperellipticModel E S) (D : Set S) (hD : IsConnected D)
            (b : S) (hb : b ∈ M.cover.branch) (hbD : b ∈ D) :
            IsConnected (M.cover.projection ⁻¹' D) := by
          classical
          letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
          letI : T2Space S := M.sphere.symm.t2Space
          have hopen : IsOpenMap M.cover.projection := by
              letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
              letI : T2Space S := M.sphere.symm.t2Space
              have hcl : IsClosedMap M.cover.projection := M.cover.projection_continuous.isClosedMap
              have hq := hcl.isQuotientMap M.cover.projection_continuous M.cover.projection_surjective
              intro U hU
              rw [← hq.isCoinducing.isOpen_preimage]
              have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
                  U ∪ M.cover.deck ⁻¹' U := by
                ext x
                constructor
                · rintro ⟨y, hy, hxy⟩
                  rcases (M.cover.fiber_pair x y).mp hxy.symm with h | h
                  · exact Or.inl (h ▸ hy)
                  · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [h] using hy)
                · rintro (hx | hx)
                  · exact ⟨x, hx, rfl⟩
                  · exact ⟨M.cover.deck x, hx, M.cover.projection_deck x⟩
              rw [heq]
              exact hU.union (hU.preimage M.cover.deck.continuous)
          have hclosed : IsClosedMap M.cover.projection :=
            M.cover.projection_continuous.isClosedMap
          let f := D.restrictPreimage M.cover.projection
          have hfopen : IsOpenMap f := hopen.restrictPreimage D
          have hfclosed : IsClosedMap f := hclosed.restrictPreimage D
          letI : ConnectedSpace D := isConnected_iff_connectedSpace.mp hD
          obtain ⟨w, hw, huniq⟩ := M.cover.branch_fiber_unique hb
          have hwD : w ∈ M.cover.projection ⁻¹' D := by change M.cover.projection w ∈ D; rw [hw]; exact hbD
          letI : Nonempty (M.cover.projection ⁻¹' D) := ⟨⟨w, hwD⟩⟩
          apply isConnected_iff_connectedSpace.mpr
          apply connectedSpace_iff_univ.mpr
          refine ⟨Set.univ_nonempty, ?_⟩
          by_contra h
          obtain ⟨U, V, hU, hV, hnU, hnV, hd, huv⟩ :=
            isClopen_univ.not_isPreconnected_iff.mp h
          have hUi : f '' U = Set.univ :=
            IsClopen.eq_univ ⟨hfclosed U hU.isClosed, hfopen U hU.isOpen⟩ (hnU.image f)
          have hVi : f '' V = Set.univ :=
            IsClopen.eq_univ ⟨hfclosed V hV.isClosed, hfopen V hV.isOpen⟩ (hnV.image f)
          obtain ⟨u, hu, hueq⟩ := (hUi.symm ▸ Set.mem_univ (⟨b, hbD⟩ : D))
          obtain ⟨v, hv, hveq⟩ := (hVi.symm ▸ Set.mem_univ (⟨b, hbD⟩ : D))
          have huval : (u : E) = w := huniq u.val (congrArg Subtype.val hueq)
          have hvval : (v : E) = w := huniq v.val (congrArg Subtype.val hveq)
          have huv' : u = v := Subtype.ext (huval.trans hvval.symm)
          exact Set.disjoint_left.mp hd hu (huv' ▸ hv)
        classical
        have hsplit : SplitsMarked M a.val 2 4 := by
          rcases a.property with h | h
          · exact h
          · obtain ⟨U,V,hU,hV,hUc,hVc,hUn,hVn,hd,hu,h4,h2⟩ := h
            exact ⟨V,U,hV,hU,hVc,hUc,hVn,hUn,hd.symm,
              (Set.union_comm V U).trans hu,h2,h4⟩
        obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
          M.puncturedCircle_closedSides a.val
        obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWn,hZn,hWZ,hWZcover,hWcount,hZcount⟩ := hsplit
        have hWsub : W ⊆ U ∪ V := by
          rw [hcover,← hWZcover]
          exact subset_union_left
        have hUsub : U ⊆ W ∪ Z := by
          rw [hWZcover,← hcover]
          exact subset_union_left
        have hVsub : V ⊆ W ∪ Z := by
          rw [hWZcover,← hcover]
          exact subset_union_right
        have hEq : W = U ∨ W = V := by
          rcases hWc.isPreconnected.subset_or_subset hUo hVo hUV hWsub with hWU | hWV
          · left
            apply Set.Subset.antisymm hWU
            rcases hUc.isPreconnected.subset_or_subset hWo hZo hWZ hUsub with hUW | hUZ
            · exact hUW
            · obtain ⟨x,hx⟩ := hWn
              exact False.elim (Set.disjoint_left.mp hWZ hx (hUZ (hWU hx)))
          · right
            apply Set.Subset.antisymm hWV
            rcases hVc.isPreconnected.subset_or_subset hWo hZo hWZ hVsub with hVW | hVZ
            · exact hVW
            · obtain ⟨x,hx⟩ := hWn
              exact False.elim (Set.disjoint_left.mp hWZ hx (hVZ (hWV hx)))
        have hOther (U V W Z : Set S) (hd : Disjoint U V) (he : Disjoint W Z)
            (hc : U ∪ V=W ∪ Z) (hWU : W=U) : Z=V := by
          subst W
          apply Set.Subset.antisymm
          · intro x hx
            rcases hc.symm ▸ (show x ∈ U ∪ Z from Or.inr hx) with hu | hv
            · exact False.elim (Set.disjoint_left.mp he hu hx)
            · exact hv
          · intro x hx
            rcases hc ▸ (show x ∈ U ∪ V from Or.inr hx) with hu | hz
            · exact False.elim (Set.disjoint_left.mp hd hu hx)
            · exact hz
        have hcounts :
            (M.cover.branch.filter (· ∈ U)).Nonempty ∧ (M.cover.branch.filter (· ∈ V)).Nonempty := by
          rcases hEq with hEq | hEq
          · have hZ := hOther U V W Z hUV hWZ (hcover.trans hWZcover.symm) hEq
            rw [hEq] at hWcount
            rw [hZ] at hZcount
            constructor <;> apply Finset.card_pos.mp
            · rw [hWcount]; norm_num
            · rw [hZcount]; norm_num
          · have hZ := hOther V U W Z hUV.symm hWZ
              ((Set.union_comm V U).trans (hcover.trans hWZcover.symm)) hEq
            rw [hEq] at hWcount
            rw [hZ] at hZcount
            constructor <;> apply Finset.card_pos.mp
            · rw [hZcount]; norm_num
            · rw [hWcount]; norm_num
        obtain ⟨u,hu⟩ := hcounts.1
        obtain ⟨v,hv⟩ := hcounts.2
        exact ⟨U,V,hUo,hVo,hUV,hcover,hclU,hclV,
          hConnected M U hUc u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2,
          hConnected M V hVc v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2⟩
      classical
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      letI : T2Space S := M.sphere.symm.t2Space
      obtain ⟨U,V,hU,hV,hdis,hcover,hclU,hclV,hconnU,hconnV⟩ := hSides M c
      have hopen : IsOpenMap M.cover.projection := by
          letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
          letI : T2Space S := M.sphere.symm.t2Space
          have hcl : IsClosedMap M.cover.projection := M.cover.projection_continuous.isClosedMap
          have hq := hcl.isQuotientMap M.cover.projection_continuous M.cover.projection_surjective
          intro U hU
          rw [← hq.isCoinducing.isOpen_preimage]
          have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
              U ∪ M.cover.deck ⁻¹' U := by
            ext x
            constructor
            · rintro ⟨y, hy, hxy⟩
              rcases (M.cover.fiber_pair x y).mp hxy.symm with h | h
              · exact Or.inl (h ▸ hy)
              · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [h] using hy)
            · rintro (hx | hx)
              · exact ⟨x, hx, rfl⟩
              · exact ⟨M.cover.deck x, hx, M.cover.projection_deck x⟩
          rw [heq]
          exact hU.union (hU.preimage M.cover.deck.continuous)
      let A : Set E := M.cover.projection ⁻¹' U
      let B : Set E := M.cover.projection ⁻¹' V
      have hAc : closure A = A ∪ M.cover.projection ⁻¹' c.val.image := by
        change closure (M.cover.projection ⁻¹' U)=_
        rw [←hopen.preimage_closure_eq_closure_preimage M.cover.projection_continuous U,hclU,Set.preimage_union]
      have hBc : closure B = B ∪ M.cover.projection ⁻¹' c.val.image := by
        change closure (M.cover.projection ⁻¹' V)=_
        rw [←hopen.preimage_closure_eq_closure_preimage M.cover.projection_continuous V,hclV,Set.preimage_union]
      have hcomp (a0 a1 : Curve E) (ha : a0.image ∪ a1.image=M.cover.projection ⁻¹' c.val.image)
          (had : Disjoint a0.image a1.image) : IsConnected a0.imageᶜ := by
        have hpre0 (x : E) (hx : x ∈ a0.image) : M.cover.projection x ∈ c.val.image := by
          have hh : x ∈ a0.image ∪ a1.image := Or.inl hx
          rw [ha] at hh
          exact hh
        have hpre1 (x : E) (hx : x ∈ a1.image) : x ∈ M.cover.projection ⁻¹' c.val.image := by
          have hh : x ∈ a0.image ∪ a1.image := Or.inr hx
          rw [ha] at hh
          exact hh
        have hAU : IsConnected (A ∪ a1.image) := hconnU.subset_closure Set.subset_union_left (by
          rintro x (hx | hx)
          · exact subset_closure hx
          · rw [hAc]; exact Or.inr (hpre1 x hx))
        have hBU : IsConnected (B ∪ a1.image) := hconnV.subset_closure Set.subset_union_left (by
          rintro x (hx | hx)
          · exact subset_closure hx
          · rw [hBc]; exact Or.inr (hpre1 x hx))
        let z : Circle := Classical.choice inferInstance
        have hmeet : ((A ∪ a1.image) ∩ (B ∪ a1.image)).Nonempty :=
          ⟨a1.map z,Or.inr (Set.mem_range_self z),Or.inr (Set.mem_range_self z)⟩
        have hc := hAU.union hmeet hBU
        have heq : (A ∪ a1.image) ∪ (B ∪ a1.image)=a0.imageᶜ := by
          ext x
          constructor
          · rintro ((hA | h1) | (hB | h1)) h0
            · have hh : M.cover.projection x ∈ U ∪ V := Or.inl hA
              rw [hcover] at hh
              exact hh (hpre0 x h0)
            · exact Set.disjoint_left.mp had h0 h1
            · have hh : M.cover.projection x ∈ U ∪ V := Or.inr hB
              rw [hcover] at hh
              exact hh (hpre0 x h0)
            · exact Set.disjoint_left.mp had h0 h1
          · intro hx
            by_cases hxc : M.cover.projection x ∈ c.val.image
            · have hh : x ∈ a0.image ∪ a1.image := by rw [ha]; exact hxc
              rcases hh with h0 | h1
              · exact False.elim (hx h0)
              · exact Or.inl (Or.inr h1)
            · have hh : M.cover.projection x ∈ U ∪ V := by rw [hcover]; exact hxc
              rcases hh with hU | hV
              · exact Or.inl (Or.inl hU)
              · exact Or.inr (Or.inl hV)
        rw [←heq]
        exact hc
      have hEssential (c : Curve E) (hconn : IsConnected c.imageᶜ) : Essential c := by
        classical
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        intro hc
        obtain ⟨f, hf, hboundary⟩ := hc
        let P := EuclideanSpace ℝ (Fin 2)
        let B := Metric.closedBall (0 : P) 1
        let O := Metric.ball (0 : P) 1
        let A : Set B := {x | (x : P) ∈ O}
        let C : Set B := {x | (x : P) ∈ Metric.sphere (0 : P) 1}
        have hfnot : ¬ Function.Surjective f := by
          intro hsurj
          let h : B ≃ₜ E := IsHomeomorph.homeomorph f
            (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hf, hsurj⟩)
          obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty (E := P).mpr
            (show (0 : ℝ) ≤ 1 by norm_num)
          let pB : B := ⟨p, Metric.sphere_subset_closedBall hp⟩
          let e := chartAt P (h pB)
          let g : e.target → P := fun y => (h.symm (e.symm y) : P)
          have hgcont : Continuous g := continuous_subtype_val.comp
            (h.symm.continuous.comp
              (e.symm.continuousOn.comp_continuous continuous_subtype_val
                (fun y => y.property)))
          have hginj : Function.Injective g := by
            intro y z hyz
            have hhs : h.symm (e.symm y) = h.symm (e.symm z) := Subtype.ext hyz
            exact Subtype.ext (e.symm.injOn y.property z.property (h.symm.injective hhs))
          have hopen : IsOpen (Set.range g) :=
            isOpen_range_of_isOpen_of_continuous_injective
              (modelWithCornersSelf ℝ P) e.open_target g hgcont hginj
          have hpim : p ∈ Set.range g := by
            refine ⟨⟨e (h pB), e.map_source (mem_chart_source P (h pB))⟩, ?_⟩
            dsimp [g]
            rw [e.left_inv (mem_chart_source P (h pB)), h.symm_apply_apply]
          have hsub : Set.range g ⊆ B := by
            rintro _ ⟨y, rfl⟩
            exact (h.symm (e.symm y)).property
          have hpint : p ∈ interior B := (hopen.subset_interior_iff.mpr hsub) hpim
          rw [interior_closedBall (0 : P) (by norm_num : (1 : ℝ) ≠ 0)] at hpint
          exact (ne_of_lt hpint) hp
        simp only [Function.Surjective, not_forall, not_exists] at hfnot
        obtain ⟨x, hx⟩ := hfnot
        have hnV : (Set.range f)ᶜ.Nonempty := ⟨x, by rintro ⟨y, hy⟩; exact hx y hy⟩
        have hopenV : IsOpen (Set.range f)ᶜ :=
          (isCompact_range f.continuous).isClosed.isOpen_compl
        let g : O → E := fun x => f ⟨x, Metric.ball_subset_closedBall x.property⟩
        have hgcont : Continuous g := f.continuous.comp
          (continuous_subtype_val.subtype_mk _)
        have hginj : Function.Injective g := by
          intro x y hxy
          have heq : (⟨x, Metric.ball_subset_closedBall x.property⟩ : B) =
              ⟨y, Metric.ball_subset_closedBall y.property⟩ := hf.injective hxy
          exact Subtype.ext (congrArg (fun z : B => (z : P)) heq)
        have hgim : Set.range g = f '' A := by
          ext y
          constructor
          · rintro ⟨x, rfl⟩
            exact ⟨⟨x, Metric.ball_subset_closedBall x.property⟩, x.property, rfl⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨⟨x, hx⟩, rfl⟩
        have hopenU : IsOpen (f '' A) := by
          rw [← hgim]
          exact isOpen_range_of_isOpen_of_continuous_injective
            (modelWithCornersSelf ℝ P) Metric.isOpen_ball g hgcont hginj
        have hnU : (f '' A).Nonempty := by
          refine ⟨f ⟨0, by simp⟩, ⟨0, by simp⟩, ?_, rfl⟩
          change dist (0 : P) 0 < 1
          simp
        have hdisj : Disjoint (f '' A) (Set.range f)ᶜ := by
          apply Set.disjoint_left.mpr
          rintro _ ⟨y, hy, rfl⟩ hx
          exact hx ⟨y, rfl⟩
        have hUc : f '' A ⊆ c.imageᶜ := by
          rintro _ ⟨y, hy, rfl⟩ hcy
          rw [← hboundary] at hcy
          obtain ⟨z, hz, hfz⟩ := hcy
          have hzy : z = y := hf.injective hfz
          subst z
          exact (ne_of_lt hy) hz
        have hVc : (Set.range f)ᶜ ⊆ c.imageᶜ := by
          intro y hy hcy
          rw [← hboundary] at hcy
          obtain ⟨z, hz, hfz⟩ := hcy
          exact hy ⟨z, hfz⟩
        have hcover : c.imageᶜ ⊆ f '' A ∪ (Set.range f)ᶜ := by
          intro y hy
          by_cases hr : y ∈ Set.range f
          · obtain ⟨z, rfl⟩ := hr
            left
            refine ⟨z, ?_, rfl⟩
            have hne : (z : P) ∉ Metric.sphere (0 : P) 1 := by
              intro hz
              exact hy (hboundary ▸ Set.mem_image_of_mem f hz)
            have hzle := z.property
            change dist (z : P) 0 ≤ 1 at hzle
            change dist (z : P) 0 < 1
            exact lt_of_le_of_ne hzle hne
          · exact Or.inr hr
        rcases hconn.isPreconnected.subset_or_subset hopenU hopenV hdisj hcover with h | h
        · obtain ⟨x, hx⟩ := hnV
          exact Set.disjoint_left.mp hdisj (h (hVc hx)) hx
        · obtain ⟨x, hx⟩ := hnU
          exact Set.disjoint_left.mp hdisj hx (h (hUc hx))
      have h0 := hcomp a0 a1 ha had
      have h1 := hcomp a1 a0 ((Set.union_comm _ _).trans ha) had.symm
      exact ⟨hEssential a0 h0,hEssential a1 h1,h0,h1⟩
    have hTrans (q : BranchedDoubleCover E S) (a0 a1 b0 b1 : Curve E) (c d : Curve S)
        (ha : a0.image ∪ a1.image=q.projection ⁻¹' c.image)
        (hb : b0.image ∪ b1.image=q.projection ⁻¹' d.image)
        (hAd : Disjoint a0.image a1.image) (hBd : Disjoint b0.image b1.image)
        (hfree : Disjoint c.image (q.branch : Set S)) (ht : Transverse c d) :
        Transverse a0 b0 := by
      classical
      have hpa (x : E) (hx : x ∈ a0.image) : q.projection x ∈ c.image := by
        have hh : x ∈ a0.image ∪ a1.image := Or.inl hx
        rw [ha] at hh
        exact hh
      have hpb (x : E) (hx : x ∈ b0.image) : q.projection x ∈ d.image := by
        have hh : x ∈ b0.image ∪ b1.image := Or.inl hx
        rw [hb] at hh
        exact hh
      let lift : S → E := fun y => Classical.choose (q.projection_surjective y)
      have hlift (y : S) : q.projection (lift y) = y := Classical.choose_spec (q.projection_surjective y)
      have hsubset : a0.image ∩ b0.image ⊆
          lift '' (c.image ∩ d.image) ∪ q.deck '' (lift '' (c.image ∩ d.image)) := by
        intro x hx
        have hy : q.projection x ∈ c.image ∩ d.image := by
          exact ⟨hpa x hx.1,hpb x hx.2⟩
        have hp : q.projection (lift (q.projection x)) = q.projection x := hlift _
        rcases (q.fiber_pair _ _).mp hp with hh | hh
        · exact Or.inl ⟨q.projection x,hy,hh.symm⟩
        · exact Or.inr ⟨lift (q.projection x),⟨q.projection x,hy,rfl⟩,hh.symm⟩
      refine ⟨((ht.1.image lift).union ((ht.1.image lift).image q.deck)).subset hsubset,?_⟩
      intro x hx
      have hy : q.projection x ∈ c.image ∩ d.image := by
        exact ⟨hpa x hx.1,hpb x hx.2⟩
      have hregular : q.projection x ∈ (q.branch : Set S)ᶜ :=
        fun h => Set.disjoint_left.mp hfree hy.1 h
      obtain ⟨G,hxG,hG⟩ := q.unbranched_cover.isLocalHomeomorphOn x hregular
      obtain ⟨F,hyF,hFU,hF0,hFc,hFd⟩ :=
        source_crossing_open_partial_chart (ht.2 _ hy) Set.univ isOpen_univ (Set.mem_univ _)
      let W : Set E := (a1.image ∪ b1.image)ᶜ
      have hW : IsOpen W :=
        ((isCompact_range a1.embedded.continuous).isClosed.union
          (isCompact_range b1.embedded.continuous).isClosed).isOpen_compl
      have hxW : x ∈ W := by
        rintro (hxA | hxB)
        · exact Set.disjoint_left.mp hAd hx.1 hxA
        · exact Set.disjoint_left.mp hBd hx.2 hxB
      let G' := G.restrOpen W hW
      let H := G'.trans F
      have hGx : G x = q.projection x := (congrFun hG x).symm
      have hxH : x ∈ H.source := by
        change x ∈ (G.source ∩ W) ∩ G ⁻¹' F.source
        refine ⟨⟨hxG,hxW⟩,?_⟩
        change G x ∈ F.source
        rw [hGx]
        exact hyF
      have hH0 : H x = (0,0) := by
        change F (G x) = (0,0)
        rw [hGx,hF0]
      refine ⟨H.source,H.target,hxH,H.toHomeomorphSourceTarget,H.open_source,H.open_target,hH0,?_⟩
      intro z hz
      have hzF : G z ∈ F.source := hz.2
      have hca : z ∈ a0.image ↔ G z ∈ c.image := by
        rw [←congrFun hG z]
        constructor
        · exact hpa z
        · intro hzC
          have hh : z ∈ a0.image ∪ a1.image := by rw [ha]; exact hzC
          rcases hh with hh | hh
          · exact hh
          · exact False.elim (hz.1.2 (Or.inl hh))
      have hdb : z ∈ b0.image ↔ G z ∈ d.image := by
        rw [←congrFun hG z]
        constructor
        · exact hpb z
        · intro hzD
          have hh : z ∈ b0.image ∪ b1.image := by rw [hb]; exact hzD
          rcases hh with hh | hh
          · exact hh
          · exact False.elim (hz.1.2 (Or.inr hh))
      exact ⟨hca.trans (hFc _ hzF),hdb.trans (hFd _ hzF)⟩
    have hTransport
        (M : HyperellipticModel E S) (c : Circle24 M) (L : AmbientIsotopy S)
        (hfix : ∀ t x, x ∈ M.cover.branch → L.map (t,x) = x) :
        ∃ c' : Circle24 M, c'.val.image = L.finalMap '' c.val.image ∧
          MarkedIsotopyRel M c.val.image c'.val.image := by
      classical
      obtain ⟨e,he⟩ := L.homeomorphism_at ⟨1,by norm_num⟩
      have hefinal : (e : S → S) = L.finalMap := funext he
      obtain ⟨c',hi,hs⟩ := M.actual_marked_homeomorph_circle_transport c.val e
        (fun x hx => (he x).trans (hfix _ x hx))
      have hc : SplitsMarked M c' 2 4 ∨ SplitsMarked M c' 4 2 :=
        c.property.elim (fun h => Or.inl (hs 2 4 h)) (fun h => Or.inr (hs 4 2 h))
      refine ⟨⟨c',hc⟩,?_,L,hfix,?_⟩
      · simpa only [hefinal] using hi
      · simpa only [hefinal] using hi.symm
    classical
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    classical
    let A := M.actualSphereSmoothAtlas
    letI : ChartedSpace Plane S := A.charts
    letI : IsManifold (𝓡 2) ∞ S := A.manifold
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      isConnected_iff_connectedSpace.mp (isConnected_sphere (by
        rw [← Module.finrank_eq_rank]
        simp) (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num))
    letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
    letI : ClosedSurface S := {}
    obtain ⟨HD,d₀,himage,hfix,ht⟩ := M.actual_marked_two_circle_transverse_extension c.val d.val
    obtain ⟨d',hd',hdiso⟩ := hTransport M d HD hfix
    have hdi : d'.val.curve.image = d₀.image := hd'.trans himage.symm
    have htbase := transverse_of_curve_images_eq c.val.curve d'.val.curve c.val.curve d₀ rfl hdi ht
    have hiso' : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image) (M.cover.projection ⁻¹' d'.val.image) :=
      ambientIsotopy_equivalence.trans hiso (M.marked_isotopy_preimage hdiso)
    obtain ⟨a0,a1,b0,b1,H,ha,hb,hAd,hBd,hDeckA,hDeckB,hH0,hH1,hap0,hap1,hbp0,hbp1⟩ := hPair M c d' hiso'
    obtain ⟨hAe0,hAe1,hAc0,hAc1⟩ := hEss M c a0 a1 ha hAd
    obtain ⟨hBe0,hBe1,hBc0,hBc1⟩ := hEss M d' b0 b1 hb hBd
    let A0 : EssentialCurve E := ⟨a0,hAe0⟩
    let A1 : EssentialCurve E := ⟨a1,hAe1⟩
    let B0 : EssentialCurve E := ⟨b0,hBe0⟩
    let B1 : EssentialCurve E := ⟨b1,hBe1⟩
    refine ⟨d',hdiso,htbase,A0,A1,B0,B1,H,ha,hb,hAd,hBd,hDeckA,hDeckB,hH0,hH1,hap0,hap1,hbp0,hbp1,
      hAc0,hAc1,hBc0,hBc1,?_,?_,?_,?_⟩
    · exact hTrans M.cover a0 a1 b0 b1 c.val.curve d'.val.curve ha hb hAd hBd c.val.avoids_branch htbase
    · exact hTrans M.cover a0 a1 b1 b0 c.val.curve d'.val.curve ha ((Set.union_comm _ _).trans hb) hAd hBd.symm c.val.avoids_branch htbase
    · exact hTrans M.cover a1 a0 b0 b1 c.val.curve d'.val.curve ((Set.union_comm _ _).trans ha) hb hAd.symm hBd c.val.avoids_branch htbase
    · exact hTrans M.cover a1 a0 b1 b0 c.val.curve d'.val.curve ((Set.union_comm _ _).trans ha) ((Set.union_comm _ _).trans hb) hAd.symm hBd.symm c.val.avoids_branch htbase

end CurveComplex.HyperellipticModel
