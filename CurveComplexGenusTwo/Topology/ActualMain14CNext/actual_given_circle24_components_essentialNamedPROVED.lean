import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
import CurveComplexGenusTwo.Dictionary.ArcGeometry

open Lean Elab Tactic in
elab "audit_main14_actual_given_essential_components_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in actual actual given Circle24 essential components: {ax}"
  logInfo m!"Actual actual given Circle24 essential components proof axiom audit: {found.toList}"
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 1000000
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
theorem actual_given_circle24_components_essential (M : HyperellipticModel E S) (c : Circle24 M) (a0 a1 : Curve E)
    (ha : a0.image ∪ a1.image = M.cover.projection ⁻¹' c.val.image)
    (had : Disjoint a0.image a1.image) :
    Essential a0 ∧ Essential a1 ∧ IsConnected a0.imageᶜ ∧ IsConnected a1.imageᶜ := by
  audit_main14_actual_given_essential_components_base3
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

end CurveComplex.HyperellipticModel
