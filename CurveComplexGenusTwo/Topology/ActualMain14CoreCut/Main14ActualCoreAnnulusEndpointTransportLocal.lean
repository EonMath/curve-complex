import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualCoreAnnulusMinimalImportsPROVED

open Lean Elab Tactic in
elab "audit_main14_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in Main14 local source proof: {ax}"
  logInfo m!"Main14 local proof axiom audit: {found.toList}"

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]

-- Local proof under the approved source caller; no new named public head.
example (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (N : ArcNeighborhood a)
    (pair : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ N.closedSet)
    (hcore : (fun z => (pair z : S)) '' ClassificationSchoenflies.standardArcCore = a.image)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' a.image)
      (M.cover.projection ⁻¹' b.image)) :
    ∃ h : E ≃ₜ E, ∃ H : Circle × Interval ≃ₜ h '' (M.cover.projection ⁻¹' N.closedSet),
      Set.range (fun z : Circle => (H (z,⟨1/2,by norm_num⟩)).val) =
        M.cover.projection ⁻¹' b.image ∧
      Set.range (fun z : Circle => (H (z,0)).val) ∪
        Set.range (fun z : Circle => (H (z,1)).val) =
        h '' (M.cover.projection ⁻¹' N.boundary.image) ∧
      AmbientIsotopy.Rel (M.cover.projection ⁻¹' N.boundary.image)
        (h '' (M.cover.projection ⁻¹' N.boundary.image)) := by
  audit_main14_base3
    obtain ⟨K,hK⟩ := hup
    obtain ⟨h,hh⟩ := K.homeomorphism_at 1
    have hf : (h : E → E) = K.finalMap := by
      funext x
      exact hh x
    obtain ⟨A,hAc,hAb⟩ :=
      M.actual_nonloop_regular_neighborhood_lift_core_annulus a N pair hcore
    let H := A.trans (h.image (M.cover.projection ⁻¹' N.closedSet))
    have he (t : Interval) : Set.range (fun z : Circle => (H (z,t)).val) =
        h '' Set.range (fun z : Circle => (A (z,t)).val) := by
      change Set.range (fun z : Circle => h (A (z,t)).val) = _
      exact Set.range_comp h (fun z : Circle => (A (z,t)).val)
    refine ⟨h,H,?_,?_,?_⟩
    · rw [he,hAc,hf]
      exact hK
    · rw [he,he,← Set.image_union,hAb]
    · exact ⟨K,by rw [← hf]⟩

-- Exact parametrization alignment of two actual annuli with the same full core.
example (U V C : Set E) (A : Circle × Interval ≃ₜ U)
    (B : Circle × Interval ≃ₜ V)
    (hA : Set.range (fun z : Circle => (A (z,⟨1/2,by norm_num⟩)).val) = C)
    (hB : Set.range (fun z : Circle => (B (z,⟨1/2,by norm_num⟩)).val) = C) :
    ∃ r : Circle ≃ₜ Circle, ∀ z : Circle,
      (B (r z,⟨1/2,by norm_num⟩)).val =
        (A (z,⟨1/2,by norm_num⟩)).val := by
  audit_main14_base3
    let c : Interval := ⟨1/2,by norm_num⟩
    have hAe : Topology.IsEmbedding (fun z : Circle => (A (z,c)).val) :=
      Topology.IsEmbedding.subtypeVal.comp
        (A.isEmbedding.comp (isEmbedding_prodMkLeft c))
    have hBe : Topology.IsEmbedding (fun z : Circle => (B (z,c)).val) :=
      Topology.IsEmbedding.subtypeVal.comp
        (B.isEmbedding.comp (isEmbedding_prodMkLeft c))
    let ea : Circle ≃ₜ C := hAe.toHomeomorph.trans (Homeomorph.setCongr hA)
    let eb : Circle ≃ₜ C := hBe.toHomeomorph.trans (Homeomorph.setCongr hB)
    refine ⟨ea.trans eb.symm,?_⟩
    intro z
    have hh := congrArg Subtype.val (eb.apply_symm_apply (ea z))
    exact hh

-- Actual uniform core band inside the second ORIGINAL neighborhood.
example (M : HyperellipticModel E S) (b : NonLoopArc M)
    (Nb : ArcNeighborhood b) (U : Set E)
    (T : Circle × Interval ≃ₜ U)
    (hTc : Set.range (fun z : Circle => (T (z,⟨1/2,by norm_num⟩)).val) =
      M.cover.projection ⁻¹' b.image) :
    ∃ V : Set Interval, IsOpen V ∧ (⟨1/2,by norm_num⟩ : Interval) ∈ V ∧
      ∀ z : Circle, ∀ t ∈ V,
        M.cover.projection (T (z,t)).val ∈ interior Nb.closedSet := by
  audit_main14_base3
    let c : Interval := ⟨1/2,by norm_num⟩
    let f : Circle × Interval → S := fun p => M.cover.projection (T p).val
    have hc : Continuous f := M.cover.projection_continuous.comp
      (continuous_subtype_val.comp T.continuous)
    have hopen : IsOpen (f ⁻¹' interior Nb.closedSet) := isOpen_interior.preimage hc
    have hmid : (Set.univ : Set Circle) ×ˢ {c} ⊆ f ⁻¹' interior Nb.closedSet := by
      rintro ⟨z,t⟩ ⟨_,ht⟩
      have he : t = c := ht
      subst t
      have hh : (T (z,c)).val ∈ M.cover.projection ⁻¹' b.image := by
        rw [← hTc]
        exact Set.mem_range_self z
      exact Nb.arc_inside hh
    obtain ⟨W,V,hW,hV,hall,hcV,hWV⟩ :=
      generalized_tube_lemma (isCompact_univ : IsCompact (Set.univ : Set Circle))
        (isCompact_singleton : IsCompact ({c} : Set Interval)) hopen hmid
    refine ⟨V,hV,hcV (Set.mem_singleton c),?_⟩
    intro z t ht
    exact hWV ⟨hall (Set.mem_univ z),ht⟩

-- Literal transition map, on the actual band produced above.
example (M : HyperellipticModel E S) (b : NonLoopArc M)
    (Nb : ArcNeighborhood b) (U : Set E)
    (T : Circle × Interval ≃ₜ U)
    (B : Circle × Interval ≃ₜ M.cover.projection ⁻¹' Nb.closedSet)
    (r : Circle ≃ₜ Circle)
    (hr : ∀ z : Circle, (B (r z,⟨1/2,by norm_num⟩)).val =
      (T (z,⟨1/2,by norm_num⟩)).val)
    (V : Set Interval) (hcV : (⟨1/2,by norm_num⟩ : Interval) ∈ V)
    (hbandV : ∀ z : Circle, ∀ t ∈ V,
      M.cover.projection (T (z,t)).val ∈ interior Nb.closedSet) :
    ∃ F : C(Circle × V, Circle × Interval), Topology.IsEmbedding F ∧
      (∀ z : Circle, ∀ t : V, (B (F (z,t))).val = (T (z,t.val)).val) ∧
      ∀ z : Circle, F (z,⟨⟨1/2,by norm_num⟩,hcV⟩) = (r z,⟨1/2,by norm_num⟩) := by
  audit_main14_base3
    let f : Circle × V → M.cover.projection ⁻¹' Nb.closedSet := fun p =>
      ⟨(T (p.1,p.2.val)).val, (show M.cover.projection (T (p.1,p.2.val)).val ∈ Nb.closedSet from interior_subset (hbandV p.1 p.2.val p.2.property))⟩
    have hfc : Continuous f :=
      (continuous_subtype_val.comp (T.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
    let F : C(Circle × V, Circle × Interval) := ⟨fun p => B.symm (f p),
      B.symm.continuous.comp hfc⟩
    have hfe : Topology.IsEmbedding f := by
      apply Topology.IsEmbedding.of_comp hfc continuous_subtype_val
      change Topology.IsEmbedding (fun p : Circle × V => (T (p.1,p.2.val)).val)
      exact Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp
        ((Homeomorph.refl Circle).isEmbedding.prodMap Topology.IsEmbedding.subtypeVal))
    refine ⟨F,B.symm.isEmbedding.comp hfe,?_,?_⟩
    · intro z t
      exact congrArg Subtype.val (B.apply_symm_apply (f (z,t)))
    · intro z
      apply B.injective
      apply Subtype.ext
      change (B (B.symm (f (z,⟨⟨1/2,by norm_num⟩,hcV⟩)))).val = _
      rw [B.apply_symm_apply]
      exact (hr z).symm

end CurveComplex.HyperellipticModel
