import CurveComplexGenusTwo.Filtration.Geometry.ActualTwoFreeGapsHeader
import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualJordanInsideChartHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.OpenEmbeddingFaceHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.HomeomorphismComponentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ParallelBoundaryDescentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RegionComponentHeaders
import CurveComplexGenusTwo.Topology.ArcStraightening
import Schoenflies.BoundaryContinuity2
import CurveComplexGenusTwo.Filtration.Geometry.MarkedCrosscutSurface
namespace CurveComplex.HyperellipticModel
open scoped Classical
open Set Schoenflies CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualGoodFreeGapHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
set_option maxHeartbeats 8000000
theorem actual_good_free_gap (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {w // w ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (hbad : badVertices (actualArcLabels M) σ = σ) (hne : σ.Nonempty) :
    ∃ O : Finset (EssentialArcClass M), ∃ U : Set S,
      O ∈ actualObjectFamily M σ ∧
      IsComplementComponent (actualObjectTrace M r O) U ∧
      IsComplementComponent (⋃ w, (r w).val.image) U ∧
      (∀ Q ∈ actualObjectFamily M σ, Q ≠ O → ¬ actualObjectTrace M r Q ⊆ closure U) ∧
      1 ≤ (M.cover.branch.filter (fun x => x ∈ U)).card ∧
      (M.cover.branch.filter (fun x => x ∈ U)).card ≤ 2 := by
  classical
  have positive (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
      (r : {w // w ∈ σ} → EssentialMarkedArc M)
      (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
      (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
      (hbad : badVertices (actualArcLabels M) σ = σ)
      (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M σ)
      (U : Set S) (hU : IsComplementComponent (actualObjectTrace M r O) U) :
      ∃ x : S, x ∈ M.cover.branch ∧ x ∈ U := by
    classical
    have endpointPositive (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
        (r : {w // w ∈ σ} → EssentialMarkedArc M)
        (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
        (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
        (hbad : badVertices (actualArcLabels M) σ = σ)
        (v : EssentialArcClass M) (hc : 2 ≤ (actualEndpointFibre M σ v).card)
        (U : Set S) (hU : IsComplementComponent (actualObjectTrace M r (actualEndpointFibre M σ v)) U) :
        ∃ x : S, x ∈ M.cover.branch ∧ x ∈ U := by
      classical
      have planar (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
          (r : {w // w ∈ σ} → EssentialMarkedArc M)
          (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
          (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
          (hbad : badVertices (actualArcLabels M) σ = σ)
          (v : EssentialArcClass M) (hc : 2 ≤ (actualEndpointFibre M σ v).card)
          (U : Set S) (hU : IsComplementComponent (actualObjectTrace M r (actualEndpointFibre M σ v)) U) :
          ∃ a b : {w // w ∈ actualEndpointFibre M σ v}, a ≠ b ∧
            frontier U =
              (r ⟨a.val, actualEndpointFibre_subset M σ v a.property⟩).val.image ∪
              (r ⟨b.val, actualEndpointFibre_subset M σ v b.property⟩).val.image ∧
            ∃ C : Set Plane, IsJordanCurve C ∧ ∃ f : Plane → S,
              Topology.IsOpenEmbedding f ∧ U = f '' inside C ∧ f '' C = frontier U ∧
              ∃ p q : Plane, ∃ A B : Set Plane,
                IsArcBetween A p q ∧ IsArcBetween B p q ∧ A ∩ B = {p,q} ∧
                C = A ∪ B ∧
                f '' A = (r ⟨a.val, actualEndpointFibre_subset M σ v a.property⟩).val.image ∧
                f '' B = (r ⟨b.val, actualEndpointFibre_subset M σ v b.property⟩).val.image := by
        classical
        letI : T2Space S := M.sphere.symm.t2Space
        have extract (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
          (r : {w // w ∈ σ} → EssentialMarkedArc M)
          (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
          (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
          (v : EssentialArcClass M) :
          ∃ rO : {w // w ∈ actualEndpointFibre M σ v} → NonLoopArc M,
            (∀ w, (rO w).val = (r ⟨w.val, actualEndpointFibre_subset M σ v w.property⟩).val) ∧
            (∀ w z, markedArcEndset (rO w).val = markedArcEndset (rO z).val) ∧
            (∀ w z, w ≠ z → Disjoint ((rO w).val.image \ (M.cover.branch : Set S))
              ((rO z).val.image \ (M.cover.branch : Set S))) ∧
            (⋃ w, (rO w).val.image) = actualObjectTrace M r (actualEndpointFibre M σ v) := by
        
          classical
          let k : {w // w ∈ actualEndpointFibre M σ v} → {w // w ∈ σ} :=
            fun w => ⟨w.val, actualEndpointFibre_subset M σ v w.property⟩
          have hn (w : {w // w ∈ actualEndpointFibre M σ v}) :
              ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (r (k w))) := by
            rw [hr]
            exact (Finset.mem_filter.mp w.property).2.1
          let rO : {w // w ∈ actualEndpointFibre M σ v} → NonLoopArc M :=
            fun w => ⟨(r (k w)).val, actualRepresentative_nonloop M (r (k w)) (hn w)⟩
          refine ⟨rO, (fun w => rfl), ?_, ?_, ?_⟩
          · intro w z
            change markedArcEndset (r (k w)).val = markedArcEndset (r (k z)).val
            rw [markedArcEndset_eq_classEndpoints, markedArcEndset_eq_classEndpoints, hr, hr]
            exact (Finset.mem_filter.mp w.property).2.2.trans
              (Finset.mem_filter.mp z.property).2.2.symm
          · intro w z hwz
            exact hd (k w) (k z) (fun h => hwz (Subtype.ext (congrArg (fun x : {w // w ∈ σ} => x.val) h)))
          · ext x
            constructor
            · intro hxG
              obtain ⟨w, hx⟩ := Set.mem_iUnion.mp hxG
              exact Set.mem_iUnion.mpr ⟨k w, Set.mem_iUnion.mpr ⟨w.property, hx⟩⟩
            · intro hxG
              obtain ⟨w, hwx⟩ := Set.mem_iUnion.mp hxG
              obtain ⟨hw, hx⟩ := Set.mem_iUnion.mp hwx
              refine Set.mem_iUnion.mpr ⟨⟨w.val, hw⟩, ?_⟩
              exact hx
        have align (M : HyperellipticModel E S) {I : Type} [Fintype I] [Nonempty I]
          (r : I → NonLoopArc M)
          (hends : ∀ i j, markedArcEndset (r i).val = markedArcEndset (r j).val)
          (hd : ∀ i j, i ≠ j → Disjoint ((r i).val.image \ (M.cover.branch : Set S))
            ((r j).val.image \ (M.cover.branch : Set S)))
          (z : S) (hz : z ∉ ⋃ i, (r i).val.image)
          (e : {x : S // x ≠ z} ≃ₜ Plane) :
          ∃ p q : Plane, p ≠ q ∧ ∃ A : I → Set Plane,
            (∀ i, IsArcBetween (A i) p q) ∧
            (∀ i j, i ≠ j → A i ∩ A j = {p, q}) ∧
            (∀ i, (fun t => (e.symm t).val) '' A i = (r i).val.image) := by
        
          classical
          have planar (M : HyperellipticModel E S) (a : NonLoopArc M) (z : S)
            (ha : z ∉ a.val.image) (e : {x : S // x ≠ z} ≃ₜ Plane) :
            IsArcBetween
              (Set.range (fun t : Interval => e ⟨a.val.map t,
                fun h => ha (h ▸ ⟨t, rfl⟩)⟩))
              (e ⟨a.val.map 0, fun h => ha (h ▸ ⟨0, rfl⟩)⟩)
              (e ⟨a.val.map 1, fun h => ha (h ▸ ⟨1, rfl⟩)⟩) := by
          
            let g : Interval → Plane := fun t => e ⟨a.val.map t,
              fun h => ha (h ▸ ⟨t, rfl⟩)⟩
            have hg : Continuous g := e.continuous.comp (a.val.continuous.subtype_mk _)
            have hi : Function.Injective g := by
              intro t u h
              apply a.injective
              exact congrArg Subtype.val (e.injective h)
            let f : ℝ → Plane := fun t => g (projIcc 0 1 (by norm_num) t)
            have hf : Continuous f := hg.comp continuous_projIcc
            refine ⟨f, hf.continuousOn, ?_, ?_, ?_, ?_⟩
            · intro t ht u hu h
              have he := hi h
              rw [projIcc_of_mem (by norm_num) ht, projIcc_of_mem (by norm_num) hu] at he
              exact congrArg Subtype.val he
            · ext x
              constructor
              · rintro ⟨t, ht, rfl⟩
                exact ⟨projIcc 0 1 (by norm_num) t, rfl⟩
              · rintro ⟨t, rfl⟩
                refine ⟨t.val, t.property, ?_⟩
                dsimp [f]
                rw [projIcc_of_mem (by norm_num) t.property]
            · dsimp [f]
              rw [projIcc_of_mem (by norm_num) (by norm_num : (0 : ℝ) ∈ Icc 0 1)]
              rfl
            · dsimp [f]
              rw [projIcc_of_mem (by norm_num) (by norm_num : (1 : ℝ) ∈ Icc 0 1)]
              rfl
          have avoid (i : I) : z ∉ (r i).val.image := fun h => hz (mem_iUnion.mpr ⟨i, h⟩)
          let g : I → Interval → Plane := fun i t => e ⟨(r i).val.map t,
            fun h => avoid i (h ▸ ⟨t, rfl⟩)⟩
          let A : I → Set Plane := fun i => range (g i)
          let i₀ : I := Classical.choice inferInstance
          let p := g i₀ 0
          let q := g i₀ 1
          have hpq : p ≠ q := by
            intro h
            have he := congrArg Subtype.val (e.injective h)
            exact (r i₀).property he
          have ordered : ∀ i, (g i 0 = p ∧ g i 1 = q) ∨ (g i 0 = q ∧ g i 1 = p) := by
            intro i
            have he := hends i i₀
            change ({(r i).val.map 0, (r i).val.map 1} : Finset S) =
              {(r i₀).val.map 0, (r i₀).val.map 1} at he
            have heS := congrArg (fun s : Finset S => (s : Set S)) he
            simp only [Finset.coe_insert, Finset.coe_singleton] at heS
            rcases Set.pair_eq_pair_iff.mp heS with he | he
            · left
              constructor
              · apply congrArg e; exact Subtype.ext he.1
              · apply congrArg e; exact Subtype.ext he.2
            · right
              constructor
              · apply congrArg e; exact Subtype.ext he.1
              · apply congrArg e; exact Subtype.ext he.2
          have harc : ∀ i, IsArcBetween (A i) p q := by
            intro i
            have hh := planar M (r i) z (avoid i) e
            change IsArcBetween (A i) (g i 0) (g i 1) at hh
            rcases ordered i with he | he
            · rw [he.1, he.2] at hh
              exact hh
            · rw [he.1, he.2] at hh
              exact hh.reverse
          refine ⟨p, q, hpq, A, harc, ?_, ?_⟩
          · intro i j hij
            apply Set.Subset.antisymm
            · rintro t ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
              have hmaps : (r j).val.map v = (r i).val.map u :=
                congrArg Subtype.val (e.injective hv)
              have hm : (r i).val.map u ∈ M.cover.branch := by
                by_contra hn
                exact Set.disjoint_left.mp (hd i j hij) ⟨⟨u, rfl⟩, hn⟩
                  ⟨⟨v, hmaps⟩, hmaps.symm ▸ hn⟩
              rcases (r i).val.marked_only_at_ends u hm with hu | hu
              · subst u
                rcases ordered i with he | he <;> simp [he.1]
              · subst u
                rcases ordered i with he | he <;> simp [he.2]
            · intro t ht
              rcases (by simpa using ht : t = p ∨ t = q) with rfl | rfl
              · exact ⟨(harc i).left_mem, (harc j).left_mem⟩
              · exact ⟨(harc i).right_mem, (harc j).right_mem⟩
          · intro i
            ext x
            constructor
            · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
              have he : (e.symm (g i t)).val = (r i).val.map t := by simp [g]
              change (e.symm (g i t)).val ∈ (r i).val.image
              rw [he]
              exact ⟨t, rfl⟩
            · rintro ⟨t, rfl⟩
              refine ⟨g i t, ⟨t, rfl⟩, ?_⟩
              simp [g]
        let O := actualEndpointFibre M σ v
        let I := {w // w ∈ O}
        obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp (lt_of_lt_of_le (by norm_num) hc)
        let u₀ : I := ⟨u, hu⟩
        let w₀ : I := ⟨w, hw⟩
        letI : Nonempty I := ⟨u₀⟩
        have hu₀w₀ : u₀ ≠ w₀ := fun he => huw (congrArg Subtype.val he)
        obtain ⟨rO, hfix, hends, hdis, hgraph⟩ := extract M r hr hd v
        obtain ⟨cS, hcS⟩ := actual_parallel_pair_curve_unordered M (rO u₀) (rO w₀)
          (hends u₀ w₀) (hdis u₀ w₀ hu₀w₀)
        obtain ⟨c, hcimage⟩ := actualCurve_sphereJordan M cS
        have hcg : c.image ⊆ M.sphere '' (⋃ k, (r k).val.image) := by
          rw [hcimage, hcS]
          apply image_mono
          intro x hx
          rcases hx with hx | hx
          · rw [hfix u₀] at hx
            exact mem_iUnion.mpr ⟨⟨u, actualEndpointFibre_subset M σ v hu⟩, hx⟩
          · rw [hfix w₀] at hx
            exact mem_iUnion.mpr ⟨⟨w, actualEndpointFibre_subset M σ v hw⟩, hx⟩
        obtain ⟨x, hxU⟩ := hU.1
        have hxgraph : x ∉ ⋃ k, (rO k).val.image := by
          rw [hgraph]
          exact hU.2.2.1 hxU
        have hxc : M.sphere x ∉ c.image := by
          rw [hcimage, hcS]
          rintro ⟨y, hy, he⟩
          have hyx := M.sphere.injective he
          rcases hy with hy | hy
          · exact hxgraph (mem_iUnion.mpr ⟨u₀, hyx ▸ hy⟩)
          · exact hxgraph (mem_iUnion.mpr ⟨w₀, hyx ▸ hy⟩)
        let W := connectedComponentIn c.imageᶜ (M.sphere x)
        have hW : IsComplementComponent c.image W := complementComponent_iff_componentIn.mpr
          ⟨M.sphere x, hxc, rfl⟩
        obtain ⟨P, hpG, heW⟩ := actual_graph_avoiding_jordan_inside_chart M r hr hd hbad c hcg W hW
        let z := M.sphere.symm P.puncture
        let es : {x : S // x ≠ z} ≃ₜ {y : CurveComplex.SpherePort.Sphere // y ≠ P.puncture} :=
          M.sphere.subtype (fun y => by
            change y ≠ M.sphere.symm P.puncture ↔ M.sphere y ≠ P.puncture
            constructor
            · intro hy he
              exact hy (M.sphere.injective (he.trans (M.sphere.apply_symm_apply P.puncture).symm))
            · intro hy he
              exact hy (he ▸ M.sphere.apply_symm_apply P.puncture))
        let e := es.trans P.plane
        let f : Plane → S := fun t => (e.symm t).val
        have hf : Topology.IsOpenEmbedding f :=
          isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
        have hzgraph : z ∉ ⋃ i, (rO i).val.image := by
          intro hz
          rw [hgraph] at hz
          have hzfull := actualObjectTrace_subset_graph M r O hz
          exact hpG ⟨z, hzfull, M.sphere.apply_symm_apply P.puncture⟩
        obtain ⟨p, q, hpq, A, harc, hmeet, himage⟩ := align M rO hends hdis z hzgraph e
        have fformula : ∀ t, f t = M.sphere.symm (P.plane.symm t).val := by
          intro t
          rfl
        have hCimage : f '' P.planeImage c = (rO u₀).val.image ∪ (rO w₀).val.image := by
          ext y
          constructor
          · rintro ⟨t, ht, rfl⟩
            obtain ⟨b, hb, hbt⟩ := ht
            rw [← hbt, fformula]
            have he := congrArg Subtype.val (P.plane.symm_apply_apply b)
            rw [he]
            rw [hcimage, hcS] at hb
            obtain ⟨a, ha, hab⟩ := hb
            have haeq : a = M.sphere.symm b.val := by
              apply M.sphere.injective
              rw [M.sphere.apply_symm_apply]
              exact hab
            exact haeq ▸ ha
          · intro hy
            have hyp : y ≠ z := by
              intro he
              have hzI : z ∈ ⋃ i, (rO i).val.image := by
                rcases hy with hy | hy
                · exact mem_iUnion.mpr ⟨u₀, he ▸ hy⟩
                · exact mem_iUnion.mpr ⟨w₀, he ▸ hy⟩
              exact hzgraph hzI
            let b : {b : CurveComplex.SpherePort.Sphere // b ≠ P.puncture} := es ⟨y, hyp⟩
            refine ⟨P.plane b, ⟨b, ?_, rfl⟩, ?_⟩
            · rw [hcimage, hcS]
              exact ⟨y, hy, rfl⟩
            · change (e.symm (e ⟨y, hyp⟩)).val = y
              simp
        have hC : P.planeImage c = A u₀ ∪ A w₀ := by
          apply (Set.image_injective.mpr hf.injective)
          rw [hCimage, image_union, himage, himage]
        have hxW : M.sphere x ∈ W := mem_connectedComponentIn hxc
        rw [heW] at hxW
        obtain ⟨t, ht, htx⟩ := hxW
        have hft : f t = x := by
          change (P.plane.symm t).val = M.sphere x at htx
          rw [fformula, htx, M.sphere.symm_apply_apply]
        have htnot : ∀ i ∈ (Finset.univ : Finset I), t ∉ A i := by
          intro i _ htI
          have hxi : x ∈ (rO i).val.image := himage i ▸ ⟨t, htI, hft⟩
          exact hxgraph (mem_iUnion.mpr ⟨i, hxi⟩)
        have hti : t ∈ inside (A u₀ ∪ A w₀) := hC ▸ ht
        obtain ⟨a, _, b, _, hab, hface, htface, hfront⟩ := parallel_family_inside_face_boundary
          (Finset.univ : Finset I) A p q t (fun i _ => harc i)
          (fun i _ j _ hij => hmeet i j hij) htnot u₀ w₀ (Finset.mem_univ _) (Finset.mem_univ _) hu₀w₀ hti
        let C := A a ∪ A b
        have hJ : IsJordanCurve C := isJordanCurve_union (harc a) (harc b) (by
          intro y hyA hyB
          have hy : y ∈ ({p, q} : Set Plane) := hmeet a b hab ▸ ⟨hyA, hyB⟩
          simpa using hy)
        have hsep := jordan_curve_theorem hJ
        have hk : IsCompact (closure (inside C)) := Metric.isCompact_of_isClosed_isBounded
          isClosed_closure hsep.isBounded_inside.closure
        have hfrsub : frontier (inside C) ⊆ ⋃ k ∈ (Finset.univ : Finset I), A k := by
          rw [hfront]
          intro y hy
          rcases hy with hy | hy
          · exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨Finset.mem_univ _, hy⟩⟩
          · exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨Finset.mem_univ _, hy⟩⟩
        have hFG := open_embedding_bounded_face_transport f hf _ _ hface hsep.isOpen_inside hk hfrsub
        have hFull : f '' (⋃ k ∈ (Finset.univ : Finset I), A k) = actualObjectTrace M r O := by
          change (fun t => (e.symm t).val) '' (⋃ k ∈ (Finset.univ : Finset I), A k) = _
          simp only [Finset.mem_univ, iUnion_true, image_iUnion, himage]
          exact hgraph
        rw [hFull] at hFG
        have hxFG : x ∈ f '' inside C := ⟨t, htface, hft⟩
        have heU : U = f '' inside C := by
          by_contra he
          exact Set.disjoint_left.mp (complementComponents_disjoint hU hFG he) hxU hxFG
        have hcl : closure (f '' inside C) = f '' closure (inside C) := by
          apply Set.Subset.antisymm
          · exact closure_minimal (image_mono subset_closure) (hk.image hf.continuous).isClosed
          · exact image_closure_subset_closure_image hf.continuous
        have hfr : frontier U = f '' C := by
          rw [heU, (hf.isOpenMap _ hsep.isOpen_inside).frontier_eq, hcl,
            ← image_sdiff hf.injective, ← hsep.isOpen_inside.frontier_eq, hfront]
        refine ⟨a, b, hab, ?_, C, hJ, f, hf, heU, hfr.symm,
          p, q, A a, A b, harc a, harc b, hmeet a b hab, rfl, ?_, ?_⟩
        · rw [hfr, image_union, himage, himage, hfix a, hfix b]
        · exact (himage a).trans (congrArg (fun u : MarkedArc M => u.image) (hfix a))
        · exact (himage b).trans (congrArg (fun u : MarkedArc M => u.image) (hfix b))
      have emptyBigon (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
          (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
          (A B : Set Plane) (p q : Plane)
          (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
          (hmeet : A ∩ B = {p,q}) (hJ : IsJordanCurve (A ∪ B))
          (haImage : a.val.image = f '' A) (hbImage : b.val.image = f '' B)
          (hboundary : ∀ t ∈ A ∪ B, f t ∈ M.cover.branch → t = p ∨ t = q)
          (hempty : ∀ t ∈ inside (A ∪ B), f t ∉ M.cover.branch) :
          Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b := by
        classical
        letI : T2Space S := M.sphere.symm.t2Space
        letI : CompactSpace S := M.sphere.symm.compactSpace
        have chart {A B : Set Plane} {a b : Plane}
            (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
            (hmeet : A ∩ B = {a,b}) (hJ : IsJordanCurve (A ∪ B))
            (P : Finset Plane) (hP : ∀ x ∈ P, x ∉ closure (inside (A ∪ B))) :
            ∃ F : Plane ≃ₜ Plane,
              F a = Plane.mk 1 0 ∧ F b = Plane.mk (-1) 0 ∧
              (∀ x ∈ A ∪ B, x ≠ a → x ≠ b → F x ∈ Plane.openSquare 0 1) ∧
              (∀ x ∈ P, F x ∉ Plane.openSquare 0 1) := by
          classical
          have split
              {A P : Set Plane} {a b : Plane}
              (hA : IsArcBetween A a b) (hP : IsArcBetween P a b)
              (hmeet : A ∩ P = {a, b})
              (hJ : IsJordanCurve (A ∪ P)) :
              ∃ F : Plane ≃ₜ Plane, F '' P = sideBottom ∪ sideRight ∧
                F a = cornerNE ∧ F b = cornerSW ∧
                F '' (A ∪ P) = modelCurve := by
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
            have hwhole : F '' (A ∪ P) = modelCurve := by
              ext y
              constructor
              · rintro ⟨x, hx, rfl⟩
                rw [hF ⟨x, hx⟩]
                exact (eModel ⟨x, hx⟩).property
              · intro hy
                obtain ⟨x, hx⟩ := eModel.surjective ⟨y, hy⟩
                refine ⟨x.val, x.property, ?_⟩
                rw [hF x]
                exact congrArg Subtype.val hx
            exact ⟨F, hImage, hFa, hFb, hwhole⟩
          
          
          have insideMap {C : Set Plane} (hC : IsJordanCurve C)
              (F : Plane ≃ₜ Plane) (him : F '' C = modelCurve) :
              F '' inside C = Plane.openSquare 0 1 := by
            have outsideComponent {C : Set Plane} (hC : IsJordanCurve C) :
                IsComplementComponent C (outside C) := by
              have hs := jordan_curve_theorem hC
              refine ⟨hs.isConnected_outside.nonempty, hs.isConnected_outside, outside_subset_compl, ?_⟩
              intro V hV hsub hVc
              apply Set.Subset.antisymm
              · apply hV.isPreconnected.subset_of_closure_inter_subset hs.isOpen_outside
                · obtain ⟨x, hx⟩ := hs.isConnected_outside.nonempty
                  exact ⟨x, hsub hx, hx⟩
                · intro x hx
                  rw [(IsRegionOf.outside C).closure_eq hs] at hx
                  rcases hx.1 with hi | hc
                  · exact hi
                  · exact False.elim (hVc hx.2 hc)
              · exact hsub
            have hc := homeomorphism_complement_component F (jordan_inside_complement_component hC)
            rw [him] at hc
            have hi := jordan_inside_complement_component isJordanCurve_modelCurve
            have ho := outsideComponent isJordanCurve_modelCurve
            obtain ⟨x, hx⟩ := hc.1
            have hxin : x ∈ inside modelCurve ∪ outside modelCurve :=
              (inside_union_outside modelCurve).symm ▸ hc.2.2.1 hx
            have heinside : F '' inside C = inside modelCurve := by
              rcases hxin with hxI | hxO
              · by_contra hn
                exact Set.disjoint_left.mp (complementComponents_disjoint hc hi hn) hx hxI
              · have heoutside : F '' inside C = outside modelCurve := by
                  by_contra hn
                  exact Set.disjoint_left.mp (complementComponents_disjoint hc ho hn) hx hxO
                have hs := jordan_curve_theorem hC
                have hk : IsCompact (closure (inside C)) :=
                  Metric.isCompact_of_isClosed_isBounded isClosed_closure hs.isBounded_inside.closure
                have hb : Bornology.IsBounded (F '' inside C) :=
                  (hk.image F.continuous).isBounded.subset (image_mono subset_closure)
                exact False.elim ((jordan_curve_theorem isJordanCurve_modelCurve).not_isBounded_outside
                  (heoutside ▸ hb))
            exact heinside.trans inside_modelCurve
          have chart (P : Finset Plane)
              (hP : ∀ x ∈ P, x ∉ Plane.closedSquare 0 1) :
              ∃ G : Plane ≃ₜ Plane,
                G cornerNE = Plane.mk 1 0 ∧ G cornerSW = Plane.mk (-1) 0 ∧
                (∀ x ∈ modelCurve, x ≠ cornerNE → x ≠ cornerSW →
                  G x ∈ Plane.openSquare 0 1) ∧
                (∀ x ∈ P, G x ∉ Plane.openSquare 0 1) := by
            classical
            have escape {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [DecidableEq V]
                (P : Finset V) (hP : ∀ x ∈ P, 1 < ‖x‖) :
                ∃ F : V ≃ₜ V, (∀ x, ‖x‖ ≤ 1 → F x = x) ∧ ∀ x ∈ P, 4 < ‖F x‖ := by
              have stretch {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
                (k : ℝ) (hk : 0 < k) :
                ∃ F : V ≃ₜ V, (∀ x, ‖x‖ ≤ 1 → F x = x) ∧
                  ∀ x, 1 < ‖x‖ → ‖F x‖ = 1 + k * (‖x‖ - 1) := by
              
                let g : ℝ → V → V := fun a x => (a + (1 - a) / max 1 ‖x‖) • x
                have cont (a : ℝ) : Continuous (g a) := by
                  apply Continuous.smul _ continuous_id
                  apply Continuous.add continuous_const
                  apply Continuous.div continuous_const (continuous_const.max continuous_norm)
                  intro x
                  have h : (0 : ℝ) < max 1 ‖x‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
                  exact ne_of_gt h
                have fixed (a : ℝ) (x : V) (hx : ‖x‖ ≤ 1) : g a x = x := by
                  simp [g, max_eq_left hx]
                have expanded (a : ℝ) (ha : 0 < a) (x : V) (hx : 1 < ‖x‖) :
                    ‖g a x‖ = 1 + a * (‖x‖ - 1) := by
                  have hn : 0 < ‖x‖ := lt_trans (by norm_num) hx
                  have hcoef : 0 < a + (1 - a) / ‖x‖ := by
                    have he : a + (1 - a) / ‖x‖ = (1 + a * (‖x‖ - 1)) / ‖x‖ := by
                      field_simp
                      <;> ring
                    rw [he]
                    positivity
                  simp only [g, max_eq_right hx.le, norm_smul, Real.norm_eq_abs, abs_of_pos hcoef]
                  field_simp
                  <;> ring
                have left (a : ℝ) (ha : 0 < a) (x : V) : g a⁻¹ (g a x) = x := by
                  by_cases hx : ‖x‖ ≤ 1
                  · rw [fixed a x hx, fixed a⁻¹ x hx]
                  · have hx' : 1 < ‖x‖ := lt_of_not_ge hx
                    have hn : ‖x‖ ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx')
                    have hg := expanded a ha x hx'
                    have hg' : 1 < ‖g a x‖ := by
                      rw [hg]
                      have hpos : 0 < a * (‖x‖ - 1) := mul_pos ha (sub_pos.mpr hx')
                      linarith
                    have hs : (1 + a * (‖x‖ - 1)) ≠ 0 := ne_of_gt (by positivity)
                    change (a⁻¹ + (1 - a⁻¹) / max 1 ‖g a x‖) •
                      ((a + (1 - a) / max 1 ‖x‖) • x) = x
                    rw [max_eq_right hg'.le, hg, max_eq_right hx'.le, smul_smul]
                    have he : (a⁻¹ + (1 - a⁻¹) / (1 + a * (‖x‖ - 1))) *
                        (a + (1 - a) / ‖x‖) = 1 := by
                      field_simp [ha.ne', hn, hs]
                      <;> ring
                    rw [he, one_smul]
                let F : V ≃ₜ V := {
                  toFun := g k
                  invFun := g k⁻¹
                  left_inv := left k hk
                  right_inv := by
                    intro x
                    have h := left k⁻¹ (inv_pos.mpr hk) x
                    simpa using h
                  continuous_toFun := cont k
                  continuous_invFun := cont k⁻¹ }
                exact ⟨F, fixed k, expanded k hk⟩
              let w : V → ℝ := fun x => 4 / (‖x‖ - 1)
              let k := 1 + ∑ x ∈ P, w x
              have hw : ∀ x ∈ P, 0 ≤ w x := by
                intro x hx
                exact le_of_lt (div_pos (by norm_num) (sub_pos.mpr (hP x hx)))
              have hk : 0 < k := by
                have hs : 0 ≤ ∑ x ∈ P, w x := Finset.sum_nonneg hw
                dsimp [k]
                linarith
              obtain ⟨F, hfixed, hnorm⟩ := stretch (V := V) k hk
              refine ⟨F, hfixed, ?_⟩
              intro x hx
              have hwle : w x ≤ ∑ y ∈ P, w y := Finset.single_le_sum hw hx
              have hkge : w x ≤ k := le_trans hwle (by dsimp [k]; linarith)
              have hmult : 4 ≤ k * (‖x‖ - 1) :=
                (div_le_iff₀ (sub_pos.mpr (hP x hx))).mp hkge
              rw [hnorm x (hP x hx)]
              linarith
            have diamond : ∃ L : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ),
                (∀ x, L x 0 = (x 0 + x 1) / 2 ∧ L x 1 = (x 0 - x 1) / 4) ∧
                (∀ x, ‖x‖ ≤ 1 → x ≠ ![1, 1] → x ≠ ![-1, -1] → ‖L x‖ < 1) ∧
                (∀ x, 4 < ‖x‖ → 1 < ‖L x‖) := by
              let f : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => ![(x 0 + x 1) / 2, (x 0 - x 1) / 4]
              let g : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun x => ![x 0 + 2 * x 1, x 0 - 2 * x 1]
              let L : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) := {
                toFun := f
                invFun := g
                left_inv := by intro x; ext i; fin_cases i <;> simp [f, g] <;> ring
                right_inv := by intro x; ext i; fin_cases i <;> simp [f, g] <;> ring
                continuous_toFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp [f] <;> fun_prop
                continuous_invFun := by apply continuous_pi; intro i; fin_cases i <;> dsimp [g] <;> fun_prop }
              refine ⟨L, (fun x => ⟨rfl, rfl⟩), ?_, ?_⟩
              · intro x hx hne hsw
                have hx0 : |x 0| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 0 |>.trans hx
                have hx1 : |x 1| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x 1 |>.trans hx
                rw [abs_le] at hx0 hx1
                have hs : -2 < x 0 + x 1 ∧ x 0 + x 1 < 2 := by
                  constructor
                  · by_contra hn
                    have h0 : x 0 = -1 := by linarith
                    have h1 : x 1 = -1 := by linarith
                    apply hsw
                    ext i; fin_cases i <;> simp [h0, h1]
                  · by_contra hn
                    have h0 : x 0 = 1 := by linarith
                    have h1 : x 1 = 1 := by linarith
                    apply hne
                    ext i; fin_cases i <;> simp [h0, h1]
                apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
                intro i
                fin_cases i
                · change ‖(x 0 + x 1) / 2‖ < 1
                  rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
                · change ‖(x 0 - x 1) / 4‖ < 1
                  rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
              · intro x hx
                by_contra hn
                have hy : ‖L x‖ ≤ 1 := le_of_not_gt hn
                have hy0 : |L x 0| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (L x) 0 |>.trans hy
                have hy1 : |L x 1| ≤ 1 := by simpa [Real.norm_eq_abs] using norm_le_pi_norm (L x) 1 |>.trans hy
                change |(x 0 + x 1) / 2| ≤ 1 at hy0
                change |(x 0 - x 1) / 4| ≤ 1 at hy1
                rw [abs_le] at hy0 hy1
                have hb : ‖x‖ ≤ 3 := (pi_norm_le_iff_of_nonneg (x := x) (by norm_num : (0 : ℝ) ≤ 3)).mpr (by
                  intro i; fin_cases i
                  · change ‖x 0‖ ≤ 3
                    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
                  · change ‖x 1‖ ≤ 3
                    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
                linarith
            let H : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
            have hnorm (x : Plane) : ‖H x‖ = Plane.supNorm x := by
              rw [show H x = fun i => x i by rfl]
              simp [Pi.norm_def, Fin.sum_univ_two, Finset.univ_fin2, Plane.supNorm,
                Real.norm_eq_abs, max_comm]
            have hclosed (x : Plane) : x ∈ Plane.closedSquare 0 1 ↔ ‖H x‖ ≤ 1 := by
              rw [mem_closedSquare_zero_one, hnorm]
            have hopen (x : Plane) : x ∈ Plane.openSquare 0 1 ↔ ‖H x‖ < 1 := by
              rw [mem_openSquare_zero_one, hnorm]
            have hmarks : ∀ y ∈ P.image H, 1 < ‖y‖ := by
              intro y hy
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
              exact lt_of_not_ge (fun h => hP x hx ((hclosed x).mpr h))
            obtain ⟨F, hfix, hescape⟩ := escape (P.image H) hmarks
            obtain ⟨L, hcoord, hinside, houtside⟩ := diamond
            let G : Plane ≃ₜ Plane := ((H.trans F).trans L).trans H.symm
            have hG (x : Plane) : H (G x) = L (F (H x)) := H.apply_symm_apply _
            have hNE : H cornerNE = ![1, 1] := by ext i; fin_cases i <;> rfl
            have hSW : H cornerSW = ![-1, -1] := by ext i; fin_cases i <;> rfl
            have hfixNE : F (H cornerNE) = H cornerNE := hfix _ (by rw [hnorm]; norm_num [cornerNE, Plane.mk, Plane.supNorm])
            have hfixSW : F (H cornerSW) = H cornerSW := hfix _ (by rw [hnorm]; norm_num [cornerSW, Plane.mk, Plane.supNorm])
            refine ⟨G, ?_, ?_, ?_, ?_⟩
            · apply H.injective
              rw [hG, hfixNE, hNE]
              ext i; fin_cases i
              · simpa [H, Plane.mk] using (hcoord ![1,1]).1
              · simpa [H, Plane.mk] using (hcoord ![1,1]).2
            · apply H.injective
              rw [hG, hfixSW, hSW]
              ext i; fin_cases i
              · simpa [H, Plane.mk] using (hcoord ![-1,-1]).1
              · simpa [H, Plane.mk] using (hcoord ![-1,-1]).2
            · intro x hx hne hsw
              have hn : ‖H x‖ ≤ 1 := (hclosed x).mp (modelCurve_subset_closedSquare hx)
              apply (hopen _).mpr
              rw [hG, hfix _ hn]
              apply hinside _ hn
              · intro he; apply hne; apply H.injective; exact he.trans hNE.symm
              · intro he; apply hsw; apply H.injective; exact he.trans hSW.symm
            · intro x hx hmem
              have hn := hescape (H x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
              have ho := houtside _ hn
              have hi := (hopen _).mp hmem
              rw [hG] at hi
              linarith
          obtain ⟨F0, hBim, ha, hb, hwhole⟩ := split hA hB hmeet hJ
          have hin := insideMap hJ F0 hwhole
          have hcl : F0 '' closure (inside (A ∪ B)) = Plane.closedSquare 0 1 := by
            rw [F0.image_closure, hin, ← inside_modelCurve,
              (IsRegionOf.inside modelCurve).closure_eq (jordan_curve_theorem isJordanCurve_modelCurve),
              inside_modelCurve]
            ext x
            simp only [mem_union, mem_openSquare_zero_one, modelCurve, mem_setOf_eq,
              mem_closedSquare_zero_one]
            constructor
            · rintro (h | h) <;> linarith
            · intro h; exact lt_or_eq_of_le h
          have hmarks : ∀ y ∈ P.image F0, y ∉ Plane.closedSquare 0 1 := by
            intro y hy hyclosed
            obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
            rw [← hcl] at hyclosed
            obtain ⟨z,hz,he⟩ := hyclosed
            exact hP x hx (F0.injective he ▸ hz)
          obtain ⟨G, hNE, hSW, hboundary, hfree⟩ := chart (P.image F0) hmarks
          refine ⟨F0.trans G, ?_, ?_, ?_, ?_⟩
          · exact (congrArg G ha).trans hNE
          · exact (congrArg G hb).trans hSW
          · intro x hx hxa hxb
            apply hboundary (F0 x) (hwhole ▸ mem_image_of_mem F0 hx)
            · exact fun he => hxa (F0.injective (he.trans ha.symm))
            · exact fun he => hxb (F0.injective (he.trans hb.symm))
          · intro x hx
            exact hfree (F0 x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
        have hfinite : (f ⁻¹' (M.cover.branch : Set S)).Finite :=
          Set.Finite.preimage hf.injective.injOn M.cover.branch.finite_toSet
        let P : Finset Plane := hfinite.toFinset.filter (fun t => t ≠ p ∧ t ≠ q)
        have hP : ∀ t ∈ P, t ∉ closure (inside (A ∪ B)) := by
          intro t ht hcl
          obtain ⟨htbranch, htp, htq⟩ := Finset.mem_filter.mp ht
          have htbranch : f t ∈ M.cover.branch := hfinite.mem_toFinset.mp htbranch
          rw [(IsRegionOf.inside (A ∪ B)).closure_eq (jordan_curve_theorem hJ)] at hcl
          rcases hcl with hi | hc
          · exact hempty t hi htbranch
          · rcases hboundary t hc htbranch with he | he
            · exact htp he
            · exact htq he
        obtain ⟨F, hp, hq, hin, hout⟩ := chart hA hB hmeet hJ P hP
        let K : Plane ≃ₜ range f := hf.isEmbedding.toHomeomorph
        let e : range f ≃ₜ (univ : Set Plane) :=
          (K.symm.trans F).trans (Homeomorph.Set.univ Plane).symm
        have he (u : range f) : (e u : Plane) = F (K.symm u) := rfl
        have hK (u : range f) : f (K.symm u) = u.val := by
          exact congrArg Subtype.val (K.apply_symm_apply u)
        have imageCoordinate (D : Set Plane) : f '' D =
            {x : S | ∃ u : range f, u.val = x ∧ (e u : Plane) ∈ F '' D} := by
          ext x
          constructor
          · rintro ⟨t,ht,rfl⟩
            refine ⟨K t, rfl, ?_⟩
            rw [he, K.symm_apply_apply]
            exact mem_image_of_mem F ht
          · rintro ⟨u,hux,t,ht,hFt⟩
            refine ⟨t,ht,?_⟩
            rw [he] at hFt
            rw [F.injective hFt, hK, hux]
        have hAi : F '' A \ {F p,F q} ⊆ Plane.openSquare 0 1 := by
          rintro y ⟨⟨t,ht,rfl⟩,hn⟩
          apply hin t (Or.inl ht)
          · intro h; apply hn; simp [h]
          · intro h; apply hn; simp [h]
        have hBi : F '' B \ {F p,F q} ⊆ Plane.openSquare 0 1 := by
          rintro y ⟨⟨t,ht,rfl⟩,hn⟩
          apply hin t (Or.inr ht)
          · intro h; apply hn; simp [h]
          · intro h; apply hn; simp [h]
        have hfp : F p ∈ modelCurve := by rw [hp]; norm_num [modelCurve, Plane.mk, Plane.supNorm]
        have hfq : F q ∈ modelCurve := by rw [hq]; norm_num [modelCurve, Plane.mk, Plane.supNorm]
        obtain ⟨G,himage,houtside,hcoordinate⟩ :=
          CurveComplex.marked_crosscut_surface_replacement S (range f) univ
            hf.isOpenMap.isOpen_range e (subset_univ _)
            (F '' A) (F '' B) (F p) (F q)
            (hA.image_of_injOn (subset_univ _) F.continuous.continuousOn F.injective.injOn)
            (hB.image_of_injOn (subset_univ _) F.continuous.continuousOn F.injective.injOn)
            hfp hfq hAi hBi
        apply Quotient.sound
        refine ⟨G, ?_, ?_⟩
        · intro t x hx
          by_cases hxrange : x ∈ range f
          · apply hcoordinate t ⟨x,hxrange⟩
            rw [he]
            let y := K.symm ⟨x,hxrange⟩
            have hybranch : f y ∈ M.cover.branch := by rw [hK]; exact hx
            change F y ∉ Plane.openSquare 0 1
            by_cases hyp : y = p
            · rw [hyp,hp]; norm_num [Plane.openSquare, Plane.supDist, Plane.supNorm, Plane.mk]
            by_cases hyq : y = q
            · rw [hyq,hq]; norm_num [Plane.openSquare, Plane.supDist, Plane.supNorm, Plane.mk]
            exact hout y (Finset.mem_filter.mpr ⟨hfinite.mem_toFinset.mpr hybranch,hyp,hyq⟩)
          · exact houtside t x hxrange
        · rw [haImage,hbImage,imageCoordinate,imageCoordinate]
          exact himage
      by_contra hmark
      have hfree : ∀ x ∈ U, x ∉ M.cover.branch := by
        intro x hx hb
        exact hmark ⟨x,hb,hx⟩
      obtain ⟨a,b,hab,hfront,C,hJ,f,hf,heU,hCfront,p,q,A,B,hA,hB,hmeet,hC,haim,hbim⟩ :=
        planar M r hr hd hbad v hc U hU
      let aσ : {w // w ∈ σ} := ⟨a.val, actualEndpointFibre_subset M σ v a.property⟩
      let bσ : {w // w ∈ σ} := ⟨b.val, actualEndpointFibre_subset M σ v b.property⟩
      have habσ : aσ ≠ bσ := by
        intro he
        apply hab
        apply Subtype.ext
        exact congrArg (fun u : {w // w ∈ σ} => u.val) he
      have hdis := hd aσ bσ habσ
      have haim : f '' A = (r aσ).val.image := haim
      have hbim : f '' B = (r bσ).val.image := hbim
      have hpq : p ≠ q := hA.ne
      have branchIntersection (t : Plane) (htA : t ∈ A) (htB : t ∈ B) :
          f t ∈ M.cover.branch := by
        by_contra hn
        have hiA : f t ∈ arcInterior M (r aσ) := ⟨haim ▸ mem_image_of_mem f htA,hn⟩
        have hiB : f t ∈ arcInterior M (r bσ) := ⟨hbim ▸ mem_image_of_mem f htB,hn⟩
        exact Set.disjoint_left.mp hdis hiA hiB
      have hbp := branchIntersection p hA.left_mem hB.left_mem
      have hbq := branchIntersection q hA.right_mem hB.right_mem
      have endpoint {t : Plane} (ht : t ∈ A) (hb : f t ∈ M.cover.branch) :
          f t = (r aσ).val.map 0 ∨ f t = (r aσ).val.map 1 := by
        have hi : f t ∈ (r aσ).val.image := haim ▸ mem_image_of_mem f ht
        obtain ⟨s,hs⟩ := hi
        have hb' : (r aσ).val.map s ∈ M.cover.branch := hs ▸ hb
        rcases (r aσ).val.marked_only_at_ends s hb' with he | he
        · exact Or.inl (by rw [he] at hs; exact hs.symm)
        · exact Or.inr (by rw [he] at hs; exact hs.symm)
      have hfp := endpoint hA.left_mem hbp
      have hfq := endpoint hA.right_mem hbq
      have hneq : f p ≠ f q := fun he => hpq (hf.injective he)
      have pairCoverage {u v c d t : S} (hne : u ≠ v)
          (hu : u = c ∨ u = d) (hv : v = c ∨ v = d)
          (ht : t = c ∨ t = d) : t = u ∨ t = v := by
        rcases hu with hu | hu
        · rcases hv with hv | hv
          · exact False.elim (hne (hu.trans hv.symm))
          · exact ht.elim (fun h => Or.inl (h.trans hu.symm)) (fun h => Or.inr (h.trans hv.symm))
        · rcases hv with hv | hv
          · exact ht.elim (fun h => Or.inr (h.trans hv.symm)) (fun h => Or.inl (h.trans hu.symm))
          · exact False.elim (hne (hu.trans hv.symm))
      have hboundary : ∀ t ∈ A ∪ B, f t ∈ M.cover.branch → t = p ∨ t = q := by
        intro t ht hb
        have hft : f t = f p ∨ f t = f q := by
          have hep : f t = (r aσ).val.map 0 ∨ f t = (r aσ).val.map 1 := by
            rcases ht with ht | ht
            · exact endpoint ht hb
            · have hiB : f t ∈ (r bσ).val.image := hbim ▸ mem_image_of_mem f ht
              obtain ⟨s,hs⟩ := hiB
              have hb' : (r bσ).val.map s ∈ M.cover.branch := hs ▸ hb
              have heB : f t = (r bσ).val.map 0 ∨ f t = (r bσ).val.map 1 := by
                rcases (r bσ).val.marked_only_at_ends s hb' with he | he
                · exact Or.inl (by rw [he] at hs; exact hs.symm)
                · exact Or.inr (by rw [he] at hs; exact hs.symm)
              have hpB := branchIntersection p hA.left_mem hB.left_mem
              have hqB := branchIntersection q hA.right_mem hB.right_mem
              have endsB (u : Plane) (hu : u ∈ B) (hb : f u ∈ M.cover.branch) :
                  f u = (r bσ).val.map 0 ∨ f u = (r bσ).val.map 1 := by
                obtain ⟨s,hs⟩ := (show f u ∈ (r bσ).val.image from hbim ▸ mem_image_of_mem f hu)
                rcases (r bσ).val.marked_only_at_ends s (hs ▸ hb) with he | he
                · exact Or.inl (by rw [he] at hs; exact hs.symm)
                · exact Or.inr (by rw [he] at hs; exact hs.symm)
              have hpb := endsB p hB.left_mem hpB
              have hqb := endsB q hB.right_mem hqB
              have he : f t = f p ∨ f t = f q := by
                exact pairCoverage hneq hpb hqb heB
              rcases he with he | he
              · exact he ▸ hfp
              · exact he ▸ hfq
          exact pairCoverage hneq hfp hfq hep
        exact hft.elim (fun he => Or.inl (hf.injective he)) (fun he => Or.inr (hf.injective he))
      have hempty : ∀ t ∈ inside (A ∪ B), f t ∉ M.cover.branch := by
        intro t ht
        apply hfree (f t)
        rw [heU,hC]
        exact mem_image_of_mem f ht
      have hclass := emptyBigon M (r aσ) (r bσ) f hf A B p q hA hB hmeet
        (hC ▸ hJ) haim.symm hbim.symm hboundary hempty
      rw [hr aσ,hr bσ] at hclass
      exact hab (Subtype.ext hclass)
    simp only [actualObjectFamily, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter] at hO
    rcases hO with ⟨v,⟨hv,hloop⟩,rfl⟩ | ⟨v,⟨hv,hn,hcard⟩,rfl⟩
    · have hc : (classEndpoints M v).card = 1 := hloop
      have hlabel : markedArcEndset (r ⟨v,hv⟩).val = classEndpoints M v :=
        (markedArcEndset_eq_classEndpoints M (r ⟨v,hv⟩)).trans
          (congrArg (classEndpoints M) (hr ⟨v,hv⟩))
      rw [← hlabel] at hc
      have he : (r ⟨v,hv⟩).val.map 0 = (r ⟨v,hv⟩).val.map 1 := by
        by_contra hn
        change ({(r ⟨v,hv⟩).val.map 0,(r ⟨v,hv⟩).val.map 1} : Finset S).card = 1 at hc
        simp [Finset.card_pair hn] at hc
      have hcomponent : IsComplementComponent (r ⟨v,hv⟩).val.image U := by
        rw [← actualObjectTrace_loop M r hv]
        exact hU
      rcases (r ⟨v,hv⟩).property with hne | hessential
      · exact False.elim (hne he)
      · exact hessential U hcomponent
    · exact endpointPositive M r hr hd hbad v hcard U hU
  have budget {S : Type} [DecidableEq S] (P : Finset S) (hcard : P.card = 6)
      (U V : Set S) (hd : Disjoint U V)
      (z : S) (hz : z ∈ P) (hzU : z ∉ U) (hzV : z ∉ V) :
      (P.filter (fun x => x ∈ U)).card ≤ 2 ∨
        (P.filter (fun x => x ∈ V)).card ≤ 2 := by
    classical
    let A := P.filter (fun x => x ∈ U)
    let B := P.filter (fun x => x ∈ V)
    have hdAB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact Set.disjoint_left.mp hd (Finset.mem_filter.mp hxA).2 (Finset.mem_filter.mp hxB).2
    have hsub : A ∪ B ⊆ P.erase z := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxP,hxU⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_erase.mpr ⟨fun he => hzU (he ▸ hxU),hxP⟩
      · obtain ⟨hxP,hxV⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_erase.mpr ⟨fun he => hzV (he ▸ hxV),hxP⟩
    have hbound := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdAB, Finset.card_erase_of_mem hz, hcard] at hbound
    change A.card ≤ 2 ∨ B.card ≤ 2
    omega
  obtain ⟨O,P,U,V,hO,hP,hOU,hPV,hUG,hVG,hfreeU,hfreeV,hUV⟩ :=
    actual_two_disjoint_free_gaps M r hr hd hbad hne
  obtain ⟨v,hv⟩ := hne
  let w : {w // w ∈ σ} := ⟨v,hv⟩
  let z := (r w).val.map 0
  have hz : z ∈ M.cover.branch := (r w).val.start_marked
  have hzG : z ∈ ⋃ w, (r w).val.image := mem_iUnion.mpr ⟨w,⟨0,rfl⟩⟩
  have hzU : z ∉ U := fun h => hUG.2.2.1 h hzG
  have hzV : z ∉ V := fun h => hVG.2.2.1 h hzG
  have lower (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M σ)
      (W : Set S) (hW : IsComplementComponent (actualObjectTrace M r O) W) :
      1 ≤ (M.cover.branch.filter (fun x => x ∈ W)).card := by
    obtain ⟨x,hx,hxW⟩ := positive M r hr hd hbad O hO W hW
    have hn : (M.cover.branch.filter (fun x => x ∈ W)).Nonempty :=
      ⟨x,Finset.mem_filter.mpr ⟨hx,hxW⟩⟩
    exact Finset.one_le_card.mpr hn
  rcases budget M.cover.branch M.cover.branch_card U V hUV z hz hzU hzV with hU | hV
  · exact ⟨O,U,hO,hOU,hUG,hfreeU,lower O hO U hOU,hU⟩
  · exact ⟨P,V,hP,hPV,hVG,hfreeV,lower P hP V hPV,hV⟩
end CurveComplex.HyperellipticModel
