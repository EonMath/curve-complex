import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
import CurveComplexGenusTwo.Filtration.Geometry.CurveJordanBridge
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualJordanInsideChartHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.OpenEmbeddingFaceHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.HomeomorphismComponentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ParallelBoundaryDescentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RegionComponentHeaders
import CurveComplexGenusTwo.Topology.ArcStraightening
namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualObjectGapChartHeaders_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
set_option maxHeartbeats 4000000
theorem actual_object_gap_marked_inside_chart (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
    (r : {w // w ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
    (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
    (hbad : badVertices (actualArcLabels M) σ = σ)
    (O : Finset (EssentialArcClass M)) (hO : O ∈ actualObjectFamily M σ)
    (U : Set S) (hU : IsComplementComponent (actualObjectTrace M r O) U) :
    ∃ C : Set Plane, IsJordanCurve C ∧ ∃ f : Plane → S,
      Topology.IsOpenEmbedding f ∧ U = f '' inside C ∧
      ∃ z ∈ C, f z ∈ M.cover.branch := by
  classical
  have loopChart (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
      (r : {w // w ∈ σ} → EssentialMarkedArc M)
      (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
      (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
      (hbad : badVertices (actualArcLabels M) σ = σ)
      (v : {w // w ∈ σ}) (hloop : (r v).val.map 0 = (r v).val.map 1)
      (U : Set S) (hU : IsComplementComponent (r v).val.image U) :
      ∃ C : Set Plane, IsJordanCurve C ∧ ∃ f : Plane → S,
        Topology.IsOpenEmbedding f ∧ U = f '' inside C ∧ f '' C = (r v).val.image := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let c : CurveComplex.SpherePort.JordanCurve := {
      map := M.sphere ∘ (r v).val.map
      continuous := M.sphere.continuous.comp (r v).val.continuous
      injective_except_ends := fun t u h => (r v).val.injective_except_loop_closure t u (M.sphere.injective h)
      closed := congrArg M.sphere hloop }
    have hcimage : c.image = M.sphere '' (r v).val.image := by
      change range (M.sphere ∘ (r v).val.map) = M.sphere '' range (r v).val.map
      exact range_comp _ _
    have hcg : c.image ⊆ M.sphere '' (⋃ w, (r w).val.image) := by
      rw [hcimage]
      exact image_mono (subset_iUnion (fun w => (r w).val.image) v)
    have hW := homeomorphism_complement_component M.sphere hU
    rw [← hcimage] at hW
    obtain ⟨P,hP,hinside⟩ := actual_graph_avoiding_jordan_inside_chart M r hr hd hbad c hcg
      (M.sphere '' U) hW
    let C := P.planeImage c
    let f : Plane → S := fun t => M.sphere.symm (P.plane.symm t).val
    have hf : Topology.IsOpenEmbedding f := M.sphere.symm.isOpenEmbedding.comp
      (isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp P.plane.symm.isOpenEmbedding)
    have heU : U = f '' inside C := by
      apply (Set.image_injective.mpr M.sphere.injective)
      rw [image_image]
      simpa [f,C] using hinside
    have heC : f '' C = (r v).val.image := by
      apply (Set.image_injective.mpr M.sphere.injective)
      rw [image_image, ← hcimage]
      ext y
      constructor
      · rintro ⟨t,ht,rfl⟩
        obtain ⟨b,hb,hbt⟩ := ht
        simp only [f,Homeomorph.apply_symm_apply]
        rw [← hbt,P.plane.symm_apply_apply]
        exact hb
      · intro hy
        have hyn : y ≠ P.puncture := fun he => P.avoids (he ▸ hy)
        let b : {x : CurveComplex.SpherePort.Sphere // x ≠ P.puncture} := ⟨y,hyn⟩
        refine ⟨P.plane b,⟨b,hy,rfl⟩,?_⟩
        simp [f,b]
    exact ⟨C,CurveComplex.SpherePort.chart_image_jordan c P,f,hf,heU,heC⟩
  have endpointChart (M : HyperellipticModel E S) {σ : Finset (EssentialArcClass M)}
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
  simp only [actualObjectFamily,Finset.mem_union,Finset.mem_image,Finset.mem_filter] at hO
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
    obtain ⟨C,hJ,f,hf,heU,heC⟩ := loopChart M r hr hd hbad ⟨v,hv⟩ he U hcomponent
    have hz : (r ⟨v,hv⟩).val.map 0 ∈ f '' C := heC.symm ▸ ⟨0,rfl⟩
    obtain ⟨z,hz,hez⟩ := hz
    exact ⟨C,hJ,f,hf,heU,z,hz,hez.symm ▸ (r ⟨v,hv⟩).val.start_marked⟩
  · obtain ⟨a,b,hab,hfront,C,hJ,f,hf,heU,hCfront,p,q,A,B,hA,hB,hmeet,hC,haim,hbim⟩ :=
      endpointChart M r hr hd hbad v hcard U hU
    let aσ : {w // w ∈ σ} := ⟨a.val,actualEndpointFibre_subset M σ v a.property⟩
    have hz : (r aσ).val.map 0 ∈ f '' A := haim.symm ▸ ⟨0,rfl⟩
    obtain ⟨z,hz,hez⟩ := hz
    refine ⟨C,hJ,f,hf,heU,z,?_,hez.symm ▸ (r aσ).val.start_marked⟩
    rw [hC]
    exact Or.inl hz
end CurveComplex.HyperellipticModel
