import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Topology.RestrictedLink.HomeomorphismComponentHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.RegionComponentHeaders
import CurveComplexGenusTwo.Dependencies.SpherePort
import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Topology.ArcStraightening
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Convex.Topology
import CurveComplexGenusTwo.Topology.Extraction
import Schoenflies.Subarc
import CurveComplexGenusTwo.Topology.TopologicalArcJoin
namespace CurveComplex.HyperellipticModel
open Set Schoenflies Metric unitInterval
set_option maxHeartbeats 8000000
theorem planar_half_arc_completion {C A : Set Plane} {x q y : Plane} (hC : IsJordanCurve C)
    (hA : IsArcBetween A x q) (hx : x ∈ C) (hy : y ∈ C) (hyx : y ≠ x)
    (hinA : A \ {x} ⊆ inside C) :
    ∃ B : Set Plane, IsArcBetween B q y ∧ A ∩ B = {q} ∧ B \ {y} ⊆ inside C := by
  classical
  have slit {C A : Set Plane} {x q : Plane} (hC : IsJordanCurve C)
      (hA : IsArcBetween A x q) (hx : x ∈ C) (hinA : A \ {x} ⊆ inside C) :
      IsConnected (inside C \ A) := by
    classical
    have slit {S : Type} [TopologicalSpace S] [T2Space S]
        (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
        (a : Interval → S) (ha : Continuous a) (hai : Function.Injective a)
        (h0 : a 0 ∉ range f) (hin : ∀ t : Interval, t ≠ 0 → a t ∈ range f)
        (x : Plane) (hx : f x ∉ range a) :
        IsConnected (range f \ range a) := by
      classical
      have collapse {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
          (f : X → Y) (hf : Topology.IsOpenEmbedding f) :
          ∃ g : Y → OnePoint X, Continuous g ∧
            (∀ x, g (f x) = (x : OnePoint X)) ∧
            (∀ y, y ∉ range f → g y = OnePoint.infty) := by
        classical
        let H := hf.isEmbedding.toHomeomorph
        let g : Y → OnePoint X := fun y => if h : y ∈ range f then
          ((H.symm ⟨y,h⟩ : X) : OnePoint X) else OnePoint.infty
        have hg (x : X) : g (f x) = (x : OnePoint X) := by
          simp [g,H]
        have hout (y : Y) (hy : y ∉ range f) : g y = OnePoint.infty := by
          dsimp only [g]
          rw [dif_neg hy]
        refine ⟨g,?_,hg,hout⟩
        apply continuous_def.mpr
        intro A hA
        by_cases hInf : OnePoint.infty ∈ A
        · let K : Set X := ((↑) : X → OnePoint X) ⁻¹' Aᶜ
          have hK : IsClosed K ∧ IsCompact K := by
            exact (OnePoint.isOpen_iff_of_mem hInf).mp hA
          have he : g ⁻¹' A = (f '' K)ᶜ := by
            ext y
            by_cases hy : y ∈ range f
            · obtain ⟨x,rfl⟩ := hy
              rw [mem_preimage,hg,mem_compl_iff,hf.injective.mem_set_image]
              simp [K]
            · rw [mem_preimage,hout y hy]
              constructor
              · intro _ hmem; exact hy (image_subset_range f K hmem)
              · intro _; exact hInf
          rw [he]
          exact (hK.2.image hf.continuous).isClosed.isOpen_compl
        · have ho : IsOpen (((↑) : X → OnePoint X) ⁻¹' A) :=
            (OnePoint.isOpen_iff_of_notMem hInf).mp hA
          have he : g ⁻¹' A = f '' (((↑) : X → OnePoint X) ⁻¹' A) := by
            ext y
            by_cases hy : y ∈ range f
            · obtain ⟨x,rfl⟩ := hy
              rw [mem_preimage,hg,hf.injective.mem_set_image]
              rfl
            · rw [mem_preimage,hout y hy]
              constructor
              · exact fun h => False.elim (hInf h)
              · exact fun h => False.elim (hy (image_subset_range f _ h))
          rw [he]
          exact hf.isOpenMap _ ho
      have complement {S : Type} [TopologicalSpace S] (esphere : S ≃ₜ CurveComplex.SpherePort.Sphere)
          (α : Interval → S) (hc : Continuous α) (hi : Function.Injective α)
          (p : S) (hp : p ∉ (Set.range α)) : IsConnected ((Set.range α))ᶜ := by
        classical
        letI : T2Space S := esphere.symm.t2Space
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
        let e : OpenPartialHomeomorph S Schoenflies.Plane :=
          esphere.toOpenPartialHomeomorph.trans (stereographic' 2 (esphere p))
        have hsource : e.source = {p}ᶜ := by
          ext x
          simp [e, OpenPartialHomeomorph.trans_source]
        have htarget : e.target = Set.univ := by
          simp [e, OpenPartialHomeomorph.trans_target]
        have hain : ∀ t : Interval, α t ∈ e.source := by
          intro t
          rw [hsource]
          intro ht
          apply hp
          exact Set.mem_singleton_iff.mp ht ▸ (show α t ∈ (Set.range α) from ⟨t, rfl⟩)
        let g : Interval → Schoenflies.Plane := e ∘ α
        have hg : Continuous g :=
          e.continuousOn.comp_continuous hc hain
        have hgi : Function.Injective g := by
          intro t u h
          have heq := e.injOn (hain t) (hain u) h
          exact hi heq
        let f : ℝ → Schoenflies.Plane := g ∘ Set.projIcc 0 1 zero_le_one
        have hf : Continuous f := hg.comp continuous_projIcc
        have hfi : Set.InjOn f (Set.Icc 0 1) := by
          intro t ht u hu h
          have h := hgi h
          simpa [f, Set.projIcc_of_mem, ht, hu] using congrArg Subtype.val h
        have hA : Schoenflies.IsArc (Set.range g) := by
          refine ⟨f, hf.continuousOn, hfi, ?_⟩
          ext y
          constructor
          · rintro ⟨t, ht, rfl⟩
            exact ⟨_, rfl⟩
          · rintro ⟨t, rfl⟩
            refine ⟨t, t.property, ?_⟩
            simp [f, Set.projIcc_of_mem]
        have hconn := Schoenflies.arc_complement hA
        have hsymm : Continuous e.symm := by
          exact continuousOn_univ.mp (htarget ▸ e.continuousOn_symm)
        have himage : e.symm '' (Set.range g)ᶜ = (Set.range α)ᶜ ∩ {p}ᶜ := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            have hys : e.symm y ∈ e.source := e.map_target (htarget ▸ Set.mem_univ y)
            refine ⟨?_, hsource ▸ hys⟩
            rintro ⟨t, ht⟩
            apply hy
            refine ⟨t, ?_⟩
            change e (α t) = y
            rw [ht]
            exact e.right_inv (htarget ▸ Set.mem_univ y)
          · rintro ⟨hx, hxp⟩
            have hxs : x ∈ e.source := hsource.symm ▸ hxp
            refine ⟨e x, ?_, e.left_inv hxs⟩
            rintro ⟨t, ht⟩
            exact hx ⟨t, e.injOn (hain t) hxs ht⟩
        have hpunct : IsConnected ((Set.range α)ᶜ ∩ {p}ᶜ) := by
          rw [← himage]
          exact hconn.image e.symm hsymm.continuousOn
        have hsphere : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
          apply isConnected_sphere _ _ (by norm_num)
          rw [← Module.finrank_eq_rank]
          norm_num
        letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
          isConnected_iff_connectedSpace.mp hsphere
        letI : ConnectedSpace S := connectedSpace_iff_univ.mpr (by
          have hi := isConnected_univ.image esphere.symm esphere.symm.continuous.continuousOn
          simpa only [Set.image_univ, esphere.symm.surjective.range_eq] using hi)
        have hdense : Dense ({p}ᶜ : Set S) := by
          apply dense_compl_singleton_iff_not_open.mpr
          intro hopen
          have hsingle : ({p} : Set S) = Set.univ :=
            (show IsClopen ({p} : Set S) from ⟨isClosed_singleton, hopen⟩).eq_univ ⟨p, rfl⟩
          have hends : α ⟨0, by norm_num⟩ = p := by
            exact Set.mem_singleton_iff.mp (hsingle.symm ▸ Set.mem_univ _)
          exact hp ⟨_, hends⟩
        have hclosed : IsClosed (Set.range α) := by
          exact (isCompact_range hc).isClosed
        have hcl : (Set.range α)ᶜ ⊆ closure ((Set.range α)ᶜ ∩ {p}ᶜ) := by
          simpa only [Set.inter_comm] using hdense.open_subset_closure_inter hclosed.isOpen_compl
        exact hpunct.subset_closure Set.inter_subset_left hcl
      
      
      obtain ⟨g,hgc,hg,hout⟩ := collapse f hf
      let b : Interval → OnePoint Plane := g ∘ a
      have hb0 : b 0 = OnePoint.infty := hout _ h0
      have hbpos (t : Interval) (ht : t ≠ 0) : ∃ y : Plane, a t = f y ∧ b t = (y : OnePoint Plane) := by
        obtain ⟨y,hy⟩ := hin t ht
        exact ⟨y,hy.symm,by change g (a t) = _; rw [← hy,hg]⟩
      have hbi : Function.Injective b := by
        intro t u he
        by_cases ht : t = 0
        · by_cases hu : u = 0
          · exact ht.trans hu.symm
          · obtain ⟨y,hy,hby⟩ := hbpos u hu
            rw [ht,hb0,hby] at he
            exact False.elim (OnePoint.infty_ne_coe y he)
        · by_cases hu : u = 0
          · obtain ⟨y,hy,hby⟩ := hbpos t ht
            rw [hu,hb0,hby] at he
            exact False.elim (OnePoint.coe_ne_infty y he)
          · obtain ⟨y,hy,hby⟩ := hbpos t ht
            obtain ⟨z,hz,hbz⟩ := hbpos u hu
            rw [hby,hbz] at he
            have hyz := OnePoint.coe_injective he
            apply hai
            rw [hy,hz,hyz]
      have hxb : (x : OnePoint Plane) ∉ range b := by
        rintro ⟨t,ht⟩
        by_cases ht0 : t = 0
        · rw [ht0,hb0] at ht
          exact OnePoint.infty_ne_coe x ht
        · obtain ⟨y,hy,hby⟩ := hbpos t ht0
          rw [hby] at ht
          have hyx := OnePoint.coe_injective ht
          exact hx ⟨t,hy.trans (congrArg f hyx)⟩
      let H : OnePoint Plane ≃ₜ CurveComplex.SpherePort.Sphere :=
        onePointEquivSphereOfFinrankEq (by simp)
      have hc := complement H b (hgc.comp ha) hbi (x : OnePoint Plane) hxb
      let K : Set Plane := {y | (y : OnePoint Plane) ∉ range b}
      have hKimage : ((↑) : Plane → OnePoint Plane) '' K = (range b)ᶜ := by
        ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          exact hz
        · intro hy
          cases y using OnePoint.rec with
          | infty => exact False.elim (hy ⟨0,hb0⟩)
          | coe z => exact ⟨z,hy,rfl⟩
      have hcK : IsConnected K := by
        rw [← hKimage] at hc
        exact ⟨Set.image_nonempty.mp hc.nonempty,
          OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp hc.isPreconnected⟩
      have htarget : f '' K = range f \ range a := by
        ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          refine ⟨⟨z,rfl⟩,?_⟩
          rintro ⟨t,ht⟩
          apply hz
          refine ⟨t,?_⟩
          change g (a t) = (z : OnePoint Plane)
          rw [ht,hg]
        · rintro ⟨⟨z,rfl⟩,hn⟩
          refine ⟨z,?_,rfl⟩
          rintro ⟨t,ht⟩
          by_cases ht0 : t = 0
          · rw [ht0,hb0] at ht
            exact OnePoint.infty_ne_coe z ht
          · obtain ⟨u,hu,hbu⟩ := hbpos t ht0
            rw [hbu] at ht
            exact hn ⟨t,hu.trans (congrArg f (OnePoint.coe_injective ht))⟩
      rw [← htarget]
      exact hcK.image f hf.continuous.continuousOn
    have disc {C : Set Plane} (hC : IsJordanCurve C) : Nonempty (Plane ≃ₜ inside C) := by
      have straight {C : Set Plane} (hC : IsJordanCurve C) :
        ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
      
        classical
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
        obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
        obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
        have him : F '' C = modelCurve := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            rw [hF ⟨y, hy⟩]
            exact (e ⟨y, hy⟩).property
          · intro hx
            let y := e.symm ⟨x, hx⟩
            refine ⟨y.val, y.property, ?_⟩
            rw [hF y]
            exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
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
        exact ⟨F, him, heinside.trans inside_modelCurve⟩
      have square : Nonempty (Plane ≃ₜ Plane.openSquare 0 1) := by
      
        let H : Plane ≃ₜ (Fin 2 → ℝ) := (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
        let B : (Fin 2 → ℝ) ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := Homeomorph.unitBall
        let K : Metric.ball (0 : Fin 2 → ℝ) 1 ≃ₜ Plane.openSquare 0 1 :=
          H.symm.subtype (fun x => by
            simp only [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)]
            change (∀ i : Fin 2, ‖x i‖ < 1) ↔ (H.symm x).supDist 0 < 1
            simp [Schoenflies.Plane.supDist, Schoenflies.Plane.supNorm, Fin.forall_fin_two, H, EuclideanSpace.equiv,
              PiLp.toLp_apply, Real.norm_eq_abs])
        exact ⟨(H.trans B).trans K⟩
      obtain ⟨F, _, hFI⟩ := straight hC
      obtain ⟨H⟩ := square
      let R : inside C ≃ₜ Plane.openSquare 0 1 :=
        (F.isEmbedding.homeomorphImage (inside C)).trans (Homeomorph.setCongr hFI)
      exact ⟨H.trans R.symm⟩
    have hAkeep := hA
    obtain ⟨k,hkc,hki,hkim,hk0,hk1⟩ := hA
    let a : Interval → Plane := fun t => k t.val
    have hac : Continuous a := continuousOn_iff_continuous_restrict.mp hkc
    have hai : Function.Injective a := by
      intro t u he
      exact Subtype.ext (hki t.property u.property he)
    have ha0 : a 0 = x := hk0
    have haImage : range a = A := by
      rw [← hkim]
      ext y
      constructor
      · rintro ⟨t,rfl⟩; exact ⟨t.val,t.property,rfl⟩
      · rintro ⟨t,ht,rfl⟩; exact ⟨⟨t,ht⟩,rfl⟩
    have h0 : a 0 ∉ inside C := by rw [ha0]; exact fun h => inside_subset_compl h hx
    have hin : ∀ t : Interval, t ≠ 0 → a t ∈ inside C := by
      intro t ht
      apply hinA
      refine ⟨haImage ▸ mem_range_self t,?_⟩
      intro he
      have he : a t = x := Set.mem_singleton_iff.mp he
      exact ht (hai (he.trans ha0.symm))
    obtain ⟨Q,hQ,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hAkeep
    have hsep := jordan_curve_theorem hJ
    have hndJ : IsNowhereDense (Q ∪ A) := by
      rw [← hsep.frontier_inside]
      change interior (closure (frontier (inside (Q ∪ A)))) = ∅
      rw [isClosed_frontier.closure_eq, ← frontier_compl]
      exact interior_frontier hsep.isOpen_inside.isClosed_compl
    have hndA := hndJ.mono (Set.subset_union_right : A ⊆ Q ∪ A)
    have hDopen := (jordan_curve_theorem hC).isOpen_inside
    obtain ⟨z,hz,hzA⟩ : ∃ z ∈ inside C, z ∉ A := by
      by_contra hn
      push_neg at hn
      have hs : inside C ⊆ closure A := fun z hz => subset_closure (hn z hz)
      have hi : inside C ⊆ interior (closure A) := hDopen.interior_eq ▸ interior_mono hs
      obtain ⟨z,hz⟩ := (jordan_curve_theorem hC).isConnected_inside.nonempty
      rw [show interior (closure A) = ∅ from hndA] at hi
      exact hi hz
    obtain ⟨H⟩ := disc hC
    let f : Plane → Plane := fun z => (H z).val
    have hf : Topology.IsOpenEmbedding f := hDopen.isOpenEmbedding_subtypeVal.comp H.isOpenEmbedding
    have hrange : range f = inside C := by
      ext y
      constructor
      · rintro ⟨t,rfl⟩; exact (H t).property
      · intro hy
        exact ⟨H.symm ⟨y,hy⟩,congrArg Subtype.val (H.apply_symm_apply ⟨y,hy⟩)⟩
    let u := H.symm ⟨z,hz⟩
    have hfu : f u = z := congrArg Subtype.val (H.apply_symm_apply ⟨z,hz⟩)
    have hc := slit f hf a hac hai (hrange.symm ▸ h0)
      (fun t ht => hrange.symm ▸ hin t ht) u (by rw [hfu,haImage]; exact hzA)
    simpa only [hrange,haImage] using hc
  have radial {C : Set Plane} (hC : IsJordanCurve C) {x q : Plane}
      (hx : x ∈ C) (hq : q ∈ inside C) :
      ∃ A : Set Plane, IsArcBetween A x q ∧ A \ {x} ⊆ inside C := by
    classical
    have chart {C : Set Plane} (hC : IsJordanCurve C) :
        ∃ F : Plane ≃ₜ Plane, F '' C = modelCurve ∧ F '' inside C = Plane.openSquare 0 1 := by
      classical
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
      obtain ⟨e⟩ := hC.homeomorph isJordanCurve_modelCurve
      obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hC isJordanCurve_modelCurve e
      have him : F '' C = modelCurve := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          rw [hF ⟨y, hy⟩]
          exact (e ⟨y, hy⟩).property
        · intro hx
          let y := e.symm ⟨x, hx⟩
          refine ⟨y.val, y.property, ?_⟩
          rw [hF y]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
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
      exact ⟨F, him, heinside.trans inside_modelCurve⟩
    obtain ⟨F,himage,hin⟩ := chart hC
    have hFx : F x ∈ modelCurve := himage ▸ mem_image_of_mem F hx
    have hFq : F q ∈ Plane.openSquare 0 1 := hin ▸ mem_image_of_mem F hq
    have hxy : F x ≠ F q := by
      intro he
      have h1 : Plane.supNorm (F x) = 1 := hFx
      have h2 : Plane.supNorm (F q) < 1 := mem_openSquare_zero_one.mp hFq
      rw [he] at h1
      linarith
    let l : ℝ → Plane := fun t => F x + t • (F q - F x)
    have hl : l = AffineMap.lineMap (F x) (F q) := by
      ext t
      simp [l,AffineMap.lineMap_apply_module]
      <;> ring
    have hli : Function.Injective l := hl ▸ AffineMap.lineMap_injective ℝ hxy
    have hinside (t : ℝ) (ht : t ∈ Ioc (0:ℝ) 1) : l t ∈ Plane.openSquare 0 1 := by
      have h := (Plane.convex_closedSquare 0 1).add_smul_sub_mem_interior
        (modelCurve_subset_closedSquare hFx)
        (show F q ∈ interior (Plane.closedSquare 0 1) by rw [interior_closedSquare_zero_one]; exact hFq) ht
      rwa [interior_closedSquare_zero_one] at h
    let a : ℝ → Plane := fun t => F.symm (l t)
    have hac : Continuous a := F.symm.continuous.comp (by dsimp [l]; fun_prop)
    have hai : Function.Injective a := F.symm.injective.comp hli
    have ha0 : a 0 = x := by simp [a,l]
    have ha1 : a 1 = q := by simp [a,l]
    refine ⟨a '' I,⟨a,hac.continuousOn,hai.injOn,rfl,ha0,ha1⟩,?_⟩
    rintro z ⟨⟨t,ht,rfl⟩,hn⟩
    have ht0 : t ≠ 0 := by
      intro he
      apply hn
      simp [he,ha0]
    have hti : t ∈ Ioc (0:ℝ) 1 := ⟨lt_of_le_of_ne' ht.1 ht0,ht.2⟩
    have hh : l t ∈ F '' inside C := hin.symm ▸ hinside t hti
    obtain ⟨z,hz,he⟩ := hh
    change F.symm (l t) ∈ inside C
    simpa [← he] using hz
  have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
      (hU : IsOpen U) (ha : a ∈ U) :
      ∃ B : Set Plane, ∃ c : Plane,
        IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
    obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
    let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
    have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
    have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
    have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
    let d := min (ε/2) (1/2:ℝ)
    have hd : 0 < d := lt_min (by linarith) (by norm_num)
    have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
    have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdmem : d ∈ I := ⟨hd.le,hd1⟩
    have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
    refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
    · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
    · rw [← himage]
      exact image_mono hsubI
    · rintro y ⟨t,ht,rfl⟩
      have htc := hsubI ht
      have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
      have hbt : t ∈ Metric.ball (0:ℝ) ε := by
        rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
        exact lt_of_le_of_lt ht'.2 hdε
      have hm := hball hbt
      change g t ∈ U at hm
      simpa only [g,projIcc_of_mem zero_le_one htc] using hm
  have access {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
      (hU : IsOpen U) (ha : a ∈ U) :
      ∃ B : Set Plane, ∃ c : Plane,
        IsArcBetween B a c ∧ B ⊆ U ∧ c ∉ A ∧ B \ {a} ⊆ Aᶜ := by
    have small {A U : Set Plane} {a b : Plane} (hA : IsArcBetween A a b)
        (hU : IsOpen U) (ha : a ∈ U) :
        ∃ B : Set Plane, ∃ c : Plane,
          IsArcBetween B a c ∧ B ⊆ A ∧ B ⊆ U := by
      obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hA
      let g : ℝ → Plane := fun t => f (projIcc 0 1 zero_le_one t)
      have hg : Continuous g := (continuousOn_iff_continuous_restrict.mp hf).comp continuous_projIcc
      have hg0 : g 0 = a := by simp [g,projIcc_of_mem zero_le_one (by norm_num : (0:ℝ) ∈ Icc 0 1),hf0]
      have hn : g ⁻¹' U ∈ nhds (0:ℝ) := hg.continuousAt.preimage_mem_nhds (hg0.symm ▸ hU.mem_nhds ha)
      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hn
      let d := min (ε/2) (1/2:ℝ)
      have hd : 0 < d := lt_min (by linarith) (by norm_num)
      have hd1 : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
      have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hdmem : d ∈ I := ⟨hd.le,hd1⟩
      have hsubI : uIcc (0:ℝ) d ⊆ I := uIcc_subset_I (by norm_num) hdmem
      refine ⟨f '' uIcc (0:ℝ) d,f d,?_,?_,?_⟩
      · simpa only [hf0] using isArcBetween_subarc_of_injOn_I hf hi (by norm_num) hdmem (ne_of_lt hd)
      · rw [← himage]
        exact image_mono hsubI
      · rintro y ⟨t,ht,rfl⟩
        have htc := hsubI ht
        have ht' : 0 ≤ t ∧ t ≤ d := by simpa [uIcc_of_le hd.le] using ht
        have hbt : t ∈ Metric.ball (0:ℝ) ε := by
          rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg ht'.1]
          exact lt_of_le_of_lt ht'.2 hdε
        have hm := hball hbt
        change g t ∈ U at hm
        simpa only [g,projIcc_of_mem zero_le_one htc] using hm
    obtain ⟨E,u,hE,hu,havoid⟩ := endpoint_access_of_isArcBetween hA
    obtain ⟨B,c,hB,hBE,hBU⟩ := small hE hU ha
    refine ⟨B,c,hB,hBU,?_,?_⟩
    · exact havoid ⟨hBE hB.right_mem,fun he => hB.ne (Set.mem_singleton_iff.mp he).symm⟩
    · intro x hx
      exact havoid ⟨hBE hx.1,hx.2⟩
  have hqD : q ∈ inside C := hinA ⟨hA.right_mem,fun he => hA.ne (Set.mem_singleton_iff.mp he).symm⟩
  have hyA : y ∉ A := by
    intro hya
    have hyD := hinA ⟨hya,fun he => hyx (Set.mem_singleton_iff.mp he)⟩
    exact inside_subset_compl hyD hy
  have hyq : y ≠ q := fun he => inside_subset_compl hqD (he ▸ hy)
  have hDopen := (jordan_curve_theorem hC).isOpen_inside
  obtain ⟨R,hR,hRinside⟩ := radial hC hy hqD
  obtain ⟨Y,u,hY,hYR,hYavoid⟩ := small hR hA.isArc.isClosed.isOpen_compl hyA
  have huD : u ∈ inside C := hRinside ⟨hYR hY.right_mem,
    fun he => hY.ne (Set.mem_singleton_iff.mp he).symm⟩
  have huA : u ∉ A := hYavoid hY.right_mem
  obtain ⟨Q,v,hQ,hQD,hvA,hQavoid⟩ := access hA.reverse hDopen hqD
  have hvD : v ∈ inside C := hQD hQ.right_mem
  have hslit : IsConnected (inside C \ A) := slit hC hA hx hinA
  have hopen : IsOpen (inside C \ A) := hDopen.sdiff hA.isArc.isClosed
  have hjoin : ∃ B : Set Plane, IsArcBetween B y q ∧
      B \ {q} ⊆ Aᶜ ∧ B \ {y} ⊆ inside C := by
    by_cases huv : u = v
    · obtain ⟨B,hBsub,hB⟩ := exists_arc_in_union_of_arcs hY (huv ▸ hQ.reverse) hyq
      refine ⟨B,hB,?_,?_⟩
      · intro z hz
        rcases hBsub hz.1 with hzY | hzQ
        · exact hYavoid hzY
        · exact hQavoid ⟨hzQ,hz.2⟩
      · intro z hz
        rcases hBsub hz.1 with hzY | hzQ
        · exact hRinside ⟨hYR hzY,hz.2⟩
        · exact hQD hzQ
    · obtain ⟨P,hPsub,hPpoly,hP⟩ := exists_simple_arc_of_isPreconnected hopen hslit.isPreconnected
        ⟨huD,huA⟩ ⟨hvD,hvA⟩ huv
      have hyv : y ≠ v := fun he => inside_subset_compl hvD (he ▸ hy)
      obtain ⟨Z,hZsub,hZ⟩ := exists_arc_in_union_of_arcs hY hP hyv
      obtain ⟨B,hBsub,hB⟩ := exists_arc_in_union_of_arcs hZ hQ.reverse hyq
      refine ⟨B,hB,?_,?_⟩
      · intro z hz
        rcases hBsub hz.1 with hzZ | hzQ
        · rcases hZsub hzZ with hzY | hzP
          · exact hYavoid hzY
          · exact (hPsub hzP).2
        · exact hQavoid ⟨hzQ,hz.2⟩
      · intro z hz
        rcases hBsub hz.1 with hzZ | hzQ
        · rcases hZsub hzZ with hzY | hzP
          · exact hRinside ⟨hYR hzY,hz.2⟩
          · exact (hPsub hzP).1
        · exact hQD hzQ
  obtain ⟨B,hB,havoid,hBD⟩ := hjoin
  refine ⟨B,hB.reverse,?_,hBD⟩
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hn
    exact havoid ⟨hz.2,hn⟩ hz.1
  · rintro z hz
    have he : z = q := Set.mem_singleton_iff.mp hz
    subst z
    exact ⟨hA.right_mem,hB.right_mem⟩
end CurveComplex.HyperellipticModel
