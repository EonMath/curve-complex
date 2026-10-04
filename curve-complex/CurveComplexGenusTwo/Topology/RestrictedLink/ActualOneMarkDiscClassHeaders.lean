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
import Schoenflies.MatchedArc
import Schoenflies.Topology
import CurveComplexGenusTwo.Topology.CrosscutFull
import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import Mathlib.Analysis.Convex.Basic
import CurveComplexGenusTwo.Topology.ChartLift
namespace CurveComplex.HyperellipticModel
open Schoenflies Metric Set unitInterval
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 24000000
theorem actual_one_mark_disc_class (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
    (C A B : Set Plane) (x q : Plane) (hC : IsJordanCurve C)
    (hA : IsArcBetween A x q) (hB : IsArcBetween B x q)
    (hx : x ∈ C) (hq : q ∈ inside C)
    (hAi : A \ {x} ⊆ inside C) (hBi : B \ {x} ⊆ inside C)
    (haImage : a.val.image = f '' A) (hbImage : b.val.image = f '' B)
    (hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = q) :
    Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b := by
  classical
  have classes (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
      (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
      (A B : Set Plane) (x q : Plane)
      (hA : IsArcBetween A x q) (hB : IsArcBetween B x q)
      (hx : x ∈ modelCurve)
      (hq : q ∈ Plane.openSquare 0 1)
      (hAi : A \ {x} ⊆ Plane.openSquare 0 1)
      (hBi : B \ {x} ⊆ Plane.openSquare 0 1)
      (haImage : a.val.image = f '' A) (hbImage : b.val.image = f '' B)
      (hmarks : ∀ z ∈ Plane.openSquare 0 1, f z ∈ M.cover.branch → z = q) :
      Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    have isotopy {A B : Set Plane} {x q y : Plane}
        (hA : IsArcBetween A x q) (hB : IsArcBetween B x q)
        (hx : x ∈ modelCurve) (hy : y ∈ modelCurve) (hyx : y ≠ x)
        (hq : q ∈ Plane.openSquare 0 1)
        (hAi : A \ {x} ⊆ Plane.openSquare 0 1)
        (hBi : B \ {x} ⊆ Plane.openSquare 0 1) :
        ∃ H : CurveComplex.AmbientIsotopy Plane, H.finalMap '' A = B ∧
          (∀ t z, z ∉ Plane.openSquare 0 1 → H.map (t,z) = z) ∧
          (∀ t, H.map (t,q) = q) := by
      have completion {C A : Set Plane} {x q y : Plane} (hC : IsJordanCurve C)
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
      have glue {A P B Q : Set Plane} {a q b c r d : Plane}
          (hA : IsArcBetween A a q) (hP : IsArcBetween P q b)
          (hB : IsArcBetween B c r) (hQ : IsArcBetween Q r d)
          (hsrc : A ∩ P = {q}) (htgt : B ∩ Q = {r}) :
          ∃ h : ArcHomeo (A ∪ P) (B ∪ Q) a b c d,
            h.toFun q = r ∧ h.toFun '' A = B := by
        classical
        obtain ⟨eA⟩ := exists_arcHomeo hA hB
        obtain ⟨eP⟩ := exists_arcHomeo hP hQ
        let f : Plane → Plane := fun x => if x ∈ A then eA.toFun x else eP.toFun x
        let g : Plane → Plane := fun x => if x ∈ B then eA.invFun x else eP.invFun x
        have fA : ∀ x ∈ A, f x = eA.toFun x := by intros; simp_all [f]
        have fP : ∀ x ∈ P, f x = eP.toFun x := by
          intro x hx
          by_cases ha : x ∈ A
          · have he : x = q := by simpa only [mem_singleton_iff] using (show x ∈ ({q} : Set Plane) from hsrc ▸ (show x ∈ A ∩ P from ⟨ha,hx⟩))
            subst x
            simp [f, hA.right_mem, eA.map_right, eP.map_left]
          · simp [f, ha]
        have gB : ∀ x ∈ B, g x = eA.invFun x := by intros; simp_all [g]
        have gQ : ∀ x ∈ Q, g x = eP.invFun x := by
          intro x hx
          by_cases hb : x ∈ B
          · have he : x = r := by simpa only [mem_singleton_iff] using (show x ∈ ({r} : Set Plane) from htgt ▸ (show x ∈ B ∩ Q from ⟨hb,hx⟩))
            subst x
            have ea : eA.invFun r = q := (congrArg eA.invFun eA.map_right.symm).trans (eA.leftInvOn hA.right_mem)
            have ep : eP.invFun r = q := (congrArg eP.invFun eP.map_left.symm).trans (eP.leftInvOn hP.left_mem)
            simp [g, hB.right_mem, ea, ep]
          · simp [g, hb]
        have fc : ContinuousOn f (A ∪ P) :=
          Plane.continuousOn_union_of_isClosed hA.isArc.isCompact.isClosed hP.isArc.isCompact.isClosed
            (eA.continuousOn_toFun.congr fA) (eP.continuousOn_toFun.congr fP)
        have gc : ContinuousOn g (B ∪ Q) :=
          Plane.continuousOn_union_of_isClosed hB.isArc.isCompact.isClosed hQ.isArc.isCompact.isClosed
            (eA.continuousOn_invFun.congr gB) (eP.continuousOn_invFun.congr gQ)
        have li : LeftInvOn g f (A ∪ P) := by
          intro x hx
          rcases hx with ha | hp
          · rw [fA x ha, gB _ (eA.mapsTo ha)]; exact eA.leftInvOn ha
          · rw [fP x hp, gQ _ (eP.mapsTo hp)]; exact eP.leftInvOn hp
        have ri : RightInvOn g f (B ∪ Q) := by
          intro x hx
          rcases hx with hb | hq
          · rw [gB x hb, fA _ (eA.mapsTo_invFun hb)]; exact eA.rightInvOn hb
          · rw [gQ x hq, fP _ (eP.mapsTo_invFun hq)]; exact eP.rightInvOn hq
        have imA : f '' A = B := by
          calc
            f '' A = eA.toFun '' A := image_congr fA
            _ = B := eA.image_eq
        have imP : f '' P = Q := by
          calc
            f '' P = eP.toFun '' P := image_congr fP
            _ = Q := eP.image_eq
        refine ⟨{ toFun := f
                  invFun := g
                  continuousOn_toFun := fc
                  continuousOn_invFun := gc
                  leftInvOn := li
                  rightInvOn := ri
                  image_eq := ?_
                  map_left := ?_
                  map_right := ?_ }, ?_, imA⟩
        · rw [image_union, imA, imP]
        · exact (fA _ hA.left_mem).trans eA.map_left
        · exact (fP _ hP.right_mem).trans eP.map_right
        · exact (fA _ hA.right_mem).trans eA.map_right
      have prescribed
          (A B : Set Plane) (a b : Plane)
          (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
          (h : ArcHomeo A B a b a b)
          (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
          (hAi : A \ {a, b} ⊆ Plane.openSquare 0 1)
          (hBi : B \ {a, b} ⊆ Plane.openSquare 0 1) :
          ∃ F : Plane ≃ₜ Plane,
            F '' A = B ∧ (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
            EqOn F h.toFun A := by
        classical
        obtain ⟨R₁, R₂, hcut⟩ := exists_isCutPair isJordanCurve_modelCurve ha hb hA.ne
        obtain ⟨F₁, G₁, h₁, hF₁fixed, hF₁arc, hF₁image⟩ :=
          exists_closed_subdisk_homeomorph_fixing_arc hcut.fst hA hB
            (model_boundary_arc_meet_crosscut hcut.fst hcut.fst_subset hA hAi)
            (model_boundary_arc_meet_crosscut hcut.fst hcut.fst_subset hB hBi) h
        obtain ⟨F₂, G₂, h₂, hF₂fixed, hF₂arc, hF₂image⟩ :=
          exists_closed_subdisk_homeomorph_fixing_arc hcut.snd hA hB
            (model_boundary_arc_meet_crosscut hcut.snd hcut.snd_subset hA hAi)
            (model_boundary_arc_meet_crosscut hcut.snd hcut.snd_subset hB hBi) h
        have closed {R P : Set Plane} {a b : Plane}
            (hR : IsArcBetween R a b) (hP : IsArcBetween P a b)
            (hRP : R ∩ P = {a,b}) : IsClosed ((R ∪ P) ∪ inside (R ∪ P)) := by
          have hJ : IsJordanCurve (R ∪ P) := by
            apply isJordanCurve_union hR hP
            intro x hxR hxP
            have hx : x ∈ ({a,b} : Set Plane) := hRP ▸ ⟨hxR,hxP⟩
            simpa using hx
          exact isClosed_union_inside (jordan_curve_theorem hJ)
        let D₁ : Set Plane := (R₁ ∪ A) ∪ inside (R₁ ∪ A)
        let D₂ : Set Plane := (R₂ ∪ A) ∪ inside (R₂ ∪ A)
        let E₁ : Set Plane := (R₁ ∪ B) ∪ inside (R₁ ∪ B)
        let E₂ : Set Plane := (R₂ ∪ B) ∪ inside (R₂ ∪ B)
        let S : Set Plane := Plane.closedSquare 0 1
        have hpartA : D₁ ∪ D₂ = S ∧ D₁ ∩ D₂ = A :=
          square_crosscut_subdisk_partition hA hcut hAi
        have hpartB : E₁ ∪ E₂ = S ∧ E₁ ∩ E₂ = B :=
          square_crosscut_subdisk_partition hB hcut hBi
        have hR₁A := model_boundary_arc_meet_crosscut hcut.fst
          hcut.fst_subset hA hAi
        have hR₂A := model_boundary_arc_meet_crosscut hcut.snd
          hcut.snd_subset hA hAi
        have hR₁B := model_boundary_arc_meet_crosscut hcut.fst
          hcut.fst_subset hB hBi
        have hR₂B := model_boundary_arc_meet_crosscut hcut.snd
          hcut.snd_subset hB hBi
        have hD₁ : IsClosed D₁ := closed hcut.fst hA hR₁A
        have hD₂ : IsClosed D₂ := closed hcut.snd hA hR₂A
        have hE₁ : IsClosed E₁ := closed hcut.fst hB hR₁B
        have hE₂ : IsClosed E₂ := closed hcut.snd hB hR₂B
        have hagree : ∀ x ∈ D₁ ∩ D₂, F₁ x = F₂ x := by
          intro x hx
          have hxA : x ∈ A := hpartA.2 ▸ hx
          rw [hF₁arc x hxA, hF₂arc x hxA]
        have himageOverlap : F₁ '' (D₁ ∩ D₂) = E₁ ∩ E₂ := by
          rw [hpartA.2, hpartB.2]
          exact hF₁image
        obtain ⟨F, G, hFG, hFD₁, hFD₂⟩ :=
          glue_closed_homeoOn hD₁ hD₂ hE₁ hE₂ h₁ h₂ hagree himageOverlap
        have hFGS : IsHomeoOn F G S S := by
          simpa only [hpartA.1, hpartB.1] using hFG
        let E : S ≃ S := {
          toFun := fun x => ⟨F x, hFGS.mapsTo x.property⟩
          invFun := fun y => ⟨G y, hFGS.mapsTo_inv y.property⟩
          left_inv := by
            intro x
            apply Subtype.ext
            exact hFGS.invOn.1 x.property
          right_inv := by
            intro y
            apply Subtype.ext
            exact hFGS.invOn.2 y.property }
        let e : S ≃ₜ S := {
          toEquiv := E
          continuous_toFun := hFGS.continuousOn.domRestrict.subtype_mk _
          continuous_invFun := hFGS.continuousOn_inv.domRestrict.subtype_mk _ }
        have hboundary : ∀ x : S, (x : Plane) ∈ modelCurve → e x = x := by
          intro x hxC
          have hxR : (x : Plane) ∈ R₁ ∪ R₂ := hcut.union_eq.symm ▸ hxC
          apply Subtype.ext
          rcases hxR with hxR₁ | hxR₂
          · exact (hFD₁ x (Or.inl (Or.inl hxR₁))).trans (hF₁fixed x hxR₁)
          · exact (hFD₂ x (Or.inl (Or.inl hxR₂))).trans (hF₂fixed x hxR₂)
        have hFA : F '' A = B := by
          have hEq : EqOn F F₁ A := by
            intro x hxA
            exact hFD₁ x (Or.inl (Or.inr hxA))
          exact hEq.image_eq.trans hF₁image
        have hAclosed : A ⊆ S := crosscut_subset_closedSquare ha hb hAi
        have hBclosed : B ⊆ S := crosscut_subset_closedSquare ha hb hBi
        have heImage : e '' {x : S | (x : Plane) ∈ A} =
            {x : S | (x : Plane) ∈ B} := by
          ext y
          constructor
          · rintro ⟨x, hxA, rfl⟩
            have hxB : F x ∈ B := by
              rw [← hFA]
              exact ⟨x, hxA, rfl⟩
            exact hxB
          · intro hyB
            have hyImage : (y : Plane) ∈ F '' A := by rw [hFA]; exact hyB
            obtain ⟨x, hxA, hxy⟩ := hyImage
            refine ⟨⟨x, hAclosed hxA⟩, hxA, ?_⟩
            apply Subtype.ext
            exact hxy
        have hSU : Plane.openSquare 0 1 ⊆ S := by
          intro x hx
          exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hx).le
        have hfix : ∀ x : S, (x : Plane) ∉ Plane.openSquare 0 1 → e x = x := by
          intro x hx
          apply hboundary
          rw [modelCurve_eq_frontier, (Plane.isClosed_closedSquare 0 1).frontier_eq,
            interior_closedSquare_zero_one]
          exact ⟨x.property, hx⟩
        let K := extendClosedHomeomorph S (Plane.openSquare 0 1)
          (Plane.isClosed_closedSquare 0 1) (Plane.isOpen_openSquare 0 1) hSU e hfix
        have kOn : ∀ x ∈ A, K x = h.toFun x := by
          intro x hx
          have hxS : x ∈ S := hAclosed hx
          have hk : K x = F x := by
            change (if hx : x ∈ S then (e ⟨x,hx⟩ : Plane) else x) = F x
            rw [dif_pos hxS]
            rfl
          exact hk.trans ((hFD₁ x (Or.inl (Or.inr hx))).trans (hF₁arc x hx))
        refine ⟨K, ?_, ?_, kOn⟩
        · exact (image_congr kOn).trans h.image_eq
        · intro x hx
          exact extendClosedHomeomorph_apply_outside S (Plane.openSquare 0 1)
            (Plane.isClosed_closedSquare 0 1) (Plane.isOpen_openSquare 0 1) hSU e hfix x hx
      have marked (F : Plane ≃ₜ Plane) (q : Plane)
          (hq : q ∈ Plane.openSquare 0 1) (hFq : F q = q)
          (hFfix : ∀ x, x ∉ Plane.openSquare 0 1 → F x = x) :
          ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
            (∀ t x, x ∉ Plane.openSquare 0 1 → H.map (t,x) = x) ∧
            (∀ t, H.map (t,q) = q) := by
        have marked (R : ℝ) (hR : 0 < R) (q : Plane)
            (F : Plane ≃ₜ Plane) (hFq : F q = q)
            (hFfix : ∀ x, R ≤ ‖x-q‖ → F x = x)
            (C : Set Plane) (hFC : ∀ x, x ∉ C → F x = x)
            (hconv : Convex ℝ C) (hq : q ∈ C) :
            ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
              (∀ t x, x ∉ C → H.map (t,x) = x) ∧
              (∀ t, H.map (t,q) = q) := by
          have centered (R : ℝ) (hR : 0 < R)
              (F : Plane ≃ₜ Plane) (hFzero : F 0 = 0) (hFfix : ∀ x, R ≤ ‖x‖ → F x = x)
              (C : Set Plane) (hFC : ∀ x, x ∉ C → F x = x)
              (hscale : ∀ (t : ℝ), 0 < t → t ≤ 1 → ∀ x, x ∉ C → t⁻¹ • x ∉ C) :
              ∃ H : AmbientIsotopy Plane, H.finalMap = F ∧
                (∀ t x, R ≤ ‖x‖ → H.map (t, x) = x) ∧
                (∀ t x, x ∉ C → H.map (t, x) = x) ∧
                (∀ t, H.map (t, 0) = 0) := by
            have hFbound (x : Plane) (hx : ‖x‖ ≤ R) : ‖F x‖ ≤ R := by
              by_contra hn
              have heq : F x = x := F.injective (hFfix (F x) (le_of_not_ge hn))
              exact hn (by rw [heq]; exact hx)
            have hdisp (x : Plane) : ‖F x - x‖ ≤ 2 * R := by
              by_cases hx : ‖x‖ ≤ R
              · exact (norm_sub_le _ _).trans (by linarith [hFbound x hx])
              · rw [hFfix x (le_of_not_ge hx), sub_self, norm_zero]
                linarith
            let G : Interval × Plane → Plane := fun z =>
              if (z.1 : ℝ) = 0 then z.2 else (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2)
            have hGbound (z : Interval × Plane) :
                dist (G z) z.2 ≤ (2 * R) * (z.1 : ℝ) := by
              by_cases ht : (z.1 : ℝ) = 0
              · simp only [G, ht, ite_true, dist_self, mul_zero, le_refl]
              · dsimp only [G]
                rw [if_neg ht, dist_eq_norm]
                have heq : (z.1 : ℝ) • F ((z.1 : ℝ)⁻¹ • z.2) - z.2 =
                    (z.1 : ℝ) • (F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2) := by
                  rw [smul_sub, smul_smul, mul_inv_cancel₀ ht, one_smul]
                rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.property.1]
                calc
                  (z.1 : ℝ) * ‖F ((z.1 : ℝ)⁻¹ • z.2) - (z.1 : ℝ)⁻¹ • z.2‖ ≤
                      (z.1 : ℝ) * (2 * R) :=
                    mul_le_mul_of_nonneg_left (hdisp _) z.1.property.1
                  _ = (2 * R) * (z.1 : ℝ) := mul_comm _ _
            have hGc : Continuous G := by
              rw [continuous_iff_continuousAt]
              intro z
              by_cases ht : (z.1 : ℝ) = 0
              · have hGz : G z = z.2 := by simp only [G, ht, ite_true]
                change Filter.Tendsto G (nhds z) (nhds (G z))
                rw [hGz, tendsto_iff_dist_tendsto_zero]
                have hlim : Filter.Tendsto
                    (fun w : Interval × Plane => (2 * R) * (w.1 : ℝ) + dist w.2 z.2)
                    (nhds z) (nhds 0) := by
                  have hc : Continuous (fun w : Interval × Plane =>
                      (2 * R) * (w.1 : ℝ) + dist w.2 z.2) := by fun_prop
                  simpa only [ContinuousAt, ht, mul_zero, dist_self, add_zero] using hc.continuousAt (x := z)
                exact squeeze_zero (fun w => dist_nonneg) (fun w =>
                  (dist_triangle (G w) w.2 z.2).trans (add_le_add (hGbound w) le_rfl)) hlim
              · have hc : ContinuousAt
                    (fun w : Interval × Plane => (w.1 : ℝ) • F ((w.1 : ℝ)⁻¹ • w.2)) z := by
                  fun_prop (disch := assumption)
                apply hc.congr_of_eventuallyEq
                have hevent : ∀ᶠ w : Interval × Plane in nhds z, (w.1 : ℝ) ≠ 0 :=
                  (continuous_subtype_val.comp continuous_fst).continuousAt.eventually_ne ht
                exact hevent.mono (fun w hw => if_neg hw)
            refine ⟨{ map := ⟨G, hGc⟩, homeomorphism_at := ?_, at_zero := ?_ }, ?_, ?_, ?_, ?_⟩
            · intro t
              by_cases ht : (t : ℝ) = 0
              · exact ⟨Homeomorph.refl _, fun x => by
                  change x = G (t, x)
                  simp only [G, ht, ite_true]⟩
              · let u : ℝˣ := Units.mk0 (t : ℝ) ht
                let e := ((Homeomorph.smul u⁻¹).trans F).trans (Homeomorph.smul u)
                refine ⟨e, ?_⟩
                intro x
                change (t : ℝ) • F ((t : ℝ)⁻¹ • x) = G (t, x)
                dsimp only [G]
                rw [if_neg ht]
            · intro x
              simp [G]
            · funext x
              simp [AmbientIsotopy.finalMap, G]
            · intro t x hx
              change G (t, x) = x
              by_cases ht : (t : ℝ) = 0
              · simp only [G, ht, ite_true]
              · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
                have hlarge : R ≤ ‖(t : ℝ)⁻¹ • x‖ := by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos), inv_mul_eq_div]
                  apply (le_div_iff₀ htpos).mpr
                  nlinarith [t.property.2]
                simp only [G, if_neg ht, hFfix _ hlarge, smul_smul, mul_inv_cancel₀ ht, one_smul]
            · intro t x hx
              change G (t, x) = x
              by_cases ht : (t : ℝ) = 0
              · simp only [G, ht, ite_true]
              · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
                have hout := hscale (t : ℝ) htpos t.property.2 x hx
                simp only [G, if_neg ht, hFC _ hout, smul_smul, mul_inv_cancel₀ ht, one_smul]
            · intro t
              change G (t, 0) = 0
              simp [G, hFzero]
          let e : Plane ≃ₜ Plane := {
            toFun := fun x => x-q
            invFun := fun x => x+q
            left_inv := by intro x; simp
            right_inv := by intro x; simp
            continuous_toFun := continuous_id.sub continuous_const
            continuous_invFun := continuous_id.add continuous_const }
          let K : Plane ≃ₜ Plane := (e.symm.trans F).trans e
          let D : Set Plane := {x | x+q ∈ C}
          have kzero : K 0 = 0 := by simp [K,e,hFq]
          have kfix : ∀ x, R ≤ ‖x‖ → K x = x := by
            intro x hx
            have hf : F (x+q) = x+q := hFfix _ (by simpa using hx)
            simp [K,e,hf]
          have kout : ∀ x, x ∉ D → K x = x := by
            intro x hx
            have hf := hFC (x+q) hx
            simp [K,e,hf]
          have scale : ∀ t : ℝ, 0<t → t≤1 → ∀ x, x∉D → t⁻¹ • x ∉D := by
            intro t ht ht1 x hx hin
            have hp : t⁻¹ • x + q ∈ C := hin
            have hm := hconv.add_smul_sub_mem hq hp (show t ∈ Icc (0:ℝ) 1 from ⟨ht.le,ht1⟩)
            have he : q + t • (t⁻¹ • x + q - q) = x+q := by
              rw [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ ht.ne', one_smul, add_comm]
            rw [he] at hm
            exact hx hm
          obtain ⟨H, hfinal, hball, hout, hzero⟩ := centered R hR K kzero kfix D kout scale
          let L : AmbientIsotopy Plane := {
            map := ⟨fun z => e.symm (H.map (z.1,e z.2)),
              e.symm.continuous.comp (H.map.continuous.comp
                (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩
            homeomorphism_at := by
              intro t
              obtain ⟨h,hh⟩ := H.homeomorphism_at t
              exact ⟨(e.trans h).trans e.symm, fun x => congrArg e.symm (hh (e x))⟩
            at_zero := by
              intro x
              change e.symm (H.map (⟨0,by norm_num⟩,e x)) = x
              rw [H.at_zero, e.symm_apply_apply] }
          refine ⟨L, ?_, ?_, ?_⟩
          · funext x
            change e.symm (H.finalMap (e x)) = F x
            rw [hfinal]
            simp [K,e]
          · intro t x hx
            change e.symm (H.map (t,e x)) = x
            rw [hout t (e x) (by simpa [D,e] using hx), e.symm_apply_apply]
          · intro t
            change e.symm (H.map (t,e q)) = q
            have heq : e q = 0 := by simp [e]
            rw [heq,hzero]
            simp [e]
        obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_ball q).mp (Plane.isBounded_closedSquare 0 1)
        have qclosed : q ∈ Plane.closedSquare 0 1 :=
          mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hq).le
        have hRpos : 0 < R := by simpa using hR qclosed
        have hball : ∀ x, R ≤ ‖x-q‖ → F x = x := by
          intro x hx
          apply hFfix x
          intro hin
          have hb := hR (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hin).le)
          exact not_lt_of_ge hx (by simpa [dist_eq_norm] using hb)
        exact marked R hRpos q F hFq hball (Plane.openSquare 0 1) hFfix
          (Plane.convex_openSquare 0 1) hq
      obtain ⟨P,hP,hAP,hPi⟩ := completion isJordanCurve_modelCurve hA hx hy hyx
        (by simpa only [inside_modelCurve] using hAi)
      obtain ⟨Q,hQ,hBQ,hQi⟩ := completion isJordanCurve_modelCurve hB hx hy hyx
        (by simpa only [inside_modelCurve] using hBi)
      have hU : IsArcBetween (A ∪ P) x y := hA.concatenate hP (by
        intro z hzA hzP
        have hz : z ∈ ({q} : Set Plane) := hAP ▸ (show z ∈ A ∩ P from ⟨hzA,hzP⟩)
        simpa using hz)
      have hV : IsArcBetween (B ∪ Q) x y := hB.concatenate hQ (by
        intro z hzB hzQ
        have hz : z ∈ ({q} : Set Plane) := hBQ ▸ (show z ∈ B ∩ Q from ⟨hzB,hzQ⟩)
        simpa using hz)
      have hUi : (A ∪ P) \ {x,y} ⊆ Plane.openSquare 0 1 := by
        intro z hz
        rcases hz.1 with ha | hp
        · exact hAi ⟨ha, fun he => hz.2 (by simp only [mem_insert_iff,mem_singleton_iff]; exact Or.inl (mem_singleton_iff.mp he))⟩
        · simpa only [inside_modelCurve] using hPi ⟨hp,fun he => hz.2 (by simp only [mem_insert_iff,mem_singleton_iff]; exact Or.inr (mem_singleton_iff.mp he))⟩
      have hVi : (B ∪ Q) \ {x,y} ⊆ Plane.openSquare 0 1 := by
        intro z hz
        rcases hz.1 with hb | hq
        · exact hBi ⟨hb, fun he => hz.2 (by simp only [mem_insert_iff,mem_singleton_iff]; exact Or.inl (mem_singleton_iff.mp he))⟩
        · simpa only [inside_modelCurve] using hQi ⟨hq,fun he => hz.2 (by simp only [mem_insert_iff,mem_singleton_iff]; exact Or.inr (mem_singleton_iff.mp he))⟩
      obtain ⟨h,hhq,hhA⟩ := glue hA hP hB hQ hAP hBQ
      obtain ⟨F,hFwhole,hFout,hFpoint⟩ := prescribed (A ∪ P) (B ∪ Q) x y hU hV h hx hy hUi hVi
      have hFq : F q = q := (hFpoint (Or.inl hA.right_mem)).trans hhq
      have hFA : F '' A = B := (image_congr (fun z hz => hFpoint (Or.inl hz))).trans hhA
      obtain ⟨H,hfinal,hout,hmark⟩ := marked F q hq hFq hFout
      exact ⟨H,by rw [hfinal]; exact hFA,hout,hmark⟩
    have other : ∃ y : Plane, y ∈ modelCurve ∧ y ≠ x := by
      by_cases hxn : x = cornerNE
      · refine ⟨cornerSW, ?_, ?_⟩
        · norm_num [modelCurve,cornerSW,Plane.mk,Plane.supNorm]
        · rw [hxn]; exact isArcBetween_upperSides.ne.symm
      · exact ⟨cornerNE,cornerNE_mem_modelCurve,Ne.symm hxn⟩
    obtain ⟨y,hy,hyx⟩ := other
    obtain ⟨H,hHA,hHout,hHmark⟩ := isotopy hA hB hx hy hyx hq hAi hBi
    let J : Plane ≃ₜ range f := hf.isEmbedding.toHomeomorph
    let e : range f ≃ₜ (univ : Set Plane) := J.symm.trans (Homeomorph.Set.univ Plane).symm
    have he (u : range f) : (e u : Plane) = J.symm u := rfl
    have hJ (u : range f) : f (J.symm u) = u.val := congrArg Subtype.val (J.apply_symm_apply u)
    have hfix : ∀ t z, z ∉ Plane.closedSquare 0 1 → H.map (t,z) = z := by
      intro t z hz
      apply hHout t z
      intro hin
      exact hz (mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hin).le)
    obtain ⟨K,G,hcoord,hGU,hGout⟩ := CurveComplex.position_surface_chart_lift S (range f) univ
      hf.isOpenMap.isOpen_range e (Plane.closedSquare 0 1) (isCompact_closedSquare 0 1)
      (subset_univ _) H hfix
    apply Quotient.sound
    refine ⟨G, ?_, ?_⟩
    · intro t z hz
      by_cases hr : z ∈ range f
      · let u : range f := ⟨z,hr⟩
        have hK : K.map (t,u) = u := by
          apply e.injective
          apply Subtype.ext
          have hc := hcoord t u
          have hp : H.map (t,(e u : Plane)) = (e u : Plane) := by
            by_cases hin : (e u : Plane) ∈ Plane.openSquare 0 1
            · have hqeq : (e u : Plane) = q := hmarks _ hin (by rw [he,hJ]; exact hz)
              rw [hqeq,hHmark]
            · exact hHout t _ hin
          exact hc.trans hp
        exact (hGU t u).trans (congrArg Subtype.val hK)
      · exact hGout t z hr
    · rw [haImage,hbImage]
      ext z
      constructor
      · rintro ⟨w,⟨t,ht,rfl⟩,hw⟩
        let u : range f := J t
        refine ⟨(e (K.finalMap u) : Plane), ?_, ?_⟩
        · have hc := hcoord (⟨1,by norm_num⟩ : Interval) u
          change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at hc
          have heu : (e u : Plane) = t := by simp [he,u]
          rw [hc,heu]
          exact hHA ▸ mem_image_of_mem H.finalMap ht
        · rw [he,hJ]
          exact (hGU (⟨1,by norm_num⟩ : Interval) u).symm.trans hw
      · rintro ⟨t,ht,rfl⟩
        obtain ⟨z,hz,hzt⟩ := (show t ∈ H.finalMap '' A from hHA.symm ▸ ht)
        let u : range f := J z
        let v : range f := J t
        have heu : (e u : Plane) = z := by simp [he,u]
        have hev : (e v : Plane) = t := by simp [he,v]
        have hKv : K.finalMap u = v := by
          apply e.injective
          apply Subtype.ext
          have hc := hcoord (⟨1,by norm_num⟩ : Interval) u
          change (e (K.finalMap u) : Plane) = H.finalMap (e u : Plane) at hc
          rw [hc,heu,hzt,hev]
        refine ⟨f z,mem_image_of_mem f hz,?_⟩
        change G.map ((⟨1,by norm_num⟩ : Interval),u.val) = v.val
        rw [hGU]
        exact congrArg Subtype.val hKv
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
  obtain ⟨F,hFC,hFin⟩ := chart hC
  let g : Plane → S := f ∘ F.symm
  have hg : Topology.IsOpenEmbedding g := hf.comp F.symm.isOpenEmbedding
  have moved (D : Set Plane) : g '' (F '' D) = f '' D := by
    rw [image_image]
    have he : g ∘ F = f := by funext z; simp [g,Function.comp_def]
    change (g ∘ F) '' D = f '' D
    rw [he]
  have inner (z : Plane) : F z ∈ Plane.openSquare 0 1 ↔ z ∈ inside C := by
    rw [← hFin]
    exact F.injective.mem_set_image
  have iA : F '' A \ {F x} ⊆ Plane.openSquare 0 1 := by
    rintro z ⟨⟨t,ht,rfl⟩,hne⟩
    apply (inner t).mpr
    apply hAi ⟨ht, ?_⟩
    intro he
    have htEq : t = x := mem_singleton_iff.mp he
    exact hne (by simp [htEq])
  have iB : F '' B \ {F x} ⊆ Plane.openSquare 0 1 := by
    rintro z ⟨⟨t,ht,rfl⟩,hne⟩
    apply (inner t).mpr
    apply hBi ⟨ht, ?_⟩
    intro he
    have htEq : t = x := mem_singleton_iff.mp he
    exact hne (by simp [htEq])
  apply classes M a b g hg (F '' A) (F '' B) (F x) (F q)
    (hA.image_of_injOn (subset_univ _) F.continuous.continuousOn F.injective.injOn)
    (hB.image_of_injOn (subset_univ _) F.continuous.continuousOn F.injective.injOn)
    (hFC ▸ mem_image_of_mem F hx) ((inner q).mpr hq) iA iB
    (haImage.trans (moved A).symm) (hbImage.trans (moved B).symm)
  intro z hz hb
  have hi : F.symm z ∈ inside C := by
    apply (inner (F.symm z)).mp
    simpa using hz
  have he := hmarks (F.symm z) hi hb
  exact (F.apply_symm_apply z).symm.trans (congrArg F he)
end CurveComplex.HyperellipticModel
