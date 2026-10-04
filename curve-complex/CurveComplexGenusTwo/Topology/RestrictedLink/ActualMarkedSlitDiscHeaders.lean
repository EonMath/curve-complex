import CurveComplexGenusTwo.Topology.RestrictedLink.ActualPlanarArcHeaders
import CurveComplexGenusTwo.Filtration.Geometry.NonloopPuncture
import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Dependencies.SpherePort
import Schoenflies.JordanClosed
import Mathlib.Topology.Compactification.OnePoint.Sphere
namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 4000000
theorem actual_marked_open_disc_single_slit_connected (M : HyperellipticModel E S) (U : Set S) (hU : IsOpen U)
    (e : Plane ≃ₜ U) (a : EssentialMarkedArc M)
    (h0 : a.val.map 0 ∉ U)
    (hin : ∀ t : Interval, t ≠ 0 → a.val.map t ∈ U) :
    IsConnected (U \ a.val.image) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
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
  have nowhere (M : HyperellipticModel E S) (a : NonLoopArc M) : IsNowhereDense a.val.image := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨p,hpB,hp⟩ := a.exists_marked_puncture
    let es : {x : S // x ≠ p} ≃ₜ {y : CurveComplex.SpherePort.Sphere // y ≠ M.sphere p} :=
      M.sphere.subtype (fun x => M.sphere.injective.ne_iff.symm)
    let e := es.trans (puncturedSpherePlane (M.sphere p))
    let f : Plane → S := fun z => (e.symm z).val
    have hf : Topology.IsOpenEmbedding f :=
      isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
    let g : Interval → Plane := fun t => e ⟨a.val.map t,fun h => hp (h ▸ ⟨t,rfl⟩)⟩
    have hA : IsArcBetween (range g) (g 0) (g 1) := actual_nonloop_planar_arc M a p hp e
    obtain ⟨Q,hQ,hmeet,hJ⟩ := exists_jordan_completion_of_isArcBetween hA
    have hsep := jordan_curve_theorem hJ
    have hndJ : IsNowhereDense (Q ∪ range g) := by
      rw [← hsep.frontier_inside]
      change interior (closure (frontier (inside (Q ∪ range g)))) = ∅
      rw [isClosed_frontier.closure_eq, ← frontier_compl]
      exact interior_frontier hsep.isOpen_inside.isClosed_compl
    have hnd := hndJ.mono (Set.subset_union_right : range g ⊆ Q ∪ range g)
    have himage : f '' range g = a.val.image := by
      ext x
      constructor
      · rintro ⟨z,⟨t,rfl⟩,rfl⟩
        refine ⟨t,?_⟩
        simp [f,g]
      · rintro ⟨t,rfl⟩
        refine ⟨g t,⟨t,rfl⟩,?_⟩
        simp [f,g]
    rw [← himage]
    exact hf.isEmbedding.isInducing.isNowhereDense_image hnd
  have h1 : a.val.map 1 ∈ U := hin 1 (by norm_num)
  have hneq : a.val.map 0 ≠ a.val.map 1 := fun he => h0 (he ▸ h1)
  let aN : NonLoopArc M := ⟨a.val,hneq⟩
  have hnd := nowhere M aN
  have hUneq : U.Nonempty := ⟨(e 0).val,(e 0).property⟩
  obtain ⟨p,hpU,hpa⟩ : ∃ p ∈ U, p ∉ a.val.image := by
    by_contra hn
    push_neg at hn
    have hsub : U ⊆ closure a.val.image := fun p hp => subset_closure (hn p hp)
    have hi : U ⊆ interior (closure a.val.image) := hU.interior_eq ▸ interior_mono hsub
    obtain ⟨p,hp⟩ := hUneq
    rw [show interior (closure a.val.image) = ∅ from hnd] at hi
    exact hi hp
  let f : Plane → S := fun z => (e z).val
  have hf : Topology.IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  have hrange : range f = U := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact (e z).property
    · intro hx
      refine ⟨e.symm ⟨x,hx⟩,?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)
  let x : Plane := e.symm ⟨p,hpU⟩
  have hfx : f x = p := congrArg Subtype.val (e.apply_symm_apply ⟨p,hpU⟩)
  have hconnected := slit f hf a.val.map a.val.continuous aN.injective
    (hrange.symm ▸ h0) (fun t ht => hrange.symm ▸ hin t ht) x (hfx.symm ▸ hpa)
  change IsConnected (U \ Set.range a.val.map)
  simpa only [hrange] using hconnected
end CurveComplex.HyperellipticModel
