import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import ClassificationJordanCurve.Arcs
import CurveComplexGenusTwo.Topology.SurfaceRecognition.ClosedCoverHomeomorph
import Schoenflies.JordanSchoenflies
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Topology.Compactness.SigmaCompact

import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCountableUniversalCoverHeader
open Set Metric Topology Schoenflies

-- Anonymous construction: geometric engulfing remains an explicit supplier.
namespace CurveComplex.LocalSurgery

theorem surface_plane_of_compact_disk_engulfing {U : Type} [TopologicalSpace U] [T2Space U]
    [SecondCountableTopology U] [ChartedSpace Plane U]
    (engulf : ∀ K : Set U, IsCompact K → ∃ D : Set U,
      IsCompact D ∧ Nonempty (closedBall (0 : Plane) 1 ≃ₜ D) ∧ K ⊆ interior D) :
    Nonempty (Plane ≃ₜ U) := by
  classical
  have reconstruct (D : ℕ → Set U) (eD : ∀ n, closedBall (0 : Plane) 1 ≃ₜ D n)
      (hnested : ∀ n, D n ⊆ interior (D (n+1)))
      (hcover : (⋃ n, interior (D n)) = univ) : Nonempty (Plane ≃ₜ U) := by
    classical
    have stage (D E : Set U) (eD : closedBall (0 : Plane) 1 ≃ₜ D)
        (eE : closedBall (0 : Plane) 1 ≃ₜ E) (hDE : D ⊆ interior E)
        (f : C(D,Plane)) (hf : IsEmbedding f) (K : Set Plane) (hK : IsCompact K) :
        ∃ g : C(E,Plane), IsEmbedding g ∧
          (∀ x : D, g ⟨x,interior_subset (hDE x.property)⟩ = f x) ∧
          K ⊆ g '' {x : E | (x : U) ∈ interior E} := by
      classical
      have param (d0 d1 : C(closedBall (0 : Plane) 1, Plane))
          (hd0 : IsEmbedding d0) (hd1 : IsEmbedding d1) :
          ∃ F : Plane ≃ₜ Plane, ∀ x, F (d0 x) = d1 x := by
        classical
        have regions (d : C(closedBall (0 : Plane) 1, Plane)) (hd : IsEmbedding d) :
            IsJordanCurve (frontier (range d)) ∧
              range d = frontier (range d) ∪ inside (frontier (range d)) ∧
              interior (range d) = inside (frontier (range d)) := by
          classical
          let A : Set Plane := closedBall 0 1
          let K : Set Plane := range d
          have hK : IsCompact K := isCompact_range d.continuous
          let cb : Circle → A := fun z =>
            ⟨ClassificationJordanCurve.Arcs.circleHomeoSphere z,
              sphere_subset_closedBall (ClassificationJordanCurve.Arcs.circleHomeoSphere z).property⟩
          have hcb : Continuous cb :=
            (continuous_subtype_val.comp ClassificationJordanCurve.Arcs.circleHomeoSphere.continuous).subtype_mk _
          have hcbi : Function.Injective cb := by
            intro x y he
            apply ClassificationJordanCurve.Arcs.circleHomeoSphere.injective
            apply Subtype.ext
            simpa only [cb] using congrArg (fun z : A => (z : Plane)) he
          let r : C(Circle, Plane) := ⟨d ∘ cb, d.continuous.comp hcb⟩
          have hr : IsEmbedding r :=
            (r.continuous.isClosedEmbedding (hd.injective.comp hcbi)).isEmbedding
          have hboundary : range r = frontier K := by
            have hfr := CurveComplex.embedded_compact_planar_region_frontier_probe A
              (isCompact_closedBall 0 1) d hd
            rw [frontier_closedBall (0 : Plane) one_ne_zero] at hfr
            rw [← hfr]
            ext x
            constructor
            · rintro ⟨z,rfl⟩
              exact ⟨cb z,(ClassificationJordanCurve.Arcs.circleHomeoSphere z).property,rfl⟩
            · rintro ⟨z,hz,rfl⟩
              let w : sphere (0 : Plane) 1 := ⟨z,hz⟩
              refine ⟨ClassificationJordanCurve.Arcs.circleHomeoSphere.symm w,?_⟩
              change d (cb _) = d z
              congr 1
              apply Subtype.ext
              change (ClassificationJordanCurve.Arcs.circleHomeoSphere
                (ClassificationJordanCurve.Arcs.circleHomeoSphere.symm w) : Plane) = (w : Plane)
              exact congrArg Subtype.val
                (ClassificationJordanCurve.Arcs.circleHomeoSphere.apply_symm_apply w)
          have hJordan : IsJordanCurve (frontier K) := by
            rw [← hboundary]
            exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
          let ob : ball (0 : Plane) 1 → A := fun x => ⟨x,ball_subset_closedBall x.property⟩
          have hob : Continuous ob := continuous_subtype_val.subtype_mk _
          let q : C(ball (0 : Plane) 1, Plane) := ⟨d ∘ ob,d.continuous.comp hob⟩
          have hiimage : range q = interior K := by
            ext y
            constructor
            · rintro ⟨z,rfl⟩
              apply (CurveComplex.embedded_planar_region_interior_iff_probe A d hd (ob z)).mpr
              simpa only [A,interior_closedBall (0 : Plane) one_ne_zero] using z.property
            · intro hy
              obtain ⟨z,rfl⟩ := interior_subset hy
              have hz := (CurveComplex.embedded_planar_region_interior_iff_probe A d hd z).mp hy
              rw [show interior A = ball 0 1 from interior_closedBall _ one_ne_zero] at hz
              exact ⟨⟨z,hz⟩,rfl⟩
          haveI : ConnectedSpace (ball (0 : Plane) 1) :=
            isConnected_iff_connectedSpace.mp (isConnected_ball zero_lt_one)
          have hiconn : IsConnected (interior K) := hiimage ▸ isConnected_range q.continuous
          obtain ⟨x,hx⟩ := hiconn.nonempty
          have hsub : interior K ⊆ (frontier K)ᶜ := by
            intro z hz hfr
            exact hfr.2 hz
          have hfront : frontier (interior K) ∩ (frontier K)ᶜ = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro z hz
            exact hz.2 (frontier_interior_subset hz.1)
          have hcomp := Plane.connectedComponentIn_eq_of_frontier_disjoint
            isOpen_interior hiconn.isPreconnected hsub hfront hx
          have hsep := jordan_curve_theorem hJordan
          have hi : interior K = inside (frontier K) := by
            rcases hsep.isRegionOf_connectedComponentIn (hsub hx) with hh | hh
            · exact hcomp.symm.trans hh
            · have heq : interior K = outside (frontier K) := hcomp.symm.trans hh
              exact (hsep.not_isBounded_outside
                (heq ▸ hK.isBounded.subset interior_subset)).elim
          refine ⟨hJordan,?_,hi⟩
          rw [← hi,hK.isClosed.frontier_eq]
          exact (diff_union_of_subset interior_subset).symm
        have ambient (C C' : Set Plane) (hC : IsJordanCurve C) (hC' : IsJordanCurve C')
            (e : (C ∪ inside C : Set Plane) ≃ₜ (C' ∪ inside C' : Set Plane))
            (b : C ≃ₜ C')
            (he : ∀ x : C, (e ⟨x, Or.inl x.property⟩ : Plane) = b x) :
            ∃ H : Plane ≃ₜ Plane, ∀ x : (C ∪ inside C : Set Plane), H x = e x := by
          classical
          obtain ⟨f,g,hfg,hfb⟩ := exists_isHomeoOn_of_homeomorph b
          obtain ⟨F,G,hFG,hF⟩ := exterior_extension_of_squareExtension squareExtension hC hC' hfg
          let ext : (C ∪ outside C : Set Plane) ≃ₜ (C' ∪ outside C' : Set Plane) := {
            toFun := fun x => ⟨F x, hFG.mapsTo x.property⟩
            invFun := fun y => ⟨G y, hFG.mapsTo_inv y.property⟩
            left_inv := fun x => Subtype.ext (hFG.invOn.1 x.property)
            right_inv := fun y => Subtype.ext (hFG.invOn.2 y.property)
            continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp
              hFG.continuousOn).subtype_mk _
            continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp
              hFG.continuousOn_inv).subtype_mk _ }
          have overlap (D : Set Plane) (x : Plane)
              (hi : x ∈ D ∪ inside D) (ho : x ∈ D ∪ outside D) : x ∈ D := by
            by_contra hn
            exact disjoint_inside_outside.le_bot ⟨hi.resolve_left hn, ho.resolve_left hn⟩
          have ext_boundary (x : C) : (ext ⟨x, Or.inl x.property⟩ : Plane) = b x := by
            change F x = _
            exact (hF x.property).trans (hfb x x.property)
          have forward : ∀ x (hi : x ∈ C ∪ inside C) (ho : x ∈ C ∪ outside C),
              (e ⟨x,hi⟩ : Plane) = ext ⟨x,ho⟩ := by
            intro x hi ho
            let xc : C := ⟨x, overlap C x hi ho⟩
            exact (he xc).trans (ext_boundary xc).symm
          have backward : ∀ y (hi : y ∈ C' ∪ inside C') (ho : y ∈ C' ∪ outside C'),
              (e.symm ⟨y,hi⟩ : Plane) = ext.symm ⟨y,ho⟩ := by
            intro y hi ho
            let yc : C' := ⟨y, overlap C' y hi ho⟩
            let xc : C := b.symm yc
            have ei : e ⟨xc, Or.inl xc.property⟩ = ⟨y,hi⟩ := by
              apply Subtype.ext
              exact (he xc).trans (congrArg Subtype.val (b.apply_symm_apply yc))
            have eo : ext ⟨xc, Or.inl xc.property⟩ = ⟨y,ho⟩ := by
              apply Subtype.ext
              exact (ext_boundary xc).trans (congrArg Subtype.val (b.apply_symm_apply yc))
            rw [← ei, e.symm_apply_apply, ← eo, ext.symm_apply_apply]
          let glued := Schoenflies.ClosedCoverHomeomorph.glue
            (isClosed_union_inside (jordan_curve_theorem hC))
            (isClosed_union_outside (jordan_curve_theorem hC))
            (isClosed_union_inside (jordan_curve_theorem hC'))
            (isClosed_union_outside (jordan_curve_theorem hC')) e ext forward backward
          let H := (Homeomorph.Set.univ Plane).symm.trans
            ((Homeomorph.setCongr (union_inside_union_outside C).symm).trans
              (glued.trans ((Homeomorph.setCongr (union_inside_union_outside C')).trans
                (Homeomorph.Set.univ Plane))))
          refine ⟨H, ?_⟩
          intro x
          exact Schoenflies.ClosedCoverHomeomorph.coe_glue_apply_of_mem_left
            (isClosed_union_inside (jordan_curve_theorem hC))
            (isClosed_union_outside (jordan_curve_theorem hC))
            (isClosed_union_inside (jordan_curve_theorem hC'))
            (isClosed_union_outside (jordan_curve_theorem hC')) e ext forward backward
            ⟨x,Or.inl x.property⟩ x.property
        have boundary (d : C(closedBall (0 : Plane) 1, Plane)) (hd : IsEmbedding d) :
            ∃ b : sphere (0 : Plane) 1 ≃ₜ frontier (range d),
              ∀ z, (b z : Plane) = d ⟨z,sphere_subset_closedBall z.property⟩ := by
          have hfr := CurveComplex.embedded_compact_planar_region_frontier_probe
            (closedBall (0 : Plane) 1) (isCompact_closedBall 0 1) d hd
          rw [frontier_closedBall (0 : Plane) one_ne_zero] at hfr
          let k : sphere (0 : Plane) 1 → frontier (range d) := fun z =>
            ⟨d ⟨z,sphere_subset_closedBall z.property⟩,
              hfr ▸ mem_image_of_mem d z.property⟩
          have hkc : Continuous k := by
            apply Continuous.subtype_mk
            exact d.continuous.comp (continuous_subtype_val.subtype_mk _)
          have hki : Function.Injective k := by
            intro x y he
            have hh := hd.injective (congrArg Subtype.val he)
            apply Subtype.ext
            exact congrArg (fun z : closedBall (0 : Plane) 1 => (z : Plane)) hh
          have hks : Function.Surjective k := by
            intro y
            have hy := hfr.symm.subset y.property
            obtain ⟨x,hx,hxy⟩ := hy
            exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
          let b := hkc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective k ⟨hki,hks⟩)
          exact ⟨b,fun _ => rfl⟩
        obtain ⟨hC0,hreg0,_⟩ := regions d0 hd0
        obtain ⟨hC1,hreg1,_⟩ := regions d1 hd1
        obtain ⟨b0,hb0⟩ := boundary d0 hd0
        obtain ⟨b1,hb1⟩ := boundary d1 hd1
        let e : (frontier (range d0) ∪ inside (frontier (range d0)) : Set Plane) ≃ₜ
            (frontier (range d1) ∪ inside (frontier (range d1)) : Set Plane) :=
          (Homeomorph.setCongr hreg0.symm).trans
            (hd0.toHomeomorph.symm.trans (hd1.toHomeomorph.trans
              (Homeomorph.setCongr hreg1)))
        let b : frontier (range d0) ≃ₜ frontier (range d1) := b0.symm.trans b1
        have he : ∀ x : frontier (range d0),
            (e ⟨x,Or.inl x.property⟩ : Plane) = b x := by
          intro x
          let z := b0.symm x
          have hz : d0 ⟨z,sphere_subset_closedBall z.property⟩ = (x : Plane) :=
            (hb0 z).symm.trans (congrArg Subtype.val (b0.apply_symm_apply x))
          have hp : hd0.toHomeomorph.symm
              ⟨x,hreg0.symm.subset (Or.inl x.property)⟩ =
              ⟨z,sphere_subset_closedBall z.property⟩ := by
            apply hd0.toHomeomorph.injective
            apply Subtype.ext
            exact (congrArg Subtype.val
              (hd0.toHomeomorph.apply_symm_apply ⟨x,_⟩)).trans hz.symm
          change d1 (hd0.toHomeomorph.symm ⟨x,_⟩) = (b1 z : Plane)
          rw [hp,hb1]
        obtain ⟨F,hF⟩ := ambient _ _ hC0 hC1 e b he
        refine ⟨F,?_⟩
        intro x
        let y : (frontier (range d0) ∪ inside (frontier (range d0)) : Set Plane) :=
          ⟨d0 x,hreg0.subset (mem_range_self x)⟩
        have hh := hF y
        change F (d0 x) = d1 (hd0.toHomeomorph.symm ⟨d0 x,_⟩) at hh
        have hp : (⟨d0 x,_⟩ : range d0) = hd0.toHomeomorph x := rfl
        rw [hp,hd0.toHomeomorph.symm_apply_apply] at hh
        exact hh
      have absorption (W K : Set Plane) (hWopen : IsOpen W)
          (hW : closedBall (0 : Plane) 1 ⊆ W) (hK : IsCompact K) :
          ∃ F : Plane ≃ₜ Plane, (∀ x ∈ closedBall (0 : Plane) 1, F x = x) ∧
            K ⊆ F '' W := by
        have ballAbsorption (r R : ℝ) (hr : 1 < r) (hR : 0 ≤ R)
            (W : Set Plane) (hW : closedBall (0 : Plane) r ⊆ W) :
            ∃ F : Plane ≃ₜ Plane, (∀ x ∈ closedBall (0 : Plane) 1, F x = x) ∧
              closedBall (0 : Plane) R ⊆ F '' W := by
          have radial (c : ℝ) (hc : 0 ≤ c) :
              ∃ F : Plane ≃ₜ Plane,
                (∀ x, F x = (1+c*(1-1/max 1 ‖x‖)) • x) ∧
                (∀ x, F.symm x = ((1+c/max 1 ‖x‖)/(1+c)) • x) ∧
                (∀ x ∈ closedBall (0 : Plane) 1, F x = x) := by
            let f : Plane → Plane := fun x => (1 + c * (1 - 1 / max 1 ‖x‖)) • x
            let g : Plane → Plane := fun x => ((1 + c / max 1 ‖x‖) / (1+c)) • x
            have hcp : 0 < 1+c := by positivity
            have hmax (x : Plane) : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
            have cm : Continuous (fun x : Plane => max 1 ‖x‖) := continuous_const.max continuous_norm
            have fc : Continuous f := by
              unfold f
              exact (continuous_const.add (continuous_const.mul (continuous_const.sub
                (continuous_const.div₀ cm (fun x => ne_of_gt (hmax x)))))).smul continuous_id
            have gc : Continuous g := by
              unfold g
              exact ((continuous_const.add
                (continuous_const.div₀ cm (fun x => ne_of_gt (hmax x)))).div_const (1+c)).smul
                continuous_id
            have fsmall (x : Plane) (hx : ‖x‖ ≤ 1) : f x = x := by
              simp [f, max_eq_left hx]
            have gsmall (x : Plane) (hx : ‖x‖ ≤ 1) : g x = x := by
              simp [g, max_eq_left hx, ne_of_gt hcp]
            have flarge (x : Plane) (hx : 1 < ‖x‖) :
                ‖f x‖ = (1+c)*‖x‖-c := by
              have hr : 0 < ‖x‖ := lt_trans zero_lt_one hx
              have hcoef : 0 ≤ 1 + c*(1-1/‖x‖) := by
                have : 1/‖x‖ ≤ 1 := (div_le_one hr).mpr hx.le
                positivity
              dsimp only [f]
              rw [max_eq_right hx.le, norm_smul, Real.norm_of_nonneg hcoef]
              field_simp
              <;> ring
            have glarge (x : Plane) (hx : 1 < ‖x‖) :
                ‖g x‖ = (‖x‖+c)/(1+c) := by
              have hr : 0 < ‖x‖ := lt_trans zero_lt_one hx
              have hcoef : 0 ≤ (1+c/‖x‖)/(1+c) := by positivity
              dsimp only [g]
              rw [max_eq_right hx.le, norm_smul, Real.norm_of_nonneg hcoef]
              field_simp
              <;> ring
            have left : Function.LeftInverse g f := by
              intro x
              by_cases hx : ‖x‖ ≤ 1
              · rw [fsmall x hx, gsmall x hx]
              · have hr : 1 < ‖x‖ := lt_of_not_ge hx
                have hr0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
                have hfnorm := flarge x hr
                have hfgt : 1 < ‖f x‖ := by rw [hfnorm]; nlinarith
                have hf0 : ‖f x‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hfgt)
                change ((1+c/max 1 ‖f x‖)/(1+c)) • f x = x
                rw [max_eq_right hfgt.le, hfnorm]
                dsimp only [f]
                rw [max_eq_right hr.le, smul_smul]
                have heq : ((1+c/((1+c)*‖x‖-c))/(1+c)) *
                    (1+c*(1-1/‖x‖)) = 1 := by
                  have hn : (1+c)*‖x‖-c ≠ 0 := hfnorm ▸ hf0
                  field_simp [hr0, ne_of_gt hcp, hn]
                  <;> ring
                rw [heq, one_smul]
            have right : Function.RightInverse g f := by
              intro x
              by_cases hx : ‖x‖ ≤ 1
              · rw [gsmall x hx, fsmall x hx]
              · have hr : 1 < ‖x‖ := lt_of_not_ge hx
                have hr0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
                have hgnorm := glarge x hr
                have hggt : 1 < ‖g x‖ := by
                  rw [hgnorm]
                  exact (lt_div_iff₀ hcp).mpr (by linarith)
                change (1+c*(1-1/max 1 ‖g x‖)) • g x = x
                rw [max_eq_right hggt.le, hgnorm]
                dsimp only [g]
                rw [max_eq_right hr.le, smul_smul]
                have heq : (1+c*(1-1/((‖x‖+c)/(1+c)))) *
                    ((1+c/‖x‖)/(1+c)) = 1 := by
                  have hn : ‖x‖+c ≠ 0 := ne_of_gt (by positivity)
                  field_simp [hr0, ne_of_gt hcp, hn]
                  <;> ring
                rw [heq, one_smul]
            refine ⟨{
              toFun := f
              invFun := g
              left_inv := left
              right_inv := right
              continuous_toFun := fc
              continuous_invFun := gc }, fun _ => rfl, fun _ => rfl, ?_⟩
            intro x hx
            exact fsmall x (by simpa only [mem_closedBall, dist_zero_right] using hx)
          let c : ℝ := R/(r-1)
          have hc : 0 ≤ c := div_nonneg hR (by linarith)
          have hcp : 0 < 1+c := by positivity
          have hcr : c*(r-1) = R := by
            dsimp only [c]
            exact div_mul_cancel₀ R (ne_of_gt (by linarith : 0 < r-1))
          obtain ⟨F,_,hginv,hfix⟩ := radial c hc
          refine ⟨F,hfix,?_⟩
          intro x hx
          have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
          have hnorm : ‖F.symm x‖ ≤ r := by
            rw [hginv]
            by_cases hx1 : ‖x‖ ≤ 1
            · rw [max_eq_left hx1]
              simp only [div_one, div_self (ne_of_gt hcp), one_smul]
              exact hx1.trans hr.le
            · have hxp : 0 < ‖x‖ := lt_trans zero_lt_one (lt_of_not_ge hx1)
              have hcoef : 0 ≤ (1+c/‖x‖)/(1+c) := by positivity
              rw [max_eq_right (le_of_not_ge hx1), norm_smul, Real.norm_of_nonneg hcoef]
              have heq : ((1+c/‖x‖)/(1+c))*‖x‖ = (‖x‖+c)/(1+c) := by
                field_simp
                <;> ring
              rw [heq]
              apply (div_le_iff₀ hcp).mpr
              nlinarith
          exact ⟨F.symm x, hW (by simpa only [mem_closedBall, dist_zero_right] using hnorm),
            F.apply_symm_apply x⟩
        obtain ⟨δ,hδpos,hδ⟩ := (isCompact_closedBall (0 : Plane) 1).exists_cthickening_subset_open hWopen hW
        rw [cthickening_closedBall hδpos.le zero_le_one] at hδ
        obtain ⟨R,hRpos,hR⟩ := hK.isBounded.exists_pos_norm_le
        obtain ⟨F,hfix,habsorb⟩ := ballAbsorption (δ+1) R (by linarith) hRpos.le W hδ
        refine ⟨F,hfix,?_⟩
        intro x hx
        exact habsorb (by simpa only [mem_closedBall, dist_zero_right] using hR x hx)
      let inc : D → E := fun x => ⟨x,interior_subset (hDE x.property)⟩
      have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
      let d0 : C(closedBall (0 : Plane) 1,Plane) :=
        ⟨fun z => (eE.symm (inc (eD z)) : Plane),
          continuous_subtype_val.comp (eE.symm.continuous.comp (hinc.comp eD.continuous))⟩
      let d1 : C(closedBall (0 : Plane) 1,Plane) := ⟨f ∘ eD,f.continuous.comp eD.continuous⟩
      have hd0 : IsEmbedding d0 := by
        apply (d0.continuous.isClosedEmbedding ?_).isEmbedding
        intro x y he
        apply eD.injective
        apply Subtype.ext
        have hh := eE.symm.injective (Subtype.ext he)
        exact congrArg (fun z : E => (z : U)) hh
      have hd1 : IsEmbedding d1 := hf.comp eD.isEmbedding
      let std : C(closedBall (0 : Plane) 1,Plane) := ⟨Subtype.val,continuous_subtype_val⟩
      obtain ⟨H,hH⟩ := param d0 d1 hd0 hd1
      obtain ⟨T,hT⟩ := param d1 std hd1 IsEmbedding.subtypeVal
      let dE : C(closedBall (0 : Plane) 1,U) := ⟨fun z => eE z,eE.continuous.subtype_val⟩
      have hdE : IsEmbedding dE := IsEmbedding.subtypeVal.comp eE.isEmbedding
      have hRangeE : range dE = E := by
        ext y
        constructor
        · rintro ⟨z,rfl⟩
          exact (eE z).property
        · intro hy
          exact ⟨eE.symm ⟨y,hy⟩,congrArg Subtype.val (eE.apply_symm_apply ⟨y,hy⟩)⟩
      have interiorE (z : closedBall (0 : Plane) 1) :
          (eE z : U) ∈ interior E ↔ (z : Plane) ∈ ball (0 : Plane) 1 := by
        have hh := CurveComplex.embedded_planar_region_interior_iff_probe
          (closedBall (0 : Plane) 1) dE hdE z
        rw [hRangeE,interior_closedBall (0 : Plane) one_ne_zero] at hh
        exact hh
      have old_in_ball (z : closedBall (0 : Plane) 1) : d0 z ∈ ball (0 : Plane) 1 := by
        apply (interiorE (eE.symm (inc (eD z)))).mp
        have hh := hDE (eD z).property
        simpa only [eE.apply_symm_apply] using hh
      let W : Set Plane := T '' (H '' ball (0 : Plane) 1)
      have hWopen : IsOpen W := T.isOpenMap _ (H.isOpenMap _ isOpen_ball)
      have hW : closedBall (0 : Plane) 1 ⊆ W := by
        intro x hx
        let z : closedBall (0 : Plane) 1 := ⟨x,hx⟩
        exact ⟨H (d0 z), ⟨d0 z,old_in_ball z,rfl⟩,
          (congrArg T (hH z)).trans (hT z)⟩
      obtain ⟨M,hMfix,hMabsorb⟩ := absorption W (T '' K) hWopen hW (hK.image T.continuous)
      let g : C(E,Plane) := ⟨fun x => T.symm (M (T (H (eE.symm x : Plane)))),
        T.symm.continuous.comp (M.continuous.comp (T.continuous.comp
          (H.continuous.comp (continuous_subtype_val.comp eE.symm.continuous))))⟩
      have hg : IsEmbedding g := T.symm.isEmbedding.comp (M.isEmbedding.comp
        (T.isEmbedding.comp (H.isEmbedding.comp
          (IsEmbedding.subtypeVal.comp eE.symm.isEmbedding))))
      refine ⟨g,hg,?_,?_⟩
      · intro x
        let z := eD.symm x
        have hh : H (eE.symm (inc x) : Plane) = f x := by
          have hh := hH z
          change H (eE.symm (inc (eD z)) : Plane) = f (eD z) at hh
          simpa only [z,eD.apply_symm_apply] using hh
        have ht : T (f x) = (z : Plane) := by
          have ht := hT z
          change T (f (eD z)) = (z : Plane) at ht
          simpa only [z,eD.apply_symm_apply] using ht
        change T.symm (M (T (H (eE.symm (inc x) : Plane)))) = f x
        rw [hh,hMfix _ (ht.symm ▸ z.property),T.symm_apply_apply]
      · intro y hy
        have hTy := hMabsorb (mem_image_of_mem T hy)
        obtain ⟨w,⟨v,⟨z,hz,hHz⟩,hTv⟩,hw⟩ := hTy
        let zz : closedBall (0 : Plane) 1 := ⟨z,ball_subset_closedBall hz⟩
        refine ⟨eE zz,(interiorE zz).mpr hz,?_⟩
        change T.symm (M (T (H (eE.symm (eE zz) : Plane)))) = y
        rw [eE.symm_apply_apply]
        change T.symm (M (T (H z))) = y
        rw [hHz,hTv,hw,T.symm_apply_apply]
    let T (n : ℕ) := {f : C(D n,Plane) // IsEmbedding f}
    let initial : T 0 := ⟨⟨fun x => (eD 0).symm x,
      continuous_subtype_val.comp (eD 0).symm.continuous⟩,
      IsEmbedding.subtypeVal.comp (eD 0).symm.isEmbedding⟩
    let next (n : ℕ) (t : T n) : T (n+1) :=
      ⟨(stage (D n) (D (n+1)) (eD n) (eD (n+1)) (hnested n) t.val t.property
        (closedBall 0 (n+1)) (isCompact_closedBall 0 (n+1))).choose,
        (stage (D n) (D (n+1)) (eD n) (eD (n+1)) (hnested n) t.val t.property
        (closedBall 0 (n+1)) (isCompact_closedBall 0 (n+1))).choose_spec.1⟩
    let seq : (n : ℕ) → T n := Nat.rec initial next
    let f (n : ℕ) := (seq n).val
    have hf (n : ℕ) : IsEmbedding (f n) := (seq n).property
    have step (n : ℕ) (x : D n) :
        f (n+1) ⟨x,interior_subset (hnested n x.property)⟩ = f n x :=
      (stage (D n) (D (n+1)) (eD n) (eD (n+1)) (hnested n) (seq n).val (seq n).property
        (closedBall 0 (n+1)) (isCompact_closedBall 0 (n+1))).choose_spec.2.1 x
    have target (n : ℕ) : closedBall (0 : Plane) (n+1) ⊆
        f (n+1) '' {x : D (n+1) | (x : U) ∈ interior (D (n+1))} :=
      (stage (D n) (D (n+1)) (eD n) (eD (n+1)) (hnested n) (seq n).val (seq n).property
        (closedBall 0 (n+1)) (isCompact_closedBall 0 (n+1))).choose_spec.2.2
    have mono : Monotone D := monotone_nat_of_le_succ fun n =>
      (hnested n).trans interior_subset
    have compat (m n : ℕ) (hmn : m ≤ n) (x : D m) :
        f n ⟨x,mono hmn x.property⟩ = f m x := by
      induction n,hmn using Nat.le_induction with
      | base => rfl
      | @succ n hmn ih =>
        calc
          f (n+1) ⟨x,mono (Nat.le_step hmn) x.property⟩ =
              f n ⟨x,mono hmn x.property⟩ := step n ⟨x,mono hmn x.property⟩
          _ = f m x := ih
    have covered (x : U) : ∃ n, x ∈ interior (D n) := by
      apply mem_iUnion.mp
      rw [hcover]
      trivial
    let k (x : U) := (covered x).choose
    let F (x : U) : Plane := f (k x) ⟨x,interior_subset (covered x).choose_spec⟩
    have agrees (n : ℕ) (x : D n) : F x = f n x := by
      let z : D (k x) := ⟨x,interior_subset (covered x).choose_spec⟩
      have h1 := compat (k x) (max (k x) n) (le_max_left _ _) z
      have h2 := compat n (max (k x) n) (le_max_right _ _) x
      exact h1.symm.trans h2
    have Fc : Continuous F := by
      apply continuous_of_continuousOn_iUnion_of_isOpen _ (fun n => isOpen_interior) hcover
      intro n
      apply continuousOn_iff_continuous_domRestrict.mpr
      let inc : interior (D n) → D n := fun x => ⟨x,interior_subset x.property⟩
      have hc : Continuous (fun x : interior (D n) => f n (inc x)) :=
        (f n).continuous.comp (continuous_subtype_val.subtype_mk _)
      convert hc using 1
      funext x
      exact agrees n (inc x)
    have Fi : Function.Injective F := by
      intro x y hxy
      let n := max (k x) (k y)
      let xx : D n := ⟨x,mono (le_max_left _ _) (interior_subset (covered x).choose_spec)⟩
      let yy : D n := ⟨y,mono (le_max_right _ _) (interior_subset (covered y).choose_spec)⟩
      have he : f n xx = f n yy := (agrees n xx).symm.trans (hxy.trans (agrees n yy))
      exact congrArg Subtype.val ((hf n).injective he)
    have Fs : Function.Surjective F := by
      intro y
      obtain ⟨n,hn⟩ := exists_nat_gt ‖y‖
      have hy : y ∈ closedBall (0 : Plane) (n+1) := by
        rw [mem_closedBall,dist_zero_right]
        exact hn.le.trans (by norm_num)
      obtain ⟨x,_,hxy⟩ := target n hy
      exact ⟨x,(agrees (n+1) x).trans hxy⟩
    have Fo : IsOpenMap F := by
      intro V hV
      apply isOpen_iff_mem_nhds.mpr
      rintro y ⟨x,hx,rfl⟩
      let E := chartAt Plane x
      let W := E.target ∩ E.symm ⁻¹' V
      have hW : IsOpen W := E.symm.continuousOn.isOpen_inter_preimage E.open_target hV
      have hxW : E x ∈ W := ⟨E.map_source (mem_chart_source Plane x),by
        change E.symm (E x) ∈ V
        rwa [E.left_inv (mem_chart_source Plane x)]⟩
      let q := F ∘ E.symm
      have hqc : ContinuousOn q W := Fc.continuousOn.comp
        (E.symm.continuousOn.mono inter_subset_left) (fun _ _ => mem_univ _)
      have hqi : InjOn q W := by
        intro a ha b hb he
        exact E.symm.injOn ha.1 hb.1 (Fi he)
      have hqopen : IsOpen (q '' W) :=
        LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
          q W hW hqc hqi
      have hsub : q '' W ⊆ F '' V := by
        rintro z ⟨w,hw,rfl⟩
        exact mem_image_of_mem F hw.2
      have hmem : F x ∈ q '' W := ⟨E x,hxW,by
        change F (E.symm (E x)) = F x
        rw [E.left_inv (mem_chart_source Plane x)]⟩
      exact Filter.mem_of_superset (hqopen.mem_nhds hmem) hsub
    let eqv := Equiv.ofBijective F ⟨Fi,Fs⟩
    have Fquot := Fo.isQuotientMap Fc Fs
    have invc : Continuous eqv.symm := by
      apply Fquot.continuous_iff.mpr
      have heq : eqv.symm ∘ F = id := funext eqv.symm_apply_apply
      rw [heq]
      exact continuous_id
    exact ⟨({
      toEquiv := eqv
      continuous_toFun := Fc
      continuous_invFun := invc } : U ≃ₜ Plane).symm⟩
  letI : LocallyCompactSpace U := ChartedSpace.locallyCompactSpace Plane U
  let A : CompactExhaustion U := CompactExhaustion.choice U
  let P : Set U → Prop := fun D => Nonempty (closedBall (0 : Plane) 1 ≃ₜ D)
  have engulf' (K : Set U) (hK : IsCompact K) :
      ∃ D : Set U, P D ∧ IsCompact D ∧ K ⊆ interior D := by
    obtain ⟨D,hc,he,hi⟩ := engulf K hK
    exact ⟨D,he,hc,hi⟩
  have recursion : ∃ D : ℕ → Set U,
      (∀ n, P (D n) ∧ IsCompact (D n)) ∧
      (∀ n, A n ⊆ interior (D n)) ∧
      (∀ n, D n ⊆ interior (D (n+1))) ∧
      (∀ K : Set U, IsCompact K → ∃ n, K ⊆ interior (D n)) ∧
      (⋃ n, interior (D n)) = univ := by
    classical
    let T := {D : Set U // P D ∧ IsCompact D}
    let choose (K : Set U) (hK : IsCompact K) : T :=
      ⟨(engulf' K hK).choose, (engulf' K hK).choose_spec.1,
        (engulf' K hK).choose_spec.2.1⟩
    have choose_contains (K : Set U) (hK : IsCompact K) :
        K ⊆ interior (choose K hK).val :=
      (engulf' K hK).choose_spec.2.2
    let seq : ℕ → T := fun n => Nat.rec
      (choose (A 0) (A.isCompact 0))
      (fun n prev => choose (A (n+1) ∪ prev.val)
        ((A.isCompact (n+1)).union prev.property.2)) n
    have seq_zero : seq 0 = choose (A 0) (A.isCompact 0) := rfl
    have seq_succ (n : ℕ) : seq (n+1) =
        choose (A (n+1) ∪ (seq n).val)
          ((A.isCompact (n+1)).union (seq n).property.2) := rfl
    have absorbs (n : ℕ) : A n ⊆ interior (seq n).val := by
      cases n with
      | zero => rw [seq_zero]; exact choose_contains (A 0) (A.isCompact 0)
      | succ n =>
        rw [seq_succ]
        exact subset_union_left.trans
          (choose_contains _ ((A.isCompact (n+1)).union (seq n).property.2))
    refine ⟨fun n => (seq n).val, fun n => (seq n).property, absorbs, ?_, ?_, ?_⟩
    · intro n
      change (seq n).val ⊆ interior (seq (n+1)).val
      rw [seq_succ]
      exact subset_union_right.trans
        (choose_contains _ ((A.isCompact (n+1)).union (seq n).property.2))
    · intro K hK
      obtain ⟨n, hn⟩ := A.exists_superset_of_isCompact hK
      exact ⟨n, hn.trans (absorbs n)⟩
    · apply eq_univ_of_forall
      intro x
      obtain ⟨n, hn⟩ := A.exists_mem x
      exact mem_iUnion.mpr ⟨n, absorbs n hn⟩
  obtain ⟨D,hD,_,hnested,_,hcover⟩ := recursion
  exact reconstruct D (fun n => (hD n).1.some) hnested hcover

end CurveComplex.LocalSurgery
