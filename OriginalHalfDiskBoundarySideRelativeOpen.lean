import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalBRecognitionConsumer
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.HalfPlaneBandOpenness

import CurveComplexGenusTwo.Topology.CapBandGeometry.LocalCapSeam

open Set Topology CurveComplex
open scoped Manifold ContDiff

/-- The strict literal B side of an actual three-side half disk lies in its Q-relative interior. -/
theorem original_half_disk_boundary_side_relative_open
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (a q : C(Interval, ↥Q))
      (M : CoherentEndpointMotion.FreeBoundaryNullGeometry.NullHalfBigonBoundary B a q)
      (e : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q)),
      IsEmbedding e →
      e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range M.first ∪ Set.range M.second ∪ Set.range M.boundarySide →
      Set.range e ∩ B = Set.range M.boundarySide →
      M.boundarySide '' Ioo (0 : Interval) 1 ⊆ interior (Set.range e : Set ↥Q) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro a q M e he hSphere hMeet
  let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
  let E := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let p := E x
  let τ : BandWidth → Interval := fun w =>
    ⟨((w : ℝ) + 1) / 2, by constructor <;> linarith [w.property.1, w.property.2]⟩
  have hτc : Continuous τ := by dsimp [τ]; fun_prop
  have hτi : Function.Injective τ := by
    intro v w h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    dsimp [τ] at hh
    linarith
  let β : BandWidth → ↥Q := fun w => M.boundarySide (τ w)
  have hβc : Continuous β := M.boundarySide.continuous.comp hτc
  have hβi : Function.Injective β := M.boundary_embedded.injective.comp hτi
  have hβsphere (w : BandWidth) : β w ∈
      e '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    rw [hSphere]
    exact Or.inr (mem_range_self _)
  let v : BandWidth → CapBandGeometry.CapDisk := fun w =>
    he.toHomeomorph.symm ⟨β w, image_subset_range _ _ (hβsphere w)⟩
  have hvimage (w : BandWidth) : e (v w) = β w :=
    congrArg Subtype.val (he.toHomeomorph.apply_symm_apply _)
  have hvnorm (w : BandWidth) : ‖(v w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    obtain ⟨z,hz,hzβ⟩ := hβsphere w
    have hvz : v w = z := he.injective ((hvimage w).trans hzβ.symm)
    rw [hvz]
    simpa [Metric.mem_sphere,dist_zero_right] using hz
  have hvc : Continuous v := he.toHomeomorph.symm.continuous.comp (hβc.subtype_mk _)
  have hvi : Function.Injective v := by
    intro w u h
    apply hβi
    exact (hvimage w).symm.trans ((congrArg e h).trans (hvimage u))
  let L : BandWidth × unitInterval → S := fun z =>
    (e (CapBandGeometry.diskRadialStrip v hvnorm z)).val
  have hL : IsEmbedding L := IsEmbedding.subtypeVal.comp
    (he.comp (CapBandGeometry.diskRadialStrip_embedded v hvnorm hvc hvi))
  have hLzero (w : BandWidth) : L (w,0) = (β w).val := by
    dsimp only [L]
    rw [CapBandGeometry.diskRadialStrip_zero, hvimage]
  have hβB (w : BandWidth) : (β w).val ∈ E.symm '' Metric.sphere p R :=
    M.boundary_in_B (τ w)
  have hβsource (w : BandWidth) : (β w).val ∈ E.source := by
    obtain ⟨z,hz,hzβ⟩ := hβB w
    rw [← hzβ]
    exact E.map_target (htarget (Metric.sphere_subset_closedBall hz))
  have hβcoord (w : BandWidth) : E (β w).val ∈ Metric.sphere p R := by
    obtain ⟨z,hz,hzβ⟩ := hβB w
    rw [← hzβ,E.right_inv (htarget (Metric.sphere_subset_closedBall hz))]
    exact hz
  let u : BandWidth → CapBandGeometry.CapDisk := fun w =>
    ⟨R⁻¹ • (E (β w).val - p), by
      rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hR)]
      have hh : ‖E (β w).val - p‖ = R := by
        simpa only [Metric.mem_sphere,dist_eq_norm] using hβcoord w
      rw [hh,inv_mul_cancel₀ hR.ne']⟩
  have hunorm (w : BandWidth) : ‖(u w : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    change ‖R⁻¹ • (E (β w).val - p)‖ = 1
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    have hh : ‖E (β w).val - p‖ = R := by
      simpa only [Metric.mem_sphere,dist_eq_norm] using hβcoord w
    rw [hh,inv_mul_cancel₀ hR.ne']
  have huc : Continuous u := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun w : BandWidth => E (β w).val) :=
      E.continuousOn.comp_continuous
        (continuous_subtype_val.comp hβc) hβsource
    exact (hc.sub continuous_const).const_smul R⁻¹
  have hui : Function.Injective u := by
    intro w z h
    apply hβi
    apply Subtype.ext
    apply E.injOn (hβsource w) (hβsource z)
    have hh := congrArg Subtype.val h
    change R⁻¹ • (E (β w).val - p) = R⁻¹ • (E (β z).val - p) at hh
    exact sub_left_injective ((smul_right_injective _ (inv_ne_zero hR.ne')) hh)
  let d : CapBandGeometry.CapDisk → S := fun z => E.symm (p + R • z.val)
  have hdt (z : CapBandGeometry.CapDisk) : p + R • z.val ∈ E.target := by
    apply htarget
    rw [Metric.mem_closedBall,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hR]
    have hz : ‖z.val‖ ≤ 1 := by
      have hh := z.property
      change dist z.val (0 : EuclideanSpace ℝ (Fin 2)) ≤ 1 at hh
      simpa only [dist_zero_right] using hh
    nlinarith
  have hdc : Continuous d := E.continuousOn_symm.comp_continuous (by fun_prop) hdt
  have hdi : Function.Injective d := by
    intro z w h
    apply Subtype.ext
    have hh := E.symm.injOn (hdt z) (hdt w) h
    exact (smul_right_injective _ hR.ne') (add_left_cancel hh)
  have hd : IsEmbedding d := (hdc.isClosedEmbedding hdi).isEmbedding
  have huimage (w : BandWidth) : d (u w) = (β w).val := by
    change E.symm (p + R • (R⁻¹ • (E (β w).val - p))) = (β w).val
    rw [smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel,
      E.left_inv (hβsource w)]
  let T : BandWidth × unitInterval → S :=
    d ∘ CapBandGeometry.diskRadialStrip u hunorm
  have hT : IsEmbedding T := hd.comp
    (CapBandGeometry.diskRadialStrip_embedded u hunorm huc hui)
  have hTzero (w : BandWidth) : T (w,0) = (β w).val := by
    dsimp only [T,Function.comp_apply]
    rw [CapBandGeometry.diskRadialStrip_zero,huimage]
  have hTQ (z : BandWidth × unitInterval) (hz : T z ∈ Q) : z.2 = 0 := by
    by_contra hn
    have ht : 0 < (z.2 : ℝ) := lt_of_le_of_ne z.2.property.1
      (fun hh => hn (Subtype.ext hh.symm))
    apply hz
    refine ⟨p + R • (CapBandGeometry.diskRadialStrip u hunorm z).val,?_,rfl⟩
    rw [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos hR]
    change R * ‖(1-(z.2:ℝ)/2) • (u z.1).val‖ < R
    rw [norm_smul,Real.norm_eq_abs,hunorm,mul_one,
      abs_of_pos (by linarith [z.2.property.2] : 0 < 1-(z.2:ℝ)/2)]
    nlinarith
  have hseam (w : BandWidth) : L (w,0) = T (w,0) :=
    (hLzero w).trans (hTzero w).symm
  have hLT : range L ∩ range T = range (fun w => L (w,0)) := by
    ext y
    constructor
    · rintro ⟨⟨z,rfl⟩,w,hw⟩
      have hwQ : T w ∈ Q := hw ▸ (e (CapBandGeometry.diskRadialStrip v hvnorm z)).property
      have hw0 := hTQ w hwQ
      refine ⟨w.1,?_⟩
      change L (w.1,0) = L z
      rw [hseam]
      exact (congrArg T (show (w.1,0) = w from Prod.ext rfl hw0.symm)).trans hw
    · rintro ⟨w,rfl⟩
      exact ⟨mem_range_self _,⟨(w,0),(hseam w).symm⟩⟩
  have hsub : (Subtype.val : ↥Q → S) ⁻¹' (range L ∪ range T) ⊆ range e := by
    intro y hy
    rcases hy with ⟨z,hz⟩ | ⟨z,hz⟩
    · exact ⟨CapBandGeometry.diskRadialStrip v hvnorm z,Subtype.ext hz⟩
    · have hz0 := hTQ z (hz ▸ y.property)
      have hyβ : (β z.1).val = y.val := by
        exact (hTzero z.1).symm.trans
          ((congrArg T (show (z.1,0) = z from Prod.ext rfl hz0.symm)).trans hz)
      exact (Subtype.ext hyβ) ▸ image_subset_range _ _ (hβsphere z.1)
  rintro y ⟨t,ht,rfl⟩
  let w : BandWidth := ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have hwlo : (-1 : ℝ) < w := by change -1 < 2*(t:ℝ)-1; linarith [show (0 : ℝ) < t from ht.1]
  have hwhi : (w : ℝ) < 1 := by change 2*(t:ℝ)-1 < 1; linarith [show (t : ℝ) < 1 from ht.2]
  have hτw : τ w = t := by apply Subtype.ext; dsimp [τ,w]; ring
  have hi := glued_half_rectangles_seam_interior_probe L T hL hT hseam hLT w hwlo hwhi
  have hβw : β w = M.boundarySide t := by dsimp only [β]; rw [hτw]
  rw [hLzero,hβw] at hi
  exact interior_maximal
    ((preimage_mono interior_subset).trans hsub)
    (isOpen_interior.preimage continuous_subtype_val) hi
