import CurveComplexGenusTwo.Dictionary.Circle24.RadialCellLift
import CurveComplexGenusTwo.Dictionary.OneBranchDiscBoundary
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 4000000

/-- Affine radial contraction of a closed disk to its actual interior mark. -/
def discRadialContraction (m : Metric.closedBall (0:Schoenflies.Plane) 1)
    (r : Interval) : C(Metric.closedBall (0:Schoenflies.Plane) 1,
      Metric.closedBall (0:Schoenflies.Plane) 1) :=
  ⟨fun z => ⟨(1-(r:ℝ)) • m.val + (r:ℝ) • z.val,
      (convex_closedBall (0:Schoenflies.Plane) 1) m.property z.property
        (sub_nonneg.mpr r.property.2) r.property.1 (by ring)⟩,
    by fun_prop⟩

private theorem radial_mark_fixed (m : Metric.closedBall (0:Schoenflies.Plane) 1)
    (r : Interval) : discRadialContraction m r m = m := by
  apply Subtype.ext
  change (1-(r:ℝ)) • m.val + (r:ℝ) • m.val = m.val
  rw [← add_smul]
  simp

private theorem radial_injective (m : Metric.closedBall (0:Schoenflies.Plane) 1)
    (r : Interval) (hr : 0 < (r:ℝ)) : Function.Injective (discRadialContraction m r) := by
  intro z z' he
  apply Subtype.ext
  have h := congrArg Subtype.val he
  change (1-(r:ℝ)) • m.val + (r:ℝ) • z.val =
    (1-(r:ℝ)) • m.val + (r:ℝ) • z'.val at h
  exact smul_right_injective Schoenflies.Plane (ne_of_gt hr) (add_left_cancel h)

/-- The full radial filling of any embedded one-mark disk lifts continuously,
with exact deck-swapped angular edges at every radius. An arbitrary boundary
anchor is preserved, allowing matching to an actual corridor sheet. -/
theorem one_mark_disc_anchored_radial_filling
    (M : HyperellipticModel E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0 = β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β = {z | ‖z.val‖=1})
    (e : E) (he : M.cover.projection e = f (β 0)) :
    ∃ Γ : C(Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,E),
      Γ ⟨(1,0),by simp⟩ = e ∧
      (∀ r t : Interval, M.cover.projection (Γ ⟨(r.val,t.val),⟨r.property,t.property⟩⟩) =
        f (discRadialContraction m r (β t))) ∧
      (∀ r : Interval, Γ ⟨(r.val,1),⟨r.property,by simp⟩⟩ =
        M.cover.deck (Γ ⟨(r.val,0),⟨r.property,by simp⟩⟩)) ∧
      (∀ t t' : Interval, Γ ⟨(0,t.val),⟨by simp,t.property⟩⟩ =
        Γ ⟨(0,t'.val),⟨by simp,t'.property⟩⟩) := by
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  let : T2Space S := M.sphere.isEmbedding.t2Space
  let R : Set (ℝ × ℝ) := Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1
  let rad : C(R,Interval) := ⟨fun z => ⟨z.val.1,z.property.1⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
  let ang : C(R,Interval) := ⟨fun z => ⟨z.val.2,z.property.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩
  let A : C(R,Metric.closedBall (0:Schoenflies.Plane) 1) :=
    ⟨fun z => discRadialContraction m (rad z) (β (ang z)),
      by
      unfold discRadialContraction
      exact (((continuous_const.sub (continuous_subtype_val.comp rad.continuous)).smul
        continuous_const).add ((continuous_subtype_val.comp rad.continuous).smul
          (continuous_subtype_val.comp (β.continuous.comp ang.continuous)))).subtype_mk _⟩
  let H : C(R,S) := f.comp A
  have hcenter (z : R) (hz : z.val.1=0) : H z = f m := by
    apply congrArg f
    apply Subtype.ext
    change (1-z.val.1) • m.val + z.val.1 • (β (ang z)).val = m.val
    simp [hz]
  have havoid (z : R) (hz : 0 < z.val.1) : H z ∉ M.cover.branch := by
    intro hb
    have hAz : A z=m := (honly _).mp hb
    have hβm : β (ang z)=m := radial_injective m (rad z) hz
      (hAz.trans (radial_mark_fixed m (rad z)).symm)
    have hn : ‖(β (ang z)).val‖=1 := by
      have hh := Set.mem_range_self (ang z) (f := β)
      rw [hrange] at hh
      exact hh
    rw [hβm] at hn
    linarith
  have hanchor : M.cover.projection e = H ⟨(1,0),by simp [R]⟩ := by
    convert he using 1
    apply congrArg f
    apply Subtype.ext
    simp [A,discRadialContraction,rad,ang]
  obtain ⟨Γ,hΓanchor,hΓπ,hΓcenter⟩ := M.cover.radial_strip_lift_exists_at
    H (f m) ((honly m).mpr rfl) hcenter havoid ⟨(1,0),by simp⟩ e hanchor
  refine ⟨Γ,hΓanchor,?_,?_,?_⟩
  · intro r t
    exact hΓπ ⟨(r.val,t.val),⟨r.property,t.property⟩⟩
  · intro r
    by_cases hr : 0 < (r:ℝ)
    · let f' := f.comp (discRadialContraction m r)
      have hf' : IsEmbedding f' :=
        hf.comp (((discRadialContraction m r).continuous.isClosedEmbedding
          (radial_injective m r hr)).isEmbedding)
      have honly' (z) : f' z ∈ M.cover.branch ↔ z=m := by
        change f (discRadialContraction m r z) ∈ M.cover.branch ↔ z=m
        rw [honly]
        constructor
        · intro hz
          exact radial_injective m r hr (hz.trans (radial_mark_fixed m r).symm)
        · intro hz
          rw [hz]
          exact radial_mark_fixed m r
      let γ : C(Interval,E) := ⟨fun t => Γ ⟨(r.val,t.val),⟨r.property,t.property⟩⟩,
        Γ.continuous.comp ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)⟩
      exact M.one_branch_disc_boundary_sheet_exchange f' hf' m hm honly'
        β hends hcoll hrange γ (fun t => hΓπ ⟨(r.val,t.val),⟨r.property,t.property⟩⟩)
    · have hr0 : r.val=0 := le_antisymm (le_of_not_gt hr) r.property.1
      have heq := hΓcenter ⟨(r.val,1),⟨r.property,by simp⟩⟩
        ⟨(r.val,0),⟨r.property,by simp⟩⟩ hr0 hr0
      have hb : M.cover.projection (Γ ⟨(r.val,0),⟨r.property,by simp⟩⟩) ∈ M.cover.branch := by
        rw [hΓπ,hcenter _ hr0]
        exact (honly m).mpr rfl
      exact heq.trans ((M.cover.fixed_iff_branch _).mpr hb).symm
  · intro t t'
    exact hΓcenter _ _ rfl rfl

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.one_mark_disc_anchored_radial_filling
