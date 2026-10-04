import CurveComplexGenusTwo.Dictionary.Circle24.ActualOneMarkDisk
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 6000000

/-- An exact ordinary disk chart for any positive-dimensional closed rectangle. -/
theorem closed_rectangle_disk_chart (a b c d : ℝ) (hab : a < b) (hcd : c < d) :
    ∃ h : Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ Icc a b ×ˢ Icc c d,
      (∀ z, (h z).val ∈ interior (Icc a b ×ˢ Icc c d) ↔ ‖z.val‖ < 1) ∧
      (∀ z, (h z).val ∈ frontier (Icc a b ×ˢ Icc c d) ↔ ‖z.val‖ = 1) := by
  let R : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d
  let e : (ℝ × ℝ) ≃L[ℝ] Schoenflies.Plane :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 2) ℝ).symm
  let K := e '' R
  have hcompact : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image e.continuous
  have hconvex : Convex ℝ K := ((convex_Icc a b).prod (convex_Icc c d)).linear_image e.toLinearEquiv.toLinearMap
  have hne : (interior K).Nonempty := by
    refine ⟨e ((a+b)/2,(c+d)/2),?_⟩
    change e.toHomeomorph ((a+b)/2,(c+d)/2) ∈ interior (e.toHomeomorph '' R)
    rw [← e.toHomeomorph.image_interior]
    refine ⟨((a+b)/2,(c+d)/2),?_,rfl⟩
    simp only [R,interior_prod_eq,interior_Icc,mem_prod,mem_Ioo]
    constructor <;> constructor <;> linarith
  obtain ⟨g,hgi,hgc,hgf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    hconvex hne hcompact.isBounded
  have hgK : g '' K=Metric.closedBall (0:Schoenflies.Plane) 1 := by
    simpa only [hcompact.isClosed.closure_eq] using hgc
  let u : K ≃ₜ Metric.closedBall (0:Schoenflies.Plane) 1 :=
    Homeomorph.sets g (by
      ext x
      constructor
      · intro hx
        rw [← hgK]
        exact Set.mem_image_of_mem g hx
      · intro hx
        rw [← hgK] at hx
        obtain ⟨y,hy,hyx⟩ := hx
        exact g.injective hyx ▸ hy)
  let v : R ≃ₜ K := e.toHomeomorph.image R
  let h := u.symm.trans v.symm
  have hval (z) : e (h z).val=g.symm z.val := by
    change e (v.symm (u.symm z)).val=(u.symm z).val
    exact congrArg Subtype.val (v.apply_symm_apply _)
  refine ⟨h,?_,?_⟩
  · intro z
    constructor
    · intro hz
      have hmem : e (h z).val ∈ interior K := by
        change e.toHomeomorph (h z).val ∈ interior (e.toHomeomorph '' R)
        rw [← e.toHomeomorph.image_interior]
        exact Set.mem_image_of_mem e hz
      rw [hval] at hmem
      have hzball : z.val ∈ Metric.ball (0:Schoenflies.Plane) 1 := by
        rw [← hgi]
        exact ⟨g.symm z.val,hmem,g.apply_symm_apply _⟩
      simpa only [Metric.mem_ball,dist_zero_right] using hzball
    · intro hz
      have hzball : z.val ∈ Metric.ball (0:Schoenflies.Plane) 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hz
      rw [← hgi] at hzball
      obtain ⟨y,hy,hyz⟩ := hzball
      have heq : y=e (h z).val := by rw [hval,← hyz,g.symm_apply_apply]
      rw [heq] at hy
      change e.toHomeomorph (h z).val ∈ interior (e.toHomeomorph '' R) at hy
      rw [← e.toHomeomorph.image_interior] at hy
      obtain ⟨x,hx,hxz⟩ := hy
      exact e.injective hxz ▸ hx
  · intro z
    constructor
    · intro hz
      have hmem : e (h z).val ∈ frontier K := by
        change e.toHomeomorph (h z).val ∈ frontier (e.toHomeomorph '' R)
        rw [← e.toHomeomorph.image_frontier]
        exact Set.mem_image_of_mem e hz
      rw [hval] at hmem
      have hzball : z.val ∈ Metric.sphere (0:Schoenflies.Plane) 1 := by
        rw [← hgf]
        exact ⟨g.symm z.val,hmem,g.apply_symm_apply _⟩
      simpa only [Metric.mem_sphere,dist_zero_right] using hzball
    · intro hz
      have hzball : z.val ∈ Metric.sphere (0:Schoenflies.Plane) 1 := by
        simpa only [Metric.mem_sphere,dist_zero_right] using hz
      rw [← hgf] at hzball
      obtain ⟨y,hy,hyz⟩ := hzball
      have heq : y=e (h z).val := by rw [hval,← hyz,g.symm_apply_apply]
      rw [heq] at hy
      change e.toHomeomorph (h z).val ∈ frontier (e.toHomeomorph '' R) at hy
      rw [← e.toHomeomorph.image_frontier] at hy
      obtain ⟨x,hx,hxz⟩ := hy
      exact e.injective hxz ▸ hx

namespace HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Fill an entire actual one-mark rectangle. Both the source image and its
upstairs full preimage are retained, so the cell can be pasted to a corridor. -/
theorem one_mark_rectangle_full_disk_lift
    (M : HyperellipticModel E S) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (f : C(Icc a b ×ˢ Icc c d,S)) (hf : IsEmbedding f)
    (m : Icc a b ×ˢ Icc c d) (hm : m.val ∈ interior (Icc a b ×ˢ Icc c d))
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m) :
    ∃ fd : C(Metric.closedBall (0:Schoenflies.Plane) 1,S), IsEmbedding fd ∧
      Set.range fd=Set.range f ∧
      fd '' {z | ‖z.val‖=1}=f '' {z | z.val ∈ frontier (Icc a b ×ˢ Icc c d)} ∧
      Nonempty (Metric.closedBall (0:Schoenflies.Plane) 1 ≃ₜ M.cover.projection ⁻¹' Set.range f) := by
  obtain ⟨h,hi,hb⟩ := closed_rectangle_disk_chart a b c d hab hcd
  let fd : C(Metric.closedBall (0:Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
  have hfd : IsEmbedding fd := hf.comp h.isEmbedding
  let md := h.symm m
  have hmd : ‖md.val‖ < 1 := (hi md).mp (by simpa only [md,h.apply_symm_apply] using hm)
  have honlyd (z) : fd z ∈ M.cover.branch ↔ z=md := by
    change f (h z) ∈ M.cover.branch ↔ z=h.symm m
    rw [honly]
    exact h.eq_symm_apply.symm
  have hrange : Set.range fd=Set.range f := by
    change Set.range (f ∘ h)=Set.range f
    exact h.surjective.range_comp f
  obtain ⟨H⟩ := M.one_mark_closed_disk_full_preimage fd hfd md hmd honlyd
  refine ⟨fd,hfd,hrange,?_,⟨H.trans (Homeomorph.setCongr (congrArg (fun A => M.cover.projection ⁻¹' A) hrange))⟩⟩
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨h z,(hb z).mpr hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    change z.val ∈ frontier (Icc a b ×ˢ Icc c d) at hz
    refine ⟨h.symm z,(hb (h.symm z)).mp (by simpa only [h.apply_symm_apply] using hz),?_⟩
    change f (h (h.symm z))=f z
    rw [h.apply_symm_apply]

end HyperellipticModel
end CurveComplex
#print axioms CurveComplex.closed_rectangle_disk_chart
#print axioms CurveComplex.HyperellipticModel.one_mark_rectangle_full_disk_lift
