import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.CollapsedHalfCollarModel
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalDiskArcLift
import Mathlib.Analysis.Convex.GaugeRescale

open CurveComplex Set Topology Schoenflies
namespace ActualHarerDiskGluing

/-- A disk-to-square homeomorphism preserving the full boundary sets. -/
theorem unit_disk_square_boundary_homeomorph :
    ∃ e : Metric.closedBall (0 : Plane) 1 ≃ₜ (Interval × Interval),
      e '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = squareBoundary := by
  classical
  obtain ⟨G,hGi,hGc,hGf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (Plane.convex_closedSquare 0 1)
    (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
    (Plane.isBounded_closedSquare 0 1)
  have hGc' : G '' Plane.closedSquare 0 1 = Metric.closedBall (0 : Plane) 1 := by
    simpa only [(Plane.isClosed_closedSquare 0 1).closure_eq] using hGc
  have hGf' : G '' modelCurve = Metric.sphere (0 : Plane) 1 := by
    simpa only [modelCurve_eq_frontier] using hGf
  let sq : C(Interval × Interval, Plane.closedSquare 0 1) := ⟨fun z =>
    ⟨Plane.mk (2*(z.1:ℝ)-1) (2*(z.2:ℝ)-1),by
      rw [Plane.closedSquare_eq_inter]
      norm_num [Plane.mk]
      constructor <;> constructor <;> linarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]⟩,
    by fun_prop⟩
  have hsqb (z : Interval × Interval) : (sq z).val ∈ modelCurve ↔ z ∈ squareBoundary := by
    rw [modelCurve_eq_sides]
    simp only [mem_union,mem_sideTop,mem_sideLeft,mem_sideBottom,mem_sideRight]
    have hx : |2*(z.1:ℝ)-1|≤1 := abs_le.mpr ⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩
    have hy : |2*(z.2:ℝ)-1|≤1 := abs_le.mpr ⟨by linarith [z.2.property.1],by linarith [z.2.property.2]⟩
    change ((2*(z.2:ℝ)-1=1 ∧ |2*(z.1:ℝ)-1|≤1) ∨
      (2*(z.1:ℝ)-1= -1 ∧ |2*(z.2:ℝ)-1|≤1)) ∨
      (2*(z.2:ℝ)-1= -1 ∧ |2*(z.1:ℝ)-1|≤1) ∨
      (2*(z.1:ℝ)-1=1 ∧ |2*(z.2:ℝ)-1|≤1) ↔ _
    simp only [hx,hy,and_true,squareBoundary,mem_setOf_eq]
    have h0 (t : Interval) : 2*(t:ℝ)-1= -1 ↔ t=0 := by
      constructor
      · intro he; apply Subtype.ext; change (t:ℝ)=0; linarith
      · rintro rfl; norm_num
    have h1 (t : Interval) : 2*(t:ℝ)-1=1 ↔ t=1 := by
      constructor
      · intro he; apply Subtype.ext; change (t:ℝ)=1; linarith
      · rintro rfl; norm_num
    rw [h0,h0,h1,h1]
    tauto
  have hi : Function.Injective sq := by
    intro x y he
    apply Prod.ext <;> apply Subtype.ext
    · have h := congrArg (fun z => z.val 0) he
      change 2*(x.1:ℝ)-1=2*(y.1:ℝ)-1 at h
      linarith
    · have h := congrArg (fun z => z.val 1) he
      change 2*(x.2:ℝ)-1=2*(y.2:ℝ)-1 at h
      linarith
  have hs : Function.Surjective sq := by
    intro z
    have hp := (Plane.closedSquare_eq_inter (0 : Plane) 1).le z.property
    norm_num only [mem_inter_iff,mem_setOf_eq,WithLp.ofLp_zero,Pi.zero_apply,zero_sub,zero_add] at hp
    refine ⟨(⟨(z.val 0+1)/2,⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩⟩,
      ⟨(z.val 1+1)/2,⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩⟩),?_⟩
    apply Subtype.ext
    ext i
    fin_cases i <;> dsimp [sq,Plane.mk] <;> ring
  let f : Interval × Interval ≃ₜ Plane.closedSquare 0 1 :=
    sq.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective sq ⟨hi,hs⟩)
  let k := (G.image (Plane.closedSquare 0 1)).trans (Homeomorph.setCongr hGc')
  let j := f.trans k
  refine ⟨j.symm,?_⟩
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    have he : G ((f (j.symm x)).val) = x.val := congrArg Subtype.val (j.apply_symm_apply x)
    have hm : (f (j.symm x)).val ∈ modelCurve := by
      have hx' : G ((f (j.symm x)).val) ∈ Metric.sphere (0 : Plane) 1 := he.symm ▸ hx
      rw [← hGf'] at hx'
      obtain ⟨y,hy,he'⟩ := hx'
      exact G.injective he' ▸ hy
    exact (hsqb _).mp hm
  · intro hz
    refine ⟨j z,?_,j.symm_apply_apply z⟩
    change G ((sq z).val) ∈ Metric.sphere (0 : Plane) 1
    rw [← hGf']
    exact ⟨_,(hsqb z).mpr hz,rfl⟩

end ActualHarerDiskGluing
