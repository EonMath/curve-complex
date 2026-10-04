import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourSideBoundaryFaceValues
import Mathlib.Topology.CompactOpen
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Four actual edge movies with fixed common corner values construct a joint
boundary movie, retaining every edge parameter at every time. -/
theorem actual_four_edge_joint_boundary_movie
    {Y : Type} [TopologicalSpace Y] (bl br tl tr : Y)
    (bottom right top left : C(Interval × Interval,Y))
    (hb : ∀ σ, bottom (σ,0)=bl ∧ bottom (σ,1)=br)
    (hr : ∀ σ, right (σ,0)=br ∧ right (σ,1)=tr)
    (ht : ∀ σ, top (σ,0)=tl ∧ top (σ,1)=tr)
    (hl : ∀ σ, left (σ,0)=bl ∧ left (σ,1)=tl) :
    ∃ f : C(Interval × {z : ℝ × ℝ // ‖z‖=1},Y),
      ∀ σ (i : Fin 4) t, f (σ,actualMaxNormSquareBoundaryFace i t)=
        if i.val=0 then bottom (σ,t) else if i.val=1 then right (σ,t)
        else if i.val=2 then top (σ,t) else left (σ,t) := by
  let B : C(Interval,C(Interval,Y)) :=
    (⟨fun z : Interval × Interval => bottom (z.2,z.1),by fun_prop⟩ :
      C(Interval × Interval,Y)).curry
  let R : C(Interval,C(Interval,Y)) :=
    (⟨fun z : Interval × Interval => right (z.2,z.1),by fun_prop⟩ :
      C(Interval × Interval,Y)).curry
  let T : C(Interval,C(Interval,Y)) :=
    (⟨fun z : Interval × Interval => top (z.2,z.1),by fun_prop⟩ :
      C(Interval × Interval,Y)).curry
  let L : C(Interval,C(Interval,Y)) :=
    (⟨fun z : Interval × Interval => left (z.2,z.1),by fun_prop⟩ :
      C(Interval × Interval,Y)).curry
  let pb : Path (ContinuousMap.const Interval bl) (ContinuousMap.const Interval br) :=
    ⟨B,by ext σ; exact (hb σ).1,by ext σ; exact (hb σ).2⟩
  let pr : Path (ContinuousMap.const Interval br) (ContinuousMap.const Interval tr) :=
    ⟨R,by ext σ; exact (hr σ).1,by ext σ; exact (hr σ).2⟩
  let pt : Path (ContinuousMap.const Interval tl) (ContinuousMap.const Interval tr) :=
    ⟨T,by ext σ; exact (ht σ).1,by ext σ; exact (ht σ).2⟩
  let pl : Path (ContinuousMap.const Interval bl) (ContinuousMap.const Interval tl) :=
    ⟨L,by ext σ; exact (hl σ).1,by ext σ; exact (hl σ).2⟩
  obtain ⟨F,hF⟩ := actual_four_side_boundary_face_values pb pr pt pl
  let f : C(Interval × {z : ℝ × ℝ // ‖z‖=1},Y) :=
    ⟨fun z => F.uncurry (z.2,z.1),by fun_prop⟩
  refine ⟨f,?_⟩
  intro σ i t
  have hh := congrArg (fun g : C(Interval,Y) => g σ) (hF i t)
  fin_cases i <;> simpa [f,pb,pr,pt,pl,B,R,T,L] using hh
end CurveComplex.HyperellipticModel
