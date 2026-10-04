import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.FirstHeightPortTrim
import CurveComplexGenusTwo.Topology.ActualPrescribedFourArcRectangle
namespace CurveComplex
open Set Schoenflies
set_option maxHeartbeats 3000000

/-- Construct the actual horizontal side join and all four corner-only
incidences, then consume the approved prescribed four-arc rectangle producer.
The two full port clocks and literal original middle-axis clock are retained. -/
theorem actual_first_height_ports_prescribed_upper_rectangle
    (E R : C(Interval,Plane)) (hE : Topology.IsEmbedding E) (hR : Topology.IsEmbedding R)
    (a b δ : ℝ) (hab : a<b) (hδ : 0<δ)
    (hE0 : E 0=Plane.mk a 0) (hR0 : R 0=Plane.mk b 0)
    (hEzero : ∀ t, E t 1=0 ↔ t=0) (hRzero : ∀ t, R t 1=0 ↔ t=0)
    (hEheight : ∀ t, E t 1=δ ↔ t=1) (hRheight : ∀ t, R t 1=δ ↔ t=1)
    (hupper : E 1 0<R 1 0) (hER : Disjoint (Set.range E) (Set.range R)) :
    ∃ P Q : C(Interval,Plane), Topology.IsEmbedding P ∧ Topology.IsEmbedding Q ∧
      (∀ t, P t=Plane.mk (a+(b-a)*(t:ℝ)) 0) ∧
      (∀ t, Q t=Plane.mk (E 1 0+(R 1 0-E 1 0)*(t:ℝ)) δ) ∧
      (∀ s t, P s=E t → s=0 ∧ t=0) ∧
      (∀ s t, P s=R t → s=1 ∧ t=0) ∧
      (∀ s t, Q s=E t → s=0 ∧ t=1) ∧
      (∀ s t, Q s=R t → s=1 ∧ t=1) ∧
      Disjoint (Set.range P) (Set.range Q) ∧
    ∃ B : Interval × Interval → Plane, Topology.IsEmbedding B ∧
      (∀ t, B (t,0)=P t) ∧ (∀ t, B (t,1)=Q t) ∧
      (∀ t, B (0,t)=E t) ∧ (∀ t, B (1,t)=R t) := by
  let P : C(Interval,Plane) := ⟨fun t => Plane.mk (a+(b-a)*(t:ℝ)) 0,by fun_prop⟩
  let Q : C(Interval,Plane) := ⟨fun t => Plane.mk (E 1 0+(R 1 0-E 1 0)*(t:ℝ)) δ,by fun_prop⟩
  have hPi : Function.Injective P := by
    intro s t he
    apply Subtype.ext
    have hh := congrArg (fun x : Plane => x 0) he
    change a+(b-a)*(s:ℝ)=a+(b-a)*(t:ℝ) at hh
    nlinarith
  have hQi : Function.Injective Q := by
    intro s t he
    apply Subtype.ext
    have hh := congrArg (fun x : Plane => x 0) he
    change E 1 0+(R 1 0-E 1 0)*(s:ℝ)=E 1 0+(R 1 0-E 1 0)*(t:ℝ) at hh
    nlinarith
  have hP : Topology.IsEmbedding P := (P.continuous.isClosedEmbedding hPi).isEmbedding
  have hQ : Topology.IsEmbedding Q := (Q.continuous.isClosedEmbedding hQi).isEmbedding
  have hP0 : P 0=E 0 := by rw [hE0]; ext i; fin_cases i <;> simp [P,Plane.mk]
  have hP1 : P 1=R 0 := by rw [hR0]; ext i; fin_cases i <;> simp [P,Plane.mk]
  have hQ0 : Q 0=E 1 := by
    ext i; fin_cases i
    · simp [Q,Plane.mk]
    · exact (hEheight 1).mpr rfl |>.symm
  have hQ1 : Q 1=R 1 := by
    ext i; fin_cases i
    · simp [Q,Plane.mk]
    · exact (hRheight 1).mpr rfl |>.symm
  have hPE : ∀ s t, P s=E t → s=0 ∧ t=0 := by
    intro s t he
    have hh := congrArg (fun x : Plane => x 1) he
    have ht : t=0 := (hEzero t).mp hh.symm
    subst t
    exact ⟨hP.injective (he.trans hP0.symm),rfl⟩
  have hPR : ∀ s t, P s=R t → s=1 ∧ t=0 := by
    intro s t he
    have hh := congrArg (fun x : Plane => x 1) he
    have ht : t=0 := (hRzero t).mp hh.symm
    subst t
    exact ⟨hP.injective (he.trans hP1.symm),rfl⟩
  have hQE : ∀ s t, Q s=E t → s=0 ∧ t=1 := by
    intro s t he
    have hh := congrArg (fun x : Plane => x 1) he
    have ht : t=1 := (hEheight t).mp hh.symm
    subst t
    exact ⟨hQ.injective (he.trans hQ0.symm),rfl⟩
  have hQR : ∀ s t, Q s=R t → s=1 ∧ t=1 := by
    intro s t he
    have hh := congrArg (fun x : Plane => x 1) he
    have ht : t=1 := (hRheight t).mp hh.symm
    subst t
    exact ⟨hQ.injective (he.trans hQ1.symm),rfl⟩
  have hPQ : Disjoint (Set.range P) (Set.range Q) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨s,rfl⟩ ⟨t,he⟩
    have hh := congrArg (fun x : Plane => x 1) he
    change δ=0 at hh
    linarith
  obtain ⟨B,hB,hBP,hBQ,hBE,hBR⟩ :=
    CurveComplex.G3Review.actual_four_arc_cycle_has_prescribed_embedded_square P Q E R hP hQ hE hR
      hP0 hP1 hQ0 hQ1 hPE hPR hQE hQR hPQ hER
  exact ⟨P,Q,hP,hQ,fun _ => rfl,fun _ => rfl,hPE,hPR,hQE,hQR,hPQ,B,hB,hBP,hBQ,hBE,hBR⟩
end CurveComplex
