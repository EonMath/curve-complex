import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualUpperPortRectangle
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualRectangleCoordinateBounds
namespace CurveComplex
open Set Schoenflies
set_option maxHeartbeats 5000000

/-- Actual first-height trimming, literal four boundary curves, two full
port clocks, prescribed filling, whole-image chart localization, and exact
center-edge detection. No filling, rectangle, side join, or incidence
certificate is assumed. -/
theorem actual_positive_ports_produce_localized_upper_rectangle
    (P Q : C(Interval,Plane)) (hP : Topology.IsEmbedding P) (hQ : Topology.IsEmbedding Q)
    (a b δ l u : ℝ) (hab : a<b) (hδ : 0<δ)
    (hP0 : P 0=Plane.mk a 0) (hQ0 : Q 0=Plane.mk b 0)
    (hPpos : ∀ t : Interval,0<(t:ℝ) → 0<P t 1)
    (hQpos : ∀ t : Interval,0<(t:ℝ) → 0<Q t 1)
    (hδP : δ<P 1 1) (hδQ : δ<Q 1 1)
    (hseparate : ∀ s t,P s 0<Q t 0)
    (hPloc : ∀ t,l≤P t 0 ∧ P t 0≤u)
    (hQloc : ∀ t,l≤Q t 0 ∧ Q t 0≤u) :
    ∃ τ σ : Interval, 0<(τ:ℝ) ∧ 0<(σ:ℝ) ∧
    ∃ B : Interval × Interval → Plane, Topology.IsEmbedding B ∧
      (∀ t,B (t,0)=Plane.mk (a+(b-a)*(t:ℝ)) 0) ∧
      (∀ t,B (0,t)=P ⟨(τ:ℝ)*(t:ℝ),by constructor <;>
        nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩) ∧
      (∀ t,B (1,t)=Q ⟨(σ:ℝ)*(t:ℝ),by constructor <;>
        nlinarith [σ.property.1,σ.property.2,t.property.1,t.property.2]⟩) ∧
      (∀ t,B (t,1)=Plane.mk (P τ 0+(Q σ 0-P τ 0)*(t:ℝ)) δ) ∧
      (∀ z,l≤B z 0 ∧ B z 0≤u ∧ 0≤B z 1 ∧ B z 1≤δ) ∧
      (∀ z,B z 1=0 ↔ z.2=0) := by
  have hPzero : P 0 1=0 := by rw [hP0]; rfl
  have hQzero : Q 0 1=0 := by rw [hQ0]; rfl
  obtain ⟨τ,hτ,E,hE,hElit,hE0,hE1,hEint,hEz,hEh⟩ :=
    actual_positive_port_first_height P hP hPzero hPpos δ hδ hδP
  obtain ⟨σ,hσ,R,hR,hRlit,hR0,hR1,hRint,hRz,hRh⟩ :=
    actual_positive_port_first_height Q hQ hQzero hQpos δ hδ hδQ
  have hEone : E 1=P τ := by rw [hElit]; apply congrArg P; apply Subtype.ext; simp
  have hRone : R 1=Q σ := by rw [hRlit]; apply congrArg Q; apply Subtype.ext; simp
  have hER : Disjoint (Set.range E) (Set.range R) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨s,rfl⟩ ⟨t,he⟩
    have hh := hseparate
      ⟨(τ:ℝ)*(s:ℝ),by constructor <;> nlinarith [τ.property.1,τ.property.2,s.property.1,s.property.2]⟩
      ⟨(σ:ℝ)*(t:ℝ),by constructor <;> nlinarith [σ.property.1,σ.property.2,t.property.1,t.property.2]⟩
    rw [← hElit,← hRlit] at hh
    rw [he] at hh
    exact lt_irrefl _ hh
  have hupper : E 1 0<R 1 0 := by rw [hEone,hRone]; exact hseparate τ σ
  obtain ⟨C,D,hC,hD,hClit,hDlit,hCE,hCR,hDE,hDR,hCD,B,hB,hBC,hBD,hBE,hBR⟩ :=
    actual_first_height_ports_prescribed_upper_rectangle E R hE hR a b δ hab hδ
      (hE0.trans hP0) (hR0.trans hQ0) hEz hRz hEh hRh hupper hER
  have hEall (t : Interval) : 0≤E t 1 ∧ E t 1≤δ := by
    by_cases ht0 : t=0
    · rw [ht0,hE0,hPzero]; exact ⟨le_refl _,hδ.le⟩
    by_cases ht1 : t=1
    · rw [ht1,hE1]; exact ⟨hδ.le,le_refl _⟩
    have hh := hEint t
      (lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)))
      (lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he)))
    exact ⟨hh.1.le,hh.2.le⟩
  have hRall (t : Interval) : 0≤R t 1 ∧ R t 1≤δ := by
    by_cases ht0 : t=0
    · rw [ht0,hR0,hQzero]; exact ⟨le_refl _,hδ.le⟩
    by_cases ht1 : t=1
    · rw [ht1,hR1]; exact ⟨hδ.le,le_refl _⟩
    have hh := hRint t
      (lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm)))
      (lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he)))
    exact ⟨hh.1.le,hh.2.le⟩
  have hCy : ∀ t,C t 1=0 := by intro t; rw [hClit]; rfl
  have hDy : ∀ t,D t 1=δ := by intro t; rw [hDlit]; rfl
  have hEslab : ∀ t,l≤E t 0 ∧ E t 0≤u := by intro t; rw [hElit]; exact hPloc _
  have hRslab : ∀ t,l≤R t 0 ∧ R t 0≤u := by intro t; rw [hRlit]; exact hQloc _
  have haslab : l≤a ∧ a≤u := by simpa [hP0,Plane.mk] using hPloc 0
  have hbslab : l≤b ∧ b≤u := by simpa [hQ0,Plane.mk] using hQloc 0
  have hCslab (t : Interval) : l≤C t 0 ∧ C t 0≤u := by
    rw [hClit]
    change l≤a+(b-a)*(t:ℝ) ∧ a+(b-a)*(t:ℝ)≤u
    constructor <;> nlinarith [haslab.1,haslab.2,hbslab.1,hbslab.2,t.property.1,t.property.2]
  have hDslab (t : Interval) : l≤D t 0 ∧ D t 0≤u := by
    rw [hDlit]
    change l≤E 1 0+(R 1 0-E 1 0)*(t:ℝ) ∧ E 1 0+(R 1 0-E 1 0)*(t:ℝ)≤u
    constructor <;> nlinarith [(hEslab 1).1,(hEslab 1).2,(hRslab 1).1,(hRslab 1).2,t.property.1,t.property.2]
  have hboundary (z : Interval × Interval)
      (hz : z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) :
      l≤B z 0 ∧ B z 0≤u ∧ 0≤B z 1 ∧ B z 1≤δ := by
    rcases hz with hz|hz|hz|hz
    · have he : z=(0,z.2) := Prod.ext hz rfl
      rw [he,hBE]
      exact ⟨(hEslab _).1,(hEslab _).2,(hEall _).1,(hEall _).2⟩
    · have he : z=(1,z.2) := Prod.ext hz rfl
      rw [he,hBR]
      exact ⟨(hRslab _).1,(hRslab _).2,(hRall _).1,(hRall _).2⟩
    · have he : z=(z.1,0) := Prod.ext rfl hz
      rw [he,hBC,hCy]
      exact ⟨(hCslab _).1,(hCslab _).2,le_refl _,hδ.le⟩
    · have he : z=(z.1,1) := Prod.ext rfl hz
      rw [he,hBD,hDy]
      exact ⟨(hDslab _).1,(hDslab _).2,hδ.le,le_refl _⟩
  have hall (z : Interval × Interval) : l≤B z 0 ∧ B z 0≤u ∧ 0≤B z 1 ∧ B z 1≤δ :=
    ⟨actual_embedded_rectangle_coordinate_lower_bound B hB 0 l (fun z hz => (hboundary z hz).1) z,
     actual_embedded_rectangle_coordinate_upper_bound B hB 0 u (fun z hz => (hboundary z hz).2.1) z,
     actual_embedded_rectangle_coordinate_lower_bound B hB 1 0 (fun z hz => (hboundary z hz).2.2.1) z,
     actual_embedded_rectangle_coordinate_upper_bound B hB 1 δ (fun z hz => (hboundary z hz).2.2.2) z⟩
  refine ⟨τ,σ,hτ,hσ,B,hB,fun t => (hBC t).trans (hClit t),
    fun t => (hBE t).trans (hElit t),fun t => (hBR t).trans (hRlit t),?_,hall,?_⟩
  · intro t
    rw [hBD,hDlit,hEone,hRone]
  · intro z
    constructor
    · intro hz
      rcases actual_embedded_rectangle_coordinate_equality_on_boundary B hB 1 0
        (fun z => (hall z).2.2.1) z hz with he|he|he|he
      · have hzz : z=(0,z.2) := Prod.ext he rfl
        rw [hzz,hBE] at hz
        exact (hEz _).mp hz
      · have hzz : z=(1,z.2) := Prod.ext he rfl
        rw [hzz,hBR] at hz
        exact (hRz _).mp hz
      · exact he
      · have hzz : z=(z.1,1) := Prod.ext rfl he
        rw [hzz,hBD,hDy] at hz
        linarith
    · intro hz
      have hzz : z=(z.1,0) := Prod.ext rfl hz
      rw [hzz,hBC,hCy]
end CurveComplex
