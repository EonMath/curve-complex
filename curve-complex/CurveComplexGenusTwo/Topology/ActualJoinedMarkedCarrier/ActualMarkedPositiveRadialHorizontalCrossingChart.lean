import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedWholeLocalVerticalTrace
namespace CurveComplex.HyperellipticModel
open Set Topology Metric Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000
set_option linter.unusedVariables false
theorem actual_marked_positive_radial_horizontal_crossing_chart
    (M : HyperellipticModel E S) [T2Space S] (c : EssentialMarkedArc M) (p : S)
      (hp : p ∈ arcInterior M c) (F : OpenPartialHomeomorph S Plane)
      (hpF : p ∈ F.source) (hFMarks : Disjoint F.source (M.cover.branch : Set S))
      (v w : Plane) (hv : 0 < v 1) (hw : w 1 < 0)
      (hmodel : ∀ x ∈ F.source, x ∈ c.val.image ↔
        F x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) w)
      (h : ℝ) (hh : 0 < h) (hph : F p 1=h) :
      ∃ G : OpenPartialHomeomorph S Plane, p ∈ G.source ∧ G p=0 ∧
        G.source ⊆ F.source ∧ Disjoint G.source (M.cover.branch : Set S) ∧
        (∀ x ∈ G.source, x ∈ c.val.image ↔ G x 0=0) ∧
        ∀ x, F x 1=h → G x 1=0 := by
  classical
  have hdet (z : Plane) (hz : z ∈ segment ℝ (0:Plane) v) : v 1*z 0-v 0*z 1=0 := by
    rw [segment_eq_image'] at hz
    obtain ⟨u,hu,he⟩ := hz
    have he0 := congrArg (fun z : Plane => z 0) he
    have he1 := congrArg (fun z : Plane => z 1) he
    change 0+u*(v 0-0)=z 0 at he0
    change 0+u*(v 1-0)=z 1 at he1
    rw [← he0,← he1]
    ring
  have hnegative (z : Plane) (hz : z ∈ segment ℝ (0:Plane) w) : z 1 ≤ 0 := by
    rw [segment_eq_image'] at hz
    obtain ⟨u,hu,he⟩ := hz
    have he1 := congrArg (fun z : Plane => z 1) he
    change 0+u*(w 1-0)=z 1 at he1
    rw [← he1]
    simpa using mul_nonpos_of_nonneg_of_nonpos hu.1 hw.le
  let positiveO : Set S := F.source ∩ F ⁻¹' {z : Plane | 0 < z 1}
  have hPositiveOpen : IsOpen positiveO := F.isOpen_inter_preimage (isOpen_lt continuous_const (by fun_prop))
  let Fpos := F.restrOpen positiveO hPositiveOpen
  have hFposSource : Fpos.source=F.source ∩ positiveO := rfl
  let H : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (v 1*z 0-v 0*z 1) (z 1-h)
    invFun := fun z => Plane.mk ((z 0+v 0*(z 1+h))/(v 1)) (z 1+h)
    left_inv := by
      intro z
      ext i
      fin_cases i
      · change ((v 1*z 0-v 0*z 1)+v 0*((z 1-h)+h))/(v 1)=z 0
        field_simp [ne_of_gt hv]
        ring
      · change (z 1-h)+h=z 1
        ring
    right_inv := by
      intro z
      ext i
      fin_cases i
      · change v 1*((z 0+v 0*(z 1+h))/(v 1))-v 0*(z 1+h)=z 0
        field_simp [ne_of_gt hv]
        ring
      · change (z 1+h)-h=z 1
        ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let FH := Fpos.trans H.toOpenPartialHomeomorph
  have hFHSource : FH.source=Fpos.source := by simp [FH]
  have hFHValue (x : S) : FH x=H (F x) := rfl
  have hpFH : p ∈ FH.source := by
    rw [hFHSource]
    exact ⟨hpF,hpF,by change 0 < F p 1; rw [hph]; exact hh⟩
  have hOldDet (x : S) (hx : x ∈ FH.source) (hc : x ∈ c.val.image) : v 1*F x 0-v 0*F x 1=0 := by
    have hs := hFHSource ▸ hx
    rcases (hmodel x hs.1).mp hc with hvseg|hwseg
    · exact hdet _ hvseg
    · exact False.elim (not_le_of_gt hs.2.2 (hnegative _ hwseg))
  have hCenter : FH p=0 := by
    ext i
    fin_cases i
    · exact hOldDet p hpFH hp.1
    · change F p 1-h=0
      rw [hph]
      ring
  have hFHMarks : Disjoint FH.source (M.cover.branch : Set S) :=
    hFMarks.mono_left (fun x hx => (hFHSource ▸ hx).1)
  obtain ⟨G,hpG,hGp,hGFH,hGValue,hGMarks,hGTrace⟩ :=
    actual_marked_whole_local_vertical_trace M c p hp FH hpFH hCenter hFHMarks
      (fun x hx => hOldDet x hx.2 hx.1)
  refine ⟨G,hpG,hGp,fun x hx => (hFHSource ▸ hGFH hx).1,hGMarks,hGTrace,?_⟩
  intro x hx
  rw [hGValue,hFHValue]
  change F x 1-h=0
  rw [hx]
  ring
end CurveComplex.HyperellipticModel
