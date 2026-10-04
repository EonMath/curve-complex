import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalSingleBandWholeStraightening

open Set Topology Schoenflies CurveComplex

/-- Explicit additive correction of an ACTUAL equivariant plane isotopy.
No claim that the raw isotopy fixes a puncture is used. -/
theorem actual_equivariant_plane_isotopy_has_point_fixed_normalization
    (H : AmbientIsotopy Plane) (T : ℝ) (p : Plane)
    (hHeq : ∀ t (i : ℤ×ℤ) z,
      H.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        H.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) :
    ∃ P : AmbientIsotopy Plane,
      (∀ t z, P.map (t,z)=H.map (t,z)-H.map (t,p)+p) ∧
      (∀ t, P.map (t,p)=p) ∧
      (∀ t (i : ℤ×ℤ) z,
        P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) ∧
      (∀ t (i : ℤ×ℤ),
        P.map (t,p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
          p+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T)) := by
  let P : AmbientIsotopy Plane := {
    map := ⟨fun tx => H.map tx-H.map (tx.1,p)+p,by fun_prop⟩
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := H.homeomorphism_at t
      refine ⟨e.trans (Homeomorph.addRight (-H.map (t,p)+p)),?_⟩
      intro z
      change e z+(-H.map (t,p)+p)=H.map (t,z)-H.map (t,p)+p
      rw [he]
      abel
    at_zero := by
      intro z
      change H.map (⟨0,by norm_num⟩,z)-H.map (⟨0,by norm_num⟩,p)+p=z
      rw [H.at_zero,H.at_zero]
      abel }
  have hP (t : Interval) (z : Plane) : P.map (t,z)=H.map (t,z)-H.map (t,p)+p := rfl
  have hFix (t : Interval) : P.map (t,p)=p := by rw [hP]; abel
  have hEq (t : Interval) (i : ℤ×ℤ) (z : Plane) :
      P.map (t,z+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T))=
        P.map (t,z)+Plane.mk ((i.1:ℝ)*T) ((i.2:ℝ)*T) := by
    rw [hP,hP,hHeq]
    abel
  exact ⟨P,hP,hFix,hEq,by intro t i; rw [hEq,hFix]⟩

#print axioms actual_equivariant_plane_isotopy_has_point_fixed_normalization
