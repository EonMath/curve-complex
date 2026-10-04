import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMeshStrictInteriorParameter
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual four-face mesh directions meet only within their own interval or
at true interval endpoints. This is independent of the contact-arc producer. -/
theorem actual_four_face_mesh_direction_collision
    (m : Fin 4 → ℕ) (mesh : ∀ i : Fin 4,Fin (m i+2) → Interval)
    (hmono : ∀ i,StrictMono (mesh i))
    (e f : Σ i : Fin 4,Fin (m i+1)) (t u : Interval)
    (he : actualMaxNormSquareBoundaryFace e.1
      (Icc.convexComb (mesh e.1 e.2.castSucc) (mesh e.1 e.2.succ) t)=
      actualMaxNormSquareBoundaryFace f.1
      (Icc.convexComb (mesh f.1 f.2.castSucc) (mesh f.1 f.2.succ) u)) :
    (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) := by
  rcases e with ⟨i,j⟩
  rcases f with ⟨k,l⟩
  rcases actual_max_norm_square_boundary_face_collision i k _ _ he with ⟨hik,hjl⟩ | ⟨hj,hl⟩
  · cases hik
    rcases actual_ordered_mesh_subinterval_collision (mesh i) (hmono i) j l t u hjl with
      ⟨hjl,htu⟩ | hend
    · cases hjl
      exact Or.inl ⟨rfl,htu⟩
    · exact Or.inr hend
  · right
    exact ⟨actual_mesh_parameter_boundary_endpoint _ _ t
      (hmono i (by change j.val<j.val+1; omega)) hj,
      actual_mesh_parameter_boundary_endpoint _ _ u
        (hmono k (by change l.val<l.val+1; omega)) hl⟩
end CurveComplex.HyperellipticModel
