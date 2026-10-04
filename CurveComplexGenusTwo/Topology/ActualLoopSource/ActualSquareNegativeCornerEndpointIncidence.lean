import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareCornerFaceIncidence
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualScalarMeshBoundaryIncidence
namespace CurveComplex.HyperellipticModel
open Set Topology
attribute [local instance] Classical.propDecidable
/-- Literal negative corner incidence for the actual source mesh on all four
faces. Both face endpoint bits are retained, and no graph or degree is input. -/
theorem actual_square_negative_corner_endpoint_incidence
    (V : Set (ℝ × ℝ)) (f : C({z : ℝ × ℝ // ‖z‖=1},V)) (center : V)
    (m : Fin 4 → ℕ) (mesh : ∀ i,Fin (m i+2) → Interval)
    (hmono : ∀ i,StrictMono (mesh i)) (h0 : ∀ i,mesh i 0=0)
    (h1 : ∀ i,mesh i (Fin.last (m i+1))=1)
    (negative : ∀ i,Fin (m i+1) → Prop)
    (hfirst : ∀ i,(f (actualMaxNormSquareBoundaryFace i 0)).val.2/center.val.2≠0 →
      (negative i 0 ↔ (f (actualMaxNormSquareBoundaryFace i 0)).val.2/center.val.2 < 0))
    (hlast : ∀ i,(f (actualMaxNormSquareBoundaryFace i 1)).val.2/center.val.2≠0 →
      (negative i (Fin.last (m i)) ↔ (f (actualMaxNormSquareBoundaryFace i 1)).val.2/center.val.2 < 0))
    (i : Fin 4) (bit : Fin 2)
    (hneg : (f (actualMaxNormSquareBoundaryFace i (if bit=0 then 0 else 1))).val.2/center.val.2 < 0) :
    {r : (Σ j : Fin 4,{k : Fin (m j+1) // negative j k}) × Fin 2 |
      actualMaxNormSquareBoundaryFace r.1.1
        (mesh r.1.1 (if r.2=0 then r.1.2.val.castSucc else r.1.2.val.succ))=
      actualMaxNormSquareBoundaryFace i (if bit=0 then 0 else 1)}.ncard=2 := by
  classical
  let c := actualMaxNormSquareBoundaryFace i (if bit=0 then 0 else 1)
  have hbound (j : Fin 4) (u : Interval) (he : actualMaxNormSquareBoundaryFace j u=c) : u=0 ∨ u=1 := by
    rcases actual_max_norm_square_boundary_face_collision j i u (if bit=0 then 0 else 1) he with
      ⟨hji,hu⟩ | ⟨hu,_⟩
    · by_cases hb : bit=0
      · exact Or.inl (by simpa [hb] using hu)
      · exact Or.inr (by simpa [hb] using hu)
    · exact hu
  have hlocalUnique (j : Fin 4) (u : Interval) (hu : u=0 ∨ u=1)
      (q r : {k : Fin (m j+1) // negative j k} × Fin 2)
      (hq : mesh j (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=u)
      (hr : mesh j (if r.2=0 then r.1.val.castSucc else r.1.val.succ)=u) : q=r := by
    have hc : {r : {k : Fin (m j+1) // negative j k} × Fin 2 |
        mesh j (if r.2=0 then r.1.val.castSucc else r.1.val.succ)=u}.ncard≤1 := by
      rcases hu with rfl | rfl
      · rw [actual_scalar_mesh_initial_endpoint_incidence (m j) (mesh j) (hmono j) (h0 j) (negative j)]
        split_ifs <;> omega
      · rw [actual_scalar_mesh_terminal_endpoint_incidence (m j) (mesh j) (hmono j) (h1 j) (negative j)]
        split_ifs <;> omega
    exact (Set.ncard_le_one (Set.toFinite _)).mp hc q hq r hr
  have heq : {r : (Σ j : Fin 4,{k : Fin (m j+1) // negative j k}) × Fin 2 |
      actualMaxNormSquareBoundaryFace r.1.1
        (mesh r.1.1 (if r.2=0 then r.1.2.val.castSucc else r.1.2.val.succ))=c}.ncard=
      {r : Fin 4 × Interval | actualMaxNormSquareBoundaryFace r.1 r.2=c}.ncard := by
    apply Set.ncard_congr (fun r _ => (r.1.1,mesh r.1.1
      (if r.2=0 then r.1.2.val.castSucc else r.1.2.val.succ)))
    · intro r hr
      exact hr
    · rintro ⟨⟨j,q⟩,qb⟩ ⟨⟨k,r⟩,rb⟩ hq hr he
      have hjk := congrArg Prod.fst he
      change j=k at hjk
      cases hjk
      have hp := congrArg Prod.snd he
      change mesh j (if qb=0 then q.val.castSucc else q.val.succ)=
        mesh j (if rb=0 then r.val.castSucc else r.val.succ) at hp
      have hh : (q,qb)=(r,rb) := hlocalUnique j _ (hbound j _ hq) (q,qb) (r,rb) rfl hp.symm
      cases hh
      rfl
    · rintro ⟨j,u⟩ hu
      change actualMaxNormSquareBoundaryFace j u=c at hu
      have hn : (f (actualMaxNormSquareBoundaryFace j u)).val.2/center.val.2 < 0 := by
        rw [hu]
        exact hneg
      rcases hbound j u hu with rfl | rfl
      · have hj : negative j 0 := (hfirst j (ne_of_lt hn)).mpr hn
        refine ⟨(⟨j,⟨0,hj⟩⟩,0),?_,?_⟩
        · change actualMaxNormSquareBoundaryFace j (mesh j 0)=c
          rw [h0]
          exact hu
        · exact Prod.ext (by rfl) (by simpa using h0 j)
      · have hj : negative j (Fin.last (m j)) := (hlast j (ne_of_lt hn)).mpr hn
        refine ⟨(⟨j,⟨Fin.last (m j),hj⟩⟩,1),?_,?_⟩
        · change actualMaxNormSquareBoundaryFace j (mesh j (Fin.last (m j+1)))=c
          rw [h1]
          exact hu
        · exact Prod.ext (by rfl) (by simpa using h1 j)
  rw [heq]
  exact actual_square_corner_face_parameter_count i bit
end CurveComplex.HyperellipticModel
