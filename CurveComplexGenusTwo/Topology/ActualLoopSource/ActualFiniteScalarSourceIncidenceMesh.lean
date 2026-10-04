import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarNegativeIntervals
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualScalarMeshBoundaryIncidence
namespace CurveComplex.HyperellipticModel
open Set Topology CurveComplex.LocalSurgery
attribute [local instance] Classical.propDecidable
/-- Finite literal scalar contacts construct their incidence mesh, retaining
the ACTUAL midpoint sign definition of every negative interval, and exact
endpoint-bit counts at both original face endpoints. -/
theorem actual_finite_scalar_source_incidence_mesh
    (g : C(Interval,ℝ)) (hf : (g ⁻¹' {0}).Finite) :
    ∃ m : ℕ,∃ mesh : Fin (m+2) → Interval,∃ negative : Fin (m+1) → Prop,
      StrictMono mesh ∧ mesh 0=0 ∧ mesh (Fin.last (m+1))=1 ∧
      (∀ j,mesh j=0 ∨ mesh j=1 ∨ g (mesh j)=0) ∧
      (∀ (j : Fin (m+1)) t,mesh j.castSucc<t → t < mesh j.succ → g t≠0) ∧
      (∀ j,negative j ↔ g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ))<0) ∧
      (∀ j,negative j → ∀ t ∈ Icc (mesh j.castSucc) (mesh j.succ),g t≤0) ∧
      (∀ t,g t≤0 ↔ g t=0 ∨ ∃ j,negative j ∧ t ∈ Icc (mesh j.castSucc) (mesh j.succ)) ∧
      {q : {j : Fin (m+1) // negative j} × Fin 2 |
        mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=0}.ncard=
          (if negative 0 then 1 else 0) ∧
      {q : {j : Fin (m+1) // negative j} × Fin 2 |
        mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=1}.ncard=
          (if negative (Fin.last m) then 1 else 0) ∧
      (g 0≠0 → (negative 0 ↔ g 0<0)) ∧
      (g 1≠0 → (negative (Fin.last m) ↔ g 1<0)) := by
  classical
  obtain ⟨m,mesh,negative,hmono,hzero,hone,hnodes,hno,hnegative,hcoverage⟩ :=
    actual_finite_scalar_negative_intervals g hf
  have hmid (j : Fin (m+1)) :
      actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ) ∈
        Ioo (mesh j.castSucc) (mesh j.succ) := by
    have hs := hmono (show j.castSucc<j.succ by change j.val<j.val+1; omega)
    have hsR : (mesh j.castSucc).val<(mesh j.succ).val := hs
    constructor
    · change (mesh j.castSucc).val<((mesh j.castSucc).val+(mesh j.succ).val)/2
      linarith only [hsR]
    · change ((mesh j.castSucc).val+(mesh j.succ).val)/2<(mesh j.succ).val
      linarith only [hsR]
  have hflag (j : Fin (m+1)) : negative j ↔
      g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ))<0 := by
    constructor
    · intro hj
      exact lt_of_le_of_ne
        (hnegative j hj _ ⟨(hmid j).1.le,(hmid j).2.le⟩)
        (hno j _ (hmid j).1 (hmid j).2)
    · intro hj
      rcases (hcoverage _).mp hj.le with hz | ⟨d,hd,hbounds⟩
      · exact False.elim ((ne_of_lt hj) hz)
      · have hlo := hmono.lt_iff_lt.mp ((hmid j).1.trans_le hbounds.2)
        have hhi := hmono.lt_iff_lt.mp (hbounds.1.trans_lt (hmid j).2)
        have hdj : d=j := by
          apply Fin.ext
          change j.val<d.val+1 at hlo
          change d.val<j.val+1 at hhi
          omega
        exact hdj ▸ hd
  have endpointFlag (j : Fin (m+1)) (t : Interval)
      (ht : t ∈ Icc (mesh j.castSucc) (mesh j.succ)) (hgt : g t≠0) :
      negative j ↔ g t<0 := by
    rw [hflag]
    constructor
    · intro hneg
      exact lt_of_le_of_ne
        (actualNoZeroIntervalSign g _ _ _ (hmid j).1 (hmid j).2 hneg (hno j) t ht) hgt
    · intro hneg
      exact actualNegativeEndpointForcesInteriorSign g _ _ _ t (hmid j) ht hneg (hno j)
  refine ⟨m,mesh,negative,hmono,hzero,hone,hnodes,hno,hflag,hnegative,hcoverage,
    actual_scalar_mesh_initial_endpoint_incidence m mesh hmono hzero negative,
    actual_scalar_mesh_terminal_endpoint_incidence m mesh hmono hone negative,?_,?_⟩
  · intro hg
    apply endpointFlag 0 0 ?_ hg
    rw [show (0:Fin (m+1)).castSucc=0 from rfl,hzero]
    exact ⟨le_rfl,(mesh _).property.1⟩
  · intro hg
    apply endpointFlag (Fin.last m) 1 ?_ hg
    rw [show (Fin.last m).succ=Fin.last (m+1) from rfl,hone]
    exact ⟨(mesh _).property.2,le_rfl⟩
end CurveComplex.HyperellipticModel
