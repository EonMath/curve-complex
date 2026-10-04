import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarZeroMesh
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualNegativeInternalMeshNodeIncidenceKernelRecovery
namespace CurveComplex.HyperellipticModel
open Set Topology
attribute [local instance] Classical.propDecidable
/-- Exact incidence at the literal initial face endpoint. This counts endpoint
bits, rather than distinct edges, as required by the original drawing target. -/
theorem actual_scalar_mesh_initial_endpoint_incidence
    (m : ℕ) (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (hzero : mesh 0=0) (negative : Fin (m+1) → Prop) :
    {q : {j : Fin (m+1) // negative j} × Fin 2 |
      mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=0}.ncard=
        if negative 0 then 1 else 0 := by
  classical
  have hcast (j : Fin (m+1)) : mesh j.castSucc=0 ↔ j=0 := by
    constructor
    · intro hj
      have he := hmono.injective (hj.trans hzero.symm)
      apply Fin.ext
      exact congrArg (fun z : Fin (m+2) => z.val) he
    · rintro rfl
      exact hzero
  have hsucc (j : Fin (m+1)) : mesh j.succ≠0 := by
    have hs := hmono (show (0:Fin (m+2))<j.succ by change 0<j.val+1; omega)
    rw [hzero] at hs
    exact ne_of_gt hs
  by_cases hn : negative 0
  · let p : {j : Fin (m+1) // negative j} × Fin 2 := (⟨0,hn⟩,0)
    have heq : {q : {j : Fin (m+1) // negative j} × Fin 2 |
        mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=0}={p} := by
      ext q
      constructor
      · intro hq
        change mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=0 at hq
        by_cases hbit : q.2=0
        · simp only [hbit,ite_true] at hq
          have hj := (hcast q.1.val).mp hq
          exact Set.mem_singleton_iff.mpr (Prod.ext (Subtype.ext hj) hbit)
        · simp only [hbit,ite_false] at hq
          exact False.elim (hsucc q.1.val hq)
      · rintro rfl
        simp [p,hzero]
    rw [heq,Set.ncard_singleton,ite_eq_left hn]
  · have heq : {q : {j : Fin (m+1) // negative j} × Fin 2 |
        mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=0}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      change mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=0 at hq
      by_cases hbit : q.2=0
      · simp only [hbit,ite_true] at hq
        have hj := (hcast q.1.val).mp hq
        exact hn (hj ▸ q.1.property)
      · simp only [hbit,ite_false] at hq
        exact hsucc q.1.val hq
    rw [heq,Set.ncard_empty,ite_eq_right hn]
/-- Exact incidence at the literal terminal face endpoint, retaining the
second endpoint bit even at the original bottom corners. -/
theorem actual_scalar_mesh_terminal_endpoint_incidence
    (m : ℕ) (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (hone : mesh (Fin.last (m+1))=1) (negative : Fin (m+1) → Prop) :
    {q : {j : Fin (m+1) // negative j} × Fin 2 |
      mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=1}.ncard=
        if negative (Fin.last m) then 1 else 0 := by
  classical
  have hsucc (j : Fin (m+1)) : mesh j.succ=1 ↔ j=Fin.last m := by
    constructor
    · intro hj
      have he := congrArg Fin.val (hmono.injective (hj.trans hone.symm))
      apply Fin.ext
      change j.val+1=m+1 at he
      change j.val=m
      omega
    · rintro rfl
      exact hone
  have hcast (j : Fin (m+1)) : mesh j.castSucc≠1 := by
    have hs := hmono (show j.castSucc<Fin.last (m+1) by change j.val < m+1; omega)
    rw [hone] at hs
    exact ne_of_lt hs
  by_cases hn : negative (Fin.last m)
  · let p : {j : Fin (m+1) // negative j} × Fin 2 := (⟨Fin.last m,hn⟩,1)
    have heq : {q : {j : Fin (m+1) // negative j} × Fin 2 |
        mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=1}={p} := by
      ext q
      constructor
      · intro hq
        change mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=1 at hq
        by_cases hbit : q.2=0
        · simp only [hbit,ite_true] at hq
          exact False.elim (hcast q.1.val hq)
        · simp only [hbit,ite_false] at hq
          have hj := (hsucc q.1.val).mp hq
          have hb : q.2=1 := by apply Fin.ext; have h := q.2.isLt; have hn := Fin.val_ne_of_ne hbit; omega
          exact Set.mem_singleton_iff.mpr (Prod.ext (Subtype.ext hj) hb)
      · rintro rfl
        simp [p,hone]
    rw [heq,Set.ncard_singleton,ite_eq_left hn]
  · have heq : {q : {j : Fin (m+1) // negative j} × Fin 2 |
        mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=1}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      change mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=1 at hq
      by_cases hbit : q.2=0
      · simp only [hbit,ite_true] at hq
        exact hcast q.1.val hq
      · simp only [hbit,ite_false] at hq
        have hj := (hsucc q.1.val).mp hq
        exact hn (hj ▸ q.1.property)
    rw [heq,Set.ncard_empty,ite_eq_right hn]
end CurveComplex.HyperellipticModel
namespace CurveComplex.HyperellipticModel
open Set Topology
attribute [local instance] Classical.propDecidable
/-- A literal source root with opposite adjacent negative flags has exactly
one endpoint-bit incidence. Uses the existing H1 uniqueness theorem. -/
theorem actual_scalar_mesh_crossing_root_incidence
    (m : ℕ) (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (negative : Fin (m+1) → Prop) (l r : Fin (m+1)) (u : Interval)
    (hl : mesh l.succ=u) (hr : mesh r.castSucc=u)
    (hflip : negative l ↔ ¬negative r) :
    {q : {j : Fin (m+1) // negative j} × Fin 2 |
      mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=u}.ncard=1 := by
  classical
  obtain ⟨j,hj,hunique⟩ := CurveComplex.LocalSurgery.actualMeshNegativeIncidenceUnique
    m mesh hmono negative l r u hl hr hflip
  have hstrict : mesh j.castSucc < mesh j.succ := hmono (by change j.val<j.val+1; omega)
  let bit : Fin 2 := if mesh j.castSucc=u then 0 else 1
  let p : {j : Fin (m+1) // negative j} × Fin 2 := (⟨j,hj.1⟩,bit)
  have hp : mesh (if p.2=0 then p.1.val.castSucc else p.1.val.succ)=u := by
    by_cases h : mesh j.castSucc=u
    · simp [p,bit,h]
    · have he := hj.2.resolve_left h
      simpa [p,bit,h] using he
  apply Set.ncard_eq_one.mpr
  refine ⟨p,?_⟩
  ext q
  constructor
  · intro hq
    change mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=u at hq
    have hinc : mesh q.1.val.castSucc=u ∨ mesh q.1.val.succ=u := by
      by_cases hbit : q.2=0
      · exact Or.inl (by simpa [hbit] using hq)
      · exact Or.inr (by simpa [hbit] using hq)
    have hidx : q.1.val=j := hunique q.1.val ⟨q.1.property,hinc⟩
    have hindex : q.1=p.1 := Subtype.ext hidx
    apply Set.mem_singleton_iff.mpr
    apply Prod.ext hindex
    by_cases h : mesh j.castSucc=u
    · have hbit : q.2=0 := by
        by_contra hb
        have hlast : mesh j.succ=u := by simpa [hb,hidx] using hq
        exact (ne_of_lt hstrict) (h.trans hlast.symm)
      simpa [p,bit,h] using hbit
    · have hbit : q.2≠0 := by
        intro hb
        have hh : mesh j.castSucc=u := by simpa [hb,hidx] using hq
        exact h hh
      have hb : q.2=1 := by
        apply Fin.ext
        have hlt := q.2.isLt
        have hn := Fin.val_ne_of_ne hbit
        omega
      simpa [p,bit,h] using hb
  · rintro rfl
    exact hp
end CurveComplex.HyperellipticModel
