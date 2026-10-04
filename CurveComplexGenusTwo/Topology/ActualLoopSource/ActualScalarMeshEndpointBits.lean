import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualScalarMeshBoundaryIncidence
namespace CurveComplex.HyperellipticModel
open Set Topology CurveComplex.LocalSurgery
attribute [local instance] Classical.propDecidable
/-- Strict mesh intervals cannot count the same contact twice. The literal
endpoint-bit count equals the number of selected intervals meeting the node. -/
theorem actual_scalar_mesh_endpoint_bits_as_interval_count
    (m : ℕ) (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (negative : Fin (m+1) → Prop) (u : Interval) :
    {q : {j : Fin (m+1) // negative j} × Fin 2 |
      mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=u}.ncard=
    (Finset.univ.filter (fun j : Fin (m+1) => negative j ∧
      (mesh j.castSucc=u ∨ mesh j.succ=u))).card := by
  classical
  let hits : Set (Fin (m+1)) := {j | negative j ∧ (mesh j.castSucc=u ∨ mesh j.succ=u)}
  have hc : {q : {j : Fin (m+1) // negative j} × Fin 2 |
      mesh (if q.2=0 then q.1.val.castSucc else q.1.val.succ)=u}.ncard=hits.ncard := by
    apply Set.ncard_congr (fun q _ => q.1.val)
    · intro q hq
      change negative q.1.val ∧ _
      refine ⟨q.1.property,?_⟩
      by_cases hb : q.2=0
      · exact Or.inl (by simpa [hb] using hq)
      · exact Or.inr (by simpa [hb] using hq)
    · intro q r hq hr he
      apply Prod.ext (Subtype.ext he)
      have hs : mesh q.1.val.castSucc < mesh q.1.val.succ := hmono (by change q.1.val.val < q.1.val.val+1; omega)
      by_cases hb : q.2=0
      · have hc : r.2=0 := by
          by_contra hn
          have hl : mesh q.1.val.castSucc=u := by simpa [hb] using hq
          have hh : mesh q.1.val.succ=u := by simpa [hn,← he] using hr
          exact (ne_of_lt hs) (hl.trans hh.symm)
        exact hb.trans hc.symm
      · have hc : r.2≠0 := by
          intro hn
          have hl : mesh q.1.val.succ=u := by simpa [hb] using hq
          have hh : mesh q.1.val.castSucc=u := by simpa [hn,← he] using hr
          exact (ne_of_lt hs) (hh.trans hl.symm)
        apply Fin.ext
        have hqv := q.2.isLt
        have hrv := r.2.isLt
        have hqb := Fin.val_ne_of_ne hb
        have hrb := Fin.val_ne_of_ne hc
        omega
    · intro j hj
      change negative j ∧ (mesh j.castSucc=u ∨ mesh j.succ=u) at hj
      by_cases hb : mesh j.castSucc=u
      · refine ⟨(⟨j,hj.1⟩,0),?_,rfl⟩
        simpa using hb
      · refine ⟨(⟨j,hj.1⟩,1),?_,rfl⟩
        simpa using hj.2.resolve_left hb
  rw [hc,Set.ncard_eq_toFinset_card']
  congr 1
  ext j
  simp [hits]
/-- Exact two literal endpoint bits at a negative internal source mesh node.
This transfers the proved H1 interval-incidence kernel without importing its
unfinished global selector. -/
theorem actual_scalar_mesh_internal_negative_endpoint_incidence
    (m : ℕ) (mesh : Fin (m+2) → Interval) (hmono : StrictMono mesh)
    (g : C(Interval,ℝ)) (negative : Fin (m+1) → Prop)
    (hflag : ∀ j,negative j ↔ g (actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ)) < 0)
    (hno : ∀ (j : Fin (m+1)) t,mesh j.castSucc < t → t < mesh j.succ → g t≠0)
    (q : Fin (m+2)) (hq0 : q≠0) (hq1 : q≠Fin.last (m+1))
    (hneg : g (mesh q) < 0) :
    {r : {j : Fin (m+1) // negative j} × Fin 2 |
      mesh (if r.2=0 then r.1.val.castSucc else r.1.val.succ)=mesh q}.ncard=2 := by
  classical
  rw [actual_scalar_mesh_endpoint_bits_as_interval_count m mesh hmono negative (mesh q)]
  have hmid (j : Fin (m+1)) : actualIntervalMidpoint (mesh j.castSucc) (mesh j.succ) ∈
      Ioo (mesh j.castSucc) (mesh j.succ) := by
    have hs : (mesh j.castSucc).val < (mesh j.succ).val := hmono (by change j.val < j.val+1; omega)
    constructor
    · change (mesh j.castSucc).val < ((mesh j.castSucc).val+(mesh j.succ).val)/2
      linarith only [hs]
    · change ((mesh j.castSucc).val+(mesh j.succ).val)/2 < (mesh j.succ).val
      linarith only [hs]
  simpa only [hflag] using actualNegativeInternalMeshNodeIncidenceTwo
    m mesh hmono g hmid hno q hq0 hq1 hneg
end CurveComplex.HyperellipticModel
