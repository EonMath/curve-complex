import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualZeroFreeScalarIntervalSign
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_ordered_scalar_mesh_cover {m : ℕ} (mesh : Fin (m+2) → Interval)
    (hmono : StrictMono mesh) (hzero : mesh 0 = 0) (hone : mesh (Fin.last (m+1)) = 1) :
    ∀ t : Interval, ∃ k : Fin (m+1), mesh k.castSucc ≤ t ∧ t ≤ mesh k.succ := by
  classical
  intro t
  let A : Finset (Fin (m+2)) := Finset.univ.filter (fun i => mesh i ≤ t)
  have h0 : (0 : Fin (m+2)) ∈ A := by
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,hzero]
    exact t.property.1
  have hne : A.Nonempty := ⟨0,h0⟩
  let i := A.max' hne
  have hi : i ∈ A := Finset.max'_mem A hne
  have hiT : mesh i ≤ t := (Finset.mem_filter.mp hi).2
  by_cases hilast : i = Fin.last (m+1)
  · have ht1 : t = 1 := by
      apply Subtype.ext
      have hge : (1 : ℝ) ≤ t.val := by
        have hgeI : (1 : Interval) ≤ t := by simpa only [hilast,hone] using hiT
        change ((1 : Interval) : ℝ) ≤ t.val at hgeI
        norm_num at hgeI
        exact hgeI
      exact le_antisymm t.property.2 hge
    refine ⟨Fin.last m,?_,?_⟩
    · rw [ht1,← hone]
      apply hmono.monotone
      change m ≤ m+1
      omega
    · have hlast : (Fin.last m).succ = Fin.last (m+1) := by apply Fin.ext; rfl
      rw [hlast,hone,ht1]
  · have hiN : i.val < m+1 := by
      have hn := i.isLt
      have hneN : i.val ≠ m+1 := by intro h; apply hilast; apply Fin.ext; exact h
      omega
    let k : Fin (m+1) := ⟨i.val,hiN⟩
    have hik : k.castSucc = i := by apply Fin.ext; rfl
    refine ⟨k,hik.symm ▸ hiT,?_⟩
    by_contra hbad
    have hsT : mesh k.succ ≤ t := le_of_lt (lt_of_not_ge hbad)
    have hsA : k.succ ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsT⟩
    have hsmax : k.succ ≤ i := Finset.le_max' A _ hsA
    have hsN : k.val+1 ≤ i.val := hsmax
    change i.val+1 ≤ i.val at hsN
    omega
end CurveComplex.HyperellipticModel
