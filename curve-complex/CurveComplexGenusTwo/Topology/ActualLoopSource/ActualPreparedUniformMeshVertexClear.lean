import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCommonStripFiniteEdgeRedrawWithContacts
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The already constructed boundary-safe movie clears EVERY noncorner
uniform-mesh vertex, including vertices lying on the literal square sides. -/
theorem actual_prepared_uniform_mesh_vertex_clear
    {S : Type} [TopologicalSpace S] (old : Set S) (G : C(Interval × Interval,S))
    (n : ℕ) (hn : 0<n) (R : C((Interval × Interval) × Interval,S))
    (hboundary : ∀ z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → R (z,σ)=G z)
    (hnodes : ∀ k : Fin n,0< k.val → ∀ t : Interval,t.val=(k.val:ℝ)/n →
      G (0,t) ∉ old ∧ G (1,t) ∉ old ∧ G (t,0) ∉ old ∧ G (t,1) ∉ old)
    (hclear : ∀ i j : Fin (2*n+1),
      0<(actualHalfMeshParameter n hn i:ℝ) → (actualHalfMeshParameter n hn i:ℝ)<1 →
      0<(actualHalfMeshParameter n hn j:ℝ) → (actualHalfMeshParameter n hn j:ℝ)<1 →
      R ((actualHalfMeshParameter n hn i,actualHalfMeshParameter n hn j),1) ∉ old)
    (i j : Fin (n+1))
    (hinterior : (0< i.val ∧ i.val<n) ∨ (0< j.val ∧ j.val<n)) :
    R ((actualHalfMeshParameter n hn ⟨2*i.val,by omega⟩,
      actualHalfMeshParameter n hn ⟨2*j.val,by omega⟩),1) ∉ old := by
  let node (k : Fin (n+1)) := actualHalfMeshParameter n hn ⟨2*k.val,by omega⟩
  have hnode (k : Fin (n+1)) : (node k:ℝ)=(k.val:ℝ)/n := actual_half_mesh_parameter_vertex n hn k
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hzero (k : Fin (n+1)) (hk : k.val=0) : node k=0 := by
    apply Subtype.ext
    rw [hnode,hk,Nat.cast_zero,zero_div]
    rfl
  have hone (k : Fin (n+1)) (hk : k.val=n) : node k=1 := by
    apply Subtype.ext
    rw [hnode,hk,div_self hnR.ne']
    rfl
  have hstrict (k : Fin (n+1)) (hk0 : k.val≠0) (hk1 : k.val≠n) :
      0<(node k:ℝ) ∧ (node k:ℝ)<1 := by
    rw [hnode]
    constructor
    · exact div_pos (by exact_mod_cast Nat.pos_of_ne_zero hk0) hnR
    · apply (div_lt_one hnR).mpr
      exact_mod_cast (by omega : k.val<n)
  have hside (k : Fin (n+1)) (hk : 0< k.val ∧ k.val<n) :
      G (0,node k) ∉ old ∧ G (1,node k) ∉ old ∧ G (node k,0) ∉ old ∧ G (node k,1) ∉ old :=
    hnodes ⟨k.val,hk.2⟩ hk.1 (node k) (hnode k)
  change R ((node i,node j),1) ∉ old
  by_cases hi0 : i.val=0
  · have hj : 0< j.val ∧ j.val<n := by
      rcases hinterior with h | h
      · omega
      · exact h
    rw [hboundary (node i,node j) 1 (Or.inl (hzero i hi0)),hzero i hi0]
    exact (hside j hj).1
  by_cases hi1 : i.val=n
  · have hj : 0< j.val ∧ j.val<n := by
      rcases hinterior with h | h
      · omega
      · exact h
    rw [hboundary (node i,node j) 1 (Or.inr (Or.inl (hone i hi1))),hone i hi1]
    exact (hside j hj).2.1
  by_cases hj0 : j.val=0
  · have hi : 0< i.val ∧ i.val<n := by omega
    rw [hboundary (node i,node j) 1 (Or.inr (Or.inr (Or.inl (hzero j hj0)))),hzero j hj0]
    exact (hside i hi).2.2.1
  by_cases hj1 : j.val=n
  · have hi : 0< i.val ∧ i.val<n := by omega
    rw [hboundary (node i,node j) 1 (Or.inr (Or.inr (Or.inr (hone j hj1)))),hone j hj1]
    exact (hside i hi).2.2.2
  exact hclear _ _ (hstrict i hi0 hi1).1 (hstrict i hi0 hi1).2
    (hstrict j hj0 hj1).1 (hstrict j hj0 hj1).2
end CurveComplex.HyperellipticModel
