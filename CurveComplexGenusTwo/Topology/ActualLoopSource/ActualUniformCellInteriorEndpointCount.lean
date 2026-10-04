import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellParameterEmbedding
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal affine cell geometry makes the global endpoint count at a strict
cell-interior point equal the actual local endpoint count. No degree input. -/
theorem actual_uniform_cell_interior_endpoint_count
    (n : ℕ) (hn : 0<n) (A : (Fin n × Fin n) → Type)
    (arc : ∀ k,A k → C(Interval,Interval × Interval))
    (k : Fin n × Fin n) (z : Interval × Interval)
    (hz : 0<z.1.val ∧ z.1.val < 1 ∧ 0<z.2.val ∧ z.2.val < 1) :
    {r : (Σ l,A l) × Fin 2 |
      (ArcFinitePosition.intervalMeshParameter n hn r.1.1.1
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).1,
       ArcFinitePosition.intervalMeshParameter n hn r.1.1.2
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).2)=
      (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
       ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)}.ncard=
    {r : A k × Fin 2 | arc k r.1 (if r.2=0 then 0 else 1)=z}.ncard := by
  classical
  have hnot : ¬(z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1) := by
    rintro (h | h | h | h)
    · simp [h] at hz
    · simp [h] at hz
    · simp [h] at hz
    · simp [h] at hz
  have hkey (l : Fin n × Fin n) (w : Interval × Interval)
      (he : (ArcFinitePosition.intervalMeshParameter n hn l.1 w.1,
        ArcFinitePosition.intervalMeshParameter n hn l.2 w.2)=
        (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
          ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)) : l=k ∧ w=z := by
    rcases actual_uniform_cell_parameter_collision n hn k l z w he.symm with h | ⟨hb,_⟩
    · exact ⟨h.1.symm,h.2.symm⟩
    · exact False.elim (hnot hb)
  symm
  apply Set.ncard_congr (fun r _ => (⟨k,r.1⟩,r.2))
  · intro r hr
    change arc k r.1 (if r.2=0 then 0 else 1)=z at hr
    change (_,_) = (_,_) 
    rw [hr]
  · intro r s hr hs he
    have hb := congrArg Prod.snd he
    have ha : r.1=s.1 := by
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst he)).2
    exact Prod.ext ha hb
  · rintro ⟨⟨l,e⟩,bit⟩ he
    have hh := hkey l (arc l e (if bit=0 then 0 else 1)) he
    rcases hh with ⟨hkl,hz⟩
    cases hkl
    exact ⟨(e,bit),hz,rfl⟩
end CurveComplex.HyperellipticModel
