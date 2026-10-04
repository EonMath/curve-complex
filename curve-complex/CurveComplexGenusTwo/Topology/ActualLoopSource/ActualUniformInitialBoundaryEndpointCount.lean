import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformOpenSeamCellIncidence
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- An open point of the literal initial outer side belongs to exactly its
single incident physical cell. Its global endpoint count is the local count. -/
theorem actual_uniform_initial_boundary_endpoint_count
    (n : ℕ) (hn : 0<n) (A : (Fin n × Fin n) → Type)
    (arc : ∀ k,A k → C(Interval,Interval × Interval))
    (i : Fin n) (s : Interval) (hs : 0<s.val ∧ s.val < 1) :
    let k : Fin n × Fin n := (⟨0,hn⟩,i)
    {r : (Σ l,A l) × Fin 2 |
      (ArcFinitePosition.intervalMeshParameter n hn r.1.1.1
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).1,
       ArcFinitePosition.intervalMeshParameter n hn r.1.1.2
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).2)=
      (0,ArcFinitePosition.intervalMeshParameter n hn i s)}.ncard=
    {r : A k × Fin 2 | arc k r.1 (if r.2=0 then 0 else 1)=(0,s)}.ncard := by
  classical
  dsimp only
  let k : Fin n × Fin n := (⟨0,hn⟩,i)
  have hzero : actualHalfMeshParameter n hn ⟨2*(0:Fin (n+1)).val,by omega⟩=0 := by
    apply Subtype.ext
    rw [actual_half_mesh_parameter_vertex]
    norm_num
  symm
  apply Set.ncard_congr (fun r _ => (⟨k,r.1⟩,r.2))
  · intro r hr
    change arc k r.1 (if r.2=0 then 0 else 1)=(0,s) at hr
    change (_,_) = (_,_)
    rw [hr]
    have hx : ArcFinitePosition.intervalMeshParameter n hn ⟨0,hn⟩ 0=0 := by
      apply Subtype.ext
      simp [ArcFinitePosition.intervalMeshParameter]
    exact Prod.ext hx rfl
  · intro r q hr hq he
    have ha : r.1=q.1 := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst he)).2
    have hb : r.2=q.2 := congrArg (fun x : (Σ l,A l) × Fin 2 => x.2) he
    exact Prod.ext ha hb
  · rintro ⟨⟨l,e⟩,bit⟩ he
    have hpoint : (ArcFinitePosition.intervalMeshParameter n hn l.1
        (arc l e (if bit=0 then 0 else 1)).1,
      ArcFinitePosition.intervalMeshParameter n hn l.2
        (arc l e (if bit=0 then 0 else 1)).2)=
      (actualHalfMeshParameter n hn ⟨2*(0:Fin (n+1)).val,by omega⟩,
        ArcFinitePosition.intervalMeshParameter n hn i s) := by rw [hzero]; exact he
    obtain ⟨hli,hpar,hleft⟩ := actual_uniform_vertical_open_seam_cell_incidence
      n hn 0 i s hs l (arc l e (if bit=0 then 0 else 1)) hpoint
    have hl0 : l.1.val=0 ∧ (arc l e (if bit=0 then 0 else 1)).1=0 := by
      rcases hleft with h | h
      · exact h
      · have hh := h.1
        change l.1.val+1=0 at hh
        omega
    have hlk : l=k := Prod.ext (Fin.ext hl0.1) hli
    cases hlk
    exact ⟨(e,bit),Prod.ext hl0.2 hpar,rfl⟩
end CurveComplex.HyperellipticModel
