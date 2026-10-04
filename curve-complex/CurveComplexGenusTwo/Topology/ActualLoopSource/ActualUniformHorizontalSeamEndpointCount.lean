import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformOpenSeamCellIncidence
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellParameterEmbedding
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Global endpoint incidence on an actual open horizontal seam is exactly the
sum of the two literal adjacent-cell endpoint incidences. -/
theorem actual_uniform_horizontal_seam_endpoint_count
    (n : ℕ) (hn : 0<n) (A : (Fin n × Fin n) → Type) [∀ k,Finite (A k)]
    (arc : ∀ k,A k → C(Interval,Interval × Interval))
    (node : Fin (n+1)) (hnode : 0<node.val ∧ node.val < n)
    (i : Fin n) (s : Interval) (hs : 0<s.val ∧ s.val < 1) :
    let L : Fin n × Fin n := (i,⟨node.val-1,by omega⟩)
    let R : Fin n × Fin n := (i,⟨node.val,hnode.2⟩)
    {r : (Σ k,A k) × Fin 2 |
      (ArcFinitePosition.intervalMeshParameter n hn r.1.1.1
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).1,
       ArcFinitePosition.intervalMeshParameter n hn r.1.1.2
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).2)=
      (ArcFinitePosition.intervalMeshParameter n hn i s,
        actualHalfMeshParameter n hn ⟨2*node.val,by omega⟩)}.ncard=
      {r : A L × Fin 2 | arc L r.1 (if r.2=0 then 0 else 1)=(s,1)}.ncard+
      {r : A R × Fin 2 | arc R r.1 (if r.2=0 then 0 else 1)=(s,0)}.ncard := by
  classical
  dsimp only
  let L : Fin n × Fin n := (i,⟨node.val-1,by omega⟩)
  let R : Fin n × Fin n := (i,⟨node.val,hnode.2⟩)
  let left : Set (A L × Fin 2) := {r | arc L r.1 (if r.2=0 then 0 else 1)=(s,1)}
  let right : Set (A R × Fin 2) := {r | arc R r.1 (if r.2=0 then 0 else 1)=(s,0)}
  let fl : A L × Fin 2 → (Σ k,A k) × Fin 2 := fun r => (⟨L,r.1⟩,r.2)
  let fr : A R × Fin 2 → (Σ k,A k) × Fin 2 := fun r => (⟨R,r.1⟩,r.2)
  have hinjL : Function.Injective fl := by
    intro x y he
    have ha : x.1=y.1 := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst he)).2
    have hb : x.2=y.2 := congrArg (fun r : (Σ k,A k) × Fin 2 => r.2) he
    exact Prod.ext ha hb
  have hinjR : Function.Injective fr := by
    intro x y he
    have ha : x.1=y.1 := eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Prod.fst he)).2
    have hb : x.2=y.2 := congrArg (fun r : (Σ k,A k) × Fin 2 => r.2) he
    exact Prod.ext ha hb
  have hne : L≠R := by
    intro he
    have hv := congrArg (fun k : Fin n × Fin n => k.2.val) he
    change node.val-1=node.val at hv
    omega
  have hdisjoint : Disjoint (fl '' left) (fr '' right) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    exact hne (congrArg (fun r : (Σ k,A k) × Fin 2 => r.1.1) he).symm
  have hLnode : ArcFinitePosition.intervalMeshParameter n hn L.2 1=
      actualHalfMeshParameter n hn ⟨2*node.val,by omega⟩ := by
    apply Subtype.ext
    rw [actual_half_mesh_parameter_vertex n hn node]
    change (((node.val-1:ℕ):ℝ)+1)/n=(node.val:ℝ)/n
    rw [Nat.cast_sub (by omega : 1≤node.val)]
    congr 1
    ring
  have hRnode : ArcFinitePosition.intervalMeshParameter n hn R.2 0=
      actualHalfMeshParameter n hn ⟨2*node.val,by omega⟩ := by
    apply Subtype.ext
    rw [actual_half_mesh_parameter_vertex n hn node]
    change ((node.val:ℝ)+0)/n=(node.val:ℝ)/n
    simp
  have heq : {r : (Σ k,A k) × Fin 2 |
      (ArcFinitePosition.intervalMeshParameter n hn r.1.1.1
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).1,
       ArcFinitePosition.intervalMeshParameter n hn r.1.1.2
        (arc r.1.1 r.1.2 (if r.2=0 then 0 else 1)).2)=
      (ArcFinitePosition.intervalMeshParameter n hn i s,
        actualHalfMeshParameter n hn ⟨2*node.val,by omega⟩)}=fl '' left ∪ fr '' right := by
    ext r
    constructor
    · intro hr
      rcases r with ⟨⟨k,e⟩,bit⟩
      obtain ⟨hki,hparam,hside⟩ := actual_uniform_horizontal_open_seam_cell_incidence
        n hn node i s hs k (arc k e (if bit=0 then 0 else 1)) hr
      rcases hside with ⟨hk,hz⟩ | ⟨hk,hz⟩
      · have hkr : k=R := Prod.ext hki (Fin.ext hk)
        cases hkr
        exact Or.inr ⟨(e,bit),Prod.ext hparam hz,rfl⟩
      · have hkl : k=L := by
          apply Prod.ext
          · exact hki
          · apply Fin.ext
            change k.2.val=node.val-1
            omega
        cases hkl
        exact Or.inl ⟨(e,bit),Prod.ext hparam hz,rfl⟩
    · rintro (⟨r,hr,rfl⟩ | ⟨r,hr,rfl⟩)
      · change arc L r.1 (if r.2=0 then 0 else 1)=(s,1) at hr
        change (_,_) = (_,_) 
        rw [hr,hLnode]
      · change arc R r.1 (if r.2=0 then 0 else 1)=(s,0) at hr
        change (_,_) = (_,_) 
        rw [hr,hRnode]
  rw [heq,Set.ncard_union_eq hdisjoint,
    Set.ncard_image_of_injective left hinjL,Set.ncard_image_of_injective right hinjR]
end CurveComplex.HyperellipticModel
