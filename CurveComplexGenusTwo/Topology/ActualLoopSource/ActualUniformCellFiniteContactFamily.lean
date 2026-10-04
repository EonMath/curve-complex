import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellParameterEmbedding
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_interval_mesh_parameter_strict_interior
    (n : ℕ) (hn : 0<n) (i : Fin n) (t : Interval)
    (ht0 : 0<t.val) (ht1 : t.val<1) :
    0<(ArcFinitePosition.intervalMeshParameter n hn i t).val ∧
      (ArcFinitePosition.intervalMeshParameter n hn i t).val<1 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hi0 : (0:ℝ) ≤ i.val := by positivity
  have hi1 : (i.val:ℝ)+1≤n := by exact_mod_cast Nat.succ_le_of_lt i.isLt
  change 0<((i.val:ℝ)+t.val)/n ∧ ((i.val:ℝ)+t.val)/n<1
  exact ⟨div_pos (by linarith) hnR,(div_lt_one hnR).mpr (by linarith)⟩
/-- Finite proper families in the actual uniform cells assemble into one
finite proper global family. Cross-cell collisions are derived from literal
mesh geometry and proper interior placement. -/
theorem actual_uniform_cell_finite_contact_family
    {S : Type} [TopologicalSpace S]
    (n : ℕ) (hn : 0<n) (G : C(Interval × Interval,S)) (old : Set S)
    (cellMap : (Fin n × Fin n) → C(Interval × Interval,S))
    (hlocal : ∀ k z,G (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2)=cellMap k z)
    (vertices : (Fin n × Fin n) → Finset (Interval × Interval))
    (A : (Fin n × Fin n) → Type) [∀ k,Finite (A k)]
    (arc : ∀ k,A k → C(Interval,Interval × Interval))
    (hends : ∀ k e,arc k e 0 ∈ vertices k ∧ arc k e 1 ∈ vertices k)
    (hcollision : ∀ k e d t u,arc k e t=arc k d u →
      (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)))
    (hclear : ∀ k e t,t≠0 → t≠1 → arc k e t ∉ vertices k)
    (hembed : ∀ k e,IsEmbedding (arc k e))
    (hinterior : ∀ k e t,0<t.val → t.val<1 →
      0<(arc k e t).1.val ∧ (arc k e t).1.val<1 ∧
        0<(arc k e t).2.val ∧ (arc k e t).2.val<1)
    (hcoverage : ∀ k z,cellMap k z ∈ old ↔ z ∈ vertices k ∨ ∃ e t,arc k e t=z) :
    ∃ V : Finset (Interval × Interval),
    ∃ arcs : (Σ k,A k) → C(Interval,Interval × Interval),
      (∀ e,IsEmbedding (arcs e)) ∧
      (∀ e,arcs e 0 ∈ V ∧ arcs e 1 ∈ V) ∧
      (∀ e t,t≠0 → t≠1 → arcs e t ∉ V) ∧
      (∀ e d t u,arcs e t=arcs d u →
        (e=d ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1))) ∧
      (∀ z,G z ∈ old ↔ z ∈ V ∨ ∃ e t,arcs e t=z) ∧
      (∀ e t,0<t.val → t.val<1 →
        0<(arcs e t).1.val ∧ (arcs e t).1.val<1 ∧
          0<(arcs e t).2.val ∧ (arcs e t).2.val<1) := by
  classical
  let parameter (k : Fin n × Fin n) : C(Interval × Interval,Interval × Interval) :=
    ⟨fun z => (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),by
        exact ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.1).comp continuous_fst).prodMk
          ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.2).comp continuous_snd)⟩
  have hlocal' (k) (z : Interval × Interval) : G (parameter k z)=cellMap k z := hlocal k z
  let V := Finset.univ.biUnion (fun k => (vertices k).image (parameter k))
  let arcs : (Σ k,A k) → C(Interval,Interval × Interval) := fun e => (parameter e.1).comp (arc e.1 e.2)
  have hV (z : Interval × Interval) : z ∈ V ↔ ∃ k,∃ w ∈ vertices k,parameter k w=z := by
    simp only [V,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
  have hnotboundary (k) (e : A k) (t : Interval) (ht0 : t≠0) (ht1 : t≠1) :
      ¬ ((arc k e t).1=0 ∨ (arc k e t).1=1 ∨ (arc k e t).2=0 ∨ (arc k e t).2=1) := by
    have ht0R : 0<t.val := lt_of_le_of_ne t.property.1 (fun h => ht0 (Subtype.ext h.symm))
    have ht1R : t.val<1 := lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))
    obtain ⟨hx0,hx1,hy0,hy1⟩ := hinterior k e t ht0R ht1R
    rintro (h | h | h | h)
    · simp [h] at hx0
    · simp [h] at hx1
    · simp [h] at hy0
    · simp [h] at hy1
  have hparametercollision (k l) (z w : Interval × Interval) (he : parameter k z=parameter l w) :=
    actual_uniform_cell_parameter_collision n hn k l z w he
  refine ⟨V,arcs,?_,?_,?_,?_,?_,?_⟩
  · intro e
    exact (actual_uniform_cell_parameter_embedding n hn e.1).comp (hembed e.1 e.2)
  · intro e
    constructor
    · exact (hV _).mpr ⟨e.1,arc e.1 e.2 0,(hends e.1 e.2).1,rfl⟩
    · exact (hV _).mpr ⟨e.1,arc e.1 e.2 1,(hends e.1 e.2).2,rfl⟩
  · rintro ⟨k,e⟩ t ht0 ht1 hv
    obtain ⟨l,w,hw,he⟩ := (hV _).mp hv
    rcases hparametercollision k l (arc k e t) w he.symm with ⟨hkl,hxy⟩ | ⟨hb,_⟩
    · subst l
      exact hclear k e t ht0 ht1 (hxy.symm ▸ hw)
    · exact hnotboundary k e t ht0 ht1 hb
  · rintro ⟨k,e⟩ ⟨l,d⟩ t u he
    change parameter k (arc k e t)=parameter l (arc l d u) at he
    rcases hparametercollision k l _ _ he with ⟨hkl,hxy⟩ | ⟨hb,hb'⟩
    · subst l
      rcases hcollision k e d t u hxy with ⟨hed,htu⟩ | hh
      · exact Or.inl ⟨congrArg (Sigma.mk k) hed,htu⟩
      · exact Or.inr hh
    · right
      constructor
      · by_contra ht
        push Not at ht
        exact hnotboundary k e t ht.1 ht.2 hb
      · by_contra hu
        push Not at hu
        exact hnotboundary l d u hu.1 hu.2 hb'
  · intro z
    constructor
    · intro hz
      obtain ⟨i,s,hs⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
      obtain ⟨j,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
      have hp : parameter (i,j) (s,t)=z := Prod.ext hs ht
      have hloc : cellMap (i,j) (s,t) ∈ old := by
        rw [←hlocal' (i,j) (s,t),hp]
        exact hz
      rcases (hcoverage (i,j) (s,t)).mp hloc with hv | ⟨e,u,he⟩
      · exact Or.inl ((hV _).mpr ⟨(i,j),(s,t),hv,hp⟩)
      · exact Or.inr ⟨⟨(i,j),e⟩,u,(congrArg (parameter (i,j)) he).trans hp⟩
    · rintro (hv | ⟨⟨k,e⟩,t,rfl⟩)
      · obtain ⟨k,w,hw,rfl⟩ := (hV _).mp hv
        rw [hlocal' k w]
        exact (hcoverage k w).mpr (Or.inl hw)
      · change G (parameter k (arc k e t)) ∈ old
        rw [hlocal' k (arc k e t)]
        exact (hcoverage k (arc k e t)).mpr (Or.inr ⟨e,t,rfl⟩)
  · intro e t ht0 ht1
    obtain ⟨hx0,hx1,hy0,hy1⟩ := hinterior e.1 e.2 t ht0 ht1
    exact ⟨(actual_interval_mesh_parameter_strict_interior n hn e.1.1 _ hx0 hx1).1,
      (actual_interval_mesh_parameter_strict_interior n hn e.1.1 _ hx0 hx1).2,
      (actual_interval_mesh_parameter_strict_interior n hn e.1.2 _ hy0 hy1).1,
      (actual_interval_mesh_parameter_strict_interior n hn e.1.2 _ hy0 hy1).2⟩
end CurveComplex.HyperellipticModel
