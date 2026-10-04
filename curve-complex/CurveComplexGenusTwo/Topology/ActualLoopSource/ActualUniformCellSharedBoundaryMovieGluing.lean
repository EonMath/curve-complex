import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformCellParameterEmbedding
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual movies on uniform cells glue when their literal boundary values
come from one shared time-dependent boundary assignment. Continuity of that raw
assignment and an overlap compatibility callback are not assumed. -/
theorem actual_uniform_cell_shared_boundary_movie_gluing
    {Y : Type} [TopologicalSpace Y] (B : ((Interval × Interval) × Interval) → Y)
    (n : ℕ) (hn : 0<n)
    (movie : (Fin n × Fin n) → C((Interval × Interval) × Interval,Y))
    (hboundary : ∀ k z σ,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 →
      movie k (z,σ)=B ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ)) :
    ∃ R : C((Interval × Interval) × Interval,Y),
      ∀ k z σ,R ((ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
        ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),σ)=movie k (z,σ) := by
  classical
  let parameter (k : Fin n × Fin n) : C(Interval × Interval,Interval × Interval) :=
    ⟨fun z => (ArcFinitePosition.intervalMeshParameter n hn k.1 z.1,
      ArcFinitePosition.intervalMeshParameter n hn k.2 z.2),by
        exact ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.1).comp continuous_fst).prodMk
          ((ArcFinitePosition.intervalMeshParameter_continuous n hn k.2).comp continuous_snd)⟩
  let cell (k) := range (parameter k)
  have hclosed (k) : IsClosed (cell k) := (isCompact_range (parameter k).continuous).isClosed
  have hcover (z : Interval × Interval) : ∃ k,z ∈ cell k := by
    obtain ⟨i,s,hs⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.1
    obtain ⟨j,t,ht⟩ := ArcFinitePosition.intervalMeshParameter_cover n hn z.2
    exact ⟨(i,j),(s,t),Prod.ext hs ht⟩
  let inverse (k) := (actual_uniform_cell_parameter_embedding n hn k).toHomeomorph.symm
  let domains : (Fin n × Fin n) → Set ((Interval × Interval) × Interval) :=
    fun k => Prod.fst ⁻¹' cell k
  let maps (k) : C(domains k,Y) :=
    ⟨fun z => movie k (inverse k ⟨z.val.1,z.property⟩,z.val.2),by
      exact (movie k).continuous.comp
        ((inverse k |>.continuous.comp
          ((continuous_fst.comp continuous_subtype_val).subtype_mk (fun z => z.property))).prodMk
          (continuous_snd.comp continuous_subtype_val))⟩
  have hagree (k l) (z : (Interval × Interval) × Interval)
      (hk : z ∈ domains k) (hl : z ∈ domains l) : maps k ⟨z,hk⟩=maps l ⟨z,hl⟩ := by
    let x := inverse k ⟨z.1,hk⟩
    let y := inverse l ⟨z.1,hl⟩
    have hx : parameter k x=z.1 := congrArg Subtype.val
      ((actual_uniform_cell_parameter_embedding n hn k).toHomeomorph.apply_symm_apply ⟨z.1,hk⟩)
    have hy : parameter l y=z.1 := congrArg Subtype.val
      ((actual_uniform_cell_parameter_embedding n hn l).toHomeomorph.apply_symm_apply ⟨z.1,hl⟩)
    rcases actual_uniform_cell_parameter_collision n hn k l x y (hx.trans hy.symm) with
      ⟨hkl,hxy⟩ | ⟨hxb,hyb⟩
    · subst l
      rfl
    · change movie k (x,z.2)=movie l (y,z.2)
      rw [hboundary k x z.2 hxb,hboundary l y z.2 hyb]
      exact congrArg (fun w => B (w,z.2)) (hx.trans hy.symm)
  have hdomainsCover (z : (Interval × Interval) × Interval) : ∃ k,z ∈ domains k := hcover z.1
  choose index hindex using hdomainsCover
  let Rfun : ((Interval × Interval) × Interval) → Y :=
    fun z => maps (index z) ⟨z,hindex z⟩
  have hR (k) (z : (Interval × Interval) × Interval) (hz : z ∈ domains k) :
      Rfun z=maps k ⟨z,hz⟩ := hagree _ k z (hindex z) hz
  have hRcont : Continuous Rfun := continuous_iff_isClosed.mpr (by
    intro D hD
    have heq : Rfun ⁻¹' D=⋃ k,Subtype.val '' ((maps k) ⁻¹' D) := by
      ext z
      constructor
      · intro hz
        exact mem_iUnion.mpr ⟨index z,⟨z,hindex z⟩,hz,rfl⟩
      · intro hz
        obtain ⟨k,x,hx,rfl⟩ := mem_iUnion.mp hz
        change Rfun x.val ∈ D
        rw [hR k x.val x.property]
        exact hx
    rw [heq]
    apply isClosed_iUnion_of_finite
    intro k
    exact ((hclosed k).preimage continuous_fst).isClosedEmbedding_subtypeVal.isClosedMap _
      (hD.preimage (maps k).continuous))
  let R : C((Interval × Interval) × Interval,Y) := ⟨Rfun,hRcont⟩
  refine ⟨R,?_⟩
  intro k z σ
  have hz : (parameter k z,σ) ∈ domains k := mem_range_self z
  have hh := hR k (parameter k z,σ) hz
  change R (parameter k z,σ)=movie k (inverse k ⟨parameter k z,hz⟩,σ) at hh
  have he : inverse k ⟨parameter k z,hz⟩=z :=
    (actual_uniform_cell_parameter_embedding n hn k).toHomeomorph.symm_apply_apply z
  rw [he] at hh
  exact hh
end CurveComplex.HyperellipticModel
