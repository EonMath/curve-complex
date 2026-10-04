import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualCommonStripNormalShiftMovie
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal gluing of a constructed supported local movie to the original map.
The two open domains are the chart domain and the closed support's complement. -/
theorem actual_closed_support_movie_gluing
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (G : C(X,Y)) (T A : Set X) (hT : IsOpen T) (hA : IsClosed A)
    (hAT : A ⊆ T) (J : C(T × Interval,Y))
    (hJ : ∀ z : T,∀ σ,z.val ∉ A → J (z,σ)=G z.val) :
    ∃ R : C(X × Interval,Y),
      (∀ (z : T) σ,R (z.val,σ)=J (z,σ)) ∧
      (∀ z σ,z ∉ A → R (z,σ)=G z) := by
  let U : Bool → Set (X × Interval) := fun b =>
    if b then Prod.fst ⁻¹' T else Prod.fst ⁻¹' Aᶜ
  have hopen (b) : IsOpen (U b) := by
    cases b
    · exact hA.isOpen_compl.preimage continuous_fst
    · exact hT.preimage continuous_fst
  let maps : ∀ b : Bool,C(U b,Y) := fun b => by
    cases b
    · exact ⟨fun z => G z.val.1,G.continuous.comp (continuous_fst.comp continuous_subtype_val)⟩
    · exact ⟨fun z => J (⟨z.val.1,z.property⟩,z.val.2),
        J.continuous.comp (((continuous_fst.comp continuous_subtype_val).subtype_mk
          (fun z => z.property)).prodMk (continuous_snd.comp continuous_subtype_val))⟩
  have hmaps (i j : Bool) (z : X × Interval) (hi : z ∈ U i) (hj : z ∈ U j) :
      maps i ⟨z,hi⟩=maps j ⟨z,hj⟩ := by
    cases i <;> cases j
    · rfl
    · exact (hJ ⟨z.1,hj⟩ z.2 hi).symm
    · exact hJ ⟨z.1,hi⟩ z.2 hj
    · rfl
  have hcover (z : X × Interval) : ∃ b,U b ∈ 𝓝 z := by
    by_cases hz : z.1 ∈ T
    · exact ⟨true,(hopen true).mem_nhds hz⟩
    · exact ⟨false,(hopen false).mem_nhds (fun ha => hz (hAT ha))⟩
  let R : C(X × Interval,Y) := ContinuousMap.liftCover U maps hmaps hcover
  refine ⟨R,?_,?_⟩
  · intro z σ
    exact ContinuousMap.liftCover_coe (i:=true) ⟨(z.val,σ),z.property⟩
  · intro z σ hz
    exact ContinuousMap.liftCover_coe (i:=false) ⟨(z,σ),hz⟩
end CurveComplex.HyperellipticModel
