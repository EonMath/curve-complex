import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1OriginalGenusAdaptersPROVED
import CurveComplexGenusTwo.Topology.RestrictedLink.OpenEmbeddingCollapseHeaders

open Set Topology CurveComplex CurveComplex.Hyperbolic

theorem actual_punctured_torus_side_torus_coordinate
    {E : Type} [TopologicalSpace E] [T2Space E]
    (V : Set E) (hV : IsOpen V)
    (e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) :
    ∃ Q : C(E,Circle × Circle),
      (∀ x : V, Q x.val = (e x).val) ∧
      (∀ x : E, x ∉ V → Q x = (1,1)) := by
  classical
  obtain ⟨κ,hκ,hκin,hκout⟩ :=
    CurveComplex.HyperellipticModel.open_embedding_collapse_continuous
      (Subtype.val : V → E) hV.isOpenEmbedding_subtypeVal
  let j : V → Circle × Circle := fun x => (e x).val
  have hj : IsEmbedding j := IsEmbedding.subtypeVal.comp e.isEmbedding
  have hr : range j = ({((1,1) : Circle × Circle)}ᶜ) := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact (e x).property
    · intro hz
      exact ⟨e.symm ⟨z,hz⟩,congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)⟩
  let J : OnePoint V ≃ₜ Circle × Circle :=
    OnePoint.equivOfIsEmbeddingOfRangeEq (1,1) j hj hr
  let Q : C(E,Circle × Circle) :=
    ⟨fun x => J (κ x), J.continuous.comp hκ⟩
  refine ⟨Q,?_,?_⟩
  · intro x
    change J (κ x.val)=(e x).val
    rw [hκin]
    rfl
  · intro x hx
    have hxr : x ∉ range (Subtype.val : V → E) := by
      rintro ⟨y,hy⟩
      exact hx (hy ▸ y.property)
    change J (κ x)=(1,1)
    rw [hκout x hxr]
    rfl

theorem actual_punctured_torus_side_circle_coordinate
    {E : Type} [TopologicalSpace E] [T2Space E]
    (V : Set E) (hV : IsOpen V)
    (e : V ≃ₜ {z : Circle × Circle // z ≠ (1,1)}) :
    ∃ q : C(E,Circle),
      (∀ x : V, q x.val = (e x).val.1) ∧
      (∀ x : E, x ∉ V → q x = 1) := by
  obtain ⟨Q,hQV,hQout⟩ :=
    actual_punctured_torus_side_torus_coordinate V hV e
  refine ⟨⟨fun x => (Q x).1,continuous_fst.comp Q.continuous⟩,?_,?_⟩
  · intro x
    exact congrArg Prod.fst (hQV x)
  · intro x hx
    exact congrArg Prod.fst (hQout x hx)

theorem actual_circle_id_not_nullhomotopic :
    ¬ (ContinuousMap.id Circle).Nullhomotopic := by
  intro hNull
  letI : ContractibleSpace Circle :=
    (contractible_iff_id_nullhomotopic Circle).mpr hNull
  letI : SimplyConnectedSpace Circle := inferInstance
  let G := AddSubgroup.zmultiples (2*Real.pi)
  let e := Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv
    (x := Circle.exp 0) ⟨0,rfl⟩
  let a : G := ⟨0,(AddSubgroup.zmultiples (2*Real.pi)).zero_mem⟩
  let b : G := ⟨2*Real.pi,AddSubgroup.mem_zmultiples (2*Real.pi)⟩
  have hab : MulOpposite.op (Multiplicative.ofAdd a) =
      MulOpposite.op (Multiplicative.ofAdd b) := by
    apply e.symm.injective
    exact Subsingleton.elim _ _
  have hv : (0 : ℝ)=2*Real.pi :=
    congrArg (fun z : (Multiplicative G)ᵐᵒᵖ =>
      ((MulOpposite.unop z).toAdd : ℝ)) hab
  linarith [Real.pi_pos]

theorem actual_horizontal_loop_cannot_homotope_to_constant_coordinate
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (d g : Curve E) (q : C(E,Circle))
    (hd : ∀ z : Circle, q (d.map z)=z)
    (x : Circle) (hg : ∀ z : Circle, q (g.map z)=x)
    (hhom : FreeHomotopic ⟨d.map,d.embedded.continuous⟩
      ⟨g.map,g.embedded.continuous⟩) : False := by
  obtain ⟨K,hK0,hK1⟩ := hhom
  have hnull : (ContinuousMap.id Circle).Nullhomotopic := by
    refine ⟨x,?_⟩
    refine ⟨{ toFun := fun p => q (K (p.2,p.1))
              continuous_toFun := q.continuous.comp
                (K.continuous.comp (continuous_snd.prodMk continuous_fst))
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      simpa using (congrArg q (hK0 z)).trans (hd z)
    · intro z
      simpa using (congrArg q (hK1 z)).trans (hg z)
  exact actual_circle_id_not_nullhomotopic hnull

theorem actual_geodesic_cannot_lie_in_constant_coordinate_side
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (d g : Curve E) (V U : Set E) (q : C(E,Circle))
    (hdV : d.image ⊆ V) (hdq : ∀ z : Circle, q (d.map z)=z)
    (hUq : ∃ x : Circle, ∀ y ∈ U, q y=x)
    (hgU : g.image ⊆ U)
    (hhom : FreeHomotopic ⟨d.map,d.embedded.continuous⟩
      ⟨g.map,g.embedded.continuous⟩) : False := by
  obtain ⟨x,hx⟩ := hUq
  apply actual_horizontal_loop_cannot_homotope_to_constant_coordinate d g q hdq x
    (fun z => hx (g.map z) (hgU ⟨z,rfl⟩)) hhom

#print axioms actual_horizontal_loop_cannot_homotope_to_constant_coordinate
#print axioms actual_punctured_torus_side_torus_coordinate
#print axioms actual_circle_id_not_nullhomotopic
