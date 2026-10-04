import Mathlib
open Set Topology
open scoped unitInterval
set_option maxHeartbeats 4000000
theorem actual_open_cut_lift_component_is_original_component_cover {E P : Type} [TopologicalSpace E] [TopologicalSpace P]
    [LocallyPathConnectedSpace E] (p : P → E) (hp : IsCoveringMap p)
    (U : Set E) (hU : IsOpen U) (hconn : IsConnected U) (x : P) (hx : p x∈U) :
    ∃ q : connectedComponentIn (p ⁻¹' U) x → U,
      IsCoveringMap q ∧ Function.Surjective q ∧ ∀ z,(q z).val=p z.val := by
  classical
  have hcomponentcover {E P : Type} [TopologicalSpace E] [TopologicalSpace P]
      [LocallyConnectedSpace E] (p : P → E) (hp : IsCoveringMap p) (x : P) :
      IsCoveringMap (fun z : connectedComponent x => p z.val) := by
    classical
    let C := connectedComponent x
    let q : C → E := fun z => p z.val
    intro y
    obtain ⟨hdis,U,hyU,hU,hpU,H,hH⟩ := hp y
    letI : DiscreteTopology (p ⁻¹' {y}) := hdis
    obtain ⟨N,⟨hN,hyN,hNconn⟩,hNU⟩ :=
      (LocallyConnectedSpace.open_connected_basis y).mem_iff.mp (hU.mem_nhds hyU)
    have hNU' : N⊆U := hNU
    let Fiber : Type := p ⁻¹' {y}
    let e : p ⁻¹' N ≃ₜ N × Fiber := {
      toFun := fun z =>
        (⟨(H ⟨z.val,hNU' z.property⟩).1.val,by rw [hH];exact z.property⟩,
          (H ⟨z.val,hNU' z.property⟩).2)
      invFun := fun z => ⟨(H.symm (⟨z.1.val,hNU' z.1.property⟩,z.2)).val,by
        change p (H.symm (⟨z.1.val,hNU' z.1.property⟩,z.2)).val∈N
        rw [←hH,H.apply_symm_apply]
        exact z.1.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        change (H.symm (H ⟨z.val,hNU' z.property⟩)).val=z.val
        exact congrArg Subtype.val (H.symm_apply_apply ⟨z.val,hNU' z.property⟩)
      right_inv := by
        intro z
        apply Prod.ext
        · apply Subtype.ext
          change (H (H.symm (⟨z.1.val,hNU' z.1.property⟩,z.2))).1.val=z.1.val
          exact congrArg (fun v => v.1.val) (H.apply_symm_apply (⟨z.1.val,hNU' z.1.property⟩,z.2))
        · change (H (H.symm (⟨z.1.val,hNU' z.1.property⟩,z.2))).2=z.2
          exact congrArg Prod.snd (H.apply_symm_apply (⟨z.1.val,hNU' z.1.property⟩,z.2))
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    have he (z : p ⁻¹' N) : (e z).1.val=p z.val := hH ⟨z.val,hNU' z.property⟩
    have hslice (i : Fiber) (u : N) : (e.symm (u,i)).val∈C ↔
        (e.symm (⟨y,hyN⟩,i)).val∈C := by
      have hc : IsPreconnected (Set.range (fun v : N => (e.symm (v,i)).val)) := by
        letI : ConnectedSpace N := isConnected_iff_connectedSpace.mp hNconn
        exact isPreconnected_range (by fun_prop)
      have hbase := hc.subset_connectedComponent (Set.mem_range_self (⟨y,hyN⟩ : N))
      have hu := hc.subset_connectedComponent (Set.mem_range_self u)
      constructor
      · intro hm
        have hh := hu (Set.mem_range_self (⟨y,hyN⟩ : N))
        rwa [←connectedComponent_eq hm] at hh
      · intro hm
        have hh := hbase (Set.mem_range_self u)
        rwa [←connectedComponent_eq hm] at hh
    let J : Type := {i : Fiber // (e.symm (⟨y,hyN⟩,i)).val∈C}
    let f : q ⁻¹' N ≃ₜ N × J := {
      toFun := fun z =>
        ((e ⟨z.val.val,z.property⟩).1,
         ⟨(e ⟨z.val.val,z.property⟩).2,by
           apply (hslice (e ⟨z.val.val,z.property⟩).2 (e ⟨z.val.val,z.property⟩).1).mp
           simpa only [e.symm_apply_apply] using z.val.property⟩)
      invFun := fun z => ⟨⟨(e.symm (z.1,z.2.val)).val,(hslice z.2.val z.1).mpr z.2.property⟩,by
        change p (e.symm (z.1,z.2.val)).val∈N
        rw [←he,e.apply_symm_apply]
        exact z.1.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        change (e.symm (e ⟨z.val.val,z.property⟩)).val=z.val.val
        exact congrArg Subtype.val (e.symm_apply_apply ⟨z.val.val,z.property⟩)
      right_inv := by
        intro z
        apply Prod.ext
        · change (e (e.symm (z.1,z.2.val))).1=z.1
          exact congrArg Prod.fst (e.apply_symm_apply (z.1,z.2.val))
        · apply Subtype.ext
          change (e (e.symm (z.1,z.2.val))).2=z.2.val
          exact congrArg Prod.snd (e.apply_symm_apply (z.1,z.2.val))
      continuous_toFun := by dsimp only [J]; fun_prop
      continuous_invFun := by dsimp only [J]; fun_prop }
    have hJ : IsEvenlyCovered q y J := by
      refine ⟨inferInstance,N,hyN,hN,hN.preimage (hp.continuous.comp continuous_subtype_val),f,?_⟩
      intro z
      exact he ⟨z.val.val,z.property⟩
    exact hJ.to_isEvenlyCovered_preimage
  have hprojection {E P : Type} [TopologicalSpace E] [TopologicalSpace P]
      [LocallyPathConnectedSpace E] (p : P → E) (hp : IsCoveringMap p)
      (U : Set E) (hU : IsOpen U) (x : P) :
      p '' connectedComponentIn (p ⁻¹' U) x=connectedComponentIn U (p x) := by
    classical
    by_cases hx : p x∈U
    · let F := p ⁻¹' U
      have hxF : x∈F := hx
      apply subset_antisymm
      · exact (hp.continuous.continuousOn.image_connectedComponentIn_subset hxF).trans
          (connectedComponentIn_mono (p x) (Set.image_preimage_subset p U))
      · intro z hz
        rw [connectedComponentIn_eq_image hx] at hz
        obtain ⟨zU,hzU,rfl⟩ := hz
        letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
        have hjoined : Joined (⟨p x,hx⟩ : U) zU := by
          rw [←mem_pathComponent_iff,pathComponent_eq_connectedComponent]
          exact hzU
        obtain ⟨γ⟩ := hjoined
        let q := U.restrictPreimage p
        let xF : p ⁻¹' U := ⟨x,hx⟩
        obtain ⟨δ,hδp,hδ0⟩ := (hp.restrictPreimage U).exists_path_lifts
          γ.toContinuousMap xF γ.source
        have hδrange : Set.range (fun t : unitInterval => (δ t).val)⊆connectedComponentIn F x := by
          apply (isConnected_range (continuous_subtype_val.comp δ.continuous)).isPreconnected.subset_connectedComponentIn
          · exact ⟨0,congrArg Subtype.val hδ0⟩
          · rintro v ⟨t,rfl⟩
            exact (δ t).property
        refine ⟨(δ 1).val,hδrange ⟨1,rfl⟩,?_⟩
        exact (congrArg Subtype.val (congrFun hδp 1)).trans (congrArg Subtype.val γ.target)
    · have hxF : x∉p ⁻¹' U := hx
      rw [connectedComponentIn_eq_empty hxF,Set.image_empty,connectedComponentIn_eq_empty hx]
  letI : LocallyPathConnectedSpace U := hU.locallyPathConnectedSpace
  let F := p ⁻¹' U
  let C := connectedComponentIn F x
  have hxF : x∈F := hx
  let xF : F := ⟨x,hxF⟩
  have hset : (Subtype.val ⁻¹' C : Set F)=connectedComponent xF := by
    dsimp only [C,xF]
    rw [connectedComponentIn_eq_image hxF,Set.preimage_image_eq _ Subtype.val_injective]
  let e : C ≃ₜ connectedComponent xF := {
    toFun := fun z => ⟨⟨z.val,connectedComponentIn_subset F x z.property⟩,by
      exact (Set.ext_iff.mp hset ⟨z.val,connectedComponentIn_subset F x z.property⟩).mp z.property⟩
    invFun := fun z => ⟨z.val.val,by
      exact (Set.ext_iff.mp hset z.val).mpr z.property⟩
    left_inv := by intro z; rfl
    right_inv := by intro z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let q : C → U := fun z => ⟨p z.val,connectedComponentIn_subset F x z.property⟩
  have hp0 : IsCoveringMap (U.restrictPreimage p) := hp.restrictPreimage U
  let q₁ : connectedComponent xF → U := fun z => U.restrictPreimage p z.val
  have hp1 : IsCoveringMap q₁ := hcomponentcover (U.restrictPreimage p) hp0 xF
  have hpq : IsCoveringMap q := hp1.comp_homeomorph e
  have himage : p '' C=U := by
    have ht := hprojection p hp U hU x
    rw [hconn.isPreconnected.connectedComponentIn hx] at ht
    exact ht
  refine ⟨q,hpq,?_,fun z => rfl⟩
  intro z
  have hz : z.val∈p '' C := by rw [himage]; exact z.property
  obtain ⟨y,hy,hpy⟩ := hz
  exact ⟨⟨y,hy⟩,Subtype.ext hpy⟩
