import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualLiftedAxisChart

open Set Topology Schoenflies CurveComplex

/-- Construct transported actual curves and their finite common-axis data
through the same literal homeomorphism. -/
theorem actual_homeomorph_transports_finite_transverse_curves
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (a b : Curve X) (hab : Transverse a b) :
    ∃ a' b' : Curve Y,
      (∀ z, a'.map z=e (a.map z)) ∧
      (∀ z, b'.map z=e (b.map z)) ∧
      a'.image=e '' a.image ∧ b'.image=e '' b.image ∧ Transverse a' b' := by
  let a' : Curve Y := ⟨fun z => e (a.map z),e.isEmbedding.comp a.embedded⟩
  let b' : Curve Y := ⟨fun z => e (b.map z),e.isEmbedding.comp b.embedded⟩
  have ha : a'.image=e '' a.image := by
    change range (e ∘ a.map)=e '' range a.map
    exact range_comp e a.map
  have hb : b'.image=e '' b.image := by
    change range (e ∘ b.map)=e '' range b.map
    exact range_comp e b.map
  have hma (z : Y) : z∈a'.image ↔ e.symm z∈a.image := by
    rw [ha]
    constructor
    · rintro ⟨x,hx,rfl⟩; simpa using hx
    · intro hz; exact ⟨e.symm z,hz,e.apply_symm_apply z⟩
  have hmb (z : Y) : z∈b'.image ↔ e.symm z∈b.image := by
    rw [hb]
    constructor
    · rintro ⟨x,hx,rfl⟩; simpa using hx
    · intro hz; exact ⟨e.symm z,hz,e.apply_symm_apply z⟩
  refine ⟨a',b',fun _ => rfl,fun _ => rfl,ha,hb,?_,?_⟩
  · apply (hab.1.image e).subset
    intro z hz
    exact ⟨e.symm z,⟨(hma z).mp hz.1,(hmb z).mp hz.2⟩,e.apply_symm_apply z⟩
  · intro z hz
    obtain ⟨U,V,hzU,h,hU,hV,hzero,haxes⟩ :=
      actual_crossing_axis_chart_lifts_through_local_homeomorph e.symm
        e.symm.isLocalHomeomorph a b z
        (hab.2 (e.symm z) ⟨(hma z).mp hz.1,(hmb z).mp hz.2⟩)
    refine ⟨U,V,hzU,h,hU,hV,hzero,?_⟩
    intro x hx
    exact ⟨(hma x).trans (haxes x hx).1,(hmb x).trans (haxes x hx).2⟩

#print axioms actual_homeomorph_transports_finite_transverse_curves
