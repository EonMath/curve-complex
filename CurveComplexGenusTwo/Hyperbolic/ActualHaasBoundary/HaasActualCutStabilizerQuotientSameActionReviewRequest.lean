import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualOpenCutComponentCoverReviewRequest
import Mathlib.Topology.Algebra.MulAction
open Set Topology
open scoped Pointwise
set_option maxHeartbeats 2000000
theorem actual_open_cut_component_deck_stabilizer_quotient_cover_same_action {E P G : Type} [TopologicalSpace E] [TopologicalSpace P]
    [LocallyPathConnectedSpace E] [Group G] [MulAction G P]
    (p : P → E) (hp : IsQuotientCoveringMap p G)
    (U : Set E) (hU : IsOpen U) (hconn : IsConnected U) (x : P) (hx : p x∈U) :
    let C := connectedComponentIn (p ⁻¹' U) x
    let K := MulAction.stabilizer G C
    ∃ a : MulAction K C,letI := a
      ∃ q : C → U,IsQuotientCoveringMap q K ∧
        (∀ z,(q z).val=p z.val) ∧
        ∀ (g : K) (z : C),(@SMul.smul K C a.toSMul g z).val=g.val • z.val := by
  classical
  let C := connectedComponentIn (p ⁻¹' U) x
  let K := MulAction.stabilizer G C
  letI : ContinuousConstSMul G P := hp.toContinuousConstSMul
  have hmaps (g : K) (z : C) : g.val • z.val∈C := by
    have hs : g.val • C=C := MulAction.mem_stabilizer_iff.mp g.property
    exact (Set.ext_iff.mp hs (g.val • z.val)).mp (Set.mem_smul_set.mpr ⟨z.val,z.property,rfl⟩)
  let a : MulAction K C := {
    smul := fun g z => ⟨g.val • z.val,hmaps g z⟩
    one_smul := fun z => Subtype.ext (one_smul G z.val)
    mul_smul := fun g h z => Subtype.ext (mul_smul g.val h.val z.val) }
  letI := a
  obtain ⟨q,hq,hqs,hqpoint⟩ := actual_open_cut_lift_component_is_original_component_cover
    p hp.isCoveringMap U hU hconn x hx
  have hfix (g : G) (z : P) : p (g • z)=p z := hp.map_smul g
  let F := p ⁻¹' U
  have hxF : x∈F := hx
  have hF (g : G) : (g • ·) '' F=F := by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      change p (g • y)∈U
      rw [hfix]
      exact hy
    · intro hz
      refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
      change p (g⁻¹ • z)∈U
      rw [hfix]
      exact hz
  have htrans (g : G) : (g • ·) '' C=connectedComponentIn F (g • x) := by
    have ht := (Homeomorph.smul g).image_connectedComponentIn hxF
    change (g • ·) '' connectedComponentIn F x=connectedComponentIn ((g • ·) '' F) (g • x) at ht
    rw [hF] at ht
    exact ht
  have hquot : IsQuotientCoveringMap q K := {
    toIsQuotientMap := hq.isQuotientMap hqs
    continuous_const_smul := by
      intro g
      exact ((hp.continuous_const_smul g.val).comp continuous_subtype_val).subtype_mk _
    apply_eq_iff_mem_orbit := by
      intro z w
      constructor
      · intro hzw
        have hpzw : p z.val=p w.val := by
          rw [←hqpoint,←hqpoint]
          exact congrArg Subtype.val hzw
        obtain ⟨g,hg⟩ := hp.apply_eq_iff_mem_orbit.mp hpzw
        change g • w.val=z.val at hg
        have hzimage : z.val∈(g • ·) '' C := ⟨w.val,w.property,hg⟩
        have hzcomp : z.val∈connectedComponentIn F (g • x) := htrans g ▸ hzimage
        have hcomp : connectedComponentIn F (g • x)=C :=
          (connectedComponentIn_eq hzcomp).trans (connectedComponentIn_eq z.property).symm
        have hgK : g∈K := by
          apply MulAction.mem_stabilizer_iff.mpr
          change (g • ·) '' C=C
          exact (htrans g).trans hcomp
        exact ⟨⟨g,hgK⟩,Subtype.ext hg⟩
      · rintro ⟨g,hg⟩
        apply Subtype.ext
        rw [hqpoint,hqpoint]
        have he := congrArg Subtype.val hg
        change g.val • w.val=z.val at he
        rw [←he,hfix]
    disjoint := by
      intro z
      obtain ⟨V,hV,hdis⟩ := hp.disjoint z.val
      refine ⟨Subtype.val ⁻¹' V,continuous_subtype_val.continuousAt.preimage_mem_nhds hV,?_⟩
      intro g hg
      apply Subtype.ext
      apply hdis g.val
      obtain ⟨y,⟨w,hw,rfl⟩,hy⟩ := hg
      exact ⟨g.val • w.val,⟨w.val,hw,rfl⟩,hy⟩ }
  exact ⟨a,q,hquot,hqpoint,fun g z => rfl⟩
