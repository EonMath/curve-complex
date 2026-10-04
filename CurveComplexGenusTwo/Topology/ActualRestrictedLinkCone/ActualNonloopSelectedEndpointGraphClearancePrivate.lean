import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35

open Set Metric Schoenflies CurveComplex
set_option maxHeartbeats 2600000

open Lean Elab Term in
elab "checkedRLNonloopPrivate0" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `CurveComplex.HyperellipticModel.actual_graph_fixed_terminal_chart_motion_lift_private
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRLNonloopPrivate1" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `actual_literal_radial_graph_arbitrary_open_support_source_motion_private
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRLNonloopPrivate2" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `actual_positive_ray_graph_fixed_old_avoiding_source_motion_private
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRLNonloopPrivate3" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `actual_old_avoiding_free_source_star_supported_motion_private
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRLNonloopPrivate4" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `actual_literal_fan_direction_normalization_preserves_ray_separation_private
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRLNonloopPrivate5" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `CurveComplex.HyperellipticModel.actual_marked_whole_trace_fan_two_prescribed_incidences_private
  discard <| getConstInfo n
  return mkConst n

open Lean Elab Term in
elab "checkedRLNonloopPrivate6" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualRelativeConvexSectorGermStraighteningPrivateV35 0).append
    `CurveComplex.HyperellipticModel.actual_graph_fixed_terminal_collars_consume_interior_preparation_private
  discard <| getConstInfo n
  return mkConst n

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_arc_selected_terminal_chart_germ_source_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (b : EssentialMarkedArc M) (terminal : Bool)
    (e : OpenPartialHomeomorph S Plane)
    (he0 : e (if terminal then b.val.map 1 else b.val.map 0)=0)
    (r : ℝ) (hr : 0<r) (hr1 : r<1)
    (hsource : ∀ t,b.val.map (endpointGermParameter terminal r hr hr1 t)∈e.source) :
    let γ : Interval → Plane := fun t => e (b.val.map (endpointGermParameter terminal r hr hr1 t))
    Topology.IsClosedEmbedding γ ∧ γ 0=0 := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  intro γ
  have hb := actual_endpoint_germ_embedding M b terminal r hr hr1
  have hc : Continuous γ := continuousOn_univ.mp (e.continuousOn.comp hb.continuous.continuousOn
    (fun t _ => hsource t))
  refine ⟨hc.isClosedEmbedding (fun t u he => hb.injective (e.injOn (hsource t) (hsource u) he)),?_⟩
  cases terminal <;> simpa [γ,endpointGermParameter] using he0
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_arc_selected_terminal_chart_germ_source_private

private theorem actual_entire_fixed_set_ambient_isotopy_reverse_private
    {X : Type} [TopologicalSpace X] (H : AmbientIsotopy X) (P : Set X)
    (hfix : ∀ t x,x∈P → H.map (t,x)=x) :
    ∃ R : AmbientIsotopy X,(∀ t x,x∈P → R.map (t,x)=x) ∧
      ∀ x,R.finalMap (H.finalMap x)=x := by
  obtain ⟨e,he⟩ := H.homeomorphism_at (1:CurveComplex.Interval)
  have hef : ∀ x∈P,e x=x := fun x hx => (he x).trans (hfix 1 x hx)
  have hes : ∀ x∈P,e.symm x=x := by
    intro x hx
    apply e.injective
    rw [e.apply_symm_apply,hef x hx]
  let rev : CurveComplex.Interval → CurveComplex.Interval := fun t => ⟨1-t.val,by
    constructor <;> linarith [t.property.1,t.property.2]⟩
  have hrev : Continuous rev := (continuous_const.sub continuous_subtype_val).subtype_mk _
  have hrev0 : rev 0=1 := by apply Subtype.ext;norm_num [rev]
  have hrev1 : rev 1=0 := by apply Subtype.ext;norm_num [rev]
  let R : AmbientIsotopy X := {
    map := ⟨fun z => H.map (rev z.1,e.symm z.2),
      H.map.continuous.comp ((hrev.comp continuous_fst).prodMk
        (e.symm.continuous.comp continuous_snd))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨f,hf⟩ := H.homeomorphism_at (rev t)
      exact ⟨e.symm.trans f,fun x => hf (e.symm x)⟩
    at_zero := by
      intro x
      change H.map (rev 0,e.symm x)=x
      rw [hrev0,←he,e.apply_symm_apply] }
  refine ⟨R,?_,?_⟩
  · intro t x hx
    change H.map (rev t,e.symm x)=x
    rw [hes x hx,hfix (rev t) x hx]
  · intro x
    change H.map (rev 1,e.symm (H.finalMap x))=x
    rw [hrev1]
    change H.map ((⟨0,by norm_num⟩ : CurveComplex.Interval),e.symm (H.finalMap x))=x
    rw [H.at_zero]
    exact (congrArg e.symm (he x).symm).trans (e.symm_apply_apply x)
#print axioms actual_entire_fixed_set_ambient_isotopy_reverse_private

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_arc_selected_terminal_full_graph_chart_supported_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M) (terminal : Bool)
    (e : OpenPartialHomeomorph S Plane)
    (hpe : (if terminal then b.val.map 1 else b.val.map 0)∈e.source)
    (he0 : e (if terminal then b.val.map 1 else b.val.map 0)=0)
    (hemarks : ∀ x,x∈e.source → x∈M.cover.branch → x=(if terminal then b.val.map 1 else b.val.map 0))
    (P : Set S) {J K : Type} [Fintype J] [Fintype K]
    (v : J → Plane) (hv : ∀ j,‖v j‖=1)
    (hmeet : ∀ i j,i≠j → segment ℝ (0:Plane) (v i) ∩ segment ℝ (0:Plane) (v j)={0})
    (i0 i1 : J) (hne : i0≠i1) (hopp : v i1=-v i0)
    (hgraph : ∀ x,x∈e.source → (x∈P ↔ ∃ j,∃ d : ℝ,0≤d ∧ e x=d • v j))
    (hbP : ∀ t : Interval,0<t.val → t.val<1 → b.val.map t∉P)
    (old : K → Plane)
    (haOld : ∀ x,x∈a.val.image → x∈e.source → ∃ k,∃ d : ℝ,0≤d ∧ e x=d • old k)
    (R : ℝ) (hR : 0<R) (hRT : closedBall (0:Plane) R⊆e.target)
    (r : ℝ) (hr : 0<r) (hrhalf : r<1/2)
    (hsource : ∀ t,b.val.map (endpointGermParameter terminal r hr (by linarith) t)∈e.source) :
    ∃ c : EssentialMarkedArc M,∃ H : AmbientIsotopy S,∃ δ : ℝ,
      0<δ ∧ δ<1/2 ∧
      Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x,x∈M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x,x∈P → H.map (t,x)=x) ∧
      (∀ t,c.val.map t=H.finalMap (b.val.map t)) ∧
      (∀ t x,x∉e.source → H.map (t,x)=x) ∧
      ∀ t : Interval,0<t.val → t.val<1 →
        (if terminal then 1-t.val else t.val)≤δ → c.val.map t∉a.val.image := by
  classical
  let γ : Interval → Plane := fun t => e (b.val.map (endpointGermParameter terminal r hr (by linarith) t))
  obtain ⟨hγ,hγ0⟩ := actual_marked_arc_selected_terminal_chart_germ_source_private
    M b terminal e he0 r hr (by linarith) hsource
  let α : Path (0:Plane) (γ 1) := {
    toFun := γ,continuous_toFun := hγ.continuous,source' := hγ0,target' := rfl }
  have havoid : ∀ t : Interval,0<t.val → ∀ j,
      γ t∉{z : Plane | ∃ d : ℝ,0≤d ∧ z=d • v j} := by
    intro t ht j hx
    have hb := (hgraph _ (hsource t)).mpr ⟨j,hx⟩
    apply hbP _ ?_ ?_ hb
    · cases terminal <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2]
    · cases terminal <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2]
  obtain ⟨L,hL0,hLout,hLgraph,cut,hcut,hcut1,q,hq,himage,hqold⟩ :=
    checkedRLNonloopPrivate1 v old hv hmeet i0 i1 hne hopp
      α hγ.injective havoid (ball (0:Plane) R) isOpen_ball (by simpa using hR)
  obtain ⟨H,hHmarks,hHP,hHout,hHstay,hHcoord⟩ :=
    checkedRLNonloopPrivate0 M _ e hpe he0 hemarks R hRT P L hL0 hLout
      (by intro t x hx hxs;obtain ⟨j,d,hd,he⟩ := (hgraph x hxs).mp hx;rw [he];exact hLgraph t j d hd)
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:Interval)
  have hHg : H.finalMap=g := funext (fun x => (hg x).symm)
  have hgmarks : ∀ x,x∈M.cover.branch → g x=x := fun x hx => by rw [←hHg];exact hHmarks 1 x hx
  let c := b.transport g hgmarks
  have hcmap (t : Interval) : c.val.map t=H.finalMap (b.val.map t) := by change g (b.val.map t)=_;rw [hHg]
  have hclass : Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hHmarks,?_⟩
    rw [hHg]
    exact (MarkedArc.transport_image b.val g hgmarks).symm
  let δ := r*cut.val/2
  have hδ : 0<δ := by
    have hcv : 0<cut.val := hcut
    dsimp [δ];positivity
  have hδr : δ≤r := by dsimp [δ];nlinarith [cut.property.2]
  have hδhalf : δ<1/2 := hδr.trans_lt hrhalf
  have hδcut : δ≤r*cut.val := by dsimp [δ];nlinarith [cut.property.1]
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hHmarks,hHP,hcmap,hHout,?_⟩
  intro t ht0 ht1 htδ hcontact
  let z := if terminal then 1-t.val else t.val
  have hz : 0≤z := by cases terminal <;> dsimp [z] <;> linarith
  let u : Interval := ⟨z/r,⟨div_nonneg hz hr.le,(div_le_one₀ hr).mpr (htδ.trans hδr)⟩⟩
  have hu : u∈Icc 0 cut := ⟨u.property.1,(div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans hδcut)⟩
  have htu : endpointGermParameter terminal r hr (by linarith) u=t := by
    apply Subtype.ext
    cases terminal <;> dsimp [endpointGermParameter,u,z] <;> field_simp <;> ring
  have hbt : b.val.map t∈e.source := htu ▸ hsource u
  have hct : c.val.map t∈e.source := by rw [hcmap];exact hHstay 1 _ hbt
  have hseg : e (c.val.map t)∈segment ℝ (0:Plane) q := by
    rw [hcmap]
    change e (H.map (1,b.val.map t))∈segment ℝ (0:Plane) q
    rw [hHcoord 1 _ hbt]
    change L.finalMap (e (b.val.map t))∈segment ℝ (0:Plane) q
    rw [←himage]
    refine ⟨γ u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg L.finalMap (congrArg e (congrArg b.val.map htu))
  obtain ⟨k,d,hd,heold⟩ := haOld _ hcontact hct
  have hzero : e (c.val.map t)=0 := by
    apply Set.mem_singleton_iff.mp
    rw [←hqold k]
    exact ⟨hseg,⟨d,hd,heold⟩⟩
  have hebase : c.val.map t=(if terminal then b.val.map 1 else b.val.map 0) := e.injOn hct hpe (hzero.trans he0.symm)
  have hm : c.val.map t∈M.cover.branch := by
    rw [hebase]
    cases terminal
    · exact b.val.start_marked
    · exact b.val.end_marked
  rcases c.val.marked_only_at_ends t hm with he|he
  · have hh := congrArg Subtype.val he;change t.val=0 at hh;linarith
  · have hh := congrArg Subtype.val he;change t.val=1 at hh;linarith
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_arc_selected_terminal_full_graph_chart_supported_clearance_private

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_arc_selected_terminal_positive_graph_chart_supported_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M) (terminal : Bool)
    (e : OpenPartialHomeomorph S Plane)
    (hpe : (if terminal then b.val.map 1 else b.val.map 0)∈e.source)
    (he0 : e (if terminal then b.val.map 1 else b.val.map 0)=0)
    (hemarks : ∀ x,x∈e.source → x∈M.cover.branch → x=(if terminal then b.val.map 1 else b.val.map 0))
    (P : Set S) {K : Type} [Fintype K]
    (hgraph : ∀ x,x∈e.source → (x∈P ↔ e x 1=0 ∧ 0≤e x 0))
    (hbP : ∀ t : Interval,0<t.val → t.val<1 → b.val.map t∉P)
    (old : K → Plane)
    (haOld : ∀ x,x∈a.val.image → x∈e.source → ∃ k,∃ d : ℝ,0≤d ∧ e x=d • old k)
    (R : ℝ) (hR : 0<R) (hRT : closedBall (0:Plane) R⊆e.target)
    (r : ℝ) (hr : 0<r) (hrhalf : r<1/2)
    (hsource : ∀ t,b.val.map (endpointGermParameter terminal r hr (by linarith) t)∈e.source) :
    ∃ c : EssentialMarkedArc M,∃ H : AmbientIsotopy S,∃ δ : ℝ,
      0<δ ∧ δ<1/2 ∧
      Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x,x∈M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x,x∈P → H.map (t,x)=x) ∧
      (∀ t,c.val.map t=H.finalMap (b.val.map t)) ∧
      (∀ t x,x∉e.source → H.map (t,x)=x) ∧
      ∀ t : Interval,0<t.val → t.val<1 →
        (if terminal then 1-t.val else t.val)≤δ → c.val.map t∉a.val.image := by
  classical
  let γ : Interval → Plane := fun t => e (b.val.map (endpointGermParameter terminal r hr (by linarith) t))
  obtain ⟨hγ,hγ0⟩ := actual_marked_arc_selected_terminal_chart_germ_source_private
    M b terminal e he0 r hr (by linarith) hsource
  let α : Path (0:Plane) (γ 1) := {
    toFun := γ,continuous_toFun := hγ.continuous,source' := hγ0,target' := rfl }
  have havoid : ∀ t : Interval,0<t → γ t∉{z : Plane | z 1=0 ∧ 0≤z 0} := by
    intro t ht hx
    have htv : 0<t.val := ht
    have hb := (hgraph _ (hsource t)).mpr hx
    apply hbP _ ?_ ?_ hb
    · cases terminal <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2]
    · cases terminal <;> dsimp [endpointGermParameter] <;> nlinarith [t.property.2]
  obtain ⟨L,R₀,hR₀,hR₀V,hL0,hLout₀,hLgraph,cut,hcut,hcut1,q,hq,himage,_,hqold⟩ :=
    checkedRLNonloopPrivate2 old α hγ.injective havoid
      (ball (0:Plane) R) isOpen_ball (by simpa using hR)
  have hLout : ∀ t x,x∉ball (0:Plane) R → L.map (t,x)=x := by
    intro t x hx
    apply hLout₀ t x
    exact fun hi => hx (hR₀V (ball_subset_closedBall hi))
  obtain ⟨H,hHmarks,hHP,hHout,hHstay,hHcoord⟩ :=
    checkedRLNonloopPrivate0 M _ e hpe he0 hemarks R hRT P L hL0 hLout
      (by intro t x hx hxs;exact hLgraph t (e x) ((hgraph x hxs).mp hx).1 ((hgraph x hxs).mp hx).2)
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:Interval)
  have hHg : H.finalMap=g := funext (fun x => (hg x).symm)
  have hgmarks : ∀ x,x∈M.cover.branch → g x=x := fun x hx => by rw [←hHg];exact hHmarks 1 x hx
  let c := b.transport g hgmarks
  have hcmap (t : Interval) : c.val.map t=H.finalMap (b.val.map t) := by change g (b.val.map t)=_;rw [hHg]
  have hclass : Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hHmarks,?_⟩
    rw [hHg]
    exact (MarkedArc.transport_image b.val g hgmarks).symm
  let δ := r*cut.val/2
  have hδ : 0<δ := by
    have hcv : 0<cut.val := hcut
    dsimp [δ];positivity
  have hδr : δ≤r := by dsimp [δ];nlinarith [cut.property.2]
  have hδhalf : δ<1/2 := hδr.trans_lt hrhalf
  have hδcut : δ≤r*cut.val := by dsimp [δ];nlinarith [cut.property.1]
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hHmarks,hHP,hcmap,hHout,?_⟩
  intro t ht0 ht1 htδ hcontact
  let z := if terminal then 1-t.val else t.val
  have hz : 0≤z := by cases terminal <;> dsimp [z] <;> linarith
  let u : Interval := ⟨z/r,⟨div_nonneg hz hr.le,(div_le_one₀ hr).mpr (htδ.trans hδr)⟩⟩
  have hu : u∈Icc 0 cut := ⟨u.property.1,(div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans hδcut)⟩
  have htu : endpointGermParameter terminal r hr (by linarith) u=t := by
    apply Subtype.ext
    cases terminal <;> dsimp [endpointGermParameter,u,z] <;> field_simp <;> ring
  have hbt : b.val.map t∈e.source := htu ▸ hsource u
  have hct : c.val.map t∈e.source := by rw [hcmap];exact hHstay 1 _ hbt
  have hseg : e (c.val.map t)∈segment ℝ (0:Plane) q := by
    rw [hcmap]
    change e (H.map (1,b.val.map t))∈segment ℝ (0:Plane) q
    rw [hHcoord 1 _ hbt]
    change L.finalMap (e (b.val.map t))∈segment ℝ (0:Plane) q
    rw [←himage]
    refine ⟨γ u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg L.finalMap (congrArg e (congrArg b.val.map htu))
  obtain ⟨k,d,hd,heold⟩ := haOld _ hcontact hct
  have hzero : e (c.val.map t)=0 := by
    apply Set.mem_singleton_iff.mp
    rw [←hqold k]
    exact ⟨hseg,⟨d,hd,heold⟩⟩
  have hebase : c.val.map t=(if terminal then b.val.map 1 else b.val.map 0) := e.injOn hct hpe (hzero.trans he0.symm)
  have hm : c.val.map t∈M.cover.branch := by
    rw [hebase]
    cases terminal
    · exact b.val.start_marked
    · exact b.val.end_marked
  rcases c.val.marked_only_at_ends t hm with he|he
  · have hh := congrArg Subtype.val he;change t.val=0 at hh;linarith
  · have hh := congrArg Subtype.val he;change t.val=1 at hh;linarith
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_arc_selected_terminal_positive_graph_chart_supported_clearance_private

namespace CurveComplex.HyperellipticModel
private theorem actual_marked_arc_selected_terminal_free_graph_chart_supported_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M) (terminal : Bool)
    (e : OpenPartialHomeomorph S Plane)
    (hpe : (if terminal then b.val.map 1 else b.val.map 0)∈e.source)
    (he0 : e (if terminal then b.val.map 1 else b.val.map 0)=0)
    (hemarks : ∀ x,x∈e.source → x∈M.cover.branch → x=(if terminal then b.val.map 1 else b.val.map 0))
    (P : Set S) {K : Type} [Fintype K]
    (hgraph : Disjoint e.source P)
    (hbP : ∀ t : Interval,0<t.val → t.val<1 → b.val.map t∉P)
    (old : K → Plane) (hold : ∀ k,old k≠0)
    (haOld : ∀ x,x∈a.val.image → x∈e.source → ∃ k,∃ d : ℝ,0≤d ∧ e x=d • old k)
    (R : ℝ) (hR : 0<R) (hRT : closedBall (0:Plane) R⊆e.target)
    (r : ℝ) (hr : 0<r) (hrhalf : r<1/2)
    (hsource : ∀ t,b.val.map (endpointGermParameter terminal r hr (by linarith) t)∈e.source) :
    ∃ c : EssentialMarkedArc M,∃ H : AmbientIsotopy S,∃ δ : ℝ,
      0<δ ∧ δ<1/2 ∧
      Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x,x∈M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x,x∈P → H.map (t,x)=x) ∧
      (∀ t,c.val.map t=H.finalMap (b.val.map t)) ∧
      (∀ t x,x∉e.source → H.map (t,x)=x) ∧
      ∀ t : Interval,0<t.val → t.val<1 →
        (if terminal then 1-t.val else t.val)≤δ → c.val.map t∉a.val.image := by
  classical
  let γ : Interval → Plane := fun t => e (b.val.map (endpointGermParameter terminal r hr (by linarith) t))
  obtain ⟨hγ,hγ0⟩ := actual_marked_arc_selected_terminal_chart_germ_source_private
    M b terminal e he0 r hr (by linarith) hsource
  let α : Path (0:Plane) (γ 1) := {
    toFun := γ,continuous_toFun := hγ.continuous,source' := hγ0,target' := rfl }
  obtain ⟨L,hL0,hLout,cut₀,v₀,hcut₀,hvOld⟩ :=
    checkedRLNonloopPrivate3
      (fun _ : PUnit => γ) (fun _ => hγ) (fun _ => hγ0)
      (by intro i j hij;exact False.elim (hij (Subsingleton.elim i j))) old hold
      (ball (0:Plane) R) isOpen_ball (by simpa using hR)
  let cut := cut₀ PUnit.unit
  let q := v₀ PUnit.unit
  obtain ⟨hcut,hcut1,hq,himage⟩ := hcut₀ PUnit.unit
  have hqold : ∀ k,segment ℝ (0:Plane) q ∩
      {z : Plane | ∃ d : ℝ,0≤d ∧ z=d • old k}={0} := hvOld PUnit.unit
  obtain ⟨H,hHmarks,hHP,hHout,hHstay,hHcoord⟩ :=
    checkedRLNonloopPrivate0 M _ e hpe he0 hemarks R hRT P L hL0 hLout
      (by intro t x hx hxs;exact False.elim (Set.disjoint_left.mp hgraph hxs hx))
  obtain ⟨g,hg⟩ := H.homeomorphism_at (1:Interval)
  have hHg : H.finalMap=g := funext (fun x => (hg x).symm)
  have hgmarks : ∀ x,x∈M.cover.branch → g x=x := fun x hx => by rw [←hHg];exact hHmarks 1 x hx
  let c := b.transport g hgmarks
  have hcmap (t : Interval) : c.val.map t=H.finalMap (b.val.map t) := by change g (b.val.map t)=_;rw [hHg]
  have hclass : Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b := by
    apply Eq.symm
    apply Quotient.sound
    refine ⟨H,hHmarks,?_⟩
    rw [hHg]
    exact (MarkedArc.transport_image b.val g hgmarks).symm
  let δ := r*cut.val/2
  have hδ : 0<δ := by
    have hcv : 0<cut.val := hcut
    dsimp [δ];positivity
  have hδr : δ≤r := by dsimp [δ];nlinarith [cut.property.2]
  have hδhalf : δ<1/2 := hδr.trans_lt hrhalf
  have hδcut : δ≤r*cut.val := by dsimp [δ];nlinarith [cut.property.1]
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hHmarks,hHP,hcmap,hHout,?_⟩
  intro t ht0 ht1 htδ hcontact
  let z := if terminal then 1-t.val else t.val
  have hz : 0≤z := by cases terminal <;> dsimp [z] <;> linarith
  let u : Interval := ⟨z/r,⟨div_nonneg hz hr.le,(div_le_one₀ hr).mpr (htδ.trans hδr)⟩⟩
  have hu : u∈Icc 0 cut := ⟨u.property.1,(div_le_iff₀ hr).mpr (by simpa only [mul_comm] using htδ.trans hδcut)⟩
  have htu : endpointGermParameter terminal r hr (by linarith) u=t := by
    apply Subtype.ext
    cases terminal <;> dsimp [endpointGermParameter,u,z] <;> field_simp <;> ring
  have hbt : b.val.map t∈e.source := htu ▸ hsource u
  have hct : c.val.map t∈e.source := by rw [hcmap];exact hHstay 1 _ hbt
  have hseg : e (c.val.map t)∈segment ℝ (0:Plane) q := by
    rw [hcmap]
    change e (H.map (1,b.val.map t))∈segment ℝ (0:Plane) q
    rw [hHcoord 1 _ hbt]
    change L.finalMap (e (b.val.map t))∈segment ℝ (0:Plane) q
    rw [←himage]
    refine ⟨γ u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg L.finalMap (congrArg e (congrArg b.val.map htu))
  obtain ⟨k,d,hd,heold⟩ := haOld _ hcontact hct
  have hzero : e (c.val.map t)=0 := by
    apply Set.mem_singleton_iff.mp
    rw [←hqold k]
    exact ⟨hseg,⟨d,hd,heold⟩⟩
  have hebase : c.val.map t=(if terminal then b.val.map 1 else b.val.map 0) := e.injOn hct hpe (hzero.trans he0.symm)
  have hm : c.val.map t∈M.cover.branch := by
    rw [hebase]
    cases terminal
    · exact b.val.start_marked
    · exact b.val.end_marked
  rcases c.val.marked_only_at_ends t hm with he|he
  · have hh := congrArg Subtype.val he;change t.val=0 at hh;linarith
  · have hh := congrArg Subtype.val he;change t.val=1 at hh;linarith
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_marked_arc_selected_terminal_free_graph_chart_supported_clearance_private

namespace CurveComplex.HyperellipticModel
private theorem actual_single_incident_graph_selected_terminal_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (selected : Bool)
    (V : Set S) (hV : IsOpen V)
    (hpV : (if selected then b.val.map 1 else b.val.map 0)∈V)
    (j₀ : G) (terminal₀ : Bool)
    (hincident : (if terminal₀ then (graph j₀).val.map 1 else (graph j₀).val.map 0) = (if selected then b.val.map 1 else b.val.map 0))
    (honly : ∀ j terminal,
      ((if terminal then (graph j).val.map 1 else (graph j).val.map 0) = (if selected then b.val.map 1 else b.val.map 0) ↔
        j = j₀ ∧ terminal = terminal₀))
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      (∀ t x,x∉V → H.map (t,x)=x) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        (if selected then 1-t.val else t.val) ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let p := (if selected then b.val.map 1 else b.val.map 0)
  let family : Option G → EssentialMarkedArc M := fun i => Option.elim i a graph
  obtain ⟨F,hpF,hFp,hFV,hmarks,r₀,hr₀,hr₀half,v,hvn,hv0,_,_,_,_,ε,hε,hεT,hεv,htrace,_⟩ :=
    actual_marked_endpoint_source_fan_chart M family hfinite p (by cases selected; exact b.val.start_marked; exact b.val.end_marked)
      V hV hpV (some j₀,terminal₀) hincident
  let U : Set S := F.source ∩ F ⁻¹' ball (0:Plane) (ε/2)
  have hU : IsOpen U := F.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hpF,by simpa [hFp] using half_pos hε⟩
  let e := F.restr U
  have hes : e.source = F.source ∩ U := by
    rw [OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have heval (x : S) : e x = F x := rfl
  have hpe : p ∈ e.source := hes.symm ▸ ⟨hpF,hpU⟩
  have he0 : e p = 0 := hFp
  have hxF (x : S) (hx : x ∈ e.source) : x ∈ F.source := (hes ▸ hx).1
  have hxBall (x : S) (hx : x ∈ e.source) : F x ∈ ball (0:Plane) ε :=
    (ball_subset_ball (by linarith : ε/2 ≤ ε)) ((hes ▸ hx).2.2)
  have hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = p := by
    intro x hx hm
    exact Set.mem_singleton_iff.mp (hmarks ▸ (show x ∈ F.source ∩ (M.cover.branch:Set S) from ⟨hxF x hx,hm⟩))
  have hR : 0 < ε/4 := by positivity
  have hRT : closedBall (0:Plane) (ε/4) ⊆ e.target := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ε/4 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hzε : z ∈ ball (0:Plane) ε := by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε by linarith)
    have hzF : z ∈ F.target := hεT hzε
    have hx : F.symm z ∈ e.source := by
      rw [hes]
      refine ⟨F.map_target hzF,⟨F.map_target hzF,?_⟩⟩
      rw [mem_preimage,F.right_inv hzF]
      simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε/2 by linarith)
    have hh := e.map_source hx
    change F (F.symm z) ∈ e.target at hh
    rw [F.right_inv hzF] at hh
    exact hh
  have hgraph : ∀ x, x ∈ e.source →
      (x ∈ ⋃ j, (graph j).val.image ↔ e x 1 = 0 ∧ 0 ≤ e x 0) := by
    intro x hx
    constructor
    · intro hp
      obtain ⟨j,hj⟩ := mem_iUnion.mp hp
      obtain ⟨terminal,hi,hs⟩ := (htrace (some j) x (hxF x hx) (hxBall x hx)).mp hj
      obtain ⟨hj0,ht0⟩ := (honly j terminal).mp hi
      subst j; subst terminal
      rw [hv0] at hs
      rw [segment_eq_image] at hs
      obtain ⟨d,hd,hde⟩ := hs
      have heq : e x = d • Plane.mk 1 0 := by simpa only [heval,smul_zero,add_zero,zero_add] using hde.symm
      rw [heq]
      constructor
      · simp
      · simpa using hd.1
    · intro hxaxis
      have hε1 : ε < 1 := by
        have hh := hεv (some j₀,terminal₀) hincident
        rw [hv0] at hh
        simpa [Plane.mk,EuclideanSpace.norm_eq] using hh
      have hx0 : e x 0 ≤ 1 := by
        have hh : |e x 0| ≤ ‖e x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (e x) 0
        have hn : ‖e x‖ < ε := by simpa only [heval,mem_ball,dist_zero_right] using hxBall x hx
        exact (le_abs_self _).trans (hh.trans (hn.le.trans hε1.le))
      have hs : e x ∈ segment ℝ (0:Plane) (Plane.mk 1 0) := by
        rw [segment_eq_image]
        refine ⟨e x 0,⟨hxaxis.2,hx0⟩,?_⟩
        ext i
        fin_cases i <;> simp [hxaxis.1]
      apply mem_iUnion.mpr
      refine ⟨j₀,(htrace (some j₀) x (hxF x hx) (hxBall x hx)).mpr ?_⟩
      exact ⟨terminal₀,hincident,by simpa only [heval,hv0] using hs⟩
  let Old : Type := {terminal : Bool // (if terminal then a.val.map 1 else a.val.map 0) = p}
  let old : Old → Plane := fun k => v (none,k.val)
  have hold : ∀ k, old k ≠ 0 := fun k => hvn (none,k.val) k.property
  have haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k : Old, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k := by
    intro x hx hxs
    obtain ⟨terminal,hi,hs⟩ := (htrace none x (hxF x hxs) (hxBall x hxs)).mp hx
    rw [segment_eq_image] at hs
    obtain ⟨d,hd,hde⟩ := hs
    exact ⟨⟨terminal,hi⟩,d,hd.1,by simpa only [heval,smul_zero,add_zero,zero_add,old] using hde.symm⟩
  obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => b) p
    e.source e.open_source hpe
  have hsource : ∀ t, b.val.map
      (endpointGermParameter selected r hr (by linarith) t) ∈ e.source := by
    intro t
    cases selected
    · apply hstart PUnit.unit rfl
      change r*t.val ≤ r
      nlinarith [t.property.2]
    · apply hend PUnit.unit rfl
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  obtain ⟨c,H,δ,hδ,hδhalf,hclass,hm,hG,hmap,hout,htail⟩ :=
    actual_marked_arc_selected_terminal_positive_graph_chart_supported_clearance_private M a b selected e
    hpe he0 hemarks (⋃ j,(graph j).val.image) hgraph hbP old haOld
    (ε/4) hR hRT r hr hrhalf hsource
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hm,hG,hmap,?_,htail⟩
  intro t x hx
  apply hout t x
  exact fun hxs => hx (hFV (hxF x hxs))
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
private theorem actual_multiple_incident_graph_selected_terminal_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (selected : Bool)
    (V : Set S) (hV : IsOpen V)
    (hpV : (if selected then b.val.map 1 else b.val.map 0)∈V)
    (g₀ g₁ : G × Bool)
    (hg₀ : (if g₀.2 then (graph g₀.1).val.map 1 else (graph g₀.1).val.map 0) = (if selected then b.val.map 1 else b.val.map 0))
    (hg₁ : (if g₁.2 then (graph g₁.1).val.map 1 else (graph g₁.1).val.map 0) = (if selected then b.val.map 1 else b.val.map 0))
    (hne : g₀≠g₁)
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      (∀ t x,x∉V → H.map (t,x)=x) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        (if selected then 1-t.val else t.val) ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let p := (if selected then b.val.map 1 else b.val.map 0)
  let family : Option G → EssentialMarkedArc M := fun i => Option.elim i a graph
  have hchosen : (some g₀.1,g₀.2) ≠ (some g₁.1,g₁.2) := by
    intro he
    apply hne
    exact Prod.ext (Option.some.inj (congrArg Prod.fst he)) (congrArg (fun z : Option G × Bool => z.2) he)
  obtain ⟨F,hpF,hFp,hFV,hmarks,r₀,hr₀,hr₀half,v,hvn,hv0,hv1,_,hvmeet,_,ε,hε,hεT,hεv,htrace,_⟩ :=
    checkedRLNonloopPrivate5 M family hfinite p (by cases selected; exact b.val.start_marked; exact b.val.end_marked)
      V hV hpV (some g₀.1,g₀.2) (some g₁.1,g₁.2) hg₀ hg₁ hchosen
  let U : Set S := F.source ∩ F ⁻¹' ball (0:Plane) (ε/2)
  have hU : IsOpen U := F.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hpF,by simpa [hFp] using half_pos hε⟩
  let e := F.restr U
  have hes : e.source = F.source ∩ U := by
    rw [OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have heval (x : S) : e x = F x := rfl
  have hpe : p ∈ e.source := hes.symm ▸ ⟨hpF,hpU⟩
  have he0 : e p = 0 := hFp
  have hxF (x : S) (hx : x ∈ e.source) : x ∈ F.source := (hes ▸ hx).1
  have hxBall (x : S) (hx : x ∈ e.source) : F x ∈ ball (0:Plane) ε :=
    (ball_subset_ball (by linarith : ε/2 ≤ ε)) ((hes ▸ hx).2.2)
  have hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = p := by
    intro x hx hm
    exact Set.mem_singleton_iff.mp (hmarks ▸ (show x ∈ F.source ∩ (M.cover.branch:Set S) from ⟨hxF x hx,hm⟩))
  have hR : 0 < ε/4 := by positivity
  have hRT : closedBall (0:Plane) (ε/4) ⊆ e.target := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ε/4 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hzε : z ∈ ball (0:Plane) ε := by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε by linarith)
    have hzF : z ∈ F.target := hεT hzε
    have hx : F.symm z ∈ e.source := by
      rw [hes]
      refine ⟨F.map_target hzF,⟨F.map_target hzF,?_⟩⟩
      rw [mem_preimage,F.right_inv hzF]
      simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε/2 by linarith)
    have hh := e.map_source hx
    change F (F.symm z) ∈ e.target at hh
    rw [F.right_inv hzF] at hh
    exact hh
  let D := {g : G × Bool // (if g.2 then (graph g.1).val.map 1 else (graph g.1).val.map 0) = p}
  let raw : D → Plane := fun g => v (some g.val.1,g.val.2)
  let unit : D → Plane := fun g => ‖raw g‖⁻¹ • raw g
  have hraw (g : D) : raw g≠0 := hvn (some g.val.1,g.val.2) g.property
  have hrawmeet : ∀ i j : D,i≠j → segment ℝ (0:Plane) (raw i) ∩ segment ℝ (0:Plane) (raw j)={0} := by
    intro i j hij
    apply hvmeet _ _ i.property j.property
    intro he
    apply hij
    apply Subtype.ext
    exact Prod.ext (Option.some.inj (congrArg (fun z => z.1) he)) (congrArg (fun z => z.2) he)
  obtain ⟨hunit,hunitmeet,hrays⟩ :=
    checkedRLNonloopPrivate4 raw hraw hrawmeet
  let d₀ : D := ⟨g₀,hg₀⟩
  let d₁ : D := ⟨g₁,hg₁⟩
  have hdne : d₀≠d₁ := fun he => hne (congrArg Subtype.val he)
  have hunitopp : unit d₁ = -unit d₀ := by
    have hn0 : ‖Plane.mk 1 0‖=(1:ℝ) := by simp [Plane.mk,EuclideanSpace.norm_eq]
    have hn1 : ‖Plane.mk (-1) 0‖=(1:ℝ) := by simp [Plane.mk,EuclideanSpace.norm_eq]
    simp only [unit,raw,d₀,d₁,hv0,hv1,hn0,hn1,inv_one,one_smul]
    ext i;fin_cases i <;> simp [Plane.mk]
  have hgraph : ∀ x,x∈e.source → (x∈⋃ j,(graph j).val.image ↔
      ∃ g : D, ∃ d : ℝ,0≤d ∧ e x=d • unit g) := by
    intro x hx
    constructor
    · intro hxP
      obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
      obtain ⟨terminal,hi,hs⟩ := (htrace (some j) x (hxF x hx) (hxBall x hx)).mp hj
      rw [segment_eq_image] at hs
      obtain ⟨d,hd,hde⟩ := hs
      let g : D := ⟨(j,terminal),hi⟩
      refine ⟨g,?_⟩
      apply (hrays g (e x)).mp
      refine ⟨d,hd.1,?_⟩
      simpa only [heval,smul_zero,zero_add,raw,g] using hde.symm
    · rintro ⟨g,d,hd,he⟩
      obtain ⟨c,hc,hce⟩ := (hrays g (e x)).mpr ⟨d,hd,he⟩
      have hn : ‖e x‖<ε := by simpa only [heval,mem_ball,dist_zero_right] using hxBall x hx
      have hvbound : ε < ‖raw g‖ := hεv (some g.val.1,g.val.2) g.property
      have hc1 : c≤1 := by
        rw [hce,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc] at hn
        have hpos := norm_pos_iff.mpr (hraw g)
        nlinarith
      apply mem_iUnion.mpr
      refine ⟨g.val.1,(htrace (some g.val.1) x (hxF x hx) (hxBall x hx)).mpr ⟨g.val.2,g.property,?_⟩⟩
      rw [segment_eq_image]
      refine ⟨c,⟨hc,hc1⟩,?_⟩
      simpa only [heval,smul_zero,zero_add,raw] using hce.symm
  let Old : Type := {terminal : Bool // (if terminal then a.val.map 1 else a.val.map 0) = p}
  let old : Old → Plane := fun k => v (none,k.val)
  have hold : ∀ k, old k ≠ 0 := fun k => hvn (none,k.val) k.property
  have haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k : Old, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k := by
    intro x hx hxs
    obtain ⟨terminal,hi,hs⟩ := (htrace none x (hxF x hxs) (hxBall x hxs)).mp hx
    rw [segment_eq_image] at hs
    obtain ⟨d,hd,hde⟩ := hs
    exact ⟨⟨terminal,hi⟩,d,hd.1,by simpa only [heval,smul_zero,add_zero,zero_add,old] using hde.symm⟩
  obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => b) p
    e.source e.open_source hpe
  have hsource : ∀ t, b.val.map
      (endpointGermParameter selected r hr (by linarith) t) ∈ e.source := by
    intro t
    cases selected
    · apply hstart PUnit.unit rfl
      change r*t.val ≤ r
      nlinarith [t.property.2]
    · apply hend PUnit.unit rfl
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  obtain ⟨c,H,δ,hδ,hδhalf,hclass,hm,hG,hmap,hout,htail⟩ :=
    actual_marked_arc_selected_terminal_full_graph_chart_supported_clearance_private M a b selected e
    hpe he0 hemarks (⋃ j,(graph j).val.image) unit hunit hunitmeet d₀ d₁ hdne hunitopp hgraph
    hbP old haOld (ε/4) hR hRT r hr hrhalf hsource
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hm,hG,hmap,?_,htail⟩
  intro t x hx
  apply hout t x
  exact fun hxs => hx (hFV (hxF x hxs))
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
private theorem actual_no_incident_graph_selected_terminal_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (selected : Bool)
    (V : Set S) (hV : IsOpen V)
    (hpV : (if selected then b.val.map 1 else b.val.map 0)∈V)
    (terminal : Bool)
    (haIncident : (if terminal then a.val.map 1 else a.val.map 0) = (if selected then b.val.map 1 else b.val.map 0))
    (hno : ∀ j (terminal : Bool),(if terminal then (graph j).val.map 1 else (graph j).val.map 0) ≠ (if selected then b.val.map 1 else b.val.map 0))
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      (∀ t x,x∉V → H.map (t,x)=x) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        (if selected then 1-t.val else t.val) ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let p := (if selected then b.val.map 1 else b.val.map 0)
  let family : Option G → EssentialMarkedArc M := fun i => Option.elim i a graph
  obtain ⟨F,hpF,hFp,hFV,hmarks,r₀,hr₀,hr₀half,v,hvn,hv0,_,_,_,_,ε,hε,hεT,hεv,htrace,_⟩ :=
    actual_marked_endpoint_source_fan_chart M family hfinite p (by cases selected; exact b.val.start_marked; exact b.val.end_marked)
      V hV hpV (none,terminal) haIncident
  let U : Set S := F.source ∩ F ⁻¹' ball (0:Plane) (ε/2)
  have hU : IsOpen U := F.isOpen_inter_preimage isOpen_ball
  have hpU : p ∈ U := ⟨hpF,by simpa [hFp] using half_pos hε⟩
  let e := F.restr U
  have hes : e.source = F.source ∩ U := by
    rw [OpenPartialHomeomorph.restr_source,hU.interior_eq]
  have heval (x : S) : e x = F x := rfl
  have hpe : p ∈ e.source := hes.symm ▸ ⟨hpF,hpU⟩
  have he0 : e p = 0 := hFp
  have hxF (x : S) (hx : x ∈ e.source) : x ∈ F.source := (hes ▸ hx).1
  have hxBall (x : S) (hx : x ∈ e.source) : F x ∈ ball (0:Plane) ε :=
    (ball_subset_ball (by linarith : ε/2 ≤ ε)) ((hes ▸ hx).2.2)
  have hemarks : ∀ x, x ∈ e.source → x ∈ M.cover.branch → x = p := by
    intro x hx hm
    exact Set.mem_singleton_iff.mp (hmarks ▸ (show x ∈ F.source ∩ (M.cover.branch:Set S) from ⟨hxF x hx,hm⟩))
  have hR : 0 < ε/4 := by positivity
  have hRT : closedBall (0:Plane) (ε/4) ⊆ e.target := by
    intro z hz
    have hzNorm : ‖z‖ ≤ ε/4 := by simpa only [mem_closedBall,dist_zero_right] using hz
    have hzε : z ∈ ball (0:Plane) ε := by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε by linarith)
    have hzF : z ∈ F.target := hεT hzε
    have hx : F.symm z ∈ e.source := by
      rw [hes]
      refine ⟨F.map_target hzF,⟨F.map_target hzF,?_⟩⟩
      rw [mem_preimage,F.right_inv hzF]
      simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < ε/2 by linarith)
    have hh := e.map_source hx
    change F (F.symm z) ∈ e.target at hh
    rw [F.right_inv hzF] at hh
    exact hh
  have hgraph : Disjoint e.source (⋃ j,(graph j).val.image) := by
    apply Set.disjoint_left.mpr
    intro x hx hxP
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
    obtain ⟨terminal,hi,_⟩ := (htrace (some j) x (hxF x hx) (hxBall x hx)).mp hj
    exact hno j terminal hi
  let Old : Type := {terminal : Bool // (if terminal then a.val.map 1 else a.val.map 0) = p}
  let old : Old → Plane := fun k => v (none,k.val)
  have hold : ∀ k, old k ≠ 0 := fun k => hvn (none,k.val) k.property
  have haOld : ∀ x, x ∈ a.val.image → x ∈ e.source →
      ∃ k : Old, ∃ d : ℝ, 0 ≤ d ∧ e x = d • old k := by
    intro x hx hxs
    obtain ⟨terminal,hi,hs⟩ := (htrace none x (hxF x hxs) (hxBall x hxs)).mp hx
    rw [segment_eq_image] at hs
    obtain ⟨d,hd,hde⟩ := hs
    exact ⟨⟨terminal,hi⟩,d,hd.1,by simpa only [heval,smul_zero,add_zero,zero_add,old] using hde.symm⟩
  obtain ⟨r,hr,hrhalf,hstart,hend⟩ := uniform_actual_endpoint_germs M PUnit (fun _ => b) p
    e.source e.open_source hpe
  have hsource : ∀ t, b.val.map
      (endpointGermParameter selected r hr (by linarith) t) ∈ e.source := by
    intro t
    cases selected
    · apply hstart PUnit.unit rfl
      change r*t.val ≤ r
      nlinarith [t.property.2]
    · apply hend PUnit.unit rfl
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  obtain ⟨c,H,δ,hδ,hδhalf,hclass,hm,hG,hmap,hout,htail⟩ :=
    actual_marked_arc_selected_terminal_free_graph_chart_supported_clearance_private M a b selected e
    hpe he0 hemarks (⋃ j,(graph j).val.image) hgraph hbP old hold haOld
    (ε/4) hR hRT r hr hrhalf hsource
  refine ⟨c,H,δ,hδ,hδhalf,hclass,hm,hG,hmap,?_,htail⟩
  intro t x hx
  apply hout t x
  exact fun hxs => hx (hFV (hxF x hxs))
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
private theorem actual_arbitrary_graph_selected_terminal_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (selected : Bool)
    (V : Set S) (hV : IsOpen V)
    (hpV : (if selected then b.val.map 1 else b.val.map 0)∈V)
    (terminal : Bool)
    (haIncident : (if terminal then a.val.map 1 else a.val.map 0) = (if selected then b.val.map 1 else b.val.map 0))
    (hbP : ∀ t : Interval, 0 < t.val → t.val < 1 →
      b.val.map t ∉ ⋃ j, (graph j).val.image) :
    ∃ c : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ,
      0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
      (∀ t x, x ∈ ⋃ j, (graph j).val.image → H.map (t,x) = x) ∧
      (∀ t, c.val.map t = H.finalMap (b.val.map t)) ∧
      (∀ t x,x∉V → H.map (t,x)=x) ∧
      ∀ t : Interval, 0 < t.val → t.val < 1 →
        (if selected then 1-t.val else t.val) ≤ δ → c.val.map t ∉ a.val.image := by
  classical
  let incident : G × Bool → Prop := fun g =>
    (if g.2 then (graph g.1).val.map 1 else (graph g.1).val.map 0) = (if selected then b.val.map 1 else b.val.map 0)
  by_cases hsome : ∃ g,incident g
  · obtain ⟨g₀,hg₀⟩ := hsome
    by_cases htwo : ∃ g₁,incident g₁ ∧ g₁≠g₀
    · obtain ⟨g₁,hg₁,hne⟩ := htwo
      exact actual_multiple_incident_graph_selected_terminal_clearance_private M graph a b hfinite
        selected V hV hpV g₀ g₁ hg₀ hg₁ hne.symm hbP
    · have honly : ∀ j terminal,
          ((if terminal then (graph j).val.map 1 else (graph j).val.map 0) = (if selected then b.val.map 1 else b.val.map 0) ↔
            j=g₀.1 ∧ terminal=g₀.2) := by
        intro j terminal
        constructor
        · intro hi
          have he : (j,terminal)=g₀ := by
            by_contra hn
            exact htwo ⟨(j,terminal),hi,hn⟩
          exact ⟨congrArg Prod.fst he,congrArg Prod.snd he⟩
        · rintro ⟨rfl,rfl⟩
          exact hg₀
      exact actual_single_incident_graph_selected_terminal_clearance_private M graph a b hfinite
        selected V hV hpV g₀.1 g₀.2 hg₀ honly hbP
  · exact actual_no_incident_graph_selected_terminal_clearance_private M graph a b hfinite selected V hV hpV
      terminal haIncident (by intro j terminal hi;exact hsome ⟨(j,terminal),hi⟩) hbP
end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
private theorem actual_nonloop_both_terminal_germs_entire_graph_clearance_private
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {G : Type} [Fintype G]
    (graph : G → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (hfinite : ∀ i j : Option G, i ≠ j →
      (ArcSurgery.crossings M (Option.elim i a graph) (Option.elim j a graph)).Finite)
    (hnonloop : b.val.map 0 ≠ b.val.map 1)
    (hends : ({a.val.map 0,a.val.map 1}:Set S)={b.val.map 0,b.val.map 1})
    (hbP : ∀ t : Interval,0<t.val → t.val<1 → b.val.map t∉⋃ j,(graph j).val.image) :
    ∃ c : EssentialMarkedArc M,∃ H : AmbientIsotopy S,∃ δ : ℝ,
      0<δ ∧ δ<1/2 ∧
      Quotient.mk (essentialArcSetoid M) c=Quotient.mk (essentialArcSetoid M) b ∧
      (∀ t x,x∈M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x,x∈⋃ j,(graph j).val.image → H.map (t,x)=x) ∧
      (∀ t,c.val.map t=H.finalMap (b.val.map t)) ∧
      ∀ t : Interval,0<t.val → t.val<1 →
        t.val≤δ ∨ 1-t.val≤δ → c.val.map t∉a.val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have haEnd (selected : Bool) : ∃ terminal : Bool,
      (if terminal then a.val.map 1 else a.val.map 0)=
      (if selected then b.val.map 1 else b.val.map 0) := by
    have hh : (if selected then b.val.map 1 else b.val.map 0)∈({a.val.map 0,a.val.map 1}:Set S) := by
      rw [hends]
      cases selected <;> simp
    rcases Set.mem_insert_iff.mp hh with hh|hh
    · exact ⟨false,hh.symm⟩
    · exact ⟨true,(Set.mem_singleton_iff.mp hh).symm⟩
  obtain ⟨terminal0,ha0⟩ := haEnd false
  obtain ⟨c,H0,δ0,hδ0,hδ0half,hclass0,hm0,hG0,hmap0,_,htail0⟩ :=
    actual_arbitrary_graph_selected_terminal_clearance_private M graph a b hfinite
      false univ isOpen_univ (mem_univ _) terminal0 ha0 hbP
  have hc0 : c.val.map 0=b.val.map 0 := by
    rw [hmap0]
    exact hm0 1 _ b.val.start_marked
  have hc1 : c.val.map 1=b.val.map 1 := by
    rw [hmap0]
    exact hm0 1 _ b.val.end_marked
  have hcne : c.val.map 0≠c.val.map 1 := by rw [hc0,hc1];exact hnonloop
  have hcinj : Function.Injective c.val.map := by
    intro t u he
    rcases c.val.injective_except_loop_closure t u he with hh|hh|hh
    · exact hh
    · rcases hh with ⟨rfl,rfl⟩
      exact False.elim (hcne he)
    · rcases hh with ⟨rfl,rfl⟩
      exact False.elim (hcne he.symm)
  let clock : Interval := ⟨δ0,⟨hδ0.le,by linarith⟩⟩
  let V : Set S := (c.val.map '' Icc (0:Interval) clock)ᶜ
  have hV : IsOpen V := ((isCompact_Icc.image c.val.continuous).isClosed).isOpen_compl
  have hc1V : c.val.map 1∈V := by
    rintro ⟨t,ht,he⟩
    have ht1 : t=1 := hcinj he
    have hh : t.val≤δ0 := ht.2
    rw [ht1] at hh
    change (1:ℝ)≤δ0 at hh
    linarith
  have hcP : ∀ t : Interval,0<t.val → t.val<1 → c.val.map t∉⋃ j,(graph j).val.image := by
    intro t ht0 ht1 hx
    obtain ⟨e,he⟩ := H0.homeomorphism_at (1:Interval)
    have hpoint : b.val.map t=c.val.map t := e.injective (by
      rw [he,he]
      exact (hmap0 t).symm.trans (hG0 1 _ hx).symm)
    exact hbP t ht0 ht1 (hpoint ▸ hx)
  obtain ⟨terminal1,ha1⟩ := haEnd true
  have ha1c : (if terminal1 then a.val.map 1 else a.val.map 0)=c.val.map 1 := ha1.trans hc1.symm
  obtain ⟨d,H1,δ1,hδ1,hδ1half,hclass1,hm1,hG1,hmap1,hout1,htail1⟩ :=
    actual_arbitrary_graph_selected_terminal_clearance_private M graph a c hfinite
      true V hV hc1V terminal1 ha1c hcP
  let δ := min δ0 δ1
  have hδ : 0<δ := lt_min hδ0 hδ1
  have hδhalf : δ<1/2 := (min_le_left δ0 δ1).trans_lt hδ0half
  refine ⟨d,H0.compose H1,δ,hδ,hδhalf,hclass1.trans hclass0,?_,?_,?_,?_⟩
  · intro t x hx
    change H1.map (t,H0.map (t,x))=x
    rw [hm0 t x hx,hm1 t x hx]
  · intro t x hx
    change H1.map (t,H0.map (t,x))=x
    rw [hG0 t x hx,hG1 t x hx]
  · intro t
    rw [AmbientIsotopy.compose_finalMap]
    exact (hmap1 t).trans (congrArg H1.finalMap (hmap0 t))
  · intro t ht0 ht1 ht
    rcases ht with ht|ht
    · have htδ0 : t.val≤δ0 := ht.trans (min_le_left δ0 δ1)
      have htclock : t∈Icc (0:Interval) clock := ⟨t.property.1,htδ0⟩
      have hcOutside : c.val.map t∉V := by
        exact fun hv => hv (mem_image_of_mem c.val.map htclock)
      have hdeq : d.val.map t=c.val.map t := (hmap1 t).trans (hout1 1 _ hcOutside)
      rw [hdeq]
      exact htail0 t ht0 ht1 htδ0
    · exact htail1 t ht0 ht1 (ht.trans (min_le_right δ0 δ1))
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actual_arbitrary_graph_selected_terminal_clearance_private
#print axioms CurveComplex.HyperellipticModel.actual_nonloop_both_terminal_germs_entire_graph_clearance_private

namespace CurveComplex.HyperellipticModel
private theorem actual_original_aligned_disjoint_families_nonloop_relative_finite_preparation_private
    {E S I : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) (r s : I → EssentialMarkedArc M)
    (hd : ∀ i j,i≠j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hsd : ∀ i j,i≠j → Disjoint (arcInterior M (s i)) (arcInterior M (s j)))
    (J : Finset I) (u : I) (hu : u∉J)
    (haligned : ∀ j∈J,(s j).val.image=(r j).val.image)
    (hnonloop : (s u).val.map 0≠(s u).val.map 1)
    (hends : ({(r u).val.map 0,(r u).val.map 1}:Set S)={(s u).val.map 0,(s u).val.map 1}) :
    ∃ d : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      Quotient.mk (essentialArcSetoid M) d=Quotient.mk (essentialArcSetoid M) (s u) ∧
      H.finalMap '' (s u).val.image=d.val.image ∧
      (∀ t x,x∈M.cover.branch → H.map (t,x)=x) ∧
      (∀ t x,x∈⋃ j : {j//j∈J},(r j.val).val.image → H.map (t,x)=x) ∧
      (ArcSurgery.crossings M (r u) d).Finite ∧
      ∀ q∈ArcSurgery.crossings M (r u) d,ArcSurgery.CrossesInDisk M (r u) d q := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let G := {j//j∈J}
  let P : Set S := ⋃ j : G,(r j.val).val.image
  have hP : IsClosed P := isClosed_iUnion_of_finite (fun j => (isCompact_range (r j.val).val.continuous).isClosed)
  have hbP : arcInterior M (s u)⊆Pᶜ := by
    intro x hx hxP
    obtain ⟨j,hj⟩ := mem_iUnion.mp hxP
    have hs : x∈arcInterior M (s j.val) := ⟨(haligned j.val j.property).symm ▸ hj,hx.2⟩
    exact Set.disjoint_left.mp (hsd u j.val (fun he => hu (he.symm ▸ j.property))) hx hs
  have hbClock : ∀ t : Interval,0<t.val → t.val<1 → (s u).val.map t∉P := by
    intro t ht0 ht1
    apply hbP
    refine ⟨mem_range_self t,?_⟩
    intro hm
    rcases (s u).val.marked_only_at_ends t hm with he|he
    · have hh := congrArg Subtype.val he
      change t.val=0 at hh
      linarith
    · have hh := congrArg Subtype.val he
      change t.val=1 at hh
      linarith
  let f : Option G → I := fun i => Option.elim i u (fun j => j.val)
  have hf : Function.Injective f := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        exfalso
        have he' : u=j.val := he
        exact hu (he'.symm ▸ j.property)
    | some i =>
      cases j with
      | none =>
        exfalso
        have he' : i.val=u := he
        exact hu (he' ▸ i.property)
      | some j => exact congrArg some (Subtype.ext he)
  have hfinite : ∀ i j : Option G,i≠j →
      (ArcSurgery.crossings M (Option.elim i (r u) (fun j : G => r j.val))
        (Option.elim j (r u) (fun j : G => r j.val))).Finite := by
    intro i j hij
    have hfamily (i : Option G) : Option.elim i (r u) (fun j : G => r j.val)=r (f i) := by cases i <;> rfl
    have hz : ArcSurgery.crossings M (r (f i)) (r (f j))=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact Set.disjoint_left.mp (hd (f i) (f j) (fun he => hij (hf he))) hx.1 hx.2
    rw [hfamily i,hfamily j,hz]
    exact Set.finite_empty
  obtain ⟨c,H,δ,hδ,hδhalf,hclass,hmarks,hgraph,hmap,htails⟩ :=
    actual_nonloop_both_terminal_germs_entire_graph_clearance_private M (fun j : G => r j.val)
      (r u) (s u) hfinite hnonloop hends hbClock
  exact checkedRLNonloopPrivate6 M (r u) (s u) c P
    hP hbP H δ hδ hδhalf hclass hmarks hgraph hmap htails
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actual_original_aligned_disjoint_families_nonloop_relative_finite_preparation_private
