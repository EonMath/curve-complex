import RegionalDecreaseSupport
import CurveComplexGenusTwo.Topology.ActualHarerNoncornerTangency.ActualHarerNoncornerTangency
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryContactFacts
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition

open CurveComplex Set Topology RegionalTotalDecrease Schoenflies
open CoherentEndpointMotion.FreeBoundaryNullGeometry
universe v
private noncomputable local instance regionalHalfDiskContactCleanupDecidable (P : Prop) : Decidable P := Classical.propDecidable P

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem regional_empty_three_side_half_disk_whole_contact_cleanup
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ a b : IntrinsicEssentialArc,
      (a.val.val 0 ≠ b.val.val 0 ∧ a.val.val 0 ≠ b.val.val 1 ∧
        a.val.val 1 ≠ b.val.val 0 ∧ a.val.val 1 ≠ b.val.val 1) →
      (range a.val.val ∩ range b.val.val).Finite →
      RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F a.val.val b.val.val →
      ∀ (N : NullHalfBigonBoundary {y | y.val ∈ boundaryCircle} a.val.val b.val.val)
        (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F)),
        IsEmbedding d →
        d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          range N.first ∪ range N.second ∪ range N.boundarySide →
        Disjoint (d '' {z | z.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
          (range a.val.val ∪ range b.val.val) →
        range d ∩ (range a.val.val ∩ range b.val.val) = {N.first 1} := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  dsimp only
  intro a b hends hfinite hcross N d hd hboundary hempty
  let B : Set ↥F := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
    Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
  have hBfront : B ⊆ {y : ↥F | y.val ∈ frontier F} := by
    intro y hy
    rw [hfrontier]
    exact Or.inl hy
  have hcontact (s t : Interval) (hst : a.val.val s = b.val.val t) :
      s ∈ Ioo (0 : Interval) 1 ∧ t ∈ Ioo (0 : Interval) 1 ∧ a.val.val s ∉ B := by
    have hp : ∀ u ∈ Ioo (0 : Interval) 1, a.val.val u ∉ B ∧ b.val.val u ∉ B :=
      fun u hu => ⟨fun h => a.val.property.2.2.2 u hu (hBfront h),
        fun h => b.val.property.2.2.2 u hu (hBfront h)⟩
    have hdis : Disjoint ({a.val.val 0,a.val.val 1} : Set ↥F)
        {b.val.val 0,b.val.val 1} := by
      simp only [Set.disjoint_insert_left, Set.disjoint_singleton_left,
        Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨⟨hends.1,hends.2.1⟩,hends.2.2⟩
    exact CoherentEndpointMotion.FreeBoundaryContactRepair.free_boundary_contact_parameters_interior
      B a.val.val b.val.val ⟨a.val.property.2.1,a.val.property.2.2.1,
        b.val.property.2.1,b.val.property.2.2.1⟩ hp hdis s t hst
  let aS : C(Interval,S) := ⟨fun t => (a.val.val t).val,continuous_subtype_val.comp a.val.val.continuous⟩
  let bS : C(Interval,S) := ⟨fun t => (b.val.val t).val,continuous_subtype_val.comp b.val.val.continuous⟩
  let fS : C(Interval,S) := ⟨fun t => (N.first t).val,continuous_subtype_val.comp N.first.continuous⟩
  let kS : C(Interval,S) := ⟨fun t => (N.second t).val,continuous_subtype_val.comp N.second.continuous⟩
  let rS : C(Interval,S) := ⟨fun t => (N.boundarySide t).val,continuous_subtype_val.comp N.boundarySide.continuous⟩
  let dS : C(Metric.closedBall (0 : Plane) 1,S) :=
    ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
  have haS : IsEmbedding aS := IsEmbedding.subtypeVal.comp a.val.property.1
  have hbS : IsEmbedding bS := IsEmbedding.subtypeVal.comp b.val.property.1
  have hfS : IsEmbedding fS := IsEmbedding.subtypeVal.comp N.first_embedded
  have hkS : IsEmbedding kS := IsEmbedding.subtypeVal.comp N.second_embedded
  have hdS : IsEmbedding dS := IsEmbedding.subtypeVal.comp hd
  have hfa : range fS ⊆ range aS := by
    rintro y ⟨u,rfl⟩
    obtain ⟨t,ht⟩ := N.first_on_a (mem_range_self u)
    exact ⟨t,congrArg Subtype.val ht⟩
  have hkb : range kS ⊆ range bS := by
    rintro y ⟨u,rfl⟩
    obtain ⟨t,ht⟩ := N.second_on_b (mem_range_self u)
    exact ⟨t,congrArg Subtype.val ht⟩
  have hboundaryS : dS '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range fS ∪ range kS ∪ range rS := by
    have hv := congrArg (Set.image (fun y : ↥F => y.val)) hboundary
    simpa [dS,fS,kS,rS,Set.image_image,←Set.range_comp'] using hv
  have hemptyS : Disjoint (interior (range dS)) (range aS ∪ range bS) := by
    rw [CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq dS hdS]
    apply Set.disjoint_left.mpr
    rintro y ⟨z,hz,rfl⟩ (⟨t,ht⟩ | ⟨t,ht⟩)
    · exact Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inl ⟨t,Subtype.ext ht⟩)
    · exact Set.disjoint_left.mp hempty ⟨z,hz,rfl⟩ (Or.inr ⟨t,Subtype.ext ht⟩)
  let rb : Path (fS 0) (kS 0) := {
    toFun := rS
    continuous_toFun := rS.continuous
    source' := congrArg Subtype.val N.boundary_zero
    target' := congrArg Subtype.val N.boundary_one }
  let fk : Path (kS 0) (fS 1) := {
    toFun := kS
    continuous_toFun := kS.continuous
    source' := rfl
    target' := congrArg Subtype.val N.corner_eq.symm }
  let ff : Path (fS 0) (kS 1) := {
    toFun := fS
    continuous_toFun := fS.continuous
    source' := rfl
    target' := congrArg Subtype.val N.corner_eq }
  let gf : C(Interval,S) := (rb.trans fk).toContinuousMap
  let gk : C(Interval,S) := (rb.symm.trans ff).toContinuousMap
  have hgf : range gf = range rS ∪ range kS := by
    exact Path.trans_range rb fk
  have hgk : range gk = range rS ∪ range fS := by
    change range (rb.symm.trans ff) = _
    rw [Path.trans_range,Path.symm_range]
    rfl
  have hboundaryF : dS '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range fS ∪ range gf := by
    rw [hboundaryS,hgf]
    ext y
    simp only [mem_union]
    clear * - y
    tauto
  have hboundaryK : dS '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      range kS ∪ range gk := by
    rw [hboundaryS,hgk]
    ext y
    simp only [mem_union]
    clear * - y
    tauto
  have hAxis := by
    run_tac
      let e ← Lean.getEnv
      let some (n, _) := e.constants.toList.find? (fun z => z.1.toString == "_private.CurveComplexGenusTwo.Topology.ActualHarerNoncornerTangency.ActualHarerNoncornerTangency.0.ActualHarerWholeAnchorRail.actual_disjoint_whole_moving_family_constructs_local_exact_axis_chart") | throwError "Frozen provider declaration missing"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact @$(Lean.mkIdent n)))
  have hBank := by
    run_tac
      let e ← Lean.getEnv
      let some (n, _) := e.constants.toList.find? (fun z => z.1.toString == "_private.CurveComplexGenusTwo.Topology.ActualHarerNoncornerTangency.ActualHarerNoncornerTangency.0.ActualHarerSupportedBypass.actual_noncorner_disk_side_constructs_whole_arc_axis_interior_bank_chart") | throwError "Frozen provider declaration missing"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact @$(Lean.mkIdent n)))
  have hWindows := by
    run_tac
      let e ← Lean.getEnv
      let some (n, _) := e.constants.toList.find? (fun z => z.1.toString == "_private.CurveComplexGenusTwo.Topology.ActualHarerNoncornerTangency.ActualHarerNoncornerTangency.0.ActualHarerContactSides.actual_isolated_whole_trace_contact_constructs_two_signed_branch_windows") | throwError "Frozen provider declaration missing"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact @$(Lean.mkIdent n)))
  have hSame := by
    run_tac
      let e ← Lean.getEnv
      let some (n, _) := e.constants.toList.find? (fun z => z.1.toString == "_private.CurveComplexGenusTwo.Topology.ActualHarerNoncornerTangency.ActualHarerNoncornerTangency.0.ActualHarerSupportedBypass.actual_empty_bank_constructs_moving_axis_same_side_window") | throwError "Frozen provider declaration missing"
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact @$(Lean.mkIdent n)))
  have hcompare (L : Set S) (p : S)
      (hp : p ∈ L) (C D : OpenPartialHomeomorph S (ℝ × ℝ))
      (hpC : p ∈ C.source) (hpD : p ∈ D.source)
      (hC : ∀ x ∈ C.source, x ∈ L ↔ (C x).1 = 0)
      (hD : ∀ x ∈ D.source, x ∈ L ↔ (D x).1 = 0) :
      ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ C.source ∩ D.source ∧
        ∀ x ∈ U, ∀ y ∈ U, x ∉ L → y ∉ L →
          (((C x).1 < 0 ↔ (C y).1 < 0) ↔
            ((D x).1 < 0 ↔ (D y).1 < 0)) := by
    classical
    clear * - L p hp C D hpC hpD hC hD
    have hCp : (C p).1 = 0 := (hC p hpC).mp hp
    have hDp : (D p).1 = 0 := (hD p hpD).mp hp
    let P := C.trans (Homeomorph.addRight (-C p)).toOpenPartialHomeomorph
    let Q := D.trans (Homeomorph.addRight (-D p)).toOpenPartialHomeomorph
    have hPs : P.source = C.source := by
      ext x
      simp only [P,OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
    have hQs : Q.source = D.source := by
      ext x
      simp only [Q,OpenPartialHomeomorph.trans_source,
        Homeomorph.toOpenPartialHomeomorph_source,preimage_univ,inter_univ]
    have hPf (x : S) : (P x).1 = (C x).1 := by
      change (C x).1 + -(C p).1 = (C x).1
      rw [hCp]
      simp
    have hQf (x : S) : (Q x).1 = (D x).1 := by
      change (D x).1 + -(D p).1 = (D x).1
      rw [hDp]
      simp
    have hPp : P p = (0,0) := by
      change C p + -C p = (0,0)
      exact add_neg_cancel _
    have hQp : Q p = (0,0) := by
      change D p + -D p = (0,0)
      exact add_neg_cancel _
    have hpP : p ∈ P.source := hPs.symm ▸ hpC
    have hpQ : p ∈ Q.source := hQs.symm ▸ hpD
    let T0 := P.symm.trans Q
    have hTs : (0,0) ∈ T0.source := by
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨hPp ▸ P.map_source hpP,?_⟩
      change P.symm (0,0) ∈ Q.source
      rw [←hPp,P.left_inv hpP]
      exact hpQ
    have hT0 : T0 (0,0) = (0,0) := by
      change Q (P.symm (0,0)) = (0,0)
      rw [←hPp,P.left_inv hpP]
      exact hQp.trans hPp.symm
    have hTa (z : ℝ × ℝ) (hz : z ∈ T0.source) : z.1 = 0 ↔ (T0 z).1 = 0 := by
      rw [OpenPartialHomeomorph.trans_source] at hz
      have hPinv := P.right_inv hz.1
      have hPaxis : P.symm z ∈ L ↔ z.1 = 0 := by
        have hh := hC (P.symm z) (hPs ▸ P.symm.map_source hz.1)
        rw [←hPf (P.symm z),hPinv] at hh
        exact hh
      have hQaxis : P.symm z ∈ L ↔ (Q (P.symm z)).1 = 0 := by
        rw [hQf]
        exact hD (P.symm z) (hQs ▸ hz.2)
      exact hPaxis.symm.trans hQaxis
    obtain ⟨r,hr,hball,ε,hrelative⟩ :=
      CurveComplex.LocalSurgery.local_axis_transition_side_constant T0 hTs hT0 hTa
    let U := Q.source ∩ (P.source ∩ P ⁻¹' Metric.ball (0,0) r)
    have hUopen : IsOpen U := Q.open_source.inter
      (P.isOpen_inter_preimage Metric.isOpen_ball)
    have hpU : p ∈ U := ⟨hpQ,hpP,by
      change P p ∈ Metric.ball (0,0) r
      rw [hPp]
      exact Metric.mem_ball_self hr⟩
    have hsub : U ⊆ C.source ∩ D.source := fun _ hx => ⟨hPs ▸ hx.2.1,hQs ▸ hx.1⟩
    have hlabel (x : S) (hx : x ∈ U) (hxb : x ∉ L) :
        (if 0 < (D x).1 then (1 : ZMod 2) else 0) =
          (if 0 < (C x).1 then (1 : ZMod 2) else 0) + ε := by
      have hn : (P x).1 ≠ 0 := by
        rw [hPf]
        exact fun hh => hxb ((hC x (hPs ▸ hx.2.1)).mpr hh)
      have hh := hrelative (P x) hx.2.2 hn
      have htrans : T0 (P x) = Q x := by
        change Q (P.symm (P x)) = Q x
        rw [P.left_inv hx.2.1]
      simpa only [htrans,hPf,hQf] using hh
    refine ⟨U,hUopen,hpU,hsub,?_⟩
    intro x hx y hy hxb hyb
    have hxnC : (C x).1 ≠ 0 := fun hh => hxb ((hC x (hsub hx).1).mpr hh)
    have hynC : (C y).1 ≠ 0 := fun hh => hyb ((hC y (hsub hy).1).mpr hh)
    have hxnD : (D x).1 ≠ 0 := fun hh => hxb ((hD x (hsub hx).2).mpr hh)
    have hynD : (D y).1 ≠ 0 := fun hh => hyb ((hD y (hsub hy).2).mpr hh)
    have hlabels :
        ((if 0 < (D x).1 then (1 : ZMod 2) else 0) =
          (if 0 < (D y).1 then (1 : ZMod 2) else 0)) ↔
        ((if 0 < (C x).1 then (1 : ZMod 2) else 0) =
          (if 0 < (C y).1 then (1 : ZMod 2) else 0)) := by
      rw [hlabel x hx hxb,hlabel y hy hyb]
      exact add_right_cancel_iff
    by_cases hcx : 0 < (C x).1 <;> by_cases hcy : 0 < (C y).1 <;>
      by_cases hdx : 0 < (D x).1 <;> by_cases hdy : 0 < (D y).1
    all_goals simp only [hcx,hcy,hdx,hdy,ite_true,ite_false] at hlabels
    all_goals have hcnegx : (C x).1 < 0 ↔ ¬0 < (C x).1 :=
      ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnC⟩
    all_goals have hcnegy : (C y).1 < 0 ↔ ¬0 < (C y).1 :=
      ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynC⟩
    all_goals have hdnegx : (D x).1 < 0 ↔ ¬0 < (D x).1 :=
      ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hxnD⟩
    all_goals have hdnegy : (D y).1 < 0 ↔ ¬0 < (D y).1 :=
      ⟨fun hh => not_lt_of_ge hh.le, fun hh => lt_of_le_of_ne (le_of_not_gt hh) hynD⟩
    all_goals rw [hcnegx,hcnegy,hdnegx,hdnegy]
    all_goals simp_all
  have hfiniteS : (range aS ∩ range bS).Finite := by
    apply (hfinite.image (fun y : ↥F => y.val)).subset
    rintro y ⟨⟨s,hs⟩,⟨t,ht⟩⟩
    exact ⟨a.val.val s,⟨mem_range_self s,⟨t,Subtype.ext (ht.trans hs.symm)⟩⟩,hs⟩
  apply Set.Subset.antisymm
  · intro p hp
    by_contra hpCorner
    obtain ⟨t,htx⟩ := hp.2.1
    obtain ⟨s,hsx⟩ := hp.2.2
    have hts := hcontact t s (htx.trans hsx.symm)
    have hti := hts.1
    have hsi := hts.2.1
    have hpB : p ∉ B := htx ▸ hts.2.2
    have hpFront : p.val ∉ frontier F := htx ▸ a.val.property.2.2.2 t hti
    have hpF : p.val ∈ interior F := by
      by_contra hn
      exact hpFront ⟨subset_closure p.property,hn⟩
    have htxS : aS t = p.val := congrArg Subtype.val htx
    have hsxS : bS s = p.val := congrArg Subtype.val hsx
    let U₀ : Set S := interior F ∩ ((range aS ∩ range bS) \ {p.val})ᶜ
    have hU₀ : IsOpen U₀ := isOpen_interior.inter
      ((hfiniteS.diff (t := {p.val})).isClosed.isOpen_compl)
    have hpU₀ : p.val ∈ U₀ := ⟨hpF,by simp⟩
    obtain ⟨Q,hpQa,hQU₀,hQp,_,hQaxis,_⟩ := hAxis
      (fun _ : Unit => aS) (fun _ => haS)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim) () t hti U₀ hU₀
      (htxS.symm ▸ hpU₀)
    have hpQ : p.val ∈ Q.source := htxS ▸ hpQa
    have hQF : Q.source ⊆ interior F := fun y hy => (hQU₀ hy).1
    have hpairQ : Q.source ∩ (range bS ∩ range aS) = {bS s} := by
      ext y
      constructor
      · rintro ⟨hyQ,hyb,hya⟩
        have hyp : y = p.val := by
          by_contra hne
          exact (hQU₀ hyQ).2 ⟨⟨hya,hyb⟩,hne⟩
        exact hyp.trans hsxS.symm
      · rintro rfl
        exact ⟨hsxS.symm ▸ hpQ,mem_range_self s,⟨t,htxS.trans hsxS.symm⟩⟩
    have hboundaryP : p ∈ range N.first ∪ range N.second ∪ range N.boundarySide := by
      obtain ⟨z,hz⟩ := hp.1
      have hznot : z.val ∉ Metric.ball (0 : Plane) 1 := by
        intro hzi
        exact Set.disjoint_left.mp hempty ⟨z,hzi,hz⟩ (Or.inl hp.2.1)
      have hzs : z.val ∈ Metric.sphere (0 : Plane) 1 :=
        le_antisymm z.property (not_lt.mp hznot)
      exact hboundary ▸ (show p ∈ d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1}
        from ⟨z,hzs,hz⟩)
    have hnotOther (side other : C(Interval,↥F))
        (hside : p ∈ range side)
        (hinter : range side ∩ range other = {N.first 1}) :
        p.val ∉ range (fun u : Interval => (other u).val) ∪ range rS := by
      rintro (⟨u,hu⟩ | ⟨u,hu⟩)
      · have hh : p ∈ range side ∩ range other := ⟨hside,⟨u,Subtype.ext hu⟩⟩
        exact hpCorner (hinter ▸ hh)
      · have he : N.boundarySide u = p := Subtype.ext hu
        exact hpB (he ▸ N.boundary_in_B u)
    have hwindows : ∃ (Q : OpenPartialHomeomorph S Plane) (ε : ℝ) (l h : Interval),
        p.val ∈ Q.source ∧ Q p.val 1 = 0 ∧ Q.source ⊆ interior F ∧
        (∀ y : ↥F, y.val ∈ Q.source → (y ∈ range a.val.val ↔ Q y.val 1 = 0)) ∧
        l < s ∧ s < h ∧ (ε = (-1 : ℝ) ∨ ε = 1) ∧
        (∀ w ∈ Icc l h, (b.val.val w).val ∈ Q.source) ∧
        (∀ w ∈ Ioo l h, w ≠ s → ε * Q ((b.val.val w).val) 1 < 0) := by
      rcases hboundaryP with (hpf | hpk) | hpr
      · obtain ⟨w,hw⟩ := hpf
        have hw0 : w ≠ 0 := by
          intro he
          exact hpB (hw ▸ he ▸ N.first_zero_boundary)
        have hw1 : w ≠ 1 := by
          intro he
          exact hpCorner (hw.symm.trans (congrArg N.first he))
        have hwi : w ∈ Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
        have hpfOther := hnotOther N.first N.second ⟨w,hw⟩ N.sides_inter
        have hwgf : fS w ∉ range gf := by
          rw [hgf]
          intro hh
          apply hpfOther
          rw [←congrArg Subtype.val hw]
          exact hh.elim Or.inr Or.inl
        obtain ⟨P,hpP,hP0,hPQ,hPaxis,hBankP⟩ := hBank aS fS gf haS hfS hfa
          dS hdS hboundaryF w hwi hwgf Q
          (by change (N.first w).val ∈ Q.source; rw [hw]; exact hpQ) hQaxis
        have hsP : bS s ∈ P.source := hsxS.symm ▸ (congrArg Subtype.val hw ▸ hpP)
        have hpairP : P.source ∩ (range bS ∩ range aS) = {bS s} := by
          apply subset_antisymm
          · intro y hy
            exact hpairQ ▸ ⟨hPQ hy.1,hy.2⟩
          · rintro y rfl
            exact ⟨hsP,mem_range_self s,⟨t,htxS.trans hsxS.symm⟩⟩
        obtain ⟨l,h,hls,hsh,hwin,_,_⟩ := hWindows bS aS hbS P hPaxis s hsi hsP hpairP
        have hneg : ∀ u ∈ Ioo l h, u ≠ s → P (bS u) 1 < 0 := by
          intro u hu hus
          have huP := hwin u ⟨hu.1.le,hu.2.le⟩
          have hne : P (bS u) 1 ≠ 0 := by
            intro he
            have hua := (hPaxis _ huP).mpr he
            have heq : bS u = bS s := Set.mem_singleton_iff.mp
              (hpairP ▸ (show bS u ∈ P.source ∩ (range bS ∩ range aS)
                from ⟨huP,mem_range_self u,hua⟩))
            exact hus (hbS.injective heq)
          have hle : P (bS u) 1 ≤ 0 := by
            by_contra hn
            have hin := (hBankP _ huP).mpr (lt_of_not_ge hn)
            exact Set.disjoint_left.mp hemptyS hin (Or.inr (mem_range_self u))
          exact lt_of_le_of_ne hle hne
        refine ⟨P,1,l,h,congrArg Subtype.val hw ▸ hpP,?_,hPQ.trans hQF,?_,
          hls,hsh,Or.inr rfl,hwin,?_⟩
        · rw [←congrArg Subtype.val hw]
          change P (fS w) 1 = 0
          rw [hP0]
          rfl
        · intro y hy
          have hh := hPaxis y.val hy
          constructor
          · rintro ⟨u,hu⟩
            exact hh.mp ⟨u,congrArg Subtype.val hu⟩
          · intro hz
            obtain ⟨u,hu⟩ := hh.mpr hz
            exact ⟨u,Subtype.ext hu⟩
        · intro u hu hus
          rw [one_mul]
          change P (bS u) 1 < 0
          exact hneg u hu hus
      · obtain ⟨w,hw⟩ := hpk
        have hw0 : w ≠ 0 := by
          intro he
          exact hpB (hw ▸ he ▸ N.second_zero_boundary)
        have hw1 : w ≠ 1 := by
          intro he
          exact hpCorner ((hw.symm.trans (congrArg N.second he)).trans N.corner_eq.symm)
        have hwi : w ∈ Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne w.property.1 (Ne.symm hw0),lt_of_le_of_ne w.property.2 hw1⟩
        have hsides : range N.second ∩ range N.first = {N.first 1} :=
          (inter_comm _ _).trans N.sides_inter
        have hpkOther := hnotOther N.second N.first ⟨w,hw⟩ hsides
        have hwgk : kS w ∉ range gk := by
          rw [hgk]
          intro hh
          apply hpkOther
          rw [←congrArg Subtype.val hw]
          exact hh.elim Or.inr Or.inl
        obtain ⟨R,hpsR,hRQ,_,_,hRaxis,_⟩ := hAxis
          (fun _ : Unit => bS) (fun _ => hbS)
          (fun i j hij => (hij (Subsingleton.elim i j)).elim) () s hsi
          Q.source Q.open_source (hsxS.symm ▸ hpQ)
        obtain ⟨P,hpP,hP0,hPR,hPaxis,hBankP⟩ := hBank bS kS gk hbS hkS hkb
          dS hdS hboundaryK w hwi hwgk R
          (by change (N.second w).val ∈ R.source; rw [hw,←hsxS]; exact hpsR) hRaxis
        have hpP' : p.val ∈ P.source := congrArg Subtype.val hw ▸ hpP
        have hp0 : P p.val = 0 := by rw [←congrArg Subtype.val hw]; exact hP0
        obtain ⟨l,h,ε,hls,hsh,hε,hwin,hsign⟩ := hSame bS aS hbS s hsi dS
          (hemptyS.mono_right (fun _ hy => Or.inl hy)) Q P
          (hsxS.symm ▸ hpP') (by rw [hsxS]; exact hp0)
          (hPR.trans hRQ) hPaxis hBankP hQaxis hpairQ
        refine ⟨Q,ε,l,h,hpQ,(hQaxis _ hpQ).mp ⟨t,htxS⟩,hQF,?_,hls,hsh,hε,hwin,hsign⟩
        intro y hy
        have hh := hQaxis y.val hy
        constructor
        · rintro ⟨u,hu⟩
          exact hh.mp ⟨u,congrArg Subtype.val hu⟩
        · intro hz
          obtain ⟨u,hu⟩ := hh.mpr hz
          exact ⟨u,Subtype.ext hu⟩
      · obtain ⟨u,hu⟩ := hpr
        exact (hpB (hu ▸ N.boundary_in_B u)).elim
    obtain ⟨Q,ε,l,h,hpQ,hQzero,hQF,hQaxis,hls,hsh,hε,hwindow,hsign⟩ := hwindows
    obtain ⟨C,hCcross⟩ := hcross t s hti hsi (Subtype.ext (htxS.trans hsxS.symm))
    have hat : a.val.val t ∈ {y : ↥F | y.val ∈ C.chart.source ∧
        C.chart y.val ∈ Schoenflies.Plane.closedSquare 0 1} ∩ range a.val.val :=
      C.whole_a_trace.symm ▸ Set.mem_image_of_mem a.val.val
        ⟨C.a_cuts.2.1.le,C.a_cuts.2.2.1.le⟩
    have hpC : p.val ∈ C.chart.source := htxS ▸ hat.1.1
    have hCp : C.chart p.val = 0 := htxS ▸ C.contact_at_origin
    let O : Set S := {y | y ∈ C.chart.source ∧
      C.chart y ∈ Schoenflies.Plane.openSquare 0 1}
    have hO : IsOpen O := C.chart.isOpen_inter_preimage (Schoenflies.Plane.isOpen_openSquare 0 1)
    let K := C.chart.restr O
    have hKs : K.source = C.chart.source ∩ O := by
      simp only [K,OpenPartialHomeomorph.restr_source,hO.interior_eq]
    have hpK : p.val ∈ K.source := by
      rw [hKs]
      refine ⟨hpC,hpC,?_⟩
      rw [hCp,Schoenflies.mem_openSquare_zero_one]
      norm_num [Schoenflies.Plane.supNorm]
    let A : Set S := range (fun u : Interval => (a.val.val u).val)
    have hCwhole (y : ↥F) (hy : y.val ∈ C.chart.source)
        (hyQ : C.chart y.val ∈ Schoenflies.Plane.closedSquare 0 1) :
        y ∈ range a.val.val ↔ C.chart y.val 1 = 0 := by
      constructor
      · intro hya
        have hytrace : y ∈ a.val.val '' Icc C.aLeft C.aRight :=
          C.whole_a_trace ▸ (show y ∈ _ ∩ range a.val.val from ⟨⟨hy,hyQ⟩,hya⟩)
        obtain ⟨u,hu,rfl⟩ := hytrace
        have hdiam : C.chart (a.val.val u).val ∈
            {z : Schoenflies.Plane | z ∈ Schoenflies.Plane.closedSquare 0 1 ∧ z 1 = 0} :=
          C.anchor_diameter ▸ Set.mem_image_of_mem (fun v => C.chart (a.val.val v).val) hu
        exact hdiam.2
      · intro hzero
        have hdiam : C.chart y.val ∈
            (fun u : Interval => C.chart (a.val.val u).val) '' Icc C.aLeft C.aRight :=
          C.anchor_diameter.symm ▸ ⟨hyQ,hzero⟩
        obtain ⟨u,hu,heq⟩ := hdiam
        have hau : a.val.val u ∈ {y : ↥F | y.val ∈ C.chart.source ∧
            C.chart y.val ∈ Schoenflies.Plane.closedSquare 0 1} ∩ range a.val.val :=
          C.whole_a_trace.symm ▸ Set.mem_image_of_mem a.val.val hu
        exact ⟨u,Subtype.ext (C.chart.injOn hau.1.1 hy heq)⟩
    have hKaxis : ∀ y ∈ K.source, y ∈ A ↔ K y 1 = 0 := by
      intro y hy
      have hyO : y ∈ O := (hKs ▸ hy).2
      have hyF : y ∈ F := interior_subset (C.closed_support_interior
        ⟨hyO.1,Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hyO.2⟩)
      let yF : ↥F := ⟨y,hyF⟩
      have hh := hCwhole yF hyO.1
        (Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hyO.2)
      change (y ∈ A ↔ C.chart y 1 = 0)
      constructor
      · rintro ⟨u,hu⟩
        exact hh.mp ⟨u,Subtype.ext hu⟩
      · intro hh0
        obtain ⟨u,hu⟩ := hh.mpr hh0
        exact ⟨u,congrArg Subtype.val hu⟩
    have hQA : ∀ y ∈ Q.source, y ∈ A ↔ Q y 1 = 0 := by
      intro y hy
      let yF : ↥F := ⟨y,interior_subset (hQF hy)⟩
      have hh := hQaxis yF hy
      constructor
      · rintro ⟨u,hu⟩
        exact hh.mp ⟨u,Subtype.ext hu⟩
      · intro hh0
        obtain ⟨u,hu⟩ := hh.mpr hh0
        exact ⟨u,congrArg Subtype.val hu⟩
    let H : Schoenflies.Plane ≃ₜ (ℝ × ℝ) :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
        (Homeomorph.piFinTwo (fun _ : Fin 2 => ℝ))).trans (Homeomorph.prodComm ℝ ℝ)
    let K' := K.trans H.toOpenPartialHomeomorph
    let Q' := Q.trans H.toOpenPartialHomeomorph
    have hK's : K'.source = K.source := by
      simp [K',OpenPartialHomeomorph.trans_source]
    have hQ's : Q'.source = Q.source := by
      simp [Q',OpenPartialHomeomorph.trans_source]
    have hK'f (y : S) : (K' y).1 = K y 1 := rfl
    have hQ'f (y : S) : (Q' y).1 = Q y 1 := rfl
    obtain ⟨U,hU,hpU,hUsub,hcomp⟩ := hcompare A p.val
      (by exact ⟨t,htxS⟩) K' Q'
      (hK's.symm ▸ hpK) (hQ's.symm ▸ hpQ)
      (by intro y hy; rw [hK'f]; exact hKaxis y (hK's ▸ hy))
      (by intro y hy; rw [hQ'f]; exact hQA y (hQ's ▸ hy))
    have hbs : (b.val.val s).val ∈ U := by
      change bS s ∈ U
      rw [hsxS]
      exact hpU
    have hnh : (fun u : Interval => (b.val.val u).val) ⁻¹' U ∈ 𝓝 s :=
      (continuous_subtype_val.comp b.val.val.continuous).continuousAt.preimage_mem_nhds
        (hU.mem_nhds hbs)
    obtain ⟨c,d,hscd,hcd⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨l,hls⟩ ⟨h,hsh⟩).mp hnh
    obtain ⟨u,hu⟩ := exists_between (max_lt (max_lt hls C.b_cuts.2.1) hscd.1)
    obtain ⟨v,hv⟩ := exists_between (lt_min (lt_min hsh C.b_cuts.2.2.1) hscd.2)
    have hlu : l < u := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hu.1)
    have hCu : C.bLeft < u := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hu.1)
    have hcu : c < u := (le_max_right _ _).trans_lt hu.1
    have hvh : v < h := hv.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hvC : v < C.bRight := hv.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hvd : v < d := hv.2.trans_le (min_le_right _ _)
    have huU : (b.val.val u).val ∈ U := hcd ⟨hcu,hu.2.trans hscd.2⟩
    have hvU : (b.val.val v).val ∈ U := hcd ⟨hscd.1.trans hv.1,hvd⟩
    have huQ : (b.val.val u).val ∈ Q.source := hQ's ▸ (hUsub huU).2
    have hvQ : (b.val.val v).val ∈ Q.source := hQ's ▸ (hUsub hvU).2
    have huSign := hsign u ⟨hlu,hu.2.trans hsh⟩ (ne_of_lt hu.2)
    have hvSign := hsign v ⟨hls.trans hv.1,hvh⟩ (ne_of_gt hv.1)
    have huA : (b.val.val u).val ∉ A := by
      intro hh
      have hzero := (hQA _ huQ).mp hh
      rw [hzero,mul_zero] at huSign
      exact lt_irrefl _ huSign
    have hvA : (b.val.val v).val ∉ A := by
      intro hh
      have hzero := (hQA _ hvQ).mp hh
      rw [hzero,mul_zero] at hvSign
      exact lt_irrefl _ hvSign
    have hsameQ : Q ((b.val.val u).val) 1 < 0 ↔ Q ((b.val.val v).val) 1 < 0 := by
      rcases hε with hε | hε
      · rw [hε] at huSign hvSign
        have hup : 0 < Q ((b.val.val u).val) 1 := by linarith
        have hvp : 0 < Q ((b.val.val v).val) 1 := by linarith
        exact iff_of_false (not_lt_of_ge hup.le) (not_lt_of_ge hvp.le)
      · rw [hε,one_mul] at huSign hvSign
        exact iff_of_true huSign hvSign
    have hsameK := (hcomp _ huU _ hvU huA hvA).mpr hsameQ
    change C.chart ((b.val.val u).val) 1 < 0 ↔ C.chart ((b.val.val v).val) 1 < 0 at hsameK
    rcases hCcross with ⟨hpLeft,hnRight⟩ | ⟨hnLeft,hpRight⟩
    · exact (not_lt_of_ge (hpLeft u ⟨hCu,hu.2⟩).le)
        (hsameK.mpr (hnRight v ⟨hv.1,hvC⟩))
    · exact (not_lt_of_ge (hpRight v ⟨hv.1,hvC⟩).le)
        (hsameK.mp (hnLeft u ⟨hCu,hu.2⟩))
  · rintro p rfl
    refine ⟨?_,N.first_on_a (mem_range_self 1),N.second_on_b ⟨1,N.corner_eq.symm⟩⟩
    apply image_subset_range d _
    rw [hboundary]
    exact Or.inl (Or.inl (mem_range_self 1))
