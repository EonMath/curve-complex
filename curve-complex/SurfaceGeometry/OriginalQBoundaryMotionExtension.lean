import CurveComplexGenusTwo.Dictionary.Genus
import ClassificationOfSurfaces.PolygonCellRadial

/-!
Source: harer_schoenflies_blueprint/c0_contraction/PLAN.md, N3; literal
Q/B chart context in proof_harer_loop_filling/SourceC0FiniteCurveLoopSurgery.lean.
A new topological cap-extension obligation, not an arbitrary surface-extension
principle. No smoothness or pointwise boundary fixation of H is required.
-/

namespace CurveComplexGenusTwo.SourceTopology

open Set Topology CurveComplex
open scoped Manifold ContDiff
set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

/-- A setwise-boundary-preserving motion of the actual chart-disk exterior
extends to the original surface. The original chart cap, the exterior, and its
frontier stay setwise invariant. The final transport equation retains every
endpoint range relation through the literal subtype inclusion into S. -/
theorem original_Q_boundary_motion_extends_over_chart_disk
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let D : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    ∀ (H : AmbientIsotopy ↥Q),
      (∀ t : Interval,
        (fun q : ↥Q => H.map (t, q)) '' {q : ↥Q | q.val ∈ B} =
          {q : ↥Q | q.val ∈ B}) →
      ∃ E : AmbientIsotopy S,
        (∀ (t : Interval) (q : ↥Q), E.map (t, q.val) = (H.map (t, q)).val) ∧
        (∀ t : Interval, (fun y : S => E.map (t, y)) '' Q = Q) ∧
        (∀ t : Interval, (fun y : S => E.map (t, y)) '' B = B) ∧
        (∀ t : Interval, (fun y : S => E.map (t, y)) '' frontier Q = frontier Q) ∧
        (∀ t : Interval, (fun y : S => E.map (t, y)) '' D = D) ∧
        (∀ q : ↥Q, E.finalMap q.val = (H.finalMap q).val) ∧
        (∀ A : Set ↥Q,
          E.finalMap '' (Subtype.val '' A) = Subtype.val '' (H.finalMap '' A)) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  let P := EuclideanSpace ℝ (Fin 2)
  let e := chartAt P x
  let p := e x
  let Q : Set S := (e.symm '' Metric.ball p R)ᶜ
  let B : Set S := e.symm '' Metric.sphere p R
  let D : Set S := e.symm '' Metric.closedBall p R
  have hO : IsOpen (e.symm '' Metric.ball p R) := e.symm.isOpen_image_of_subset_source
    Metric.isOpen_ball (Metric.ball_subset_closedBall.trans htarget)
  have hQc : IsClosed Q := hO.isClosed_compl
  have hDc : IsClosed D := ((isCompact_closedBall p R).image_of_continuousOn
    (e.symm.continuousOn.mono htarget)).isClosed
  have hBQ : B ⊆ Q := by
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, he⟩
    have heq : w = z := e.symm.injOn
      (htarget (Metric.ball_subset_closedBall hw))
      (htarget (Metric.sphere_subset_closedBall hz)) he
    exact (not_lt_of_ge (Metric.mem_sphere.mp hz).ge) (heq ▸ Metric.mem_ball.mp hw)
  have hBD : B ⊆ D := Set.image_mono Metric.sphere_subset_closedBall
  have hQD : Q ∩ D = B := by
    ext y
    constructor
    · rintro ⟨hQ, z, hz, rfl⟩
      refine ⟨z, Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hz) ?_), rfl⟩
      exact not_lt.mp fun hlt => hQ ⟨z, Metric.mem_ball.mpr hlt, rfl⟩
    · intro hy
      exact ⟨hBQ hy, hBD hy⟩
  have hcover : Q ∪ D = univ := by
    apply Set.eq_univ_of_forall
    intro y
    by_cases hy : y ∈ Q
    · exact Or.inl hy
    · exact Or.inr (Set.image_mono Metric.ball_subset_closedBall (not_not.mp hy))
  have hclosure : closure (e.symm '' Metric.ball p R) = D := by
    apply Set.Subset.antisymm
      (closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hDc)
    have hcb : closure (Metric.ball p R) = Metric.closedBall p R :=
      closure_ball p hR.ne'
    have hc : ContinuousOn e.symm (closure (Metric.ball p R)) := by
      rw [hcb]
      exact e.symm.continuousOn.mono htarget
    change e.symm '' Metric.closedBall p R ⊆ closure (e.symm '' Metric.ball p R)
    rw [← hcb]
    exact hc.image_closure
  have hfront : frontier Q = B := by
    rw [frontier_compl,hO.frontier_eq,hclosure]
    change D ∩ Q = B
    rw [Set.inter_comm,hQD]
  let lin : P ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let a : ℂ ≃ₜ P := lin.symm.toHomeomorph.trans
    ((Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft p))
  have ha (z : ℂ) : a z = p + R • lin.symm z := rfl
  have hdist (z : ℂ) : dist (a z) p = R * ‖z‖ := by
    rw [ha, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hR,
      lin.symm.norm_map]
  let da : Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall p R := a.subtype (by
    intro z
    simp only [Metric.mem_closedBall, dist_zero_right, hdist]
    constructor
    · intro hz; nlinarith
    · intro hz; nlinarith)
  let ba : Circle ≃ₜ Metric.sphere p R := a.subtype (by
    intro z
    change dist z 0 = 1 ↔ dist (a z) p = R
    rw [dist_zero_right]
    rw [hdist]
    constructor
    · intro hz; rw [hz,mul_one]
    · intro hz; nlinarith)
  let d : Metric.closedBall p R → S := fun z => e.symm z.val
  have hd : IsEmbedding d := e.symm.isEmbedding_restrict.comp (IsEmbedding.inclusion htarget)
  have hdrange : range d = D := by
    ext y
    simp only [mem_range]
    constructor
    · rintro ⟨z,rfl⟩; exact ⟨z,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,hz⟩,rfl⟩
  let ed : Metric.closedBall (0 : ℂ) 1 ≃ₜ D := da.trans
    (hd.toHomeomorph.trans (Homeomorph.setCongr hdrange))
  let b : Metric.sphere p R → S := fun z => e.symm z.val
  have hb : IsEmbedding b := e.symm.isEmbedding_restrict.comp
    (IsEmbedding.inclusion (Metric.sphere_subset_closedBall.trans htarget))
  have hbrange : range b = B := by
    ext y
    simp only [mem_range]
    constructor
    · rintro ⟨z,rfl⟩; exact ⟨z,z.property,rfl⟩
    · rintro ⟨z,hz,rfl⟩; exact ⟨⟨z,hz⟩,rfl⟩
  let eb : Circle ≃ₜ B := ba.trans (hb.toHomeomorph.trans (Homeomorph.setCongr hbrange))
  have hboundary (z : Circle) :
      (ed ⟨z, by simp [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩).val =
        (eb z).val := rfl
  dsimp only
  intro H hpres
  change AmbientIsotopy Q at H
  change ∀ t : Interval, (fun q : Q => H.map (t,q)) '' {q : Q | q.val ∈ B} = {q : Q | q.val ∈ B} at hpres
  choose hq hhq using H.homeomorphism_at
  have hmem (t : Interval) (q : Q) : (H.map (t,q)).val ∈ B ↔ q.val ∈ B := by
    constructor
    · intro h
      have hm : H.map (t,q) ∈ (fun q : Q => H.map (t,q)) '' {q : Q | q.val ∈ B} := by
        rw [hpres t]
        exact h
      obtain ⟨q',hq',heq⟩ := hm
      have he : q' = q := (hq t).injective (by rw [hhq t q',hhq t q]; exact heq)
      exact he ▸ hq'
    · intro h
      have hm : H.map (t,q) ∈ (fun q : Q => H.map (t,q)) '' {q : Q | q.val ∈ B} :=
        ⟨q,h,rfl⟩
      rwa [hpres t] at hm
  let BQ : Set Q := {q : Q | q.val ∈ B}
  let eBQ : B ≃ₜ BQ := {
    toFun := fun y => ⟨⟨y.val,hBQ y.property⟩,y.property⟩
    invFun := fun y => ⟨y.val.val,y.property⟩
    left_inv := by intro y; rfl
    right_inv := by intro y; rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.subtype_mk _
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val }
  let ec : Circle ≃ₜ BQ := eb.trans eBQ
  let k : Interval → Circle ≃ₜ Circle := fun t => ec.trans
    (((hq t).subtype (fun q => by rw [hhq]; exact (hmem t q).symm)).trans ec.symm)
  have hk (t : Interval) (z : Circle) :
      (ec (k t z)).val = H.map (t,(ec z).val) := by
    simp only [k,Homeomorph.trans_apply,Homeomorph.apply_symm_apply]
    exact hhq t (ec z).val
  have hkcont : Continuous (fun w : Interval × Circle => k w.1 w.2) := by
    have hc : Continuous (fun w : Interval × Circle =>
        H.map (w.1,(ec w.2).val)) := H.map.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp (ec.continuous.comp continuous_snd)))
    let f : Interval × Circle → BQ := fun w =>
      ⟨H.map (w.1,(ec w.2).val),(hmem w.1 (ec w.2).val).mpr (ec w.2).property⟩
    have hf : Continuous f := hc.subtype_mk _
    have heq : (fun w : Interval × Circle => k w.1 w.2) = ec.symm ∘ f := by
      funext w
      apply ec.injective
      apply Subtype.ext
      simpa only [Function.comp_apply,Homeomorph.apply_symm_apply] using hk w.1 w.2
    rw [heq]
    exact ec.symm.continuous.comp hf
  have hkzero (z : Circle) : k ⟨0,by norm_num⟩ z = z := by
    apply ec.injective
    apply Subtype.ext
    exact (hk _ z).trans (H.at_zero _)
  generalize hkdef : k = kk at hk hkcont hkzero
  let k := kk
  let radial : Interval × ℂ → ℂ := fun w =>
    LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap (k w.1) w.2
  have hradnorm (w : Interval × ℂ) : ‖radial w‖ = ‖w.2‖ :=
    LeanEval.Topology.ClassificationOfSurfaces.Circle.norm_radialMap _ _
  have hradzero (t : Interval) : radial (t,0) = 0 :=
    LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap_zero _
  have hradcont : Continuous radial := by
    rw [continuous_iff_continuousAt]
    intro w
    by_cases hw : w.2 = 0
    · rw [Metric.continuousAt_iff]
      intro ε hε
      refine ⟨ε,hε,?_⟩
      intro v hv
      have hzero : radial w = 0 := by
        rw [show w = (w.1,0) from Prod.ext rfl hw]
        exact hradzero _
      rw [hzero,dist_zero_right,hradnorm]
      have hdist : ‖v.2‖ ≤ dist v w := by
        simpa only [hw,dist_zero_right,Prod.dist_eq] using (le_max_right (dist v.1 w.1) (dist v.2 w.2))
      exact hdist.trans_lt hv
    · have hrestrict : Continuous (fun v : {w : Interval × ℂ // w.2 ≠ 0} => radial v.val) := by
        let dir : {w : Interval × ℂ // w.2 ≠ 0} → Circle := fun v =>
          LeanEval.Topology.ClassificationOfSurfaces.Circle.direction v.val.2 v.property
        have hd : Continuous dir :=
          LeanEval.Topology.ClassificationOfSurfaces.Circle.continuous_direction.comp
            ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun v => v.property))
        have ht : Continuous (fun v : {w : Interval × ℂ // w.2 ≠ 0} => v.val.1) :=
          continuous_fst.comp continuous_subtype_val
        have hkc : Continuous (fun v : {w : Interval × ℂ // w.2 ≠ 0} =>
            k v.val.1 (dir v)) := by
          convert hkcont.comp (ht.prodMk hd) using 1
          rfl
        have hk' : Continuous (fun v : {w : Interval × ℂ // w.2 ≠ 0} =>
            (k v.val.1 (dir v) : ℂ)) := by
          exact continuous_subtype_val.comp hkc
        have hn : Continuous (fun v : {w : Interval × ℂ // w.2 ≠ 0} =>
            (‖v.val.2‖ : ℂ)) :=
          Complex.continuous_ofReal.comp (continuous_snd.comp continuous_subtype_val).norm
        convert hn.mul hk' using 1
        funext v
        exact LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap_of_ne _ v.property
      have hOn : ContinuousOn radial {w : Interval × ℂ | w.2 ≠ 0} :=
        continuousOn_iff_continuous_domRestrict.mpr hrestrict
      exact (hOn w hw).continuousAt
        ((isOpen_compl_singleton.preimage continuous_snd).mem_nhds hw)
  let rd : Interval → Metric.closedBall (0 : ℂ) 1 ≃ₜ Metric.closedBall (0 : ℂ) 1 := fun t => {
    toFun := fun z => ⟨radial (t,z.val),by
      simpa only [Metric.mem_closedBall,dist_zero_right,hradnorm] using z.property⟩
    invFun := fun z => ⟨LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap (k t).symm z.val,by
      simpa only [Metric.mem_closedBall,dist_zero_right,
        LeanEval.Topology.ClassificationOfSurfaces.Circle.norm_radialMap] using z.property⟩
    left_inv := by
      intro z
      apply Subtype.ext
      exact LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap_symm_apply (k t) z.val
    right_inv := by
      intro z
      apply Subtype.ext
      exact LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap_symm_apply (k t).symm z.val
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (LeanEval.Topology.ClassificationOfSurfaces.Circle.continuous_radialMap (k t)).comp
        continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact (LeanEval.Topology.ClassificationOfSurfaces.Circle.continuous_radialMap (k t).symm).comp
        continuous_subtype_val }
  have hrdcont : Continuous (fun w : Interval × Metric.closedBall (0 : ℂ) 1 => rd w.1 w.2) :=
    (hradcont.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hrdbdry (t : Interval) (z : Circle) :
      rd t ⟨z,by simp [Metric.mem_closedBall,dist_zero_right,Circle.norm_coe]⟩ =
        ⟨k t z,by simp [Metric.mem_closedBall,dist_zero_right,Circle.norm_coe]⟩ := by
    apply Subtype.ext
    exact LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap_coe _ _
  have hrdzero (z : Metric.closedBall (0 : ℂ) 1) : rd ⟨0,by norm_num⟩ z = z := by
    apply Subtype.ext
    change LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap (k _) z.val = z.val
    have hk0 : k ⟨0,by norm_num⟩ = Homeomorph.refl Circle := by
      ext u
      exact congrArg Subtype.val (hkzero u)
    rw [hk0]
    by_cases hz : z.val = 0
    · simp [hz]
    · rw [LeanEval.Topology.ClassificationOfSurfaces.Circle.radialMap_of_ne _ hz]
      change (‖z.val‖ : ℂ) * (z.val / ‖z.val‖) = z.val
      field_simp [norm_ne_zero_iff.mpr hz]
  let md : Interval → D ≃ₜ D := fun t => ed.symm.trans ((rd t).trans ed)
  have hmdcont : Continuous (fun w : Interval × D => md w.1 w.2) :=
    ed.continuous.comp (hrdcont.comp (continuous_fst.prodMk
      (ed.symm.continuous.comp continuous_snd)))
  have hmdbdry (t : Interval) (y : B) :
      (md t ⟨y.val,hBD y.property⟩).val =
        (H.map (t,⟨y.val,hBQ y.property⟩)).val := by
    obtain ⟨z,rfl⟩ := eb.surjective y
    have hin : ed.symm ⟨(eb z).val,hBD (eb z).property⟩ =
        ⟨z,by simp [Metric.mem_closedBall,dist_zero_right,Circle.norm_coe]⟩ := by
      apply ed.injective
      rw [ed.apply_symm_apply]
      apply Subtype.ext
      exact (hboundary z).symm
    change (ed (rd t (ed.symm ⟨(eb z).val,_⟩))).val = _
    rw [hin,hrdbdry,hboundary]
    exact congrArg Subtype.val (hk t z)
  have hmdzero (y : D) : md ⟨0,by norm_num⟩ y = y := by
    change ed (rd _ (ed.symm y)) = y
    rw [hrdzero,ed.apply_symm_apply]
  generalize hmddef : md = mm at hmdcont hmdbdry hmdzero
  let md := mm
  have houtD (y : S) (hy : y ∉ Q) : y ∈ D := by
    have hc : y ∈ Q ∪ D := by rw [hcover]; trivial
    exact hc.resolve_left hy
  let f : Interval × S → S := fun w =>
    if h : w.2 ∈ Q then (H.map (w.1,⟨w.2,h⟩)).val
    else (md w.1 ⟨w.2,houtD w.2 h⟩).val
  have hfQ (t : Interval) (y : Q) : f (t,y.val) = (H.map (t,y)).val := by
    simp only [f,dite_eq_left y.property]
  have hfD (t : Interval) (y : D) : f (t,y.val) = (md t y).val := by
    by_cases hy : y.val ∈ Q
    · have hB : y.val ∈ B := by rw [← hQD]; exact ⟨hy,y.property⟩
      exact (hfQ t ⟨y.val,hy⟩).trans (hmdbdry t ⟨y.val,hB⟩).symm
    · simp only [f,dite_eq_right hy]
  have hfcont : Continuous f := by
    have hfcQ : ContinuousOn f (Prod.snd ⁻¹' Q) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc : Continuous (fun w : Prod.snd ⁻¹' Q =>
          (H.map (w.val.1,⟨w.val.2,w.property⟩)).val) :=
        continuous_subtype_val.comp (H.map.continuous.comp
          ((continuous_fst.comp continuous_subtype_val).prodMk
            ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun w => w.property))))
      convert hc using 1
      funext w
      exact hfQ w.val.1 ⟨w.val.2,w.property⟩
    have hfcD : ContinuousOn f (Prod.snd ⁻¹' D) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hc' : Continuous (fun w : Prod.snd ⁻¹' D =>
          md w.val.1 ⟨w.val.2,w.property⟩) := by
        convert hmdcont.comp
          ((continuous_fst.comp continuous_subtype_val).prodMk
            ((continuous_snd.comp continuous_subtype_val).subtype_mk
              (fun (w : Prod.snd ⁻¹' D) => w.property))) using 1
        rfl
      have hc : Continuous (fun w : Prod.snd ⁻¹' D =>
          (md w.val.1 ⟨w.val.2,w.property⟩).val) := continuous_subtype_val.comp hc' 
      convert hc using 1
      funext w
      exact hfD w.val.1 ⟨w.val.2,w.property⟩
    have hc := hfcQ.union_of_isClosed hfcD (hQc.preimage continuous_snd) (hDc.preimage continuous_snd)
    have hu : (Prod.snd ⁻¹' Q : Set (Interval × S)) ∪ (Prod.snd ⁻¹' D) = univ := by
      rw [← Set.preimage_union,hcover,Set.preimage_univ]
    rw [hu] at hc
    exact continuousOn_univ.mp hc
  have hfzero (y : S) : f (⟨0,by norm_num⟩,y) = y := by
    by_cases hy : y ∈ Q
    · exact (hfQ _ ⟨y,hy⟩).trans (congrArg Subtype.val (H.at_zero ⟨y,hy⟩))
    · exact (hfD _ ⟨y,houtD y hy⟩).trans (congrArg Subtype.val (hmdzero ⟨y,houtD y hy⟩))
  have hfinj (t : Interval) : Function.Injective (fun y => f (t,y)) := by
    have hQQ (y z : Q) (he : f (t,y.val) = f (t,z.val)) : y.val = z.val := by
      apply congrArg Subtype.val
      apply (hq t).injective
      rw [hhq,hhq]
      apply Subtype.ext
      simpa only [hfQ] using he
    have hDD (y z : D) (he : f (t,y.val) = f (t,z.val)) : y.val = z.val := by
      apply congrArg Subtype.val
      apply (md t).injective
      apply Subtype.ext
      simpa only [hfD] using he
    have hQD' (y : Q) (z : D) (he : f (t,y.val) = f (t,z.val)) : y.val = z.val := by
      have hHB : (H.map (t,y)).val ∈ B := by
        rw [← hQD]
        refine ⟨(H.map (t,y)).property,?_⟩
        rw [← hfQ] 
        exact he.symm ▸ (by rw [hfD]; exact (md t z).property)
      exact hDD ⟨y.val,hBD ((hmem t y).mp hHB)⟩ z he
    intro y z he
    by_cases hy : y ∈ Q <;> by_cases hz : z ∈ Q
    · exact hQQ ⟨y,hy⟩ ⟨z,hz⟩ he
    · exact hQD' ⟨y,hy⟩ ⟨z,houtD z hz⟩ he
    · exact (hQD' ⟨z,hz⟩ ⟨y,houtD y hy⟩ he.symm).symm
    · exact hDD ⟨y,houtD y hy⟩ ⟨z,houtD z hz⟩ he
  have hfsurj (t : Interval) : Function.Surjective (fun y => f (t,y)) := by
    intro y
    by_cases hy : y ∈ Q
    · let z := (hq t).symm ⟨y,hy⟩
      refine ⟨z.val,?_⟩
      exact (hfQ t z).trans (congrArg Subtype.val ((hhq t z).symm.trans ((hq t).apply_symm_apply ⟨y,hy⟩)))
    · let z := (md t).symm ⟨y,houtD y hy⟩
      refine ⟨z.val,?_⟩
      exact (hfD t z).trans (congrArg Subtype.val ((md t).apply_symm_apply ⟨y,houtD y hy⟩))
  let E : AmbientIsotopy S := {
    map := ⟨f,hfcont⟩
    homeomorphism_at := by
      intro t
      have hc : Continuous (fun y : S => f (t,y)) :=
        hfcont.comp (continuous_const.prodMk continuous_id)
      let et : S ≃ S := Equiv.ofBijective (fun y => f (t,y)) ⟨hfinj t,hfsurj t⟩
      exact ⟨et.toHomeomorphOfContinuousClosed hc hc.isClosedMap,fun y => rfl⟩
    at_zero := hfzero }
  have hEQ (t : Interval) (q : Q) : E.map (t,q.val) = (H.map (t,q)).val := hfQ t q
  have himageQ (t : Interval) : (fun y : S => E.map (t,y)) '' Q = Q := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change E.map (t,z) ∈ Q
      rw [hEQ t ⟨z,hz⟩]
      exact (H.map (t,⟨z,hz⟩)).property
    · intro hy
      let z := (hq t).symm ⟨y,hy⟩
      refine ⟨z.val,z.property,?_⟩
      exact (hEQ t z).trans (congrArg Subtype.val ((hhq t z).symm.trans ((hq t).apply_symm_apply ⟨y,hy⟩)))
  have himageB (t : Interval) : (fun y : S => E.map (t,y)) '' B = B := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change E.map (t,z) ∈ B
      rw [hEQ t ⟨z,hBQ hz⟩]
      exact (hmem t ⟨z,hBQ hz⟩).mpr hz
    · intro hy
      have hm : (⟨y,hBQ hy⟩ : Q) ∈ (fun q : Q => H.map (t,q)) '' BQ := by
        change (⟨y,hBQ hy⟩ : Q) ∈ (fun q : Q => H.map (t,q)) '' {q : Q | q.val ∈ B}
        rw [hpres t]
        exact hy
      obtain ⟨z,hz,he⟩ := hm
      exact ⟨z.val,hz,(hEQ t z).trans (congrArg Subtype.val he)⟩
  have himageD (t : Interval) : (fun y : S => E.map (t,y)) '' D = D := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change f (t,z) ∈ D
      rw [hfD t ⟨z,hz⟩]
      exact (md t ⟨z,hz⟩).property
    · intro hy
      let z := (md t).symm ⟨y,hy⟩
      refine ⟨z.val,z.property,?_⟩
      exact (hfD t z).trans (congrArg Subtype.val ((md t).apply_symm_apply ⟨y,hy⟩))
  refine ⟨E,hEQ,himageQ,himageB,?_,himageD,?_,?_⟩
  · intro t
    rw [hfront]
    exact himageB t
  · intro q
    exact hEQ ⟨1,by norm_num⟩ q
  · intro A
    rw [Set.image_image,Set.image_image]
    apply congrArg (fun f : Q → S => f '' A)
    funext q
    exact hEQ ⟨1,by norm_num⟩ q

end CurveComplexGenusTwo.SourceTopology
