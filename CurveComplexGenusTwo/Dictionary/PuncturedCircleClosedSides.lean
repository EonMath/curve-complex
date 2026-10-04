import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Dependencies.SphereOmittedPoint
import CurveComplexGenusTwo.Filtration.Geometry.ActualJordanRegionsHeader
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
 [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
theorem puncturedCircle_closedSides (a : PuncturedCircle M) :
 ∃ U V : Set S,
 IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧ U ∪ V = a.imageᶜ ∧
 ∃ dU : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure U,
 ∃ dV : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure V,
 (∀ x, (dU x:S) ∈ a.image ↔ ‖x.val‖=1) ∧
 (∀ x, (dV x:S) ∈ a.image ↔ ‖x.val‖=1) ∧
 (∀ x, (dU x:S) ∈ U ↔ ‖x.val‖<1) ∧
 (∀ x, (dV x:S) ∈ V ↔ ‖x.val‖<1) ∧
 closure U = U ∪ a.image ∧ closure V = V ∪ a.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hJordan (a : PuncturedCircle M) :
   ∃ c : CurveComplex.SpherePort.JordanCurve, c.image = M.sphere '' a.image := by
   let b : C(Interval,Circle) := ⟨fun t => Circle.exp (2 * Real.pi * t.val),
     Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)⟩
   have hb : Function.Surjective b := by
     intro z
     have hz : z ∈ Circle.exp '' Icc (0:ℝ) (2*Real.pi) := by
       have hset := Circle.periodic_exp.image_Icc (a := (0:ℝ)) (by positivity)
       simp only [zero_add] at hset
       rw [hset]
       exact ⟨z.val.arg,Circle.exp_arg z⟩
     obtain ⟨t,ht,he⟩ := hz
     refine ⟨⟨t/(2*Real.pi),?_⟩,?_⟩
     · constructor
       · exact div_nonneg ht.1 (by positivity)
       · exact (div_le_one (by positivity)).mpr ht.2
     · change Circle.exp (2*Real.pi*(t/(2*Real.pi))) = z
       rw [mul_div_cancel₀ _ (by positivity)]
       exact he
   have hcoll : ∀ s t : Interval, b s = b t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
     intro s t he
     obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp he
     obtain ⟨hs0,hs1⟩ := s.property
     obtain ⟨ht0,ht1⟩ := t.property
     have hrel : s.val = t.val + n := by nlinarith [Real.pi_pos]
     have hnlow : (-1:ℝ) ≤ n := by linarith
     have hnup : (n:ℝ) ≤ 1 := by linarith
     have hnl : (-1:ℤ) ≤ n := by exact_mod_cast hnlow
     have hnu : n ≤ (1:ℤ) := by exact_mod_cast hnup
     have hcases : n = 0 ∨ n = -1 ∨ n = 1 := by omega
     rcases hcases with rfl | rfl | rfl
     · left; apply Subtype.ext; simpa using hrel
     · simp only [Int.cast_neg,Int.cast_one] at hrel
       right; left
       constructor
       · apply Subtype.ext; change s.val = 0; linarith
       · apply Subtype.ext; change t.val = 1; linarith
     · simp only [Int.cast_one] at hrel
       right; right
       constructor
       · apply Subtype.ext; change s.val = 1; linarith
       · apply Subtype.ext; change t.val = 0; linarith
   let c : CurveComplex.SpherePort.JordanCurve := {
     map := fun t => M.sphere (a.curve.map (b t))
     continuous := M.sphere.continuous.comp (a.curve.embedded.continuous.comp b.continuous)
     injective_except_ends := fun s t he => hcoll s t (a.curve.embedded.injective (M.sphere.injective he))
     closed := by change M.sphere (a.curve.map (Circle.exp (2*Real.pi*0))) = M.sphere (a.curve.map (Circle.exp (2*Real.pi*1))); simp }
   refine ⟨c,?_⟩
   change Set.range (M.sphere ∘ (a.curve.map ∘ b)) = M.sphere '' Set.range a.curve.map
   rw [Set.range_comp, hb.range_comp]
  obtain ⟨c,hc⟩ := hJordan a
  let d : Curve CurveComplex.SpherePort.Sphere :=
    ⟨M.sphere ∘ a.curve.map,M.sphere.isEmbedding.comp a.curve.embedded⟩
  obtain ⟨p,hp⟩ := CurveComplex.sphere_embedded_circle_omits_point d
  have hd : d.image = M.sphere '' a.image := by
    change Set.range (M.sphere ∘ a.curve.map) = M.sphere '' Set.range a.curve.map
    exact Set.range_comp _ _
  let P : CurveComplex.SpherePort.Chart c := {
    puncture := p
    avoids := by rw [hc,← hd]; exact hp
    plane := puncturedSpherePlane p }
  let C := P.planeImage c
  have hC : Schoenflies.IsJordanCurve C := CurveComplex.SpherePort.chart_image_jordan c P
  have hsep := Schoenflies.jordan_curve_theorem hC
  let F : OnePoint JordanPlane ≃ₜ S :=
    (CurveComplex.SpherePort.chartOnePoint c P).trans M.sphere.symm
  let B : Set (OnePoint JordanPlane) := OnePoint.some '' C
  let U : Set (OnePoint JordanPlane) := OnePoint.some '' Schoenflies.inside C
  let V : Set (OnePoint JordanPlane) :=
    {OnePoint.infty} ∪ OnePoint.some '' Schoenflies.outside C
  have hB0 : (CurveComplex.SpherePort.chartOnePoint c P) '' B = c.image := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y, hy, hzy⟩ := hz
      change (P.plane.symm z).val ∈ c.image
      rw [← hzy, P.plane.symm_apply_apply]
      exact hy
    · intro hx
      let y : {x : CurveComplex.SpherePort.Sphere // x ≠ P.puncture} :=
        ⟨x, fun he => P.avoids (he ▸ hx)⟩
      refine ⟨OnePoint.some (P.plane y), ⟨P.plane y, ⟨y, hx, rfl⟩, rfl⟩, ?_⟩
      change (P.plane.symm (P.plane y)).val = x
      rw [P.plane.symm_apply_apply]
  have hBimage : F '' B = a.image := by
    have hcomp : F '' B = M.sphere.symm '' ((CurveComplex.SpherePort.chartOnePoint c P) '' B) := by
      exact (Set.image_image M.sphere.symm (CurveComplex.SpherePort.chartOnePoint c P) B).symm
    rw [hcomp,hB0,hc,Set.image_image]
    simp only [Homeomorph.symm_apply_apply,Set.image_id']
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hx hy
    cases x with
    | infty => simp [U] at hx
    | coe z =>
      have hzU : z ∈ Schoenflies.inside C := by simpa [U] using hx
      have hzV : z ∈ Schoenflies.outside C := by simpa [V] using hy
      exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzU hzV
  have hcover : U ∪ V = Bᶜ := by
    ext x
    cases x with
    | infty => simp [U, V, B]
    | coe z =>
      have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
      simpa [U, V, B] using hz
  have hclU0 : closure U = OnePoint.some '' closure (Schoenflies.inside C) := by
    have hk : IsCompact (closure (Schoenflies.inside C)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.image_mono subset_closure) (hk.image OnePoint.continuous_coe).isClosed
    · exact image_closure_subset_closure_image OnePoint.continuous_coe
  have hclU : closure U = U ∪ B := by
    rw [hclU0, (Schoenflies.IsRegionOf.inside C).closure_eq hsep, Set.image_union]
  have hclV : closure V = V ∪ B := by
    change closure (CurveComplex.SpherePort.compactifiedOutside (Schoenflies.outside C)) = _
    rw [CurveComplex.SpherePort.closure_compactifiedOutside,
      (Schoenflies.IsRegionOf.outside C).closure_eq hsep]
    simp only [CurveComplex.SpherePort.compactifiedOutside, Set.image_union]
    exact Set.union_assoc _ _ _ |>.symm
  have hUcomp : closure U = Vᶜ := by
    rw [hclU]
    ext x
    cases x with
    | infty => simp [U, V, B]
    | coe z =>
      have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
      have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
        fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
      have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
      have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
      have hz' : z ∈ Schoenflies.inside C ∨ z ∈ C ↔ z ∉ Schoenflies.outside C := by
        simp only [Set.mem_union, Set.mem_compl_iff] at hz
        tauto
      simpa [U, V, B] using hz'
  have hVcomp : closure V = Uᶜ := by
    rw [hclV]
    ext x
    cases x with
    | infty => simp [U, V, B]
    | coe z =>
      have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
      have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
        fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
      have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
      have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
      have hz' : z ∈ Schoenflies.outside C ∨ z ∈ C ↔ z ∉ Schoenflies.inside C := by
        simp only [Set.mem_union, Set.mem_compl_iff] at hz
        tauto
      simpa [U, V, B] using hz'
  have hopenU : IsOpen U := by
    rw [← compl_compl U, ← hVcomp]
    exact isClosed_closure.isOpen_compl
  have hopenV : IsOpen V := by
    rw [← compl_compl V, ← hUcomp]
    exact isClosed_closure.isOpen_compl
  have hintU : interior (closure U) = U := by
    rw [hUcomp, interior_compl, hVcomp, compl_compl]
  have hintV : interior (closure V) = V := by
    rw [hVcomp, interior_compl, hUcomp, compl_compl]
  have hboundU : frontier U = B := by
    rw [hopenU.frontier_eq, hclU]
    ext x
    have hn : x ∈ U → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inl hx)
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto
  have hboundV : frontier V = B := by
    rw [hopenV.frontier_eq, hclV]
    ext x
    have hn : x ∈ V → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inr hx)
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto
  obtain ⟨dU, hdUb, hdUi⟩ := CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary C hC
  let eU : JordanClosedDisk ≃ₜ closure U :=
    dU.trans ((OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage
      (closure (Schoenflies.inside C))).trans (Homeomorph.setCongr hclU0.symm))
  have heUb : ∀ x : JordanClosedDisk, (eU x : OnePoint JordanPlane) ∈ B ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change OnePoint.some (dU x : JordanPlane) ∈ OnePoint.some '' C ↔ _
    simpa using hdUb x
  obtain ⟨q, hq⟩ := hsep.isConnected_inside.nonempty
  let C' := Schoenflies.invert q '' C
  have hC' : Schoenflies.IsJordanCurve C' := hC.invert_image hq.1
  obtain ⟨dV, hdVb, hdVi⟩ := CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary C' hC'
  let j := CurveComplex.SphereGapFinish.exteriorToInvertedInterior C hC q hq
  have hclV0 : CurveComplex.SphereGapFinish.compactifiedExterior C = closure V := by
    change _ = closure (CurveComplex.SpherePort.compactifiedOutside (Schoenflies.outside C))
    rw [CurveComplex.SpherePort.closure_compactifiedOutside]
    rfl
  let eV : JordanClosedDisk ≃ₜ closure V :=
    dV.trans (j.symm.trans (Homeomorph.setCongr hclV0))
  have hjb : ∀ z : CurveComplex.SphereGapFinish.compactifiedExterior C,
      (j z : JordanPlane) ∈ C' ↔ (z : OnePoint JordanPlane) ∈ B := by
    intro z
    change CurveComplex.SphereGapFinish.invertAtInfinity q z ∈ Schoenflies.invert q '' C ↔ _
    constructor
    · rintro ⟨y, hy, he⟩
      have hyext : (OnePoint.some y : OnePoint JordanPlane) ∈
          CurveComplex.SphereGapFinish.compactifiedExterior C := by
        change (OnePoint.some y) ∈ {OnePoint.infty} ∪ OnePoint.some '' closure (Schoenflies.outside C)
        exact Or.inr ⟨y, (Schoenflies.IsRegionOf.outside C).subset_closure hsep hy, rfl⟩
      have heq : OnePoint.some y = (z : OnePoint JordanPlane) :=
        CurveComplex.SphereGapFinish.invertAtInfinity_injOn_exterior C hC q hq hyext z.property he
      exact heq ▸ Set.mem_image_of_mem OnePoint.some hy
    · rintro ⟨y, hy, he⟩
      rw [← he]
      exact Set.mem_image_of_mem (Schoenflies.invert q) hy
  have heVb : ∀ x : JordanClosedDisk, (eV x : OnePoint JordanPlane) ∈ B ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change (j.symm (dV x) : OnePoint JordanPlane) ∈ B ↔ _
    rw [← hjb (j.symm (dV x)), j.apply_symm_apply]
    exact hdVb x
  have heUi : ∀ x : JordanClosedDisk, (eU x : OnePoint JordanPlane) ∈ U ↔ ‖(x : JordanPlane)‖ < 1 := by
    intro x
    change OnePoint.some (dU x : JordanPlane) ∈ OnePoint.some '' Schoenflies.inside C ↔ _
    simpa using hdUi x
  have heVi : ∀ x : JordanClosedDisk, (eV x : OnePoint JordanPlane) ∈ V ↔ ‖(x : JordanPlane)‖ < 1 := by
    intro x
    have hxle : ‖(x : JordanPlane)‖ ≤ 1 := by
      simpa only [dist_zero_right] using Metric.mem_closedBall.mp x.property
    have hxcl : (eV x : OnePoint JordanPlane) ∈ V ∪ B := hclV ▸ (eV x).property
    have hxnot : (eV x : OnePoint JordanPlane) ∈ V ↔ (eV x : OnePoint JordanPlane) ∉ B := by
      constructor
      · intro hx hb
        exact (Set.ext_iff.mp hcover _).mp (Or.inr hx) hb
      · intro hn
        exact hxcl.resolve_right hn
    rw [hxnot, heVb]
    exact ⟨lt_of_le_of_ne hxle, fun h => h.ne⟩
  have openDiskOf (T : Type) [TopologicalSpace T] (W : Set T)
      (d : JordanClosedDisk ≃ₜ closure W)
      (hdi : ∀ x : JordanClosedDisk, (d x : T) ∈ W ↔ ‖(x : JordanPlane)‖ < 1) :
      Nonempty (JordanOpenDisk ≃ₜ W) := by
    let f : JordanOpenDisk → JordanClosedDisk := fun x =>
      ⟨x, by
        apply Metric.mem_closedBall.mpr
        exact (Metric.mem_ball.mp x.property).le⟩
    let k : W → closure W := fun y => ⟨y, subset_closure y.property⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk (fun x => (f x).property)
    have hk : Continuous k := continuous_subtype_val.subtype_mk (fun y => (k y).property)
    refine ⟨{
      toFun := fun x => ⟨d (f x), (hdi (f x)).mpr (by
        simpa only [dist_zero_right] using Metric.mem_ball.mp x.property)⟩
      invFun := fun y => ⟨(d.symm (k y) : JordanPlane), by
        apply Metric.mem_ball.mpr
        simpa only [dist_zero_right, Function.comp_apply] using (hdi (d.symm (k y))).mp (by
          rw [d.apply_symm_apply]
          exact y.property)⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := (continuous_subtype_val.comp (d.continuous.comp hf)).subtype_mk
        (fun x => (hdi (f x)).mpr (by
          simpa only [dist_zero_right] using Metric.mem_ball.mp x.property))
      continuous_invFun := (continuous_subtype_val.comp (d.symm.continuous.comp hk)).subtype_mk
        (fun y => by
          apply Metric.mem_ball.mpr
          simpa only [dist_zero_right, Function.comp_apply] using (hdi (d.symm (k y))).mp (by
            rw [d.apply_symm_apply]
            exact y.property)) }⟩
    · intro x
      apply Subtype.ext
      have hkf : k ⟨d (f x), (hdi (f x)).mpr (by
          simpa only [dist_zero_right] using Metric.mem_ball.mp x.property)⟩ = d (f x) :=
        Subtype.ext rfl
      change (d.symm (k _) : JordanPlane) = x.val
      rw [hkf, d.symm_apply_apply]
    · intro y
      apply Subtype.ext
      have hfk : f ⟨(d.symm (k y) : JordanPlane), by
          apply Metric.mem_ball.mpr
          simpa only [dist_zero_right, Function.comp_apply] using (hdi (d.symm (k y))).mp (by
            rw [d.apply_symm_apply]
            exact y.property)⟩ = d.symm (k y) := Subtype.ext rfl
      change (d (f _) : T) = y.val
      rw [hfk, d.apply_symm_apply]
  obtain ⟨oU⟩ := openDiskOf (OnePoint JordanPlane) U eU heUi
  obtain ⟨oV⟩ := openDiskOf (OnePoint JordanPlane) V eV heVi
  have hball : IsConnected (JordanOpenDisk : Set JordanPlane) :=
    (convex_ball (0 : JordanPlane) 1).isConnected ⟨0, by simp⟩
  letI : ConnectedSpace JordanOpenDisk := isConnected_iff_connectedSpace.mp hball
  have hconnU : IsConnected U :=
    isConnected_iff_connectedSpace.mpr (oU.connectedSpace_iff.mp inferInstance)
  have hconnV : IsConnected V :=
    isConnected_iff_connectedSpace.mpr (oV.connectedSpace_iff.mp inferInstance)
  let SU := F '' U
  let SV := F '' V
  have hsopenU : IsOpen SU := F.isOpenMap U hopenU
  have hsopenV : IsOpen SV := F.isOpenMap V hopenV
  have hsconnU : IsConnected SU := (F.isConnected_image).mpr hconnU
  have hsconnV : IsConnected SV := (F.isConnected_image).mpr hconnV
  have hsdisj : Disjoint SU SV := Set.disjoint_image_of_injective F.injective hdisj
  have hscover : SU ∪ SV = a.imageᶜ := by
    change F '' U ∪ F '' V = _
    rw [← Set.image_union, hcover, F.image_compl, hBimage]
  have hsclU : closure SU = SU ∪ a.image := by
    rw [← F.image_closure, hclU, Set.image_union, hBimage]
  have hsclV : closure SV = SV ∪ a.image := by
    rw [← F.image_closure, hclV, Set.image_union, hBimage]
  have hsintU : interior (closure SU) = SU := by
    rw [← F.image_closure, ← F.image_interior, hintU]
  have hsintV : interior (closure SV) = SV := by
    rw [← F.image_closure, ← F.image_interior, hintV]
  have hsboundU : frontier SU = a.image := by
    rw [← F.image_frontier, hboundU, hBimage]
  have hsboundV : frontier SV = a.image := by
    rw [← F.image_frontier, hboundV, hBimage]
  let dsU : JordanClosedDisk ≃ₜ closure SU :=
    eU.trans ((F.isEmbedding.homeomorphImage (closure U)).trans
      (Homeomorph.setCongr (F.image_closure U)))
  let dsV : JordanClosedDisk ≃ₜ closure SV :=
    eV.trans ((F.isEmbedding.homeomorphImage (closure V)).trans
      (Homeomorph.setCongr (F.image_closure V)))
  have hFmem (D : Set (OnePoint JordanPlane)) (z : OnePoint JordanPlane) :
      F z ∈ F '' D ↔ z ∈ D := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      exact F.injective hwz ▸ hw
    · intro hz
      exact Set.mem_image_of_mem F hz
  have hsUi : ∀ x : JordanClosedDisk, (dsU x : S) ∈ SU ↔ ‖(x : JordanPlane)‖ < 1 := by
    intro x
    change F (eU x : OnePoint JordanPlane) ∈ F '' U ↔ _
    rw [hFmem]
    exact heUi x
  have hsVi : ∀ x : JordanClosedDisk, (dsV x : S) ∈ SV ↔ ‖(x : JordanPlane)‖ < 1 := by
    intro x
    change F (eV x : OnePoint JordanPlane) ∈ F '' V ↔ _
    rw [hFmem]
    exact heVi x
  have hsUb : ∀ x : JordanClosedDisk, (dsU x : S) ∈ a.image ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change F (eU x : OnePoint JordanPlane) ∈ a.image ↔ _
    rw [← hBimage, hFmem]
    exact heUb x
  have hsVb : ∀ x : JordanClosedDisk, (dsV x : S) ∈ a.image ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change F (eV x : OnePoint JordanPlane) ∈ a.image ↔ _
    rw [← hBimage, hFmem]
    exact heVb x
  exact ⟨SU,SV,hsopenU,hsopenV,hsconnU,hsconnV,hsdisj,hscover,dsU,dsV,hsUb,hsVb,hsUi,hsVi,hsclU,hsclV⟩
end CurveComplex.HyperellipticModel
