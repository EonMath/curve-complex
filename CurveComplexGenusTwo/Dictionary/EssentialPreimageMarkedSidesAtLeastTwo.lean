import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Dependencies.SphereOmittedPoint
import CurveComplexGenusTwo.Filtration.Geometry.ActualJordanRegionsHeader
open Set Topology Filter
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
 [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
theorem essentialPreimage_markedSidesAtLeastTwo (a : PuncturedCircle M) (c : EssentialCurve E)
 (hc : c.val.image = M.cover.projection ⁻¹' a.image) :
 ∃ m n : ℕ, 1 < m ∧ 1 < n ∧ m+n=6 ∧ SplitsMarked M a m n := by
  classical
  have hSides (a : PuncturedCircle M) :
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
  have hNoCircle (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
   (hf : IsEmbedding f) (havoid : ∀ z, f z ∉ M.cover.branch)
   (β : C(Circle,Metric.closedBall (0 : Schoenflies.Plane) 1))
   (c : Curve E) (hc : c.image = M.cover.projection ⁻¹' Set.range (f.comp β)) : False := by
    have hLifts (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
     (hf : IsEmbedding f) (havoid : ∀ z, f z ∉ M.cover.branch) :
     ∃ F : C(Metric.closedBall (0 : Schoenflies.Plane) 1,E),
     IsEmbedding F ∧ (∀ z, M.cover.projection (F z) = f z) ∧
     M.cover.projection ⁻¹' Set.range f = Set.range F ∪ M.cover.deck '' Set.range F ∧
     Disjoint (Set.range F) (M.cover.deck '' Set.range F) := by
     classical
     letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
     letI : ContractibleSpace (Metric.closedBall (0 : Schoenflies.Plane) 1) :=
       Metric.contractibleSpace_closedBall (by norm_num)
     letI : LocallyPathConnectedSpace (Metric.closedBall (0 : Schoenflies.Plane) 1) :=
       (convex_closedBall (0 : Schoenflies.Plane) 1).locallyPathConnectedSpace
     let a : Metric.closedBall (0 : Schoenflies.Plane) 1 := ⟨0,by simp⟩
     obtain ⟨x,hx⟩ := M.cover.projection_surjective (f a)
     let g : C(Metric.closedBall (0 : Schoenflies.Plane) 1,M.cover.unramifiedBase) :=
       ⟨fun z => ⟨f z,havoid z⟩, f.continuous.subtype_mk _⟩
     let y : M.cover.unramifiedTotal := ⟨x, by change M.cover.projection x ∉ M.cover.branch; rw [hx]; exact havoid a⟩
     have hy : M.cover.unramifiedProjection y = g a := Subtype.ext hx
     obtain ⟨G,⟨_,hG⟩,_⟩ := M.cover.unramified_isCoveringMap.existsUnique_continuousMap_lifts g a y hy
     let F : C(Metric.closedBall (0 : Schoenflies.Plane) 1,E) :=
       ⟨fun z => (G z).val, continuous_subtype_val.comp G.continuous⟩
     have hF (z) : M.cover.projection (F z) = f z :=
       congrArg Subtype.val (congrFun hG z)
     have hFi : Function.Injective F := by
       intro z w he
       apply hf.injective
       rw [← hF z,← hF w,he]
     refine ⟨F,(F.continuous.isClosedEmbedding hFi).isEmbedding,hF,?_,?_⟩
     · ext w
       constructor
       · rintro ⟨z,hz⟩
         rcases (M.cover.fiber_pair (F z) w).mp ((hF z).trans hz) with he | he
         · exact Or.inl ⟨z,he.symm⟩
         · exact Or.inr ⟨F z,⟨z,rfl⟩,he.symm⟩
       · rintro (⟨z,rfl⟩ | ⟨w,⟨z,rfl⟩,rfl⟩)
         · exact ⟨z,(hF z).symm⟩
         · exact ⟨z,((M.cover.projection_deck (F z)).trans (hF z)).symm⟩
     · apply Set.disjoint_left.mpr
       rintro w ⟨z,rfl⟩ ⟨v,⟨t,rfl⟩,he⟩
       have hzt : z = t := hf.injective (by rw [← hF z,← hF t,← he,M.cover.projection_deck])
       subst t
       exact havoid z ((hF z) ▸ (M.cover.fixed_iff_branch (F z)).mp he)
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    obtain ⟨F,hF,hπ,hfull,hdisj⟩ := hLifts f hf havoid
    let A := Set.range (F.comp β)
    let B := M.cover.deck '' A
    have hAclosed : IsClosed A := (isCompact_range (F.comp β).continuous).isClosed
    have hBclosed : IsClosed B := (isCompact_range (F.comp β).continuous).image M.cover.deck.continuous |>.isClosed
    have hAB : Disjoint A B := hdisj.mono
      (by rintro x ⟨t,rfl⟩; exact ⟨β t,rfl⟩)
      (Set.image_mono (by rintro x ⟨t,rfl⟩; exact ⟨β t,rfl⟩))
    have hcover : c.image = A ∪ B := by
      rw [hc]
      ext x
      constructor
      · rintro ⟨t,ht⟩
        rcases (M.cover.fiber_pair (F (β t)) x).mp ((hπ (β t)).trans ht) with he | he
        · exact Or.inl ⟨t,he.symm⟩
        · exact Or.inr ⟨F (β t),⟨t,rfl⟩,he.symm⟩
      · rintro (⟨t,rfl⟩ | ⟨y,⟨t,rfl⟩,rfl⟩)
        · exact ⟨t,(hπ (β t)).symm⟩
        · exact ⟨t,((M.cover.projection_deck _).trans (hπ (β t))).symm⟩
    have hconn : IsPreconnected c.image := isPreconnected_range c.embedded.continuous
    have hAn : (c.image ∩ A).Nonempty := by
      refine ⟨F (β 1),?_,⟨1,rfl⟩⟩
      rw [hcover]; exact Or.inl ⟨1,rfl⟩
    have hBn : (c.image ∩ B).Nonempty := by
      refine ⟨M.cover.deck (F (β 1)),?_,⟨F (β 1),⟨1,rfl⟩,rfl⟩⟩
      rw [hcover]; exact Or.inr ⟨F (β 1),⟨1,rfl⟩,rfl⟩
    obtain ⟨x,_,hxA,hxB⟩ := isPreconnected_closed_iff.mp hconn A B hAclosed hBclosed hcover.subset hAn hBn
    exact Set.disjoint_left.mp hAB hxA hxB

  have hDisc (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
   (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (hm : ‖m.val‖<1)
   (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
   (c : Curve E) (hc : c.image = M.cover.projection ⁻¹'
     (f '' {z : Metric.closedBall (0 : Schoenflies.Plane) 1 | ‖z.val‖=1})) : BoundsDisc c := by
    have hPuncture (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
     (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (hm : ‖m.val‖<1)
     (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
     (β : C(Circle,Metric.closedBall (0 : Schoenflies.Plane) 1)) (hβ : ∀ t, ‖(β t).val‖=1)
     (c : Curve E) (hπc : ∀ t, M.cover.projection (c.map t)=f (β t)) :
     ∃ θ : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Circle),
     ∃ F : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},E),
     (∀ z, Complex.orthonormalBasisOneI.repr (‖z.val.val‖ • (θ z:ℂ))=z.val.val) ∧
     Function.Injective F ∧
     (∀ z, ∃ d : Metric.closedBall (0 : Schoenflies.Plane) 1,
       d.val=m.val+‖z.val.val‖ • ((β (θ z)).val-m.val) ∧ M.cover.projection (F z)=f d) ∧
     (∀ z, M.cover.projection (F z) ∉ M.cover.branch) ∧
     (∀ z, ‖z.val.val‖=1 → F z=c.map (θ z)) := by
    
      have hLift (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
       (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (hm : ‖m.val‖<1)
       (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
       (β : C(Circle,Metric.closedBall (0 : Schoenflies.Plane) 1)) (hβ : ∀ t, ‖(β t).val‖=1)
       (c : Curve E) (hπc : ∀ t, M.cover.projection (c.map t)=f (β t)) :
       ∃ θ : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Circle),
       ∃ δ : C(Interval × {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Metric.closedBall (0 : Schoenflies.Plane) 1),
       ∃ G : C(Interval × {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},E),
       (∀ z, Complex.orthonormalBasisOneI.repr (‖z.val.val‖ • (θ z : ℂ))=z.val.val) ∧
       (∀ z, G (0,z)=c.map (θ z)) ∧
       (∀ p, M.cover.projection (G p)=f (δ p)) ∧
       (∀ z, (δ (1,z)).val=m.val+‖z.val.val‖ • ((β (θ z)).val-m.val)) ∧
       (∀ t z, ‖z.val.val‖=1 → δ (t,z)=β (θ z)) ∧
       (∀ p, (δ p).val = m.val + (1-p.1.val+p.1.val*‖p.2.val.val‖) • ((β (θ p.2)).val-m.val)) ∧
       (∀ p, δ p ≠ m) := by
        have hPolar : ∃ θ : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Circle),
         ∀ z, Complex.orthonormalBasisOneI.repr (‖z.val.val‖ • (θ z : ℂ)) = z.val.val := by
         let L := Complex.orthonormalBasisOneI.repr.symm
         have hne (z : {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0}) : L z.val.val ≠ 0 := by
           intro he
           apply z.property
           exact L.injective (he.trans (map_zero L).symm)
         let g : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},ℂ) :=
           ⟨fun z => L z.val.val,L.continuous.comp (continuous_subtype_val.comp continuous_subtype_val)⟩
         have hg : Continuous (fun z => NormedSpace.normalize (g z)) := by
           change Continuous (fun z => ‖g z‖⁻¹ • g z)
           exact (g.continuous.norm.inv₀ (fun z => norm_ne_zero_iff.mpr (hne z))).smul g.continuous
         let θ : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Circle) :=
           ⟨fun z => ⟨NormedSpace.normalize (g z),by change NormedSpace.normalize (g z) ∈ Metric.sphere (0:ℂ) 1; exact mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hne z))⟩,
           hg.subtype_mk (fun z => by change NormedSpace.normalize (g z) ∈ Metric.sphere (0:ℂ) 1; exact mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (hne z)))⟩
         refine ⟨θ,?_⟩
         intro z
         have hnorm : ‖g z‖ = ‖z.val.val‖ := L.norm_map _
         change Complex.orthonormalBasisOneI.repr (‖z.val.val‖ • NormedSpace.normalize (g z)) = z.val.val
         rw [← hnorm,NormedSpace.norm_smul_normalize]
         exact Complex.orthonormalBasisOneI.repr.apply_symm_apply _
        have hRadial (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
         (β : C(Circle,Metric.closedBall (0 : Schoenflies.Plane) 1)) (hβ : ∀ t, ‖(β t).val‖=1)
         (θ : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Circle)) :
         ∃ δ : C(Interval × {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Metric.closedBall (0 : Schoenflies.Plane) 1),
         (∀ z, δ (0,z) = β (θ z)) ∧
         (∀ z, (δ (1,z)).val = m.val + ‖z.val.val‖ • ((β (θ z)).val-m.val)) ∧
         (∀ p, δ p ≠ m) ∧
         (∀ t z, ‖z.val.val‖=1 → δ (t,z) = β (θ z)) ∧
         (∀ p, (δ p).val = m.val + (1-p.1.val+p.1.val*‖p.2.val.val‖) • ((β (θ p.2)).val-m.val)) := by
         let R : Interval × {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0} → ℝ :=
           fun p => 1-p.1.val+p.1.val*‖p.2.val.val‖
         have hR (p) : 0 < R p ∧ R p ≤ 1 := by
           obtain ⟨ht0,ht1⟩ := p.1.property
           have hr0 : 0 < ‖p.2.val.val‖ := norm_pos_iff.mpr p.2.property
           have hr1 : ‖p.2.val.val‖ ≤ 1 := by simpa only [dist_zero_right] using Metric.mem_closedBall.mp p.2.val.property
           dsimp [R]
           constructor <;> nlinarith
         have hv (p) : ‖m.val + R p • ((β (θ p.2)).val-m.val)‖ ≤ 1 := by
           have he : m.val + R p • ((β (θ p.2)).val-m.val) = (1-R p) • m.val + R p • (β (θ p.2)).val := by module
           rw [he]
           have hn := norm_add_le ((1-R p) • m.val) (R p • (β (θ p.2)).val)
           simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hR p).2),
             abs_of_pos (hR p).1,hβ,mul_one] at hn
           nlinarith [(hR p).2]
         have hcR : Continuous R := (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
           ((continuous_subtype_val.comp continuous_fst).mul
             ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).norm))
         have hδ : Continuous (fun p => m.val + R p • ((β (θ p.2)).val-m.val)) :=
           continuous_const.add (hcR.smul ((continuous_subtype_val.comp (β.continuous.comp (θ.continuous.comp continuous_snd))).sub continuous_const))
         let δ : C(Interval × {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Metric.closedBall (0 : Schoenflies.Plane) 1) :=
           ⟨fun p => ⟨m.val+R p • ((β (θ p.2)).val-m.val),by apply Metric.mem_closedBall.mpr; simpa only [dist_zero_right] using hv p⟩,
           hδ.subtype_mk (fun p => by apply Metric.mem_closedBall.mpr; simpa only [dist_zero_right] using hv p)⟩
         refine ⟨δ,?_,?_,?_,?_,?_⟩
         · intro z; apply Subtype.ext; simp [δ,R]
         · intro z; simp [δ,R]
         · intro p he
           have he' := congrArg Subtype.val he
           change m.val + R p • ((β (θ p.2)).val-m.val) = m.val at he'
           have hzero : R p • ((β (θ p.2)).val-m.val) = 0 := by
             apply add_left_cancel (a := m.val)
             simpa only [add_zero] using he'
           have hvm : (β (θ p.2)).val = m.val := by
             have := congrArg (fun x : Schoenflies.Plane => (R p)⁻¹ • x) hzero
             have hs : (β (θ p.2)).val-m.val=0 := by simpa [smul_smul,(hR p).1.ne'] using this
             exact sub_eq_zero.mp hs
           have hn := hβ (θ p.2)
           rw [hvm] at hn
           exact hm.ne hn
         · intro t z hz; apply Subtype.ext; simp [δ,R,hz]
         · intro p; rfl
        obtain ⟨θ,hθ⟩ := hPolar
        obtain ⟨δ,hδ0,hδ1,hδne,hδbound,hδformula⟩ := hRadial m hm β hβ θ
        have hcavoid (t) : M.cover.projection (c.map t) ∉ M.cover.branch := by
          intro hb
          rw [hπc] at hb
          have he := (honly (β t)).mp hb
          have hn := hβ t
          rw [he] at hn
          exact hm.ne hn
        let g : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},M.cover.unramifiedTotal) :=
          ⟨fun z => ⟨c.map (θ z),hcavoid (θ z)⟩,
           (c.embedded.continuous.comp θ.continuous).subtype_mk (fun z => hcavoid (θ z))⟩
        have hdavoid (p) : f (δ p) ∉ M.cover.branch := fun hb => hδne p ((honly (δ p)).mp hb)
        let H : C(Interval × {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},M.cover.unramifiedBase) :=
          ⟨fun p => ⟨f (δ p),hdavoid p⟩,(f.continuous.comp δ.continuous).subtype_mk hdavoid⟩
        have H0 (z) : H (0,z)=M.cover.unramifiedProjection (g z) := by
          apply Subtype.ext
          change f (δ (0,z)) = M.cover.projection (c.map (θ z))
          rw [hδ0,hπc]
        let L := M.cover.unramified_isCoveringMap.liftHomotopy H g H0
        let G : C(Interval × {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},E) :=
          ⟨fun p => (L p).val,continuous_subtype_val.comp L.continuous⟩
        refine ⟨θ,δ,G,hθ,?_,?_,hδ1,hδbound,hδformula,hδne⟩
        · intro z
          exact congrArg Subtype.val (M.cover.unramified_isCoveringMap.liftHomotopy_zero H g H0 z)
        · intro p
          exact congrArg Subtype.val (congrFun (M.cover.unramified_isCoveringMap.liftHomotopy_lifts H g H0) p)
      have hUnique (m v w : Schoenflies.Plane) (hm : ‖m‖ < 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
       (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
       (he : m + r • (v-m) = m + s • (w-m)) : r=s ∧ v=w := by
       have hvec : r • (v-m) = s • (w-m) := add_left_cancel he
       have horder (m v w : Schoenflies.Plane) (hm : ‖m‖ < 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
         (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
         (hvec : r • (v-m) = s • (w-m)) : ¬ r < s := by
         intro hlt
         have hlin : s • w = (s-r) • m + r • v := by
           calc
             s • w = s • (w-m) + s • m := by module
             _ = r • (v-m) + s • m := by rw [← hvec]
             _ = (s-r) • m + r • v := by module
         have hnorm := norm_add_le ((s-r) • m) (r • v)
         rw [← hlin] at hnorm
         simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hs,abs_of_pos hr,
           abs_of_pos (sub_pos.mpr hlt),hv,hw,mul_one] at hnorm
         nlinarith
       have hrs : r=s := le_antisymm (not_lt.mp (horder m w v hm hw hv s r hs hr hvec.symm))
         (not_lt.mp (horder m v w hm hv hw r s hr hs hvec))
       refine ⟨hrs,?_⟩
       rw [hrs] at hvec
       have hcancel : v-m = w-m := by
         have := congrArg (fun z : Schoenflies.Plane => s⁻¹ • z) hvec
         simpa [smul_smul,hs.ne'] using this
       exact add_right_cancel (show v + -m = w + -m from by simpa only [sub_eq_add_neg] using hcancel)
      obtain ⟨θ,δ,G,hθ,hG0,hπG,hδ1,hδbound,hδformula,hδne⟩ := hLift f m hm honly β hβ c hπc
      let F : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},E) :=
        ⟨fun z => G (1,z),G.continuous.comp (continuous_const.prodMk continuous_id)⟩
      have havoid (t : Interval) (z : {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0}) :
        M.cover.projection (G (t,z)) ∉ M.cover.branch := by
        rw [hπG]
        exact fun hb => hδne (t,z) ((honly (δ (t,z))).mp hb)
      let q (z : {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0}) : C(Interval,M.cover.unramifiedTotal) :=
        ⟨fun t => ⟨G (t,z),havoid t z⟩,
         (G.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk (fun t => havoid t z)⟩
      refine ⟨θ,F,hθ,?_,?_,?_,?_⟩
      · intro z w he
        have hd : δ (1,z)=δ (1,w) := hf.injective (by rw [← hπG,← hπG]; exact congrArg M.cover.projection he)
        have hrad : m.val+‖z.val.val‖ • ((β (θ z)).val-m.val) = m.val+‖w.val.val‖ • ((β (θ w)).val-m.val) :=
          (hδ1 z).symm.trans ((congrArg Subtype.val hd).trans (hδ1 w))
        obtain ⟨hr,hv⟩ := hUnique m.val (β (θ z)).val (β (θ w)).val hm (hβ _) (hβ _) _ _
          (norm_pos_iff.mpr z.property) (norm_pos_iff.mpr w.property) hrad
        have hcomp : M.cover.unramifiedProjection ∘ q z = M.cover.unramifiedProjection ∘ q w := by
          funext t
          apply Subtype.ext
          change M.cover.projection (G (t,z)) = M.cover.projection (G (t,w))
          rw [hπG,hπG]
          congr 1
          apply Subtype.ext
          rw [hδformula,hδformula,hr,hv]
        have hq : (q z : Interval → M.cover.unramifiedTotal) = q w := M.cover.unramified_isCoveringMap.eq_of_comp_eq
          (q z).continuous (q w).continuous hcomp 1 (Subtype.ext he)
        have hcz : c.map (θ z)=c.map (θ w) := by
          rw [← hG0,← hG0]
          exact congrArg Subtype.val (congrFun hq 0)
        have hangle := c.embedded.injective hcz
        apply Subtype.ext
        apply Subtype.ext
        rw [← hθ z,← hθ w,hr,hangle]
      · intro z; exact ⟨δ (1,z),hδ1 z,hπG (1,z)⟩
      · intro z; exact havoid 1 z
      · intro z hz
        have hconst : ∀ t t' : Interval, M.cover.unramifiedProjection (q z t)=M.cover.unramifiedProjection (q z t') := by
          intro t t'; apply Subtype.ext
          change M.cover.projection (G (t,z)) = M.cover.projection (G (t',z))
          rw [hπG,hπG,hδbound t z hz,hδbound t' z hz]
        have he := M.cover.unramified_isCoveringMap.const_of_comp (q z).continuous hconst 1 0
        exact (congrArg Subtype.val he).trans (hG0 z)
    have hExtend (f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S))
     (m : Metric.closedBall (0 : Schoenflies.Plane) 1) (_hm : ‖m.val‖<1)
     (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
     (β : C(Circle,Metric.closedBall (0 : Schoenflies.Plane) 1)) (hβ : ∀ t, ‖(β t).val‖=1)
     (θ : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},Circle))
     (F : C({z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val ≠ 0},E))
     (hFi : Function.Injective F)
     (hproj : ∀ z, ∃ d : Metric.closedBall (0 : Schoenflies.Plane) 1,
       d.val=m.val+‖z.val.val‖ • ((β (θ z)).val-m.val) ∧ M.cover.projection (F z)=f d)
     (havoid : ∀ z, M.cover.projection (F z) ∉ M.cover.branch) :
     ∃ T : C(Metric.closedBall (0 : Schoenflies.Plane) 1,E),
     IsEmbedding T ∧ (∀ z, T z.val=F z) ∧ M.cover.projection (T ⟨0,by simp⟩)=f m := by
     classical
     letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
     choose d hd hπ using hproj
     let o : Metric.closedBall (0 : Schoenflies.Plane) 1 := ⟨0,by simp⟩
     obtain ⟨w,hw⟩ := M.cover.projection_surjective (f m)
     have hwbranch : M.cover.projection w ∈ M.cover.branch := hw ▸ (honly m).mpr rfl
     let Q : Metric.closedBall (0 : Schoenflies.Plane) 1 → Metric.closedBall (0 : Schoenflies.Plane) 1 :=
       fun z => if hz : z.val=0 then m else d ⟨z,hz⟩
     let T : Metric.closedBall (0 : Schoenflies.Plane) 1 → E :=
       fun z => if hz : z.val=0 then w else F ⟨z,hz⟩
     have hQ0 : Q o=m := dite_eq_left rfl
     have hT0 : T o=w := dite_eq_left rfl
     have hQT (z) : M.cover.projection (T z)=f (Q z) := by
       by_cases hz : z.val=0
       · simp only [T,Q,dite_eq_left hz]; exact hw
       · simp only [T,Q,dite_eq_right hz]; exact hπ ⟨z,hz⟩
     have hbound (z) : ‖(Q z).val-m.val‖ ≤ ‖z.val‖*(1+‖m.val‖) := by
       by_cases hz : z.val=0
       · simp only [Q,dite_eq_left hz,sub_self,norm_zero,hz,zero_mul,le_refl]
       · simp only [Q,dite_eq_right hz]
         rw [hd]
         simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_norm]
         apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
         simpa only [hβ] using norm_sub_le (β (θ ⟨z,hz⟩)).val m.val
     have hQcont : ContinuousAt Q o := by
       rw [Metric.continuousAt_iff]
       intro ε hε
       have hK : 0 < 1+‖m.val‖ := by positivity
       refine ⟨ε/(1+‖m.val‖),div_pos hε hK,?_⟩
       intro z hz
       have hz' : ‖z.val‖ < ε/(1+‖m.val‖) := by simpa only [o,Subtype.dist_eq,dist_zero_right] using hz
       rw [hQ0]
       change dist (Q z).val m.val < ε
       rw [dist_eq_norm]
       exact (hbound z).trans_lt ((lt_div_iff₀ hK).mp hz')
     have hTcont : Continuous T := by
       rw [continuous_iff_continuousAt]
       intro z
       by_cases hz : z.val=0
       · have hzo : z=o := Subtype.ext hz
         subst z
         have hbase : Tendsto (fun z => M.cover.projection (T z)) (𝓝 o) (𝓝 (M.cover.projection w)) := by
           have h := (f.continuous.continuousAt.comp hQcont).tendsto
           change Tendsto (fun z => f (Q z)) (𝓝 o) (𝓝 (f (Q o))) at h
           rw [hQ0] at h
           rw [hw]
           exact h.congr' (Filter.Eventually.of_forall (fun z => (hQT z).symm))
         simpa only [ContinuousAt,hT0] using M.tendsto_branch_of_projection (𝓝 o) T w hwbranch hbase
       · let U : Set (Metric.closedBall (0 : Schoenflies.Plane) 1) := {z | z.val≠0}
         have hU : IsOpen U := isClosed_singleton.isOpen_compl.preimage continuous_subtype_val
         have hTU : ContinuousOn T U := by
           rw [continuousOn_iff_continuous_domRestrict]
           change Continuous (fun z : {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val≠0} => T z.val)
           have he : (fun z : {z : Metric.closedBall (0 : Schoenflies.Plane) 1 // z.val≠0} => T z.val) = F := by
             funext z
             exact dite_eq_right z.property
           rw [he]
           exact F.continuous
         exact (hTU z hz).continuousAt (hU.mem_nhds hz)
     have hTi : Function.Injective T := by
       intro z y he
       by_cases hz : z.val=0
       · by_cases hy : y.val=0
         · exact Subtype.ext (hz.trans hy.symm)
         · have hπeq := congrArg M.cover.projection he
           simp only [T,dite_eq_left hz,dite_eq_right hy] at hπeq
           exact False.elim (havoid ⟨y,hy⟩ (hπeq ▸ hwbranch))
       · by_cases hy : y.val=0
         · have hπeq := congrArg M.cover.projection he
           simp only [T,dite_eq_left hy,dite_eq_right hz] at hπeq
           exact False.elim (havoid ⟨z,hz⟩ (hπeq.symm ▸ hwbranch))
         · simp only [T,dite_eq_right hz,dite_eq_right hy] at he
           exact congrArg Subtype.val (hFi he)
     refine ⟨⟨T,hTcont⟩,(hTcont.isClosedEmbedding hTi).isEmbedding,?_,?_⟩
     · intro z; exact dite_eq_right z.property
     · change M.cover.projection (T o)=f m
       rw [hT0]; exact hw
    let e := hf.toHomeomorph
    have hmem (t) : M.cover.projection (c.map t) ∈ Set.range f := by
      have ht : c.map t ∈ c.image := ⟨t,rfl⟩
      rw [hc] at ht
      obtain ⟨z,_,he⟩ := ht
      exact ⟨z,he⟩
    let k : C(Circle,Set.range f) := ⟨fun t => ⟨M.cover.projection (c.map t),hmem t⟩,
      (M.cover.projection_continuous.comp c.embedded.continuous).subtype_mk hmem⟩
    let β : C(Circle,Metric.closedBall (0 : Schoenflies.Plane) 1) :=
      ⟨fun t => e.symm (k t),e.symm.continuous.comp k.continuous⟩
    have hπc (t) : M.cover.projection (c.map t)=f (β t) :=
      (congrArg Subtype.val (e.apply_symm_apply (k t))).symm
    have hβ (t) : ‖(β t).val‖=1 := by
      have ht : c.map t ∈ c.image := ⟨t,rfl⟩
      rw [hc] at ht
      obtain ⟨z,hz,he⟩ := ht
      have he' : β t=z := hf.injective ((hπc t).symm.trans he.symm)
      rw [he']; exact hz
    obtain ⟨θ,F,hθ,hFi,hproj,havoid,hboundary⟩ := hPuncture f hf m hm honly β hβ c hπc
    obtain ⟨T,hT,hTF,_⟩ := hExtend f m hm honly β hβ θ F hFi hproj havoid
    refine ⟨T,hT,?_⟩
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hz1 : ‖z.val‖=1 := by simpa only [Set.mem_ofPred_eq,Metric.mem_sphere,dist_zero_right] using hz
      have hz0 : z.val≠0 := by intro he; rw [he,norm_zero] at hz1; norm_num at hz1
      rw [hTF ⟨z,hz0⟩,hboundary ⟨z,hz0⟩ hz1]
      exact ⟨θ ⟨z,hz0⟩,rfl⟩
    · rintro ⟨t,rfl⟩
      have hn : ‖Complex.orthonormalBasisOneI.repr (t:ℂ)‖=1 :=
        (Complex.orthonormalBasisOneI.repr.norm_map _).trans t.norm_coe
      let z : Metric.closedBall (0 : Schoenflies.Plane) 1 :=
        ⟨Complex.orthonormalBasisOneI.repr (t:ℂ),by apply Metric.mem_closedBall.mpr; simpa only [dist_zero_right] using hn.le⟩
      have hz0 : z.val≠0 := by intro he; have := hn; change ‖z.val‖=1 at this; rw [he,norm_zero] at this; norm_num at this
      have hz1 : ‖z.val‖=1 := hn
      have hangle : θ ⟨z,hz0⟩=t := by
        apply Subtype.ext
        apply Complex.orthonormalBasisOneI.repr.injective
        have he := hθ ⟨z,hz0⟩
        simpa only [hz1,one_smul] using he
      refine ⟨z,?_,?_⟩
      · exact mem_sphere_zero_iff_norm.mpr hz1
      · rw [hTF ⟨z,hz0⟩,hboundary ⟨z,hz0⟩ hz1,hangle]
  obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hdUb,hdVb,hdUi,hdVi,hclU,hclV⟩ := hSides a
  have hPositive (W : Set S) (d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure W)
    (hcl : closure W = W ∪ a.image) : 0 < (M.cover.branch.filter (· ∈ W)).card := by
    by_contra hn
    have hz : (M.cover.branch.filter (· ∈ W)).card = 0 := by omega
    have hnone (b : S) (hb : b ∈ M.cover.branch) : b ∉ W := by
      intro hW
      have : 0 < (M.cover.branch.filter (· ∈ W)).card :=
        Finset.card_pos.mpr ⟨b,Finset.mem_filter.mpr ⟨hb,hW⟩⟩
      omega
    let f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S) :=
      ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
    have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp d.isEmbedding
    have havoid (z) : f z ∉ M.cover.branch := by
      intro hb
      have hmem : f z ∈ W ∪ a.image := hcl ▸ (d z).property
      rcases hmem with hW | hA
      · exact hnone (f z) hb hW
      · exact Set.disjoint_left.mp a.avoids_branch hA hb
    let k : C(Circle,closure W) := ⟨fun t => ⟨a.curve.map t,by rw [hcl]; exact Or.inr ⟨t,rfl⟩⟩,
      a.curve.embedded.continuous.subtype_mk (fun t => by rw [hcl]; exact Or.inr ⟨t,rfl⟩)⟩
    let β : C(Circle,Metric.closedBall (0 : Schoenflies.Plane) 1) :=
      ⟨fun t => d.symm (k t),d.symm.continuous.comp k.continuous⟩
    have hβ : Set.range (f.comp β) = a.image := by
      have he : (f.comp β).toFun = a.curve.map := by
        funext t
        change (d (d.symm (k t))).val = a.curve.map t
        rw [d.apply_symm_apply]; rfl
      exact congrArg Set.range he
    apply hNoCircle f hf havoid β c.val
    rw [hβ]
    exact hc

  have hCount (W : Set S) (d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure W)
    (hcl : closure W=W ∪ a.image)
    (hdb : ∀ z, (d z:S) ∈ a.image ↔ ‖z.val‖=1)
    (hdi : ∀ z, (d z:S) ∈ W ↔ ‖z.val‖<1) :
    1 < (M.cover.branch.filter (· ∈ W)).card := by
    have hpos := hPositive W d hcl
    by_contra hn
    have hcard : (M.cover.branch.filter (· ∈ W)).card=1 := by omega
    obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hcard
    have hbfilter : b ∈ M.cover.branch.filter (· ∈ W) := hb.symm ▸ Finset.mem_singleton_self b
    obtain ⟨hbB,hbW⟩ := Finset.mem_filter.mp hbfilter
    let f : C(Metric.closedBall (0 : Schoenflies.Plane) 1,S) :=
      ⟨fun z => (d z).val,continuous_subtype_val.comp d.continuous⟩
    have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp d.isEmbedding
    let m := d.symm ⟨b,subset_closure hbW⟩
    have hfm : f m=b := congrArg Subtype.val (d.apply_symm_apply ⟨b,subset_closure hbW⟩)
    have hm : ‖m.val‖<1 := (hdi m).mp (by change f m ∈ W; rw [hfm]; exact hbW)
    have honly (z) : f z ∈ M.cover.branch ↔ z=m := by
      constructor
      · intro hzB
        have hzcl : f z ∈ W ∪ a.image := hcl ▸ (d z).property
        have hzW : f z ∈ W := hzcl.resolve_right (fun hzA => Set.disjoint_left.mp a.avoids_branch hzA hzB)
        have hzfilter : f z ∈ M.cover.branch.filter (· ∈ W) := Finset.mem_filter.mpr ⟨hzB,hzW⟩
        rw [hb] at hzfilter
        have hzb : f z=b := Finset.mem_singleton.mp hzfilter
        exact hf.injective (hzb.trans hfm.symm)
      · intro he; rw [he,hfm]; exact hbB
    have hboundary : f '' {z : Metric.closedBall (0 : Schoenflies.Plane) 1 | ‖z.val‖=1} = a.image := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩; exact (hdb z).mpr hz
      · intro hy
        let z := d.symm ⟨y,by rw [hcl]; exact Or.inr hy⟩
        have hfy : f z=y := congrArg Subtype.val (d.apply_symm_apply _)
        exact ⟨z,(hdb z).mp (by change f z ∈ a.image; rw [hfy]; exact hy),hfy⟩
    apply c.property
    apply hDisc f hf m hm honly c.val
    rw [hboundary]
    exact hc
  have hm := hCount U dU hclU hdUb hdUi
  have hn := hCount V dV hclV hdVb hdVi
  have hnot (b : S) (hb : b ∈ M.cover.branch) : b ∈ V ↔ b ∉ U := by
    have hba : b ∉ a.image := fun he => Set.disjoint_left.mp a.avoids_branch he hb
    have hex : b ∈ U ∪ V := by rw [hcover]; exact hba
    exact ⟨fun hV hU => Set.disjoint_left.mp hUV hU hV,fun hU => hex.resolve_left hU⟩
  have hfilter : M.cover.branch.filter (· ∈ V) = M.cover.branch.filter (fun b => b ∉ U) :=
    Finset.filter_congr (fun b hb => hnot b hb)
  refine ⟨(M.cover.branch.filter (· ∈ U)).card,(M.cover.branch.filter (· ∈ V)).card,hm,hn,?_,?_⟩
  · rw [hfilter,Finset.card_filter_add_card_filter_not,M.cover.branch_card]
  · exact ⟨U,V,hUo,hVo,hUc,hVc,hUc.nonempty,hVc.nonempty,hUV,hcover,rfl,rfl⟩
end CurveComplex.HyperellipticModel
