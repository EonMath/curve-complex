import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualSphereTwoTraceComparisonAnnulusLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreOuterTraceClearanceLocal
import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualGivenCoreUniformTargetBandLocal
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 50000000

-- The new source cylinders are constructed on the SAME G outer traces and the
-- actual uniform near-core levels; no desired annulus is supplied as an input.
example (M : HyperellipticModel E S)
    (G : C(Circle × Interval,Circle × Interval)) (hGe : IsEmbedding G)
    (r : Circle ≃ₜ Circle)
    (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩)) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ hεq : ε < 1/4, ∃ Φ : C(Circle × Interval,S), IsEmbedding Φ ∧
      (∀ z (u : Interval), |(u:ℝ)-1/2| ≤ ε → ∃ p : Circle × Interval,
        0 < (p.2:ℝ) ∧ (p.2:ℝ)<1 ∧ G p=(z,u)) ∧
      ∀ a b : Bool, ∃ q : C(Circle × Interval,S), IsEmbedding q ∧
        Set.range (fun z : Circle => q (z,0))=
          Set.range (fun z : Circle => Φ (G (z,if a then 1 else 0))) ∧
        Set.range (fun z : Circle => q (z,1))=
          Set.range (fun z : Circle => Φ (z,⟨1/2+(if b then ε else -ε),by
            split_ifs <;> constructor <;> linarith⟩)) ∧
        IsComplementComponent
          (Set.range (fun z : Circle => Φ (G (z,if a then 1 else 0))) ∪
            Set.range (fun z : Circle => Φ (z,⟨1/2+(if b then ε else -ε),by
              split_ifs <;> constructor <;> linarith⟩)))
          (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
  audit_main14_base3
    have actual_curve_closedSides (a : Curve S) :
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
      have hJordan (a : Curve S) :
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
         map := fun t => M.sphere (a.map (b t))
         continuous := M.sphere.continuous.comp (a.embedded.continuous.comp b.continuous)
         injective_except_ends := fun s t he => hcoll s t (a.embedded.injective (M.sphere.injective he))
         closed := by change M.sphere (a.map (Circle.exp (2*Real.pi*0))) = M.sphere (a.map (Circle.exp (2*Real.pi*1))); simp }
       refine ⟨c,?_⟩
       change Set.range (M.sphere ∘ (a.map ∘ b)) = M.sphere '' Set.range a.map
       rw [Set.range_comp, hb.range_comp]
      obtain ⟨c,hc⟩ := hJordan a
      let d : Curve CurveComplex.SpherePort.Sphere :=
        ⟨M.sphere ∘ a.map,M.sphere.isEmbedding.comp a.embedded⟩
      obtain ⟨p,hp⟩ := CurveComplex.sphere_embedded_circle_omits_point d
      have hd : d.image = M.sphere '' a.image := by
        change Set.range (M.sphere ∘ a.map) = M.sphere '' Set.range a.map
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
    have actual_sphere_pair_annulus (c d : Curve S) (w : S)
        (hwc : w ∉ c.image) (hwd : w ∉ d.image) (hd : Disjoint c.image d.image) :
        ∃ q : C(Circle × Interval,S), Topology.IsEmbedding q ∧
          Set.range (fun z : Circle => q (z,0))=c.image ∧
          Set.range (fun z : Circle => q (z,1))=d.image ∧
          IsComplementComponent (c.image ∪ d.image)
            (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
      classical
      -- Construct the connector from metric compactness, not an input arc certificate.
      have closest_connector (C K : Set Plane) (hC : IsCompact C) (hK : IsCompact K)
          (hnC : C.Nonempty) (hnK : K.Nonempty) (hCK : Disjoint C K) :
          ∃ a ∈ C, ∃ b ∈ K, a ≠ b ∧
            Disjoint (openSegment ℝ a b) (C ∪ K) := by
        obtain ⟨p, hp, hmin⟩ := (hC.prod hK).exists_isMinOn (hnC.prod hnK)
          (continuous_fst.dist continuous_snd).continuousOn
        have hab : p.1 ≠ p.2 := hCK.ne_of_mem hp.1 hp.2
        have hpos : 0 < dist p.1 p.2 := dist_pos.mpr hab
        refine ⟨p.1,hp.1,p.2,hp.2,hab,Set.disjoint_left.mpr ?_⟩
        intro x hx hmem
        rw [openSegment_eq_image_lineMap] at hx
        obtain ⟨t,ht,rfl⟩ := hx
        rcases hmem with hc | hk
        · have hm := hmin (a := (AffineMap.lineMap p.1 p.2 t,p.2)) ⟨hc,hp.2⟩
          change dist p.1 p.2 ≤ dist (AffineMap.lineMap p.1 p.2 t) p.2 at hm
          rw [dist_lineMap_right,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ht.2)] at hm
          nlinarith [mul_pos ht.1 hpos]
        · have hm := hmin (a := (p.1,AffineMap.lineMap p.1 p.2 t)) ⟨hp.1,hk⟩
          change dist p.1 p.2 ≤ dist p.1 (AffineMap.lineMap p.1 p.2 t) at hm
          rw [dist_left_lineMap,Real.norm_eq_abs,abs_of_pos ht.1] at hm
          nlinarith [mul_pos (sub_pos.mpr ht.2) hpos]
      have nested_connector (C K : Set Plane) (hC : IsSeparating C)
          (hK : IsSeparating K) (hKC : K ⊆ inside C) (hCK : C ⊆ outside K) :
          ∃ a ∈ C, ∃ b ∈ K, IsArcBetween (segment ℝ a b) a b ∧
            openSegment ℝ a b ⊆ inside C ∩ outside K := by
        have hdisj : Disjoint C K := Set.disjoint_left.mpr fun x hxC hxK =>
          (hKC hxK).1 hxC
        obtain ⟨a,ha,b,hb,hab,havoid⟩ := closest_connector C K
          hC.isJordanCurve.isCompact hK.isJordanCurve.isCompact
          hC.isJordanCurve.nonempty hK.isJordanCurve.nonempty hdisj
        have hcont : Continuous (AffineMap.lineMap a b : ℝ → Plane) := by fun_prop
        have harc : IsArcBetween (segment ℝ a b) a b := by
          refine ⟨AffineMap.lineMap a b,hcont.continuousOn,
            (AffineMap.lineMap_injective ℝ hab).injOn,?_,?_,?_⟩
          · exact (segment_eq_image_lineMap ℝ a b).symm
          · simp
          · simp
        have hconn : IsPreconnected (openSegment ℝ a b) := by
          rw [openSegment_eq_image_lineMap]
          exact isPreconnected_Ioo.image _ hcont.continuousOn
        have hnotC : openSegment ℝ a b ⊆ Cᶜ := fun x hx hc =>
          Set.disjoint_left.mp havoid hx (Or.inl hc)
        have hnotK : openSegment ℝ a b ⊆ Kᶜ := fun x hx hk =>
          Set.disjoint_left.mp havoid hx (Or.inr hk)
        have haClosure : a ∈ closure (openSegment ℝ a b) :=
          segment_subset_closure_openSegment (left_mem_segment ℝ a b)
        have hbClosure : b ∈ closure (openSegment ℝ a b) :=
          segment_subset_closure_openSegment (right_mem_segment ℝ a b)
        have hinside : openSegment ℝ a b ⊆ inside C := by
          have hs : openSegment ℝ a b ⊆ inside C ∪ outside C := by
            rw [inside_union_outside];exact hnotC
          rcases hconn.subset_or_subset hC.isOpen_inside hC.isOpen_outside
            disjoint_inside_outside hs with hi | ho
          · exact hi
          · have he := closure_mono ho hbClosure
            rw [closure_eq_self_union_frontier,hC.frontier_outside] at he
            rcases he with he | he
            · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside (hKC hb) he)
            · exact False.elim ((hKC hb).1 he)
        have houtside : openSegment ℝ a b ⊆ outside K := by
          have hs : openSegment ℝ a b ⊆ inside K ∪ outside K := by
            rw [inside_union_outside];exact hnotK
          rcases hconn.subset_or_subset hK.isOpen_inside hK.isOpen_outside
            disjoint_inside_outside hs with hi | ho
          · have he := closure_mono hi haClosure
            rw [closure_eq_self_union_frontier,hK.frontier_inside] at he
            rcases he with he | he
            · exact False.elim (Set.disjoint_left.mp disjoint_inside_outside he (hCK ha))
            · exact False.elim ((hCK ha).1 he)
          · exact ho
        exact ⟨a,ha,b,hb,harc,fun x hx => ⟨hinside hx,houtside hx⟩⟩
      have nested_proper_connector (C K : Set Plane) (hC : IsSeparating C)
          (hK : IsSeparating K) (hKC : K ⊆ inside C) (hCK : C ⊆ outside K) :
          ∃ a ∈ C, ∃ b ∈ K, IsArcBetween (segment ℝ a b) a b ∧
            segment ℝ a b ∩ C = {a} ∧ segment ℝ a b ∩ K = {b} ∧
            segment ℝ a b \ {a,b} ⊆ inside C ∩ outside K := by
        obtain ⟨a,ha,b,hb,harc,hgap⟩ := nested_connector C K hC hK hKC hCK
        have hsplit (x : Plane) (hx : x ∈ segment ℝ a b) :
            x = a ∨ x = b ∨ x ∈ openSegment ℝ a b := by
          rw [← insert_endpoints_openSegment] at hx
          exact hx
        refine ⟨a,ha,b,hb,harc,?_,?_,?_⟩
        · apply Set.Subset.antisymm
          · rintro x ⟨hx,hxc⟩
            rcases hsplit x hx with rfl | rfl | hx
            · simp
            · exact False.elim ((hKC hb).1 hxc)
            · exact False.elim ((hgap hx).1.1 hxc)
          · intro x hx
            have he : x = a := Set.mem_singleton_iff.mp hx
            rw [he]
            exact ⟨left_mem_segment ℝ a b,ha⟩
        · apply Set.Subset.antisymm
          · rintro x ⟨hx,hxk⟩
            rcases hsplit x hx with rfl | rfl | hx
            · exact False.elim ((hCK ha).1 hxk)
            · simp
            · exact False.elim ((hgap hx).2.1 hxk)
          · intro x hx
            have he : x = b := Set.mem_singleton_iff.mp hx
            rw [he]
            exact ⟨right_mem_segment ℝ a b,hb⟩
        · rintro x ⟨hx,hends⟩
          rcases hsplit x hx with rfl | rfl | hx
          · exact False.elim (hends (by simp))
          · exact False.elim (hends (by simp))
          · exact hgap hx
      have actual_joining_arc : ∃ j : C(Interval,S), Topology.IsEmbedding j ∧
          j 0 ∈ c.image ∧ j 1 ∈ d.image ∧
          ∀ t : Interval, 0 < (t : ℝ) → (t : ℝ) < 1 →
            j t ∉ c.image ∪ d.image := by
        let : T2Space S := M.sphere.symm.t2Space
        have havoidw (p : Curve S) (hp : w ∉ p.image) (z : Circle) : p.map z ≠ w := by
          intro he
          exact hp (he ▸ Set.mem_range_self z)
        let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
        let chart := stereographic' 2 (M.sphere w)
        have hcsource : chart.source = {M.sphere w}ᶜ := stereographic'_source _
        have hctarget : chart.target = Set.univ := stereographic'_target _
        let es : {z : S // z ≠ w} ≃ₜ chart.source :=
          M.sphere.subtype (fun z => by simp only [hcsource,Set.mem_compl_iff,
            Set.mem_singleton_iff,M.sphere.injective.eq_iff])
        let e : {z : S // z ≠ w} ≃ₜ Plane := es.trans
          (chart.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr hctarget).trans
            (Homeomorph.Set.univ _)))
        let Cmap : Circle → Plane := fun z => e ⟨c.map z,havoidw c hwc z⟩
        let Kmap : Circle → Plane := fun z => e ⟨d.map z,havoidw d hwd z⟩
        have hCc : Continuous Cmap := e.continuous.comp
          (c.embedded.continuous.subtype_mk (havoidw c hwc))
        have hKc : Continuous Kmap := e.continuous.comp
          (d.embedded.continuous.subtype_mk (havoidw d hwd))
        have hdisj : Disjoint (Set.range Cmap) (Set.range Kmap) := by
          apply Set.disjoint_left.mpr
          rintro x ⟨z,rfl⟩ ⟨v,hv⟩
          have he := congrArg Subtype.val (e.injective hv)
          exact Set.disjoint_left.mp hd ⟨z,rfl⟩ ⟨v,he⟩
        obtain ⟨a,ha,b,hb,hab,hinter⟩ := closest_connector
          (Set.range Cmap) (Set.range Kmap) (isCompact_range hCc) (isCompact_range hKc)
          ⟨Cmap 1,1,rfl⟩ ⟨Kmap 1,1,rfl⟩ hdisj
        have hline : Continuous (AffineMap.lineMap a b : ℝ → Plane) := by fun_prop
        let j : C(Interval,S) := ⟨fun t => (e.symm (AffineMap.lineMap a b (t : ℝ))).val,
          continuous_subtype_val.comp (e.symm.continuous.comp
            (hline.comp continuous_subtype_val))⟩
        have hj : Function.Injective j := by
          intro t u he
          have he' := congrArg e (Subtype.ext he)
          apply Subtype.ext
          exact AffineMap.lineMap_injective ℝ hab (by simpa [j] using he')
        refine ⟨j,(j.continuous.isClosedEmbedding hj).isEmbedding,?_,?_,?_⟩
        · obtain ⟨z,hz⟩ := ha
          refine ⟨z,?_⟩
          change c.map z = (e.symm (AffineMap.lineMap a b (0:ℝ))).val
          simp only [AffineMap.lineMap_apply_zero]
          rw [← hz]
          exact (congrArg Subtype.val (e.symm_apply_apply ⟨c.map z,havoidw c hwc z⟩)).symm
        · obtain ⟨z,hz⟩ := hb
          refine ⟨z,?_⟩
          change d.map z = (e.symm (AffineMap.lineMap a b (1:ℝ))).val
          simp only [AffineMap.lineMap_apply_one]
          rw [← hz]
          exact (congrArg Subtype.val (e.symm_apply_apply ⟨d.map z,havoidw d hwd z⟩)).symm
        · intro t ht0 ht1 hmem
          have ht : AffineMap.lineMap a b (t : ℝ) ∈ openSegment ℝ a b :=
            lineMap_mem_openSegment ℝ a b ⟨ht0,ht1⟩
          apply Set.disjoint_left.mp hinter ht
          rcases hmem with ⟨z,hz⟩ | ⟨z,hz⟩
          · left;refine ⟨z,?_⟩
            have he : (⟨c.map z,havoidw c hwc z⟩ : {z : S // z ≠ w}) =
                e.symm (AffineMap.lineMap a b (t : ℝ)) := Subtype.ext hz
            exact (congrArg e he).trans (e.apply_symm_apply _)
          · right;refine ⟨z,?_⟩
            have he : (⟨d.map z,havoidw d hwd z⟩ : {z : S // z ≠ w}) =
                e.symm (AffineMap.lineMap a b (t : ℝ)) := Subtype.ext hz
            exact (congrArg e he).trans (e.apply_symm_apply _)
      have endpoint_radial_core (c : Curve S) (f : C(Interval,S))
          (hf : Topology.IsEmbedding f) (hfc : f 0 ∈ c.image)
          (hunique : ∀ t : Interval, f t ∈ c.image → t = 0)
          (E : OpenPartialHomeomorph S Plane) (hE0 : E (f 0) = 0)
          (U : Set S) (hU : IsOpen U) (hpU : f 0 ∈ U) (hUE : U ⊆ E.source) :
          ∃ γ : Option Bool → Interval → Plane,
            ∃ R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E '' U),
              R.vector (some true) = -R.vector (some false) ∧
              ∀ x, x ∈ E.source → ‖R.H (E x)‖ ≤ R.coreRadius →
                (x ∈ c.image ↔ R.H (E x) ∈
                  segment ℝ (0:Plane) (R.vector (some false)) ∪
                  segment ℝ (0:Plane) (R.vector (some true))) ∧
                (x ∈ Set.range f ↔ R.H (E x) ∈
                  segment ℝ (0:Plane) (R.vector none)) := by
        let : T2Space S := M.sphere.symm.t2Space
        obtain ⟨q,hq⟩ := hfc
        let ψ : ℝ → S := fun t => c.map (q * Circle.exp t)
        have hψ : Continuous ψ := c.embedded.continuous.comp
          (continuous_const.mul Circle.exp.continuous)
        have hψ0 : ψ 0 = f 0 := by simp [ψ,hq]
        obtain ⟨rC,hrC,hballC⟩ := Metric.isOpen_iff.mp (hU.preimage hψ) 0
          (by simpa [hψ0] using hpU)
        let ε := min rC Real.pi / 2
        have hε : 0 < ε := half_pos (lt_min hrC Real.pi_pos)
        have hεr : ε < rC := by dsimp [ε];linarith [min_le_left rC Real.pi]
        have hεπ : ε < Real.pi := by dsimp [ε];linarith [min_le_right rC Real.pi,Real.pi_pos]
        have hSmall (t : ℝ) (ht : t ∈ Icc (-ε) ε) : ψ t ∈ U := by
          apply hballC
          rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
          constructor <;> linarith [ht.1,ht.2]
        obtain ⟨rF,hrF,hballF⟩ := Metric.isOpen_iff.mp (hU.preimage f.continuous) (0:Interval) hpU
        let r : ℝ := min rF 1 / 2
        have hr : 0 < r := half_pos (lt_min hrF zero_lt_one)
        have hrr : r < rF := by dsimp [r];linarith [min_le_left rF 1]
        have hr1 : r < 1 := by dsimp [r];linarith [min_le_right rF 1]
        let fp : Interval → Interval := fun t => ⟨r*(t:ℝ),
          ⟨mul_nonneg hr.le t.property.1,by nlinarith [t.property.2]⟩⟩
        have hfp : Continuous fp := (continuous_const.mul continuous_subtype_val).subtype_mk _
        have hfpU (t : Interval) : f (fp t) ∈ U := by
          apply hballF
          rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
          change |r*(t:ℝ)-0| < rF
          rw [sub_zero,abs_of_nonneg (mul_nonneg hr.le t.property.1)]
          nlinarith [t.property.2]
        let θ : Bool → Interval → ℝ := fun b t => if b then ε*(t:ℝ) else -(ε*(t:ℝ))
        have hθ (b : Bool) (t : Interval) : θ b t ∈ Icc (-ε) ε := by
          dsimp [θ];split_ifs <;> constructor <;> nlinarith [t.property.1,t.property.2]
        let φ : Option Bool → Interval → S := fun j t =>
          match j with | none => f (fp t) | some b => ψ (θ b t)
        have hφU (j : Option Bool) (t : Interval) : φ j t ∈ U := by
          cases j with
          | none => exact hfpU t
          | some b => exact hSmall _ (hθ b t)
        have hφ0 (j : Option Bool) : φ j 0 = f 0 := by
          cases j <;> simp [φ,fp,θ,hψ0]
        have hφc (j : Option Bool) : Continuous (φ j) := by
          cases j with
          | none => exact f.continuous.comp hfp
          | some b => exact hψ.comp (by dsimp [θ];split_ifs <;> fun_prop)
        have hφi (j : Option Bool) : Function.Injective (φ j) := by
          cases j with
          | none =>
            intro t s he
            have hh := congrArg Subtype.val (hf.injective he)
            apply Subtype.ext
            change r*(t:ℝ)=r*(s:ℝ) at hh
            nlinarith
          | some b =>
            intro t s he
            have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
              (hθ b t) (hθ b s) (mul_left_cancel (c.embedded.injective he))
            apply Subtype.ext
            dsimp [θ] at hang;split_ifs at hang <;> nlinarith
        have hφmeet (i j : Option Bool) (hij : i ≠ j) (t s : Interval)
            (he : φ i t = φ j s) : φ i t = f 0 := by
          cases i with
          | none =>
            cases j with
            | none => exact False.elim (hij rfl)
            | some b =>
              have hu := hunique (fp t) ⟨q * Circle.exp (θ b s),he.symm⟩
              change f (fp t) = f 0
              rw [hu]
          | some b =>
            cases j with
            | none =>
              have hu := hunique (fp s) ⟨q * Circle.exp (θ b t),he⟩
              rw [he];change f (fp s)=f 0;rw [hu]
            | some k =>
              have hbk : b ≠ k := fun h => hij (congrArg some h)
              have hang := Circle.exp_injOn_Icc (by linarith : ε - -ε < 2*Real.pi)
                (hθ b t) (hθ k s) (mul_left_cancel (c.embedded.injective he))
              have ht0 : (t:ℝ)=0 := by
                cases b <;> cases k
                · exact False.elim (hbk rfl)
                · simp [θ] at hang;nlinarith [s.property.1,t.property.1]
                · simp [θ] at hang;nlinarith [s.property.1,t.property.1]
                · exact False.elim (hbk rfl)
              have ht : t=0 := Subtype.ext ht0
              rw [ht];exact hφ0 (some b)
        let γ : Option Bool → Interval → Plane := fun j t => E (φ j t)
        have hγc (j : Option Bool) : Continuous (γ j) :=
          E.continuousOn.comp_continuous (hφc j) (fun t => hUE (hφU j t))
        have hγi (j : Option Bool) : Function.Injective (γ j) := fun t s he =>
          hφi j (E.injOn (hUE (hφU j t)) (hUE (hφU j s)) he)
        have hγ0 (j : Option Bool) : γ j 0 = 0 := by simp only [γ,hφ0,hE0]
        have hγmeet (i j : Option Bool) (hij : i ≠ j) :
            Set.range (γ i) ∩ Set.range (γ j) = {0} := by
          apply Set.Subset.antisymm
          · rintro x ⟨⟨t,rfl⟩,⟨s,he⟩⟩
            have hs := E.injOn (hUE (hφU j s)) (hUE (hφU i t)) he
            change E (φ i t) = 0
            rw [hφmeet i j hij t s hs.symm,hE0]
          · rintro x rfl;exact ⟨⟨0,hγ0 i⟩,⟨0,hγ0 j⟩⟩
        let angles : Set Circle := (fun t : ℝ => q * Circle.exp t) '' Ioo (-ε) ε
        have hAngles : IsOpen angles :=
          ((isOpenMap_mul_left q).comp Circle.isCoveringMap_exp.isOpenMap) _ isOpen_Ioo
        let badC : Set S := c.map '' anglesᶜ
        let badF : Set S := f '' {t : Interval | r ≤ (t:ℝ)}
        let bad : Set S := badC ∪ badF
        have hBad : IsClosed bad :=
          ((hAngles.isClosed_compl.isCompact.image c.embedded.continuous).isClosed).union
            (((isClosed_le continuous_const continuous_subtype_val).isCompact.image f.continuous).isClosed)
        have hpBad : f 0 ∉ bad := by
          rintro (⟨z,hz,hzp⟩ | ⟨t,ht,he⟩)
          · have hzq : z=q := c.embedded.injective (hzp.trans hq.symm)
            apply hz;exact ⟨0,⟨by linarith,hε⟩,by simpa using hzq.symm⟩
          · have ht0 : t=0 := hf.injective he
            subst t;change r ≤ 0 at ht;linarith
        let W : Set S := U \ bad
        have hW : IsOpen W := hU.sdiff hBad
        have hpW : f 0 ∈ W := ⟨hpU,hpBad⟩
        have hWE : W ⊆ E.source := fun x hx => hUE hx.1
        have hPlaneW : IsOpen (E '' W) := E.isOpen_image_of_subset_source hW hWE
        obtain ⟨R₀,hRop⟩ := prescribed_pair_finite_actual_star_radialization_zero γ
          (fun j => (hγc j).isClosedEmbedding (hγi j)) hγ0 hγmeet
          (some false) (some true) (by simp) (E '' W) hPlaneW ⟨f 0,hpW,hE0⟩
        let R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 (E '' U) :=
          {R₀ with support_subset := R₀.support_subset.trans (Set.image_mono Set.sdiff_subset)}
        have hNotBad (x : S) (hxE : x ∈ E.source)
            (hxN : ‖R.H (E x)‖ ≤ R.coreRadius) : x ∉ bad := by
          intro hxBad
          have hxPlane : E x ∉ E '' W := by
            rintro ⟨y,hy,he⟩
            have hyx := E.injOn (hWE hy) hxE he
            exact hy.2 (hyx.symm ▸ hxBad)
          have hxOut : E x ∉ Metric.ball (0:Plane) R₀.supportRadius := by
            intro hx;exact hxPlane (R₀.support_subset (Metric.ball_subset_closedBall hx))
          have hxFix : R.H (E x)=E x := R₀.fixes_exterior _ hxOut
          rw [hxFix] at hxN
          exact hxPlane (R₀.support_subset (by
            rw [Metric.mem_closedBall,dist_zero_right];exact hxN.trans R₀.core_lt_support.le))
        have hCcover (x : S) (hx : x ∈ c.image) (hxB : x ∉ badC) :
            ∃ b : Bool, ∃ t : Interval, γ (some b) t = E x := by
          obtain ⟨z,hzx⟩ := hx
          have hz : z ∈ angles := by by_contra hn;exact hxB ⟨z,hn,hzx⟩
          obtain ⟨a,ha,haz⟩ := hz
          change q * Circle.exp a = z at haz
          by_cases hapos : 0 ≤ a
          · let t : Interval := ⟨a/ε,⟨div_nonneg hapos hε.le,(div_le_one hε).mpr ha.2.le⟩⟩
            refine ⟨true,t,?_⟩
            have hmul : ε*(t:ℝ)=a := by dsimp [t];field_simp
            change E (c.map (q * Circle.exp (ε*(t:ℝ))))=E x
            rw [hmul,haz,hzx]
          · let t : Interval := ⟨(-a)/ε,⟨div_nonneg (by linarith) hε.le,
              (div_le_one hε).mpr (by linarith [ha.1])⟩⟩
            refine ⟨false,t,?_⟩
            have hmul : -(ε*(t:ℝ))=a := by dsimp [t];field_simp
            change E (c.map (q * Circle.exp (-(ε*(t:ℝ)))))=E x
            rw [hmul,haz,hzx]
        have hFcover (x : S) (hx : x ∈ Set.range f) (hxB : x ∉ badF) :
            ∃ t : Interval, γ none t = E x := by
          obtain ⟨s,hs⟩ := hx
          have hslt : (s:ℝ)<r := by by_contra hn;exact hxB ⟨s,le_of_not_gt hn,hs⟩
          let t : Interval := ⟨(s:ℝ)/r,⟨div_nonneg s.property.1 hr.le,
            (div_le_one hr).mpr hslt.le⟩⟩
          have hfpEq : fp t=s := by apply Subtype.ext;dsimp [fp,t];field_simp
          refine ⟨t,?_⟩
          change E (f (fp t))=E x
          rw [hfpEq,hs]
        have hToRay (j : Option Bool) (x : S) (hxN : ‖R.H (E x)‖ ≤ R.coreRadius)
            (t : Interval) (htx : γ j t=E x) :
            R.H (E x) ∈ segment ℝ (0:Plane) (R.vector j) := by
          have hcut : (t:ℝ) ≤ (R.cut j:ℝ) := by
            by_contra hn
            have htail : R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
              ⟨γ j t,⟨t,(lt_of_not_ge hn).le,rfl⟩,rfl⟩
            exact Set.disjoint_left.mp (R.excludes_tails j) htail (by
              rw [htx,Metric.mem_closedBall,dist_zero_right];exact hxN)
          have hh : R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) :=
            ⟨γ j t,⟨t,hcut,rfl⟩,rfl⟩
          simpa only [R.prefix_image,zero_add,htx] using hh
        have hFromRay (j : Option Bool) (x : S) (hxE : x ∈ E.source)
            (hx : R.H (E x) ∈ segment ℝ (0:Plane) (R.vector j)) :
            ∃ t : Interval, φ j t=x := by
          have hh : R.H (E x) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) := by
            rw [R.prefix_image,zero_add];exact hx
          obtain ⟨z,⟨t,ht,rfl⟩,he⟩ := hh
          exact ⟨t,E.injOn (hUE (hφU j t)) hxE (R.H.injective he)⟩
        refine ⟨γ,R,hRop,?_⟩
        intro x hxE hxN
        have hxBC : x ∉ badC := fun h => hNotBad x hxE hxN (Or.inl h)
        have hxBF : x ∉ badF := fun h => hNotBad x hxE hxN (Or.inr h)
        constructor
        · constructor
          · intro hx
            obtain ⟨b,t,htx⟩ := hCcover x hx hxBC
            have hray := hToRay (some b) x hxN t htx
            cases b
            · exact Or.inl hray
            · exact Or.inr hray
          · intro hx
            rcases hx with hx | hx
            · obtain ⟨t,ht⟩ := hFromRay (some false) x hxE hx
              exact ⟨q * Circle.exp (θ false t),ht⟩
            · obtain ⟨t,ht⟩ := hFromRay (some true) x hxE hx
              exact ⟨q * Circle.exp (θ true t),ht⟩
        · constructor
          · intro hx
            obtain ⟨t,ht⟩ := hFcover x hx hxBF
            exact hToRay none x hxN t ht
          · intro hx
            obtain ⟨t,ht⟩ := hFromRay none x hxE hx
            exact ⟨fp t,ht⟩
      have radial_three_arm_independent (γ : Option Bool → Interval → Plane)
          (V : Set Plane) (R : CurveComplex.FiniteStarGeometry.RadializedStar γ 0 V)
          (hop : R.vector (some true) = -R.vector (some false)) :
          LinearIndependent ℝ ![R.vector none,R.vector (some false)] := by
        have positive_ray_contradiction (u v : Plane) (hun : u ≠ 0)
            (hdis : Disjoint (segment ℝ (0:Plane) u \ {0})
              (segment ℝ (0:Plane) v \ {0}))
            (a : ℝ) (ha : 0 < a) (he : a • v = u) : False := by
          let b : ℝ := 1/(a+1)
          have hb : 0 < b := by dsimp [b];positivity
          have hsum : b*(a+1)=1 := div_mul_cancel₀ 1 (by linarith)
          have hb1 : b ≤ 1 := by nlinarith [mul_pos hb ha]
          have hba : 0 ≤ b*a ∧ b*a ≤ 1 := by
            constructor
            · positivity
            · nlinarith
          have hu : b • u ∈ segment ℝ (0:Plane) u := by
            rw [segment_eq_image]
            exact ⟨b,⟨hb.le,hb1⟩,by simp⟩
          have hv : b • u ∈ segment ℝ (0:Plane) v := by
            rw [segment_eq_image]
            refine ⟨b*a,hba,?_⟩
            simp only [smul_zero,zero_add,mul_smul,he]
          have hn : b • u ≠ 0 := smul_ne_zero (ne_of_gt hb) hun
          exact Set.disjoint_left.mp hdis ⟨hu,by simpa using hn⟩ ⟨hv,by simpa using hn⟩
        rw [linearIndependent_fin2]
        simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
        refine ⟨R.vector_nonzero (some false),?_⟩
        intro a he
        rcases lt_trichotomy a 0 with ha | ha | ha
        · have hdis := R.distinct_rays none (some true) (by simp)
          simp only [zero_add] at hdis
          apply positive_ray_contradiction (R.vector none) (R.vector (some true))
            (R.vector_nonzero none) hdis (-a) (by linarith)
          rw [hop,smul_neg,neg_smul,neg_neg]
          exact he
        · subst a
          simp only [zero_smul] at he
          exact R.vector_nonzero none he.symm
        · have hdis := R.distinct_rays none (some false) (by simp)
          simp only [zero_add] at hdis
          exact positive_ray_contradiction (R.vector none) (R.vector (some false))
            (R.vector_nonzero none) hdis a ha he
      have endpoint_axis_chart (a : Curve S) (f : C(Interval,S))
          (hf : Topology.IsEmbedding f) (hfc : f 0 ∈ a.image)
          (hunique : ∀ t : Interval, f t ∈ a.image → t=0)
          (Eraw : OpenPartialHomeomorph S Plane) (hEraw0 : Eraw (f 0)=0)
          (U : Set S) (hU : IsOpen U) (hpU : f 0 ∈ U) (hUE : U ⊆ Eraw.source) :
          ∃ N : OpenPartialHomeomorph S Plane,
            f 0 ∈ N.source ∧ N (f 0)=0 ∧ N.source ⊆ U ∧
            (∀ x, x ∈ N.source → (x ∈ a.image ↔ N x 0=0)) ∧
            (∀ u : Interval, f u ∈ N.source → N (f u) 1=0) := by
        obtain ⟨γstart,Rstart,hRstartOpposite,hRstartTrace⟩ := endpoint_radial_core
          a f hf hfc hunique Eraw hEraw0 U hU hpU hUE
        have hStartIndependent := radial_three_arm_independent γstart (Eraw '' U)
          Rstart hRstartOpposite
        let Estart := Eraw
        have hpEstart : f 0 ∈ Estart.source := hUE hpU
        have hEstart0 : Estart (f 0)=0 := hEraw0
        let Bstart : Module.Basis (Fin 2) ℝ Plane :=
          basisOfLinearIndependentOfCardEqFinrank hStartIndependent (by simp)
        let Astart : Plane ≃L[ℝ] Plane := Bstart.equivFun.toContinuousLinearEquiv.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm
        have hBstart (i : Fin 2) : Bstart i = ![Rstart.vector none,Rstart.vector (some false)] i := by
          exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank
            hStartIndependent (by simp)) i
        have hAstartNone : Astart (Rstart.vector none)=Plane.mk 1 0 := by
          have hB0 : Bstart 0=Rstart.vector none := by simpa using hBstart 0
          rw [← hB0]
          ext i
          change Bstart.equivFun (Bstart 0) i = Plane.mk 1 0 i
          rw [Module.Basis.equivFun_self]
          fin_cases i <;> rfl
        have hAstartCircle : Astart (Rstart.vector (some false))=Plane.mk 0 1 := by
          have hB1 : Bstart 1=Rstart.vector (some false) := by simpa using hBstart 1
          rw [← hB1]
          ext i
          change Bstart.equivFun (Bstart 1) i = Plane.mk 0 1 i
          rw [Module.Basis.equivFun_self]
          fin_cases i <;> rfl
        have hCoreCircleAxis (Y : Plane) (hY : ‖Y‖ ≤ Rstart.coreRadius) :
            Y ∈ segment ℝ (0:Plane) (Rstart.vector (some false)) ∪
              segment ℝ (0:Plane) (Rstart.vector (some true)) ↔ (Astart Y) 0=0 := by
          constructor
          · intro hmem
            rcases hmem with hx | hx
            · rw [segment_eq_image] at hx
              obtain ⟨t,ht,rfl⟩ := hx
              simp [map_add,map_smul,hAstartCircle]
            · rw [segment_eq_image] at hx
              obtain ⟨t,ht,rfl⟩ := hx
              simp [map_add,map_smul,hRstartOpposite,hAstartCircle]
          · intro haxis
            let y : ℝ := (Astart Y) 1
            have hYe : Y=y • Rstart.vector (some false) := by
              apply Astart.injective
              rw [map_smul,hAstartCircle]
              ext i
              fin_cases i
              · simpa using haxis
              · simp [y]
            have hn : ‖Y‖=|y| * ‖Rstart.vector (some false)‖ := by
              rw [hYe,norm_smul,Real.norm_eq_abs]
            have hvpos : 0 < ‖Rstart.vector (some false)‖ :=
              norm_pos_iff.mpr (Rstart.vector_nonzero (some false))
            have hyabs : |y| ≤ 1 := by
              by_contra hh
              have hlt := Rstart.core_lt_length (some false)
              rw [hn] at hY
              nlinarith [mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hvpos]
            by_cases hy : 0 ≤ y
            · left
              rw [segment_eq_image]
              exact ⟨y,⟨hy,(le_abs_self y).trans hyabs⟩,by simpa using hYe.symm⟩
            · right
              rw [segment_eq_image]
              refine ⟨-y,⟨by linarith,by simpa [abs_of_neg (lt_of_not_ge hy)] using hyabs⟩,?_⟩
              simp only [smul_zero,zero_add,hRstartOpposite,neg_smul,smul_neg,neg_neg]
              exact hYe.symm
        let Gstart : OpenPartialHomeomorph S Plane :=
          (Estart.trans Rstart.H.toOpenPartialHomeomorph).trans
            Astart.toHomeomorph.toOpenPartialHomeomorph
        have hGstartSource : Gstart.source=Estart.source := by
          ext x
          simp only [Gstart,OpenPartialHomeomorph.trans_source,
            Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
        let Tstart : Set S := Estart.source ∩
          Estart ⁻¹' (Rstart.H ⁻¹' Metric.ball (0:Plane) Rstart.coreRadius)
        have hTstart : IsOpen Tstart := Estart.isOpen_inter_preimage
          (Metric.isOpen_ball.preimage Rstart.H.continuous)
        have hpTstart : f 0 ∈ Tstart := by
          refine ⟨hpEstart,?_⟩
          change Rstart.H (Estart (f 0)) ∈ Metric.ball (0:Plane) Rstart.coreRadius
          rw [hEstart0,Rstart.fixes_center]
          exact Metric.mem_ball_self Rstart.core_pos
        let Nstart := Gstart.restrOpen Tstart hTstart
        have hpNstart : f 0 ∈ Nstart.source := by
          change f 0 ∈ Gstart.source ∩ Tstart
          exact ⟨hGstartSource.symm ▸ hpEstart,hpTstart⟩
        have hNstart0 : Nstart (f 0)=0 := by
          change Astart (Rstart.H (Estart (f 0)))=0
          rw [hEstart0,Rstart.fixes_center,map_zero]
        have hNstartCircle (x : S) (hx : x ∈ Nstart.source) :
            x ∈ a.image ↔ Nstart x 0=0 := by
          have hxT : x ∈ Tstart := hx.2
          have hxN : ‖Rstart.H (Estart x)‖ ≤ Rstart.coreRadius := by
            have hh : Rstart.H (Estart x) ∈ Metric.ball (0:Plane) Rstart.coreRadius := hxT.2
            rw [Metric.mem_ball,dist_zero_right] at hh
            exact hh.le
          exact (hRstartTrace x hxT.1 hxN).1.trans (hCoreCircleAxis _ hxN)
        have hNstartArc (u : Interval) (hu : f u ∈ Nstart.source) :
            Nstart (f u) 1=0 := by
          have huT : f u ∈ Tstart := hu.2
          have huN : ‖Rstart.H (Estart (f u))‖ ≤ Rstart.coreRadius := by
            have hh : Rstart.H (Estart (f u)) ∈ Metric.ball (0:Plane) Rstart.coreRadius := huT.2
            rw [Metric.mem_ball,dist_zero_right] at hh
            exact hh.le
          have hRay := (hRstartTrace (f u) huT.1 huN).2.mp (Set.mem_range_self u)
          rw [segment_eq_image] at hRay
          obtain ⟨t,ht,he⟩ := hRay
          change Astart (Rstart.H (Estart (f u))) 1=0
          rw [← he]
          simp [map_add,map_smul,hAstartNone]
        have hNU : Nstart.source ⊆ U := by
          intro x hx
          have hxT : x ∈ Tstart := hx.2
          have hxN : ‖Rstart.H (Estart x)‖ < Rstart.coreRadius := by
            have hh : Rstart.H (Estart x) ∈ Metric.ball (0:Plane) Rstart.coreRadius := hxT.2
            simpa only [Metric.mem_ball,dist_zero_right] using hh
          have hxBall : Estart x ∈ Metric.ball (0:Plane) Rstart.supportRadius := by
            by_contra hn
            have hfix := Rstart.fixes_exterior (Estart x) hn
            rw [hfix] at hxN
            have hn' : Rstart.supportRadius ≤ ‖Estart x‖ := by
              simpa only [Metric.mem_ball,dist_zero_right,not_lt] using hn
            linarith [Rstart.core_lt_support]
          obtain ⟨y,hy,he⟩ := Rstart.support_subset (Metric.ball_subset_closedBall hxBall)
          have hyx := Estart.injOn (hUE hy) hxT.1 he
          exact hyx ▸ hy
        exact ⟨Nstart,hpNstart,hNstart0,hNU,hNstartCircle,hNstartArc⟩
      let : T2Space S := M.sphere.symm.t2Space
      obtain ⟨j,hj,hj0,hj1,hjavoid⟩ := actual_joining_arc
      have hstart_unique (t : Interval) (ht : j t ∈ c.image) : t=0 := by
        by_cases ht0 : t=0
        · exact ht0
        by_cases ht1 : t=1
        · subst t
          exact False.elim (Set.disjoint_left.mp hd ht hj1)
        have htpos : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (by
          intro he;exact ht0 (Subtype.ext he.symm))
        have htlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (by
          intro he;exact ht1 (Subtype.ext he))
        exact False.elim (hjavoid t htpos htlt (Or.inl ht))
      let atlas := M.actualSphereSmoothAtlas
      let : ChartedSpace Plane S := atlas.charts
      let : CompactSpace S := M.sphere.symm.compactSpace
      let Cstart := chartAt Plane (j 0)
      let Estart : OpenPartialHomeomorph S Plane := Cstart.trans
        (Homeomorph.addRight (-Cstart (j 0))).toOpenPartialHomeomorph
      have hEstartSource : Estart.source=Cstart.source := by
        ext x
        simp only [Estart,OpenPartialHomeomorph.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
      have hpEstart : j 0 ∈ Estart.source := by
        rw [hEstartSource];exact mem_chart_source Plane (j 0)
      have hEstart0 : Estart (j 0)=0 := by
        change Cstart (j 0) + -Cstart (j 0)=0
        exact add_neg_cancel _
      have hdclosed : IsClosed d.image :=
        (isCompact_range d.embedded.continuous).isClosed
      obtain ⟨Wstart,hWstart,hpWstart,hWstartClosure⟩ := normal_exists_closure_subset
        (isClosed_singleton : IsClosed ({j 0} : Set S)) hdclosed.isOpen_compl
        (Set.singleton_subset_iff.mpr (fun h => Set.disjoint_left.mp hd hj0 h))
      let Ustart : Set S := Estart.source ∩ Wstart
      have hUstart : IsOpen Ustart := Estart.open_source.inter hWstart
      have hpUstart : j 0 ∈ Ustart :=
        ⟨hpEstart,hpWstart (Set.mem_singleton _)⟩
      obtain ⟨Nstart,hpNstart,hNstart0,hNstartU,hNstartCircle,hNstartArc⟩ :=
        endpoint_axis_chart c j hj hj0 hstart_unique Estart hEstart0
          Ustart hUstart hpUstart (fun x hx => hx.1)
      let jrev : C(Interval,S) := ⟨j ∘ unitInterval.symm,
        j.continuous.comp unitInterval.continuous_symm⟩
      have hjrev : Topology.IsEmbedding jrev :=
        hj.comp unitInterval.symmHomeomorph.isEmbedding
      have hjrev0 : jrev 0=j 1 := by simp [jrev]
      have hjrev1 : jrev 1=j 0 := by simp [jrev]
      have hfinish_unique (t : Interval) (ht : jrev t ∈ d.image) : t=0 := by
        by_cases ht0 : t=0
        · exact ht0
        by_cases ht1 : t=1
        · subst t
          rw [hjrev1] at ht
          exact False.elim (Set.disjoint_left.mp hd hj0 ht)
        have htpos : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (by
          intro he;exact ht0 (Subtype.ext he.symm))
        have htlt : (t:ℝ)<1 := lt_of_le_of_ne t.property.2 (by
          intro he;exact ht1 (Subtype.ext he))
        have hsp : 0 < (unitInterval.symm t:ℝ) := by
          change 0<1-(t:ℝ);linarith
        have hsl : (unitInterval.symm t:ℝ)<1 := by
          change 1-(t:ℝ)<1;linarith
        exact False.elim (hjavoid (unitInterval.symm t) hsp hsl (Or.inr ht))
      let Cfinish := chartAt Plane (jrev 0)
      let Efinish : OpenPartialHomeomorph S Plane := Cfinish.trans
        (Homeomorph.addRight (-Cfinish (jrev 0))).toOpenPartialHomeomorph
      have hEfinishSource : Efinish.source=Cfinish.source := by
        ext x
        simp only [Efinish,OpenPartialHomeomorph.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
      have hpEfinish : jrev 0 ∈ Efinish.source := by
        rw [hEfinishSource];exact mem_chart_source Plane (jrev 0)
      have hEfinish0 : Efinish (jrev 0)=0 := by
        change Cfinish (jrev 0) + -Cfinish (jrev 0)=0
        exact add_neg_cancel _
      have hcclosed : IsClosed c.image :=
        (isCompact_range c.embedded.continuous).isClosed
      let Ufinish : Set S := (Efinish.source ∩ (closure Wstart)ᶜ) ∩ c.imageᶜ
      have hUfinish : IsOpen Ufinish :=
        (Efinish.open_source.inter isClosed_closure.isOpen_compl).inter hcclosed.isOpen_compl
      have hpUfinish : jrev 0 ∈ Ufinish := by
        refine ⟨⟨hpEfinish,?_⟩,?_⟩
        · intro hh
          have hdnot := hWstartClosure hh
          rw [hjrev0] at hdnot
          exact hdnot hj1
        · intro hhc
          rw [hjrev0] at hhc
          exact Set.disjoint_left.mp hd hhc hj1
      have hjrev0d : jrev 0 ∈ d.image := hjrev0.symm ▸ hj1
      obtain ⟨Nfinish,hpNfinish,hNfinish0,hNfinishU,hNfinishCircle,hNfinishArc⟩ :=
        endpoint_axis_chart d jrev hjrev hjrev0d hfinish_unique Efinish hEfinish0
          Ufinish hUfinish hpUfinish (fun x hx => hx.1.1)
      have hNfinishOriginal (u : Interval) (hu : j u ∈ Nfinish.source) :
          Nfinish (j u) 1=0 := by
        have he : jrev (unitInterval.symm u)=j u := by simp [jrev]
        simpa only [he] using hNfinishArc (unitInterval.symm u) (he.symm ▸ hu)
      have hEndpointSourcesDisjoint : Disjoint Nstart.source Nfinish.source := by
        apply Set.disjoint_left.mpr
        intro x hx0 hx1
        have hw : x ∈ Wstart := (hNstartU hx0).2
        exact (hNfinishU hx1).1.2 (subset_closure hw)
      have hrankSphere : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
        simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]
        norm_num
      let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
        Subtype.connectedSpace (isConnected_sphere hrankSphere 0 zero_le_one)
      let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
      letI := atlas.manifold
      let : ClosedSurface S := {}
      let θend : Bool → Interval := fun b => if b then 1 else 0
      have hθend : Function.Injective θend := by
        intro b k he
        cases b <;> cases k
        · rfl
        · have hv := congrArg (fun t : Interval => (t:ℝ)) he
          norm_num [θend] at hv
        · have hv := congrArg (fun t : Interval => (t:ℝ)) he
          norm_num [θend] at hv
        · rfl
      let Eend : Bool → OpenPartialHomeomorph S Plane := fun b => if b then Nfinish else Nstart
      have hpEend (b : Bool) : j (θend b) ∈ (Eend b).source := by
        cases b
        · exact hpNstart
        · change j 1 ∈ Nfinish.source
          rw [← hjrev0]
          exact hpNfinish
      have hEend0 (b : Bool) : Eend b (j (θend b))=0 := by
        cases b
        · exact hNstart0
        · change Nfinish (j 1)=0
          rw [← hjrev0]
          exact hNfinish0
      have hEendAxis (b : Bool) (u : Interval) (hu : j u ∈ (Eend b).source) :
          Eend b (j u) 1=0 := by
        cases b
        · exact hNstartArc u hu
        · exact hNfinishOriginal u hu
      obtain ⟨B,hB,hBU,hBcenter,σend,δend,ηend,hσend,hδηend,hBend⟩ :=
        CurveComplex.source_finite_axis_framed_arc_strip S j hj Bool θend hθend
          Eend hpEend hEend0 hEendAxis Set.univ isOpen_univ (Set.subset_univ _)
      have hBstartPort (w : Set.Icc (-1:ℝ) 1) : B (0,w) ∈ c.image := by
        obtain ⟨hs,hcoord⟩ := hBend false (0:Interval) w (by
          change |(0:ℝ)-0| < ηend false
          simpa using (hδηend false).2)
        apply (hNstartCircle _ hs).mpr
        have hh := congrArg (fun y : Plane => y 0) hcoord
        change Nstart (B (0,w)) 0 = Nstart (j 0) 0 at hh
        rw [hNstart0] at hh
        exact hh
      have hBfinishPort (w : Set.Icc (-1:ℝ) 1) : B (1,w) ∈ d.image := by
        obtain ⟨hs,hcoord⟩ := hBend true (1:Interval) w (by
          change |(1:ℝ)-1| < ηend true
          simpa using (hδηend true).2)
        apply (hNfinishCircle _ hs).mpr
        have hh := congrArg (fun y : Plane => y 0) hcoord
        change Nfinish (B (1,w)) 0 = Nfinish (j 1) 0 at hh
        rw [← hjrev0,hNfinish0] at hh
        exact hh
      let a : ℝ := min (ηend false / 4) (min (ηend true / 4) (1/4))
      have ha : 0 < a := lt_min (by linarith [(hδηend false).2])
        (lt_min (by linarith [(hδηend true).2]) (by norm_num))
      have haquarter : a ≤ 1/4 := (min_le_right _ _).trans (min_le_right _ _)
      have haη0 : a < ηend false := by
        have hh := min_le_left (ηend false / 4) (min (ηend true / 4) (1/4:ℝ))
        dsimp [a];linarith [(hδηend false).2]
      have haη1 : a < ηend true := by
        have hh := (min_le_right (ηend false / 4) (min (ηend true / 4) (1/4:ℝ))).trans
          (min_le_left (ηend true / 4) (1/4:ℝ))
        dsimp [a];linarith [(hδηend true).2]
      let middle : Interval → Interval := fun t => ⟨a+(1-2*a)*(t:ℝ),by
        constructor <;> nlinarith [t.property.1,t.property.2]⟩
      have hMiddleContinuous : Continuous middle :=
        (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
      have hMiddleBounds (t : Interval) : 0 < (middle t:ℝ) ∧ (middle t:ℝ)<1 := by
        change 0<a+(1-2*a)*(t:ℝ) ∧ a+(1-2*a)*(t:ℝ)<1
        constructor <;> nlinarith [t.property.1,t.property.2]
      let Bmid : Interval × Set.Icc (-1:ℝ) 1 → S := fun p => B (middle p.1,p.2)
      have hBmid : Continuous Bmid := hB.continuous.comp
        ((hMiddleContinuous.comp continuous_fst).prodMk continuous_snd)
      have hBmidCenter (t : Interval) :
          Bmid (t,⟨0,by norm_num⟩) ∈ (c.image ∪ d.image)ᶜ := by
        change B (middle t,⟨0,by norm_num⟩) ∉ c.image ∪ d.image
        rw [hBcenter]
        exact hjavoid (middle t) (hMiddleBounds t).1 (hMiddleBounds t).2
      obtain ⟨ρ,hρ,hNarrowMiddle⟩ := CurveComplex.source_continuous_strip_uniform_width
        Bmid hBmid (c.image ∪ d.image)ᶜ
          (hcclosed.union hdclosed).isOpen_compl hBmidCenter
      let width : Set.Icc (-1:ℝ) 1 → Set.Icc (-1:ℝ) 1 := fun w => ⟨ρ*(w:ℝ),by
        constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩
      have hWidthContinuous : Continuous width :=
        (continuous_const.mul continuous_subtype_val).subtype_mk _
      have hWidthInjective : Function.Injective width := by
        intro w v he
        have hv := congrArg Subtype.val he
        apply Subtype.ext
        change ρ*(w:ℝ)=ρ*(v:ℝ) at hv
        nlinarith [hρ.1]
      let Bsmall : C(Interval × Set.Icc (-1:ℝ) 1,S) :=
        ⟨fun p => B (p.1,width p.2),hB.continuous.comp
          (continuous_fst.prodMk (hWidthContinuous.comp continuous_snd))⟩
      have hBsmall : Topology.IsEmbedding Bsmall :=
        (Bsmall.continuous.isClosedEmbedding (by
          intro p q he
          have hh := hB.injective he
          apply Prod.ext
          · have hfirst := congrArg (fun r : Interval × Set.Icc (-1:ℝ) 1 => r.1) hh
            exact hfirst
          · have hsecond := congrArg (fun r : Interval × Set.Icc (-1:ℝ) 1 => r.2) hh
            exact hWidthInjective hsecond)).isEmbedding
      have hBsmallCenter (u : Interval) : Bsmall (u,⟨0,by norm_num⟩)=j u := by
        change B (u,width ⟨0,by norm_num⟩)=j u
        have hw0 : width ⟨0,by norm_num⟩=⟨0,by norm_num⟩ := by
          apply Subtype.ext;simp [width]
        rw [hw0,hBcenter]
      have hMiddleAvoid (u : Interval) (hu0 : a ≤ (u:ℝ)) (hu1 : (u:ℝ)≤1-a)
          (w : Set.Icc (-1:ℝ) 1) : Bsmall (u,w) ∉ c.image ∪ d.image := by
        have hden : 0 < 1-2*a := by linarith
        let t : Interval := ⟨((u:ℝ)-a)/(1-2*a),
          ⟨div_nonneg (by linarith) hden.le,(div_le_one hden).mpr (by linarith)⟩⟩
        have hmiddle : middle t=u := by
          apply Subtype.ext
          change a+(1-2*a)*(((u:ℝ)-a)/(1-2*a))=(u:ℝ)
          rw [mul_div_cancel₀ _ (ne_of_gt hden)];ring
        have hh := hNarrowMiddle t w
        change B (middle t,width w) ∉ c.image ∪ d.image at hh
        rw [hmiddle] at hh
        exact hh
      have hStartFrame (u : Interval) (hu : (u:ℝ)<a) (w : Set.Icc (-1:ℝ) 1) :
          Bsmall (u,w) ∈ Nstart.source ∧
            Nstart (Bsmall (u,w)) 0=Nstart (j u) 0 := by
        have hwindow : |(u:ℝ)-(θend false:ℝ)| < ηend false := by
          change |(u:ℝ)-0| < ηend false
          rw [sub_zero,abs_of_nonneg u.property.1]
          exact hu.trans haη0
        obtain ⟨hs,he⟩ := hBend false u (width w) hwindow
        have hh := congrArg (fun y : Plane => y 0) he
        change Nstart (Bsmall (u,w)) 0=Nstart (j u) 0 at hh
        exact ⟨hs,hh⟩
      have hFinishFrame (u : Interval) (hu : 1-a<(u:ℝ)) (w : Set.Icc (-1:ℝ) 1) :
          Bsmall (u,w) ∈ Nfinish.source ∧
            Nfinish (Bsmall (u,w)) 0=Nfinish (j u) 0 := by
        have hwindow : |(u:ℝ)-(θend true:ℝ)| < ηend true := by
          change |(u:ℝ)-1| < ηend true
          rw [abs_of_nonpos (by linarith [u.property.2])]
          linarith [haη1]
        obtain ⟨hs,he⟩ := hBend true u (width w) hwindow
        have hh := congrArg (fun y : Plane => y 0) he
        change Nfinish (Bsmall (u,w)) 0=Nfinish (j u) 0 at hh
        exact ⟨hs,hh⟩
      have hBsmallC (u : Interval) (w : Set.Icc (-1:ℝ) 1) :
          Bsmall (u,w) ∈ c.image ↔ u=0 := by
        constructor
        · intro hc
          by_cases hu : (u:ℝ)<a
          · obtain ⟨hs,he⟩ := hStartFrame u hu w
            have hzero := (hNstartCircle _ hs).mp hc
            have hju : j u ∈ Nstart.source := by
              have hh := (hStartFrame u hu ⟨0,by norm_num⟩).1
              rwa [hBsmallCenter] at hh
            apply hstart_unique u
            exact (hNstartCircle _ hju).mpr (he.symm.trans hzero)
          · by_cases hv : 1-a<(u:ℝ)
            · have hs := (hFinishFrame u hv w).1
              exact False.elim ((hNfinishU hs).2 hc)
            · exact False.elim (hMiddleAvoid u (le_of_not_gt hu) (le_of_not_gt hv) w (Or.inl hc))
        · intro he
          subst u
          exact hBstartPort (width w)
      have hBsmallD (u : Interval) (w : Set.Icc (-1:ℝ) 1) :
          Bsmall (u,w) ∈ d.image ↔ u=1 := by
        constructor
        · intro hdmem
          by_cases hu : (u:ℝ)<a
          · have hs := (hStartFrame u hu w).1
            have hw : Bsmall (u,w) ∈ Wstart := (hNstartU hs).2
            exact False.elim (hWstartClosure (subset_closure hw) hdmem)
          · by_cases hv : 1-a<(u:ℝ)
            · obtain ⟨hs,he⟩ := hFinishFrame u hv w
              have hzero := (hNfinishCircle _ hs).mp hdmem
              have hju : j u ∈ Nfinish.source := by
                have hh := (hFinishFrame u hv ⟨0,by norm_num⟩).1
                rwa [hBsmallCenter] at hh
              have hdu : j u ∈ d.image :=
                (hNfinishCircle _ hju).mpr (he.symm.trans hzero)
              have hjrevu : jrev (unitInterval.symm u) ∈ d.image := by simpa [jrev] using hdu
              have hh := hfinish_unique (unitInterval.symm u) hjrevu
              have hv0 := congrArg (fun t : Interval => (t:ℝ)) hh
              apply Subtype.ext
              change 1-(u:ℝ)=0 at hv0
              change (u:ℝ)=1
              linarith
            · exact False.elim (hMiddleAvoid u (le_of_not_gt hu) (le_of_not_gt hv) w (Or.inr hdmem))
        · intro he
          subst u
          exact hBfinishPort (width w)
      have circle_arc_complement (f : C(Interval,Circle)) (hf : Topology.IsEmbedding f) :
          ∃ g : C(Interval,Circle), Topology.IsEmbedding g ∧ g 0=f 0 ∧ g 1=f 1 ∧
            Set.range f ∪ Set.range g=Set.univ ∧ Set.range f ∩ Set.range g={f 0,f 1} := by
        have hne : f 0 ≠ f 1 := by
          intro he
          have hh := congrArg (fun t : Interval => (t:ℝ)) (hf.injective he)
          norm_num at hh
        let P : C(Interval,Circle) := ⟨Circle.path (f 0) (f 1),(Circle.path _ _).continuous⟩
        let Q : C(Interval,Circle) := ⟨(Circle.path (f 1) (f 0)).symm,
          (Circle.path _ _).symm.continuous⟩
        have hP : Topology.IsEmbedding P := (P.continuous.isClosedEmbedding
          (Circle.path_injective_of_ne hne)).isEmbedding
        have hQ : Topology.IsEmbedding Q := (Q.continuous.isClosedEmbedding
          ((Circle.path_injective_of_ne hne.symm).comp unitInterval.symm_involutive.injective)).isEmbedding
        have hP0 : P 0=f 0 := (Circle.path (f 0) (f 1)).source
        have hP1 : P 1=f 1 := (Circle.path (f 0) (f 1)).target
        have hQ0 : Q 0=f 0 := (Circle.path (f 1) (f 0)).symm.source
        have hQ1 : Q 1=f 1 := (Circle.path (f 1) (f 0)).symm.target
        have hcover : Set.range P ∪ Set.range Q=Set.univ := by
          change Set.range (Circle.path (f 0) (f 1)) ∪
            Set.range (Circle.path (f 1) (f 0)).symm=Set.univ
          rw [Path.symm_range,Circle.range_path_union_range_path hne]
        have hinter : Set.range P ∩ Set.range Q={f 0,f 1} := by
          change Set.range (Circle.path (f 0) (f 1)) ∩
            Set.range (Circle.path (f 1) (f 0)).symm={f 0,f 1}
          rw [Path.symm_range,Circle.range_path_inter_range_path hne]
        have hcl (g : C(Interval,Circle)) :
            closure (g '' Set.Ioo (0:Interval) 1)=Set.range g := by
          rw [g.continuous.isClosedMap.closure_image_eq_of_continuous g.continuous,
            closure_Ioo (by norm_num : (0:Interval) ≠ 1),← unitInterval.univ_eq_Icc,Set.image_univ]
        let U : Set Circle := (Set.range Q)ᶜ
        let V : Set Circle := (Set.range P)ᶜ
        have hU : IsOpen U := (isCompact_range Q.continuous).isClosed.isOpen_compl
        have hV : IsOpen V := (isCompact_range P.continuous).isClosed.isOpen_compl
        have hdisj : Disjoint U V := by
          rw [Set.disjoint_iff_inter_eq_empty,← Set.compl_union,Set.union_comm,hcover,Set.compl_univ]
        have hUV : U ∪ V=({f 0,f 1}:Set Circle)ᶜ := by
          rw [← Set.compl_inter,Set.inter_comm,hinter]
        have hclU : closure U=Set.range P := by
          change closure (Set.range (Circle.path (f 1) (f 0)).symm)ᶜ=
            Set.range (Circle.path (f 0) (f 1))
          rw [Path.symm_range,Circle.compl_range_path hne.symm]
          exact hcl P
        have hclV : closure V=Set.range Q := by
          change closure (Set.range (Circle.path (f 0) (f 1)))ᶜ=
            Set.range (Circle.path (f 1) (f 0)).symm
          rw [Path.symm_range,Circle.compl_range_path hne]
          exact hcl ⟨Circle.path (f 1) (f 0),(Circle.path _ _).continuous⟩
        have hmid : f '' Set.Ioo (0:Interval) 1 ⊆ U ∪ V := by
          rw [hUV]
          rintro x ⟨t,ht,rfl⟩ (he | he)
          · exact (ne_of_gt ht.1) (hf.injective he)
          · exact (ne_of_lt ht.2) (hf.injective he)
        have range_eq_of_subset (g : C(Interval,Circle)) (hg : Topology.IsEmbedding g)
            (hg0 : g 0=f 0) (hg1 : g 1=f 1) (hsub : Set.range f ⊆ Set.range g) :
            Set.range f=Set.range g := by
          let k : C(Interval,Interval) := ⟨fun t => hg.toHomeomorph.symm ⟨f t,hsub (Set.mem_range_self t)⟩,
            hg.toHomeomorph.symm.continuous.comp (f.continuous.subtype_mk _)⟩
          have hklift (t : Interval) : g (k t)=f t :=
            congrArg Subtype.val (hg.toHomeomorph.apply_symm_apply ⟨f t,hsub (Set.mem_range_self t)⟩)
          have hk0 : k 0=0 := hg.injective ((hklift 0).trans hg0.symm)
          have hk1 : k 1=1 := hg.injective ((hklift 1).trans hg1.symm)
          have hkimage : Set.Icc (0:Interval) 1 ⊆ Set.range k :=
            (isPreconnected_range k.continuous).ordConnected.out ⟨0,hk0⟩ ⟨1,hk1⟩
          apply Set.Subset.antisymm hsub
          rintro x ⟨u,rfl⟩
          obtain ⟨v,hv⟩ := hkimage ⟨u.property.1,u.property.2⟩
          exact ⟨v,(hklift v).symm.trans (congrArg g hv)⟩
        rcases (isPreconnected_Ioo.image f f.continuous.continuousOn).subset_or_subset
          hU hV hdisj hmid with hsub | hsub
        · have hfull : Set.range f ⊆ Set.range P := by
            rw [← hcl f,← hclU]
            exact closure_mono hsub
          have heq := range_eq_of_subset P hP hP0 hP1 hfull
          exact ⟨Q,hQ,hQ0,hQ1,by rwa [heq],by rwa [heq]⟩
        · have hfull : Set.range f ⊆ Set.range Q := by
            rw [← hcl f,← hclV]
            exact closure_mono hsub
          have heq := range_eq_of_subset Q hQ hQ0 hQ1 hfull
          refine ⟨P,hP,hP0,hP1,?_,?_⟩
          · rw [heq,Set.union_comm,hcover]
          · rw [heq,Set.inter_comm,hinter]
      have curve_arc_complement (k : Curve S) (f : C(Interval,S))
          (hf : Topology.IsEmbedding f) (hsub : Set.range f ⊆ k.image) :
          ∃ g : C(Interval,S), Topology.IsEmbedding g ∧ g 0=f 0 ∧ g 1=f 1 ∧
            Set.range f ∪ Set.range g=k.image ∧ Set.range f ∩ Set.range g={f 0,f 1} := by
        let F : C(Interval,Circle) := ⟨fun t => k.embedded.toHomeomorph.symm ⟨f t,hsub ⟨t,rfl⟩⟩,
          k.embedded.toHomeomorph.symm.continuous.comp (f.continuous.subtype_mk _)⟩
        have hF (t : Interval) : k.map (F t)=f t :=
          congrArg Subtype.val (k.embedded.toHomeomorph.apply_symm_apply ⟨f t,hsub ⟨t,rfl⟩⟩)
        have hFemb : Topology.IsEmbedding F := (F.continuous.isClosedEmbedding (by
          intro t u he
          apply hf.injective
          exact (hF t).symm.trans ((congrArg k.map he).trans (hF u)))).isEmbedding
        obtain ⟨G,hG,hG0,hG1,hcover,hinter⟩ := circle_arc_complement F hFemb
        let g : C(Interval,S) := ⟨fun t => k.map (G t),k.embedded.continuous.comp G.continuous⟩
        have hfg : Set.range f=k.map '' Set.range F := by
          ext x
          constructor
          · rintro ⟨t,rfl⟩
            exact ⟨F t,⟨t,rfl⟩,hF t⟩
          · rintro ⟨z,⟨t,rfl⟩,rfl⟩
            exact ⟨t,(hF t).symm⟩
        have hgg : Set.range g=k.map '' Set.range G := by
          exact Set.range_comp k.map G
        refine ⟨g,k.embedded.comp hG,?_,?_,?_,?_⟩
        · exact (congrArg k.map hG0).trans (hF 0)
        · exact (congrArg k.map hG1).trans (hF 1)
        · rw [hfg,hgg,← Set.image_union,hcover,Set.image_univ]
          rfl
        · rw [hfg,hgg,← Set.image_inter k.embedded.injective,hinter]
          simp only [Set.image_insert_eq,Set.image_singleton]
          rw [hF 0,hF 1]
      let transverse : C(Interval,Set.Icc (-1:ℝ) 1) :=
        ⟨fun t => ⟨2*(t:ℝ)-1,by constructor <;> nlinarith [t.property.1,t.property.2]⟩,
          (by fun_prop)⟩
      have htransverse : Topology.IsEmbedding transverse :=
        (transverse.continuous.isClosedEmbedding (by
          intro t u he
          have hh := congrArg Subtype.val he
          apply Subtype.ext
          change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
          linarith)).isEmbedding
      let cport : C(Interval,S) := ⟨fun t => Bsmall (0,transverse t),
        Bsmall.continuous.comp (continuous_const.prodMk transverse.continuous)⟩
      let dport : C(Interval,S) := ⟨fun t => Bsmall (1,transverse t),
        Bsmall.continuous.comp (continuous_const.prodMk transverse.continuous)⟩
      have hcport : Topology.IsEmbedding cport := (cport.continuous.isClosedEmbedding (by
        intro t u he
        apply htransverse.injective
        exact congrArg Prod.snd (hBsmall.injective he))).isEmbedding
      have hdport : Topology.IsEmbedding dport := (dport.continuous.isClosedEmbedding (by
        intro t u he
        apply htransverse.injective
        exact congrArg Prod.snd (hBsmall.injective he))).isEmbedding
      have hcportsub : Set.range cport ⊆ c.image := by
        rintro x ⟨t,rfl⟩
        exact (hBsmallC 0 (transverse t)).mpr rfl
      have hdportsub : Set.range dport ⊆ d.image := by
        rintro x ⟨t,rfl⟩
        exact (hBsmallD 1 (transverse t)).mpr rfl
      obtain ⟨ccomplement,hccomplement,hccomplement0,hccomplement1,hcpartition,hcportmeet⟩ :=
        curve_arc_complement c cport hcport hcportsub
      obtain ⟨dcomplement,hdcomplement,hdcomplement0,hdcomplement1,hdpartition,hdportmeet⟩ :=
        curve_arc_complement d dport hdport hdportsub
      have htransverse_surj : Function.Surjective transverse := by
        intro w
        let t : Interval := ⟨((w:ℝ)+1)/2,by constructor <;> nlinarith [w.property.1,w.property.2]⟩
        refine ⟨t,?_⟩
        apply Subtype.ext
        change 2*(((w:ℝ)+1)/2)-1=(w:ℝ)
        ring
      have hccomplementSub : Set.range ccomplement ⊆ c.image := by
        intro x hx
        change x ∈ c.image
        rw [← hcpartition]
        exact Or.inr hx
      have hdcomplementSub : Set.range dcomplement ⊆ d.image := by
        intro x hx
        change x ∈ d.image
        rw [← hdpartition]
        exact Or.inr hx
      have hccomplementBand : Set.range ccomplement ∩ Set.range Bsmall={cport 0,cport 1} := by
        ext x
        constructor
        · rintro ⟨hx,⟨⟨u,w⟩,rfl⟩⟩
          have hu := (hBsmallC u w).mp (hccomplementSub hx)
          subst u
          obtain ⟨t,ht⟩ := htransverse_surj w
          have hp : Bsmall (0,w) ∈ Set.range cport := ⟨t,by change Bsmall (0,transverse t)=_; rw [ht]⟩
          rw [← hcportmeet]
          exact ⟨hp,hx⟩
        · intro hx
          rw [← hcportmeet] at hx
          refine ⟨hx.2,?_⟩
          obtain ⟨t,ht⟩ := hx.1
          exact ⟨(0,transverse t),ht⟩
      have hdcomplementBand : Set.range dcomplement ∩ Set.range Bsmall={dport 0,dport 1} := by
        ext x
        constructor
        · rintro ⟨hx,⟨⟨u,w⟩,rfl⟩⟩
          have hu := (hBsmallD u w).mp (hdcomplementSub hx)
          subst u
          obtain ⟨t,ht⟩ := htransverse_surj w
          have hp : Bsmall (1,w) ∈ Set.range dport := ⟨t,by change Bsmall (1,transverse t)=_; rw [ht]⟩
          rw [← hdportmeet]
          exact ⟨hp,hx⟩
        · intro hx
          rw [← hdportmeet] at hx
          refine ⟨hx.2,?_⟩
          obtain ⟨t,ht⟩ := hx.1
          exact ⟨(1,transverse t),ht⟩
      have hcomplementsDisjoint : Disjoint (Set.range ccomplement) (Set.range dcomplement) :=
        hd.mono hccomplementSub hdcomplementSub
      let : ConnectedSpace (Set.Icc (-1:ℝ) 1) :=
        Subtype.connectedSpace (isConnected_Icc (by norm_num : (-1:ℝ) ≤ 1))
      let Dband : Set S := Bsmall '' (Set.Ioo (0:Interval) 1 ×ˢ (Set.univ : Set (Set.Icc (-1:ℝ) 1)))
      have hDbandConnected : IsConnected Dband :=
        ((isConnected_Ioo (by norm_num : (0:Interval)<1)).prod isConnected_univ).image _
          Bsmall.continuous.continuousOn
      have hbandClosure (u : Interval) (w : Set.Icc (-1:ℝ) 1) :
          Bsmall (u,w) ∈ closure Dband := by
        let k : Interval → S := fun t => Bsmall (t,w)
        have hk : Continuous k := Bsmall.continuous.comp (continuous_id.prodMk continuous_const)
        have hu : u ∈ closure (Set.Ioo (0:Interval) 1) := by
          rw [closure_Ioo (by norm_num : (0:Interval) ≠ 1)]
          exact ⟨u.property.1,u.property.2⟩
        have hsub : k '' Set.Ioo (0:Interval) 1 ⊆ Dband := by
          rintro x ⟨t,ht,rfl⟩
          exact ⟨(t,w),⟨ht,Set.mem_univ _⟩,rfl⟩
        exact closure_mono hsub (image_closure_subset_closure_image hk ⟨u,hu,rfl⟩)
      have hbandRangeClosure : Set.range Bsmall ⊆ closure Dband := by
        rintro x ⟨⟨u,w⟩,rfl⟩
        exact hbandClosure u w
      have hDbandAvoidC : Dband ⊆ c.imageᶜ := by
        rintro x ⟨⟨u,w⟩,⟨hu,hw⟩,rfl⟩ hc
        exact (ne_of_gt hu.1) ((hBsmallC u w).mp hc)
      have hDbandAvoidD : Dband ⊆ d.imageᶜ := by
        rintro x ⟨⟨u,w⟩,⟨hu,hw⟩,rfl⟩ hdmem
        exact (ne_of_lt hu.2) ((hBsmallD u w).mp hdmem)
      have oriented_band_sides (p : Curve S) (havoid : Dband ⊆ p.imageᶜ) :
          ∃ U V : Set S,
            IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
            Disjoint U V ∧ U ∪ V=p.imageᶜ ∧ Dband ⊆ U ∧
            closure U=U ∪ p.image ∧ closure V=V ∪ p.image := by
        obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,dU,dV,hUb,hVb,hUi,hVi,hclU,hclV⟩ :=
          actual_curve_closedSides p
        have hsub : Dband ⊆ U ∪ V := by rwa [hcover]
        rcases hDbandConnected.isPreconnected.subset_or_subset hUo hVo hUV hsub with hDU | hDV
        · exact ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcover,hDU,hclU,hclV⟩
        · exact ⟨V,U,hVo,hUo,hVc,hUc,hUV.symm,(Set.union_comm V U).trans hcover,
            hDV,hclV,hclU⟩
      obtain ⟨U,V,hUo,hVo,hUc,hVc,hUV,hcoverc,hDU,hclU,hclV⟩ :=
        oriented_band_sides c hDbandAvoidC
      obtain ⟨W,Z,hWo,hZo,hWc,hZc,hWZ,hcoverd,hDW,hclW,hclZ⟩ :=
        oriented_band_sides d hDbandAvoidD
      have hdU : d.image ⊆ U := by
        have hsub : d.image ⊆ U ∪ V := by
          rw [hcoverc]
          exact fun x hx hc => Set.disjoint_left.mp hd hc hx
        have hdc : IsPreconnected d.image :=
          (isConnected_range d.embedded.continuous).isPreconnected
        rcases hdc.subset_or_subset hUo hVo hUV hsub with hdU | hdV
        · exact hdU
        · have hpointD : Bsmall (1,⟨0,by norm_num⟩) ∈ d.image := (hBsmallD _ _).mpr rfl
          have hpointCl := closure_mono hDU (hbandClosure 1 ⟨0,by norm_num⟩)
          rw [hclU] at hpointCl
          exact False.elim (hpointCl.elim
            (fun hpU => Set.disjoint_left.mp hUV hpU (hdV hpointD))
            (fun hpC => Set.disjoint_left.mp hd hpC hpointD))
      have hcW : c.image ⊆ W := by
        have hsub : c.image ⊆ W ∪ Z := by
          rw [hcoverd]
          exact fun x hx hdmem => Set.disjoint_left.mp hd hx hdmem
        have hcc : IsPreconnected c.image :=
          (isConnected_range c.embedded.continuous).isPreconnected
        rcases hcc.subset_or_subset hWo hZo hWZ hsub with hcW | hcZ
        · exact hcW
        · have hpointC : Bsmall (0,⟨0,by norm_num⟩) ∈ c.image := (hBsmallC _ _).mpr rfl
          have hpointCl := closure_mono hDW (hbandClosure 0 ⟨0,by norm_num⟩)
          rw [hclW] at hpointCl
          exact False.elim (hpointCl.elim
            (fun hpW => Set.disjoint_left.mp hWZ hpW (hcZ hpointC))
            (fun hpD => Set.disjoint_left.mp hd hpointC hpD))
      have hVsubW : V ⊆ W := by
        have hVavoid : V ⊆ d.imageᶜ :=
          fun x hx hdx => Set.disjoint_left.mp hUV (hdU hdx) hx
        have hsub : V ⊆ W ∪ Z := by rwa [hcoverd]
        rcases hVc.isPreconnected.subset_or_subset hWo hZo hWZ hsub with hVW | hVZ
        · exact hVW
        · let y := c.map 1
          have hyc : y ∈ c.image := Set.mem_range_self _
          have hycl : y ∈ closure V := by rw [hclV]; exact Or.inr hyc
          have hyz := closure_mono hVZ hycl
          rw [hclZ] at hyz
          exact False.elim (hyz.elim
            (fun hz => Set.disjoint_left.mp hWZ (hcW hyc) hz)
            (fun hyd => Set.disjoint_left.mp hd hyc hyd))
      have hBandDisjointV : Disjoint (Set.range Bsmall) V := by
        apply Set.disjoint_left.mpr
        intro x hx hxV
        have hcl := closure_mono hDU (hbandRangeClosure hx)
        rw [hclU] at hcl
        rcases hcl with hxU | hxC
        · exact Set.disjoint_left.mp hUV hxU hxV
        · have hh : x ∈ c.imageᶜ := by rw [← hcoverc]; exact Or.inr hxV
          exact hh hxC
      obtain ⟨omitted,homittedV⟩ := hVc.nonempty
      have homittedC : omitted ∉ c.image := by
        have hh : omitted ∈ c.imageᶜ := by rw [← hcoverc]; exact Or.inr homittedV
        exact hh
      have homittedD : omitted ∉ d.image := by
        intro hmem
        exact Set.disjoint_left.mp hUV (hdU hmem) homittedV
      have homittedBand : omitted ∉ Set.range Bsmall :=
        fun hmem => Set.disjoint_left.mp hBandDisjointV hmem homittedV
      let minus : Set.Icc (-1:ℝ) 1 := ⟨-1,by norm_num⟩
      let plus : Set.Icc (-1:ℝ) 1 := ⟨1,by norm_num⟩
      have htransverse0 : transverse 0=minus := Subtype.ext (by norm_num [transverse,minus])
      have htransverse1 : transverse 1=plus := Subtype.ext (by norm_num [transverse,plus])
      have hcmeetBand : Set.range ccomplement ∩ Set.range Bsmall={Bsmall (0,minus),Bsmall (0,plus)} := by
        simpa only [cport,ContinuousMap.coe_mk,htransverse0,htransverse1] using hccomplementBand
      have hdmeetBand : Set.range dcomplement ∩ Set.range Bsmall={Bsmall (1,minus),Bsmall (1,plus)} := by
        simpa only [dport,ContinuousMap.coe_mk,htransverse0,htransverse1] using hdcomplementBand
      have band_side_meet (f : C(Interval,S)) (k : Interval)
          (hmeet : Set.range f ∩ Set.range Bsmall={Bsmall (k,minus),Bsmall (k,plus)})
          (u : Interval) (w : Set.Icc (-1:ℝ) 1) (hx : Bsmall (u,w) ∈ Set.range f) : u=k := by
        have hpoint : Bsmall (u,w) ∈ ({Bsmall (k,minus),Bsmall (k,plus)}:Set S) :=
          hmeet ▸ ⟨hx,Set.mem_range_self _⟩
        rcases hpoint with he | he
        · exact congrArg Prod.fst (hBsmall.injective he)
        · exact congrArg Prod.fst (hBsmall.injective he)
      let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
      let gapChart := stereographic' 2 (M.sphere omitted)
      have hgapSource : gapChart.source={M.sphere omitted}ᶜ := stereographic'_source _
      have hgapTarget : gapChart.target=Set.univ := stereographic'_target _
      let gapSphere : {x : S // x ≠ omitted} ≃ₜ gapChart.source :=
        M.sphere.subtype (fun x => by simp only [hgapSource,Set.mem_compl_iff,
          Set.mem_singleton_iff,M.sphere.injective.eq_iff])
      let gapPlane : {x : S // x ≠ omitted} ≃ₜ Plane := gapSphere.trans
        (gapChart.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr hgapTarget).trans
          (Homeomorph.Set.univ _)))
      let Pband : C(Interval × Set.Icc (-1:ℝ) 1,Plane) :=
        ⟨fun p => gapPlane ⟨Bsmall p,fun he => homittedBand (he ▸ Set.mem_range_self p)⟩,
          gapPlane.continuous.comp (Bsmall.continuous.subtype_mk _)⟩
      have hPband : Topology.IsEmbedding Pband := (Pband.continuous.isClosedEmbedding (by
        intro p q he
        apply hBsmall.injective
        exact congrArg Subtype.val (gapPlane.injective he))).isEmbedding
      let Cedge : C(Interval,Plane) :=
        ⟨fun t => gapPlane ⟨ccomplement t,fun he => homittedC (he ▸ hccomplementSub (Set.mem_range_self t))⟩,
          gapPlane.continuous.comp (ccomplement.continuous.subtype_mk _)⟩
      let Dedge : C(Interval,Plane) :=
        ⟨fun t => gapPlane ⟨dcomplement t,fun he => homittedD (he ▸ hdcomplementSub (Set.mem_range_self t))⟩,
          gapPlane.continuous.comp (dcomplement.continuous.subtype_mk _)⟩
      have hCedge : Topology.IsEmbedding Cedge := (Cedge.continuous.isClosedEmbedding (by
        intro t u he
        apply hccomplement.injective
        exact congrArg Subtype.val (gapPlane.injective he))).isEmbedding
      have hDedge : Topology.IsEmbedding Dedge := (Dedge.continuous.isClosedEmbedding (by
        intro t u he
        apply hdcomplement.injective
        exact congrArg Subtype.val (gapPlane.injective he))).isEmbedding
      let Ledge : C(Interval,Plane) := ⟨fun t => Pband (t,minus),
        Pband.continuous.comp (continuous_id.prodMk continuous_const)⟩
      let Redge : C(Interval,Plane) := ⟨fun t => Pband (t,plus),
        Pband.continuous.comp (continuous_id.prodMk continuous_const)⟩
      have hLedge : Topology.IsEmbedding Ledge := (Ledge.continuous.isClosedEmbedding (by
        intro t u he
        exact congrArg Prod.fst (hPband.injective he))).isEmbedding
      have hRedge : Topology.IsEmbedding Redge := (Redge.continuous.isClosedEmbedding (by
        intro t u he
        exact congrArg Prod.fst (hPband.injective he))).isEmbedding
      have hCedge0 : Cedge 0=Ledge 0 := by
        apply congrArg gapPlane
        apply Subtype.ext
        change ccomplement 0=Bsmall (0,minus)
        rw [hccomplement0]
        change Bsmall (0,transverse 0)=_
        rw [htransverse0]
      have hCedge1 : Cedge 1=Redge 0 := by
        apply congrArg gapPlane
        apply Subtype.ext
        change ccomplement 1=Bsmall (0,plus)
        rw [hccomplement1]
        change Bsmall (0,transverse 1)=_
        rw [htransverse1]
      have hDedge0 : Dedge 0=Ledge 1 := by
        apply congrArg gapPlane
        apply Subtype.ext
        change dcomplement 0=Bsmall (1,minus)
        rw [hdcomplement0]
        change Bsmall (1,transverse 0)=_
        rw [htransverse0]
      have hDedge1 : Dedge 1=Redge 1 := by
        apply congrArg gapPlane
        apply Subtype.ext
        change dcomplement 1=Bsmall (1,plus)
        rw [hdcomplement1]
        change Bsmall (1,transverse 1)=_
        rw [htransverse1]
      have hCbandMeet (t u : Interval) (w : Set.Icc (-1:ℝ) 1)
          (he : Cedge t=Pband (u,w)) : u=0 := by
        have hh : ccomplement t=Bsmall (u,w) :=
          congrArg Subtype.val (gapPlane.injective he)
        exact band_side_meet ccomplement 0 hcmeetBand u w ⟨t,hh⟩
      have hDbandMeet (t u : Interval) (w : Set.Icc (-1:ℝ) 1)
          (he : Dedge t=Pband (u,w)) : u=1 := by
        have hh : dcomplement t=Bsmall (u,w) :=
          congrArg Subtype.val (gapPlane.injective he)
        exact band_side_meet dcomplement 1 hdmeetBand u w ⟨t,hh⟩
      have hCDdisjoint : Disjoint (Set.range Cedge) (Set.range Dedge) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh : dcomplement u=ccomplement t :=
          congrArg Subtype.val (gapPlane.injective he)
        exact Set.disjoint_left.mp hcomplementsDisjoint ⟨t,rfl⟩ ⟨u,hh⟩
      have hLRdisjoint : Disjoint (Set.range Ledge) (Set.range Redge) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hPband.injective he)
        change (1:ℝ)=-1 at hh
        norm_num at hh
      have hCRmeet : ∀ x ∈ Set.range Cedge, x ∈ Set.range Redge → x=Cedge 1 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hu := hCbandMeet t u plus he.symm
        exact he.symm.trans ((congrArg Redge hu).trans hCedge1.symm)
      have hCLmeet : ∀ x ∈ Set.range Cedge, x ∈ Set.range Ledge → x=Cedge 0 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hu := hCbandMeet t u minus he.symm
        exact he.symm.trans ((congrArg Ledge hu).trans hCedge0.symm)
      have hDRmeet : ∀ x ∈ Set.range Dedge, x ∈ Set.range Redge → x=Dedge 1 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hu := hDbandMeet t u plus he.symm
        exact he.symm.trans ((congrArg Redge hu).trans hDedge1.symm)
      have hDLmeet : ∀ x ∈ Set.range Dedge, x ∈ Set.range Ledge → x=Dedge 0 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hu := hDbandMeet t u minus he.symm
        exact he.symm.trans ((congrArg Ledge hu).trans hDedge0.symm)
      have interval_isArcBetween (f : C(Interval,Plane)) (hf : Topology.IsEmbedding f) :
          IsArcBetween (Set.range f) (f 0) (f 1) := by
        let F : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
        have hFc : Continuous F := f.continuous.comp continuous_projIcc
        have hval (t : Interval) : F t=f t := by
          simp [F,Set.projIcc_of_mem zero_le_one t.property]
        have hi : InjOn F Interval := by
          intro x hx y hy he
          have hh : f ⟨x,hx⟩=f ⟨y,hy⟩ := by simpa only [← hval] using he
          exact congrArg Subtype.val (hf.injective hh)
        have hr : F '' Interval=Set.range f := by
          ext x
          constructor
          · rintro ⟨t,ht,rfl⟩
            exact ⟨⟨t,ht⟩,(hval ⟨t,ht⟩).symm⟩
          · rintro ⟨t,rfl⟩
            exact ⟨t,t.property,hval t⟩
        exact ⟨F,hFc.continuousOn,hi,hr,hval 0,hval 1⟩
      have hCarc := interval_isArcBetween Cedge hCedge
      have hDarc := interval_isArcBetween Dedge hDedge
      have hLarc := interval_isArcBetween Ledge hLedge
      have hRarc := interval_isArcBetween Redge hRedge
      have hCRarc : IsArcBetween (Set.range Cedge ∪ Set.range Redge) (Cedge 0) (Redge 1) :=
        hCarc.concatenate (by simpa only [hCedge1] using hRarc) hCRmeet
      have hDLarc : IsArcBetween (Set.range Dedge ∪ Set.range Ledge) (Redge 1) (Cedge 0) := by
        have hh := hDarc.reverse.concatenate (by simpa only [hDedge0] using hLarc.reverse) hDLmeet
        simpa only [hDedge1,hCedge0] using hh
      have hJordanBoundary : IsJordanCurve
          ((Set.range Cedge ∪ Set.range Redge) ∪ (Set.range Dedge ∪ Set.range Ledge)) := by
        apply IsJordanCurve.of_two_arcs hCRarc hDLarc
        intro x hx hy
        rcases hx with hxC | hxR <;> rcases hy with hyD | hyL
        · exact False.elim (Set.disjoint_left.mp hCDdisjoint hxC hyD)
        · exact Or.inl (hCLmeet x hxC hyL)
        · exact Or.inr ((hDRmeet x hyD hxR).trans hDedge1)
        · exact False.elim (Set.disjoint_left.mp hLRdisjoint hyL hxR)
      let Jboundary : Set Plane :=
        (Set.range Cedge ∪ Set.range Redge) ∪ (Set.range Dedge ∪ Set.range Ledge)
      have hJboundary : IsJordanCurve Jboundary := hJordanBoundary
      let back : C(Plane,S) := ⟨fun x => (gapPlane.symm x).val,
        continuous_subtype_val.comp gapPlane.symm.continuous⟩
      have hbackEmbedding : Topology.IsOpenEmbedding back := by
        have ho : IsOpen {x : S | x ≠ omitted} := isClosed_singleton.isOpen_compl
        exact ho.isOpenEmbedding_subtypeVal.comp gapPlane.symm.isOpenEmbedding
      have hbackC (t : Interval) : back (Cedge t)=ccomplement t :=
        congrArg Subtype.val (gapPlane.symm_apply_apply _)
      have hbackD (t : Interval) : back (Dedge t)=dcomplement t :=
        congrArg Subtype.val (gapPlane.symm_apply_apply _)
      have hbackBand (p : Interval × Set.Icc (-1:ℝ) 1) : back (Pband p)=Bsmall p :=
        congrArg Subtype.val (gapPlane.symm_apply_apply _)
      let Lsource : C(Interval,S) := ⟨fun t => Bsmall (t,minus),
        Bsmall.continuous.comp (continuous_id.prodMk continuous_const)⟩
      let Rsource : C(Interval,S) := ⟨fun t => Bsmall (t,plus),
        Bsmall.continuous.comp (continuous_id.prodMk continuous_const)⟩
      let Jsource : Set S :=
        (Set.range ccomplement ∪ Set.range Rsource) ∪ (Set.range dcomplement ∪ Set.range Lsource)
      have hbackJ : back '' Jboundary=Jsource := by
        have himage (f : C(Interval,Plane)) (g : C(Interval,S)) (he : ∀ t,back (f t)=g t) :
            back '' Set.range f=Set.range g := by
          rw [← Set.range_comp]
          exact congrArg Set.range (funext he)
        rw [Set.image_union,Set.image_union,Set.image_union,
          himage Cedge ccomplement hbackC,himage Dedge dcomplement hbackD,
          himage Redge Rsource (fun t => hbackBand (t,plus)),
          himage Ledge Lsource (fun t => hbackBand (t,minus))]
      let remainingInterior : Set S := back '' Schoenflies.inside Jboundary
      let remainingClosed : Set S := back '' closure (Schoenflies.inside Jboundary)
      have hremainingOpen : IsOpen remainingInterior :=
        hbackEmbedding.isOpenMap _ (Schoenflies.isOpen_inside hJboundary.isClosed)
      have hremainingCompact : IsCompact remainingClosed :=
        (Metric.isCompact_of_isClosed_isBounded isClosed_closure
          (jordan_curve_theorem hJboundary).isBounded_inside.closure).image back.continuous
      have hremainingClosed : IsClosed remainingClosed := hremainingCompact.isClosed
      have hremainingUnion : remainingClosed=remainingInterior ∪ Jsource := by
        have hcl : closure (Schoenflies.inside Jboundary)=Schoenflies.inside Jboundary ∪ Jboundary :=
          (Schoenflies.IsRegionOf.inside Jboundary).closure_eq (jordan_curve_theorem hJboundary)
        change back '' closure (Schoenflies.inside Jboundary)=_
        rw [hcl,Set.image_union,hbackJ]
      have hremainingInteriorSub : remainingInterior ⊆ remainingClosed := by
        exact Set.image_mono subset_closure
      have hremainingJSub : Jsource ⊆ remainingClosed := by
        rw [hremainingUnion]
        exact Set.subset_union_right
      have homittedRemaining : omitted ∉ remainingClosed := by
        rintro ⟨x,hx,he⟩
        exact (gapPlane.symm x).property he
      have hVoffJ : V ⊆ Jsourceᶜ := by
        intro x hxV hxJ
        rcases hxJ with (hxC | hxR) | (hxD | hxL)
        · have hx : x ∈ c.image := hccomplementSub hxC
          have hh : x ∈ c.imageᶜ := by rw [← hcoverc];exact Or.inr hxV
          exact hh hx
        · obtain ⟨t,ht⟩ := hxR
          exact Set.disjoint_left.mp hBandDisjointV ⟨(t,plus),ht⟩ hxV
        · exact Set.disjoint_left.mp hUV (hdU (hdcomplementSub hxD)) hxV
        · obtain ⟨t,ht⟩ := hxL
          exact Set.disjoint_left.mp hBandDisjointV ⟨(t,minus),ht⟩ hxV
      have hremainingDisjointV : Disjoint remainingClosed V := by
        have hsub : V ⊆ remainingInterior ∪ remainingClosedᶜ := by
          intro x hxV
          by_cases hxK : x ∈ remainingClosed
          · left
            rw [hremainingUnion] at hxK
            exact hxK.resolve_right (hVoffJ hxV)
          · exact Or.inr hxK
        have hdisj : Disjoint remainingInterior remainingClosedᶜ :=
          Set.disjoint_left.mpr (fun x hxI hxK => hxK (hremainingInteriorSub hxI))
        rcases hVc.isPreconnected.subset_or_subset hremainingOpen hremainingClosed.isOpen_compl
          hdisj hsub with hVI | hVoutside
        · exact False.elim (homittedRemaining (hremainingInteriorSub (hVI homittedV)))
        · exact Set.disjoint_left.mpr (fun x hxK hxV => hVoutside hxV hxK)
      have hbandCoreOffJ (u : Interval) (w : Set.Icc (-1:ℝ) 1)
          (hw0 : -1 < (w:ℝ)) (hw1 : (w:ℝ)<1) : Bsmall (u,w) ∉ Jsource := by
        intro hxJ
        rcases hxJ with (hxC | hxR) | (hxD | hxL)
        · have hpoint : Bsmall (u,w) ∈ ({Bsmall (0,minus),Bsmall (0,plus)}:Set S) :=
            hcmeetBand ▸ ⟨hxC,Set.mem_range_self _⟩
          rcases hpoint with he | he
          · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
            change (w:ℝ)=-1 at hh
            linarith
          · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
            change (w:ℝ)=1 at hh
            linarith
        · obtain ⟨t,ht⟩ := hxR
          have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective ht)
          change (1:ℝ)=(w:ℝ) at hh
          linarith
        · have hpoint : Bsmall (u,w) ∈ ({Bsmall (1,minus),Bsmall (1,plus)}:Set S) :=
            hdmeetBand ▸ ⟨hxD,Set.mem_range_self _⟩
          rcases hpoint with he | he
          · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
            change (w:ℝ)=-1 at hh
            linarith
          · have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective he)
            change (w:ℝ)=1 at hh
            linarith
        · obtain ⟨t,ht⟩ := hxL
          have hh := congrArg (fun p : Interval × Set.Icc (-1:ℝ) 1 => (p.2:ℝ)) (hBsmall.injective ht)
          change (-1:ℝ)=(w:ℝ) at hh
          linarith
      let BandCore : Set S := Bsmall '' ((Set.univ : Set Interval) ×ˢ Set.Ioo minus plus)
      have hWidthCoreConnected : IsConnected (Set.Ioo minus plus) := by
        have himage : Set.projIcc (-1:ℝ) 1 (by norm_num) '' Set.Ioo (-1:ℝ) 1=Set.Ioo minus plus := by
          ext w
          constructor
          · rintro ⟨x,hx,rfl⟩
            have hh := Set.projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1) ⟨hx.1.le,hx.2.le⟩
            change -1 < (Set.projIcc (-1:ℝ) 1 (by norm_num) x:ℝ) ∧
              (Set.projIcc (-1:ℝ) 1 (by norm_num) x:ℝ)<1
            simpa only [hh,Set.mem_Ioo] using hx
          · intro hw
            refine ⟨(w:ℝ),hw,?_⟩
            exact Set.projIcc_of_mem (by norm_num) w.property
        rw [← himage]
        exact (isConnected_Ioo (by norm_num : (-1:ℝ)<1)).image _ continuous_projIcc.continuousOn
      have hBandCoreConnected : IsConnected BandCore :=
        (isConnected_univ.prod hWidthCoreConnected).image _ Bsmall.continuous.continuousOn
      have hBandCoreOffJ : BandCore ⊆ Jsourceᶜ := by
        rintro x ⟨⟨u,w⟩,⟨hu,hw⟩,rfl⟩
        exact hbandCoreOffJ u w hw.1 hw.2
      have hBandCoreOutside : BandCore ⊆ remainingClosedᶜ := by
        have hsub : BandCore ⊆ remainingInterior ∪ remainingClosedᶜ := by
          intro x hxB
          by_cases hxK : x ∈ remainingClosed
          · left
            rw [hremainingUnion] at hxK
            exact hxK.resolve_right (hBandCoreOffJ hxB)
          · exact Or.inr hxK
        have hdisj : Disjoint remainingInterior remainingClosedᶜ :=
          Set.disjoint_left.mpr (fun x hxI hxK => hxK (hremainingInteriorSub hxI))
        rcases hBandCoreConnected.isPreconnected.subset_or_subset hremainingOpen hremainingClosed.isOpen_compl
          hdisj hsub with hBI | hBoutside
        · let wzero : Set.Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
          have hxB : Bsmall (0,wzero) ∈ BandCore := ⟨(0,wzero),⟨Set.mem_univ _,by
            constructor <;> norm_num [minus,plus,wzero]⟩,rfl⟩
          have hxC : Bsmall (0,wzero) ∈ c.image := (hBsmallC _ _).mpr rfl
          have hxClV : Bsmall (0,wzero) ∈ closure V := by rw [hclV];exact Or.inr hxC
          have hVnotI : V ⊆ remainingInteriorᶜ :=
            fun x hxV hxI => Set.disjoint_left.mp hremainingDisjointV (hremainingInteriorSub hxI) hxV
          have hclVnotI : closure V ⊆ remainingInteriorᶜ :=
            closure_minimal hVnotI hremainingOpen.isClosed_compl
          exact False.elim (hclVnotI hxClV (hBI hxB))
        · exact hBoutside
      have hRemainingBandSeams : remainingClosed ∩ Set.range Bsmall=
          Set.range Lsource ∪ Set.range Rsource := by
        ext x
        constructor
        · rintro ⟨hxK,⟨⟨u,w⟩,rfl⟩⟩
          by_cases hwminus : w=minus
          · left
            exact ⟨u,by change Bsmall (u,minus)=_;rw [hwminus]⟩
          · by_cases hwplus : w=plus
            · right
              exact ⟨u,by change Bsmall (u,plus)=_;rw [hwplus]⟩
            · have hw0 : minus<w := lt_of_le_of_ne w.property.1 (Ne.symm hwminus)
              have hw1 : w<plus := lt_of_le_of_ne w.property.2 hwplus
              exact False.elim (hBandCoreOutside ⟨(u,w),⟨Set.mem_univ _,⟨hw0,hw1⟩⟩,rfl⟩ hxK)
        · rintro (⟨u,rfl⟩ | ⟨u,rfl⟩)
          · exact ⟨hremainingJSub (Or.inr (Or.inr ⟨u,rfl⟩)),⟨(u,minus),rfl⟩⟩
          · exact ⟨hremainingJSub (Or.inl (Or.inr ⟨u,rfl⟩)),⟨(u,plus),rfl⟩⟩
      obtain ⟨remainingDisk,hremainingDiskBoundary,hremainingDiskInterior⟩ :=
        CurveComplex.SpherePort.plane_inside_closed_disc_with_boundary Jboundary hJboundary
      let actualRemainingDisk : C(Metric.closedBall (0:Plane) 1,S) :=
        ⟨fun x => back (remainingDisk x),back.continuous.comp
          (continuous_subtype_val.comp remainingDisk.continuous)⟩
      have hactualRemainingDisk : Topology.IsEmbedding actualRemainingDisk :=
        hbackEmbedding.isEmbedding.comp (Topology.IsEmbedding.subtypeVal.comp remainingDisk.isEmbedding)
      have hactualRemainingRange : Set.range actualRemainingDisk=remainingClosed := by
        ext x
        constructor
        · rintro ⟨z,rfl⟩
          exact ⟨remainingDisk z,(remainingDisk z).property,rfl⟩
        · rintro ⟨z,hz,rfl⟩
          refine ⟨remainingDisk.symm ⟨z,hz⟩,?_⟩
          change back (remainingDisk (remainingDisk.symm ⟨z,hz⟩))=back z
          rw [remainingDisk.apply_symm_apply]
      have hactualRemainingBandSeams : Set.range actualRemainingDisk ∩ Set.range Bsmall=
          Set.range Lsource ∪ Set.range Rsource := by
        rw [hactualRemainingRange]
        exact hRemainingBandSeams
      have four_edge_loop (C D L R : C(Interval,Plane))
          (hC : Topology.IsEmbedding C) (hD : Topology.IsEmbedding D)
          (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding R)
          (hC0 : C 0=L 0) (hC1 : C 1=R 0) (hD0 : D 0=L 1) (hD1 : D 1=R 1)
          (hCD : Disjoint (Set.range C) (Set.range D))
          (hLR : Disjoint (Set.range L) (Set.range R))
          (hCR : ∀ x ∈ Set.range C,x ∈ Set.range R → x=C 1)
          (hCL : ∀ x ∈ Set.range C,x ∈ Set.range L → x=C 0)
          (hDR : ∀ x ∈ Set.range D,x ∈ Set.range R → x=D 1)
          (hDL : ∀ x ∈ Set.range D,x ∈ Set.range L → x=D 0) :
          ∃ f : ℝ → Plane, IsLoop f ∧
            f '' Interval=((Set.range C ∪ Set.range R) ∪ (Set.range D ∪ Set.range L)) ∧
            ∀ t : Interval, f ((t:ℝ)/4)=C t ∧ f (((t:ℝ)+1)/4)=R t ∧
              f ((3-(t:ℝ))/4)=D t ∧ f (1-(t:ℝ)/4)=L t := by
        have raw_arc (g : C(Interval,Plane)) (hg : Topology.IsEmbedding g) :
            ∃ F : ℝ → Plane, ContinuousOn F Interval ∧ InjOn F Interval ∧
              F '' Interval=Set.range g ∧ ∀ t : Interval,F (t:ℝ)=g t := by
          let F : ℝ → Plane := g ∘ Set.projIcc 0 1 zero_le_one
          have hval (t : Interval) : F (t:ℝ)=g t := by
            simp [F,Set.projIcc_of_mem zero_le_one t.property]
          refine ⟨F,(g.continuous.comp continuous_projIcc).continuousOn,?_,?_,hval⟩
          · intro x hx y hy he
            have hh : g ⟨x,hx⟩=g ⟨y,hy⟩ := by simpa only [← hval] using he
            exact congrArg Subtype.val (hg.injective hh)
          · ext x
            constructor
            · rintro ⟨t,ht,rfl⟩
              exact ⟨⟨t,ht⟩,(hval ⟨t,ht⟩).symm⟩
            · rintro ⟨t,rfl⟩
              exact ⟨t,t.property,hval t⟩
        let Dr : C(Interval,Plane) := D.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩
        let Lr : C(Interval,Plane) := L.comp ⟨unitInterval.symm,unitInterval.continuous_symm⟩
        have hDr : Topology.IsEmbedding Dr := (Dr.continuous.isClosedEmbedding
          (hD.injective.comp unitInterval.symm_involutive.injective)).isEmbedding
        have hLr : Topology.IsEmbedding Lr := (Lr.continuous.isClosedEmbedding
          (hL.injective.comp unitInterval.symm_involutive.injective)).isEmbedding
        have hDrange : Set.range Dr=Set.range D := by
          ext x
          constructor
          · rintro ⟨t,rfl⟩
            exact ⟨unitInterval.symm t,rfl⟩
          · rintro ⟨t,rfl⟩
            exact ⟨unitInterval.symm t,by simp [Dr,Lr]⟩
        have hLrange : Set.range Lr=Set.range L := by
          ext x
          constructor
          · rintro ⟨t,rfl⟩
            exact ⟨unitInterval.symm t,rfl⟩
          · rintro ⟨t,rfl⟩
            exact ⟨unitInterval.symm t,by simp [Dr,Lr]⟩
        obtain ⟨craw,hcc,hci,hcr,hcv⟩ := raw_arc C hC
        obtain ⟨rraw,hrc,hri,hrr,hrv⟩ := raw_arc R hR
        obtain ⟨draw,hdc,hdi,hdr,hdv⟩ := raw_arc Dr hDr
        obtain ⟨lraw,hlc,hli,hlr,hlv⟩ := raw_arc Lr hLr
        have hc0 : craw 0=C 0 := hcv 0
        have hc1 : craw 1=C 1 := hcv 1
        have hr0 : rraw 0=R 0 := hrv 0
        have hr1 : rraw 1=R 1 := hrv 1
        have hd0 : draw 0=D 1 := by simpa [Dr] using hdv 0
        have hd1 : draw 1=D 0 := by simpa [Dr] using hdv 1
        have hl0 : lraw 0=L 1 := by simpa [Lr] using hlv 0
        have hl1 : lraw 1=L 0 := by simpa [Lr] using hlv 1
        have hcmid : craw 1=rraw 0 := hc1.trans (hC1.trans hr0.symm)
        have hdmid : draw 1=lraw 0 := hd1.trans (hD0.trans hl0.symm)
        have hcmeet : ∀ x ∈ craw '' Interval,x ∈ rraw '' Interval → x=craw 1 := by
          intro x hx hy
          rw [hcr] at hx
          rw [hrr] at hy
          exact (hCR x hx hy).trans hc1.symm
        have hdmeet : ∀ x ∈ draw '' Interval,x ∈ lraw '' Interval → x=draw 1 := by
          intro x hx hy
          rw [hdr,hDrange] at hx
          rw [hlr,hLrange] at hy
          exact (hDL x hx hy).trans hd1.symm
        let F := Schoenflies.concatenate craw rraw
        let G := Schoenflies.concatenate draw lraw
        have hFc : ContinuousOn F Interval := continuousOn_concatenate hcc hrc hcmid
        have hGc : ContinuousOn G Interval := continuousOn_concatenate hdc hlc hdmid
        have hFi : InjOn F Interval := injOn_concatenate hci hri hcmid hcmeet
        have hGi : InjOn G Interval := injOn_concatenate hdi hli hdmid hdmeet
        have hFr : F '' Interval=Set.range C ∪ Set.range R := by
          rw [image_concatenate hcmid,hcr,hrr]
        have hGr : G '' Interval=Set.range D ∪ Set.range L := by
          rw [image_concatenate hdmid,hdr,hlr,hDrange,hLrange]
        have hF0 : F 0=C 0 := (concatenate_zero).trans hc0
        have hF1 : F 1=R 1 := (concatenate_one).trans hr1
        have hG0 : G 0=D 1 := (concatenate_zero).trans hd0
        have hG1 : G 1=L 0 := (concatenate_one).trans hl1
        have hmid : F 1=G 0 := hF1.trans (hD1.symm.trans hG0.symm)
        have hclose : G 1=F 0 := hG1.trans (hC0.symm.trans hF0.symm)
        have hmeet : ∀ x ∈ F '' Interval,x ∈ G '' Interval → x=F 0 ∨ x=F 1 := by
          intro x hx hy
          rw [hFr] at hx
          rw [hGr] at hy
          rcases hx with hxC | hxR <;> rcases hy with hyD | hyL
          · exact False.elim (Set.disjoint_left.mp hCD hxC hyD)
          · exact Or.inl ((hCL x hxC hyL).trans hF0.symm)
          · exact Or.inr ((hDR x hyD hxR).trans (hD1.trans hF1.symm))
          · exact False.elim (Set.disjoint_left.mp hLR hyL hxR)
        let f := Schoenflies.concatenate F G
        refine ⟨f,IsLoop.concatenate hFc hFi hGc hGi hmid hclose hmeet,?_,?_⟩
        · rw [image_concatenate hmid,hFr,hGr]
        · intro t
          refine ⟨?_,?_,?_,?_⟩
          · change Schoenflies.concatenate F G ((t:ℝ)/4)=C t
            rw [concatenate_of_le (by linarith [t.property.2])]
            change Schoenflies.concatenate craw rraw (2*((t:ℝ)/4))=C t
            rw [concatenate_of_le (by linarith [t.property.2])]
            convert hcv t using 1 <;> congr 1 <;> ring
          · change Schoenflies.concatenate F G (((t:ℝ)+1)/4)=R t
            rw [concatenate_of_le (by linarith [t.property.2])]
            change Schoenflies.concatenate craw rraw (2*(((t:ℝ)+1)/4))=R t
            rw [concatenate_upperHalf hcmid ⟨by linarith [t.property.1],by linarith [t.property.2]⟩]
            convert hrv t using 1 <;> congr 1 <;> ring
          · change Schoenflies.concatenate F G ((3-(t:ℝ))/4)=D t
            rw [concatenate_upperHalf hmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
            change Schoenflies.concatenate draw lraw (2*((3-(t:ℝ))/4)-1)=D t
            rw [concatenate_of_le (by linarith [t.property.1])]
            have hh := hdv (unitInterval.symm t)
            simpa only [Dr,ContinuousMap.comp_apply,ContinuousMap.coe_mk,unitInterval.symm_symm] using
              (show draw (2*(2*((3-(t:ℝ))/4)-1))=Dr (unitInterval.symm t) from by
                convert hh using 1 <;> congr 1 <;> change _=1-(t:ℝ) <;> ring)
          · change Schoenflies.concatenate F G (1-(t:ℝ)/4)=L t
            rw [concatenate_upperHalf hmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
            change Schoenflies.concatenate draw lraw (2*(1-(t:ℝ)/4)-1)=L t
            rw [concatenate_upperHalf hdmid ⟨by linarith [t.property.2],by linarith [t.property.1]⟩]
            have hh := hlv (unitInterval.symm t)
            simpa only [Lr,ContinuousMap.comp_apply,ContinuousMap.coe_mk,unitInterval.symm_symm] using
              (show lraw (2*(2*(1-(t:ℝ)/4)-1)-1)=Lr (unitInterval.symm t) from by
                convert hh using 1 <;> congr 1 <;> change _=1-(t:ℝ) <;> ring)
      obtain ⟨actualBoundaryLoop,hactualBoundaryLoop,hactualBoundaryLoopRange,hactualBoundaryQuarter⟩ :=
        four_edge_loop Cedge Dedge Ledge Redge hCedge hDedge hLedge hRedge
          hCedge0 hCedge1 hDedge0 hDedge1 hCDdisjoint hLRdisjoint hCRmeet hCLmeet hDRmeet hDLmeet
      let horizontal (a : ℝ) : C(Interval,Plane) := ⟨fun t => Plane.mk (2*(t:ℝ)-1) a,by fun_prop⟩
      let vertical (a : ℝ) : C(Interval,Plane) := ⟨fun t => Plane.mk a (2*(t:ℝ)-1),by fun_prop⟩
      have hhorizontal (a : ℝ) : Topology.IsEmbedding (horizontal a) :=
        ((horizontal a).continuous.isClosedEmbedding (by
          intro t u he
          have hh := congrArg (fun x : Plane => x 0) he
          apply Subtype.ext
          change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
          linarith)).isEmbedding
      have hvertical (a : ℝ) : Topology.IsEmbedding (vertical a) :=
        ((vertical a).continuous.isClosedEmbedding (by
          intro t u he
          have hh := congrArg (fun x : Plane => x 1) he
          apply Subtype.ext
          change 2*(t:ℝ)-1=2*(u:ℝ)-1 at hh
          linarith)).isEmbedding
      have hhorizontalRange (a : ℝ) : Set.range (horizontal a)={x : Plane | x 1=a ∧ |x 0| ≤ 1} := by
        ext x
        constructor
        · rintro ⟨t,rfl⟩
          refine ⟨rfl,?_⟩
          change |2*(t:ℝ)-1| ≤ 1
          rw [abs_le]
          constructor <;> linarith [t.property.1,t.property.2]
        · intro hx
          let t : Interval := ⟨(x 0+1)/2,by
            rcases abs_le.mp hx.2 with ⟨hl,hu⟩
            constructor <;> linarith⟩
          refine ⟨t,?_⟩
          ext i
          fin_cases i
          · change 2*((x 0+1)/2)-1=x 0
            ring
          · exact hx.1.symm
      have hverticalRange (a : ℝ) : Set.range (vertical a)={x : Plane | x 0=a ∧ |x 1| ≤ 1} := by
        ext x
        constructor
        · rintro ⟨t,rfl⟩
          refine ⟨rfl,?_⟩
          change |2*(t:ℝ)-1| ≤ 1
          rw [abs_le]
          constructor <;> linarith [t.property.1,t.property.2]
        · intro hx
          let t : Interval := ⟨(x 1+1)/2,by
            rcases abs_le.mp hx.2 with ⟨hl,hu⟩
            constructor <;> linarith⟩
          refine ⟨t,?_⟩
          ext i
          fin_cases i
          · exact hx.1.symm
          · change 2*((x 1+1)/2)-1=x 1
            ring
      have hmC0 : horizontal (-1) 0=vertical (-1) 0 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
      have hmC1 : horizontal (-1) 1=vertical 1 0 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
      have hmD0 : horizontal 1 0=vertical (-1) 1 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
      have hmD1 : horizontal 1 1=vertical 1 1 := by ext i;fin_cases i <;> norm_num [horizontal,vertical]
      have hmCD : Disjoint (Set.range (horizontal (-1))) (Set.range (horizontal 1)) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh := congrArg (fun x : Plane => x 1) he
        change (1:ℝ)=-1 at hh
        norm_num at hh
      have hmLR : Disjoint (Set.range (vertical (-1))) (Set.range (vertical 1)) := by
        apply Set.disjoint_left.mpr
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh := congrArg (fun x : Plane => x 0) he
        change (1:ℝ)=-1 at hh
        norm_num at hh
      have horizontal_vertical_meet (a b : ℝ) (t u : Interval)
          (he : horizontal a t=vertical b u) : horizontal a t=Plane.mk b a := by
        have hh := congrArg (fun x : Plane => x 0) he
        ext i
        fin_cases i
        · exact hh
        · rfl
      have hmCR : ∀ x ∈ Set.range (horizontal (-1)),x ∈ Set.range (vertical 1) → x=horizontal (-1) 1 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh := horizontal_vertical_meet (-1) 1 t u he.symm
        exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
      have hmCL : ∀ x ∈ Set.range (horizontal (-1)),x ∈ Set.range (vertical (-1)) → x=horizontal (-1) 0 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh := horizontal_vertical_meet (-1) (-1) t u he.symm
        exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
      have hmDR : ∀ x ∈ Set.range (horizontal 1),x ∈ Set.range (vertical 1) → x=horizontal 1 1 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh := horizontal_vertical_meet 1 1 t u he.symm
        exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
      have hmDL : ∀ x ∈ Set.range (horizontal 1),x ∈ Set.range (vertical (-1)) → x=horizontal 1 0 := by
        rintro x ⟨t,rfl⟩ ⟨u,he⟩
        have hh := horizontal_vertical_meet 1 (-1) t u he.symm
        exact hh.trans (by ext i;fin_cases i <;> norm_num [horizontal])
      obtain ⟨modelBoundaryLoop,hmodelBoundaryLoop,hmodelBoundaryLoopRange,hmodelBoundaryQuarter⟩ :=
        four_edge_loop (horizontal (-1)) (horizontal 1) (vertical (-1)) (vertical 1)
          (hhorizontal (-1)) (hhorizontal 1) (hvertical (-1)) (hvertical 1)
          hmC0 hmC1 hmD0 hmD1 hmCD hmLR hmCR hmCL hmDR hmDL
      have hmodelRange : modelBoundaryLoop '' Interval=Schoenflies.modelCurve := by
        rw [hmodelBoundaryLoopRange,hhorizontalRange,hhorizontalRange,hverticalRange,hverticalRange,
          Schoenflies.modelCurve_eq_sides]
        ext x
        simp only [Set.mem_union,Set.mem_setOf_eq,Schoenflies.mem_sideTop,Schoenflies.mem_sideLeft,
          Schoenflies.mem_sideBottom,Schoenflies.mem_sideRight]
        tauto
      obtain ⟨matchedBoundary,hmatchedBoundary⟩ := hmodelBoundaryLoop.exists_homeomorph hactualBoundaryLoop
      let boundaryHomeo : Schoenflies.modelCurve ≃ₜ Jboundary :=
        (Homeomorph.setCongr hmodelRange.symm).trans (matchedBoundary.trans
          (Homeomorph.setCongr hactualBoundaryLoopRange))
      have hboundaryLoop (t : ℝ) (ht : t ∈ Interval) :
          (boundaryHomeo ⟨modelBoundaryLoop t,hmodelRange ▸ Set.mem_image_of_mem _ ht⟩).val=actualBoundaryLoop t :=
        hmatchedBoundary t ht
      obtain ⟨boundaryF,boundaryG,hboundaryFG,hboundaryFvalue⟩ :=
        Schoenflies.exists_isHomeoOn_of_homeomorph boundaryHomeo
      obtain ⟨fillF,fillG,hfillFG,hfillBoundary⟩ :=
        Schoenflies.closed_interior_extension Schoenflies.squareExtension
          Schoenflies.isJordanCurve_modelCurve hJboundary hboundaryFG
      have hfillLoop (t : ℝ) (ht : t ∈ Interval) : fillF (modelBoundaryLoop t)=actualBoundaryLoop t := by
        have hx : modelBoundaryLoop t ∈ Schoenflies.modelCurve := hmodelRange ▸ Set.mem_image_of_mem _ ht
        exact (hfillBoundary hx).trans ((hboundaryFvalue _ hx).trans (hboundaryLoop t ht))
      have hclosedJordan : Jboundary ∪ Schoenflies.inside Jboundary=closure (Schoenflies.inside Jboundary) := by
        exact (Set.union_comm _ _).trans
          ((Schoenflies.IsRegionOf.inside Jboundary).closure_eq (jordan_curve_theorem hJboundary)).symm
      have hfill : Schoenflies.IsHomeoOn fillF fillG (Plane.closedSquare 0 1)
          (closure (Schoenflies.inside Jboundary)) := by
        simpa only [Schoenflies.modelCurve_union_inside,hclosedJordan] using hfillFG
      let fillSquare : Plane.closedSquare 0 1 ≃ₜ closure (Schoenflies.inside Jboundary) := {
        toFun := fun x => ⟨fillF x,hfill.mapsTo x.property⟩
        invFun := fun x => ⟨fillG x,hfill.mapsTo_inv x.property⟩
        left_inv := fun x => Subtype.ext (hfill.invOn.1 x.property)
        right_inv := fun x => Subtype.ext (hfill.invOn.2 x.property)
        continuous_toFun := hfill.continuousOn.domRestrict.subtype_mk _
        continuous_invFun := hfill.continuousOn_inv.domRestrict.subtype_mk _ }
      let RawSquare := Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1
      let squarePlane : RawSquare ≃ₜ Plane.closedSquare 0 1 := {
        toFun := fun p => ⟨Plane.mk p.val.1 p.val.2,by
          apply Schoenflies.mem_closedSquare_zero_one.mpr
          exact max_le (abs_le.mpr p.property.1) (abs_le.mpr p.property.2)⟩
        invFun := fun x => ⟨(x.val 0,x.val 1),by
          have hx : max |x.val 0| |x.val 1| ≤ 1 := Schoenflies.mem_closedSquare_zero_one.mp x.property
          exact ⟨abs_le.mp (le_trans (le_max_left _ _) hx),abs_le.mp (le_trans (le_max_right _ _) hx)⟩⟩
        left_inv := by intro p;apply Subtype.ext;rfl
        right_inv := by intro x;apply Subtype.ext;ext i;fin_cases i <;> rfl
        continuous_toFun := by apply Continuous.subtype_mk;fun_prop
        continuous_invFun := by apply Continuous.subtype_mk;fun_prop }
      let : CompactSpace (closure (Schoenflies.inside Jboundary)) :=
        isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded isClosed_closure
          (jordan_curve_theorem hJboundary).isBounded_inside.closure)
      let backClosed : closure (Schoenflies.inside Jboundary) → remainingClosed :=
        fun x => ⟨back x,Set.mem_image_of_mem back x.property⟩
      have hbackClosed : Continuous backClosed := (back.continuous.comp continuous_subtype_val).subtype_mk _
      have hbackClosedBij : Function.Bijective backClosed := by
        constructor
        · intro x y he
          have hh : back x=back y := congrArg (fun z : remainingClosed => z.val) he
          exact Subtype.ext (hbackEmbedding.injective hh)
        · rintro ⟨x,y,hy,rfl⟩
          exact ⟨⟨y,hy⟩,rfl⟩
      let backHomeo : closure (Schoenflies.inside Jboundary) ≃ₜ remainingClosed :=
        Continuous.homeoOfEquivCompactToT2 (f:=Equiv.ofBijective backClosed hbackClosedBij) hbackClosed
      let D₁ : RawSquare ≃ₜ remainingClosed := squarePlane.trans (fillSquare.trans backHomeo)
      have hD₁value (p : RawSquare) : (D₁ p).val=back (fillF (Plane.mk p.val.1 p.val.2)) := rfl
      have hfillC (t : Interval) : fillF (horizontal (-1) t)=Cedge t := by
        have ht : (t:ℝ)/4 ∈ Interval := ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
        have hh := hfillLoop ((t:ℝ)/4) ht
        rw [(hmodelBoundaryQuarter t).1,(hactualBoundaryQuarter t).1] at hh
        exact hh
      have hfillD (t : Interval) : fillF (horizontal 1 t)=Dedge t := by
        have ht : (3-(t:ℝ))/4 ∈ Interval := ⟨by linarith [t.property.2],by linarith [t.property.1]⟩
        have hh := hfillLoop ((3-(t:ℝ))/4) ht
        rw [(hmodelBoundaryQuarter t).2.2.1,(hactualBoundaryQuarter t).2.2.1] at hh
        exact hh
      have hfillL (t : Interval) : fillF (vertical (-1) t)=Ledge t := by
        have ht : 1-(t:ℝ)/4 ∈ Interval := ⟨by linarith [t.property.2],by linarith [t.property.1]⟩
        have hh := hfillLoop (1-(t:ℝ)/4) ht
        rw [(hmodelBoundaryQuarter t).2.2.2,(hactualBoundaryQuarter t).2.2.2] at hh
        exact hh
      have hfillR (t : Interval) : fillF (vertical 1 t)=Redge t := by
        have ht : ((t:ℝ)+1)/4 ∈ Interval := ⟨by linarith [t.property.1],by linarith [t.property.2]⟩
        have hh := hfillLoop (((t:ℝ)+1)/4) ht
        rw [(hmodelBoundaryQuarter t).2.1,(hactualBoundaryQuarter t).2.1] at hh
        exact hh
      have hD₁Left (t : Interval) : (D₁ (squareLeftSeam t)).val=Lsource t := by
        rw [hD₁value]
        change back (fillF (vertical (-1) t))=Lsource t
        rw [hfillL]
        exact hbackBand (t,minus)
      have hD₁Right (t : Interval) : (D₁ (squareRightSeam t)).val=Rsource (unitInterval.symm t) := by
        rw [hD₁value]
        have hh : Plane.mk 1 (1-2*(t:ℝ))=vertical 1 (unitInterval.symm t) := by
          ext i;fin_cases i
          · rfl
          · change 1-2*(t:ℝ)=2*(1-(t:ℝ))-1
            ring
        change back (fillF (Plane.mk 1 (1-2*(t:ℝ))))=Rsource (unitInterval.symm t)
        rw [hh,hfillR]
        exact hbackBand (unitInterval.symm t,plus)
      have hD₁Bottom (t : Interval) : (D₁ (boundaryUnitSquareRaw (t,0))).val=ccomplement t := by
        rw [hD₁value]
        change back (fillF (Plane.mk (2*(t:ℝ)-1) (2*(0:ℝ)-1)))=ccomplement t
        norm_num
        change back (fillF (horizontal (-1) t))=ccomplement t
        rw [hfillC,hbackC]
      have hD₁Top (t : Interval) : (D₁ (boundaryUnitSquareRaw (t,1))).val=dcomplement t := by
        rw [hD₁value]
        change back (fillF (Plane.mk (2*(t:ℝ)-1) (2*(1:ℝ)-1)))=dcomplement t
        norm_num
        change back (fillF (horizontal 1 t))=dcomplement t
        rw [hfillD,hbackD]
      let squareBandParams : RawSquare ≃ₜ (Interval × Set.Icc (-1:ℝ) 1) := {
        toFun := fun p => (⟨(p.val.2+1)/2,by constructor <;> linarith [p.property.2.1,p.property.2.2]⟩,
          ⟨p.val.1,p.property.1⟩)
        invFun := fun p => ⟨(p.2.val,2*p.1.val-1),⟨p.2.property,by
          constructor <;> linarith [p.1.property.1,p.1.property.2]⟩⟩
        left_inv := by
          intro p
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · dsimp;ring
        right_inv := by
          intro p
          apply Prod.ext
          · apply Subtype.ext;dsimp;ring
          · apply Subtype.ext;rfl
        continuous_toFun := by apply Continuous.prodMk <;> apply Continuous.subtype_mk <;> fun_prop
        continuous_invFun := by apply Continuous.subtype_mk;fun_prop }
      let D₀ : RawSquare ≃ₜ Set.range Bsmall := squareBandParams.trans hBsmall.toHomeomorph
      have hD₀value (p : RawSquare) : (D₀ p).val=Bsmall (squareBandParams p) := rfl
      have hD₀Left (t : Interval) : (D₀ (squareLeftSeam t)).val=Lsource t := by
        rw [hD₀value]
        apply congrArg Bsmall
        apply Prod.ext
        · apply Subtype.ext;change ((2*(t:ℝ)-1)+1)/2=(t:ℝ);ring
        · apply Subtype.ext;rfl
      have hD₀Right (t : Interval) : (D₀ (squareRightSeam t)).val=Rsource (unitInterval.symm t) := by
        rw [hD₀value]
        apply congrArg Bsmall
        apply Prod.ext
        · apply Subtype.ext;change ((1-2*(t:ℝ))+1)/2=1-(t:ℝ);ring
        · apply Subtype.ext;rfl
      have hD₀Bottom (t : Interval) : (D₀ (boundaryUnitSquareRaw (t,0))).val=cport t := by
        rw [hD₀value]
        apply congrArg Bsmall
        apply Prod.ext
        · apply Subtype.ext;norm_num [squareBandParams,boundaryUnitSquareRaw]
        · apply Subtype.ext;rfl
      have hD₀Top (t : Interval) : (D₀ (boundaryUnitSquareRaw (t,1))).val=dport t := by
        rw [hD₀value]
        apply congrArg Bsmall
        apply Prod.ext
        · apply Subtype.ext;norm_num [squareBandParams,boundaryUnitSquareRaw]
        · apply Subtype.ext;rfl
      let reversedR : Interval → S := fun t => Rsource (unitInterval.symm t)
      have hreversedRange : Set.range reversedR=Set.range Rsource := by
        ext x
        constructor
        · rintro ⟨t,rfl⟩
          exact ⟨unitInterval.symm t,rfl⟩
        · rintro ⟨t,rfl⟩
          exact ⟨unitInterval.symm t,by simp [reversedR]⟩
      have hglueIntersection : Set.range Bsmall ∩ remainingClosed=Set.range Lsource ∪ Set.range reversedR := by
        rw [Set.inter_comm,hRemainingBandSeams,hreversedRange]
      obtain ⟨annulusHomeo,hannulusLevels⟩ := square_pair_prescribed_seams_cylinder_edge_ranges
        (Set.range Bsmall) remainingClosed D₀ D₁ Lsource reversedR
          hD₀Left hD₁Left hD₀Right hD₁Right hglueIntersection
      let q : C(Circle × Interval,S) := ⟨fun p => (annulusHomeo p).val,
        continuous_subtype_val.comp annulusHomeo.continuous⟩
      have hq : Topology.IsEmbedding q := Topology.IsEmbedding.subtypeVal.comp annulusHomeo.isEmbedding
      have hq0 : Set.range (fun z : Circle => q (z,0))=c.image := by
        change Set.range (fun z : Circle => (annulusHomeo (z,0)).val)=c.image
        rw [hannulusLevels 0]
        have hfirst : Set.range (fun t : Interval => (D₀ (boundaryUnitSquareRaw (t,0))).val)=Set.range cport :=
          congrArg Set.range (funext hD₀Bottom)
        have hsecond : Set.range (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,0))).val)=Set.range ccomplement := by
          have he : (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,0))).val)=
              (fun t : Interval => ccomplement (unitInterval.symm t)) := funext (fun t => hD₁Bottom _)
          rw [he]
          ext x
          constructor
          · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,rfl⟩
          · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,by simp⟩
        rw [hfirst,hsecond]
        exact hcpartition
      have hq1 : Set.range (fun z : Circle => q (z,1))=d.image := by
        change Set.range (fun z : Circle => (annulusHomeo (z,1)).val)=d.image
        rw [hannulusLevels 1]
        have hfirst : Set.range (fun t : Interval => (D₀ (boundaryUnitSquareRaw (t,1))).val)=Set.range dport :=
          congrArg Set.range (funext hD₀Top)
        have hsecond : Set.range (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,1))).val)=Set.range dcomplement := by
          have he : (fun t : Interval => (D₁ (boundaryUnitSquareRaw (unitInterval.symm t,1))).val)=
              (fun t : Interval => dcomplement (unitInterval.symm t)) := funext (fun t => hD₁Top _)
          rw [he]
          ext x
          constructor
          · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,rfl⟩
          · rintro ⟨t,rfl⟩;exact ⟨unitInterval.symm t,by simp⟩
        rw [hfirst,hsecond]
        exact hdpartition
      have hqRange : Set.range q=Set.range Bsmall ∪ remainingClosed := by
        ext x
        constructor
        · rintro ⟨p,rfl⟩
          exact (annulusHomeo p).property
        · intro hx
          refine ⟨annulusHomeo.symm ⟨x,hx⟩,?_⟩
          exact congrArg Subtype.val (annulusHomeo.apply_symm_apply ⟨x,hx⟩)
      let Qmiddle : Set S := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
      have hQmiddleConnected : IsConnected Qmiddle := by
        have he : {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}=
            (Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1 := by ext p;simp
        change IsConnected (q '' _)
        rw [he]
        exact (isConnected_univ.prod (isConnected_Ioo (by norm_num : (0:Interval)<1))).image _
          q.continuous.continuousOn
      have hQmiddleAvoid : Qmiddle ⊆ (c.image ∪ d.image)ᶜ := by
        rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩ (hc | hdmem)
        · obtain ⟨w,hw⟩ := hq0.symm ▸ hc
          have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
          change (0:ℝ)=(t:ℝ) at hh
          linarith
        · obtain ⟨w,hw⟩ := hq1.symm ▸ hdmem
          have hh := congrArg (fun p : Circle × Interval => (p.2:ℝ)) (hq.injective hw)
          change (1:ℝ)=(t:ℝ) at hh
          linarith
      have hQmiddleDiff : Qmiddle=Set.range q \ (c.image ∪ d.image) := by
        apply Set.Subset.antisymm
        · exact fun x hx => ⟨by obtain ⟨p,hp,he⟩:=hx;exact ⟨p,he⟩,hQmiddleAvoid hx⟩
        · rintro x ⟨⟨⟨z,t⟩,rfl⟩,hx⟩
          have ht0 : (t:ℝ) ≠ 0 := by
            intro he
            have ht : t=0 := Subtype.ext he
            apply hx
            left
            rw [ht,← hq0]
            exact Set.mem_range_self z
          have ht1 : (t:ℝ) ≠ 1 := by
            intro he
            have ht : t=1 := Subtype.ext he
            apply hx
            right
            rw [ht,← hq1]
            exact Set.mem_range_self z
          exact ⟨(z,t),⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩
      have hQmiddleOpen : IsOpen Qmiddle := by
        rw [isOpen_iff_forall_mem_open]
        rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩
        let k : Plane → S := fun x => q (z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1))
        let O : Set Plane := {x | x 0 ∈ Set.Ioo (-1:ℝ) 1 ∧ x 1 ∈ Set.Ioo (0:ℝ) 1}
        have hO : IsOpen O := (isOpen_Ioo.preimage (by fun_prop)).inter
          (isOpen_Ioo.preimage (by fun_prop))
        have hk : Continuous k := q.continuous.comp
          ((continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))).prodMk
            (continuous_projIcc.comp (by fun_prop)))
        have hki : InjOn k O := by
          intro x hx y hy he
          have hh := hq.injective he
          have h0 : Circle.exp (x 0)=Circle.exp (y 0) := mul_left_cancel (congrArg Prod.fst hh)
          have hlen : (1:ℝ)-(-1)<2*Real.pi := by linarith [Real.pi_gt_three]
          have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩ ⟨hy.1.1.le,hy.1.2.le⟩ h0
          have h1 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
          simp only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,
            Set.projIcc_of_mem zero_le_one ⟨hy.2.1.le,hy.2.2.le⟩] at h1
          ext i
          fin_cases i
          · exact h0'
          · exact h1
        have hopen := CurveComplex.surface_invariance_of_domain_probe k O hO hk.continuousOn hki
        have hsub : k '' O ⊆ Qmiddle := by
          rintro y ⟨x,hx,rfl⟩
          refine ⟨(z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1)),?_,rfl⟩
          change 0 < (Set.projIcc 0 1 zero_le_one (x 1):ℝ) ∧
            (Set.projIcc 0 1 zero_le_one (x 1):ℝ)<1
          simpa only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,Set.mem_Ioo] using hx.2
        refine ⟨k '' O,hsub,hopen,?_⟩
        refine ⟨Plane.mk 0 (t:ℝ),⟨by norm_num [O],⟨ht0,ht1⟩⟩,?_⟩
        simp [k,Set.projIcc_of_mem zero_le_one t.property]
      have hqRangeClosed : IsClosed (Set.range q) := (isCompact_range q.continuous).isClosed
      have hQcomponent : IsComplementComponent (c.image ∪ d.image) Qmiddle := by
        refine ⟨hQmiddleConnected.nonempty,hQmiddleConnected,hQmiddleAvoid,?_⟩
        intro T hT hQT hTavoid
        have hsub : T ⊆ Qmiddle ∪ (Set.range q)ᶜ := by
          intro x hxT
          by_cases hxq : x ∈ Set.range q
          · left
            rw [hQmiddleDiff]
            exact ⟨hxq,hTavoid hxT⟩
          · exact Or.inr hxq
        have hdisj : Disjoint Qmiddle (Set.range q)ᶜ := by
          apply Set.disjoint_left.mpr
          intro x hx hxq
          rw [hQmiddleDiff] at hx
          exact hxq hx.1
        rcases hT.isPreconnected.subset_or_subset hQmiddleOpen hqRangeClosed.isOpen_compl
          hdisj hsub with hTQ | hTout
        · exact Set.Subset.antisymm hTQ hQT
        · obtain ⟨x,hx⟩ := hQmiddleConnected.nonempty
          exact False.elim (Set.disjoint_left.mp hdisj hx (hTout (hQT hx)))
      exact ⟨q,hq,hq0,hq1,hQcomponent⟩
    have hClear : ∃ ε : ℝ, 0 < ε ∧ ε < 1/4 ∧
      ∀ z, ε < |((G (z,0)).2:ℝ)-1/2| ∧ ε < |((G (z,1)).2:ℝ)-1/2| := by
      have hpos (z : Circle) (a : Interval) (ha : a=0 ∨ a=1) :
          0 < |((G (z,a)).2:ℝ)-1/2| := by
        apply abs_pos.mpr
        intro he
        have hv : ((G (z,a)).2:ℝ)=1/2 := by linarith
        have hh : G (r.symm (G (z,a)).1,⟨1/2,by norm_num⟩)=G (z,a) := by
          rw [hcore,r.apply_symm_apply]
          exact Prod.ext rfl (Subtype.ext hv.symm)
        have heq := congrArg Prod.snd (hGe.injective hh)
        have hv' := congrArg Subtype.val heq
        rcases ha with rfl | rfl
        · change (1/2:ℝ)=0 at hv'
          norm_num at hv'
        · change (1/2:ℝ)=1 at hv'
          norm_num at hv'
      let f0 : Circle → ℝ := fun z => |((G (z,0)).2:ℝ)-1/2|
      let f1 : Circle → ℝ := fun z => |((G (z,1)).2:ℝ)-1/2|
      have hc0 : Continuous f0 := by dsimp [f0]; fun_prop
      have hc1 : Continuous f1 := by dsimp [f1]; fun_prop
      obtain ⟨z0,hz0,hmin0⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).exists_isMinOn
        Set.univ_nonempty hc0.continuousOn
      obtain ⟨z1,hz1,hmin1⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).exists_isMinOn
        Set.univ_nonempty hc1.continuousOn
      have hp0 : 0 < f0 z0 := hpos z0 0 (Or.inl rfl)
      have hp1 : 0 < f1 z1 := hpos z1 1 (Or.inr rfl)
      let ε : ℝ := min ((min (f0 z0) (f1 z1))/2) (1/8)
      have hp : 0 < ε := lt_min (half_pos (lt_min hp0 hp1)) (by norm_num)
      have he0 : ε ≤ f0 z0 / 2 := (min_le_left _ _).trans
        ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr (min_le_left _ _))
      have he1 : ε ≤ f1 z1 / 2 := (min_le_left _ _).trans
        ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ)<2)).mpr (min_le_right _ _))
      refine ⟨ε,hp,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
      intro z
      have hm0 := hmin0 (a := z) (Set.mem_univ z)
      have hm1 := hmin1 (a := z) (Set.mem_univ z)
      change f0 z0 ≤ f0 z at hm0
      change f1 z1 ≤ f1 z at hm1
      change ε < f0 z ∧ ε < f1 z
      constructor <;> linarith
    have hPolar : ∃ P : C(Circle × Interval,Plane), Topology.IsEmbedding P := by
      let f : C(Circle × Interval,ℂ) :=
        ⟨fun p => (1+(p.2:ℝ)) • (p.1:ℂ),by fun_prop⟩
      let P : C(Circle × Interval,Plane) :=
        ⟨fun p => Plane.mk (f p).re (f p).im,by fun_prop⟩
      have hi : Function.Injective P := by
        rintro ⟨z,u⟩ ⟨w,v⟩ he
        have hf : f (z,u)=f (w,v) := by
          apply Complex.ext
          · exact congrArg (fun x : Plane => x 0) he
          · exact congrArg (fun x : Plane => x 1) he
        have hu : u=v := by
          have hn := congrArg norm hf
          have hr : 0 < 1+(u:ℝ) := by linarith [u.property.1]
          have hs : 0 < 1+(v:ℝ) := by linarith [v.property.1]
          change ‖(1+(u:ℝ)) • (z:ℂ)‖ = ‖(1+(v:ℝ)) • (w:ℂ)‖ at hn
          simp only [norm_smul,Circle.norm_coe,mul_one,Real.norm_eq_abs,
            abs_of_pos hr,abs_of_pos hs] at hn
          apply Subtype.ext
          linarith
        subst v
        have hr : (1+(u:ℝ)) ≠ 0 := by linarith [u.property.1]
        have hz : (z:ℂ)=(w:ℂ) := by
          have hh := congrArg (fun x : ℂ => (1+(u:ℝ))⁻¹ • x) hf
          change (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (z:ℂ)) =
            (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (w:ℂ)) at hh
          simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hh
        exact Prod.ext (Subtype.ext hz) rfl
      exact ⟨P,(P.continuous.isClosedEmbedding hi).isEmbedding⟩
    have hUniform (M : HyperellipticModel E S)
        (G : C(Circle × Interval,Circle × Interval)) (hGe : IsEmbedding G)
        (r : Circle ≃ₜ Circle)
        (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩)=(r z,⟨1/2,by norm_num⟩)) :
        ∃ δ : ℝ, 0 < δ ∧ δ < 1/4 ∧
          ∀ z (u : Interval), |(u:ℝ)-1/2| ≤ δ →
            ∃ p : Circle × Interval, 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1 ∧ G p=(z,u) := by
      audit_main14_base3
        have hPolar : ∃ P : C(Circle × Interval,Plane), IsEmbedding P := by
          let f : C(Circle × Interval,ℂ) :=
            ⟨fun p => (1+(p.2:ℝ)) • (p.1:ℂ),by fun_prop⟩
          let P : C(Circle × Interval,Plane) :=
            ⟨fun p => Plane.mk (f p).re (f p).im,by fun_prop⟩
          have hi : Function.Injective P := by
            rintro ⟨z,u⟩ ⟨w,v⟩ he
            have hf : f (z,u)=f (w,v) := by
              apply Complex.ext
              · exact congrArg (fun x : Plane => x 0) he
              · exact congrArg (fun x : Plane => x 1) he
            have hu : u=v := by
              have hn := congrArg norm hf
              have hr : 0 < 1+(u:ℝ) := by linarith [u.property.1]
              have hs : 0 < 1+(v:ℝ) := by linarith [v.property.1]
              change ‖(1+(u:ℝ)) • (z:ℂ)‖ = ‖(1+(v:ℝ)) • (w:ℂ)‖ at hn
              simp only [norm_smul,Circle.norm_coe,mul_one,Real.norm_eq_abs,
                abs_of_pos hr,abs_of_pos hs] at hn
              apply Subtype.ext
              linarith
            subst v
            have hr : (1+(u:ℝ)) ≠ 0 := by linarith [u.property.1]
            have hz : (z:ℂ)=(w:ℂ) := by
              have hh := congrArg (fun x : ℂ => (1+(u:ℝ))⁻¹ • x) hf
              change (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (z:ℂ)) =
                (1+(u:ℝ))⁻¹ • ((1+(u:ℝ)) • (w:ℂ)) at hh
              simpa only [smul_smul,inv_mul_cancel₀ hr,one_smul] using hh
            exact Prod.ext (Subtype.ext hz) rfl
          exact ⟨P,(P.continuous.isClosedEmbedding hi).isEmbedding⟩
        letI : ChartedSpace Plane S := M.sphere.symm.chartedSpace
        have hOpen (q : C(Circle × Interval,S)) (hq : IsEmbedding q) :
            IsOpen (q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}) := by
          let Qmiddle := q '' {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}
          change IsOpen Qmiddle
          rw [isOpen_iff_forall_mem_open]
          rintro x ⟨⟨z,t⟩,⟨ht0,ht1⟩,rfl⟩
          let k : Plane → S := fun x => q (z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1))
          let O : Set Plane := {x | x 0 ∈ Set.Ioo (-1:ℝ) 1 ∧ x 1 ∈ Set.Ioo (0:ℝ) 1}
          have hO : IsOpen O := (isOpen_Ioo.preimage (by fun_prop)).inter
            (isOpen_Ioo.preimage (by fun_prop))
          have hk : Continuous k := q.continuous.comp
            ((continuous_const.mul (Circle.exp.continuous.comp (by fun_prop))).prodMk
              (continuous_projIcc.comp (by fun_prop)))
          have hki : InjOn k O := by
            intro x hx y hy he
            have hh := hq.injective he
            have h0 : Circle.exp (x 0)=Circle.exp (y 0) := mul_left_cancel (congrArg Prod.fst hh)
            have hlen : (1:ℝ)-(-1)<2*Real.pi := by linarith [Real.pi_gt_three]
            have h0' := Circle.exp_injOn_Icc hlen ⟨hx.1.1.le,hx.1.2.le⟩ ⟨hy.1.1.le,hy.1.2.le⟩ h0
            have h1 := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
            simp only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,
              Set.projIcc_of_mem zero_le_one ⟨hy.2.1.le,hy.2.2.le⟩] at h1
            ext i
            fin_cases i
            · exact h0'
            · exact h1
          have hopen := CurveComplex.surface_invariance_of_domain_probe k O hO hk.continuousOn hki
          have hsub : k '' O ⊆ Qmiddle := by
            rintro y ⟨x,hx,rfl⟩
            refine ⟨(z*Circle.exp (x 0),Set.projIcc 0 1 zero_le_one (x 1)),?_,rfl⟩
            change 0 < (Set.projIcc 0 1 zero_le_one (x 1):ℝ) ∧
              (Set.projIcc 0 1 zero_le_one (x 1):ℝ)<1
            simpa only [Set.projIcc_of_mem zero_le_one ⟨hx.2.1.le,hx.2.2.le⟩,Set.mem_Ioo] using hx.2
          refine ⟨k '' O,hsub,hopen,?_⟩
          refine ⟨Plane.mk 0 (t:ℝ),⟨by norm_num [O],⟨ht0,ht1⟩⟩,?_⟩
          simp [k,Set.projIcc_of_mem zero_le_one t.property]
    
        obtain ⟨P,hP⟩ := hPolar
        letI : T2Space S := M.sphere.symm.t2Space
        obtain ⟨w,hw⟩ := Finset.card_pos.mp (by rw [M.cover.branch_card];norm_num)
        letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))=2+1) := ⟨by simp⟩
        let chart := stereographic' 2 (M.sphere w)
        have hs : chart.source={M.sphere w}ᶜ := stereographic'_source _
        have ht : chart.target=Set.univ := stereographic'_target _
        let es : {x : S // x ≠ w} ≃ₜ chart.source := M.sphere.subtype
          (fun x => by simp only [hs,Set.mem_compl_iff,Set.mem_singleton_iff,M.sphere.injective.eq_iff])
        let e : {x : S // x ≠ w} ≃ₜ Plane := es.trans
          (chart.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
        let Φ : C(Circle × Interval,S) := ⟨fun p => (e.symm (P p)).val,
          continuous_subtype_val.comp (e.symm.continuous.comp P.continuous)⟩
        have hΦ : IsEmbedding Φ := IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hP)
        let c : Interval := ⟨1/2,by norm_num⟩
        let O := G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
        let Q : C(Circle × Interval,S) := Φ.comp G
        have hQ : IsEmbedding Q := hΦ.comp hGe
        have hEq : O=Φ ⁻¹' (Q '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
          ext x
          constructor
          · rintro ⟨p,hp,rfl⟩
            exact ⟨p,hp,rfl⟩
          · rintro ⟨p,hp,he⟩
            exact ⟨p,hp,hΦ.injective he⟩
        have ho : IsOpen O := by
          rw [hEq]
          have hopen := hOpen Q hQ
          have he : {p : Circle × Interval | 0 < (p.2:ℝ) ∧ (p.2:ℝ)<1}=
              Set.univ ×ˢ Set.Ioo (0:Interval) 1 := by ext p;simp
          rw [he] at hopen
          exact hopen.preimage Φ.continuous
        have hmid : (Set.univ : Set Circle) ×ˢ {c} ⊆ O := by
          rintro ⟨z,u⟩ ⟨hz,hu⟩
          have he : u=c := hu
          subst u
          refine ⟨(r.symm z,c),⟨Set.mem_univ _,?_⟩,?_⟩
          · constructor
            · change (0:ℝ)<1/2;norm_num
            · change (1/2:ℝ)<1;norm_num
          · rw [hcore,r.apply_symm_apply]
        obtain ⟨D,V,hD,hV,hall,hcV,hDV⟩ := generalized_tube_lemma
          (isCompact_univ : IsCompact (Set.univ : Set Circle))
          (isCompact_singleton : IsCompact ({c}:Set Interval)) ho hmid
        let clip : ℝ → Interval := Set.projIcc 0 1 (by norm_num)
        have hclip : Continuous clip := continuous_projIcc
        have hpre : IsOpen (clip ⁻¹' V) := hV.preimage hclip
        have hcclip : clip (1/2)=c := Set.projIcc_of_mem (by norm_num)
          (by norm_num : (1/2:ℝ) ∈ Set.Icc 0 1)
        have hcpre : (1/2:ℝ) ∈ clip ⁻¹' V := by
          change clip (1/2) ∈ V
          rw [hcclip]
          exact hcV (Set.mem_singleton c)
        obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hpre (1/2) hcpre
        let δ : ℝ := min (ε/2) (1/8)
        have hd : 0 < δ := lt_min (half_pos hε) (by norm_num)
        have hsmall : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
        refine ⟨δ,hd,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
        intro z u hu
        have hb : (u:ℝ) ∈ Metric.ball (1/2) ε := by
          rw [Metric.mem_ball,Real.dist_eq]
          exact hu.trans_lt hsmall
        have hv : u ∈ V := by
          have hh := hball hb
          change clip (u:ℝ) ∈ V at hh
          have huclip : clip (u:ℝ)=u := Set.projIcc_of_mem (by norm_num) u.property
          rw [huclip] at hh
          exact hh
        have hmem : (z,u) ∈ O := hDV (show (z,u) ∈ D ×ˢ V from ⟨hall (Set.mem_univ z),hv⟩)
        obtain ⟨p,hp,he⟩ := hmem
        exact ⟨p,by exact hp.2.1,by exact hp.2.2,he⟩
    obtain ⟨ε0,hε0,hε0q,hgap0⟩ := hClear
    obtain ⟨δ,hδ,hδq,hband⟩ := hUniform M G hGe r hcore
    let ε : ℝ := min ε0 (δ/2)
    have hε : 0 < ε := lt_min hε0 (half_pos hδ)
    have hεq : ε < 1/4 := lt_of_le_of_lt (min_le_left _ _) hε0q
    have hεδ : ε ≤ δ := (min_le_right _ _).trans (by linarith)
    have hgap : ∀ z, ε < |((G (z,0)).2:ℝ)-1/2| ∧ ε < |((G (z,1)).2:ℝ)-1/2| := by
      intro z
      exact ⟨lt_of_le_of_lt (min_le_left _ _) (hgap0 z).1,
        lt_of_le_of_lt (min_le_left _ _) (hgap0 z).2⟩
    obtain ⟨P,hP⟩ := hPolar
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨w,hw⟩ := Finset.card_pos.mp (by rw [M.cover.branch_card];norm_num)
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))=2+1) := ⟨by simp⟩
    let chart := stereographic' 2 (M.sphere w)
    have hs : chart.source={M.sphere w}ᶜ := stereographic'_source _
    have ht : chart.target=Set.univ := stereographic'_target _
    let es : {x : S // x ≠ w} ≃ₜ chart.source := M.sphere.subtype
      (fun x => by simp only [hs,Set.mem_compl_iff,Set.mem_singleton_iff,M.sphere.injective.eq_iff])
    let e : {x : S // x ≠ w} ≃ₜ Plane := es.trans
      (chart.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
    let Φ : C(Circle × Interval,S) := ⟨fun p => (e.symm (P p)).val,
      continuous_subtype_val.comp (e.symm.continuous.comp P.continuous)⟩
    have hΦ : IsEmbedding Φ := IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hP)
    refine ⟨ε,hε,hεq,Φ,hΦ,(fun z u hu => hband z u (hu.trans hεδ)),?_⟩
    intro a b
    let u : Interval := if a then 1 else 0
    let v : Interval := ⟨1/2+(if b then ε else -ε),by split_ifs <;> constructor <;> linarith⟩
    let c : Curve S := ⟨fun z => Φ (G (z,u)),hΦ.comp (hGe.comp
      (isEmbedding_prodMkLeft u))⟩
    let d : Curve S := ⟨fun z => Φ (z,v),hΦ.comp
      (isEmbedding_prodMkLeft v)⟩
    have hc : w ∉ c.image := by
      rintro ⟨z,hz⟩
      exact (e.symm (P (G (z,u)))).property hz
    have hd : w ∉ d.image := by
      rintro ⟨z,hz⟩
      exact (e.symm (P (z,v))).property hz
    have hdis : Disjoint c.image d.image := by
      apply Set.disjoint_left.mpr
      rintro x ⟨z,rfl⟩ ⟨y,hy⟩
      have he := hΦ.injective hy
      have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) he
      have hgg : ε < |((G (z,u)).2:ℝ)-1/2| := by
        cases a
        · exact (hgap z).1
        · exact (hgap z).2
      cases b
      · change (1/2:ℝ)-ε=((G (z,u)).2:ℝ) at hv
        have hn : ((G (z,u)).2:ℝ)-1/2=-ε := by linarith
        rw [hn,abs_neg,abs_of_pos hε] at hgg
        exact (lt_irrefl _ hgg)
      · change (1/2:ℝ)+ε=((G (z,u)).2:ℝ) at hv
        have hn : ((G (z,u)).2:ℝ)-1/2=ε := by linarith
        rw [hn,abs_of_pos hε] at hgg
        exact (lt_irrefl _ hgg)
    exact actual_sphere_pair_annulus c d w hc hd hdis
end CurveComplex.HyperellipticModel
