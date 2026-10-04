import CurveComplexGenusTwo.Dictionary.JordanEssentiality

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section
set_option maxHeartbeats 2000000

/-- Actual Schoenflies geometry produces an embedded disk for the SPECIFIED
complementary component of a Jordan trace. No disk or interior identification
is input. The trace may contain several marked boundary points. -/
theorem actual_selected_jordan_component_closed_disk
    (M : HyperellipticModel E S) (L : C(Interval,S))
    (hloop : L 0 = L 1)
    (hcollision : ∀ t u, L t = L u → t = u ∨
      (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0))
    (p : S) (hp : p ∉ (range L)) (W : Set S)
    (hW : IsComplementComponent ((range L)) W) :
    ∃ e : JordanClosedDisk ≃ₜ closure W,
      (∀ x : JordanClosedDisk, (e x : S) ∈ W ↔ ‖(x : JordanPlane)‖ < 1) ∧
      (∀ x : JordanClosedDisk, (e x : S) ∈ range L ↔ ‖(x : JordanPlane)‖ = 1) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let c : CurveComplex.SpherePort.JordanCurve := {
    map := M.sphere ∘ L
    continuous := M.sphere.continuous.comp L.continuous
    injective_except_ends := fun t u h => hcollision t u (M.sphere.injective h)
    closed := congrArg M.sphere hloop }
  let P : CurveComplex.SpherePort.Chart c := {
    puncture := M.sphere p
    avoids := by
      rintro ⟨t,ht⟩
      exact hp ⟨t,M.sphere.injective ht⟩
    plane := puncturedSpherePlane (M.sphere p) }
  let C := P.planeImage c
  have hC : Schoenflies.IsJordanCurve C := CurveComplex.SpherePort.chart_image_jordan c P
  have hsep := Schoenflies.jordan_curve_theorem hC
  let F : OnePoint JordanPlane ≃ₜ S :=
    (CurveComplex.SpherePort.chartOnePoint c P).trans M.sphere.symm
  let B : Set (OnePoint JordanPlane) := OnePoint.some '' C
  let U : Set (OnePoint JordanPlane) := OnePoint.some '' Schoenflies.inside C
  let V : Set (OnePoint JordanPlane) :=
    {OnePoint.infty} ∪ OnePoint.some '' Schoenflies.outside C
  have hBimage : F '' B = (range L) := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y, ⟨t, ht⟩, hzy⟩ := hz
      have hval : F (OnePoint.some (P.plane y)) = M.sphere.symm y.val := by
        change M.sphere.symm (P.plane.symm (P.plane y)).val = M.sphere.symm y.val
        rw [P.plane.symm_apply_apply]
      rw [← hzy, hval]
      refine ⟨t, ?_⟩
      rw [← ht]
      exact (M.sphere.symm_apply_apply _).symm
    · rintro ⟨t, rfl⟩
      let y : {x : CurveComplex.SpherePort.Sphere // x ≠ P.puncture} :=
        ⟨c.map t, fun he => P.avoids (he ▸ Set.mem_range_self t)⟩
      refine ⟨OnePoint.some (P.plane y), ⟨P.plane y, ⟨y, ⟨t, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      change M.sphere.symm (P.plane.symm (P.plane y)).val = L t
      rw [P.plane.symm_apply_apply]
      exact M.sphere.symm_apply_apply (L t)
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
  let : ConnectedSpace JordanOpenDisk := isConnected_iff_connectedSpace.mp hball
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
  have hscover : SU ∪ SV = (range L)ᶜ := by
    change F '' U ∪ F '' V = _
    rw [← Set.image_union, hcover, F.image_compl, hBimage]
  have hsclU : closure SU = SU ∪ (range L) := by
    rw [← F.image_closure, hclU, Set.image_union, hBimage]
  have hsclV : closure SV = SV ∪ (range L) := by
    rw [← F.image_closure, hclV, Set.image_union, hBimage]
  have hsintU : interior (closure SU) = SU := by
    rw [← F.image_closure, ← F.image_interior, hintU]
  have hsintV : interior (closure SV) = SV := by
    rw [← F.image_closure, ← F.image_interior, hintV]
  have hsboundU : frontier SU = (range L) := by
    rw [← F.image_frontier, hboundU, hBimage]
  have hsboundV : frontier SV = (range L) := by
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
  have hsUb : ∀ x : JordanClosedDisk, (dsU x : S) ∈ (range L) ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change F (eU x : OnePoint JordanPlane) ∈ (range L) ↔ _
    rw [← hBimage, hFmem]
    exact heUb x
  have hsVb : ∀ x : JordanClosedDisk, (dsV x : S) ∈ (range L) ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change F (eV x : OnePoint JordanPlane) ∈ (range L) ↔ _
    rw [← hBimage, hFmem]
    exact heVb x
  obtain ⟨osU⟩ := openDiskOf S SU dsU hsUi
  obtain ⟨osV⟩ := openDiskOf S SV dsV hsVi
  have hmaximal (T R : Set S) (hT : IsConnected T) (hTopen : IsOpen T)
      (hRopen : IsOpen R) (hTR : Disjoint T R) (hc : T ∪ R = (range L)ᶜ) :
      IsComplementComponent (range L) T := by
    have hsub : T ⊆ (range L)ᶜ := fun x hx => hc ▸ Or.inl hx
    refine ⟨hT.nonempty, hT, hsub, ?_⟩
    intro W hW hTW hWc
    have hsplit : W ⊆ T ∨ W ⊆ R :=
      hW.isPreconnected.subset_or_subset hTopen hRopen hTR (hc.symm ▸ hWc)
    rcases hsplit with hWT | hWR
    · exact Set.Subset.antisymm hWT hTW
    · obtain ⟨x, hx⟩ := hT.nonempty
      exact False.elim (Set.disjoint_left.mp hTR hx (hWR (hTW hx)))
  have hcU := hmaximal SU SV hsconnU hsopenU hsopenV hsdisj hscover
  have hcV := hmaximal SV SU hsconnV hsopenV hsopenU hsdisj.symm
    ((Set.union_comm SV SU).trans hscover)
  have hall : ∀ W, IsComplementComponent (range L) W ↔ W = SU ∨ W = SV := by
    intro W
    constructor
    · intro hW
      rcases hW.2.1.isPreconnected.subset_or_subset hsopenU hsopenV hsdisj
          (hscover.symm ▸ hW.2.2.1) with hWU | hWV
      · exact Or.inl (hW.2.2.2 SU hsconnU hWU hcU.2.2.1).symm
      · exact Or.inr (hW.2.2.2 SV hsconnV hWV hcV.2.2.1).symm
    · rintro (rfl | rfl)
      · exact hcU
      · exact hcV
  have hdistinct : SU ≠ SV := by
    intro heq
    obtain ⟨x, hx⟩ := hsconnU.nonempty
    exact Set.disjoint_left.mp hsdisj hx (heq ▸ hx)
  have hdisc : ∃ e : JordanClosedDisk ≃ₜ closure W,
      (∀ x : JordanClosedDisk, (e x : S) ∈ W ↔ ‖(x : JordanPlane)‖ < 1) ∧
      (∀ x : JordanClosedDisk, (e x : S) ∈ (range L) ↔ ‖(x : JordanPlane)‖ = 1) := by
    rcases (hall W).mp hW with rfl | rfl
    · exact ⟨dsU,hsUi,hsUb⟩
    · exact ⟨dsV,hsVi,hsVb⟩
  exact hdisc

/-- Actual closed disk coordinates give the literal surface disk and its
exact open interior and boundary images. -/
theorem actual_closed_component_disk_embedded_map
    {S : Type} [TopologicalSpace S] (W A : Set S)
    (e : JordanClosedDisk ≃ₜ closure W)
    (hi : ∀ x : JordanClosedDisk, (e x : S) ∈ W ↔ ‖(x : JordanPlane)‖ < 1)
    (hb : ∀ x : JordanClosedDisk, (e x : S) ∈ A ↔ ‖(x : JordanPlane)‖ = 1)
    (hboundary : A ⊆ closure W) :
    ∃ d : C(JordanClosedDisk,S), IsEmbedding d ∧
      d '' {x | x.val ∈ Metric.ball (0 : JordanPlane) 1} = W ∧
      d '' {x | x.val ∈ Metric.sphere (0 : JordanPlane) 1} = A := by
  let d : C(JordanClosedDisk,S) := ⟨fun x => (e x).val,continuous_subtype_val.comp e.continuous⟩
  refine ⟨d,IsEmbedding.subtypeVal.comp e.isEmbedding,?_,?_⟩
  · ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      change dist x.val 0 < 1 at hx
      exact (hi x).mpr (by simpa only [dist_zero_right] using hx)
    · intro hz
      let x := e.symm ⟨z,subset_closure hz⟩
      have he : (e x).val = z := congrArg Subtype.val (e.apply_symm_apply ⟨z,subset_closure hz⟩)
      refine ⟨x,?_,he⟩
      change dist x.val 0 < 1
      simpa only [dist_zero_right] using (hi x).mp (he.symm ▸ hz)
  · ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      change dist x.val 0 = 1 at hx
      exact (hb x).mpr (by simpa only [dist_zero_right] using hx)
    · intro hz
      have hzcl : z ∈ closure W := hboundary hz
      let x := e.symm ⟨z,hzcl⟩
      have he : (e x).val = z := congrArg Subtype.val (e.apply_symm_apply ⟨z,hzcl⟩)
      refine ⟨x,?_,he⟩
      change dist x.val 0 = 1
      simpa only [dist_zero_right] using (hb x).mp (he.symm ▸ hz)

theorem actual_selected_jordan_component_embedded_disk
    (M : HyperellipticModel E S) (L : C(Interval,S))
    (hloop : L 0 = L 1)
    (hcollision : ∀ t u, L t = L u → t = u ∨
      (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0))
    (p : S) (hp : p ∉ range L) (W : Set S)
    (hW : IsComplementComponent (range L) W)
    (hfrontier : frontier W = range L) :
    ∃ d : C(JordanClosedDisk,S), IsEmbedding d ∧
      d '' {x | x.val ∈ Metric.ball (0 : JordanPlane) 1} = W ∧
      d '' {x | x.val ∈ Metric.sphere (0 : JordanPlane) 1} = range L := by
  obtain ⟨e,hi,hb⟩ := actual_selected_jordan_component_closed_disk M L hloop hcollision p hp W hW
  exact actual_closed_component_disk_embedded_map W (range L) e hi hb
    (hfrontier ▸ frontier_subset_closure)
end
end CurveComplex.HyperellipticModel
