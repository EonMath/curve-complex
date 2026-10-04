import CurveComplexGenusTwo.Dictionary.JordanEssentiality

set_option maxHeartbeats 2000000
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

structure UnmarkedComplementaryDiscSide (a : C(Interval,S)) (U : Set S) where
  component : IsComplementComponent (Set.range a) U
  open_side : IsOpen U
  closedDisk : JordanClosedDisk ≃ₜ closure U
  openDisk : JordanOpenDisk ≃ₜ U
  interior_closure : interior (closure U) = U
  boundary : frontier U = (Set.range a)
  closure_eq : closure U = U ∪ (Set.range a)
  disk_interior : ∀ x : JordanClosedDisk,
    (closedDisk x : S) ∈ U ↔ ‖(x : JordanPlane)‖ < 1
  disk_boundary : ∀ x : JordanClosedDisk,
    (closedDisk x : S) ∈ (Set.range a) ↔ ‖(x : JordanPlane)‖ = 1

/-- Jordan-Schoenflies data for the actual marked loop, including exhaustivity
of the two complementary components; no smooth atlas is involved. -/
structure UnmarkedLoopDiscDecomposition (a : C(Interval,S)) where
  side : Fin 2 → Set S
  discs : ∀ i, UnmarkedComplementaryDiscSide a (side i)
  distinct : side 0 ≠ side 1
  disjoint : Disjoint (side 0) (side 1)
  complement : side 0 ∪ side 1 = (Set.range a)ᶜ
  all_components : ∀ U, IsComplementComponent (Set.range a) U ↔ ∃ i, U = side i
  closed_cover : closure (side 0) ∪ closure (side 1) = Set.univ
  closed_intersection : closure (side 0) ∩ closure (side 1) = (Set.range a)

/-- The Jordan decomposition depends only on an embedded interval loop and
an off-loop puncture; no branch marks are used. -/
theorem unmarked_loop_disc_decomposition_exists (M : HyperellipticModel E S)
    (a : C(Interval,S)) (hloop : a 0 = a 1)
    (hinj : ∀ t u, a t = a u →
      t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0))
    (p : S) (hp : p ∉ (Set.range a)) :
    Nonempty (UnmarkedLoopDiscDecomposition a) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let c : CurveComplex.SpherePort.JordanCurve := {
    map := M.sphere ∘ a
    continuous := M.sphere.continuous.comp a.continuous
    injective_except_ends := fun t u h =>
      hinj t u (M.sphere.injective h)
    closed := congrArg M.sphere hloop }
  let P : CurveComplex.SpherePort.Chart c := {
    puncture := M.sphere p
    avoids := by
      rintro ⟨t, ht⟩
      exact hp ⟨t, M.sphere.injective ht⟩
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
  have hBimage : F '' B = (Set.range a) := by
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
      change M.sphere.symm (P.plane.symm (P.plane y)).val = a t
      rw [P.plane.symm_apply_apply]
      exact M.sphere.symm_apply_apply (a t)
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
  have hscover : SU ∪ SV = (Set.range a)ᶜ := by
    change F '' U ∪ F '' V = _
    rw [← Set.image_union, hcover, F.image_compl, hBimage]
  have hsclU : closure SU = SU ∪ (Set.range a) := by
    rw [← F.image_closure, hclU, Set.image_union, hBimage]
  have hsclV : closure SV = SV ∪ (Set.range a) := by
    rw [← F.image_closure, hclV, Set.image_union, hBimage]
  have hsintU : interior (closure SU) = SU := by
    rw [← F.image_closure, ← F.image_interior, hintU]
  have hsintV : interior (closure SV) = SV := by
    rw [← F.image_closure, ← F.image_interior, hintV]
  have hsboundU : frontier SU = (Set.range a) := by
    rw [← F.image_frontier, hboundU, hBimage]
  have hsboundV : frontier SV = (Set.range a) := by
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
  have hsUb : ∀ x : JordanClosedDisk, (dsU x : S) ∈ (Set.range a) ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change F (eU x : OnePoint JordanPlane) ∈ (Set.range a) ↔ _
    rw [← hBimage, hFmem]
    exact heUb x
  have hsVb : ∀ x : JordanClosedDisk, (dsV x : S) ∈ (Set.range a) ↔ ‖(x : JordanPlane)‖ = 1 := by
    intro x
    change F (eV x : OnePoint JordanPlane) ∈ (Set.range a) ↔ _
    rw [← hBimage, hFmem]
    exact heVb x
  obtain ⟨osU⟩ := openDiskOf S SU dsU hsUi
  obtain ⟨osV⟩ := openDiskOf S SV dsV hsVi
  have hmaximal (T R : Set S) (hT : IsConnected T) (hTopen : IsOpen T)
      (hRopen : IsOpen R) (hTR : Disjoint T R) (hc : T ∪ R = (Set.range a)ᶜ) :
      IsComplementComponent (Set.range a) T := by
    have hsub : T ⊆ (Set.range a)ᶜ := fun x hx => hc ▸ Or.inl hx
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
  have hall : ∀ W, IsComplementComponent (Set.range a) W ↔ W = SU ∨ W = SV := by
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
  let discU : UnmarkedComplementaryDiscSide a SU := {
    component := hcU
    open_side := hsopenU
    closedDisk := dsU
    openDisk := osU
    interior_closure := hsintU
    boundary := hsboundU
    closure_eq := hsclU
    disk_interior := hsUi
    disk_boundary := hsUb }
  let discV : UnmarkedComplementaryDiscSide a SV := {
    component := hcV
    open_side := hsopenV
    closedDisk := dsV
    openDisk := osV
    interior_closure := hsintV
    boundary := hsboundV
    closure_eq := hsclV
    disk_interior := hsVi
    disk_boundary := hsVb }
  let side : Fin 2 → Set S := ![SU, SV]
  refine ⟨{
    side := side
    discs := ?_
    distinct := hdistinct
    disjoint := hsdisj
    complement := hscover
    all_components := ?_
    closed_cover := ?_
    closed_intersection := ?_ }⟩
  · intro i
    exact Fin.cases discU (fun j => Fin.cases discV (fun k => Fin.elim0 k) j) i
  · intro W
    rw [hall]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
  · change closure SU ∪ closure SV = Set.univ
    rw [hsclU, hsclV]
    ext x
    have hx := Set.ext_iff.mp hscover x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hb : x ∈ (Set.range a)
    · exact Or.inl (Or.inr hb)
    · rcases hx.mpr hb with hu | hv
      · exact Or.inl (Or.inl hu)
      · exact Or.inr (Or.inl hv)
  · change closure SU ∩ closure SV = (Set.range a)
    rw [hsclU, hsclV]
    ext x
    have hn : ¬ (x ∈ SU ∧ x ∈ SV) := fun h => Set.disjoint_left.mp hsdisj h.1 h.2
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto

end CurveComplex.HyperellipticModel
