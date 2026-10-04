import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
import Schoenflies.JordanClosed
import CurveComplexGenusTwo.Dictionary.JordanDiscHelper
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.SphereGapFinish.SphereClosedDiscs

set_option maxHeartbeats 2000000

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

abbrev JordanPlane := EuclideanSpace ℝ (Fin 2)
abbrev JordanClosedDisk := Metric.closedBall (0 : JordanPlane) 1
abbrev JordanOpenDisk := Metric.ball (0 : JordanPlane) 1

/-- A complementary open component whose closure is an actual closed disc,
with the given arc as its entire boundary. -/
structure ComplementaryDiscSide {M : HyperellipticModel E S}
    (a : MarkedArc M) (U : Set S) where
  component : IsComplementComponent a.image U
  open_side : IsOpen U
  closedDisk : JordanClosedDisk ≃ₜ closure U
  openDisk : JordanOpenDisk ≃ₜ U
  interior_closure : interior (closure U) = U
  boundary : frontier U = a.image
  closure_eq : closure U = U ∪ a.image
  disk_interior : ∀ x : JordanClosedDisk,
    (closedDisk x : S) ∈ U ↔ ‖(x : JordanPlane)‖ < 1
  disk_boundary : ∀ x : JordanClosedDisk,
    (closedDisk x : S) ∈ a.image ↔ ‖(x : JordanPlane)‖ = 1

/-- Jordan-Schoenflies data for the actual marked loop, including exhaustivity
of the two complementary components; no smooth atlas is involved. -/
structure MarkedLoopDiscDecomposition {M : HyperellipticModel E S}
    (a : MarkedArc M) where
  side : Fin 2 → Set S
  discs : ∀ i, ComplementaryDiscSide a (side i)
  distinct : side 0 ≠ side 1
  disjoint : Disjoint (side 0) (side 1)
  complement : side 0 ∪ side 1 = a.imageᶜ
  all_components : ∀ U, IsComplementComponent a.image U ↔ ∃ i, U = side i
  closed_cover : closure (side 0) ∪ closure (side 1) = Set.univ
  closed_intersection : closure (side 0) ∩ closure (side 1) = a.image

/-- Source Definition 2.3, using the closure of a complementary disc when
saying it meets B only at the endpoints. Non-separation makes non-loops
essential; two distinct complementary disc components witness separation. -/
def SourceEssentialMarkedArc (M : HyperellipticModel E S) (a : MarkedArc M) : Prop :=
  ¬ ∃ U V : Set S, U ≠ V ∧
    Nonempty (ComplementaryDiscSide a U) ∧
    IsComplementComponent a.image V ∧
    U ∪ V = a.imageᶜ ∧
    closure U ∩ (M.cover.branch : Set S) ⊆
      {a.map ⟨0, by norm_num⟩, a.map ⟨1, by norm_num⟩}

/-- The interval loop in any punctured chart is a genuine vendored Jordan curve. -/
theorem markedLoop_chart_jordan (M : HyperellipticModel E S) (a : MarkedArc M)
    (hloop : a.map ⟨0, by norm_num⟩ = a.map ⟨1, by norm_num⟩)
    (e : OpenPartialHomeomorph S JordanPlane)
    (hain : ∀ t : Interval, a.map t ∈ e.source) :
    Schoenflies.IsJordanCurve (Set.range (e ∘ a.map)) := by
  let g : Interval → JordanPlane := e ∘ a.map
  have hg : Continuous g := e.continuousOn.comp_continuous a.continuous hain
  let f : ℝ → JordanPlane := g ∘ Set.projIcc 0 1 zero_le_one
  have hf : Continuous f := hg.comp continuous_projIcc
  refine ⟨f, ⟨hf.continuousOn, ?_, ?_⟩, ?_⟩
  · simpa [f, g, Set.projIcc_of_mem] using congrArg e hloop
  · intro t ht u hu h
    let ti : Interval := ⟨t, ht.1, ht.2.le⟩
    let ui : Interval := ⟨u, hu.1, hu.2.le⟩
    have heq : e (a.map ti) = e (a.map ui) := by
      simpa only [f, g, Function.comp_apply, Set.projIcc_of_mem zero_le_one ⟨ht.1, ht.2.le⟩,
        Set.projIcc_of_mem zero_le_one ⟨hu.1, hu.2.le⟩, ti, ui] using h
    rcases a.injective_except_loop_closure ti ui (e.injOn (hain ti) (hain ui) heq) with h | h | h
    · exact congrArg Subtype.val h
    · have he : u = 1 := congrArg Subtype.val h.2
      exact (hu.2.ne he).elim
    · have he : t = 1 := congrArg Subtype.val h.1
      exact (ht.2.ne he).elim
  · ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t, t.property, ?_⟩
      simp [f, g, Set.projIcc_of_mem]

private theorem markedArc_exists_off_image (M : HyperellipticModel E S)
    (a : MarkedArc M) : ∃ p : S, p ∉ a.image := by
  classical
  have hnot : ¬ (M.cover.branch : Set S) ⊆
      {a.map ⟨0, by norm_num⟩, a.map ⟨1, by norm_num⟩} := by
    intro h
    have hcard := Finset.card_le_card (show M.cover.branch ⊆
      {a.map ⟨0, by norm_num⟩, a.map ⟨1, by norm_num⟩} from by
        intro x hx
        simpa only [Finset.mem_insert, Finset.mem_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] using h hx)
    have hbound : ({a.map ⟨0, by norm_num⟩, a.map ⟨1, by norm_num⟩} : Finset S).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [M.cover.branch_card] at hcard
    omega
  obtain ⟨p, hp, hends⟩ := Set.not_subset.mp hnot
  refine ⟨p, ?_⟩
  rintro ⟨t, rfl⟩
  rcases a.marked_only_at_ends t hp with rfl | rfl
  · exact hends (Set.mem_insert _ _)
  · exact hends (Set.mem_insert_of_mem _ (Set.mem_singleton _))


/-- Producer: every original model and every embedded marked loop admits the
two closed/open disc sides, not merely models supplied with a Jordan witness. -/
theorem markedLoop_disc_decomposition_exists (M : HyperellipticModel E S)
    (a : MarkedArc M)
    (hloop : a.map ⟨0, by norm_num⟩ = a.map ⟨1, by norm_num⟩) :
    Nonempty (MarkedLoopDiscDecomposition a) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨p, hp⟩ := markedArc_exists_off_image M a
  let c : CurveComplex.SpherePort.JordanCurve := {
    map := M.sphere ∘ a.map
    continuous := M.sphere.continuous.comp a.continuous
    injective_except_ends := fun t u h =>
      a.injective_except_loop_closure t u (M.sphere.injective h)
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
  have hBimage : F '' B = a.image := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y, ⟨t, ht⟩, hzy⟩ := hz
      have hval : F (OnePoint.some (P.plane y)) = M.sphere.symm y.val := by
        change M.sphere.symm (P.plane.symm (P.plane y)).val = M.sphere.symm y.val
        rw [P.plane.symm_apply_apply]
      rw [← hzy, hval]
      refine ⟨t, ?_⟩
      change a.map t = M.sphere.symm y.val
      rw [← ht]
      exact (M.sphere.symm_apply_apply _).symm
    · rintro ⟨t, rfl⟩
      let y : {x : CurveComplex.SpherePort.Sphere // x ≠ P.puncture} :=
        ⟨c.map t, fun he => P.avoids (he ▸ Set.mem_range_self t)⟩
      refine ⟨OnePoint.some (P.plane y), ⟨P.plane y, ⟨y, ⟨t, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      change M.sphere.symm (P.plane.symm (P.plane y)).val = a.map t
      rw [P.plane.symm_apply_apply]
      exact M.sphere.symm_apply_apply (a.map t)
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hx hy
    cases x with
    | infty => simpa [U] using hx
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
  obtain ⟨osU⟩ := openDiskOf S SU dsU hsUi
  obtain ⟨osV⟩ := openDiskOf S SV dsV hsVi
  have hmaximal (T R : Set S) (hT : IsConnected T) (hTopen : IsOpen T)
      (hRopen : IsOpen R) (hTR : Disjoint T R) (hc : T ∪ R = a.imageᶜ) :
      IsComplementComponent a.image T := by
    have hsub : T ⊆ a.imageᶜ := fun x hx => hc ▸ Or.inl hx
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
  have hall : ∀ W, IsComplementComponent a.image W ↔ W = SU ∨ W = SV := by
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
  let discU : ComplementaryDiscSide a SU := {
    component := hcU
    open_side := hsopenU
    closedDisk := dsU
    openDisk := osU
    interior_closure := hsintU
    boundary := hsboundU
    closure_eq := hsclU
    disk_interior := hsUi
    disk_boundary := hsUb }
  let discV : ComplementaryDiscSide a SV := {
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
    by_cases hb : x ∈ a.image
    · exact Or.inl (Or.inr hb)
    · rcases hx.mpr hb with hu | hv
      · exact Or.inl (Or.inl hu)
      · exact Or.inr (Or.inl hv)
  · change closure SU ∩ closure SV = a.image
    rw [hsclU, hsclV]
    ext x
    have hn : ¬ (x ∈ SU ∧ x ∈ SV) := fun h => Set.disjoint_left.mp hsdisj h.1 h.2
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto

/-- Observation 2.4: the actual non-loop complement is connected, so it does
not split into two complementary components. -/
theorem markedNonLoop_complement_connected (M : HyperellipticModel E S)
    (a : MarkedArc M)
    (hnonloop : a.map ⟨0, by norm_num⟩ ≠ a.map ⟨1, by norm_num⟩) :
    IsConnected a.imageᶜ := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨p, hp⟩ := markedArc_exists_off_image M a
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e : OpenPartialHomeomorph S JordanPlane :=
    M.sphere.toOpenPartialHomeomorph.trans (stereographic' 2 (M.sphere p))
  have hsource : e.source = {p}ᶜ := by
    ext x
    simp [e, OpenPartialHomeomorph.trans_source]
  have htarget : e.target = Set.univ := by
    simp [e, OpenPartialHomeomorph.trans_target]
  have hain : ∀ t : Interval, a.map t ∈ e.source := by
    intro t
    rw [hsource]
    intro ht
    apply hp
    exact Set.mem_singleton_iff.mp ht ▸ (show a.map t ∈ a.image from ⟨t, rfl⟩)
  let g : Interval → JordanPlane := e ∘ a.map
  have hg : Continuous g :=
    e.continuousOn.comp_continuous a.continuous hain
  have hgi : Function.Injective g := by
    intro t u h
    have heq := e.injOn (hain t) (hain u) h
    exact NonLoopArc.injective ⟨a, hnonloop⟩ heq
  let f : ℝ → JordanPlane := g ∘ Set.projIcc 0 1 zero_le_one
  have hf : Continuous f := hg.comp continuous_projIcc
  have hfi : Set.InjOn f (Set.Icc 0 1) := by
    intro t ht u hu h
    have h := hgi h
    simpa [f, Set.projIcc_of_mem, ht, hu] using congrArg Subtype.val h
  have hA : Schoenflies.IsArc (Set.range g) := by
    refine ⟨f, hf.continuousOn, hfi, ?_⟩
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t, t.property, ?_⟩
      simp [f, Set.projIcc_of_mem]
  have hconn := Schoenflies.arc_complement hA
  have hsymm : Continuous e.symm := by
    exact continuousOn_univ.mp (htarget ▸ e.continuousOn_symm)
  have himage : e.symm '' (Set.range g)ᶜ = a.imageᶜ ∩ {p}ᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hys : e.symm y ∈ e.source := e.map_target (htarget ▸ Set.mem_univ y)
      refine ⟨?_, hsource ▸ hys⟩
      rintro ⟨t, ht⟩
      apply hy
      refine ⟨t, ?_⟩
      change e (a.map t) = y
      rw [ht]
      exact e.right_inv (htarget ▸ Set.mem_univ y)
    · rintro ⟨hx, hxp⟩
      have hxs : x ∈ e.source := hsource.symm ▸ hxp
      refine ⟨e x, ?_, e.left_inv hxs⟩
      rintro ⟨t, ht⟩
      exact hx ⟨t, e.injOn (hain t) hxs ht⟩
  have hpunct : IsConnected (a.imageᶜ ∩ {p}ᶜ) := by
    rw [← himage]
    exact hconn.image e.symm hsymm.continuousOn
  have hsphere : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
    apply isConnected_sphere _ _ (by norm_num)
    rw [← Module.finrank_eq_rank]
    norm_num
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp hsphere
  letI : ConnectedSpace S := connectedSpace_iff_univ.mpr (by
    have hi := isConnected_univ.image M.sphere.symm M.sphere.symm.continuous.continuousOn
    simpa only [Set.image_univ, M.sphere.symm.surjective.range_eq] using hi)
  have hdense : Dense ({p}ᶜ : Set S) := by
    apply dense_compl_singleton_iff_not_open.mpr
    intro hopen
    have hsingle : ({p} : Set S) = Set.univ :=
      (show IsClopen ({p} : Set S) from ⟨isClosed_singleton, hopen⟩).eq_univ ⟨p, rfl⟩
    have hends : a.map ⟨0, by norm_num⟩ = p := by
      exact Set.mem_singleton_iff.mp (hsingle.symm ▸ Set.mem_univ _)
    exact hp ⟨_, hends⟩
  have hclosed : IsClosed a.image := by
    exact (isCompact_range a.continuous).isClosed
  have hcl : a.imageᶜ ⊆ closure (a.imageᶜ ∩ {p}ᶜ) := by
    simpa only [Set.inter_comm] using hdense.open_subset_closure_inter hclosed.isOpen_compl
  exact hpunct.subset_closure Set.inter_subset_left hcl

/-- Explicit boundary marked-point identification for an actual loop. -/
theorem markedLoop_image_inter_branch (M : HyperellipticModel E S)
    (a : MarkedArc M)
    (hloop : a.map ⟨0, by norm_num⟩ = a.map ⟨1, by norm_num⟩) :
    a.image ∩ (M.cover.branch : Set S) = {a.map ⟨0, by norm_num⟩} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    rcases a.marked_only_at_ends t ht with h | h
    · subst t
      rfl
    · subst t
      exact hloop.symm
  · intro hx
    have hx' : x = a.map ⟨0, by norm_num⟩ := hx
    subst x
    exact ⟨⟨⟨0, by norm_num⟩, rfl⟩, a.start_marked⟩

/-- Empty marked interior is precisely a closed disc whose sole mark is the
loop endpoint. This states equality, not just avoidance of other marks. -/
theorem markedLoop_disc_marked_iff (M : HyperellipticModel E S)
    (a : MarkedArc M)
    (hloop : a.map ⟨0, by norm_num⟩ = a.map ⟨1, by norm_num⟩)
    (U : Set S) (D : ComplementaryDiscSide a U) :
    (¬ ∃ b, b ∈ M.cover.branch ∧ b ∈ U) ↔
      closure U ∩ (M.cover.branch : Set S) = {a.map ⟨0, by norm_num⟩} := by
  have hboundary := markedLoop_image_inter_branch M a hloop
  constructor
  · intro hnone
    rw [D.closure_eq, Set.union_inter_distrib_right, hboundary]
    have hempty : U ∩ (M.cover.branch : Set S) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact hnone ⟨b, hb.2, hb.1⟩
    rw [hempty, Set.empty_union]
  · intro heq
    rintro ⟨b, hb, hbU⟩
    have he : b = a.map ⟨0, by norm_num⟩ :=
      Set.mem_singleton_iff.mp (heq ▸ (show b ∈ closure U ∩ (M.cover.branch : Set S) from
        ⟨subset_closure hbU, hb⟩))
    have himage : b ∈ a.image := by
      rw [he]
      exact ⟨⟨0, by norm_num⟩, rfl⟩
    exact D.component.2.2.1 hbU himage

/-- The requested unconditional source-definition identification. The Jordan
disc equivalence is a conclusion/producer dependency, never an extra input. -/
theorem essentialMarkedArc_iff_source (M : HyperellipticModel E S)
    (a : MarkedArc M) :
    IsEssentialMarkedArc M a ↔ SourceEssentialMarkedArc M a := by
  classical
  change (a.map ⟨0, by norm_num⟩ ≠ a.map ⟨1, by norm_num⟩ ∨
    ∀ U, IsComplementComponent a.image U →
      ∃ b, b ∈ M.cover.branch ∧ b ∈ U) ↔ _
  by_cases hloop : a.map ⟨0, by norm_num⟩ = a.map ⟨1, by norm_num⟩
  · constructor
    · rintro (hne | hall)
      · exact (hne hloop).elim
      · rintro ⟨U, V, hne, ⟨D⟩, hV, hcover, hmarks⟩
        obtain ⟨b, hb, hbU⟩ := hall U D.component
        have hend := hmarks ⟨subset_closure hbU, hb⟩
        have himage : b ∈ a.image := by
          rcases Set.mem_insert_iff.mp hend with h | h
          · exact h ▸ (show a.map ⟨0, by norm_num⟩ ∈ a.image from ⟨_, rfl⟩)
          · exact (Set.mem_singleton_iff.mp h) ▸
              (show a.map ⟨1, by norm_num⟩ ∈ a.image from ⟨_, rfl⟩)
        exact D.component.2.2.1 hbU himage
    · intro hsource
      right
      intro U hU
      by_contra hnone
      obtain ⟨J⟩ := markedLoop_disc_decomposition_exists M a hloop
      obtain ⟨i, rfl⟩ := (J.all_components U).mp hU
      have hmarks := (markedLoop_disc_marked_iff M a hloop (J.side i) (J.discs i)).mp hnone
      have hsubset : closure (J.side i) ∩ (M.cover.branch : Set S) ⊆
          {a.map ⟨0, by norm_num⟩, a.map ⟨1, by norm_num⟩} := by
        rw [hmarks]
        exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
      apply hsource
      fin_cases i
      · exact ⟨J.side 0, J.side 1, J.distinct, ⟨J.discs 0⟩,
          (J.discs 1).component, J.complement, hsubset⟩
      · exact ⟨J.side 1, J.side 0, J.distinct.symm, ⟨J.discs 1⟩,
          (J.discs 0).component, (Set.union_comm _ _).trans J.complement, hsubset⟩
  · have hsource : SourceEssentialMarkedArc M a := by
      rintro ⟨U, V, hne, ⟨D⟩, hV, hcover, hmarks⟩
      have hconn := markedNonLoop_complement_connected M a hloop
      have hUeq := D.component.2.2.2 a.imageᶜ hconn D.component.2.2.1 (Set.Subset.refl _)
      have hVeq := hV.2.2.2 a.imageᶜ hconn hV.2.2.1 (Set.Subset.refl _)
      exact hne (hUeq.symm.trans hVeq)
    exact ⟨fun _ => hsource, fun _ => Or.inl hloop⟩

end CurveComplex.HyperellipticModel
