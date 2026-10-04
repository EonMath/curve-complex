import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverDefinitions
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChartSelection
import CurveComplexGenusTwo.Topology.IntersectionParity.CutTransition
import CurveComplexGenusTwo.Topology.IntersectionParity.TwoSheetCocycle
open Set Topology Filter

namespace CurveComplex.LocalSurgery

/-- Construct the genuine two-sheeted cut cover of the actual embedded circle.
All local sheet transitions are prescribed in CurveCutCover; no crossing-count
or isotopy-parity identity occurs in its assumptions or fields. -/
theorem embedded_curve_has_cut_double_cover
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a : Curve S) : Nonempty (CurveCutCover a) := by
  classical
  let C := selectedAxisChart a
  let D := cutAtlasDomain a
  let label := cutAtlasOffAxisLabel a
  have hchart (p : a.image) : p.val ∈ (C p).source ∧ C p p.val = (0, 0) ∧
      ∀ x ∈ (C p).source, x ∈ a.image ↔ (C p x).1 = 0 := by
    let H := embedded_curve_has_local_axis_chart a p p.property
    let U := H.choose
    let V := H.choose_spec.choose
    let hp := H.choose_spec.choose_spec.choose
    let h := H.choose_spec.choose_spec.choose_spec.choose
    let spec := H.choose_spec.choose_spec.choose_spec.choose_spec
    have hCs : (C p).source = U := by simp [C, selectedAxisChart, H, U, V, hp, h, crossingPartialChart]
    have hval (x : S) (hx : x ∈ U) : C p x = (h ⟨x, hx⟩ : ℝ × ℝ) := by
      change crossingPartialChart U V spec.1 spec.2.1 ⟨p, hp⟩ h x = _
      simp only [crossingPartialChart, OpenPartialHomeomorph.trans_apply,
        Homeomorph.toOpenPartialHomeomorph_apply]
      change (h (((⟨U, spec.1⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
        ⟨⟨p, hp⟩⟩).symm x) : ℝ × ℝ) = (h ⟨x, hx⟩ : ℝ × ℝ)
      have hinv := ((⟨U, spec.1⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
        ⟨⟨p, hp⟩⟩).left_inv (show (⟨x, hx⟩ : U) ∈ Set.univ from trivial)
      change ((⟨U, spec.1⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
        ⟨⟨p, hp⟩⟩).symm x = ⟨x, hx⟩ at hinv
      rw [hinv]
    refine ⟨hCs.symm ▸ hp, (hval p hp).trans spec.2.2.1, ?_⟩
    intro x hx
    rw [hval x (hCs ▸ hx)]
    have hxU : x ∈ U := hCs ▸ hx
    exact spec.2.2.2 x hxU
  have hclosed : IsClosed a.image := by
    simpa [Curve.image, Set.image_univ] using (isCompact_univ.image a.embedded.continuous).isClosed
  have hDopen : ∀ i, IsOpen (D i) := by
    intro i
    cases i with
    | none => exact hclosed.isOpen_compl
    | some p => exact (C p).open_source
  have hDmem : ∀ x, x ∈ D (cutAtlasIndexAt a x) := by
    intro x
    by_cases hx : x ∈ a.image
    · simpa [cutAtlasIndexAt, D, cutAtlasDomain, hx, C] using (hchart ⟨x, hx⟩).1
    · simpa [cutAtlasIndexAt, D, cutAtlasDomain, hx] using hx
  have hlabelcont : ∀ i, ContinuousOn (label i) (D i ∩ a.imageᶜ) := by
    intro i
    cases i with
    | none => exact continuousOn_const
    | some p =>
      intro x hx
      have hn : (C p x).1 ≠ 0 := fun hz => hx.2 ((hchart p).2.2 x hx.1 |>.mpr hz)
      have hc := continuous_fst.continuousAt.comp ((C p).continuousAt hx.1)
      have he : (label (some p)) =ᶠ[𝓝 x] fun _ => label (some p) x := by
        by_cases hpos : 0 < (C p x).1
        · filter_upwards [hc.preimage_mem_nhds (Ioi_mem_nhds hpos)] with y hy
          change 0 < (C p y).1 at hy
          simp [label, cutAtlasOffAxisLabel, C, hpos, hy]
        · have hneg : (C p x).1 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hn
          filter_upwards [hc.preimage_mem_nhds (Iio_mem_nhds hneg)] with y hy
          change (C p y).1 < 0 at hy
          simp [label, cutAtlasOffAxisLabel, C, hpos, not_lt_of_ge hy.le]
      exact he.continuousAt.continuousWithinAt
  have hchanges : ∀ i j : Option a.image, ∃ τ : S → ZMod 2,
      ContinuousOn τ (D i ∩ D j) ∧
      ∀ x ∈ D i ∩ D j, x ∉ a.image → τ x = label i x + label j x := by
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact ⟨fun _ => 0, continuousOn_const, by intros; simp [label, cutAtlasOffAxisLabel]⟩
      | some q =>
        refine ⟨label (some q), (hlabelcont (some q)).mono (fun x hx => ⟨hx.2, hx.1⟩), ?_⟩
        intros
        simp [label, cutAtlasOffAxisLabel]
    | some p =>
      cases j with
      | none =>
        refine ⟨label (some p), (hlabelcont (some p)).mono (fun _ hx => hx), ?_⟩
        intros
        simp [label, cutAtlasOffAxisLabel]
      | some q =>
        exact axis_chart_relative_side_extension a.image (C p) (C q)
          (hchart p).2.2 (hchart q).2.2
  let τ := fun i j => (hchanges i j).choose
  have hτcont (i j) : ContinuousOn (τ i j) (D i ∩ D j) := (hchanges i j).choose_spec.1
  have hτval (i j) (x : S) (hx : x ∈ D i ∩ D j) (hxa : x ∉ a.image) :
      τ i j x = label i x + label j x := (hchanges i j).choose_spec.2 x hx hxa
  have hdense (i : Option a.image) (W : Set S) (hW : IsOpen W) (hWi : W ⊆ D i) :
      Dense {x : W | (x : S) ∉ a.image} := by
    cases i with
    | none =>
      have heq : {x : W | (x : S) ∉ a.image} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact hWi x.property
      rw [heq]
      exact dense_univ
    | some p => exact axis_chart_complement_dense a.image (C p) (hchart p).2.2 W hW hWi
  have huniq (i : Option a.image) (W : Set S) (hW : IsOpen W) (hWi : W ⊆ D i)
      (f g : S → ZMod 2) (hf : ContinuousOn f W) (hg : ContinuousOn g W)
      (heq : ∀ x ∈ W, x ∉ a.image → f x = g x) : Set.EqOn f g W := by
    have hden := (hdense i W hW hWi).denseRange_val
    have heq' : W.domRestrict f = W.domRestrict g := hden.equalizer
      (continuousOn_iff_continuous_restrict.mp hf)
      (continuousOn_iff_continuous_restrict.mp hg)
      (funext fun x => heq x.val.val x.val.property x.property)
    intro x hx
    exact congrFun heq' ⟨x, hx⟩
  have hself : ∀ i x, x ∈ D i → τ i i x = 0 := by
    intro i
    apply huniq i (D i) (hDopen i) (fun _ hx => hx) (τ i i) (fun _ => 0)
      (by simpa only [Set.inter_self] using hτcont i i) continuousOn_const
    intro x hx hxa
    rw [hτval i i x ⟨hx, hx⟩ hxa, CharTwo.add_self_eq_zero]
  have hAdd : Continuous (fun q : ZMod 2 × ZMod 2 => q.1 + q.2) := continuous_of_discreteTopology
  have hcocycle : ∀ i j k x, x ∈ D i ∩ D j ∩ D k →
      τ i j x + τ j k x = τ i k x := by
    intro i j k
    apply huniq i (D i ∩ D j ∩ D k) ((hDopen i).inter (hDopen j) |>.inter (hDopen k))
      (fun _ hx => hx.1.1) (fun x => τ i j x + τ j k x) (τ i k)
      (hAdd.comp_continuousOn (((hτcont i j).mono fun _ hx => hx.1).prodMk
        ((hτcont j k).mono fun _ hx => ⟨hx.1.2, hx.2⟩)))
      ((hτcont i k).mono fun _ hx => ⟨hx.1.1, hx.2⟩)
    intro x hx hxa
    rw [hτval i j x hx.1 hxa, hτval j k x ⟨hx.1.2, hx.2⟩ hxa,
      hτval i k x ⟨hx.1.1, hx.2⟩ hxa]
    rw [add_assoc, ← add_assoc (label j x), CharTwo.add_self_eq_zero, zero_add]
  let atlas : TwoSheetCocycle (Option a.image) S :=
    ⟨D, hDopen, cutAtlasIndexAt a, hDmem, τ, hτcont, hself, hcocycle⟩
  let core := atlas.bundleCore
  refine ⟨{
    core := core
    complementTriv := core.localTriv none
    complement_baseSet := rfl
    localCut := ?_ }⟩
  intro p hp
  let q : a.image := ⟨p, hp⟩
  refine ⟨C q, (hchart q).1, (hchart q).2.1, (hchart q).2.2,
    core.localTriv (some q), rfl, ?_⟩
  intro z hz hzoff
  have hidx := hDmem z.proj
  have hco := hcocycle (cutAtlasIndexAt a z.proj) (some q) none z.proj ⟨⟨hidx, hz⟩, hzoff⟩
  have hlast := hτval (some q) none z.proj ⟨hz, hzoff⟩ hzoff
  change τ (some q) none z.proj =
    (if 0 < (C q z.proj).1 then 1 else 0) + 0 at hlast
  rw [add_zero] at hlast
  rw [FiberBundleCore.localTriv_apply, FiberBundleCore.localTriv_apply]
  change (show ZMod 2 from z.snd) + τ (cutAtlasIndexAt a z.proj) none z.proj =
    ((show ZMod 2 from z.snd) + τ (cutAtlasIndexAt a z.proj) (some q) z.proj) +
      (if 0 < (C q z.proj).1 then 1 else 0)
  rw [← hco, hlast, add_assoc]

end CurveComplex.LocalSurgery
