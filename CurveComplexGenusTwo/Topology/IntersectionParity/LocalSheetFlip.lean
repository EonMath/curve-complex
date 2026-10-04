import CurveComplexGenusTwo.Topology.IntersectionParity.CutCoverDefinitions
import CurveComplexGenusTwo.Topology.IntersectionParity.CrossingChartCoordinates
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition
import CurveComplexGenusTwo.Topology.IntersectionParity.RealIntervalCoordinates
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge

open Set Topology

open scoped unitInterval

namespace CurveComplex.LocalSurgery

/-- A genuine transverse crossing changes the complement sheet of its lift
once. The interval parametrization is an actual local embedding through b. -/
theorem cut_cover_sheet_flips_at_crossing
    {S : Type*} [TopologicalSpace S] {a b : Curve S}
    (A : CurveCutCover a) (u : unitInterval)
    (hu : 0 < (u : ℝ) ∧ (u : ℝ) < 1)
    (γ : C(unitInterval, S)) (hγ : Set.InjOn γ (Set.Ioo 0 1))
    (hγimage : Set.range γ = b.image) (hcross : CrossesAt a b (γ u))
    (g : C(unitInterval, A.core.TotalSpace)) (hlift : A.core.proj ∘ g = γ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ v w : unitInterval,
        (u : ℝ) - δ < v → v < u → u < w → (w : ℝ) < u + δ →
        (A.complementTriv (g v)).2 = (A.complementTriv (g w)).2 + 1 := by
  classical
  obtain ⟨U, V, hpU, k, hU, hV, kzero, kaxes⟩ := hcross
  let K := crossingPartialChart U V hU hV ⟨γ u, hpU⟩ k
  have hKs : K.source = U := by simp [K, crossingPartialChart]
  have hKval (x : S) (hx : x ∈ U) : K x = (k ⟨x, hx⟩ : ℝ × ℝ) := by
    change crossingPartialChart U V hU hV ⟨γ u, hpU⟩ k x = _
    simp only [crossingPartialChart, OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    change (k (((⟨U, hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨γ u, hpU⟩⟩).symm x) : ℝ × ℝ) = (k ⟨x, hx⟩ : ℝ × ℝ)
    have hinv := ((⟨U, hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨γ u, hpU⟩⟩).left_inv (show (⟨x, hx⟩ : U) ∈ Set.univ from trivial)
    change ((⟨U, hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨γ u, hpU⟩⟩).symm x = ⟨x, hx⟩ at hinv
    rw [hinv]
  have hKzero : K (γ u) = (0, 0) := (hKval _ hpU).trans kzero
  have hKa (x : S) (hx : x ∈ K.source) : x ∈ a.image ↔ (K x).1 = 0 := by
    rw [hKval x (hKs ▸ hx)]
    exact (kaxes x (hKs ▸ hx)).1
  have hKb (x : S) (hx : x ∈ K.source) : x ∈ b.image ↔ (K x).2 = 0 := by
    rw [hKval x (hKs ▸ hx)]
    exact (kaxes x (hKs ▸ hx)).2
  have hpA : γ u ∈ a.image := (hKa _ (hKs.symm ▸ hpU)).mpr (by rw [hKzero])
  obtain ⟨C, hpC, hCzero, hCa, t, hts, hsheet⟩ := A.localCut (γ u) hpA
  let T := K.symm.trans C
  have hTsource : (0, 0) ∈ T.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · change (0, 0) ∈ K.target
      exact hKzero ▸ K.map_source (hKs.symm ▸ hpU)
    · change K.symm (0, 0) ∈ C.source
      rw [← hKzero, K.left_inv (hKs.symm ▸ hpU)]
      exact hpC
  have hTzero : T (0, 0) = (0, 0) := by
    change C (K.symm (0, 0)) = (0, 0)
    rw [← hKzero, K.left_inv (hKs.symm ▸ hpU)]
    exact hCzero.trans hKzero.symm
  have hTaxis (x : ℝ × ℝ) (hx : x ∈ T.source) : x.1 = 0 ↔ (T x).1 = 0 := by
    rw [OpenPartialHomeomorph.trans_source] at hx
    have hKinv : K (K.symm x) = x := K.right_inv hx.1
    have hxKs : K.symm x ∈ K.source := K.symm.map_source hx.1
    have haxisK := hKa (K.symm x) hxKs
    rw [hKinv] at haxisK
    exact haxisK.symm.trans (hCa (K.symm x) hx.2)
  obtain ⟨r, hr, hrT, ε, hrelative⟩ :=
    local_axis_transition_side_constant T hTsource hTzero hTaxis
  let realγ := realIntervalPath γ
  let realg := realIntervalPath g
  have hγreal (v : unitInterval) : realγ (v : ℝ) = γ v := by
    change γ (Set.projIcc 0 1 (by norm_num) (v : ℝ)) = γ v
    rw [Set.projIcc_of_mem _ v.property]
  have hgreal (v : unitInterval) : realg (v : ℝ) = g v := by
    change g (Set.projIcc 0 1 (by norm_num) (v : ℝ)) = g v
    rw [Set.projIcc_of_mem _ v.property]
  have hliftReal (v : ℝ) : A.core.proj (realg v) = realγ v :=
    congrFun hlift (clampToUnitInterval v)
  let Ω := C.source ∩ (K.source ∩ K ⁻¹' Metric.ball (0, 0) r)
  have hΩopen : IsOpen Ω := C.open_source.inter
    (K.isOpen_inter_preimage Metric.isOpen_ball)
  have hpΩ : γ u ∈ Ω := ⟨hpC, hKs.symm ▸ hpU, by
    change K (γ u) ∈ Metric.ball (0, 0) r
    rw [hKzero]
    exact Metric.mem_ball_self hr⟩
  obtain ⟨d, hd, hdΩ⟩ := Metric.mem_nhds_iff.mp
    (realγ.continuous.continuousAt.preimage_mem_nhds
      (hΩopen.mem_nhds (hγreal u ▸ hpΩ)))
  let δ := min d (min (u : ℝ) (1 - (u : ℝ))) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min hd (lt_min hu.1 (sub_pos.mpr hu.2))) (by norm_num)
  have hδd : δ < d := by dsimp [δ]; linarith [min_le_left d (min (u : ℝ) (1 - (u : ℝ)))]
  have hδu : δ < (u : ℝ) := by
    dsimp [δ]
    linarith [min_le_right d (min (u : ℝ) (1 - (u : ℝ))),
      min_le_left (u : ℝ) (1 - (u : ℝ))]
  have hδone : δ < 1 - (u : ℝ) := by
    dsimp [δ]
    linarith [min_le_right d (min (u : ℝ) (1 - (u : ℝ))),
      min_le_right (u : ℝ) (1 - (u : ℝ))]
  let J := Set.Icc ((u : ℝ) - δ) ((u : ℝ) + δ)
  have hJI : J ⊆ Set.Ioo (0 : ℝ) 1 :=
    Set.Icc_subset_Ioo (by linarith) (by linarith)
  have hJΩ (v : ℝ) (hv : v ∈ J) : realγ v ∈ Ω := by
    apply hdΩ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hv.1, hv.2]
  let normal : ℝ → ℝ := fun v => (K (realγ v)).1
  have hncont : ContinuousOn normal J := continuous_fst.comp_continuousOn
    (K.continuousOn.comp realγ.continuous.continuousOn (fun v hv => (hJΩ v hv).2.1))
  have hnzero : normal (u : ℝ) = 0 := by
    dsimp only [normal]
    rw [hγreal, hKzero]
  have hninj : Set.InjOn normal J := by
    intro v hv w hw heq
    have hvI := hJI hv
    have hwI := hJI hw
    let vI : unitInterval := ⟨v, hvI.1.le, hvI.2.le⟩
    let wI : unitInterval := ⟨w, hwI.1.le, hwI.2.le⟩
    have hvb : realγ v ∈ b.image := by
      rw [← hγimage, hγreal vI]
      exact ⟨vI, rfl⟩
    have hwb : realγ w ∈ b.image := by
      rw [← hγimage, hγreal wI]
      exact ⟨wI, rfl⟩
    have hvzero := (hKb _ (hJΩ v hv).2.1).mp hvb
    have hwzero := (hKb _ (hJΩ w hw).2.1).mp hwb
    have hcoords : K (realγ v) = K (realγ w) :=
      Prod.ext heq (hvzero.trans hwzero.symm)
    have hsame := K.injOn (hJΩ v hv).2.1 (hJΩ w hw).2.1 hcoords
    rw [hγreal vI, hγreal wI] at hsame
    exact congrArg Subtype.val (hγ hvI hwI hsame)
  have hmono := hncont.strictMonoOn_of_injOn_Icc'
    (show (u : ℝ) - δ ≤ (u : ℝ) + δ by linarith) hninj
  let localLabel : ℝ → ZMod 2 := fun v => (t (realg v)).2
  have hlabelcont : ContinuousOn localLabel J := continuous_snd.comp_continuousOn
    (t.continuousOn.comp realg.continuous.continuousOn (by
      intro v hv
      apply t.mem_source.mpr
      rw [hts, hliftReal]
      exact (hJΩ v hv).1))
  refine ⟨δ, hδ, ?_⟩
  intro v w hvlo hvu huw hwhi
  have hvJ : (v : ℝ) ∈ J := ⟨hvlo.le, by exact le_trans hvu.le (by linarith)⟩
  have hwJ : (w : ℝ) ∈ J := ⟨by exact le_trans (by linarith) huw.le, hwhi.le⟩
  have huJ : (u : ℝ) ∈ J := ⟨by linarith, by linarith⟩
  have hlabel : (t (g v)).2 = (t (g w)).2 := by
    have hc := isPreconnected_Icc.constant hlabelcont hvJ hwJ
    simpa only [localLabel, hgreal] using hc
  have hsigns : (0 < normal (v : ℝ) ∧ normal (w : ℝ) < 0) ∨
      (normal (v : ℝ) < 0 ∧ 0 < normal (w : ℝ)) := by
    rcases hmono with hm | hm
    · right
      constructor
      · simpa only [hnzero] using hm hvJ huJ hvu
      · simpa only [hnzero] using hm huJ hwJ huw
    · left
      constructor
      · simpa only [hnzero] using hm hvJ huJ hvu
      · simpa only [hnzero] using hm huJ hwJ huw
  have hOff (x : unitInterval) (hxJ : (x : ℝ) ∈ J)
      (hx0 : normal (x : ℝ) ≠ 0) : γ x ∉ a.image := by
    intro hxa
    have haxis := (hKa _ (hγreal x ▸ (hJΩ (x : ℝ) hxJ).2.1)).mp hxa
    exact hx0 (by simpa only [normal, hγreal] using haxis)
  have hv0 : normal (v : ℝ) ≠ 0 := by
    rcases hsigns with h | h
    · exact ne_of_gt h.1
    · exact ne_of_lt h.1
  have hw0 : normal (w : ℝ) ≠ 0 := by
    rcases hsigns with h | h
    · exact ne_of_lt h.2
    · exact ne_of_gt h.2
  have hproj (x : unitInterval) : A.core.proj (g x) = γ x := congrFun hlift x
  have sheetFormula (x : unitInterval) (hxJ : (x : ℝ) ∈ J)
      (hx0 : normal (x : ℝ) ≠ 0) :
      (A.complementTriv (g x)).2 = (t (g x)).2 +
        (if 0 < normal (x : ℝ) then (1 : ZMod 2) else 0) + ε := by
    have hxΩ := hγreal x ▸ hJΩ (x : ℝ) hxJ
    have hs := hsheet (g x) (hproj x ▸ hxΩ.1) (hproj x ▸ hOff x hxJ hx0)
    rw [hproj x] at hs
    have hrel := hrelative (K (γ x)) hxΩ.2.2 (by simpa only [normal, hγreal] using hx0)
    have hTval : T (K (γ x)) = C (γ x) := by
      change C (K.symm (K (γ x))) = C (γ x)
      rw [K.left_inv hxΩ.2.1]
    rw [hTval] at hrel
    rw [hrel] at hs
    simpa only [normal, hγreal, add_assoc] using hs
  rw [sheetFormula v hvJ hv0, sheetFormula w hwJ hw0, hlabel]
  rcases hsigns with ⟨hvp, hwn⟩ | ⟨hvn, hwp⟩
  · simp only [ite_eq_left hvp, ite_eq_right (not_lt.mpr hwn.le), add_zero]
    ring
  · simp only [ite_eq_right (not_lt.mpr hvn.le), ite_eq_left hwp, add_zero]
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    linear_combination -htwo

end CurveComplex.LocalSurgery
