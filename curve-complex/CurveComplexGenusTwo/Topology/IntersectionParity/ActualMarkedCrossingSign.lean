import CurveComplexGenusTwo.Topology.IntersectionParity.CrossingChartCoordinates
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition
import CurveComplexGenusTwo.Topology.IntersectionParity.RealIntervalCoordinates
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Mathlib.Topology.ContinuousMap.Basic

namespace CurveComplex.HyperellipticModel
open Set Topology CurveComplex.LocalSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Marked-arc version of the existing uncentered adapted-axis sign change.
Its crossing hypothesis is the original open mark-free two-axis disk chart.
There is no sign-change, graph, selector, or puncture-free-region input. -/
theorem actual_marked_transverse_uncentered_axis_signs_flip
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (u : Interval) (hu : 0<u.val ∧ u.val<1)
    (γ : C(Interval,S)) (hγ : Set.InjOn γ (Set.Ioo 0 1))
    (hγimage : Set.range γ⊆b.val.image)
    (hcross : ArcSurgery.CrossesInDisk M a b (γ u))
    (C : OpenPartialHomeomorph S (ℝ × ℝ)) (hpC : γ u∈C.source)
    (hCa : ∀ x∈C.source,x∈a.val.image ↔ (C x).1=0) :
    ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
      u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
      (C (γ v)).1≠0 ∧ (C (γ w)).1≠0 ∧
      ((0<(C (γ v)).1) ↔ ¬(0<(C (γ w)).1)) := by
  have centered (C : OpenPartialHomeomorph S (ℝ × ℝ))
      (hpC : γ u ∈ C.source) (hCzero : C (γ u) = (0,0))
      (hCa : ∀ x∈C.source,x∈a.val.image ↔ (C x).1=0) :
      ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,
        u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
        (C (γ v)).1≠0 ∧ (C (γ w)).1≠0 ∧
        ((0<(C (γ v)).1) ↔ ¬(0<(C (γ w)).1)) := by
    classical
    obtain ⟨U, hU, hpU, hmarks, e, hezero, hea, heb⟩ := hcross
    let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
    have hV : IsOpen V := (isOpen_lt (continuous_fst.abs) continuous_const).inter
      (isOpen_lt (continuous_snd.abs) continuous_const)
    let swap : V ≃ₜ V :=
      { toFun := fun q => ⟨(q.val.2,q.val.1),q.property.2,q.property.1⟩
        invFun := fun q => ⟨(q.val.2,q.val.1),q.property.2,q.property.1⟩
        left_inv := fun q => by cases q; rfl
        right_inv := fun q => by cases q; rfl
        continuous_toFun := (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _
        continuous_invFun := (continuous_subtype_val.snd.prodMk continuous_subtype_val.fst).subtype_mk _ }
    let k : U ≃ₜ V := e.trans swap
    have kzero : (k ⟨γ u,hpU⟩ : ℝ × ℝ) = (0,0) := by
      change ((e ⟨γ u,hpU⟩).val.2,(e ⟨γ u,hpU⟩).val.1) = (0,0)
      rw [hezero]
    have kaxes (x : S) (hx : x∈U) :
        (x∈a.val.image ↔ (k ⟨x,hx⟩).val.1=0) ∧
        (x∈b.val.image ↔ (k ⟨x,hx⟩).val.2=0) := ⟨hea ⟨x,hx⟩,heb ⟨x,hx⟩⟩
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
    have hKa (x : S) (hx : x ∈ K.source) : x ∈ a.val.image ↔ (K x).1 = 0 := by
      rw [hKval x (hKs ▸ hx)]
      exact (kaxes x (hKs ▸ hx)).1
    have hKb (x : S) (hx : x ∈ K.source) : x ∈ b.val.image ↔ (K x).2 = 0 := by
      rw [hKval x (hKs ▸ hx)]
      exact (kaxes x (hKs ▸ hx)).2
    have hpA : γ u ∈ a.val.image := (hKa _ (hKs.symm ▸ hpU)).mpr (by rw [hKzero])
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
    have hγreal (v : unitInterval) : realγ (v : ℝ) = γ v := by
      change γ (Set.projIcc 0 1 (by norm_num) (v : ℝ)) = γ v
      rw [Set.projIcc_of_mem _ v.property]
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
      have hvb : realγ v ∈ b.val.image := by
        rw [hγreal vI]
        exact hγimage ⟨vI, rfl⟩
      have hwb : realγ w ∈ b.val.image := by
        rw [hγreal wI]
        exact hγimage ⟨wI, rfl⟩
      have hvzero := (hKb _ (hJΩ v hv).2.1).mp hvb
      have hwzero := (hKb _ (hJΩ w hw).2.1).mp hwb
      have hcoords : K (realγ v) = K (realγ w) :=
        Prod.ext heq (hvzero.trans hwzero.symm)
      have hsame := K.injOn (hJΩ v hv).2.1 (hJΩ w hw).2.1 hcoords
      rw [hγreal vI, hγreal wI] at hsame
      exact congrArg Subtype.val (hγ hvI hwI hsame)
    have hmono := hncont.strictMonoOn_of_injOn_Icc'
      (show (u : ℝ) - δ ≤ (u : ℝ) + δ by linarith) hninj
    refine ⟨δ,hδ,?_⟩
    intro v w hvlo hvu huw hwhi
    have hvJ : (v : ℝ) ∈ J := ⟨hvlo.le, by exact le_trans hvu.le (by linarith)⟩
    have hwJ : (w : ℝ) ∈ J := ⟨by exact le_trans (by linarith) huw.le, hwhi.le⟩
    have huJ : (u : ℝ) ∈ J := ⟨by linarith, by linarith⟩
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
    have hnv : normal (v : ℝ) ≠ 0 := by
      rcases hsigns with h | h
      · exact ne_of_gt h.1
      · exact ne_of_lt h.1
    have hnw : normal (w : ℝ) ≠ 0 := by
      rcases hsigns with h | h
      · exact ne_of_lt h.2
      · exact ne_of_gt h.2
    have pointAxis (x : unitInterval) (hxJ : (x : ℝ) ∈ J)
        (hx0 : normal (x : ℝ) ≠ 0) :
        (C (γ x)).1 ≠ 0 ∧
        (if 0 < (C (γ x)).1 then (1 : ZMod 2) else 0) =
          (if 0 < normal (x : ℝ) then (1 : ZMod 2) else 0) + ε := by
      have hxΩ := hγreal x ▸ hJΩ (x : ℝ) hxJ
      have hrel := hrelative (K (γ x)) hxΩ.2.2 (by
        simpa only [normal, hγreal] using hx0)
      have hTval : T (K (γ x)) = C (γ x) := by
        change C (K.symm (K (γ x))) = C (γ x)
        rw [K.left_inv hxΩ.2.1]
      rw [hTval] at hrel
      constructor
      · intro hz
        have ha := (hCa _ hxΩ.1).mpr hz
        have hK := (hKa _ hxΩ.2.1).mp ha
        exact hx0 (by simpa only [normal, hγreal] using hK)
      · simpa only [normal, hγreal] using hrel
    obtain ⟨hcv,hvlabel⟩ := pointAxis v hvJ hnv
    obtain ⟨hcw,hwlabel⟩ := pointAxis w hwJ hnw
    have hdiff : (if 0 < (C (γ v)).1 then (1 : ZMod 2) else 0) ≠
        (if 0 < (C (γ w)).1 then (1 : ZMod 2) else 0) := by
      intro he
      have hh := add_right_cancel (hvlabel.symm.trans (he.trans hwlabel))
      rcases hsigns with ⟨hvp,hwn⟩ | ⟨hvn,hwp⟩
      · simp [hvp,not_lt.mpr hwn.le] at hh
      · simp [not_lt.mpr hvn.le,hwp] at hh
    refine ⟨hcv,hcw,?_⟩
    by_cases hvp : 0 < (C (γ v)).1
    · by_cases hwp : 0 < (C (γ w)).1
      · exact False.elim (hdiff (by simp only [if_pos hvp,if_pos hwp]))
      · simp only [hvp,hwp,not_false_eq_true]
    · by_cases hwp : 0 < (C (γ w)).1
      · simp only [hvp,hwp,not_true_eq_false]
      · exact False.elim (hdiff (by simp only [if_neg hvp,if_neg hwp]))
  have hmem : γ u ∈ a.val.image := by
    obtain ⟨U,hU,hp,hmarks,e,hzero,ha,hb⟩ := hcross
    apply (ha ⟨γ u,hp⟩).mpr
    exact congrArg Prod.snd hzero
  have hnzero : (C (γ u)).1 = 0 := (hCa _ hpC).mp hmem
  let D : OpenPartialHomeomorph S (ℝ × ℝ) :=
    C.trans (Homeomorph.addRight (-C (γ u))).toOpenPartialHomeomorph
  have hsource : D.source = C.source := by
    ext x
    simp only [D,OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source,Set.preimage_univ,Set.inter_univ]
  have hfirst (x : S) : (D x).1 = (C x).1 := by
    change (C x).1 + (-(C (γ u))).1 = (C x).1
    change (C x).1 + -(C (γ u)).1 = (C x).1
    rw [hnzero]
    simp
  have hDzero : D (γ u) = (0,0) := by
    change C (γ u) + -C (γ u) = (0,0)
    exact add_neg_cancel _
  have hDa (x : S) (hx : x ∈ D.source) : x ∈ a.val.image ↔ (D x).1 = 0 := by
    rw [hfirst]
    exact hCa x (hsource ▸ hx)
  obtain ⟨δ,hδ,hflip⟩ := centered
    D (hsource.symm ▸ hpC) hDzero hDa
  refine ⟨δ,hδ,?_⟩
  intro v w hvlo hvu huw hwhi
  simpa only [hfirst] using hflip v w hvlo hvu huw hwhi

end CurveComplex.HyperellipticModel
