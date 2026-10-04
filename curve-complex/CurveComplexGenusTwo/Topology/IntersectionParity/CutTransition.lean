import CurveComplexGenusTwo.Topology.IntersectionParity.AxisTransition
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisRecenter
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisDensity
open Set Topology Filter

namespace CurveComplex.LocalSurgery

/-- The relative side label of two actual charts straightening the same locus
extends continuously across that locus. This supplies the transition function
on their whole overlap, including points on the cut. -/
theorem axis_chart_relative_side_extension
    {S : Type*} [TopologicalSpace S] (A : Set S)
    (h k : OpenPartialHomeomorph S (ℝ × ℝ))
    (hh : ∀ x ∈ h.source, x ∈ A ↔ (h x).1 = 0)
    (hk : ∀ x ∈ k.source, x ∈ A ↔ (k x).1 = 0) :
    ∃ τ : S → ZMod 2,
      ContinuousOn τ (h.source ∩ k.source) ∧
      ∀ x ∈ h.source ∩ k.source, x ∉ A →
        τ x = (if 0 < (h x).1 then (1 : ZMod 2) else 0) +
          (if 0 < (k x).1 then (1 : ZMod 2) else 0) := by
  classical
  let W := h.source ∩ k.source
  let side : S → ZMod 2 := fun x =>
    (if 0 < (h x).1 then 1 else 0) + (if 0 < (k x).1 then 1 else 0)
  have hW : IsOpen W := h.open_source.inter k.open_source
  have hdense : Dense {x : W | (x : S) ∉ A} :=
    axis_chart_complement_dense A h hh W hW (fun _ hx => hx.1)
  have hlocal : ∀ p ∈ W, ∃ N : Set S, N ∈ 𝓝 p ∧ N ⊆ W ∧
      ∃ ε : ZMod 2, ∀ x ∈ N, x ∉ A → side x = ε := by
    intro p hp
    by_cases hpA : p ∈ A
    · let H := recenterAxisChart h p
      let K := recenterAxisChart k p
      have hs : H.source = h.source := by simp [H, recenterAxisChart]
      have ks : K.source = k.source := by simp [K, recenterAxisChart]
      have hfst (x : S) : (H x).1 = (h x).1 := rfl
      have kfst (x : S) : (K x).1 = (k x).1 := rfl
      have hpH : p ∈ H.source := hs.symm ▸ hp.1
      have hpK : p ∈ K.source := ks.symm ▸ hp.2
      have hzero : H p = (0, 0) := by
        change ((h p).1, (h p).2 - (h p).2) = (0, 0)
        rw [(hh p hp.1).mp hpA, sub_self]
      have kzero : K p = (0, 0) := by
        change ((k p).1, (k p).2 - (k p).2) = (0, 0)
        rw [(hk p hp.2).mp hpA, sub_self]
      let T := H.symm.trans K
      have hTs : (0, 0) ∈ T.source := by
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨hzero ▸ H.map_source hpH, ?_⟩
        change H.symm (0, 0) ∈ K.source
        rw [← hzero, H.left_inv hpH]
        exact hpK
      have hTzero : T (0, 0) = (0, 0) := by
        change K (H.symm (0, 0)) = (0, 0)
        calc
          K (H.symm (0, 0)) = K p := congrArg K (by rw [← hzero, H.left_inv hpH])
          _ = (0, 0) := kzero
      have hTaxis (x : ℝ × ℝ) (hx : x ∈ T.source) : x.1 = 0 ↔ (T x).1 = 0 := by
        rw [OpenPartialHomeomorph.trans_source] at hx
        have hinv : H (H.symm x) = x := H.right_inv hx.1
        have hxH := H.symm.map_source hx.1
        have haxisH := hh (H.symm x) (hs ▸ hxH)
        change H.symm x ∈ A ↔ (H (H.symm x)).1 = 0 at haxisH
        rw [hinv] at haxisH
        exact haxisH.symm.trans (hk (H.symm x) (ks ▸ hx.2))
      obtain ⟨r, hr, hrT, ε, hrelative⟩ :=
        local_axis_transition_side_constant T hTs hTzero hTaxis
      let N := W ∩ H ⁻¹' Metric.ball (0, 0) r
      have hNopen : IsOpen N := by
        have hN : N = k.source ∩ (H.source ∩ H ⁻¹' Metric.ball (0, 0) r) := by
          rw [hs]; ext x; simp [N, W, and_comm, and_left_comm, and_assoc]
        rw [hN]
        exact k.open_source.inter (H.isOpen_inter_preimage Metric.isOpen_ball)
      have hpN : p ∈ N := ⟨hp, by change H p ∈ Metric.ball (0, 0) r; rw [hzero]; exact Metric.mem_ball_self hr⟩
      refine ⟨N, hNopen.mem_nhds hpN, fun _ hx => hx.1, ε, ?_⟩
      intro x hx hxA
      have hxH : x ∈ H.source := hs.symm ▸ hx.1.1
      have hxnot : (H x).1 ≠ 0 := by
        rw [hfst]; exact fun hz => hxA ((hh x hx.1.1).mpr hz)
      have heq := hrelative (H x) hx.2 hxnot
      change (if 0 < (K (H.symm (H x))).1 then (1 : ZMod 2) else 0) = _ at heq
      rw [H.left_inv hxH, kfst, hfst] at heq
      dsimp only [side]
      rw [heq, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    · have hsign (e : OpenPartialHomeomorph S (ℝ × ℝ)) (he : p ∈ e.source)
          (hne : (e p).1 ≠ 0) :
          ∀ᶠ x in 𝓝 p,
            (if 0 < (e x).1 then (1 : ZMod 2) else 0) =
              (if 0 < (e p).1 then (1 : ZMod 2) else 0) := by
        have hc := continuous_fst.continuousAt.comp (e.continuousAt he)
        by_cases hpos : 0 < (e p).1
        · filter_upwards [hc.preimage_mem_nhds (Ioi_mem_nhds hpos)] with x hx
          change 0 < (e x).1 at hx
          simp only [if_pos hpos, if_pos hx]
        · have hneg : (e p).1 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
          filter_upwards [hc.preimage_mem_nhds (Iio_mem_nhds hneg)] with x hx
          change (e x).1 < 0 at hx
          simp only [if_neg hpos, if_neg (not_lt_of_ge hx.le)]
      have hhn : (h p).1 ≠ 0 := fun hz => hpA ((hh p hp.1).mpr hz)
      have hkn : (k p).1 ≠ 0 := fun hz => hpA ((hk p hp.2).mpr hz)
      let N := W ∩ {x | side x = side p}
      have hN : N ∈ 𝓝 p := by
        apply inter_mem (hW.mem_nhds hp)
        filter_upwards [hsign h hp.1 hhn, hsign k hp.2 hkn] with x hx hkx
        change side x = side p
        exact congrArg₂ (· + ·) hx hkx
      exact ⟨N, hN, fun _ hx => hx.1, side p, fun _ hx _ => hx.2⟩
  let D : Set W := {x | (x : S) ∉ A}
  let f : D → ZMod 2 := fun x => side x.val.val
  let di := hdense.isDenseInducing_val
  have limits (p : W) : ∃ ε : ZMod 2,
      Tendsto f (Filter.comap Subtype.val (𝓝 p)) (𝓝 ε) := by
    obtain ⟨N, hN, hNW, ε, hε⟩ := hlocal p p.property
    refine ⟨ε, ?_⟩
    have hpre : (Subtype.val : W → S) ⁻¹' N ∈ 𝓝 p :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds hN
    have hev : ∀ᶠ x : D in Filter.comap Subtype.val (𝓝 p), f x = ε := by
      apply eventually_comap.mpr
      filter_upwards [hpre] with x hx
      intro y hy
      have hyN : y.val.val ∈ N := by
        change x.val ∈ N at hx
        change y.val = x at hy
        rw [hy]
        exact hx
      exact hε y.val.val hyN y.property
    exact tendsto_const_nhds.congr' (hev.mono fun _ he => he.symm)
  let τ : S → ZMod 2 := fun x => if hx : x ∈ W then di.extend f ⟨x, hx⟩ else 0
  have hτ (x : W) : τ x = di.extend f x := by simp [τ, x.property]
  refine ⟨τ, ?_, ?_⟩
  · apply continuousOn_iff_continuous_restrict.mpr
    exact (di.continuous_extend limits).congr (fun x => (hτ x).symm)
  · intro x hx hxA
    change τ x = side x
    rw [hτ ⟨x, hx⟩]
    exact di.extend_eq' limits ⟨⟨x, hx⟩, hxA⟩

end CurveComplex.LocalSurgery
