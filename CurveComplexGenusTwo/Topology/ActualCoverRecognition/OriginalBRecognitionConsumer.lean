import CurveComplexGenusTwo.Topology.ActualCoverRecognition.OriginalActualCoverRecognitionProved
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.FiniteFundamentalGroupFirstHomologyProof
import CurveComplexGenusTwo.Dictionary.Genus
import Schoenflies.GeneralCrosscut
import Schoenflies.JordanSchoenflies
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import CurveComplexGenusTwo.Topology.ActualCoverRecognition.EssentialCirclePlanarNoReturnDependencies
import CurveComplexGenusTwo.Topology.PositionExtension.SurfacePuncture
import CurveComplexGenusTwo.Topology.PositionExtension.LocalOrientationAlgebra
import CurveComplexGenusTwo.Topology.CapBandGeometry.GlobalCountableUniversalCoverHeader
import CurveComplexGenusTwo.Topology.IntersectionParity.BigonDiskData
import CurveComplexGenusTwo.Topology.LocalSurgery.LoopCircleStatement

namespace CurveComplex.LocalSurgery

/-- The actual clean lifted arc and its one-turn translate cannot have
alternating endpoints on an escaping, two-sided periodic strip. -/
theorem periodic_strip_clean_embedded_arc_has_short_displacement
    (Φ : C(Set.Ioo (-1 : ℝ) 1 × ℝ, Schoenflies.Plane))
    (hΦ : Topology.IsOpenEmbedding Φ)
    (D : Schoenflies.Plane ≃ₜ Schoenflies.Plane)
    (hshift : ∀ v : Set.Ioo (-1 : ℝ) 1 × ℝ,
      D (Φ v) = Φ (v.1, v.2 + 2 * Real.pi))
    (hescape : ∀ K : Set Schoenflies.Plane, IsCompact K →
      ∀ a : ℝ, ∀ k : ℤ, k ≠ 0 → ∃ n : ℕ,
        Φ (⟨0, by norm_num⟩, a + (k * n : ℤ) * (2 * Real.pi)) ∉ K)
    (x y : ℝ)
    (α : Path (Φ (⟨0, by norm_num⟩, x)) (Φ (⟨0, by norm_num⟩, y)))
    (hα : Topology.IsEmbedding α)
    (hclean : α '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆
      (Set.range (fun r : ℝ => Φ (⟨0, by norm_num⟩, r)))ᶜ)
    (hdisjoint : Disjoint (Set.range α) (D '' Set.range α)) :
    |y - x| < 2 * Real.pi := by
  classical
  have forward (x y : ℝ)
      (α : Path (Φ (⟨0, by norm_num⟩, x)) (Φ (⟨0, by norm_num⟩, y)))
      (hα : Topology.IsEmbedding α)
      (hclean : α '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆
        (Set.range (fun r : ℝ => Φ (⟨0, by norm_num⟩, r)))ᶜ)
      (hdisjoint : Disjoint (Set.range α) (D '' Set.range α))
      (hxy : x < y) : y - x < 2 * Real.pi := by
    let zeroW : Set.Ioo (-1 : ℝ) 1 := ⟨0, by norm_num⟩
    let β : ℝ → Schoenflies.Plane := fun r => Φ (zeroW, r)
    have hβcont : Continuous β := Φ.continuous.comp (continuous_const.prodMk continuous_id)
    have hβinj : Function.Injective β := by
      intro r s he
      exact congrArg Prod.snd (hΦ.injective he)
    have hxyne : x ≠ y := by
      intro he
      have hh : α (0 : CurveComplex.Interval) = α 1 := by simp [he]
      have := hα.injective hh
      exact zero_ne_one this
    have hmeet (r : ℝ) (t : CurveComplex.Interval) (he : β r = α t) :
        t = 0 ∨ t = 1 := by
      by_contra ht
      have ht0 : t ≠ 0 := fun h => ht (Or.inl h)
      have ht1 : t ≠ 1 := fun h => ht (Or.inr h)
      have hti : t ∈ Set.Ioo (0 : CurveComplex.Interval) 1 :=
        ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0),
         lt_of_le_of_ne (unitInterval.le_one t) ht1⟩
      exact hclean ⟨t, hti, rfl⟩ ⟨r, he⟩
    have hαarc : Schoenflies.IsArcBetween (Set.range α) (β x) (β y) := by
      refine ⟨α.extend, α.continuous_extend.continuousOn, ?_, ?_, α.extend_zero, α.extend_one⟩
      · intro t ht u hu he
        rw [Path.extend_apply α ht, Path.extend_apply α hu] at he
        exact congrArg Subtype.val (hα.injective he)
      · ext z
        constructor
        · rintro ⟨t, ht, he⟩
          exact ⟨⟨t, ht⟩, (Path.extend_apply α ht).symm.trans he⟩
        · rintro ⟨t, rfl⟩
          exact ⟨t.val, t.property, Path.extend_apply α t.property⟩
    let q : ℝ → Schoenflies.Plane := fun t => β (x + t * (y - x))
    have hqarc : Schoenflies.IsArcBetween (β '' Set.uIcc x y) (β x) (β y) := by
      refine ⟨q, hβcont.comp (by fun_prop) |>.continuousOn, ?_, ?_, ?_, ?_⟩
      · intro t ht s hs he
        have hh := hβinj he
        apply mul_right_cancel₀ (sub_ne_zero.mpr hxyne.symm)
        linarith
      · change (β ∘ Schoenflies.reparam x y) '' Set.Icc (0 : ℝ) 1 = _
        rw [Set.image_comp, Schoenflies.image_reparam_I]
      · simp [q]
      · simp [q]
    let J : Set Schoenflies.Plane := Set.range α ∪ β '' Set.uIcc x y
    have hJ : Schoenflies.IsJordanCurve J := by
      apply Schoenflies.isJordanCurve_union hαarc hqarc
      rintro z ⟨t, rfl⟩ ⟨r, hr, he⟩
      rcases hmeet r t he with rfl | rfl
      · exact Or.inl α.source
      · exact Or.inr α.target
    have hsep := Schoenflies.jordan_curve_theorem hJ
    have hJcompact : IsCompact (closure (Schoenflies.inside J)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
    have hshiftβ (r : ℝ) : D (β r) = β (r + 2 * Real.pi) := hshift (zeroW, r)
    have hendshift : y ≠ x + 2 * Real.pi ∧ x ≠ y + 2 * Real.pi := by
      constructor
      · intro he
        exact Set.disjoint_left.mp hdisjoint ⟨1, α.target⟩
          ⟨α 0, ⟨0, rfl⟩, by rw [α.source]; exact (hshiftβ x).trans (congrArg β he.symm)⟩
      · intro he
        exact Set.disjoint_left.mp hdisjoint ⟨0, α.source⟩
          ⟨α 1, ⟨1, rfl⟩, by rw [α.target]; exact (hshiftβ y).trans (congrArg β he.symm)⟩
    have hcenteravoid (r : ℝ) (hr : r ∉ Set.uIcc x y) : β r ∉ J := by
      rintro (⟨t, ht⟩ | ⟨s, hs, he⟩)
      · rcases hmeet r t ht.symm with rfl | rfl
        · have he : r = x := hβinj (ht.symm.trans α.source)
          exact hr (he ▸ Set.left_mem_uIcc)
        · have he : r = y := hβinj (ht.symm.trans α.target)
          exact hr (he ▸ Set.right_mem_uIcc)
      · exact hr (hβinj he ▸ hs)
    have hcenteroutside (r : ℝ) (hr : r ∉ Set.uIcc x y) :
        β r ∈ Schoenflies.outside J := by
      have havoid := hcenteravoid r hr
      have hregions : β r ∈ Schoenflies.inside J ∪ Schoenflies.outside J := by
        rw [Schoenflies.inside_union_outside]
        exact havoid
      refine hregions.resolve_left ?_
      intro hinside
      let R : Set ℝ := if max x y < r then Set.Ioi (max x y) else Set.Iio (min x y)
      have hrR : r ∈ R := by
        dsimp [R]
        split_ifs with hh
        · exact hh
        · have := hr
          rw [Set.uIcc, Set.mem_Icc, not_and_or] at this
          rcases this with ht | ht
          · exact lt_of_not_ge ht
          · exact (hh (lt_of_not_ge ht)).elim
      have hRconn : IsPreconnected R := by
        dsimp [R]
        split_ifs
        · exact isPreconnected_Ioi
        · exact isPreconnected_Iio
      have hRavoid : β '' R ⊆ Jᶜ := by
        rintro z ⟨s, hs, rfl⟩
        apply hcenteravoid
        intro hi
        dsimp [R] at hs
        split_ifs at hs with hh
        · exact (not_lt_of_ge hi.2) hs
        · exact (not_lt_of_ge hi.1) hs
      have hRinside : β '' R ⊆ Schoenflies.inside J := by
        have hh := (hRconn.image β hβcont.continuousOn).subset_connectedComponentIn
          (Set.mem_image_of_mem β hrR) hRavoid
        rwa [hsep.connectedComponentIn_eq_inside hinside] at hh
      let k : ℤ := if max x y < r then 1 else -1
      have hk : k ≠ 0 := by dsimp [k]; split_ifs <;> norm_num
      obtain ⟨n, hn⟩ := hescape (closure (Schoenflies.inside J)) hJcompact r k hk
      apply hn
      apply subset_closure
      apply hRinside
      refine ⟨r + (k * n : ℤ) * (2 * Real.pi), ?_, rfl⟩
      dsimp [R, k]
      split_ifs with hh
      · change max x y < r + ((1 : ℤ) * n : ℤ) * (2 * Real.pi)
        simp only [one_mul, Int.cast_natCast]
        have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [Real.pi_pos]
      · change r + ((-1 : ℤ) * n : ℤ) * (2 * Real.pi) < min x y
        simp only [neg_one_mul, Int.cast_neg, Int.cast_natCast]
        have : r < min x y := by simpa [R, hh] using hrR
        have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [Real.pi_pos]
    by_contra hlt
    have hlarge : x + 2 * Real.pi < y := by
      have hle : x + 2 * Real.pi ≤ y := by linarith
      exact lt_of_le_of_ne hle (Ne.symm hendshift.1)
    let Jd : Set Schoenflies.Plane := D '' J
    have hJd : Schoenflies.IsJordanCurve Jd :=
      CurveComplex.jordan_curve_homeomorph_image hJ D
    have hsepd := Schoenflies.jordan_curve_theorem hJd
    have hDinside : D '' Schoenflies.inside J = Schoenflies.inside Jd :=
      CurveComplex.jordan_inside_homeomorph_image D J
    have hDoutside (z : Schoenflies.Plane) (hz : z ∈ Schoenflies.outside J) :
        D z ∈ Schoenflies.outside Jd := by
      have havoid : D z ∉ Jd := by
        rintro ⟨w, hw, he⟩
        exact hz.1 (D.injective he ▸ hw)
      have hregions : D z ∈ Schoenflies.inside Jd ∪ Schoenflies.outside Jd := by
        rw [Schoenflies.inside_union_outside]
        exact havoid
      refine hregions.resolve_left ?_
      intro hi
      rw [← hDinside] at hi
      obtain ⟨w, hw, he⟩ := hi
      exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside
        (D.injective he ▸ hw) hz
    have hcenteroutsideD (r : ℝ) (hr : r - 2 * Real.pi ∉ Set.uIcc x y) :
        β r ∈ Schoenflies.outside Jd := by
      have hh := hDoutside (β (r - 2 * Real.pi)) (hcenteroutside _ hr)
      rw [hshiftβ] at hh
      convert hh using 1 <;> congr 1 <;> ring
    have hxoutsideD : β x ∈ Schoenflies.outside Jd := by
      apply hcenteroutsideD
      rw [Set.uIcc_of_le hxy.le]
      intro hi
      linarith [hi.1, Real.pi_pos]
    have hαavoidD : α '' Set.Ico (0 : CurveComplex.Interval) 1 ⊆ Jdᶜ := by
      rintro z ⟨t, ht, rfl⟩ ⟨w, (⟨s, rfl⟩ | ⟨r, hr, rfl⟩), he⟩
      · exact Set.disjoint_left.mp hdisjoint ⟨t, rfl⟩ ⟨α s, ⟨s, rfl⟩, he⟩
      · have htJd : α t ∈ Jd := ⟨β r, Or.inr ⟨r, hr, rfl⟩, he⟩
        rw [hshiftβ] at he
        rcases hmeet _ t he with ht0 | ht1
        · exact hxoutsideD.1 (by simpa [ht0] using htJd)
        · exact (ne_of_lt ht.2) ht1
    have hαoutsideD : α '' Set.Ico (0 : CurveComplex.Interval) 1 ⊆
        Schoenflies.outside Jd := by
      have hh := (isPreconnected_Ico.image α α.continuous.continuousOn).subset_connectedComponentIn
          (show α 0 ∈ α '' Set.Ico (0 : CurveComplex.Interval) 1 from
            ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩) hαavoidD
      rw [α.source, hsepd.connectedComponentIn_eq_outside hxoutsideD] at hh
      exact hh
    have hJnoinsideD : J ⊆ (Schoenflies.inside Jd)ᶜ := by
      rintro z (⟨t, rfl⟩ | ⟨r, hr, rfl⟩) hi
      · by_cases ht : t < 1
        · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hi
            (hαoutsideD ⟨t, ⟨unitInterval.nonneg t, ht⟩, rfl⟩)
        · have ht1 : t = 1 := le_antisymm (unitInterval.le_one t) (le_of_not_gt ht)
          subst t
          apply hi.1
          refine ⟨β (y - 2 * Real.pi), Or.inr ⟨y - 2 * Real.pi, ?_, rfl⟩, ?_⟩
          · rw [Set.uIcc_of_le hxy.le]
            constructor <;> linarith [Real.pi_pos]
          · rw [hshiftβ, α.target]
            congr 1
            ring
      · by_cases hrl : r < x + 2 * Real.pi
        · apply Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hi
          apply hcenteroutsideD
          rw [Set.uIcc_of_le hxy.le]
          intro hh
          linarith [hh.1]
        · apply hi.1
          refine ⟨β (r - 2 * Real.pi), Or.inr ⟨r - 2 * Real.pi, ?_, rfl⟩, ?_⟩
          · rw [Set.uIcc_of_le hxy.le] at hr ⊢
            constructor <;> linarith [hr.1, hr.2, Real.pi_pos]
          · rw [hshiftβ]
            congr 1
            ring
    have hoverlap : (Schoenflies.inside Jd ∩ Schoenflies.inside J).Nonempty := by
      let s : ℝ := (x + y - 2 * Real.pi) / 2
      let a : ℝ := (x + s) / 2
      let b : ℝ := (s + 2 * Real.pi + y) / 2
      have hxa : x < a := by dsimp [a, s]; linarith
      have has : a < s := by dsimp [a, s]; linarith
      have hsT : s + 2 * Real.pi < b := by dsimp [b, s]; linarith
      have hby : b < y := by dsimp [b, s]; linarith
      have hab : a < b := by linarith [Real.pi_pos]
      let O : Set (Set.Ioo (-1 : ℝ) 1 × ℝ) := Φ ⁻¹' (Set.range α)ᶜ
      have hO : IsOpen O := (isCompact_range α.continuous).isClosed.isOpen_compl.preimage Φ.continuous
      have hcenterO : ({zeroW} : Set (Set.Ioo (-1 : ℝ) 1)) ×ˢ Set.Icc a b ⊆ O := by
        rintro ⟨w, r⟩ ⟨hw, hr⟩
        have hw0 : w = zeroW := hw
        subst w
        rintro ⟨t, he⟩
        rcases hmeet r t he.symm with ht | ht
        · have hh : r = x := hβinj (he.symm.trans (ht ▸ α.source))
          linarith [hr.1]
        · have hh : r = y := hβinj (he.symm.trans (ht ▸ α.target))
          linarith [hr.2]
      obtain ⟨U, V, hU, hV, hzeroU, hIV, hUV⟩ :=
        generalized_tube_lemma isCompact_singleton isCompact_Icc hO hcenterO
      have hzero : zeroW ∈ U := hzeroU (Set.mem_singleton zeroW)
      let B : Set (Set.Ioo (-1 : ℝ) 1 × ℝ) := U ×ˢ Set.Ioo a (b - 2 * Real.pi)
      have hBopen : IsOpen B := hU.prod isOpen_Ioo
      have hBs : (zeroW, s) ∈ B := ⟨hzero, has, by linarith⟩
      have hβsclosure : β s ∈ closure (Schoenflies.inside J) := by
        apply frontier_subset_closure
        rw [hsep.frontier_inside]
        exact Or.inr ⟨s, by rw [Set.uIcc_of_le hxy.le]; constructor <;> linarith [Real.pi_pos], rfl⟩
      have hboxopen : IsOpen (Φ '' B) := hΦ.isOpenMap B hBopen
      have hβsbox : β s ∈ Φ '' B := ⟨(zeroW, s), hBs, rfl⟩
      obtain ⟨z, hzbox, hzi⟩ : (Φ '' B ∩ Schoenflies.inside J).Nonempty :=
        Set.Nonempty.of_closure ⟨_, hboxopen.inter_closure ⟨hβsbox, hβsclosure⟩⟩
      obtain ⟨⟨w, t⟩, ⟨hwU, hat, htb⟩, rfl⟩ := hzbox
      change a < t at hat
      change t < b - 2 * Real.pi at htb
      have hwne : w ≠ zeroW := by
        intro hw
        apply hzi.1
        refine Or.inr ⟨t, ?_, ?_⟩
        · rw [Set.uIcc_of_le hxy.le]
          constructor <;> linarith [Real.pi_pos]
        · subst w
          rfl
      let H : Set Schoenflies.Plane := (fun r : ℝ => Φ (w, r)) '' Set.Icc t (t + 2 * Real.pi)
      have hHconn : IsPreconnected H := isPreconnected_Icc.image _
        (Φ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn
      have hHavoid : H ⊆ Jᶜ := by
        rintro z ⟨r, hr, rfl⟩ (hαr | ⟨q, hq, he⟩)
        · have hrab : r ∈ Set.Icc a b := by constructor <;> linarith [hr.1, hr.2]
          exact hUV (show (w, r) ∈ U ×ˢ V from ⟨hwU, hIV hrab⟩) hαr
        · have hh : (zeroW, q) = (w, r) := hΦ.injective he
          exact hwne (congrArg Prod.fst hh).symm
      have hHinside : H ⊆ Schoenflies.inside J := by
        have hh := hHconn.subset_connectedComponentIn
          (show Φ (w, t) ∈ H from ⟨t, ⟨le_rfl, by linarith [Real.pi_pos]⟩, rfl⟩) hHavoid
        rwa [hsep.connectedComponentIn_eq_inside hzi] at hh
      refine ⟨Φ (w, t + 2 * Real.pi), ?_, ?_⟩
      · rw [← hDinside]
        exact ⟨Φ (w, t), hzi, hshift (w, t)⟩
      · exact hHinside ⟨t + 2 * Real.pi, ⟨by linarith [Real.pi_pos], le_rfl⟩, rfl⟩
    obtain ⟨w, hwd, hw⟩ := hoverlap
    have hDsubset : Schoenflies.inside Jd ⊆ Schoenflies.inside J := by
      have hh := hsepd.isConnected_inside.isPreconnected.subset_connectedComponentIn hwd
        (show Schoenflies.inside Jd ⊆ Jᶜ from fun z hz hJz => hJnoinsideD hJz hz)
      rwa [hsep.connectedComponentIn_eq_inside hw] at hh
    have hlast : β (y + 2 * Real.pi) ∈ closure (Schoenflies.inside J) := by
      apply closure_mono hDsubset
      apply frontier_subset_closure
      rw [hsepd.frontier_inside]
      exact ⟨β y, Or.inr ⟨y, Set.right_mem_uIcc, rfl⟩, hshiftβ y⟩
    have hlastoutside : β (y + 2 * Real.pi) ∈ Schoenflies.outside J := by
      apply hcenteroutside
      rw [Set.uIcc_of_le hxy.le]
      intro hi
      linarith [hi.2, Real.pi_pos]
    have hnonempty : (Schoenflies.outside J ∩ Schoenflies.inside J).Nonempty :=
      Set.Nonempty.of_closure ⟨_, hsep.isOpen_outside.inter_closure ⟨hlastoutside, hlast⟩⟩
    obtain ⟨z, hzo, hzi⟩ := hnonempty
    exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzi hzo
  have hxyne : x ≠ y := by
    intro he
    have hh : α (0 : CurveComplex.Interval) = α 1 := by simp [he]
    exact zero_ne_one (hα.injective hh)
  rcases lt_or_gt_of_ne hxyne with hxy | hyx
  · simpa [abs_of_pos (sub_pos.mpr hxy)] using forward x y α hα hclean hdisjoint hxy
  · have hrev : Topology.IsEmbedding α.symm := hα.comp unitInterval.symmHomeomorph.isEmbedding
    have hrevclean : α.symm '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆
        (Set.range (fun r : ℝ => Φ (⟨0, by norm_num⟩, r)))ᶜ := by
      rintro z ⟨t, ht, rfl⟩
      apply hclean
      refine ⟨unitInterval.symm t, ?_, rfl⟩
      constructor <;> change _ < _
      · change 0 < 1 - (t : ℝ)
        have := ht.2
        exact sub_pos.mpr this
      · change 1 - (t : ℝ) < 1
        have htpos : (0 : ℝ) < t := by exact_mod_cast ht.1
        linarith
    have hrevdisjoint : Disjoint (Set.range α.symm) (D '' Set.range α.symm) := by
      simpa only [Path.symm_range] using hdisjoint
    have hh := forward y x α.symm hrev hrevclean hrevdisjoint hyx
    rw [abs_of_neg (sub_neg.mpr hyx)]
    linarith

end CurveComplex.LocalSurgery

namespace CurveComplex.LocalSurgery
open scoped Manifold ContDiff

theorem actual_original_returning_comparison_has_short_angular_lift
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (genus : ℕ) (hgenus : 2 ≤ genus) (hS : CurveComplex.IsGenus S genus)
    (a b : CurveComplex.EssentialCurve S)
    (ht : CurveComplex.Transverse a.val b.val)
    (u z : S) (huz : u ≠ z) (f g : Path u z)
    (hf : Topology.IsEmbedding f)
    (hfcurve : Set.range f ⊆ a.val.image)
    (hgcurve : Set.range g ⊆ b.val.image)
    (hclean : f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.val.imageᶜ)
    (hhom : f.Homotopic g) :
    ∃ p : C(CurveComplex.Interval, ℝ),
      (∀ t, b.val.map (Circle.exp (p t)) = g t) ∧
      |p 1 - p 0| < 2 * Real.pi := by
  classical
  let E := b.val.embedded.toHomeomorph
  let γ : C(CurveComplex.Interval, Circle) :=
    ⟨fun t => E.symm ⟨g t, hgcurve ⟨t, rfl⟩⟩,
      E.symm.continuous.comp (g.continuous.subtype_mk _)⟩
  have hγ (t : CurveComplex.Interval) : b.val.map (γ t) = g t :=
    congrArg Subtype.val (E.apply_symm_apply ⟨g t, hgcurve ⟨t, rfl⟩⟩)
  obtain ⟨r, hr⟩ := Circle.exp_surjective (γ 0)
  let p := Circle.isCoveringMap_exp.liftPath γ r hr.symm
  have hp (t : CurveComplex.Interval) : b.val.map (Circle.exp (p t)) = g t := by
    have hl := congrFun (Circle.isCoveringMap_exp.liftPath_lifts γ r hr.symm) t
    change Circle.exp (p t) = γ t at hl
    rw [hl]
    exact hγ t
  have hfmeet (t : CurveComplex.Interval) (htb : f t ∈ b.val.image) : t = 0 ∨ t = 1 := by
    by_cases ht0 : t = 0
    · exact Or.inl ht0
    by_cases ht1 : t = 1
    · exact Or.inr ht1
    have hti : t ∈ Set.Ioo (0 : CurveComplex.Interval) 1 :=
      ⟨lt_of_le_of_ne (by exact t.property.1) (Ne.symm ht0),
        lt_of_le_of_ne (by exact t.property.2) ht1⟩
    exact False.elim ((hclean ⟨t, hti, rfl⟩) htb)
  have hNoReflection (x : S) (W : CurveComplex.GenusOrientationCandidate.LocalReflectionWitness x) : False :=
    CurveComplex.GenusOrientationCandidate.no_local_reflection_witness genus hS x
      (CurveComplex.GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W
  obtain ⟨tU, hcount, hhaus, ⟨chartU⟩, hsimply, hquot, hsurj, hnull⟩ :=
    closed_surface_actual_second_countable_universal_cover u
  let U := Σ z : S, Path.Homotopic.Quotient u z
  letI : TopologicalSpace U := tU
  letI : T2Space U := hhaus
  letI : SecondCountableTopology U := hcount
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) U := chartU
  letI : SimplyConnectedSpace U := hsimply
  let e : U := ⟨u, Path.Homotopic.Quotient.mk (Path.refl u)⟩
  let cov := hquot.isCoveringMap
  let F : C(CurveComplex.Interval, U) := cov.liftPath f.toContinuousMap e f.source
  let G : C(CurveComplex.Interval, U) := cov.liftPath g.toContinuousMap e g.source
  have hF (v : CurveComplex.Interval) : (F v).1 = f v :=
    congrFun (cov.liftPath_lifts f.toContinuousMap e f.source) v
  have hG (v : CurveComplex.Interval) : (G v).1 = g v :=
    congrFun (cov.liftPath_lifts g.toContinuousMap e g.source) v
  have hstart : F 0 = G 0 := by
    dsimp [F, G]
    rw [cov.liftPath_zero, cov.liftPath_zero]
  have hend : F 1 = G 1 :=
    cov.liftPath_apply_one_eq_of_homotopicRel hhom e f.source g.source
  have hFembedded : Topology.IsEmbedding F := by
    have hc : (Sigma.fst : U → S) ∘ F = f := funext hF
    have hi := hf
    rw [← hc] at hi
    exact Topology.IsEmbedding.of_comp F.continuous cov.continuous hi
  have hFavoid (v : CurveComplex.Interval) (hv : v ∈ Set.Ioo (0 : CurveComplex.Interval) 1) :
      (F v).1 ∉ b.val.image := by
    rw [hF]
    exact hclean ⟨v, hv, rfl⟩
  have hGon (v : CurveComplex.Interval) : (G v).1 ∈ b.val.image := by
    rw [hG]
    exact hgcurve ⟨v, rfl⟩
  letI : IsCancelSMul (deck (Sigma.fst : U → S)) U := hquot.isCancelSMul
  have hdeckDisjoint (d : deck (Sigma.fst : U → S)) (hd : d ≠ 1) :
      Disjoint (Set.range F) (Set.range (fun v : CurveComplex.Interval => d • F v)) := by
    rw [Set.disjoint_left]
    rintro x ⟨v, rfl⟩ ⟨w, hw⟩
    have hbase : f w = f v := by
      have hh := congrArg (Sigma.fst : U → S) hw
      rw [deck.proj_smul (p := (Sigma.fst : U → S)) d (F w), hF, hF] at hh
      exact hh
    have hwv : w = v := hf.injective hbase
    subst w
    exact hd (IsCancelSMul.right_cancel d 1 (F v) (by simpa using hw))
  let B : C(ℝ, S) := ⟨fun v => b.val.map (Circle.exp v),
    b.val.embedded.continuous.comp Circle.exp.continuous⟩
  have hBstart : (F 0).1 = B (p 0) := by
    calc (F 0).1 = f 0 := hF 0
         _ = u := f.source
         _ = g 0 := g.source.symm
         _ = b.val.map (Circle.exp (p 0)) := (hp 0).symm
  obtain ⟨β, ⟨hβstart, hβprojection⟩, hβunique⟩ :=
    cov.existsUnique_continuousMap_lifts B (p 0) (F 0) hBstart
  have hβ (v : ℝ) : (β v).1 = b.val.map (Circle.exp v) :=
    congrFun hβprojection v
  have hβp : (fun v : CurveComplex.Interval => β (p v)) = G := by
    apply cov.eq_of_comp_eq (β.continuous.comp p.continuous) G.continuous
    · ext v
      exact (hβ (p v)).trans ((hp v).trans (hG v).symm)
    · exact hβstart.trans hstart
  have hβend : β (p 1) = F 1 := (congrFun hβp 1).trans hend.symm
  have hturn : (β (p 0 + 2 * Real.pi)).1 = (β (p 0)).1 := by
    rw [hβ, hβ, Circle.periodic_exp]
  obtain ⟨d, hd⟩ := hquot.apply_eq_iff_mem_orbit.mp hturn
  have hdeckShift (v : ℝ) : d • β v = β (v + 2 * Real.pi) := by
    have heq : (fun w : ℝ => d • β w) = (fun w : ℝ => β (w + 2 * Real.pi)) := by
      apply cov.eq_of_comp_eq
        ((continuous_const_smul d).comp β.continuous)
        (β.continuous.comp (by fun_prop))
      · ext w
        change (d • β w).1 = (β (w + 2 * Real.pi)).1
        rw [deck.proj_smul (p := (Sigma.fst : U → S)) d (β w), hβ, hβ, Circle.periodic_exp]
      · exact hd
    exact congrFun heq v
  have hH1Infinite : Infinite (CurveComplex.integralHomology S 1) := by
    obtain ⟨E⟩ := hS.2.2.2
    let j : Fin (2 * genus) := ⟨0, by omega⟩
    let v : ℤ → CurveComplex.integralHomology S 1 :=
      fun n => E.toLinearEquiv.symm (fun _ => n)
    apply Infinite.of_injective v
    intro n m he
    have hh := congrArg (fun w => E.toLinearEquiv w j) he
    simpa [v] using hh
  have hplane : Nonempty (Schoenflies.Plane ≃ₜ U) := by
    have hmodel : Nonempty (Schoenflies.Plane ≃ₜ U) ∨
        Nonempty ((Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ≃ₜ U) := by
      exact closed_surface_simply_connected_cover_plane_or_sphere
        (Sigma.fst : U → S) cov hsurj
    rcases hmodel with hplane | hsphere
    · exact hplane
    · obtain ⟨esphere⟩ := hsphere
      letI : CompactSpace U := esphere.compactSpace
      let K : Set U := (Sigma.fst : U → S) ⁻¹' {u}
      have hKclosed : IsClosed K := isClosed_singleton.preimage cov.continuous
      letI : CompactSpace K := isCompact_iff_compactSpace.mp hKclosed.isCompact
      letI : DiscreteTopology K := (cov u).discreteTopology_fiber
      letI : Finite K := finite_of_compact_of_discrete
      let point : Path.Homotopic.Quotient u u → K :=
        fun q => ⟨⟨u, q⟩, rfl⟩
      have hpoint : Function.Injective point := by
        intro q r he
        have hh : HEq q r := (Sigma.mk.inj_iff.mp (congrArg Subtype.val he)).2
        exact eq_of_heq hh
      letI : Finite (Path.Homotopic.Quotient u u) := Finite.of_injective point hpoint
      letI : Finite (FundamentalGroup S u) := by
        change Finite (Path.Homotopic.Quotient u u)
        infer_instance
      letI : LocallyPathConnectedSpace S :=
        ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
      letI : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
      have hFiniteH1 : Finite (CurveComplex.integralHomology S 1) := by
        exact finite_integral_first_homology_of_finite_fundamental_group S u
      letI := hFiniteH1
      letI := hH1Infinite
      exact (not_finite (CurveComplex.integralHomology S 1)).elim
  obtain ⟨e⟩ := hplane
  have hnoreturn := actual_planar_essential_lift_has_no_integer_return
    (Sigma.fst : U → S) hquot e.symm b β hβ
  have hβinjective : Function.Injective β := by
    intro v w hvw
    have hexp : Circle.exp v = Circle.exp w :=
      b.val.embedded.injective ((hβ v).symm.trans
        ((congrArg (Sigma.fst : U → S) hvw).trans (hβ w)))
    obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp hexp
    by_cases hnzero : n = 0
    · simpa [hnzero] using hn
    · apply False.elim
      apply hnoreturn n hnzero w
      rw [← hn]
      exact hvw
  have hdne : d ≠ 1 := by
    intro he
    change d • β (p 0) = β (p 0 + 2 * Real.pi) at hd
    rw [he, one_smul] at hd
    have hx := hβinjective hd
    nlinarith [Real.pi_pos]
  have hUnoncompact (hcomp : CompactSpace U) : False := by
    letI := hcomp
    let K : Set U := (Sigma.fst : U → S) ⁻¹' {u}
    have hKclosed : IsClosed K := isClosed_singleton.preimage cov.continuous
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKclosed.isCompact
    letI : DiscreteTopology K := (cov u).discreteTopology_fiber
    letI : Finite K := finite_of_compact_of_discrete
    let point : ℕ → K := fun n => ⟨β (p 0 + (n : ℝ) * (2 * Real.pi)), by
      change (β (p 0 + (n : ℝ) * (2 * Real.pi))).1 = u
      rw [hβ]
      have hexp : Circle.exp (p 0 + (n : ℝ) * (2 * Real.pi)) = Circle.exp (p 0) :=
        Circle.exp_eq_exp.mpr ⟨(n : ℤ), by push_cast; ring⟩
      rw [hexp, hp 0, g.source]⟩
    have hi : Function.Injective point := by
      intro m n hh
      have hh' := hβinjective (congrArg Subtype.val hh)
      have hc : (m : ℝ) = n := by nlinarith [Real.pi_pos]
      exact_mod_cast hc
    letI : Finite ℕ := Finite.of_injective point hi
    exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) Set.finite_univ
  have hcompactFiber (K : Set U) (hK : IsCompact K) (q : S) :
      (K ∩ (Sigma.fst : U → S) ⁻¹' {q}).Finite := by
    let V : Set U := (Sigma.fst : U → S) ⁻¹' {q}
    let M : Set U := K ∩ V
    letI : DiscreteTopology V := (cov q).discreteTopology_fiber
    letI : DiscreteTopology M :=
      (Topology.IsEmbedding.inclusion (show M ⊆ V from Set.inter_subset_right)).discreteTopology
    have hm : IsCompact M := hK.inter_right (isClosed_singleton.preimage cov.continuous)
    exact hm.finite (isDiscrete_iff_discreteTopology.mpr inferInstance)
  have hβescape (K : Set U) (hK : IsCompact K) (a : ℝ) (k : ℤ) (hk : k ≠ 0) :
      ∃ n : ℕ, β (a + (k * n : ℤ) * (2 * Real.pi)) ∉ K := by
    by_contra h
    push_neg at h
    let M : Set U := K ∩ (Sigma.fst : U → S) ⁻¹' {b.val.map (Circle.exp a)}
    letI : Finite M := (hcompactFiber K hK (b.val.map (Circle.exp a))).to_subtype
    let point : ℕ → M := fun n => ⟨β (a + (k * n : ℤ) * (2 * Real.pi)), h n, by
      change (β (a + (k * n : ℤ) * (2 * Real.pi))).1 = b.val.map (Circle.exp a)
      rw [hβ]
      congr 1
      exact Circle.exp_eq_exp.mpr ⟨k * n, rfl⟩⟩
    have hi : Function.Injective point := by
      intro m n hh
      have hr := hβinjective (congrArg Subtype.val hh)
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      have he : ((m : ℝ) - n) * (k : ℝ) = 0 := by
        push_cast at hr
        have ht : ((k : ℝ) * m - (k : ℝ) * n) * (2 * Real.pi) = 0 := by nlinarith [hr]
        have hz := (mul_eq_zero.mp ht).resolve_right (by positivity : 2 * Real.pi ≠ 0)
        nlinarith [hz]
      have hc := (mul_eq_zero.mp he).resolve_right hkR
      have hmn : (m : ℝ) = n := sub_eq_zero.mp hc
      exact_mod_cast hmn
    letI : Finite ℕ := Finite.of_injective point hi
    exact (Set.infinite_univ : (Set.univ : Set ℕ).Infinite) Set.finite_univ
  obtain ⟨collar, hcollar, hcollarCenter⟩ :=
    actual_original_essential_circle_has_annular_collar S genus hgenus hS b
  let W := Set.Ioo (-1 : ℝ) 1
  let zeroW : W := ⟨0, by norm_num [W]⟩
  letI : ContractibleSpace W := (convex_Ioo (𝕜 := ℝ) (-1 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩
  letI : LocallyPathConnectedSpace W := isOpen_Ioo.locallyPathConnectedSpace
  let PC : C(W × ℝ, W × Circle) :=
    ⟨fun z => (z.1, Circle.exp z.2), continuous_fst.prodMk (Circle.exp.continuous.comp continuous_snd)⟩
  let Cmap : C(W × ℝ, S) := collar.comp PC
  have hPC : IsLocalHomeomorph PC := by
    intro z
    obtain ⟨e, he, heq⟩ := Circle.isCoveringMap_exp.isLocalHomeomorph z.2
    refine ⟨(OpenPartialHomeomorph.refl W).prod e, ?_, ?_⟩
    · exact ⟨Set.mem_univ _, he⟩
    · funext v
      exact Prod.ext rfl (congrFun heq v.2)
  have hCstart : (F 0).1 = Cmap (zeroW, p 0) := by
    change (F 0).1 = collar (zeroW, Circle.exp (p 0))
    rw [hcollarCenter]
    exact hBstart
  obtain ⟨Φ, ⟨hΦstart, hΦprojection⟩, hΦunique⟩ :=
    cov.existsUnique_continuousMap_lifts Cmap (zeroW, p 0) (F 0) hCstart
  have hΦPoint (v : W × ℝ) : (Φ v).1 = collar (PC v) := congrFun hΦprojection v
  have hΦcenter (v : ℝ) : Φ (zeroW, v) = β v := by
    have heq : (fun w : ℝ => Φ (zeroW, w)) = β := by
      apply cov.eq_of_comp_eq
        (Φ.continuous.comp (continuous_const.prodMk continuous_id)) β.continuous
      · ext w
        change (Φ (zeroW, w)).1 = (β w).1
        rw [hΦPoint, hβ]
        exact hcollarCenter (Circle.exp w)
      · exact hΦstart.trans hβstart.symm
    exact congrFun heq v
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have hh := congrArg (Sigma.fst : U → S) hxy
    have hh' : collar (PC x) = collar (PC y) := by
      exact (hΦPoint x).symm.trans (hh.trans (hΦPoint y))
    have hpcs := hcollar.injective hh'
    have hwidth : x.1 = y.1 := congrArg (fun z : W × Circle => z.1) hpcs
    have hcircle : Circle.exp x.2 = Circle.exp y.2 := congrArg (fun z : W × Circle => z.2) hpcs
    have heq : (fun w : W => Φ (w, x.2)) = (fun w : W => Φ (w, y.2)) := by
      refine cov.eq_of_comp_eq
        (Φ.continuous.comp (continuous_id.prodMk continuous_const))
        (Φ.continuous.comp (continuous_id.prodMk continuous_const)) ?_ x.1 ?_
      · ext w
        change (Φ (w, x.2)).1 = (Φ (w, y.2)).1
        rw [hΦPoint, hΦPoint]
        change collar (w, Circle.exp x.2) = collar (w, Circle.exp y.2)
        rw [hcircle]
      · exact hxy.trans (congrArg Φ (Prod.ext hwidth.symm rfl))
    have hreal : x.2 = y.2 := hβinjective (by
      simpa only [hΦcenter] using congrFun heq zeroW)
    exact Prod.ext hwidth hreal
  have hΦloc : IsLocalHomeomorph Φ := by
    have hloc := hcollar.isLocalHomeomorph.comp hPC
    change IsLocalHomeomorph Cmap at hloc
    rw [← hΦprojection] at hloc
    exact hloc.of_comp cov.isLocalHomeomorph Φ.continuous
  have hΦopen : Topology.IsOpenEmbedding Φ := hΦloc.isOpenEmbedding_of_injective hΦinj
  have hΦshift (v : W × ℝ) : d • Φ v = Φ (v.1, v.2 + 2 * Real.pi) := by
    have heq : (fun w : W × ℝ => d • Φ w) =
        (fun w : W × ℝ => Φ (w.1, w.2 + 2 * Real.pi)) := by
      apply cov.eq_of_comp_eq ((continuous_const_smul d).comp Φ.continuous)
        (Φ.continuous.comp (by fun_prop))
      · ext w
        change (d • Φ w).1 = (Φ (w.1, w.2 + 2 * Real.pi)).1
        rw [deck.proj_smul (p := (Sigma.fst : U → S)) d (Φ w)]
        rw [hΦPoint, hΦPoint]
        change collar (w.1, Circle.exp w.2) = collar (w.1, Circle.exp (w.2 + 2 * Real.pi))
        rw [Circle.periodic_exp]
      · change d • Φ (zeroW, p 0) = Φ (zeroW, p 0 + 2 * Real.pi)
        rw [hΦcenter, hΦcenter]
        exact hdeckShift (p 0)
    exact congrFun heq v
  let ΦP : C(W × ℝ, Schoenflies.Plane) := (⟨e.symm, e.symm.continuous⟩ : C(U, Schoenflies.Plane)).comp Φ
  have hΦPopen : Topology.IsOpenEmbedding ΦP := e.symm.isOpenEmbedding.comp hΦopen
  let D : Schoenflies.Plane ≃ₜ Schoenflies.Plane :=
    (e.trans (d : U ≃ₜ U)).trans e.symm
  have hΦPshift (v : W × ℝ) : D (ΦP v) = ΦP (v.1, v.2 + 2 * Real.pi) := by
    change e.symm ((d : U ≃ₜ U) (e (e.symm (Φ v)))) =
      e.symm (Φ (v.1, v.2 + 2 * Real.pi))
    rw [e.apply_symm_apply]
    exact congrArg e.symm (hΦshift v)
  let α : Path (ΦP (zeroW, p 0)) (ΦP (zeroW, p 1)) :=
    { toFun := fun v => e.symm (F v)
      continuous_toFun := e.symm.continuous.comp F.continuous
      source' := congrArg e.symm (hβstart.symm.trans (hΦcenter (p 0)).symm)
      target' := congrArg e.symm (hβend.symm.trans (hΦcenter (p 1)).symm) }
  have hαembedded : Topology.IsEmbedding α := e.symm.isEmbedding.comp hFembedded
  have hαclean : α '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆
      (Set.range (fun r : ℝ => ΦP (zeroW, r)))ᶜ := by
    rintro z ⟨v, hv, rfl⟩ ⟨r, hr⟩
    have hr' : β r = F v := by
      apply e.symm.injective
      change e.symm (Φ (zeroW, r)) = e.symm (F v) at hr
      rw [hΦcenter] at hr
      exact hr
    apply hFavoid v hv
    rw [← congrArg (Sigma.fst : U → S) hr', hβ]
    exact Set.mem_range_self _
  have hαdisjoint : Disjoint (Set.range α) (D '' Set.range α) := by
    rw [Set.disjoint_left]
    rintro z ⟨v, rfl⟩ ⟨w, ⟨r, rfl⟩, he⟩
    have heU : d • F r = F v := by
      have hh := congrArg e he
      change e (e.symm ((d : U ≃ₜ U) (e (e.symm (F r))))) = e (e.symm (F v)) at hh
      change (d : U ≃ₜ U) (F r) = F v
      simpa only [Homeomorph.apply_symm_apply] using hh
    exact Set.disjoint_left.mp (hdeckDisjoint d hdne) ⟨v, rfl⟩ ⟨r, heU⟩
  have hΦPescape (K : Set Schoenflies.Plane) (hK : IsCompact K) (a : ℝ) (k : ℤ)
      (hk : k ≠ 0) : ∃ n : ℕ, ΦP (zeroW, a + (k * n : ℤ) * (2 * Real.pi)) ∉ K := by
    obtain ⟨n, hn⟩ := hβescape (e '' K) (hK.image e.continuous) a k hk
    refine ⟨n, ?_⟩
    intro hh
    apply hn
    refine ⟨ΦP (zeroW, a + (k * n : ℤ) * (2 * Real.pi)), hh, ?_⟩
    change e (e.symm (Φ (zeroW, a + (k * n : ℤ) * (2 * Real.pi)))) = _
    rw [e.apply_symm_apply, hΦcenter]
  refine ⟨p, hp, ?_⟩
  exact periodic_strip_clean_embedded_arc_has_short_displacement
    ΦP hΦPopen D hΦPshift hΦPescape (p 0) (p 1) α hαembedded hαclean hαdisjoint

theorem embedded_comparison_of_short_angular_lift
    {S : Type} [TopologicalSpace S] [T2Space S]
    (b : CurveComplex.Curve S) (u z : S) (huz : u ≠ z)
    (g : Path u z) (p : C(CurveComplex.Interval, ℝ))
    (hp : ∀ t, b.map (Circle.exp (p t)) = g t)
    (hshort : |p 1 - p 0| < 2 * Real.pi) :
    ∃ g' : Path u z, Topology.IsEmbedding g' ∧
      Set.range g' ⊆ b.image ∧ g.Homotopic g' := by
  let q : C(CurveComplex.Interval, ℝ) :=
    ⟨fun t => (1 - (t : ℝ)) * p 0 + (t : ℝ) * p 1, by fun_prop⟩
  have q0 : q 0 = p 0 := by simp [q]
  have q1 : q 1 = p 1 := by simp [q]
  have hne : p 0 ≠ p 1 := by
    intro he
    apply huz
    calc u = b.map (Circle.exp (p 0)) := g.source.symm.trans (hp 0).symm
         _ = b.map (Circle.exp (p 1)) := by rw [he]
         _ = z := (hp 1).trans g.target
  let g' : Path u z :=
    { toFun := fun t => b.map (Circle.exp (q t))
      continuous_toFun := b.embedded.continuous.comp (Circle.exp.continuous.comp q.continuous)
      source' := by rw [q0, hp]; exact g.source
      target' := by rw [q1, hp]; exact g.target }
  have hbounds (t : CurveComplex.Interval) :
      q t ∈ Set.Icc (min (p 0) (p 1)) (max (p 0) (p 1)) := by
    dsimp [q]
    constructor
    · have h0 := min_le_left (p 0) (p 1)
      have h1 := min_le_right (p 0) (p 1)
      nlinarith [t.property.1, t.property.2]
    · have h0 := le_max_left (p 0) (p 1)
      have h1 := le_max_right (p 0) (p 1)
      nlinarith [t.property.1, t.property.2]
  have hwidth : max (p 0) (p 1) - min (p 0) (p 1) < 2 * Real.pi := by
    rw [max_sub_min_eq_abs]
    simpa [abs_sub_comm] using hshort
  have hqi : Function.Injective (fun t => Circle.exp (q t)) := by
    intro t v he
    have hh := Circle.exp_injOn_Icc hwidth (hbounds t) (hbounds v) he
    apply Subtype.ext
    dsimp [q] at hh
    have hn : p 1 - p 0 ≠ 0 := sub_ne_zero.mpr hne.symm
    have hm : ((t : ℝ) - (v : ℝ)) * (p 1 - p 0) = 0 := by nlinarith [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hn)
  refine ⟨g', ?_, ?_, ?_⟩
  · exact b.embedded.comp
      ((Circle.exp.continuous.comp q.continuous).isClosedEmbedding hqi).isEmbedding
  · rintro y ⟨t, rfl⟩
    exact Set.mem_range_self _
  · refine ⟨{ toFun := fun x => b.map (Circle.exp
        ((1 - (x.1 : ℝ)) * p x.2 + (x.1 : ℝ) * q x.2))
              continuous_toFun := b.embedded.continuous.comp (Circle.exp.continuous.comp (by fun_prop))
              map_zero_left := ?_
              map_one_left := ?_
              prop' := ?_ }⟩
    · intro t
      simpa using hp t
    · intro t
      simp [g']
    · intro t v hv
      rcases hv with hv | hv
      · subst v
        change b.map (Circle.exp ((1 - (t : ℝ)) * p 0 + (t : ℝ) * q 0)) = g 0
        rw [q0]
        convert hp 0 using 2 <;> ring
      · have hv' : v = 1 := hv
        subst v
        change b.map (Circle.exp ((1 - (t : ℝ)) * p 1 + (t : ℝ) * q 1)) = g 1
        rw [q1]
        convert hp 1 using 2 <;> ring

theorem actual_original_returning_comparison_has_embedded_path
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (genus : ℕ) (hgenus : 2 ≤ genus) (hS : CurveComplex.IsGenus S genus)
    (a b : CurveComplex.EssentialCurve S)
    (ht : CurveComplex.Transverse a.val b.val)
    (u z : S) (huz : u ≠ z) (f g : Path u z)
    (hf : Topology.IsEmbedding f)
    (hfcurve : Set.range f ⊆ a.val.image)
    (hgcurve : Set.range g ⊆ b.val.image)
    (hclean : f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.val.imageᶜ)
    (hhom : f.Homotopic g) :
    ∃ g' : Path u z, Topology.IsEmbedding g' ∧
      Set.range g' ⊆ b.val.image ∧ f.Homotopic g' := by
  obtain ⟨p, hp, hshort⟩ := actual_original_returning_comparison_has_short_angular_lift
    S genus hgenus hS a b ht u z huz f g hf hfcurve hgcurve hclean hhom
  obtain ⟨g', hg', hgb, hgg'⟩ := embedded_comparison_of_short_angular_lift b.val u z huz g p hp hshort
  exact ⟨g', hg', hgb, hhom.trans hgg'⟩

end CurveComplex.LocalSurgery
