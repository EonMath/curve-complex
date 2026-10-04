import Mathlib
namespace CurveComplex.LocalSurgery

/-- Two local charts straightening the same curve have a constant relative
side label near a point of the curve. This is the transition needed both for
cut-cover gluing and for comparing its local chart with a crossing chart. -/
theorem local_axis_transition_side_constant
    (h : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ))
    (hsource : (0, 0) ∈ h.source) (hzero : h (0, 0) = (0, 0))
    (haxis : ∀ x ∈ h.source, x.1 = 0 ↔ (h x).1 = 0) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0, 0) r ⊆ h.source ∧
      ∃ ε : ZMod 2, ∀ x ∈ Metric.ball (0, 0) r, x.1 ≠ 0 →
        (if 0 < (h x).1 then (1 : ZMod 2) else 0) =
          (if 0 < x.1 then (1 : ZMod 2) else 0) + ε := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp h.open_source (0, 0) hsource
  let B := Metric.ball ((0, 0) : ℝ × ℝ) r
  have hfcont : ContinuousOn (fun x : ℝ × ℝ => (h x).1) B :=
    continuous_fst.comp_continuousOn (h.continuousOn.mono hball)
  have hnonzero (x : ℝ × ℝ) (hx : x ∈ B) (hx0 : x.1 ≠ 0) : (h x).1 ≠ 0 :=
    fun hz => hx0 ((haxis x (hball hx)).mpr hz)
  have hside (positive : Bool) :
      IsPreconnected (B ∩ {x : ℝ × ℝ | if positive then 0 < x.1 else x.1 < 0}) := by
    apply Convex.isPreconnected
    apply (convex_ball (0, 0) r).inter
    have hfst : IsLinearMap ℝ (fun x : ℝ × ℝ => x.1) :=
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    cases positive
    · exact convex_halfSpace_lt hfst 0
    · exact convex_halfSpace_gt hfst 0
  have hsign (positive : Bool) (x y : ℝ × ℝ)
      (hx : x ∈ B ∩ {x : ℝ × ℝ | if positive then 0 < x.1 else x.1 < 0})
      (hy : y ∈ B ∩ {x : ℝ × ℝ | if positive then 0 < x.1 else x.1 < 0}) :
      (0 < (h x).1 ↔ 0 < (h y).1) := by
    have hx0 : x.1 ≠ 0 := by cases positive <;> simp_all [B] <;> linarith
    have hy0 : y.1 ≠ 0 := by cases positive <;> simp_all [B] <;> linarith
    have hxout := hnonzero x hx.1 hx0
    have hyout := hnonzero y hy.1 hy0
    have hnoCross (u v : ℝ × ℝ)
        (hu : u ∈ B ∩ {x : ℝ × ℝ | if positive then 0 < x.1 else x.1 < 0})
        (hv : v ∈ B ∩ {x : ℝ × ℝ | if positive then 0 < x.1 else x.1 < 0})
        (huout : (h u).1 < 0) (hvout : 0 < (h v).1) : False := by
      obtain ⟨z, hz, hz0⟩ := (hside positive).intermediate_value hu hv
        (hfcont.mono Set.inter_subset_left) ⟨huout.le, hvout.le⟩
      have hzin : z.1 = 0 := (haxis z (hball hz.1)).mpr hz0
      cases positive <;> simp_all
    constructor <;> intro hp <;> by_contra hn
    · exact hnoCross y x hy hx (lt_of_le_of_ne (le_of_not_gt hn) hyout) hp
    · exact hnoCross x y hx hy (lt_of_le_of_ne (le_of_not_gt hn) hxout) hp
  have hopen : IsOpen (h '' B) :=
    h.isOpen_image_of_subset_source Metric.isOpen_ball hball
  have hzeroB : (0, 0) ∈ h '' B := by
    refine ⟨(0, 0), Metric.mem_ball_self hr, hzero⟩
  obtain ⟨s, hs, hsball⟩ := Metric.isOpen_iff.mp hopen (0, 0) hzeroB
  have hposB : ((s / 2, 0) : ℝ × ℝ) ∈ Metric.ball (0, 0) s := by
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, abs_zero]
    rw [abs_of_pos (by linarith : 0 < s / 2), max_eq_left (by linarith)]
    linarith
  have hnegB : ((-s / 2, 0) : ℝ × ℝ) ∈ Metric.ball (0, 0) s := by
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, abs_zero]
    rw [abs_of_neg (by linarith : -s / 2 < 0), max_eq_left (by linarith)]
    linarith
  obtain ⟨u, hu, huout⟩ := hsball hposB
  obtain ⟨v, hv, hvout⟩ := hsball hnegB
  have hu0 : u.1 ≠ 0 := by
    intro hz
    have := (haxis u (hball hu)).mp hz
    rw [huout] at this
    change s / 2 = 0 at this
    linarith
  have hv0 : v.1 ≠ 0 := by
    intro hz
    have := (haxis v (hball hv)).mp hz
    rw [hvout] at this
    change -s / 2 = 0 at this
    linarith
  have hup : 0 < (h u).1 := by rw [huout]; change 0 < s / 2; linarith
  have hvn : ¬0 < (h v).1 := by rw [hvout]; change ¬0 < -s / 2; linarith
  have hopposite : (0 < u.1 ↔ v.1 < 0) := by
    constructor
    · intro hp
      by_contra hn
      have hvp : 0 < v.1 := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hv0)
      exact hvn ((hsign true u v ⟨hu, hp⟩ ⟨hv, hvp⟩).mp hup)
    · intro hn
      by_contra hp
      have hun : u.1 < 0 := lt_of_le_of_ne (le_of_not_gt hp) hu0
      exact hvn ((hsign false u v ⟨hu, hun⟩ ⟨hv, hn⟩).mp hup)
  refine ⟨r, hr, hball, ?_⟩
  by_cases hupin : 0 < u.1
  · refine ⟨0, ?_⟩
    intro x hx hx0
    by_cases hxp : 0 < x.1
    · have hout := (hsign true u x ⟨hu, hupin⟩ ⟨hx, hxp⟩).mp hup
      simp [hout, hxp]
    · have hxn : x.1 < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx0
      have hout : ¬0 < (h x).1 := fun hp => hvn
        ((hsign false x v ⟨hx, hxn⟩ ⟨hv, hopposite.mp hupin⟩).mp hp)
      simp [hout, hxp]
  · refine ⟨1, ?_⟩
    intro x hx hx0
    have hun : u.1 < 0 := lt_of_le_of_ne (le_of_not_gt hupin) hu0
    have hvp : 0 < v.1 := by
      by_contra hn
      exact hupin (hopposite.mpr (lt_of_le_of_ne (le_of_not_gt hn) hv0))
    by_cases hxp : 0 < x.1
    · have hout : ¬0 < (h x).1 := fun hp => hvn
        ((hsign true x v ⟨hx, hxp⟩ ⟨hv, hvp⟩).mp hp)
      simp only [if_neg hout, if_pos hxp]
      decide
    · have hxn : x.1 < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx0
      have hout := (hsign false u x ⟨hu, hun⟩ ⟨hx, hxn⟩).mp hup
      simp [hout, hxp]

end CurveComplex.LocalSurgery
