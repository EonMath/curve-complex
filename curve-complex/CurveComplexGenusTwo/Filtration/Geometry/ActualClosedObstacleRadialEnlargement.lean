import CurveComplexGenusTwo.Foundations.Definitions
import Schoenflies.ModelCurve
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section
namespace CurveComplex
open Set Topology Schoenflies Metric Filter
set_option maxHeartbeats 6000000

theorem actual_relative_radial_isotopy : ∀ (h : (ℝ × ℝ) → ℝ) (hc : Continuous h)
    (hp : ∀ z, 0 ≤ h z) (hb : ∀ z, h z ≤ 1/8),
    ∃ H : AmbientIsotopy (ℝ × ℝ),
      (∀ t z, H.map (t,z) =
        ((‖z‖ + max 0 (t.val*h (‖z‖⁻¹ • z)-|‖z‖-1|/2))/‖z‖) • z) ∧
      (∀ t z, h (‖z‖⁻¹ • z) = 0 → H.map (t,z) = z) ∧
      (∀ z, ‖z‖ = 1 → ‖H.finalMap z‖ = 1+h z) := by
  intro h hc hp hb
  have inverse : ∀ (h : (ℝ × ℝ) → ℝ) (hp : ∀ z, 0 ≤ h z) (hb : ∀ z, h z ≤ 1/8),
      let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
      let R := fun z : ℝ × ℝ => ‖z‖ + max 0 (h (d z) - |‖z‖-1|/2)
      let Q := fun z : ℝ × ℝ => ‖z‖ - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))
      let f := fun z : ℝ × ℝ => (R z / ‖z‖) • z
      let g := fun z : ℝ × ℝ => (Q z / ‖z‖) • z
      Function.LeftInverse g f ∧ Function.RightInverse g f := by
    intro h hp hb
    have scalar : ∀ (k r : ℝ) (hk : 0 ≤ k) (hkb : k ≤ 1/8) (hr : 0 ≤ r),
        let f := fun y : ℝ => y + max 0 (k - |y|/2)
        let g := fun y : ℝ => y - max 0 (min ((y+2*k)/3) (2*k-y))
        0 ≤ 1 + f (r-1) ∧ 0 ≤ 1 + g (r-1) ∧
        (1 + f (r-1) = 0 ↔ r = 0) ∧
        (1 + g (r-1) = 0 ↔ r = 0) ∧
        (r ≤ 1/2 → 1 + f (r-1) = r ∧ 1 + g (r-1) = r) ∧
        1 + g (f (r-1)) = r ∧ 1 + f (g (r-1)) = r := by
      intro k r hk hkb hr
      let f : ℝ → ℝ → ℝ := fun k y => y + max 0 (k - |y|/2)
      let g : ℝ → ℝ → ℝ := fun k z => z - max 0 (min ((z+2*k)/3) (2*k-z))
      have left (k : ℝ) (hk : 0 ≤ k) (y : ℝ) : g k (f k y) = y := by
        by_cases hy0 : y ≤ 0
        ·
          by_cases hy : y ≤ -2*k
          · have hf : f k y = y := by
              dsimp [f]
              rw [abs_of_nonpos hy0, max_eq_left (by linarith)]
              ring
            rw [hf]
            dsimp [g]
            have h1 : (y+2*k)/3 ≤ 2*k-y := by linarith
            rw [min_eq_left h1,max_eq_left (by linarith)]
            ring
          · have hf : f k y = 3/2*y+k := by
              dsimp [f]
              rw [abs_of_nonpos hy0,max_eq_right (by linarith)]
              ring
            rw [hf]
            dsimp [g]
            have h1 : ((3/2*y+k)+2*k)/3 ≤ 2*k-(3/2*y+k) := by linarith
            rw [min_eq_left h1,max_eq_right (by linarith)]
            ring
        · have hy0' : 0 ≤ y := (not_le.mp hy0).le
          by_cases hy : 2*k ≤ y
          · have hf : f k y = y := by
              dsimp [f]
              rw [abs_of_nonneg hy0',max_eq_left (by linarith)]
              ring
            rw [hf]
            dsimp [g]
            have h1 : 2*k-y ≤ (y+2*k)/3 := by linarith
            rw [min_eq_right h1,max_eq_left (by linarith)]
            ring
          · have hf : f k y = 1/2*y+k := by
              dsimp [f]
              rw [abs_of_nonneg hy0',max_eq_right (by linarith)]
              ring
            rw [hf]
            dsimp [g]
            have h1 : 2*k-(1/2*y+k) ≤ ((1/2*y+k)+2*k)/3 := by linarith
            rw [min_eq_right h1,max_eq_right (by linarith)]
            ring
      have right (k : ℝ) (hk : 0 ≤ k) (z : ℝ) : f k (g k z) = z := by
        by_cases hz : z ≤ -2*k
        · have hg : g k z = z := by
            dsimp [g]
            rw [min_eq_left (by linarith),max_eq_left (by linarith)]
            ring
          rw [hg]
          dsimp [f]
          rw [abs_of_nonpos (by linarith),max_eq_left (by linarith)]
          ring
        · by_cases hz2 : 2*k ≤ z
          · have hg : g k z = z := by
              dsimp [g]
              rw [min_eq_right (by linarith),max_eq_left (by linarith)]
              ring
            rw [hg]
            dsimp [f]
            rw [abs_of_nonneg (by linarith),max_eq_left (by linarith)]
            ring
          · by_cases hzk : z ≤ k
            · have hg : g k z = 2/3*(z-k) := by
                dsimp [g]
                rw [min_eq_left (by linarith),max_eq_right (by linarith)]
                ring
              rw [hg]
              dsimp [f]
              rw [abs_of_nonpos (by linarith),max_eq_right (by linarith)]
              ring
            · have hg : g k z = 2*(z-k) := by
                dsimp [g]
                rw [min_eq_right (by linarith),max_eq_right (by linarith)]
                ring
              rw [hg]
              dsimp [f]
              rw [abs_of_nonneg (by linarith),max_eq_right (by linarith)]
              ring
      change 0 ≤ 1 + f k (r-1) ∧ 0 ≤ 1 + g k (r-1) ∧ _
      have small (r : ℝ) (hr : r ≤ 1/2) :
          1 + f k (r-1) = r ∧ 1 + g k (r-1) = r := by
        constructor
        · dsimp [f]
          rw [abs_of_nonpos (by linarith),max_eq_left (by linarith)]
          ring
        · dsimp [g]
          rw [min_eq_left (by linarith),max_eq_left (by linarith)]
          ring
      have fp : 0 ≤ 1 + f k (r-1) := by
        dsimp [f]; have := le_max_left 0 (k-|r-1|/2); linarith
      have gp : 0 ≤ 1 + g k (r-1) := by
        by_cases hs : r ≤ 1/2
        · rw [(small r hs).2]; exact hr
        · have hm : max 0 (min ((r-1+2*k)/3) (2*k-(r-1))) ≤ r := by
            apply max_le
            · exact hr
            · exact (min_le_left _ _).trans (by linarith)
          dsimp [g]; linarith
      refine ⟨fp,gp,?_,?_,small r,?_,?_⟩
      · constructor
        · intro he
          dsimp [f] at he
          have := le_max_left 0 (k-|r-1|/2)
          linarith
        · intro he; subst r; exact (small 0 (by norm_num)).1
      · constructor
        · intro he
          by_cases hs : r ≤ 1/2
          · rw [(small r hs).2] at he; exact he
          · have hm : max 0 (min ((r-1+2*k)/3) (2*k-(r-1))) < r := by
              apply max_lt
              · linarith
              · exact (min_le_left _ _).trans_lt (by linarith)
            dsimp [g] at he
            linarith
        · intro he; subst r; exact (small 0 (by norm_num)).2
      · change 1 + g k (f k (r-1)) = r
        rw [left k hk]; ring
      · change 1 + f k (g k (r-1)) = r
        rw [right k hk]; ring
    dsimp only
    let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
    let R := fun z : ℝ × ℝ => ‖z‖ + max 0 (h (d z) - |‖z‖-1|/2)
    let Q := fun z : ℝ × ℝ => ‖z‖ - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))
    let f := fun z : ℝ × ℝ => (R z / ‖z‖) • z
    let g := fun z : ℝ × ℝ => (Q z / ‖z‖) • z
    change Function.LeftInverse g f ∧ Function.RightInverse g f
    have radial (A : (ℝ × ℝ) → ℝ) (z : ℝ × ℝ) (hz : z ≠ 0) (hA : 0 < A z) :
        ‖(A z / ‖z‖) • z‖ = A z ∧ d ((A z / ‖z‖) • z) = d z := by
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hr : 0 ≤ A z / ‖z‖ := (div_pos hA hn).le
      have he : ‖(A z / ‖z‖) • z‖ = A z := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
        field_simp
      refine ⟨he,?_⟩
      dsimp [d]
      rw [he,smul_smul]
      congr 1
      field_simp
    have posR (z : ℝ × ℝ) (hz : z ≠ 0) : 0 < R z := by
      have hs := scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)
      have he : 1 + (‖z‖-1 + max 0 (h (d z)-|‖z‖-1|/2)) = R z := by dsimp [R]; ring
      dsimp only at hs
      rw [he] at hs
      exact lt_of_le_of_ne hs.1 (Ne.symm (fun hh => hz (norm_eq_zero.mp (hs.2.2.1.mp hh))))
    have posQ (z : ℝ × ℝ) (hz : z ≠ 0) : 0 < Q z := by
      have hs := scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)
      have he : 1 + (‖z‖-1 - max 0 (min ((‖z‖-1+2*h (d z))/3) (2*h (d z)-(‖z‖-1)))) = Q z := by dsimp [Q]; ring
      dsimp only at hs
      rw [he] at hs
      exact lt_of_le_of_ne hs.2.1 (Ne.symm (fun hh => hz (norm_eq_zero.mp (hs.2.2.2.1.mp hh))))
    constructor
    · intro z
      by_cases hz : z = 0
      · subst z; simp [f,g]
      have hn := norm_pos_iff.mpr hz
      obtain ⟨hfn,hfd⟩ := radial R z hz (posR z hz)
      have hQ : Q (f z) = ‖z‖ := by
        dsimp [Q]
        rw [hfn]
        change R z - max 0 (min ((R z-1+2*h (d (f z)))/3) (2*h (d (f z))-(R z-1))) = ‖z‖
        rw [hfd]
        have hs := (scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)).2.2.2.2.2.1
        dsimp [R]
        convert hs using 1 <;> ring_nf
      change (Q (f z) / ‖f z‖) • ((R z / ‖z‖) • z) = z
      rw [hQ,hfn,smul_smul]
      have he : (‖z‖/R z)*(R z/‖z‖) = 1 := by field_simp [ne_of_gt hn,ne_of_gt (posR z hz),ne_of_gt (posQ z hz)]
      rw [he,one_smul]
    · intro z
      by_cases hz : z = 0
      · subst z; simp [f,g]
      have hn := norm_pos_iff.mpr hz
      obtain ⟨hgn,hgd⟩ := radial Q z hz (posQ z hz)
      have hR : R (g z) = ‖z‖ := by
        dsimp [R]
        rw [hgn]
        change Q z + max 0 (h (d (g z))-|Q z-1|/2) = ‖z‖
        rw [hgd]
        have hs := (scalar (h (d z)) ‖z‖ (hp _) (hb _) (norm_nonneg _)).2.2.2.2.2.2
        dsimp [Q]
        convert hs using 1 <;> ring_nf
      change (R (g z) / ‖g z‖) • ((Q z / ‖z‖) • z) = z
      rw [hR,hgn,smul_smul]
      have he : (‖z‖/Q z)*(Q z/‖z‖) = 1 := by field_simp [ne_of_gt hn,ne_of_gt (posR z hz),ne_of_gt (posQ z hz)]
      rw [he,one_smul]
  let d := fun z : ℝ × ℝ => ‖z‖⁻¹ • z
  let R := fun z : Interval × (ℝ × ℝ) => ‖z.2‖ + max 0 (z.1.val*h (d z.2)-|‖z.2‖-1|/2)
  let Q := fun z : Interval × (ℝ × ℝ) => ‖z.2‖ - max 0 (min ((‖z.2‖-1+2*(z.1.val*h (d z.2)))/3) (2*(z.1.val*h (d z.2))-(‖z.2‖-1)))
  let f := fun z : Interval × (ℝ × ℝ) => (R z / ‖z.2‖) • z.2
  let g := fun z : Interval × (ℝ × ℝ) => (Q z / ‖z.2‖) • z.2
  have small (z : Interval × (ℝ × ℝ)) (hz : ‖z.2‖ < 1/2) : f z = z.2 ∧ g z = z.2 := by
    have hkp : 0 ≤ z.1.val * h (d z.2) := mul_nonneg z.1.property.1 (hp _)
    have hk : z.1.val * h (d z.2) ≤ 1/8 := (mul_le_of_le_one_left (hp _) z.1.property.2).trans (hb _)
    have hR : R z = ‖z.2‖ := by
      dsimp [R]
      rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
      ring
    have hQ : Q z = ‖z.2‖ := by
      dsimp [Q]
      rw [min_eq_left (by linarith),max_eq_left (by linarith)]
      ring
    by_cases he : z.2 = 0
    · simp [f,g,he]
    · have hn : ‖z.2‖ ≠ 0 := norm_ne_zero_iff.mpr he
      simp [f,g,hR,hQ,hn]
  have cont : Continuous f ∧ Continuous g := by
    constructor <;> rw [continuous_iff_continuousAt] <;> intro z
    · by_cases hz : z.2 = 0
      · have hh : ∀ᶠ w in 𝓝 z, ‖w.2‖ < 1/2 :=
          (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds (by simp [hz]))
        apply continuous_snd.continuousAt.congr_of_eventuallyEq
        filter_upwards [hh] with w hw
        exact (small w hw).1
      · dsimp [f,R,d]
        fun_prop (disch := exact norm_ne_zero_iff.mpr hz)
    · by_cases hz : z.2 = 0
      · have hh : ∀ᶠ w in 𝓝 z, ‖w.2‖ < 1/2 :=
          (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds (by simp [hz]))
        apply continuous_snd.continuousAt.congr_of_eventuallyEq
        filter_upwards [hh] with w hw
        exact (small w hw).2
      · dsimp [g,Q,d]
        fun_prop (disch := exact norm_ne_zero_iff.mpr hz)
  let e : Interval → (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := fun t => {
    toEquiv := {
      toFun := fun z => f (t,z)
      invFun := fun z => g (t,z)
      left_inv := (inverse (fun z => t.val*h z)
        (fun z => mul_nonneg t.property.1 (hp z))
        (fun z => (mul_le_of_le_one_left (hp z) t.property.2).trans (hb z))).1
      right_inv := (inverse (fun z => t.val*h z)
        (fun z => mul_nonneg t.property.1 (hp z))
        (fun z => (mul_le_of_le_one_left (hp z) t.property.2).trans (hb z))).2 }
    continuous_toFun := cont.1.comp (continuous_const.prodMk continuous_id)
    continuous_invFun := cont.2.comp (continuous_const.prodMk continuous_id) }
  let H : AmbientIsotopy (ℝ × ℝ) := {
    map := ⟨f,cont.1⟩
    homeomorphism_at := fun t => ⟨e t,fun z => rfl⟩
    at_zero := by
      intro z
      by_cases hz : z = 0
      · simp [f,hz]
      · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
        change ((‖z‖+max 0 (0*h (d z)-|‖z‖-1|/2))/‖z‖) • z = z
        rw [zero_mul,zero_sub,max_eq_left (neg_nonpos.mpr (div_nonneg (abs_nonneg _) (by norm_num))),add_zero,div_self hn,one_smul] }
  refine ⟨H,fun t z => rfl,?_,?_⟩
  · intro t z hz
    by_cases he : z = 0
    · simp [H,f,he]
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
      change ((‖z‖+max 0 (t.val*h (d z)-|‖z‖-1|/2))/‖z‖) • z = z
      rw [hz,mul_zero,zero_sub,max_eq_left (neg_nonpos.mpr (div_nonneg (abs_nonneg _) (by norm_num))),add_zero,div_self hn,one_smul]
  · intro z hz
    change ‖((‖z‖+max 0 (1*h (d z)-|‖z‖-1|/2))/‖z‖) • z‖ = _
    simp [d,hz,norm_smul,Real.norm_eq_abs,max_eq_right (hp z),abs_of_nonneg (by linarith [hp z] : 0 ≤ 1+h z)]

/-- A closed obstacle may touch the circle at its prescribed endpoints. The
outward enlargement fixes that obstacle pointwise and places every other old
boundary point INSIDE the enlarged disk, not merely off the old boundary. -/
theorem actual_closed_obstacle_radial_enlargement
    (F : Set (ℝ × ℝ)) (hF : IsClosed F) (hne : F.Nonempty)
    (hinside : Disjoint {z : ℝ × ℝ | ‖z‖ < 1} F) :
    ∃ H : AmbientIsotopy (ℝ × ℝ),
      (∀ t z, z ∈ F → H.map (t, z) = z) ∧
      {z : ℝ × ℝ | ‖z‖ = 1} \ F ⊆ H.finalMap '' {z : ℝ × ℝ | ‖z‖ < 1} ∧
      Disjoint (H.finalMap '' {z : ℝ × ℝ | ‖z‖ < 1}) F := by
  let h : (ℝ × ℝ) → ℝ := fun z => min (1/8) (infDist z F/8)
  have hc : Continuous h := continuous_const.min ((Metric.continuous_infDist_pt F).div_const 8)
  have hp : ∀ z, 0 ≤ h z := fun z => le_min (by norm_num) (div_nonneg infDist_nonneg (by norm_num))
  have hb : ∀ z, h z ≤ 1/8 := fun z => min_le_left _ _
  obtain ⟨H,hmap,hzero,hnorm⟩ := actual_relative_radial_isotopy h hc hp hb
  have distdir (z : ℝ × ℝ) (hz : z ≠ 0) : dist (‖z‖⁻¹ • z) z = |‖z‖-1| := by
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hd : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      exact inv_mul_cancel₀ hn
    have he : (‖z‖ : ℝ) • (‖z‖⁻¹ • z) = z := by rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
    calc
      dist (‖z‖⁻¹ • z) z = ‖(1-‖z‖) • (‖z‖⁻¹ • z)‖ := by rw [dist_eq_norm,sub_smul,one_smul,he]
      _ = |‖z‖-1| := by rw [norm_smul,Real.norm_eq_abs,hd,mul_one,abs_sub_comm]
  have fix : ∀ t z, z ∈ F → H.map (t,z) = z := by
    intro t z hz
    by_cases he : z = 0
    · subst z; rw [hmap]; simp
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr he
    have hi : infDist (‖z‖⁻¹ • z) F ≤ |‖z‖-1| := by
      rw [←distdir z he]
      exact infDist_le_dist_of_mem hz
    have hh : h (‖z‖⁻¹ • z) ≤ |‖z‖-1|/8 := (min_le_right _ _).trans (div_le_div_of_nonneg_right hi (by norm_num))
    have ht : t.val*h (‖z‖⁻¹ • z) ≤ h (‖z‖⁻¹ • z) := mul_le_of_le_one_left (hp _) t.property.2
    rw [hmap,max_eq_left (by have := abs_nonneg (‖z‖-1); linarith),add_zero,div_self hn,one_smul]
  have hnormlower (z : ℝ × ℝ) : ‖z‖ ≤ ‖H.finalMap z‖ := by
    by_cases hz : z = 0
    · subst z
      simpa using norm_nonneg (H.finalMap (0 : ℝ × ℝ))
    · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      let R := ‖z‖ + max 0 (h (‖z‖⁻¹ • z) - |‖z‖-1|/2)
      have hR : 0 ≤ R := add_nonneg (norm_nonneg _) (le_max_left _ _)
      have he : ‖H.finalMap z‖ = R := by
        rw [show H.finalMap z = ((R / ‖z‖) : ℝ) • z from by
          rw [AmbientIsotopy.finalMap, hmap]
          change ((‖z‖ + max 0 (1 * h (‖z‖⁻¹ • z) - |‖z‖ - 1| / 2)) / ‖z‖) • z = _
          simp only [one_mul]
          rfl]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR hn.le)]
        exact div_mul_cancel₀ _ (ne_of_gt hn)
      rw [he]
      exact le_add_of_nonneg_right (le_max_left _ _)
  obtain ⟨g, hg⟩ := H.homeomorphism_at (1 : Interval)
  have hgfinal (z : ℝ × ℝ) : g z = H.finalMap z := hg z
  have hboundary : {z : ℝ × ℝ | ‖z‖ = 1} \ F ⊆
      H.finalMap '' {z : ℝ × ℝ | ‖z‖ < 1} := by
    intro z hz
    let w := g.symm z
    have hwz : H.finalMap w = z := (hgfinal w).symm.trans (g.apply_symm_apply z)
    have hwnot : w ∉ F := by
      intro hw
      have he : H.finalMap w = w := fix 1 w hw
      exact hz.2 (hwz ▸ (he.symm ▸ hw))
    have hzNorm : ‖z‖ = 1 := hz.1
    have hle : ‖w‖ ≤ 1 := by simpa only [hwz, hzNorm] using hnormlower w
    have hlt : ‖w‖ < 1 := by
      by_contra hh
      have hweq : ‖w‖ = 1 := le_antisymm hle (not_lt.mp hh)
      have hpw : 0 < h w := by
        apply lt_min (by norm_num)
        exact div_pos ((hF.notMem_iff_infDist_pos hne).mp hwnot) (by norm_num)
      have he := hnorm w hweq
      rw [hwz, hzNorm] at he
      linarith
    exact ⟨w, hlt, hwz⟩
  have hfree : Disjoint (H.finalMap '' {z : ℝ × ℝ | ‖z‖ < 1}) F := by
    apply Set.disjoint_left.mpr
    rintro z ⟨w, hw, hwz⟩ hzF
    have he : g w = g z := by
      rw [hgfinal, hgfinal]
      change H.map (1, w) = H.map (1, z)
      rw [fix 1 z hzF]
      exact hwz
    have hew : w = z := g.injective he
    exact Set.disjoint_left.mp hinside hw (hew.symm ▸ hzF)
  exact ⟨H, fix, hboundary, hfree⟩

#print axioms actual_relative_radial_isotopy
#print axioms actual_closed_obstacle_radial_enlargement

end CurveComplex
