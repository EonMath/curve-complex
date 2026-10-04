import CurveComplexGenusTwo.Topology.CapBandGeometry.BandSideCap

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

abbrev SupSquare (r : ℝ) := Metric.closedBall ((0, 0) : ℝ × ℝ) r

theorem supSquare_top_mem (r x : ℝ) (hr : 0 < r) (hx0 : -r < x) (hx1 : x < r) :
    (x, r) ∈ Metric.closedBall ((0, 0) : ℝ × ℝ) r := by
  simp only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
    Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero, Real.norm_eq_abs,
    max_le_iff, abs_le]
  constructor <;> constructor <;> linarith

/-- A literal embedded half rectangle at any noncorner point of a square side,
small enough to lie in the prescribed open ambient neighborhood. -/
theorem embedded_square_top_half_patch
    {S : Type} [TopologicalSpace S] [T2Space S]
    (r : ℝ) (hr : 0 < r) (E : SupSquare r → S) (hE : IsEmbedding E)
    (x : ℝ) (hx0 : -r < x) (hx1 : x < r)
    (W : Set S) (hW : IsOpen W)
    (hpoint : E ⟨(x, r), supSquare_top_mem r x hr hx0 hx1⟩ ∈ W) :
    ∃ L : BandWidth × I → S, IsEmbedding L ∧
      Set.range L ⊆ Set.range E ∩ W ∧
      L (⟨0, by norm_num⟩, 0) = E ⟨(x, r), supSquare_top_mem r x hr hx0 hx1⟩ ∧
      (∀ p, ∃ z : SupSquare r, E z = L p ∧
        (((z : ℝ × ℝ).2 = r ↔ p.2 = 0) ∧
          ((z : ℝ × ℝ).1 ∈ Ioo (-r) r) ∧
          -r < (z : ℝ × ℝ).2)) := by
  let z : SupSquare r := ⟨(x, r), supSquare_top_mem r x hr hx0 hx1⟩
  obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.mp (hW.preimage hE.continuous) z hpoint
  let δ := min (min (r - |x|) r) η / 2
  have hrx : 0 < r - |x| := by
    have hh : |x| < r := abs_lt.mpr ⟨hx0, hx1⟩
    linarith
  have hd : 0 < δ := div_pos (lt_min (lt_min hrx hr) hη) (by norm_num)
  have hdη : δ ≤ η/2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hdr : δ ≤ r/2 := div_le_div_of_nonneg_right
    ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
  have hdx : δ ≤ (r - |x|)/2 := div_le_div_of_nonneg_right
    ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
  have hcoords (p : BandWidth × I) :
      -r < x + δ*(p.1 : ℝ) ∧ x + δ*(p.1 : ℝ) < r ∧
        -r < r - δ*(p.2 : ℝ) ∧ r - δ*(p.2 : ℝ) ≤ r := by
    have ha0 := neg_abs_le x
    have ha1 := le_abs_self x
    constructor
    · nlinarith [p.1.property.1, p.1.property.2]
    constructor
    · nlinarith [p.1.property.1, p.1.property.2]
    constructor
    · nlinarith [p.2.property.1, p.2.property.2]
    · nlinarith [p.2.property.1]
  let l : BandWidth × I → SupSquare r := fun p =>
    ⟨(x + δ*(p.1 : ℝ), r - δ*(p.2 : ℝ)), by
      have hh := hcoords p
      simp only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
        Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero, Real.norm_eq_abs,
        max_le_iff, abs_le]
      exact ⟨⟨hh.1.le, hh.2.1.le⟩, ⟨hh.2.2.1.le, hh.2.2.2⟩⟩⟩
  have hlc : Continuous l := by fun_prop
  have hli : Function.Injective l := by
    intro p q he
    have hx := congrArg (fun z : SupSquare r => (z : ℝ × ℝ).1) he
    have hy := congrArg (fun z : SupSquare r => (z : ℝ × ℝ).2) he
    apply Prod.ext <;> apply Subtype.ext <;> dsimp [l] at hx hy <;> nlinarith
  let L := E ∘ l
  refine ⟨L, hE.comp (hlc.isClosedEmbedding hli).isEmbedding, ?_, ?_, ?_⟩
  · rintro y ⟨p, rfl⟩
    refine ⟨Set.mem_range_self _, hηball ?_⟩
    change dist (l p) z < η
    change dist (x + δ*(p.1 : ℝ), r - δ*(p.2 : ℝ)) (x, r) < η
    simp only [dist_eq_norm, Prod.norm_def, Prod.fst_sub, Prod.snd_sub,
      Real.norm_eq_abs, max_lt_iff, abs_lt]
    constructor <;> constructor <;> nlinarith [p.1.property.1, p.1.property.2,
      p.2.property.1, p.2.property.2]
  · apply congrArg E
    apply Subtype.ext
    simp [l]
  · intro p
    refine ⟨l p, rfl, ?_, ?_, ?_⟩
    · change r - δ*(p.2 : ℝ) = r ↔ p.2 = 0
      constructor
      · intro h
        apply Subtype.ext
        change (p.2 : ℝ) = 0
        nlinarith
      · intro h
        simp [h]
    · exact ⟨(hcoords p).1, (hcoords p).2.1⟩
    · exact (hcoords p).2.2.1

#print axioms embedded_square_top_half_patch
end CurveComplex.CapBandGeometry

namespace CurveComplex.CapBandGeometry

noncomputable def squareSymmetry (r : ℝ) (i : Fin 4) : SupSquare r ≃ₜ SupSquare r where
  toFun z := ⟨match i with
    | 0 => z.1
    | 1 => (z.1.2, z.1.1)
    | 2 => (z.1.1, -z.1.2)
    | 3 => (-z.1.2, -z.1.1), by
      have hz := z.2
      fin_cases i <;> simp only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def,
        Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero,
        Real.norm_eq_abs, abs_neg] at hz ⊢ <;> first | exact hz | simpa [max_comm] using hz⟩
  invFun z := ⟨match i with
    | 0 => z.1
    | 1 => (z.1.2, z.1.1)
    | 2 => (z.1.1, -z.1.2)
    | 3 => (-z.1.2, -z.1.1), by
      have hz := z.2
      fin_cases i <;> simp only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def,
        Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero,
        Real.norm_eq_abs, abs_neg] at hz ⊢ <;> first | exact hz | simpa [max_comm] using hz⟩
  left_inv z := by fin_cases i <;> apply Subtype.ext <;> simp
  right_inv z := by fin_cases i <;> apply Subtype.ext <;> simp
  continuous_toFun := by fin_cases i <;> fun_prop
  continuous_invFun := by fin_cases i <;> fun_prop

theorem squareSymmetry_ball (r : ℝ) (i : Fin 4) (z : SupSquare r) :
    ((squareSymmetry r i z : SupSquare r) : ℝ × ℝ) ∈ Metric.ball ((0, 0) : ℝ × ℝ) r ↔
      (z : ℝ × ℝ) ∈ Metric.ball ((0, 0) : ℝ × ℝ) r := by
  fin_cases i <;> simp [squareSymmetry, Metric.mem_ball, dist_eq_norm, Prod.norm_def,
    Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero,
    Real.norm_eq_abs, abs_neg, max_comm]

theorem squareSymmetry_sphere (r : ℝ) (i : Fin 4) (z : SupSquare r) :
    ((squareSymmetry r i z : SupSquare r) : ℝ × ℝ) ∈ Metric.sphere ((0, 0) : ℝ × ℝ) r ↔
      (z : ℝ × ℝ) ∈ Metric.sphere ((0, 0) : ℝ × ℝ) r := by
  fin_cases i <;> simp [squareSymmetry, Metric.mem_sphere, dist_eq_norm, Prod.norm_def,
    Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero,
    Real.norm_eq_abs, abs_neg, max_comm]

/-- All noncorner square-boundary points are on one of the four explicit side charts. -/
theorem supSquare_noncorner_side_chart (r : ℝ) (hr : 0 < r) (z : SupSquare r)
    (hz : (z : ℝ × ℝ) ∈ Metric.sphere ((0, 0) : ℝ × ℝ) r)
    (hcorner : ¬ (|(z : ℝ × ℝ).1| = r ∧ |(z : ℝ × ℝ).2| = r)) :
    ∃ i : Fin 4, ∃ x : ℝ, ∃ hx0 : -r < x, ∃ hx1 : x < r,
      squareSymmetry r i ⟨(x, r), supSquare_top_mem r x hr hx0 hx1⟩ = z := by
  have hxy : max |z.1.1| |z.1.2| = r := by
    simpa [Metric.mem_sphere, dist_eq_norm, Prod.norm_def, Real.norm_eq_abs] using hz
  have hxle : |z.1.1| ≤ r := (max_le_iff.mp hxy.le).1
  have hyle : |z.1.2| ≤ r := (max_le_iff.mp hxy.le).2
  have hside : |z.1.1| = r ∨ |z.1.2| = r := (max_eq_iff.mp hxy).imp And.left And.left
  rcases hside with hx | hy
  · have hylt : |z.1.2| < r := lt_of_le_of_ne hyle (fun h => hcorner ⟨hx, h⟩)
    have hy0 := (abs_lt.mp hylt).1
    have hy1 := (abs_lt.mp hylt).2
    rcases (abs_eq (le_of_lt hr)).mp hx with hx | hx
    · refine ⟨1, z.1.2, hy0, hy1, ?_⟩
      apply Subtype.ext
      ext <;> simp [squareSymmetry, hx]
    · refine ⟨3, -z.1.2, by linarith, by linarith, ?_⟩
      apply Subtype.ext
      ext <;> simp [squareSymmetry, hx]
  · have hxlt : |z.1.1| < r := lt_of_le_of_ne hxle (fun h => hcorner ⟨h, hy⟩)
    have hx0 := (abs_lt.mp hxlt).1
    have hx1 := (abs_lt.mp hxlt).2
    rcases (abs_eq (le_of_lt hr)).mp hy with hy | hy
    · refine ⟨0, z.1.1, hx0, hx1, ?_⟩
      apply Subtype.ext
      ext <;> simp [squareSymmetry, hy]
    · refine ⟨2, z.1.1, hx0, hx1, ?_⟩
      apply Subtype.ext
      ext <;> simp [squareSymmetry, hy]

end CurveComplex.CapBandGeometry
