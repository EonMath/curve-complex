import CurveComplexGenusTwo.Hyperbolic.SixSideSymmetryWave11
import CurveComplexGenusTwo.Hyperbolic.IdealHexagonInteriorWave10

namespace CurveComplex.Hyperbolic.IdealHexagonDouble

open CurveComplex.Hyperbolic

noncomputable def idealHexagonDiscClosed : Set ℂ :=
  {w | w ∈ Metric.ball (0 : ℂ) 1 ∧
    ∀ j : Fin 6, 0 ≤ idealHexagonSideEquation j w}

noncomputable def idealHexagonCayleyClosed : Set H2 :=
  {z | (cayley z : ℂ) ∈ idealHexagonDiscClosed}

private theorem firstIdealVertex_mul_conj :
    star (idealHexagonVertex 1) * idealHexagonVertex 1 = 1 := by
  have hnorm : ‖idealHexagonVertex 1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using
      idealHexagonVertex_mem_circle 1
  simpa [Complex.star_def, hnorm] using
    (RCLike.conj_mul (idealHexagonVertex 1))

theorem sideCenter_rotate_next (j : Fin 6) :
    idealHexagonVertex 1 * idealHexagonSideCenter j =
      idealHexagonSideCenter (j + 1) := by
  have hleft : idealHexagonVertex 1 * idealHexagonVertex j =
      idealHexagonVertex (j + 1) := by
    simpa [mul_comm] using idealVertex_rotate_next j
  have hright : idealHexagonVertex 1 * idealHexagonVertex (j + 1) =
      idealHexagonVertex ((j + 1) + 1) := by
    simpa [mul_comm] using idealVertex_rotate_next (j + 1)
  calc
    idealHexagonVertex 1 * idealHexagonSideCenter j =
        (2 / 3 : ℂ) *
          (idealHexagonVertex 1 * idealHexagonVertex j +
            idealHexagonVertex 1 * idealHexagonVertex (j + 1)) := by
              simp only [idealHexagonSideCenter]
              push_cast
              ring
    _ = idealHexagonSideCenter (j + 1) := by
      rw [hleft, hright]
      simp [idealHexagonSideCenter]

theorem sideEquation_rotate_next (j : Fin 6) (w : ℂ) :
    idealHexagonSideEquation (j + 1) (idealHexagonVertex 1 * w) =
      idealHexagonSideEquation j w := by
  simp only [idealHexagonSideEquation]
  rw [← sideCenter_rotate_next j]
  rw [Complex.normSq_mul, idealHexagonVertex_normSq]
  simp only [one_mul, star_mul']
  have hmul : star (idealHexagonVertex 1) * star (idealHexagonSideCenter j) *
      (idealHexagonVertex 1 * w) = star (idealHexagonSideCenter j) * w := by
    calc
      star (idealHexagonVertex 1) * star (idealHexagonSideCenter j) *
          (idealHexagonVertex 1 * w) =
          (star (idealHexagonVertex 1) * idealHexagonVertex 1) *
            (star (idealHexagonSideCenter j) * w) := by ring
      _ = star (idealHexagonSideCenter j) * w := by
        rw [firstIdealVertex_mul_conj]
        ring
  rw [hmul]

theorem discClosed_rotation_next (w : ℂ) :
    w ∈ idealHexagonDiscClosed ↔
      idealHexagonVertex 1 * w ∈ idealHexagonDiscClosed := by
  constructor
  · rintro ⟨hw, hs⟩
    constructor
    · have hn : ‖idealHexagonVertex 1‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using
          idealHexagonVertex_mem_circle 1
      simpa [Metric.mem_ball, dist_zero_right, norm_mul, hn] using hw
    · intro j
      have h := hs (j - 1)
      have hidx : (j - 1) + 1 = j := by fin_cases j <;> decide
      rw [← hidx, sideEquation_rotate_next]
      exact h
  · rintro ⟨hw, hs⟩
    constructor
    · have hn : ‖idealHexagonVertex 1‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using
          idealHexagonVertex_mem_circle 1
      simpa [Metric.mem_ball, dist_zero_right, norm_mul, hn] using hw
    · intro j
      have h := hs (j + 1)
      rw [sideEquation_rotate_next] at h
      exact h

theorem idealVertex_mul (i j : Fin 6) :
    idealHexagonVertex i * idealHexagonVertex j =
      idealHexagonVertex (i + j) := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [idealHexagonVertex, Complex.mul_re, Complex.mul_im] <;>
    nlinarith [hs]

theorem sideCenter_rotate (i j : Fin 6) :
    idealHexagonVertex i * idealHexagonSideCenter j =
      idealHexagonSideCenter (i + j) := by
  calc
    idealHexagonVertex i * idealHexagonSideCenter j =
      (2 / 3 : ℂ) *
        (idealHexagonVertex i * idealHexagonVertex j +
          idealHexagonVertex i * idealHexagonVertex (j + 1)) := by
            simp only [idealHexagonSideCenter]
            push_cast
            ring
    _ = idealHexagonSideCenter (i + j) := by
      rw [idealVertex_mul, idealVertex_mul]
      simp [idealHexagonSideCenter, add_assoc]

theorem sideEquation_rotate (i j : Fin 6) (w : ℂ) :
    idealHexagonSideEquation (i + j) (idealHexagonVertex i * w) =
      idealHexagonSideEquation j w := by
  simp only [idealHexagonSideEquation]
  rw [← sideCenter_rotate i j]
  rw [Complex.normSq_mul, idealHexagonVertex_normSq]
  simp only [one_mul, star_mul']
  have hunit : star (idealHexagonVertex i) * idealHexagonVertex i = 1 := by
    have hnorm : ‖idealHexagonVertex i‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using
        idealHexagonVertex_mem_circle i
    simpa [Complex.star_def, hnorm] using
      (RCLike.conj_mul (idealHexagonVertex i))
  have hmul : star (idealHexagonVertex i) * star (idealHexagonSideCenter j) *
      (idealHexagonVertex i * w) = star (idealHexagonSideCenter j) * w := by
    calc
      star (idealHexagonVertex i) * star (idealHexagonSideCenter j) *
          (idealHexagonVertex i * w) =
          (star (idealHexagonVertex i) * idealHexagonVertex i) *
            (star (idealHexagonSideCenter j) * w) := by ring
      _ = star (idealHexagonSideCenter j) * w := by rw [hunit]; ring
  rw [hmul]

theorem discClosed_rotation (i : Fin 6) (w : ℂ) :
    w ∈ idealHexagonDiscClosed ↔
      idealHexagonVertex i * w ∈ idealHexagonDiscClosed := by
  constructor
  · rintro ⟨hw, hs⟩
    constructor
    · have hn : ‖idealHexagonVertex i‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using
          idealHexagonVertex_mem_circle i
      simpa [Metric.mem_ball, dist_zero_right, norm_mul, hn] using hw
    · intro j
      have h := hs (j - i)
      have hidx : i + (j - i) = j := by
        fin_cases i <;> fin_cases j <;> decide
      rw [← hidx, sideEquation_rotate]
      exact h
  · rintro ⟨hw, hs⟩
    constructor
    · have hn : ‖idealHexagonVertex i‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using
          idealHexagonVertex_mem_circle i
      simpa [Metric.mem_ball, dist_zero_right, norm_mul, hn] using hw
    · intro j
      have h := hs (i + j)
      rw [sideEquation_rotate] at h
      exact h

theorem cayleyClosed_rotation (i : Fin 6) (z : H2) :
    z ∈ idealHexagonCayleyClosed ↔
      h2Rotation i z ∈ idealHexagonCayleyClosed := by
  change (cayley z : ℂ) ∈ idealHexagonDiscClosed ↔
    (cayley (h2Rotation i z) : ℂ) ∈ idealHexagonDiscClosed
  rw [h2Rotation_cayley]
  exact discClosed_rotation i (cayley z : ℂ)

theorem cayleyClosed_rotation_image (i : Fin 6) :
    h2Rotation i '' idealHexagonCayleyClosed =
      idealHexagonCayleyClosed := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (cayleyClosed_rotation i w).1 hw
  · intro hz
    refine ⟨(h2RotationIso i).symm z, ?_, ?_⟩
    · apply (cayleyClosed_rotation i _).2
      have heq : h2Rotation i ((h2RotationIso i).symm z) = z :=
        (h2RotationIso i).apply_symm_apply z
      rw [heq]
      exact hz
    · exact (h2RotationIso i).apply_symm_apply z

end CurveComplex.Hyperbolic.IdealHexagonDouble
