import CurveComplexGenusTwo.Hyperbolic.HexagonEdges

namespace CurveComplex.Hyperbolic

private theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num

theorem regularHexagonRadiusSq_pos : 0 < 2 - Real.sqrt 3 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]

theorem regularHexagonRadiusSq_lt_one : 2 - Real.sqrt 3 < 1 := by
  nlinarith [sqrt_three_sq, sqrt_three_pos]

theorem regularHexagonRadiusSq_relation :
    (1 - (2 - Real.sqrt 3)) ^ 2 = 2 * (2 - Real.sqrt 3) := by
  nlinarith [sqrt_three_sq]

/-- The six sixth roots of unity, expressed without trigonometric functions. -/
noncomputable def idealHexagonVertex : Fin 6 → ℂ
  | 0 => 1
  | 1 => ⟨1 / 2, Real.sqrt 3 / 2⟩
  | 2 => ⟨-1 / 2, Real.sqrt 3 / 2⟩
  | 3 => -1
  | 4 => ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩
  | 5 => ⟨1 / 2, -(Real.sqrt 3 / 2)⟩

theorem idealHexagonVertex_normSq (i : Fin 6) :
    Complex.normSq (idealHexagonVertex i) = 1 := by
  fin_cases i <;> simp [idealHexagonVertex, Complex.normSq_apply] <;>
    nlinarith [sqrt_three_sq]

theorem idealHexagonVertex_mem_circle (i : Fin 6) :
    idealHexagonVertex i ∈ Metric.sphere (0 : ℂ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right, Complex.norm_def]
  rw [idealHexagonVertex_normSq]
  norm_num

noncomputable def idealHexagonCircleVertex (i : Fin 6) : Circle :=
  ⟨idealHexagonVertex i, idealHexagonVertex_mem_circle i⟩

theorem idealHexagonVertex_injective : Function.Injective idealHexagonVertex := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [idealHexagonVertex, Complex.ext_iff] <;>
    nlinarith [sqrt_three_pos]

theorem idealHexagonCircleVertex_injective :
    Function.Injective idealHexagonCircleVertex := by
  intro i j h
  exact idealHexagonVertex_injective (congrArg Subtype.val h)

noncomputable def regularHexagonRadius : ℝ := Real.sqrt (2 - Real.sqrt 3)

theorem regularHexagonRadius_pos : 0 < regularHexagonRadius :=
  Real.sqrt_pos.2 regularHexagonRadiusSq_pos

theorem regularHexagonRadius_lt_one : regularHexagonRadius < 1 := by
  rw [regularHexagonRadius]
  nlinarith [Real.sq_sqrt regularHexagonRadiusSq_pos.le,
    Real.sqrt_nonneg (2 - Real.sqrt 3), regularHexagonRadiusSq_lt_one]

theorem regularHexagonRadius_sq :
    regularHexagonRadius ^ 2 = 2 - Real.sqrt 3 :=
  Real.sq_sqrt regularHexagonRadiusSq_pos.le

noncomputable def regularHexagonDiscPoint (i : Fin 6) : ℂ :=
  regularHexagonRadius * idealHexagonVertex i

theorem regularHexagonDiscPoint_norm (i : Fin 6) :
    ‖regularHexagonDiscPoint i‖ = regularHexagonRadius := by
  rw [regularHexagonDiscPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos regularHexagonRadius_pos]
  have h : ‖idealHexagonVertex i‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using idealHexagonVertex_mem_circle i
  simp [h]

theorem regularHexagonDiscPoint_mem_ball (i : Fin 6) :
    regularHexagonDiscPoint i ∈ Metric.ball (0 : ℂ) 1 := by
  simpa [Metric.mem_ball, dist_zero_right, regularHexagonDiscPoint_norm] using
    regularHexagonRadius_lt_one

noncomputable def regularHexagonH2Point (i : Fin 6) : H2 :=
  cayleyInverse ⟨regularHexagonDiscPoint i, regularHexagonDiscPoint_mem_ball i⟩

theorem regularHexagonH2Point_injective :
    Function.Injective regularHexagonH2Point := by
  intro i j h
  have hc := congrArg (fun z : H2 => (cayley z : ℂ)) h
  simp only [regularHexagonH2Point, cayley_cayleyInverse] at hc
  have hr : (regularHexagonRadius : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr regularHexagonRadius_pos.ne'
  apply idealHexagonVertex_injective
  exact (mul_left_cancel₀ hr) hc

noncomputable def regularHexagonCandidate : Hexagon where
  vertex := regularHexagonH2Point
  injective := regularHexagonH2Point_injective

theorem idealHexagon_adjacent_chord_normSq (i : Fin 6) :
    Complex.normSq (idealHexagonVertex i - idealHexagonVertex (i + 1)) = 1 := by
  fin_cases i <;> simp [idealHexagonVertex, Complex.normSq_apply] <;>
    nlinarith [sqrt_three_sq]

theorem idealHexagon_adjacent_inner_re (i : Fin 6) :
    (star (idealHexagonVertex i) * idealHexagonVertex (i + 1)).re = 1 / 2 := by
  fin_cases i <;>
    simp [idealHexagonVertex, Complex.mul_re, Complex.conj_re, Complex.conj_im] <;>
    nlinarith [sqrt_three_sq]

private theorem normSq_one_sub_star_mul (z w : ℂ) :
    Complex.normSq (1 - star z * w) =
      1 + Complex.normSq z * Complex.normSq w - 2 * (star z * w).re := by
  rw [Complex.normSq_sub]
  simp [Complex.normSq_mul, Complex.normSq_conj]

theorem regularHexagon_adjacent_chord_normSq (i : Fin 6) :
    Complex.normSq (regularHexagonDiscPoint i - regularHexagonDiscPoint (i + 1)) =
      regularHexagonRadius ^ 2 := by
  rw [regularHexagonDiscPoint, regularHexagonDiscPoint, ← mul_sub,
    Complex.normSq_mul, idealHexagon_adjacent_chord_normSq]
  simp [Complex.normSq_ofReal, pow_two]

theorem regularHexagon_adjacent_inner_re (i : Fin 6) :
    (star (regularHexagonDiscPoint i) *
      regularHexagonDiscPoint (i + 1)).re = regularHexagonRadius ^ 2 / 2 := by
  simp only [regularHexagonDiscPoint, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  have heq : (↑regularHexagonRadius : ℂ) *
      (starRingEnd ℂ) (idealHexagonVertex i) *
      (↑regularHexagonRadius * idealHexagonVertex (i + 1)) =
      (↑(regularHexagonRadius ^ 2) : ℂ) *
      ((starRingEnd ℂ) (idealHexagonVertex i) * idealHexagonVertex (i + 1)) := by
    push_cast
    ring
  rw [heq]
  have hi := idealHexagon_adjacent_inner_re i
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] at hi ⊢
  simp only [Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at *
  rw [hi]
  ring

theorem regularHexagon_adjacent_denominator_normSq (i : Fin 6) :
    Complex.normSq (1 - star (regularHexagonDiscPoint i) *
      regularHexagonDiscPoint (i + 1)) =
      1 - regularHexagonRadius ^ 2 + regularHexagonRadius ^ 4 := by
  rw [normSq_one_sub_star_mul, regularHexagon_adjacent_inner_re]
  have hi (j : Fin 6) : Complex.normSq (regularHexagonDiscPoint j) =
      regularHexagonRadius ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, regularHexagonDiscPoint_norm]
  rw [hi, hi]
  ring

theorem regularHexagon_adjacent_chord_norm (i : Fin 6) :
    ‖regularHexagonDiscPoint i - regularHexagonDiscPoint (i + 1)‖ =
      regularHexagonRadius := by
  rw [Complex.norm_def, regularHexagon_adjacent_chord_normSq]
  simp [regularHexagonRadius_pos.le]

theorem Hexagon.edge_nonempty (P : Hexagon) (i : Fin 6) :
    (P.edge i).Nonempty := ⟨P.vertex i, P.left_mem_edge i⟩

theorem Hexagon.edge_isClosed (P : Hexagon) (i : Fin 6) :
    IsClosed (P.edge i) := by
  let f : H2 → ℝ := fun z =>
    dist (P.vertex i) z + dist z (P.vertex (i + 1))
  change IsClosed {z | f z = dist (P.vertex i) (P.vertex (i + 1))}
  exact isClosed_eq (continuous_const.dist continuous_id |>.add
    (continuous_id.dist continuous_const)) continuous_const

theorem Hexagon.edge_subset_closedBall (P : Hexagon) (i : Fin 6) :
    P.edge i ⊆ Metric.closedBall (P.vertex i)
      (dist (P.vertex i) (P.vertex (i + 1))) := by
  intro z hz
  rw [Metric.mem_closedBall]
  rw [dist_comm z (P.vertex i)]
  have h := hz
  change dist (P.vertex i) z + dist z (P.vertex (i + 1)) =
    dist (P.vertex i) (P.vertex (i + 1)) at h
  linarith [dist_nonneg (x := z) (y := P.vertex (i + 1))]

theorem Hexagon.edge_isCompact (P : Hexagon) (i : Fin 6) :
    IsCompact (P.edge i) := by
  exact (isCompact_closedBall (P.vertex i)
    (dist (P.vertex i) (P.vertex (i + 1)))).of_isClosed_subset
      (P.edge_isClosed i) (P.edge_subset_closedBall i)

theorem Hexagon.edges_isClosed (P : Hexagon) :
    IsClosed (⋃ i : Fin 6, P.edge i) := by
  exact isClosed_iUnion_of_finite (fun i => P.edge_isClosed i)

theorem Hexagon.edges_isCompact (P : Hexagon) :
    IsCompact (⋃ i : Fin 6, P.edge i) := by
  exact isCompact_iUnion (fun i => P.edge_isCompact i)

theorem Hexagon.edges_nonempty (P : Hexagon) :
    (⋃ i : Fin 6, P.edge i).Nonempty := by
  refine ⟨P.vertex 0, Set.mem_iUnion.mpr ?_⟩
  exact ⟨0, P.left_mem_edge 0⟩

end CurveComplex.Hyperbolic
