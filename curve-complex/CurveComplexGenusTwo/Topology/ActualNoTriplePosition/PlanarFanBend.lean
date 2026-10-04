import CurveComplexGenusTwo.Topology.Smoothing.GraphShear

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Schoenflies
noncomputable section

def bendHeight (a b x : ℝ) : ℝ := max 0 (min 1 ((b - |x|) / (b - a)))

private theorem bendHeight_nonneg (a b x : ℝ) : 0 ≤ bendHeight a b x := by
  simp [bendHeight]

private theorem bendHeight_le_one (a b x : ℝ) : bendHeight a b x ≤ 1 := by
  simp only [bendHeight, max_le_iff, min_le_iff]
  exact ⟨zero_le_one, Or.inl le_rfl⟩

theorem bendHeight_middle {a b x : ℝ} (hab : a < b) (hx : |x| ≤ a) :
    bendHeight a b x = 1 := by
  have h : 1 ≤ (b - |x|) / (b-a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    nlinarith
  simp only [bendHeight, min_eq_left h, max_eq_right zero_le_one]

private theorem bendHeight_outside {a b x : ℝ} (hab : a < b) (hx : b ≤ |x|) :
    bendHeight a b x = 0 := by
  have h : (b - |x|) / (b-a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le
  have hmin : min 1 ((b - |x|) / (b-a)) ≤ 0 := (min_le_right _ _).trans h
  exact max_eq_left hmin

private theorem bendHeight_continuous (a b : ℝ) : Continuous (bendHeight a b) := by
  unfold bendHeight
  fun_prop

def bendGraph (a b δ : ℝ) : Set Plane :=
  (fun x : ℝ => Plane.mk x (δ * bendHeight a b x)) '' Icc (-b) b

def positiveRay (v : Plane) : Set Plane :=
  {z | ∃ s : ℝ, 0 ≤ s ∧ z = s • v}

/-- A small upward bend meets an upper radial arm exactly in its flat part. -/
theorem bendGraph_upper_ray_singleton
    (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (v : Plane) (hv : 0 < v 1) (hsmall : δ * |v 0| < a * v 1) :
    bendGraph a b δ ∩ positiveRay v =
      {Plane.mk (δ * v 0 / v 1) δ} := by
  ext z
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,s,hs,he⟩
    have hxval : x = s * v 0 := by
      have h := congrArg (fun z : Plane => z 0) he
      simpa [Plane.mk] using h
    have hyval : δ * bendHeight a b x = s * v 1 := by
      have h := congrArg (fun z : Plane => z 1) he
      simpa [Plane.mk] using h
    have hsbound : s * v 1 ≤ δ := by
      rw [← hyval]
      exact mul_le_of_le_one_right hδ.le (bendHeight_le_one a b x)
    have hxsmall : |x| < a := by
      rw [hxval, abs_mul, abs_of_nonneg hs]
      have hbound : s * |v 0| * v 1 ≤ δ * |v 0| := by
        nlinarith [mul_le_mul_of_nonneg_right hsbound (abs_nonneg (v 0))]
      by_contra hn
      have hmul := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hv.le
      nlinarith [hmul]
    have hheight : bendHeight a b x = 1 :=
      bendHeight_middle hab (le_of_lt hxsmall)
    have hsval : s = δ / v 1 := by
      rw [hheight, mul_one] at hyval
      exact (eq_div_iff (ne_of_gt hv)).2 hyval.symm
    apply Set.mem_singleton_iff.mpr
    ext i
    fin_cases i
    · change x = δ * v 0 / v 1
      rw [hxval,hsval]
      ring
    · change δ * bendHeight a b x = δ
      rw [hheight, mul_one]
  · intro hz
    have hz' : z = Plane.mk (δ * v 0 / v 1) δ := Set.mem_singleton_iff.mp hz
    subst z
    let x : ℝ := δ * v 0 / v 1
    have hxsmall : |x| < a := by
      dsimp [x]
      rw [abs_div, abs_mul, abs_of_pos hδ, abs_of_pos hv]
      exact (div_lt_iff₀ hv).2 hsmall
    have hx : x ∈ Icc (-b) b := by
      have habs := abs_lt.mp (hxsmall.trans hab)
      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have hheight : bendHeight a b x = 1 :=
      bendHeight_middle hab (le_of_lt hxsmall)
    constructor
    · refine ⟨x,hx,?_⟩
      ext i
      fin_cases i
      · rfl
      · simp [hheight]
    · refine ⟨δ / v 1, (div_nonneg hδ.le hv.le), ?_⟩
      ext i
      fin_cases i
      · change δ * v 0 / v 1 = (δ / v 1) * v 0
        ring
      · change δ = (δ / v 1) * v 1
        field_simp [ne_of_gt hv]

theorem bendGraph_upper_segment_singleton
    (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (v : Plane) (hv : 0 < v 1) (hsmall : δ * |v 0| < a * v 1)
    (hinside : δ < v 1) :
    bendGraph a b δ ∩ segment ℝ (0 : Plane) v =
      {Plane.mk (δ * v 0 / v 1) δ} := by
  let z := Plane.mk (δ * v 0 / v 1) δ
  have hray : segment ℝ (0 : Plane) v ⊆ positiveRay v := by
    intro x hx
    rw [segment_eq_image'] at hx
    obtain ⟨s,hs,he⟩ := hx
    refine ⟨s,hs.1,?_⟩
    simpa using he.symm
  have hseg : z ∈ segment ℝ (0 : Plane) v := by
    rw [segment_eq_image']
    refine ⟨δ / v 1,⟨div_nonneg hδ.le hv.le, (div_le_iff₀ hv).2 (by simpa using hinside.le)⟩,?_⟩
    ext i
    fin_cases i
    · change (0 : ℝ) + δ / v 1 * (v 0 - 0) = δ * v 0 / v 1
      ring
    · change (0 : ℝ) + δ / v 1 * (v 1 - 0) = δ
      field_simp [ne_of_gt hv]
      ring
  have hrayEq := bendGraph_upper_ray_singleton a b δ ha hab hδ v hv hsmall
  apply Set.Subset.antisymm
  · intro x hx
    exact hrayEq.subset ⟨hx.1, hray hx.2⟩
  · intro x hx
    have hEq : x = z := Set.mem_singleton_iff.mp hx
    subst x
    have hg : z ∈ bendGraph a b δ := by
      have hz : z ∈ ({z} : Set Plane) := Set.mem_singleton z
      exact (hrayEq.symm ▸ hz).1
    exact ⟨hg,hseg⟩

theorem bendGraph_lower_ray_disjoint
    (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (v : Plane) (hv : v 1 < 0) :
    Disjoint (bendGraph a b δ) (positiveRay v) := by
  apply Set.disjoint_left.mpr
  intro z hz hr
  obtain ⟨x,hx,hzx⟩ := hz
  obtain ⟨s,hs,he⟩ := hr
  have hy : δ * bendHeight a b x = s * v 1 := by
    have h := congrArg (fun z : Plane => z 1) (hzx.trans he)
    simpa [Plane.mk] using h
  have hs0 : s = 0 := by
    by_contra hn
    have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hn)
    have hleft : 0 ≤ δ * bendHeight a b x :=
      mul_nonneg hδ.le (bendHeight_nonneg a b x)
    nlinarith
  have hx0 : x = 0 := by
    have h := congrArg (fun z : Plane => z 0) (hzx.trans he)
    simpa [Plane.mk, hs0] using h
  have hheight : bendHeight a b x = 1 := by
    rw [hx0]
    exact bendHeight_middle hab (by simpa using ha.le)
  rw [hs0, zero_mul, hheight, mul_one] at hy
  exact (ne_of_gt hδ) hy

theorem bendGraph_lower_segment_disjoint
    (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (v : Plane) (hv : v 1 < 0) :
    Disjoint (bendGraph a b δ) (segment ℝ (0 : Plane) v) := by
  apply (bendGraph_lower_ray_disjoint a b δ ha hab hδ v hv).mono_right
  intro x hx
  rw [segment_eq_image'] at hx
  obtain ⟨s,hs,he⟩ := hx
  refine ⟨s,hs.1,?_⟩
  simpa using he.symm

theorem exists_uniform_bend_height
    {J : Type} [Fintype J] (v : J → Plane) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hv : ∀ j, 0 < (v j) 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      ∀ j, δ * |(v j) 0| < a * (v j) 1 ∧ δ < (v j) 1 := by
  let O : Set ℝ := ⋂ j : J,
    {δ : ℝ | δ * |(v j) 0| < a * (v j) 1 ∧ δ < (v j) 1}
  have hO : IsOpen O := isOpen_iInter_of_finite (fun j =>
    (isOpen_lt (continuous_id.mul continuous_const) continuous_const).inter
      (isOpen_lt continuous_id continuous_const))
  have h0 : (0 : ℝ) ∈ O := by
    apply Set.mem_iInter.mpr
    intro j
    exact ⟨by simpa using mul_pos ha (hv j), hv j⟩
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hO 0 h0
  let δ := min R ε / 2
  have hδ : 0 < δ := half_pos (lt_min hR hε)
  have hδR : δ < R := by dsimp [δ]; linarith [min_le_left R ε]
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_right R ε]
  have hδO : δ ∈ O := by
    apply hball
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ] using hδR
  exact ⟨δ,hδ,hδε,fun j => Set.mem_iInter.mp hδO j⟩

theorem unit_bend_is_arc (δ : ℝ) :
    IsArcBetween (bendGraph (1 / 2) 1 δ)
      (Plane.mk (-1) 0) (Plane.mk 1 0) := by
  let f : ℝ → Plane := fun t =>
    Plane.mk (-1 + 2 * t) (δ * bendHeight (1 / 2) 1 (-1 + 2 * t))
  have hfcont : Continuous f := by
    have hx : Continuous (fun t : ℝ => -1 + 2 * t) := by fun_prop
    have hy : Continuous (fun t : ℝ => δ * bendHeight (1 / 2) 1 (-1 + 2 * t)) :=
      continuous_const.mul ((bendHeight_continuous (1 / 2) 1).comp hx)
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact hx
    · exact hy
  have hfinj : Set.InjOn f (Icc (0 : ℝ) 1) := by
    intro s hs t ht he
    have h := congrArg (fun z : Plane => z 0) he
    change -1 + 2 * s = -1 + 2 * t at h
    linarith
  have hfimage : f '' Icc (0 : ℝ) 1 = bendGraph (1 / 2) 1 δ := by
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨-1 + 2 * t,?_,rfl⟩
      constructor <;> linarith [ht.1, ht.2]
    · rintro ⟨x,hx,rfl⟩
      let t := (x + 1) / 2
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        dsimp [t]
        constructor <;> linarith [hx.1,hx.2]
      refine ⟨t,ht,?_⟩
      have he : -1 + 2 * t = x := by dsimp [t]; ring
      simp only [f,he]
  have hleft : bendHeight (1 / 2) 1 (-1) = 0 :=
    bendHeight_outside (by norm_num) (by norm_num)
  have hright : bendHeight (1 / 2) 1 1 = 0 :=
    bendHeight_outside (by norm_num) (by norm_num)
  refine ⟨f,hfcont.continuousOn,hfinj,hfimage,?_,?_⟩
  · ext i
    fin_cases i <;> norm_num [f,hleft]
  · ext i
    fin_cases i <;> norm_num [f,hright]

theorem unit_bend_inside_square (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    bendGraph (1 / 2) 1 δ \
      {Plane.mk (-1) 0, Plane.mk 1 0} ⊆ Plane.openSquare 0 1 := by
  rintro z ⟨⟨x,hx,rfl⟩,hnot⟩
  have hleft : bendHeight (1 / 2) 1 (-1) = 0 :=
    bendHeight_outside (by norm_num) (by norm_num)
  have hright : bendHeight (1 / 2) 1 1 = 0 :=
    bendHeight_outside (by norm_num) (by norm_num)
  have hxl : -1 < x := by
    by_contra hn
    have he : x = -1 := by linarith [hx.1]
    subst x
    apply hnot
    change Plane.mk (-1) (δ * bendHeight (1 / 2) 1 (-1)) ∈
      ({Plane.mk (-1) 0, Plane.mk 1 0} : Set Plane)
    rw [hleft]
    simp
  have hxr : x < 1 := by
    by_contra hn
    have he : x = 1 := by linarith [hx.2]
    subst x
    apply hnot
    change Plane.mk 1 (δ * bendHeight (1 / 2) 1 1) ∈
      ({Plane.mk (-1) 0, Plane.mk 1 0} : Set Plane)
    rw [hright]
    simp
  have hy0 : 0 ≤ δ * bendHeight (1 / 2) 1 x :=
    mul_nonneg hδ.le (bendHeight_nonneg _ _ _)
  have hy1 : δ * bendHeight (1 / 2) 1 x < 1 := by
    have hbound := bendHeight_le_one (1 / 2) 1 x
    nlinarith
  rw [Schoenflies.mem_openSquare_zero_one]
  change max |x| |δ * bendHeight (1 / 2) 1 x| < 1
  exact max_lt (abs_lt.mpr ⟨hxl,hxr⟩)
    (by rw [abs_of_nonneg hy0]; exact hy1)

theorem unit_horizontal_inside_square :
    segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) \
      {Plane.mk (-1) 0, Plane.mk 1 0} ⊆ Plane.openSquare 0 1 := by
  rintro z ⟨hz,hnot⟩
  rw [segment_eq_image'] at hz
  obtain ⟨t,ht,he⟩ := hz
  have hz0 : z 0 = -1 + 2 * t := by
    have h := congrArg (fun w : Plane => w 0) he
    simp [Plane.mk] at h
    linarith
  have hz1 : z 1 = 0 := by
    have h := congrArg (fun w : Plane => w 1) he
    simpa [Plane.mk] using h.symm
  have htl : 0 < t := by
    by_contra hn
    have ht0 : t = 0 := by linarith [ht.1]
    have hzl : z = Plane.mk (-1) 0 := by
      ext i
      fin_cases i
      · simpa [ht0] using hz0
      · simpa using hz1
    exact hnot (by simp [hzl])
  have htr : t < 1 := by
    by_contra hn
    have ht1 : t = 1 := by linarith [ht.2]
    have hzr : z = Plane.mk 1 0 := by
      ext i
      fin_cases i
      · norm_num [ht1] at hz0 ⊢
        exact hz0
      · simpa using hz1
    exact hnot (by simp [hzr])
  rw [Schoenflies.mem_openSquare_zero_one]
  change max |z 0| |z 1| < 1
  rw [hz0,hz1,abs_zero]
  exact max_lt (abs_lt.mpr ⟨by linarith,by linarith⟩) (by norm_num)

theorem unit_bend_subset_closed_square (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    bendGraph (1 / 2) 1 δ ⊆ Plane.closedSquare 0 1 := by
  rintro z ⟨x,hx,rfl⟩
  rw [Schoenflies.mem_closedSquare_zero_one]
  change max |x| |δ * bendHeight (1 / 2) 1 x| ≤ 1
  have hxabs : |x| ≤ 1 := abs_le.mpr hx
  have hy0 : 0 ≤ δ * bendHeight (1 / 2) 1 x :=
    mul_nonneg hδ.le (bendHeight_nonneg _ _ _)
  have hy1 : δ * bendHeight (1 / 2) 1 x ≤ 1 := by
    have hbound := bendHeight_le_one (1 / 2) 1 x
    nlinarith
  exact max_le hxabs (by rwa [abs_of_nonneg hy0])

theorem horizontal_segment_radial_intersection_zero
    (v : Plane) (hv : v 1 ≠ 0) :
    segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) ∩
      segment ℝ (0 : Plane) v = {0} := by
  apply Set.Subset.antisymm
  · rintro z ⟨hzA,hzV⟩
    have hz1 : z 1 = 0 := by
      rw [segment_eq_image'] at hzA
      obtain ⟨t,ht,he⟩ := hzA
      have h := congrArg (fun w : Plane => w 1) he
      simpa [Plane.mk] using h.symm
    rw [segment_eq_image'] at hzV
    obtain ⟨s,hs,he⟩ := hzV
    have hcoord := congrArg (fun w : Plane => w 1) he
    have hs0 : s = 0 := by
      have hmul : s * v 1 = 0 := by simpa [hz1] using hcoord
      exact (mul_eq_zero.mp hmul).resolve_right hv
    apply Set.mem_singleton_iff.mpr
    simpa [hs0] using he.symm
  · rintro z rfl
    refine ⟨?_, left_mem_segment ℝ (0 : Plane) v⟩
    rw [segment_eq_image']
    refine ⟨(1 / 2 : ℝ),by norm_num,?_⟩
    ext i
    fin_cases i <;> norm_num [Plane.mk]

theorem unit_bend_avoids_zero (δ : ℝ) (hδ : 0 < δ) :
    (0 : Plane) ∉ bendGraph (1 / 2) 1 δ := by
  rintro ⟨x,hx,he⟩
  have hx0 : x = 0 := by
    have h := congrArg (fun z : Plane => z 0) he
    simpa [Plane.mk] using h
  have hy0 : δ * bendHeight (1 / 2) 1 x = 0 := by
    have h := congrArg (fun z : Plane => z 1) he
    simpa [Plane.mk] using h
  rw [hx0,bendHeight_middle (by norm_num) (by norm_num),mul_one] at hy0
  exact (ne_of_gt hδ) hy0

theorem unit_horizontal_segment_iff (z : Plane) :
    z ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) ↔
      z ∈ Plane.closedSquare 0 1 ∧ z 1 = 0 := by
  constructor
  · intro hz
    have hsq : z ∈ Plane.closedSquare 0 1 := by
      rw [Schoenflies.mem_closedSquare_zero_one]
      rw [segment_eq_image_lineMap] at hz
      obtain ⟨t,ht,rfl⟩ := hz
      have h0 : (AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 0 = -1 + 2 * t := by
        simp [AffineMap.lineMap_apply_module,Plane.mk]
        ring
      have h1 : (AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 1 = 0 := by
        simp [AffineMap.lineMap_apply_module,Plane.mk]
      change max |(AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 0|
        |(AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t) 1| ≤ 1
      rw [h0,h1,abs_zero]
      exact max_le (abs_le.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩) (by norm_num)
    have hy : z 1 = 0 := by
      rw [segment_eq_image'] at hz
      obtain ⟨t,ht,he⟩ := hz
      have h := congrArg (fun w : Plane => w 1) he
      simpa [Plane.mk] using h.symm
    exact ⟨hsq,hy⟩
  · rintro ⟨hsq,hy⟩
    have hsup : Plane.supNorm z ≤ 1 := Schoenflies.mem_closedSquare_zero_one.mp hsq
    have habs : |z 0| ≤ 1 := by
      exact (le_max_left _ _).trans hsup
    have hzbound := abs_le.mp habs
    rw [segment_eq_image_lineMap]
    refine ⟨(z 0 + 1) / 2,⟨by linarith [hzbound.1],by linarith [hzbound.2]⟩,?_⟩
    ext i
    fin_cases i
    · simp [AffineMap.lineMap_apply_module,Plane.mk]
      ring
    · simpa [AffineMap.lineMap_apply_module,Plane.mk] using hy.symm

end
end CurveComplex.HyperellipticModel.ArcSurgery

#print axioms CurveComplex.HyperellipticModel.ArcSurgery.bendGraph_upper_segment_singleton
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.bendGraph_lower_ray_disjoint
#print axioms CurveComplex.HyperellipticModel.ArcSurgery.exists_uniform_bend_height
