import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalPuncturedSourceDefinitions
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex
open scoped unitInterval

theorem punctured_slope_family_injective (p : Torus)
    (F : FareySlope → Curve (Punctured p))
    (hF : ∀ s, AmbientIsotopy.Rel (fill (F s)).image
      (Set.range (torusWindingMap (slopeDirection s).1 (slopeDirection s).2)))
    (s t : FareySlope) (h : AmbientIsotopy.Rel (F s).image (F t).image) : s = t := by
  have power_zero (k : ℤ)
      (h : (⟨fun z : Circle => z ^ k, continuous_zpow k⟩ : C(Circle, Circle)).Nullhomotopic) :
      k = 0 := by
    obtain ⟨r, ⟨H⟩⟩ := h
    obtain ⟨r₀, hr₀⟩ := Circle.exp_surjective r
    let G := H.symm
    let L : C(I × Circle, ℝ) := Circle.isCoveringMap_exp.liftHomotopy
      G.toContinuousMap (ContinuousMap.const Circle r₀)
      (fun z => (G.apply_zero z).trans hr₀.symm)
    have hL (t : I) (z : Circle) : Circle.exp (L (t, z)) = G (t, z) :=
      congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts G.toContinuousMap
        (ContinuousMap.const Circle r₀) _) (t, z)
    let F : C(Circle, ℝ) := ⟨fun z => L (1, z), L.continuous.comp
      (continuous_const.prodMk continuous_id)⟩
    have hF (z : Circle) : Circle.exp (F z) = z ^ k :=
      (hL 1 z).trans (G.apply_one z)
    let γ : C(I, Circle) :=
      ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
    let δ : C(I, Circle) := ⟨fun t => (γ t) ^ k, (continuous_zpow k).comp γ.continuous⟩
    let Γ : C(I, ℝ) := F.comp γ
    let Λ : C(I, ℝ) := ⟨fun t => Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ)), by fun_prop⟩
    have hΓlift : Circle.exp ∘ Γ = δ := by
      funext t
      exact hF (γ t)
    have hΛlift : Circle.exp ∘ Λ = δ := by
      funext t
      change Circle.exp (Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ))) = (γ t) ^ k
      rw [Circle.exp_add]
      have hΓ0 : Circle.exp (Γ 0) = 1 := by
        have hh := congrFun hΓlift 0
        simpa [δ, γ] using hh
      rw [hΓ0, one_mul]
      simpa only [zsmul_eq_mul, γ, ContinuousMap.coe_mk] using
        Circle.exp_zsmul (2 * Real.pi * (t : ℝ)) k
    have hΓ0 : Γ 0 = Λ 0 := by simp [Λ]
    have hΓeq : Γ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
        simpa using (congrFun hΓlift 0).symm) :=
      (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
        simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΓlift, rfl⟩
    have hΛeq : Λ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
        simpa using (congrFun hΓlift 0).symm) :=
      (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
        simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΛlift, hΓ0.symm⟩
    have hend : Γ 1 = Λ 1 := by rw [hΓeq, hΛeq]
    have hloop : Γ 1 = Γ 0 := by
      change F (γ 1) = F (γ 0)
      congr 1
      simp [γ]
    rw [hloop] at hend
    have he : (k : ℝ) * (2 * Real.pi) = 0 := by
      have hh : Γ 0 = Γ 0 + (k : ℝ) * (2 * Real.pi) := by simpa [Λ] using hend
      linarith
    have hk : (k : ℝ) = 0 := (mul_eq_zero.mp he).resolve_right
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    exact_mod_cast hk
  have transfer {S : Type} [TopologicalSpace S] (c d : Curve S) (χ : C(S, Circle))
      (h : AmbientIsotopy.Rel c.image d.image)
      (hd : (χ.comp ⟨d.map, d.embedded.continuous⟩).Nullhomotopic) :
      (χ.comp ⟨c.map, c.embedded.continuous⟩).Nullhomotopic := by
    obtain ⟨H, hH⟩ := h
    have hr (z : Circle) : H.finalMap (c.map z) ∈ Set.range d.map := by
      rw [show Set.range d.map = d.image from rfl, ← hH]
      exact ⟨c.map z, ⟨z, rfl⟩, rfl⟩
    let η : C(Circle, Circle) := ⟨fun z => d.embedded.toHomeomorph.symm
      ⟨H.finalMap (c.map z), hr z⟩,
      d.embedded.toHomeomorph.symm.continuous.comp
        ((H.map.continuous.comp (continuous_const.prodMk c.embedded.continuous)).subtype_mk _)⟩
    have hη (z : Circle) : d.map (η z) = H.finalMap (c.map z) :=
      congrArg Subtype.val (d.embedded.toHomeomorph.apply_symm_apply
        ⟨H.finalMap (c.map z), hr z⟩)
    let G : (χ.comp ⟨c.map, c.embedded.continuous⟩).Homotopy
        ((χ.comp ⟨d.map, d.embedded.continuous⟩).comp η) := {
      toContinuousMap := ⟨fun tz => χ (H.map (tz.1, c.map tz.2)),
        χ.continuous.comp (H.map.continuous.comp
          (continuous_fst.prodMk (c.embedded.continuous.comp continuous_snd)))⟩
      map_zero_left := by
        intro z
        change χ (H.map (⟨0, by norm_num⟩, c.map z)) = χ (c.map z)
        rw [H.at_zero (c.map z)]
      map_one_left := by
        intro z
        change χ (H.finalMap (c.map z)) = χ (d.map (η z))
        rw [hη] }
    obtain ⟨r, hr⟩ := hd.comp_left η
    exact ⟨r, ContinuousMap.Homotopic.trans ⟨G⟩ hr⟩
  have prim (a : FareySlope) : (slopeDirection a).1.gcd (slopeDirection a).2 = 1 := by
    cases a with
    | none => decide
    | some q => exact rationalSlope_primitive q
  let χ : C(Torus, Circle) := ⟨fun x =>
    x.1 ^ (slopeDirection t).2 * x.2 ^ (-(slopeDirection t).1), by fun_prop⟩
  have χw (i j : ℤ) (z : Circle) : χ (torusWindingMap i j z) =
      z ^ (i * (slopeDirection t).2 - j * (slopeDirection t).1) := by
    change (z ^ i) ^ (slopeDirection t).2 * (z ^ j) ^ (-(slopeDirection t).1) = _
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    congr 1
    ring
  have ht : (χ.comp ⟨(fill (F t)).map, (fill (F t)).embedded.continuous⟩).Nullhomotopic := by
    apply transfer (fill (F t))
      (primitiveTorusCurve (slopeDirection t).1 (slopeDirection t).2 (prim t)) χ (hF t)
    have heq : χ.comp ⟨(primitiveTorusCurve (slopeDirection t).1
        (slopeDirection t).2 (prim t)).map,
        (primitiveTorusCurve (slopeDirection t).1 (slopeDirection t).2 (prim t)).embedded.continuous⟩ =
        ContinuousMap.const Circle 1 := by
      apply ContinuousMap.ext
      intro z
      change χ (torusWindingMap (slopeDirection t).1 (slopeDirection t).2 z) = 1
      rw [χw]
      simp [mul_comm]
    rw [heq]
    exact ContinuousMap.nullhomotopic_of_constant 1
  let χp : C(Punctured p, Circle) := χ.comp ⟨Subtype.val, continuous_subtype_val⟩
  have hs := transfer (F s) (F t) χp h ht
  have hw := transfer
    (primitiveTorusCurve (slopeDirection s).1 (slopeDirection s).2 (prim s))
    (fill (F s)) χ (ambientIsotopy_equivalence.symm (hF s)) hs
  have heq : χ.comp ⟨(primitiveTorusCurve (slopeDirection s).1
      (slopeDirection s).2 (prim s)).map,
      (primitiveTorusCurve (slopeDirection s).1 (slopeDirection s).2 (prim s)).embedded.continuous⟩ =
      (⟨fun z : Circle => z ^ ((slopeDirection s).1 * (slopeDirection t).2 -
        (slopeDirection s).2 * (slopeDirection t).1), continuous_zpow _⟩ : C(Circle, Circle)) := by
    apply ContinuousMap.ext
    intro z
    exact χw _ _ z
  rw [heq] at hw
  have hzero := power_zero _ hw
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some q =>
      simp [slopeDirection] at hzero
  | some q =>
    cases t with
    | none =>
      simp [slopeDirection] at hzero
    | some r =>
      congr 1
      have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      have hr : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
      rw [← q.num_div_den, ← r.num_div_den, div_eq_div_iff hq hr]
      have hz : q.num * (r.den : ℤ) = (q.den : ℤ) * r.num := sub_eq_zero.mp hzero
      exact_mod_cast hz.trans (mul_comm (q.den : ℤ) r.num)

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
