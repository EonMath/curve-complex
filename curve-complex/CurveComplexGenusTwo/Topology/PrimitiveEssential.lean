import CurveComplexGenusTwo.Topology.TorusPrimitiveLift
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import Mathlib.Topology.Homotopy.Lifting
import CurveComplexGenusTwo.Topology.PrimitiveTorusCurve

namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex
open _root_.Topology
open scoped unitInterval

theorem torus_boundsDisc_of_nullhomotopic_from_cover (c : Curve Torus)
    (hc : (⟨c.map, c.embedded.continuous⟩ : C(Circle, Torus)).Nullhomotopic) :
    BoundsDisc c := by
  let Z := AddSubgroup.zmultiples (2 * Real.pi)
  let G := Z × Z
  let : AddAction G (ℝ × ℝ) := {
    vadd := fun g x => ((g.1 : ℝ) + x.1, (g.2 : ℝ) + x.2)
    zero_vadd := by
      intro x
      change ((0 : ℝ) + x.1, (0 : ℝ) + x.2) = x
      simp
    add_vadd := by
      intro g h x
      change (((g.1 : ℝ) + (h.1 : ℝ)) + x.1,
        ((g.2 : ℝ) + (h.2 : ℝ)) + x.2) =
        ((g.1 : ℝ) + ((h.1 : ℝ) + x.1), (g.2 : ℝ) + ((h.2 : ℝ) + x.2))
      simp only [add_assoc] }
  let q : (ℝ × ℝ) → Torus := fun x => (Circle.exp x.1, Circle.exp x.2)
  have hq : IsAddQuotientCoveringMap q G := {
    toIsQuotientMap :=
      (Circle.isCoveringMap_exp.isOpenMap.prodMap Circle.isCoveringMap_exp.isOpenMap).isQuotientMap
        (by fun_prop) (Circle.exp_surjective.prodMap Circle.exp_surjective)
    continuous_const_vadd := by
      intro g
      change Continuous (fun x : ℝ × ℝ => ((g.1 : ℝ) + x.1, (g.2 : ℝ) + x.2))
      fun_prop
    apply_eq_iff_mem_orbit := by
      intro x y
      constructor
      · intro h
        obtain ⟨g₁, hg₁⟩ := Circle.isAddQuotientCoveringMap_exp.apply_eq_iff_mem_orbit.mp
          (congrArg Prod.fst h)
        obtain ⟨g₂, hg₂⟩ := Circle.isAddQuotientCoveringMap_exp.apply_eq_iff_mem_orbit.mp
          (congrArg Prod.snd h)
        exact ⟨(g₁, g₂), Prod.ext hg₁ hg₂⟩
      · rintro ⟨g, rfl⟩
        exact Prod.ext (Circle.isAddQuotientCoveringMap_exp.map_vadd g.1)
          (Circle.isAddQuotientCoveringMap_exp.map_vadd g.2)
    disjoint := by
      intro x
      obtain ⟨U, hU, hUd⟩ := Circle.isAddQuotientCoveringMap_exp.disjoint x.1
      obtain ⟨V, hV, hVd⟩ := Circle.isAddQuotientCoveringMap_exp.disjoint x.2
      refine ⟨U ×ˢ V, prod_mem_nhds hU hV, ?_⟩
      intro g hg
      obtain ⟨z, ⟨y, hy, hyz⟩, hz⟩ := hg
      apply Prod.ext
      · apply hUd g.1
        exact ⟨z.1, ⟨y.1, hy.1, congrArg Prod.fst hyz⟩, hz.1⟩
      · apply hVd g.2
        exact ⟨z.2, ⟨y.2, hy.2, congrArg Prod.snd hyz⟩, hz.2⟩ }
  let e : Schoenflies.Plane ≃ₜ ℝ × ℝ :=
    (PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans Homeomorph.finTwoArrow
  let : AddAction G Schoenflies.Plane := e.toEquiv.addAction G
  have he_vadd (g : G) (x : Schoenflies.Plane) : e (g +ᵥ x) = g +ᵥ e x := by
    change e (e.symm (g +ᵥ e x)) = _
    exact e.apply_symm_apply _
  have hqe : IsAddQuotientCoveringMap (q ∘ e) G := {
    toIsQuotientMap := hq.toIsQuotientMap.comp e.isQuotientMap
    continuous_const_vadd := by
      intro g
      change Continuous (fun x => e.symm ((g.1 : ℝ) + (e x).1, (g.2 : ℝ) + (e x).2))
      fun_prop
    apply_eq_iff_mem_orbit := by
      intro x y
      change q (e x) = q (e y) ↔ _
      rw [hq.apply_eq_iff_mem_orbit]
      constructor
      · rintro ⟨g, hg⟩
        exact ⟨g, e.injective ((he_vadd g y).trans hg)⟩
      · rintro ⟨g, rfl⟩
        exact ⟨g, (he_vadd g y).symm⟩
    disjoint := by
      intro x
      obtain ⟨U, hU, hUd⟩ := hq.disjoint (e x)
      refine ⟨e ⁻¹' U, e.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
      intro g hg
      obtain ⟨z, ⟨y, hy, hyz⟩, hz⟩ := hg
      apply hUd g
      exact ⟨e z, ⟨e y, hy, (he_vadd g y).symm.trans (congrArg e hyz)⟩, hz⟩ }
  exact boundsDisc_of_nullhomotopic_planar_quotient_cover_complete
    (q ∘ e) (IsAddQuotientCoveringMap.toMultiplicative (q ∘ e) G hqe) c hc

theorem torus_curve_nullhomotopic_of_zero_deck_lift (c : Curve Torus)
    (F : C(ℝ, ℝ × ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x))
    (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) = F x) :
    (⟨c.map, c.embedded.continuous⟩ : C(Circle, Torus)).Nullhomotopic := by
  have hfactor : Function.FactorsThrough F Circle.exp := by
    intro x y hxy
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hxy
    rw [hk, hperiod]
  let L : C(Circle, ℝ × ℝ) :=
    (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).lift F hfactor
  have hL (x : ℝ) : L (Circle.exp x) = F x := by
    exact congrArg (fun f : C(ℝ, ℝ × ℝ) => f x)
      ((Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).lift_comp F hfactor)
  let q : C(ℝ × ℝ, Torus) :=
    ⟨fun x => (Circle.exp x.1, Circle.exp x.2), by fun_prop⟩
  have hc : q.comp L = (⟨c.map, c.embedded.continuous⟩ : C(Circle, Torus)) := by
    apply ContinuousMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Circle.exp_surjective z
    change (Circle.exp (L (Circle.exp x)).1, Circle.exp (L (Circle.exp x)).2) = _
    rw [hL]
    exact hproj x
  rw [← hc]
  have hcontract : ContractibleSpace (ℝ × ℝ) := inferInstance
  have hnull : L.Nullhomotopic :=
    ((contractible_iff_id_nullhomotopic _).mp hcontract).comp_left L
  exact hnull.comp_right q

theorem circle_map_homotopic_winding_of_lift (f : C(Circle, Circle))
    (k : ℤ) (F : C(ℝ, ℝ))
    (hF : ∀ x : ℝ, Circle.exp (F x) = f (Circle.exp x))
    (hp : ∀ x : ℝ, F (x + 2 * Real.pi) = F x + (k : ℝ) * (2 * Real.pi)) :
    f.Homotopic ⟨fun z : Circle => z ^ k, continuous_zpow k⟩ := by
  let B : ℝ → ℝ := fun x => F x - (k : ℝ) * x
  have hBp : Function.Periodic B (2 * Real.pi) := by
    intro x
    dsimp [B]
    rw [hp]
    ring
  have hBfiber {x y : ℝ} (h : Circle.exp x = Circle.exp y) : B x = B y := by
    obtain ⟨n, rfl⟩ := Circle.exp_eq_exp.mp h
    exact hBp.int_mul n y
  let b : Circle → ℝ := fun z => B (Complex.arg z)
  have hb (x : ℝ) : b (Circle.exp x) = B x := by
    apply hBfiber
    exact Circle.exp_arg _
  have hbc : Continuous b := by
    apply (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).continuous_iff.mpr
    have he : b ∘ Circle.exp = B := funext hb
    rw [he]
    dsimp [B]
    fun_prop
  have hf (z : Circle) : Circle.exp (b z) * z ^ k = f z := by
    obtain ⟨x, rfl⟩ := Circle.exp_surjective z
    rw [hb]
    change Circle.exp (F x - (k : ℝ) * x) * Circle.exp x ^ k = f (Circle.exp x)
    rw [← Circle.exp_zsmul]
    simp only [zsmul_eq_mul]
    rw [← Circle.exp_add]
    convert hF x using 1 <;> congr 1 <;> ring
  refine ⟨{
    toContinuousMap := ⟨fun tz => Circle.exp ((1 - (tz.1 : ℝ)) * b tz.2) * tz.2 ^ k,
      by fun_prop⟩
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    simpa using hf z
  · intro z
    simp

theorem torus_curve_homotopic_winding_of_deck_lift (c : Curve Torus)
    (m n : ℤ) (F : C(ℝ, ℝ × ℝ))
    (hproj : ∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x))
    (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
      ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
       (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) :
    (⟨c.map, c.embedded.continuous⟩ : C(Circle, Torus)).Homotopic
      ⟨torusWindingMap m n, continuous_torusWindingMap m n⟩ := by
  let f₁ : C(Circle, Circle) :=
    ⟨fun z => (c.map z).1, continuous_fst.comp c.embedded.continuous⟩
  let f₂ : C(Circle, Circle) :=
    ⟨fun z => (c.map z).2, continuous_snd.comp c.embedded.continuous⟩
  let A : C(ℝ, ℝ) := ⟨fun x => (F x).1, continuous_fst.comp F.continuous⟩
  let B : C(ℝ, ℝ) := ⟨fun x => (F x).2, continuous_snd.comp F.continuous⟩
  have hA : f₁.Homotopic ⟨fun z : Circle => z ^ m, continuous_zpow m⟩ := by
    apply circle_map_homotopic_winding_of_lift f₁ m A
    · intro x
      exact congrArg Prod.fst (hproj x)
    · intro x
      change (F (x + 2 * Real.pi)).1 = (F x).1 + (m : ℝ) * (2 * Real.pi)
      simpa using congrArg Prod.fst (hperiod 1 x)
  have hB : f₂.Homotopic ⟨fun z : Circle => z ^ n, continuous_zpow n⟩ := by
    apply circle_map_homotopic_winding_of_lift f₂ n B
    · intro x
      exact congrArg Prod.snd (hproj x)
    · intro x
      change (F (x + 2 * Real.pi)).2 = (F x).2 + (n : ℝ) * (2 * Real.pi)
      simpa using congrArg Prod.snd (hperiod 1 x)
  exact hA.prodMk hB

/-- An essential embedded torus curve has a nonzero primitive deck period. -/
theorem essential_torus_curve_has_primitive_deck_lift (c : Curve Torus)
    (hc : Essential c) :
    ∃ (m n : ℤ) (F : C(ℝ, ℝ × ℝ)),
      (m ≠ 0 ∨ n ≠ 0) ∧ m.gcd n = 1 ∧
      (∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x)) ∧
      (∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
        ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
         (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) ∧
      IsProperMap F ∧ Topology.IsClosedEmbedding F := by
  obtain ⟨m, n, F, hproj, hperiod, hprimitive, _⟩ :=
    torus_curve_has_primitive_or_zero_deck_lift c
  have hnonzero : m ≠ 0 ∨ n ≠ 0 := by
    by_contra hzero
    have ⟨hm, hn⟩ : m = 0 ∧ n = 0 := by simpa using hzero
    have hz (k : ℤ) (x : ℝ) : F (x + (k : ℝ) * (2 * Real.pi)) = F x := by
      simpa [hm, hn] using hperiod k x
    exact hc (torus_boundsDisc_of_nullhomotopic_from_cover c
      (torus_curve_nullhomotopic_of_zero_deck_lift c F hproj hz))
  obtain ⟨hgcd, hp, he⟩ := hprimitive hnonzero
  exact ⟨m, n, F, hnonzero, hgcd, hproj, hperiod, hp, he⟩

theorem essential_torus_curve_has_primitive_winding (c : Curve Torus)
    (hc : Essential c) :
    ∃ m n : ℤ, (m ≠ 0 ∨ n ≠ 0) ∧ m.gcd n = 1 ∧
      (⟨c.map, c.embedded.continuous⟩ : C(Circle, Torus)).Homotopic
        ⟨torusWindingMap m n, continuous_torusWindingMap m n⟩ := by
  obtain ⟨m, n, F, hnonzero, hgcd, hproj, hperiod, _, _⟩ :=
    essential_torus_curve_has_primitive_deck_lift c hc
  exact ⟨m, n, hnonzero, hgcd,
    torus_curve_homotopic_winding_of_deck_lift c m n F hproj hperiod⟩

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
