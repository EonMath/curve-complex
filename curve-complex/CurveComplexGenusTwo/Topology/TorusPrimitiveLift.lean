import CurveComplexGenusTwo.Topology.TorusDeckLift
import CurveComplexGenusTwo.SphereGapFinish.ExteriorInversion
import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import ClassificationJordanCurve.Arcs
import ClassificationJordanCurve.Main
import ClassificationJordanCurve.Brouwer
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Order.Iterate
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open CurveComplex Set Filter Metric _root_.Topology
open Schoenflies CurveComplex.SphereGapFinish

theorem proper_line_inversion_isJordanCurve (F : C(ℝ, Schoenflies.Plane)) (hF : IsProperMap F)
    (hinj : Function.Injective F) (a : Schoenflies.Plane)
    (ha : a ∉ Set.range F) :
    Schoenflies.IsJordanCurve (insert a (Schoenflies.invert a '' Set.range F)) := by
  let q : OnePoint ℝ → Schoenflies.Plane :=
    invertAtInfinity a ∘ OnePoint.map F
  have hmap : Continuous (OnePoint.map F) := by
    apply OnePoint.continuous_map F.continuous
    simpa only [coclosedCompact_eq_cocompact] using
      (isProperMap_iff_tendsto_cocompact.mp hF).2
  have hq : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro z
    cases z with
    | infty =>
      exact (invertAtInfinity_continuousAt_infty a).comp hmap.continuousAt
    | coe x =>
      apply OnePoint.continuousAt_coe.mpr
      change ContinuousAt (fun x : ℝ => Schoenflies.invert a (F x)) x
      exact (Schoenflies.continuousAt_invert (by
        intro h; exact ha ⟨x, h⟩)).comp F.continuous.continuousAt
  have hqi : Function.Injective q := by
    intro x y hxy
    cases x with
    | infty =>
      cases y with
      | infty => rfl
      | coe y =>
        change a = Schoenflies.invert a (F y) at hxy
        exact False.elim (ha ⟨y, Schoenflies.invert_eq_center_iff.mp hxy.symm⟩)
    | coe x =>
      cases y with
      | infty =>
        change Schoenflies.invert a (F x) = a at hxy
        exact False.elim (ha ⟨x, Schoenflies.invert_eq_center_iff.mp hxy⟩)
      | coe y =>
        change Schoenflies.invert a (F x) = Schoenflies.invert a (F y) at hxy
        exact congrArg OnePoint.some (hinj (Schoenflies.invert_injective a hxy))
  let e : OnePoint ℝ ≃ₜ Circle :=
    (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).trans
      ClassificationJordanCurve.Arcs.circleHomeoSphere.symm
  let r : C(Circle, Schoenflies.Plane) := ⟨q ∘ e.symm, hq.comp e.symm.continuous⟩
  have hr : IsEmbedding r := (r.continuous.isClosedEmbedding (hqi.comp e.symm.injective)).isEmbedding
  have hrange : Set.range r = insert a (Schoenflies.invert a '' Set.range F) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      change q (e.symm x) ∈ _
      generalize e.symm x = y
      cases y with
      | infty => exact Set.mem_insert a _
      | coe t => exact Set.mem_insert_of_mem _ ⟨F t, ⟨t, rfl⟩, rfl⟩
    · intro hz
      rcases hz with hz | ⟨w, ⟨t, rfl⟩, rfl⟩
      · subst z
        exact ⟨e OnePoint.infty, by simp [r, q, invertAtInfinity]⟩
      · exact ⟨e (OnePoint.some t), by simp [r, q, invertAtInfinity]⟩
  rw [← hrange]
  exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr

theorem proper_line_sides_of_inversion_jordan (L : Set Plane) (a : Plane) (ha : a ∉ L)
    (hJ : IsJordanCurve (insert a (invert a '' L))) :
    ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Lᶜ ∧ frontier U = L ∧ frontier V = L := by
  let C := insert a (invert a '' L)
  have hsep : IsSeparating C := jordan_curve_theorem hJ
  have haC : a ∈ C := Set.mem_insert a _
  have hain : a ∉ inside C := fun h => h.1 haC
  have haout : a ∉ outside C := fun h => h.1 haC
  let U := invert a '' inside C
  let V := invert a '' outside C ∪ {a}
  have hUopen : IsOpen U := isOpen_invert_image hsep.isOpen_inside hain
  have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show z ≠ a from fun h => haout (h ▸ hz))
  have hinc : inside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show z ≠ a from fun h => hain (h ▸ hz))
  have hUconn : IsConnected U :=
    hsep.isConnected_inside.image _ ((continuousOn_invert a).mono hinc)
  obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
  have hTopen : IsOpen (invert a '' outside C) :=
    isOpen_invert_image hsep.isOpen_outside haout
  have hVball : ball a R⁻¹ ⊆ V := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact Or.inr rfl
    · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
      have hpos : 0 < dist z a := dist_pos.2 hza
      rw [mem_compl_iff, mem_closedBall, dist_invert_center]
      exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
  have hVopen : IsOpen V := by
    have hrw : V = invert a '' outside C ∪ ball a R⁻¹ := by
      refine Subset.antisymm (union_subset subset_union_left ?_)
        (union_subset subset_union_left hVball)
      rintro z rfl
      exact Or.inr (mem_ball_self (by positivity))
    rw [hrw]
    exact hTopen.union isOpen_ball
  have hacl : a ∈ closure (invert a '' outside C) := by
    rw [Metric.mem_closure_iff]
    intro e he
    obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_isBounded_outside
        ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
    refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
    rw [dist_comm, dist_invert_center]
    exact inv_lt_of_inv_lt₀ he hzfar
  have hVconn : IsConnected V := by
    refine ⟨⟨a, Or.inr rfl⟩, ?_⟩
    exact (hsep.isConnected_outside.image _
      ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (by rintro z rfl; exact hacl))
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | he)
    · have he' := invert_injective a he
      exact Set.disjoint_left.mp disjoint_inside_outside hx (he' ▸ hy)
    · exact hain ((invert_eq_center_iff.mp he) ▸ hx)
  have hinv (z : Plane) : invert a z ∈ C ↔ z = a ∨ z ∈ L := by
    dsimp [C]
    simp only [mem_insert_iff, invert_eq_center_iff]
    rw [Set.mem_image]
    constructor
    · rintro (h | ⟨x, hx, he⟩)
      · exact Or.inl h
      · exact Or.inr ((invert_injective a he) ▸ hx)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨z, h, rfl⟩
  have hpart : U ∪ V = Lᶜ := by
    ext z
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl)
      · intro hz
        have := (hinv (invert a x)).mpr (Or.inr hz)
        rw [invert_invert] at this
        exact hx.1 this
      · intro hz
        have := (hinv (invert a x)).mpr (Or.inr hz)
        rw [invert_invert] at this
        exact hx.1 this
      · exact ha
    · intro hz
      by_cases hza : z = a
      · exact Or.inr (Or.inr hza)
      · have hzC : invert a z ∉ C := by simpa [hinv, hza] using hz
        have hzside : invert a z ∈ inside C ∪ outside C := by
          rwa [inside_union_outside]
        rcases hzside with hu | hv
        · exact Or.inl ⟨invert a z, hu, invert_invert a z⟩
        · exact Or.inr (Or.inl ⟨invert a z, hv, invert_invert a z⟩)
  have hUL : Disjoint U L := by
    apply Set.disjoint_left.mpr
    intro x hx hL
    exact (show x ∈ Lᶜ from hpart ▸ Or.inl hx) hL
  have hVL : Disjoint V L := by
    apply Set.disjoint_left.mpr
    intro x hx hL
    exact (show x ∈ Lᶜ from hpart ▸ Or.inr hx) hL
  have hfrontU : frontier U = L := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxL
      have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
      rcases hside with hu | hv
      · exact (hUopen.frontier_eq ▸ hx).2 hu
      · exact Set.disjoint_right.mp (hdis.closure_left hVopen) hv (frontier_subset_closure hx)
    · intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
      have hixcl : invert a x ∈ closure (inside C) := by
        rw [← hsep.frontier_inside] at hixC
        exact frontier_subset_closure hixC
      rw [hUopen.frontier_eq]
      refine ⟨?_, fun h => Set.disjoint_left.mp hUL h hx⟩
      simpa only [invert_invert] using
        mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
  have hfrontV : frontier V = L := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxL
      have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
      rcases hside with hu | hv
      · exact Set.disjoint_left.mp (hdis.closure_right hUopen) hu (frontier_subset_closure hx)
      · exact (hVopen.frontier_eq ▸ hx).2 hv
    · intro x hx
      have hxa : x ≠ a := fun h => ha (h ▸ hx)
      have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
      have hixcl : invert a x ∈ closure (outside C) := by
        rw [← hsep.frontier_outside] at hixC
        exact frontier_subset_closure hixC
      rw [hVopen.frontier_eq]
      refine ⟨?_, fun h => Set.disjoint_left.mp hVL h hx⟩
      apply closure_mono (show invert a '' outside C ⊆ V from subset_union_left)
      simpa only [invert_invert] using
        mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
  exact ⟨U, V, hUopen, hVopen, hUconn, hVconn, hdis, hpart, hfrontU, hfrontV⟩

theorem separating_set_no_disjoint_periodic_translate {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X)
    (L U V A B : Set X) (hL : IsConnected L)
    (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
    (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
    (hfU : frontier U = L) (hfV : frontier V = L)
    (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A ⊆ U) (hBV : B ⊆ V)
    (heA : e '' A = A) (heB : e '' B = B)
    (n : ℕ) (hn : 0 < n) (hperiod : e^[n] '' L = L) :
    ¬ Disjoint L (e '' L) := by
  have ordered
      (L₁ L₂ U₁ V₁ U₂ V₂ : Set X)
      (hL₁ : L₁.Nonempty) (hL₂ : IsConnected L₂)
      (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
      (hcU₁ : IsConnected U₁) (hcV₁ : IsConnected V₁)
      (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
      (hp₁ : U₁ ∪ V₁ = L₁ᶜ) (hp₂ : U₂ ∪ V₂ = L₂ᶜ)
      (hfU₁ : frontier U₁ = L₁) (hfV₁ : frontier V₁ = L₁)
      (hdL : Disjoint L₁ L₂)
      (hcommonU : (U₁ ∩ U₂).Nonempty) (hcommonV : (V₁ ∩ V₂).Nonempty) :
      U₁ ⊂ U₂ ∨ U₂ ⊂ U₁ := by
    have hU₁L : Disjoint U₁ L₁ := by
      apply disjoint_left.mpr
      intro x hx hL
      exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inl hx) hL
    have hV₁L : Disjoint V₁ L₁ := by
      apply disjoint_left.mpr
      intro x hx hL
      exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inr hx) hL
    have hU₂L : Disjoint U₂ L₂ := by
      apply disjoint_left.mpr
      intro x hx hL
      exact (show x ∈ L₂ᶜ from hp₂ ▸ Or.inl hx) hL
    have hclU : closure U₁ = U₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfU₁]
    have hclV : closure V₁ = V₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfV₁]
    have hsub : L₂ ⊆ U₁ ∪ V₁ := by
      rw [hp₁]
      exact fun x hx h => disjoint_left.mp hdL h hx
    rcases hL₂.isPreconnected.subset_or_subset hU₁ hV₁ hd₁ hsub with hLU | hLV
    · have hsubcl : closure V₁ ⊆ U₂ ∪ V₂ := by
        rw [hp₂, hclV]
        rintro x (hx | hx) hL
        · exact disjoint_left.mp hd₁ (hLU hL) hx
        · exact disjoint_left.mp hdL hx hL
      have hcl : closure V₁ ⊆ V₂ := by
        rcases hcV₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
        · obtain ⟨x, hx₁, hx₂⟩ := hcommonV
          exact False.elim (disjoint_left.mp hd₂ (h (subset_closure hx₁)) hx₂)
        · exact h
      have hUU : U₂ ⊆ U₁ := by
        intro x hx
        by_contra hx₁
        have hxcl : x ∈ closure V₁ := by
          rw [hclV]
          by_cases hxL : x ∈ L₁
          · exact Or.inr hxL
          · have hside : x ∈ U₁ ∪ V₁ := hp₁.symm ▸ hxL
            exact Or.inl (hside.resolve_left hx₁)
        exact disjoint_left.mp hd₂ hx (hcl hxcl)
      right
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨hUU, ?_⟩
      intro he
      obtain ⟨x, hx⟩ := hL₂.nonempty
      exact disjoint_left.mp hU₂L (he.symm ▸ hLU hx) hx
    · have hsubcl : closure U₁ ⊆ U₂ ∪ V₂ := by
        rw [hp₂, hclU]
        rintro x (hx | hx) hL
        · exact disjoint_left.mp hd₁ hx (hLV hL)
        · exact disjoint_left.mp hdL hx hL
      have hcl : closure U₁ ⊆ U₂ := by
        rcases hcU₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
        · exact h
        · obtain ⟨x, hx₁, hx₂⟩ := hcommonU
          exact False.elim (disjoint_left.mp hd₂ hx₂ (h (subset_closure hx₁)))
      left
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨subset_closure.trans hcl, ?_⟩
      intro he
      obtain ⟨x, hx⟩ := hL₁
      have hxc : x ∈ closure U₁ := hclU.symm ▸ Or.inr hx
      exact disjoint_left.mp hU₁L (he.symm ▸ hcl hxc) hx
  have fixed_iter (S : Set X) (hS : e '' S = S) (k : ℕ) : e^[k] '' S = S := by
    rw [Set.image_iterate_eq]
    induction k with
    | zero => rfl
    | succ k hk => simpa only [Function.iterate_succ_apply', hk] using hS
  have hmarker (S W : Set X) (hS : S.Nonempty) (hSW : S ⊆ W)
      (hfix : e '' S = S) : (W ∩ e '' W).Nonempty := by
    obtain ⟨x, hx⟩ := hS
    refine ⟨e x, ?_, ⟨x, hSW hx, rfl⟩⟩
    exact hSW (hfix ▸ mem_image_of_mem e hx)
  have hUsub : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
  have hVsub : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
  have hUP : e^[n] '' U ⊆ U := by
    have hsub : e^[n] '' U ⊆ U ∪ V := by
      rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
      exact Set.image_mono hUsub
    rcases (hcU.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
      hU hV hd hsub with h | h
    · exact h
    · obtain ⟨a, ha⟩ := hA
      have hai : a ∈ e^[n] '' A := (fixed_iter A heA n).symm ▸ ha
      exact False.elim (disjoint_left.mp hd (hAU ha) (h (Set.image_mono hAU hai)))
  have hVP : e^[n] '' V ⊆ V := by
    have hsub : e^[n] '' V ⊆ U ∪ V := by
      rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
      exact Set.image_mono hVsub
    rcases (hcV.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
      hU hV hd hsub with h | h
    · obtain ⟨b, hb⟩ := hB
      have hbi : b ∈ e^[n] '' B := (fixed_iter B heB n).symm ▸ hb
      exact False.elim (disjoint_left.mp hd (h (Set.image_mono hBV hbi)) (hBV hb))
    · exact h
  have hperiodU : e^[n] '' U = U := by
    apply Subset.antisymm hUP
    intro x hx
    have hxp : x ∈ e^[n] '' U ∪ e^[n] '' V := by
      rw [← Set.image_union, hpart, Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩, hperiod]
      exact hUsub hx
    exact hxp.resolve_right (fun h => disjoint_left.mp hd hx (hVP h))
  intro hdisL
  have hpartE : (e '' U) ∪ (e '' V) = (e '' L)ᶜ := by
    rw [← Set.image_union, hpart, e.image_compl]
  have horder := ordered L (e '' L) U V (e '' U) (e '' V)
    hL.nonempty (hL.image _ e.continuous.continuousOn) hU hV
    (e.isOpenMap _ hU) (e.isOpenMap _ hV) hcU hcV hd
    ((Set.disjoint_image_iff e.injective).mpr hd) hpart hpartE hfU hfV hdisL
    (hmarker A U hA hAU heA) (hmarker B V hB hBV heB)
  have hmono : StrictMono (Set.image e) := e.injective.image_strictMono
  have hp : (Set.image e)^[n] U = U := by simpa only [← Set.image_iterate_eq] using hperiodU
  rcases horder with h | h
  · have hh := hmono.strictMono_iterate_of_lt_map h hn
    simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh
  · have hh := hmono.strictAnti_iterate_of_map_lt h hn
    simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh

theorem periodic_proper_line_meets_root_translate (F : C(ℝ, ℝ × ℝ)) (hF : IsProperMap F) (hinj : Function.Injective F)
    (T a b : ℝ) (hT : 0 < T) (hab : a ≠ 0 ∨ b ≠ 0) (n : ℕ) (hn : 0 < n)
    (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * T) =
      F x + ((k : ℝ) * (n : ℝ) * a, (k : ℝ) * (n : ℝ) * b)) :
    ¬ Disjoint (Set.range F) ((fun z : ℝ × ℝ => z + (a, b)) '' Set.range F) := by
  have normalize (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
      ∃ e : (ℝ × ℝ) →ₗ[ℝ] Schoenflies.Plane,
        IsProperMap e ∧ Function.Injective e ∧
        (∀ x, e x 0 = a * x.1 + b * x.2) ∧
        (∀ x, e x 1 = -b * x.1 + a * x.2) ∧
        (∀ k : ℝ, e (k * a, k * b) = !₂[k * (a ^ 2 + b ^ 2), 0]) := by
    let e : (ℝ × ℝ) →ₗ[ℝ] Schoenflies.Plane := {
      toFun := fun x => !₂[a * x.1 + b * x.2, -b * x.1 + a * x.2]
      map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
      map_smul' := by intro c x; ext i; fin_cases i <;> simp <;> ring }
    have hpos : 0 < a ^ 2 + b ^ 2 := by
      rcases hab with ha | hb
      · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
      · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
    have hi : Function.Injective e := by
      intro x y he
      have h0 : a * x.1 + b * x.2 = a * y.1 + b * y.2 := congrArg (fun z => z 0) he
      have h1 : -b * x.1 + a * x.2 = -b * y.1 + a * y.2 := congrArg (fun z => z 1) he
      have hdx : (a ^ 2 + b ^ 2) * (x.1 - y.1) = 0 := by
        linear_combination a * h0 - b * h1
      have hdy : (a ^ 2 + b ^ 2) * (x.2 - y.2) = 0 := by
        linear_combination b * h0 + a * h1
      exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hdx).resolve_left (ne_of_gt hpos)))
        (sub_eq_zero.mp ((mul_eq_zero.mp hdy).resolve_left (ne_of_gt hpos)))
    refine ⟨e, (e.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)).isProperMap, hi, fun _ => rfl, fun _ => rfl, ?_⟩
    intro k
    ext i
    fin_cases i <;> dsimp [e] <;> ring
  have horizontal (F : C(ℝ, Plane)) (hF : IsProperMap F) (hinj : Function.Injective F)
      (T p : ℝ) (hT : 0 < T) (hp : 0 < p) (n : ℕ) (hn : 0 < n)
      (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * T) =
        F x + !₂[(k : ℝ) * ((n : ℝ) * p), 0]) :
      ¬ Disjoint (Set.range F) ((fun z : Plane => z + !₂[p, 0]) '' Set.range F) := by
    have horizontal (F : C(ℝ, Plane)) (hF : IsProperMap F) (hinj : Function.Injective F)
        (B : ℝ) (hB : 0 < B) (hbound : ∀ x : ℝ, |F x 1| < B)
        (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
        (p : ℝ) (n : ℕ) (hn : 0 < n)
        (hperiod : (fun z : Plane => z + !₂[p, 0])^[n] '' Set.range F = Set.range F) :
        ¬ Disjoint (Set.range F) ((fun z : Plane => z + !₂[p, 0]) '' Set.range F) := by
      have line_jordan (F : C(ℝ, Schoenflies.Plane)) (hF : IsProperMap F)
          (hinj : Function.Injective F) (a : Schoenflies.Plane)
          (ha : a ∉ Set.range F) :
          Schoenflies.IsJordanCurve (insert a (Schoenflies.invert a '' Set.range F)) := by
        let q : OnePoint ℝ → Schoenflies.Plane :=
          invertAtInfinity a ∘ OnePoint.map F
        have hmap : Continuous (OnePoint.map F) := by
          apply OnePoint.continuous_map F.continuous
          simpa only [coclosedCompact_eq_cocompact] using
            (isProperMap_iff_tendsto_cocompact.mp hF).2
        have hq : Continuous q := by
          apply continuous_iff_continuousAt.mpr
          intro z
          cases z with
          | infty =>
            exact (invertAtInfinity_continuousAt_infty a).comp hmap.continuousAt
          | coe x =>
            apply OnePoint.continuousAt_coe.mpr
            change ContinuousAt (fun x : ℝ => Schoenflies.invert a (F x)) x
            exact (Schoenflies.continuousAt_invert (by
              intro h; exact ha ⟨x, h⟩)).comp F.continuous.continuousAt
        have hqi : Function.Injective q := by
          intro x y hxy
          cases x with
          | infty =>
            cases y with
            | infty => rfl
            | coe y =>
              change a = Schoenflies.invert a (F y) at hxy
              exact False.elim (ha ⟨y, Schoenflies.invert_eq_center_iff.mp hxy.symm⟩)
          | coe x =>
            cases y with
            | infty =>
              change Schoenflies.invert a (F x) = a at hxy
              exact False.elim (ha ⟨x, Schoenflies.invert_eq_center_iff.mp hxy⟩)
            | coe y =>
              change Schoenflies.invert a (F x) = Schoenflies.invert a (F y) at hxy
              exact congrArg OnePoint.some (hinj (Schoenflies.invert_injective a hxy))
        let e : OnePoint ℝ ≃ₜ Circle :=
          (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).trans
            ClassificationJordanCurve.Arcs.circleHomeoSphere.symm
        let r : C(Circle, Schoenflies.Plane) := ⟨q ∘ e.symm, hq.comp e.symm.continuous⟩
        have hr : IsEmbedding r := (r.continuous.isClosedEmbedding (hqi.comp e.symm.injective)).isEmbedding
        have hrange : Set.range r = insert a (Schoenflies.invert a '' Set.range F) := by
          ext z
          constructor
          · rintro ⟨x, rfl⟩
            change q (e.symm x) ∈ _
            generalize e.symm x = y
            cases y with
            | infty => exact Set.mem_insert a _
            | coe t => exact Set.mem_insert_of_mem _ ⟨F t, ⟨t, rfl⟩, rfl⟩
          · intro hz
            rcases hz with hz | ⟨w, ⟨t, rfl⟩, rfl⟩
            · subst z
              exact ⟨e OnePoint.infty, by simp [r, q, invertAtInfinity]⟩
            · exact ⟨e (OnePoint.some t), by simp [r, q, invertAtInfinity]⟩
        rw [← hrange]
        exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
      have split (L : Set Plane) (a : Plane) (ha : a ∉ L)
          (hJ : IsJordanCurve (insert a (invert a '' L))) :
          ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
            Disjoint U V ∧ U ∪ V = Lᶜ ∧ frontier U = L ∧ frontier V = L := by
        let C := insert a (invert a '' L)
        have hsep : IsSeparating C := jordan_curve_theorem hJ
        have haC : a ∈ C := Set.mem_insert a _
        have hain : a ∉ inside C := fun h => h.1 haC
        have haout : a ∉ outside C := fun h => h.1 haC
        let U := invert a '' inside C
        let V := invert a '' outside C ∪ {a}
        have hUopen : IsOpen U := isOpen_invert_image hsep.isOpen_inside hain
        have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
          intro z hz
          simpa only [mem_compl_iff, mem_singleton_iff] using
            (show z ≠ a from fun h => haout (h ▸ hz))
        have hinc : inside C ⊆ ({a}ᶜ : Set Plane) := by
          intro z hz
          simpa only [mem_compl_iff, mem_singleton_iff] using
            (show z ≠ a from fun h => hain (h ▸ hz))
        have hUconn : IsConnected U :=
          hsep.isConnected_inside.image _ ((continuousOn_invert a).mono hinc)
        obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
        have hTopen : IsOpen (invert a '' outside C) :=
          isOpen_invert_image hsep.isOpen_outside haout
        have hVball : ball a R⁻¹ ⊆ V := by
          intro z hz
          rcases eq_or_ne z a with rfl | hza
          · exact Or.inr rfl
          · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
            have hpos : 0 < dist z a := dist_pos.2 hza
            rw [mem_compl_iff, mem_closedBall, dist_invert_center]
            exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
        have hVopen : IsOpen V := by
          have hrw : V = invert a '' outside C ∪ ball a R⁻¹ := by
            refine Subset.antisymm (union_subset subset_union_left ?_)
              (union_subset subset_union_left hVball)
            rintro z rfl
            exact Or.inr (mem_ball_self (by positivity))
          rw [hrw]
          exact hTopen.union isOpen_ball
        have hacl : a ∈ closure (invert a '' outside C) := by
          rw [Metric.mem_closure_iff]
          intro e he
          obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
            by_contra hcon
            push Not at hcon
            exact hsep.not_isBounded_outside
              ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
          refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
          rw [dist_comm, dist_invert_center]
          exact inv_lt_of_inv_lt₀ he hzfar
        have hVconn : IsConnected V := by
          refine ⟨⟨a, Or.inr rfl⟩, ?_⟩
          exact (hsep.isConnected_outside.image _
            ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
            (union_subset subset_closure (by rintro z rfl; exact hacl))
        have hdis : Disjoint U V := by
          apply Set.disjoint_left.mpr
          rintro z ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | he)
          · have he' := invert_injective a he
            exact Set.disjoint_left.mp disjoint_inside_outside hx (he' ▸ hy)
          · exact hain ((invert_eq_center_iff.mp he) ▸ hx)
        have hinv (z : Plane) : invert a z ∈ C ↔ z = a ∨ z ∈ L := by
          dsimp [C]
          simp only [mem_insert_iff, invert_eq_center_iff]
          rw [Set.mem_image]
          constructor
          · rintro (h | ⟨x, hx, he⟩)
            · exact Or.inl h
            · exact Or.inr ((invert_injective a he) ▸ hx)
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr ⟨z, h, rfl⟩
        have hpart : U ∪ V = Lᶜ := by
          ext z
          constructor
          · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl)
            · intro hz
              have := (hinv (invert a x)).mpr (Or.inr hz)
              rw [invert_invert] at this
              exact hx.1 this
            · intro hz
              have := (hinv (invert a x)).mpr (Or.inr hz)
              rw [invert_invert] at this
              exact hx.1 this
            · exact ha
          · intro hz
            by_cases hza : z = a
            · exact Or.inr (Or.inr hza)
            · have hzC : invert a z ∉ C := by simpa [hinv, hza] using hz
              have hzside : invert a z ∈ inside C ∪ outside C := by
                rwa [inside_union_outside]
              rcases hzside with hu | hv
              · exact Or.inl ⟨invert a z, hu, invert_invert a z⟩
              · exact Or.inr (Or.inl ⟨invert a z, hv, invert_invert a z⟩)
        have hUL : Disjoint U L := by
          apply Set.disjoint_left.mpr
          intro x hx hL
          exact (show x ∈ Lᶜ from hpart ▸ Or.inl hx) hL
        have hVL : Disjoint V L := by
          apply Set.disjoint_left.mpr
          intro x hx hL
          exact (show x ∈ Lᶜ from hpart ▸ Or.inr hx) hL
        have hfrontU : frontier U = L := by
          apply Subset.antisymm
          · intro x hx
            by_contra hxL
            have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
            rcases hside with hu | hv
            · exact (hUopen.frontier_eq ▸ hx).2 hu
            · exact Set.disjoint_right.mp (hdis.closure_left hVopen) hv (frontier_subset_closure hx)
          · intro x hx
            have hxa : x ≠ a := fun h => ha (h ▸ hx)
            have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
            have hixcl : invert a x ∈ closure (inside C) := by
              rw [← hsep.frontier_inside] at hixC
              exact frontier_subset_closure hixC
            rw [hUopen.frontier_eq]
            refine ⟨?_, fun h => Set.disjoint_left.mp hUL h hx⟩
            simpa only [invert_invert] using
              mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
        have hfrontV : frontier V = L := by
          apply Subset.antisymm
          · intro x hx
            by_contra hxL
            have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
            rcases hside with hu | hv
            · exact Set.disjoint_left.mp (hdis.closure_right hUopen) hu (frontier_subset_closure hx)
            · exact (hVopen.frontier_eq ▸ hx).2 hv
          · intro x hx
            have hxa : x ≠ a := fun h => ha (h ▸ hx)
            have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
            have hixcl : invert a x ∈ closure (outside C) := by
              rw [← hsep.frontier_outside] at hixC
              exact frontier_subset_closure hixC
            rw [hVopen.frontier_eq]
            refine ⟨?_, fun h => Set.disjoint_left.mp hVL h hx⟩
            apply closure_mono (show invert a '' outside C ⊆ V from subset_union_left)
            simpa only [invert_invert] using
              mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
        exact ⟨U, V, hUopen, hVopen, hUconn, hVconn, hdis, hpart, hfrontU, hfrontV⟩
      have no_crossing (F : C(ℝ, Plane)) (B : ℝ) (hB : 0 < B)
          (hbound : ∀ x : ℝ, |F x 1| < B)
          (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
          (u w : Plane) (hu : u 1 ≤ -B) (hw : B ≤ w 1) :
          ¬ JoinedIn (Set.range F)ᶜ u w := by
        have crossing_strip {a b c d : ℝ} (hab : a < b) (hcd : c < d)
            (h v : ℝ → Plane)
            (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
            (hhY : ∀ t ∈ Icc (-1 : ℝ) 1, c < h t 1 ∧ h t 1 < d)
            (hvX : ∀ t ∈ Icc (-1 : ℝ) 1, a < v t 0 ∧ v t 0 < b)
            (hh1 : h (-1) 0 ≤ a) (hh2 : b ≤ h 1 0)
            (hv1 : v (-1) 1 ≤ c) (hv2 : d ≤ v 1 1) :
            ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, h s = v t := by
          let H : ℝ → Plane := fun s => !₂[max a (min b (h s 0)), h s 1]
          let V : ℝ → Plane := fun t => !₂[v t 0, max c (min d (v t 1))]
          have hH : ContinuousOn H (Icc (-1) 1) := by
            apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
            apply continuousOn_pi.mpr
            intro i
            fin_cases i
            · exact (show Continuous (fun x : ℝ => max a (min b x)) by fun_prop).comp_continuousOn
                ((EuclideanSpace.proj 0).continuous.comp_continuousOn hh)
            · exact (EuclideanSpace.proj 1).continuous.comp_continuousOn hh
          have hV : ContinuousOn V (Icc (-1) 1) := by
            apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
            apply continuousOn_pi.mpr
            intro i
            fin_cases i
            · exact (EuclideanSpace.proj 0).continuous.comp_continuousOn hv
            · exact (show Continuous (fun x : ℝ => max c (min d x)) by fun_prop).comp_continuousOn
                ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv)
          have hHE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
              H t 0 ∈ Icc a b ∧ H t 1 ∈ Icc c d := by
            exact ⟨⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩, (hhY t ht).1.le, (hhY t ht).2.le⟩
          have hVE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
              V t 0 ∈ Icc a b ∧ V t 1 ∈ Icc c d := by
            exact ⟨⟨(hvX t ht).1.le, (hvX t ht).2.le⟩, le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
          have hH1 : H (-1) 0 = a := by
            dsimp [H]
            rw [min_eq_right (hh1.trans hab.le), max_eq_left hh1]
          have hH2 : H 1 0 = b := by
            dsimp [H]
            rw [min_eq_left hh2, max_eq_right hab.le]
          have hV1 : V (-1) 1 = c := by
            dsimp [V]
            rw [min_eq_right (hv1.trans hcd.le), max_eq_left hv1]
          have hV2 : V 1 1 = d := by
            dsimp [V]
            rw [min_eq_left hv2, max_eq_right hcd.le]
          obtain ⟨s, hs, t, ht, he⟩ := ClassificationJordanCurve.crossing ClassificationJordanCurve.Brouwer.brouwerFPT
            hab.le hcd.le H V hH hV hHE hVE hH1 hH2 hV1 hV2
          have clamp {l u x z : ℝ} (hlu : l < u) (hz : l < z ∧ z < u)
              (he : max l (min u x) = z) : x = z := by
            by_cases hx : x ≤ l
            · rw [min_eq_right (hx.trans hlu.le), max_eq_left hx] at he
              linarith [hz.1]
            · by_cases hxu : u ≤ x
              · rw [min_eq_left hxu, max_eq_right hlu.le] at he
                linarith [hz.2]
              · rwa [min_eq_right (le_of_not_ge hxu), max_eq_right (le_of_not_ge hx)] at he
          refine ⟨s, hs, t, ht, ?_⟩
          have he0 := congrArg (fun p : Plane => p 0) he
          have he1 := congrArg (fun p : Plane => p 1) he
          ext i
          fin_cases i
          · exact clamp hab (hvX t ht) he0
          · exact (clamp hcd (hhY s hs) he1.symm).symm
        intro hjoin
        obtain ⟨v, hv, hv0, hv1, hvmem⟩ := ClassificationJordanCurve.arc_path hjoin
        have hvc : ContinuousOn (fun t : ℝ => |v t 0|) (Icc (-1) 1) :=
          continuous_abs.comp_continuousOn ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv)
        obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hvc).bddAbove
        let R := max M 0 + 1
        have hR : 0 < R := by dsimp [R]; positivity
        have hMv (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |v t 0| < R := by
          have hm := hM (Set.mem_image_of_mem _ ht)
          dsimp [R]
          linarith [le_max_left M 0]
        obtain ⟨A, hA0, hA1⟩ := hends R
        let h : ℝ → Plane := fun s => F (A * s)
        have hhc : ContinuousOn h (Icc (-1) 1) :=
          (F.continuous.comp (by fun_prop : Continuous (fun s : ℝ => A * s))).continuousOn
        have hhY (t : ℝ) (_ht : t ∈ Icc (-1 : ℝ) 1) : -B < h t 1 ∧ h t 1 < B :=
          abs_lt.mp (hbound (A * t))
        have hvX (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -R < v t 0 ∧ v t 0 < R :=
          abs_lt.mp (hMv t ht)
        have hh0 : h (-1) 0 ≤ -R := by simpa [h] using hA0.le
        have hh1 : R ≤ h 1 0 := by simpa [h] using hA1.le
        have hv0' : v (-1) 1 ≤ -B := by simpa [hv0] using hu
        have hv1' : B ≤ v 1 1 := by simpa [hv1] using hw
        obtain ⟨s, hs, t, ht, he⟩ := crossing_strip (by linarith : -R < R)
          (by linarith : -B < B) h v hhc hv hhY hvX hh0 hh1 hv0' hv1'
        exact hvmem t ht ⟨A * s, he⟩
      have orient 
          (L U V A B : Set Plane)
          (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
          (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
          (hA : IsConnected A) (hB : IsConnected B) (hAL : A ⊆ Lᶜ) (hBL : B ⊆ Lᶜ)
          (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ JoinedIn Lᶜ a b) :
          (A ⊆ U ∧ B ⊆ V) ∨ (A ⊆ V ∧ B ⊆ U) := by
        have hAs : A ⊆ U ∪ V := hpart.symm ▸ hAL
        have hBs : B ⊆ U ∪ V := hpart.symm ▸ hBL
        have hUL : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
        have hVL : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
        obtain ⟨a, ha⟩ := hA.nonempty
        obtain ⟨b, hb⟩ := hB.nonempty
        rcases hA.isPreconnected.subset_or_subset hU hV hd hAs with hAU | hAV
        · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
          · exact False.elim (hno a ha b hb
              (((hU.isConnected_iff_isPathConnected.mp hcU).joinedIn a (hAU ha) b (hBU hb)).mono hUL))
          · exact Or.inl ⟨hAU, hBV⟩
        · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
          · exact Or.inr ⟨hAV, hBU⟩
          · exact False.elim (hno a ha b hb
              (((hV.isConnected_iff_isPathConnected.mp hcV).joinedIn a (hAV ha) b (hBV hb)).mono hVL))
      have no_cycle (e : Plane ≃ₜ Plane)
          (L U V A B : Set Plane) (hL : IsConnected L)
          (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
          (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
          (hfU : frontier U = L) (hfV : frontier V = L)
          (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A ⊆ U) (hBV : B ⊆ V)
          (heA : e '' A = A) (heB : e '' B = B)
          (n : ℕ) (hn : 0 < n) (hperiod : e^[n] '' L = L) :
          ¬ Disjoint L (e '' L) := by
        have ordered
            (L₁ L₂ U₁ V₁ U₂ V₂ : Set Plane)
            (hL₁ : L₁.Nonempty) (hL₂ : IsConnected L₂)
            (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
            (hcU₁ : IsConnected U₁) (hcV₁ : IsConnected V₁)
            (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
            (hp₁ : U₁ ∪ V₁ = L₁ᶜ) (hp₂ : U₂ ∪ V₂ = L₂ᶜ)
            (hfU₁ : frontier U₁ = L₁) (hfV₁ : frontier V₁ = L₁)
            (hdL : Disjoint L₁ L₂)
            (hcommonU : (U₁ ∩ U₂).Nonempty) (hcommonV : (V₁ ∩ V₂).Nonempty) :
            U₁ ⊂ U₂ ∨ U₂ ⊂ U₁ := by
          have hU₁L : Disjoint U₁ L₁ := by
            apply disjoint_left.mpr
            intro x hx hL
            exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inl hx) hL
          have hV₁L : Disjoint V₁ L₁ := by
            apply disjoint_left.mpr
            intro x hx hL
            exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inr hx) hL
          have hU₂L : Disjoint U₂ L₂ := by
            apply disjoint_left.mpr
            intro x hx hL
            exact (show x ∈ L₂ᶜ from hp₂ ▸ Or.inl hx) hL
          have hclU : closure U₁ = U₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfU₁]
          have hclV : closure V₁ = V₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfV₁]
          have hsub : L₂ ⊆ U₁ ∪ V₁ := by
            rw [hp₁]
            exact fun x hx h => disjoint_left.mp hdL h hx
          rcases hL₂.isPreconnected.subset_or_subset hU₁ hV₁ hd₁ hsub with hLU | hLV
          · have hsubcl : closure V₁ ⊆ U₂ ∪ V₂ := by
              rw [hp₂, hclV]
              rintro x (hx | hx) hL
              · exact disjoint_left.mp hd₁ (hLU hL) hx
              · exact disjoint_left.mp hdL hx hL
            have hcl : closure V₁ ⊆ V₂ := by
              rcases hcV₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
              · obtain ⟨x, hx₁, hx₂⟩ := hcommonV
                exact False.elim (disjoint_left.mp hd₂ (h (subset_closure hx₁)) hx₂)
              · exact h
            have hUU : U₂ ⊆ U₁ := by
              intro x hx
              by_contra hx₁
              have hxcl : x ∈ closure V₁ := by
                rw [hclV]
                by_cases hxL : x ∈ L₁
                · exact Or.inr hxL
                · have hside : x ∈ U₁ ∪ V₁ := hp₁.symm ▸ hxL
                  exact Or.inl (hside.resolve_left hx₁)
              exact disjoint_left.mp hd₂ hx (hcl hxcl)
            right
            apply Set.ssubset_iff_subset_ne.mpr
            refine ⟨hUU, ?_⟩
            intro he
            obtain ⟨x, hx⟩ := hL₂.nonempty
            exact disjoint_left.mp hU₂L (he.symm ▸ hLU hx) hx
          · have hsubcl : closure U₁ ⊆ U₂ ∪ V₂ := by
              rw [hp₂, hclU]
              rintro x (hx | hx) hL
              · exact disjoint_left.mp hd₁ hx (hLV hL)
              · exact disjoint_left.mp hdL hx hL
            have hcl : closure U₁ ⊆ U₂ := by
              rcases hcU₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
              · exact h
              · obtain ⟨x, hx₁, hx₂⟩ := hcommonU
                exact False.elim (disjoint_left.mp hd₂ hx₂ (h (subset_closure hx₁)))
            left
            apply Set.ssubset_iff_subset_ne.mpr
            refine ⟨subset_closure.trans hcl, ?_⟩
            intro he
            obtain ⟨x, hx⟩ := hL₁
            have hxc : x ∈ closure U₁ := hclU.symm ▸ Or.inr hx
            exact disjoint_left.mp hU₁L (he.symm ▸ hcl hxc) hx
        have fixed_iter (S : Set Plane) (hS : e '' S = S) (k : ℕ) : e^[k] '' S = S := by
          rw [Set.image_iterate_eq]
          induction k with
          | zero => rfl
          | succ k hk => simpa only [Function.iterate_succ_apply', hk] using hS
        have hmarker (S W : Set Plane) (hS : S.Nonempty) (hSW : S ⊆ W)
            (hfix : e '' S = S) : (W ∩ e '' W).Nonempty := by
          obtain ⟨x, hx⟩ := hS
          refine ⟨e x, ?_, ⟨x, hSW hx, rfl⟩⟩
          exact hSW (hfix ▸ mem_image_of_mem e hx)
        have hUsub : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
        have hVsub : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
        have hUP : e^[n] '' U ⊆ U := by
          have hsub : e^[n] '' U ⊆ U ∪ V := by
            rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
            exact Set.image_mono hUsub
          rcases (hcU.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
            hU hV hd hsub with h | h
          · exact h
          · obtain ⟨a, ha⟩ := hA
            have hai : a ∈ e^[n] '' A := (fixed_iter A heA n).symm ▸ ha
            exact False.elim (disjoint_left.mp hd (hAU ha) (h (Set.image_mono hAU hai)))
        have hVP : e^[n] '' V ⊆ V := by
          have hsub : e^[n] '' V ⊆ U ∪ V := by
            rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
            exact Set.image_mono hVsub
          rcases (hcV.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
            hU hV hd hsub with h | h
          · obtain ⟨b, hb⟩ := hB
            have hbi : b ∈ e^[n] '' B := (fixed_iter B heB n).symm ▸ hb
            exact False.elim (disjoint_left.mp hd (h (Set.image_mono hBV hbi)) (hBV hb))
          · exact h
        have hperiodU : e^[n] '' U = U := by
          apply Subset.antisymm hUP
          intro x hx
          have hxp : x ∈ e^[n] '' U ∪ e^[n] '' V := by
            rw [← Set.image_union, hpart, Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩, hperiod]
            exact hUsub hx
          exact hxp.resolve_right (fun h => disjoint_left.mp hd hx (hVP h))
        intro hdisL
        have hpartE : (e '' U) ∪ (e '' V) = (e '' L)ᶜ := by
          rw [← Set.image_union, hpart, e.image_compl]
        have horder := ordered L (e '' L) U V (e '' U) (e '' V)
          hL.nonempty (hL.image _ e.continuous.continuousOn) hU hV
          (e.isOpenMap _ hU) (e.isOpenMap _ hV) hcU hcV hd
          ((Set.disjoint_image_iff e.injective).mpr hd) hpart hpartE hfU hfV hdisL
          (hmarker A U hA hAU heA) (hmarker B V hB hBV heB)
        have hmono : StrictMono (Set.image e) := e.injective.image_strictMono
        have hp : (Set.image e)^[n] U = U := by simpa only [← Set.image_iterate_eq] using hperiodU
        rcases horder with h | h
        · have hh := hmono.strictMono_iterate_of_lt_map h hn
          simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh
        · have hh := hmono.strictAnti_iterate_of_map_lt h hn
          simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh
      let L := Set.range F
      let A : Set Plane := {z | z 1 < -B}
      let D : Set Plane := {z | B < z 1}
      have hAn : A.Nonempty := ⟨!₂[0, -B - 1], by dsimp [A]; linarith⟩
      have hDn : D.Nonempty := ⟨!₂[0, B + 1], by dsimp [D]; linarith⟩
      have hAc : IsConnected A := by
        apply Convex.isConnected _ hAn
        exact (convex_Iio (-B)).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
      have hDc : IsConnected D := by
        apply Convex.isConnected _ hDn
        exact (convex_Ioi B).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
      have hAL : A ⊆ Lᶜ := by
        rintro z hz ⟨x, rfl⟩
        have hh := (abs_lt.mp (hbound x)).1
        exact (not_lt_of_ge hh.le) hz
      have hDL : D ⊆ Lᶜ := by
        rintro z hz ⟨x, rfl⟩
        have hh := (abs_lt.mp (hbound x)).2
        exact (not_lt_of_ge hh.le) hz
      obtain ⟨a, ha⟩ := hAn
      have hJ := line_jordan F hF hinj a (hAL ha)
      obtain ⟨U, V, hU, hV, hcU, hcV, hd, hpart, hfU, hfV⟩ := split L a (hAL ha) hJ
      have hno (a : Plane) (ha : a ∈ A) (b : Plane) (hb : b ∈ D) : ¬ JoinedIn Lᶜ a b :=
        no_crossing F B hB hbound hends a b ha.le hb.le
      let e : Plane ≃ₜ Plane := Homeomorph.addRight !₂[p, 0]
      have heA : e '' A = A := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa [e, A] using hx
        · intro hz
          refine ⟨z - !₂[p, 0], ?_, ?_⟩
          · simpa [A] using hz
          · simp [e]
      have heD : e '' D = D := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa [e, D] using hx
        · intro hz
          refine ⟨z - !₂[p, 0], ?_, ?_⟩
          · simpa [D] using hz
          · simp [e]
      have hLc : IsConnected L := isConnected_range F.continuous
      have hp : e^[n] '' L = L := hperiod
      rcases orient L U V A D hU hV hcU hcV hd hpart hAc hDc hAL hDL hno with h | h
      · exact no_cycle e L U V A D hLc hU hV hcU hcV hd hpart hfU hfV
          hAc.nonempty hDn h.1 h.2 heA heD n hn hp
      · exact no_cycle e L V U A D hLc hV hU hcV hcU hd.symm
          (by simpa only [union_comm] using hpart) hfV hfU
          hAc.nonempty hDn h.1 h.2 heA heD n hn hp
    have hyperiod : Function.Periodic (fun x => F x 1) T := by
      intro x
      have hh := congrArg (fun z : Plane => z 1) (hperiod 1 x)
      simpa using hh
    have hycont : Continuous (fun x => F x 1) := (EuclideanSpace.proj 1).continuous.comp F.continuous
    have hcompact : IsCompact (Set.range (fun x => F x 1)) := by
      rw [← hyperiod.image_Icc hT 0]
      exact isCompact_Icc.image hycont
    obtain ⟨M, hM⟩ := (hcompact.image continuous_abs).bddAbove
    let B := max M 0 + 1
    have hB : 0 < B := by dsimp [B]; positivity
    have hbound (x : ℝ) : |F x 1| < B := by
      have hh := hM ⟨F x 1, ⟨x, rfl⟩, rfl⟩
      dsimp [B]
      linarith [le_max_left M 0]
    have hq : 0 < (n : ℝ) * p := mul_pos (by exact_mod_cast hn) hp
    have hends (R : ℝ) : ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0 := by
      obtain ⟨N, hN⟩ := exists_nat_gt ((R + |F 0 0|) / ((n : ℝ) * p))
      have hNm := (div_lt_iff₀ hq).mp hN
      refine ⟨(N : ℝ) * T, ?_, ?_⟩
      · have hh := congrArg (fun z : Plane => z 0) (hperiod (-(N : ℤ)) 0)
        simp only [Int.cast_neg, Int.cast_natCast, zero_add, neg_mul] at hh
        change F (-((N : ℝ) * T)) 0 = F 0 0 + -((N : ℝ) * ((n : ℝ) * p)) at hh
        linarith [le_abs_self (F 0 0)]
      · have hh := congrArg (fun z : Plane => z 0) (hperiod (N : ℤ) 0)
        simp only [Int.cast_natCast, zero_add] at hh
        change F ((N : ℝ) * T) 0 = F 0 0 + (N : ℝ) * ((n : ℝ) * p) at hh
        linarith [neg_abs_le (F 0 0)]
    have hiter (k : ℕ) (z : Plane) : (fun z : Plane => z + !₂[p, 0])^[k] z =
        z + !₂[(k : ℝ) * p, 0] := by
      induction k with
      | zero => simp
      | succ k hk =>
        rw [Function.iterate_succ_apply', hk]
        ext i
        fin_cases i <;> simp <;> ring
    have hsetperiod : (fun z : Plane => z + !₂[p, 0])^[n] '' Set.range F = Set.range F := by
      ext z
      constructor
      · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
        refine ⟨x + T, ?_⟩
        rw [hiter]
        simpa using hperiod 1 x
      · rintro ⟨x, rfl⟩
        refine ⟨F (x - T), ⟨x - T, rfl⟩, ?_⟩
        rw [hiter]
        have hh := hperiod 1 (x - T)
        simpa using hh.symm
    exact horizontal F hF hinj B hB hbound hends p n hn hsetperiod
  obtain ⟨e, heproper, heinj, he0, he1, hedir⟩ := normalize a b hab
  let G : C(ℝ, Plane) := ⟨fun x => e (F x), e.continuous_of_finiteDimensional.comp F.continuous⟩
  have hGp : IsProperMap G := heproper.comp hF
  have hGi : Function.Injective G := heinj.comp hinj
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
  have hGperiod (k : ℤ) (x : ℝ) : G (x + (k : ℝ) * T) =
      G x + !₂[(k : ℝ) * ((n : ℝ) * (a ^ 2 + b ^ 2)), 0] := by
    change e (F (x + (k : ℝ) * T)) = e (F x) + _
    rw [hperiod, map_add, hedir]
    congr 1
    ext i
    fin_cases i <;> dsimp <;> ring
  have hnondis := horizontal G hGp hGi T (a ^ 2 + b ^ 2) hT hpos n hn hGperiod
  intro hdis
  apply hnondis
  apply Set.disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, ⟨t, rfl⟩, heq⟩
  have hevec : e (a, b) = !₂[a ^ 2 + b ^ 2, 0] := by simpa using hedir 1
  have hxy : F t + (a, b) = F x := by
    apply heinj
    rw [map_add, hevec]
    exact heq
  exact Set.disjoint_left.mp hdis ⟨x, rfl⟩ ⟨F t, ⟨t, rfl⟩, hxy⟩

theorem torus_deck_monodromy_primitive (F : C(ℝ, ℝ × ℝ)) (m n : ℤ)
    (hproper : IsProperMap F) (hinj : Function.Injective F)
    (hnonzero : m ≠ 0 ∨ n ≠ 0)
    (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
      ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
       (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi)))
    (hcollision : ∀ (x y : ℝ) (a b : ℤ),
      F x = ((F y).1 + (a : ℝ) * (2 * Real.pi),
        (F y).2 + (b : ℝ) * (2 * Real.pi)) →
      ∃ k : ℤ, a = k * m ∧ b = k * n) :
    m.gcd n = 1 := by
  have root_meets (F : C(ℝ, ℝ × ℝ)) (hF : IsProperMap F) (hinj : Function.Injective F)
      (T a b : ℝ) (hT : 0 < T) (hab : a ≠ 0 ∨ b ≠ 0) (n : ℕ) (hn : 0 < n)
      (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * T) =
        F x + ((k : ℝ) * (n : ℝ) * a, (k : ℝ) * (n : ℝ) * b)) :
      ¬ Disjoint (Set.range F) ((fun z : ℝ × ℝ => z + (a, b)) '' Set.range F) := by
    have normalize (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
        ∃ e : (ℝ × ℝ) →ₗ[ℝ] Schoenflies.Plane,
          IsProperMap e ∧ Function.Injective e ∧
          (∀ x, e x 0 = a * x.1 + b * x.2) ∧
          (∀ x, e x 1 = -b * x.1 + a * x.2) ∧
          (∀ k : ℝ, e (k * a, k * b) = !₂[k * (a ^ 2 + b ^ 2), 0]) := by
      let e : (ℝ × ℝ) →ₗ[ℝ] Schoenflies.Plane := {
        toFun := fun x => !₂[a * x.1 + b * x.2, -b * x.1 + a * x.2]
        map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
        map_smul' := by intro c x; ext i; fin_cases i <;> simp <;> ring }
      have hpos : 0 < a ^ 2 + b ^ 2 := by
        rcases hab with ha | hb
        · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
        · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
      have hi : Function.Injective e := by
        intro x y he
        have h0 : a * x.1 + b * x.2 = a * y.1 + b * y.2 := congrArg (fun z => z 0) he
        have h1 : -b * x.1 + a * x.2 = -b * y.1 + a * y.2 := congrArg (fun z => z 1) he
        have hdx : (a ^ 2 + b ^ 2) * (x.1 - y.1) = 0 := by
          linear_combination a * h0 - b * h1
        have hdy : (a ^ 2 + b ^ 2) * (x.2 - y.2) = 0 := by
          linear_combination b * h0 + a * h1
        exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hdx).resolve_left (ne_of_gt hpos)))
          (sub_eq_zero.mp ((mul_eq_zero.mp hdy).resolve_left (ne_of_gt hpos)))
      refine ⟨e, (e.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)).isProperMap, hi, fun _ => rfl, fun _ => rfl, ?_⟩
      intro k
      ext i
      fin_cases i <;> dsimp [e] <;> ring
    have horizontal (F : C(ℝ, Plane)) (hF : IsProperMap F) (hinj : Function.Injective F)
        (T p : ℝ) (hT : 0 < T) (hp : 0 < p) (n : ℕ) (hn : 0 < n)
        (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * T) =
          F x + !₂[(k : ℝ) * ((n : ℝ) * p), 0]) :
        ¬ Disjoint (Set.range F) ((fun z : Plane => z + !₂[p, 0]) '' Set.range F) := by
      have horizontal (F : C(ℝ, Plane)) (hF : IsProperMap F) (hinj : Function.Injective F)
          (B : ℝ) (hB : 0 < B) (hbound : ∀ x : ℝ, |F x 1| < B)
          (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
          (p : ℝ) (n : ℕ) (hn : 0 < n)
          (hperiod : (fun z : Plane => z + !₂[p, 0])^[n] '' Set.range F = Set.range F) :
          ¬ Disjoint (Set.range F) ((fun z : Plane => z + !₂[p, 0]) '' Set.range F) := by
        have line_jordan (F : C(ℝ, Schoenflies.Plane)) (hF : IsProperMap F)
            (hinj : Function.Injective F) (a : Schoenflies.Plane)
            (ha : a ∉ Set.range F) :
            Schoenflies.IsJordanCurve (insert a (Schoenflies.invert a '' Set.range F)) := by
          let q : OnePoint ℝ → Schoenflies.Plane :=
            invertAtInfinity a ∘ OnePoint.map F
          have hmap : Continuous (OnePoint.map F) := by
            apply OnePoint.continuous_map F.continuous
            simpa only [coclosedCompact_eq_cocompact] using
              (isProperMap_iff_tendsto_cocompact.mp hF).2
          have hq : Continuous q := by
            apply continuous_iff_continuousAt.mpr
            intro z
            cases z with
            | infty =>
              exact (invertAtInfinity_continuousAt_infty a).comp hmap.continuousAt
            | coe x =>
              apply OnePoint.continuousAt_coe.mpr
              change ContinuousAt (fun x : ℝ => Schoenflies.invert a (F x)) x
              exact (Schoenflies.continuousAt_invert (by
                intro h; exact ha ⟨x, h⟩)).comp F.continuous.continuousAt
          have hqi : Function.Injective q := by
            intro x y hxy
            cases x with
            | infty =>
              cases y with
              | infty => rfl
              | coe y =>
                change a = Schoenflies.invert a (F y) at hxy
                exact False.elim (ha ⟨y, Schoenflies.invert_eq_center_iff.mp hxy.symm⟩)
            | coe x =>
              cases y with
              | infty =>
                change Schoenflies.invert a (F x) = a at hxy
                exact False.elim (ha ⟨x, Schoenflies.invert_eq_center_iff.mp hxy⟩)
              | coe y =>
                change Schoenflies.invert a (F x) = Schoenflies.invert a (F y) at hxy
                exact congrArg OnePoint.some (hinj (Schoenflies.invert_injective a hxy))
          let e : OnePoint ℝ ≃ₜ Circle :=
            (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).trans
              ClassificationJordanCurve.Arcs.circleHomeoSphere.symm
          let r : C(Circle, Schoenflies.Plane) := ⟨q ∘ e.symm, hq.comp e.symm.continuous⟩
          have hr : IsEmbedding r := (r.continuous.isClosedEmbedding (hqi.comp e.symm.injective)).isEmbedding
          have hrange : Set.range r = insert a (Schoenflies.invert a '' Set.range F) := by
            ext z
            constructor
            · rintro ⟨x, rfl⟩
              change q (e.symm x) ∈ _
              generalize e.symm x = y
              cases y with
              | infty => exact Set.mem_insert a _
              | coe t => exact Set.mem_insert_of_mem _ ⟨F t, ⟨t, rfl⟩, rfl⟩
            · intro hz
              rcases hz with hz | ⟨w, ⟨t, rfl⟩, rfl⟩
              · subst z
                exact ⟨e OnePoint.infty, by simp [r, q, invertAtInfinity]⟩
              · exact ⟨e (OnePoint.some t), by simp [r, q, invertAtInfinity]⟩
          rw [← hrange]
          exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
        have split (L : Set Plane) (a : Plane) (ha : a ∉ L)
            (hJ : IsJordanCurve (insert a (invert a '' L))) :
            ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
              Disjoint U V ∧ U ∪ V = Lᶜ ∧ frontier U = L ∧ frontier V = L := by
          let C := insert a (invert a '' L)
          have hsep : IsSeparating C := jordan_curve_theorem hJ
          have haC : a ∈ C := Set.mem_insert a _
          have hain : a ∉ inside C := fun h => h.1 haC
          have haout : a ∉ outside C := fun h => h.1 haC
          let U := invert a '' inside C
          let V := invert a '' outside C ∪ {a}
          have hUopen : IsOpen U := isOpen_invert_image hsep.isOpen_inside hain
          have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
            intro z hz
            simpa only [mem_compl_iff, mem_singleton_iff] using
              (show z ≠ a from fun h => haout (h ▸ hz))
          have hinc : inside C ⊆ ({a}ᶜ : Set Plane) := by
            intro z hz
            simpa only [mem_compl_iff, mem_singleton_iff] using
              (show z ≠ a from fun h => hain (h ▸ hz))
          have hUconn : IsConnected U :=
            hsep.isConnected_inside.image _ ((continuousOn_invert a).mono hinc)
          obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
          have hTopen : IsOpen (invert a '' outside C) :=
            isOpen_invert_image hsep.isOpen_outside haout
          have hVball : ball a R⁻¹ ⊆ V := by
            intro z hz
            rcases eq_or_ne z a with rfl | hza
            · exact Or.inr rfl
            · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
              have hpos : 0 < dist z a := dist_pos.2 hza
              rw [mem_compl_iff, mem_closedBall, dist_invert_center]
              exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
          have hVopen : IsOpen V := by
            have hrw : V = invert a '' outside C ∪ ball a R⁻¹ := by
              refine Subset.antisymm (union_subset subset_union_left ?_)
                (union_subset subset_union_left hVball)
              rintro z rfl
              exact Or.inr (mem_ball_self (by positivity))
            rw [hrw]
            exact hTopen.union isOpen_ball
          have hacl : a ∈ closure (invert a '' outside C) := by
            rw [Metric.mem_closure_iff]
            intro e he
            obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
              by_contra hcon
              push Not at hcon
              exact hsep.not_isBounded_outside
                ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
            refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
            rw [dist_comm, dist_invert_center]
            exact inv_lt_of_inv_lt₀ he hzfar
          have hVconn : IsConnected V := by
            refine ⟨⟨a, Or.inr rfl⟩, ?_⟩
            exact (hsep.isConnected_outside.image _
              ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
              (union_subset subset_closure (by rintro z rfl; exact hacl))
          have hdis : Disjoint U V := by
            apply Set.disjoint_left.mpr
            rintro z ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | he)
            · have he' := invert_injective a he
              exact Set.disjoint_left.mp disjoint_inside_outside hx (he' ▸ hy)
            · exact hain ((invert_eq_center_iff.mp he) ▸ hx)
          have hinv (z : Plane) : invert a z ∈ C ↔ z = a ∨ z ∈ L := by
            dsimp [C]
            simp only [mem_insert_iff, invert_eq_center_iff]
            rw [Set.mem_image]
            constructor
            · rintro (h | ⟨x, hx, he⟩)
              · exact Or.inl h
              · exact Or.inr ((invert_injective a he) ▸ hx)
            · rintro (h | h)
              · exact Or.inl h
              · exact Or.inr ⟨z, h, rfl⟩
          have hpart : U ∪ V = Lᶜ := by
            ext z
            constructor
            · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl)
              · intro hz
                have := (hinv (invert a x)).mpr (Or.inr hz)
                rw [invert_invert] at this
                exact hx.1 this
              · intro hz
                have := (hinv (invert a x)).mpr (Or.inr hz)
                rw [invert_invert] at this
                exact hx.1 this
              · exact ha
            · intro hz
              by_cases hza : z = a
              · exact Or.inr (Or.inr hza)
              · have hzC : invert a z ∉ C := by simpa [hinv, hza] using hz
                have hzside : invert a z ∈ inside C ∪ outside C := by
                  rwa [inside_union_outside]
                rcases hzside with hu | hv
                · exact Or.inl ⟨invert a z, hu, invert_invert a z⟩
                · exact Or.inr (Or.inl ⟨invert a z, hv, invert_invert a z⟩)
          have hUL : Disjoint U L := by
            apply Set.disjoint_left.mpr
            intro x hx hL
            exact (show x ∈ Lᶜ from hpart ▸ Or.inl hx) hL
          have hVL : Disjoint V L := by
            apply Set.disjoint_left.mpr
            intro x hx hL
            exact (show x ∈ Lᶜ from hpart ▸ Or.inr hx) hL
          have hfrontU : frontier U = L := by
            apply Subset.antisymm
            · intro x hx
              by_contra hxL
              have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
              rcases hside with hu | hv
              · exact (hUopen.frontier_eq ▸ hx).2 hu
              · exact Set.disjoint_right.mp (hdis.closure_left hVopen) hv (frontier_subset_closure hx)
            · intro x hx
              have hxa : x ≠ a := fun h => ha (h ▸ hx)
              have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
              have hixcl : invert a x ∈ closure (inside C) := by
                rw [← hsep.frontier_inside] at hixC
                exact frontier_subset_closure hixC
              rw [hUopen.frontier_eq]
              refine ⟨?_, fun h => Set.disjoint_left.mp hUL h hx⟩
              simpa only [invert_invert] using
                mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
          have hfrontV : frontier V = L := by
            apply Subset.antisymm
            · intro x hx
              by_contra hxL
              have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
              rcases hside with hu | hv
              · exact Set.disjoint_left.mp (hdis.closure_right hUopen) hu (frontier_subset_closure hx)
              · exact (hVopen.frontier_eq ▸ hx).2 hv
            · intro x hx
              have hxa : x ≠ a := fun h => ha (h ▸ hx)
              have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
              have hixcl : invert a x ∈ closure (outside C) := by
                rw [← hsep.frontier_outside] at hixC
                exact frontier_subset_closure hixC
              rw [hVopen.frontier_eq]
              refine ⟨?_, fun h => Set.disjoint_left.mp hVL h hx⟩
              apply closure_mono (show invert a '' outside C ⊆ V from subset_union_left)
              simpa only [invert_invert] using
                mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
          exact ⟨U, V, hUopen, hVopen, hUconn, hVconn, hdis, hpart, hfrontU, hfrontV⟩
        have no_crossing (F : C(ℝ, Plane)) (B : ℝ) (hB : 0 < B)
            (hbound : ∀ x : ℝ, |F x 1| < B)
            (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
            (u w : Plane) (hu : u 1 ≤ -B) (hw : B ≤ w 1) :
            ¬ JoinedIn (Set.range F)ᶜ u w := by
          have crossing_strip {a b c d : ℝ} (hab : a < b) (hcd : c < d)
              (h v : ℝ → Plane)
              (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
              (hhY : ∀ t ∈ Icc (-1 : ℝ) 1, c < h t 1 ∧ h t 1 < d)
              (hvX : ∀ t ∈ Icc (-1 : ℝ) 1, a < v t 0 ∧ v t 0 < b)
              (hh1 : h (-1) 0 ≤ a) (hh2 : b ≤ h 1 0)
              (hv1 : v (-1) 1 ≤ c) (hv2 : d ≤ v 1 1) :
              ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, h s = v t := by
            let H : ℝ → Plane := fun s => !₂[max a (min b (h s 0)), h s 1]
            let V : ℝ → Plane := fun t => !₂[v t 0, max c (min d (v t 1))]
            have hH : ContinuousOn H (Icc (-1) 1) := by
              apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
              apply continuousOn_pi.mpr
              intro i
              fin_cases i
              · exact (show Continuous (fun x : ℝ => max a (min b x)) by fun_prop).comp_continuousOn
                  ((EuclideanSpace.proj 0).continuous.comp_continuousOn hh)
              · exact (EuclideanSpace.proj 1).continuous.comp_continuousOn hh
            have hV : ContinuousOn V (Icc (-1) 1) := by
              apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
              apply continuousOn_pi.mpr
              intro i
              fin_cases i
              · exact (EuclideanSpace.proj 0).continuous.comp_continuousOn hv
              · exact (show Continuous (fun x : ℝ => max c (min d x)) by fun_prop).comp_continuousOn
                  ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv)
            have hHE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                H t 0 ∈ Icc a b ∧ H t 1 ∈ Icc c d := by
              exact ⟨⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩, (hhY t ht).1.le, (hhY t ht).2.le⟩
            have hVE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                V t 0 ∈ Icc a b ∧ V t 1 ∈ Icc c d := by
              exact ⟨⟨(hvX t ht).1.le, (hvX t ht).2.le⟩, le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
            have hH1 : H (-1) 0 = a := by
              dsimp [H]
              rw [min_eq_right (hh1.trans hab.le), max_eq_left hh1]
            have hH2 : H 1 0 = b := by
              dsimp [H]
              rw [min_eq_left hh2, max_eq_right hab.le]
            have hV1 : V (-1) 1 = c := by
              dsimp [V]
              rw [min_eq_right (hv1.trans hcd.le), max_eq_left hv1]
            have hV2 : V 1 1 = d := by
              dsimp [V]
              rw [min_eq_left hv2, max_eq_right hcd.le]
            obtain ⟨s, hs, t, ht, he⟩ := ClassificationJordanCurve.crossing ClassificationJordanCurve.Brouwer.brouwerFPT
              hab.le hcd.le H V hH hV hHE hVE hH1 hH2 hV1 hV2
            have clamp {l u x z : ℝ} (hlu : l < u) (hz : l < z ∧ z < u)
                (he : max l (min u x) = z) : x = z := by
              by_cases hx : x ≤ l
              · rw [min_eq_right (hx.trans hlu.le), max_eq_left hx] at he
                linarith [hz.1]
              · by_cases hxu : u ≤ x
                · rw [min_eq_left hxu, max_eq_right hlu.le] at he
                  linarith [hz.2]
                · rwa [min_eq_right (le_of_not_ge hxu), max_eq_right (le_of_not_ge hx)] at he
            refine ⟨s, hs, t, ht, ?_⟩
            have he0 := congrArg (fun p : Plane => p 0) he
            have he1 := congrArg (fun p : Plane => p 1) he
            ext i
            fin_cases i
            · exact clamp hab (hvX t ht) he0
            · exact (clamp hcd (hhY s hs) he1.symm).symm
          intro hjoin
          obtain ⟨v, hv, hv0, hv1, hvmem⟩ := ClassificationJordanCurve.arc_path hjoin
          have hvc : ContinuousOn (fun t : ℝ => |v t 0|) (Icc (-1) 1) :=
            continuous_abs.comp_continuousOn ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv)
          obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hvc).bddAbove
          let R := max M 0 + 1
          have hR : 0 < R := by dsimp [R]; positivity
          have hMv (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |v t 0| < R := by
            have hm := hM (Set.mem_image_of_mem _ ht)
            dsimp [R]
            linarith [le_max_left M 0]
          obtain ⟨A, hA0, hA1⟩ := hends R
          let h : ℝ → Plane := fun s => F (A * s)
          have hhc : ContinuousOn h (Icc (-1) 1) :=
            (F.continuous.comp (by fun_prop : Continuous (fun s : ℝ => A * s))).continuousOn
          have hhY (t : ℝ) (_ht : t ∈ Icc (-1 : ℝ) 1) : -B < h t 1 ∧ h t 1 < B :=
            abs_lt.mp (hbound (A * t))
          have hvX (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -R < v t 0 ∧ v t 0 < R :=
            abs_lt.mp (hMv t ht)
          have hh0 : h (-1) 0 ≤ -R := by simpa [h] using hA0.le
          have hh1 : R ≤ h 1 0 := by simpa [h] using hA1.le
          have hv0' : v (-1) 1 ≤ -B := by simpa [hv0] using hu
          have hv1' : B ≤ v 1 1 := by simpa [hv1] using hw
          obtain ⟨s, hs, t, ht, he⟩ := crossing_strip (by linarith : -R < R)
            (by linarith : -B < B) h v hhc hv hhY hvX hh0 hh1 hv0' hv1'
          exact hvmem t ht ⟨A * s, he⟩
        have orient 
            (L U V A B : Set Plane)
            (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
            (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
            (hA : IsConnected A) (hB : IsConnected B) (hAL : A ⊆ Lᶜ) (hBL : B ⊆ Lᶜ)
            (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ JoinedIn Lᶜ a b) :
            (A ⊆ U ∧ B ⊆ V) ∨ (A ⊆ V ∧ B ⊆ U) := by
          have hAs : A ⊆ U ∪ V := hpart.symm ▸ hAL
          have hBs : B ⊆ U ∪ V := hpart.symm ▸ hBL
          have hUL : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
          have hVL : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
          obtain ⟨a, ha⟩ := hA.nonempty
          obtain ⟨b, hb⟩ := hB.nonempty
          rcases hA.isPreconnected.subset_or_subset hU hV hd hAs with hAU | hAV
          · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
            · exact False.elim (hno a ha b hb
                (((hU.isConnected_iff_isPathConnected.mp hcU).joinedIn a (hAU ha) b (hBU hb)).mono hUL))
            · exact Or.inl ⟨hAU, hBV⟩
          · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
            · exact Or.inr ⟨hAV, hBU⟩
            · exact False.elim (hno a ha b hb
                (((hV.isConnected_iff_isPathConnected.mp hcV).joinedIn a (hAV ha) b (hBV hb)).mono hVL))
        have no_cycle (e : Plane ≃ₜ Plane)
            (L U V A B : Set Plane) (hL : IsConnected L)
            (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
            (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
            (hfU : frontier U = L) (hfV : frontier V = L)
            (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A ⊆ U) (hBV : B ⊆ V)
            (heA : e '' A = A) (heB : e '' B = B)
            (n : ℕ) (hn : 0 < n) (hperiod : e^[n] '' L = L) :
            ¬ Disjoint L (e '' L) := by
          have ordered
              (L₁ L₂ U₁ V₁ U₂ V₂ : Set Plane)
              (hL₁ : L₁.Nonempty) (hL₂ : IsConnected L₂)
              (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
              (hcU₁ : IsConnected U₁) (hcV₁ : IsConnected V₁)
              (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
              (hp₁ : U₁ ∪ V₁ = L₁ᶜ) (hp₂ : U₂ ∪ V₂ = L₂ᶜ)
              (hfU₁ : frontier U₁ = L₁) (hfV₁ : frontier V₁ = L₁)
              (hdL : Disjoint L₁ L₂)
              (hcommonU : (U₁ ∩ U₂).Nonempty) (hcommonV : (V₁ ∩ V₂).Nonempty) :
              U₁ ⊂ U₂ ∨ U₂ ⊂ U₁ := by
            have hU₁L : Disjoint U₁ L₁ := by
              apply disjoint_left.mpr
              intro x hx hL
              exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inl hx) hL
            have hV₁L : Disjoint V₁ L₁ := by
              apply disjoint_left.mpr
              intro x hx hL
              exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inr hx) hL
            have hU₂L : Disjoint U₂ L₂ := by
              apply disjoint_left.mpr
              intro x hx hL
              exact (show x ∈ L₂ᶜ from hp₂ ▸ Or.inl hx) hL
            have hclU : closure U₁ = U₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfU₁]
            have hclV : closure V₁ = V₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfV₁]
            have hsub : L₂ ⊆ U₁ ∪ V₁ := by
              rw [hp₁]
              exact fun x hx h => disjoint_left.mp hdL h hx
            rcases hL₂.isPreconnected.subset_or_subset hU₁ hV₁ hd₁ hsub with hLU | hLV
            · have hsubcl : closure V₁ ⊆ U₂ ∪ V₂ := by
                rw [hp₂, hclV]
                rintro x (hx | hx) hL
                · exact disjoint_left.mp hd₁ (hLU hL) hx
                · exact disjoint_left.mp hdL hx hL
              have hcl : closure V₁ ⊆ V₂ := by
                rcases hcV₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
                · obtain ⟨x, hx₁, hx₂⟩ := hcommonV
                  exact False.elim (disjoint_left.mp hd₂ (h (subset_closure hx₁)) hx₂)
                · exact h
              have hUU : U₂ ⊆ U₁ := by
                intro x hx
                by_contra hx₁
                have hxcl : x ∈ closure V₁ := by
                  rw [hclV]
                  by_cases hxL : x ∈ L₁
                  · exact Or.inr hxL
                  · have hside : x ∈ U₁ ∪ V₁ := hp₁.symm ▸ hxL
                    exact Or.inl (hside.resolve_left hx₁)
                exact disjoint_left.mp hd₂ hx (hcl hxcl)
              right
              apply Set.ssubset_iff_subset_ne.mpr
              refine ⟨hUU, ?_⟩
              intro he
              obtain ⟨x, hx⟩ := hL₂.nonempty
              exact disjoint_left.mp hU₂L (he.symm ▸ hLU hx) hx
            · have hsubcl : closure U₁ ⊆ U₂ ∪ V₂ := by
                rw [hp₂, hclU]
                rintro x (hx | hx) hL
                · exact disjoint_left.mp hd₁ hx (hLV hL)
                · exact disjoint_left.mp hdL hx hL
              have hcl : closure U₁ ⊆ U₂ := by
                rcases hcU₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
                · exact h
                · obtain ⟨x, hx₁, hx₂⟩ := hcommonU
                  exact False.elim (disjoint_left.mp hd₂ hx₂ (h (subset_closure hx₁)))
              left
              apply Set.ssubset_iff_subset_ne.mpr
              refine ⟨subset_closure.trans hcl, ?_⟩
              intro he
              obtain ⟨x, hx⟩ := hL₁
              have hxc : x ∈ closure U₁ := hclU.symm ▸ Or.inr hx
              exact disjoint_left.mp hU₁L (he.symm ▸ hcl hxc) hx
          have fixed_iter (S : Set Plane) (hS : e '' S = S) (k : ℕ) : e^[k] '' S = S := by
            rw [Set.image_iterate_eq]
            induction k with
            | zero => rfl
            | succ k hk => simpa only [Function.iterate_succ_apply', hk] using hS
          have hmarker (S W : Set Plane) (hS : S.Nonempty) (hSW : S ⊆ W)
              (hfix : e '' S = S) : (W ∩ e '' W).Nonempty := by
            obtain ⟨x, hx⟩ := hS
            refine ⟨e x, ?_, ⟨x, hSW hx, rfl⟩⟩
            exact hSW (hfix ▸ mem_image_of_mem e hx)
          have hUsub : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
          have hVsub : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
          have hUP : e^[n] '' U ⊆ U := by
            have hsub : e^[n] '' U ⊆ U ∪ V := by
              rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
              exact Set.image_mono hUsub
            rcases (hcU.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
              hU hV hd hsub with h | h
            · exact h
            · obtain ⟨a, ha⟩ := hA
              have hai : a ∈ e^[n] '' A := (fixed_iter A heA n).symm ▸ ha
              exact False.elim (disjoint_left.mp hd (hAU ha) (h (Set.image_mono hAU hai)))
          have hVP : e^[n] '' V ⊆ V := by
            have hsub : e^[n] '' V ⊆ U ∪ V := by
              rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
              exact Set.image_mono hVsub
            rcases (hcV.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
              hU hV hd hsub with h | h
            · obtain ⟨b, hb⟩ := hB
              have hbi : b ∈ e^[n] '' B := (fixed_iter B heB n).symm ▸ hb
              exact False.elim (disjoint_left.mp hd (h (Set.image_mono hBV hbi)) (hBV hb))
            · exact h
          have hperiodU : e^[n] '' U = U := by
            apply Subset.antisymm hUP
            intro x hx
            have hxp : x ∈ e^[n] '' U ∪ e^[n] '' V := by
              rw [← Set.image_union, hpart, Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩, hperiod]
              exact hUsub hx
            exact hxp.resolve_right (fun h => disjoint_left.mp hd hx (hVP h))
          intro hdisL
          have hpartE : (e '' U) ∪ (e '' V) = (e '' L)ᶜ := by
            rw [← Set.image_union, hpart, e.image_compl]
          have horder := ordered L (e '' L) U V (e '' U) (e '' V)
            hL.nonempty (hL.image _ e.continuous.continuousOn) hU hV
            (e.isOpenMap _ hU) (e.isOpenMap _ hV) hcU hcV hd
            ((Set.disjoint_image_iff e.injective).mpr hd) hpart hpartE hfU hfV hdisL
            (hmarker A U hA hAU heA) (hmarker B V hB hBV heB)
          have hmono : StrictMono (Set.image e) := e.injective.image_strictMono
          have hp : (Set.image e)^[n] U = U := by simpa only [← Set.image_iterate_eq] using hperiodU
          rcases horder with h | h
          · have hh := hmono.strictMono_iterate_of_lt_map h hn
            simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh
          · have hh := hmono.strictAnti_iterate_of_map_lt h hn
            simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh
        let L := Set.range F
        let A : Set Plane := {z | z 1 < -B}
        let D : Set Plane := {z | B < z 1}
        have hAn : A.Nonempty := ⟨!₂[0, -B - 1], by dsimp [A]; linarith⟩
        have hDn : D.Nonempty := ⟨!₂[0, B + 1], by dsimp [D]; linarith⟩
        have hAc : IsConnected A := by
          apply Convex.isConnected _ hAn
          exact (convex_Iio (-B)).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
        have hDc : IsConnected D := by
          apply Convex.isConnected _ hDn
          exact (convex_Ioi B).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
        have hAL : A ⊆ Lᶜ := by
          rintro z hz ⟨x, rfl⟩
          have hh := (abs_lt.mp (hbound x)).1
          exact (not_lt_of_ge hh.le) hz
        have hDL : D ⊆ Lᶜ := by
          rintro z hz ⟨x, rfl⟩
          have hh := (abs_lt.mp (hbound x)).2
          exact (not_lt_of_ge hh.le) hz
        obtain ⟨a, ha⟩ := hAn
        have hJ := line_jordan F hF hinj a (hAL ha)
        obtain ⟨U, V, hU, hV, hcU, hcV, hd, hpart, hfU, hfV⟩ := split L a (hAL ha) hJ
        have hno (a : Plane) (ha : a ∈ A) (b : Plane) (hb : b ∈ D) : ¬ JoinedIn Lᶜ a b :=
          no_crossing F B hB hbound hends a b ha.le hb.le
        let e : Plane ≃ₜ Plane := Homeomorph.addRight !₂[p, 0]
        have heA : e '' A = A := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            simpa [e, A] using hx
          · intro hz
            refine ⟨z - !₂[p, 0], ?_, ?_⟩
            · simpa [A] using hz
            · simp [e]
        have heD : e '' D = D := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            simpa [e, D] using hx
          · intro hz
            refine ⟨z - !₂[p, 0], ?_, ?_⟩
            · simpa [D] using hz
            · simp [e]
        have hLc : IsConnected L := isConnected_range F.continuous
        have hp : e^[n] '' L = L := hperiod
        rcases orient L U V A D hU hV hcU hcV hd hpart hAc hDc hAL hDL hno with h | h
        · exact no_cycle e L U V A D hLc hU hV hcU hcV hd hpart hfU hfV
            hAc.nonempty hDn h.1 h.2 heA heD n hn hp
        · exact no_cycle e L V U A D hLc hV hU hcV hcU hd.symm
            (by simpa only [union_comm] using hpart) hfV hfU
            hAc.nonempty hDn h.1 h.2 heA heD n hn hp
      have hyperiod : Function.Periodic (fun x => F x 1) T := by
        intro x
        have hh := congrArg (fun z : Plane => z 1) (hperiod 1 x)
        simpa using hh
      have hycont : Continuous (fun x => F x 1) := (EuclideanSpace.proj 1).continuous.comp F.continuous
      have hcompact : IsCompact (Set.range (fun x => F x 1)) := by
        rw [← hyperiod.image_Icc hT 0]
        exact isCompact_Icc.image hycont
      obtain ⟨M, hM⟩ := (hcompact.image continuous_abs).bddAbove
      let B := max M 0 + 1
      have hB : 0 < B := by dsimp [B]; positivity
      have hbound (x : ℝ) : |F x 1| < B := by
        have hh := hM ⟨F x 1, ⟨x, rfl⟩, rfl⟩
        dsimp [B]
        linarith [le_max_left M 0]
      have hq : 0 < (n : ℝ) * p := mul_pos (by exact_mod_cast hn) hp
      have hends (R : ℝ) : ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0 := by
        obtain ⟨N, hN⟩ := exists_nat_gt ((R + |F 0 0|) / ((n : ℝ) * p))
        have hNm := (div_lt_iff₀ hq).mp hN
        refine ⟨(N : ℝ) * T, ?_, ?_⟩
        · have hh := congrArg (fun z : Plane => z 0) (hperiod (-(N : ℤ)) 0)
          simp only [Int.cast_neg, Int.cast_natCast, zero_add, neg_mul] at hh
          change F (-((N : ℝ) * T)) 0 = F 0 0 + -((N : ℝ) * ((n : ℝ) * p)) at hh
          linarith [le_abs_self (F 0 0)]
        · have hh := congrArg (fun z : Plane => z 0) (hperiod (N : ℤ) 0)
          simp only [Int.cast_natCast, zero_add] at hh
          change F ((N : ℝ) * T) 0 = F 0 0 + (N : ℝ) * ((n : ℝ) * p) at hh
          linarith [neg_abs_le (F 0 0)]
      have hiter (k : ℕ) (z : Plane) : (fun z : Plane => z + !₂[p, 0])^[k] z =
          z + !₂[(k : ℝ) * p, 0] := by
        induction k with
        | zero => simp
        | succ k hk =>
          rw [Function.iterate_succ_apply', hk]
          ext i
          fin_cases i <;> simp <;> ring
      have hsetperiod : (fun z : Plane => z + !₂[p, 0])^[n] '' Set.range F = Set.range F := by
        ext z
        constructor
        · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
          refine ⟨x + T, ?_⟩
          rw [hiter]
          simpa using hperiod 1 x
        · rintro ⟨x, rfl⟩
          refine ⟨F (x - T), ⟨x - T, rfl⟩, ?_⟩
          rw [hiter]
          have hh := hperiod 1 (x - T)
          simpa using hh.symm
      exact horizontal F hF hinj B hB hbound hends p n hn hsetperiod
    obtain ⟨e, heproper, heinj, he0, he1, hedir⟩ := normalize a b hab
    let G : C(ℝ, Plane) := ⟨fun x => e (F x), e.continuous_of_finiteDimensional.comp F.continuous⟩
    have hGp : IsProperMap G := heproper.comp hF
    have hGi : Function.Injective G := heinj.comp hinj
    have hpos : 0 < a ^ 2 + b ^ 2 := by
      rcases hab with ha | hb
      · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
      · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
    have hGperiod (k : ℤ) (x : ℝ) : G (x + (k : ℝ) * T) =
        G x + !₂[(k : ℝ) * ((n : ℝ) * (a ^ 2 + b ^ 2)), 0] := by
      change e (F (x + (k : ℝ) * T)) = e (F x) + _
      rw [hperiod, map_add, hedir]
      congr 1
      ext i
      fin_cases i <;> dsimp <;> ring
    have hnondis := horizontal G hGp hGi T (a ^ 2 + b ^ 2) hT hpos n hn hGperiod
    intro hdis
    apply hnondis
    apply Set.disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, ⟨t, rfl⟩, heq⟩
    have hevec : e (a, b) = !₂[a ^ 2 + b ^ 2, 0] := by simpa using hedir 1
    have hxy : F t + (a, b) = F x := by
      apply heinj
      rw [map_add, hevec]
      exact heq
    exact Set.disjoint_left.mp hdis ⟨x, rfl⟩ ⟨F t, ⟨t, rfl⟩, hxy⟩
  have root_disjoint (F : ℝ → ℝ × ℝ) (m n : ℤ)
      (hcollision : ∀ (x y : ℝ) (a b : ℤ),
        F x = ((F y).1 + (a : ℝ) * (2 * Real.pi),
          (F y).2 + (b : ℝ) * (2 * Real.pi)) →
        ∃ k : ℤ, a = k * m ∧ b = k * n)
      (hnonzero : m ≠ 0 ∨ n ≠ 0)
      (d a b : ℤ) (hd : 1 < d) (hm : m = d * a) (hn : n = d * b) :
      Disjoint (Set.range F)
        (Set.range (fun x => ((F x).1 + (a : ℝ) * (2 * Real.pi),
          (F x).2 + (b : ℝ) * (2 * Real.pi)))) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, rfl⟩ ⟨y, hy⟩
    obtain ⟨k, hka, hkb⟩ := hcollision x y a b hy.symm
    have heq : k * d = 1 := by
      rcases hnonzero with hm0 | hn0
      · have ha : a ≠ 0 := by intro h; simp [h] at hm; exact hm0 hm
        have hz : (k * d - 1) * a = 0 := by rw [hm] at hka; nlinarith
        have := (mul_eq_zero.mp hz).resolve_right ha
        omega
      · have hb : b ≠ 0 := by intro h; simp [h] at hn; exact hn0 hn
        have hz : (k * d - 1) * b = 0 := by rw [hn] at hkb; nlinarith
        have := (mul_eq_zero.mp hz).resolve_right hb
        omega
    by_cases hk : k ≤ 0
    · nlinarith
    · have : 1 ≤ k := by omega
      nlinarith
  have hg : 0 < m.gcd n := by
    rcases hnonzero with hm | hn
    · exact Int.gcd_pos_of_ne_zero_left n hm
    · exact Int.gcd_pos_of_ne_zero_right m hn
  by_contra hg1
  have hg2 : 1 < m.gcd n := by omega
  obtain ⟨a, ha⟩ := Int.gcd_dvd_left m n
  obtain ⟨b, hb⟩ := Int.gcd_dvd_right m n
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h
    have hm : m = 0 := by simp [h.1] at ha; exact ha
    have hn : n = 0 := by simp [h.2] at hb; exact hb
    exact hnonzero.elim (fun hh => hh hm) (fun hh => hh hn)
  have habR : (a : ℝ) * (2 * Real.pi) ≠ 0 ∨ (b : ℝ) * (2 * Real.pi) ≠ 0 := by
    rcases hab with ha | hb
    · exact Or.inl (mul_ne_zero (by exact_mod_cast ha) (ne_of_gt (mul_pos (by norm_num) Real.pi_pos)))
    · exact Or.inr (mul_ne_zero (by exact_mod_cast hb) (ne_of_gt (mul_pos (by norm_num) Real.pi_pos)))
  have hscaled (k : ℤ) (x : ℝ) : F (x + (k : ℝ) * (2 * Real.pi)) =
      F x + ((k : ℝ) * (m.gcd n : ℝ) * ((a : ℝ) * (2 * Real.pi)),
        (k : ℝ) * (m.gcd n : ℝ) * ((b : ℝ) * (2 * Real.pi))) := by
    rw [hperiod]
    have ham : (m : ℝ) = (m.gcd n : ℝ) * (a : ℝ) := by exact_mod_cast ha
    have hbn : (n : ℝ) = (m.gcd n : ℝ) * (b : ℝ) := by exact_mod_cast hb
    rw [ham, hbn]
    ext <;> dsimp <;> ring
  have hmeet := root_meets F hproper hinj (2 * Real.pi)
    ((a : ℝ) * (2 * Real.pi)) ((b : ℝ) * (2 * Real.pi))
    (mul_pos (by norm_num) Real.pi_pos) habR (m.gcd n) hg hscaled
  have hdis := root_disjoint F m n hcollision hnonzero (m.gcd n : ℤ) a b
    (by exact_mod_cast hg2) ha hb
  apply hmeet
  apply Set.disjoint_left.mpr
  rintro z hz ⟨w, ⟨y, rfl⟩, hy⟩
  exact Set.disjoint_left.mp hdis hz ⟨y, hy⟩

theorem torus_curve_has_primitive_or_zero_deck_lift (c : Curve Torus) :
    ∃ (m n : ℤ) (F : C(ℝ, ℝ × ℝ)),
      (∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x)) ∧
      (∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
        ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
         (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) ∧
      ((m ≠ 0 ∨ n ≠ 0) → m.gcd n = 1 ∧ IsProperMap F ∧ Topology.IsClosedEmbedding F) ∧
      (∀ (x y : ℝ) (a b : ℤ),
        F x = ((F y).1 + (a : ℝ) * (2 * Real.pi), (F y).2 + (b : ℝ) * (2 * Real.pi)) →
        ∃ k : ℤ, a = k * m ∧ b = k * n) := by
  have primitive (F : C(ℝ, ℝ × ℝ)) (m n : ℤ)
      (hproper : IsProperMap F) (hinj : Function.Injective F)
      (hnonzero : m ≠ 0 ∨ n ≠ 0)
      (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
        ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
         (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi)))
      (hcollision : ∀ (x y : ℝ) (a b : ℤ),
        F x = ((F y).1 + (a : ℝ) * (2 * Real.pi),
          (F y).2 + (b : ℝ) * (2 * Real.pi)) →
        ∃ k : ℤ, a = k * m ∧ b = k * n) :
      m.gcd n = 1 := by
    have root_meets (F : C(ℝ, ℝ × ℝ)) (hF : IsProperMap F) (hinj : Function.Injective F)
        (T a b : ℝ) (hT : 0 < T) (hab : a ≠ 0 ∨ b ≠ 0) (n : ℕ) (hn : 0 < n)
        (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * T) =
          F x + ((k : ℝ) * (n : ℝ) * a, (k : ℝ) * (n : ℝ) * b)) :
        ¬ Disjoint (Set.range F) ((fun z : ℝ × ℝ => z + (a, b)) '' Set.range F) := by
      have normalize (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
          ∃ e : (ℝ × ℝ) →ₗ[ℝ] Schoenflies.Plane,
            IsProperMap e ∧ Function.Injective e ∧
            (∀ x, e x 0 = a * x.1 + b * x.2) ∧
            (∀ x, e x 1 = -b * x.1 + a * x.2) ∧
            (∀ k : ℝ, e (k * a, k * b) = !₂[k * (a ^ 2 + b ^ 2), 0]) := by
        let e : (ℝ × ℝ) →ₗ[ℝ] Schoenflies.Plane := {
          toFun := fun x => !₂[a * x.1 + b * x.2, -b * x.1 + a * x.2]
          map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
          map_smul' := by intro c x; ext i; fin_cases i <;> simp <;> ring }
        have hpos : 0 < a ^ 2 + b ^ 2 := by
          rcases hab with ha | hb
          · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
          · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
        have hi : Function.Injective e := by
          intro x y he
          have h0 : a * x.1 + b * x.2 = a * y.1 + b * y.2 := congrArg (fun z => z 0) he
          have h1 : -b * x.1 + a * x.2 = -b * y.1 + a * y.2 := congrArg (fun z => z 1) he
          have hdx : (a ^ 2 + b ^ 2) * (x.1 - y.1) = 0 := by
            linear_combination a * h0 - b * h1
          have hdy : (a ^ 2 + b ^ 2) * (x.2 - y.2) = 0 := by
            linear_combination b * h0 + a * h1
          exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hdx).resolve_left (ne_of_gt hpos)))
            (sub_eq_zero.mp ((mul_eq_zero.mp hdy).resolve_left (ne_of_gt hpos)))
        refine ⟨e, (e.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hi)).isProperMap, hi, fun _ => rfl, fun _ => rfl, ?_⟩
        intro k
        ext i
        fin_cases i <;> dsimp [e] <;> ring
      have horizontal (F : C(ℝ, Plane)) (hF : IsProperMap F) (hinj : Function.Injective F)
          (T p : ℝ) (hT : 0 < T) (hp : 0 < p) (n : ℕ) (hn : 0 < n)
          (hperiod : ∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * T) =
            F x + !₂[(k : ℝ) * ((n : ℝ) * p), 0]) :
          ¬ Disjoint (Set.range F) ((fun z : Plane => z + !₂[p, 0]) '' Set.range F) := by
        have horizontal (F : C(ℝ, Plane)) (hF : IsProperMap F) (hinj : Function.Injective F)
            (B : ℝ) (hB : 0 < B) (hbound : ∀ x : ℝ, |F x 1| < B)
            (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
            (p : ℝ) (n : ℕ) (hn : 0 < n)
            (hperiod : (fun z : Plane => z + !₂[p, 0])^[n] '' Set.range F = Set.range F) :
            ¬ Disjoint (Set.range F) ((fun z : Plane => z + !₂[p, 0]) '' Set.range F) := by
          have line_jordan (F : C(ℝ, Schoenflies.Plane)) (hF : IsProperMap F)
              (hinj : Function.Injective F) (a : Schoenflies.Plane)
              (ha : a ∉ Set.range F) :
              Schoenflies.IsJordanCurve (insert a (Schoenflies.invert a '' Set.range F)) := by
            let q : OnePoint ℝ → Schoenflies.Plane :=
              invertAtInfinity a ∘ OnePoint.map F
            have hmap : Continuous (OnePoint.map F) := by
              apply OnePoint.continuous_map F.continuous
              simpa only [coclosedCompact_eq_cocompact] using
                (isProperMap_iff_tendsto_cocompact.mp hF).2
            have hq : Continuous q := by
              apply continuous_iff_continuousAt.mpr
              intro z
              cases z with
              | infty =>
                exact (invertAtInfinity_continuousAt_infty a).comp hmap.continuousAt
              | coe x =>
                apply OnePoint.continuousAt_coe.mpr
                change ContinuousAt (fun x : ℝ => Schoenflies.invert a (F x)) x
                exact (Schoenflies.continuousAt_invert (by
                  intro h; exact ha ⟨x, h⟩)).comp F.continuous.continuousAt
            have hqi : Function.Injective q := by
              intro x y hxy
              cases x with
              | infty =>
                cases y with
                | infty => rfl
                | coe y =>
                  change a = Schoenflies.invert a (F y) at hxy
                  exact False.elim (ha ⟨y, Schoenflies.invert_eq_center_iff.mp hxy.symm⟩)
              | coe x =>
                cases y with
                | infty =>
                  change Schoenflies.invert a (F x) = a at hxy
                  exact False.elim (ha ⟨x, Schoenflies.invert_eq_center_iff.mp hxy⟩)
                | coe y =>
                  change Schoenflies.invert a (F x) = Schoenflies.invert a (F y) at hxy
                  exact congrArg OnePoint.some (hinj (Schoenflies.invert_injective a hxy))
            let e : OnePoint ℝ ≃ₜ Circle :=
              (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).trans
                ClassificationJordanCurve.Arcs.circleHomeoSphere.symm
            let r : C(Circle, Schoenflies.Plane) := ⟨q ∘ e.symm, hq.comp e.symm.continuous⟩
            have hr : IsEmbedding r := (r.continuous.isClosedEmbedding (hqi.comp e.symm.injective)).isEmbedding
            have hrange : Set.range r = insert a (Schoenflies.invert a '' Set.range F) := by
              ext z
              constructor
              · rintro ⟨x, rfl⟩
                change q (e.symm x) ∈ _
                generalize e.symm x = y
                cases y with
                | infty => exact Set.mem_insert a _
                | coe t => exact Set.mem_insert_of_mem _ ⟨F t, ⟨t, rfl⟩, rfl⟩
              · intro hz
                rcases hz with hz | ⟨w, ⟨t, rfl⟩, rfl⟩
                · subst z
                  exact ⟨e OnePoint.infty, by simp [r, q, invertAtInfinity]⟩
                · exact ⟨e (OnePoint.some t), by simp [r, q, invertAtInfinity]⟩
            rw [← hrange]
            exact CurveComplex.isJordanCurve_range_of_isEmbedding_circle r hr
          have split (L : Set Plane) (a : Plane) (ha : a ∉ L)
              (hJ : IsJordanCurve (insert a (invert a '' L))) :
              ∃ U V : Set Plane, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
                Disjoint U V ∧ U ∪ V = Lᶜ ∧ frontier U = L ∧ frontier V = L := by
            let C := insert a (invert a '' L)
            have hsep : IsSeparating C := jordan_curve_theorem hJ
            have haC : a ∈ C := Set.mem_insert a _
            have hain : a ∉ inside C := fun h => h.1 haC
            have haout : a ∉ outside C := fun h => h.1 haC
            let U := invert a '' inside C
            let V := invert a '' outside C ∪ {a}
            have hUopen : IsOpen U := isOpen_invert_image hsep.isOpen_inside hain
            have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
              intro z hz
              simpa only [mem_compl_iff, mem_singleton_iff] using
                (show z ≠ a from fun h => haout (h ▸ hz))
            have hinc : inside C ⊆ ({a}ᶜ : Set Plane) := by
              intro z hz
              simpa only [mem_compl_iff, mem_singleton_iff] using
                (show z ≠ a from fun h => hain (h ▸ hz))
            have hUconn : IsConnected U :=
              hsep.isConnected_inside.image _ ((continuousOn_invert a).mono hinc)
            obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
            have hTopen : IsOpen (invert a '' outside C) :=
              isOpen_invert_image hsep.isOpen_outside haout
            have hVball : ball a R⁻¹ ⊆ V := by
              intro z hz
              rcases eq_or_ne z a with rfl | hza
              · exact Or.inr rfl
              · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
                have hpos : 0 < dist z a := dist_pos.2 hza
                rw [mem_compl_iff, mem_closedBall, dist_invert_center]
                exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
            have hVopen : IsOpen V := by
              have hrw : V = invert a '' outside C ∪ ball a R⁻¹ := by
                refine Subset.antisymm (union_subset subset_union_left ?_)
                  (union_subset subset_union_left hVball)
                rintro z rfl
                exact Or.inr (mem_ball_self (by positivity))
              rw [hrw]
              exact hTopen.union isOpen_ball
            have hacl : a ∈ closure (invert a '' outside C) := by
              rw [Metric.mem_closure_iff]
              intro e he
              obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
                by_contra hcon
                push Not at hcon
                exact hsep.not_isBounded_outside
                  ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
              refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
              rw [dist_comm, dist_invert_center]
              exact inv_lt_of_inv_lt₀ he hzfar
            have hVconn : IsConnected V := by
              refine ⟨⟨a, Or.inr rfl⟩, ?_⟩
              exact (hsep.isConnected_outside.image _
                ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
                (union_subset subset_closure (by rintro z rfl; exact hacl))
            have hdis : Disjoint U V := by
              apply Set.disjoint_left.mpr
              rintro z ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | he)
              · have he' := invert_injective a he
                exact Set.disjoint_left.mp disjoint_inside_outside hx (he' ▸ hy)
              · exact hain ((invert_eq_center_iff.mp he) ▸ hx)
            have hinv (z : Plane) : invert a z ∈ C ↔ z = a ∨ z ∈ L := by
              dsimp [C]
              simp only [mem_insert_iff, invert_eq_center_iff]
              rw [Set.mem_image]
              constructor
              · rintro (h | ⟨x, hx, he⟩)
                · exact Or.inl h
                · exact Or.inr ((invert_injective a he) ▸ hx)
              · rintro (h | h)
                · exact Or.inl h
                · exact Or.inr ⟨z, h, rfl⟩
            have hpart : U ∪ V = Lᶜ := by
              ext z
              constructor
              · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl)
                · intro hz
                  have := (hinv (invert a x)).mpr (Or.inr hz)
                  rw [invert_invert] at this
                  exact hx.1 this
                · intro hz
                  have := (hinv (invert a x)).mpr (Or.inr hz)
                  rw [invert_invert] at this
                  exact hx.1 this
                · exact ha
              · intro hz
                by_cases hza : z = a
                · exact Or.inr (Or.inr hza)
                · have hzC : invert a z ∉ C := by simpa [hinv, hza] using hz
                  have hzside : invert a z ∈ inside C ∪ outside C := by
                    rwa [inside_union_outside]
                  rcases hzside with hu | hv
                  · exact Or.inl ⟨invert a z, hu, invert_invert a z⟩
                  · exact Or.inr (Or.inl ⟨invert a z, hv, invert_invert a z⟩)
            have hUL : Disjoint U L := by
              apply Set.disjoint_left.mpr
              intro x hx hL
              exact (show x ∈ Lᶜ from hpart ▸ Or.inl hx) hL
            have hVL : Disjoint V L := by
              apply Set.disjoint_left.mpr
              intro x hx hL
              exact (show x ∈ Lᶜ from hpart ▸ Or.inr hx) hL
            have hfrontU : frontier U = L := by
              apply Subset.antisymm
              · intro x hx
                by_contra hxL
                have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
                rcases hside with hu | hv
                · exact (hUopen.frontier_eq ▸ hx).2 hu
                · exact Set.disjoint_right.mp (hdis.closure_left hVopen) hv (frontier_subset_closure hx)
              · intro x hx
                have hxa : x ≠ a := fun h => ha (h ▸ hx)
                have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
                have hixcl : invert a x ∈ closure (inside C) := by
                  rw [← hsep.frontier_inside] at hixC
                  exact frontier_subset_closure hixC
                rw [hUopen.frontier_eq]
                refine ⟨?_, fun h => Set.disjoint_left.mp hUL h hx⟩
                simpa only [invert_invert] using
                  mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
            have hfrontV : frontier V = L := by
              apply Subset.antisymm
              · intro x hx
                by_contra hxL
                have hside : x ∈ U ∪ V := hpart.symm ▸ hxL
                rcases hside with hu | hv
                · exact Set.disjoint_left.mp (hdis.closure_right hUopen) hu (frontier_subset_closure hx)
                · exact (hVopen.frontier_eq ▸ hx).2 hv
              · intro x hx
                have hxa : x ≠ a := fun h => ha (h ▸ hx)
                have hixC : invert a x ∈ C := (hinv x).mpr (Or.inr hx)
                have hixcl : invert a x ∈ closure (outside C) := by
                  rw [← hsep.frontier_outside] at hixC
                  exact frontier_subset_closure hixC
                rw [hVopen.frontier_eq]
                refine ⟨?_, fun h => Set.disjoint_left.mp hVL h hx⟩
                apply closure_mono (show invert a '' outside C ⊆ V from subset_union_left)
                simpa only [invert_invert] using
                  mem_closure_image (continuousAt_invert (invert_ne_center hxa)) hixcl
            exact ⟨U, V, hUopen, hVopen, hUconn, hVconn, hdis, hpart, hfrontU, hfrontV⟩
          have no_crossing (F : C(ℝ, Plane)) (B : ℝ) (hB : 0 < B)
              (hbound : ∀ x : ℝ, |F x 1| < B)
              (hends : ∀ R : ℝ, ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0)
              (u w : Plane) (hu : u 1 ≤ -B) (hw : B ≤ w 1) :
              ¬ JoinedIn (Set.range F)ᶜ u w := by
            have crossing_strip {a b c d : ℝ} (hab : a < b) (hcd : c < d)
                (h v : ℝ → Plane)
                (hh : ContinuousOn h (Icc (-1) 1)) (hv : ContinuousOn v (Icc (-1) 1))
                (hhY : ∀ t ∈ Icc (-1 : ℝ) 1, c < h t 1 ∧ h t 1 < d)
                (hvX : ∀ t ∈ Icc (-1 : ℝ) 1, a < v t 0 ∧ v t 0 < b)
                (hh1 : h (-1) 0 ≤ a) (hh2 : b ≤ h 1 0)
                (hv1 : v (-1) 1 ≤ c) (hv2 : d ≤ v 1 1) :
                ∃ s ∈ Icc (-1 : ℝ) 1, ∃ t ∈ Icc (-1 : ℝ) 1, h s = v t := by
              let H : ℝ → Plane := fun s => !₂[max a (min b (h s 0)), h s 1]
              let V : ℝ → Plane := fun t => !₂[v t 0, max c (min d (v t 1))]
              have hH : ContinuousOn H (Icc (-1) 1) := by
                apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
                apply continuousOn_pi.mpr
                intro i
                fin_cases i
                · exact (show Continuous (fun x : ℝ => max a (min b x)) by fun_prop).comp_continuousOn
                    ((EuclideanSpace.proj 0).continuous.comp_continuousOn hh)
                · exact (EuclideanSpace.proj 1).continuous.comp_continuousOn hh
              have hV : ContinuousOn V (Icc (-1) 1) := by
                apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
                apply continuousOn_pi.mpr
                intro i
                fin_cases i
                · exact (EuclideanSpace.proj 0).continuous.comp_continuousOn hv
                · exact (show Continuous (fun x : ℝ => max c (min d x)) by fun_prop).comp_continuousOn
                    ((EuclideanSpace.proj 1).continuous.comp_continuousOn hv)
              have hHE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                  H t 0 ∈ Icc a b ∧ H t 1 ∈ Icc c d := by
                exact ⟨⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩, (hhY t ht).1.le, (hhY t ht).2.le⟩
              have hVE (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
                  V t 0 ∈ Icc a b ∧ V t 1 ∈ Icc c d := by
                exact ⟨⟨(hvX t ht).1.le, (hvX t ht).2.le⟩, le_max_left _ _, max_le hcd.le (min_le_left _ _)⟩
              have hH1 : H (-1) 0 = a := by
                dsimp [H]
                rw [min_eq_right (hh1.trans hab.le), max_eq_left hh1]
              have hH2 : H 1 0 = b := by
                dsimp [H]
                rw [min_eq_left hh2, max_eq_right hab.le]
              have hV1 : V (-1) 1 = c := by
                dsimp [V]
                rw [min_eq_right (hv1.trans hcd.le), max_eq_left hv1]
              have hV2 : V 1 1 = d := by
                dsimp [V]
                rw [min_eq_left hv2, max_eq_right hcd.le]
              obtain ⟨s, hs, t, ht, he⟩ := ClassificationJordanCurve.crossing ClassificationJordanCurve.Brouwer.brouwerFPT
                hab.le hcd.le H V hH hV hHE hVE hH1 hH2 hV1 hV2
              have clamp {l u x z : ℝ} (hlu : l < u) (hz : l < z ∧ z < u)
                  (he : max l (min u x) = z) : x = z := by
                by_cases hx : x ≤ l
                · rw [min_eq_right (hx.trans hlu.le), max_eq_left hx] at he
                  linarith [hz.1]
                · by_cases hxu : u ≤ x
                  · rw [min_eq_left hxu, max_eq_right hlu.le] at he
                    linarith [hz.2]
                  · rwa [min_eq_right (le_of_not_ge hxu), max_eq_right (le_of_not_ge hx)] at he
              refine ⟨s, hs, t, ht, ?_⟩
              have he0 := congrArg (fun p : Plane => p 0) he
              have he1 := congrArg (fun p : Plane => p 1) he
              ext i
              fin_cases i
              · exact clamp hab (hvX t ht) he0
              · exact (clamp hcd (hhY s hs) he1.symm).symm
            intro hjoin
            obtain ⟨v, hv, hv0, hv1, hvmem⟩ := ClassificationJordanCurve.arc_path hjoin
            have hvc : ContinuousOn (fun t : ℝ => |v t 0|) (Icc (-1) 1) :=
              continuous_abs.comp_continuousOn ((EuclideanSpace.proj 0).continuous.comp_continuousOn hv)
            obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hvc).bddAbove
            let R := max M 0 + 1
            have hR : 0 < R := by dsimp [R]; positivity
            have hMv (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : |v t 0| < R := by
              have hm := hM (Set.mem_image_of_mem _ ht)
              dsimp [R]
              linarith [le_max_left M 0]
            obtain ⟨A, hA0, hA1⟩ := hends R
            let h : ℝ → Plane := fun s => F (A * s)
            have hhc : ContinuousOn h (Icc (-1) 1) :=
              (F.continuous.comp (by fun_prop : Continuous (fun s : ℝ => A * s))).continuousOn
            have hhY (t : ℝ) (_ht : t ∈ Icc (-1 : ℝ) 1) : -B < h t 1 ∧ h t 1 < B :=
              abs_lt.mp (hbound (A * t))
            have hvX (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : -R < v t 0 ∧ v t 0 < R :=
              abs_lt.mp (hMv t ht)
            have hh0 : h (-1) 0 ≤ -R := by simpa [h] using hA0.le
            have hh1 : R ≤ h 1 0 := by simpa [h] using hA1.le
            have hv0' : v (-1) 1 ≤ -B := by simpa [hv0] using hu
            have hv1' : B ≤ v 1 1 := by simpa [hv1] using hw
            obtain ⟨s, hs, t, ht, he⟩ := crossing_strip (by linarith : -R < R)
              (by linarith : -B < B) h v hhc hv hhY hvX hh0 hh1 hv0' hv1'
            exact hvmem t ht ⟨A * s, he⟩
          have orient 
              (L U V A B : Set Plane)
              (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
              (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
              (hA : IsConnected A) (hB : IsConnected B) (hAL : A ⊆ Lᶜ) (hBL : B ⊆ Lᶜ)
              (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ JoinedIn Lᶜ a b) :
              (A ⊆ U ∧ B ⊆ V) ∨ (A ⊆ V ∧ B ⊆ U) := by
            have hAs : A ⊆ U ∪ V := hpart.symm ▸ hAL
            have hBs : B ⊆ U ∪ V := hpart.symm ▸ hBL
            have hUL : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
            have hVL : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
            obtain ⟨a, ha⟩ := hA.nonempty
            obtain ⟨b, hb⟩ := hB.nonempty
            rcases hA.isPreconnected.subset_or_subset hU hV hd hAs with hAU | hAV
            · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
              · exact False.elim (hno a ha b hb
                  (((hU.isConnected_iff_isPathConnected.mp hcU).joinedIn a (hAU ha) b (hBU hb)).mono hUL))
              · exact Or.inl ⟨hAU, hBV⟩
            · rcases hB.isPreconnected.subset_or_subset hU hV hd hBs with hBU | hBV
              · exact Or.inr ⟨hAV, hBU⟩
              · exact False.elim (hno a ha b hb
                  (((hV.isConnected_iff_isPathConnected.mp hcV).joinedIn a (hAV ha) b (hBV hb)).mono hVL))
          have no_cycle (e : Plane ≃ₜ Plane)
              (L U V A B : Set Plane) (hL : IsConnected L)
              (hU : IsOpen U) (hV : IsOpen V) (hcU : IsConnected U) (hcV : IsConnected V)
              (hd : Disjoint U V) (hpart : U ∪ V = Lᶜ)
              (hfU : frontier U = L) (hfV : frontier V = L)
              (hA : A.Nonempty) (hB : B.Nonempty) (hAU : A ⊆ U) (hBV : B ⊆ V)
              (heA : e '' A = A) (heB : e '' B = B)
              (n : ℕ) (hn : 0 < n) (hperiod : e^[n] '' L = L) :
              ¬ Disjoint L (e '' L) := by
            have ordered
                (L₁ L₂ U₁ V₁ U₂ V₂ : Set Plane)
                (hL₁ : L₁.Nonempty) (hL₂ : IsConnected L₂)
                (hU₁ : IsOpen U₁) (hV₁ : IsOpen V₁) (hU₂ : IsOpen U₂) (hV₂ : IsOpen V₂)
                (hcU₁ : IsConnected U₁) (hcV₁ : IsConnected V₁)
                (hd₁ : Disjoint U₁ V₁) (hd₂ : Disjoint U₂ V₂)
                (hp₁ : U₁ ∪ V₁ = L₁ᶜ) (hp₂ : U₂ ∪ V₂ = L₂ᶜ)
                (hfU₁ : frontier U₁ = L₁) (hfV₁ : frontier V₁ = L₁)
                (hdL : Disjoint L₁ L₂)
                (hcommonU : (U₁ ∩ U₂).Nonempty) (hcommonV : (V₁ ∩ V₂).Nonempty) :
                U₁ ⊂ U₂ ∨ U₂ ⊂ U₁ := by
              have hU₁L : Disjoint U₁ L₁ := by
                apply disjoint_left.mpr
                intro x hx hL
                exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inl hx) hL
              have hV₁L : Disjoint V₁ L₁ := by
                apply disjoint_left.mpr
                intro x hx hL
                exact (show x ∈ L₁ᶜ from hp₁ ▸ Or.inr hx) hL
              have hU₂L : Disjoint U₂ L₂ := by
                apply disjoint_left.mpr
                intro x hx hL
                exact (show x ∈ L₂ᶜ from hp₂ ▸ Or.inl hx) hL
              have hclU : closure U₁ = U₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfU₁]
              have hclV : closure V₁ = V₁ ∪ L₁ := by rw [closure_eq_self_union_frontier, hfV₁]
              have hsub : L₂ ⊆ U₁ ∪ V₁ := by
                rw [hp₁]
                exact fun x hx h => disjoint_left.mp hdL h hx
              rcases hL₂.isPreconnected.subset_or_subset hU₁ hV₁ hd₁ hsub with hLU | hLV
              · have hsubcl : closure V₁ ⊆ U₂ ∪ V₂ := by
                  rw [hp₂, hclV]
                  rintro x (hx | hx) hL
                  · exact disjoint_left.mp hd₁ (hLU hL) hx
                  · exact disjoint_left.mp hdL hx hL
                have hcl : closure V₁ ⊆ V₂ := by
                  rcases hcV₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
                  · obtain ⟨x, hx₁, hx₂⟩ := hcommonV
                    exact False.elim (disjoint_left.mp hd₂ (h (subset_closure hx₁)) hx₂)
                  · exact h
                have hUU : U₂ ⊆ U₁ := by
                  intro x hx
                  by_contra hx₁
                  have hxcl : x ∈ closure V₁ := by
                    rw [hclV]
                    by_cases hxL : x ∈ L₁
                    · exact Or.inr hxL
                    · have hside : x ∈ U₁ ∪ V₁ := hp₁.symm ▸ hxL
                      exact Or.inl (hside.resolve_left hx₁)
                  exact disjoint_left.mp hd₂ hx (hcl hxcl)
                right
                apply Set.ssubset_iff_subset_ne.mpr
                refine ⟨hUU, ?_⟩
                intro he
                obtain ⟨x, hx⟩ := hL₂.nonempty
                exact disjoint_left.mp hU₂L (he.symm ▸ hLU hx) hx
              · have hsubcl : closure U₁ ⊆ U₂ ∪ V₂ := by
                  rw [hp₂, hclU]
                  rintro x (hx | hx) hL
                  · exact disjoint_left.mp hd₁ hx (hLV hL)
                  · exact disjoint_left.mp hdL hx hL
                have hcl : closure U₁ ⊆ U₂ := by
                  rcases hcU₁.closure.isPreconnected.subset_or_subset hU₂ hV₂ hd₂ hsubcl with h | h
                  · exact h
                  · obtain ⟨x, hx₁, hx₂⟩ := hcommonU
                    exact False.elim (disjoint_left.mp hd₂ hx₂ (h (subset_closure hx₁)))
                left
                apply Set.ssubset_iff_subset_ne.mpr
                refine ⟨subset_closure.trans hcl, ?_⟩
                intro he
                obtain ⟨x, hx⟩ := hL₁
                have hxc : x ∈ closure U₁ := hclU.symm ▸ Or.inr hx
                exact disjoint_left.mp hU₁L (he.symm ▸ hcl hxc) hx
            have fixed_iter (S : Set Plane) (hS : e '' S = S) (k : ℕ) : e^[k] '' S = S := by
              rw [Set.image_iterate_eq]
              induction k with
              | zero => rfl
              | succ k hk => simpa only [Function.iterate_succ_apply', hk] using hS
            have hmarker (S W : Set Plane) (hS : S.Nonempty) (hSW : S ⊆ W)
                (hfix : e '' S = S) : (W ∩ e '' W).Nonempty := by
              obtain ⟨x, hx⟩ := hS
              refine ⟨e x, ?_, ⟨x, hSW hx, rfl⟩⟩
              exact hSW (hfix ▸ mem_image_of_mem e hx)
            have hUsub : U ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inl hx
            have hVsub : V ⊆ Lᶜ := by intro x hx; exact hpart ▸ Or.inr hx
            have hUP : e^[n] '' U ⊆ U := by
              have hsub : e^[n] '' U ⊆ U ∪ V := by
                rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
                exact Set.image_mono hUsub
              rcases (hcU.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
                hU hV hd hsub with h | h
              · exact h
              · obtain ⟨a, ha⟩ := hA
                have hai : a ∈ e^[n] '' A := (fixed_iter A heA n).symm ▸ ha
                exact False.elim (disjoint_left.mp hd (hAU ha) (h (Set.image_mono hAU hai)))
            have hVP : e^[n] '' V ⊆ V := by
              have hsub : e^[n] '' V ⊆ U ∪ V := by
                rw [hpart, ← hperiod, ← Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩]
                exact Set.image_mono hVsub
              rcases (hcV.image _ (e.continuous.iterate n).continuousOn).isPreconnected.subset_or_subset
                hU hV hd hsub with h | h
              · obtain ⟨b, hb⟩ := hB
                have hbi : b ∈ e^[n] '' B := (fixed_iter B heB n).symm ▸ hb
                exact False.elim (disjoint_left.mp hd (h (Set.image_mono hBV hbi)) (hBV hb))
              · exact h
            have hperiodU : e^[n] '' U = U := by
              apply Subset.antisymm hUP
              intro x hx
              have hxp : x ∈ e^[n] '' U ∪ e^[n] '' V := by
                rw [← Set.image_union, hpart, Set.image_compl_eq ⟨e.injective.iterate n, e.surjective.iterate n⟩, hperiod]
                exact hUsub hx
              exact hxp.resolve_right (fun h => disjoint_left.mp hd hx (hVP h))
            intro hdisL
            have hpartE : (e '' U) ∪ (e '' V) = (e '' L)ᶜ := by
              rw [← Set.image_union, hpart, e.image_compl]
            have horder := ordered L (e '' L) U V (e '' U) (e '' V)
              hL.nonempty (hL.image _ e.continuous.continuousOn) hU hV
              (e.isOpenMap _ hU) (e.isOpenMap _ hV) hcU hcV hd
              ((Set.disjoint_image_iff e.injective).mpr hd) hpart hpartE hfU hfV hdisL
              (hmarker A U hA hAU heA) (hmarker B V hB hBV heB)
            have hmono : StrictMono (Set.image e) := e.injective.image_strictMono
            have hp : (Set.image e)^[n] U = U := by simpa only [← Set.image_iterate_eq] using hperiodU
            rcases horder with h | h
            · have hh := hmono.strictMono_iterate_of_lt_map h hn
              simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh
            · have hh := hmono.strictAnti_iterate_of_map_lt h hn
              simpa only [Function.iterate_zero_apply, hp, lt_self_iff_false] using hh
          let L := Set.range F
          let A : Set Plane := {z | z 1 < -B}
          let D : Set Plane := {z | B < z 1}
          have hAn : A.Nonempty := ⟨!₂[0, -B - 1], by dsimp [A]; linarith⟩
          have hDn : D.Nonempty := ⟨!₂[0, B + 1], by dsimp [D]; linarith⟩
          have hAc : IsConnected A := by
            apply Convex.isConnected _ hAn
            exact (convex_Iio (-B)).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
          have hDc : IsConnected D := by
            apply Convex.isConnected _ hDn
            exact (convex_Ioi B).is_linear_preimage (EuclideanSpace.proj (1 : Fin 2)).isLinear
          have hAL : A ⊆ Lᶜ := by
            rintro z hz ⟨x, rfl⟩
            have hh := (abs_lt.mp (hbound x)).1
            exact (not_lt_of_ge hh.le) hz
          have hDL : D ⊆ Lᶜ := by
            rintro z hz ⟨x, rfl⟩
            have hh := (abs_lt.mp (hbound x)).2
            exact (not_lt_of_ge hh.le) hz
          obtain ⟨a, ha⟩ := hAn
          have hJ := line_jordan F hF hinj a (hAL ha)
          obtain ⟨U, V, hU, hV, hcU, hcV, hd, hpart, hfU, hfV⟩ := split L a (hAL ha) hJ
          have hno (a : Plane) (ha : a ∈ A) (b : Plane) (hb : b ∈ D) : ¬ JoinedIn Lᶜ a b :=
            no_crossing F B hB hbound hends a b ha.le hb.le
          let e : Plane ≃ₜ Plane := Homeomorph.addRight !₂[p, 0]
          have heA : e '' A = A := by
            ext z
            constructor
            · rintro ⟨x, hx, rfl⟩
              simpa [e, A] using hx
            · intro hz
              refine ⟨z - !₂[p, 0], ?_, ?_⟩
              · simpa [A] using hz
              · simp [e]
          have heD : e '' D = D := by
            ext z
            constructor
            · rintro ⟨x, hx, rfl⟩
              simpa [e, D] using hx
            · intro hz
              refine ⟨z - !₂[p, 0], ?_, ?_⟩
              · simpa [D] using hz
              · simp [e]
          have hLc : IsConnected L := isConnected_range F.continuous
          have hp : e^[n] '' L = L := hperiod
          rcases orient L U V A D hU hV hcU hcV hd hpart hAc hDc hAL hDL hno with h | h
          · exact no_cycle e L U V A D hLc hU hV hcU hcV hd hpart hfU hfV
              hAc.nonempty hDn h.1 h.2 heA heD n hn hp
          · exact no_cycle e L V U A D hLc hV hU hcV hcU hd.symm
              (by simpa only [union_comm] using hpart) hfV hfU
              hAc.nonempty hDn h.1 h.2 heA heD n hn hp
        have hyperiod : Function.Periodic (fun x => F x 1) T := by
          intro x
          have hh := congrArg (fun z : Plane => z 1) (hperiod 1 x)
          simpa using hh
        have hycont : Continuous (fun x => F x 1) := (EuclideanSpace.proj 1).continuous.comp F.continuous
        have hcompact : IsCompact (Set.range (fun x => F x 1)) := by
          rw [← hyperiod.image_Icc hT 0]
          exact isCompact_Icc.image hycont
        obtain ⟨M, hM⟩ := (hcompact.image continuous_abs).bddAbove
        let B := max M 0 + 1
        have hB : 0 < B := by dsimp [B]; positivity
        have hbound (x : ℝ) : |F x 1| < B := by
          have hh := hM ⟨F x 1, ⟨x, rfl⟩, rfl⟩
          dsimp [B]
          linarith [le_max_left M 0]
        have hq : 0 < (n : ℝ) * p := mul_pos (by exact_mod_cast hn) hp
        have hends (R : ℝ) : ∃ A : ℝ, F (-A) 0 < -R ∧ R < F A 0 := by
          obtain ⟨N, hN⟩ := exists_nat_gt ((R + |F 0 0|) / ((n : ℝ) * p))
          have hNm := (div_lt_iff₀ hq).mp hN
          refine ⟨(N : ℝ) * T, ?_, ?_⟩
          · have hh := congrArg (fun z : Plane => z 0) (hperiod (-(N : ℤ)) 0)
            simp only [Int.cast_neg, Int.cast_natCast, zero_add, neg_mul] at hh
            change F (-((N : ℝ) * T)) 0 = F 0 0 + -((N : ℝ) * ((n : ℝ) * p)) at hh
            linarith [le_abs_self (F 0 0)]
          · have hh := congrArg (fun z : Plane => z 0) (hperiod (N : ℤ) 0)
            simp only [Int.cast_natCast, zero_add] at hh
            change F ((N : ℝ) * T) 0 = F 0 0 + (N : ℝ) * ((n : ℝ) * p) at hh
            linarith [neg_abs_le (F 0 0)]
        have hiter (k : ℕ) (z : Plane) : (fun z : Plane => z + !₂[p, 0])^[k] z =
            z + !₂[(k : ℝ) * p, 0] := by
          induction k with
          | zero => simp
          | succ k hk =>
            rw [Function.iterate_succ_apply', hk]
            ext i
            fin_cases i <;> simp <;> ring
        have hsetperiod : (fun z : Plane => z + !₂[p, 0])^[n] '' Set.range F = Set.range F := by
          ext z
          constructor
          · rintro ⟨w, ⟨x, rfl⟩, rfl⟩
            refine ⟨x + T, ?_⟩
            rw [hiter]
            simpa using hperiod 1 x
          · rintro ⟨x, rfl⟩
            refine ⟨F (x - T), ⟨x - T, rfl⟩, ?_⟩
            rw [hiter]
            have hh := hperiod 1 (x - T)
            simpa using hh.symm
        exact horizontal F hF hinj B hB hbound hends p n hn hsetperiod
      obtain ⟨e, heproper, heinj, he0, he1, hedir⟩ := normalize a b hab
      let G : C(ℝ, Plane) := ⟨fun x => e (F x), e.continuous_of_finiteDimensional.comp F.continuous⟩
      have hGp : IsProperMap G := heproper.comp hF
      have hGi : Function.Injective G := heinj.comp hinj
      have hpos : 0 < a ^ 2 + b ^ 2 := by
        rcases hab with ha | hb
        · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
        · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
      have hGperiod (k : ℤ) (x : ℝ) : G (x + (k : ℝ) * T) =
          G x + !₂[(k : ℝ) * ((n : ℝ) * (a ^ 2 + b ^ 2)), 0] := by
        change e (F (x + (k : ℝ) * T)) = e (F x) + _
        rw [hperiod, map_add, hedir]
        congr 1
        ext i
        fin_cases i <;> dsimp <;> ring
      have hnondis := horizontal G hGp hGi T (a ^ 2 + b ^ 2) hT hpos n hn hGperiod
      intro hdis
      apply hnondis
      apply Set.disjoint_left.mpr
      rintro z ⟨x, rfl⟩ ⟨y, ⟨t, rfl⟩, heq⟩
      have hevec : e (a, b) = !₂[a ^ 2 + b ^ 2, 0] := by simpa using hedir 1
      have hxy : F t + (a, b) = F x := by
        apply heinj
        rw [map_add, hevec]
        exact heq
      exact Set.disjoint_left.mp hdis ⟨x, rfl⟩ ⟨F t, ⟨t, rfl⟩, hxy⟩
    have root_disjoint (F : ℝ → ℝ × ℝ) (m n : ℤ)
        (hcollision : ∀ (x y : ℝ) (a b : ℤ),
          F x = ((F y).1 + (a : ℝ) * (2 * Real.pi),
            (F y).2 + (b : ℝ) * (2 * Real.pi)) →
          ∃ k : ℤ, a = k * m ∧ b = k * n)
        (hnonzero : m ≠ 0 ∨ n ≠ 0)
        (d a b : ℤ) (hd : 1 < d) (hm : m = d * a) (hn : n = d * b) :
        Disjoint (Set.range F)
          (Set.range (fun x => ((F x).1 + (a : ℝ) * (2 * Real.pi),
            (F x).2 + (b : ℝ) * (2 * Real.pi)))) := by
      apply Set.disjoint_left.mpr
      rintro z ⟨x, rfl⟩ ⟨y, hy⟩
      obtain ⟨k, hka, hkb⟩ := hcollision x y a b hy.symm
      have heq : k * d = 1 := by
        rcases hnonzero with hm0 | hn0
        · have ha : a ≠ 0 := by intro h; simp [h] at hm; exact hm0 hm
          have hz : (k * d - 1) * a = 0 := by rw [hm] at hka; nlinarith
          have := (mul_eq_zero.mp hz).resolve_right ha
          omega
        · have hb : b ≠ 0 := by intro h; simp [h] at hn; exact hn0 hn
          have hz : (k * d - 1) * b = 0 := by rw [hn] at hkb; nlinarith
          have := (mul_eq_zero.mp hz).resolve_right hb
          omega
      by_cases hk : k ≤ 0
      · nlinarith
      · have : 1 ≤ k := by omega
        nlinarith
    have hg : 0 < m.gcd n := by
      rcases hnonzero with hm | hn
      · exact Int.gcd_pos_of_ne_zero_left n hm
      · exact Int.gcd_pos_of_ne_zero_right m hn
    by_contra hg1
    have hg2 : 1 < m.gcd n := by omega
    obtain ⟨a, ha⟩ := Int.gcd_dvd_left m n
    obtain ⟨b, hb⟩ := Int.gcd_dvd_right m n
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push_neg at h
      have hm : m = 0 := by simp [h.1] at ha; exact ha
      have hn : n = 0 := by simp [h.2] at hb; exact hb
      exact hnonzero.elim (fun hh => hh hm) (fun hh => hh hn)
    have habR : (a : ℝ) * (2 * Real.pi) ≠ 0 ∨ (b : ℝ) * (2 * Real.pi) ≠ 0 := by
      rcases hab with ha | hb
      · exact Or.inl (mul_ne_zero (by exact_mod_cast ha) (ne_of_gt (mul_pos (by norm_num) Real.pi_pos)))
      · exact Or.inr (mul_ne_zero (by exact_mod_cast hb) (ne_of_gt (mul_pos (by norm_num) Real.pi_pos)))
    have hscaled (k : ℤ) (x : ℝ) : F (x + (k : ℝ) * (2 * Real.pi)) =
        F x + ((k : ℝ) * (m.gcd n : ℝ) * ((a : ℝ) * (2 * Real.pi)),
          (k : ℝ) * (m.gcd n : ℝ) * ((b : ℝ) * (2 * Real.pi))) := by
      rw [hperiod]
      have ham : (m : ℝ) = (m.gcd n : ℝ) * (a : ℝ) := by exact_mod_cast ha
      have hbn : (n : ℝ) = (m.gcd n : ℝ) * (b : ℝ) := by exact_mod_cast hb
      rw [ham, hbn]
      ext <;> dsimp <;> ring
    have hmeet := root_meets F hproper hinj (2 * Real.pi)
      ((a : ℝ) * (2 * Real.pi)) ((b : ℝ) * (2 * Real.pi))
      (mul_pos (by norm_num) Real.pi_pos) habR (m.gcd n) hg hscaled
    have hdis := root_disjoint F m n hcollision hnonzero (m.gcd n : ℤ) a b
      (by exact_mod_cast hg2) ha hb
    apply hmeet
    apply Set.disjoint_left.mpr
    rintro z hz ⟨w, ⟨y, rfl⟩, hy⟩
    exact Set.disjoint_left.mp hdis hz ⟨y, hy⟩
  have lifting (c : Curve Torus) :
      ∃ (m n : ℤ) (F : C(ℝ, ℝ × ℝ)),
        (∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x)) ∧
        (∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
          ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
           (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) ∧
        ((m ≠ 0 ∨ n ≠ 0) → IsProperMap F ∧ Topology.IsClosedEmbedding F) ∧
        (∀ (x y : ℝ) (a b : ℤ),
          F x = ((F y).1 + (a : ℝ) * (2 * Real.pi), (F y).2 + (b : ℝ) * (2 * Real.pi)) →
          ∃ k : ℤ, a = k * m ∧ b = k * n) := by
    have hlift :
        ∃ (m n : ℤ) (F : C(ℝ, ℝ × ℝ)),
          (∀ x, (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x)) ∧
          (∀ (k : ℤ) (x : ℝ), F (x + (k : ℝ) * (2 * Real.pi)) =
            ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
             (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi))) ∧
          ((m ≠ 0 ∨ n ≠ 0) → Function.Injective F) ∧
          (∀ (x y : ℝ) (a b : ℤ),
            F x = ((F y).1 + (a : ℝ) * (2 * Real.pi), (F y).2 + (b : ℝ) * (2 * Real.pi)) →
            ∃ k : ℤ, a = k * m ∧ b = k * n) := by
      have lifting (f : C(Circle, Circle)) :
          ∃ (k : ℤ) (F : C(ℝ, ℝ)),
            (∀ x : ℝ, Circle.exp (F x) = f (Circle.exp x)) ∧
            (∀ x : ℝ, F (x + 2 * Real.pi) = F x + (k : ℝ) * (2 * Real.pi)) := by
        let g : C(ℝ, Circle) := f.comp ⟨Circle.exp, by fun_prop⟩
        obtain ⟨r, hr⟩ := Circle.exp_surjective (g 0)
        obtain ⟨F, hF, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g 0 r hr
        have hFexp (x : ℝ) : Circle.exp (F x) = f (Circle.exp x) := congrFun hF.2 x
        have hperiod : Circle.exp (F (2 * Real.pi)) = Circle.exp (F 0) := by
          rw [hFexp, hFexp]
          simp
        obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hperiod
        let F₁ : C(ℝ, ℝ) := ⟨fun x => F (x + 2 * Real.pi), by fun_prop⟩
        let F₂ : C(ℝ, ℝ) := ⟨fun x => F x + (k : ℝ) * (2 * Real.pi), by fun_prop⟩
        have he : Circle.exp ∘ F₁ = Circle.exp ∘ F₂ := by
          funext x
          change Circle.exp (F (x + 2 * Real.pi)) = Circle.exp (F x + (k : ℝ) * (2 * Real.pi))
          rw [hFexp, Circle.exp_add, Circle.exp_two_pi, mul_one,
            Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one, hFexp]
        have hzero : F₁ 0 = F₂ 0 := by simpa [F₁, F₂] using hk
        have hEq : F₁ = F₂ := DFunLike.coe_injective
          (Circle.isCoveringMap_exp.eq_of_comp_eq F₁.continuous F₂.continuous he 0 hzero)
        refine ⟨k, F, hFexp, ?_⟩
        intro x
        exact congrArg (fun A : C(ℝ, ℝ) => A x) hEq
      let f₁ : C(Circle, Circle) := ⟨fun z => (c.map z).1, continuous_fst.comp c.embedded.continuous⟩
      let f₂ : C(Circle, Circle) := ⟨fun z => (c.map z).2, continuous_snd.comp c.embedded.continuous⟩
      obtain ⟨m, A, hA, hpA⟩ := lifting f₁
      obtain ⟨n, B, hB, hpB⟩ := lifting f₂
      have all_period (k : ℤ) (F : C(ℝ, ℝ))
          (hp : ∀ x, F (x + 2 * Real.pi) = F x + (k : ℝ) * (2 * Real.pi)) :
          ∀ (j : ℤ) (x : ℝ), F (x + (j : ℝ) * (2 * Real.pi)) =
            F x + (j : ℝ) * (k : ℝ) * (2 * Real.pi) := by
        have h : Function.Periodic (fun x => F x - (k : ℝ) * x) (2 * Real.pi) := by
          intro x
          dsimp
          rw [hp]
          ring
        intro j x
        have hj := h.int_mul j x
        change F (x + (j : ℝ) * (2 * Real.pi)) - (k : ℝ) * (x + (j : ℝ) * (2 * Real.pi)) = F x - (k : ℝ) * x at hj
        linarith
      let F : C(ℝ, ℝ × ℝ) := A.prodMk B
      have hproj (x : ℝ) : (Circle.exp (F x).1, Circle.exp (F x).2) = c.map (Circle.exp x) :=
        Prod.ext (hA x) (hB x)
      have hperiod (k : ℤ) (x : ℝ) : F (x + (k : ℝ) * (2 * Real.pi)) =
          ((F x).1 + (k : ℝ) * (m : ℝ) * (2 * Real.pi),
           (F x).2 + (k : ℝ) * (n : ℝ) * (2 * Real.pi)) :=
        Prod.ext (all_period m A hpA k x) (all_period n B hpB k x)
      refine ⟨m, n, F, hproj, hperiod, ?_⟩
      constructor
      · intro hnonzero x y hxy
        have he : Circle.exp x = Circle.exp y := c.embedded.injective
          ((hproj x).symm.trans ((congrArg (fun v : ℝ × ℝ => (Circle.exp v.1, Circle.exp v.2)) hxy).trans (hproj y)))
        obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
        have hper := hperiod k y
        rw [← hk, hxy] at hper
        have h1 := congrArg Prod.fst hper
        have h2 := congrArg Prod.snd hper
        dsimp at h1 h2
        have hk0 : (k : ℝ) = 0 := by
          rcases hnonzero with hm | hn
          · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
            have hz : (k : ℝ) * (m : ℝ) * (2 * Real.pi) = 0 := by linarith
            rcases mul_eq_zero.mp hz with h | h
            · exact (mul_eq_zero.mp h).resolve_right hm'
            · exact False.elim ((ne_of_gt (mul_pos (by norm_num) Real.pi_pos)) h)
          · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
            have hz : (k : ℝ) * (n : ℝ) * (2 * Real.pi) = 0 := by linarith
            rcases mul_eq_zero.mp hz with h | h
            · exact (mul_eq_zero.mp h).resolve_right hn'
            · exact False.elim ((ne_of_gt (mul_pos (by norm_num) Real.pi_pos)) h)
        simpa [hk0] using hk
      · intro x y a b hxy
        have he : Circle.exp x = Circle.exp y := by
          apply c.embedded.injective
          rw [← hproj x, ← hproj y, hxy]
          simp only [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
        obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
        have hp := hperiod k y
        rw [← hk, hxy] at hp
        have h1 := congrArg Prod.fst hp
        have h2 := congrArg Prod.snd hp
        dsimp at h1 h2
        refine ⟨k, ?_, ?_⟩
        · have ha : (a : ℝ) = (k : ℝ) * (m : ℝ) := by
            nlinarith [Real.pi_pos]
          exact_mod_cast ha
        · have hb : (b : ℝ) = (k : ℝ) * (n : ℝ) := by
            nlinarith [Real.pi_pos]
          exact_mod_cast hb
    have proper (F : C(ℝ, ℝ × ℝ)) (m n : ℤ)
        (hp : ∀ x : ℝ, F (x + 2 * Real.pi) =
          ((F x).1 + (m : ℝ) * (2 * Real.pi),
           (F x).2 + (n : ℝ) * (2 * Real.pi)))
        (hnonzero : m ≠ 0 ∨ n ≠ 0) :
        IsProperMap F ∧ (Function.Injective F → Topology.IsClosedEmbedding F) := by
      have hproper : IsProperMap F := by
        have scalar (f : C(ℝ, ℝ)) (a : ℝ) (ha : a ≠ 0)
            (hperiod : ∀ x, f (x + 2 * Real.pi) = f x + a * (2 * Real.pi)) :
            IsProperMap f := by
          let B : ℝ → ℝ := fun x => f x - a * x
          have hB : Continuous B := by dsimp [B]; fun_prop
          have hper : Function.Periodic B (2 * Real.pi) := by
            intro x
            dsimp [B]
            rw [hperiod]
            ring
          have hrange : IsCompact (Set.range B) := by
            rw [← hper.image_Icc (mul_pos (by norm_num) Real.pi_pos) 0]
            exact isCompact_Icc.image hB
          obtain ⟨M, hM⟩ := (hrange.image continuous_norm).bddAbove
          have hbound (x : ℝ) : ‖B x‖ ≤ M := hM ⟨B x, ⟨x, rfl⟩, rfl⟩
          have hlinear (x : ℝ) : ‖a‖ * ‖x‖ ≤ ‖f x‖ + M := by
            have h := norm_sub_le (f x) (B x)
            have he : f x - B x = a * x := by dsimp [B]; ring
            rw [he, norm_mul] at h
            linarith [hbound x]
          apply isProperMap_iff_tendsto_cocompact.mpr
          refine ⟨f.continuous, Filter.tendsto_cocompact_cocompact_of_norm ?_⟩
          intro ε
          refine ⟨(ε + M) / ‖a‖, ?_⟩
          intro x hx
          have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
          have hh := (div_lt_iff₀ ha').mp hx
          have hb := hlinear x
          nlinarith
        rcases hnonzero with hm | hn
        · let f : C(ℝ, ℝ) := ⟨fun x => (F x).1, continuous_fst.comp F.continuous⟩
          apply isProperMap_of_comp_of_t2 F.continuous continuous_fst
          apply scalar f (m : ℝ) (by exact_mod_cast hm)
          intro x
          exact congrArg Prod.fst (hp x)
        · let f : C(ℝ, ℝ) := ⟨fun x => (F x).2, continuous_snd.comp F.continuous⟩
          apply isProperMap_of_comp_of_t2 F.continuous continuous_snd
          apply scalar f (n : ℝ) (by exact_mod_cast hn)
          intro x
          exact congrArg Prod.snd (hp x)
      exact ⟨hproper, fun hinj =>
        Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
          F.continuous hinj hproper.isClosedMap⟩
    obtain ⟨m, n, F, hproj, hperiod, hinj, hcollision⟩ := hlift
    refine ⟨m, n, F, hproj, hperiod, ?_, hcollision⟩
    intro hnonzero
    have hp (x : ℝ) : F (x + 2 * Real.pi) =
        ((F x).1 + (m : ℝ) * (2 * Real.pi), (F x).2 + (n : ℝ) * (2 * Real.pi)) := by
      simpa using hperiod 1 x
    obtain ⟨hproper, hclosed⟩ := proper F m n hp hnonzero
    exact ⟨hproper, hclosed (hinj hnonzero)⟩
  obtain ⟨m, n, F, hproj, hperiod, hproper, hcollision⟩ := lifting c
  refine ⟨m, n, F, hproj, hperiod, ?_, hcollision⟩
  intro hnonzero
  obtain ⟨hp, he⟩ := hproper hnonzero
  exact ⟨primitive F m n hp he.injective hnonzero hperiod hcollision, hp, he⟩

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
