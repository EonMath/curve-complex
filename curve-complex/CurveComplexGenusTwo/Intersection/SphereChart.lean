import CurveComplexGenusTwo.Dictionary.MarkedSphere
import Mathlib.Geometry.Manifold.Instances.Sphere
import Schoenflies.JordanClosed

namespace CurveComplex.HyperellipticModel

/-- The stereographic chart at any specified point of the concrete sphere. -/
noncomputable def puncturedSpherePlane
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 // x ≠ p} ≃ₜ
      EuclideanSpace ℝ (Fin 2) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e := stereographic' 2 p
  exact (Homeomorph.setCongr (by ext x; change (x ≠ p) ↔ x ∈ e.source; simp [e])).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (by simp [e])).trans
        (Homeomorph.Set.univ _)))

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A chart at any chosen point of the model sphere. -/
noncomputable def puncturedPlane
    (M : HyperellipticModel E S) (p : S) :
    {x : S // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  (M.sphere.subtype (fun x => by
    constructor
    · intro hx he; exact hx (M.sphere.injective he)
    · intro hx he; exact hx (congrArg M.sphere he))).trans
    (puncturedSpherePlane (M.sphere p))

/-- One of the six branch marks can be used as a puncture off a non-loop arc. -/
theorem NonLoopArc.exists_marked_puncture
    {M : HyperellipticModel E S} (a : NonLoopArc M) :
    ∃ p ∈ M.cover.branch, p ∉ a.image := by
  classical
  by_contra h
  push Not at h
  have hsubset : M.cover.branch ⊆
      ({a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩} : Finset S) := by
    intro x hx
    have hxA : x ∈ a.val.image := h x hx
    have hxE : x ∈ ({a.val.map ⟨0, by norm_num⟩,
        a.val.map ⟨1, by norm_num⟩} : Set S) := by
      rw [← a.image_inter_branch]
      exact ⟨hxA, hx⟩
    simpa using hxE
  have hcard := Finset.card_le_card hsubset
  rw [M.cover.branch_card] at hcard
  have htwo : ({a.val.map ⟨0, by norm_num⟩,
      a.val.map ⟨1, by norm_num⟩} : Finset S).card ≤ 2 := Finset.card_le_two
  omega

/-- Every non-loop arc has a stereographic plane chart punctured at another
actual branch mark. -/
theorem NonLoopArc.exists_marked_plane_chart
    {M : HyperellipticModel E S} (a : NonLoopArc M) :
    ∃ p ∈ M.cover.branch,
      p ∉ a.image ∧ Nonempty ({x : S // x ≠ p} ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  obtain ⟨p, hp, hpa⟩ := a.exists_marked_puncture
  exact ⟨p, hp, hpa, ⟨M.puncturedPlane p⟩⟩

/-- In a stereographic chart avoiding it, the original parametrized arc is
exactly an `IsArcBetween` of the plane Schoenflies interface. -/
theorem NonLoopArc.plane_isArcBetween
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p : S) (hp : p ∉ a.image) :
    let g : Interval → Schoenflies.Plane := fun t =>
      M.puncturedPlane p ⟨a.val.map t, by
        intro he
        exact hp (he ▸ Set.mem_range_self t)⟩
    Schoenflies.IsArcBetween (Set.range g)
      (g ⟨0, by norm_num⟩) (g ⟨1, by norm_num⟩) := by
  let g : Interval → Schoenflies.Plane := fun t =>
    M.puncturedPlane p ⟨a.val.map t, by
      intro he
      exact hp (he ▸ Set.mem_range_self t)⟩
  have hg : Continuous g := (M.puncturedPlane p).continuous.comp
    (Continuous.subtype_mk a.val.continuous _)
  let f : ℝ → Schoenflies.Plane := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) 1 then g ⟨t, ht⟩
    else g ⟨0, by norm_num⟩
  have hf (t : Interval) : f t = g t := dite_eq_left t.property
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuousOn_iff_continuous_domRestrict).2 (by
      convert hg using 1
      funext t
      exact hf t)
  · intro t ht u hu htu
    have hgeq : g ⟨t, ht⟩ = g ⟨u, hu⟩ := by
      exact (hf ⟨t, ht⟩).symm.trans (htu.trans (hf ⟨u, hu⟩))
    have hae : a.val.map ⟨t, ht⟩ = a.val.map ⟨u, hu⟩ :=
      congrArg Subtype.val ((M.puncturedPlane p).injective hgeq)
    exact congrArg Subtype.val (a.injective hae)
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (hf ⟨t, ht⟩).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t.1, t.2, hf t⟩
  · exact hf ⟨0, by norm_num⟩
  · exact hf ⟨1, by norm_num⟩

/-- From any point off the projected arc, the plane Schoenflies theorem gives
a simple polygonal escape path to a second point off the arc. This is the
barrier construction needed to keep forbidden marks outside a later disk. -/
theorem NonLoopArc.exists_polygonal_escape
    {M : HyperellipticModel E S} (a : NonLoopArc M)
    (p x : S) (hp : p ∉ a.image) (hxp : x ≠ p) (hx : x ∉ a.image)
    (w : Schoenflies.Plane)
    (hw : w ∉ Set.range (fun t : Interval =>
      M.puncturedPlane p ⟨a.val.map t, by
        intro he
        exact hp (he ▸ Set.mem_range_self t)⟩))
    (huw : M.puncturedPlane p ⟨x, hxp⟩ ≠ w) :
    let g : Interval → Schoenflies.Plane := fun t =>
      M.puncturedPlane p ⟨a.val.map t, by
        intro he
        exact hp (he ▸ Set.mem_range_self t)⟩
    ∃ P : Set Schoenflies.Plane,
      Schoenflies.IsPolygonal P ∧
      Schoenflies.IsArcBetween P (M.puncturedPlane p ⟨x, hxp⟩) w ∧
      P ⊆ (Set.range g)ᶜ := by
  let g : Interval → Schoenflies.Plane := fun t =>
    M.puncturedPlane p ⟨a.val.map t, by
      intro he
      exact hp (he ▸ Set.mem_range_self t)⟩
  have hArc : Schoenflies.IsArc (Set.range g) :=
    (a.plane_isArcBetween p hp).isArc
  have hu : M.puncturedPlane p ⟨x, hxp⟩ ∉ Set.range g := by
    rintro ⟨t, ht⟩
    have heq : x = a.val.map t :=
      congrArg Subtype.val ((M.puncturedPlane p).injective ht.symm)
    exact hx ⟨t, heq.symm⟩
  exact Schoenflies.arc_complement_poly hArc huw hu hw

end CurveComplex.HyperellipticModel
