import Schoenflies.JordanClosed
import Schoenflies.JordanSchoenflies
import Mathlib.Topology.Compactification.OnePoint.Sphere

namespace CurveComplex.SpherePort

abbrev Sphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
abbrev Interval := Set.Icc (0 : ℝ) 1

/-- A parametrized simple closed curve on the actual metric sphere. -/
structure JordanCurve where
  map : Interval → Sphere
  continuous : Continuous map
  injective_except_ends : ∀ t u, map t = map u →
    t = u ∨
      (t = ⟨0, by norm_num⟩ ∧ u = ⟨1, by norm_num⟩) ∨
      (t = ⟨1, by norm_num⟩ ∧ u = ⟨0, by norm_num⟩)
  closed : map ⟨0, by norm_num⟩ = map ⟨1, by norm_num⟩

def JordanCurve.image (c : JordanCurve) : Set Sphere := Set.range c.map

/-- A puncture chosen off the circle, with a genuine punctured-plane chart. -/
structure Chart (c : JordanCurve) where
  puncture : Sphere
  avoids : puncture ∉ c.image
  plane : {x : Sphere // x ≠ puncture} ≃ₜ Schoenflies.Plane

def Chart.planeImage (c : JordanCurve) (P : Chart c) :
    Set Schoenflies.Plane :=
  P.plane '' {x : {x : Sphere // x ≠ P.puncture} | (x : Sphere) ∈ c.image}

def Chart.pullback (c : JordanCurve) (P : Chart c)
    (A : Set Schoenflies.Plane) : Set Sphere :=
  {x | ∃ hx : x ≠ P.puncture, P.plane ⟨x, hx⟩ ∈ A}

/-- The one-point compactification is the concrete sphere on the dictionary
side as well. -/
noncomputable def onePointSphere : OnePoint Schoenflies.Plane ≃ₜ Sphere :=
  onePointEquivSphereOfFinrankEq (by simp [Schoenflies.Plane])

/-- The circle parametrization survives the puncture chart and satisfies the
port's exact `IsJordanCurve` predicate. -/
theorem chart_image_jordan (c : JordanCurve) (P : Chart c) :
    Schoenflies.IsJordanCurve (P.planeImage c) := by
  let g : Interval → Schoenflies.Plane := fun t =>
    P.plane ⟨c.map t, by
      intro hp
      exact P.avoids (hp ▸ Set.mem_range_self t)⟩
  have hg : Continuous g := P.plane.continuous.comp
    (Continuous.subtype_mk c.continuous _)
  let f : ℝ → Schoenflies.Plane := fun t =>
    if ht : t ∈ Interval then g ⟨t, ht⟩ else g ⟨0, by norm_num⟩
  have hf (t : Interval) : f t = g t := by
    exact dif_pos t.property
  refine ⟨f, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (continuousOn_iff_continuous_domRestrict).2 (by
        convert hg using 1
        funext t
        exact hf t)
    · have hclosed : g ⟨0, by norm_num⟩ = g ⟨1, by norm_num⟩ := by
        apply congrArg P.plane
        exact Subtype.ext c.closed
      exact (hf _).trans (hclosed.trans (hf _).symm)
    · intro t ht u hu htu
      have hgeq : g ⟨t, ⟨ht.1, ht.2.le⟩⟩ =
          g ⟨u, ⟨hu.1, hu.2.le⟩⟩ :=
        (hf ⟨t, ⟨ht.1, ht.2.le⟩⟩).symm.trans
          (htu.trans (hf ⟨u, ⟨hu.1, hu.2.le⟩⟩))
      have hcu : c.map ⟨t, ⟨ht.1, ht.2.le⟩⟩ =
          c.map ⟨u, ⟨hu.1, hu.2.le⟩⟩ := by
        exact congrArg Subtype.val (P.plane.injective hgeq)
      rcases c.injective_except_ends _ _ hcu with h | h | h
      · exact congrArg Subtype.val h
      · exact False.elim ((ne_of_lt hu.2) (congrArg Subtype.val h.2))
      · exact False.elim ((ne_of_lt ht.2) (congrArg Subtype.val h.1))
  · ext z
    simp only [Set.mem_image, Chart.planeImage]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨c.map ⟨t, ht⟩, by
        intro hp
        exact P.avoids (hp ▸ Set.mem_range_self (⟨t, ht⟩ : Interval))⟩,
        ⟨⟨t, ht⟩, rfl⟩, (hf ⟨t, ht⟩).symm⟩
    · rintro ⟨x, ⟨t, htx⟩, rfl⟩
      refine ⟨t, t.property, ?_⟩
      rw [hf]
      exact congrArg P.plane (Subtype.ext htx)

/-- Transport the port's bounded plane side to the sphere. -/
def Chart.inside (c : JordanCurve) (P : Chart c) : Set Sphere :=
  P.pullback c (Schoenflies.inside (P.planeImage c))

/-- The unbounded plane side includes the chosen puncture on the sphere. -/
def Chart.outside (c : JordanCurve) (P : Chart c) : Set Sphere :=
  {P.puncture} ∪ P.pullback c (Schoenflies.outside (P.planeImage c))

end CurveComplex.SpherePort
