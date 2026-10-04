import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.CurveCombinatorics

/-!
Concrete primitive-slope embedded circles in the product torus. The map has
winding numbers `m,n` in the two circle factors. The proof of injectivity
uses the integer Bézout identity through `pow_intGCD_eq_one`.
-/

namespace CurveComplexGenusTwo.Topology

open CurveComplex
open _root_.Topology

noncomputable def torusWindingMap (m n : ℤ) (z : Circle) : Circle × Circle :=
  (z ^ m, z ^ n)

theorem continuous_torusWindingMap (m n : ℤ) :
    Continuous (torusWindingMap m n) := by
  exact (continuous_zpow m).prodMk (continuous_zpow n)

theorem torusWindingMap_injective {m n : ℤ}
    (h : m.gcd n = 1) :
    Function.Injective (torusWindingMap m n) := by
  intro z w hzw
  have hm : z ^ m = w ^ m := congrArg Prod.fst hzw
  have hn : z ^ n = w ^ n := congrArg Prod.snd hzw
  have hratio_m : (z / w) ^ m = 1 := by
    rw [div_zpow, hm, div_self']
  have hratio_n : (z / w) ^ n = 1 := by
    rw [div_zpow, hn, div_self']
  have hratio : z / w = 1 := by
    have hg := (pow_intGCD_eq_one (a := z / w) (m := m) (n := n)).mpr
      ⟨hratio_m, hratio_n⟩
    simpa [h] using hg
  exact eq_of_div_eq_one hratio

theorem torusWindingMap_isEmbedding {m n : ℤ}
    (h : m.gcd n = 1) :
    IsEmbedding (torusWindingMap m n) := by
  exact ((continuous_torusWindingMap m n).isClosedEmbedding
    (torusWindingMap_injective h)).isEmbedding

noncomputable def primitiveTorusCurve (m n : ℤ) (h : m.gcd n = 1) :
    Curve (Circle × Circle) where
  map := torusWindingMap m n
  embedded := torusWindingMap_isEmbedding h

theorem rationalSlope_primitive (q : ℚ) :
    q.num.gcd (q.den : ℤ) = 1 := by
  simpa [Int.gcd] using q.reduced

/-- The reduced numerator and denominator produce an actual embedded curve
in the product torus. This is the finite-slope geometric producer. -/
noncomputable def rationalSlopeTorusCurve (q : ℚ) :
    Curve (Circle × Circle) :=
  primitiveTorusCurve q.num q.den (rationalSlope_primitive q)

/-- Infinity is the primitive circle with direction `(1,0)`. -/
noncomputable def infinitySlopeTorusCurve : Curve (Circle × Circle) :=
  primitiveTorusCurve 1 0 (by decide)

/-- Every project Farey slope now has an actual embedded-circle producer on
the product torus. The remaining work is essentiality, isotopy classification,
intersection calculation, puncture avoidance, and cut-side transfer. -/
noncomputable def fareySlopeTorusCurve :
    FareySlope → Curve (Circle × Circle)
  | none => infinitySlopeTorusCurve
  | some q => rationalSlopeTorusCurve q

/-- Reversing a primitive integral direction only reverses the parameter
and hence has the same embedded image. -/
theorem torusWindingMap_neg_range (m n : ℤ) :
    Set.range (torusWindingMap (-m) (-n)) =
      Set.range (torusWindingMap m n) := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨z⁻¹, ?_⟩
    simp [torusWindingMap]
  · rintro ⟨z, rfl⟩
    refine ⟨z⁻¹, ?_⟩
    simp [torusWindingMap]

theorem primitiveTorusCurve_neg_image (m n : ℤ)
    (h : m.gcd n = 1) :
    (primitiveTorusCurve (-m) (-n) (by simpa using h)).image =
      (primitiveTorusCurve m n h).image := by
  exact torusWindingMap_neg_range m n

end CurveComplexGenusTwo.Topology
