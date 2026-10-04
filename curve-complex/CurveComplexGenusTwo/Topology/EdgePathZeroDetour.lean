import CurveComplexGenusTwo.Topology.CurveCombinatorics

/-!
Scratch packet for the combinatorial part of Section 7.

The surface-specific regular-neighborhood construction is represented only by
the explicit `FillsIntersectionOneEdge` hypothesis from `CurveCombinatorics`.
The theorem below lifts any finite/refl-transitive `C₁` edge path to a `C₀`
edge path, which is the relation-level core of Lemma 7.6.
-/

namespace CurveComplexGenusTwo.Topology

variable {V : Type*} [DecidableEq V]

/-- A nontrivial edge in the `d`-curve complex, expressed only through
the intersection bound. -/
def EdgeLe (intersect : V → V → ℕ) (d : ℕ) (a b : V) : Prop :=
  a ≠ b ∧ intersect a b ≤ d

/-- Once the regular-neighborhood construction supplies its actual geometric
intersection data, all face conditions in Lemma 7.5 follow formally. -/
theorem fillsIntersectionOneEdge_of_geometric_data
    (intersect : V → V → ℕ)
    (hsym : ∀ x y, intersect x y = intersect y x)
    {a b c : V} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hab1 : intersect a b = 1)
    (hac0 : intersect a c = 0) (hbc0 : intersect b c = 0) :
    FillsIntersectionOneEdge intersect a b c := by
  have htri : CurveFace intersect 1 ({a, b, c} : Finset V) := by
    intro x hx y hy hxy
    change x ∈ ({a, b, c} : Finset V) at hx
    change y ∈ ({a, b, c} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    all_goals simp_all
  have hacface : CurveFace intersect 0 ({a, c} : Finset V) := by
    intro x hx y hy hxy
    change x ∈ ({a, c} : Finset V) at hx
    change y ∈ ({a, c} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals simp_all
  have hbcface : CurveFace intersect 0 ({b, c} : Finset V) := by
    intro x hx y hy hxy
    change x ∈ ({b, c} : Finset V) at hx
    change y ∈ ({b, c} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals simp_all
  exact ⟨hab, hbc, hac, hab1, hac0, hbc0, htri, hacface, hbcface⟩

theorem fillsIntersectionOneEdge_zero_edges
    (intersect : V → V → ℕ) {a b c : V}
    (hsym : ∀ x y, intersect x y = intersect y x)
    (h : FillsIntersectionOneEdge intersect a b c) :
    EdgeLe intersect 0 a c ∧ EdgeLe intersect 0 c b := by
  rcases h with ⟨hab, hbc, hac, hab1, hac0, hbc0, htri, hacface, hbcface⟩
  constructor
  · exact ⟨hac, by simpa using hac0⟩
  · exact ⟨Ne.symm hbc, by simp [hsym, hbc0]⟩

/-- Every `C₁` edge expands to a `C₀` path when the source-specific third
curve exists for intersection-one edges. -/
theorem edgeLe_one_to_zero_reflTransGen
    (intersect : V → V → ℕ)
    (hsym : ∀ x y, intersect x y = intersect y x)
    (hfill : ∀ a b, a ≠ b → intersect a b = 1 →
      ∃ c, FillsIntersectionOneEdge intersect a b c) {a b : V}
    (hab : Relation.ReflTransGen (EdgeLe intersect 1) a b) :
    Relation.ReflTransGen (EdgeLe intersect 0) a b := by
  have hstep : (EdgeLe intersect 1) ≤
      Relation.ReflTransGen (EdgeLe intersect 0) := by
    intro x y hxy
    by_cases hzero : intersect x y = 0
    · exact Relation.ReflTransGen.single ⟨hxy.1, by simp [hzero]⟩
    · have hle : intersect x y ≤ 1 := hxy.2
      have hone : intersect x y = 1 := by omega
      obtain ⟨z, hz⟩ := hfill x y hxy.1 hone
      have hdetour := fillsIntersectionOneEdge_zero_edges intersect hsym hz
      exact (Relation.ReflTransGen.single hdetour.1).trans
        (Relation.ReflTransGen.single hdetour.2)
  exact Relation.reflTransGen_closed hstep a b hab

/-- The explicit connectivity consequence of the finite edge detour. -/
theorem edgeLe_zero_connected_of_one_connected
    (intersect : V → V → ℕ)
    (hsym : ∀ x y, intersect x y = intersect y x)
    (hfill : ∀ a b, a ≠ b → intersect a b = 1 →
      ∃ c, FillsIntersectionOneEdge intersect a b c)
    (hconnected : ∀ a b : V,
      Relation.ReflTransGen (EdgeLe intersect 1) a b) :
    ∀ a b : V, Relation.ReflTransGen (EdgeLe intersect 0) a b := by
  intro a b
  exact edgeLe_one_to_zero_reflTransGen intersect hsym hfill (hconnected a b)

end CurveComplexGenusTwo.Topology
