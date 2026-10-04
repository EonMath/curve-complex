import CurveComplexGenusTwo.Hyperbolic.CompactDoubleSphere
import CurveComplexGenusTwo.Hyperbolic.FiniteSphereConfiguration
import CurveComplexGenusTwo.Hyperbolic.FiniteRightHexagon
import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex.Hyperbolic
open Filter Topology MeasureTheory
open scoped Manifold ContDiff UpperHalfPlane MeasureTheory

abbrev DoubledPolygon {P : Hexagon} (R : HexagonRegion P) :=
  Metric.GlueSpace (boundaryInclusion_isometry R)
    (boundaryInclusion_isometry R)

noncomputable def doubledVertex (P : Hexagon) (R : HexagonRegion P)
    (i : Fin 6) : DoubledPolygon R :=
  Metric.toGlueL (boundaryInclusion_isometry R)
    (boundaryInclusion_isometry R)
    ⟨P.vertex i, hexagon_vertex_mem_closure P R i⟩

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [originalAtlas : ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem compact_cone_model_for_actual_marked_sphere
    (M : HyperellipticModel E S) :
    ∃ P : Hexagon, P.IsRegularRight ∧
      ∃ R : HexagonRegion P, ∃ identify : S ≃ₜ DoubledPolygon R,
        ∀ b : S, b ∈ M.cover.branch ↔
          identify b ∈ Set.range (doubledVertex P R) := by
  classical
  let P := regularHexagonCandidate
  let R := regularHexagonRegion
  obtain ⟨d⟩ := regularHexagon_double_is_sphere
  let e : Fin 6 ≃ M.cover.branch := (Finset.equivFinOfCardEq M.cover.branch_card).symm
  let a (i : Fin 6) := M.sphere (e i).val
  let b (i : Fin 6) := d (doubledVertex P R i)
  have ha : Function.Injective a := M.sphere.injective.comp (Subtype.val_injective.comp e.injective)
  have hb : Function.Injective b := d.injective.comp (polygon_double_vertex_injective R)
  obtain ⟨h, hh⟩ := finite_sphere_configuration_transport a b ha hb
  let identify : S ≃ₜ DoubledPolygon R := M.sphere.trans (h.trans d.symm)
  refine ⟨P, regularHexagonCandidate_isRegularRight, R, identify, ?_⟩
  intro x
  have he (i : Fin 6) : identify (e i).val = doubledVertex P R i := by
    change d.symm (h (a i)) = doubledVertex P R i
    rw [hh]
    exact d.symm_apply_apply _
  constructor
  · intro hx
    let i := e.symm ⟨x, hx⟩
    refine ⟨i, ?_⟩
    have hi : (e i).val = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    exact (he i).symm.trans (congrArg identify hi)
  · rintro ⟨i, hi⟩
    have hx : x = (e i).val := identify.injective (hi.symm.trans (he i).symm)
    rw [hx]
    exact (e i).property

end CurveComplex.Hyperbolic
