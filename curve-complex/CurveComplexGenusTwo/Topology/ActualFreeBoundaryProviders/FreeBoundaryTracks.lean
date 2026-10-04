import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryPairCore
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryCircle
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Topology.GlobalMonodromy.GlobalLoopSubdivision
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.Lifting

namespace CoherentEndpointMotion.FreeBoundaryContactRepair

open CurveComplex Set Topology
open CurveComplex.BranchedDoubleCover

universe v

theorem source_actual_boundary_track_pair_normalization
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (τ : Fin 2 → C(Interval, ↥Q)),
      (∀ i t, τ i t ∈ B) →
      (∀ t, τ 0 t ≠ τ 1 t) →
      (∀ i, τ i 0 ≠ τ i 1) →
      ∃ (β : Circle ≃ₜ ↥B) (θ : Fin 2 → C(Interval, ℝ))
        (ℓ : Fin 2 → C(Interval, ↥Q))
        (J : ∀ i, ContinuousMap.HomotopyRel (τ i) (ℓ i) ({0, 1} : Set Interval)),
        (range (fun z : Circle => (β z).val) = B) ∧
        (∀ i t, (β (Circle.exp (θ i t))).val = τ i t) ∧
        (∀ t, 0 < θ 1 t - θ 0 t ∧ θ 1 t - θ 0 t < 2 * Real.pi) ∧
        (∀ i, θ i 0 ≠ θ i 1) ∧
        (∀ i t, ℓ i t =
          (β (Circle.exp ((1 - t.val) * θ i 0 + t.val * θ i 1))).val) ∧
        (∀ i, ℓ i 0 = τ i 0 ∧ ℓ i 1 = τ i 1) ∧
        (∀ i r t, J i (r, t) =
          (β (Circle.exp ((1 - r.val) * θ i t +
            r.val * ((1 - t.val) * θ i 0 + t.val * θ i 1)))).val) ∧
        (∀ i t, J i (0, t) = τ i t ∧ J i (1, t) = ℓ i t) ∧
        (∀ i r, J i (r, 0) = τ i 0 ∧ J i (r, 1) = τ i 1) ∧
        (∀ i r t, J i (r, t) ∈ B) ∧
        (∀ r t, J 0 (r, t) ≠ J 1 (r, t)) ∧
        (∀ t, ℓ 0 t ≠ ℓ 1 t) ∧
        (∀ (Y : Type v) [TopologicalSpace Y]
          (p : Y → ↥Q), IsCoveringMap p →
          ∀ (T : Fin 2 → C(Interval, Y)),
            (∀ i t, p (T i t) = τ i t) →
            ∃ L : Fin 2 → C(Interval, Y),
              (∀ i t, p (L i t) = ℓ i t) ∧
              (∀ i, L i 0 = T i 0 ∧ L i 1 = T i 1)) := by
  intro Q B τ hB hne hstart
  letI : ClosedSurface S := hS.2.1.some
  obtain ⟨β⟩ := actual_boundary_circle S x R hR htarget
  obtain ⟨θ, ℓ, J, hτ, hgap, hℓ, hend, hJ, hJ01, hJend, hJB, hJneq, hℓneq, hcover⟩ :=
    boundary_pair_affine_normalization.{0, v} β τ hB hne
  refine ⟨β, θ, ℓ, J, ?_, hτ, hgap, ?_, hℓ, hend, hJ, hJ01, hJend, hJB, hJneq, hℓneq, hcover⟩
  · ext y
    constructor
    · rintro ⟨z, rfl⟩; exact (β z).property
    · intro hy
      exact ⟨β.symm ⟨y, hy⟩, congrArg Subtype.val (β.apply_symm_apply _)⟩
  · intro i he
    apply hstart i
    rw [← hτ i 0, ← hτ i 1, he]

theorem source_actual_affine_boundary_track_finite_contacts
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (β : Circle ≃ₜ ↥B) (u v : ℝ), u ≠ v →
      ∀ (ℓ : C(Interval, ↥Q)),
        (∀ t, ℓ t = (β (Circle.exp ((1 - t.val) * u + t.val * v))).val) →
        ∀ (P : Set ↥Q), P.Finite → {t : Interval | ℓ t ∈ P}.Finite := by
  intro Q B β u v huv ℓ hℓ P hP
  exact affineBoundary_finite_contacts β huv ℓ hℓ P hP

theorem source_actual_affine_boundary_track_two_marker_subsegment
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (β : Circle ≃ₜ ↥B) (u v : ℝ), u ≠ v →
      ∀ (ℓ : C(Interval, ↥Q)),
        (∀ t, ℓ t = (β (Circle.exp ((1 - t.val) * u + t.val * v))).val) →
        ∀ (x₀ x₁ : ↥Q), x₀ ∈ B → x₁ ∈ B → x₀ ≠ x₁ →
          ∀ (l r : Interval), l < r →
            ℓ l ∈ ({x₀, x₁} : Set ↥Q) → ℓ r ∈ ({x₀, x₁} : Set ↥Q) →
            (∀ t : Interval, l < t → t < r → ℓ t ∉ ({x₀, x₁} : Set ↥Q)) →
            IsEmbedding (fun t : Interval => ℓ (intervalAffine l r t)) ∧
              ({ℓ l, ℓ r} : Set ↥Q) = {x₀, x₁} := by
  intro Q B β u v huv ℓ hℓ x₀ x₁ hx₀ hx₁ hx l r hlr hl hr havoid
  exact affineBoundary_two_marker β huv ℓ hℓ x₀ x₁ hx₀ hx₁ hx hlr hl hr havoid

theorem source_actual_affine_boundary_track_one_marker_subsegment
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target) :
    let Q : Set S := ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R}
    ∀ (β : Circle ≃ₜ ↥B) (u v : ℝ), u ≠ v →
      ∀ (ℓ : C(Interval, ↥Q)),
        (∀ t, ℓ t = (β (Circle.exp ((1 - t.val) * u + t.val * v))).val) →
        ∀ (z : ↥Q), z ∈ B →
          ∀ (l r : Interval), l < r → ℓ l = z →
            (∀ t : Interval, l < t → t ≤ r → ℓ t ≠ z) →
            IsEmbedding (fun t : Interval => ℓ (intervalAffine l r t)) := by
  intro Q B β u v huv ℓ hℓ z hz l r hlr hl havoid
  exact affineBoundary_one_marker β huv ℓ hℓ hlr (by
    intro t hlt htr
    rw [hl]
    exact havoid t hlt htr)

end CoherentEndpointMotion.FreeBoundaryContactRepair
