import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.FreeBoundaryContactDropGeometry
import CurveComplexGenusTwo.Topology.ActualFreeBoundarySupportedContactDrop.ChartDeletedDiskFrontier

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies
open RegionalEmbeddedFamily

/-- Produce actual same-side local geometry or crossings at EVERY strict
interior contact of the same original pair. No local normal form is assumed. -/
theorem source_actual_original_free_boundary_finite_contact_dichotomy
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
    ∀ (a b : C(Interval, ↥Q)),
      IsEmbedding a → IsEmbedding b →
      (a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range a ∪ range c) →
      (¬ ∃ c : C(Interval, ↥Q), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥Q),
          IsEmbedding d ∧ d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            range b ∪ range c) →
      Disjoint ({a 0, a 1} : Set ↥Q) {b 0, b 1} →
      (range a ∩ range b).Finite →
      (∃ H : AmbientIsotopy ↥Q,
        (∀ t, (fun y => H.map (t, y)) '' B = B) ∧
        H.finalMap '' range a = range b) →
      (∃ (r s : Interval) (C : RegionalIsolatedContactChart Q a b r s),
        C.SameSide) ∨ RegionalAllInteriorContactsCross Q a b := by
  classical
  intro Q B a b ha hb hend hint haess hbess hends hfinite hclass
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hfront : frontier Q =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R :=
    CoherentEndpointMotion.chart_deleted_disk_complement_frontier _ _ R hR htarget
  by_cases hsame : ∃ (r s : Interval)
      (C : RegionalIsolatedContactChart Q a b r s), C.SameSide
  · exact Or.inl hsame
  · refine Or.inr ?_
    intro r s hr hs hrs
    have hp : (a r).val ∈ interior Q := by
      by_contra hn
      have hf : (a r).val ∈ frontier Q := ⟨subset_closure (a r).property, hn⟩
      rw [hfront] at hf
      exact (hint r hr).1 hf
    obtain ⟨C, hC⟩ := regional_finite_contact_has_isolated_contact_chart
      Q a b ha hb hfinite r s hr hs hrs hp
    rcases hC with hsameC | hcross
    · exact (hsame ⟨r, s, C, hsameC⟩).elim
    · exact ⟨C, hcross⟩


end CoherentEndpointMotion.FreeBoundaryContactRepair
