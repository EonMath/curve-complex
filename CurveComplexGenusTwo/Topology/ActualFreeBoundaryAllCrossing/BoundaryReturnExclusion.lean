import CurveComplexGenusTwo.Topology.ActualFreeBoundaryAllCrossing.MixedHalfBoundary
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.W81BoundaryOnlyReturn

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies FreeBoundaryNullGeometry
open CurveComplex.BranchedDoubleCover

theorem simple_boundary_lift_return_contradicts_essentiality
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (F : Set S) (B : Set ↥F)
    (a : C(Interval,↥F)) (ha : IsEmbedding a)
    (hai : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B)
    (haEssential : ¬ ∃ c : C(Interval,↥F), IsEmbedding c ∧ (∀ t, c t ∈ B) ∧
      ∃ d : C(Metric.closedBall (0 : Plane) 1,↥F), IsEmbedding d ∧
        d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} = range a ∪ range c)
    {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (p : X → ↥F) (hp : Continuous p)
    (E L : C(Interval,X)) (hEp : ∀ t, p (E t) = a t)
    (hLB : ∀ t, p (L t) ∈ B)
    (l r : Interval) (hl : L l ∈ range E) (hr : L r ∈ range E)
    (hseg : IsEmbedding (fun t => p (L (intervalAffine l r t)))) : False := by
  let c : C(Interval,↥F) := ⟨fun t => p (L (intervalAffine l r t)),by
    apply hp.comp; apply L.continuous.comp
    apply Continuous.subtype_mk; fun_prop⟩
  let J := arcSegment L l r
  obtain ⟨s,hs⟩ := hl
  obtain ⟨t,ht⟩ := hr
  have boundary_parameter (w : Interval) (hw : a w ∈ B) : w = 0 ∨ w = 1 := by
    by_contra hn
    push Not at hn
    exact hai w ⟨lt_of_le_of_ne w.property.1 hn.1.symm,
      lt_of_le_of_ne w.property.2 hn.2⟩ hw
  have hs01 := boundary_parameter s (by rw [← hEp,hs]; exact hLB l)
  have ht01 := boundary_parameter t (by rw [← hEp,ht]; exact hLB r)
  have hne : s ≠ t := by
    intro he
    have hc01 : c 0 = c 1 := by
      change p (L (intervalAffine l r 0)) = p (L (intervalAffine l r 1))
      simpa [intervalAffine] using congrArg p (hs.symm.trans (he ▸ ht))
    exact zero_ne_one (hseg.injective hc01)
  have hend : (J 0 = E 0 ∧ J 1 = E 1) ∨ (J 0 = E 1 ∧ J 1 = E 0) := by
    rcases hs01 with rfl | rfl <;> rcases ht01 with rfl | rfl
    · exact False.elim (hne rfl)
    · exact Or.inl ⟨by simpa only [J,arcSegment_zero] using hs.symm,
        by simpa only [J,arcSegment_one] using ht.symm⟩
    · exact Or.inr ⟨by simpa only [J,arcSegment_zero] using hs.symm,
        by simpa only [J,arcSegment_one] using ht.symm⟩
    · exact False.elim (hne rfl)
  exact free_boundary_essential_excludes_boundary_only_lift_return S g hg hS F B a ha hai
    haEssential p hp E J c hseg (fun u => hLB _) hEp (fun _ => rfl) hend

end CoherentEndpointMotion.FreeBoundaryContactRepair
