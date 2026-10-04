import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
open Set Topology Schoenflies
open scoped Manifold
namespace CurveComplex
open LocalSurgery

-- Actual angular remainder + actual surgery disk. Essentiality rules out the
-- wrong component; avoidance of the retained remainder is a conclusion.
theorem actual_surgery_disk_retained_remainder_exterior
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (c : EssentialCurve S) (A B : Set S) (r : C(Interval,S))
    (hr : Topology.IsEmbedding r)
    (himage : c.val.image = A ∪ Set.range r)
    (hends : r 0 ∈ A ∧ r 1 ∈ A)
    (hAmeet : A ∩ Set.range r ⊆ {r 0,r 1})
    (hBmeet : B ∩ Set.range r ⊆ {r 0,r 1})
    (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)) (hd : Topology.IsEmbedding d)
    (hfrontier : frontier (Set.range d) = A ∪ B) :
    Disjoint (Set.range r) (interior (Set.range d)) := by
  have hclosed : IsClosed (Set.range d) := (isCompact_range d.continuous).isClosed
  let R := r '' Set.Ioo (0 : Interval) 1
  have hR : IsPreconnected R := isPreconnected_Ioo.image r r.continuous.continuousOn
  have hnoend (t : Interval) (ht : t ∈ Set.Ioo (0 : Interval) 1) : r t ∉ ({r 0,r 1} : Set S) := by
    intro he
    rcases Set.mem_insert_iff.mp he with he | he
    · have he0 := hr.injective he
      exact (ne_of_gt ht.1) he0
    · have he1 := hr.injective (Set.mem_singleton_iff.mp he)
      exact (ne_of_lt ht.2) he1
  have havoid : Disjoint R (frontier (Set.range d)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,ht,rfl⟩ hf
    rw [hfrontier] at hf
    rcases hf with ha | hb
    · exact hnoend t ht (hAmeet ⟨ha,⟨t,rfl⟩⟩)
    · exact hnoend t ht (hBmeet ⟨hb,⟨t,rfl⟩⟩)
  have hcover : R ⊆ interior (Set.range d) ∪ (Set.range d)ᶜ := by
    intro x hx
    by_cases hxD : x ∈ Set.range d
    · left
      by_contra hn
      exact Set.disjoint_left.mp havoid hx (hclosed.frontier_eq ▸ ⟨hxD,hn⟩)
    · exact Or.inr hxD
  have hdis : Disjoint (interior (Set.range d)) (Set.range d)ᶜ :=
    Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))
  have hA : A ⊆ Set.range d := fun x hx => hclosed.frontier_subset (hfrontier.symm ▸ Or.inl hx)
  have hclass := hR.subset_or_subset isOpen_interior hclosed.isOpen_compl hdis hcover
  have hOut : R ⊆ (Set.range d)ᶜ := by
    rcases hclass with hIn | hOut
    · have hRclosed : Set.range r ⊆ Set.range d := by
        rintro x ⟨t,rfl⟩
        rcases eq_or_ne t 0 with he0 | hn0
        · subst t
          exact hA hends.1
        · rcases eq_or_ne t 1 with he1 | hn1
          · subst t
            exact hA hends.2
          · have ht : t ∈ Set.Ioo (0 : Interval) 1 :=
              ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm hn0),
                lt_of_le_of_ne (unitInterval.le_one t) hn1⟩
            exact interior_subset (hIn ⟨t,ht,rfl⟩)
      have hcD : c.val.image ⊆ Set.range d := by
        rw [himage]
        exact Set.union_subset hA hRclosed
      obtain ⟨e,he,hb,_⟩ := curve_in_embedded_disk_bounds_subdisk c.val d hd hcD
      exact False.elim (c.property ⟨e,he,hb⟩)
    · exact hOut
  apply Set.disjoint_left.mpr
  rintro x ⟨t,rfl⟩ hxIn
  rcases eq_or_ne t 0 with he0 | hn0
  · subst t
    have hf : r 0 ∈ frontier (Set.range d) := hfrontier.symm ▸ Or.inl hends.1
    exact (hclosed.frontier_eq ▸ hf).2 hxIn
  · rcases eq_or_ne t 1 with he1 | hn1
    · subst t
      have hf : r 1 ∈ frontier (Set.range d) := hfrontier.symm ▸ Or.inl hends.2
      exact (hclosed.frontier_eq ▸ hf).2 hxIn
    · have ht : t ∈ Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm hn0),
            lt_of_le_of_ne (unitInterval.le_one t) hn1⟩
      exact hOut ⟨t,ht,rfl⟩ (interior_subset hxIn)
end CurveComplex
