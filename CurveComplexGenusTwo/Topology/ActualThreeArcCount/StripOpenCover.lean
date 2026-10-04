import CurveComplexGenusTwo.Topology.ActualThreeArcCount.OriginalRegionVanishing
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.StripHomotopy
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.FiniteDisjointProperArcStripsNamed
import CurveComplexGenusTwo.Topology.FrontierCircle.FrontierGeometry

open CurveComplex Set Topology ContinuousMap
open scoped Manifold ContDiff
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut
private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev OpenRect := Set.Ioo (0 : ℝ) 1 × Set.Ioo (-1 : ℝ) 1
private abbrev ClosedRect := Interval × Set.Icc (-1 : ℝ) 1
private def rectInclusion : OpenRect → ClosedRect :=
  Prod.map (Set.inclusion Ioo_subset_Icc_self) (Set.inclusion Ioo_subset_Icc_self)
private theorem rectInclusion_embedding : IsEmbedding rectInclusion :=
  (IsEmbedding.inclusion Ioo_subset_Icc_self).prodMap
    (IsEmbedding.inclusion Ioo_subset_Icc_self)

private theorem openRectangle_range_open
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S]
    (E : ClosedRect → S) (hE : IsEmbedding E) :
    IsOpen (Set.range (E ∘ rectInclusion)) := by
  let K : Set ClosedRect := {p | (p.1 : ℝ) ∈ Ioo 0 1 ∧ (p.2 : ℝ) ∈ Ioo (-1) 1}
  have hK : IsOpen K :=
    (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
  have hrange : Set.range (E ∘ rectInclusion) = E '' K := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨rectInclusion p, ⟨p.1.property, p.2.property⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(⟨p.1, hp.1⟩, ⟨p.2, hp.2⟩), rfl⟩
  obtain ⟨O, hO, heq⟩ := hE.isInducing.image_eq_isOpen_inter_range hK
  have hint : E '' K ⊆ interior (Set.range E) := by
    rintro _ ⟨p, hp, rfl⟩
    exact embedded_band_open_rectangle_interior E hE p.1 p.2
      hp.1.1 hp.1.2 hp.2.1 hp.2.2
  have hi : E '' K = O ∩ interior (Set.range E) := by
    apply Set.Subset.antisymm
    · intro y hy
      exact ⟨(heq ▸ hy).1, hint hy⟩
    · intro y hy
      rw [heq]
      exact ⟨hy.1, interior_subset hy.2⟩
  rw [hrange, hi]
  exact hO.inter isOpen_interior

/-- Actual disjoint proper-arc strips give an open cover of the literal exterior
interior. Each strip is contractible, and its overlap with the uncut open regions
has precisely the homotopy type of two points. -/
theorem original_disjoint_strips_open_cover
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target)
    (n : ℕ) (a : Fin n → C(Interval, ↥(exterior S x R)))
    (hemb : ∀ i, IsEmbedding (a i))
    (hend : ∀ i, (a i 0).val ∈ originalBoundary S x R ∧ (a i 1).val ∈ originalBoundary S x R)
    (hint : ∀ i t, t ∈ Ioo (0 : Interval) 1 → (a i t).val ∉ originalBoundary S x R)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j))) :
    let D : Set S := (OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R ∪ arcTrace a)ᶜ
    ∃ W : Fin n → Set S,
      (∀ i, IsOpen (W i) ∧ ContractibleSpace ↥(W i)) ∧
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
      D ∪ ⋃ i, W i = interior (exterior S x R) ∧
      (∀ i, Nonempty (↥(D ∩ W i) ≃ₕ (Unit ⊕ Unit))) := by
  classical
  dsimp only
  let Q : Set S := exterior S x R
  let B : Set S := originalBoundary S x R
  let D : Set S := (OriginalBoundaryArc.openDisk S x R ∪ B ∪ arcTrace a)ᶜ
  obtain ⟨p, E, hp, hE, hEE⟩ := OriginalBoundaryArc.source_finite_disjoint_proper_arc_strips
    S g hg hS x R hR htarget n a hemb hend hint hdisj
  let F (i : Fin n) : OpenRect → S := fun z => (E i (rectInclusion z)).val
  let W (i : Fin n) : Set S := Set.range (F i)
  have hF (i : Fin n) : IsEmbedding (F i) :=
    IsEmbedding.subtypeVal.comp ((hE i).1.comp rectInclusion_embedding)
  have hWi (i : Fin n) : W i ⊆ interior Q := by
    rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget]
    rintro _ ⟨z, rfl⟩ (hopen | hboundary)
    · exact (E i (rectInclusion z)).property hopen
    · exact (hE i).2.2.2.1 (rectInclusion z).1
        ⟨z.1.property.1, z.1.property.2⟩ (rectInclusion z).2 hboundary
  have hD : D ⊆ interior Q := by
    rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget]
    intro y hy hb
    exact hy (Or.inl hb)
  have hpair (i j : Fin n) (hij : i ≠ j) : Disjoint (W i) (W j) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨z, rfl⟩ ⟨w, hw⟩
    exact Set.disjoint_left.mp (hEE i j hij) (Set.mem_range_self (rectInclusion z))
      ⟨rectInclusion w, Subtype.ext hw⟩
  have hcover : D ∪ ⋃ i, W i = interior Q := by
    apply Set.Subset.antisymm
    · exact union_subset hD (iUnion_subset hWi)
    · intro y hy
      by_cases ht : y ∈ arcTrace a
      · obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp ht
        have hnB : (a i t).val ∉ B := by
          rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget] at hy
          exact fun h => hy (Or.inr h)
        have ht0 : (0 : ℝ) < t := by
          have hne : t ≠ 0 := fun h => hnB (h ▸ (hend i).1)
          exact lt_of_le_of_ne t.property.1 (fun h => hne (Subtype.ext h.symm))
        have ht1 : (t : ℝ) < 1 := by
          have hne : t ≠ 1 := fun h => hnB (h ▸ (hend i).2)
          exact lt_of_le_of_ne t.property.2 (fun h => hne (Subtype.ext h))
        apply Or.inr
        apply Set.mem_iUnion.mpr
        refine ⟨i, (⟨⟨t, ht0, ht1⟩, ⟨0, by norm_num⟩⟩ : OpenRect), ?_⟩
        exact congrArg Subtype.val ((hE i).2.1 t)
      · apply Or.inl
        intro hbad
        rcases hbad with hb | ha
        · rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget] at hy
          exact hy hb
        · exact ht ha
  refine ⟨W, ?_, hpair, hcover, ?_⟩
  · intro i
    refine ⟨openRectangle_range_open (fun z => (E i z).val)
      (IsEmbedding.subtypeVal.comp (hE i).1), ?_⟩
    letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
      (convex_Ioo _ _).contractibleSpace ⟨1/2, by norm_num⟩
    letI : ContractibleSpace (Set.Ioo (-1 : ℝ) 1) :=
      (convex_Ioo _ _).contractibleSpace ⟨0, by norm_num⟩
    exact (hF i).toHomeomorph.contractibleSpace_iff.mp inferInstance
  · intro i
    let C := {z : OpenRect | (z.2 : ℝ) ≠ 0}
    let G : C → S := fun z => F i z.val
    have hG : IsEmbedding G := (hF i).comp IsEmbedding.subtypeVal
    have hrange : Set.range G = D ∩ W i := by
      apply Set.Subset.antisymm
      · rintro _ ⟨z, rfl⟩
        refine ⟨?_, ⟨z.val, rfl⟩⟩
        intro hbad
        rcases hbad with hb | ha
        · have hi := hWi i (Set.mem_range_self z.val)
          rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget] at hi
          exact hi hb
        · obtain ⟨j, t, ht⟩ := Set.mem_iUnion.mp ha
          have he : E j (t, ⟨0, by norm_num⟩) = E i (rectInclusion z.val) :=
            ((hE j).2.1 t).trans (Subtype.ext ht)
          by_cases hij : i = j
          · subst j
            have hz := congrArg (fun p : ClosedRect => (p.2 : ℝ)) ((hE i).1.injective he)
            exact z.property hz.symm
          · exact Set.disjoint_left.mp (hEE i j hij) (Set.mem_range_self _)
              ⟨(t, ⟨0, by norm_num⟩), he⟩
      · rintro y ⟨hy, z, rfl⟩
        have hz : (z.2 : ℝ) ≠ 0 := by
          intro he
          apply hy
          apply Or.inr
          apply Set.mem_iUnion.mpr
          refine ⟨i, (rectInclusion z).1, ?_⟩
          have hwidth : (rectInclusion z).2 = (⟨0, by norm_num⟩ : Set.Icc (-1 : ℝ) 1) := Subtype.ext he
          change (a i (rectInclusion z).1).val = (E i (rectInclusion z)).val
          conv_rhs => rw [show rectInclusion z = ((rectInclusion z).1, (rectInclusion z).2) from rfl, hwidth]
          exact congrArg Subtype.val ((hE i).2.1 _).symm
        exact ⟨⟨z, hz⟩, rfl⟩
    let e := (hG.toHomeomorph.trans (Homeomorph.setCongr hrange)).symm
    exact ⟨e.toHomotopyEquiv.trans cutRectangleHomotopyTwo⟩

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
