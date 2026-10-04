import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialHalfBigonDescent
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualHalfBigonCornerOrientation

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Actual geometric half-bigon data. Neither innermostness nor a sequence,
relative isotopy, or crossing-descent oracle occurs in this record. -/
structure ActualEssentialHalfBigon (M : HyperellipticModel E S) {ι : Type}
    (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M) where
  index : ι
  firstSide : C(Interval,S)
  newSide : C(Interval,S)
  first_embedded : IsEmbedding firstSide
  new_embedded : IsEmbedding newSide
  first_zero : firstSide 0 = newSide 0
  first_one : firstSide 1 = newSide 1
  first_on_old : range firstSide ⊆ (old index).val.image
  new_on_arc : range newSide ⊆ a.val.image
  sides_inter : range firstSide ∩ range newSide = {firstSide 0,firstSide 1}
  disk : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)
  disk_embedded : IsEmbedding disk
  boundary_eq : disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    range firstSide ∪ range newSide
  marked_free_interior : Disjoint
    (disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
    (M.cover.branch : Set S)
  marks_are_first : ∀ p ∈ range disk, p ∈ M.cover.branch → p = newSide 0
  last_unmarked : newSide 1 ∉ M.cover.branch

/-- PRODUCE a properly oriented smaller actual half-bigon even when the
entering old representative is an essential loop. Its finite crossing energy
strictly decreases, and the original unmarked corner leaves the WHOLE disk. -/
theorem actual_essential_half_bigon_produce_smaller
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hsystem : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M)
    (hfinite : ∀ k, (ArcSurgery.crossings M (old k) a).Finite)
    (B : ActualEssentialHalfBigon M old a) (j : ι) (hji : j ≠ B.index)
    (hin : ((old j).val.image ∩
      (B.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty) :
    ∃ D : ActualEssentialHalfBigon M old a,
      D.index = j ∧ range D.disk ⊆ range B.disk ∧ B.newSide 1 ∉ range D.disk ∧
      (∑ k, (ArcSurgery.crossings M (old k) a ∩ range D.disk).ncard) <
        ∑ k, (ArcSurgery.crossings M (old k) a ∩ range B.disk).ncard := by
  obtain ⟨f,g,d,hf,hg,hd,hfne,hg0,hg1,hfon,hgon,hsides,hbd,hsub,hmissing,hmarks,hcorner,hcorners,hlt⟩ :=
    actual_essential_half_bigon_obstruction_strict_total_descent M old hsystem a B.index j hji
      B.firstSide B.newSide B.new_embedded B.first_on_old B.new_on_arc
      B.first_zero B.first_one B.disk B.disk_embedded B.marked_free_interior
      B.marks_are_first B.last_unmarked B.boundary_eq hfinite hin
  have hend (t : Interval) : g t ∈ range d :=
    Set.image_subset_range _ _ (hbd.symm ▸
      (show g t ∈ range f ∪ range g from Or.inr ⟨t,rfl⟩))
  obtain ⟨f',g',hf',hg',hfr,hgr,hz,ho,hmark',hlast⟩ :=
    actual_half_bigon_orient_marked_corner (M.cover.branch : Set S) (range d) (B.newSide 0)
      f g hf hg hg0.symm hg1.symm (hend 0) (hend 1) hcorner hcorners
  have hsides' : range f' ∩ range g' = {f' 0,f' 1} := by
    -- Embedded intervals have the same two intrinsic endpoints when their ranges agree.
    have endmap (t : Interval) (ht : t=0 ∨ t=1) : f' t = f 0 ∨ f' t = f 1 := by
      obtain ⟨u,hu⟩ := hfr ▸ Set.mem_range_self t
      have hut : u=0 ∨ u=1 :=
        actual_embedded_side_source_endpoint f' f hf' hf (hfr.symm ▸ Set.Subset.refl _) u
          (by rcases ht with ht | ht
              · exact Or.inl (hu.trans (congrArg f' ht))
              · exact Or.inr (hu.trans (congrArg f' ht)))
      rcases hut with rfl | rfl
      · exact Or.inl hu.symm
      · exact Or.inr hu.symm
    have endsback (t : Interval) (ht : t=0 ∨ t=1) : f t = f' 0 ∨ f t = f' 1 := by
      obtain ⟨u,hu⟩ := hfr.symm ▸ Set.mem_range_self t
      have hut : u=0 ∨ u=1 :=
        actual_embedded_side_source_endpoint f f' hf hf' (hfr ▸ Set.Subset.refl _) u
          (by rcases ht with ht | ht
              · exact Or.inl (hu.trans (congrArg f ht))
              · exact Or.inr (hu.trans (congrArg f ht)))
      rcases hut with rfl | rfl
      · exact Or.inl hu.symm
      · exact Or.inr hu.symm
    rw [hfr,hgr,hsides]
    ext p
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact endsback 0 (Or.inl rfl)
      · exact endsback 1 (Or.inr rfl)
    · rintro (rfl | rfl)
      · exact endmap 0 (Or.inl rfl)
      · exact endmap 1 (Or.inr rfl)
  let D : ActualEssentialHalfBigon M old a := {
    index := j, firstSide := f', newSide := g', first_embedded := hf', new_embedded := hg',
    first_zero := hz, first_one := ho,
    first_on_old := hfr ▸ hfon, new_on_arc := hgr ▸ hgon,
    sides_inter := hsides', disk := d, disk_embedded := hd,
    boundary_eq := by rw [hfr,hgr]; exact hbd,
    marked_free_interior := hmarks, marks_are_first := hmark', last_unmarked := hlast }
  exact ⟨D,rfl,hsub,hmissing,hlt⟩

/-- Finite-energy minimization together with ACTUAL produced smaller disks
selects a half-bigon avoiding every other old arc. It includes all essential
loops and shared marked corners and never assumes a finite move sequence. -/
theorem actual_essential_half_bigon_select_avoiding_other_arcs
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hsystem : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M)
    (hfinite : ∀ k, (ArcSurgery.crossings M (old k) a).Finite)
    (B : ActualEssentialHalfBigon M old a) :
    ∃ D : ActualEssentialHalfBigon M old a, ∀ j, j ≠ D.index →
      Disjoint (D.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (old j).val.image := by
  classical
  let energy : ActualEssentialHalfBigon M old a → ℕ := fun D =>
    ∑ k, (ArcSurgery.crossings M (old k) a ∩ range D.disk).ncard
  let P : ℕ → Prop := fun n => ∃ D : ActualEssentialHalfBigon M old a, energy D = n
  have hex : ∃ n,P n := ⟨energy B,B,rfl⟩
  obtain ⟨D,hD⟩ := Nat.find_spec hex
  refine ⟨D,?_⟩
  intro j hji
  apply disjoint_left.mpr
  intro p hpDisk hpOld
  obtain ⟨D',hindex,hsub,hmissing,hlt⟩ :=
    actual_essential_half_bigon_produce_smaller M old hsystem a hfinite D j hji
      ⟨p,hpOld,hpDisk⟩
  have hlt' : energy D' < Nat.find hex := hlt.trans_eq hD
  exact Nat.find_min hex hlt' ⟨D',rfl⟩

#print axioms actual_essential_half_bigon_produce_smaller
#print axioms actual_essential_half_bigon_select_avoiding_other_arcs
end CurveComplex.HyperellipticModel
