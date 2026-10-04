import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RelativeCancellationBookkeepingScaffolds
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem relative_finite_contact_produces_first_arc_clean_prefix
    (M : HyperellipticModel E S) (a b : NonLoopArc M)
    (hstart : a.val.map 0 = b.val.map 0)
    (hfinite : (ArcSurgery.crossings M a.toEssential b.toEssential).Finite)
    (hpositive : (ArcSurgery.crossings M a.toEssential b.toEssential).Nonempty) :
    ∃ r s : Interval,
      0 < r ∧ r < 1 ∧ 0 < s ∧ s < 1 ∧ a.val.map r = b.val.map s ∧
      ∀ u v : Interval, u ≤ r → a.val.map u = b.val.map v →
        (u = 0 ∧ v = 0) ∨ (u = r ∧ v = s) := by
  classical
  let T : Set (Interval × Interval) := {z |
    a.val.map z.1 = b.val.map z.2 ∧
    a.val.map z.1 ∈ ArcSurgery.crossings M a.toEssential b.toEssential}
  have hTf : T.Finite := hfinite.of_injOn
    (show MapsTo (fun z : Interval × Interval => a.val.map z.1) T
      (ArcSurgery.crossings M a.toEssential b.toEssential) from fun _ hz => hz.2)
    (by
      intro z hz w hw he
      apply Prod.ext
      · exact a.injective he
      · apply b.injective
        exact hz.1.symm.trans (he.trans hw.1))
  have hTn : T.Nonempty := by
    obtain ⟨p, hp⟩ := hpositive
    obtain ⟨r, hr⟩ := hp.1.1
    obtain ⟨s, hs⟩ := hp.2.1
    exact ⟨(r,s), hr.trans hs.symm, hr.symm ▸ hp⟩
  obtain ⟨z, hz, hmin⟩ := Set.exists_min_image T
    (fun z : Interval × Interval => z.1.val) hTf hTn
  have hzA : a.val.map z.1 ∉ M.cover.branch := hz.2.1.2
  have hzB : b.val.map z.2 ∉ M.cover.branch := hz.1 ▸ hzA
  have hr0 : z.1 ≠ 0 := by intro h; exact hzA (h ▸ a.val.start_marked)
  have hr1 : z.1 ≠ 1 := by intro h; exact hzA (h ▸ a.val.end_marked)
  have hs0 : z.2 ≠ 0 := by intro h; exact hzB (h ▸ b.val.start_marked)
  have hs1 : z.2 ≠ 1 := by intro h; exact hzB (h ▸ b.val.end_marked)
  have hrlt : z.1 < 1 := lt_of_le_of_ne z.1.property.2 hr1
  have hslt : z.2 < 1 := lt_of_le_of_ne z.2.property.2 hs1
  refine ⟨z.1,z.2,lt_of_le_of_ne z.1.property.1 (Ne.symm hr0), hrlt,
    lt_of_le_of_ne z.2.property.1 (Ne.symm hs0),hslt,hz.1,?_⟩
  intro u v hur he
  by_cases hmark : a.val.map u ∈ M.cover.branch
  · have hu0 : u = 0 := by
      rcases a.val.marked_only_at_ends u hmark with hu | hu
      · exact hu
      · have hbad : (1 : Interval) ≤ z.1 := by
          calc (1 : Interval) = u := hu.symm
               _ ≤ z.1 := hur
        exact False.elim (not_le_of_gt hrlt hbad)
    left
    refine ⟨hu0, b.injective ?_⟩
    exact he.symm.trans ((congrArg a.val.map hu0).trans hstart)
  · have huvT : (u,v) ∈ T := by
      refine ⟨he, ?_⟩
      exact ⟨⟨⟨u,rfl⟩,hmark⟩,⟨⟨v,he.symm⟩,he ▸ hmark⟩⟩
    have hsmall := hmin (u,v) huvT
    have hu : u = z.1 := by
      apply Subtype.ext
      exact le_antisymm (show u.val ≤ z.1.val from hur) hsmall
    have hv : v = z.2 := b.injective (he.symm.trans ((congrArg a.val.map hu).trans hz.1))
    exact Or.inr ⟨hu,hv⟩

end CurveComplex.HyperellipticModel
