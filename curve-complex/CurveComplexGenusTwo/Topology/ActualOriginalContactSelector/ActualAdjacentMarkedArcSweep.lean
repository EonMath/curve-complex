import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualAdjacentFixedArcCompetitor

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Source adjacency constructs an actual two-parameter isotopy sweep from
the original new arc to an arc disjoint from the specified old arc. Every
slice is embedded, ordered marked endpoints remain fixed, and no interior
parameter encounters a mark at any time. This is genuine isotopy geometry,
not an assumed bigon or an assumed replacement witness. -/
theorem actual_adjacent_marked_arc_embedded_sweep
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hadj : ArcAdjacent M (Quotient.mk (essentialArcSetoid M) a)
      (Quotient.mk (essentialArcSetoid M) b)) :
    ∃ F : C(Interval × Interval,S),
      (∀ t, F (0,t) = b.val.map t) ∧
      (∀ τ, Function.Injective (fun t => F (τ,t))) ∧
      (∀ τ, F (τ,0) = b.val.map 0 ∧ F (τ,1) = b.val.map 1) ∧
      (∀ τ t, t ≠ 0 → t ≠ 1 → F (τ,t) ∉ (M.cover.branch : Set S)) ∧
      (∀ t, t ≠ 0 → t ≠ 1 → F (1,t) ∉ arcInterior M a) := by
  classical
  obtain ⟨c,hc,hdis⟩ := actual_adjacent_fixed_arc_disjoint_competitor M a b hadj
  obtain ⟨H,hmarks,himage⟩ := (markedIsotopy_equivalence M).symm (Quotient.exact hc)
  let F : C(Interval × Interval,S) :=
    ⟨fun z => H.map (z.1,b.val.map z.2),
      H.map.continuous.comp (continuous_fst.prodMk (b.val.continuous.comp continuous_snd))⟩
  have hbne : b.val.map 0 ≠ b.val.map 1 := by
    have hclass := hadj.2.2.1
    have hcard := (actualArcLabels M).nonloop_endpoint_card _ hclass
    change (classEndpoints M (Quotient.mk (essentialArcSetoid M) b)).card = 2 at hcard
    intro he
    change ({b.val.map 0,b.val.map 1} : Finset S).card = 2 at hcard
    simp [he] at hcard
  have hbinj : Function.Injective b.val.map := NonLoopArc.injective ⟨b.val,hbne⟩
  have hnotmark (τ t : Interval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
      F (τ,t) ∉ (M.cover.branch : Set S) := by
    intro hm
    obtain ⟨g,hg⟩ := H.homeomorphism_at τ
    have hfix : g (F (τ,t)) = F (τ,t) := (hg _).trans (hmarks τ _ hm)
    have hsame : b.val.map t = F (τ,t) :=
      g.injective ((hg (b.val.map t)).trans hfix.symm)
    have hbmark : b.val.map t ∈ M.cover.branch := hsame.symm ▸ hm
    exact (b.val.marked_only_at_ends t hbmark).elim ht0 ht1
  refine ⟨F,?_,?_,?_,hnotmark,?_⟩
  · intro t
    exact H.at_zero _
  · intro τ t u he
    obtain ⟨g,hg⟩ := H.homeomorphism_at τ
    exact hbinj (g.injective ((hg _).trans (he.trans (hg _).symm)))
  · intro τ
    exact ⟨hmarks τ _ b.val.start_marked,hmarks τ _ b.val.end_marked⟩
  · intro t ht0 ht1 hpa
    have hpc : F (1,t) ∈ c.val.image := by
      rw [← himage]
      exact ⟨b.val.map t,⟨t,rfl⟩,rfl⟩
    exact disjoint_left.mp hdis hpa ⟨hpc,hnotmark 1 t ht0 ht1⟩

end CurveComplex.HyperellipticModel
