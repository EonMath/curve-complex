import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.GlobalOnePointStep

namespace CurveComplex.HyperellipticModel.ArcSurgery

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A count-preserving general-position redraw for an actual finite marked-arc
family. The local six-germ and compact-tail input is produced by
`actual_marked_interior_contact_fan_preprocessing`; it is not an assumption. -/
theorem actual_raw_count_preserving_no_triple_family
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (hanchor : ∀ i, (crossings M anchor (r i)).Finite ∧
      ∀ p ∈ crossings M anchor (r i), CrossesInDisk M anchor (r i) p)
    (hpair : ∀ i j, i ≠ j → (crossings M (r i) (r j)).Finite ∧
      ∀ p ∈ crossings M (r i) (r j), CrossesInDisk M (r i) (r j) p) :
    ∃ q : I → EssentialMarkedArc M,
      (∀ i, vertex M (q i) = vertex M (r i)) ∧
      (∀ i, (crossings M anchor (q i)).Finite ∧
        (∀ p ∈ crossings M anchor (q i), CrossesInDisk M anchor (q i) p) ∧
        (crossings M anchor (q i)).ncard =
          (crossings M anchor (r i)).ncard) ∧
      (∀ i j, i ≠ j → (crossings M (q i) (q j)).Finite ∧
        (∀ p ∈ crossings M (q i) (q j), CrossesInDisk M (q i) (q j) p) ∧
        (crossings M (q i) (q j)).ncard =
          (crossings M (r i) (r j)).ncard) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        Disjoint (crossings M (q i) (q j)) (arcInterior M (q k))) ∧
      ∀ i j, i ≠ j →
        Disjoint (crossings M (q i) (q j)) (arcInterior M anchor) := by
  classical
  let Inv (s : I → EssentialMarkedArc M) : Prop :=
    (∀ i, vertex M (s i) = vertex M (r i)) ∧
    (∀ a b : Option I, a ≠ b →
      (crossings M (fullArc M anchor s a) (fullArc M anchor s b)).Finite ∧
      (∀ p ∈ crossings M (fullArc M anchor s a) (fullArc M anchor s b),
        CrossesInDisk M (fullArc M anchor s a) (fullArc M anchor s b) p) ∧
      (crossings M (fullArc M anchor s a) (fullArc M anchor s b)).ncard =
        (crossings M (fullArc M anchor r a) (fullArc M anchor r b)).ncard)
  have hsolve : ∀ n : ℕ, ∀ s : I → EssentialMarkedArc M,
      (tripleContactWitnesses M anchor s).ncard = n → Inv s →
      ∃ q : I → EssentialMarkedArc M,
        Inv q ∧ tripleContactWitnesses M anchor q = ∅ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hs
      have hsfinite : ∀ a b : Option I, a ≠ b →
          (crossings M (fullArc M anchor s a) (fullArc M anchor s b)).Finite :=
        fun a b hab => (hs.2 a b hab).1
      have hstrans : ∀ a b : Option I, a ≠ b →
          ∀ p ∈ crossings M (fullArc M anchor s a) (fullArc M anchor s b),
            CrossesInDisk M (fullArc M anchor s a) (fullArc M anchor s b) p :=
        fun a b hab => (hs.2 a b hab).2.1
      have hwfinite : (tripleContactWitnesses M anchor s).Finite :=
        triple_contact_witnesses_finite M anchor s
          (fun i => hsfinite none (some i) (by simp))
          (fun i j hij => hsfinite (some i) (some j)
            (fun he => hij (Option.some.inj he)))
      by_cases hempty : tripleContactWitnesses M anchor s = ∅
      · exact ⟨s,hs,hempty⟩
      · have hne : (tripleContactWitnesses M anchor s).Nonempty :=
          Set.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨i,b,c,p,hp⟩ := triple_witness_selects_family_arc M anchor s hne
        obtain ⟨s',hclass,hkeep,hpairs,hdecrease⟩ :=
          actual_one_point_global_descent M anchor s hsfinite hstrans i b c p hp hwfinite
        have hclass' : ∀ j, vertex M (s' j) = vertex M (r j) := by
          intro j
          by_cases hj : j = i
          · subst j
            exact hclass.trans (hs.1 i)
          · rw [hkeep j hj]
            exact hs.1 j
        have hinv' : Inv s' := by
          refine ⟨hclass',?_⟩
          intro a z haz
          obtain ⟨hf,ht,hcount⟩ := hpairs a z haz
          exact ⟨hf,ht,hcount.trans (hs.2 a z haz).2.2⟩
        exact ih _ (hn ▸ hdecrease) s' rfl hinv'
  have hinit : Inv r := by
    refine ⟨fun _ => rfl,?_⟩
    intro a b hab
    exact ⟨all_full_pair_crossings_finite M anchor r
        (fun i => (hanchor i).1) (fun i j hij => (hpair i j hij).1) a b hab,
      all_full_pair_crossings_transverse M anchor r
        (fun i => (hanchor i).2) (fun i j hij => (hpair i j hij).2)
        a b hab,rfl⟩
  obtain ⟨q,hq,hempty⟩ := hsolve _ r rfl hinit
  obtain ⟨htriple,hpairAnchor⟩ :=
    empty_triple_witnesses_give_no_triples M anchor q hempty
  refine ⟨q,hq.1,?_,?_,htriple,hpairAnchor⟩
  · intro i
    exact hq.2 none (some i) (by simp)
  · intro i j hij
    exact hq.2 (some i) (some j) (fun he => hij (Option.some.inj he))

end CurveComplex.HyperellipticModel.ArcSurgery

#print axioms CurveComplex.HyperellipticModel.ArcSurgery.actual_raw_count_preserving_no_triple_family
