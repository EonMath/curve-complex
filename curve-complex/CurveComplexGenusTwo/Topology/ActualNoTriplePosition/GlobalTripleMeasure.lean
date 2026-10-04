import CurveComplexGenusTwo.Topology.ActualNoTriplePosition.IncidentFamilyRedraw

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

def fullArc (M : HyperellipticModel E S) {I : Type}
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (i : Option I) : EssentialMarkedArc M := Option.elim i anchor r

def tripleContactWitnesses
    (M : HyperellipticModel E S) {I : Type}
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M) :
    Set ((Option I × Option I × Option I) × S) :=
  {z | z.1.1 ≠ z.1.2.1 ∧ z.1.1 ≠ z.1.2.2 ∧
    z.1.2.1 ≠ z.1.2.2 ∧
    z.2 ∈ crossings M (fullArc M anchor r z.1.1)
      (fullArc M anchor r z.1.2.1) ∧
    z.2 ∈ arcInterior M (fullArc M anchor r z.1.2.2)}

theorem crossings_comm (M : HyperellipticModel E S)
    (a b : EssentialMarkedArc M) :
    crossings M a b = crossings M b a := Set.inter_comm _ _

theorem all_full_pair_crossings_finite
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (hanchor : ∀ i, (crossings M anchor (r i)).Finite)
    (hpair : ∀ i j, i ≠ j → (crossings M (r i) (r j)).Finite) :
    ∀ i j : Option I, i ≠ j →
      (crossings M (fullArc M anchor r i) (fullArc M anchor r j)).Finite := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some k => exact hanchor k
  | some k =>
    cases j with
    | none =>
      rw [crossings_comm]
      exact hanchor k
    | some l =>
      exact hpair k l (fun h => hij (congrArg Option.some h))

theorem all_full_pair_crossings_transverse
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (hanchor : ∀ i, ∀ p ∈ crossings M anchor (r i),
      CrossesInDisk M anchor (r i) p)
    (hpair : ∀ i j, i ≠ j →
      ∀ p ∈ crossings M (r i) (r j),
        CrossesInDisk M (r i) (r j) p) :
    ∀ a b : Option I, a ≠ b →
      ∀ p ∈ crossings M (fullArc M anchor r a) (fullArc M anchor r b),
        CrossesInDisk M (fullArc M anchor r a) (fullArc M anchor r b) p := by
  intro a b hab p hp
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some j => exact hanchor j p hp
  | some i =>
    cases b with
    | none =>
      apply crossesSymm M anchor (r i) p
      exact hanchor i p (crossings_comm M (r i) anchor ▸ hp)
    | some j =>
      exact hpair i j (fun he => hab (congrArg Option.some he)) p hp

theorem triple_contact_witnesses_finite
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (hanchor : ∀ i, (crossings M anchor (r i)).Finite)
    (hpair : ∀ i j, i ≠ j → (crossings M (r i) (r j)).Finite) :
    (tripleContactWitnesses M anchor r).Finite := by
  classical
  let B : Set S := ⋃ i : Option I, ⋃ j : Option I,
    if i = j then ∅ else crossings M (fullArc M anchor r i) (fullArc M anchor r j)
  have hB : B.Finite := Set.finite_iUnion (fun i => Set.finite_iUnion (fun j => by
    split_ifs with h
    · exact Set.finite_empty
    · exact all_full_pair_crossings_finite M anchor r hanchor hpair i j h))
  have hbound : tripleContactWitnesses M anchor r ⊆
      (Set.univ : Set (Option I × Option I × Option I)) ×ˢ B := by
    intro z hz
    refine ⟨Set.mem_univ _,?_⟩
    exact Set.mem_iUnion.mpr ⟨z.1.1,Set.mem_iUnion.mpr
      ⟨z.1.2.1,by rw [if_neg hz.1]; exact hz.2.2.2.1⟩⟩
  exact (Set.finite_univ.prod hB).subset hbound

theorem empty_triple_witnesses_give_no_triples
    (M : HyperellipticModel E S) {I : Type}
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (hempty : tripleContactWitnesses M anchor r = ∅) :
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      Disjoint (crossings M (r i) (r j)) (arcInterior M (r k))) ∧
    (∀ i j, i ≠ j →
      Disjoint (crossings M (r i) (r j)) (arcInterior M anchor)) := by
  constructor
  · intro i j k hij hik hjk
    apply Set.disjoint_left.mpr
    intro p hpij hpk
    have h : ((some i,some j,some k),p) ∈
        tripleContactWitnesses M anchor r := by
      exact ⟨by simpa using hij,by simpa using hik,
        by simpa using hjk,hpij,hpk⟩
    rw [hempty] at h
    exact h
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro p hpij hpa
    have h : ((some i,some j,none),p) ∈
        tripleContactWitnesses M anchor r := by
      exact ⟨by simpa using hij,by simp,by simp,hpij,hpa⟩
    rw [hempty] at h
    exact h

theorem triple_witnesses_subset_of_local_move
    (M : HyperellipticModel E S) {I : Type}
    (anchor : EssentialMarkedArc M) (r q : I → EssentialMarkedArc M)
    (i0 : I)
    (hkeep : ∀ a : Option I, a ≠ some i0 →
      fullArc M anchor q a = fullArc M anchor r a)
    (hnoNewTriple : ∀ a b : Option I,
      a ≠ some i0 → b ≠ some i0 → a ≠ b →
      ∀ x, x ∈ crossings M (q i0) (fullArc M anchor r a) →
        x ∈ (fullArc M anchor r b).val.image →
        x ∈ crossings M (r i0) (fullArc M anchor r a)) :
    tripleContactWitnesses M anchor q ⊆
      tripleContactWitnesses M anchor r := by
  rintro ⟨⟨a,b,c⟩,x⟩ hz
  change a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    x ∈ crossings M (fullArc M anchor q a) (fullArc M anchor q b) ∧
    x ∈ arcInterior M (fullArc M anchor q c) at hz
  change a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    x ∈ crossings M (fullArc M anchor r a) (fullArc M anchor r b) ∧
    x ∈ arcInterior M (fullArc M anchor r c)
  obtain ⟨hab,hac,hbc,hcross,hthird⟩ := hz
  by_cases ha : a = some i0
  · have hb : b ≠ some i0 := fun he => hab (ha.trans he.symm)
    have hc : c ≠ some i0 := fun he => hac (ha.trans he.symm)
    have hcross' : x ∈ crossings M (q i0) (fullArc M anchor r b) := by
      rw [ha,hkeep b hb] at hcross
      simpa [fullArc] using hcross
    have hthird' : x ∈ (fullArc M anchor r c).val.image := by
      simpa only [hkeep c hc] using hthird.1
    have hOld := hnoNewTriple b c hb hc hbc x hcross' hthird'
    refine ⟨hab,hac,hbc,?_,?_⟩
    · simpa [fullArc,ha] using hOld
    · simpa only [hkeep c hc] using hthird
  · by_cases hb : b = some i0
    · have hc : c ≠ some i0 := fun he => hbc (hb.trans he.symm)
      have hcross' : x ∈ crossings M (q i0) (fullArc M anchor r a) := by
        have h : x ∈ crossings M (fullArc M anchor r a) (q i0) := by
          rw [hb,hkeep a ha] at hcross
          simpa [fullArc] using hcross
        rwa [crossings_comm] at h
      have hthird' : x ∈ (fullArc M anchor r c).val.image := by
        simpa only [hkeep c hc] using hthird.1
      have hOld := hnoNewTriple a c ha hc hac x hcross' hthird'
      refine ⟨hab,hac,hbc,?_,?_⟩
      · rw [crossings_comm] at hOld
        simpa [fullArc,hb,hkeep a ha] using hOld
      · simpa only [hkeep c hc] using hthird
    · by_cases hc : c = some i0
      · have hcross' : x ∈ crossings M (q i0) (fullArc M anchor r a) := by
          refine ⟨?_,?_⟩
          · simpa [fullArc,hc] using hthird
          · simpa only [hkeep a ha] using hcross.1
        have hthird' : x ∈ (fullArc M anchor r b).val.image := by
          simpa only [hkeep b hb] using hcross.2.1
        have hOld := hnoNewTriple a b ha hb hab x hcross' hthird'
        refine ⟨hab,hac,hbc,?_,?_⟩
        · simpa only [hkeep a ha,hkeep b hb] using hcross
        · simpa [fullArc,hc] using hOld.1
      · refine ⟨hab,hac,hbc,?_,?_⟩
        · simpa only [hkeep a ha,hkeep b hb] using hcross
        · simpa only [hkeep c hc] using hthird

theorem triple_witnesses_strict_after_center_removal
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (anchor : EssentialMarkedArc M) (r q : I → EssentialMarkedArc M)
    (i0 : I) (b c : Option I) (p : S)
    (hold : ((some i0,b,c),p) ∈ tripleContactWitnesses M anchor r)
    (hcenter : p ∉ (q i0).val.image)
    (hsubset : tripleContactWitnesses M anchor q ⊆
      tripleContactWitnesses M anchor r)
    (hfinite : (tripleContactWitnesses M anchor r).Finite) :
    (tripleContactWitnesses M anchor q).ncard <
      (tripleContactWitnesses M anchor r).ncard := by
  have hnot : ((some i0,b,c),p) ∉ tripleContactWitnesses M anchor q := by
    intro h
    have hpq : p ∈ arcInterior M (q i0) := h.2.2.2.1.1
    exact hcenter hpq.1
  have hproper : tripleContactWitnesses M anchor q ⊂
      tripleContactWitnesses M anchor r :=
    Set.ssubset_iff_subset_ne.mpr ⟨hsubset,by
      intro he
      exact hnot (he.symm ▸ hold)⟩
  exact Set.ncard_lt_ncard hproper hfinite

theorem triple_witness_selects_family_arc
    (M : HyperellipticModel E S) {I : Type}
    (anchor : EssentialMarkedArc M) (r : I → EssentialMarkedArc M)
    (hne : (tripleContactWitnesses M anchor r).Nonempty) :
    ∃ i : I, ∃ b c : Option I, ∃ p : S,
      ((some i,b,c),p) ∈ tripleContactWitnesses M anchor r := by
  obtain ⟨⟨⟨a,b,c⟩,p⟩,h⟩ := hne
  obtain ⟨hab,hac,hbc,hcross,hthird⟩ := h
  cases a with
  | some i => exact ⟨i,b,c,p,hab,hac,hbc,hcross,hthird⟩
  | none =>
    cases b with
    | some i =>
      refine ⟨i,none,c,p,?_,?_,?_,?_,hthird⟩
      · exact Ne.symm hab
      · exact hbc
      · exact hac
      · rwa [crossings_comm]
    | none => exact (hab rfl).elim

end CurveComplex.HyperellipticModel.ArcSurgery

#print axioms CurveComplex.HyperellipticModel.ArcSurgery.triple_contact_witnesses_finite
