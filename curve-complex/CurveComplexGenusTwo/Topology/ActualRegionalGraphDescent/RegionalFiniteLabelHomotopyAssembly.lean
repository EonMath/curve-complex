import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteLabelMovie

open CurveComplex Set
open scoped BigOperators

/-- Endpoint fiber formulas identify the actual bundled maps, so a contiguous
    label movie is a genuine homotopy between those maps. -/
theorem regional_finite_label_maps_homotopic
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f g : V → W)
    (hcommon : ∀ σ : Finset V, σ ∈ K.faces → σ.image f ∪ σ.image g ∈ L.faces)
    (M N : C(RealizationPoint K,RealizationPoint L))
    (hM : ∀ x v, (M x).weight v = ∑ i : V, if f i = v then x.weight i else 0)
    (hN : ∀ x v, (N x).weight v = ∑ i : V, if g i = v then x.weight i else 0) :
    ContinuousMap.Homotopic M N := by
  obtain ⟨H,hw⟩ := regional_finite_label_contiguity_movie K L f g hcommon
  refine ⟨{ toFun := H
            continuous_toFun := H.continuous
            map_zero_left := ?_
            map_one_left := ?_ }⟩
  · intro x
    apply RealizationPoint.ext
    funext v
    rw [hw,hM]
    simp
  · intro x
    apply RealizationPoint.ext
    funext v
    rw [hw,hN]
    simp

/-- Actual finite successor homotopies concatenate, including a zero-length
    descent, without changing the chosen initial and terminal maps. -/
theorem regional_finite_successor_homotopies_concatenate
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (maps : ℕ → C(X,Y)) (n : ℕ)
    (hsteps : ∀ i < n, ContinuousMap.Homotopic (maps i) (maps (i+1))) :
    ContinuousMap.Homotopic (maps 0) (maps n) := by
  induction n with
  | zero => exact ContinuousMap.Homotopic.refl _
  | succ n ih =>
    exact (ih (fun i hi => hsteps i (Nat.lt.step hi))).trans (hsteps n (Nat.lt_succ_self n))

/-- Finite domain weight sums are one in the literal weak realization. -/
theorem regional_finite_domain_realization_weight_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : AbstractSimplicialComplex V) (x : RealizationPoint K) :
    ∑ i : V, x.weight i = 1 := by
  obtain ⟨σ,hσ,hzero,hsum⟩ := x.liesInFace
  have heq : (∑ i ∈ σ, x.weight i) = ∑ i : V, x.weight i := by
    apply Finset.sum_subset (Finset.subset_univ σ)
    intro i hi his
    exact hzero i his
  exact heq.symm.trans hsum

/-- Once the terminal image has an actual anchor common face on every domain
    face, its induced map is nullhomotopic at the anchor vertex. -/
theorem regional_finite_label_map_anchor_nullhomotopic
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : V → W) (anchor : W)
    (hcone : ∀ σ : Finset V, σ ∈ K.faces → insert anchor (σ.image f) ∈ L.faces)
    (M : C(RealizationPoint K,RealizationPoint L))
    (hM : ∀ x v, (M x).weight v = ∑ i : V, if f i = v then x.weight i else 0) :
    ContinuousMap.Homotopic M
      (ContinuousMap.const (RealizationPoint K) (coneVertex L anchor)) := by
  have hcommon : ∀ σ : Finset V, σ ∈ K.faces →
      σ.image f ∪ σ.image (fun _ => anchor) ∈ L.faces := by
    intro σ hσ
    have hne : σ.Nonempty := (K.isRelLowerSet_faces hσ).1
    have heq : σ.image (fun _ : V => anchor) = {anchor} := by
      ext v
      simp only [Finset.mem_image,Finset.mem_singleton]
      constructor
      · rintro ⟨i,hi,rfl⟩
        rfl
      · intro he
        obtain ⟨i,hi⟩ := hne
        exact ⟨i,hi,he.symm⟩
    simpa [heq,Finset.union_comm] using hcone σ hσ
  apply regional_finite_label_maps_homotopic K L f (fun _ => anchor) hcommon M
    (ContinuousMap.const _ (coneVertex L anchor)) hM
  intro x v
  by_cases hv : v = anchor
  · subst v
    simpa [coneVertex] using (regional_finite_domain_realization_weight_sum K x).symm
  · have ha : anchor ≠ v := Ne.symm hv
    simp [coneVertex,hv,ha]

#print axioms regional_finite_label_maps_homotopic
#print axioms regional_finite_successor_homotopies_concatenate
#print axioms regional_finite_domain_realization_weight_sum
#print axioms regional_finite_label_map_anchor_nullhomotopic

/-- A concrete finite label descent with paid successor common faces and a
    paid terminal anchor cone gives an actual initial-map nullhomotopy. -/
theorem regional_finite_label_descent_nullhomotopic
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (labels : ℕ → V → W) (n : ℕ) (anchor : W)
    (hfaces : ∀ i ≤ n, ∀ σ : Finset V, σ ∈ K.faces → σ.image (labels i) ∈ L.faces)
    (hcommon : ∀ i < n, ∀ σ : Finset V, σ ∈ K.faces →
      σ.image (labels i) ∪ σ.image (labels (i+1)) ∈ L.faces)
    (hterminal : ∀ σ : Finset V, σ ∈ K.faces →
      insert anchor (σ.image (labels n)) ∈ L.faces) :
    ∃ M : C(RealizationPoint K,RealizationPoint L),
      (∀ x v, (M x).weight v = ∑ i : V, if labels 0 i = v then x.weight i else 0) ∧
      ContinuousMap.Homotopic M
        (ContinuousMap.const (RealizationPoint K) (coneVertex L anchor)) := by
  classical
  have hex : ∀ i : ℕ, ∃ M : C(RealizationPoint K,RealizationPoint L),
      ∀ x v, (M x).weight v =
        ∑ j : V, if labels (min i n) j = v then x.weight j else 0 := by
    intro i
    exact regional_finite_label_realization_map K L (labels (min i n))
      (hfaces _ (Nat.min_le_right i n))
  choose maps hw using hex
  have hsteps : ∀ i < n, ContinuousMap.Homotopic (maps i) (maps (i+1)) := by
    intro i hi
    have hwi : ∀ x v, (maps i x).weight v =
        ∑ j : V, if labels i j = v then x.weight j else 0 := by
      simpa [Nat.min_eq_left (Nat.le_of_lt hi)] using hw i
    have hwj : ∀ x v, (maps (i+1) x).weight v =
        ∑ j : V, if labels (i+1) j = v then x.weight j else 0 := by
      simpa [Nat.min_eq_left (by omega : i+1 ≤ n)] using hw (i+1)
    exact regional_finite_label_maps_homotopic K L (labels i) (labels (i+1))
      (hcommon i hi) (maps i) (maps (i+1)) hwi hwj
  have hchain := regional_finite_successor_homotopies_concatenate maps n hsteps
  have hend := regional_finite_label_map_anchor_nullhomotopic K L (labels n)
    anchor hterminal (maps n) (by simpa using hw n)
  exact ⟨maps 0,by simpa using hw 0,hchain.trans hend⟩

#print axioms regional_finite_label_descent_nullhomotopic
