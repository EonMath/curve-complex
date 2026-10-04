import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3

namespace CurveComplex.HyperellipticModel

open CurveGenusTwo.Filtration

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable local instance integrationLocalInstance_ActualObjects_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- The non-loop endpoint class of Definition 9.1, within the actual support. -/
noncomputable def actualEndpointFibre (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (v : EssentialArcClass M) :
    Finset (EssentialArcClass M) := by
  classical
  exact σ.filter fun w => ¬ (actualArcLabels M).isLoop w ∧
    classEndpoints M w = classEndpoints M v

/-- The source objects: singleton loops and non-loop endpoint classes of size at least two. -/
noncomputable def actualObjectFamily (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) : Finset (Finset (EssentialArcClass M)) := by
  classical
  exact ((σ.filter ((actualArcLabels M).isLoop)).image fun v => {v}) ∪
    ((σ.filter fun v => ¬ (actualArcLabels M).isLoop v ∧
      2 ≤ (actualEndpointFibre M σ v).card).image (actualEndpointFibre M σ))

theorem actualEndpointFibre_subset (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (v : EssentialArcClass M) :
    actualEndpointFibre M σ v ⊆ σ := by
  classical
  exact Finset.filter_subset _ _

theorem actualObjectFamily_subset (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) {O : Finset (EssentialArcClass M)}
    (hO : O ∈ actualObjectFamily M σ) : O ⊆ σ := by
  classical
  simp only [actualObjectFamily, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hO
  rcases hO with ⟨v, ⟨hv, _⟩, rfl⟩ | ⟨v, _, rfl⟩
  · simpa using hv
  · exact actualEndpointFibre_subset M σ v

theorem actualObjectFamily_cover (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hbad : badVertices (actualArcLabels M) σ = σ)
    {v : EssentialArcClass M} (hv : v ∈ σ) :
    ∃ O ∈ actualObjectFamily M σ, v ∈ O := by
  classical
  have hvb : v ∈ badVertices (actualArcLabels M) σ := hbad.symm ▸ hv
  simp only [badVertices, Finset.mem_filter] at hvb
  rcases hvb.2 with hl | ⟨w, hw, hwv, hvl, hwl, he⟩
  · refine ⟨{v}, ?_, by simp⟩
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hl⟩, rfl⟩
  · have hvf : v ∈ actualEndpointFibre M σ v := by
      simp [actualEndpointFibre, hv, hvl]
    have hwf : w ∈ actualEndpointFibre M σ v := by
      simp only [actualEndpointFibre, Finset.mem_filter]
      exact ⟨hw, hwl, he⟩
    have hcard : 2 ≤ (actualEndpointFibre M σ v).card := by
      have hsub : ({v, w} : Finset (EssentialArcClass M)) ⊆ actualEndpointFibre M σ v := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hvf
        · exact hwf
      have hc := Finset.card_le_card hsub
      simpa [hwv, hwv.symm] using hc
    refine ⟨actualEndpointFibre M σ v, ?_, hvf⟩
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, hvl, hcard⟩, rfl⟩

theorem actualEndpointFibre_eq_of_member (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) {v w : EssentialArcClass M}
    (hw : w ∈ actualEndpointFibre M σ v) :
    actualEndpointFibre M σ w = actualEndpointFibre M σ v := by
  classical
  have he : classEndpoints M w = classEndpoints M v :=
    (Finset.mem_filter.mp hw).2.2
  ext u
  simp only [actualEndpointFibre, Finset.mem_filter, he]

theorem actualEndpointFibre_disjoint_or_eq (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (v w : EssentialArcClass M) :
    Disjoint (actualEndpointFibre M σ v) (actualEndpointFibre M σ w) ∨
      actualEndpointFibre M σ v = actualEndpointFibre M σ w := by
  classical
  by_cases hd : Disjoint (actualEndpointFibre M σ v) (actualEndpointFibre M σ w)
  · exact Or.inl hd
  · right
    rw [Finset.disjoint_left] at hd
    push_neg at hd
    obtain ⟨u, huv, huw⟩ := hd
    exact (actualEndpointFibre_eq_of_member M σ huv).symm.trans
      (actualEndpointFibre_eq_of_member M σ huw)


theorem actualObjectFamily_union (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hbad : badVertices (actualArcLabels M) σ = σ) :
    (actualObjectFamily M σ).biUnion id = σ := by
  classical
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨O, hO, hvO⟩ := Finset.mem_biUnion.mp hv
    exact actualObjectFamily_subset M σ hO hvO
  · intro v hv
    obtain ⟨O, hO, hvO⟩ := actualObjectFamily_cover M σ hbad hv
    exact Finset.mem_biUnion.mpr ⟨O, hO, hvO⟩


theorem actualObjectFamily_eq_of_shared_class (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) {O P : Finset (EssentialArcClass M)}
    (hO : O ∈ actualObjectFamily M σ) (hP : P ∈ actualObjectFamily M σ)
    {x : EssentialArcClass M} (hxO : x ∈ O) (hxP : x ∈ P) : O = P := by
  classical
  simp only [actualObjectFamily, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hO hP
  rcases hO with ⟨v, ⟨hv, hvloop⟩, rfl⟩ | ⟨v, _, rfl⟩
  · have hxv : x = v := Finset.mem_singleton.mp hxO
    subst x
    rcases hP with ⟨w, _, rfl⟩ | ⟨w, _, rfl⟩
    · have hvw : v = w := Finset.mem_singleton.mp hxP
      rw [hvw]
    · exact False.elim ((Finset.mem_filter.mp hxP).2.1 hvloop)
  · rcases hP with ⟨w, ⟨_, hwloop⟩, rfl⟩ | ⟨w, _, rfl⟩
    · have hxw : x = w := Finset.mem_singleton.mp hxP
      subst x
      exact False.elim ((Finset.mem_filter.mp hxO).2.1 hwloop)
    · exact (actualEndpointFibre_eq_of_member M σ hxO).symm.trans
        (actualEndpointFibre_eq_of_member M σ hxP)

theorem actualObjectFamily_distinct_disjoint (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) {O P : Finset (EssentialArcClass M)}
    (hO : O ∈ actualObjectFamily M σ) (hP : P ∈ actualObjectFamily M σ)
    (hne : O ≠ P) : Disjoint O P := by
  classical
  exact Finset.disjoint_left.mpr (fun x hxO hxP =>
    hne (actualObjectFamily_eq_of_shared_class M σ hO hP hxO hxP))


theorem actualObjectFamily_nonempty_positive (M : HyperellipticModel E S)
    {p : ℕ} (hp : 1 ≤ p) (T : ActualStratum M p) :
    (actualObjectFamily M T.val).Nonempty := by
  have hcard : 0 < T.val.card := by rw [T.property.2.1]; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
  obtain ⟨O, hO, _⟩ := actualObjectFamily_cover M T.val T.property.2.2 hv
  exact ⟨O, hO⟩

end CurveComplex.HyperellipticModel
