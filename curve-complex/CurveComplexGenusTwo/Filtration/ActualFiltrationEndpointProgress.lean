import CurveComplexGenusTwo.Filtration.Geometry.ActualArcFiltrationV3
import CurveComplexGenusTwo.Filtration.Geometry.ActualFamilyRealignmentHeader

namespace CurveComplex.HyperellipticModel

open CurveGenusTwo.Filtration

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

noncomputable local instance integrationLocalInstance_ActualFiltrationEndpointProgress_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

theorem empty_mem_actualA (M : HyperellipticModel E S) :
    (∅ : Finset (EssentialArcClass M)) ∈ actualA M := by
  classical
  change IsArcSimplex M ∅
  refine ⟨fun v => False.elim (by simpa only [Finset.notMem_empty] using v.property), ?_, ?_⟩
  · intro v
    exact False.elim (by simpa only [Finset.notMem_empty] using v.property)
  · intro v w h
    exact False.elim (by simpa only [Finset.notMem_empty] using v.property)

theorem actual_filtration_lower_endpoints (M : HyperellipticModel E S) :
    actualY M (-1) = void (EssentialArcClass M) ∧
    (∅ : Finset (EssentialArcClass M)) ∈ actualY M 0 := by
  exact ⟨filtration_neg_one_eq_void (actualA M) (actualArcLabels M),
    empty_mem_filtration_zero (actualA M) (actualArcLabels M) (empty_mem_actualA M)⟩

/-- Exact graph definition from the protected endpoint scaffold. -/
def ArcAdjacent (M : HyperellipticModel E S)
    (v w : EssentialArcClass M) : Prop :=
  v ≠ w ∧ ¬ (actualArcLabels M).isLoop v ∧
  ¬ (actualArcLabels M).isLoop w ∧
  classEndpoints M v ≠ classEndpoints M w ∧
  ∃ a b : EssentialMarkedArc M,
    Quotient.mk (essentialArcSetoid M) a = v ∧
    Quotient.mk (essentialArcSetoid M) b = w ∧
    Disjoint (arcInterior M a) (arcInterior M b)

def IsXSimplex (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) : Prop :=
  (∀ v ∈ σ, ¬ (actualArcLabels M).isLoop v) ∧
    ∀ v ∈ σ, ∀ w ∈ σ, v ≠ w → ArcAdjacent M v w

theorem xSimplex_down (M : HyperellipticModel E S)
    {σ τ : Finset (EssentialArcClass M)}
    (h : τ ⊆ σ) (hσ : IsXSimplex M σ) : IsXSimplex M τ := by
  exact ⟨fun v hv => hσ.1 v (h hv),
    fun v hv w hw hvw => hσ.2 v (h hv) w (h hw) hvw⟩

noncomputable def actualX (M : HyperellipticModel E S) :
    FiniteComplex (EssentialArcClass M) where
  simplices := {σ | IsXSimplex M σ}
  down_closed := by
    intro σ τ hsub hσ
    exact xSimplex_down M hsub hσ

theorem actualY_zero_subcomplex_actualX (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ actualY M 0) :
    σ ∈ actualX M := by
  classical
  change σ ∈ actualA M ∧ (badVertices (actualArcLabels M) σ).card ≤ (0 : ℤ) at hσ
  have hbad : badVertices (actualArcLabels M) σ = ∅ := by
    apply Finset.card_eq_zero.mp
    omega
  have hnotbad (v) : v ∉ badVertices (actualArcLabels M) σ := by rw [hbad]; simp
  have hnonloop (v) (hv : v ∈ σ) : ¬ (actualArcLabels M).isLoop v := by
    intro hl
    exact hnotbad v (Finset.mem_filter.mpr ⟨hv, Or.inl hl⟩)
  change IsXSimplex M σ
  refine ⟨hnonloop, ?_⟩
  intro v hv w hw hvw
  refine ⟨hvw, hnonloop v hv, hnonloop w hw, ?_, ?_⟩
  · intro heq
    exact hnotbad v (Finset.mem_filter.mpr
      ⟨hv, Or.inr ⟨w, hw, hvw.symm, hnonloop v hv, hnonloop w hw, heq.symm⟩⟩)
  · obtain ⟨r, hr, hd⟩ := hσ.1
    refine ⟨r ⟨v, hv⟩, r ⟨w, hw⟩, hr ⟨v, hv⟩, hr ⟨w, hw⟩, hd _ _ ?_⟩
    intro heq
    exact hvw (congrArg Subtype.val heq)

theorem actualX_badVertices_empty (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ actualX M) :
    badVertices (actualArcLabels M) σ = ∅ := by
  classical
  ext v
  simp only [Finset.notMem_empty, iff_false]
  intro hv
  rcases Finset.mem_filter.mp hv with ⟨hvσ, hl | ⟨w, hwσ, hwv, hvl, hwl, heq⟩⟩
  · exact hσ.1 v hvσ hl
  · exact (hσ.2 v hvσ w hwσ hwv.symm).2.2.2.1 heq.symm

theorem actualX_mem_actualY_zero_iff (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ actualX M) :
    σ ∈ actualY M 0 ↔ σ ∈ actualA M := by
  constructor
  · exact And.left
  · intro hA
    exact ⟨hA, by rw [actualX_badVertices_empty M σ hσ]; simp⟩

/-- The literal quotient-class support of a finite family of actual essential arcs.
Repeated classes are removed by the image, rather than counted as new vertices. -/
noncomputable def finiteArcSupport (M : HyperellipticModel E S)
    {I : Type} [Fintype I] (r : I → EssentialMarkedArc M) :
    Finset (EssentialArcClass M) := by
  classical
  exact Finset.univ.image (fun i => Quotient.mk (essentialArcSetoid M) (r i))

theorem finiteArcSupport_mem_actualA (M : HyperellipticModel E S)
    {I : Type} [Fintype I] (r : I → EssentialMarkedArc M)
    (hd : ∀ i j,
      Quotient.mk (essentialArcSetoid M) (r i) ≠
        Quotient.mk (essentialArcSetoid M) (r j) →
      Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    finiteArcSupport M r ∈ actualA M := by
  classical
  have pre : ∀ v : {v // v ∈ finiteArcSupport M r},
      ∃ i, Quotient.mk (essentialArcSetoid M) (r i) = v.val := by
    intro v
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp v.property
    exact ⟨i, hi⟩
  choose lift hlift using pre
  change IsArcSimplex M (finiteArcSupport M r)
  refine ⟨fun v => r (lift v), hlift, ?_⟩
  intro v w hvw
  apply hd
  intro heq
  exact hvw (Subtype.ext ((hlift v).symm.trans (heq.trans (hlift w))))

theorem finiteArcSupport_card_le (M : HyperellipticModel E S)
    {I : Type} [Fintype I] (r : I → EssentialMarkedArc M) :
    (finiteArcSupport M r).card ≤ Fintype.card I := by
  classical
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

/-- A concrete finite disjoint representative family is already inside the
filtration at its number of indexing slots, including quotient duplicates. -/
theorem finiteArcSupport_mem_actualY (M : HyperellipticModel E S)
    {I : Type} [Fintype I] (r : I → EssentialMarkedArc M)
    (hd : ∀ i j,
      Quotient.mk (essentialArcSetoid M) (r i) ≠
        Quotient.mk (essentialArcSetoid M) (r j) →
      Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    finiteArcSupport M r ∈ actualY M (Fintype.card I) := by
  classical
  refine ⟨finiteArcSupport_mem_actualA M r hd, ?_⟩
  have hc := (Finset.card_le_card
    (Finset.filter_subset _ _ : badVertices (actualArcLabels M) (finiteArcSupport M r) ⊆
      finiteArcSupport M r)).trans (finiteArcSupport_card_le M r)
  exact_mod_cast hc

/-- Every genuine A simplex stabilizes at its own finite cardinality. This
requires no global twelve-arc bound. -/
theorem actualY_simplex_stabilizes (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ actualA M) :
    σ ∈ actualY M σ.card := by
  classical
  refine ⟨hσ, ?_⟩
  exact_mod_cast Finset.card_le_card
    (Finset.filter_subset _ _ : badVertices (actualArcLabels M) σ ⊆ σ)

theorem actualY_mono (M : HyperellipticModel E S) {p q : ℤ} (hpq : p ≤ q)
    {σ : Finset (EssentialArcClass M)} (hσ : σ ∈ actualY M p) :
    σ ∈ actualY M q :=
  ⟨hσ.1, hσ.2.trans hpq⟩

/-- Filtration membership gives a simultaneous representative family matching
any specified representative at one vertex, without changing its finite support. -/
theorem actualY_fixed_representative (M : HyperellipticModel E S)
    {p : ℤ} {σ : Finset (EssentialArcClass M)} (hσ : σ ∈ actualY M p)
    (u : {v // v ∈ σ}) (a : EssentialMarkedArc M)
    (ha : Quotient.mk (essentialArcSetoid M) a = u.val) :
    ∃ s : {v // v ∈ σ} → EssentialMarkedArc M,
      (∀ v, Quotient.mk (essentialArcSetoid M) (s v) = v.val) ∧
      (s u).val.image = a.val.image ∧
      (∀ v w, v ≠ w → Disjoint (arcInterior M (s v)) (arcInterior M (s w))) ∧
      (badVertices (actualArcLabels M) σ).card ≤ p := by
  obtain ⟨r, hr, hd⟩ := hσ.1
  obtain ⟨s, hs, himage, hdisj⟩ :=
    actual_family_realign_to_representative M r hr hd u a ha
  exact ⟨s, hs, himage, hdisj, hσ.2⟩

/-- Every actual filtration simplex has its canonical bad stratum and a
restricted-link witness. Conversely those actual witnesses reconstruct it. -/
theorem actualY_mem_iff_stratum_split (M : HyperellipticModel E S)
    (σ : Finset (EssentialArcClass M)) (p : ℤ) :
    σ ∈ actualY M p ↔
      ∃ q : ℕ, (q : ℤ) ≤ p ∧
        ∃! T : ActualStratum M q,
          ∃ τ : Finset (EssentialArcClass M), τ ∈ actualRestrictedLink M T ∧
            σ = T.val ∪ τ := by
  classical
  constructor
  · intro hσ
    refine ⟨(badVertices (actualArcLabels M) σ).card, hσ.2, ?_⟩
    exact unique_bad_support_split (actualA M) (actualArcLabels M) hσ.1 _ rfl
  · rintro ⟨q, hqp, T, ⟨τ, hτ, hσ⟩, _⟩
    subst σ
    refine ⟨hτ.2.1, ?_⟩
    rw [hτ.2.2, T.property.2.1]
    exact hqp

/-- Passing to a finite quotient image recovers exactly the original simplex
when the concrete family represents its named vertices. -/
theorem finiteArcSupport_of_representatives (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val) :
    finiteArcSupport M r = σ := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hv
    exact (hw ▸ hr w ▸ w.property)
  · intro hv
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, hr ⟨v, hv⟩⟩

/-- The exact unconditional zero-level description. The remaining geometric
producer must show that every X simplex lies in A to remove this intersection. -/
theorem actualY_zero_simplices (M : HyperellipticModel E S) :
    (actualY M 0).simplices = (actualA M).simplices ∩ (actualX M).simplices := by
  classical
  ext σ
  constructor
  · intro hσ
    exact ⟨hσ.1, actualY_zero_subcomplex_actualX M σ hσ⟩
  · rintro ⟨hA, hX⟩
    exact (actualX_mem_actualY_zero_iff M σ hX).mpr hA

/-- The actual filtration exhausts A. The remaining twelve-arc producer must
make this pointwise stabilization uniform at level twelve. -/
theorem actualY_exhausts_actualA (M : HyperellipticModel E S) :
    (⋃ p : ℕ, (actualY M p).simplices) = (actualA M).simplices := by
  classical
  ext σ
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hσ⟩
    exact hσ.1
  · intro hσ
    exact ⟨σ.card, actualY_simplex_stabilizes M σ hσ⟩

/-- Concrete systems indexed by a subset of the twelve slots belong to the
literal level twelve. This counts quotient support, not an assumed A bound. -/
theorem finiteArcSupport_twelve_slots (M : HyperellipticModel E S)
    (slots : Finset (Fin 12)) (r : {i // i ∈ slots} → EssentialMarkedArc M)
    (hd : ∀ i j,
      Quotient.mk (essentialArcSetoid M) (r i) ≠
        Quotient.mk (essentialArcSetoid M) (r j) →
      Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    finiteArcSupport M r ∈ actualY M 12 := by
  classical
  apply actualY_mono M ?_ (finiteArcSupport_mem_actualY M r hd)
  have hc : Fintype.card {i // i ∈ slots} ≤ 12 := by
    rw [Fintype.card_coe]
    exact Finset.card_le_univ slots
  exact_mod_cast hc

/-- Actual endpoint sets certify that a finite representative family has no
bad quotient classes. Distinct representatives of the same class are harmless. -/
theorem finiteArcSupport_badVertices_empty (M : HyperellipticModel E S)
    {I : Type} [Fintype I] (r : I → EssentialMarkedArc M)
    (hn : ∀ i, (arcEndpoints M (r i)).card = 2)
    (hp : ∀ i j,
      Quotient.mk (essentialArcSetoid M) (r i) ≠
        Quotient.mk (essentialArcSetoid M) (r j) →
      arcEndpoints M (r i) ≠ arcEndpoints M (r j)) :
    badVertices (actualArcLabels M) (finiteArcSupport M r) = ∅ := by
  classical
  ext v
  simp only [Finset.notMem_empty, iff_false]
  intro hv
  rcases Finset.mem_filter.mp hv with ⟨hv, hloop | ⟨w, hw, hwv, _, _, heq⟩⟩
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    change (arcEndpoints M (r i)).card = 1 at hloop
    have hi := hn i
    omega
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    change arcEndpoints M (r j) = arcEndpoints M (r i) at heq
    exact hp i j hwv.symm heq.symm

/-- Direct level-zero transport from concrete disjoint arcs and their literal
endpoint sets, ready for a geometric representative producer. -/
theorem finiteArcSupport_mem_actualY_zero (M : HyperellipticModel E S)
    {I : Type} [Fintype I] (r : I → EssentialMarkedArc M)
    (hd : ∀ i j,
      Quotient.mk (essentialArcSetoid M) (r i) ≠
        Quotient.mk (essentialArcSetoid M) (r j) →
      Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (hn : ∀ i, (arcEndpoints M (r i)).card = 2)
    (hp : ∀ i j,
      Quotient.mk (essentialArcSetoid M) (r i) ≠
        Quotient.mk (essentialArcSetoid M) (r j) →
      arcEndpoints M (r i) ≠ arcEndpoints M (r j)) :
    finiteArcSupport M r ∈ actualY M 0 := by
  refine ⟨finiteArcSupport_mem_actualA M r hd, ?_⟩
  rw [finiteArcSupport_badVertices_empty M r hn hp]
  simp

end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.empty_mem_actualA
#print axioms CurveComplex.HyperellipticModel.actual_filtration_lower_endpoints
#print axioms CurveComplex.HyperellipticModel.xSimplex_down
#print axioms CurveComplex.HyperellipticModel.actualY_zero_subcomplex_actualX
#print axioms CurveComplex.HyperellipticModel.actualX_badVertices_empty
#print axioms CurveComplex.HyperellipticModel.actualX_mem_actualY_zero_iff
#print axioms CurveComplex.HyperellipticModel.finiteArcSupport_mem_actualA
#print axioms CurveComplex.HyperellipticModel.finiteArcSupport_card_le
#print axioms CurveComplex.HyperellipticModel.finiteArcSupport_mem_actualY
#print axioms CurveComplex.HyperellipticModel.actualY_simplex_stabilizes
#print axioms CurveComplex.HyperellipticModel.actualY_mono
#print axioms CurveComplex.HyperellipticModel.actualY_fixed_representative
#print axioms CurveComplex.HyperellipticModel.actualY_mem_iff_stratum_split
#print axioms CurveComplex.HyperellipticModel.finiteArcSupport_of_representatives
#print axioms CurveComplex.HyperellipticModel.actualY_zero_simplices
#print axioms CurveComplex.HyperellipticModel.actualY_exhausts_actualA
#print axioms CurveComplex.HyperellipticModel.finiteArcSupport_twelve_slots
#print axioms CurveComplex.HyperellipticModel.finiteArcSupport_badVertices_empty
#print axioms CurveComplex.HyperellipticModel.finiteArcSupport_mem_actualY_zero
