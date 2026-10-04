import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology

def actualReverseEmbeddedSide {X : Type} [TopologicalSpace X]
    (f : C(Interval,X)) : C(Interval,X) :=
  ⟨f ∘ unitInterval.symm,f.continuous.comp unitInterval.continuous_symm⟩

@[simp] theorem actualReverseEmbeddedSide_zero {X : Type} [TopologicalSpace X]
    (f : C(Interval,X)) : actualReverseEmbeddedSide f 0 = f 1 := by
  simp [actualReverseEmbeddedSide]

@[simp] theorem actualReverseEmbeddedSide_one {X : Type} [TopologicalSpace X]
    (f : C(Interval,X)) : actualReverseEmbeddedSide f 1 = f 0 := by
  simp [actualReverseEmbeddedSide]

theorem actualReverseEmbeddedSide_range {X : Type} [TopologicalSpace X]
    (f : C(Interval,X)) : range (actualReverseEmbeddedSide f) = range f := by
  exact unitInterval.symm_bijective.surjective.range_comp f

theorem actualReverseEmbeddedSide_embedded {X : Type} [TopologicalSpace X]
    (f : C(Interval,X)) (hf : IsEmbedding f) : IsEmbedding (actualReverseEmbeddedSide f) := by
  -- The domain involution is a homeomorphism, so no separation hypothesis is needed.
  let e : Interval ≃ₜ Interval := {
    toEquiv := {
      toFun := unitInterval.symm
      invFun := unitInterval.symm
      left_inv := unitInterval.symm_symm
      right_inv := unitInterval.symm_symm }
    continuous_toFun := unitInterval.continuous_symm
    continuous_invFun := unitInterval.continuous_symm }
  have he : IsEmbedding unitInterval.symm := e.isEmbedding
  exact hf.comp he

/-- Reorient an ACTUAL constructed half-bigon, retaining a possibly marked
corner as its initial endpoint and an unmarked terminal endpoint. The old
base mark may disappear in the subdisk; it need not be retained artificially. -/
theorem actual_half_bigon_orient_marked_corner
    {X : Type} [TopologicalSpace X] (marks K : Set X) (p : X)
    (f g : C(Interval,X)) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hzero : f 0 = g 0) (hone : f 1 = g 1)
    (h0K : g 0 ∈ K) (h1K : g 1 ∈ K)
    (hmark : ∀ z ∈ K, z ∈ marks → z = p)
    (hcorners : ∀ z ∈ K, z ∈ marks → z = f 0 ∨ z = f 1) :
    ∃ f' g' : C(Interval,X),
      IsEmbedding f' ∧ IsEmbedding g' ∧
      range f' = range f ∧ range g' = range g ∧
      f' 0 = g' 0 ∧ f' 1 = g' 1 ∧
      (∀ z ∈ K, z ∈ marks → z = g' 0) ∧ g' 1 ∉ marks := by
  classical
  by_cases h1 : g 1 ∈ marks
  · have h1p := hmark (g 1) h1K h1
    have h0 : g 0 ∉ marks := by
      intro hm
      have h0p := hmark (g 0) h0K hm
      have he := hg.injective (h0p.trans h1p.symm)
      exact zero_ne_one he
    refine ⟨actualReverseEmbeddedSide f,actualReverseEmbeddedSide g,
      actualReverseEmbeddedSide_embedded f hf,actualReverseEmbeddedSide_embedded g hg,
      actualReverseEmbeddedSide_range f,actualReverseEmbeddedSide_range g,?_,?_,?_,?_⟩
    · simpa using hone
    · simpa using hzero
    · intro z hz hm
      simpa using (hmark z hz hm).trans h1p.symm
    · simpa using h0
  · refine ⟨f,g,hf,hg,rfl,rfl,hzero,hone,?_,h1⟩
    intro z hz hm
    rcases hcorners z hz hm with he | he
    · exact he.trans hzero
    · exact False.elim (h1 ((he.trans hone) ▸ hm))

#print axioms actualReverseEmbeddedSide_zero
#print axioms actualReverseEmbeddedSide_one
#print axioms actualReverseEmbeddedSide_range
#print axioms actualReverseEmbeddedSide_embedded
#print axioms actual_half_bigon_orient_marked_corner
end CurveComplex.HyperellipticModel
