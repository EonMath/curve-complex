import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualDiskBigonChartProducer
import CurveComplexGenusTwo.Filtration.Geometry.ActualEndpointBigonEnlargement
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface

noncomputable section
namespace CurveComplex
open Set Topology Schoenflies

/-- The existing supported crosscut move replaces raw tails, with arbitrary
unmarked common endpoints. The actual enlargement protects the full closed
obstacle at EVERY time. No marked-arc interpretation of a raw tail is used. -/
theorem actual_raw_bigon_supported_replacement
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
    (f : Plane → S) (hf : IsOpenEmbedding f)
    (A B : Set Plane) (p q : Plane)
    (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
    (hwhole : A ∪ B = modelCurve)
    (Q : Set S) (hQc : IsClosed Q)
    (hQboundary : ∀ z ∈ modelCurve, f z ∈ Q → z=p ∨ z=q)
    (hQinside : Disjoint (f '' Plane.openSquare 0 1) Q) :
    ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ Q → G.map (t,z) = z) ∧
      G.finalMap '' (f '' A) = f '' B := by
  classical
  let F := f ⁻¹' Q ∪ ({p,q} : Set Plane)
  have hFc : IsClosed F := (hQc.preimage hf.continuous).union ((Set.finite_singleton q).insert p).isClosed
  have hpC : p ∈ modelCurve := hwhole ▸ Or.inl hA.left_mem
  have hqC : q ∈ modelCurve := hwhole ▸ Or.inl hA.right_mem
  have hFb : ∀ z ∈ F, z ∈ modelCurve → z=p ∨ z=q := by
    intro z hz hzc
    rcases hz with hz | hz
    · exact hQboundary z hzc hz
    · simpa only [mem_insert_iff,mem_singleton_iff] using hz
  have hFi : Disjoint (Plane.openSquare 0 1) F := by
    apply Set.disjoint_left.mpr
    intro z hzi hzF
    rcases hzF with hzQ | hz
    · exact Set.disjoint_left.mp hQinside (mem_image_of_mem f hzi) hzQ
    · have hzC : z ∈ modelCurve := by
        rcases mem_insert_iff.mp hz with rfl | hz
        · exact hpC
        · exact mem_singleton_iff.mp hz ▸ hqC
      exact (show Disjoint (Plane.openSquare 0 1) modelCurve by
        rw [← inside_modelCurve]; exact (disjoint_curve_inside modelCurve).symm).le_bot ⟨hzi,hzC⟩
  obtain ⟨φ,hφp,hφq,hA',hB',hAi,hBi,hfree⟩ :=
    actual_endpoint_preserving_bigon_enlargement A B p q hA hB hwhole F hFc
      (Or.inr (mem_insert p _)) (Or.inr (mem_insert_of_mem p (mem_singleton q))) hFb hFi
  let k := f ∘ φ
  have hk : IsOpenEmbedding k := hf.comp φ.isOpenEmbedding
  let J : Plane ≃ₜ range k := hk.isEmbedding.toHomeomorph
  let e : range k ≃ₜ (univ : Set Plane) := J.symm.trans (Homeomorph.Set.univ Plane).symm
  have he (u : range k) : (e u : Plane) = J.symm u := rfl
  have hJ (u : range k) : k (J.symm u) = u.val := congrArg Subtype.val (J.apply_symm_apply u)
  have htrace (C : Set Plane) :
      {x : S | ∃ u : range k, u.val=x ∧ (e u : Plane) ∈ C} = k '' C := by
    ext x
    constructor
    · rintro ⟨u,rfl,hu⟩
      exact ⟨J.symm u,hu,hJ u⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨J z,rfl,?_⟩
      simpa only [he,J.symm_apply_apply] using hz
  obtain ⟨G,hmove,hfix⟩ := position_crosscut_surface_square_support S
    (range k) univ hk.isOpenMap.isOpen_range e (subset_univ _)
    (φ.symm '' A) (φ.symm '' B) p q hA' hB' hpC hqC hAi hBi
  rw [htrace,htrace] at hmove
  rw [htrace] at hfix
  have hcancel (C : Set Plane) : k '' (φ.symm '' C) = f '' C := by
    change (f ∘ φ) '' (φ.symm '' C) = f '' C
    ext z; simp
  refine ⟨G,?_,by simpa only [hcancel] using hmove⟩
  intro t z hzQ
  apply hfix t z
  rintro ⟨x,hx,hxz⟩
  apply hfree x hx
  left
  change f (φ x) = z at hxz
  change f (φ x) ∈ Q
  rw [hxz]
  exact hzQ

namespace HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Produce the marked/protected raw-tail move from actual embedded disk data.
The raw sides are subarcs of possibly LOOP representatives; their endpoints
need not be branch marks. The chart and enlarged support are constructed. -/
theorem actual_raw_disk_bigon_supported_replacement
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (D : ActualMarkedTwoSideDisk M a b)
    (Q : Set S) (hQc : IsClosed Q)
    (hQboundary : ∀ z ∈ range D.firstSide ∪ range D.secondSide,
      z ∈ Q → z = D.firstCorner ∨ z = D.secondCorner)
    (hQinside : Disjoint D.openInterior Q) :
    ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ Q → G.map (t,z) = z) ∧
      G.finalMap '' range D.firstSide = range D.secondSide := by
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨f,A,B,p,q,hf,hA,hB,hwhole,hfA,hfB,hfp,hfq,hfi⟩ :=
    actual_two_side_disk_produces_bigon_chart M a b D
  have hb : ∀ z ∈ modelCurve, f z ∈ Q → z=p ∨ z=q := by
    intro z hz hzQ
    have hzB : f z ∈ range D.firstSide ∪ range D.secondSide := by
      rw [← hfA,← hfB,← image_union,hwhole]
      exact mem_image_of_mem f hz
    rcases hQboundary (f z) hzB hzQ with hzp | hzq
    · exact Or.inl (hf.injective (hzp.trans hfp.symm))
    · exact Or.inr (hf.injective (hzq.trans hfq.symm))
  obtain ⟨G,hfix,hmove⟩ := actual_raw_bigon_supported_replacement f hf A B p q
    hA hB hwhole Q hQc hb (by rwa [hfi])
  exact ⟨G,hfix,by simpa only [hfA,hfB] using hmove⟩

/-- The raw-tail move reaches the SPECIFIED complete target, including loops,
when both complete images share the actual closed exterior E. All of E,
marks and the original protected graph Q remain fixed at every time. -/
theorem actual_common_exterior_disk_bigon_alignment
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (D : ActualMarkedTwoSideDisk M a b)
    (E₀ Q : Set S) (hQc : IsClosed Q)
    (hmQ : (M.cover.branch : Set S) ⊆ Q) (hEQ : E₀ ⊆ Q)
    (ha : a.val.image = E₀ ∪ range D.firstSide)
    (hb : b.val.image = E₀ ∪ range D.secondSide)
    (hQboundary : ∀ z ∈ range D.firstSide ∪ range D.secondSide,
      z ∈ Q → z = D.firstCorner ∨ z = D.secondCorner)
    (hQinside : Disjoint D.openInterior Q) :
    ∃ G : AmbientIsotopy S,
      (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
      (∀ t z, z ∈ Q → G.map (t,z) = z) ∧
      (∀ t z, z ∈ E₀ → G.map (t,z) = z) ∧
      G.finalMap '' a.val.image = b.val.image ∧
      Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b := by
  obtain ⟨G,hfix,hmove⟩ := actual_raw_disk_bigon_supported_replacement M a b D Q hQc
    hQboundary hQinside
  have hE : G.finalMap '' E₀ = E₀ := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [AmbientIsotopy.finalMap,hfix _ x (hEQ hx)] using hx
    · intro hz
      exact ⟨z,hz,hfix _ z (hEQ hz)⟩
  have himage : G.finalMap '' a.val.image = b.val.image := by
    rw [ha,hb,image_union,hE,hmove]
  have hm := fun t z hz => hfix t z (hmQ hz)
  exact ⟨G,hm,hfix,fun t z hz => hfix t z (hEQ hz),himage,Quotient.sound ⟨G,hm,himage⟩⟩

#print axioms actual_raw_bigon_supported_replacement
#print axioms actual_raw_disk_bigon_supported_replacement
#print axioms actual_common_exterior_disk_bigon_alignment
end HyperellipticModel
end CurveComplex
