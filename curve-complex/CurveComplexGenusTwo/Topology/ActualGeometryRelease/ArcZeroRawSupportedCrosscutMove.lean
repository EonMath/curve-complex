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

end CurveComplex
