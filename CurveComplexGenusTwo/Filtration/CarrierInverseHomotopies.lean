import CurveComplexGenusTwo.Filtration.CarrierApproximationHomology
import CurveComplexGenusTwo.Foundations.ConeRealization
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.Grp.Adjunctions

open CategoryTheory Topology Convexity
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace CurveComplex.CarrierEmbedding
universe u v
variable {W : Type u} {V : Type v} [DecidableEq W] [DecidableEq V]

noncomputable def mapPoint (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces)
    (x : RealizationPoint L) : RealizationPoint K := by
  classical
  refine ⟨Function.extend f x.weight (fun _ => 0), ?_, ?_⟩
  · intro v
    by_cases hv : ∃ w, f w = v
    · obtain ⟨w, rfl⟩ := hv
      rw [f.injective.extend_apply]
      exact x.nonneg w
    · rw [Function.extend_apply' _ _ _ hv]
  · obtain ⟨σ, hσ, hz, hs⟩ := x.liesInFace
    refine ⟨σ.image f, hf σ hσ, ?_, ?_⟩
    · intro v hv
      by_cases hw : ∃ w, f w = v
      · obtain ⟨w, rfl⟩ := hw
        rw [f.injective.extend_apply]
        exact hz w (by simpa only [Finset.mem_image, f.injective.eq_iff, exists_eq_right] using hv)
      · exact Function.extend_apply' _ _ _ hw
    · rw [Finset.sum_image (fun _ _ _ _ h => f.injective h)]
      simpa only [f.injective.extend_apply] using hs

@[simp] theorem mapPoint_weight (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces)
    (x : RealizationPoint L) (w : W) :
    (mapPoint L K f hf x).weight (f w) = x.weight w := by
  simp only [mapPoint, f.injective.extend_apply]

theorem mapPoint_weight_outside (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces)
    (x : RealizationPoint L) (v : V) (hv : v ∉ Set.range f) :
    (mapPoint L K f hf x).weight v = 0 := by
  simp only [mapPoint, Function.extend_apply' _ _ _ hv]

theorem mapPoint_injective (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces) :
    Function.Injective (mapPoint L K f hf) := by
  intro x y h
  apply RealizationPoint.ext
  funext w
  have hh := congrArg (fun z : RealizationPoint K => z.weight (f w)) h
  simpa only [mapPoint_weight] using hh

noncomputable def faceEquiv (f : W ↪ V) (σ : Finset W) : σ ≃ σ.image f :=
  Equiv.ofBijective (fun w => ⟨f w, Finset.mem_image.mpr ⟨w, w.2, rfl⟩⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      exact f.injective (congrArg Subtype.val h)
    · rintro ⟨v, hv⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨⟨w, hw⟩, rfl⟩)

noncomputable def mapFiniteSimplex (f : W ↪ V) (σ : Finset W)
    (x : FiniteSimplex σ) : FiniteSimplex (σ.image f) :=
  ⟨fun w => x.1 ((faceEquiv f σ).symm w),
    (fun w => x.2.1 _), by
      rw [Equiv.sum_comp]
      exact x.2.2⟩

theorem mapFiniteSimplex_continuous (f : W ↪ V) (σ : Finset W) :
    Continuous (mapFiniteSimplex f σ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  exact (continuous_apply ((faceEquiv f σ).symm w)).comp continuous_subtype_val

theorem mapPoint_faceInclusion (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces)
    (σ : Finset W) (hσ : σ ∈ L.faces) (x : FiniteSimplex σ) :
    mapPoint L K f hf (faceInclusion L σ hσ x) =
      faceInclusion K (σ.image f) (hf σ hσ) (mapFiniteSimplex f σ x) := by
  classical
  apply RealizationPoint.ext
  funext v
  by_cases hv : ∃ w, f w = v
  · obtain ⟨w, rfl⟩ := hv
    rw [mapPoint_weight]
    by_cases hw : w ∈ σ
    · rw [faceInclusion_weight_of_mem L σ hσ x w hw,
        faceInclusion_weight_of_mem K (σ.image f) (hf σ hσ) _ (f w)
          (Finset.mem_image.mpr ⟨w, hw, rfl⟩)]
      change x.1 ⟨w, hw⟩ = x.1 ((faceEquiv f σ).symm (faceEquiv f σ ⟨w, hw⟩))
      rw [Equiv.symm_apply_apply]
    · rw [faceInclusion_weight_of_not_mem L σ hσ x w hw,
        faceInclusion_weight_of_not_mem K (σ.image f) (hf σ hσ) _ (f w) (by
          simpa only [Finset.mem_image, f.injective.eq_iff, exists_eq_right] using hw)]
  · rw [mapPoint_weight_outside L K f hf _ v hv,
      faceInclusion_weight_of_not_mem K (σ.image f) (hf σ hσ) _ v (by
        intro h
        obtain ⟨w, hw, he⟩ := Finset.mem_image.mp h
        exact hv ⟨w, he⟩)]

theorem mapPoint_continuous (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces) :
    Continuous (mapPoint L K f hf) := by
  apply (continuous_iff_continuous_on_faces L _).mpr
  intro σ hσ
  have he : mapPoint L K f hf ∘ faceInclusion L σ hσ =
      faceInclusion K (σ.image f) (hf σ hσ) ∘ mapFiniteSimplex f σ := by
    funext x
    exact mapPoint_faceInclusion L K f hf σ hσ x
  rw [he]
  exact (continuous_faceInclusion K _ _).comp (mapFiniteSimplex_continuous f σ)

theorem mapPoint_isClosedMap (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces) :
    IsClosedMap (mapPoint L K f hf) := by
  classical
  intro A hA
  rw [← isOpen_compl_iff]
  change ∀ (σ : Finset V) (hσ : σ ∈ K.faces),
    IsOpen ((faceInclusion K σ hσ) ⁻¹' (mapPoint L K f hf '' A)ᶜ)
  intro σ hσ
  rw [Set.preimage_compl, isOpen_compl_iff]
  let ρ := σ.preimage f f.injective.injOn
  let t := ρ.powerset.filter (fun τ => τ ∈ L.faces)
  let B : Set (RealizationPoint K) := ⋃ τ ∈ t,
    mapPoint L K f hf '' (A ∩ faceCarrier L τ)
  have hB : IsClosed B := by
    apply isClosed_biUnion_finset
    intro τ hτ
    have hface : τ ∈ L.faces := (Finset.mem_filter.mp hτ).2
    have hcompact : IsCompact (faceCarrier L τ) := by
      rw [faceCarrier_eq_range_faceInclusion L τ hface]
      exact isCompact_range (continuous_faceInclusion L τ hface)
    exact ((hcompact.inter_left hA).image (mapPoint_continuous L K f hf)).isClosed
  have he : (faceInclusion K σ hσ) ⁻¹' (mapPoint L K f hf '' A) =
      (faceInclusion K σ hσ) ⁻¹' B := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      have hsupp : supportFinset L y ⊆ ρ := by
        intro w hw
        apply Finset.mem_preimage.mpr
        by_contra hnot
        have hzero := faceInclusion_weight_of_not_mem K σ hσ x (f w) hnot
        rw [← he, mapPoint_weight] at hzero
        exact (mem_supportFinset_iff L y w).mp hw hzero
      apply Set.mem_iUnion.mpr
      refine ⟨supportFinset L y, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsupp, supportFinset_mem_faces L y⟩
      · refine ⟨y, ⟨hy, ?_⟩, he⟩
        exact (mem_faceCarrier_iff_support_subset L _ y).mpr (Finset.Subset.refl _)
    · intro hx
      obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hτ, y, hy, he⟩ := Set.mem_iUnion.mp hτ
      exact ⟨y, hy.1, he⟩
  rw [he]
  exact hB.preimage (continuous_faceInclusion K σ hσ)

theorem mapPoint_isClosedEmbedding (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces) :
    Topology.IsClosedEmbedding (mapPoint L K f hf) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (mapPoint_continuous L K f hf) (mapPoint_injective L K f hf)
    (mapPoint_isClosedMap L K f hf)

#print axioms mapPoint_isClosedEmbedding

end CurveComplex.CarrierEmbedding

namespace CurveComplex.CarrierEmbedding
universe u v
variable {W : Type u} {V : Type v} [DecidableEq W] [DecidableEq V]

theorem mapFiniteSimplex_surjective (f : W ↪ V) (σ : Finset W) :
    Function.Surjective (mapFiniteSimplex f σ) := by
  intro y
  let x : FiniteSimplex σ := ⟨fun w => y.1 (faceEquiv f σ w),
    fun w => y.2.1 _, by rw [Equiv.sum_comp]; exact y.2.2⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext w
  exact congrArg y.1 ((faceEquiv f σ).apply_symm_apply w)

theorem mem_range_mapPoint_of_support (L : AbstractSimplicialComplex W) (K : AbstractSimplicialComplex V)
    (f : W ↪ V) (hf : ∀ σ, σ ∈ L.faces → σ.image f ∈ K.faces)
    (x : RealizationPoint K) (σ : Finset W) (hσ : σ ∈ L.faces)
    (hx : supportFinset K x ⊆ σ.image f) : x ∈ Set.range (mapPoint L K f hf) := by
  have hcar : x ∈ faceCarrier K (σ.image f) :=
    (mem_faceCarrier_iff_support_subset K _ x).mpr hx
  rw [faceCarrier_eq_range_faceInclusion K _ (hf σ hσ)] at hcar
  obtain ⟨y, hy⟩ := hcar
  obtain ⟨z, rfl⟩ := mapFiniteSimplex_surjective f σ y
  exact ⟨faceInclusion L σ hσ z, (mapPoint_faceInclusion L K f hf σ hσ z).trans hy⟩
end CurveComplex.CarrierEmbedding

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]
open CurveComplex

noncomputable def activeVertexInclusion (L K : FiniteComplex V) (h : L.simplices ⊆ K.simplices) :
    ActiveVertex L ↪ ActiveVertex K :=
  ⟨fun v => ⟨v.1, h v.2⟩, fun _ _ he => Subtype.ext (congrArg (fun v : ActiveVertex K => v.1) he)⟩

theorem activeVertexInclusion_faces (L K : FiniteComplex V) (h : L.simplices ⊆ K.simplices)
    (σ : Finset (ActiveVertex L)) (hσ : σ ∈ (geometricComplex L).faces) :
    σ.image (activeVertexInclusion L K h) ∈ (geometricComplex K).faces := by
  letI : DecidableEq (ActiveVertex K) := activeVertexDecidableEq K
  letI : DecidableEq (ActiveVertex L) := activeVertexDecidableEq L
  refine ⟨hσ.1.image _, ?_⟩
  change (σ.image (activeVertexInclusion L K h)).image Subtype.val ∈ K
  have he : (σ.image (activeVertexInclusion L K h)).image Subtype.val = σ.image Subtype.val := by
    ext v
    constructor
    · rintro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
    · intro hv
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨activeVertexInclusion L K h z,
        Finset.mem_image.mpr ⟨z, hz, rfl⟩, rfl⟩
  rw [he]
  exact h hσ.2

noncomputable def finiteRealizationInclusion (L K : FiniteComplex V) (h : L.simplices ⊆ K.simplices) :
    C(geometricRealization L, geometricRealization K) :=
  ⟨CarrierEmbedding.mapPoint (geometricComplex L) (geometricComplex K)
    (activeVertexInclusion L K h) (activeVertexInclusion_faces L K h),
    CarrierEmbedding.mapPoint_continuous _ _ _ _⟩

theorem finiteRealizationInclusion_isClosedEmbedding (L K : FiniteComplex V)
    (h : L.simplices ⊆ K.simplices) :
    Topology.IsClosedEmbedding (finiteRealizationInclusion L K h) :=
  CarrierEmbedding.mapPoint_isClosedEmbedding _ _ _ (activeVertexInclusion_faces L K h)

@[simp] theorem finiteRealizationInclusion_weight (L K : FiniteComplex V)
    (h : L.simplices ⊆ K.simplices) (x : geometricRealization L) (v : ActiveVertex L) :
    (finiteRealizationInclusion L K h x).weight ⟨v.1, h v.2⟩ = x.weight v :=
  CarrierEmbedding.mapPoint_weight _ _ _ (activeVertexInclusion_faces L K h) x v

noncomputable abbrev carrierRealizationInclusion (K : FiniteComplex V)
    (S : Set (geometricRealization K)) :=
  finiteRealizationInclusion (realizationCarrier K S) K (realizationCarrier_subcomplex K S)

theorem mem_range_carrierRealizationInclusion (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (x : geometricRealization K) (hx : x ∈ S) :
    x ∈ Set.range (carrierRealizationInclusion K S) := by
  classical
  letI : DecidableEq (ActiveVertex K) := activeVertexDecidableEq K
  letI : DecidableEq (ActiveVertex (realizationCarrier K S)) := activeVertexDecidableEq _
  let τ := supportFinset (geometricComplex K) x
  have hτ : τ.image Subtype.val ∈ realizationCarrier K S := by
    refine ⟨x, hx, ?_⟩
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨w.2, (mem_supportFinset_iff_pos (geometricComplex K) x w).mp hw⟩
  let g : τ → ActiveVertex (realizationCarrier K S) := fun w =>
    ⟨w.1.1, (realizationCarrier K S).down_closed
      (Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩)) hτ⟩
  let σ := Finset.univ.image g
  have hσimage : σ.image (activeVertexInclusion _ K (realizationCarrier_subcomplex K S)) = τ := by
    ext v
    simp only [σ, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨a, rfl⟩, he⟩
      have hav : a.1 = v := Subtype.ext (congrArg Subtype.val he)
      exact hav ▸ a.2
    · intro hv
      exact ⟨g ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
  have hσface : σ ∈ (geometricComplex (realizationCarrier K S)).faces := by
    refine ⟨?_, ?_⟩
    · have ht : τ.Nonempty := supportFinset_nonempty (geometricComplex K) x
      rw [← hσimage] at ht
      exact Finset.image_nonempty.mp ht
    · have he : σ.image Subtype.val = τ.image Subtype.val := by
        ext v
        constructor
        · intro hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          refine Finset.mem_image.mpr ⟨activeVertexInclusion _ K (realizationCarrier_subcomplex K S) w, ?_, rfl⟩
          rw [← hσimage]
          exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
        · intro hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          rw [← hσimage] at hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
      rw [he]
      exact hτ
  apply CarrierEmbedding.mem_range_mapPoint_of_support _ _ _
    (activeVertexInclusion_faces _ K (realizationCarrier_subcomplex K S)) x σ hσface
  rw [hσimage]

/-- Every singular simplex lifts continuously into its actual image carrier. -/
theorem singularSimplex_lifts_to_realizationCarrier (K : FiniteComplex V) (n : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) :
    ∃ t : C(StdSimplex ℝ (Fin (n+1)),
        geometricRealization (realizationCarrier K (singularSimplexImage K n s))),
      (carrierRealizationInclusion K (singularSimplexImage K n s)).comp t =
        TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K)) (.op ⦋n⦌) s := by
  classical
  let S := singularSimplexImage K n s
  let j := carrierRealizationInclusion K S
  let f := TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K)) (.op ⦋n⦌) s
  have hr (x : StdSimplex ℝ (Fin (n+1))) : f x ∈ Set.range j :=
    mem_range_carrierRealizationInclusion K S (f x) ⟨x, rfl⟩
  choose t ht using hr
  have hcont : Continuous t := by
    apply (finiteRealizationInclusion_isClosedEmbedding _ K
      (realizationCarrier_subcomplex K S)).isEmbedding.continuous_iff.mpr
    have he : j ∘ t = f := funext ht
    rw [he]
    exact f.continuous
  exact ⟨⟨t, hcont⟩, ContinuousMap.ext ht⟩

#print axioms singularSimplex_lifts_to_realizationCarrier
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

theorem exists_normalized_starSmall_zero_approximation (K : FiniteComplex V) :
    ∃ f : FreeAbelianGroup (StarSmallSimplex K 0) →+ chains K 0,
      (∀ s : StarSmallSimplex K 0, f (FreeAbelianGroup.of s) ∈
        (chainInclusion (realizationCarrier K (singularSimplexImage K 0 s.1)) K
          (realizationCarrier_subcomplex K _) 0).range) ∧
      (∀ c : FreeAbelianGroup (StarSmallSimplex K 1),
        boundary K 0 (f (starSmallBoundary K 0 c)) = 0) ∧
      (∀ s : StarSmallSimplex K 0, ∃ v : ActiveVertex K,
        f (FreeAbelianGroup.of s) = FreeAbelianGroup.of
          (⟨{v.1}, v.2, Or.inr ⟨by omega, by simp⟩⟩ : SimplexAt K 0)) := by
  classical
  choose v hv using starSmallSimplex_exists_carried_vertex K 0
  let σ (s : StarSmallSimplex K 0) : SimplexAt K 0 :=
    ⟨{(v s).1}, (v s).2, Or.inr ⟨by omega, by simp⟩⟩
  let f : FreeAbelianGroup (StarSmallSimplex K 0) →+ chains K 0 :=
    FreeAbelianGroup.lift (fun s => FreeAbelianGroup.of (σ s))
  have heq (s t : StarSmallSimplex K 0) :
      boundary K 0 (f (FreeAbelianGroup.of s)) =
        boundary K 0 (f (FreeAbelianGroup.of t)) := by
    have he : (∅ : Finset V) ∈ K := K.down_closed (Finset.empty_subset _) (v s).2
    simp [f, σ, boundary, faceBoundary, he, Finset.filter_singleton]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro s
    refine ⟨FreeAbelianGroup.of (⟨{(v s).1}, hv s,
      Or.inr ⟨by omega, by simp⟩⟩ : SimplexAt _ 0), ?_⟩
    rfl
  · intro c
    have h : ((boundary K 0).comp f).comp (starSmallBoundary K 0) = 0 := by
      apply FreeAbelianGroup.lift_ext
      intro s
      change boundary K 0 (f (starSmallBoundary K 0 (FreeAbelianGroup.of s))) = 0
      rw [starSmallBoundary_of, Fin.sum_univ_two]
      simp only [map_add, map_zsmul]
      norm_num
      rw [heq (starSmallFace K 0 0 s) (starSmallFace K 0 1 s), add_neg_cancel]
    exact DFunLike.congr_fun h c

  · intro s
    exact ⟨v s, rfl⟩

noncomputable def normalizedStarSmallZero (K : FiniteComplex V) :
    StarSmallApproximationStage K 0 where
  map := (exists_normalized_starSmall_zero_approximation K).choose
  carried := (exists_normalized_starSmall_zero_approximation K).choose_spec.1
  cycle := (exists_normalized_starSmall_zero_approximation K).choose_spec.2.1

noncomputable def normalizedStarSmallStage (K : FiniteComplex V) :
    (n : ℕ) → StarSmallApproximationStage K n :=
  Nat.rec (normalizedStarSmallZero K) (fun n a => starSmallApproximationNext K n a)

noncomputable def normalizedStarSmallApproximation (K : FiniteComplex V) (n : ℕ) :
    FreeAbelianGroup (StarSmallSimplex K n) →+ chains K (n:ℤ) :=
  (normalizedStarSmallStage K n).map

theorem normalizedStarSmallApproximation_zero (K : FiniteComplex V)
    (s : StarSmallSimplex K 0) : ∃ v : ActiveVertex K,
    normalizedStarSmallApproximation K 0 (FreeAbelianGroup.of s) =
      FreeAbelianGroup.of (⟨{v.1}, v.2, Or.inr ⟨by omega, by simp⟩⟩ : SimplexAt K 0) :=
  (exists_normalized_starSmall_zero_approximation K).choose_spec.2.2 s

theorem normalizedStarSmallApproximation_carried (K : FiniteComplex V) (n : ℕ)
    (s : StarSmallSimplex K n) :
    normalizedStarSmallApproximation K n (FreeAbelianGroup.of s) ∈
      (chainInclusion (realizationCarrier K (singularSimplexImage K n s.1)) K
        (realizationCarrier_subcomplex K _) (n:ℤ)).range :=
  (normalizedStarSmallStage K n).carried s

theorem normalizedStarSmallApproximation_boundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n+1))) :
    positiveBoundary K n (normalizedStarSmallApproximation K (n+1) c) =
      normalizedStarSmallApproximation K n (starSmallBoundary K n c) :=
  starSmallApproximationNext_boundary K n (normalizedStarSmallStage K n) c

#print axioms normalizedStarSmallApproximation_zero
#print axioms normalizedStarSmallApproximation_boundary
end CurveGenusTwo.Filtration

-- Raw cone contraction helpers, rebuilt from the verified RawConeHelpers source.

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace CurveGenusTwo.Filtration.RawCone
universe u

private lemma hom_sum {A B : AddCommGrpCat.{u}} {ι : Type*} (s : Finset ι)
    (f : ι → (A ⟶ B)) : (∑ i ∈ s, f i).hom = ∑ i ∈ s, (f i).hom :=
  map_sum AddCommGrpCat.homAddEquiv f s

noncomputable abbrev chains (X : TopCat.{u}) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (alternatingFaceMapComplex AddCommGrpCat).obj (TopCat.toSSet.obj X ⋙ AddCommGrpCat.free)

noncomputable def boundary (X : TopCat.{u}) (n : ℕ) :
    FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n + 1⦌) →+
      FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n⦌) :=
  ((chains X).d (n + 1) n).hom

lemma boundary_of (X : TopCat.{u}) (n : ℕ)
    (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) :
    boundary X n (.of s) = ∑ i : Fin (n + 2), (-1 : ℤ)^i.val •
      FreeAbelianGroup.of ((TopCat.toSSet.obj X).δ i s) := by
  simp [boundary, chains, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, SimplicialObject.δ, AddCommGrpCat.free, hom_sum]

lemma boundary_eq {V : Type u} [LinearOrder V] (K : FiniteComplex V) (n : ℕ) :
    boundary (TopCat.of (geometricRealization K)) n = singularGeneratorBoundary K n := by
  ext s
  rw [boundary_of, singularGeneratorBoundary_of]

noncomputable def constSimplex (X : TopCat.{u}) (x : X) (n : ℕ) :
    (TopCat.toSSet.obj X) _⦋n⦌ :=
  (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).symm (.const _ x)

lemma constSimplex_face (X : TopCat.{u}) (x : X) (n : ℕ) (i : Fin (n+2)) :
    (TopCat.toSSet.obj X).δ i (constSimplex X x (n+1)) = constSimplex X x n := by
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext t
  rfl

noncomputable def aug {A : Type u} : FreeAbelianGroup A →+ ℤ :=
  FreeAbelianGroup.lift (fun _ => 1)

lemma boundary_const (X : TopCat.{u}) (x : X) (n : ℕ) :
    boundary X n (.of (constSimplex X x (n+1))) =
      (∑ i : Fin (n+2), (-1 : ℤ)^i.val) • FreeAbelianGroup.of (constSimplex X x n) := by
  rw [boundary_of]
  simp only [constSimplex_face, Finset.sum_smul]

lemma aug_boundary (X : TopCat.{u}) (n : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n+1⦌)) :
    aug (boundary X n z) = (∑ i : Fin (n+2), (-1 : ℤ)^i.val) * aug z := by
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of s => simp [boundary_of, map_sum, map_zsmul, aug]
  | neg z hz => simp only [map_neg, mul_neg, hz]
  | add z w hz hw => simp only [map_add, mul_add, hz, hw]

noncomputable def chainMap {X Y : TopCat.{u}} (f : X ⟶ Y) : chains X ⟶ chains Y :=
  (alternatingFaceMapComplex AddCommGrpCat).map
    (Functor.whiskerRight (TopCat.toSSet.map f) AddCommGrpCat.free)

lemma chainMap_const (X : TopCat.{u}) (x : X) (n : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n⦌)) :
    ((chainMap (TopCat.const (X := X) x)).f n).hom z =
      aug z • FreeAbelianGroup.of (constSimplex X x n) := by
  change (FreeAbelianGroup.map ((TopCat.toSSet.map (TopCat.const (X := X) x)).app (.op ⦋n⦌))) z = _
  induction z using FreeAbelianGroup.induction_on with
  | zero => simp
  | of s => rfl
  | neg z hz => simp only [map_neg, hz, neg_smul]
  | add z w hz hw => simp only [map_add, hz, hw, add_smul]

noncomputable def chainHomotopy {X Y : TopCat.{u}} {f g : X ⟶ Y}
    (H : TopCat.Homotopy f g) : Homotopy (chainMap f) (chainMap g) :=
  (H.toSSet.toSimplicialObjectHomotopy.whiskerRight AddCommGrpCat.free).toChainHomotopy

lemma constant_cycle_bounds (X : TopCat.{u}) (x : X) (n : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n+1⦌))
    (hz : boundary X n z = 0) :
    ∃ c, boundary X (n+1) c = aug z • FreeAbelianGroup.of (constSimplex X x (n+1)) := by
  have ha := aug_boundary X n z
  rw [hz, map_zero, Fin.sum_neg_one_pow] at ha
  by_cases he : Even (n+2)
  · refine ⟨aug z • FreeAbelianGroup.of (constSimplex X x (n+2)), ?_⟩
    rw [map_zsmul, boundary_const, Fin.sum_neg_one_pow]
    have ho : ¬ Even (n+1+2) := by simpa only [show n+1+2 = (n+2)+1 by omega,
      Nat.even_add_one, not_not] using he
    simp [ho]
  · have haz : aug z = 0 := by simpa [he] using ha.symm
    exact ⟨0, by simp [haz]⟩

lemma cycles_bound_of_contraction (X : TopCat.{u}) (x : X)
    (H : TopCat.Homotopy (𝟙 X) (TopCat.const (X := X) x))
    (n : ℕ) (z : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n+1⦌))
    (hz : boundary X n z = 0) : ∃ c, boundary X (n+1) c = z := by
  let h := chainHomotopy H
  let q (i j : ℕ) : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋i⦌) →+
      FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋j⦌) := (h.hom i j).hom
  have hc := h.comm (n+1)
  rw [dNext_eq h.hom (show (ComplexShape.down ℕ).Rel (n+1) n from rfl),
      prevD_eq h.hom (show (ComplexShape.down ℕ).Rel (n+2) (n+1) from rfl)] at hc
  have he := congrArg (fun f => AddCommGrpCat.Hom.hom f z) hc
  obtain ⟨c, hc⟩ := constant_cycle_bounds X x n z hz
  refine ⟨q (n+1) (n+2) z + c, ?_⟩
  let r : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n+1⦌) →+
      FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n+1⦌) :=
    ((chainMap (TopCat.const (X := X) x)).f (n+1)).hom
  have hr : r z = aug z • FreeAbelianGroup.of (constSimplex X x (n+1)) :=
    chainMap_const X x (n+1) z
  change (FreeAbelianGroup.map id) z = q n (n+1) (boundary X n z) +
    boundary X (n+1) (q (n+1) (n+2) z) + r z at he
  rw [hr] at he
  rw [hz, map_zero, zero_add] at he
  simp only [FreeAbelianGroup.map_id] at he
  rw [map_add, hc]
  exact he.symm
end CurveGenusTwo.Filtration.RawCone

namespace CurveGenusTwo.Filtration.RawCone
universe u

theorem augmentation_zero_bounds_of_contraction (X : TopCat.{u}) (x : X)
    (H : TopCat.Homotopy (𝟙 X) (TopCat.const (X := X) x))
    (z : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋0⦌)) (hz : aug z = 0) :
    ∃ c, boundary X 0 c = z := by
  let h := chainHomotopy H
  have hc := h.comm 0
  rw [dNext_eq_zero h.hom 0 (by simp),
    prevD_eq h.hom (show (ComplexShape.down ℕ).Rel 1 0 from rfl)] at hc
  have he := congrArg (fun f => AddCommGrpCat.Hom.hom f z) hc
  let q : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋0⦌) →+
      FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋1⦌) := (h.hom 0 1).hom
  let r : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋0⦌) →+
      FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋0⦌) :=
    ((chainMap (TopCat.const (X := X) x)).f 0).hom
  have hr : r z = aug z • FreeAbelianGroup.of (constSimplex X x 0) := chainMap_const X x 0 z
  refine ⟨q z, ?_⟩
  change (FreeAbelianGroup.map id) z = 0 + boundary X 0 (q z) + r z at he
  rw [hr, hz, zero_smul, add_zero, zero_add, FreeAbelianGroup.map_id] at he
  exact he.symm

noncomputable def push {X Y : TopCat.{u}} (j : X ⟶ Y) (n : ℕ) :
    FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n⦌) →+
      FreeAbelianGroup ((TopCat.toSSet.obj Y) _⦋n⦌) :=
  ((chainMap j).f n).hom

theorem push_boundary {X Y : TopCat.{u}} (j : X ⟶ Y) (n : ℕ)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n+1⦌)) :
    boundary Y n (push j (n+1) c) = push j n (boundary X n c) := by
  exact congrArg (fun f => f.hom c) ((chainMap j).comm (n+1) n)

theorem freeAbelianGroup_map_injective {α β : Type u} (f : α → β)
    (hf : Function.Injective f) : Function.Injective (FreeAbelianGroup.map f) := by
  classical
  let r : FreeAbelianGroup β →+ FreeAbelianGroup α := FreeAbelianGroup.lift fun b =>
    if hb : ∃ a, f a = b then FreeAbelianGroup.of hb.choose else 0
  have he : r.comp (FreeAbelianGroup.map f) = AddMonoidHom.id _ := by
    apply FreeAbelianGroup.lift_ext
    intro a
    simp only [AddMonoidHom.comp_apply, FreeAbelianGroup.map_of_apply,
      r, FreeAbelianGroup.lift_apply_of, AddMonoidHom.id_apply]
    rw [dif_pos (show ∃ a', f a' = f a from ⟨a, rfl⟩)]
    congr 1
    exact hf (Exists.choose_spec (show ∃ a', f a' = f a from ⟨a, rfl⟩))
  intro a b hab
  have hh := congrArg r hab
  simpa only [← AddMonoidHom.comp_apply, he, AddMonoidHom.id_apply] using hh

theorem push_injective {X Y : TopCat.{u}} (j : X ⟶ Y)
    (hj : Function.Injective j) (n : ℕ) : Function.Injective (push j n) := by
  apply freeAbelianGroup_map_injective
  intro a b hab
  apply (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).injective
  ext t
  apply hj
  exact congrArg (fun s => TopCat.toSSetObjEquiv Y (.op ⦋n⦌) s t) hab

theorem push_aug {X Y : TopCat.{u}} (j : X ⟶ Y) (n : ℕ)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj X) _⦋n⦌)) :
    aug (push j n c) = aug c := by
  have h : aug.comp (push j n) = aug := by
    apply FreeAbelianGroup.lift_ext
    intro s
    rfl
  exact DFunLike.congr_fun h c

end CurveGenusTwo.Filtration.RawCone

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

noncomputable def carrierRawInclusion (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (n : ℕ) :=
  RawCone.push (TopCat.ofHom (carrierRealizationInclusion K S)) n

theorem carrierRawInclusion_boundary (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (n : ℕ)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj
      (TopCat.of (geometricRealization (realizationCarrier K S)))) _⦋n+1⦌)) :
    singularGeneratorBoundary K n (carrierRawInclusion K S (n+1) c) =
      carrierRawInclusion K S n (singularGeneratorBoundary (realizationCarrier K S) n c) := by
  simpa only [RawCone.boundary_eq, carrierRawInclusion] using
    RawCone.push_boundary (TopCat.ofHom (carrierRealizationInclusion K S)) n c

theorem carrierRawInclusion_injective (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (n : ℕ) :
    Function.Injective (carrierRawInclusion K S n) :=
  RawCone.push_injective _
    (finiteRealizationInclusion_isClosedEmbedding _ K (realizationCarrier_subcomplex K S)).injective n

theorem finiteRealization_cone_contraction (L : FiniteComplex V) (hL : IsNonemptyCone L) :
    ∃ x : geometricRealization L,
      Nonempty (TopCat.Homotopy (𝟙 (TopCat.of (geometricRealization L)))
        (TopCat.const (X := TopCat.of (geometricRealization L)) x)) := by
  classical
  obtain ⟨a, ha, hcone⟩ := hL
  let av : ActiveVertex L := ⟨a, ha⟩
  have hapex : CurveComplex.HasConeApex (geometricComplex L) av := by
    intro σ hσ
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    change (insert av σ).image (fun v : ActiveVertex L => v.val) ∈ L
    rw [Finset.image_insert]
    exact hcone _ hσ.2
  exact ⟨CurveComplex.coneVertex (geometricComplex L) av,
    ⟨CurveComplex.coneHomotopy (geometricComplex L) av hapex⟩⟩

theorem exists_carried_raw_positive_filling (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (hS : S.Nonempty) (v : ActiveVertex K)
    (hstar : S ⊆ CurveComplex.openVertexStar (geometricComplex K) v)
    (n : ℕ)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n+1⦌))
    (hz : singularGeneratorBoundary K n z = 0)
    (hcar : z ∈ (carrierRawInclusion K S (n+1)).range) :
    ∃ b : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n+2⦌),
      b ∈ (carrierRawInclusion K S (n+2)).range ∧ singularGeneratorBoundary K (n+1) b = z := by
  obtain ⟨a, ha⟩ := hcar
  have hacycle : RawCone.boundary (TopCat.of (geometricRealization (realizationCarrier K S))) n a = 0 := by
    rw [RawCone.boundary_eq]
    apply carrierRawInclusion_injective K S n
    rw [← carrierRawInclusion_boundary, ha, hz, map_zero]
  obtain ⟨x, ⟨H⟩⟩ := finiteRealization_cone_contraction (realizationCarrier K S)
    (realizationCarrier_isNonemptyCone K S hS v hstar)
  obtain ⟨b, hb⟩ := RawCone.cycles_bound_of_contraction _ x H n a hacycle
  refine ⟨carrierRawInclusion K S (n+2) b, ⟨b, rfl⟩, ?_⟩
  rw [carrierRawInclusion_boundary, ← RawCone.boundary_eq, hb, ha]

theorem exists_carried_raw_zero_filling (K : FiniteComplex V)
    (S : Set (geometricRealization K)) (hS : S.Nonempty) (v : ActiveVertex K)
    (hstar : S ⊆ CurveComplex.openVertexStar (geometricComplex K) v)
    (z : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋0⦌))
    (hz : RawCone.aug z = 0) (hcar : z ∈ (carrierRawInclusion K S 0).range) :
    ∃ b : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋1⦌),
      b ∈ (carrierRawInclusion K S 1).range ∧ singularGeneratorBoundary K 0 b = z := by
  obtain ⟨a, ha⟩ := hcar
  have haaug : RawCone.aug a = 0 := by
    rw [← RawCone.push_aug (TopCat.ofHom (carrierRealizationInclusion K S)) 0]
    change RawCone.aug (carrierRawInclusion K S 0 a) = 0
    rw [ha, hz]
  obtain ⟨x, ⟨H⟩⟩ := finiteRealization_cone_contraction (realizationCarrier K S)
    (realizationCarrier_isNonemptyCone K S hS v hstar)
  obtain ⟨b, hb⟩ := RawCone.augmentation_zero_bounds_of_contraction _ x H a haaug
  refine ⟨carrierRawInclusion K S 1 b, ⟨b, rfl⟩, ?_⟩
  rw [carrierRawInclusion_boundary, ← RawCone.boundary_eq, hb, ha]

theorem raw_generator_mem_carrier (K : FiniteComplex V) (n : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n⦌) :
    FreeAbelianGroup.of s ∈ (carrierRawInclusion K (singularSimplexImage K n s) n).range := by
  obtain ⟨t, ht⟩ := singularSimplex_lifts_to_realizationCarrier K n s
  let a := (TopCat.toSSetObjEquiv
    (TopCat.of (geometricRealization (realizationCarrier K (singularSimplexImage K n s))))
    (.op ⦋n⦌)).symm t
  refine ⟨FreeAbelianGroup.of a, ?_⟩
  change FreeAbelianGroup.of ((TopCat.toSSet.map
    (TopCat.ofHom (carrierRealizationInclusion K (singularSimplexImage K n s)))).app (.op ⦋n⦌) a) = _
  congr 1
  apply (TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K)) (.op ⦋n⦌)).injective
  exact ht

#print axioms exists_carried_raw_positive_filling
#print axioms exists_carried_raw_zero_filling
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]
open CurveComplex

theorem mem_range_finiteRealizationInclusion (L K : FiniteComplex V)
    (hLK : L.simplices ⊆ K.simplices) (x : geometricRealization K)
    (hτ : (CurveComplex.supportFinset (geometricComplex K) x).image Subtype.val ∈ L) :
    x ∈ Set.range (finiteRealizationInclusion L K hLK) := by
  classical
  letI : DecidableEq (ActiveVertex K) := activeVertexDecidableEq K
  letI : DecidableEq (ActiveVertex L) := activeVertexDecidableEq L
  let τ := CurveComplex.supportFinset (geometricComplex K) x
  let g : τ → ActiveVertex L := fun w =>
    ⟨w.1.1, L.down_closed
      (Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨w.1, w.2, rfl⟩)) hτ⟩
  let σ := Finset.univ.image g
  have hσimage : σ.image (activeVertexInclusion _ K hLK) = τ := by
    ext v
    simp only [σ, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, ⟨a, rfl⟩, he⟩
      have hav : a.1 = v := Subtype.ext (congrArg Subtype.val he)
      exact hav ▸ a.2
    · intro hv
      exact ⟨g ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
  have hσface : σ ∈ (geometricComplex L).faces := by
    refine ⟨?_, ?_⟩
    · have ht : τ.Nonempty := supportFinset_nonempty (geometricComplex K) x
      rw [← hσimage] at ht
      exact Finset.image_nonempty.mp ht
    · have he : σ.image Subtype.val = τ.image Subtype.val := by
        ext v
        constructor
        · intro hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          refine Finset.mem_image.mpr ⟨activeVertexInclusion _ K hLK w, ?_, rfl⟩
          rw [← hσimage]
          exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
        · intro hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
          rw [← hσimage] at hw
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
          exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
      rw [he]
      exact hτ
  apply CarrierEmbedding.mem_range_mapPoint_of_support _ _ _
    (activeVertexInclusion_faces _ K hLK) x σ hσface
  rw [hσimage]


end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]
open CurveComplex

theorem finiteRealizationInclusion_support (L K : FiniteComplex V)
    (hLK : L.simplices ⊆ K.simplices) (x : geometricRealization L) :
    (supportFinset (geometricComplex K) (finiteRealizationInclusion L K hLK x)).image Subtype.val ∈ L := by
  classical
  letI : DecidableEq (ActiveVertex K) := activeVertexDecidableEq K
  letI : DecidableEq (ActiveVertex L) := activeVertexDecidableEq L
  have he : (supportFinset (geometricComplex K) (finiteRealizationInclusion L K hLK x)).image Subtype.val =
      (supportFinset (geometricComplex L) x).image Subtype.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have hwpos := (mem_supportFinset_iff_pos (geometricComplex K) _ w).mp hw
      have hr : w ∈ Set.range (activeVertexInclusion L K hLK) := by
        by_contra hn
        have hz := CarrierEmbedding.mapPoint_weight_outside _ _ _ (activeVertexInclusion_faces L K hLK) x w hn
        change (finiteRealizationInclusion L K hLK x).weight w = 0 at hz
        linarith
      obtain ⟨a, rfl⟩ := hr
      change 0 < (finiteRealizationInclusion L K hLK x).weight ⟨a.1, hLK a.2⟩ at hwpos
      rw [finiteRealizationInclusion_weight] at hwpos
      exact Finset.mem_image.mpr ⟨a, (mem_supportFinset_iff_pos _ _ a).mpr hwpos, rfl⟩
    · intro hv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      refine Finset.mem_image.mpr ⟨activeVertexInclusion L K hLK a, ?_, rfl⟩
      apply (mem_supportFinset_iff_pos _ _ _).mpr
      change 0 < (finiteRealizationInclusion L K hLK x).weight ⟨a.1, hLK a.2⟩
      rw [finiteRealizationInclusion_weight]
      exact (mem_supportFinset_iff_pos _ _ a).mp ha
  rw [he]
  exact (supportFinset_mem_faces (geometricComplex L) x).2

theorem finiteRealizationInclusion_range_mono (L M K : FiniteComplex V)
    (hLM : L.simplices ⊆ M.simplices) (hLK : L.simplices ⊆ K.simplices)
    (hMK : M.simplices ⊆ K.simplices) :
    Set.range (finiteRealizationInclusion L K hLK) ⊆
      Set.range (finiteRealizationInclusion M K hMK) := by
  rintro x ⟨a, rfl⟩
  apply mem_range_finiteRealizationInclusion M K hMK
  exact hLM (finiteRealizationInclusion_support L K hLK a)

end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration.RawCone
universe u

theorem generator_mem_push_range {X Y : TopCat.{u}} (j : X ⟶ Y)
    (hj : Topology.IsEmbedding j) (n : ℕ)
    (s : (TopCat.toSSet.obj Y) _⦋n⦌)
    (hs : Set.range (TopCat.toSSetObjEquiv Y (.op ⦋n⦌) s) ⊆ Set.range j) :
    FreeAbelianGroup.of s ∈ (push j n).range := by
  classical
  let f := TopCat.toSSetObjEquiv Y (.op ⦋n⦌) s
  have hr (x : StdSimplex ℝ (Fin (n+1))) : ∃ y, j y = f x := hs ⟨x, rfl⟩
  choose t ht using hr
  have hcont : Continuous t := by
    apply hj.continuous_iff.mpr
    have he : j ∘ t = f := funext ht
    rw [he]
    exact f.continuous
  let a := (TopCat.toSSetObjEquiv X (.op ⦋n⦌)).symm ⟨t, hcont⟩
  refine ⟨FreeAbelianGroup.of a, ?_⟩
  change FreeAbelianGroup.of ((TopCat.toSSet.map j).app (.op ⦋n⦌) a) = _
  congr 1
  apply (TopCat.toSSetObjEquiv Y (.op ⦋n⦌)).injective
  exact ContinuousMap.ext ht

theorem push_range_mono {X Y Z : TopCat.{u}} (j : X ⟶ Z) (k : Y ⟶ Z)
    (hk : Topology.IsEmbedding k) (hjk : Set.range j ⊆ Set.range k) (n : ℕ) :
    (push j n).range ≤ (push k n).range := by
  rintro c ⟨a, rfl⟩
  induction a using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]; exact AddSubgroup.zero_mem _
  | neg a ha => simpa only [map_neg] using AddSubgroup.neg_mem _ ha
  | add a b ha hb => simpa only [map_add] using AddSubgroup.add_mem _ ha hb
  | of s =>
    apply generator_mem_push_range k hk n
    rintro x ⟨t, rfl⟩
    apply hjk
    exact ⟨TopCat.toSSetObjEquiv X (.op ⦋n⦌) s t, rfl⟩
end CurveGenusTwo.Filtration.RawCone

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

theorem carrierRawInclusion_range_mono (K : FiniteComplex V)
    {S T : Set (geometricRealization K)} (hST : S ⊆ T) (n : ℕ) :
    (carrierRawInclusion K S n).range ≤ (carrierRawInclusion K T n).range :=
  RawCone.push_range_mono _ _
    (finiteRealizationInclusion_isClosedEmbedding _ K (realizationCarrier_subcomplex K T)).isEmbedding
    (finiteRealizationInclusion_range_mono _ _ K (realizationCarrier_mono K hST)
      (realizationCarrier_subcomplex K S) (realizationCarrier_subcomplex K T)) n

end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]
open CurveComplex

theorem simplexAtSingular_support_subset (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) (t : StdSimplex ℝ (Fin (n+1))) :
    (supportFinset (geometricComplex K)
      (TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K)) (.op ⦋n⦌)
        (simplexAtSingular K n σ) t)).image Subtype.val ⊆ σ.1 := by
  classical
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  have hcard : σ.1.card = n+1 := by rcases σ.2.2 with h | h <;> omega
  have hnonempty : σ.1.Nonempty := Finset.card_pos.mp (by omega)
  have hnz := (mem_supportFinset_iff (geometricComplex K) _ w).mp hw
  by_contra hnot
  apply hnz
  have hout := affineSingular_weight_outside (activeFace K σ.1 σ.2.1)
    (activeFace_mem_geometricComplex K σ.1 σ.2.1 hnonempty)
    ((activeFace_card K σ.1 σ.2.1).trans hcard) t w
    (by simpa only [mem_activeFace_iff] using hnot)
  exact hout

theorem simplicialToSingular_carried (L K : FiniteComplex V)
    (hLK : L.simplices ⊆ K.simplices) (n : ℕ) (c : chains L (n:ℤ)) :
    simplicialToSingularGenerators K n (chainInclusion L K hLK (n:ℤ) c) ∈
      (RawCone.push (TopCat.ofHom (finiteRealizationInclusion L K hLK)) n).range := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]; exact AddSubgroup.zero_mem _
  | neg c hc => simpa only [map_neg] using AddSubgroup.neg_mem _ hc
  | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
  | of σ =>
    change FreeAbelianGroup.of (simplexAtSingular K n ⟨σ.1, hLK σ.2.1, σ.2.2⟩) ∈ _
    apply RawCone.generator_mem_push_range _
      (finiteRealizationInclusion_isClosedEmbedding L K hLK).isEmbedding n
    rintro x ⟨t, rfl⟩
    apply mem_range_finiteRealizationInclusion L K hLK
    exact L.down_closed (simplexAtSingular_support_subset K n _ t) σ.2.1

theorem normalizedApproximation_realization_carried (K : FiniteComplex V) (n : ℕ)
    (s : StarSmallSimplex K n) :
    simplicialToSingularGenerators K n (normalizedStarSmallApproximation K n (FreeAbelianGroup.of s)) ∈
      (carrierRawInclusion K (singularSimplexImage K n s.1) n).range := by
  obtain ⟨c, hc⟩ := normalizedStarSmallApproximation_carried K n s
  rw [← hc]
  exact simplicialToSingular_carried _ K (realizationCarrier_subcomplex K _) n c

end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

noncomputable def normalizedComparisonDefect (K : FiniteComplex V) (n : ℕ) :=
  starSmallChainInclusion K n -
    (simplicialToSingularGenerators K n).comp (normalizedStarSmallApproximation K n)

theorem normalizedComparisonDefect_boundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n+1))) :
    singularGeneratorBoundary K n (normalizedComparisonDefect K (n+1) c) =
      normalizedComparisonDefect K n (starSmallBoundary K n c) := by
  simp only [normalizedComparisonDefect, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, map_sub]
  rw [← starSmallChainInclusion_boundary, ← simplicialToSingular_boundary,
    normalizedStarSmallApproximation_boundary]

theorem normalizedComparisonDefect_carried (K : FiniteComplex V) (n : ℕ)
    (s : StarSmallSimplex K n) :
    normalizedComparisonDefect K n (FreeAbelianGroup.of s) ∈
      (carrierRawInclusion K (singularSimplexImage K n s.1) n).range := by
  apply AddSubgroup.sub_mem
  · exact raw_generator_mem_carrier K n s.1
  · exact normalizedApproximation_realization_carried K n s

theorem normalizedComparisonDefect_zero_aug (K : FiniteComplex V)
    (s : StarSmallSimplex K 0) :
    RawCone.aug (normalizedComparisonDefect K 0 (FreeAbelianGroup.of s)) = 0 := by
  obtain ⟨v, hv⟩ := normalizedStarSmallApproximation_zero K s
  simp only [normalizedComparisonDefect, AddMonoidHom.sub_apply,
    AddMonoidHom.comp_apply, hv, simplicialToSingularGenerators_of, map_sub]
  change RawCone.aug (FreeAbelianGroup.of s.1) - RawCone.aug (FreeAbelianGroup.of _) = 0
  simp [RawCone.aug]

theorem exists_normalizedComparisonHomotopy_zero (K : FiniteComplex V) :
    ∃ H : FreeAbelianGroup (StarSmallSimplex K 0) →+
        FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋1⦌),
      (∀ c, singularGeneratorBoundary K 0 (H c) = normalizedComparisonDefect K 0 c) ∧
      (∀ s : StarSmallSimplex K 0, H (FreeAbelianGroup.of s) ∈
        (carrierRawInclusion K (singularSimplexImage K 0 s.1) 1).range) := by
  classical
  have fill (s : StarSmallSimplex K 0) :
      ∃ b : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋1⦌),
        b ∈ (carrierRawInclusion K (singularSimplexImage K 0 s.1) 1).range ∧
        singularGeneratorBoundary K 0 b = normalizedComparisonDefect K 0 (FreeAbelianGroup.of s) := by
    obtain ⟨v, hv⟩ := s.2
    apply exists_carried_raw_zero_filling K _ _ v hv
    · exact normalizedComparisonDefect_zero_aug K s
    · exact normalizedComparisonDefect_carried K 0 s
    · exact ⟨(TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K))
        (.op ⦋0⦌) s.1) (.single 0), ⟨.single 0, rfl⟩⟩
  choose b hb hd using fill
  let H := FreeAbelianGroup.lift b
  refine ⟨H, ?_, ?_⟩
  · have he : (singularGeneratorBoundary K 0).comp H = normalizedComparisonDefect K 0 := by
      apply FreeAbelianGroup.lift_ext
      intro s
      simpa only [H, FreeAbelianGroup.lift_apply_of, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply] using hd s
    exact fun c => DFunLike.congr_fun he c
  · intro s
    simpa only [H, FreeAbelianGroup.lift_apply_of] using hb s

structure NormalizedComparisonHomotopyStage (K : FiniteComplex V) (n : ℕ) where
  map : FreeAbelianGroup (StarSmallSimplex K n) →+
    FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n+1⦌)
  carried : ∀ s : StarSmallSimplex K n, map (FreeAbelianGroup.of s) ∈
    (carrierRawInclusion K (singularSimplexImage K n s.1) (n+1)).range
  cycle : ∀ c : FreeAbelianGroup (StarSmallSimplex K (n+1)),
    singularGeneratorBoundary K n (normalizedComparisonDefect K (n+1) c - map (starSmallBoundary K n c)) = 0

noncomputable def normalizedComparisonHomotopyZero (K : FiniteComplex V) :
    NormalizedComparisonHomotopyStage K 0 where
  map := (exists_normalizedComparisonHomotopy_zero K).choose
  carried := (exists_normalizedComparisonHomotopy_zero K).choose_spec.2
  cycle := by
    intro c
    rw [map_sub, (exists_normalizedComparisonHomotopy_zero K).choose_spec.1,
      normalizedComparisonDefect_boundary, sub_self]

theorem exists_normalizedComparisonHomotopy_next (K : FiniteComplex V) (n : ℕ)
    (a : NormalizedComparisonHomotopyStage K n) :
    ∃ H : FreeAbelianGroup (StarSmallSimplex K (n+1)) →+
        FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n+2⦌),
      (∀ c, singularGeneratorBoundary K (n+1) (H c) =
        normalizedComparisonDefect K (n+1) c - a.map (starSmallBoundary K n c)) ∧
      (∀ s : StarSmallSimplex K (n+1), H (FreeAbelianGroup.of s) ∈
        (carrierRawInclusion K (singularSimplexImage K (n+1) s.1) (n+2)).range) := by
  classical
  have fill (s : StarSmallSimplex K (n+1)) :
      ∃ b : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋n+2⦌),
        b ∈ (carrierRawInclusion K (singularSimplexImage K (n+1) s.1) (n+2)).range ∧
        singularGeneratorBoundary K (n+1) b = normalizedComparisonDefect K (n+1) (FreeAbelianGroup.of s) -
          a.map (starSmallBoundary K n (FreeAbelianGroup.of s)) := by
    obtain ⟨v, hv⟩ := s.2
    apply exists_carried_raw_positive_filling K _ _ v hv n
    · exact a.cycle _
    · apply AddSubgroup.sub_mem
      · exact normalizedComparisonDefect_carried K (n+1) s
      · rw [starSmallBoundary_of, map_sum]
        apply AddSubgroup.sum_mem
        intro i hi
        rw [map_zsmul]
        apply AddSubgroup.zsmul_mem
        apply carrierRawInclusion_range_mono K (singularSimplexImage_face_subset K n s.1 i)
        exact a.carried (starSmallFace K n i s)
    · exact ⟨(TopCat.toSSetObjEquiv (TopCat.of (geometricRealization K))
        (.op ⦋n+1⦌) s.1) (.single 0), ⟨.single 0, rfl⟩⟩
  choose b hb hd using fill
  let H := FreeAbelianGroup.lift b
  refine ⟨H, ?_, ?_⟩
  · have he : (singularGeneratorBoundary K (n+1)).comp H =
        normalizedComparisonDefect K (n+1) - a.map.comp (starSmallBoundary K n) := by
      apply FreeAbelianGroup.lift_ext
      intro s
      simpa only [H, FreeAbelianGroup.lift_apply_of, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply] using hd s
    exact fun c => DFunLike.congr_fun he c
  · intro s
    simpa only [H, FreeAbelianGroup.lift_apply_of] using hb s

noncomputable def normalizedComparisonHomotopyNext (K : FiniteComplex V) (n : ℕ)
    (a : NormalizedComparisonHomotopyStage K n) : NormalizedComparisonHomotopyStage K (n+1) where
  map := (exists_normalizedComparisonHomotopy_next K n a).choose
  carried := (exists_normalizedComparisonHomotopy_next K n a).choose_spec.2
  cycle := by
    intro c
    rw [map_sub, (exists_normalizedComparisonHomotopy_next K n a).choose_spec.1,
      starSmallBoundary_squared, map_zero, sub_zero, normalizedComparisonDefect_boundary, sub_self]

noncomputable def normalizedComparisonHomotopyStage (K : FiniteComplex V) :
    (n : ℕ) → NormalizedComparisonHomotopyStage K n :=
  Nat.rec (normalizedComparisonHomotopyZero K) (fun n a => normalizedComparisonHomotopyNext K n a)

noncomputable def normalizedComparisonHomotopy (K : FiniteComplex V) (n : ℕ) :=
  (normalizedComparisonHomotopyStage K n).map

theorem normalizedComparisonHomotopy_boundary (K : FiniteComplex V) (n : ℕ)
    (c : FreeAbelianGroup (StarSmallSimplex K (n+1))) :
    singularGeneratorBoundary K (n+1) (normalizedComparisonHomotopy K (n+1) c) +
      normalizedComparisonHomotopy K n (starSmallBoundary K n c) =
        normalizedComparisonDefect K (n+1) c := by
  have h := (exists_normalizedComparisonHomotopy_next K n (normalizedComparisonHomotopyStage K n)).choose_spec.1 c
  change singularGeneratorBoundary K (n+1) (normalizedComparisonHomotopy K (n+1) c) =
    normalizedComparisonDefect K (n+1) c - normalizedComparisonHomotopy K n (starSmallBoundary K n c) at h
  rw [h, sub_add_cancel]

#print axioms normalizedComparisonHomotopy_boundary
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

noncomputable def normalizedStarSmallCyclesMap (K : FiniteComplex V) (n : ℕ) :
    (starSmallBoundary K n).ker →+ cycles K ((n+1:ℕ):ℤ) :=
  ((normalizedStarSmallApproximation K (n+1)).comp (starSmallBoundary K n).ker.subtype).codRestrict
    (cycles K ((n+1:ℕ):ℤ)) (by
      intro c
      change boundary K ((n+1:ℕ):ℤ) (normalizedStarSmallApproximation K (n+1) c.1) = 0
      apply (positiveBoundary_eq_zero_iff K n _).mp
      rw [normalizedStarSmallApproximation_boundary,
        show starSmallBoundary K n c.1 = 0 from c.2, map_zero])

theorem normalizedStarSmallCyclesMap_realization (K : FiniteComplex V) (n : ℕ)
    (a : (starSmallBoundary K n).ker) :
    starSmallChainInclusion K (n+1) a.1 -
      (positiveCyclesMap K n (normalizedStarSmallCyclesMap K n a)).1 ∈
        singularPositiveBoundaries K n := by
  refine ⟨normalizedComparisonHomotopy K (n+1) a.1, ?_⟩
  have h := normalizedComparisonHomotopy_boundary K n a.1
  rw [show starSmallBoundary K n a.1 = 0 from a.2, map_zero, add_zero] at h
  exact h

end CurveGenusTwo.Filtration
namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

/-- Producer A in universe zero, from the normalized actual carrier homotopy. -/
theorem singularPositiveCycle_lift_mod_boundaries_universe_zero :
    ∀ (K : FiniteComplex V) (n : ℕ) (z : singularPositiveCycles K n),
      ∃ c : cycles K ((n+1:ℕ):ℤ),
        z.1 - (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n := by
  intro K n
  apply (singularPositiveCycle_lift_iff_starSmall K n).mpr
  intro a ha
  exact ⟨normalizedStarSmallCyclesMap K n ⟨a, ha⟩,
    normalizedStarSmallCyclesMap_realization K n ⟨a, ha⟩⟩

#print axioms normalizedStarSmallCyclesMap_realization
#print axioms singularPositiveCycle_lift_mod_boundaries_universe_zero
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz

theorem barycentricFlag_first_weight_pos (n : ℕ) (π : Equiv.Perm (Fin (n+1)))
    (t : StdSimplex ℝ (Fin (n+1))) :
    0 < (barycentricFlag n π t).weights (π 0) := by
  classical
  let S (k : Fin (n+1)) := Finset.univ.filter (fun i => π.symm i ≤ k)
  have hS (k : Fin (n+1)) : (S k).Nonempty := by
    refine ⟨π 0, ?_⟩
    simp [S]
  change 0 < (StdSimplex.iConvexComb t (fun k => StdSimplex.subBarycenter (S k) (hS k))).weights (π 0)
  rw [StdSimplex.weights_iConvexComb, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  have hp (k : Fin (n+1)) : 0 < (StdSimplex.subBarycenter (K := ℝ) (S k) (hS k)).weights (π 0) := by
    have hmem : π 0 ∈ S k := by simp [S]
    simp only [StdSimplex.weights_subBarycenter, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single (π 0)]
    · simp only [ite_true]
      exact inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr (hS k)))
    · intro b hb hne
      simp [hne]
    · exact fun hn => False.elim (hn hmem)
  have ht : ∑ j : Fin (n+1), t.weights j = 1 := by
    have ht := t.total
    rw [Finsupp.sum_fintype _ _ (by simp)] at ht
    exact ht
  have hex : ∃ j, 0 < t.weights j := by
    by_contra hn
    push_neg at hn
    have hz (j) : t.weights j = 0 := le_antisymm (hn j) (t.weights_nonneg j)
    simp only [hz, Finset.sum_const_zero] at ht
    norm_num at ht
  obtain ⟨j, hjpos⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (t.weights_nonneg j) (le_of_lt (hp j)))
    ⟨j, Finset.mem_univ _, mul_pos hjpos (hp j)⟩

variable {V : Type} [LinearOrder V]

theorem affine_barycentricFlag_starSmall (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) (π : Equiv.Perm (Fin (n+1))) :
    ∃ v : ActiveVertex K, singularSimplexImage K n
      (barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ)) ⊆
        CurveComplex.openVertexStar (geometricComplex K) v := by
  have hcard : σ.1.card = n+1 := by rcases σ.2.2 with h | h <;> omega
  have hnonempty : σ.1.Nonempty := Finset.card_pos.mp (by omega)
  let τ := activeFace K σ.1 σ.2.1
  have hτcard : τ.card = n+1 := (activeFace_card K σ.1 σ.2.1).trans hcard
  refine ⟨τ.orderEmbOfFin hτcard (π 0), ?_⟩
  rintro x ⟨t, rfl⟩
  change 0 < (CurveComplex.affineSingular τ
    (activeFace_mem_geometricComplex K σ.1 σ.2.1 hnonempty) hτcard
      (barycentricFlag n π t)).weight (τ.orderEmbOfFin hτcard (π 0))
  rw [CurveComplex.affineSingular_weight_ordered]
  exact barycentricFlag_first_weight_pos n π t

theorem rawSingularSubdivision_affine_starSmall (K : FiniteComplex V) (n : ℕ)
    (c : chains K (n:ℤ)) :
    rawSingularSubdivision K n (simplicialToSingularGenerators K n c) ∈
      (starSmallChainInclusion K n).range := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero]; exact AddSubgroup.zero_mem _
  | neg c hc => simpa only [map_neg] using AddSubgroup.neg_mem _ hc
  | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
  | of σ =>
    simp only [simplicialToSingularGenerators_of, rawSingularSubdivision, AddMonoidHom.comp_apply,
      FreeAbelianGroup.toFinsupp_of, LinearMap.toAddMonoidHom_coe, singularBarycentricFinsupp_single,
      map_sum, map_zsmul, Finsupp.toFreeAbelianGroup_single, one_smul]
    apply AddSubgroup.sum_mem
    intro π hπ
    apply AddSubgroup.zsmul_mem
    exact ⟨FreeAbelianGroup.of ⟨_, affine_barycentricFlag_starSmall K n σ π⟩, rfl⟩

end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz
variable {V : Type} [LinearOrder V]

noncomputable def affineSmallSubdivision (K : FiniteComplex V) (n : ℕ) :
    chains K (n:ℤ) →+ FreeAbelianGroup (StarSmallSimplex K n) :=
  FreeAbelianGroup.lift fun σ => ∑ π : Equiv.Perm (Fin (n+1)),
    (π.sign : ℤ) • FreeAbelianGroup.of
      ⟨barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ),
        affine_barycentricFlag_starSmall K n σ π⟩

theorem affineSmallSubdivision_inclusion (K : FiniteComplex V) (n : ℕ)
    (c : chains K (n:ℤ)) :
    starSmallChainInclusion K n (affineSmallSubdivision K n c) =
      rawSingularSubdivision K n (simplicialToSingularGenerators K n c) := by
  have he : (starSmallChainInclusion K n).comp (affineSmallSubdivision K n) =
      (rawSingularSubdivision K n).comp (simplicialToSingularGenerators K n) := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    simp only [AddMonoidHom.comp_apply, affineSmallSubdivision, FreeAbelianGroup.lift_apply_of,
      simplicialToSingularGenerators_of, rawSingularSubdivision,
      FreeAbelianGroup.toFinsupp_of, LinearMap.toAddMonoidHom_coe, singularBarycentricFinsupp_single,
      map_sum, map_zsmul, Finsupp.toFreeAbelianGroup_single, one_smul,
      starSmallChainInclusion, FreeAbelianGroup.map_of_apply]
  exact DFunLike.congr_fun he c

theorem affineSmallSubdivision_boundary (K : FiniteComplex V) (n : ℕ)
    (c : chains K ((n+1:ℕ):ℤ)) :
    starSmallBoundary K n (affineSmallSubdivision K (n+1) c) =
      affineSmallSubdivision K n (positiveBoundary K n c) := by
  apply starSmallChainInclusion_injective K n
  rw [starSmallChainInclusion_boundary, affineSmallSubdivision_inclusion,
    rawSingularSubdivision_boundary, ← simplicialToSingular_boundary, affineSmallSubdivision_inclusion]

noncomputable def simplicialCarrierComposite (K : FiniteComplex V) (n : ℕ) :
    chains K (n:ℤ) →+ chains K (n:ℤ) :=
  (normalizedStarSmallApproximation K n).comp (affineSmallSubdivision K n)

theorem simplicialCarrierComposite_boundary (K : FiniteComplex V) (n : ℕ)
    (c : chains K ((n+1:ℕ):ℤ)) :
    positiveBoundary K n (simplicialCarrierComposite K (n+1) c) =
      simplicialCarrierComposite K n (positiveBoundary K n c) := by
  simp only [simplicialCarrierComposite, AddMonoidHom.comp_apply]
  rw [normalizedStarSmallApproximation_boundary, affineSmallSubdivision_boundary]

end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

/-- The full subcomplex consisting of the faces of one finite simplex. -/
def fullFaceComplex (σ : Finset V) : FiniteComplex V where
  simplices := {τ | τ ⊆ σ}
  down_closed := by intro τ υ hsub hτ; exact hsub.trans hτ

theorem fullFaceComplex_subcomplex (K : FiniteComplex V) (σ : Finset V) (hσ : σ ∈ K) :
    (fullFaceComplex σ).simplices ⊆ K.simplices :=
  fun _ hτ => K.down_closed hτ hσ

theorem fullFaceComplex_isNonemptyCone (σ : Finset V) (hne : σ.Nonempty) :
    IsNonemptyCone (fullFaceComplex σ) := by
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, Finset.singleton_subset_iff.mpr hv, ?_⟩
  intro τ hτ
  exact Finset.insert_subset hv hτ

theorem chainInclusion_range_mono_of_subcomplex (L M K : FiniteComplex V)
    (hLM : L.simplices ⊆ M.simplices) (hLK : L.simplices ⊆ K.simplices)
    (hMK : M.simplices ⊆ K.simplices) (q : ℤ) :
    (chainInclusion L K hLK q).range ≤ (chainInclusion M K hMK q).range := by
  have he : (chainInclusion M K hMK q).comp (chainInclusion L M hLM q) =
      chainInclusion L K hLK q := by
    apply FreeAbelianGroup.lift_ext
    intro s
    rfl
  rintro c ⟨a, rfl⟩
  exact ⟨chainInclusion L M hLM q a, DFunLike.congr_fun he a⟩

end CurveGenusTwo.Filtration
namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz
variable {V : Type} [LinearOrder V]

theorem affine_flag_carrier_in_fullFace (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) (π : Equiv.Perm (Fin (n+1))) :
    (realizationCarrier K (singularSimplexImage K n
      (barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ)))).simplices ⊆
      (fullFaceComplex σ.1).simplices := by
  rintro τ ⟨x, hx, hpos⟩
  obtain ⟨t, rfl⟩ := hx
  intro v hv
  obtain ⟨ha, hp⟩ := hpos v hv
  apply simplexAtSingular_support_subset K n σ (barycentricFlag n π t)
  apply Finset.mem_image.mpr
  refine ⟨⟨v, ha⟩, ?_, rfl⟩
  apply (CurveComplex.mem_supportFinset_iff_pos _ _ _).mpr
  exact hp

theorem affineSmallSubdivision_of (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) : affineSmallSubdivision K n (FreeAbelianGroup.of σ) =
      ∑ π : Equiv.Perm (Fin (n+1)), (π.sign : ℤ) • FreeAbelianGroup.of
        (⟨barycentricFlagSingular (TopCat.of (geometricRealization K)) n π (simplexAtSingular K n σ),
          affine_barycentricFlag_starSmall K n σ π⟩ : StarSmallSimplex K n) := by
  unfold affineSmallSubdivision
  rw [FreeAbelianGroup.lift_apply_of]

set_option maxHeartbeats 200000 in
theorem simplicialCarrierComposite_carried (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) :
    simplicialCarrierComposite K n (FreeAbelianGroup.of σ) ∈
      (chainInclusion (fullFaceComplex σ.1) K (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)).range := by
  change affineSmallSubdivision K n (FreeAbelianGroup.of σ) ∈
    ((chainInclusion (fullFaceComplex σ.1) K (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)).range).comap
      (normalizedStarSmallApproximation K n)
  rw [affineSmallSubdivision_of]
  apply AddSubgroup.sum_mem
  intro π hπ
  apply AddSubgroup.zsmul_mem
  exact chainInclusion_range_mono_of_subcomplex _ _ K
    (affine_flag_carrier_in_fullFace K n σ π)
    (realizationCarrier_subcomplex K _) (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)
    (normalizedStarSmallApproximation_carried K n
      ⟨_, affine_barycentricFlag_starSmall K n σ π⟩)

end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
universe u
variable {V : Type u} [LinearOrder V]

private theorem inverse_cast_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) f.range =
      (Eq.mp (congrArg (fun k => A →+ F k) h) f).range := by cases h; rfl

theorem boundaries_nat_eq_positiveBoundary_range (K : FiniteComplex V) (n : ℕ) :
    boundaries K (n:ℤ) = (positiveBoundary K n).range := by
  have h : ((n:ℤ)+1-1) = (n:ℤ) := by omega
  have h' : (((n+1:ℕ):ℤ)-1) = (n:ℤ) := by omega
  change Eq.mp (congrArg (fun k : ℤ => AddSubgroup (chains K k)) h)
      (boundary K ((n:ℤ)+1)).range =
    (Eq.mp (congrArg (fun k : ℤ => chains K ((n+1:ℕ):ℤ) →+ chains K k) h')
      (boundary K ((n+1:ℕ):ℤ))).range
  exact inverse_cast_range h (boundary K ((n:ℤ)+1))

theorem fullFace_carried_top_cycle_zero (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n:ℤ)) (c : chains K (n:ℤ))
    (hc : boundary K (n:ℤ) c = 0)
    (hcar : c ∈ (chainInclusion (fullFaceComplex σ.1) K
      (fullFaceComplex_subcomplex K σ.1 σ.2.1) (n:ℤ)).range) : c = 0 := by
  let L := fullFaceComplex σ.1
  let hLK := fullFaceComplex_subcomplex K σ.1 σ.2.1
  have hcard : σ.1.card = n+1 := by rcases σ.2.2 with h | h <;> omega
  have hne : σ.1.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hcar
  have hacycle : a ∈ cycles L (n:ℤ) := by
    change boundary L (n:ℤ) a = 0
    apply carrierChainInclusion_injective L K hLK ((n:ℤ)-1)
    have hcomm := DFunLike.congr_fun (chainInclusion_boundary L K hLK (n:ℤ)) a
    change boundary K (n:ℤ) (chainInclusion L K hLK (n:ℤ) a) =
      chainInclusion L K hLK ((n:ℤ)-1) (boundary L (n:ℤ) a) at hcomm
    rw [ha, hc] at hcomm
    simpa only [map_zero] using hcomm.symm
  letI := nonemptyCone_reducedHomology L (fullFaceComplex_isNonemptyCone σ.1 hne) (n:ℤ) (by omega)
  have hzero : (QuotientAddGroup.mk (⟨a, hacycle⟩ : cycles L (n:ℤ)) : reducedHomology L (n:ℤ)) = 0 :=
    Subsingleton.elim _ _
  have hb := (QuotientAddGroup.eq_zero_iff (⟨a, hacycle⟩ : cycles L (n:ℤ))).mp hzero
  change a ∈ boundaries L (n:ℤ) at hb
  rw [boundaries_nat_eq_positiveBoundary_range] at hb
  obtain ⟨b, hb⟩ := hb
  letI : IsEmpty (SimplexAt L ((n+1:ℕ):ℤ)) := ⟨by
    intro τ
    have hle : τ.1.card ≤ σ.1.card := Finset.card_le_card τ.2.1
    rcases τ.2.2 with h | h <;> omega⟩
  have hbzero : b = 0 := Subsingleton.elim _ _
  rw [hbzero, map_zero] at hb
  rw [← ha, ← hb, map_zero]

theorem boundary_zero_augmentation (K : FiniteComplex V) (v : ActiveVertex K)
    (c : chains K 0) :
    boundary K 0 c = RawCone.aug c • FreeAbelianGroup.of
      (⟨∅, K.down_closed (Finset.empty_subset _) v.2, Or.inl ⟨rfl, rfl⟩⟩ : SimplexAt K (-1)) := by
  classical
  have he : (∅ : Finset V) ∈ K := K.down_closed (Finset.empty_subset _) v.2
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero, zero_smul]
  | of σ =>
    have hc : σ.1.card = 1 := by rcases σ.2.2 with h | h <;> omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
    simp [boundary, faceBoundary, hw, he, RawCone.aug, Finset.filter_singleton]
  | neg c hc => simp only [map_neg, hc, neg_smul]
  | add c d hc hd => simp only [map_add, hc, hd, add_smul]

theorem normalizedStarSmallApproximation_zero_aug (K : FiniteComplex V)
    (c : FreeAbelianGroup (StarSmallSimplex K 0)) :
    RawCone.aug (normalizedStarSmallApproximation K 0 c) =
      RawCone.aug (starSmallChainInclusion K 0 c) := by
  have he : RawCone.aug.comp (normalizedStarSmallApproximation K 0) =
      RawCone.aug.comp (starSmallChainInclusion K 0) := by
    apply FreeAbelianGroup.lift_ext
    intro s
    obtain ⟨v, hv⟩ := normalizedStarSmallApproximation_zero K s
    simp only [AddMonoidHom.comp_apply, hv, RawCone.aug, FreeAbelianGroup.lift_apply_of,
      starSmallChainInclusion, FreeAbelianGroup.map_of_apply]
  exact DFunLike.congr_fun he c

end CurveGenusTwo.Filtration
namespace CurveGenusTwo.Filtration
open CurveComplexGenusTwo.CWHurewicz
variable {V : Type} [LinearOrder V]

theorem rawSingularSubdivision_degree_zero (K : FiniteComplex V)
    (c : FreeAbelianGroup ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))) _⦋0⦌)) :
    rawSingularSubdivision K 0 c = c := by
  simp only [rawSingularSubdivision, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    singularBarycentricFinsupp_degree_zero, Finsupp.toFreeAbelianGroup_toFinsupp]

theorem simplicialCarrierComposite_zero_aug (K : FiniteComplex V) (c : chains K 0) :
    RawCone.aug (simplicialCarrierComposite K 0 c) = RawCone.aug c := by
  change RawCone.aug (normalizedStarSmallApproximation K 0 (affineSmallSubdivision K 0 c)) = _
  rw [normalizedStarSmallApproximation_zero_aug, affineSmallSubdivision_inclusion,
    rawSingularSubdivision_degree_zero]
  have he : RawCone.aug.comp (simplicialToSingularGenerators K 0) = RawCone.aug := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    simp only [AddMonoidHom.comp_apply, simplicialToSingularGenerators_of, RawCone.aug, FreeAbelianGroup.lift_apply_of]
  exact DFunLike.congr_fun he c

/-- The normalized carried approximation of one barycentric subdivision of
an affine simplicial chain is exactly that original chain. -/
theorem simplicialCarrierComposite_eq_id (K : FiniteComplex V) (n : ℕ)
    (c : chains K (n:ℤ)) : simplicialCarrierComposite K n c = c := by
  suffices he : simplicialCarrierComposite K n = AddMonoidHom.id _ by rw [he]; rfl
  induction n with
  | zero =>
    apply FreeAbelianGroup.lift_ext
    intro σ
    apply sub_eq_zero.mp
    apply fullFace_carried_top_cycle_zero K 0 σ
    · have hc : σ.1.card = 1 := by rcases σ.2.2 with h | h <;> omega
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
      have hav : ({v} : Finset V) ∈ K := hv ▸ σ.2.1
      change boundary K 0 (simplicialCarrierComposite K 0 (FreeAbelianGroup.of σ) - FreeAbelianGroup.of σ) = 0
      have haug : RawCone.aug (simplicialCarrierComposite K 0 (FreeAbelianGroup.of σ) - FreeAbelianGroup.of σ) = 0 := by
        exact (map_sub RawCone.aug _ _).trans
          (sub_eq_zero.mpr (simplicialCarrierComposite_zero_aug K (FreeAbelianGroup.of σ)))
      exact (boundary_zero_augmentation K ⟨v, hav⟩ _).trans
        ((congrArg (fun t : ℤ => t • (FreeAbelianGroup.of ⟨∅, K.down_closed (Finset.empty_subset _) hav, Or.inl ⟨rfl, rfl⟩⟩ : chains K (-1))) haug).trans (zero_smul _ _))
    · apply AddSubgroup.sub_mem
      · exact simplicialCarrierComposite_carried K 0 σ
      · exact ⟨FreeAbelianGroup.of ⟨σ.1, Finset.Subset.refl _, σ.2.2⟩, rfl⟩
  | succ n ih =>
    apply FreeAbelianGroup.lift_ext
    intro σ
    apply sub_eq_zero.mp
    apply fullFace_carried_top_cycle_zero K (n+1) σ
    · apply (positiveBoundary_eq_zero_iff K n _).mp
      rw [map_sub, simplicialCarrierComposite_boundary, ih 0]
      simp
    · apply AddSubgroup.sub_mem
      · exact simplicialCarrierComposite_carried K (n+1) σ
      · exact ⟨FreeAbelianGroup.of ⟨σ.1, Finset.Subset.refl _, σ.2.2⟩, rfl⟩

#print axioms simplicialCarrierComposite_eq_id
end CurveGenusTwo.Filtration

namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

/-- Producer B in universe zero, using the actual normalized reverse map. -/
theorem positiveCyclesMap_reflects_boundaries_universe_zero :
    ∀ (K : FiniteComplex V) (n : ℕ) (c : cycles K ((n+1:ℕ):ℤ)),
      (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n →
        c.1 ∈ boundaries K ((n+1:ℕ):ℤ) := by
  intro K n c hc
  let a := affineSmallSubdivision K (n+1) c.1
  have hacycle : starSmallBoundary K n a = 0 := by
    rw [affineSmallSubdivision_boundary,
      (positiveBoundary_eq_zero_iff K n c.1).mpr c.2, map_zero]
  have haraw : starSmallChainInclusion K (n+1) a ∈ singularPositiveBoundaries K n := by
    obtain ⟨b, hb⟩ := hc
    refine ⟨rawSingularSubdivision K (n+2) b, ?_⟩
    rw [rawSingularSubdivision_boundary, hb]
    exact (affineSmallSubdivision_inclusion K (n+1) c.1).symm
  obtain ⟨b, hb⟩ := starSmallCycle_bounds_of_raw_bounds K n a hacycle haraw
  rw [boundaries_nat_eq_positiveBoundary_range]
  refine ⟨normalizedStarSmallApproximation K (n+2) b, ?_⟩
  rw [normalizedStarSmallApproximation_boundary, hb]
  exact simplicialCarrierComposite_eq_id K (n+1) c.1

#print axioms positiveCyclesMap_reflects_boundaries_universe_zero
end CurveGenusTwo.Filtration
