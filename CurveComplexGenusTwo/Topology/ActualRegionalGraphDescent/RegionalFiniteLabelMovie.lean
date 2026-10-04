import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteSimplexPushforward
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalRealizationMovieGluing

open CurveComplex Set
open scoped BigOperators

private theorem regionalPushforwardFaceWeight
    {V W : Type*} [DecidableEq W]
    (L : AbstractSimplicialComplex W) (σ : Finset V) (τ : Finset W)
    (hτ : τ ∈ L.faces) (f : V → W) (hf : ∀ i ∈ σ, f i ∈ τ)
    (p : FiniteSimplex σ) (v : W) :
    (faceInclusion L τ hτ (regionalFiniteSimplexPushforward σ τ
      (fun i => ⟨f i.val,hf i.val i.property⟩) p)).weight v =
      ∑ i : ↥σ, if f i.val = v then p.val i else 0 := by
  classical
  by_cases hv : v ∈ τ
  · rw [faceInclusion_weight_of_mem L τ hτ _ v hv]
    simp only [regionalFiniteSimplexPushforward,Subtype.mk.injEq]
  · rw [faceInclusion_weight_of_not_mem L τ hτ _ v hv]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hn : f i.val ≠ v := fun he => hv (he ▸ hf i.val i.property)
    simp [hn]

private theorem regionalFaceFiberSum
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (K : AbstractSimplicialComplex V) (σ : Finset V) (hσ : σ ∈ K.faces)
    (f : V → W) (p : FiniteSimplex σ) (v : W) :
    (∑ i : ↥σ, if f i.val = v then p.val i else 0) =
      ∑ i : V, if f i = v then (faceInclusion K σ hσ p).weight i else 0 := by
  classical
  have hsub : (∑ i ∈ σ, if f i = v then (faceInclusion K σ hσ p).weight i else 0) =
      ∑ i : V, if f i = v then (faceInclusion K σ hσ p).weight i else 0 := by
    apply Finset.sum_subset (Finset.subset_univ σ)
    intro i hi his
    rw [faceInclusion_weight_of_not_mem K σ hσ p i his]
    split_ifs <;> rfl
  rw [← hsub]
  calc
    (∑ i : ↥σ, if f i.val = v then p.val i else 0) =
        ∑ i ∈ σ.attach, if f i.val = v then (faceInclusion K σ hσ p).weight i.val else 0 := by
      rw [← Finset.univ_eq_attach]
      apply Finset.sum_congr rfl
      intro i hi
      rw [faceInclusion_weight_of_mem K σ hσ p i.val i.property]
    _ = ∑ i ∈ σ, if f i = v then (faceInclusion K σ hσ p).weight i else 0 :=
      Finset.sum_attach σ (fun i : V => if f i = v then (faceInclusion K σ hσ p).weight i else 0)

/-- Contiguous finite-domain label maps produce a jointly continuous movie
    on the whole weak realization, summing over colliding label fibers. -/
theorem regional_finite_label_contiguity_movie
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f g : V → W)
    (hcommon : ∀ σ : Finset V, σ ∈ K.faces →
      σ.image f ∪ σ.image g ∈ L.faces) :
    ∃ H : C(ConeTime × RealizationPoint K,RealizationPoint L),
      ∀ t x v, (H (t,x)).weight v =
        (1-(t : ℝ)) * (∑ i : V, if f i = v then x.weight i else 0) +
        (t : ℝ) * (∑ i : V, if g i = v then x.weight i else 0) := by
  classical
  have existsMovie (σ : Finset V) (hσ : σ ∈ K.faces) :
      ∃ M : C(ConeTime × FiniteSimplex σ,RealizationPoint L),
        ∀ t p v, (M (t,p)).weight v =
          (1-(t : ℝ)) * (∑ i : V, if f i = v then (faceInclusion K σ hσ p).weight i else 0) +
          (t : ℝ) * (∑ i : V, if g i = v then (faceInclusion K σ hσ p).weight i else 0) := by
    let τ := σ.image f ∪ σ.image g
    have hτ : τ ∈ L.faces := hcommon σ hσ
    have hf : ∀ i ∈ σ, f i ∈ τ := fun i hi =>
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    have hg : ∀ i ∈ σ, g i ∈ τ := fun i hi =>
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    let P := regionalFiniteSimplexPushforward σ τ (fun i => ⟨f i.val,hf i.val i.property⟩)
    let Q := regionalFiniteSimplexPushforward σ τ (fun i => ⟨g i.val,hg i.val i.property⟩)
    let M : C(ConeTime × FiniteSimplex σ,RealizationPoint L) :=
      ⟨fun z => faceInclusion L τ hτ
        (regionalFiniteSimplexInterpolation τ (P z.2) (Q z.2) z.1),
        (continuous_faceInclusion L τ hτ).comp
          ((regionalFiniteSimplexInterpolation_continuous τ).comp
            (continuous_fst.prodMk
              (((regionalFiniteSimplexPushforward_continuous σ τ _).comp continuous_snd).prodMk
                ((regionalFiniteSimplexPushforward_continuous σ τ _).comp continuous_snd))))⟩
    refine ⟨M,?_⟩
    intro t p v
    have hw : (M (t,p)).weight v =
        (1-(t : ℝ)) * (faceInclusion L τ hτ (P p)).weight v +
        (t : ℝ) * (faceInclusion L τ hτ (Q p)).weight v := by
      by_cases hv : v ∈ τ
      · simp only [M,ContinuousMap.coe_mk,faceInclusion_weight_of_mem L τ hτ _ v hv,
          regionalFiniteSimplexInterpolation]
      · simp only [M,ContinuousMap.coe_mk,faceInclusion_weight_of_not_mem L τ hτ _ v hv]
        ring
    rw [hw]
    rw [regionalPushforwardFaceWeight L σ τ hτ f hf p v,
      regionalPushforwardFaceWeight L σ τ hτ g hg p v,
      regionalFaceFiberSum K σ hσ f p v,regionalFaceFiberSum K σ hσ g p v]
  choose M hM using existsMovie
  have hcoherent : ∀ σ τ (hσ : σ ∈ K.faces) (hτ : τ ∈ K.faces)
      (t : ConeTime) (p : FiniteSimplex σ) (q : FiniteSimplex τ),
      faceInclusion K σ hσ p = faceInclusion K τ hτ q →
      M σ hσ (t,p) = M τ hτ (t,q) := by
    intro σ τ hσ hτ t p q he
    apply RealizationPoint.ext
    funext v
    rw [hM σ hσ,hM τ hτ,he]
  obtain ⟨H,hH⟩ := regional_coherent_finite_face_movies_glue K L
    (fun σ hσ => M σ hσ) (fun σ hσ => (M σ hσ).continuous) hcoherent
  refine ⟨H,?_⟩
  intro t x v
  obtain ⟨σ,hσ,p,rfl⟩ := exists_faceInclusion_eq K x
  rw [hH]
  exact hM σ hσ t p v

#print axioms regional_finite_label_contiguity_movie

/-- A finite vertex map preserving faces induces an actual continuous map of
    weak realizations, with exact fiber-summed weights. -/
theorem regional_finite_label_realization_map
    {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : V → W) (hface : ∀ σ : Finset V, σ ∈ K.faces → σ.image f ∈ L.faces) :
    ∃ M : C(RealizationPoint K,RealizationPoint L),
      ∀ x v, (M x).weight v = ∑ i : V, if f i = v then x.weight i else 0 := by
  obtain ⟨H,hw⟩ := regional_finite_label_contiguity_movie K L f f
    (fun σ hσ => by simpa using hface σ hσ)
  refine ⟨⟨fun x => H (0,x),H.continuous.comp (continuous_const.prodMk continuous_id)⟩,?_⟩
  intro x v
  simpa using hw 0 x v

/-- A one-index replacement is contiguous when the SAME new label extends
    every incident image face. An index with a colliding old label is still
    moved independently. -/
theorem regional_indexed_label_replacement_contiguous
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : V → W) (k : V) (new : W)
    (hface : ∀ σ : Finset V, σ ∈ K.faces → σ.image f ∈ L.faces)
    (hcommon : ∀ σ : Finset V, σ ∈ K.faces → k ∈ σ →
      insert new (σ.image f) ∈ L.faces) :
    ∀ σ : Finset V, σ ∈ K.faces →
      σ.image f ∪ σ.image (Function.update f k new) ∈ L.faces := by
  intro σ hσ
  by_cases hk : k ∈ σ
  · have heq : σ.image f ∪ σ.image (Function.update f k new) =
        insert new (σ.image f) := by
      ext v
      constructor
      · intro hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact Finset.mem_insert_of_mem hv
        · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
          by_cases hik : i = k
          · simp [hik]
          · simp only [Function.update_of_ne hik]
            exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
      · intro hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,hk,by simp⟩)
        · exact Finset.mem_union_left _ hv
    rw [heq]
    exact hcommon σ hσ hk
  · have heq : σ.image (Function.update f k new) = σ.image f := by
      apply Finset.image_congr
      intro i hi
      have hik : i ≠ k := fun he => hk (he ▸ hi)
      simp [hik]
    simpa [heq] using hface σ hσ

#print axioms regional_finite_label_realization_map
#print axioms regional_indexed_label_replacement_contiguous
