import CurveComplexGenusTwo.Foundations.RealizationCW
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import CurveComplexGenusTwo.Foundations.FullSubcomplex

namespace CurveComplex.WeightedFlowScratch

open scoped BigOperators
set_option maxHeartbeats 1000000
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

noncomputable def pushWeight {K : AbstractSimplicialComplex V}
    (f : V → W) (p : RealizationPoint K) (w : W) : ℝ := by
  classical
  exact ∑ v, if f v = w then p.weight v else 0

theorem pushWeight_face (K : AbstractSimplicialComplex V) (f : V → W)
    (p : RealizationPoint K) (σ : Finset V)
    (hz : ∀ v ∉ σ, p.weight v = 0) (w : W) :
    pushWeight f p w = ∑ v ∈ σ with f v = w, p.weight v := by
  classical
  rw [pushWeight, Finset.sum_filter]
  apply (Finset.sum_subset (Finset.subset_univ σ) ?_).symm
  intro v hv hvs
  simp [hz v hvs]

noncomputable def finiteVertexPush (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces)
    (p : RealizationPoint K) : RealizationPoint L := by
  classical
  refine ⟨pushWeight f p, ?_, ?_⟩
  · intro w
    apply Finset.sum_nonneg
    intro v hv
    split_ifs
    · exact p.nonneg v
    · exact le_refl 0
  · obtain ⟨σ, hσ, hz, hs⟩ := p.liesInFace
    refine ⟨σ.image f, hf σ hσ, ?_, ?_⟩
    · intro w hw
      rw [pushWeight_face K f p σ hz]
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨hvs, hfv⟩ := Finset.mem_filter.mp hv
      exact False.elim (hw (Finset.mem_image.mpr ⟨v, hvs, hfv⟩))
    · simp_rw [pushWeight_face K f p σ hz]
      rw [Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem f hv)]
      exact hs

theorem finiteVertexPush_weight (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces)
    (p : RealizationPoint K) (w : W) :
    (finiteVertexPush K L f hf p).weight w = pushWeight f p w := rfl

theorem pushWeight_continuous (K : AbstractSimplicialComplex V) (f : V → W)
    (w : W) : Continuous (fun p : RealizationPoint K => pushWeight f p w) := by
  classical
  unfold pushWeight
  apply continuous_finsetSum
  intro v hv
  by_cases h : f v = w
  · simp only [h, ite_true]
    exact continuous_weight K v
  · simp only [h, ite_false]
    exact continuous_const

theorem finiteVertexPush_continuous (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces) :
    Continuous (finiteVertexPush K L f hf) := by
  classical
  apply (continuous_iff_continuous_on_faces K _).mpr
  intro σ hσ
  let τ := σ.image f
  let a (x : FiniteSimplex σ) : RealizationPoint L :=
    finiteVertexPush K L f hf (faceInclusion K σ hσ x)
  have hz (x : FiniteSimplex σ) (w : W) (hw : w ∉ τ) : (a x).weight w = 0 := by
    change pushWeight f (faceInclusion K σ hσ x) w = 0
    rw [pushWeight_face K f _ σ (fun v hv => faceInclusion_weight_of_not_mem K σ hσ x v hv)]
    apply Finset.sum_eq_zero
    intro v hv
    obtain ⟨hvs, hfv⟩ := Finset.mem_filter.mp hv
    exact False.elim (hw (Finset.mem_image.mpr ⟨v, hvs, hfv⟩))
  have hs (x : FiniteSimplex σ) : ∑ w ∈ τ, (a x).weight w = 1 := by
    change (∑ w ∈ σ.image f, pushWeight f (faceInclusion K σ hσ x) w) = 1
    simp_rw [pushWeight_face K f _ σ (fun v hv => faceInclusion_weight_of_not_mem K σ hσ x v hv)]
    rw [Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem f hv)]
    have heq : (∑ v ∈ σ, (faceInclusion K σ hσ x).weight v) =
        ∑ v : σ, x.val v := by
      rw [← Finset.sum_attach]
      simp only [Finset.univ_eq_attach]
      apply Finset.sum_congr rfl
      intro v hv
      exact faceInclusion_weight_of_mem K σ hσ x v v.property
    exact heq.trans x.property.2
  let y : FiniteSimplex σ → FiniteSimplex τ := fun x =>
    ⟨fun w => (a x).weight w, (fun w => (a x).nonneg w), by
      simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hs x⟩
  have hy : Continuous y := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro w
    exact (pushWeight_continuous K f w).comp (continuous_faceInclusion K σ hσ)
  have heq : finiteVertexPush K L f hf ∘ faceInclusion K σ hσ =
      faceInclusion L τ (hf σ hσ) ∘ y := by
    funext x
    apply RealizationPoint.ext
    funext w
    by_cases hw : w ∈ τ
    · change (a x).weight w = (faceInclusion L τ (hf σ hσ) (y x)).weight w
      rw [faceInclusion_weight_of_mem L τ (hf σ hσ) (y x) w hw]
    · change (a x).weight w = (faceInclusion L τ (hf σ hσ) (y x)).weight w
      rw [faceInclusion_weight_of_not_mem L τ (hf σ hσ) (y x) w hw, hz x w hw]
  rw [heq]
  exact (continuous_faceInclusion L τ (hf σ hσ)).comp hy

theorem weight_sum_of_supported {U : Type*} (K : AbstractSimplicialComplex U)
    (p : RealizationPoint K) (σ : Finset U)
    (hz : ∀ v ∉ σ, p.weight v = 0) : ∑ v ∈ σ, p.weight v = 1 := by
  classical
  obtain ⟨ρ, hρ, hzero, hsum⟩ := p.liesInFace
  have hρu : (∑ v ∈ ρ, p.weight v) = ∑ v ∈ ρ ∪ σ, p.weight v :=
    Finset.sum_subset Finset.subset_union_left (fun v _ hv => hzero v hv)
  have hσu : (∑ v ∈ σ, p.weight v) = ∑ v ∈ ρ ∪ σ, p.weight v :=
    Finset.sum_subset Finset.subset_union_right (fun v _ hv => hz v hv)
  rw [hσu, ← hρu, hsum]

theorem continuous_of_face_coordinates {U X : Type*} [TopologicalSpace X]
    (K : AbstractSimplicialComplex U) (σ : Finset U) (hσ : σ ∈ K.faces)
    (f : X → RealizationPoint K)
    (hz : ∀ x v, v ∉ σ → (f x).weight v = 0)
    (hw : ∀ v, Continuous (fun x => (f x).weight v)) : Continuous f := by
  classical
  let y : X → FiniteSimplex σ := fun x =>
    ⟨fun v => (f x).weight v, (fun v => (f x).nonneg v), by
      simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
        weight_sum_of_supported K (f x) σ (hz x)⟩
  have hy : Continuous y := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact hw v
  have heq : f = faceInclusion K σ hσ ∘ y := by
    funext x
    apply RealizationPoint.ext
    funext v
    by_cases hv : v ∈ σ
    · exact (faceInclusion_weight_of_mem K σ hσ (y x) v hv).symm
    · exact (hz x v hv).trans (faceInclusion_weight_of_not_mem K σ hσ (y x) v hv).symm
  rw [heq]
  exact (continuous_faceInclusion K σ hσ).comp hy

theorem pushWeight_zero_outside (K : AbstractSimplicialComplex V) (f : V → W)
    (p : RealizationPoint K) (σ : Finset V)
    (hz : ∀ v ∉ σ, p.weight v = 0) (w : W) (hw : w ∉ σ.image f) :
    pushWeight f p w = 0 := by
  classical
  rw [pushWeight_face K f p σ hz]
  apply Finset.sum_eq_zero
  intro v hv
  obtain ⟨hvs, hfv⟩ := Finset.mem_filter.mp hv
  exact False.elim (hw (Finset.mem_image.mpr ⟨v, hvs, hfv⟩))

noncomputable def finiteContiguousBlend (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f g : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces)
    (hg : ∀ σ, σ ∈ K.faces → σ.image g ∈ L.faces)
    (hfg : ∀ σ, σ ∈ K.faces → σ.image f ∪ σ.image g ∈ L.faces)
    (z : EdgeTime × RealizationPoint K) : RealizationPoint L := by
  classical
  refine ⟨fun w => (1 - z.1.val) * pushWeight f z.2 w + z.1.val * pushWeight g z.2 w,
    ?_, ?_⟩
  · intro w
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr z.1.property.2) ((finiteVertexPush K L f hf z.2).nonneg w))
      (mul_nonneg z.1.property.1 ((finiteVertexPush K L g hg z.2).nonneg w))
  · obtain ⟨σ, hσ, hz, hs⟩ := z.2.liesInFace
    let τ := σ.image f ∪ σ.image g
    have hzf (w : W) (hw : w ∉ τ) : pushWeight f z.2 w = 0 :=
      pushWeight_zero_outside K f z.2 σ hz w (fun hv => hw (Finset.mem_union_left _ hv))
    have hzg (w : W) (hw : w ∉ τ) : pushWeight g z.2 w = 0 :=
      pushWeight_zero_outside K g z.2 σ hz w (fun hv => hw (Finset.mem_union_right _ hv))
    have hsf : (∑ w ∈ τ, pushWeight f z.2 w) = 1 :=
      weight_sum_of_supported L (finiteVertexPush K L f hf z.2) τ hzf
    have hsg : (∑ w ∈ τ, pushWeight g z.2 w) = 1 :=
      weight_sum_of_supported L (finiteVertexPush K L g hg z.2) τ hzg
    refine ⟨τ, hfg σ hσ, ?_, ?_⟩
    · intro w hw
      rw [hzf w hw, hzg w hw]
      ring
    · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsf, hsg]
      ring

theorem finiteContiguousBlend_zero (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f g : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces)
    (hg : ∀ σ, σ ∈ K.faces → σ.image g ∈ L.faces)
    (hfg : ∀ σ, σ ∈ K.faces → σ.image f ∪ σ.image g ∈ L.faces)
    (p : RealizationPoint K) :
    finiteContiguousBlend K L f g hf hg hfg (0, p) = finiteVertexPush K L f hf p := by
  apply RealizationPoint.ext
  funext w
  change (1 - (0 : ℝ)) * pushWeight f p w + 0 * pushWeight g p w = pushWeight f p w
  ring

theorem finiteContiguousBlend_one (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f g : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces)
    (hg : ∀ σ, σ ∈ K.faces → σ.image g ∈ L.faces)
    (hfg : ∀ σ, σ ∈ K.faces → σ.image f ∪ σ.image g ∈ L.faces)
    (p : RealizationPoint K) :
    finiteContiguousBlend K L f g hf hg hfg (1, p) = finiteVertexPush K L g hg p := by
  apply RealizationPoint.ext
  funext w
  change (1 - (1 : ℝ)) * pushWeight f p w + 1 * pushWeight g p w = pushWeight g p w
  ring

theorem finiteContiguousBlend_continuous (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f g : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces)
    (hg : ∀ σ, σ ∈ K.faces → σ.image g ∈ L.faces)
    (hfg : ∀ σ, σ ∈ K.faces → σ.image f ∪ σ.image g ∈ L.faces) :
    Continuous (finiteContiguousBlend K L f g hf hg hfg) := by
  classical
  have hswap : Continuous (fun z : RealizationPoint K × EdgeTime =>
      finiteContiguousBlend K L f g hf hg hfg (z.2, z.1)) := by
    apply CurveComplexGenusTwo.Topology.continuous_realization_product_of_faces
    intro σ hσ
    let τ := σ.image f ∪ σ.image g
    apply continuous_of_face_coordinates L τ (hfg σ hσ)
    · intro x w hw
      change (1 - x.2.val) * pushWeight f (faceInclusion K σ hσ x.1) w +
        x.2.val * pushWeight g (faceInclusion K σ hσ x.1) w = 0
      have hz v hv := faceInclusion_weight_of_not_mem K σ hσ x.1 v hv
      rw [pushWeight_zero_outside K f _ σ hz w
        (fun hv => hw (Finset.mem_union_left _ hv)),
        pushWeight_zero_outside K g _ σ hz w
        (fun hv => hw (Finset.mem_union_right _ hv))]
      ring
    · intro w
      change Continuous (fun x : FiniteSimplex σ × EdgeTime =>
        (1 - x.2.val) * pushWeight f (faceInclusion K σ hσ x.1) w +
        x.2.val * pushWeight g (faceInclusion K σ hσ x.1) w)
      have ht : Continuous (fun x : FiniteSimplex σ × EdgeTime => x.2.val) :=
        continuous_subtype_val.comp continuous_snd
      have hp : Continuous (fun x : FiniteSimplex σ × EdgeTime =>
          faceInclusion K σ hσ x.1) := (continuous_faceInclusion K σ hσ).comp continuous_fst
      exact ((continuous_const.sub ht).mul ((pushWeight_continuous K f w).comp hp)).add
        (ht.mul ((pushWeight_continuous K g w).comp hp))
  exact hswap.comp (continuous_snd.prodMk continuous_fst)

noncomputable def finiteContiguousHomotopy (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f g : V → W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image f ∈ L.faces)
    (hg : ∀ σ, σ ∈ K.faces → σ.image g ∈ L.faces)
    (hfg : ∀ σ, σ ∈ K.faces → σ.image f ∪ σ.image g ∈ L.faces) :
    ContinuousMap.Homotopy
      ⟨finiteVertexPush K L f hf, finiteVertexPush_continuous K L f hf⟩
      ⟨finiteVertexPush K L g hg, finiteVertexPush_continuous K L g hg⟩ where
  toFun := finiteContiguousBlend K L f g hf hg hfg
  continuous_toFun := finiteContiguousBlend_continuous K L f g hf hg hfg
  map_zero_left := finiteContiguousBlend_zero K L f g hf hg hfg
  map_one_left := finiteContiguousBlend_one K L f g hf hg hfg

theorem finiteHomotopyChain {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (maps : Fin (n + 1) → C(X, Y))
    (h : ∀ (i : ℕ) (hi : i < n), Nonempty
      ((maps ⟨i, by omega⟩).Homotopy (maps ⟨i + 1, by omega⟩))) :
    Nonempty ((maps ⟨0, by omega⟩).Homotopy (maps ⟨n, by omega⟩)) := by
  have hs (i : ℕ) : ∀ hi : i ≤ n,
      Nonempty ((maps ⟨0, by omega⟩).Homotopy (maps ⟨i, by omega⟩)) := by
    induction i with
    | zero =>
      intro hi
      exact ⟨ContinuousMap.Homotopy.refl _⟩
    | succ i ih =>
      intro hi
      obtain ⟨H⟩ := ih (by omega)
      obtain ⟨G⟩ := h i (by omega)
      exact ⟨H.trans G⟩
  exact hs n le_rfl

theorem finiteVertexPush_subtype {U : Type*} [DecidableEq U]
    (K : AbstractSimplicialComplex U) (F : Finset U)
    (p : RealizationPoint (fullSubcomplex K (· ∈ F))) :
    finiteVertexPush (fullSubcomplex K (· ∈ F)) K Subtype.val
      (fun _ h => h) p = fullToAmbient K (· ∈ F) p := by
  classical
  apply RealizationPoint.ext
  funext w
  by_cases hw : w ∈ F
  · rw [fullToAmbient_weight_of_property K (· ∈ F) p w hw]
    change pushWeight Subtype.val p w = p.weight ⟨w, hw⟩
    have heq (v : {v : U // v ∈ F}) : v.val = w ↔ v = ⟨w, hw⟩ := by
      constructor
      · intro h
        apply Subtype.ext
        exact h
      · intro h
        exact congrArg Subtype.val h
    simp only [pushWeight, heq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [fullToAmbient_weight_of_not_property K (· ∈ F) p w hw]
    change pushWeight Subtype.val p w = 0
    unfold pushWeight
    apply Finset.sum_eq_zero
    intro v hv
    have hne : v.val ≠ w := by
      intro heq
      exact hw (heq ▸ v.property)
    simp [hne]

theorem finiteVertexPush_constant (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (w : W)
    (hf : ∀ σ, σ ∈ K.faces → σ.image (fun _ : V => w) ∈ L.faces)
    (p : RealizationPoint K) :
    finiteVertexPush K L (fun _ => w) hf p = realizationVertex L w (L.singleton_mem w) := by
  classical
  apply RealizationPoint.ext
  funext v
  rw [realizationVertex_weight]
  change pushWeight (fun _ : V => w) p v = if v = w then 1 else 0
  by_cases hv : v = w
  · subst v
    simp only [pushWeight, if_true]
    exact weight_sum_of_supported K p Finset.univ (fun v hv => False.elim (hv (Finset.mem_univ v)))
  · simp [pushWeight, hv, Ne.symm hv]

end CurveComplex.WeightedFlowScratch
