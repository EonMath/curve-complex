import FiniteBarycentricInverseHelpers
open CurveComplex Set Topology
attribute [local instance] instDecidable_c0RelativeCarrierScaffold instDecidableEq_c0RelativeCarrierScaffold
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace C0RelativeCarrier
theorem finite_barycentric_realization_homeomorph_relative
    {V : Type*} [Fintype V] (D : AbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex V)
    (hLD : ∀ σ ∈ L.faces, σ ∈ D.faces) :
    ∃ e : RealizationPoint (barycentricSubdivision D) ≃ₜ RealizationPoint D,
      (∀ x v, (e x).weight v =
        ∑ σ : Face D, if v ∈ σ.val then x.weight σ / (σ.val.card : ℝ) else 0) ∧
      e '' range (fullToAmbient (barycentricSubdivision D)
        (fun σ : Face D => σ.val ∈ L.faces)) =
        {x : RealizationPoint D | ∃ σ ∈ L.faces, ∀ v ∉ σ, x.weight v = 0} := by
  classical
  have _hLD := hLD
  have hcard (σ : Face D) : (0 : ℝ) < (σ.val.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (D.isRelLowerSet_faces σ.property).1
  have hmax (Γ : Finset (Face D)) (hΓ : Γ ∈ flagFaces D) :
      ∃ τ ∈ Γ, ∀ σ ∈ Γ, σ.val ⊆ τ.val := by
    obtain ⟨τ, hτ, hτmax⟩ := Γ.exists_max_image (fun σ => σ.val.card) hΓ.1
    refine ⟨τ, hτ, ?_⟩
    intro σ hσ
    rcases hΓ.2 σ hσ τ hτ with h | h
    · exact h
    · have heq := Finset.eq_of_subset_of_card_le h (hτmax σ hσ)
      exact heq ▸ Finset.Subset.refl τ.val
  have hsum (x : RealizationPoint (barycentricSubdivision D)) :
      ∑ σ : Face D, x.weight σ = 1 := by
    obtain ⟨Γ, hΓ, hz, hs⟩ := x.liesInFace
    have heq : (∑ σ ∈ Γ, x.weight σ) = ∑ σ : Face D, x.weight σ :=
      Finset.sum_subset (Finset.subset_univ Γ) (fun σ _ hσ => hz σ hσ)
    exact heq.symm.trans hs
  let b : RealizationPoint (barycentricSubdivision D) → V → ℝ :=
    fun x v => ∑ σ : Face D, if v ∈ σ.val then x.weight σ / (σ.val.card : ℝ) else 0
  have hbnonneg (x : RealizationPoint (barycentricSubdivision D)) (v : V) :
      0 ≤ b x v := by
    apply Finset.sum_nonneg
    intro σ hσ
    split_ifs
    · exact div_nonneg (x.nonneg σ) (le_of_lt (hcard σ))
    · exact le_rfl
  have hbsum (x : RealizationPoint (barycentricSubdivision D)) :
      ∑ v : V, b x v = 1 := by
    dsimp only [b]
    rw [Finset.sum_comm]
    convert hsum x using 1
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.sum_ite_mem]
    simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    exact mul_div_cancel₀ (x.weight σ) (ne_of_gt (hcard σ))
  have hbface (x : RealizationPoint (barycentricSubdivision D)) :
      ∃ τ : Face D, ∀ v ∉ τ.val, b x v = 0 := by
    obtain ⟨Γ, hΓ, hz, hs⟩ := x.liesInFace
    obtain ⟨τ, hτ, hτmax⟩ := hmax Γ hΓ
    refine ⟨τ, ?_⟩
    intro v hv
    apply Finset.sum_eq_zero
    intro σ hσ
    by_cases hσΓ : σ ∈ Γ
    · have hvσ : v ∉ σ.val := fun hm => hv (hτmax σ hσΓ hm)
      simp [hvσ]
    · simp [hz σ hσΓ]
  let f : RealizationPoint (barycentricSubdivision D) → RealizationPoint D :=
    fun x => {
      weight := b x
      nonneg := hbnonneg x
      liesInFace := by
        obtain ⟨τ, hτ⟩ := hbface x
        refine ⟨τ.val, τ.property, hτ, ?_⟩
        have heq : (∑ v ∈ τ.val, b x v) = ∑ v : V, b x v :=
          Finset.sum_subset (Finset.subset_univ τ.val) (fun v _ hv => hτ v hv)
        exact heq.trans (hbsum x) }
  have hcompact {A : Type _} [Fintype A] (K : AbstractSimplicialComplex A) :
      CompactSpace (RealizationPoint K) := by
    have heq : (Set.univ : Set (RealizationPoint K)) =
        ⋃ σ : {σ : Finset A // σ ∈ K.faces},
          range (faceInclusion K σ.val σ.property) := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      obtain ⟨σ, hσ, y, hy⟩ := exists_faceInclusion_eq K x
      exact ⟨⟨σ, hσ⟩, y, hy⟩
    apply isCompact_univ_iff.mp
    rw [heq]
    apply isCompact_iUnion
    intro σ
    exact isCompact_range (continuous_faceInclusion K σ.val σ.property)
  let : CompactSpace (RealizationPoint D) := hcompact D
  let : CompactSpace (RealizationPoint (barycentricSubdivision D)) :=
    hcompact (barycentricSubdivision D)
  have hwcont : Continuous (fun x : RealizationPoint D => x.weight) :=
    continuous_pi (fun v => continuous_weight D v)
  have hwinj : Function.Injective (fun x : RealizationPoint D => x.weight) := by
    intro x y h
    exact RealizationPoint.ext h
  have hwemb := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    hwcont hwinj (by
      intro T hT
      exact (hT.isCompact.image hwcont).isClosed)
  have hfcont : Continuous f := by
    apply hwemb.isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro v
    apply continuous_finsetSum
    intro σ hσ
    by_cases hv : v ∈ σ.val
    · simpa [Function.comp_def, f, b, hv] using
        (continuous_weight (barycentricSubdivision D) σ).div_const (σ.val.card : ℝ)
    · simpa [Function.comp_def, f, b, hv] using
        (continuous_const : Continuous (fun _ : RealizationPoint (barycentricSubdivision D) => (0 : ℝ)))
  have hrelative (x : RealizationPoint (barycentricSubdivision D)) :
      x ∈ range (fullToAmbient (barycentricSubdivision D)
        (fun σ : Face D => σ.val ∈ L.faces)) ↔
        ∃ τ ∈ L.faces, ∀ v ∉ τ, b x v = 0 := by
    constructor
    · rintro ⟨z, rfl⟩
      let x := fullToAmbient (barycentricSubdivision D)
        (fun σ : Face D => σ.val ∈ L.faces) z
      let Γ := supportFinset (barycentricSubdivision D) x
      have hΓ : Γ ∈ flagFaces D :=
        supportFinset_mem_faces (barycentricSubdivision D) x
      obtain ⟨τ, hτ, hτmax⟩ := hmax Γ hΓ
      have hτL : τ.val ∈ L.faces := by
        by_contra hn
        have hz := fullToAmbient_weight_of_not_property (barycentricSubdivision D)
          (fun σ : Face D => σ.val ∈ L.faces) z τ hn
        exact ((mem_supportFinset_iff (barycentricSubdivision D) x τ).mp hτ) hz
      refine ⟨τ.val, hτL, ?_⟩
      intro v hv
      apply Finset.sum_eq_zero
      intro σ hσ
      by_cases hσΓ : σ ∈ Γ
      · have hvσ : v ∉ σ.val := fun hm => hv (hτmax σ hσΓ hm)
        simp [hvσ]
      · have hz : x.weight σ = 0 := by
          by_contra hn
          exact hσΓ ((mem_supportFinset_iff (barycentricSubdivision D) x σ).mpr hn)
        change (if v ∈ σ.val then x.weight σ / (σ.val.card : ℝ) else 0) = 0
        simp [hz]
    · rintro ⟨τ, hτL, hz⟩
      have hx : x ∈ fullSupportLocus (barycentricSubdivision D)
          (fun σ : Face D => σ.val ∈ L.faces) := by
        intro σ hσL
        by_contra hn
        have hσpos : 0 < x.weight σ := lt_of_le_of_ne (x.nonneg σ) (Ne.symm hn)
        have hsub : σ.val ⊆ τ := by
          intro v hvσ
          by_contra hvτ
          have hterm : x.weight σ / (σ.val.card : ℝ) ≤ b x v := by
            calc
              _ = (if v ∈ σ.val then x.weight σ / (σ.val.card : ℝ) else 0) := by simp [hvσ]
              _ ≤ b x v := Finset.single_le_sum
                (f := fun ρ : Face D => if v ∈ ρ.val then x.weight ρ / (ρ.val.card : ℝ) else 0) (by
                intro ρ hρ
                split_ifs
                · exact div_nonneg (x.nonneg ρ) (le_of_lt (hcard ρ))
                · exact le_rfl) (Finset.mem_univ σ)
          have hpos := div_pos hσpos (hcard σ)
          rw [hz v hvτ] at hterm
          exact (not_le_of_gt hpos) hterm
        exact hσL ((L.isRelLowerSet_faces hτL).2 hsub
          (D.isRelLowerSet_faces σ.property).1)
      exact ⟨supportedToFull (barycentricSubdivision D)
        (fun σ : Face D => σ.val ∈ L.faces) ⟨x, hx⟩,
        fullToAmbient_supportedToFull (barycentricSubdivision D) _ ⟨x, hx⟩⟩
  have hpositive_chain (z : RealizationPoint (barycentricSubdivision D))
      (σ τ : Face D) (hσ : 0 < z.weight σ) (hτ : 0 < z.weight τ) :
      σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val := by
    obtain ⟨Γ, hΓ, hz, hs⟩ := z.liesInFace
    have hσΓ : σ ∈ Γ := by
      by_contra hn
      rw [hz σ hn] at hσ
      exact (lt_irrefl 0) hσ
    have hτΓ : τ ∈ Γ := by
      by_contra hn
      rw [hz τ hn] at hτ
      exact (lt_irrefl 0) hτ
    exact hΓ.2 σ hσΓ τ hτΓ
  have hinverse (y : RealizationPoint D) :
      ∃! x : RealizationPoint (barycentricSubdivision D), ∀ v, b x v = y.weight v := by
    let A : Finset ℝ := (Finset.univ.image y.weight).filter (fun a => 0 < a)
    let predecessor : ℝ → ℝ := fun a =>
      (({(0 : ℝ)} : Finset ℝ) ∪ A.filter (fun b => b < a)).max' (by simp)
    let delta : ℝ → ℝ := fun a => a - predecessor a
    have hE := BarycentricInverseHelpers.finite_positive_level_gap_reconstruction
      y.weight y.nonneg
    change (∀ a ∈ A, 0 < delta a) ∧
      (∀ v, ∑ a ∈ A, (if a ≤ y.weight v then delta a else 0) = y.weight v) at hE
    have hAne : A.Nonempty := by
      obtain ⟨v, hv⟩ := exists_mem_openVertexStar D y
      refine ⟨y.weight v, Finset.mem_filter.mpr ⟨?_, hv⟩⟩
      exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
    obtain ⟨S, hS, hzS, hsS⟩ := y.liesInFace
    have hYsum : ∑ v : V, y.weight v = 1 := by
      have heq : (∑ v ∈ S, y.weight v) = ∑ v : V, y.weight v :=
        Finset.sum_subset (Finset.subset_univ S) (fun v _ hv => hzS v hv)
      exact heq.symm.trans hsS
    let θ : A → Face D := fun a =>
      ⟨Finset.univ.filter (fun v => a.val ≤ y.weight v), by
        apply (D.isRelLowerSet_faces hS).2
        · intro v hv
          have hav : a.val ≤ y.weight v := (Finset.mem_filter.mp hv).2
          by_contra hn
          rw [hzS v hn] at hav
          exact (not_le_of_gt (Finset.mem_filter.mp a.property).2) hav
        · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp a.property).1
          refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩⟩
          rw [heq]⟩
    have hθmem (a : A) (v : V) : v ∈ (θ a).val ↔ a.val ≤ y.weight v := by
      simp [θ]
    have hθchain (a d : A) : (θ a).val ⊆ (θ d).val ∨ (θ d).val ⊆ (θ a).val := by
      rcases le_total a.val d.val with had | hda
      · right
        intro v hv
        exact (hθmem a v).mpr (had.trans ((hθmem d v).mp hv))
      · left
        intro v hv
        exact (hθmem d v).mpr (hda.trans ((hθmem a v).mp hv))
    let Γ : Finset (Face D) := Finset.univ.image θ
    have hΓ : Γ ∈ (barycentricSubdivision D).faces := by
      constructor
      · obtain ⟨a, ha⟩ := hAne
        exact ⟨θ ⟨a, ha⟩, Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩⟩
      · intro σ hσ τ hτ
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hσ
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hτ
        exact hθchain a d
    let c : Face D → ℝ := fun σ =>
      ∑ a : A, if θ a = σ then ((θ a).val.card : ℝ) * delta a.val else 0
    have hc (σ : Face D) : 0 ≤ c σ := by
      apply Finset.sum_nonneg
      intro a ha
      split_ifs
      · exact mul_nonneg (le_of_lt (hcard (θ a))) (hE.1 a.val a.property).le
      · exact le_rfl
    have hc_zero (σ : Face D) (hσ : σ ∉ Γ) : c σ = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      have hn : θ a ≠ σ := by
        intro heq
        exact hσ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, heq⟩)
      simp [hn]
    have hlevelsum (v : V) :
        (∑ a : A, if a.val ≤ y.weight v then delta a.val else 0) = y.weight v := by
      rw [← Finset.sum_subtype A (fun a => Iff.rfl)
        (fun a => if a ≤ y.weight v then delta a else 0)]
      exact hE.2 v
    have hc_bar (v : V) :
        (∑ σ : Face D, if v ∈ σ.val then c σ / (σ.val.card : ℝ) else 0) = y.weight v := by
      calc
        _ = ∑ σ : Face D, ∑ a : A,
            if θ a = σ then (if v ∈ (θ a).val then delta a.val else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro σ hσ
          by_cases hv : v ∈ σ.val
          · rw [ite_eq_left hv]
            dsimp only [c]
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro a ha
            by_cases heq : θ a = σ
            · rw [ite_eq_left heq, ite_eq_left heq, heq, ite_eq_left hv]
              exact mul_div_cancel_left₀ (delta a.val) (ne_of_gt (hcard σ))
            · simp [heq]
          · rw [ite_eq_right hv]
            symm
            apply Finset.sum_eq_zero
            intro a ha
            by_cases heq : θ a = σ
            · simp [heq, hv]
            · simp [heq]
        _ = ∑ a : A, ∑ σ : Face D,
            if θ a = σ then (if v ∈ (θ a).val then delta a.val else 0) else 0 :=
          Finset.sum_comm
        _ = ∑ a : A, if v ∈ (θ a).val then delta a.val else 0 := by
          simp
        _ = y.weight v := by
          simp only [hθmem]
          exact hlevelsum v
    have hc_sum : ∑ σ : Face D, c σ = 1 := by
      calc
        _ = ∑ v : V, ∑ σ : Face D,
            if v ∈ σ.val then c σ / (σ.val.card : ℝ) else 0 := by
          symm
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [Finset.sum_ite_mem]
          simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          exact mul_div_cancel₀ (c σ) (ne_of_gt (hcard σ))
        _ = ∑ v : V, y.weight v := Finset.sum_congr rfl (fun v _ => hc_bar v)
        _ = 1 := hYsum
    let x : RealizationPoint (barycentricSubdivision D) := {
      weight := c
      nonneg := hc
      liesInFace := ⟨Γ, hΓ, hc_zero, by
        have heq : (∑ σ ∈ Γ, c σ) = ∑ σ : Face D, c σ :=
          Finset.sum_subset (Finset.subset_univ Γ) (fun σ _ hσ => hc_zero σ hσ)
        exact heq.trans hc_sum⟩ }
    refine ⟨x, hc_bar, ?_⟩
    intro z hz
    apply RealizationPoint.ext
    apply BarycentricInverseHelpers.nonnegative_chain_barycenter_injective D
      z.weight x.weight z.nonneg x.nonneg (hpositive_chain z) (hpositive_chain x)
    intro v
    exact (hz v).trans (hc_bar v).symm
  have hbij : Function.Bijective f := by
    constructor
    · intro x z hxz
      obtain ⟨w, hw, huniq⟩ := hinverse (f x)
      have hx : ∀ v, b x v = (f x).weight v := fun _ => rfl
      have hz : ∀ v, b z v = (f x).weight v := by
        intro v
        change (f z).weight v = (f x).weight v
        rw [hxz]
      exact (huniq x hx).trans (huniq z hz).symm
    · intro y
      obtain ⟨x, hx, huniq⟩ := hinverse y
      refine ⟨x, ?_⟩
      exact RealizationPoint.ext (funext hx)
  let e : RealizationPoint (barycentricSubdivision D) ≃ₜ RealizationPoint D :=
    hfcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)
  refine ⟨e, ?_, ?_⟩
  · intro x v
    rfl
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hrelative x).mp hx
    · intro hy
      obtain ⟨x, hx⟩ := hbij.2 y
      refine ⟨x, (hrelative x).mpr ?_, hx⟩
      rcases hy with ⟨τ, hτ, hz⟩
      refine ⟨τ, hτ, ?_⟩
      intro v hv
      change (f x).weight v = 0
      rw [hx]
      exact hz v hv
end C0RelativeCarrier
