import C0RelativeCarrierScaffold
import CurveComplexGenusTwo.CWHurewicz.CellDiskExtension

open CurveComplex Set Topology Metric
attribute [local instance] instDecidable_c0RelativeCarrierScaffold
attribute [local instance] instDecidableEq_c0RelativeCarrierScaffold
set_option autoImplicit false

namespace C0RelativeCarrier

theorem finite_antitone_full_carrier_relative_extension
    {V W : Type*} [Fintype V]
    (D : AbstractSimplicialComplex V)
    (hdim : ∀ σ ∈ D.faces, σ.card ≤ 3)
    (L : PreAbstractSimplicialComplex V)
    (hLD : ∀ σ ∈ L.faces, σ ∈ D.faces)
    (C : AbstractSimplicialComplex W) (P : Face D → W → Prop)
    (hantitone : ∀ σ τ : Face D, σ.val ⊆ τ.val → ∀ v, P τ v → P σ v)
    (hcontractible : ∀ σ : Face D,
      ContractibleSpace (RealizationPoint (fullSubcomplex C (P σ))))
    (b : C(RealizationPoint (boundarySubdivision D L), RealizationPoint C))
    (hboundary :
      ∀ (Γ : Finset {σ : Face D // σ.val ∈ L.faces})
        (hΓ : Γ ∈ (boundarySubdivision D L).faces),
        ∀ σ₀ ∈ Γ, (∀ τ ∈ Γ, σ₀.val.val ⊆ τ.val.val) →
          ∀ x : FiniteSimplex Γ,
            b (faceInclusion (boundarySubdivision D L) Γ hΓ x) ∈
              fullSupportLocus C (P σ₀.val)) :
    ∃ f : C(RealizationPoint (barycentricSubdivision D), RealizationPoint C),
      (∀ x : RealizationPoint (boundarySubdivision D L),
        f (fullToAmbient (barycentricSubdivision D)
          (fun σ : Face D => σ.val ∈ L.faces) x) = b x) ∧
      FlagwiseSupported D C P f := by
  classical
  let K := barycentricSubdivision D
  let Q : Face D → Prop := fun σ => σ.val ∈ L.faces
  let A := fullSupportLocus K Q
  let Y := RealizationPoint C
  have hmono (σ τ : Face D) (h : σ.val ⊆ τ.val) :
      fullSupportLocus C (P τ) ⊆ fullSupportLocus C (P σ) := by
    intro y hy v hv
    exact hy v (fun hp => hv (hantitone σ τ h v hp))
  have hleast (Γ : Finset (Face D)) (hΓ : Γ ∈ K.faces) :
      ∃ σ₀ ∈ Γ, ∀ τ ∈ Γ, σ₀.val ⊆ τ.val := by
    obtain ⟨σ₀, hσ₀, hm⟩ := Γ.exists_min_image (fun σ => σ.val.card) hΓ.1
    refine ⟨σ₀, hσ₀, ?_⟩
    intro τ hτ
    rcases hΓ.2 σ₀ hσ₀ τ hτ with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hm τ hτ)).symm.subset
  have hsimplex (Γ : Finset (Face D)) (hne : Γ.Nonempty) (σ₀ : Face D)
      (g : C({x : FiniteSimplex Γ // ∃ v : Γ, x.val v = 0},
        RealizationPoint (fullSubcomplex C (P σ₀)))) :
      ∃ F : C(FiniteSimplex Γ, RealizationPoint (fullSubcomplex C (P σ₀))),
        ∀ x : {x : FiniteSimplex Γ // ∃ v : Γ, x.val v = 0}, F x.val = g x := by
    let := hcontractible σ₀
    let n := Γ.card - 1
    have hc : Γ.card = n + 1 := by
      have hp := Finset.card_pos.mpr hne
      dsimp [n]
      omega
    let e : (closedBall (0 : Fin n → ℝ) 1) ≃ₜ FiniteSimplex Γ :=
      closedBallFaceSimplexHomeomorph Γ hc
    let j : C((sphere (0 : Fin n → ℝ) 1),
        {x : FiniteSimplex Γ // ∃ v : Γ, x.val v = 0}) :=
      ⟨fun z => ⟨e ⟨z.val, sphere_subset_closedBall z.property⟩,
        (closedBallFaceSimplexHomeomorph_mem_zero_iff Γ hc _).mpr z.property⟩,
        by
          apply Continuous.subtype_mk
          exact e.continuous.comp (continuous_subtype_val.subtype_mk _)⟩
    let gs := g.comp j
    obtain ⟨y₀, hy₀⟩ := (id_nullhomotopic
      (RealizationPoint (fullSubcomplex C (P σ₀)))).comp_left gs
    obtain ⟨F, hF⟩ := CurveComplexGenusTwo.CWHurewicz.cellSphereMap_extends_cellDisk
      n gs y₀ (Classical.choice hy₀)
    refine ⟨F.comp (⟨e.symm, e.symm.continuous⟩ : C(_, _)), ?_⟩
    intro x
    let z := e.symm x.val
    have hz : z.val ∈ sphere (0 : Fin n → ℝ) 1 := by
      apply (closedBallFaceSimplexHomeomorph_mem_zero_iff Γ hc z).mp
      change ∃ v : Γ, (e z).val v = 0
      rw [e.apply_symm_apply]
      exact x.property
    have he : (⟨z.val, sphere_subset_closedBall hz⟩ :
        closedBall (0 : Fin n → ℝ) 1) = z := Subtype.ext rfl
    have hj : j ⟨z.val, hz⟩ = x := by
      apply Subtype.ext
      change e ⟨z.val, sphere_subset_closedBall hz⟩ = x.val
      rw [he]
      exact e.apply_symm_apply x.val
    change F z = g x
    exact (congrArg F he).symm.trans
      ((hF ⟨z.val, hz⟩).trans (congrArg g hj))
  let eA := fullSubcomplexHomeomorphSupported K Q
  let bA : C(A, Y) := b.comp ⟨eA.symm, eA.symm.continuous⟩
  have hbA (x : A) (Γ : Finset (Face D)) (hΓ : Γ ∈ K.faces)
      (σ₀ : Face D) (hσ₀ : σ₀ ∈ Γ) (hmin : ∀ τ ∈ Γ, σ₀.val ⊆ τ.val)
      (hxΓ : x.val ∈ faceCarrier K Γ) : bA x ∈ fullSupportLocus C (P σ₀) := by
    let y := eA.symm x
    let Δ := supportFinset (boundarySubdivision D L) y
    have hΔ : Δ ∈ (boundarySubdivision D L).faces :=
      supportFinset_mem_faces (boundarySubdivision D L) y
    have hne : Δ.Nonempty := supportFinset_nonempty (boundarySubdivision D L) y
    have hcomp : ∀ δ ∈ Δ, ∀ τ ∈ Δ,
        δ.val.val ⊆ τ.val.val ∨ τ.val.val ⊆ δ.val.val := by
      intro δ hδ τ hτ
      exact hΔ.2 δ.val (Finset.mem_image.mpr ⟨δ, hδ, rfl⟩)
        τ.val (Finset.mem_image.mpr ⟨τ, hτ, rfl⟩)
    obtain ⟨δ₀, hδ₀, hm⟩ := Δ.exists_min_image (fun δ => δ.val.val.card) hne
    have hmδ : ∀ τ ∈ Δ, δ₀.val.val ⊆ τ.val.val := by
      intro τ hτ
      rcases hcomp δ₀ hδ₀ τ hτ with h | h
      · exact h
      · exact (Finset.eq_of_subset_of_card_le h (hm τ hτ)).symm.subset
    have hΔΓ : ∀ δ ∈ Δ, δ.val ∈ Γ := by
      intro δ hδ
      have hweight : y.weight δ ≠ 0 :=
        (mem_supportFinset_iff (boundarySubdivision D L) y δ).mp hδ
      have he : fullToAmbient K Q y = x.val := by
        exact congrArg Subtype.val (eA.apply_symm_apply x)
      by_contra hn
      have hz := hxΓ δ.val hn
      rw [← he, fullToAmbient_weight_of_property K Q y δ.val δ.property] at hz
      exact hweight hz
    have hy : y ∈ faceCarrier (boundarySubdivision D L) Δ :=
      (mem_faceCarrier_iff_support_subset (boundarySubdivision D L) Δ y).mpr
        (Finset.Subset.refl Δ)
    rw [faceCarrier_eq_range_faceInclusion (boundarySubdivision D L) Δ hΔ] at hy
    obtain ⟨z, hz⟩ := hy
    have hb : b y ∈ fullSupportLocus C (P δ₀.val) := by
      rw [← hz]
      exact hboundary Δ hΔ δ₀ hδ₀ hmδ z
    exact hmono σ₀ δ₀.val (hmin δ₀.val (hΔΓ δ₀ hδ₀)) hb
  let S (n : ℕ) : Set (RealizationPoint K) :=
    A ∪ {x | (supportFinset K x).card ≤ n}
  have hclosed (n : ℕ) : IsClosed (S n) := by
    have he : {x : RealizationPoint K | (supportFinset K x).card ≤ n} =
        ⋃ Γ : {Γ : Finset (Face D) // Γ ∈ K.faces ∧ Γ.card ≤ n}, faceCarrier K Γ.val := by
      ext x
      constructor
      · intro hx
        exact Set.mem_iUnion.mpr ⟨⟨supportFinset K x,
          supportFinset_mem_faces K x, hx⟩,
          (mem_faceCarrier_iff_support_subset K _ x).mpr (Finset.Subset.refl _)⟩
      · intro hx
        obtain ⟨Γ, hΓ⟩ := Set.mem_iUnion.mp hx
        exact (Finset.card_le_card ((mem_faceCarrier_iff_support_subset K Γ.val x).mp hΓ)).trans
          Γ.property.2
    exact (isClosed_fullSupportLocus K Q).union
      (he.symm ▸ isClosed_iUnion_of_finite (fun Γ => isClosed_faceCarrier K Γ.val))
  have hSmono {n m : ℕ} (hnm : n ≤ m) : S n ⊆ S m := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hx.trans hnm)
  have hSface (n : ℕ) (Γ : Finset (Face D)) (hΓ : Γ ∈ K.faces)
      (hc : Γ.card = n + 1)
      (x : {x : FiniteSimplex Γ // ∃ v : Γ, x.val v = 0}) :
      faceInclusion K Γ hΓ x.val ∈ S n := by
    right
    let y := faceInclusion K Γ hΓ x.val
    have hs : supportFinset K y ⊆ Γ :=
      (mem_faceCarrier_iff_support_subset K Γ y).mp
        (faceInclusion_mem_faceCarrier K Γ hΓ x.val)
    obtain ⟨v, hv⟩ := x.property
    have hn : v.val ∉ supportFinset K y := by
      intro hm
      have hh := (mem_supportFinset_iff K y v.val).mp hm
      exact hh ((faceInclusion_weight_of_mem K Γ hΓ x.val v.val v.property).trans hv)
    have hss : supportFinset K y ⊂ Γ :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hs, by
        intro he
        apply hn
        simpa only [he] using v.property⟩
    have hlt := Finset.card_lt_card hss
    change (supportFinset K y).card ≤ n
    omega
  have hSzero : S 0 = A := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hx
      · change (supportFinset K x).card ≤ 0 at hx
        have hp := Finset.card_pos.mpr (supportFinset_nonempty K x)
        omega
    · exact Or.inl
  let Supported (T : Set (RealizationPoint K)) (f : C(T, Y)) : Prop :=
    ∀ (Γ : Finset (Face D)) (hΓ : Γ ∈ K.faces),
      ∀ σ₀ ∈ Γ, (∀ τ ∈ Γ, σ₀.val ⊆ τ.val) →
        ∀ x : T, x.val ∈ faceCarrier K Γ → f x ∈ fullSupportLocus C (P σ₀)
  have hbase : ∃ f : C(S 0, Y),
      (∀ x : A, f ⟨x.val, Or.inl x.property⟩ = bA x) ∧ Supported (S 0) f := by
    let i : C(S 0, A) := ⟨fun x => ⟨x.val, hSzero ▸ x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
    refine ⟨bA.comp i, fun x => rfl, ?_⟩
    intro Γ hΓ σ₀ hσ₀ hmin x hxΓ
    exact hbA (i x) Γ hΓ σ₀ hσ₀ hmin hxΓ
  have hstep (n : ℕ) (f : C(S n, Y))
      (hfB : ∀ x : A, f ⟨x.val, Or.inl x.property⟩ = bA x)
      (hf : Supported (S n) f) :
      ∃ g : C(S (n + 1), Y),
        (∀ x : A, g ⟨x.val, Or.inl x.property⟩ = bA x) ∧ Supported (S (n + 1)) g := by
    let J := {Γ : Finset (Face D) // Γ ∈ K.faces ∧ Γ.card = n + 1}
    have hcell (Γ : J) :
        ∃ F : C(faceCarrier K Γ.val, Y),
          (∀ x : faceCarrier K Γ.val, ∀ hx : x.val ∈ S n, F x = f ⟨x.val, hx⟩) ∧
          (∀ σ₀ ∈ Γ.val, (∀ τ ∈ Γ.val, σ₀.val ⊆ τ.val) →
            ∀ x, F x ∈ fullSupportLocus C (P σ₀)) := by
      let e := faceCharacteristicHomeomorph K Γ.val Γ.property.1
      obtain ⟨σ₀, hσ₀, hmin⟩ := hleast Γ.val Γ.property.1
      by_cases hQ : ∀ σ ∈ Γ.val, Q σ
      · have hA (x : faceCarrier K Γ.val) : x.val ∈ A := by
          intro σ hσ
          exact x.property σ (fun hm => hσ (hQ σ hm))
        let j : C(faceCarrier K Γ.val, A) :=
          ⟨fun x => ⟨x.val, hA x⟩, continuous_subtype_val.subtype_mk _⟩
        refine ⟨bA.comp j, ?_, ?_⟩
        · intro x hx
          exact (hfB (j x)).symm
        · intro τ hτ hmτ x
          exact hbA (j x) Γ.val Γ.property.1 τ hτ hmτ x.property
      · let T : Set (FiniteSimplex Γ.val) := {x | ∃ v : Γ.val, x.val v = 0}
        let j : C(T, S n) :=
          ⟨fun x => ⟨faceInclusion K Γ.val Γ.property.1 x.val,
            hSface n Γ.val Γ.property.1 Γ.property.2 x⟩,
            ((continuous_faceInclusion K Γ.val Γ.property.1).comp
              continuous_subtype_val).subtype_mk _⟩
        have hs (x : T) : f (j x) ∈ fullSupportLocus C (P σ₀) :=
          hf Γ.val Γ.property.1 σ₀ hσ₀ hmin (j x)
            (faceInclusion_mem_faceCarrier K Γ.val Γ.property.1 x.val)
        let ef := fullSubcomplexHomeomorphSupported C (P σ₀)
        let bg : C(T, RealizationPoint (fullSubcomplex C (P σ₀))) :=
          (⟨ef.symm, ef.symm.continuous⟩ : C(_, _)).comp
            ⟨fun x => ⟨f (j x), hs x⟩, (f.continuous.comp j.continuous).subtype_mk _⟩
        obtain ⟨F, hF⟩ := hsimplex Γ.val Γ.property.1.1 σ₀ bg
        let G : C(faceCarrier K Γ.val, Y) :=
          (⟨fullToAmbient C (P σ₀), fullToAmbient_continuous C (P σ₀)⟩ : C(_, _)).comp
            (F.comp ⟨e.symm, e.symm.continuous⟩)
        have hGeq (x : faceCarrier K Γ.val) (hx : x.val ∈ S n) : G x = f ⟨x.val, hx⟩ := by
          let z := e.symm x
          have he : faceInclusion K Γ.val Γ.property.1 z = x.val := by
            exact congrArg Subtype.val (e.apply_symm_apply x)
          have hz : ∃ v : Γ.val, z.val v = 0 := by
            by_contra hn
            have hzpos : ∀ v : Γ.val, z.val v ≠ 0 := by simpa using hn
            have hall : Γ.val ⊆ supportFinset K x.val := by
              intro σ hσ
              apply (mem_supportFinset_iff K x.val σ).mpr
              rw [← he, faceInclusion_weight_of_mem K Γ.val Γ.property.1 z σ hσ]
              exact hzpos ⟨σ, hσ⟩
            rcases hx with hx | hx
            · apply hQ
              intro σ hσ
              by_contra hs
              exact ((mem_supportFinset_iff K x.val σ).mp (hall hσ)) (hx σ hs)
            · change (supportFinset K x.val).card ≤ n at hx
              have hc := Finset.card_le_card hall
              have hcΓ : Γ.val.card = n + 1 := Γ.property.2
              omega
          change fullToAmbient C (P σ₀) (F z) = f ⟨x.val, hx⟩
          rw [hF ⟨z, hz⟩]
          have hh := fullToAmbient_supportedToFull C (P σ₀) ⟨f (j ⟨z, hz⟩), hs ⟨z, hz⟩⟩
          exact hh.trans (congrArg f (Subtype.ext he))
        refine ⟨G, hGeq, ?_⟩
        intro τ hτ hmτ x
        have heq : τ = σ₀ := by
          apply Subtype.ext
          exact Finset.Subset.antisymm (hmτ σ₀ hσ₀) (hmin τ hτ)
        subst τ
        exact fullToAmbient_mem_supported C (P σ₀) _
    choose F hFold hFsupport using hcell
    let I := Option J
    let SS : I → Set (S (n + 1)) := fun i => match i with
      | none => {x | x.val ∈ S n}
      | some Γ => {x | x.val ∈ faceCarrier K Γ.val}
    have hcover : ⋃ i, SS i = Set.univ := by
      ext x
      constructor
      · intro _; trivial
      · intro _
        by_cases hxn : x.val ∈ S n
        · exact Set.mem_iUnion.mpr ⟨none, hxn⟩
        · have hxA : x.val ∉ A := fun h => hxn (Or.inl h)
          have hcard : (supportFinset K x.val).card ≤ n + 1 :=
            x.property.resolve_left hxA
          have hle : ¬ (supportFinset K x.val).card ≤ n :=
            fun h => hxn (Or.inr h)
          have heq : (supportFinset K x.val).card = n + 1 := by omega
          exact Set.mem_iUnion.mpr ⟨some ⟨supportFinset K x.val,
            supportFinset_mem_faces K x.val, heq⟩,
            (mem_faceCarrier_iff_support_subset K _ x.val).mpr (Finset.Subset.refl _)⟩
    have hclosedSS : ∀ i, IsClosed (SS i) := by
      intro i
      cases i with
      | none => exact (hclosed n).preimage continuous_subtype_val
      | some Γ => exact (isClosed_faceCarrier K Γ.val).preimage continuous_subtype_val
    let φ : ∀ i : I, C(SS i, Y) := fun i => match i with
      | none =>
          ⟨fun x => f ⟨x.val.val, x.property⟩,
            f.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
      | some Γ =>
          ⟨fun x => F Γ ⟨x.val.val, x.property⟩,
            (F Γ).continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)⟩
    have hcompat : ∀ i j (x : S (n+1)) (hxi : x ∈ SS i) (hxj : x ∈ SS j),
        φ i ⟨x, hxi⟩ = φ j ⟨x, hxj⟩ := by
      intro i j x hxi hxj
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some Γ =>
          change f ⟨x.val, hxi⟩ = F Γ ⟨x.val, hxj⟩
          exact (hFold Γ ⟨x.val, hxj⟩ hxi).symm
      | some Γ =>
        cases j with
        | none =>
          change F Γ ⟨x.val, hxi⟩ = f ⟨x.val, hxj⟩
          exact hFold Γ ⟨x.val, hxi⟩ hxj
        | some Δ =>
          by_cases heq : Γ = Δ
          · subst Δ; rfl
          · have hsubΓ : supportFinset K x.val ⊆ Γ.val :=
              (mem_faceCarrier_iff_support_subset K Γ.val x.val).mp hxi
            have hsubΔ : supportFinset K x.val ⊆ Δ.val :=
              (mem_faceCarrier_iff_support_subset K Δ.val x.val).mp hxj
            have hxn : x.val ∈ S n := by
              right
              change (supportFinset K x.val).card ≤ n
              have hcΓ : Γ.val.card = n+1 := Γ.property.2
              have hcΔ : Δ.val.card = n+1 := Δ.property.2
              have hle := Finset.card_le_card hsubΓ
              have hle' : (supportFinset K x.val).card ≤ n+1 := by simpa [hcΓ] using hle
              by_contra hn
              have hc : (supportFinset K x.val).card = n+1 := by omega
              have heΓ : supportFinset K x.val = Γ.val :=
                Finset.eq_of_subset_of_card_le hsubΓ ((hcΓ.trans hc.symm).le)
              have heΔ : supportFinset K x.val = Δ.val :=
                Finset.eq_of_subset_of_card_le hsubΔ ((hcΔ.trans hc.symm).le)
              exact heq (Subtype.ext (heΓ.symm.trans heΔ))
            change F Γ ⟨x.val, hxi⟩ = F Δ ⟨x.val, hxj⟩
            exact (hFold Γ ⟨x.val, hxi⟩ hxn).trans
              (hFold Δ ⟨x.val, hxj⟩ hxn).symm
    let G : S (n+1) → Y := Set.liftCover SS (fun i => φ i) hcompat hcover
    have hcont : ∀ i, ContinuousOn G (SS i) := by
      intro i
      rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (fun x : SS i => G x.val)
      have he : (fun x : SS i => G x.val) = φ i := by
        funext x
        exact Set.liftCover_coe x
      rw [he]
      exact (φ i).continuous
    let g : C(S (n+1), Y) :=
      ⟨G, (locallyFinite_of_finite SS).continuous hcover hclosedSS hcont⟩
    have hg (i : I) (x : S (n+1)) (hx : x ∈ SS i) :
        g x = φ i ⟨x, hx⟩ := by
      change Set.liftCover SS (fun i => φ i) hcompat hcover x = _
      exact Set.liftCover_of_mem hx
    refine ⟨g, ?_, ?_⟩
    · intro x
      exact (hg none ⟨x.val, Or.inl x.property⟩ (Or.inl x.property)).trans (hfB x)
    · intro Γ hΓ σ₀ hσ₀ hmin x hx
      by_cases hxn : x.val ∈ S n
      · rw [hg none x hxn]
        exact hf Γ hΓ σ₀ hσ₀ hmin ⟨x.val, hxn⟩ hx
      · have hxA : x.val ∉ A := fun h => hxn (Or.inl h)
        have hle : (supportFinset K x.val).card ≤ n+1 := x.property.resolve_left hxA
        have hn : ¬ (supportFinset K x.val).card ≤ n := fun h => hxn (Or.inr h)
        have heq : (supportFinset K x.val).card = n+1 := by omega
        let Δ : J := ⟨supportFinset K x.val, supportFinset_mem_faces K x.val, heq⟩
        have hΔx : x.val ∈ faceCarrier K Δ.val :=
          (mem_faceCarrier_iff_support_subset K Δ.val x.val).mpr (Finset.Subset.refl _)
        obtain ⟨τ, hτ, hmτ⟩ := hleast Δ.val Δ.property.1
        have hsub : Δ.val ⊆ Γ := (mem_faceCarrier_iff_support_subset K Γ x.val).mp hx
        rw [hg (some Δ) x hΔx]
        exact hmono σ₀ τ (hmin τ (hsub hτ))
          (hFsupport Δ τ hτ hmτ ⟨x.val, hΔx⟩)
  have hall (n : ℕ) : ∃ f : C(S n, Y),
      (∀ x : A, f ⟨x.val, Or.inl x.property⟩ = bA x) ∧ Supported (S n) f := by
    induction n with
    | zero => exact hbase
    | succ n ih =>
      obtain ⟨f, hfB, hf⟩ := ih
      exact hstep n f hfB hf
  let N := Fintype.card (Face D)
  obtain ⟨g, hgB, hg⟩ := hall N
  have hN (x : RealizationPoint K) : x ∈ S N := by
    right
    exact Finset.card_le_univ _
  let j : C(RealizationPoint K, S N) := ⟨fun x => ⟨x, hN x⟩, continuous_id.subtype_mk _⟩
  refine ⟨g.comp j, ?_, ?_⟩
  · intro x
    have hh := hgB (eA x)
    change g ⟨fullToAmbient K Q x, _⟩ = bA (eA x) at hh
    exact hh.trans (by
      change b (eA.symm (eA x)) = b x
      rw [eA.symm_apply_apply])
  · intro Γ hΓ σ₀ hσ₀ hmin x
    exact hg Γ hΓ σ₀ hσ₀ hmin (j (faceInclusion K Γ hΓ x))
      (faceInclusion_mem_faceCarrier K Γ hΓ x)

end C0RelativeCarrier
