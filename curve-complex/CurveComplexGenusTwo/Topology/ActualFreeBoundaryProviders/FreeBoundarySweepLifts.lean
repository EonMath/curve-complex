import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryContactFacts
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.BoundaryAmbientTransport

namespace CoherentEndpointMotion.FreeBoundaryContactRepair
open CurveComplex Set Topology Schoenflies RegionalEmbeddedFamily

/-- Lift the SAME free-boundary ambient sweep through a cover of its actual
codomain. The final arc is reparameterized by the homeomorphism induced by
its whole-image equality; both moving endpoint tracks stay over B. -/
theorem free_boundary_ambient_sweep_lifts
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : Y → X) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (B : Set X) (a b : C(Interval,X)) (ha : IsEmbedding a) (hb : IsEmbedding b)
    (hends : a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B)
    (hproper : ∀ t ∈ Ioo (0 : Interval) 1, a t ∉ B ∧ b t ∉ B)
    (H : AmbientIsotopy X)
    (hHB : ∀ t, (fun y => H.map (t,y)) '' B = B)
    (hHa : H.finalMap '' range a = range b) :
    ∃ (ρ : Interval ≃ₜ Interval) (A D : C(Interval,Y))
        (W : C(Interval × Interval,Y)),
      ((ρ 0 = 0 ∧ ρ 1 = 1) ∨ (ρ 0 = 1 ∧ ρ 1 = 0)) ∧
      (∀ s, p (A s) = a s) ∧ (∀ s, p (D s) = b s) ∧
      (∀ s, W (0,s) = A s) ∧ (∀ s, W (1,s) = D (ρ s)) ∧
      (∀ t, IsEmbedding (fun s => W (t,s))) ∧
      (∀ t s, p (W (t,s)) = H.map (t,a s)) ∧
      (∀ t s, p (W (t,s)) ∈ B ↔ s = 0 ∨ s = 1) := by
  classical
  let V : C(Interval × Interval,X) :=
    ⟨fun z => H.map (z.1,a z.2),
      H.map.continuous.comp (continuous_fst.prodMk (a.continuous.comp continuous_snd))⟩
  have hVzero (s : Interval) : V (0,s) = a s := H.at_zero (a s)
  have hVembedded (t : Interval) : IsEmbedding (fun s => V (t,s)) := by
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have hfun : (fun s => V (t,s)) = e ∘ a := by
      funext s
      exact (he (a s)).symm
    rw [hfun]
    exact e.isEmbedding.comp ha
  have haBoundary (s : Interval) : a s ∈ B ↔ s = 0 ∨ s = 1 := by
    constructor
    · intro hs
      by_cases h0 : s = 0
      · exact Or.inl h0
      by_cases h1 : s = 1
      · exact Or.inr h1
      exact False.elim ((hproper s ⟨lt_of_le_of_ne s.property.1 (Ne.symm h0),
        lt_of_le_of_ne s.property.2 h1⟩).1 hs)
    · rintro (rfl | rfl)
      · exact hends.1
      · exact hends.2.1
  have hbBoundary (s : Interval) : b s ∈ B ↔ s = 0 ∨ s = 1 := by
    constructor
    · intro hs
      by_cases h0 : s = 0
      · exact Or.inl h0
      by_cases h1 : s = 1
      · exact Or.inr h1
      exact False.elim ((hproper s ⟨lt_of_le_of_ne s.property.1 (Ne.symm h0),
        lt_of_le_of_ne s.property.2 h1⟩).2 hs)
    · rintro (rfl | rfl)
      · exact hends.2.2.1
      · exact hends.2.2.2
  have hVBoundary (t s : Interval) : V (t,s) ∈ B ↔ s = 0 ∨ s = 1 := by
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have heB : e '' B = B := by
      have hefun : (e : X → X) = fun y => H.map (t,y) := funext he
      rw [hefun]
      exact hHB t
    change H.map (t,a s) ∈ B ↔ _
    rw [← he]
    exact (boundary_preserving_homeomorph_mem B e heB (a s)).trans (haBoundary s)
  let v₁ : C(Interval,X) :=
    ⟨fun s => V (1,s),V.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hv₁ : IsEmbedding v₁ := hVembedded 1
  have hv₁range : range v₁ = range b := by
    change range (H.finalMap ∘ a) = range b
    rw [Set.range_comp]
    exact hHa
  let ρ : Interval ≃ₜ Interval :=
    hv₁.toHomeomorph.trans ((Homeomorph.setCongr hv₁range).trans hb.toHomeomorph.symm)
  have hρ (s : Interval) : b (ρ s) = V (1,s) := by
    have he := hb.toHomeomorph.apply_symm_apply
      ((Homeomorph.setCongr hv₁range) (hv₁.toHomeomorph s))
    exact congrArg Subtype.val he
  have hρends : (ρ 0 = 0 ∧ ρ 1 = 1) ∨ (ρ 0 = 1 ∧ ρ 1 = 0) := by
    have h0 : ρ 0 = 0 ∨ ρ 0 = 1 := (hbBoundary (ρ 0)).mp (by
      rw [hρ]
      exact (hVBoundary 1 0).mpr (Or.inl rfl))
    have h1 : ρ 1 = 0 ∨ ρ 1 = 1 := (hbBoundary (ρ 1)).mp (by
      rw [hρ]
      exact (hVBoundary 1 1).mpr (Or.inr rfl))
    have hne : ρ 0 ≠ ρ 1 := ρ.injective.ne (by norm_num)
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
    · exact False.elim (hne (h0.trans h1.symm))
    · exact Or.inl ⟨h0,h1⟩
    · exact Or.inr ⟨h0,h1⟩
    · exact False.elim (hne (h0.trans h1.symm))
  let : ContractibleSpace Interval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
  let : LocallyPathConnectedSpace Interval := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨y,hy⟩ := hsurj (a 0)
  obtain ⟨W,⟨_,hWp⟩,_⟩ := hp.existsUnique_continuousMap_lifts V (0,0) y
    (hy.trans (hVzero 0).symm)
  have hproj (t s : Interval) : p (W (t,s)) = V (t,s) := congrFun hWp (t,s)
  let A : C(Interval,Y) := ⟨fun s => W (0,s),by fun_prop⟩
  let D : C(Interval,Y) := ⟨fun s => W (1,ρ.symm s),by fun_prop⟩
  refine ⟨ρ,A,D,W,hρends,?_,?_,fun _ => rfl,?_,?_,?_,?_⟩
  · intro s
    exact (hproj 0 s).trans (hVzero s)
  · intro s
    exact (hproj 1 (ρ.symm s)).trans ((hρ (ρ.symm s)).symm.trans
      (congrArg b (ρ.apply_symm_apply s)))
  · intro s
    change W (1,s) = W (1,ρ.symm (ρ s))
    rw [ρ.symm_apply_apply]
  · intro t
    apply IsEmbedding.of_comp (show Continuous (fun s => W (t,s)) by fun_prop) hp.continuous
    have he : p ∘ (fun s => W (t,s)) = fun s => V (t,s) := funext (hproj t)
    rw [he]
    exact hVembedded t
  · exact hproj
  · intro t s
    rw [hproj]
    exact hVBoundary t s

end CoherentEndpointMotion.FreeBoundaryContactRepair
