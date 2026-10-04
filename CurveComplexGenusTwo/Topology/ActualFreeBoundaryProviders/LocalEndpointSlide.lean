import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.GraphRelativeFreeBoundaryPosition

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies

theorem signed_interval_width_homeomorph :
    ∃ k : Interval ≃ₜ Icc (-1:ℝ) 1, ∀ t, (k t).val = 2*(t:ℝ)-1 := by
  let f : Interval → Icc (-1:ℝ) 1 :=
    fun t => ⟨2*(t:ℝ)-1,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have hfc : Continuous f := by dsimp [f]; fun_prop
  have hi : Function.Injective f := by
    intro s t he
    apply Subtype.ext
    have he := congrArg Subtype.val he
    dsimp [f] at he
    linarith
  have hs : Function.Surjective f := by
    intro w
    refine ⟨⟨(w.val+1)/2,by constructor <;> linarith [w.property.1,w.property.2]⟩,
      Subtype.ext ?_⟩
    dsimp [f]
    ring
  let k := hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hi,hs⟩)
  exact ⟨k,fun _ => rfl⟩

/-- Normalize the checked signed collar for the existing supported rail
motion, retaining its actual center and whole carrier. -/
theorem signed_strip_normalize_with_center
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (b : C(Interval,X))
    (E : C(Interval × Icc (-1:ℝ) 1,X)) (hE : IsEmbedding E)
    (hcenter : ∀ s, E (s,⟨0,by norm_num⟩) = b s)
    (hend : ∀ w, E (0,w) ∈ B ∧ E (1,w) ∈ B)
    (hint : ∀ s ∈ Ioo (0:Interval) 1, ∀ w, E (s,w) ∉ B)
    (hopen : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1})) :
    ∃ D : C(Interval × Interval,X), ∃ p : Interval,
      IsEmbedding D ∧ p ∈ Ioo (0:Interval) 1 ∧
      (∀ s, D (s,p) = b s) ∧
      (∀ z, D z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      IsOpen (D '' {z | z.2 ∈ Ioo (0:Interval) 1}) ∧ range D = range E := by
  obtain ⟨k,hk⟩ := signed_interval_width_homeomorph
  let r := (Homeomorph.refl Interval).prodCongr k
  let D : C(Interval × Interval,X) := ⟨E ∘ r,E.continuous.comp r.continuous⟩
  have hD : IsEmbedding D := hE.comp r.isEmbedding
  let p : Interval := ⟨1/2,by constructor <;> norm_num⟩
  have hp : p ∈ Ioo (0:Interval) 1 := by
    change (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1
    norm_num
  have hkp : k p = (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1) :=
    Subtype.ext (by rw [hk]; change 2*(1/2:ℝ)-1 = 0; norm_num)
  have hcenterD (s : Interval) : D (s,p) = b s := by
    change E (s,k p) = b s
    rw [hkp,hcenter]
  have hDB (z : Interval × Interval) : D z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
    change E (z.1,k z.2) ∈ B ↔ _
    constructor
    · intro hz
      by_cases h0 : z.1 = 0
      · exact Or.inl h0
      · have h1 : z.1 = 1 := by
          apply le_antisymm le_top
          exact le_of_not_gt (fun h1 =>
            hint z.1 ⟨bot_lt_iff_ne_bot.mpr h0,h1⟩ _ hz)
        exact Or.inr h1
    · rintro (hz | hz)
      · simpa only [hz] using (hend (k z.2)).1
      · simpa only [hz] using (hend (k z.2)).2
  have hwidth (t : Interval) : -1 < (k t).val ∧ (k t).val < 1 ↔
      t ∈ Ioo (0:Interval) 1 := by
    rw [hk]
    change (-1 < 2*(t:ℝ)-1 ∧ 2*(t:ℝ)-1 < 1) ↔ (0 < (t:ℝ) ∧ (t:ℝ) < 1)
    constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith
  have himage : D '' {z | z.2 ∈ Ioo (0:Interval) 1} =
      E '' {z | -1 < z.2.val ∧ z.2.val < 1} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨r z,(hwidth z.2).mpr hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      refine ⟨r.symm z,?_,?_⟩
      · apply (hwidth _).mp
        change -1 < (k (k.symm z.2)).val ∧ (k (k.symm z.2)).val < 1
        rw [k.apply_symm_apply]
        exact hz
      · change E (r (r.symm z)) = E z
        rw [r.apply_symm_apply]
  refine ⟨D,p,hD,hp,hcenterD,hDB,by rw [himage]; exact hopen,?_⟩
  change range (E ∘ r) = range E
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨r z,rfl⟩
  · rintro ⟨z,rfl⟩
    exact ⟨r.symm z,congrArg E (r.apply_symm_apply z)⟩

/-- A local supported rail slide avoids every point in a finite forbidden
set at both boundary endpoints. No global boundary rotation is necessary. -/
theorem strip_rail_endpoint_slide_avoiding_finite_set
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B : Set X) (D : C(Interval × Interval,X)) (hD : IsEmbedding D)
    (hopen : IsOpen (D '' {z | z.2 ∈ Ioo (0:Interval) 1}))
    (hB : ∀ z, D z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (p : Interval) (hp : p ∈ Ioo (0:Interval) 1)
    (A : Set X) (hA : A.Finite) :
    ∃ w : Interval, ∃ H : AmbientIsotopy X,
      w ∈ Ioo (0:Interval) 1 ∧ D (0,w) ∉ A ∧ D (1,w) ∉ A ∧
      (∀ t, (fun y => H.map (t,y)) '' B = B) ∧
      (∀ s, H.finalMap (D (s,p)) = D (s,w)) ∧
      (∀ t y, y ∉ range D → H.map (t,y) = y) := by
  have hi (t : Interval) : Function.Injective (fun w : Interval => D (t,w)) := by
    intro w v he
    exact congrArg Prod.snd (hD.injective he)
  have hbad : ((fun w : Interval => D (0,w)) ⁻¹' A ∪
      (fun w : Interval => D (1,w)) ⁻¹' A).Finite :=
    (hA.preimage (hi 0).injOn).union (hA.preimage (hi 1).injOn)
  have hinf : (Ioo (0:Interval) 1).Infinite := Set.Ioo_infinite (by norm_num)
  obtain ⟨w,hw,hwnot⟩ := hinf.exists_notMem_finite hbad
  obtain ⟨H,hHB,hHmove,hHfix⟩ := embedded_strip_rail_ambient_motion B D hD hopen hB p w hp hw
  exact ⟨w,H,hw,(fun h => hwnot (Or.inl h)),(fun h => hwnot (Or.inr h)),hHB,hHmove,
    fun t y hy => hHfix t y (fun h => hy (Set.image_subset_range D _ h))⟩

end CoherentEndpointMotion
