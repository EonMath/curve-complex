import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperStripFromCompactDiagram

open Set Topology Schoenflies
namespace CurveComplex.HyperellipticModel

/-- Convex interpolation of two increasing real homeomorphisms gives a proper
embedding of the closed strip and retains both boundary parametrizations. -/
theorem increasing_real_homeomorphisms_strip_interpolation
    (a b : ℝ ≃ₜ ℝ) (ha : StrictMono a) (hb : StrictMono b) :
    ∃ K : C(ℝ × unitInterval,ℝ × unitInterval), IsClosedEmbedding K ∧
      (∀ s, K (s,0) = (a s,0)) ∧ (∀ s, K (s,1) = (b s,1)) := by
  let k (s : ℝ) (w : unitInterval) := (1-(w:ℝ))*a s + (w:ℝ)*b s
  have hmono (w : unitInterval) : StrictMono (fun s => k s w) := by
    intro s t hst
    have hA := ha hst
    have hB := hb hst
    by_cases hw : (w:ℝ)=1
    · simpa [k,hw] using hB
    have hwpos : 0 < 1-(w:ℝ) := sub_pos.mpr (lt_of_le_of_ne w.property.2 hw)
    have h₁ := mul_pos hwpos (sub_pos.mpr hA)
    have h₂ := mul_nonneg w.property.1 (sub_nonneg.mpr hB.le)
    dsimp [k]
    nlinarith
  let K : C(ℝ × unitInterval,ℝ × unitInterval) :=
    ⟨fun z => (k z.1 z.2,z.2),by dsimp [k];fun_prop⟩
  have hi : Function.Injective K := by
    intro z w he
    change (k z.1 z.2,z.2) = (k w.1 w.2,w.2) at he
    have h₂ := congrArg Prod.snd he
    have h₁ := congrArg Prod.fst he
    apply Prod.ext
    · rw [h₂] at h₁
      exact (hmono w.2).injective h₁
    · exact h₂
  have hp : IsProperMap K := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨K.continuous,?_⟩
    intro C hC
    obtain ⟨L,hL⟩ := (hC.image continuous_fst).bddBelow
    obtain ⟨R,hR⟩ := (hC.image continuous_fst).bddAbove
    let l := min (a.symm (L-1)) (b.symm (L-1))
    let r := max (a.symm (R+1)) (b.symm (R+1))
    have hbound : K ⁻¹' C ⊆ Icc l r ×ˢ (univ : Set unitInterval) := by
      intro z hz
      change K z ∈ C at hz
      have hlow : L ≤ k z.1 z.2 := hL ((show (K z).1 ∈ Prod.fst '' C from mem_image_of_mem Prod.fst hz))
      have hupp : k z.1 z.2 ≤ R := hR ((show (K z).1 ∈ Prod.fst '' C from mem_image_of_mem Prod.fst hz))
      have hw₀ := z.2.property.1
      have hw₁ := z.2.property.2
      refine ⟨⟨?_,?_⟩,mem_univ _⟩
      · by_contra hn
        have hs : z.1 < l := lt_of_not_ge hn
        have hA : a z.1 < L-1 := by
          have hh := ha (hs.trans_le (min_le_left _ _))
          simpa only [Homeomorph.apply_symm_apply] using hh
        have hB : b z.1 < L-1 := by
          have hh := hb (hs.trans_le (min_le_right _ _))
          simpa only [Homeomorph.apply_symm_apply] using hh
        have h₁ := mul_nonneg (sub_nonneg.mpr hw₁) (sub_nonneg.mpr hA.le)
        have h₂ := mul_nonneg hw₀ (sub_nonneg.mpr hB.le)
        dsimp [k] at hlow
        nlinarith
      · by_contra hn
        have hs : r < z.1 := lt_of_not_ge hn
        have hA : R+1 < a z.1 := by
          have hh := ha ((le_max_left _ _).trans_lt hs)
          simpa only [Homeomorph.apply_symm_apply] using hh
        have hB : R+1 < b z.1 := by
          have hh := hb ((le_max_right _ _).trans_lt hs)
          simpa only [Homeomorph.apply_symm_apply] using hh
        have h₁ := mul_nonneg (sub_nonneg.mpr hw₁) (sub_nonneg.mpr hA.le)
        have h₂ := mul_nonneg hw₀ (sub_nonneg.mpr hB.le)
        dsimp [k] at hupp
        nlinarith
    exact (isCompact_Icc.prod isCompact_univ).of_isClosed_subset
      (hC.isClosed.preimage K.continuous) hbound
  refine ⟨K,IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap.mpr
    ⟨K.continuous,hi,hp.isClosedMap⟩,?_,?_⟩
  · intro s; simp [K,k]
  · intro s; simp [K,k]

theorem aligned_real_homeomorphisms_strip_interpolation
    (a b : ℝ ≃ₜ ℝ)
    (haligned : (StrictMono a ∧ StrictMono b) ∨ (StrictAnti a ∧ StrictAnti b)) :
    ∃ K : C(ℝ × unitInterval,ℝ × unitInterval), IsClosedEmbedding K ∧
      (∀ s, K (s,0) = (a s,0)) ∧ (∀ s, K (s,1) = (b s,1)) := by
  rcases haligned with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact increasing_real_homeomorphisms_strip_interpolation a b ha hb
  · let a' := (Homeomorph.neg ℝ).trans a
    let b' := (Homeomorph.neg ℝ).trans b
    have ha' : StrictMono a' := fun s t hst => ha (neg_lt_neg hst)
    have hb' : StrictMono b' := fun s t hst => hb (neg_lt_neg hst)
    obtain ⟨K,hK,hK0,hK1⟩ := increasing_real_homeomorphisms_strip_interpolation a' b' ha' hb'
    let r := (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl unitInterval)
    let K' : C(ℝ × unitInterval,ℝ × unitInterval) := K.comp ⟨r,r.continuous⟩
    refine ⟨K',hK.comp r.isClosedEmbedding,?_,?_⟩
    · intro s
      change K (-s,0) = (a s,0)
      rw [hK0]
      simp [a']
    · intro s
      change K (-s,1) = (b s,1)
      rw [hK1]
      simp [b']

theorem embedded_lines_equal_range_parameter
    (f g : ℝ → Plane) (hf : IsEmbedding f) (hg : IsEmbedding g)
    (hrange : range f = range g) :
    ∃ e : ℝ ≃ₜ ℝ, ∀ s, g (e s) = f s := by
  let e := hf.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans hg.toHomeomorph.symm)
  refine ⟨e,?_⟩
  intro s
  have h := hg.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange) (hf.toHomeomorph s))
  exact congrArg Subtype.val h

/-- A proper embedded pair-strip with literal prescribed boundary maps. Only
the unavoidable reversal of the upper real parameter is permitted. -/
theorem proper_disjoint_lines_prescribed_strip
    (F G : C(ℝ,Plane)) (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (range F) (range G)) :
    ∃ flip : Bool, ∃ H : C(ℝ × unitInterval,Plane), IsClosedEmbedding H ∧
      (∀ s, H (s,0) = F s) ∧
      (∀ s, H (s,1) = G (if flip then -s else s)) := by
  obtain ⟨H,hH,hH0,hH1⟩ := proper_disjoint_lines_range_strip F G hF hG hdis
  have hedge (w : unitInterval) : IsEmbedding (fun s : ℝ => H (s,w)) :=
    hH.isEmbedding.comp (isEmbedding_prodMkLeft w)
  obtain ⟨a,ha⟩ := embedded_lines_equal_range_parameter F (fun s => H (s,0)) hF.isEmbedding
    (hedge 0) hH0.symm
  obtain ⟨b,hb⟩ := embedded_lines_equal_range_parameter G (fun s => H (s,1)) hG.isEmbedding
    (hedge 1) hH1.symm
  have halign : ∃ flip : Bool, ∃ b' : ℝ ≃ₜ ℝ,
      (∀ s, b' s = b (if flip then -s else s)) ∧
      ((StrictMono a ∧ StrictMono b') ∨ (StrictAnti a ∧ StrictAnti b')) := by
    rcases a.continuous.strictMono_of_inj a.injective with ha | ha
    · rcases b.continuous.strictMono_of_inj b.injective with hb | hb
      · exact ⟨false,b,fun _ => rfl,Or.inl ⟨ha,hb⟩⟩
      · exact ⟨true,(Homeomorph.neg ℝ).trans b,fun _ => rfl,
          Or.inl ⟨ha,fun s t hst => hb (neg_lt_neg hst)⟩⟩
    · rcases b.continuous.strictMono_of_inj b.injective with hb | hb
      · exact ⟨true,(Homeomorph.neg ℝ).trans b,fun _ => rfl,
          Or.inr ⟨ha,fun s t hst => hb (neg_lt_neg hst)⟩⟩
      · exact ⟨false,b,fun _ => rfl,Or.inr ⟨ha,hb⟩⟩
  obtain ⟨flip,b',hb',hdir⟩ := halign
  obtain ⟨K,hK,hK0,hK1⟩ := aligned_real_homeomorphisms_strip_interpolation a b' hdir
  refine ⟨flip,H.comp K,hH.comp hK,?_,?_⟩
  · intro s
    change H (K (s,0)) = F s
    rw [hK0,ha]
  · intro s
    change H (K (s,1)) = G (if flip then -s else s)
    rw [hK1,hb',hb]

end CurveComplex.HyperellipticModel
