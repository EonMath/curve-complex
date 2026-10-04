import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalBoundarySimultaneousCompressionSourceLocal

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
set_option maxHeartbeats 3000000

-- This local consumer is instantiated only with the actual transition derived
-- from the two supplied annuli; its openness comes from actual ambient embedding.
example (G : C(Circle × Interval,Circle × Interval))
    (hG : Topology.IsEmbedding G) (r : Circle ≃ₜ Circle)
    (hcore : ∀ z, G (z,⟨1/2,by norm_num⟩) = (r z,⟨1/2,by norm_num⟩))
    (hopen : IsOpen (G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1))) :
    ((∀ z (u : Interval), (u:ℝ) < 1/2 → ((G (z,u)).2:ℝ) < 1/2) ∧
      (∀ z (u : Interval), 1/2 < (u:ℝ) → 1/2 < ((G (z,u)).2:ℝ))) ∨
    ((∀ z (u : Interval), (u:ℝ) < 1/2 → 1/2 < ((G (z,u)).2:ℝ)) ∧
      (∀ z (u : Interval), 1/2 < (u:ℝ) → ((G (z,u)).2:ℝ) < 1/2)) := by
  audit_main14_base3
    let c : Interval := ⟨1/2,by norm_num⟩
    let L := G '' (Set.univ ×ˢ Set.Iio c)
    let R := G '' (Set.univ ×ˢ Set.Ioi c)
    let O := G '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
    let Vlo : Set (Circle × Interval) := {p | p.2 < c}
    let Vhi : Set (Circle × Interval) := {p | c < p.2}
    have hLconn : IsPreconnected L := by
      letI : ConnectedSpace (Set.Ico (0:ℝ) (1/2)) :=
        Subtype.connectedSpace (isConnected_Ico (by norm_num : (0:ℝ) < 1/2))
      let f : Circle × Set.Ico (0:ℝ) (1/2) → Circle × Interval := fun p =>
        (p.1,⟨p.2.val,⟨p.2.property.1,p.2.property.2.le.trans (by norm_num)⟩⟩)
      have hf : Continuous f := by dsimp [f]; fun_prop
      have hr : Set.range (G ∘ f) = L := by
        ext p
        constructor
        · rintro ⟨⟨z,u⟩,rfl⟩
          exact ⟨f (z,u),⟨Set.mem_univ _,u.property.2⟩,rfl⟩
        · rintro ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩
          exact ⟨(z,⟨u.val,⟨u.property.1,hu⟩⟩),rfl⟩
      rw [← hr]
      exact (isConnected_range (G.continuous.comp hf)).isPreconnected
    have hRconn : IsPreconnected R := by
      letI : ConnectedSpace (Set.Ioc (1/2:ℝ) 1) :=
        Subtype.connectedSpace (isConnected_Ioc (by norm_num : (1/2:ℝ) < 1))
      let f : Circle × Set.Ioc (1/2:ℝ) 1 → Circle × Interval := fun p =>
        (p.1,⟨p.2.val,⟨(by norm_num : (0:ℝ) ≤ 1/2).trans p.2.property.1.le,p.2.property.2⟩⟩)
      have hf : Continuous f := by dsimp [f]; fun_prop
      have hr : Set.range (G ∘ f) = R := by
        ext p
        constructor
        · rintro ⟨⟨z,u⟩,rfl⟩
          exact ⟨f (z,u),⟨Set.mem_univ _,u.property.1⟩,rfl⟩
        · rintro ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩
          exact ⟨(z,⟨u.val,⟨hu,u.property.2⟩⟩),rfl⟩
      rw [← hr]
      exact (isConnected_range (G.continuous.comp hf)).isPreconnected
    have havoid (z : Circle) (u : Interval) (hu : u ≠ c) : (G (z,u)).2 ≠ c := by
      intro he
      let w := r.symm (G (z,u)).1
      have hg : G (w,c) = G (z,u) := by
        rw [hcore]
        exact Prod.ext (r.apply_symm_apply _) he.symm
      exact hu (congrArg Prod.snd (hG.injective hg)).symm
    have hsub (D : Set (Circle × Interval))
        (hD : ∀ p ∈ D, p.2 ≠ c) : D ⊆ Vlo ∪ Vhi := by
      intro p hp
      exact lt_or_gt_of_ne (hD p hp)
    have hdis : Disjoint Vlo Vhi := by
      apply Set.disjoint_left.mpr
      intro p hp hq
      change p.2 < c at hp
      change c < p.2 at hq
      exact lt_asymm hp hq
    have hld : L ⊆ Vlo ∨ L ⊆ Vhi :=
      IsPreconnected.subset_or_subset (isOpen_Iio.preimage continuous_snd)
        (isOpen_Ioi.preimage continuous_snd)
        hdis
        (hsub L (by rintro _ ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩; exact havoid z u hu.ne)) hLconn
    have hrd : R ⊆ Vlo ∨ R ⊆ Vhi :=
      IsPreconnected.subset_or_subset (isOpen_Iio.preimage continuous_snd)
        (isOpen_Ioi.preimage continuous_snd)
        hdis
        (hsub R (by rintro _ ⟨⟨z,u⟩,⟨_,hu⟩,rfl⟩; exact havoid z u hu.ne')) hRconn
    have hmid : (r 1,c) ∈ O := ⟨(1,c),⟨Set.mem_univ _,by change (0:ℝ) < 1/2 ∧ (1/2:ℝ) < 1; norm_num⟩,hcore 1⟩
    have hnotlo : ¬ (L ⊆ Vlo ∧ R ⊆ Vlo) := by
      rintro ⟨hl,hr⟩
      have hO : ∀ p ∈ O, p.2 ≤ c := by
        rintro _ ⟨⟨z,u⟩,hu,rfl⟩
        rcases lt_trichotomy u c with hh | hh | hh
        · exact (hl ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
        · rw [hh,hcore]
        · exact (hr ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
      have hc : (r 1,c) ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo c 1) := by
        rw [closure_prod_eq,closure_univ,closure_Ioo (show c ≠ 1 by intro hh; have hv := congrArg Subtype.val hh; norm_num [c] at hv)]
        exact ⟨Set.mem_univ _,le_rfl,by change (1/2:ℝ) ≤ 1; norm_num⟩
      obtain ⟨p,hpO,hp⟩ := mem_closure_iff.mp hc O hopen hmid
      exact not_lt_of_ge (hO p hpO) hp.2.1
    have hnothi : ¬ (L ⊆ Vhi ∧ R ⊆ Vhi) := by
      rintro ⟨hl,hr⟩
      have hO : ∀ p ∈ O, c ≤ p.2 := by
        rintro _ ⟨⟨z,u⟩,hu,rfl⟩
        rcases lt_trichotomy u c with hh | hh | hh
        · exact (hl ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
        · rw [hh,hcore]
        · exact (hr ⟨(z,u),⟨Set.mem_univ _,hh⟩,rfl⟩).le
      have hc : (r 1,c) ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo 0 c) := by
        rw [closure_prod_eq,closure_univ,closure_Ioo (show (0:Interval) ≠ c by intro hh; have hv := congrArg Subtype.val hh; norm_num [c] at hv)]
        exact ⟨Set.mem_univ _,by change (0:ℝ) ≤ 1/2; norm_num,le_rfl⟩
      obtain ⟨p,hpO,hp⟩ := mem_closure_iff.mp hc O hopen hmid
      exact not_lt_of_ge (hO p hpO) hp.2.2
    rcases hld with hl | hl <;> rcases hrd with hr | hr
    · exact False.elim (hnotlo ⟨hl,hr⟩)
    · exact Or.inl ⟨fun z u hu => hl ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩,
        fun z u hu => hr ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩⟩
    · exact Or.inr ⟨fun z u hu => hl ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩,
        fun z u hu => hr ⟨(z,u),⟨Set.mem_univ _,hu⟩,rfl⟩⟩
    · exact False.elim (hnothi ⟨hl,hr⟩)

end CurveComplex.HyperellipticModel
