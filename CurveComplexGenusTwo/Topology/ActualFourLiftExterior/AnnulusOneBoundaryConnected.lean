import CurveComplexGenusTwo.Dictionary.ActualCircle24Components

namespace CurveComplex.HyperellipticModel
open Set Topology

theorem annulus_except_zero_boundary_connected
    {E : Type} [TopologicalSpace E] (A : Set E)
    (F : Circle × Interval ≃ₜ A) :
    IsConnected (A \ Set.range (fun z : Circle => (F (z,0)).val)) := by
  let T : Set (Circle × Interval) := Set.univ ×ˢ Set.Ioc (0:Interval) 1
  have hT : IsConnected T :=
    isConnected_univ.prod (isConnected_Ioc (by norm_num : (0:Interval) < 1))
  have hImage : (fun p : Circle × Interval => (F p).val) '' T =
      A \ Set.range (fun z : Circle => (F (z,0)).val) := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,⟨_,ht0,ht1⟩,rfl⟩
      refine ⟨(F (z,t)).property,?_⟩
      rintro ⟨w,hw⟩
      have he : (w,(0:Interval)) = (z,t) := F.injective (Subtype.ext hw)
      have ht := congrArg Prod.snd he
      rw [← ht] at ht0
      exact (lt_irrefl _) ht0
    · rintro ⟨hxA,hxNot⟩
      obtain ⟨p,hp⟩ := F.surjective ⟨x,hxA⟩
      rcases p with ⟨z,t⟩
      have ht0 : (0:Interval) < t := by
        have hne : t ≠ 0 := by
          intro ht
          apply hxNot
          exact ⟨z,by simpa only [ht] using congrArg Subtype.val hp⟩
        exact lt_of_le_of_ne (bot_le : (0:Interval) ≤ t) (Ne.symm hne)
      exact ⟨(z,t),⟨Set.mem_univ _,⟨ht0,t.property.2⟩⟩,
        congrArg Subtype.val hp⟩
  rw [← hImage]
  exact hT.image _ (continuous_subtype_val.comp F.continuous).continuousOn

theorem annulus_except_one_boundary_connected
    {E : Type} [TopologicalSpace E] (A : Set E)
    (F : Circle × Interval ≃ₜ A) :
    IsConnected (A \ Set.range (fun z : Circle => (F (z,1)).val)) := by
  let T : Set (Circle × Interval) := Set.univ ×ˢ Set.Ico (0:Interval) 1
  have hT : IsConnected T :=
    isConnected_univ.prod (isConnected_Ico (by norm_num : (0:Interval) < 1))
  have hImage : (fun p : Circle × Interval => (F p).val) '' T =
      A \ Set.range (fun z : Circle => (F (z,1)).val) := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩,⟨_,ht0,ht1⟩,rfl⟩
      refine ⟨(F (z,t)).property,?_⟩
      rintro ⟨w,hw⟩
      have he : (w,(1:Interval)) = (z,t) := F.injective (Subtype.ext hw)
      have ht := congrArg Prod.snd he
      rw [← ht] at ht1
      exact (lt_irrefl _) ht1
    · rintro ⟨hxA,hxNot⟩
      obtain ⟨p,hp⟩ := F.surjective ⟨x,hxA⟩
      rcases p with ⟨z,t⟩
      have ht1 : t < (1:Interval) := by
        have hne : t ≠ 1 := by
          intro ht
          apply hxNot
          exact ⟨z,by simpa only [ht] using congrArg Subtype.val hp⟩
        exact lt_of_le_of_ne t.property.2 hne
      exact ⟨(z,t),⟨Set.mem_univ _,⟨t.property.1,ht1⟩⟩,
        congrArg Subtype.val hp⟩
  rw [← hImage]
  exact hT.image _ (continuous_subtype_val.comp F.continuous).continuousOn

end CurveComplex.HyperellipticModel
