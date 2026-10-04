import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedCollarUpperSquareParameterKernelRecovery
namespace CurveComplex.LocalSurgery
open Set Topology
open scoped unitInterval

theorem actualLowerMarkedTailCentralBandOnlyMeetAtSeamContact
    (r : ℝ) (hr : 0<r) (P : unitInterval → ℝ × ℝ)
    (hP : ∀ t,(P t).2=r*t.val)
    (B : Set (ℝ × ℝ)) (hB : ∀ z∈B,r≤z.2) (hend : P 1∈B) :
    range P∩B={P 1} := by
  ext z
  constructor
  · rintro ⟨⟨t,rfl⟩,ht⟩
    have hb := hB (P t) ht
    rw [hP] at hb
    have ht₁ : t=1 := by
      apply Subtype.ext
      change t.val=1
      have hlo : 1≤t.val := by
        by_contra! ht
        have hs : r*t.val<r := by simpa using mul_lt_mul_of_pos_left ht hr
        exact (not_lt_of_ge hb) hs
      exact le_antisymm t.property.2 hlo
    subst t
    exact mem_singleton _
  · intro hz
    have he := mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨1,rfl⟩,hend⟩

theorem actualUpperMarkedTailCentralBandOnlyMeetAtSeamContact
    (r : ℝ) (hr : 0<r) (P : unitInterval → ℝ × ℝ)
    (hP : ∀ t,(P t).2=1-r*t.val)
    (B : Set (ℝ × ℝ)) (hB : ∀ z∈B,z.2≤1-r) (hend : P 1∈B) :
    range P∩B={P 1} := by
  ext z
  constructor
  · rintro ⟨⟨t,rfl⟩,ht⟩
    have hb := hB (P t) ht
    rw [hP] at hb
    have ht₁ : t=1 := by
      apply Subtype.ext
      change t.val=1
      have hm : r≤r*t.val := by linarith only [hb]
      have hlo : 1≤t.val := by
        by_contra! ht
        have hs : r*t.val<r := by simpa using mul_lt_mul_of_pos_left ht hr
        exact (not_lt_of_ge hm) hs
      exact le_antisymm t.property.2 hlo
    subst t
    exact mem_singleton _
  · intro hz
    have he := mem_singleton_iff.mp hz
    subst z
    exact ⟨⟨1,rfl⟩,hend⟩

theorem actualMarkedTailCentralDrawingLowerAttachment
    (φ : C(unitInterval,unitInterval)) (hφ : StrictMono φ)
    (P : unitInterval → ℝ × ℝ) (hr : 0<(φ 0).val)
    (hP : ∀ t,(P t).2=(φ 0).val*t.val)
    (A : Set (unitInterval × unitInterval))
    (hend : P 1∈(fun z : unitInterval × unitInterval => (z.1.val,(φ z.2).val)) '' A) :
    range P∩(fun z : unitInterval × unitInterval => (z.1.val,(φ z.2).val)) '' A={P 1} := by
  apply actualLowerMarkedTailCentralBandOnlyMeetAtSeamContact (φ 0).val hr P hP _ _ hend
  rintro z ⟨w,hw,rfl⟩
  exact hφ.monotone w.2.property.1

theorem actualMarkedTailCentralDrawingUpperAttachment
    (φ : C(unitInterval,unitInterval)) (hφ : StrictMono φ)
    (P : unitInterval → ℝ × ℝ) (hq : (φ 1).val<1)
    (hP : ∀ t,(P t).2=1-(1-(φ 1).val)*t.val)
    (A : Set (unitInterval × unitInterval))
    (hend : P 1∈(fun z : unitInterval × unitInterval => (z.1.val,(φ z.2).val)) '' A) :
    range P∩(fun z : unitInterval × unitInterval => (z.1.val,(φ z.2).val)) '' A={P 1} := by
  apply actualUpperMarkedTailCentralBandOnlyMeetAtSeamContact (1-(φ 1).val)
    (sub_pos.mpr hq) P hP _ _ hend
  rintro z ⟨w,hw,rfl⟩
  have he : 1-(1-(φ 1).val)=(φ 1).val := by ring
  rw [he]
  exact hφ.monotone w.2.property.2
end CurveComplex.LocalSurgery
