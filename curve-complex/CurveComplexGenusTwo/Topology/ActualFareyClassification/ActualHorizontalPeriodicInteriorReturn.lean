import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalFamilyNoHalfplaneTouch
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTerminalReturningParameters

open Set Topology Schoenflies CurveComplex

/-- A genuine transverse horizontal contact of a zero-normal-drift periodic
source has ANOTHER contact strictly inside one period. It cannot be the lone
periodic endpoint event. No finite-fold or second-contact certificate. -/
theorem actual_horizontal_periodic_transverse_contact_has_interior_return
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T d r : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) x, G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (i j : ℤ), G x=G y+Plane.mk ((i:ℝ)*T) ((j:ℝ)*T) → j=0)
    (hContact : G r 1=d)
    (U : Set Plane) (V : Set (ℝ×ℝ)) (hrU : G r∈U) (h : U ≃ₜ V)
    (hU : IsOpen U) (hV : IsOpen V)
    (hrZero : ((h ⟨G r,hrU⟩ : V) : ℝ×ℝ)=(0,0))
    (hAxes : ∀ z (hz : z∈U),
      (z 1=d ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
      (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
        ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)) :
    ∃ s∈Ioo r (r+T), G s 1=d := by
  by_contra hNo
  push Not at hNo
  have hcont : Continuous (fun x : ℝ => G x 1) := by fun_prop
  have hPre : IsPreconnected ((fun x : ℝ => G x 1) '' Ioo r (r+T)) :=
    isPreconnected_Ioo.image _ hcont.continuousOn
  have hCover : ((fun x : ℝ => G x 1) '' Ioo r (r+T))⊆Iio d∪Ioi d := by
    rintro y ⟨x,hx,rfl⟩
    exact lt_or_gt_of_ne (hNo x hx)
  have hSides := hPre.subset_or_subset isOpen_Iio isOpen_Ioi
    (Set.disjoint_left.mpr (by
      intro y hy hz
      change y<d at hy
      change d<y at hz
      exact lt_asymm hy hz)) hCover
  have hGlobal : (∀ x, G x 1≤d) ∨ (∀ x, d≤G x 1) := by
    rcases hSides with hLower | hUpper
    · left
      intro x
      obtain ⟨k,t,ht,hxt⟩ := actual_parameter_has_fundamental_window T r x hT
      have hVal : G x 1=G t 1 := by
        rw [hxt,hp]
        change G t 1+0=G t 1
        ring
      rw [hVal]
      by_cases htr : t=r
      · rw [htr,hContact]
      · exact (hLower ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm htr),ht.2⟩,rfl⟩).le
    · right
      intro x
      obtain ⟨k,t,ht,hxt⟩ := actual_parameter_has_fundamental_window T r x hT
      have hVal : G x 1=G t 1 := by
        rw [hxt,hp]
        change G t 1+0=G t 1
        ring
      rw [hVal]
      by_cases htr : t=r
      · rw [htr,hContact]
      · exact (hUpper ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm htr),ht.2⟩,rfl⟩).le
  have hside : (∀ x∈Icc (r-T) (r+T), G x 1≤d) ∨
      (∀ x∈Icc (r-T) (r+T), d≤G x 1) := by
    rcases hGlobal with hl | hu
    · exact Or.inl (fun x _ => hl x)
    · exact Or.inr (fun x _ => hu x)
  exact actual_horizontal_transverse_family_no_internal_halfplane_touch
    G hG T (r-T) (r+T) r d hT hp hc (by constructor <;> linarith)
    hContact hside U V hrU h hU hV hrZero hAxes

#print axioms actual_horizontal_periodic_transverse_contact_has_interior_return
