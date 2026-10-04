import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalPeriodicInteriorReturn
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalCompactOrbitEvents
import CurveComplexGenusTwo.Topology.ActualFareyClassification.InnermostFiberBigon

open Set Topology Schoenflies CurveComplex

theorem horizontal_fiber_free_interval_actual_jordan_candidate
    (G : C(ℝ,Plane)) (hinj : Function.Injective G) (c r s : ℝ)
    (hrs : r < s) (hr : G r 1=c) (hs : G s 1=c)
    (hno : ∀ u ∈ Ioo r s, G u 1 ≠ c) :
    IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) := by
  have hA := continuous_injective_interval_isArcBetween G hinj hrs
  have hB := isArcBetween_segment (fun he => (ne_of_lt hrs) (hinj he))
  have hsegment : ∀ z ∈ segment ℝ (G r) (G s), z 1=c := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change t*(G s 1-G r 1)+G r 1=c
    rw [hr,hs]
    ring
  apply isJordanCurve_union hA hB
  rintro z ⟨u,hu,rfl⟩ hz
  by_cases hur : u=r
  · exact Or.inl (congrArg G hur)
  by_cases hus : u=s
  · exact Or.inr (congrArg G hus)
  exact False.elim (hno u ⟨lt_of_le_of_ne hu.1 (Ne.symm hur),
    lt_of_le_of_ne hu.2 hus⟩ (hsegment _ hz))


/-- Positive actual quotient contact count produces a short genuine Jordan bigon.
No second contact, shortness, or Jordan certificate is an input. -/
theorem actual_horizontal_positive_count_has_short_jordan_bigon
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (T c : ℝ) (hT : 0<T)
    (hp : ∀ (k : ℤ) (x : ℝ), G (x+(k:ℝ)*T)=G x+Plane.mk ((k:ℝ)*T) 0)
    (hc : ∀ (x y : ℝ) (a b : ℤ), G x=G y+Plane.mk ((a:ℝ)*T) ((b:ℝ)*T) → b=0)
    (hfinite : {t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.Finite)
    (hcount : 0<{t : Ico 0 (0+T) | ∃ i : ℤ, G t.val 1=c+(i:ℝ)*T}.ncard)
    (htrans : ∀ (q : Plane) (i : ℤ),
      q∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) → q 1=c+(i:ℝ)*T →
      ∃ (U : Set Plane) (V : Set (ℝ×ℝ)) (hqU : q∈U) (h : U ≃ₜ V),
        IsOpen U ∧ IsOpen V ∧ ((h ⟨q,hqU⟩ : V) : ℝ×ℝ)=(0,0) ∧
        (∀ z (hz : z∈U),
          (z 1=c+(i:ℝ)*T ↔ ((h ⟨z,hz⟩ : V) : ℝ×ℝ).1=0) ∧
          (z∈(⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T))) ↔
            ((h ⟨z,hz⟩ : V) : ℝ×ℝ).2=0)))
    : ∃ (i : ℤ) (r s : ℝ), r<s ∧ s<r+T ∧
      G r 1=c+(i:ℝ)*T ∧ G s 1=c+(i:ℝ)*T ∧
      (∀ u∈Ioo r s, G u 1≠c+(i:ℝ)*T) ∧
      IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)) := by
  obtain ⟨r,hr⟩ := (Set.ncard_pos hfinite).mp hcount
  obtain ⟨i,hi⟩ := hr
  have hrFamily : G r.val∈⋃ j : ℤ, range (fun x : ℝ => G x+Plane.mk 0 ((j:ℝ)*T)) := by
    refine mem_iUnion.mpr ⟨0,r.val,?_⟩
    ext q
    fin_cases q <;> simp [Plane.mk]
  obtain ⟨U,V,hUq,h,hU,hV,hZero,hAxes⟩ := htrans (G r.val) i hrFamily hi
  obtain ⟨v,hv,hvContact⟩ := actual_horizontal_periodic_transverse_contact_has_interior_return
    G hG T (c+(i:ℝ)*T) r.val hT hp hc hi U V hUq h hU hV hZero hAxes
  let F : Set ℝ := {u | u∈Ioc r.val v ∧ G u 1=c+(i:ℝ)*T}
  have hF : F.Finite := (actual_horizontal_fiber_contacts_finite_on_compact_interval
    G hG.injective T c r.val v i hT hp hfinite).subset (by
      intro u hu
      exact ⟨⟨hu.1.1.le,hu.1.2⟩,hu.2⟩)
  obtain ⟨s,hs,hmin⟩ := Set.exists_min_image F id hF ⟨v,⟨hv.1,le_rfl⟩,hvContact⟩
  have hrs : r.val<s := hs.1.1
  have hno : ∀ u∈Ioo r.val s, G u 1≠c+(i:ℝ)*T := by
    intro u hu he
    have huF : u∈F := ⟨⟨hu.1,hu.2.le.trans hs.1.2⟩,he⟩
    exact not_le_of_gt hu.2 (hmin u huF)
  exact ⟨i,r.val,s,hrs,hs.1.2.trans_lt hv.2,hi,hs.2,hno,
    horizontal_fiber_free_interval_actual_jordan_candidate G hG.injective
      (c+(i:ℝ)*T) r.val s hrs hi hs.2 hno⟩

#print axioms horizontal_fiber_free_interval_actual_jordan_candidate
#print axioms actual_horizontal_positive_count_has_short_jordan_bigon
