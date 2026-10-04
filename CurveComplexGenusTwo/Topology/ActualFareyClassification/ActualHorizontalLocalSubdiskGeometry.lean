import CurveComplexGenusTwo.Topology.ActualFareyClassification.PeriodicSpatialMinimum

open Set Topology Schoenflies

theorem jordan_inside_avoids_supporting_horizontal_fiber
    (C : Set Plane) (hC : IsJordanCurve C) (c : ℝ)
    (hside : (∀ z ∈ C, z 1 ≤ c) ∨ (∀ z ∈ C, c ≤ z 1)) :
    ∀ z ∈ inside C, z 1 ≠ c := by
  intro z hz hzc
  let q : ℝ → Plane := fun u => z+Plane.mk 0 u
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hqzero : q 0=z := by
    ext i
    fin_cases i <;> simp [q,Plane.mk]
  have hpre : q ⁻¹' inside C ∈ 𝓝 (0:ℝ) :=
    ((jordan_curve_theorem hC).isOpen_inside.preimage hq).mem_nhds (by
      change q 0 ∈ inside C
      rw [hqzero]
      exact hz)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hpre
  rcases hside with hupper | hlower
  · have hu : ε/2 ∈ Metric.ball (0:ℝ) ε := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith
    have hin := hball hu
    have hb := jordan_coordinate_upper_bound hC 1 c hupper _ (subset_closure hin)
    change z 1+ε/2 ≤ c at hb
    linarith
  · have hu : -ε/2 ∈ Metric.ball (0:ℝ) ε := by
      rw [Metric.mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith
    have hin := hball hu
    have hb := jordan_coordinate_lower_bound hC 1 c hlower _ (subset_closure hin)
    change c ≤ z 1+(-ε/2) at hb
    linarith

theorem horizontal_fiber_free_interval_bigon_inside_avoids_fiber
    (G : C(ℝ,Plane)) (c r s : ℝ)
    (hr : G r 1=c) (hs : G s 1=c)
    (hno : ∀ t ∈ Ioo r s, G t 1 ≠ c)
    (hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    ∀ z ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)), z 1 ≠ c := by
  let f : ℝ → ℝ := fun u => G u 1
  have hf : Continuous f := by dsimp [f]; fun_prop
  let S : Set ℝ := f '' Ioo r s
  have hconn : IsPreconnected S := isPreconnected_Ioo.image f hf.continuousOn
  have hpart : S ⊆ Iio c ∪ Ioi c := by
    rintro z ⟨t,ht,rfl⟩
    exact lt_or_gt_of_ne (hno t ht)
  have hdis : Disjoint (Iio c) (Ioi c) := disjoint_left.mpr (by
    intro u hu hv
    exact lt_asymm (show u<c from hu) (show c<u from hv))
  have hsign := hconn.subset_or_subset isOpen_Iio isOpen_Ioi hdis hpart
  have hsegment : ∀ z ∈ segment ℝ (G r) (G s), z 1=c := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    simp only [AffineMap.lineMap_apply]
    change t*(G s 1-G r 1)+G r 1=c
    rw [hr,hs]
    ring
  apply jordan_inside_avoids_supporting_horizontal_fiber _ hC c
  have hendpoint (t : ℝ) (ht : t ∈ Icc r s) :
      t=r ∨ t=s ∨ t ∈ Ioo r s := by
    by_cases htr : t=r
    · exact Or.inl htr
    by_cases hts : t=s
    · exact Or.inr (Or.inl hts)
    exact Or.inr (Or.inr ⟨lt_of_le_of_ne ht.1 (Ne.symm htr),lt_of_le_of_ne ht.2 hts⟩)
  rcases hsign with hleft | hright
  · left
    rintro z (⟨t,ht,rfl⟩ | hz)
    · rcases hendpoint t ht with he | he | hi
      · simp [he,hr]
      · simp [he,hs]
      · exact (hleft (mem_image_of_mem _ hi)).le
    · exact (hsegment z hz).le
  · right
    rintro z (⟨t,ht,rfl⟩ | hz)
    · rcases hendpoint t ht with he | he | hi
      · simp [he,hr]
      · simp [he,hs]
      · exact (hright (mem_image_of_mem _ hi)).le
    · exact (hsegment z hz).ge

theorem horizontal_segment_endpoint_extreme
    (p q u v : Plane) (hvertical : p 1=q 1)
    (hu : u ∈ segment ℝ p q) (hv : v ∈ segment ℝ p q)
    (hp : p ∈ segment ℝ u v) : u=p ∨ v=p := by
  have coord (i : Fin 2) {a b z : Plane} (hz : z ∈ segment ℝ a b) :
      z i ∈ segment ℝ (a i) (b i) := by
    have hh := mem_image_of_mem (EuclideanSpace.proj i).toAffineMap hz
    rwa [image_segment] at hh
  have hu0 : u 1=p 1 := by
    have hh := coord 1 hu
    rw [← hvertical,segment_same] at hh
    exact hh
  have hv0 : v 1=p 1 := by
    have hh := coord 1 hv
    rw [← hvertical,segment_same] at hh
    exact hh
  have hh := endpoint_of_nested_real_segment (p 0) (q 0) (u 0) (v 0)
    (coord 0 hu) (coord 0 hv) (coord 0 hp)
  rcases hh with hh | hh
  · left
    ext i
    fin_cases i
    · exact hh
    · exact hu0
  · right
    ext i
    fin_cases i
    · exact hh
    · exact hv0

theorem horizontal_spatial_contacts_strict_subsegment
    (E : Set Plane) (p q u v : Plane)
    (hfinite : (E ∩ segment ℝ p q).Finite)
    (hp : p ∈ E) (hq : q ∈ E) (hpq : p ≠ q)
    (hvertical : p 1=q 1)
    (hu : u ∈ segment ℝ p q) (hv : v ∈ segment ℝ p q)
    (hnot : ¬ (u=p ∧ v=q)) (hnot' : ¬ (u=q ∧ v=p)) :
    (E ∩ segment ℝ u v).ncard < (E ∩ segment ℝ p q).ncard := by
  have hsub : E ∩ segment ℝ u v ⊆ E ∩ segment ℝ p q := by
    intro z hz
    exact ⟨hz.1,(convex_segment (𝕜:=ℝ) p q).segment_subset hu hv hz.2⟩
  have hn : ¬ (p ∈ segment ℝ u v ∧ q ∈ segment ℝ u v) := by
    rintro ⟨hpp,hqq⟩
    have ha := horizontal_segment_endpoint_extreme p q u v hvertical hu hv hpp
    have hb := horizontal_segment_endpoint_extreme q p u v hvertical.symm
      (by rwa [segment_symm]) (by rwa [segment_symm]) hqq
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hpq (ha.symm.trans hb)
    · exact hnot ⟨ha,hb⟩
    · exact hnot' ⟨hb,ha⟩
    · exact hpq (ha.symm.trans hb)
  apply ncard_lt_ncard _ hfinite
  apply ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro he
  apply hn
  have hpp : p ∈ E ∩ segment ℝ p q := ⟨hp,left_mem_segment ℝ _ _⟩
  have hqq : q ∈ E ∩ segment ℝ p q := ⟨hq,right_mem_segment ℝ _ _⟩
  rw [← he] at hpp hqq
  exact ⟨hpp.2,hqq.2⟩


#print axioms horizontal_spatial_contacts_strict_subsegment
#print axioms horizontal_fiber_free_interval_bigon_inside_avoids_fiber
