import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalShiftedSubdisk
import CurveComplexGenusTwo.Topology.ActualFareyClassification.SameFiberSubdisk

open Set Topology Schoenflies

theorem supporting_horizontal_fiber_crosscut_endpoints_on_curve
    (G : C(ℝ,Plane)) (c r s u v : ℝ) (hrs : r<s) (huv : u<v)
    (hr : G r 1=c) (hs : G s 1=c)
    (huC : Plane.mk u c∈(G '' Icc r s) ∪ segment ℝ (G r) (G s))
    (hvC : Plane.mk v c∈(G '' Icc r s) ∪ segment ℝ (G r) (G s))
    (hin : ∀ t∈Ioo u v, Plane.mk t c∈inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    Plane.mk u c∈G '' Icc r s ∧ Plane.mk v c∈G '' Icc r s := by
  let l := min (G r 0) (G s 0)
  let h := max (G r 0) (G s 0)
  have hcoords (z : Plane) (hz : z 1=c) : z=Plane.mk (z 0) c := by
    ext i
    fin_cases i <;> simp [hz]
  have hseg : segment ℝ (G r) (G s)=(fun t : ℝ => Plane.mk t c) '' Icc l h := by
    rw [hcoords (G r) hr,hcoords (G s) hs]
    by_cases hh : G r 0≤G s 0
    · simpa [l,h,min_eq_left hh,max_eq_right hh] using
        (horizontal_fiber_interval_image c (G r 0) (G s 0) hh).symm
    · have hh' : G s 0≤G r 0 := (le_of_not_ge hh)
      rw [segment_symm]
      simpa [l,h,min_eq_right hh',max_eq_left hh'] using
        (horizontal_fiber_interval_image c (G s 0) (G r 0) hh').symm
  have hnone (t : ℝ) (ht : t∈Ioo u v) : t∉Icc l h := by
    intro hh
    apply inside_subset_compl (hin t ht)
    right
    rw [hseg]
    exact ⟨t,hh,rfl⟩
  have hend (w : ℝ) (hw : w=u ∨ w=v)
      (hwC : Plane.mk w c∈(G '' Icc r s) ∪ segment ℝ (G r) (G s)) :
      Plane.mk w c∈G '' Icc r s := by
    rcases hwC with hh | hh
    · exact hh
    rw [hseg] at hh
    obtain ⟨t,ht,he⟩ := hh
    have htw : t=w := by simpa [Plane.mk] using congrArg (fun z : Plane => z 0) he
    subst t
    have hnot : ¬(l<w ∧ w<h) := by
      rintro ⟨hlw,hwh⟩
      rcases hw with hwu | hwv
      · rw [hwu] at hlw hwh
        let z := (u+min v h)/2
        have huz : u<z := by dsimp [z]; linarith [lt_min huv hwh]
        have hzv : z<v := by dsimp [z]; linarith [min_le_left v h]
        have hzl : l≤z := by linarith
        have hzh : z≤h := by dsimp [z]; linarith [min_le_right v h]
        exact hnone z ⟨huz,hzv⟩ ⟨hzl,hzh⟩
      · rw [hwv] at hlw hwh
        let z := (max u l+v)/2
        have huz : u<z := by dsimp [z]; linarith [le_max_left u l]
        have hzv : z<v := by dsimp [z]; linarith [max_lt huv hlw]
        have hzl : l≤z := by dsimp [z]; linarith [le_max_right u l]
        have hzh : z≤h := by linarith
        exact hnone z ⟨huz,hzv⟩ ⟨hzl,hzh⟩
    have hew : w=l ∨ w=h := by
      rcases le_iff_lt_or_eq.mp ht.1 with hh|hh
      · exact Or.inr (le_antisymm ht.2 (le_of_not_gt (fun hw => hnot ⟨hh,hw⟩)))
      · exact Or.inl hh.symm
    have hwends : w=G r 0 ∨ w=G s 0 := by
      rcases hew with hew|hew
      · by_cases hh : G r 0≤G s 0
        · exact Or.inl (hew.trans (min_eq_left hh))
        · exact Or.inr (hew.trans (min_eq_right (le_of_not_ge hh)))
      · by_cases hh : G r 0≤G s 0
        · exact Or.inr (hew.trans (max_eq_right hh))
        · exact Or.inl (hew.trans (max_eq_left (le_of_not_ge hh)))
    rcases hwends with hew|hew
    · exact ⟨r,⟨le_rfl, hrs.le⟩,by
        rw [hew]; exact hcoords (G r) hr⟩
    · exact ⟨s,⟨hrs.le,le_rfl⟩,by
        rw [hew]; exact hcoords (G s) hs⟩
  exact ⟨hend u (Or.inl rfl) huC,hend v (Or.inr rfl) hvC⟩

theorem supporting_horizontal_fiber_entering_empty_bigon_has_actual_subdisk
    (G : C(ℝ,Plane)) (hG : IsClosedEmbedding G) (c r s : ℝ)
    (hrs : r<s) (hr : G r 1=c) (hs : G s 1=c)
    (hC : IsJordanCurve ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))
    (hempty : Disjoint (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) (range G))
    (t : ℝ) (ht : Plane.mk t c ∈ inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s))) :
    ∃ a b : ℝ, r ≤ a ∧ a<b ∧ b ≤ s ∧ G a 1=c ∧ G b 1=c ∧
      IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ∧
      (((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ⊆
        closure (inside ((G '' Icc r s) ∪ segment ℝ (G r) (G s)))) ∧
      (∃ p ∈ ({G r,G s} : Set Plane), p ∉ ((G '' Icc a b) ∪ segment ℝ (G a) (G b))) := by
  let C := (G '' Icc r s) ∪ segment ℝ (G r) (G s)
  let F : C(ℝ,Plane) := ⟨fun u => Plane.mk u c, by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop⟩
  obtain ⟨u,v,hut,htv,huC,hvC,hin,hArc⟩ :=
    proper_line_entering_jordan_has_interval_crosscut F (horizontal_fiber_isClosedEmbedding c) C hC t ht
  have huv : u<v := hut.trans htv
  obtain ⟨huG,hvG⟩ := supporting_horizontal_fiber_crosscut_endpoints_on_curve G c r s u v hrs huv hr hs huC hvC hin
  have hend (w : ℝ) (hw : F w ∈ G '' Icc r s) : ∃ a ∈ Icc r s, G a=F w := hw
  obtain ⟨a,ha,hea⟩ := hend u huG
  obtain ⟨b,hb,heb⟩ := hend v hvG
  have hne : a≠b := by
    intro he
    have hh : F u=F v := hea.symm.trans (he ▸ heb)
    exact (ne_of_lt huv) ((horizontal_fiber_isClosedEmbedding c).injective hh)
  have hSeg : ∀ z ∈ segment ℝ (G a) (G b), z=G a ∨ z=G b ∨ z∈inside C := by
    intro z hz
    rw [hea,heb] at hz
    change z ∈ segment ℝ (Plane.mk u c) (Plane.mk v c) at hz
    rw [← horizontal_fiber_interval_image c u v huv.le] at hz
    obtain ⟨w,hw,rfl⟩ := hz
    by_cases hwu : w=u
    · left
      simpa only [hwu,F,ContinuousMap.coe_mk] using hea.symm
    by_cases hwv : w=v
    · right; left
      simpa only [hwv,F,ContinuousMap.coe_mk] using heb.symm
    · right; right
      exact hin w ⟨lt_of_le_of_ne hw.1 (Ne.symm hwu),lt_of_le_of_ne hw.2 hwv⟩
  have hCcl : C ⊆ closure (inside C) := by
    have hh : frontier (inside C)=C := (jordan_curve_theorem hC).frontier_inside
    intro z hz
    exact frontier_subset_closure (hh.symm ▸ hz)
  have build (a b : ℝ) (ha : a∈Icc r s) (hb : b∈Icc r s)
      (hab : a<b) (ha0 : G a 1=c) (hb0 : G b 1=c)
      (hSeg : ∀ z ∈ segment ℝ (G a) (G b), z=G a ∨ z=G b ∨ z∈inside C) :
      IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ∧
      ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) ⊆ closure (inside C) ∧
      (∃ p ∈ ({G r,G s} : Set Plane), p ∉ ((G '' Icc a b) ∪ segment ℝ (G a) (G b))) := by
    have hJ : IsJordanCurve ((G '' Icc a b) ∪ segment ℝ (G a) (G b)) := by
      apply isJordanCurve_union (continuous_injective_interval_isArcBetween G hG.injective hab)
        (isArcBetween_segment (fun he => (ne_of_lt hab) (hG.injective he)))
      intro z hz hzS
      rcases hSeg z hzS with hh | hh | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact False.elim (disjoint_left.mp hempty hh (image_subset_range G _ hz))
    refine ⟨hJ,?_,?_⟩
    · intro z hz
      rcases hz with ⟨w,hw,rfl⟩ | hz
      · exact hCcl (Or.inl ⟨w,⟨ha.1.trans hw.1,hw.2.trans hb.2⟩,rfl⟩)
      · rcases hSeg z hz with hh | hh | hh
        · rw [hh]; exact hCcl (Or.inl ⟨a,⟨ha.1,ha.2⟩,rfl⟩)
        · rw [hh]; exact hCcl (Or.inl ⟨b,⟨hb.1,hb.2⟩,rfl⟩)
        · exact subset_closure hh
    · exact fiber_crosscut_subinterval_omits_old_corner G hG.injective r s a b hrs ha hb hab hSeg
  have ha0 : G a 1=c := by rw [hea]; rfl
  have hb0 : G b 1=c := by rw [heb]; rfl
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨hJ,hcl,hcorner⟩ := build a b ha hb hab ha0 hb0 hSeg
    exact ⟨a,b,ha.1,hab,hb.2,ha0,hb0,hJ,hcl,hcorner⟩
  · have hSeg' : ∀ z ∈ segment ℝ (G b) (G a), z=G b ∨ z=G a ∨ z∈inside C := by
      intro z hz
      rw [segment_symm] at hz
      rcases hSeg z hz with hh | hh | hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inl hh
      · exact Or.inr (Or.inr hh)
    obtain ⟨hJ,hcl,hcorner⟩ := build b a hb ha hba hb0 ha0 hSeg'
    exact ⟨b,a,hb.1,hba,ha.2,hb0,ha0,hJ,hcl,hcorner⟩



#print axioms supporting_horizontal_fiber_entering_empty_bigon_has_actual_subdisk
