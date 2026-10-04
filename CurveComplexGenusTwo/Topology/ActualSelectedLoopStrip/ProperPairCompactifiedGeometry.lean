import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperLineFacingSides
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperLineConnector
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.TangentJordanHalfRegions

open Set Metric Topology Schoenflies Bornology
namespace CurveComplexGenusTwo.Topology.PuncturedTorusCandidate

/-- Choosing the inversion pole in the opposite side makes the specified
facing side exactly the bounded Jordan interior after inversion. -/
theorem proper_line_inversion_facing_side
    (F : C(ℝ,Plane)) (hF : IsClosedEmbedding F)
    (Uin Uout : Set Plane) (hinOpen : IsOpen Uin) (houtOpen : IsOpen Uout)
    (houtConn : IsConnected Uout)
    (hgivenDisj : Disjoint Uin Uout) (hgivenPart : Uin ∪ Uout = (range F)ᶜ)
    (a : Plane) (haOut : a ∈ Uout) :
    invert a '' Uin = inside (insert a (invert a '' range F)) := by
  classical
  let L := Set.range F
  have ha : a ∉ L := by
    have hx : a ∈ Uin ∪ Uout := Or.inr haOut
    rw [hgivenPart] at hx
    exact hx
  have ha : a ∉ L := by
    change a ∈ (range F)ᶜ
    rw [← hgivenPart]
    exact Or.inr haOut
  have hJ := proper_line_inversion_isJordanCurve F hF.isProperMap hF.injective a ha
  let C := insert a (invert a '' L)
  have hsep : IsSeparating C := jordan_curve_theorem hJ
  have haC : a ∈ C := Set.mem_insert a _
  have hain : a ∉ inside C := fun h => h.1 haC
  have haout : a ∉ outside C := fun h => h.1 haC
  let U := invert a '' inside C
  let V := invert a '' outside C ∪ {a}
  have hUopen : IsOpen U := isOpen_invert_image hsep.isOpen_inside hain
  have houtc : outside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show z ≠ a from fun h => haout (h ▸ hz))
  have hinc : inside C ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show z ≠ a from fun h => hain (h ▸ hz))
  have hUconn : IsConnected U :=
    hsep.isConnected_inside.image _ ((continuousOn_invert a).mono hinc)
  obtain ⟨R, hR, hRout⟩ := exists_radius_compl_closedBall_subset_outside hsep a
  have hTopen : IsOpen (invert a '' outside C) :=
    isOpen_invert_image hsep.isOpen_outside haout
  have hVball : ball a R⁻¹ ⊆ V := by
    intro z hz
    rcases eq_or_ne z a with rfl | hza
    · exact Or.inr rfl
    · refine Or.inl ⟨invert a z, hRout ?_, invert_invert a z⟩
      have hpos : 0 < dist z a := dist_pos.2 hza
      rw [mem_compl_iff, mem_closedBall, dist_invert_center]
      exact not_le.2 (lt_inv_of_lt_inv₀ hpos (mem_ball.1 hz))
  have hVopen : IsOpen V := by
    have hrw : V = invert a '' outside C ∪ ball a R⁻¹ := by
      refine Subset.antisymm (union_subset subset_union_left ?_)
        (union_subset subset_union_left hVball)
      rintro z rfl
      exact Or.inr (mem_ball_self (by positivity))
    rw [hrw]
    exact hTopen.union isOpen_ball
  have hacl : a ∈ closure (invert a '' outside C) := by
    rw [Metric.mem_closure_iff]
    intro e he
    obtain ⟨z, hzout, hzfar⟩ : ∃ z ∈ outside C, e⁻¹ < dist z a := by
      by_contra hcon
      push Not at hcon
      exact hsep.not_isBounded_outside
        ((isBounded_iff_subset_closedBall a).2 ⟨e⁻¹, fun z hz => hcon z hz⟩)
    refine ⟨invert a z, ⟨z, hzout, rfl⟩, ?_⟩
    rw [dist_comm, dist_invert_center]
    exact inv_lt_of_inv_lt₀ he hzfar
  have hVconn : IsConnected V := by
    refine ⟨⟨a, Or.inr rfl⟩, ?_⟩
    exact (hsep.isConnected_outside.image _
      ((continuousOn_invert a).mono houtc)).isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (by rintro z rfl; exact hacl))
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ (⟨y, hy, he⟩ | he)
    · have he' := invert_injective a he
      exact Set.disjoint_left.mp disjoint_inside_outside hx (he' ▸ hy)
    · exact hain ((invert_eq_center_iff.mp he) ▸ hx)
  have hinv (z : Plane) : invert a z ∈ C ↔ z = a ∨ z ∈ L := by
    dsimp [C]
    simp only [mem_insert_iff, invert_eq_center_iff]
    rw [Set.mem_image]
    constructor
    · rintro (h | ⟨x, hx, he⟩)
      · exact Or.inl h
      · exact Or.inr ((invert_injective a he) ▸ hx)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨z, h, rfl⟩
  have hpart : U ∪ V = Lᶜ := by
    ext z
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩ | rfl)
      · intro hz
        have := (hinv (invert a x)).mpr (Or.inr hz)
        rw [invert_invert] at this
        exact hx.1 this
      · intro hz
        have := (hinv (invert a x)).mpr (Or.inr hz)
        rw [invert_invert] at this
        exact hx.1 this
      · exact ha
    · intro hz
      by_cases hza : z = a
      · exact Or.inr (Or.inr hza)
      · have hzC : invert a z ∉ C := by simpa [hinv, hza] using hz
        have hzside : invert a z ∈ inside C ∪ outside C := by
          rwa [inside_union_outside]
        rcases hzside with hu | hv
        · exact Or.inl ⟨invert a z, hu, invert_invert a z⟩
        · exact Or.inr (Or.inl ⟨invert a z, hv, invert_invert a z⟩)
  have hOutCover : Uout ⊆ U ∪ V := by
    intro z hz
    rw [hpart]
    exact hgivenPart ▸ Or.inr hz
  have hUoutSubsetV : Uout ⊆ V := by
    rcases houtConn.isPreconnected.subset_or_subset hUopen hVopen hdis hOutCover with hh | hh
    · exact False.elim (notMem_invert_image hain (hh haOut))
    · exact hh
  have hVsubOut : V ⊆ Uout := by
    have hVCover : V ⊆ Uin ∪ Uout := by
      intro z hz
      rw [hgivenPart]
      exact hpart ▸ Or.inr hz
    rcases hVconn.isPreconnected.subset_or_subset hinOpen houtOpen hgivenDisj hVCover with hh | hh
    · exact False.elim (Set.disjoint_left.mp hgivenDisj (hh (Or.inr rfl)) haOut)
    · exact hh
  have hUeq : U = Uin := by
    ext z
    constructor
    · intro hz
      have hh : z ∈ Uin ∪ Uout := hgivenPart.symm ▸ (hpart ▸ Or.inl hz)
      exact hh.resolve_right (fun hh => Set.disjoint_left.mp hdis hz (hUoutSubsetV hh))
    · intro hz
      have hh : z ∈ U ∪ V := hpart.symm ▸ (hgivenPart ▸ Or.inl hz)
      exact hh.resolve_right (fun hh => Set.disjoint_left.mp hgivenDisj hz (hVsubOut hh))
  calc
    invert a '' Uin = invert a '' U := by rw [hUeq]
    _ = inside C := by
      dsimp [U]
      rw [image_image]
      simp only [invert_invert, image_id']

/-- The outer side of one of two disjoint proper boundaries lies in the
facing side of the other boundary. -/
theorem proper_pair_outer_side_contained_in_facing
    {K L U Uout V Vout : Set Plane}
    (hK : K.Nonempty) (hUout : IsConnected Uout)
    (hV : IsOpen V) (hVout : IsOpen Vout)
    (hUUout : Disjoint U Uout) (hVVout : Disjoint V Vout)
    (hpart : V ∪ Vout = Lᶜ) (hfront : frontier Uout = K)
    (hLU : L ⊆ U) (hKV : K ⊆ V) : Uout ⊆ V := by
  have hcover : Uout ⊆ V ∪ Vout := by
    rw [hpart]
    intro z hz hzL
    exact disjoint_left.mp hUUout (hLU hzL) hz
  rcases hUout.isPreconnected.subset_or_subset hV hVout hVVout hcover with h | h
  · exact h
  · obtain ⟨z,hz⟩ := hK
    have hzcl : z ∈ closure Vout := closure_mono h (frontier_subset_closure (hfront.symm ▸ hz))
    exact False.elim (disjoint_left.mp (hVVout.closure_right hV) (hKV hz) hzcl)

/-- Compactification at an actual exterior pole turns the two arbitrary
proper lines into nested tangent Jordan curves, retaining an actual connector. -/
theorem proper_disjoint_lines_nested_tangent_connector
    (F G : C(ℝ,Plane)) (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (range F) (range G)) :
    ∃ (a : Plane) (s t : ℝ),
      a ∉ range F ∧ a ∉ range G ∧
      let C := insert a (invert a '' range F)
      let D := insert a (invert a '' range G)
      let P := invert a '' segment ℝ (F s) (G t)
      IsJordanCurve C ∧ IsJordanCurve D ∧
      IsArcBetween P (invert a (F s)) (invert a (G t)) ∧
      C ∩ D = {a} ∧ P ∩ C = {invert a (F s)} ∧ P ∩ D = {invert a (G t)} ∧
      D \ {a} ⊆ inside C ∧ P \ {invert a (F s)} ⊆ inside C ∧
      (∀ u v : ℝ, (∀ w ∈ Ioo (0:ℝ) 1,
        AffineMap.lineMap (F u) (G v) w ∉ range F ∪ range G) →
        ∀ w ∈ Icc (0:ℝ) 1,
          AffineMap.lineMap (F u) (G v) w ≠ a ∧
          invert a (AffineMap.lineMap (F u) (G v) w) ∈ C ∪ D ∪ (inside C \ inside D)) := by
  obtain ⟨U,Uout,V,Vout,hU,hUout,hV,hVout,hUc,hUoutc,hVc,hVoutc,
      hdU,hdV,hpartU,hpartV,hfU,hfUout,hfV,hfVout,hGU,hFV⟩ :=
    proper_disjoint_lines_choose_facing_sides F G hF hG hdis
  obtain ⟨a,ha⟩ := hUoutc.nonempty
  have haF : a ∉ range F := by
    change a ∈ (range F)ᶜ
    rw [← hpartU]
    exact Or.inr ha
  have haG : a ∉ range G := fun h => disjoint_left.mp hdU (hGU h) ha
  have hin : invert a '' U = inside (insert a (invert a '' range F)) :=
    proper_line_inversion_facing_side F hF U Uout hU hUout hUoutc hdU hpartU a ha
  obtain ⟨s,t,hst,hfree⟩ := proper_disjoint_lines_have_straight_connector F G hF hG hdis
  let f : ℝ → Plane := AffineMap.lineMap (F s) (G t)
  have hf0 : f 0 = F s := by simp [f]
  have hf1 : f 1 = G t := by simp [f]
  have hseg : segment ℝ (F s) (G t) = f '' Icc 0 1 := by
    exact segment_eq_image_lineMap ℝ (F s) (G t)
  have hfin (u : ℝ) (hu : u ∈ Ioo (0:ℝ) 1) : f u ∈ U ∩ V :=
    straight_connector_in_facing_sides (range F) (range G) U Uout V Vout hdis
      hU hUout hV hVout hdU hdV hpartU hpartV hGU hFV (F s) (G t)
      (mem_range_self s) (mem_range_self t) hfree u hu
  have hsegpole : segment ℝ (F s) (G t) ⊆ ({a}ᶜ : Set Plane) := by
    rw [hseg]
    rintro z ⟨u,hu,rfl⟩ he
    have hea : f u = a := he
    by_cases hu0 : u=0
    · exact haF ⟨s,by simpa only [hu0,hf0] using hea⟩
    by_cases hu1 : u=1
    · exact haG ⟨t,by simpa only [hu1,hf1] using hea⟩
    exact disjoint_left.mp hdU ((hfin u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),
      lt_of_le_of_ne hu.2 hu1⟩).1) (hea.symm ▸ ha)
  have hPC : segment ℝ (F s) (G t) ∩ range F = {F s} := by
    ext z
    constructor
    · rintro ⟨hz,hzF⟩
      obtain ⟨u,hu,rfl⟩ := hseg ▸ hz
      by_cases hu0 : u=0
      · simp only [hu0,hf0,mem_singleton_iff]
      by_cases hu1 : u=1
      · exact False.elim (disjoint_left.mp hdis (by simpa only [hu1,hf1] using hzF) (mem_range_self t))
      exact False.elim (hfree u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),lt_of_le_of_ne hu.2 hu1⟩ (Or.inl hzF))
    · rintro rfl
      exact ⟨left_mem_segment ℝ _ _,mem_range_self s⟩
  have hPD : segment ℝ (F s) (G t) ∩ range G = {G t} := by
    ext z
    constructor
    · rintro ⟨hz,hzG⟩
      obtain ⟨u,hu,rfl⟩ := hseg ▸ hz
      by_cases hu1 : u=1
      · simp only [hu1,hf1,mem_singleton_iff]
      by_cases hu0 : u=0
      · exact False.elim (disjoint_left.mp hdis (mem_range_self s) (by simpa only [hu0,hf0] using hzG))
      exact False.elim (hfree u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),lt_of_le_of_ne hu.2 hu1⟩ (Or.inr hzG))
    · rintro rfl
      exact ⟨right_mem_segment ℝ _ _,mem_range_self t⟩
  have invert_meet (L : Set Plane) (z : Plane)
      (hL : segment ℝ (F s) (G t) ∩ L = {z}) :
      (invert a '' segment ℝ (F s) (G t)) ∩ insert a (invert a '' L) = {invert a z} := by
    ext w
    constructor
    · rintro ⟨⟨v,hv,rfl⟩,hw⟩
      rcases hw with he | ⟨v',hv',he⟩
      · exact False.elim (hsegpole hv (invert_eq_center_iff.mp he))
      · have heq := invert_injective a he
        have hvz : v = z := mem_singleton_iff.mp (hL ▸ ⟨hv,heq ▸ hv'⟩)
        simp only [hvz,mem_singleton_iff]
    · rintro rfl
      have hz : z ∈ segment ℝ (F s) (G t) ∩ L := hL.symm ▸ mem_singleton z
      exact ⟨mem_image_of_mem _ hz.1,Or.inr (mem_image_of_mem _ hz.2)⟩
  refine ⟨a,s,t,haF,haG,
    proper_line_inversion_isJordanCurve F hF.isProperMap hF.injective a haF,
    proper_line_inversion_isJordanCurve G hG.isProperMap hG.injective a haG,
    (isArcBetween_segment hst).image_of_injOn hsegpole (continuousOn_invert a)
      (invert_injective a).injOn,?_,invert_meet _ _ hPC,invert_meet _ _ hPD,?_,?_,?_⟩
  · ext z
    constructor
    · rintro ⟨hzF | ⟨u,hu,rfl⟩,hzG | ⟨v,hv,he⟩⟩
      · exact hzF
      · exact hzF
      · exact hzG
      · exact False.elim (disjoint_left.mp hdis hu ((invert_injective a he) ▸ hv))
    · rintro rfl
      exact ⟨mem_insert _ _,mem_insert _ _⟩
  · rintro z ⟨hz,hne⟩
    rcases hz with rfl | ⟨v,hv,rfl⟩
    · exact False.elim (hne rfl)
    · exact hin ▸ mem_image_of_mem (invert a) (hGU hv)
  · rintro z ⟨⟨v,hv,rfl⟩,hne⟩
    obtain ⟨u,hu,rfl⟩ := hseg ▸ hv
    have hu0 : u ≠ 0 := by
      intro he
      exact hne (by simp only [he,hf0,mem_singleton_iff])
    have huU : f u ∈ U := by
      by_cases hu1 : u=1
      · simpa only [hu1,hf1] using hGU (mem_range_self t)
      · exact (hfin u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),lt_of_le_of_ne hu.2 hu1⟩).1
    exact hin ▸ mem_image_of_mem (invert a) huU

  · intro u v hfree' w hw
    by_cases hw0 : w=0
    · subst w
      simp only [AffineMap.lineMap_apply_zero]
      exact ⟨fun he => haF ⟨u,he⟩,Or.inl (Or.inl (Or.inr ⟨F u,mem_range_self u,rfl⟩))⟩
    by_cases hw1 : w=1
    · subst w
      simp only [AffineMap.lineMap_apply_one]
      exact ⟨fun he => haG ⟨v,he⟩,Or.inl (Or.inr (Or.inr ⟨G v,mem_range_self v,rfl⟩))⟩
    have hw' : w ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hw.1 (Ne.symm hw0),lt_of_le_of_ne hw.2 hw1⟩
    have hz := straight_connector_in_facing_sides (range F) (range G) U Uout V Vout hdis
      hU hUout hV hVout hdU hdV hpartU hpartV hGU hFV (F u) (G v)
      (mem_range_self u) (mem_range_self v) hfree' w hw'
    have haV : a ∈ V := proper_pair_outer_side_contained_in_facing (range_nonempty F)
      hUoutc hV hVout hdU hdV hpartV hfUout hGU hFV ha
    have hDin : invert a '' Vout = inside (insert a (invert a '' range G)) :=
      proper_line_inversion_facing_side G hG Vout V hVout hV hVc hdV.symm
        (by simpa only [union_comm] using hpartV) a haV
    refine ⟨fun he => disjoint_left.mp hdU hz.1 (he.symm ▸ ha),Or.inr ⟨?_,?_⟩⟩
    · exact hin ▸ mem_image_of_mem (invert a) hz.1
    · intro hi
      obtain ⟨q,hq,he⟩ := hDin.symm ▸ hi
      exact disjoint_left.mp hdV hz.2 ((invert_injective a he) ▸ hq)

end CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
