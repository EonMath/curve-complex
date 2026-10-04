import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalFiniteMovieAssembly
import CurveComplexGenusTwo.Topology.CrosscutIsotopy

open CurveComplex Set Topology Schoenflies

namespace RegionalFinitePosition

abbrev Square := ↥(Plane.closedSquare 0 1)

noncomputable def horizontalPoint (s : Interval) : Square :=
  ⟨Plane.mk (2*(s:ℝ)-1) 0, by
    apply mem_closedSquare_zero_one.mpr
    change max |2*(s:ℝ)-1| |(0:ℝ)| ≤ 1
    simp only [abs_zero,max_eq_left (abs_nonneg (2*(s:ℝ)-1))]
    rw [abs_le]
    constructor <;> linarith [s.property.1,s.property.2]⟩

theorem horizontalPoint_continuous : Continuous horizontalPoint := by
  apply Continuous.subtype_mk
  fun_prop

theorem horizontalPoint_injective : Function.Injective horizontalPoint := by
  intro s t h
  have h := congrArg (fun z : Square => z.val 0) h
  apply Subtype.ext
  dsimp [horizontalPoint,Plane.mk] at h
  linarith

theorem horizontalPoint_open (s : Interval) (hs : s ∈ Ioo (0:Interval) 1) :
    (horizontalPoint s).val ∈ Plane.openSquare 0 1 := by
  apply mem_openSquare_zero_one.mpr
  change max |2*(s:ℝ)-1| |(0:ℝ)| < 1
  simp only [abs_zero,max_eq_left (abs_nonneg (2*(s:ℝ)-1))]
  rw [abs_lt]
  have h0 : (0:ℝ) < s := hs.1
  have h1 : (s:ℝ) < 1 := hs.2
  constructor <;> linarith

theorem horizontalPoint_range :
    Set.range (fun s => (horizontalPoint s).val) =
      segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := by
  rw [segment_eq_image_lineMap]
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    refine ⟨s,s.property,?_⟩
    ext i
    fin_cases i <;> simp [horizontalPoint,Plane.mk,AffineMap.lineMap_apply_module] <;> ring
  · rintro ⟨s,hs,rfl⟩
    refine ⟨⟨s,hs⟩,?_⟩
    ext i
    fin_cases i <;> simp [horizontalPoint,Plane.mk,AffineMap.lineMap_apply_module] <;> ring

/-- An actual finite-contact crosscut inside an embedded square gives the
literal initial arc a fixed-endpoint movie, with every slice in the same F. -/
theorem embedded_square_finite_crosscut_movie
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (F : Set S) (a b : C(Interval, ↥F))
    (D : C(Square, ↥F)) (hD : IsEmbedding D)
    (hcenter : ∀ s, D (horizontalPoint s) = b s)
    (hclear : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 →
      (D z).val ∉ frontier F)
    (C : Set Plane)
    (hC : IsArcBetween C (Plane.mk (-1) 0) (Plane.mk 1 0))
    (hCi : C \ {Plane.mk (-1) 0, Plane.mk 1 0} ⊆ Plane.openSquare 0 1)
    (hfinite : {z : Square | z.val ∈ C ∧ D z ∈ Set.range a}.Finite) :
    ∃ q : C(Interval, ↥F), q 0 = b 0 ∧ q 1 = b 1 ∧
      IsEmbedding q ∧
      (∀ s ∈ Ioo (0:Interval) 1, (q s).val ∉ frontier F) ∧
      RegionalEmbeddedFamily.RegionalMovie F b q ∧
      (Set.range a ∩ Set.range q).Finite := by
  let A := segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
  have hA : IsArcBetween A (Plane.mk (-1) 0) (Plane.mk 1 0) :=
    isArcBetween_segment (by intro h; have := congrArg (fun z : Plane => z 0) h; norm_num [Plane.mk] at this)
  have hAi : A \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 := by
    intro z hz
    have hzA : z ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := hz.1
    rw [← horizontalPoint_range] at hzA
    obtain ⟨s,rfl⟩ := hzA
    apply horizontalPoint_open
    constructor
    · apply bot_lt_iff_ne_bot.mpr
      intro he
      exact hz.2 (Or.inl (by norm_num [he,horizontalPoint,Plane.mk]))
    · apply lt_top_iff_ne_top.mpr
      intro he
      exact hz.2 (Or.inr (by norm_num [he,horizontalPoint,Plane.mk]))
  obtain ⟨R,H,hR,hmove,hfixBall,hfix⟩ := position_crosscut_supported_isotopy A C
    (Plane.mk (-1) 0) (Plane.mk 1 0) hA hC
    (by norm_num [modelCurve,Plane.supNorm,Plane.mk])
    (by norm_num [modelCurve,Plane.supNorm,Plane.mk]) hAi hCi
  have hstay (t : Interval) (z : Plane) (hz : z ∈ Plane.openSquare 0 1) :
      H.map (t,z) ∈ Plane.openSquare 0 1 := by
    by_contra hn
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have heq : H.map (t,z) = z := e.injective (by
      rw [he,he]
      exact hfix t _ hn)
    exact hn (heq.symm ▸ hz)
  have hstayClosed (t : Interval) (z : Square) : H.map (t,z.val) ∈ Plane.closedSquare 0 1 := by
    by_cases hz : z.val ∈ Plane.openSquare 0 1
    · exact Plane.openSquare_subset_closedSquare 0 1 (hstay t z.val hz)
    · rw [hfix t z.val hz]
      exact z.property
  let V : C(Interval × Interval, ↥F) :=
    ⟨fun p => D ⟨H.map (p.1,(horizontalPoint p.2).val),hstayClosed p.1 _⟩,
      D.continuous.comp ((H.map.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp
          (horizontalPoint_continuous.comp continuous_snd)))).subtype_mk _)⟩
  let q : C(Interval, ↥F) :=
    ⟨fun s => V (1,s),V.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hV0 (s : Interval) : V (0,s) = b s := by
    change D ⟨H.map (0,_),_⟩ = b s
    convert hcenter s using 2
    exact Subtype.ext (H.at_zero _)
  have hEmb (t : Interval) : IsEmbedding (fun s => V (t,s)) := by
    apply (V.continuous.comp (continuous_const.prodMk continuous_id)).isClosedEmbedding ?_ |>.isEmbedding
    intro s u h
    have h := congrArg Subtype.val (hD.injective h)
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    have hp : (horizontalPoint s).val = (horizontalPoint u).val :=
      e.injective (by simpa only [he,id_eq] using h)
    exact horizontalPoint_injective (Subtype.ext hp)
  have hends (t : Interval) : V (t,0) = b 0 ∧ V (t,1) = b 1 := by
    constructor
    · change D ⟨H.map (t,(horizontalPoint 0).val),_⟩ = b 0
      convert hcenter 0 using 2
      apply Subtype.ext
      apply hfix
      norm_num [horizontalPoint,mem_openSquare_zero_one,Plane.supNorm,Plane.mk]
    · change D ⟨H.map (t,(horizontalPoint 1).val),_⟩ = b 1
      convert hcenter 1 using 2
      apply Subtype.ext
      apply hfix
      norm_num [horizontalPoint,mem_openSquare_zero_one,Plane.supNorm,Plane.mk]
  have hVclear (t s : Interval) (hs : s ∈ Ioo (0:Interval) 1) :
      (V (t,s)).val ∉ frontier F :=
    hclear _ (hstay t _ (horizontalPoint_open s hs))
  refine ⟨q,(hends 1).1,(hends 1).2,hEmb 1,hVclear 1,
    ⟨V,Homeomorph.refl _,rfl,rfl,hV0,fun _ => rfl,hEmb,hends,hVclear⟩,?_⟩
  apply (hfinite.image D).subset
  rintro z ⟨hza,⟨s,rfl⟩⟩
  refine ⟨⟨H.map (1,(horizontalPoint s).val),hstayClosed 1 _⟩,⟨?_,hza⟩,rfl⟩
  rw [← hmove]
  refine ⟨(horizontalPoint s).val,?_,rfl⟩
  change (horizontalPoint s).val ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
  rw [← horizontalPoint_range]
  exact Set.mem_range_self s

#print axioms embedded_square_finite_crosscut_movie

end RegionalFinitePosition
