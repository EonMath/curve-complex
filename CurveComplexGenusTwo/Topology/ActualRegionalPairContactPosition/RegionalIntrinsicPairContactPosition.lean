import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalActualGraphDescent
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalGraphCommonFaceMovie
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalTerminalGraphConeFace
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteLabelHomotopyAssembly
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalSquareFiniteContact
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

section InsertionImplementation
open CurveComplex Set Topology Schoenflies RegionalFinitePosition
open scoped Manifold ContDiff BigOperators
noncomputable local instance actualRegionalPairContactPositionImplementationPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P

private theorem square_minus_finite_connected (P : Set Plane) (hP : P.Finite) :
    IsPreconnected (Plane.openSquare 0 1 \ P) := by
  let u : ℝ ≃ₜ Metric.ball (0:ℝ) 1 := Homeomorph.unitBall
  let e : Plane ≃ₜ ↥(Plane.openSquare 0 1) := {
    toFun := fun z => ⟨Plane.mk (u (z 0)).val (u (z 1)).val, by
      rw [mem_openSquare_zero_one]
      change max |(u (z 0)).val| |(u (z 1)).val| < 1
      rw [max_lt_iff]
      exact ⟨by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using (u (z 0)).property,
        by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using (u (z 1)).property⟩⟩
    invFun := fun z => Plane.mk
      (u.symm ⟨z.val 0,by
        have h := (max_lt_iff.mp (mem_openSquare_zero_one.mp z.property)).1
        simpa [Real.dist_eq] using h⟩)
      (u.symm ⟨z.val 1,by
        have h := (max_lt_iff.mp (mem_openSquare_zero_one.mp z.property)).2
        simpa [Real.dist_eq] using h⟩)
    left_inv := by
      intro z
      ext i
      fin_cases i <;> simp [Plane.mk]
    right_inv := by
      intro z
      apply Subtype.ext
      ext i
      fin_cases i <;> simp [Plane.mk]
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (by fun_prop)
    continuous_invFun := by
      fun_prop }
  have hp : (fun z : Plane => (e z).val) ⁻¹' P |>.Finite :=
    hP.preimage (Subtype.val_injective.comp e.injective).injOn
  have hc := hp.countable.isConnected_compl_of_one_lt_rank
    (Module.one_lt_rank_of_one_lt_finrank (by simp [Plane]))
  have heq : (fun z : Plane => (e z).val) ''
      ((fun z : Plane => (e z).val) ⁻¹' P)ᶜ = Plane.openSquare 0 1 \ P := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨(e x).property,hx⟩
    · intro hz
      obtain ⟨x,hx⟩ := e.surjective ⟨z,hz.1⟩
      exact ⟨x,by change (e x).val ∉ P; simpa [hx] using hz.2,
        congrArg Subtype.val hx⟩
  rw [← heq]
  exact hc.isPreconnected.image _ (continuous_subtype_val.comp e.continuous).continuousOn


private theorem embedded_compact_isotopy_extend
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [CompactSpace X] [CompactSpace Y]
    (E : C(Y,X)) (hE : IsEmbedding E) (V : Set Y)
    (hU : IsOpen (E '' V))
    (k : Interval × Y → Y) (hkc : Continuous k)
    (hkbij : ∀ s : Interval, Function.Bijective (fun z => k (s,z)))
    (hk0 : ∀ z, k (0,z) = z)
    (hkfix : ∀ s z, z ∉ V → k (s,z) = z) :
    ∃ H : AmbientIsotopy X,
      (∀ s z, H.map (s,E z) = E (k (s,z))) ∧
      ∀ s y, y ∉ E '' V → H.map (s,y) = y := by
  classical
  let d := hE.toHomeomorph
  let U := E '' V
  let A := Set.range E
  let F : Interval × X → X := fun z =>
    if hy : z.2 ∈ A then E (k (z.1,d.symm ⟨z.2,hy⟩)) else z.2
  have hdinv (y : X) (hy : y ∈ A) : E (d.symm ⟨y,hy⟩) = y :=
    congrArg (fun y : Set.range E => y.val) (d.apply_symm_apply ⟨y,hy⟩)
  have hde (z : Y) :
      d.symm ⟨E z,Set.mem_range_self z⟩ = z := d.symm_apply_apply z
  have hband (s : Interval) (z : Y) :
      F (s,E z) = E (k (s,z)) := by
    dsimp only [F]
    rw [dite_eq_left (show E z ∈ A from Set.mem_range_self z),hde z]
  have hout (s : Interval) (y : X) (hy : y ∉ A) : F (s,y) = y := by
    dsimp only [F]
    rw [dite_eq_right hy]
  have hfixed (s : Interval) (y : X) (hy : y ∉ U) : F (s,y) = y := by
    by_cases hyA : y ∈ A
    · let z := d.symm ⟨y,hyA⟩
      have hzy : E z = y := hdinv y hyA
      have hzV : z ∉ V := fun hz => hy ⟨z,hz,hzy⟩
      have hkz : k (s,z) = z := hkfix s z hzV
      dsimp only [F]
      rw [dite_eq_left hyA]
      change E (k (s,z)) = y
      rw [hkz,hzy]
    · exact hout s y hyA
  let P : Set (Interval × X) := Set.univ ×ˢ A
  let Qe : Set (Interval × X) := Set.univ ×ˢ Uᶜ
  have hA : IsClosed A := (isCompact_range E.continuous).isClosed
  have hP : IsClosed P := isClosed_univ.prod hA
  have hQ : IsClosed Qe := isClosed_univ.prod hU.isClosed_compl
  have hFP : ContinuousOn F P := by
    rw [continuousOn_iff_continuous_domRestrict]
    let j : P → Set.range E := fun z => ⟨z.val.2,z.property.2⟩
    have hj : Continuous j :=
      (continuous_snd.comp continuous_subtype_val).subtype_mk _
    have hcont : Continuous (fun z : P => E (k (z.val.1,d.symm (j z)))) :=
      E.continuous.comp (hkc.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          (d.symm.continuous.comp hj)))
    convert hcont using 1
    funext z
    dsimp only [Set.domRestrict,F]
    rw [dite_eq_left z.property.2]
  have hFQ : ContinuousOn F Qe := by
    apply continuous_snd.continuousOn.congr
    intro z hz
    exact hfixed z.1 z.2 hz.2
  have hcover : P ∪ Qe = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro z
    by_cases hz : z.2 ∈ A
    · exact Or.inl ⟨Set.mem_univ _,hz⟩
    · exact Or.inr ⟨Set.mem_univ _,fun he => hz (Set.image_subset_range _ _ he)⟩
  have hFc : Continuous F := by
    have hc := hFP.union_of_isClosed hFQ hP hQ
    rw [hcover] at hc
    exact continuousOn_univ.mp hc
  have hFbij (s : Interval) : Function.Bijective (fun y => F (s,y)) := by
    constructor
    · intro y z he
      change F (s,y) = F (s,z) at he
      by_cases hy : y ∈ A
      · obtain ⟨a,ha⟩ := hy
        by_cases hz : z ∈ A
        · obtain ⟨b,hb⟩ := hz
          rw [←ha,←hb,hband,hband] at he
          exact ha.symm.trans
            ((congrArg E ((hkbij s).1 (hE.injective he))).trans hb)
        · rw [←ha,hband,hout s z hz] at he
          exact False.elim (hz ⟨k (s,a),he⟩)
      · by_cases hz : z ∈ A
        · obtain ⟨b,hb⟩ := hz
          rw [←hb,hout s y hy,hband] at he
          exact False.elim (hy ⟨k (s,b),he.symm⟩)
        · rw [hout s y hy,hout s z hz] at he
          exact he
    · intro y
      by_cases hy : y ∈ A
      · obtain ⟨z,hz⟩ := hy
        obtain ⟨w,hw⟩ := (hkbij s).2 z
        exact ⟨E w,(hband s w).trans ((congrArg E hw).trans hz)⟩
      · exact ⟨y,hout s y hy⟩
  let H : AmbientIsotopy X :=
    { map := ⟨F,hFc⟩,
      homeomorphism_at := by
        intro s
        have hc : Continuous (fun y => F (s,y)) :=
          hFc.comp (continuous_const.prodMk continuous_id)
        let h := (Equiv.ofBijective (fun y => F (s,y)) (hFbij s)).toHomeomorphOfContinuousClosed
          hc hc.isClosedMap
        exact ⟨h,fun y => rfl⟩,
      at_zero := by
        intro y
        by_cases hy : y ∈ A
        · obtain ⟨z,hz⟩ := hy
          rw [←hz]
          exact (hband 0 z).trans (congrArg E (hk0 z))
        · exact hout 0 y hy }
  exact ⟨H,hband,hfixed⟩



private theorem square_family_local_finite
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (D : C(Square,↥F))
    (hclear : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 →
      (D z).val ∉ frontier F)
    (P : OpenPartialHomeomorph Plane S)
    (hPs : P.source = Plane.openSquare 0 1)
    (hP : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → P z.val = (D z).val)
    {κ : Type} [Fintype κ] (a : κ → C(Interval,↥F))
    (ha0 : ∀ i, (a i 0).val ∈ frontier F)
    (ha1 : ∀ i, (a i 1).val ∈ frontier F)
    (Q : κ → OpenPartialHomeomorph S Plane)
    (hQa : ∀ i s, s ∈ Ioo (0:Interval) 1 → (a i s).val ∈ (Q i).source)
    (hQaxis : ∀ i z, z ∈ (Q i).source →
      z ∈ Set.range (fun s => (a i s).val) → Q i z 1 = 0)
    (bad : Set Plane) (hbad : bad.Finite)
    (hbadContains : ∀ i j, i ≠ j → squareObstacle D (a i) ∩ squareObstacle D (a j) ⊆ bad) :
    let U := Plane.openSquare 0 1 \ bad
    ∀ x ∈ U, ∃ V : Set Plane, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, x ≠ y → ∃ C ⊆ U, IsArcBetween C x y ∧
        (C ∩ ⋃ i, squareObstacle D (a i)).Finite := by
  classical
  intro U x hx
  have hU : IsOpen U := (Plane.isOpen_openSquare 0 1).sdiff hbad.isClosed
  by_cases hex : ∃ i, x ∈ squareObstacle D (a i)
  · obtain ⟨i,hxi⟩ := hex
    let other : Set Plane := ⋃ j : {j : κ // j ≠ i}, squareObstacle D (a j.val)
    have hother : IsClosed other := isClosed_iUnion_of_finite (fun j => squareObstacle_closed D (a j.val))
    have hxother : x ∉ other := by
      intro hh
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
      exact hx.2 (hbadContains i j.val j.property.symm ⟨hxi,hj⟩)
    let W := U \ other
    have hW : IsOpen W := hU.sdiff hother
    have hxW : x ∈ W := ⟨hx,hxother⟩
    obtain ⟨hxS,s,hs⟩ := hxi
    have hs0 : s ≠ 0 := by
      intro he
      exact hclear ⟨x,hxS⟩ hx.1 (by rw [← hs,he]; exact ha0 i)
    have hs1 : s ≠ 1 := by
      intro he
      exact hclear ⟨x,hxS⟩ hx.1 (by rw [← hs,he]; exact ha1 i)
    let E := (P.trans (Q i)).restr W
    have hxE : x ∈ E.source := by
      rw [OpenPartialHomeomorph.restr_source' _ _ hW]
      refine ⟨⟨(show x ∈ P.source by rw [hPs]; exact hx.1),?_⟩,hxW⟩
      change P x ∈ (Q i).source
      rw [hP ⟨x,hxS⟩ hx.1,← hs]
      exact hQa i s ⟨bot_lt_iff_ne_bot.mpr hs0,lt_top_iff_ne_top.mpr hs1⟩
    apply axis_chart_local_finite_contact U (⋃ i, squareObstacle D (a i)) x E hxE
    · intro z hz
      rw [OpenPartialHomeomorph.restr_source' _ _ hW] at hz
      exact hz.2.1
    · intro z hz hzA
      rw [OpenPartialHomeomorph.restr_source' _ _ hW] at hz
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hzA
      have hji : j = i := by
        by_contra hji
        exact hz.2.2 (Set.mem_iUnion.mpr ⟨⟨j,hji⟩,hj⟩)
      subst j
      obtain ⟨hzS,t,ht⟩ := hj
      change Q i (P z) 1 = 0
      apply hQaxis i _ hz.1.2
      refine ⟨t,?_⟩
      exact (congrArg Subtype.val ht).trans (hP ⟨z,hzS⟩ hz.2.1.1).symm
  · let A := ⋃ i, squareObstacle D (a i)
    have hA : IsClosed A := isClosed_iUnion_of_finite (fun i => squareObstacle_closed D (a i))
    let W := U \ A
    have hW : IsOpen W := hU.sdiff hA
    let E := OpenPartialHomeomorph.ofSet W hW
    apply axis_chart_local_finite_contact U A x E ⟨hx,by simpa only [A, Set.mem_iUnion] using hex⟩
    · exact Set.sdiff_subset
    · intro z hz hzA
      exact (hz.2 hzA).elim


private theorem planar_clean_endpoint_access
    (k : C(Interval,Plane)) (hk : IsEmbedding k)
    (hki : ∀ s ∈ Ioo (0:Interval) 1, k s ∈ Plane.openSquare 0 1)
    (A bad : Set Plane) (hA : IsClosed A) (hbad : bad ⊆ A)
    (hk0 : k 0 ∉ A) :
    ∃ u L, u ∈ Plane.openSquare 0 1 \ bad ∧ IsArcBetween L (k 0) u ∧
      L \ {k 0} ⊆ Plane.openSquare 0 1 \ bad ∧ (L ∩ A).Finite := by
  obtain ⟨δ,hδ,hδA⟩ := Metric.mem_nhds_iff.mp
    ((hA.isOpen_compl.preimage k.continuous).mem_nhds hk0)
  let ε : ℝ := min δ 1 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ 1]
  have hε1 : ε < 1 := by dsimp [ε]; linarith [min_le_right δ 1]
  let τ (s : Interval) : Interval := ⟨ε*(s:ℝ),by
    constructor
    · exact mul_nonneg hε.le s.property.1
    · nlinarith [s.property.2]⟩
  have hτc : Continuous τ := by apply Continuous.subtype_mk; fun_prop
  have hτi : Function.Injective τ := by
    intro s t h
    apply Subtype.ext
    exact mul_left_cancel₀ hε.ne' (congrArg Subtype.val h)
  have hτ0 : τ 0 = 0 := Subtype.ext (by simp [τ])
  have hτ1 (s : Interval) : (τ s:ℝ) < 1 := by
    change ε*(s:ℝ) < 1
    nlinarith [s.property.2]
  have havoid (s : Interval) : k (τ s) ∉ A := by
    apply hδA
    change dist (τ s) (0:Interval) < δ
    rw [Subtype.dist_eq,Real.dist_eq]
    change |ε*(s:ℝ)-0| < δ
    rw [sub_zero,abs_of_nonneg (mul_nonneg hε.le s.property.1)]
    nlinarith [s.property.2]
  let f : C(Interval,Plane) := ⟨k ∘ τ,k.continuous.comp hτc⟩
  have hfE : IsEmbedding f := (f.continuous.isClosedEmbedding (hk.injective.comp hτi)).isEmbedding
  have hf0 : f 0 = k 0 := congrArg k hτ0
  have hfU (s : Interval) (hs : s ≠ 0) : f s ∈ Plane.openSquare 0 1 \ bad := by
    refine ⟨hki (τ s) ⟨?_,hτ1 s⟩,fun hh => havoid s (hbad hh)⟩
    change (0:ℝ) < ε*(s:ℝ)
    exact mul_pos hε (bot_lt_iff_ne_bot.mpr hs)
  refine ⟨f 1,Set.range f,hfU 1 (by norm_num),?_,?_,?_⟩
  · simpa only [hf0] using RegionalEmbeddedFamily.planar_embedded_path_isArcBetween f hfE
  · rintro z ⟨⟨s,rfl⟩,hz⟩
    apply hfU
    intro he
    exact hz (by simpa [he,hf0])
  · have he : Set.range f ∩ A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨⟨s,rfl⟩,hs⟩
      exact havoid s hs
    rw [he]
    exact Set.finite_empty


private theorem embedded_square_crosscut_ambient
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBF : B ⊆ frontier F)
    (b : C(Interval,↥F)) (hb : IsEmbedding b)
    (hb0 : (b 0).val ∈ B) (hb1 : (b 1).val ∈ B)
    (hbclear : ∀ s ∈ Ioo (0:Interval) 1, (b s).val ∉ frontier F)
    (D : C(Square,↥F)) (hD : IsEmbedding D)
    (hcenter : ∀ s, D (horizontalPoint s) = b s)
    (hclear : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → (D z).val ∉ frontier F)
    (hopen : IsOpen (D '' {z : Square | z.val ∈ Plane.openSquare 0 1}))
    (C : Set Plane)
    (hC : IsArcBetween C (Plane.mk (-1) 0) (Plane.mk 1 0))
    (hCi : C \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1) :
    ∃ q : C(Interval,↥F), IsEmbedding q ∧ q 0 = b 0 ∧ q 1 = b 1 ∧
      (∀ s ∈ Ioo (0:Interval) 1, (q s).val ∉ frontier F) ∧
      Set.range q ⊆ D '' {z : Square | z.val ∈ C} ∧
      ∃ K : AmbientIsotopy ↥F,
        (∀ t, (fun y => K.map (t,y)) '' {y | y.val ∈ B} = {y | y.val ∈ B}) ∧
        (∀ t, (fun y => K.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧ K.finalMap '' Set.range b = Set.range q := by
  letI : CompactSpace ↥F := isCompact_iff_compactSpace.mp hF
  letI : CompactSpace Square := isCompact_iff_compactSpace.mp (isCompact_closedSquare (0:Plane) 1)
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
  have hclosed (t : Interval) (z : Plane) :
      z ∈ Plane.closedSquare 0 1 ↔ H.map (t,z) ∈ Plane.closedSquare 0 1 := by
    constructor
    · intro hz
      by_cases ho : z ∈ Plane.openSquare 0 1
      · exact Plane.openSquare_subset_closedSquare 0 1 (hstay t z ho)
      · rw [hfix t z ho]; exact hz
    · intro hz
      by_contra hn
      rw [hfix t z (fun ho => hn (Plane.openSquare_subset_closedSquare 0 1 ho))] at hz
      exact hn hz
  let k : Interval × Square → Square :=
    fun z => ⟨H.map (z.1,z.2.val),(hclosed z.1 z.2.val).mp z.2.property⟩
  have hkc : Continuous k := (H.map.continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hkbij (t : Interval) : Function.Bijective (fun z => k (t,z)) := by
    obtain ⟨e,he⟩ := H.homeomorphism_at t
    let f : Square ≃ₜ Square := e.subtype (fun z => by rw [he]; exact hclosed t z)
    have hf : (fun z => k (t,z)) = f := by
      funext z
      exact Subtype.ext (he z.val).symm
    rw [hf]
    exact f.bijective
  obtain ⟨K,hK,hKfix⟩ := embedded_compact_isotopy_extend D hD
    {z : Square | z.val ∈ Plane.openSquare 0 1} hopen k hkc hkbij
    (fun z => Subtype.ext (H.at_zero z.val))
    (fun t z hz => Subtype.ext (hfix t z.val hz))
  have hKfront (t : Interval) (y : ↥F) (hy : y.val ∈ frontier F) : K.map (t,y) = y := by
    apply hKfix
    rintro ⟨z,hz,rfl⟩
    exact hclear z hz hy
  have hKimage (T : Set S) (hT : T ⊆ frontier F) (t : Interval) :
      (fun y => K.map (t,y)) '' {y | y.val ∈ T} = {y | y.val ∈ T} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      simpa only [hKfront t z (hT hz)] using hz
    · intro hy
      exact ⟨y,hy,hKfront t y (hT hy)⟩
  let q : C(Interval,↥F) := ⟨fun s => K.map (1,b s),
    K.map.continuous.comp (continuous_const.prodMk b.continuous)⟩
  have hqE : IsEmbedding q := by
    obtain ⟨e,he⟩ := K.homeomorphism_at 1
    have hq : (q : Interval → ↥F) = e ∘ b := by
      funext s
      exact (he (b s)).symm
    rw [hq]
    exact e.isEmbedding.comp hb
  refine ⟨q,hqE,hKfront 1 (b 0) (hBF hb0),hKfront 1 (b 1) (hBF hb1),?_,?_,
    K,hKimage B hBF,hKimage (frontier F) (fun _ h => h),?_⟩
  · intro s hs hqfront
    obtain ⟨e,he⟩ := K.homeomorphism_at 1
    have heq : q s = b s := e.injective (by
      rw [he,he]
      exact hKfront 1 (q s) hqfront)
    exact hbclear s hs (heq ▸ hqfront)
  · rintro z ⟨s,rfl⟩
    refine ⟨k (1,horizontalPoint s),?_,?_⟩
    · change H.finalMap (horizontalPoint s).val ∈ C
      rw [← hmove]
      refine ⟨(horizontalPoint s).val,?_,rfl⟩
      change (horizontalPoint s).val ∈ segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
      rw [← horizontalPoint_range]
      exact Set.mem_range_self s
    · rw [← hK, hcenter]
      rfl
  · change (fun y => K.map (1,y)) '' Set.range b = Set.range q
    exact Set.range_comp _ _ |>.symm


private theorem square_finite_family_crosscut
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (D : C(Square,↥F)) (hD : IsEmbedding D)
    (b : C(Interval,↥F))
    (hcenter : ∀ s, D (horizontalPoint s) = b s)
    (hclear : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 →
      (D z).val ∉ frontier F)
    (P : OpenPartialHomeomorph Plane S)
    (hPs : P.source = Plane.openSquare 0 1)
    (hP : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → P z.val = (D z).val)
    {κ : Type} [Fintype κ] (a : κ → C(Interval,↥F))
    (ha0 : ∀ i, (a i 0).val ∈ frontier F)
    (ha1 : ∀ i, (a i 1).val ∈ frontier F)
    (Q : κ → OpenPartialHomeomorph S Plane)
    (hQa : ∀ i s, s ∈ Ioo (0:Interval) 1 → (a i s).val ∈ (Q i).source)
    (hQaxis : ∀ i z, z ∈ (Q i).source →
      z ∈ Set.range (fun s => (a i s).val) → Q i z 1 = 0)
    (hfinite : ∀ i j, i ≠ j → (Set.range (a i) ∩ Set.range (a j)).Finite)
    (h0 : ∀ i, b 0 ∉ Set.range (a i))
    (h1 : ∀ i, b 1 ∉ Set.range (a i)) :
    ∃ C : Set Plane, IsArcBetween C (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
      C \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
      (C ∩ ⋃ i, squareObstacle D (a i)).Finite := by
  classical
  let A := ⋃ i, squareObstacle D (a i)
  let pairs := {ij : κ × κ // ij.1 ≠ ij.2}
  let bad : Set Plane := ⋃ ij : pairs,
    squareObstacle D (a ij.val.1) ∩ squareObstacle D (a ij.val.2)
  have hpair (i j : κ) (hij : i ≠ j) :
      (squareObstacle D (a i) ∩ squareObstacle D (a j)).Finite := by
    have hf : (D ⁻¹' (Set.range (a i) ∩ Set.range (a j))).Finite :=
      (hfinite i j hij).preimage hD.injective.injOn
    apply (hf.image (fun z : Square => z.val)).subset
    rintro z ⟨⟨hz,hi⟩,⟨hz',hj⟩⟩
    exact ⟨⟨z,hz⟩,⟨hi,hj⟩,rfl⟩
  have hbad : bad.Finite := Set.finite_iUnion (fun ij : pairs => hpair _ _ ij.property)
  have hbadContains (i j : κ) (hij : i ≠ j) :
      squareObstacle D (a i) ∩ squareObstacle D (a j) ⊆ bad := by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hz⟩
  have hbadA : bad ⊆ A := by
    intro z hz
    obtain ⟨ij,hz⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion.mpr ⟨ij.val.1,hz.1⟩
  have hA : IsClosed A := isClosed_iUnion_of_finite (fun i => squareObstacle_closed D (a i))
  let U := Plane.openSquare 0 1 \ bad
  have hU : IsOpen U := (Plane.isOpen_openSquare 0 1).sdiff hbad.isClosed
  have hconn : IsPreconnected U := square_minus_finite_connected bad hbad
  have hlocal := square_family_local_finite F D hclear P hPs hP a ha0 ha1 Q hQa hQaxis bad hbad hbadContains
  let k : C(Interval,Plane) := ⟨fun s => (horizontalPoint s).val,
    continuous_subtype_val.comp horizontalPoint_continuous⟩
  have hk : IsEmbedding k := (k.continuous.isClosedEmbedding
    (fun s t h => horizontalPoint_injective (Subtype.ext h))).isEmbedding
  have hki : ∀ s ∈ Ioo (0:Interval) 1, k s ∈ Plane.openSquare 0 1 := horizontalPoint_open
  have hk0 : k 0 ∉ A := by
    intro hh
    obtain ⟨i,hz,hi⟩ := Set.mem_iUnion.mp hh
    exact h0 i (hcenter 0 ▸ hi)
  have hk1 : k 1 ∉ A := by
    intro hh
    obtain ⟨i,hz,hi⟩ := Set.mem_iUnion.mp hh
    exact h1 i (hcenter 1 ▸ hi)
  obtain ⟨u,L,hu,hL,hLU,hLA⟩ := planar_clean_endpoint_access k hk hki A bad hA hbadA hk0
  let kr : C(Interval,Plane) := ⟨fun s => k (unitInterval.symm s),
    k.continuous.comp unitInterval.continuous_symm⟩
  have hkr : IsEmbedding kr := (kr.continuous.isClosedEmbedding
    (hk.injective.comp unitInterval.symm_bijective.injective)).isEmbedding
  have hkri : ∀ s ∈ Ioo (0:Interval) 1, kr s ∈ Plane.openSquare 0 1 := by
    intro s hs
    apply hki
    change 0 < unitInterval.symm s ∧ unitInterval.symm s < 1
    constructor
    · change (0:ℝ) < 1-(s:ℝ)
      have h : (s:ℝ) < 1 := hs.2
      linarith
    · change 1-(s:ℝ) < (1:ℝ)
      have h : (0:ℝ) < s := hs.1
      linarith
  have hkr0 : kr 0 = k 1 := by simp [kr]
  obtain ⟨v,R,hv,hR,hRU,hRA⟩ := planar_clean_endpoint_access kr hkr hkri A bad hA hbadA
    (by rw [hkr0]; exact hk1)
  rw [hkr0] at hR hRU
  have hleft : k 0 = Plane.mk (-1) 0 := by norm_num [k,horizontalPoint,Plane.mk]
  have hright : k 1 = Plane.mk 1 0 := by norm_num [k,horizontalPoint,Plane.mk]
  obtain ⟨C,hC,hCi,hCA⟩ := finite_contact_arc_with_access U A L R hU hconn hlocal
    (k 0) (k 1) u v (fun he => zero_ne_one (hk.injective he))
    (fun hh => by
      have hh := hh.1
      rw [hleft] at hh
      norm_num [mem_openSquare_zero_one,Plane.supNorm,Plane.mk] at hh)
    (fun hh => by
      have hh := hh.1
      rw [hright] at hh
      norm_num [mem_openSquare_zero_one,Plane.supNorm,Plane.mk] at hh)
    hu hv hL hR hLU hRU hLA hRA
  rw [hleft,hright] at hC hCi
  exact ⟨C,hC,hCi.trans Set.sdiff_subset,hCA⟩


private theorem square_finite_family_ambient
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F B : Set S) (hF : IsCompact F) (hBF : B ⊆ frontier F)
    (b : C(Interval,↥F)) (hb : IsEmbedding b)
    (hb0 : (b 0).val ∈ B) (hb1 : (b 1).val ∈ B)
    (hbclear : ∀ s ∈ Ioo (0:Interval) 1, (b s).val ∉ frontier F)
    (D : C(Square,↥F)) (hD : IsEmbedding D)
    (hcenter : ∀ s, D (horizontalPoint s) = b s)
    (hclear : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → (D z).val ∉ frontier F)
    (P : OpenPartialHomeomorph Plane S)
    (hPs : P.source = Plane.openSquare 0 1)
    (hP : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → P z.val = (D z).val)
    {κ : Type} [Fintype κ] (a : κ → C(Interval,↥F))
    (ha0 : ∀ i, (a i 0).val ∈ frontier F)
    (ha1 : ∀ i, (a i 1).val ∈ frontier F)
    (Q : κ → OpenPartialHomeomorph S Plane)
    (hQa : ∀ i s, s ∈ Ioo (0:Interval) 1 → (a i s).val ∈ (Q i).source)
    (hQaxis : ∀ i z, z ∈ (Q i).source →
      z ∈ Set.range (fun s => (a i s).val) → Q i z 1 = 0)
    (hfinite : ∀ i j, i ≠ j → (Set.range (a i) ∩ Set.range (a j)).Finite)
    (h0 : ∀ i, b 0 ∉ Set.range (a i))
    (h1 : ∀ i, b 1 ∉ Set.range (a i)) :
    ∃ q : C(Interval,↥F), IsEmbedding q ∧ q 0 = b 0 ∧ q 1 = b 1 ∧
      (∀ s ∈ Ioo (0:Interval) 1, (q s).val ∉ frontier F) ∧
      (∀ i, (Set.range q ∩ Set.range (a i)).Finite) ∧
      ∃ K : AmbientIsotopy ↥F,
        (∀ t, (fun y => K.map (t,y)) '' {y | y.val ∈ B} = {y | y.val ∈ B}) ∧
        (∀ t, (fun y => K.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧ K.finalMap '' Set.range b = Set.range q := by
  obtain ⟨C,hC,hCi,hCA⟩ := square_finite_family_crosscut F D hD b hcenter hclear P hPs hP
    a ha0 ha1 Q hQa hQaxis hfinite h0 h1
  have heq : D '' {z : Square | z.val ∈ Plane.openSquare 0 1} =
      Subtype.val ⁻¹' P.target := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      change (D z).val ∈ P.target
      rw [← hP z hz]
      exact P.map_source (by rw [hPs]; exact hz)
    · intro hy
      have hz : P.symm y.val ∈ Plane.openSquare 0 1 := hPs ▸ P.map_target hy
      let z : Square := ⟨P.symm y.val,Plane.openSquare_subset_closedSquare 0 1 hz⟩
      refine ⟨z,hz,?_⟩
      apply Subtype.ext
      exact (hP z hz).symm.trans (P.right_inv hy)
  have hopen : IsOpen (D '' {z : Square | z.val ∈ Plane.openSquare 0 1}) := by
    rw [heq]
    exact P.open_target.preimage continuous_subtype_val
  obtain ⟨q,hq,hq0,hq1,hqclear,hqC,K,hKB,hKF,hKmove⟩ :=
    embedded_square_crosscut_ambient F B hF hBF b hb hb0 hb1 hbclear D hD hcenter hclear hopen C hC hCi
  refine ⟨q,hq,hq0,hq1,hqclear,?_,K,hKB,hKF,hKmove⟩
  intro i
  have hf : ((fun z : Square => z.val) ⁻¹' (C ∩ ⋃ j, squareObstacle D (a j))).Finite :=
    hCA.preimage Subtype.val_injective.injOn
  apply (hf.image D).subset
  intro y hy
  obtain ⟨z,hz,hzy⟩ := hqC hy.1
  refine ⟨z,⟨hz,?_⟩,hzy⟩
  exact Set.mem_iUnion.mpr ⟨i,z.property,hzy.symm ▸ hy.2⟩


end InsertionImplementation

open CurveComplex Set Topology
open scoped Manifold ContDiff BigOperators
noncomputable local instance actualRegionalPairContactPositionEndpointPropDecidable (P : Prop) : Decidable P := Classical.propDecidable P
theorem regional_original_intrinsic_finite_family_pair_contact_position
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ (ι : Type) [Fintype ι] (given : ι → IntrinsicEssentialArc)
      (givenAnchor : IntrinsicEssentialArc),
      ∃ (a : ι → IntrinsicEssentialArc) (anchor : IntrinsicEssentialArc),
        (∀ i, Quot.mk intrinsicArcRel (a i) = Quot.mk intrinsicArcRel (given i)) ∧
        Quot.mk intrinsicArcRel anchor = Quot.mk intrinsicArcRel givenAnchor ∧
        (∀ i j, i ≠ j → (Set.range (a i).val.val ∩ Set.range (a j).val.val).Finite) ∧
        (∀ i j, i ≠ j → (a i).val.val 0 ≠ (a j).val.val 0 ∧
          (a i).val.val 0 ≠ (a j).val.val 1 ∧
          (a i).val.val 1 ≠ (a j).val.val 0 ∧
          (a i).val.val 1 ≠ (a j).val.val 1) ∧
        (∀ i, anchor.val.val 0 ∉ Set.range (a i).val.val) ∧
        (∀ i, anchor.val.val 1 ∉ Set.range (a i).val.val) ∧
        (∀ i, (Set.range anchor.val.val ∩ Set.range (a i).val.val).Finite) := by
  classical
  intro B Proper Parallel Arc rel V faces L ι inst given givenAnchor
  by_cases hempty : IsEmpty ι
  · letI := hempty
    refine ⟨given,givenAnchor,?_,rfl,?_,?_,?_,?_,?_⟩
    all_goals intro i; exact isEmptyElim i
  let : ClosedSurface S := Classical.choice hS.2.1
  have hBF : B ⊆ frontier F := by
    change (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ frontier F
    rw [hfrontier]
    exact Set.subset_union_left
  have pointAvoidance
      {S : Type} [TopologicalSpace S] [T2Space S]
      (F B : Set S) (hF : IsCompact F) (hBF : B ⊆ frontier F)
      (a : C(Interval, ↥F))
      (E : C(Interval × Set.Icc (-1 : ℝ) 1, ↥F))
      (hE : Topology.IsEmbedding E)
      (hcenter : ∀ t, E (t, ⟨0, by norm_num⟩) = a t)
      (hend : ∀ w, (E (0,w)).val ∈ B ∧ (E (1,w)).val ∈ B)
      (hint : ∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        (E (t,w)).val ∈ interior F)
      (hopen : IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}))
      (P : Set ↥F) (hP : P.Finite) (hPF : ∀ y ∈ P, y.val ∈ frontier F) :
      ∃ b : C(Interval, ↥F),
        Topology.IsEmbedding b ∧ (b 0).val ∈ B ∧ (b 1).val ∈ B ∧
        (∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F) ∧
        Disjoint (Set.range b) P ∧
        ∃ H : AmbientIsotopy ↥F,
          (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ B} = {y | y.val ∈ B}) ∧
          (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
            {y | y.val ∈ frontier F}) ∧
          H.finalMap '' Set.range a = Set.range b := by
    classical
    let W := Set.Icc (-1 : ℝ) 1
    let f₀ : W → ↥F := fun w => E (0,w)
    let f₁ : W → ↥F := fun w => E (1,w)
    have hf₀ : Function.Injective f₀ := by
      intro w v h
      exact congrArg Prod.snd (hE.injective h)
    have hf₁ : Function.Injective f₁ := by
      intro w v h
      exact congrArg Prod.snd (hE.injective h)
    have hbad₀ : (f₀ ⁻¹' P).Finite := hP.preimage hf₀.injOn
    have hbad₁ : (f₁ ⁻¹' P).Finite := hP.preimage hf₁.injOn
    let bad : Set ℝ := Subtype.val '' ((f₀ ⁻¹' P) ∪ (f₁ ⁻¹' P))
    have hbad : bad.Finite := (hbad₀.union hbad₁).image Subtype.val
    obtain ⟨ε,hε,hεbad⟩ :=
      (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finite hbad
    let w : W := ⟨ε, by constructor <;> linarith [hε.1,hε.2]⟩
    have hzero : E (0,w) ∉ P := fun h => hεbad ⟨w,Or.inl h,rfl⟩
    have hone : E (1,w) ∉ P := fun h => hεbad ⟨w,Or.inr h,rfl⟩
    let b : C(Interval, ↥F) :=
      ⟨fun t => E (t,w), E.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have hb : Topology.IsEmbedding b :=
      (b.continuous.isClosedEmbedding (fun s t h =>
        congrArg Prod.fst (hE.injective h))).isEmbedding
    have hbproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, (b t).val ∉ frontier F := by
      intro t ht
      exact (mem_interior_iff_notMem_frontier
        (interior_subset (hint t ht w))).mp (hint t ht w)
    have hbP : Disjoint (Set.range b) P := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨t,rfl⟩ htP
      by_cases ht0 : t = 0
      · exact hzero (ht0 ▸ htP)
      by_cases ht1 : t = 1
      · exact hone (ht1 ▸ htP)
      exact hbproper t ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩
        (hPF (b t) htP)
    obtain ⟨H,hHB,hHF,hmove,hout⟩ :=
      regional_proper_strip_small_width_ambient_move F B hF hBF E hE
        hend hint hopen ε hε.1 hε.2
    have harange : Set.range a =
        Set.range (fun t : Interval => E (t,⟨0,by norm_num⟩)) := by
      apply congrArg Set.range
      exact funext (fun t => (hcenter t).symm)
    refine ⟨b,hb,(hend w).1,(hend w).2,hbproper,hbP,H,hHB,hHF,?_⟩
    rw [harange]
    exact hmove
  have familyAssembly
      {X A : Type} [TopologicalSpace X]
      (arc : A → C(Interval,X)) (label : A → A → Prop)
      (front : Set X) (hends : ∀ a, arc a 0 ∈ front ∧ arc a 1 ∈ front)
      (anchor : A)
      (avoid : ∀ a : A, ∀ P : Set X, P.Finite → P ⊆ front →
        ∃ b : A, label b a ∧ Disjoint (Set.range (arc b)) P)
      {ι : Type} [Fintype ι] (given : ι → A) :
      ∃ b : ι → A,
        (∀ i, label (b i) (given i)) ∧
        (∀ i j, i ≠ j → arc (b i) 0 ≠ arc (b j) 0 ∧
          arc (b i) 0 ≠ arc (b j) 1 ∧
          arc (b i) 1 ≠ arc (b j) 0 ∧
          arc (b i) 1 ≠ arc (b j) 1) ∧
        (∀ i, arc anchor 0 ∉ Set.range (arc (b i))) ∧
        (∀ i, arc anchor 1 ∉ Set.range (arc (b i))) := by
    classical
    have build (σ : Finset ι) : ∃ b : ι → A,
        (∀ i ∈ σ, label (b i) (given i)) ∧
        (∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → arc (b i) 0 ≠ arc (b j) 0 ∧
          arc (b i) 0 ≠ arc (b j) 1 ∧
          arc (b i) 1 ≠ arc (b j) 0 ∧
          arc (b i) 1 ≠ arc (b j) 1) ∧
        (∀ i ∈ σ, arc anchor 0 ∉ Set.range (arc (b i))) ∧
        (∀ i ∈ σ, arc anchor 1 ∉ Set.range (arc (b i))) := by
      induction σ using Finset.induction_on with
      | empty => exact ⟨given,by simp,by simp,by simp,by simp⟩
      | @insert k σ hk ih =>
        obtain ⟨b,hlabel,hpair,hzero,hone⟩ := ih
        let endpoints : Set X :=
          ⋃ i : ↥σ, ({arc (b i.val) 0,arc (b i.val) 1} : Set X)
        let P : Set X := {arc anchor 0,arc anchor 1} ∪ endpoints
        have hP : P.Finite := ((Set.finite_singleton _).insert _).union
          (Set.finite_iUnion (fun i : ↥σ => (Set.finite_singleton _).insert _))
        have hPF : P ⊆ front := by
          intro x hx
          rcases hx with hx | hx
          · rcases hx with rfl | hx
            · exact (hends anchor).1
            · exact (Set.mem_singleton_iff.mp hx) ▸ (hends anchor).2
          · obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hx
            rcases hxi with rfl | hxi
            · exact (hends (b i.val)).1
            · exact (Set.mem_singleton_iff.mp hxi) ▸ (hends (b i.val)).2
        obtain ⟨copy,hcopy,hdis⟩ := avoid (given k) P hP hPF
        have hclear (i : ↥σ) :
            arc copy 0 ≠ arc (b i.val) 0 ∧ arc copy 0 ≠ arc (b i.val) 1 ∧
            arc copy 1 ≠ arc (b i.val) 0 ∧ arc copy 1 ≠ arc (b i.val) 1 := by
          have hmem₀ : arc (b i.val) 0 ∈ P :=
            Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inl rfl⟩)
          have hmem₁ : arc (b i.val) 1 ∈ P :=
            Or.inr (Set.mem_iUnion.mpr ⟨i,Or.inr rfl⟩)
          refine ⟨?_,?_,?_,?_⟩ <;> intro h
          · exact Set.disjoint_left.mp hdis (Set.mem_range_self 0) (h.symm ▸ hmem₀)
          · exact Set.disjoint_left.mp hdis (Set.mem_range_self 0) (h.symm ▸ hmem₁)
          · exact Set.disjoint_left.mp hdis (Set.mem_range_self 1) (h.symm ▸ hmem₀)
          · exact Set.disjoint_left.mp hdis (Set.mem_range_self 1) (h.symm ▸ hmem₁)
        let out : ι → A := Function.update b k copy
        have hselected : out k = copy := by simp [out]
        have hretained (i : ι) (hi : i ≠ k) : out i = b i :=
          Function.update_of_ne hi _ _
        refine ⟨out,?_,?_,?_,?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · rw [hselected]; exact hcopy
          · rw [hretained i (fun h => hk (h ▸ hi))]; exact hlabel i hi
        · intro i hi j hj hij
          by_cases hik : i = k
          · subst i
            have hjs : j ∈ σ := (Finset.mem_insert.mp hj).resolve_left hij.symm
            rw [hselected,hretained j hij.symm]
            exact hclear ⟨j,hjs⟩
          have his : i ∈ σ := (Finset.mem_insert.mp hi).resolve_left hik
          by_cases hjk : j = k
          · subst j
            rw [hretained i hik,hselected]
            obtain ⟨h00,h01,h10,h11⟩ := hclear ⟨i,his⟩
            exact ⟨h00.symm,h10.symm,h01.symm,h11.symm⟩
          have hjs : j ∈ σ := (Finset.mem_insert.mp hj).resolve_left hjk
          rw [hretained i hik,hretained j hjk]
          exact hpair i his j hjs hij
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · rw [hselected]
            exact fun h => Set.disjoint_right.mp hdis (Or.inl (Or.inl rfl)) h
          · rw [hretained i (fun h => hk (h ▸ hi))]; exact hzero i hi
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · rw [hselected]
            exact fun h => Set.disjoint_right.mp hdis (Or.inl (Or.inr rfl)) h
          · rw [hretained i (fun h => hk (h ▸ hi))]; exact hone i hi
    obtain ⟨b,hlabel,hpair,hzero,hone⟩ := build Finset.univ
    exact ⟨b,fun i => hlabel i (Finset.mem_univ i),
      fun i j hij => hpair i (Finset.mem_univ i) j (Finset.mem_univ j) hij,
      fun i => hzero i (Finset.mem_univ i),fun i => hone i (Finset.mem_univ i)⟩
  have contactAssembly
      {X A V : Type} [TopologicalSpace X]
      (arc : A → C(Interval,X)) (label : A → V)
      (front : Set X) (hends : ∀ a, arc a 0 ∈ front ∧ arc a 1 ∈ front)
      (boundaryRange : ∀ a p, p ∈ front → p ≠ arc a 0 → p ≠ arc a 1 →
        p ∉ Set.range (arc a))
      (extend : ∀ (κ : Type) [Fintype κ] (old : κ → A),
        (∀ i j, i ≠ j → (Set.range (arc (old i)) ∩ Set.range (arc (old j))).Finite) →
        ∀ new : A,
          (∀ i, arc new 0 ∉ Set.range (arc (old i))) →
          (∀ i, arc new 1 ∉ Set.range (arc (old i))) →
          ∃ d : A, label d = label new ∧ arc d 0 = arc new 0 ∧ arc d 1 = arc new 1 ∧
            ∀ i, (Set.range (arc d) ∩ Set.range (arc (old i))).Finite)
      {ι : Type} [Fintype ι] (given : ι → A) (anchor : A)
      (hpair : ∀ i j, i ≠ j → arc (given i) 0 ≠ arc (given j) 0 ∧
        arc (given i) 0 ≠ arc (given j) 1 ∧
        arc (given i) 1 ≠ arc (given j) 0 ∧
        arc (given i) 1 ≠ arc (given j) 1)
      (hzero : ∀ i, arc anchor 0 ∉ Set.range (arc (given i)))
      (hone : ∀ i, arc anchor 1 ∉ Set.range (arc (given i))) :
      ∃ b : ι → A,
        (∀ i, label (b i) = label (given i)) ∧
        (∀ i, arc (b i) 0 = arc (given i) 0 ∧ arc (b i) 1 = arc (given i) 1) ∧
        (∀ i j, i ≠ j → (Set.range (arc (b i)) ∩ Set.range (arc (b j))).Finite) ∧
        (∀ i, (Set.range (arc anchor) ∩ Set.range (arc (b i))).Finite) := by
    classical
    have build (σ : Finset ι) : ∃ b : ι → A,
        (∀ i, label (b i) = label (given i)) ∧
        (∀ i, arc (b i) 0 = arc (given i) 0 ∧ arc (b i) 1 = arc (given i) 1) ∧
        (∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
          (Set.range (arc (b i)) ∩ Set.range (arc (b j))).Finite) ∧
        (∀ i ∈ σ, (Set.range (arc anchor) ∩ Set.range (arc (b i))).Finite) := by
      induction σ using Finset.induction_on with
      | empty => exact ⟨given,fun _ => rfl,fun _ => ⟨rfl,rfl⟩,by simp,by simp⟩
      | @insert k σ hk ih =>
        obtain ⟨b,hlabel,hend,hfinite,hanchor⟩ := ih
        let old : Option ↥σ → A := fun i =>
          match i with
          | none => anchor
          | some j => b j.val
        have hold : ∀ i j : Option ↥σ, i ≠ j →
            (Set.range (arc (old i)) ∩ Set.range (arc (old j))).Finite := by
          intro i j hij
          cases i with
          | none =>
            cases j with
            | none => exact False.elim (hij rfl)
            | some j => exact hanchor j.val j.property
          | some i =>
            cases j with
            | none => simpa only [Set.inter_comm] using hanchor i.val i.property
            | some j =>
              apply hfinite i.val i.property j.val j.property
              exact fun h => hij (congrArg some (Subtype.ext h))
        have hk0 : ∀ i, arc (given k) 0 ∉ Set.range (arc (old i)) := by
          intro i
          cases i with
          | none =>
            apply boundaryRange anchor _ (hends (given k)).1
            · exact fun h => hzero k ⟨0,h⟩
            · exact fun h => hone k ⟨0,h⟩
          | some i =>
            have hki : k ≠ i.val := fun h => hk (h.symm ▸ i.property)
            apply boundaryRange (b i.val) _ (hends (given k)).1
            · rw [(hend i.val).1]; exact (hpair k i.val hki).1
            · rw [(hend i.val).2]; exact (hpair k i.val hki).2.1
        have hk1 : ∀ i, arc (given k) 1 ∉ Set.range (arc (old i)) := by
          intro i
          cases i with
          | none =>
            apply boundaryRange anchor _ (hends (given k)).2
            · exact fun h => hzero k ⟨1,h⟩
            · exact fun h => hone k ⟨1,h⟩
          | some i =>
            have hki : k ≠ i.val := fun h => hk (h.symm ▸ i.property)
            apply boundaryRange (b i.val) _ (hends (given k)).2
            · rw [(hend i.val).1]; exact (hpair k i.val hki).2.2.1
            · rw [(hend i.val).2]; exact (hpair k i.val hki).2.2.2
        obtain ⟨copy,hcopy,hcopy0,hcopy1,hcopyfinite⟩ :=
          extend (Option ↥σ) old hold (given k) hk0 hk1
        let out : ι → A := Function.update b k copy
        have hselected : out k = copy := by simp [out]
        have hretained (i : ι) (hi : i ≠ k) : out i = b i :=
          Function.update_of_ne hi _ _
        refine ⟨out,?_,?_,?_,?_⟩
        · intro i
          by_cases hi : i = k
          · subst i; rw [hselected]; exact hcopy
          · rw [hretained i hi]; exact hlabel i
        · intro i
          by_cases hi : i = k
          · subst i; rw [hselected]; exact ⟨hcopy0,hcopy1⟩
          · rw [hretained i hi]; exact hend i
        · intro i hi j hj hij
          by_cases hik : i = k
          · subst i
            have hjs : j ∈ σ := (Finset.mem_insert.mp hj).resolve_left hij.symm
            rw [hselected,hretained j hij.symm]
            exact hcopyfinite (some ⟨j,hjs⟩)
          have his : i ∈ σ := (Finset.mem_insert.mp hi).resolve_left hik
          by_cases hjk : j = k
          · subst j
            rw [hretained i hik,hselected,Set.inter_comm]
            exact hcopyfinite (some ⟨i,his⟩)
          have hjs : j ∈ σ := (Finset.mem_insert.mp hj).resolve_left hjk
          rw [hretained i hik,hretained j hjk]
          exact hfinite i his j hjs hij
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · rw [hselected,Set.inter_comm]
            exact hcopyfinite none
          · rw [hretained i (fun h => hk (h ▸ hi))]; exact hanchor i hi
    obtain ⟨b,hlabel,hend,hfinite,hanchor⟩ := build Finset.univ
    exact ⟨b,hlabel,hend,
      fun i j hij => hfinite i (Finset.mem_univ i) j (Finset.mem_univ j) hij,
      fun i => hanchor i (Finset.mem_univ i)⟩
  have one (d : Arc) (P : Set ↥F) (hP : P.Finite)
      (hPF : P ⊆ {y : ↥F | y.val ∈ frontier F}) :
      ∃ b : Arc, Quot.mk rel b = Quot.mk rel d ∧
        Disjoint (Set.range b.val.val) P := by
    obtain ⟨E,hE,hcenter,hend,hint,hopen⟩ :=
      regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget
        F hFcompact hbase houtside J c hbaseDisjoint hfrontier
        d.val.val d.val.property.1 d.val.property.2.1
        d.val.property.2.2.1 d.val.property.2.2.2
    obtain ⟨b,hb,hb0,hb1,hbp,hbP,H,hHB,hHF,hmove⟩ :=
      pointAvoidance F B hFcompact hBF d.val.val E hE hcenter
        hend hint hopen P hP hPF
    have hbess := (regional_essential_arc_ambient_transport F B
      d.val.val b H (hHB 1) hmove).mp d.property
    let copy : Arc := ⟨⟨b,hb,hb0,hb1,hbp⟩,hbess⟩
    exact ⟨copy,(Quot.sound (show rel d copy from ⟨H,hHB,hHF,hmove⟩)).symm,hbP⟩
  obtain ⟨a,hclass,hpair,hzero,hone⟩ := familyAssembly
    (fun d : Arc => d.val.val)
    (fun b d : Arc => Quot.mk rel b = Quot.mk rel d)
    {y : ↥F | y.val ∈ frontier F}
    (fun d => ⟨hBF d.val.property.2.1,hBF d.val.property.2.2.1⟩)
    givenAnchor one given
  have boundaryRange (d : Arc) (p : ↥F) (hp : p.val ∈ frontier F)
      (h0 : p ≠ d.val.val 0) (h1 : p ≠ d.val.val 1) :
      p ∉ Set.range d.val.val := by
    rintro ⟨t,ht⟩
    by_cases ht0 : t = 0
    · exact h0 (ht.symm.trans (congrArg d.val.val ht0))
    by_cases ht1 : t = 1
    · exact h1 (ht.symm.trans (congrArg d.val.val ht1))
    exact d.val.property.2.2.2 t
      ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩
      (ht.symm ▸ hp)
  -- Insert in the original F ambient class, preserving literal endpoints.
  have extend (κ : Type) [Fintype κ] (old : κ → Arc)
      (hκfinite : ∀ i j, i ≠ j →
        (Set.range (old i).val.val ∩ Set.range (old j).val.val).Finite)
      (new : Arc)
      (hκ0 : ∀ i, new.val.val 0 ∉ Set.range (old i).val.val)
      (hκ1 : ∀ i, new.val.val 1 ∉ Set.range (old i).val.val) :
      ∃ d : Arc, Quot.mk rel d = Quot.mk rel new ∧
        d.val.val 0 = new.val.val 0 ∧ d.val.val 1 = new.val.val 1 ∧
        ∀ i, (Set.range d.val.val ∩ Set.range (old i).val.val).Finite := by
    obtain ⟨E,hE,hcenter,hend,hint,hopen⟩ :=
      regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget
        F hFcompact hbase houtside J c hbaseDisjoint hfrontier
        new.val.val new.val.property.1 new.val.property.2.1
        new.val.property.2.2.1 new.val.property.2.2.2
    obtain ⟨D,hD,hDcenter,hDclear,hDback,hDopen,P,hPs,hP⟩ :=
      RegionalFinitePosition.strip_square_package F new.val.val E hE hcenter
        (fun w => ⟨hBF (hend w).1,hBF (hend w).2⟩)
        (fun t ht w => (mem_interior_iff_notMem_frontier
          (interior_subset (hint t ht w))).mp (hint t ht w)) hopen
    have charts (i : κ) : ∃ Q : OpenPartialHomeomorph S Schoenflies.Plane,
        (∀ t ∈ Set.Ioo (0:Interval) 1, ((old i).val.val t).val ∈ Q.source) ∧
        ∀ z ∈ Q.source, z ∈ Set.range (fun s => ((old i).val.val s).val) → Q z 1 = 0 := by
      obtain ⟨N,hN,hNc,hNend,hNint,hNopen⟩ :=
        regional_original_proper_arc_has_F_strip S g hg hS x R hR htarget
          F hFcompact hbase houtside J c hbaseDisjoint hfrontier
          (old i).val.val (old i).val.property.1 (old i).val.property.2.1
          (old i).val.property.2.2.1 (old i).val.property.2.2.2
      let aS : C(Interval,S) := ⟨fun t => ((old i).val.val t).val,
        continuous_subtype_val.comp (old i).val.val.continuous⟩
      obtain ⟨Q,hQs,hQt,hQcoord,hQaxis⟩ := source_embedded_strip_interior_chart
        (fun z => (N z).val) (Topology.IsEmbedding.subtypeVal.comp hN) aS
        (fun t => congrArg Subtype.val (hNc t))
      refine ⟨Q,?_,fun z hz ha => (hQaxis z hz).mp ha⟩
      intro t ht
      rw [hQs]
      refine ⟨(t,⟨0,by norm_num⟩),⟨ht.1,ht.2,by norm_num,by norm_num⟩,
        congrArg Subtype.val (hNc t)⟩
    choose Q hQa hQaxis using charts
    obtain ⟨q,hq,hq0,hq1,hqclear,hqfinite,K,hKB,hKF,hKmove⟩ :=
      square_finite_family_ambient F B hFcompact hBF new.val.val new.val.property.1
        new.val.property.2.1 new.val.property.2.2.1 new.val.property.2.2.2
        D hD hDcenter hDclear P hPs hP (fun i => (old i).val.val)
        (fun i => hBF (old i).val.property.2.1)
        (fun i => hBF (old i).val.property.2.2.1)
        Q hQa hQaxis hκfinite hκ0 hκ1
    have hqess := (regional_essential_arc_ambient_transport F B
      new.val.val q K (hKB 1) hKmove).mp new.property
    let copy : Arc := ⟨⟨q,hq,hq0 ▸ new.val.property.2.1,
      hq1 ▸ new.val.property.2.2.1,hqclear⟩,hqess⟩
    exact ⟨copy,(Quot.sound (show rel new copy from ⟨K,hKB,hKF,hKmove⟩)).symm,
      hq0,hq1,hqfinite⟩
  obtain ⟨b,hbclass,hbends,hbfinite,hbanchor⟩ := contactAssembly
    (fun d : Arc => d.val.val) (fun d : Arc => Quot.mk rel d)
    {y : ↥F | y.val ∈ frontier F}
    (fun d => ⟨hBF d.val.property.2.1,hBF d.val.property.2.2.1⟩)
    boundaryRange extend a givenAnchor hpair hzero hone
  refine ⟨b,givenAnchor,fun i => (hbclass i).trans (hclass i),rfl,
    hbfinite,?_,?_,?_,hbanchor⟩
  · intro i j hij
    simpa only [(hbends i).1,(hbends i).2,(hbends j).1,(hbends j).2] using hpair i j hij
  · intro i
    apply boundaryRange (b i) (givenAnchor.val.val 0) (hBF givenAnchor.val.property.2.1)
    · rw [(hbends i).1]
      exact fun h => hzero i ⟨0,h.symm⟩
    · rw [(hbends i).2]
      exact fun h => hzero i ⟨1,h.symm⟩
  · intro i
    apply boundaryRange (b i) (givenAnchor.val.val 1) (hBF givenAnchor.val.property.2.2.1)
    · rw [(hbends i).1]
      exact fun h => hone i ⟨0,h.symm⟩
    · rw [(hbends i).2]
      exact fun h => hone i ⟨1,h.symm⟩

#print axioms regional_original_intrinsic_finite_family_pair_contact_position
