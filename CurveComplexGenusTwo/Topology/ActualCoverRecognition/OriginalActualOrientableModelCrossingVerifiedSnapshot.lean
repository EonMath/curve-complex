import Mathlib
import ClassificationOfSurfaces.RepresentativeCarrier
import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import ClassificationJordanCurve.Arcs
import CurveComplexGenusTwo.Topology.SourceCycleActual.SourceEssentialCurveComplete
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
open Set Topology ClassificationJordanCurve.Arcs LeanEval.Topology.ClassificationOfSurfaces
open scoped Manifold ContDiff
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
private theorem quotient_interior (p n : ℕ) (x y : Complex.ClosedUnitDisc)
    (h : Quot.mk (OrientableRel p n) x = Quot.mk (OrientableRel p n) y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
  have hboundary {x y : Complex.ClosedUnitDisc} (h : OrientableRel p n x y) :
      ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 := by
    cases h <;> simp [Complex.ClosedUnitDisc.bdyPtOfReal]
  have hgeneral : ∀ x y : Complex.ClosedUnitDisc,
      Relation.EqvGen (OrientableRel p n) x y →
        x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
    intro x y heq
    induction heq with
    | rel a b hr => exact Or.inr (hboundary hr)
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with ih | ⟨ha,hb⟩
      · exact Or.inl ih.symm
      · exact Or.inr ⟨hb,ha⟩
    | trans a b c _ _ hab hbc =>
      rcases hab with rfl | ⟨ha,hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨hb,hc⟩
        · exact Or.inr ⟨ha,hb⟩
        · exact Or.inr ⟨ha,hc⟩
  exact hgeneral x y (Quot.eqvGen_exact h)

private theorem chordCurve {U : Type} [TopologicalSpace U] [T2Space U]
    (p n : ℕ) (f : Quot (OrientableRel p n) → U) (hf : IsEmbedding f)
    (x y : Complex.ClosedUnitDisc) (hne : x ≠ y)
    (hclose : Quot.mk (OrientableRel p n) x = Quot.mk (OrientableRel p n) y) :
    ∃ c : CurveComplex.Curve U,
      c.image = (f ∘ Quot.mk (OrientableRel p n)) ''
        {z : Complex.ClosedUnitDisc | (z : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ)} := by
  let q := Quot.mk (OrientableRel p n)
  have hne' : (x : ℂ) ≠ (y : ℂ) := fun h => hne (Subtype.ext h)
  let γ : Path x y :=
    { toFun := fun t => ⟨AffineMap.lineMap (x : ℂ) (y : ℂ) (t : ℝ),
        (convex_closedBall (0 : ℂ) 1).lineMap_mem x.property y.property t.property⟩
      continuous_toFun := by fun_prop
      source' := by apply Subtype.ext; simp
      target' := by apply Subtype.ext; simp }
  let l : Path (f (q x)) (f (q x)) :=
    ((γ.map continuous_quot_mk).map hf.continuous).cast rfl
      (congrArg f hclose)
  have hint (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
      ‖(γ t : ℂ)‖ < 1 := by
    have ht0' : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1
      (fun h => ht0 (Subtype.ext h.symm))
    have ht1' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
      (fun h => ht1 (Subtype.ext h))
    change ‖AffineMap.lineMap (x : ℂ) (y : ℂ) (t : ℝ)‖ < 1
    rw [AffineMap.lineMap_apply_module]
    exact norm_combo_lt_of_ne (by simpa only [Metric.mem_closedBall, dist_zero_right] using x.property) (by simpa only [Metric.mem_closedBall, dist_zero_right] using y.property) hne'
      (by linarith) ht0' (by ring)
  have hcoll : ∀ s t : CurveComplex.Interval, l s = l t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
    intro s t h
    have heq : q (γ s) = q (γ t) := hf.injective h
    rcases quotient_interior p n _ _ heq with heq | ⟨hs, ht⟩
    · apply Or.inl
      apply Subtype.ext
      exact AffineMap.lineMap_injective ℝ hne' (congrArg Subtype.val heq)
    · have hsEnd : s = 0 ∨ s = 1 := by
        by_contra hEnd
        push_neg at hEnd
        linarith [hint s hEnd.1 hEnd.2]
      have htEnd : t = 0 ∨ t = 1 := by
        by_contra hEnd
        push_neg at hEnd
        linarith [hint t hEnd.1 hEnd.2]
      rcases hsEnd with rfl | rfl <;> rcases htEnd with rfl | rfl <;> simp
  obtain ⟨c,hc⟩ := CurveComplexGenusTwo.SourceTopology.simple_loop_gives_embedded_curve _ l hcoll
  refine ⟨c,hc.trans ?_⟩
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨γ t, by
      change AffineMap.lineMap (x : ℂ) (y : ℂ) (t : ℝ) ∈ segment ℝ (x : ℂ) (y : ℂ)
      rw [segment_eq_image_lineMap]
      exact ⟨t,t.property,rfl⟩,rfl⟩
  · rintro ⟨w,hw,rfl⟩
    rw [segment_eq_image_lineMap] at hw
    obtain ⟨t,ht,heq⟩ := hw
    refine ⟨⟨t,ht⟩,?_⟩
    have hwγ : γ ⟨t,ht⟩ = w := Subtype.ext heq
    change f (q (γ ⟨t,ht⟩)) = f (q w)
    rw [hwγ]

private theorem angleInjective {r s : ℝ} (hr : r ∈ Ico 0 1) (hs : s ∈ Ico 0 1)
    (h : Complex.ClosedUnitDisc.bdyPtOfReal r =
      Complex.ClosedUnitDisc.bdyPtOfReal s) : r = s := by
  let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hparam (t : ℝ) : H (t : AddCircle (1 : ℝ)) = Real.fourierChar t := by
    simp only [H, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
      div_one, Real.fourierChar_apply']
  have hc : Real.fourierChar r = Real.fourierChar s := by
    apply Subtype.ext
    exact congrArg (fun z : Complex.ClosedUnitDisc => (z : ℂ)) h
  rw [← hparam r, ← hparam s] at hc
  have heq := H.injective hc
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0) (by simpa using hr)
    (by simpa using hs)).mp heq

private theorem actualPair {U : Type} [TopologicalSpace U] [T2Space U]
    (p n : ℕ) (hp : 1 ≤ p)
    (f : Quot (OrientableRel p n) → U) (hf : IsEmbedding f) :
    ∃ a b : CurveComplex.Curve U,
      a.image = (f ∘ Quot.mk (OrientableRel p n)) ''
        {z : Complex.ClosedUnitDisc | (z : ℂ) ∈ segment ℝ
          (Complex.ClosedUnitDisc.bdyPtOfReal ((1/2 : ℝ)/(4*p+3*n)) : ℂ)
          (Complex.ClosedUnitDisc.bdyPtOfReal ((5/2 : ℝ)/(4*p+3*n)) : ℂ)} ∧
      b.image = (f ∘ Quot.mk (OrientableRel p n)) ''
        {z : Complex.ClosedUnitDisc | (z : ℂ) ∈ segment ℝ
          (Complex.ClosedUnitDisc.bdyPtOfReal ((3/2 : ℝ)/(4*p+3*n)) : ℂ)
          (Complex.ClosedUnitDisc.bdyPtOfReal ((7/2 : ℝ)/(4*p+3*n)) : ℂ)} := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hN : (0 : ℝ) < 4*p+3*n := by linarith
  have ha : Complex.ClosedUnitDisc.bdyPtOfReal ((1/2 : ℝ)/(4*p+3*n)) ≠
      Complex.ClosedUnitDisc.bdyPtOfReal ((5/2 : ℝ)/(4*p+3*n)) := by
    intro heq
    have h := angleInjective
      ⟨by positivity, (div_lt_one hN).mpr (by linarith)⟩
      ⟨by positivity, (div_lt_one hN).mpr (by linarith)⟩ heq
    have := (div_left_inj' hN.ne').mp h
    norm_num at this
  have hb : Complex.ClosedUnitDisc.bdyPtOfReal ((3/2 : ℝ)/(4*p+3*n)) ≠
      Complex.ClosedUnitDisc.bdyPtOfReal ((7/2 : ℝ)/(4*p+3*n)) := by
    intro heq
    have h := angleInjective
      ⟨by positivity, (div_lt_one hN).mpr (by linarith)⟩
      ⟨by positivity, (div_lt_one hN).mpr (by linarith)⟩ heq
    have := (div_left_inj' hN.ne').mp h
    norm_num at this
  let t : Icc (0 : ℝ) 1 := ⟨1/2, by norm_num⟩
  let i : Fin p := ⟨0, by omega⟩
  have hca : Quot.mk (OrientableRel p n)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((1/2 : ℝ)/(4*p+3*n))) =
      Quot.mk (OrientableRel p n)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((5/2 : ℝ)/(4*p+3*n))) := by
    convert Quot.sound (OrientableRel.a (n := n) t i) using 1 <;>
      norm_num [t,i]
  have hcb : Quot.mk (OrientableRel p n)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((3/2 : ℝ)/(4*p+3*n))) =
      Quot.mk (OrientableRel p n)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((7/2 : ℝ)/(4*p+3*n))) := by
    convert Quot.sound (OrientableRel.b (n := n) t i) using 1 <;>
      norm_num [t,i]
  obtain ⟨a,haImage⟩ := chordCurve p n f hf _ _ ha hca
  obtain ⟨b,hbImage⟩ := chordCurve p n f hf _ _ hb hcb
  exact ⟨a,b,haImage,hbImage⟩

private theorem phase (p n : ℕ) (hp : 1 ≤ p) :
    ∃ ψ : C(Complex.ClosedUnitDisc, ℝ),
      (∀ x y, OrientableRel p n x y → ∃ k : ℤ, ψ x - ψ y = (k : ℝ)) ∧
      (∀ r ∈ Icc (0 : ℝ) (4*p+3*n),
        ψ (Complex.ClosedUnitDisc.bdyPtOfReal (r / (4*p+3*n))) =
          max 0 (min 1 (min r (3-r)))) := by
  have build (N peak width : ℝ) (hpeak : 0 ≤ peak) (hwidth : 0 ≤ width)
      (hN : width ≤ N) :
      ∃ φ : C(Circle,ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
        φ (Real.fourierChar t) = max 0 (min peak (min (N*t) (width-N*t))) := by
    have build : ∃ φ : C(AddCircle (1 : ℝ),ℝ), ∀ t ∈ Icc (0 : ℝ) 1,
        φ (t : AddCircle (1 : ℝ)) = max 0 (min peak (min (N*t) (width-N*t))) := by
      let u : ℝ → ℝ := fun t => max 0 (min peak (min (N*t) (width-N*t)))
      have h0 : u 0 = 0 := by simp [u, hwidth, hpeak]
      have h1 : u 1 = 0 := by
        apply max_eq_left
        exact (min_le_right _ _).trans ((min_le_right _ _).trans
          (by simpa only [mul_one] using sub_nonpos.mpr hN))
      have he : u 0 = u (0+1) := by simpa only [zero_add,h0,h1]
      have hc : Continuous u := by
        exact continuous_const.max (continuous_const.min
          ((continuous_const.mul continuous_id).min
            (continuous_const.sub (continuous_const.mul continuous_id))))
      let φ : C(AddCircle (1 : ℝ),ℝ) :=
        ⟨AddCircle.liftIco (1 : ℝ) 0 u, AddCircle.liftIco_continuous he hc.continuousOn⟩
      refine ⟨φ, ?_⟩
      intro t ht
      rcases lt_or_eq_of_le ht.2 with hlt | rfl
      · change AddCircle.liftIco (1 : ℝ) 0 u (t : AddCircle (1 : ℝ)) = u t
        exact AddCircle.liftIco_coe_apply (by simpa only [zero_add, Set.mem_Ico] using And.intro ht.1 hlt)
      · have hz : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
        rw [hz]
        change AddCircle.liftIco (1 : ℝ) 0 u (0 : AddCircle (1 : ℝ)) = u 1
        rw [← AddCircle.coe_zero, AddCircle.liftIco_coe_apply (by norm_num),h0,h1]
    obtain ⟨φ,hφ⟩ := build
    let H := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
    let ψ : C(Circle,ℝ) := φ.comp ⟨H.symm,H.symm.continuous⟩
    have hparam (t : ℝ) : H (t : AddCircle (1 : ℝ)) = Real.fourierChar t := by
      simp only [H, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
        div_one, Real.fourierChar_apply']
    refine ⟨ψ, ?_⟩
    intro t ht
    change φ (H.symm (Real.fourierChar t)) = _
    rw [← hparam t, H.symm_apply_apply]
    exact hφ t ht
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  let N : ℝ := 4*p+3*n
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hN : 4 ≤ N := by dsimp [N]; linarith
  have hNpos : 0 < N := by linarith
  obtain ⟨φ,hφ⟩ := build N 1 3 (by norm_num) (by norm_num) (by linarith)
  let e : Circle → Complex.ClosedUnitDisc := fun z => ⟨z, by simp⟩
  have hec : Continuous e := continuous_subtype_val.subtype_mk _
  have hei : Function.Injective e := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : Complex.ClosedUnitDisc => (z : ℂ)) h)
  have he : IsClosedEmbedding e := hec.isClosedEmbedding hei
  obtain ⟨ψ,hψ⟩ := φ.exists_extension he
  have agrees (z : Circle) : ψ (e z) = φ z := congrArg (fun f : C(Circle,ℝ) => f z) hψ
  let q : ℝ → ℝ := fun r => max 0 (min 1 (min r (3-r)))
  have value (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
      ψ (Complex.ClosedUnitDisc.bdyPtOfReal (r/N)) = q r := by
    change ψ (e (Real.fourierChar (r/N))) = q r
    rw [agrees]
    have ht : r/N ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hr0 hNpos.le, (div_le_one hNpos).mpr hrN⟩
    rw [hφ _ ht]
    dsimp [q]
    rw [mul_div_cancel₀ r hNpos.ne']
  have valueNeg (r : ℝ) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
      ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-r/N)) = q (N-r) := by
    have hperiod := Complex.ClosedUnitDisc.bdyPtOfReal_add_int (-r/N) 1
    have hh : -r/N + (1:ℤ) = (N-r)/N := by field_simp; ring
    rw [hh] at hperiod
    rw [← hperiod]
    exact value _ (by linarith) (by linarith)
  have qlow (t : ℝ) (ht : t ∈ Icc 0 1) : q t = t := by
    dsimp [q]
    rw [min_eq_left (by linarith [ht.2] : t ≤ 3-t), min_eq_right ht.2, max_eq_right ht.1]
  have qhigh (r : ℝ) (hr : 3 ≤ r) : q r = 0 := by
    dsimp [q]
    apply max_eq_left
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (by linarith))
  refine ⟨ψ, ?_, ?_⟩
  · intro x y hxy
    cases hxy with
    | a t i =>
      have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
      have hi0 : (0 : ℝ) ≤ i := by positivity
      have ht0 := t.property.1
      have ht1 := t.property.2
      change ∃ k : ℤ,
        ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+(t:ℝ))/N)) -
        ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+3-(t:ℝ))/N)) = (k:ℝ)
      rw [value _ (by linarith) (by dsimp [N]; linarith),
          value _ (by linarith) (by dsimp [N]; linarith)]
      by_cases hz : i.val = 0
      · have hi' : (i : ℝ) = 0 := by exact_mod_cast hz
        rw [hi']; simp only [mul_zero,zero_add]
        rw [qlow _ t.property]
        have hq : q (3-(t:ℝ)) = (t:ℝ) := by
          dsimp [q]
          rw [min_eq_right (by linarith : 3-(t:ℝ) ≥ 3-(3-(t:ℝ)))]
          have hh : 3-(3-(t:ℝ)) = (t:ℝ) := by ring
          rw [hh,min_eq_right ht1,max_eq_right ht0]
        rw [hq]
        exact ⟨0,by simp⟩
      · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i.val by omega)
        rw [qhigh _ (by linarith), qhigh _ (by linarith)]
        exact ⟨0,by simp⟩
    | b t i =>
      have hi : (i : ℝ) + 1 ≤ p := by exact_mod_cast i.isLt
      have hi0 : (0 : ℝ) ≤ i := by positivity
      have ht0 := t.property.1
      have ht1 := t.property.2
      change ∃ k : ℤ,
        ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+1+(t:ℝ))/N)) -
        ψ (Complex.ClosedUnitDisc.bdyPtOfReal ((4*(i:ℝ)+4-(t:ℝ))/N)) = (k:ℝ)
      rw [value _ (by linarith) (by dsimp [N]; linarith),
          value _ (by linarith) (by dsimp [N]; linarith)]
      by_cases hz : i.val = 0
      · have hi' : (i : ℝ) = 0 := by exact_mod_cast hz
        rw [hi']; simp only [mul_zero,zero_add]
        have hq : q (1+(t:ℝ)) = 1 := by
          dsimp [q]
          rw [min_eq_left (le_min (by linarith) (by linarith)), max_eq_right (by norm_num)]
        rw [hq,qhigh _ (by linarith)]
        exact ⟨1,by simp⟩
      · have hi' : (1 : ℝ) ≤ i := by exact_mod_cast (show 1 ≤ i.val by omega)
        rw [qhigh _ (by linarith), qhigh _ (by linarith)]
        exact ⟨0,by simp⟩
    | c t i =>
      have hi : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      have hi0 : (0 : ℝ) ≤ i := by positivity
      have ht0 := t.property.1
      have ht1 := t.property.2
      change ∃ k : ℤ,
        ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+(t:ℝ))/N)) -
        ψ (Complex.ClosedUnitDisc.bdyPtOfReal (-(3*(i:ℝ)+3-(t:ℝ))/N)) = (k:ℝ)
      rw [valueNeg _ (by linarith) (by dsimp [N]; linarith),
          valueNeg _ (by linarith) (by dsimp [N]; linarith)]
      rw [qhigh _ (by dsimp [N]; linarith), qhigh _ (by dsimp [N]; linarith)]
      exact ⟨0,by simp⟩
  · intro r hr
    exact value r hr.1 hr.2

private theorem endpointSeparation (p n : ℕ) (hp : 1 ≤ p) :
    Quot.mk (OrientableRel p n)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((1/2 : ℝ)/(4*p+3*n))) ≠
    Quot.mk (OrientableRel p n)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((3/2 : ℝ)/(4*p+3*n))) := by
  obtain ⟨ψ, hrel, hv⟩ := phase p n hp
  have hgen : ∀ x y, Relation.EqvGen (OrientableRel p n) x y →
      ∃ k : ℤ, ψ x - ψ y = (k : ℝ) := by
    intro x y h
    induction h with
    | rel x y h => exact hrel x y h
    | refl x => exact ⟨0, by simp⟩
    | symm x y h ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨-k, by push_cast; linarith⟩
    | trans x y z hxy hyz ihxy ihyz =>
      obtain ⟨k, hk⟩ := ihxy
      obtain ⟨l, hl⟩ := ihyz
      exact ⟨k+l, by push_cast; linarith⟩
  intro heq
  obtain ⟨k, hk⟩ := hgen _ _ (Quot.eqvGen_exact heq)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnR : (0 : ℝ) ≤ n := by positivity
  rw [hv _ ⟨by norm_num, by linarith⟩,
      hv _ ⟨by norm_num, by linarith⟩] at hk
  norm_num at hk
  have hk0 : k < 0 := by exact_mod_cast (show (k : ℝ) < 0 by linarith)
  have hk1 : -1 < k := by exact_mod_cast (show (-1 : ℝ) < k by linarith)
  omega

private theorem symmetricChordIntersection (u w v z : ℝ) (huw : u < w) (hv : 0 < v) (hz : 0 < z) :
    segment ℝ (Complex.mk u (-v)) (Complex.mk w z) ∩
      segment ℝ (Complex.mk w (-z)) (Complex.mk u v) =
    {Complex.mk ((z*u+v*w)/(v+z)) 0} := by
  have hd : 0 < v+z := by linarith
  have hw : w-u ≠ 0 := by linarith
  ext q
  rw [mem_inter_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hqa,hqb⟩
    rw [segment_eq_image_lineMap] at hqa hqb
    obtain ⟨a,ha,hqa⟩ := hqa
    obtain ⟨b,hb,hqb⟩ := hqb
    have hr := congrArg Complex.re (hqa.trans hqb.symm)
    have hi := congrArg Complex.im (hqa.trans hqb.symm)
    simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im] at hr hi
    dsimp at hr hi
    have hmul : (w-u)*(a+b-1)=0 := by nlinarith [hr]
    have hab : a+b=1 := by
      have := (mul_eq_zero.mp hmul).resolve_left hw
      linarith
    have hav : (v+z)*a=v := by nlinarith [hi,hab]
    have hae : a=v/(v+z) := by apply (eq_div_iff hd.ne').mpr; nlinarith
    rw [← hqa,hae]
    apply Complex.ext
    · simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im]
      dsimp
      field_simp
      ring
    · simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im]
      dsimp
      field_simp
      ring
  · intro hq
    subst q
    constructor
    · rw [segment_eq_image_lineMap]
      refine ⟨v/(v+z),⟨by positivity,(div_le_one hd).mpr (by linarith)⟩,?_⟩
      apply Complex.ext <;>
        simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im] <;>
        dsimp <;>
        field_simp <;> ring
    · rw [segment_eq_image_lineMap]
      refine ⟨z/(v+z),⟨by positivity,(div_le_one hd).mpr (by linarith)⟩,?_⟩
      apply Complex.ext <;>
        simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im] <;>
        dsimp <;>
        field_simp <;> ring

private theorem rotationLine (R x y : ℂ) (t : ℝ) :
    R * AffineMap.lineMap x y t = AffineMap.lineMap (R*x) (R*y) t := by
  simp only [AffineMap.lineMap_apply_module,mul_add,mul_smul_comm]
private theorem rotationSegment (R q x y : ℂ) (hR : R ≠ 0) :
    R*q ∈ segment ℝ (R*x) (R*y) ↔ q ∈ segment ℝ x y := by
  simp only [segment_eq_image_lineMap,mem_image]
  constructor
  · rintro ⟨t,ht,heq⟩
    refine ⟨t,ht,?_⟩
    apply mul_left_cancel₀ hR
    rw [rotationLine]
    exact heq
  · rintro ⟨t,ht,heq⟩
    refine ⟨t,ht,?_⟩
    rw [← rotationLine,heq]

private theorem rotationCoordinates (r s : ℝ) :
    (Real.fourierChar r : ℂ) * (Complex.ClosedUnitDisc.bdyPtOfReal s : ℂ) =
      Complex.mk (Real.cos (2*Real.pi*(r+s))) (Real.sin (2*Real.pi*(r+s))) := by
  change ((Real.fourierChar r * Real.fourierChar s : Circle) : ℂ) = _
  rw [← AddChar.map_add_eq_mul]
  apply Complex.ext
  · change (Complex.exp (((2*Real.pi*(r+s) : ℝ) : ℂ)*Complex.I)).re = _
    exact Complex.exp_ofReal_mul_I_re _
  · change (Complex.exp (((2*Real.pi*(r+s) : ℝ) : ℂ)*Complex.I)).im = _
    exact Complex.exp_ofReal_mul_I_im _
private theorem actualRotatedCoordinates (p n : ℕ) (hp : 1 ≤ p) :
    let N : ℝ := 4*p+3*n
    let δ := Real.pi/N
    let R : ℂ := Real.fourierChar (-2/N)
    R * (Complex.ClosedUnitDisc.bdyPtOfReal ((1/2)/N) : ℂ) =
        Complex.mk (Real.cos (3*δ)) (-Real.sin (3*δ)) ∧
    R * (Complex.ClosedUnitDisc.bdyPtOfReal ((5/2)/N) : ℂ) =
        Complex.mk (Real.cos δ) (Real.sin δ) ∧
    R * (Complex.ClosedUnitDisc.bdyPtOfReal ((3/2)/N) : ℂ) =
        Complex.mk (Real.cos δ) (-Real.sin δ) ∧
    R * (Complex.ClosedUnitDisc.bdyPtOfReal ((7/2)/N) : ℂ) =
        Complex.mk (Real.cos (3*δ)) (Real.sin (3*δ)) := by
  dsimp only
  have h1 : 2*Real.pi*(-2/(4*(p:ℝ)+3*n)+(1/2)/(4*p+3*n)) =
      -(3*(Real.pi/(4*p+3*n))) := by ring
  have h2 : 2*Real.pi*(-2/(4*(p:ℝ)+3*n)+(5/2)/(4*p+3*n)) =
      Real.pi/(4*p+3*n) := by ring
  have h3 : 2*Real.pi*(-2/(4*(p:ℝ)+3*n)+(3/2)/(4*p+3*n)) =
      -(Real.pi/(4*p+3*n)) := by ring
  have h4 : 2*Real.pi*(-2/(4*(p:ℝ)+3*n)+(7/2)/(4*p+3*n)) =
      3*(Real.pi/(4*p+3*n)) := by ring
  simp only [rotationCoordinates,h1,h2,h3,h4,Real.cos_neg,Real.sin_neg]
  simp

private theorem actualChordSigns (p n : ℕ) (hp : 1 ≤ p) :
    let δ : ℝ := Real.pi/(4*p+3*n)
    Real.cos (3*δ) < Real.cos δ ∧
      0 < Real.sin (3*δ) ∧ 0 < Real.sin δ := by
  dsimp only
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hN : (4 : ℝ) ≤ 4*p+3*n := by linarith
  have hNpos : (0 : ℝ) < 4*p+3*n := by linarith
  have hdpos : 0 < Real.pi/(4*p+3*n) := div_pos Real.pi_pos hNpos
  have hdBound : Real.pi/(4*p+3*n) ≤ Real.pi/4 := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hN
  have h3 : 3*(Real.pi/(4*p+3*n)) < Real.pi := by
    linarith [Real.pi_pos]
  exact ⟨Real.cos_lt_cos_of_nonneg_of_le_pi hdpos.le h3.le (by linarith),
    Real.sin_pos_of_pos_of_lt_pi (by linarith) h3,
    Real.sin_pos_of_pos_of_lt_pi hdpos (by linarith)⟩

private theorem rawIntersection (p n : ℕ) (hp : 1 ≤ p) :
    let N : ℝ := 4*p+3*n
    let δ := Real.pi/N
    let R : ℂ := Real.fourierChar (-2/N)
    let c := Complex.mk
      ((Real.sin δ * Real.cos (3*δ) + Real.sin (3*δ) * Real.cos δ)/
        (Real.sin (3*δ)+Real.sin δ)) 0
    segment ℝ
      (Complex.ClosedUnitDisc.bdyPtOfReal ((1/2)/N) : ℂ)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((5/2)/N) : ℂ) ∩
    segment ℝ
      (Complex.ClosedUnitDisc.bdyPtOfReal ((3/2)/N) : ℂ)
      (Complex.ClosedUnitDisc.bdyPtOfReal ((7/2)/N) : ℂ) = {c/R} := by
  dsimp only
  let N : ℝ := 4*p+3*n
  let δ := Real.pi/N
  let R : ℂ := Real.fourierChar (-2/N)
  obtain ⟨hA,hC,hB,hD⟩ := actualRotatedCoordinates p n hp
  obtain ⟨hcos,hsin3,hsin⟩ := actualChordSigns p n hp
  have hR : R ≠ 0 := Circle.coe_ne_zero _
  have hbase := symmetricChordIntersection _ _ _ _ hcos hsin3 hsin
  ext q
  rw [mem_inter_iff,mem_singleton_iff]
  have hA' := rotationSegment R q
    (Complex.ClosedUnitDisc.bdyPtOfReal ((1/2)/N))
    (Complex.ClosedUnitDisc.bdyPtOfReal ((5/2)/N)) hR
  have hB' := rotationSegment R q
    (Complex.ClosedUnitDisc.bdyPtOfReal ((3/2)/N))
    (Complex.ClosedUnitDisc.bdyPtOfReal ((7/2)/N)) hR
  change _ ↔ q = _
  rw [← hA',← hB']
  dsimp only [R,N] at hA' hB' ⊢
  rw [hA,hC,hB,hD,← mem_inter_iff,hbase,mem_singleton_iff]
  rw [eq_div_iff hR,mul_comm]

private theorem quotientInterior (p n : ℕ) (x y : Complex.ClosedUnitDisc)
    (h : Quot.mk (OrientableRel p n) x = Quot.mk (OrientableRel p n) y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
  have hboundary {x y : Complex.ClosedUnitDisc} (h : OrientableRel p n x y) :
      ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 := by
    cases h <;> simp [Complex.ClosedUnitDisc.bdyPtOfReal]
  have hgeneral : ∀ x y : Complex.ClosedUnitDisc,
      Relation.EqvGen (OrientableRel p n) x y →
        x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
    intro x y heq
    induction heq with
    | rel a b hr => exact Or.inr (hboundary hr)
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with ih | ⟨ha,hb⟩
      · exact Or.inl ih.symm
      · exact Or.inr ⟨hb,ha⟩
    | trans a b c _ _ hab hbc =>
      rcases hab with rfl | ⟨ha,hb⟩
      · exact hbc
      · rcases hbc with rfl | ⟨hb,hc⟩
        · exact Or.inr ⟨ha,hb⟩
        · exact Or.inr ⟨ha,hc⟩
  exact hgeneral x y (Quot.eqvGen_exact h)

private theorem boundaryEndpoints (x y z : Complex.ClosedUnitDisc) (hne : x ≠ y)
    (hz : (z : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ))
    (hnorm : ‖(z : ℂ)‖ = 1) : z = x ∨ z = y := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t,ht,heq⟩ := hz
  by_cases ht0 : t = 0
  · left
    apply Subtype.ext
    simpa [ht0] using heq.symm
  by_cases ht1 : t = 1
  · right
    apply Subtype.ext
    simpa [ht1] using heq.symm
  have hne' : (x : ℂ) ≠ (y : ℂ) := fun h => hne (Subtype.ext h)
  have hlt : ‖AffineMap.lineMap (x : ℂ) (y : ℂ) t‖ < 1 := by
    rw [AffineMap.lineMap_apply_module]
    exact norm_combo_lt_of_ne
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using y.property)
      hne' (by have := lt_of_le_of_ne ht.2 ht1; linarith)
      (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (by ring)
  rw [heq,hnorm] at hlt
  linarith

private theorem projectedSingleton {U : Type} [TopologicalSpace U] (p n : ℕ)
    (f : Quot (OrientableRel p n) → U) (hf : Function.Injective f)
    (x y x' y' r : Complex.ClosedUnitDisc) (hne : x ≠ y) (hne' : x' ≠ y')
    (hclose : Quot.mk (OrientableRel p n) x = Quot.mk (OrientableRel p n) y)
    (hclose' : Quot.mk (OrientableRel p n) x' = Quot.mk (OrientableRel p n) y')
    (hsep : Quot.mk (OrientableRel p n) x ≠ Quot.mk (OrientableRel p n) x')
    (hraw : segment ℝ (x : ℂ) (y : ℂ) ∩ segment ℝ (x' : ℂ) (y' : ℂ) = {(r : ℂ)}) :
    (f ∘ Quot.mk (OrientableRel p n)) ''
      {z : Complex.ClosedUnitDisc | (z : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ)} ∩
    (f ∘ Quot.mk (OrientableRel p n)) ''
      {z : Complex.ClosedUnitDisc | (z : ℂ) ∈ segment ℝ (x' : ℂ) (y' : ℂ)} =
      {f (Quot.mk (OrientableRel p n) r)} := by
  let q := Quot.mk (OrientableRel p n)
  ext a
  constructor
  · rintro ⟨⟨z,hz,rfl⟩,⟨w,hw,heq⟩⟩
    have hzw : q z = q w := (hf heq).symm
    rcases quotientInterior p n z w hzw with hzw | ⟨hzNorm,hwNorm⟩
    · subst w
      have hzRaw : (z : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ) ∩
          segment ℝ (x' : ℂ) (y' : ℂ) := ⟨hz,hw⟩
      rw [hraw] at hzRaw
      have hzr : z = r := Subtype.ext hzRaw
      simp only [mem_singleton_iff,Function.comp_apply]
      rw [hzr]
    · rcases boundaryEndpoints x y z hne hz hzNorm with rfl | rfl <;>
        rcases boundaryEndpoints x' y' w hne' hw hwNorm with rfl | rfl
      · exact False.elim (hsep hzw)
      · exact False.elim (hsep (hzw.trans hclose'.symm))
      · exact False.elim (hsep (hclose.trans hzw))
      · exact False.elim (hsep (hclose.trans (hzw.trans hclose'.symm)))
  · intro ha
    have ha' : a = f (q r) := ha
    rw [ha']
    have hr : (r : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ) ∩
        segment ℝ (x' : ℂ) (y' : ℂ) := by rw [hraw]; exact mem_singleton _
    exact ⟨⟨r,hr.1,rfl⟩,⟨r,hr.2,rfl⟩⟩

private theorem openRegion {U : Type} [TopologicalSpace U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
    (O : Set (EuclideanSpace ℝ (Fin 2))) (hO : IsOpen O)
    (g : O → U) (hc : Continuous g) (hi : Function.Injective g) :
    IsOpenEmbedding g := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨hc,hi,?_⟩
  intro W hW
  by_cases hEmpty : O = ∅
  · have hWEmpty : W = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      simpa [hEmpty] using x.property
    simp [hWEmpty]
  obtain ⟨o,ho⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  let F : EuclideanSpace ℝ (Fin 2) → U :=
    Function.extend Subtype.val g (fun _ => g ⟨o,ho⟩)
  have hFg (z : O) : F z = g z := Subtype.val_injective.extend_apply _ _ z
  have hFc : ContinuousOn F O := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : O.domRestrict F = g := funext hFg
    rw [heq]
    exact hc
  have hFi : InjOn F O := by
    intro a ha b hb he
    have he' : g ⟨a,ha⟩ = g ⟨b,hb⟩ := by
      rw [←hFg ⟨a,ha⟩,←hFg ⟨b,hb⟩]
      exact he
    exact congrArg Subtype.val (hi he')
  let V : Set (EuclideanSpace ℝ (Fin 2)) := Subtype.val '' W
  have hV : IsOpen V := hO.isOpenEmbedding_subtypeVal.isOpenMap _ hW
  have hVO : V ⊆ O := by rintro z ⟨w,hw,rfl⟩; exact w.property
  have hopen : IsOpen (F '' V) := CurveComplex.surface_invariance_of_domain_probe
    F V hV (hFc.mono hVO) (hFi.mono hVO)
  have heq : F '' V = g '' W := by
    ext z
    constructor
    · rintro ⟨a,⟨w,hw,rfl⟩,rfl⟩
      exact ⟨w,hw,(hFg w).symm⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w,⟨w,hw,rfl⟩,hFg w⟩
  rwa [heq] at hopen

private theorem actualOpen {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
    (p n : ℕ) (f : Quot (OrientableRel p n) → U) (hf : IsEmbedding f) :
    IsOpenEmbedding (fun z : Metric.ball (0 : ℂ) 1 =>
      f (Quot.mk (OrientableRel p n)
        (⟨z.val,Metric.ball_subset_closedBall z.property⟩ : Complex.ClosedUnitDisc))) := by
  let j : Metric.ball (0 : ℂ) 1 → Complex.ClosedUnitDisc := fun z =>
    ⟨z.val,Metric.ball_subset_closedBall z.property⟩
  let g : Metric.ball (0 : ℂ) 1 → U := f ∘ Quot.mk (OrientableRel p n) ∘ j
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hg : Continuous g := hf.continuous.comp (continuous_quot_mk.comp hj)
  have hgi : Function.Injective g := by
    intro z w h
    rcases quotientInterior p n (j z) (j w) (hf.injective h) with h | ⟨hz,hw⟩
    · exact Subtype.ext (congrArg (fun v : Complex.ClosedUnitDisc => (v : ℂ)) h)
    · have hzlt : ‖z.val‖ < 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using z.property
      change ‖z.val‖ = 1 at hz
      linarith
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ ℂ := complexLIE.toHomeomorph.symm
  let O : Set (EuclideanSpace ℝ (Fin 2)) := e ⁻¹' Metric.ball (0 : ℂ) 1
  have hO : IsOpen O := Metric.isOpen_ball.preimage e.continuous
  let E : O ≃ₜ Metric.ball (0 : ℂ) 1 := e.subtype (fun _ => Iff.rfl)
  have hk : IsOpenEmbedding (g ∘ E) := openRegion O hO (g ∘ E)
    (hg.comp E.continuous) (hgi.comp E.injective)
  have hgOpen : IsOpenEmbedding g := by
    convert hk.comp E.symm.isOpenEmbedding using 1
    ext z
    exact congrArg g (E.apply_symm_apply z).symm
  exact hgOpen

private theorem actualTrace {U : Type} [TopologicalSpace U]
    (p n : ℕ) (f : Quot (OrientableRel p n) → U) (hf : Function.Injective f)
    (x y z : Complex.ClosedUnitDisc) (hz : ‖(z : ℂ)‖ < 1)
    (a : CurveComplex.Curve U)
    (ha : a.image = (f ∘ Quot.mk (OrientableRel p n)) ''
      {w : Complex.ClosedUnitDisc | (w : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ)}) :
    f (Quot.mk (OrientableRel p n) z) ∈ a.image ↔
      (z : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ) := by
  rw [ha]
  constructor
  · rintro ⟨w,hw,heq⟩
    have heq' := hf heq
    rcases quotientInterior p n w z heq' with rfl | ⟨hwN,hzN⟩
    · exact hw
    · linarith
  · intro hzSeg
    exact ⟨z,hzSeg,rfl⟩

private theorem chordTrace (u w v z : ℝ) (hv : 0 < v) (hz : 0 < z) (q : ℂ) :
    q ∈ segment ℝ (Complex.mk u (-v)) (Complex.mk w z) ↔
      (v+z)*q.re-(w-u)*q.im=z*u+v*w ∧ -v ≤ q.im ∧ q.im ≤ z := by
  have hd : 0 < v+z := by linarith
  rw [segment_eq_image_lineMap]
  constructor
  · rintro ⟨t,ht,rfl⟩
    simp only [AffineMap.lineMap_apply_module,Complex.add_re,Complex.add_im,
      Complex.smul_re,Complex.smul_im]
    dsimp
    refine ⟨by ring,?_,?_⟩ <;> nlinarith [ht.1,ht.2]
  · rintro ⟨hline,hlo,hhi⟩
    let t : ℝ := (q.im+v)/(v+z)
    have ht : t ∈ Icc 0 1 := by
      refine ⟨div_nonneg (by linarith) hd.le,?_⟩
      exact (div_le_one hd).mpr (by linarith)
    refine ⟨t,ht,?_⟩
    apply Complex.ext
    · simp only [AffineMap.lineMap_apply_module,Complex.add_re,Complex.smul_re]
      dsimp [t]
      field_simp
      nlinarith [hline]
    · simp only [AffineMap.lineMap_apply_module,Complex.add_im,Complex.smul_im]
      dsimp [t]
      field_simp
      ring

private theorem axesHomeo (u w v z : ℝ) (huw : u < w) (hv : 0 < v) (hz : 0 < z) :
    ∃ h : ℂ ≃ₜ (ℝ×ℝ), ∀ q : ℂ,
      h q = ((v+z)*q.re-(w-u)*q.im-(z*u+v*w),
        (v+z)*q.re+(w-u)*q.im-(z*u+v*w)) := by
  have hs : v+z ≠ 0 := by linarith
  have hd : w-u ≠ 0 := by linarith
  let h : ℂ ≃ₜ (ℝ×ℝ) :=
    { toEquiv :=
        { toFun := fun q => ((v+z)*q.re-(w-u)*q.im-(z*u+v*w),
            (v+z)*q.re+(w-u)*q.im-(z*u+v*w))
          invFun := fun xy => Complex.mk
            ((xy.1+xy.2+2*(z*u+v*w))/(2*(v+z)))
            ((xy.2-xy.1)/(2*(w-u)))
          left_inv := by
            intro q
            apply Complex.ext <;> dsimp <;> field_simp <;> ring
          right_inv := by
            intro xy
            apply Prod.ext <;> dsimp <;> field_simp <;> ring }
      continuous_toFun := by fun_prop
      continuous_invFun := by
        have hmk (a b : ℝ) : Complex.mk a b = (a : ℂ) + (b : ℂ)*Complex.I := by
          apply Complex.ext <;> simp
        simp only [hmk]
        fun_prop }
  exact ⟨h,fun _ => rfl⟩

private theorem crossingChart {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
    (p n : ℕ) (f : Quot (OrientableRel p n) → U) (hf : IsEmbedding f)
    (A C B D r : Complex.ClosedUnitDisc)
    (u w v z : ℝ) (huw : u < w) (hv : 0 < v) (hz : 0 < z)
    (R : ℂ) (hR : R ≠ 0)
    (hA : R*(A : ℂ)=Complex.mk u (-v))
    (hC : R*(C : ℂ)=Complex.mk w z)
    (hB : R*(B : ℂ)=Complex.mk w (-z))
    (hD : R*(D : ℂ)=Complex.mk u v)
    (hr : ‖(r : ℂ)‖ < 1)
    (hCenter : R*(r : ℂ)=Complex.mk ((z*u+v*w)/(v+z)) 0)
    (a b : CurveComplex.Curve U)
    (ha : a.image=(f ∘ Quot.mk (OrientableRel p n)) ''
      {q : Complex.ClosedUnitDisc | (q : ℂ) ∈ segment ℝ (A : ℂ) (C : ℂ)})
    (hb : b.image=(f ∘ Quot.mk (OrientableRel p n)) ''
      {q : Complex.ClosedUnitDisc | (q : ℂ) ∈ segment ℝ (B : ℂ) (D : ℂ)}) :
    CurveComplex.CrossesAt a b (f (Quot.mk (OrientableRel p n) r)) := by
  have hm : 0 < min v z := lt_min hv hz
  have hs : v+z ≠ 0 := by linarith
  obtain ⟨axes,haxes⟩ := axesHomeo u w v z huw hv hz
  let rot : ℂ ≃ₜ ℂ :=
    { toEquiv :=
        { toFun := fun q => R*q
          invFun := fun q => q/R
          left_inv := by intro q; field_simp
          right_inv := by intro q; field_simp }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let frame := rot.trans axes
  let O : Set (Metric.ball (0 : ℂ) 1) := {q | |(R*q.val).im| < min v z}
  have hO : IsOpen O := isOpen_lt (by fun_prop) continuous_const
  let Oraw : Set ℂ := {q | ‖q‖ < 1 ∧ |(R*q).im| < min v z}
  have hOraw : IsOpen Oraw :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt (by fun_prop : Continuous (fun q : ℂ => |(R*q).im|)) continuous_const)
  let E : O ≃ₜ Oraw :=
    { toEquiv :=
        { toFun := fun q => ⟨q.val.val,⟨by
            simpa only [Metric.mem_ball,dist_zero_right] using q.val.property,q.property⟩⟩
          invFun := fun q => ⟨⟨q.val,by
            simpa only [Metric.mem_ball,dist_zero_right] using q.property.1⟩,q.property.2⟩
          left_inv := by intro q; rfl
          right_inv := by intro q; rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let G : Metric.ball (0 : ℂ) 1 → U := fun q => f (Quot.mk (OrientableRel p n)
    (⟨q.val,Metric.ball_subset_closedBall q.property⟩ : Complex.ClosedUnitDisc))
  let g : O → U := G ∘ Subtype.val
  have hg : IsOpenEmbedding g := (actualOpen p n f hf).comp hO.isOpenEmbedding_subtypeVal
  let H := hg.isEmbedding.toHomeomorph.symm.trans (E.trans (frame.image Oraw))
  let r0 : Metric.ball (0 : ℂ) 1 := ⟨r.val,by
    simpa only [Metric.mem_ball,dist_zero_right] using hr⟩
  have hrO : r0 ∈ O := by
    change |(R*(r : ℂ)).im| < min v z
    rw [hCenter]
    simpa using hm
  let origin : O := ⟨r0,hrO⟩
  have hg0 : g origin=f (Quot.mk (OrientableRel p n) r) := rfl
  have hp : f (Quot.mk (OrientableRel p n) r) ∈ range g := ⟨origin,hg0⟩
  have hInv : hg.isEmbedding.toHomeomorph.symm ⟨f (Quot.mk (OrientableRel p n) r),hp⟩=origin := by
    apply hg.isEmbedding.toHomeomorph.injective
    rw [hg.isEmbedding.toHomeomorph.apply_symm_apply]
    exact Subtype.ext hg0.symm
  refine ⟨range g,frame '' Oraw,hp,H,hg.isOpen_range,frame.isOpenMap _ hOraw,?_,?_⟩
  · change frame (E (hg.isEmbedding.toHomeomorph.symm ⟨_,hp⟩))=(0,0)
    rw [hInv]
    change axes (R*(r : ℂ))=(0,0)
    rw [hCenter,haxes]
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  · intro x hx
    let q := hg.isEmbedding.toHomeomorph.symm ⟨x,hx⟩
    have hgq : g q=x := congrArg Subtype.val
      (hg.isEmbedding.toHomeomorph.apply_symm_apply ⟨x,hx⟩)
    let raw : Complex.ClosedUnitDisc := ⟨q.val.val,Metric.ball_subset_closedBall q.val.property⟩
    have hNorm : ‖(raw : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball,dist_zero_right] using q.val.property
    have hAbs : |(R*(raw : ℂ)).im| < min v z := q.property
    have hy : -min v z < (R*(raw : ℂ)).im ∧ (R*(raw : ℂ)).im < min v z := abs_lt.mp hAbs
    have htA := actualTrace p n f hf.injective A C raw hNorm a ha
    have htB := actualTrace p n f hf.injective B D raw hNorm b hb
    change f (Quot.mk (OrientableRel p n) raw)=x at hgq
    rw [hgq] at htA htB
    change (x∈a.image ↔ (frame (raw : ℂ)).1=0) ∧
      (x∈b.image ↔ (frame (raw : ℂ)).2=0)
    rw [htA,htB,←rotationSegment R (raw : ℂ) (A : ℂ) (C : ℂ) hR,
      ←rotationSegment R (raw : ℂ) (B : ℂ) (D : ℂ) hR,hA,hC,hB,hD,
      chordTrace u w v z hv hz,chordTrace w u z v hz hv]
    change (_ ↔ (axes (R*(raw : ℂ))).1=0) ∧
      (_ ↔ (axes (R*(raw : ℂ))).2=0)
    rw [haxes]
    have hvLo := min_le_left v z
    have hzLo := min_le_right v z
    constructor <;> constructor
    · intro h; dsimp; linarith [h.1]
    · intro h; dsimp at h; refine ⟨by linarith,by linarith [hy.1],by linarith [hy.2]⟩
    · intro h; dsimp; linarith [h.1]
    · intro h; dsimp at h; refine ⟨by linarith,by linarith [hy.1],by linarith [hy.2]⟩

private theorem contactInterior (p n : ℕ) (x y x' y' r : Complex.ClosedUnitDisc)
    (hne : x ≠ y) (hne' : x' ≠ y')
    (hrA : (r : ℂ) ∈ segment ℝ (x : ℂ) (y : ℂ))
    (hrB : (r : ℂ) ∈ segment ℝ (x' : ℂ) (y' : ℂ))
    (hclose : Quot.mk (OrientableRel p n) x = Quot.mk (OrientableRel p n) y)
    (hclose' : Quot.mk (OrientableRel p n) x' = Quot.mk (OrientableRel p n) y')
    (hsep : Quot.mk (OrientableRel p n) x ≠ Quot.mk (OrientableRel p n) x') :
    ‖(r : ℂ)‖ < 1 := by
  have hrLe : ‖(r : ℂ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall,dist_zero_right] using r.property
  rcases lt_or_eq_of_le hrLe with hlt | heq
  · exact hlt
  have hA : Quot.mk (OrientableRel p n) r = Quot.mk (OrientableRel p n) x := by
    rcases boundaryEndpoints x y r hne hrA heq with h | h
    · rw [h]
    · rw [h]; exact hclose.symm
  have hB : Quot.mk (OrientableRel p n) r = Quot.mk (OrientableRel p n) x' := by
    rcases boundaryEndpoints x' y' r hne' hrB heq with h | h
    · rw [h]
    · rw [h]; exact hclose'.symm
  exact False.elim (hsep (hA.symm.trans hB))

namespace CurveComplex.LocalSurgery
theorem actual_orientable_handle_embedding_has_single_crossing
    {U : Type} [TopologicalSpace U] [T2Space U]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) U]
    (p n : ℕ) (hp : 1 ≤ p)
    (f : Quot (OrientableRel p n) → U) (hf : Topology.IsEmbedding f) :
    ∃ (a b : Curve U) (hab : Transverse a b), hab.1.toFinset.card = 1 := by
  let N : ℝ := 4*p+3*n
  let δ := Real.pi/N
  let R : ℂ := Real.fourierChar (-2/N)
  let A := Complex.ClosedUnitDisc.bdyPtOfReal ((1/2)/N)
  let B := Complex.ClosedUnitDisc.bdyPtOfReal ((3/2)/N)
  let C := Complex.ClosedUnitDisc.bdyPtOfReal ((5/2)/N)
  let D := Complex.ClosedUnitDisc.bdyPtOfReal ((7/2)/N)
  let point : ℂ := Complex.mk
    ((Real.sin δ * Real.cos (3*δ)+Real.sin (3*δ)*Real.cos δ)/
      (Real.sin (3*δ)+Real.sin δ)) 0 / R
  have hRaw : segment ℝ (A : ℂ) (C : ℂ) ∩
      segment ℝ (B : ℂ) (D : ℂ) = {point} := rawIntersection p n hp
  have hPoint : point ∈ segment ℝ (A : ℂ) (C : ℂ) ∩
      segment ℝ (B : ℂ) (D : ℂ) := by rw [hRaw]; exact mem_singleton _
  let r : Complex.ClosedUnitDisc := ⟨point,
    (convex_closedBall (0 : ℂ) 1).segment_subset A.property C.property hPoint.1⟩
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hN : 0 < N := by dsimp [N]; linarith
  have hAC : A ≠ C := by
    intro heq
    have h := angleInjective
      ⟨by positivity, (div_lt_one hN).mpr (by dsimp [N]; linarith)⟩
      ⟨by positivity, (div_lt_one hN).mpr (by dsimp [N]; linarith)⟩ heq
    have := (div_left_inj' hN.ne').mp h
    norm_num at this
  have hBD : B ≠ D := by
    intro heq
    have h := angleInjective
      ⟨by positivity, (div_lt_one hN).mpr (by dsimp [N]; linarith)⟩
      ⟨by positivity, (div_lt_one hN).mpr (by dsimp [N]; linarith)⟩ heq
    have := (div_left_inj' hN.ne').mp h
    norm_num at this
  let t : Icc (0 : ℝ) 1 := ⟨1/2,by norm_num⟩
  let i : Fin p := ⟨0,by omega⟩
  have hca : Quot.mk (OrientableRel p n) A = Quot.mk (OrientableRel p n) C := by
    convert Quot.sound (OrientableRel.a (n := n) t i) using 1 <;> norm_num [A,C,N,t,i]
  have hcb : Quot.mk (OrientableRel p n) B = Quot.mk (OrientableRel p n) D := by
    convert Quot.sound (OrientableRel.b (n := n) t i) using 1 <;> norm_num [B,D,N,t,i]
  obtain ⟨a,b,ha,hb⟩ := actualPair p n hp f hf
  have hOne : a.image ∩ b.image = {f (Quot.mk (OrientableRel p n) r)} := by
    rw [ha,hb]
    exact projectedSingleton p n f hf.injective A C B D r hAC hBD hca hcb
      (endpointSeparation p n hp) hRaw
  have hFinite : (a.image ∩ b.image).Finite := hOne ▸ finite_singleton _
  have hrNorm : ‖(r : ℂ)‖ < 1 := contactInterior p n A C B D r
    hAC hBD hPoint.1 hPoint.2 hca hcb (endpointSeparation p n hp)
  obtain ⟨hA,hC,hB,hD⟩ := actualRotatedCoordinates p n hp
  obtain ⟨hcos,hsin3,hsin⟩ := actualChordSigns p n hp
  have hR : R ≠ 0 := Circle.coe_ne_zero _
  have hCenter : R*(r : ℂ)=Complex.mk
      ((Real.sin δ*Real.cos (3*δ)+Real.sin (3*δ)*Real.cos δ)/
        (Real.sin (3*δ)+Real.sin δ)) 0 := by
    change R*(Complex.mk _ 0 /R)=_
    field_simp
  have hCross : CrossesAt a b (f (Quot.mk (OrientableRel p n) r)) :=
    crossingChart p n f hf A C B D r
      (Real.cos (3*δ)) (Real.cos δ) (Real.sin (3*δ)) (Real.sin δ)
      hcos hsin3 hsin R hR hA hC hB hD hrNorm hCenter a b ha hb
  have hab : Transverse a b := by
    refine ⟨hFinite,?_⟩
    intro x hx
    rw [hOne] at hx
    have hx' : x=f (Quot.mk (OrientableRel p n) r) := hx
    simpa only [hx'] using hCross
  refine ⟨a,b,hab,?_⟩
  simp [hOne]

#print axioms actual_orientable_handle_embedding_has_single_crossing
end CurveComplex.LocalSurgery
