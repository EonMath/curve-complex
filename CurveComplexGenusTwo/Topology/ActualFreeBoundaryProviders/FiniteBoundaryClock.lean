import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
open Set Topology CurveComplex

/-- Ordered interior configurations extend to a strictly increasing continuous clock. -/
theorem finite_ordered_interval_clock (n : ℕ) (a b : Fin n → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (haI : ∀ i, a i ∈ Ioo (0 : ℝ) 1) (hbI : ∀ i, b i ∈ Ioo (0 : ℝ) 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧ f 0 = 0 ∧ f 1 = 1 ∧
      ∀ i, f (a i) = b i := by
  induction n with
  | zero =>
    exact ⟨id, continuous_id, strictMono_id, rfl, rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    let A := a (Fin.last n)
    let B := b (Fin.last n)
    have hA : 0 < A ∧ A < 1 := haI _
    have hB : 0 < B ∧ B < 1 := hbI _
    let a' : Fin n → ℝ := fun i => a i.castSucc / A
    let b' : Fin n → ℝ := fun i => b i.castSucc / B
    have ha' : StrictMono a' := by
      intro i j hij
      exact (div_lt_div_iff_of_pos_right hA.1).mpr (ha (by simpa using hij))
    have hb' : StrictMono b' := by
      intro i j hij
      exact (div_lt_div_iff_of_pos_right hB.1).mpr (hb (by simpa using hij))
    have haI' (i : Fin n) : a' i ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨div_pos (haI _).1 hA.1,
        (div_lt_one hA.1).mpr (ha (Fin.castSucc_lt_last i))⟩
    have hbI' (i : Fin n) : b' i ∈ Ioo (0 : ℝ) 1 := by
      exact ⟨div_pos (hbI _).1 hB.1,
        (div_lt_one hB.1).mpr (hb (Fin.castSucc_lt_last i))⟩
    obtain ⟨f,hfc,hfm,hf0,hf1,hfab⟩ := ih a' b' ha' hb' haI' hbI'
    let m : ℝ := (1 - B) / (1 - A)
    have hm : 0 < m := div_pos (sub_pos.mpr hB.2) (sub_pos.mpr hA.2)
    let g : ℝ → ℝ := fun x => if x ≤ A then B * f (x / A) else B + m * (x - A)
    have hgA : g A = B := by simp [g, hA.1.ne', hf1]
    have hgc : Continuous g := by
      apply continuous_if_le continuous_id continuous_const
        (continuous_const.mul (hfc.comp (continuous_id.div_const A))).continuousOn (by fun_prop)
      intro x hx
      change x = A at hx
      subst x
      simp [hA.1.ne', hf1, B]
    have hgm : StrictMono g := by
      intro x y hxy
      dsimp [g]
      split_ifs with hx hy
      · exact mul_lt_mul_of_pos_left
          (hfm ((div_lt_div_iff_of_pos_right hA.1).mpr hxy)) hB.1
      · have hleft : B * f (x / A) ≤ B := by
          have hh := hfm.monotone ((div_le_one hA.1).mpr hx)
          rw [hf1] at hh
          simpa using mul_le_mul_of_nonneg_left hh hB.1.le
        have hright : 0 < m * (y - A) := mul_pos hm (sub_pos.mpr (lt_of_not_ge hy))
        linarith
      · have hyA : y ≤ A := by assumption
        exact False.elim (hx (hxy.le.trans hyA))
      · nlinarith [mul_pos hm (sub_pos.mpr hxy)]
    refine ⟨g,hgc,hgm,?_,?_,?_⟩
    · simp [g,hA.1.le,hf0]
    · simp only [g, if_neg (not_le.mpr hA.2)]
      dsimp [m]
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hA.2.ne')]
      ring
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hgA
      · have hj : a j.castSucc ≤ A := (ha (Fin.castSucc_lt_last j)).le
        simp only [g, if_pos hj]
        change B * f (a' j) = b j.castSucc
        rw [hfab]
        exact mul_div_cancel₀ _ hB.1.ne'

private noncomputable def intervalClockFamily (W : ℝ → ℝ)
    (t : Interval) (x : ℝ) : ℝ :=
  (1 - (t : ℝ)) * x + (t : ℝ) * W x

private theorem intervalClockFamily_props (W : ℝ → ℝ)
    (hWc : Continuous W) (hWm : StrictMono W) (hW0 : W 0 = 0) (hW1 : W 1 = 1) :
    Continuous (fun p : Interval × ℝ => intervalClockFamily W p.1 p.2) ∧
    (∀ t, intervalClockFamily W t 0 = 0 ∧
      intervalClockFamily W t 1 = 1) ∧
    (∀ t, StrictMonoOn (intervalClockFamily W t) (Icc (0 : ℝ) 1)) ∧
    (∀ x, intervalClockFamily W 0 x = x) ∧
    ∀ x, intervalClockFamily W 1 x = W x := by
  have hcont : Continuous (fun p : Interval × ℝ =>
      intervalClockFamily W p.1 p.2) := by
    dsimp [intervalClockFamily]
    exact ((continuous_const.sub continuous_fst.subtype_val).mul continuous_snd).add
      (continuous_fst.subtype_val.mul (hWc.comp continuous_snd))
  have hends (t : Interval) :
      intervalClockFamily W t 0 = 0 ∧
      intervalClockFamily W t 1 = 1 := by
    dsimp [intervalClockFamily]
    rw [hW0,hW1]
    constructor <;> ring
  have hmono (t : Interval) :
      StrictMonoOn (intervalClockFamily W t) (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hwxy : W x < W y :=
      hWm hxy
    change (1 - (t : ℝ)) * x + (t : ℝ) * W x <
      (1 - (t : ℝ)) * y + (t : ℝ) * W y
    by_cases ht : (t : ℝ) = 0
    · rw [ht]
      simpa using hxy
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have hterm0 : 0 ≤ (1 - (t : ℝ)) * (y - x) :=
        mul_nonneg (by linarith [t.property.2]) (sub_nonneg.mpr hxy.le)
      have hterm1 : 0 < (t : ℝ) * (W y - W x) :=
        mul_pos htpos (sub_pos.mpr hwxy)
      nlinarith
  refine ⟨hcont,hends,hmono,?_,?_⟩
  · intro x
    simp [intervalClockFamily]
  · intro x
    simp [intervalClockFamily]

private theorem intervalClockMotion (W : ℝ → ℝ)
    (hWc : Continuous W) (hWm : StrictMono W) (hW0 : W 0 = 0) (hW1 : W 1 = 1) :
    ∃ H : AmbientIsotopy Interval,
      (∀ t (x : Interval), (H.map (t,x) : ℝ) = intervalClockFamily W t x) ∧
      (∀ t, H.map (t,0) = 0 ∧ H.map (t,1) = 1) ∧
      ∀ x : Interval, (H.finalMap x : ℝ) = W x := by
  obtain ⟨hcont,hends,hmono,hzero,hone⟩ :=
    intervalClockFamily_props W hWc hWm hW0 hW1
  have hbound (t : Interval) (x : Interval) :
      intervalClockFamily W t x ∈ Icc (0 : ℝ) 1 := by
    have hm := hmono t
    have hx0 : (0 : ℝ) ≤ (x : ℝ) := x.property.1
    have hx1 : (x : ℝ) ≤ 1 := x.property.2
    have hmon : MonotoneOn (intervalClockFamily W t) (Icc (0 : ℝ) 1) :=
      hm.monotoneOn
    constructor
    · simpa [hends t |>.1] using hmon (by norm_num) x.property hx0
    · simpa [hends t |>.2] using hmon x.property (by norm_num) hx1
  let f : Interval × Interval → Interval :=
    fun p => ⟨intervalClockFamily W p.1 p.2,hbound p.1 p.2⟩
  have hfcont : Continuous f :=
    (hcont.comp (continuous_fst.prodMk continuous_snd.subtype_val)).subtype_mk _
  have hhomeo (t : Interval) :
      ∃ h : Interval ≃ₜ Interval, ∀ x, h x = f (t,x) := by
    have hinj : Function.Injective (fun x => f (t,x)) := by
      intro x y hxy
      apply Subtype.ext
      apply (hmono t).injOn x.property y.property
      exact congrArg Subtype.val hxy
    have hsurj : Function.Surjective (fun x => f (t,x)) := by
      intro y
      have hy : (y : ℝ) ∈ Icc (intervalClockFamily W t 0)
          (intervalClockFamily W t 1) := by
        simpa [hends t |>.1,hends t |>.2] using y.property
      obtain ⟨x,hx,hxy⟩ :=
        (intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
          ((hcont.comp (continuous_const.prodMk continuous_id)).continuousOn)) hy
      refine ⟨⟨x,hx⟩,Subtype.ext ?_⟩
      exact hxy
    let h := (hfcont.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective (fun x => f (t,x)) ⟨hinj,hsurj⟩)
    exact ⟨h,fun x => rfl⟩
  let H : AmbientIsotopy Interval := {
    map := ⟨f,hfcont⟩
    homeomorphism_at := hhomeo
    at_zero := by
      intro x
      apply Subtype.ext
      exact hzero x }
  refine ⟨H,fun t x => rfl,?_,?_⟩
  · intro t
    constructor <;> apply Subtype.ext
    · exact (hends t).1
    · exact (hends t).2
  · intro x
    exact hone x


private theorem intervalClockQuotientMap :
    Topology.IsQuotientMap (fun x : Interval => (x.val : AddCircle (1 : ℝ))) := by
  let q : Interval → AddCircle (1 : ℝ) := fun x => (x.val : AddCircle (1 : ℝ))
  have hqcont : Continuous q :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  have hqsurj : Function.Surjective q := by
    intro z
    obtain ⟨x,hx,hxz⟩ := AddCircle.eq_coe_Ico z
    refine ⟨⟨x,⟨hx.1,hx.2.le⟩⟩,?_⟩
    exact hxz
  have hqclosed : IsClosedMap q := by
    intro s hs
    exact (hs.isCompact.image hqcont).isClosed
  exact hqclosed.isQuotientMap hqcont hqsurj

private theorem intervalClockQuotientMotion (W : ℝ → ℝ)
    (hWc : Continuous W) (hWm : StrictMono W) (hW0 : W 0 = 0) (hW1 : W 1 = 1) :
    ∃ H : AmbientIsotopy (AddCircle (1 : ℝ)),
      (∀ x : Interval, H.finalMap (x.val : AddCircle (1 : ℝ)) = (W x : AddCircle (1 : ℝ))) ∧
      (∀ t, H.map (t,0) = 0) := by
  obtain ⟨I,hI,hIends,hIab⟩ := intervalClockMotion W hWc hWm hW0 hW1
  let q : Interval → AddCircle (1 : ℝ) := fun x => (x.val : AddCircle (1 : ℝ))
  have hqquot : Topology.IsQuotientMap q := intervalClockQuotientMap
  let f : Interval × AddCircle (1 : ℝ) → AddCircle (1 : ℝ) :=
    fun p => AddCircle.liftIco 1 0
      (fun x : ℝ => ((intervalClockFamily W p.1 x : ℝ) : AddCircle (1 : ℝ))) p.2
  have hfq (t : Interval) (x : Interval) : f (t,q x) = q (I.map (t,x)) := by
    by_cases hx : (x : ℝ) < 1
    · change AddCircle.liftIco 1 0
        (fun y : ℝ => ((intervalClockFamily W t y : ℝ) : AddCircle (1 : ℝ)))
        (x : AddCircle (1 : ℝ)) =
        ((I.map (t,x) : ℝ) : AddCircle (1 : ℝ))
      rw [AddCircle.liftIco_zero_coe_apply ⟨x.property.1,hx⟩,hI]
    · have hx1 : x = 1 := Subtype.ext (by
        change (x : ℝ) = 1
        linarith [x.property.2])
      rw [hx1]
      change AddCircle.liftIco 1 0
        (fun y : ℝ => ((intervalClockFamily W t y : ℝ) : AddCircle (1 : ℝ)))
        ((1 : ℝ) : AddCircle (1 : ℝ)) = q (I.map (t,1))
      rw [(hIends t).2]
      simp only [q]
      have hq10 : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by simp
      rw [hq10]
      have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := by norm_num
      rw [← AddCircle.coe_zero, AddCircle.liftIco_zero_coe_apply h0]
      simpa [intervalClockFamily,hW0] using hq10.symm
  have hfcont : Continuous f := by
    apply hqquot.continuous_lift_prod_right
    have hc : Continuous (fun p : Interval × Interval => q (I.map p)) :=
      hqquot.continuous.comp I.map.continuous
    exact hc.congr (fun p => (hfq p.1 p.2).symm)
  have hhomeo (t : Interval) :
      ∃ h : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ),
        ∀ z, h z = f (t,z) := by
    have hqinj {x y : Interval} (hx : (x : ℝ) < 1) (hy : (y : ℝ) < 1)
        (he : q x = q y) : x = y := by
      apply Subtype.ext
      apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
        (a := (0 : ℝ)) (p := (1 : ℝ))
        (by simpa only [zero_add] using (show (x : ℝ) ∈ Ico 0 1 from ⟨x.property.1,hx⟩))
        (by simpa only [zero_add] using (show (y : ℝ) ∈ Ico 0 1 from ⟨y.property.1,hy⟩))).mp
      exact he
    obtain ⟨hIhomeo,hIeq⟩ := I.homeomorphism_at t
    have hIlt (x : Interval) (hx : (x : ℝ) < 1) :
        (I.map (t,x) : ℝ) < 1 := by
      have hle := (I.map (t,x)).property.2
      apply lt_of_le_of_ne hle
      intro heq
      have hIeq1 : I.map (t,x) = I.map (t,1) := by
        rw [(hIends t).2]
        exact Subtype.ext heq
      have hx1 : x = 1 := hIhomeo.injective (by simpa only [hIeq] using hIeq1)
      exact (ne_of_lt hx) (congrArg Subtype.val hx1)
    have hinj : Function.Injective (fun z => f (t,z)) := by
      intro z w hzw
      obtain ⟨x,hx,hxz⟩ := AddCircle.eq_coe_Ico z
      obtain ⟨y,hy,hyw⟩ := AddCircle.eq_coe_Ico w
      have hxyimage : q (I.map (t,⟨x,⟨hx.1,hx.2.le⟩⟩)) =
          q (I.map (t,⟨y,⟨hy.1,hy.2.le⟩⟩)) := by
        rw [← hfq,← hfq]
        change q ⟨x,⟨hx.1,hx.2.le⟩⟩ = z at hxz
        change q ⟨y,⟨hy.1,hy.2.le⟩⟩ = w at hyw
        rw [hxz,hyw]
        exact hzw
      have hxy : (⟨x,⟨hx.1,hx.2.le⟩⟩ : Interval) =
          (⟨y,⟨hy.1,hy.2.le⟩⟩ : Interval) := by
        apply hIhomeo.injective
        rw [hIeq,hIeq]
        exact hqinj (hIlt _ hx.2) (hIlt _ hy.2) hxyimage
      exact hxz.symm.trans ((congrArg q hxy).trans hyw)
    have hsurj : Function.Surjective (fun z => f (t,z)) := by
      intro z
      obtain ⟨x,hx,hxz⟩ := AddCircle.eq_coe_Ico z
      obtain ⟨y,hy⟩ := hIhomeo.surjective
        (⟨x,⟨hx.1,hx.2.le⟩⟩ : Interval)
      refine ⟨q y,?_⟩
      change f (t,q y) = z
      rw [hfq,← hIeq,hy]
      exact hxz
    let h := (hfcont.comp (continuous_const.prodMk continuous_id)).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective (fun z => f (t,z)) ⟨hinj,hsurj⟩)
    exact ⟨h,fun z => rfl⟩
  let H : AmbientIsotopy (AddCircle (1 : ℝ)) := {
    map := ⟨f,hfcont⟩
    homeomorphism_at := hhomeo
    at_zero := by
      intro z
      obtain ⟨x,rfl⟩ := hqquot.surjective z
      change f (0,q x) = q x
      rw [hfq]
      exact congrArg q (I.at_zero x) }
  refine ⟨H,?_,?_⟩
  · intro x
    change f (1,q x) = (W x : AddCircle (1 : ℝ))
    rw [hfq]
    change ((I.finalMap x : ℝ) : AddCircle (1 : ℝ)) = _
    rw [hIab]
  · intro t
    have hq0 : (0 : AddCircle (1 : ℝ)) = q 0 := by simp [q]
    change f (t,0) = 0
    rw [hq0,hfq,(hIends t).1]


/-- A common circle isotopy realizes any two finite configurations listed in the
same strict cyclic order after cutting at the fixed point zero. -/
theorem finite_ordered_circle_motion (n : ℕ) (a b : Fin n → ℝ)
    (ha : StrictMono a) (hb : StrictMono b)
    (haI : ∀ i, a i ∈ Ioo (0 : ℝ) 1) (hbI : ∀ i, b i ∈ Ioo (0 : ℝ) 1) :
    ∃ H : AmbientIsotopy (AddCircle (1 : ℝ)),
      (∀ t, H.map (t,0) = 0) ∧
      ∀ i, H.finalMap (a i : AddCircle (1 : ℝ)) = (b i : AddCircle (1 : ℝ)) := by
  obtain ⟨W,hWc,hWm,hW0,hW1,hWab⟩ := finite_ordered_interval_clock n a b ha hb haI hbI
  obtain ⟨H,hHW,hH0⟩ := intervalClockQuotientMotion W hWc hWm hW0 hW1
  refine ⟨H,hH0,?_⟩
  intro i
  have h := hHW ⟨a i, (haI i).1.le, (haI i).2.le⟩
  simpa only [hWab] using h

#print axioms finite_ordered_interval_clock
#print axioms finite_ordered_circle_motion

private def ambient_isotopy_compose {X : Type} [TopologicalSpace X]
    (H K : AmbientIsotopy X) : AmbientIsotopy X := {
  map := ⟨fun p => K.map (p.1, H.map (p.1,p.2)),
    K.map.continuous.comp
      (continuous_fst.prodMk
        (H.map.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
  homeomorphism_at := by
    intro t
    obtain ⟨h,hh⟩ := H.homeomorphism_at t
    obtain ⟨k,hk⟩ := K.homeomorphism_at t
    exact ⟨h.trans k, fun x => by simp [Homeomorph.trans_apply,hh,hk]⟩
  at_zero := by
    intro x
    change K.map (0,H.map (0,x)) = x
    have hH : H.map (0,x) = x := H.at_zero x
    have hK : K.map (0,x) = x := K.at_zero x
    rw [hH,hK] }

private theorem ambient_isotopy_compose_final {X : Type} [TopologicalSpace X]
    (H K : AmbientIsotopy X) (x : X) :
    (ambient_isotopy_compose H K).finalMap x = K.finalMap (H.finalMap x) := rfl


private def circlePairConjugate {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (H : AmbientIsotopy X) :
    AmbientIsotopy Y := {
  map := ⟨fun p => e (H.map (p.1,e.symm p.2)),
    e.continuous.comp (H.map.continuous.comp
      (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))⟩
  homeomorphism_at := by
    intro t
    obtain ⟨h,hh⟩ := H.homeomorphism_at t
    exact ⟨(e.symm.trans h).trans e,fun y => by
      simp [Homeomorph.trans_apply,hh]⟩
  at_zero := by
    intro y
    change e (H.map (0,e.symm y)) = y
    have h := H.at_zero (e.symm y)
    calc
      e (H.map (0,e.symm y)) = e (e.symm y) := congrArg e h
      _ = y := e.apply_symm_apply y }

private theorem circlePairConjugate_final {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (H : AmbientIsotopy X) (x : X) :
    (circlePairConjugate e H).finalMap (e x) = e (H.finalMap x) := by
  change e (H.map (1,e.symm (e x))) = e (H.map (1,x))
  rw [e.symm_apply_apply]


private theorem circle_multiplier_isotopy (q : Circle) :
    ∃ H : AmbientIsotopy Circle, ∀ z, H.finalMap z = q * z := by
  obtain ⟨θ,hθ⟩ := Circle.exp_surjective q
  let H : AmbientIsotopy Circle := {
    map := ⟨fun p => Circle.exp ((p.1 : ℝ) * θ) * p.2, by fun_prop⟩
    homeomorphism_at := fun t =>
      ⟨Homeomorph.mulLeft (Circle.exp ((t : ℝ) * θ)), fun _ => rfl⟩
    at_zero := by intro z; change Circle.exp ((0 : ℝ) * θ) * z = z; simp }
  refine ⟨H,?_⟩
  intro z
  change Circle.exp ((1 : ℝ) * θ) * z = q * z
  rw [one_mul,hθ]

/-- The finite clock also allows different choices of cut on the source and target circles. -/
theorem finite_ordered_circle_motion_with_cuts
    (n : ℕ) (a b : Fin n → ℝ) (α β : Circle)
    (ha : StrictMono a) (hb : StrictMono b)
    (haI : ∀ i, a i ∈ Ioo (0 : ℝ) 1) (hbI : ∀ i, b i ∈ Ioo (0 : ℝ) 1) :
    let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
    ∃ H : AmbientIsotopy Circle,
      ∀ i, H.finalMap (α * e (a i : AddCircle (1 : ℝ))) =
        β * e (b i : AddCircle (1 : ℝ)) := by
  intro e
  obtain ⟨A,-,hA⟩ := finite_ordered_circle_motion n a b ha hb haI hbI
  let K := circlePairConjugate e A
  obtain ⟨L,hL⟩ := circle_multiplier_isotopy α⁻¹
  obtain ⟨R,hR⟩ := circle_multiplier_isotopy β
  refine ⟨ambient_isotopy_compose (ambient_isotopy_compose L K) R,?_⟩
  intro i
  rw [ambient_isotopy_compose_final,ambient_isotopy_compose_final,hL]
  rw [inv_mul_cancel_left]
  rw [show K.finalMap (e (a i : AddCircle (1 : ℝ))) =
      e (A.finalMap (a i : AddCircle (1 : ℝ))) from circlePairConjugate_final e A _]
  rw [hA,hR]

#print axioms finite_ordered_circle_motion_with_cuts
