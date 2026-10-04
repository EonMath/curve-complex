import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed

open Set Topology

namespace CurveComplex.LocalSurgery

/-- Descend a relatively contractible interval loop with exactly the endpoint
identification to an actual embedded nullhomotopic circle. This is a quotient
parameter bridge, not a geometric disk-recognition assumption. -/
theorem nullhomotopic_loop_with_only_endpoint_collision_gives_curve
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (x : X) (l : Path x x)
    (hcoll : ∀ s t : Interval, l s = l t →
      s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0))
    (hnull : l.Homotopic (Path.refl x)) :
    ∃ c : Curve X, c.image = Set.range l ∧
      (⟨c.map,c.embedded.continuous⟩ : C(Circle,X)).Nullhomotopic := by
  let r := AddCircle.EndpointIdent (1 : ℝ) 0
  let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa using t.property⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
    rintro a b ⟨⟩
    simpa [j] using l.source.trans l.target.symm
  let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
  have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
  have hLi : Function.Injective L := by
    intro a b
    induction a using Quot.inductionOn with | h a =>
      induction b using Quot.inductionOn with | h b =>
        intro hab
        rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
        · apply congrArg (Quot.mk r)
          exact Subtype.ext (congrArg (fun t : Interval => t.val) he)
        · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact Quot.sound AddCircle.EndpointIdent.mk
        · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
          have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
          subst a; subst b
          exact (Quot.sound AddCircle.EndpointIdent.mk).symm
  let e : Circle ≃ₜ Quot r :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
      (AddCircle.homeoIccQuot (1 : ℝ) 0)
  let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
  obtain ⟨H⟩ := hnull
  let K : Icc (0 : ℝ) (0+1) → C(Interval,X) := fun a =>
    ⟨fun t => H (t,j a), H.continuous.comp (continuous_id.prodMk continuous_const)⟩
  have hK : Continuous K := ContinuousMap.continuous_of_continuous_uncurry K
    (H.continuous.comp (continuous_snd.prodMk (hj.comp continuous_fst)))
  have hrespectK : ∀ a b, r a b → K a = K b := by
    rintro a b ⟨⟩
    ext t
    simpa [K,j] using (H.source t).trans (H.target t).symm
  let J : Quot r → C(Interval,X) := Quot.lift K hrespectK
  have hJ : Continuous J := continuous_quot_lift _ hK
  let R : C(Quot r,C(Interval,X)) := ⟨J,hJ⟩
  have hJ0 (q : Quot r) : J q 0 = L q := by
    induction q using Quot.inductionOn with | h a =>
      exact H.apply_zero (j a)
  have hJ1 (q : Quot r) : J q 1 = x := by
    induction q using Quot.inductionOn with | h a =>
      exact H.apply_one (j a)
  let T : (⟨c.map,c.embedded.continuous⟩ : C(Circle,X)).Homotopy
      (ContinuousMap.const Circle x) := {
    toFun := fun z => J (e z.2) z.1
    continuous_toFun := R.uncurry.continuous.comp
      ((e.continuous.comp continuous_snd).prodMk continuous_fst)
    map_zero_left := fun z => hJ0 (e z)
    map_one_left := fun z => hJ1 (e z) }
  refine ⟨c,?_,x,⟨T⟩⟩
  change range (L ∘ e) = range l
  rw [e.surjective.range_comp]
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quot.inductionOn with | h t =>
      exact ⟨j t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Quot.mk r ⟨t.val, by simpa using t.property⟩, rfl⟩

end CurveComplex.LocalSurgery
