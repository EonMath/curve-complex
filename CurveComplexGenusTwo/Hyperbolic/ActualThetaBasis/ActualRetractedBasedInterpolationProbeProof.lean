import CurveComplexGenusTwo.Hyperbolic.ActualThetaBasis.ActualLoopTransportDefinitions
open Set Topology ContinuousMap
namespace CurveComplex.Hyperbolic.PantsTheta
theorem retracted_based_interpolation {T : Type*} [TopologicalSpace T] (R : C(ActualPuncturedRealPlane,T))
    (base : T) (b c : ActualPuncturedRealPlane) (p : Path b b) (q : Path c c)
    (hb : R b=base) (hc : R c=base)
    (hsafe : ∀ (s t : unitInterval),
      (1-s.val) • (p t).val+s.val • (q t).val ≠ ((0:ℝ),0) ∧
      (1-s.val) • (p t).val+s.val • (q t).val ≠ ((1:ℝ),0))
    (hbase : ∀ (s : unitInterval) (z : ActualPuncturedRealPlane),
      z.val=(1-s.val) • b.val+s.val • c.val → R z=base) :
    Path.Homotopic ((p.map R.continuous).cast hb.symm hb.symm)
      ((q.map R.continuous).cast hc.symm hc.symm) := by
  refine ⟨{
    toFun st := R ⟨(1-st.1.val) • (p st.2).val+st.1.val • (q st.2).val,hsafe st.1 st.2⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · apply R.continuous.comp
    apply Continuous.subtype_mk
    have ht : Continuous (fun st : unitInterval × unitInterval => st.1.val) := continuous_subtype_val.comp continuous_fst
    exact ((continuous_const.sub ht).smul (continuous_subtype_val.comp (p.continuous.comp continuous_snd))).add
      (ht.smul (continuous_subtype_val.comp (q.continuous.comp continuous_snd)))
  · intro t
    apply congrArg R
    apply Subtype.ext
    simp
  · intro t
    apply congrArg R
    apply Subtype.ext
    simp
  · intro s t ht
    rcases ht with rfl|ht
    · change R _=R (p 0)
      conv_rhs => rw [p.source,hb]
      apply hbase s
      simp
    · have ht' : t=1 := by simpa using ht
      subst t
      change R _=R (p 1)
      conv_rhs => rw [p.target,hb]
      apply hbase s
      simp
end CurveComplex.Hyperbolic.PantsTheta
