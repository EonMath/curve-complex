import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopBoundaryFixedMeshPerturbation
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- A literal edge lying in the common strip is straightened there relative to
both endpoints. Nonzero actual endpoint normals imply finitely many contacts
with the old arc, with no drawing or edge-homotopy certificate assumed. -/
theorem actual_common_strip_finite_edge_straightening
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (hmarks : ∀ z,BC z ∉ (M.cover.branch : Set S))
    (haxis : ∀ z,BC z ∈ a.val.image ↔ z.2.val=0)
    (original : C(Interval,S)) (Q : C(Interval,range BC))
    (hQ : ∀ t,(Q t).val=original t)
    (hstart : original 0 ∉ a.val.image) (hend : original 1 ∉ a.val.image) :
    ∃ edge : C(Interval,S),∃ H : C(Interval × Interval,S),
      (∀ t,H (0,t)=original t) ∧ (∀ t,H (1,t)=edge t) ∧
      (∀ σ,H (σ,0)=original 0 ∧ H (σ,1)=original 1) ∧
      (∀ z,H z ∉ (M.cover.branch : Set S)) ∧
      (edge 0 ∉ a.val.image ∧ edge 1 ∉ a.val.image) ∧
      {t : Interval | edge t ∈ a.val.image}.Finite := by
  let q : C(Interval,Interval × Icc (-1:ℝ) 1) :=
    ⟨fun t => hBC.toHomeomorph.symm (Q t),hBC.toHomeomorph.symm.continuous.comp Q.continuous⟩
  let line : C(Interval,Interval × Icc (-1:ℝ) 1) :=
    ⟨fun t => (Icc.convexComb (q 0).1 (q 1).1 t,
      Icc.convexComb (q 0).2 (q 1).2 t),by fun_prop⟩
  let hc : C(Interval × Interval,Interval × Icc (-1:ℝ) 1) :=
    ⟨fun z => (Icc.convexComb (q z.2).1 (line z.2).1 z.1,
      Icc.convexComb (q z.2).2 (line z.2).2 z.1),by fun_prop⟩
  let edge : C(Interval,S) := ⟨fun t => BC (line t),hBC.continuous.comp line.continuous⟩
  let H : C(Interval × Interval,S) := ⟨fun z => BC (hc z),hBC.continuous.comp hc.continuous⟩
  have hq (t) : BC (q t)=original t :=
    (congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Q t))).trans (hQ t)
  have hzero : ((q 0).2:ℝ)≠0 := by
    intro he
    exact hstart (hq 0 ▸ (haxis (q 0)).mpr he)
  have hn (t) (ht : edge t ∈ a.val.image) :
      (1-t.val)*((q 0).2:ℝ)+t.val*((q 1).2:ℝ)=0 := (haxis (line t)).mp ht
  refine ⟨edge,H,?_,?_,?_,(fun z => hmarks (hc z)),?_,?_⟩
  · intro t
    simpa [H,hc] using hq t
  · intro t
    simp [H,hc,edge]
  · intro σ
    constructor
    · simpa [H,hc,line] using hq 0
    · simpa [H,hc,line] using hq 1
  · constructor
    · have he : edge 0=original 0 := by simpa [edge,line] using hq 0
      exact he ▸ hstart
    · have he : edge 1=original 1 := by simpa [edge,line] using hq 1
      exact he ▸ hend
  · by_cases he : ((q 0).2:ℝ)=((q 1).2:ℝ)
    · have hempty : {t : Interval | edge t ∈ a.val.image}=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro t ht
        have hh := hn t ht
        rw [← he] at hh
        exact hzero (by nlinarith only [hh])
      rw [hempty]
      exact finite_empty
    · have hs : ({t : Interval | edge t ∈ a.val.image}).Subsingleton := by
        intro t ht u hu
        have hh := hn t ht
        have hk := hn u hu
        have hprod : (t.val-u.val)*(((q 1).2:ℝ)-((q 0).2:ℝ))=0 := by
          nlinarith only [hh,hk]
        have hdiff : t.val-u.val=0 := (mul_eq_zero.mp hprod).resolve_right
          (sub_ne_zero.mpr (Ne.symm he))
        exact Subtype.ext (sub_eq_zero.mp hdiff)
      exact hs.finite
end CurveComplex.HyperellipticModel
