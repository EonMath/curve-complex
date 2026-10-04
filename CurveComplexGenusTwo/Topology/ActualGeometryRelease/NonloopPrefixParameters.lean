import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedTwoSideDisk
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingAfterClosedReplacement
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
namespace CurveComplex.HyperellipticModel
open Set Topology
open scoped BigOperators
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_nonloop_marked_prefix_recovers_original_parameters
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a)) (f : C(Interval,S)) (hf : IsEmbedding f)
      (hon : range f ⊆ a.val.image) (hstart : f 0=a.val.map 0)
      (hlast : f 1 ∉ M.cover.branch) :
      ∃ β : ℝ, 0 < β ∧ β < 1 ∧
        range f=(a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 β ∧
        f 1=a.val.map (projIcc 0 1 zero_le_one β) := by
  letI : T2Space S := M.sphere.symm.t2Space
  have hane := actualRepresentative_nonloop M a ha
  have haInjective : Function.Injective a.val.map := NonLoopArc.injective ⟨a.val,hane⟩
  let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  have hA : IsEmbedding A := (a.val.continuous.isClosedEmbedding haInjective).isEmbedding
  let q : Interval → Interval := fun t => hA.toHomeomorph.symm ⟨f t,hon (mem_range_self t)⟩
  have hq : Continuous q := hA.toHomeomorph.symm.continuous.comp
    (f.continuous.subtype_mk _)
  have hqmap (t : Interval) : a.val.map (q t)=f t :=
    congrArg Subtype.val (hA.toHomeomorph.apply_symm_apply ⟨f t,hon (mem_range_self t)⟩)
  have hq0 : q 0=0 := haInjective ((hqmap 0).trans hstart)
  have hqi : Function.Injective q := by
    intro t u he
    exact hf.injective ((hqmap t).symm.trans ((congrArg a.val.map he).trans (hqmap u)))
  have hqmono : StrictMono q := hq.strictMono_of_inj_boundedOrder
    (by change q 0 ≤ q 1; rw [hq0]; exact (q 1).property.1) hqi
  let β : ℝ := (q 1:ℝ)
  have hβ0 : 0 < β := by
    have hh := hqmono (by norm_num : (0:Interval) < 1)
    rw [hq0] at hh
    exact hh
  have hβ1 : β < 1 := lt_of_le_of_ne (q 1).property.2 (by
    intro he
    apply hlast
    have hh : q 1=1 := Subtype.ext he
    rw [← hqmap 1,hh]
    exact a.val.end_marked)
  have hreal : Continuous (fun t : Interval => (q t:ℝ)) := continuous_subtype_val.comp hq
  refine ⟨β,hβ0,hβ1,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨t,rfl⟩
      refine ⟨(q t:ℝ),⟨(q t).property.1,hqmono.monotone t.property.2⟩,?_⟩
      simpa only [Function.comp_apply,projIcc_of_mem zero_le_one (q t).property] using hqmap t
    · rintro ⟨s,hs,rfl⟩
      have hsreal : s ∈ Icc ((q 0:Interval):ℝ) ((q 1:Interval):ℝ) := by
        rw [hq0]; exact hs
      obtain ⟨t,ht,hqt⟩ := intermediate_value_Icc
        (by norm_num : (0:Interval) ≤ 1) hreal.continuousOn hsreal
      refine ⟨t,?_⟩
      have hs01 : s ∈ Icc (0:ℝ) 1 := ⟨hs.1,hs.2.trans hβ1.le⟩
      have he : q t=⟨s,hs01⟩ := Subtype.ext hqt
      rw [← hqmap t,he]
      simp only [Function.comp_apply,projIcc_of_mem zero_le_one hs01]
  · simpa only [β,projIcc_of_mem zero_le_one (q 1).property] using (hqmap 1).symm

end CurveComplex.HyperellipticModel
