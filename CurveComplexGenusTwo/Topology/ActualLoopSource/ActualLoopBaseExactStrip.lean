import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopBaseOriginalArc
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorCoreExactStrip
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual original loop data construct a strip centered at its marked base.
It detects the ENTIRE original loop image exactly and avoids every other
mark. The complementary old-curve tail is actually excluded by shrinking. -/
theorem actual_loop_base_exact_strip
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1) :
    ∃ B : Interval × Set.Icc (-1:ℝ) 1 → S,
      IsEmbedding B ∧
      B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩)=a.val.map 0 ∧
      (∀ z, B z ∉ ((M.cover.branch : Set S) \ {a.val.map 0})) ∧
      (∀ z, B z ∈ a.val.image ↔ z.2.val=0) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  let := (actualSphereSmoothAtlas M).charts
  obtain ⟨f,hf,hfa,_,_,hmarks,Tail,hTail,hunion,hinter,_,r,hr0,hr1,hfr⟩ :=
    actual_loop_base_original_arc M a ha
  let Q : Set S := ((M.cover.branch : Set S) \ {a.val.map 0})ᶜ
  have hQ : IsOpen Q := (M.cover.branch.finite_toSet.subset sdiff_subset).isClosed.isOpen_compl
  have hfQ : range f ⊆ Q := by
    rintro _ ⟨t,rfl⟩ ⟨hm,hn⟩
    exact hn (mem_singleton_iff.mpr ((hmarks t).mp hm))
  obtain ⟨E,hE,hEc,hEQ⟩ := CurveComplex.source_whole_embedded_arc_strip f hf Q hQ hfQ
  change (0:ℝ)<(r:ℝ) at hr0
  change (r:ℝ)<1 at hr1
  let δ : ℝ := min (r:ℝ) (1-(r:ℝ))/2
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδr : δ≤(r:ℝ)/2 := by dsimp [δ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ1 : δ≤(1-(r:ℝ))/2 := by dsimp [δ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let α := (r:ℝ)-δ
  let β := (r:ℝ)+δ
  have hα : 0<α := by dsimp [α]; linarith
  have hβ : β<1 := by dsimp [β]; linarith
  have hαβ : α<β := by dsimp [α,β]; linarith
  let q := actualCoreParameter α β hα.le hβ.le hαβ.le
  have hqc : Continuous q := actualCoreParameter_continuous _ _ _ _ _
  have hqi : Function.Injective q := by
    intro t u he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    dsimp [q,actualCoreParameter] at hh
    nlinarith
  have hqinterior (t : Interval) : 0<(q t:ℝ) ∧ (q t:ℝ)<1 := by
    dsimp [q,actualCoreParameter]
    constructor <;> nlinarith [t.property.1,t.property.2]
  let R : Interval × Icc (-1:ℝ) 1 → S := fun z => E (q z.1,z.2)
  have hRc : Continuous R := hE.continuous.comp ((hqc.comp continuous_fst).prodMk continuous_snd)
  have hRi : Function.Injective R := by
    intro z w he
    have hh := hE.injective he
    exact Prod.ext (hqi (congrArg Prod.fst hh)) (by simpa using congrArg Prod.snd hh)
  have hR : IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
  have hcenter (t : Interval) : R (t,⟨0,by norm_num⟩)=f (q t) := hEc _
  have hcenterTail (t : Interval) : R (t,⟨0,by norm_num⟩) ∈ Tailᶜ := by
    rw [hcenter]
    intro ht
    have he : f (q t) ∈ ({f 0,f 1}:Set S) := hinter ▸ ⟨mem_range_self _,ht⟩
    rcases he with he | he
    · have hh := congrArg Subtype.val (hf.injective he)
      exact (ne_of_gt (hqinterior t).1) hh
    · have hh := congrArg Subtype.val (hf.injective (mem_singleton_iff.mp he))
      exact (ne_of_lt (hqinterior t).2) hh
  obtain ⟨ρ,hρ,N,hN,hNT,hNR,hNc⟩ := CurveComplex.source_shrink_embedded_strip_in_open
    R hR Tailᶜ hTail.isOpen_compl hcenterTail
  have hmid : q ⟨1/2,by norm_num⟩=r := by
    apply Subtype.ext
    dsimp [q,actualCoreParameter,α,β]
    ring
  refine ⟨N,hN,?_,?_,?_⟩
  · rw [hNc,hcenter,hmid,hfr]
  · intro z
    rw [hNR]
    exact hEQ (mem_range_self _)
  · intro z
    constructor
    · intro hz
      have hz' : N z ∈ range f ∪ Tail := hunion ▸ hz
      have hzF : N z ∈ range f := hz'.resolve_right (hNT (mem_range_self z))
      obtain ⟨t,ht⟩ := hzF
      have he : E (t,⟨0,by norm_num⟩)=N z := (hEc t).trans ht
      rw [hNR] at he
      have hh := congrArg (fun w : Interval × Icc (-1:ℝ) 1 => w.2.val) (hE.injective he)
      change 0=ρ*z.2.val at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left hρ.1.ne'
    · intro hz
      have hz0 : z.2=(⟨0,by norm_num⟩ : Icc (-1:ℝ) 1) := Subtype.ext hz
      rw [←Prod.eta z,hz0,hNc,hcenter]
      exact hfa (mem_range_self _)
end CurveComplex.HyperellipticModel.ArcSurgery
