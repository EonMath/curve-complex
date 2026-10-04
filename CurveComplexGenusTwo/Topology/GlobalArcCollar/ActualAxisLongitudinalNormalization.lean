import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualCompactAxisChartStrip
import Mathlib.Topology.Order.IntermediateValue
namespace CurveComplex
open Set Topology Schoenflies

/-- Select the exact original arc parameter for each horizontal chart coordinate.
The selection is continuous and embedded; the axis segment is produced by IVT. -/
theorem source_axis_longitudinal_inverse
    {S A : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace A] [CompactSpace A] [PreconnectedSpace A]
    (p : C(A,S)) (hp : IsEmbedding p)
    (e : OpenPartialHomeomorph S Plane) (hps : Set.range p ⊆ e.source)
    (haxis : ∀ a, e (p a) 1 = 0)
    (r : ℝ) (hr : 0 < r) (a b : A)
    (ha : e (p a) 0 ≤ -r) (hb : r ≤ e (p b) 0) :
    ∃ j : C(Set.Icc (-1 : ℝ) 1,A), IsEmbedding j ∧
      ∀ x, e (p (j x)) = Plane.mk (r*(x:ℝ)) 0 := by
  let g : A → ℝ := fun a => e (p a) 0
  have hgc : Continuous g := by
    have he : Continuous (e ∘ p) :=
      e.continuousOn.comp_continuous p.continuous
        (fun a => hps (Set.mem_range_self a))
    exact (by fun_prop : Continuous (fun z : Plane => z 0)).comp he
  have hgi : Function.Injective g := by
    intro a b he
    apply hp.injective
    apply e.injOn (hps (Set.mem_range_self a)) (hps (Set.mem_range_self b))
    apply PiLp.ext
    intro i
    fin_cases i
    · exact he
    · change e (p a) 1 = e (p b) 1
      rw [haxis a,haxis b]
  have hge : IsEmbedding g := (hgc.isClosedEmbedding hgi).isEmbedding
  let H := hge.toHomeomorph
  have hcover : ∀ x : Set.Icc (-1 : ℝ) 1, r*(x:ℝ) ∈ Set.range g := by
    intro x
    have hl : -r ≤ r*(x:ℝ) := by nlinarith [x.property.1]
    have hu : r*(x:ℝ) ≤ r := by nlinarith [x.property.2]
    have hx : r*(x:ℝ) ∈ Set.Icc (g a) (g b) := ⟨ha.trans hl,hu.trans hb⟩
    have hh := intermediate_value_univ a b hgc hx
    simpa only [Set.image_univ] using hh
  let q : Set.Icc (-1 : ℝ) 1 → Set.range g := fun x => ⟨r*(x:ℝ),hcover x⟩
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqi : Function.Injective q := by
    intro x y he
    apply Subtype.ext
    have hh := congrArg Subtype.val he
    exact (mul_left_cancel₀ hr.ne' hh)
  letI : CompactSpace (Set.Icc (-1 : ℝ) 1) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  have hqe : IsEmbedding q := (hqc.isClosedEmbedding hqi).isEmbedding
  let j : C(Set.Icc (-1 : ℝ) 1,A) := ⟨H.symm ∘ q,H.symm.continuous.comp hqc⟩
  refine ⟨j,H.symm.isEmbedding.comp hqe,?_⟩
  intro x
  have hg : g (j x) = r*(x:ℝ) := by
    have hh := congrArg Subtype.val (H.apply_symm_apply (q x))
    exact hh
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hg
  · exact haxis (j x)
end CurveComplex
#print axioms CurveComplex.source_axis_longitudinal_inverse
