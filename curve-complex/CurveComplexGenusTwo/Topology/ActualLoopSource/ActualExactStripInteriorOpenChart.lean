import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualExactStripPointChartAvoiding
import CurveComplexGenusTwo.Topology.IntersectionParity.ActualMarkedCrossingSign
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide CurveComplex.LocalSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- The actual embedded strip supplies an open adapted chart on its full
strict interior, with literal inverse strip normal as first chart coordinate. -/
theorem actual_exact_strip_interior_open_chart
    (M : HyperellipticModel E S) (B : Interval × Icc (-1:ℝ) 1 → S)
    (hB : IsEmbedding B) (z : Interval × Icc (-1:ℝ) 1)
    (hz : 0<z.1.val ∧ z.1.val < 1 ∧ -1<z.2.val ∧ z.2.val < 1) :
    ∃ C : OpenPartialHomeomorph S (ℝ × ℝ),
      (∀ w : Interval × Icc (-1:ℝ) 1,
        0<w.1.val → w.1.val < 1 → -1<w.2.val → w.2.val < 1 → B w∈C.source) ∧
      (∀ x∈C.source,∃ w,B w=x ∧ C x=(w.2.val,2*w.1.val-1)) ∧
      (∀ w : Interval × Icc (-1:ℝ) 1,
        0<w.1.val → w.1.val < 1 → -1<w.2.val → w.2.val < 1 →
          C (B w)=(w.2.val,2*w.1.val-1)) := by
  let := (actualSphereSmoothAtlas M).charts
  let q : UnitBox → Interval × Icc (-1:ℝ) 1 := fun z =>
    (⟨(z.val.1+1)/2,by have h := abs_lt.mp z.property.1; constructor <;> linarith⟩,
      ⟨z.val.2,(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩)
  have hqc : Continuous q := by unfold q; fun_prop
  let inv : Interval × Icc (-1:ℝ) 1 → ℝ × ℝ := fun z => (2*z.1.val-1,z.2.val)
  have hinv : Continuous inv := by unfold inv; fun_prop
  have hqi : IsEmbedding q := by
    apply IsEmbedding.of_comp hqc hinv
    have he : inv ∘ q = (Subtype.val : UnitBox → ℝ × ℝ) := by
      funext z; apply Prod.ext
      · dsimp [inv,q]; ring
      · rfl
    rw [he]
    exact IsEmbedding.subtypeVal
  let f : UnitBox → S := B ∘ q
  have hf : IsEmbedding f := hB.comp hqi
  let U : Set S := range f
  let F : Plane → S := fun z => B (projIcc 0 1 zero_le_one ((z 0+1)/2),
    projIcc (-1) 1 (by norm_num) (z 1))
  have hFc : Continuous F := by
    apply hB.continuous.comp
    exact (continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop))
  have hFU : F '' Plane.openSquare 0 1 = U := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      have hz' : |z 0| < 1 ∧ |z 1| < 1 :=
        max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
      refine ⟨⟨(z 0,z 1),hz'⟩,?_⟩
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext
      · have h := abs_lt.mp hz'.1
        rw [projIcc_of_mem zero_le_one
          (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
      · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
          ⟨(abs_lt.mp hz'.2).1.le,(abs_lt.mp hz'.2).2.le⟩]
    · rintro ⟨z,rfl⟩
      refine ⟨Plane.mk z.val.1 z.val.2,?_,?_⟩
      · apply mem_openSquare_zero_one.mpr
        exact max_lt_iff.mpr z.property
      · apply congrArg B
        apply Prod.ext <;> apply Subtype.ext
        · have h := abs_lt.mp z.property.1
          change (projIcc 0 1 zero_le_one ((z.val.1+1)/2)).val = (z.val.1+1)/2
          rw [projIcc_of_mem zero_le_one (show (z.val.1+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
        · change (projIcc (-1) 1 (by norm_num) z.val.2).val = z.val.2
          rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
              ⟨(abs_lt.mp z.property.2).1.le,(abs_lt.mp z.property.2).2.le⟩]
  have hFi : InjOn F (Plane.openSquare 0 1) := by
    intro z hz w hw he
    have hz' := max_lt_iff.mp (mem_openSquare_zero_one.mp hz)
    have hw' := max_lt_iff.mp (mem_openSquare_zero_one.mp hw)
    have hqcoord (z : Plane) (hz : |z 0| < 1 ∧ |z 1| < 1) :
        F z = f ⟨(z 0,z 1),hz⟩ := by
      apply congrArg B
      apply Prod.ext <;> apply Subtype.ext
      · have h := abs_lt.mp hz.1
        rw [projIcc_of_mem zero_le_one
          (show (z 0+1)/2 ∈ Icc (0:ℝ) 1 by constructor <;> linarith)]
      · rw [projIcc_of_mem (by norm_num : (-1:ℝ) ≤ 1)
          ⟨(abs_lt.mp hz.2).1.le,(abs_lt.mp hz.2).2.le⟩]
    rw [hqcoord z hz',hqcoord w hw'] at he
    have h := congrArg Subtype.val (hf.injective he)
    ext i
    fin_cases i
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  have hU : IsOpen U := hFU ▸ surface_invariance_of_domain_probe F _
    (Plane.isOpen_openSquare 0 1) hFc.continuousOn hFi
  let j : UnitBox ≃ₜ U := hf.toHomeomorph
  let V : Set (ℝ × ℝ) := {r | |r.1|<1 ∧ |r.2|<1}
  have hV : IsOpen V := (isOpen_lt continuous_fst.abs continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)
  let swap : UnitBox ≃ₜ V :=
    { toFun := fun r => ⟨(r.val.2,r.val.1),r.property.2,r.property.1⟩
      invFun := fun r => ⟨(r.val.2,r.val.1),r.property.2,r.property.1⟩
      left_inv := by intro r; rfl
      right_inv := by intro r; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let e : U ≃ₜ V := j.symm.trans swap
  have hmem (w : Interval × Icc (-1:ℝ) 1)
      (h0 : 0<w.1.val) (h1 : w.1.val < 1) (hl : -1<w.2.val) (hr : w.2.val < 1) : B w∈U := by
    refine ⟨⟨(2*w.1.val-1,w.2.val),⟨abs_lt.mpr ⟨by linarith only [h0],by linarith only [h1]⟩,
      abs_lt.mpr ⟨hl,hr⟩⟩⟩,?_⟩
    apply congrArg B
    apply Prod.ext <;> apply Subtype.ext
    · change ((2*w.1.val-1)+1)/2=w.1.val
      ring
    · rfl
  have hp := hmem z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
  let C := crossingPartialChart U V hU hV ⟨B z,hp⟩ e
  have hsource : C.source=U := by simp [C,crossingPartialChart]
  have hval (x : S) (hx : x∈U) : C x=(e ⟨x,hx⟩).val := by
    change crossingPartialChart U V hU hV ⟨B z,hp⟩ e x=_
    simp only [crossingPartialChart,OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    change (e (((⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨B z,hp⟩⟩).symm x)).val=_
    have hi := ((⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨B z,hp⟩⟩).left_inv (show (⟨x,hx⟩ : U)∈Set.univ from trivial)
    change ((⟨U,hU⟩ : TopologicalSpace.Opens S).openPartialHomeomorphSubtypeCoe
      ⟨⟨B z,hp⟩⟩).symm x=⟨x,hx⟩ at hi
    rw [hi]
  have hdecode (x : S) (hx : x∈U) : ∃ w,B w=x ∧ C x=(w.2.val,2*w.1.val-1) := by
    let r := j.symm ⟨x,hx⟩
    refine ⟨q r,congrArg Subtype.val (j.apply_symm_apply ⟨x,hx⟩),?_⟩
    rw [hval x hx]
    change (r.val.2,r.val.1)=((q r).2.val,2*(q r).1.val-1)
    apply Prod.ext
    · rfl
    · change r.val.1=2*((r.val.1+1)/2)-1
      ring
  refine ⟨C,?_,?_,?_⟩
  · intro w h0 h1 hl hr
    rw [hsource]
    exact hmem w h0 h1 hl hr
  · intro x hx
    exact hdecode x (hsource ▸ hx)
  · intro w h0 h1 hl hr
    obtain ⟨v,hv,he⟩ := hdecode (B w) (hmem w h0 h1 hl hr)
    have hvw : v=w := hB.injective hv
    exact hvw ▸ he
end CurveComplex.HyperellipticModel.ArcSurgery
