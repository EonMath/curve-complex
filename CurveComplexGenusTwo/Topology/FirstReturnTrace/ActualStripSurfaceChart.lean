import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualSubarcLocalTrace
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe

namespace CurveComplex
open Set Topology Schoenflies

/-- The open interior of ANY actual embedded compact source strip gives an
actual surface chart. It retains the exact two strip coordinates and excludes
all nonzero tracks from the entire center arc. -/
theorem source_embedded_strip_interior_chart
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (B : Interval × Set.Icc (-1:ℝ) 1 → S) (hB : IsEmbedding B)
    (f : C(Interval,S)) (hcenter : ∀ t, B (t,⟨0,by norm_num⟩) = f t) :
    ∃ E : OpenPartialHomeomorph S Plane,
      E.source = B '' {z | 0 < (z.1:ℝ) ∧ (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1} ∧
      E.target = {z : Plane | 0 < z 0 ∧ z 0 < 1 ∧ -1 < z 1 ∧ z 1 < 1} ∧
      (∀ z, 0 < (z.1:ℝ) → (z.1:ℝ) < 1 → -1 < (z.2:ℝ) → (z.2:ℝ) < 1 →
        E (B z) = Plane.mk z.1 z.2) ∧
      (∀ x ∈ E.source, x ∈ Set.range f ↔ E x 1 = 0) := by
  classical
  let O : Set Plane := {z | 0 < z 0 ∧ z 0 < 1 ∧ -1 < z 1 ∧ z 1 < 1}
  have hc0 : Continuous (fun z : Plane => z 0) := by fun_prop
  have hc1 : Continuous (fun z : Plane => z 1) := by fun_prop
  have hO : IsOpen O :=
    (isOpen_lt continuous_const hc0).inter
      ((isOpen_lt hc0 continuous_const).inter
        ((isOpen_lt continuous_const hc1).inter (isOpen_lt hc1 continuous_const)))
  let clip : Plane → Interval × Set.Icc (-1:ℝ) 1 := fun z =>
    (projIcc 0 1 zero_le_one (z 0),projIcc (-1) 1 (by norm_num) (z 1))
  let F : Plane → S := B ∘ clip
  have hFc : Continuous F := hB.continuous.comp (by dsimp [clip]; fun_prop)
  have hclip (z : Plane) (hz : z ∈ O) :
      clip z = (⟨z 0,⟨hz.1.le,hz.2.1.le⟩⟩,⟨z 1,⟨hz.2.2.1.le,hz.2.2.2.le⟩⟩) := by
    apply Prod.ext
    · exact projIcc_of_mem zero_le_one ⟨hz.1.le,hz.2.1.le⟩
    · exact projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ⟨hz.2.2.1.le,hz.2.2.2.le⟩
  have hFi : Set.InjOn F O := by
    intro z hz w hw he
    have hq := hB.injective he
    change clip z = clip w at hq
    rw [hclip z hz,hclip w hw] at hq
    have h0 := congrArg (fun q => (q.1:ℝ)) hq
    have h1 := congrArg (fun q => (q.2:ℝ)) hq
    ext j
    fin_cases j <;> assumption
  have : Nonempty O := ⟨⟨Plane.mk (1/2) 0,by norm_num [O,Plane.mk]⟩⟩
  let G : O → S := fun z => F z
  have hGc : Continuous G := hFc.comp continuous_subtype_val
  have hGi : Function.Injective G := by
    intro z w he
    exact Subtype.ext (hFi z.property w.property he)
  have hGmap : IsOpenMap G := by
    intro T hT
    have hTopen : IsOpen (Subtype.val '' T : Set Plane) := hO.isOpenMap_subtype_val T hT
    have hTsub : (Subtype.val '' T : Set Plane) ⊆ O := by
      rintro z ⟨w,hw,rfl⟩
      exact w.property
    have hh := surface_invariance_of_domain_probe F _ hTopen hFc.continuousOn (hFi.mono hTsub)
    rw [Set.image_image] at hh
    exact hh
  have hGopen : IsOpenEmbedding G :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap hGc hGi hGmap
  let P := hGopen.toOpenPartialHomeomorph G
  let Q := hO.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
  let E := P.symm.trans Q
  have hEs : E.source = Set.range G := by simp [E,P,Q]
  have hEt : E.target = O := by
    ext z
    simp [E,P,Q]
  have hcoord (z : Interval × Set.Icc (-1:ℝ) 1) (hz0 : 0 < (z.1:ℝ))
      (hz1 : (z.1:ℝ) < 1) (hzw0 : -1 < (z.2:ℝ)) (hzw1 : (z.2:ℝ) < 1) :
      E (B z) = Plane.mk z.1 z.2 := by
    let w : O := ⟨Plane.mk z.1 z.2,⟨hz0,hz1,hzw0,hzw1⟩⟩
    have hGw : G w = B z := by
      change B (clip w.val) = B z
      apply congrArg B
      rw [hclip w.val w.property]
      rfl
    change (P.symm (B z) : Plane) = w.val
    rw [← hGw]
    exact congrArg Subtype.val (hGopen.toOpenPartialHomeomorph_left_inv (x := w))
  have hEsimage : E.source = B '' {z | 0 < (z.1:ℝ) ∧ (z.1:ℝ) < 1 ∧ -1 < (z.2:ℝ) ∧ (z.2:ℝ) < 1} := by
    rw [hEs]
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      refine ⟨clip w.val,?_,rfl⟩
      rw [hclip w.val w.property]
      exact w.property
    · rintro ⟨z,hz,rfl⟩
      let w : O := ⟨Plane.mk z.1 z.2,hz⟩
      refine ⟨w,?_⟩
      change B (clip w.val) = B z
      rw [hclip w.val w.property]
      rfl
  refine ⟨E,hEsimage,hEt,hcoord,?_⟩
  intro x hx
  rw [hEsimage] at hx
  obtain ⟨z,hz,rfl⟩ := hx
  rw [hcoord z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2]
  constructor
  · rintro ⟨t,he⟩
    have hh := hB.injective ((hcenter t).trans he)
    exact congrArg (fun z => (z.2:ℝ)) hh.symm
  · intro he
    refine ⟨z.1,?_⟩
    have hw : z.2 = (⟨0,by norm_num⟩ : Set.Icc (-1:ℝ) 1) := Subtype.ext he
    have hz : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl hw
    rw [hz]
    exact (hcenter z.1).symm

end CurveComplex
#print axioms CurveComplex.source_embedded_strip_interior_chart
