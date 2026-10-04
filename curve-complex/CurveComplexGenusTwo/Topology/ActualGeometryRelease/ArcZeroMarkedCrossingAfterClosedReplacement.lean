import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroLocalizedMarkedCrossingRectangle
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The genuine two-axis compact rectangle produces the actual normalized
marked crossing chart. This converts local equality outside closed changed
pieces into preserved crossing geometry, not merely an intersection count. -/
theorem actual_axis_rectangle_produces_marked_crossing
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M) (p : S)
    (R : ActualCornerInterval × ActualCornerInterval → S) (hR : IsEmbedding R)
    (hm : Disjoint (range R) (M.cover.branch : Set S))
    (hcenter : R (actualCornerZero,actualCornerZero)=p)
    (ha : ∀ z, R z ∈ a.val.image ↔ (z.2:ℝ)=0)
    (hb : ∀ z, R z ∈ b.val.image ↔ (z.1:ℝ)=0) :
    ArcSurgery.CrossesInDisk M a b p := by
  letI := (actualSphereSmoothAtlas M).charts
  let V : Set (ℝ × ℝ) := {q | |q.1|<1 ∧ |q.2|<1}
  let j : V → ActualCornerInterval × ActualCornerInterval := fun q =>
    (⟨q.val.1,(abs_lt.mp q.property.1).1.le,(abs_lt.mp q.property.1).2.le⟩,
      ⟨q.val.2,(abs_lt.mp q.property.2).1.le,(abs_lt.mp q.property.2).2.le⟩)
  let k : ActualCornerInterval × ActualCornerInterval → ℝ × ℝ := fun q => (q.1.val,q.2.val)
  have hj : IsEmbedding j := IsEmbedding.of_comp (by dsimp [j]; fun_prop)
    (by dsimp [k]; fun_prop) (show IsEmbedding (k ∘ j) from IsEmbedding.subtypeVal)
  let F : V → S := R ∘ j
  have hF : IsEmbedding F := hR.comp hj
  let f : Plane → S := fun z => R
    (projIcc (-1) 1 (by norm_num) (z 0),projIcc (-1) 1 (by norm_num) (z 1))
  let U0 : Set Plane := {z | z 0 ∈ Ioo (-1) 1 ∧ z 1 ∈ Ioo (-1) 1}
  have hU0 : IsOpen U0 := (isOpen_Ioo.preimage (by fun_prop)).inter
    (isOpen_Ioo.preimage (by fun_prop))
  have hf : Continuous f := hR.continuous.comp
    ((continuous_projIcc.comp (by fun_prop)).prodMk
      (continuous_projIcc.comp (by fun_prop)))
  have hinj : InjOn f U0 := by
    intro z hz w hw he
    have hh := hR.injective he
    have h0 := congrArg (fun q => q.1.val) hh
    have h1 := congrArg (fun q => q.2.val) hh
    simp only [projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ⟨hz.1.1.le,hz.1.2.le⟩,
      projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ⟨hw.1.1.le,hw.1.2.le⟩] at h0
    simp only [projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ⟨hz.2.1.le,hz.2.2.le⟩,
      projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num) ⟨hw.2.1.le,hw.2.2.le⟩] at h1
    ext i; fin_cases i
    · exact h0
    · exact h1
  have heq : range F=f '' U0 := by
    ext x; constructor
    · rintro ⟨q,rfl⟩
      refine ⟨Plane.mk q.val.1 q.val.2,⟨abs_lt.mp q.property.1,abs_lt.mp q.property.2⟩,?_⟩
      simp [f,F,j,Plane.mk,projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
        ⟨(abs_lt.mp q.property.1).1.le,(abs_lt.mp q.property.1).2.le⟩,
        projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
        ⟨(abs_lt.mp q.property.2).1.le,(abs_lt.mp q.property.2).2.le⟩]
    · rintro ⟨z,hz,rfl⟩
      refine ⟨⟨(z 0,z 1),abs_lt.mpr hz.1,abs_lt.mpr hz.2⟩,?_⟩
      simp [f,F,j,projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
        ⟨hz.1.1.le,hz.1.2.le⟩,projIcc_of_mem (show (-1:ℝ) ≤ 1 by norm_num)
        ⟨hz.2.1.le,hz.2.2.le⟩]
  have hopen : IsOpen (range F) := heq.symm ▸
    CurveComplex.surface_invariance_of_domain_probe f U0 hU0 hf.continuousOn hinj
  let q0 : V := ⟨(0,0),by norm_num [V]⟩
  have hq0 : F q0=p := hcenter
  let e : range F ≃ₜ V := hF.toHomeomorph.symm
  have hpF : p ∈ range F := ⟨q0,hq0⟩
  have hp0 : e ⟨p,hpF⟩=q0 := by
    change hF.toHomeomorph.symm ⟨p,hpF⟩=q0
    apply hF.toHomeomorph.injective
    rw [hF.toHomeomorph.apply_symm_apply]
    exact Subtype.ext hq0.symm
  refine ⟨range F,hopen,hpF,hm.mono_left (by rintro x ⟨q,rfl⟩; exact mem_range_self _),
    e,congrArg Subtype.val hp0,?_,?_⟩
  · intro x
    have hx : F (e x)=x.val := congrArg Subtype.val (hF.toHomeomorph.apply_symm_apply x)
    rw [←hx]
    exact ha (j (e x))
  · intro x
    have hx : F (e x)=x.val := congrArg Subtype.val (hF.toHomeomorph.apply_symm_apply x)
    rw [←hx]
    exact hb (j (e x))

/-- Original transverse marked crossings persist after an actual closed-piece
replacement if the retained contacts avoid both closed changed pieces. The
open chart is manufactured by localizing the original crossing geometry. -/
theorem actual_closed_replacement_retained_marked_crossing
    (M : HyperellipticModel E S) (a a' b : EssentialMarkedArc M)
    (C B R : Set S) (hC : IsClosed C) (hB : IsClosed B)
    (hold : a.val.image=C ∪ R) (hnew : a'.val.image=B ∪ R)
    (p : S) (hp : ArcSurgery.CrossesInDisk M a b p) (hpout : p ∉ C ∪ B) :
    ArcSurgery.CrossesInDisk M a' b p := by
  let W := (C ∪ B)ᶜ
  obtain ⟨Q,hQ,hW,hm,hcenter,ha,hb,_⟩ := actual_marked_crossing_rectangle_in_open
    M a b p hp W ((hC.union hB).isOpen_compl) hpout
  apply actual_axis_rectangle_produces_marked_crossing M a' b p Q hQ hm hcenter
  · intro z
    have hzn : Q z ∉ C ∪ B := hW (mem_range_self z)
    simp only [Set.mem_union] at hzn
    have he : Q z ∈ a'.val.image ↔ Q z ∈ a.val.image := by
      rw [hold,hnew]
      simp only [mem_union]
      tauto
    exact he.trans (ha z)
  · exact hb

#print axioms actual_axis_rectangle_produces_marked_crossing
#print axioms actual_closed_replacement_retained_marked_crossing
end CurveComplex.HyperellipticModel
