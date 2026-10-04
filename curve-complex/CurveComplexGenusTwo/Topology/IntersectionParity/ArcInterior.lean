import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.IntersectionParity.SubarcCircleCoordinates
import CurveComplexGenusTwo.Topology.IntersectionParity.RealIntervalCoordinates

open Set Topology

namespace CurveComplex.LocalSurgery

/-- The interior of a genuine embedded subarc is relatively open in its
ambient embedded circle. This prevents an interior disk crosscut from leaving
its own boundary side at an interior point of that side. -/
theorem embedded_curve_subarc_interior_isOpen
    {S : Type*} [TopologicalSpace S]
    (a : Curve S) (f : C(Interval, S))
    (hf : Topology.IsEmbedding f) (hfa : Set.range f ⊆ a.image) :
    IsOpen {x : a.image | (x : S) ∈ f '' Set.Ioo (0 : Interval) 1} := by
  classical
  let q := subarcCircleCoordinates a f hfa
  let θ := subarcAngleCoordinates a f hfa
  have hq (t : Interval) : a.map (q t) = f t :=
    congrArg Subtype.val (a.embedded.toHomeomorph.apply_symm_apply ⟨f t, hfa ⟨t, rfl⟩⟩)
  have hθ : Circle.exp ∘ θ = q := Circle.isCoveringMap_exp.liftPath_lifts q
    (q 0).val.arg (Circle.exp_arg _).symm
  have hinj : Function.Injective θ := by
    intro t u heq
    apply hf.injective
    rw [← hq t, ← hq u]
    exact congrArg a.map ((congrFun hθ t).symm.trans
      ((congrArg Circle.exp heq).trans (congrFun hθ u)))
  let realTheta := realIntervalPath θ
  have hrealTheta (t : Interval) : realTheta t.val = θ t := by
    change θ (Set.projIcc 0 1 (by norm_num) t.val) = θ t
    rw [Set.projIcc_of_mem _ t.property]
  have hrealThetainj : Set.InjOn realTheta (Set.Icc (0 : ℝ) 1) := by
    intro t ht u hu heq
    have heq' : θ ⟨t, ht⟩ = θ ⟨u, hu⟩ := by
      rw [← hrealTheta ⟨t, ht⟩, ← hrealTheta ⟨u, hu⟩]
      exact heq
    exact congrArg Subtype.val (hinj heq')
  have hmono := realTheta.continuous.continuousOn.strictMonoOn_of_injOn_Icc'
    (show (0 : ℝ) ≤ 1 by norm_num) hrealThetainj
  have himage : θ '' Set.Ioo (0 : Interval) 1 = realTheta '' Set.Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t.val, ⟨ht.1, ht.2⟩, hrealTheta t⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, ⟨ht.1.le, ht.2.le⟩⟩, ⟨ht.1, ht.2⟩, ?_⟩
      exact (hrealTheta _).symm
  have hangleOpen : IsOpen (θ '' Set.Ioo (0 : Interval) 1) := by
    rw [himage]
    rcases hmono with hm | hm
    · rw [realTheta.continuous.continuousOn.image_Ioo_of_strictMonoOn (by norm_num) hm]
      exact isOpen_Ioo
    · rw [realTheta.continuous.continuousOn.image_Ioo_of_strictAntiOn (by norm_num) hm]
      exact isOpen_Ioo
  have hqimage : q '' Set.Ioo (0 : Interval) 1 = Circle.exp '' (θ '' Set.Ioo (0 : Interval) 1) := by
    rw [← Set.image_comp, hθ]
  have hopen : IsOpen (q '' Set.Ioo (0 : Interval) 1) := by
    rw [hqimage]
    exact Circle.isCoveringMap_exp.isOpenMap _ hangleOpen
  have hset : {x : a.image | (x : S) ∈ f '' Set.Ioo (0 : Interval) 1} =
      a.embedded.toHomeomorph.symm ⁻¹' (q '' Set.Ioo (0 : Interval) 1) := by
    ext x
    constructor
    · rintro ⟨t, ht, heq⟩
      refine ⟨t, ht, ?_⟩
      change a.embedded.toHomeomorph.symm ⟨f t, hfa ⟨t, rfl⟩⟩ = _
      exact congrArg a.embedded.toHomeomorph.symm (Subtype.ext heq)
    · rintro ⟨t, ht, heq⟩
      refine ⟨t, ht, ?_⟩
      have hinv : a.map (a.embedded.toHomeomorph.symm x) = x.val :=
        congrArg Subtype.val (a.embedded.toHomeomorph.apply_symm_apply x)
      exact (hq t).symm.trans ((congrArg a.map heq).trans hinv)
  rw [hset]
  exact hopen.preimage a.embedded.toHomeomorph.symm.continuous

end CurveComplex.LocalSurgery
