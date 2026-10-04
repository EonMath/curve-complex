import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.AnalyticCechAlgebra

open TopologicalSpace SameAtlasRRLocal SameAtlasAnalyticCohomology
open scoped Manifold ContDiff Bundle
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDimensionTwo

universe u
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

/-- The literal ordered cover: false is U and true is the punctured surface. -/
noncomputable def actualPunctureCechCover (p : E) (U : Opens E) (hp : p ∈ U) :
    OpenCover.{u, 0} E where
  Index := Bool
  opens := fun i => if i then puncturedOpen p else U
  covers := by
    apply le_antisymm le_top
    intro x hx
    by_cases hxp : x = p
    · subst x
      exact Opens.mem_iSup.mpr ⟨false, hp⟩
    · exact Opens.mem_iSup.mpr ⟨true, hxp⟩

/-- The positive 01 representative and negative swapped 10 representative.
The diagonal representatives vanish. -/
noncomputable def actualTwoOpenOneCochain (p : E) (U : Opens E) (hp : p ∈ U)
    (h : HolOn (overlapOpen p U)) : CechOne (actualPunctureCechCover p U hp) :=
  fun i j => match i, j with
    | false, false => 0
    | false, true => h
    | true, false => -HolOn.restrict (show puncturedOpen p ⊓ U ≤ overlapOpen p U by
        simp only [overlapOpen, inf_comm, le_refl]) h
    | true, true => 0

/-- Negating both local functions pays the difference between hU-hV
and the general differential f_j-f_i. -/
noncomputable def actualTwoOpenZeroCochain (p : E) (U : Opens E) (hp : p ∈ U)
    (h : HolOn U × HolOn (puncturedOpen p)) :
    CechZero (actualPunctureCechCover p U hp) :=
  fun i => match i with
    | false => -h.1
    | true => -h.2

/-- Source-review candidate: the explicit ordered one-cochain is a cocycle. -/
theorem actualTwoOpenOneCochain_cocycle (p : E) (U : Opens E) (hp : p ∈ U)
    (h : HolOn (overlapOpen p U)) :
    IsOneCocycle (actualPunctureCechCover p U hp)
      (actualTwoOpenOneCochain p U hp h) := by
  intro i j k
  cases i <;> cases j <;> cases k <;>
    ext x <;>
    simp [actualTwoOpenOneCochain, actualPunctureCechCover, HolOn.restrict,
      LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_zero, Submodule.coe_neg, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Pi.neg_apply]

/-- The exact signed differential comparison, before taking quotients. -/
theorem actualTwoOpenOneCochain_coboundary (p : E) (U : Opens E) (hp : p ∈ U)
    (h : HolOn U × HolOn (puncturedOpen p)) :
    actualTwoOpenOneCochain p U hp (twoOpenCoboundary p U h) =
      deltaZero (actualPunctureCechCover p U hp)
        (actualTwoOpenZeroCochain p U hp h) := by
  funext i j
  cases i <;> cases j <;>
    ext x <;>
    simp [actualTwoOpenOneCochain, actualTwoOpenZeroCochain,
      actualPunctureCechCover, twoOpenCoboundary, deltaZero, HolOn.restrict,
      LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add, Submodule.coe_sub,
      Submodule.coe_zero, Submodule.coe_neg, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, Pi.neg_apply] <;> ring

noncomputable def actualTwoOpenCocycle (p : E) (U : Opens E) (hp : p ∈ U) :
    HolOn (overlapOpen p U) →ₗ[ℂ] oneCocycles (actualPunctureCechCover p U hp) where
  toFun h := ⟨actualTwoOpenOneCochain p U hp h,
    actualTwoOpenOneCochain_cocycle p U hp h⟩
  map_add' := by
    intro h k
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> ext x <;>
      simp [actualTwoOpenOneCochain, HolOn.restrict, add_comm]
  map_smul' := by
    intro c h
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> ext x <;>
      simp [actualTwoOpenOneCochain, HolOn.restrict, add_comm]

/-- The literal quotient comparison is induced by the specified cocycle. -/
noncomputable def actualTwoOpenCechComparison (p : E) (U : Opens E) (hp : p ∈ U) :
    twoOpenCechOne p U →ₗ[ℂ] CechHOne (actualPunctureCechCover p U hp) :=
  (twoOpenCoboundary p U).range.liftQ
    ((classOf (actualPunctureCechCover p U hp)).comp (actualTwoOpenCocycle p U hp))
    (by
      rintro h ⟨f, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      change (deltaZero (actualPunctureCechCover p U hp)).range.mkQ
        (actualTwoOpenOneCochain p U hp (twoOpenCoboundary p U f)) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨actualTwoOpenZeroCochain p U hp f,
        (actualTwoOpenOneCochain_coboundary p U hp f).symm⟩)

theorem actualTwoOpenCechComparison_mkQ (p : E) (U : Opens E) (hp : p ∈ U)
    (h : HolOn (overlapOpen p U)) :
    actualTwoOpenCechComparison p U hp ((twoOpenCoboundary p U).range.mkQ h) =
      classOf (actualPunctureCechCover p U hp) (actualTwoOpenCocycle p U hp h) := by
  rfl

/-- Actual two-open overlap cohomology equals general Cech H1 on this
same ordered cover. No acyclicity or analytic duality premise. -/
theorem actualTwoOpenCechComparison_bijective (p : E) (U : Opens E) (hp : p ∈ U) :
    Function.Bijective (actualTwoOpenCechComparison p U hp) := by
  have hdiag (p : E) (U : Opens E) (hp : p ∈ U)
      (g : oneCocycles (actualPunctureCechCover p U hp)) (i : Bool) : g.1 i i = 0 := by
    ext x
    have hc := congrArg (fun f => f.1 ⟨x.1, ⟨x.property, x.property.1⟩⟩)
      (g.property i i i)
    simpa [HolOn.restrict] using hc
  have hswap (p : E) (U : Opens E) (hp : p ∈ U)
      (g : oneCocycles (actualPunctureCechCover p U hp))
      (x : ↥(U ⊓ puncturedOpen p)) :
      (g.1 true false).1 ⟨x.1, ⟨x.property.2, x.property.1⟩⟩ = -(g.1 false true).1 x := by
    have hc := congrArg (fun f => f.1 ⟨x.1, ⟨⟨x.property.1, x.property.2⟩, x.property.1⟩⟩)
      (g.property false true false)
    have hzero := congrArg (fun f : HolOn (U ⊓ U) => f.1 ⟨x.1, x.property.1, x.property.1⟩)
      (hdiag p U hp g false)
    simp [HolOn.restrict] at hc hzero
    linear_combination hc + hzero
  have hrecover (p : E) (U : Opens E) (hp : p ∈ U)
      (g : oneCocycles (actualPunctureCechCover p U hp)) :
      actualTwoOpenOneCochain p U hp (g.1 false true) = g.1 := by
    funext i j
    cases i <;> cases j
    · exact (hdiag p U hp g false).symm
    · rfl
    · ext x
      change -(g.1 false true).1 ⟨x.1, ⟨x.property.2, x.property.1⟩⟩ = (g.1 true false).1 x
      exact (hswap p U hp g ⟨x.1, ⟨x.property.2, x.property.1⟩⟩).symm
    · exact (hdiag p U hp g true).symm
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [eq_bot_iff]
    intro q hq
    have hq0 := LinearMap.mem_ker.mp hq
    obtain ⟨h, rfl⟩ := (twoOpenCoboundary p U).range.mkQ_surjective q
    rw [actualTwoOpenCechComparison_mkQ] at hq0
    have hval := congrArg Subtype.val hq0
    change (deltaZero (actualPunctureCechCover p U hp)).range.mkQ
      (actualTwoOpenOneCochain p U hp h) = 0 at hval
    obtain ⟨f, hf⟩ := (Submodule.Quotient.mk_eq_zero _).mp hval
    have hv : twoOpenCoboundary p U (-f false, -f true) = h := by
      ext x
      have hc := congrArg
        (fun g : CechOne (actualPunctureCechCover p U hp) => (g false true).1 x) hf
      change -(f false).1 ⟨x.1, x.property.1⟩ -
        -(f true).1 ⟨x.1, x.property.2⟩ = h.1 x
      change (f true).1 ⟨x.1, x.property.2⟩ -
        (f false).1 ⟨x.1, x.property.1⟩ = h.1 x at hc
      linear_combination hc
    have hz : (twoOpenCoboundary p U).range.mkQ h = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨(-f false, -f true), hv⟩
    exact hz ▸ Submodule.zero_mem _
  · intro x
    obtain ⟨g, rfl⟩ := classOf_surjective (actualPunctureCechCover p U hp) x
    refine ⟨(twoOpenCoboundary p U).range.mkQ (g.1 false true), ?_⟩
    rw [actualTwoOpenCechComparison_mkQ]
    apply congrArg (classOf (actualPunctureCechCover p U hp))
    apply Subtype.ext
    exact hrecover p U hp g

end CanonicalDimensionTwo
