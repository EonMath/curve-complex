import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkFullCell
import CurveComplexGenusTwo.Dictionary.Circle24.OneMarkPolarGluing
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 6000000

/-- The whole lift of a source one-mark disk is homeomorphic to the explicit
two-strip polar cell, with its chosen boundary anchor. The strips and the
quotient map are constructed; no upstairs disk or cell certificate is assumed. -/
theorem one_mark_disc_polar_cell_homeomorph
    (M : HyperellipticModel E S)
    (f : C(Metric.closedBall (0:Schoenflies.Plane) 1,S)) (hf : IsEmbedding f)
    (m : Metric.closedBall (0:Schoenflies.Plane) 1) (hm : ‖m.val‖ < 1)
    (honly : ∀ z, f z ∈ M.cover.branch ↔ z=m)
    (β : C(Interval,Metric.closedBall (0:Schoenflies.Plane) 1))
    (hends : β 0 = β 1)
    (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
    (hrange : Set.range β = {z | ‖z.val‖=1})
    (e : E) (he : M.cover.projection e = f (β 0)) :
    ∃ H : OneMarkPolarCell ≃ₜ M.cover.projection ⁻¹' Set.range f,
      (H (Quot.mk oneMarkPolarRel ((1,0),false))).val=e ∧
      (∀ x : OneMarkPolarStrip,
        M.cover.projection (H (Quot.mk oneMarkPolarRel x)).val ∈
          f '' {z | ‖z.val‖=1} ↔ x.1.1=1) := by
  let : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨h,L,hzero,hboundary,hanchor,hπ,hedge,hcenter,hcover⟩ :=
    M.one_mark_disc_full_cell_filling f hf m hm honly β hends hcoll hrange e he
  let f' : C(Metric.closedBall (0:Schoenflies.Plane) 1,S) := f.comp ⟨h,h.continuous⟩
  let z₀ : Metric.closedBall (0:Schoenflies.Plane) 1 := ⟨0,by simp⟩
  have honly' (z) : f' z ∈ M.cover.branch ↔ z=z₀ := by
    change f (h z) ∈ M.cover.branch ↔ z=z₀
    rw [honly]
    exact ⟨fun hz => h.injective (hz.trans hzero.symm),fun hz => hz ▸ hzero⟩
  have hnorm (t : Interval) : ‖(β t).val‖=1 := by
    have hh := Set.mem_range_self t (f := β)
    rw [hrange] at hh
    exact hh
  have hπ' (r t : Interval) : M.cover.projection (L (r,t))=
      f' (discRadialContraction z₀ r (β t)) := by
    convert hπ r t using 1
    apply congrArg (fun z => f (h z))
    apply Subtype.ext
    simp [discRadialContraction,z₀]
  let J : C(OneMarkPolarStrip,E) := ⟨fun z => M.cover.sheetSelect z.2 (L z.1),by
    apply continuous_prod_of_discrete_right.mpr
    intro b
    cases b
    · simpa only [BranchedDoubleCover.sheetSelect,Bool.false_eq_true,↓reduceIte] using L.continuous
    · simpa only [BranchedDoubleCover.sheetSelect,↓reduceIte,Function.comp_def] using M.cover.deck.continuous.comp L.continuous⟩
  have hcollision (x y : OneMarkPolarStrip) : J x=J y ↔ oneMarkPolarRel x y :=
    M.cover.radial_sheet_collision_iff f' (hf.comp h.isEmbedding) honly'
      β hcoll hnorm L hπ' hedge hcenter x y
  have hJrange : Set.range J=Set.range L ∪ M.cover.deck '' Set.range L := by
    ext y
    constructor
    · rintro ⟨⟨z,b⟩,rfl⟩
      cases b
      · exact Or.inl ⟨z,rfl⟩
      · exact Or.inr ⟨L z,⟨z,rfl⟩,rfl⟩
    · rintro (⟨z,rfl⟩ | ⟨y,⟨z,rfl⟩,rfl⟩)
      · exact ⟨(z,false),rfl⟩
      · exact ⟨(z,true),rfl⟩
  let F : OneMarkPolarCell → E := Quot.lift J (fun x y hxy => (hcollision x y).mpr hxy)
  have hF : Continuous F := continuous_quot_lift _ J.continuous
  have hFinj : Function.Injective F := by
    intro x y
    induction x using Quot.inductionOn with | h x =>
      induction y using Quot.inductionOn with | h y =>
        intro hxy
        exact Quot.sound ((hcollision x y).mp hxy)
  have hFrange : Set.range F=M.cover.projection ⁻¹' Set.range f := by
    rw [← hcover,← hJrange]
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      induction x using Quot.inductionOn with | h x => exact ⟨x,rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨Quot.mk oneMarkPolarRel x,rfl⟩
  let G : OneMarkPolarCell → M.cover.projection ⁻¹' Set.range f :=
    fun x => ⟨F x,hFrange ▸ Set.mem_range_self x⟩
  have hG : Continuous G := hF.subtype_mk _
  have hGbij : Function.Bijective G := by
    constructor
    · intro x y hxy
      exact hFinj (congrArg Subtype.val hxy)
    · intro y
      have hyrange : y.val ∈ Set.range F := by rw [hFrange]; exact y.property
      obtain ⟨x,hx⟩ := hyrange
      exact ⟨x,Subtype.ext hx⟩
  let H : OneMarkPolarCell ≃ₜ M.cover.projection ⁻¹' Set.range f :=
    (Equiv.ofBijective G hGbij).toHomeomorphOfContinuousClosed hG hG.isClosedMap
  refine ⟨H,hanchor,?_⟩
  intro x
  have hproj : M.cover.projection (H (Quot.mk oneMarkPolarRel x)).val =
      f' (discRadialContraction z₀ x.1.1 (β x.1.2)) := by
    change M.cover.projection (M.cover.sheetSelect x.2 (L x.1))=_
    cases x.2 <;> simpa only [BranchedDoubleCover.sheetSelect,Bool.false_eq_true,↓reduceIte,
      M.cover.projection_deck] using hπ' x.1.1 x.1.2
  rw [hproj]
  let z := discRadialContraction z₀ x.1.1 (β x.1.2)
  have hznorm : ‖z.val‖=(x.1.1:ℝ) := by
    simp [z,discRadialContraction,z₀,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg x.1.1.property.1,hnorm]
  constructor
  · rintro ⟨y,hy,hfy⟩
    have hh : y=h z := hf.injective hfy
    have hyfix := hboundary y hy
    have hyz : y=z := h.injective (hyfix.trans hh)
    have hrval : (x.1.1:ℝ)=1 := by rw [← hznorm,← hyz]; exact hy
    exact Subtype.ext hrval
  · intro hr
    have hz : ‖z.val‖=1 := by rw [hznorm,hr]; rfl
    exact ⟨z,hz,congrArg f (hboundary z hz).symm⟩

end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.one_mark_disc_polar_cell_homeomorph
