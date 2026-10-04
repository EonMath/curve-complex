import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalFProperStrip
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalRawSurgeryBranches

open CurveComplex Set Topology

noncomputable def regionalStripReflect
    (w : Set.Icc (-1 : ℝ) 1) : Set.Icc (-1 : ℝ) 1 :=
  ⟨-w, by
    obtain ⟨hl,hr⟩ := w.property
    constructor <;> linarith⟩

theorem regionalStripReflect_involutive (w : Set.Icc (-1 : ℝ) 1) :
    regionalStripReflect (regionalStripReflect w) = w := by
  apply Subtype.ext
  simp [regionalStripReflect]

theorem regionalStripReflect_embedding :
    Topology.IsEmbedding regionalStripReflect := by
  apply ((show Continuous regionalStripReflect from by
    apply Continuous.subtype_mk
    fun_prop).isClosedEmbedding ?_).isEmbedding
  intro w v h
  have he := congrArg regionalStripReflect h
  simpa [regionalStripReflect_involutive] using he

noncomputable def regionalReflectedStrip
    {S : Type} [TopologicalSpace S] {F : Set S}
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F)) :
    C(Interval × Set.Icc (-1 : ℝ) 1,↥F) :=
  ⟨fun z => E (z.1,regionalStripReflect z.2),
    E.continuous.comp (continuous_fst.prodMk
      ((show Continuous regionalStripReflect from
        regionalStripReflect_embedding.continuous).comp continuous_snd))⟩

theorem regionalReflectedStrip_embedding
    {S : Type} [TopologicalSpace S] [T2Space S] {F : Set S}
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F))
    (hE : Topology.IsEmbedding E) :
    Topology.IsEmbedding (regionalReflectedStrip E) := by
  apply hE.comp
  apply ((show Continuous
      (fun z : Interval × Set.Icc (-1 : ℝ) 1 =>
        (z.1,regionalStripReflect z.2)) from by
      exact continuous_fst.prodMk
        (regionalStripReflect_embedding.continuous.comp continuous_snd)).isClosedEmbedding ?_).isEmbedding
  intro z w h
  change (z.1,regionalStripReflect z.2) =
    (w.1,regionalStripReflect w.2) at h
  obtain ⟨h1,h2⟩ := Prod.mk.inj h
  exact Prod.ext h1 (regionalStripReflect_embedding.injective h2)

theorem regionalReflectedStrip_core_image
    {S : Type} [TopologicalSpace S] {F : Set S}
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F)) :
    regionalReflectedStrip E ''
      {z | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1} =
    E '' {z | (-1 : ℝ) < (z.2 : ℝ) ∧ (z.2 : ℝ) < 1} := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    refine ⟨(z.1,regionalStripReflect z.2),?_,rfl⟩
    change (-1 : ℝ) < -(z.2 : ℝ) ∧ -(z.2 : ℝ) < 1
    constructor <;> linarith [hz.1,hz.2]
  · rintro ⟨z,hz,rfl⟩
    refine ⟨(z.1,regionalStripReflect z.2),?_,?_⟩
    · change (-1 : ℝ) < -(z.2 : ℝ) ∧ -(z.2 : ℝ) < 1
      constructor <;> linarith [hz.1,hz.2]
    · change E (z.1,regionalStripReflect (regionalStripReflect z.2)) = E z
      rw [regionalStripReflect_involutive]

theorem regionalReflectedStrip_range
    {S : Type} [TopologicalSpace S] {F : Set S}
    (E : C(Interval × Set.Icc (-1 : ℝ) 1,↥F)) :
    Set.range (regionalReflectedStrip E) = Set.range E := by
  ext z
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨(w.1,regionalStripReflect w.2),rfl⟩
  · rintro ⟨w,rfl⟩
    exact ⟨(w.1,regionalStripReflect w.2),by
      change E (w.1,regionalStripReflect (regionalStripReflect w.2)) = E w
      rw [regionalStripReflect_involutive]⟩

#print axioms regionalStripReflect
#print axioms regionalStripReflect_involutive
#print axioms regionalStripReflect_embedding
#print axioms regionalReflectedStrip
#print axioms regionalReflectedStrip_embedding
#print axioms regionalReflectedStrip_core_image
#print axioms regionalReflectedStrip_range
