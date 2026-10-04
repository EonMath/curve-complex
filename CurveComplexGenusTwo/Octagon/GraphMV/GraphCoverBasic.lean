import CurveComplexGenusTwo.Octagon.GraphEdgeFiber

noncomputable section
namespace CurveComplex.Octagon.AttachingMap.GraphMV

def vertexStar : Set BoundaryGraph :=
  {x | ∃ (i : Fin 4) (t : unitInterval),
    sideLoop (graphEdgeIndex i) t = x ∧ ((t : ℝ) < 3/8 ∨ 5/8 < (t : ℝ))}

def edgeMiddles : Set BoundaryGraph :=
  {x | ∃ (i : Fin 4) (t : unitInterval),
    sideLoop (graphEdgeIndex i) t = x ∧ 1/4 < (t : ℝ) ∧ (t : ℝ) < 3/4}

theorem vertexStar_preimage :
    graphEdgeMap ⁻¹' vertexStar =
      {p : Fin 4 × unitInterval | (p.2 : ℝ) < 3/8 ∨ 5/8 < (p.2 : ℝ)} := by
  ext p
  change (∃ (i : Fin 4) (t : unitInterval),
    sideLoop (graphEdgeIndex i) t = graphEdgeMap p ∧
      ((t : ℝ) < 3/8 ∨ 5/8 < (t : ℝ))) ↔
      ((p.2 : ℝ) < 3/8 ∨ 5/8 < (p.2 : ℝ))
  constructor
  · rintro ⟨i, t, h, ht⟩
    have hf := (graphEdgeMap_fiber i p.1 t p.2).mp h
    rcases hf with ⟨_, htp⟩ | ⟨_, hp⟩
    · simpa [← htp] using ht
    · rcases hp with hp | hp
      · rw [hp]
        exact Or.inl (by norm_num)
      · rw [hp]
        exact Or.inr (by norm_num)
  · intro hp
    exact ⟨p.1, p.2, rfl, hp⟩

theorem edgeMiddles_preimage :
    graphEdgeMap ⁻¹' edgeMiddles =
      {p : Fin 4 × unitInterval | 1/4 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 3/4} := by
  ext p
  change (∃ (i : Fin 4) (t : unitInterval),
    sideLoop (graphEdgeIndex i) t = graphEdgeMap p ∧
      1/4 < (t : ℝ) ∧ (t : ℝ) < 3/4) ↔
      (1/4 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 3/4)
  constructor
  · rintro ⟨i, t, h, hlo, hhi⟩
    have hf := (graphEdgeMap_fiber i p.1 t p.2).mp h
    rcases hf with ⟨_, htp⟩ | ⟨ht, _⟩
    · simpa [← htp] using And.intro hlo hhi
    · rcases ht with ht | ht
      · norm_num [ht] at hlo
      · norm_num [ht] at hhi
  · rintro ⟨hlo, hhi⟩
    exact ⟨p.1, p.2, rfl, hlo, hhi⟩

theorem vertexStar_open : IsOpen vertexStar := by
  apply graphEdgeMap_isQuotientMap.1.isOpen_preimage.mp
  rw [vertexStar_preimage]
  let f : Fin 4 × unitInterval → ℝ := fun p => p.2
  have hf : Continuous f := continuous_subtype_val.comp continuous_snd
  change IsOpen (f ⁻¹' Set.Iio (3/8 : ℝ) ∪ f ⁻¹' Set.Ioi (5/8 : ℝ))
  exact (isOpen_Iio.preimage hf).union (isOpen_Ioi.preimage hf)

theorem edgeMiddles_open : IsOpen edgeMiddles := by
  apply graphEdgeMap_isQuotientMap.1.isOpen_preimage.mp
  rw [edgeMiddles_preimage]
  let f : Fin 4 × unitInterval → ℝ := fun p => p.2
  have hf : Continuous f := continuous_subtype_val.comp continuous_snd
  change IsOpen (f ⁻¹' Set.Ioi (1/4 : ℝ) ∩ f ⁻¹' Set.Iio (3/4 : ℝ))
  exact (isOpen_Ioi.preimage hf).inter (isOpen_Iio.preimage hf)

/-- The quotient map is a homeomorphism on the four middle-edge intervals. -/
def edgeMiddlesQuotientChart :
    (graphEdgeMap ⁻¹' edgeMiddles) ≃ₜ edgeMiddles := by
  let q := edgeMiddles.restrictPreimage graphEdgeMap
  have hq : Topology.IsQuotientMap q :=
    graphEdgeMap_isQuotientMap.restrictPreimage_isOpen edgeMiddles_open
  have hi : Function.Injective q := by
    intro a b hab
    have hab' : graphEdgeMap a.1 = graphEdgeMap b.1 := congrArg Subtype.val hab
    have ha : 1/4 < (a.1.2 : ℝ) ∧ (a.1.2 : ℝ) < 3/4 := by
      exact (Set.ext_iff.mp edgeMiddles_preimage a.1).mp a.2
    have hf := (graphEdgeMap_fiber a.1.1 b.1.1 a.1.2 b.1.2).mp hab'
    rcases hf with ⟨hidx, ht⟩ | ⟨ht, _⟩
    · apply Subtype.ext
      exact Prod.ext hidx ht
    · rcases ht with ht | ht
      · norm_num [ht] at ha
      · norm_num [ht] at ha
  exact ((isHomeomorph_iff_isQuotientMap_injective).mpr ⟨hq, hi⟩).homeomorph q

/-- The same quotient restriction gives a chart on the eight overlap intervals. -/
def overlapQuotientChart :
    (graphEdgeMap ⁻¹' (vertexStar ∩ edgeMiddles)) ≃ₜ
      ↥(vertexStar ∩ edgeMiddles) := by
  let s : Set BoundaryGraph := vertexStar ∩ edgeMiddles
  let q := s.restrictPreimage graphEdgeMap
  have hq : Topology.IsQuotientMap q :=
    graphEdgeMap_isQuotientMap.restrictPreimage_isOpen
      (vertexStar_open.inter edgeMiddles_open)
  have hi : Function.Injective q := by
    intro a b hab
    have hab' : graphEdgeMap a.1 = graphEdgeMap b.1 := congrArg Subtype.val hab
    have ha : 1/4 < (a.1.2 : ℝ) ∧ (a.1.2 : ℝ) < 3/4 := by
      exact (Set.ext_iff.mp edgeMiddles_preimage a.1).mp a.2.2
    have hf := (graphEdgeMap_fiber a.1.1 b.1.1 a.1.2 b.1.2).mp hab'
    rcases hf with ⟨hidx, ht⟩ | ⟨ht, _⟩
    · apply Subtype.ext
      exact Prod.ext hidx ht
    · rcases ht with ht | ht
      · norm_num [ht] at ha
      · norm_num [ht] at ha
  exact ((isHomeomorph_iff_isQuotientMap_injective).mpr ⟨hq, hi⟩).homeomorph q

theorem graph_cover : vertexStar ∪ edgeMiddles = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨i, t, h⟩ := sideLoop_four_cover x
    by_cases hlo : (t : ℝ) < 3/8
    · exact Or.inl ⟨i, t, h, Or.inl hlo⟩
    by_cases hhi : 5/8 < (t : ℝ)
    · exact Or.inl ⟨i, t, h, Or.inr hhi⟩
    · exact Or.inr ⟨i, t, h, by linarith, by linarith⟩

theorem base_mem_vertexStar : base ∈ vertexStar := by
  refine ⟨0, 0, ?_, Or.inl (by norm_num)⟩
  change sideLoop 0 0 = base
  exact (sideLoop 0).source

end CurveComplex.Octagon.AttachingMap.GraphMV

#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.graph_cover
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.base_mem_vertexStar
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.vertexStar_open
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.edgeMiddles_open
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.edgeMiddlesQuotientChart
#print axioms CurveComplex.Octagon.AttachingMap.GraphMV.overlapQuotientChart
