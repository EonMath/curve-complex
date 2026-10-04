import CurveComplexGenusTwo.Topology.Smoothing.ActualEndpointGerms
import CurveComplexGenusTwo.Topology.Smoothing.RegularCrosscut

open Set
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Normalize the actual initial or terminal subinterval without discarding a
loop's second incidence. -/
def endpointGermParameter (terminal : Bool) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (t : Interval) : Interval :=
  if terminal then ⟨1 - r * t.val, ⟨by nlinarith [t.property.2], by nlinarith [t.property.1]⟩⟩
  else ⟨r * t.val, ⟨mul_nonneg hr.le t.property.1, by nlinarith [t.property.2]⟩⟩

lemma endpointGermParameter_continuous (b : Bool) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Continuous (endpointGermParameter b r hr hr1) := by
  cases b
  · exact (continuous_const.mul continuous_subtype_val).subtype_mk _
  · exact (continuous_const.sub (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- The actual normalized germ is an embedded closed interval even when the
whole caller's arc is a loop. -/
theorem actual_endpoint_germ_embedding
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (b : Bool) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Topology.IsClosedEmbedding (a.val.map ∘ endpointGermParameter b r hr hr1) := by
  letI : T2Space S := M.sphere.symm.t2Space
  apply (a.val.continuous.comp (endpointGermParameter_continuous b r hr hr1)).isClosedEmbedding
  intro t u heq
  have heq' : a.val.map (endpointGermParameter b r hr hr1 t) =
      a.val.map (endpointGermParameter b r hr hr1 u) := heq
  rcases a.val.injective_except_loop_closure _ _ heq' with hsame | hclose | hclose
  · have hval := congrArg Subtype.val hsame
    apply Subtype.ext
    cases b <;> dsimp [endpointGermParameter] at hval <;> nlinarith
  · cases b
    · have hv := congrArg Subtype.val hclose.2
      dsimp [endpointGermParameter] at hv
      nlinarith [u.property.2]
    · have hv := congrArg Subtype.val hclose.1
      dsimp [endpointGermParameter] at hv
      nlinarith [t.property.2]
  · cases b
    · have hv := congrArg Subtype.val hclose.1
      dsimp [endpointGermParameter] at hv
      nlinarith [t.property.2]
    · have hv := congrArg Subtype.val hclose.2
      dsimp [endpointGermParameter] at hv
      nlinarith [u.property.2]

/-- An actual incident germ contained in a chosen coordinate patch is a
planar embedded arc, with the supplied endpoint ordering. -/
theorem actual_endpoint_germ_chart_arc
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (b : Bool) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (e : OpenPartialHomeomorph S Schoenflies.Plane)
    (hsource : ∀ t : Interval, a.val.map (endpointGermParameter b r hr hr1 t) ∈ e.source) :
    Schoenflies.IsArcBetween
      (Set.range (fun t : Interval => e (a.val.map (endpointGermParameter b r hr hr1 t))))
      (e (a.val.map (endpointGermParameter b r hr hr1 ⟨0, by norm_num⟩)))
      (e (a.val.map (endpointGermParameter b r hr hr1 ⟨1, by norm_num⟩))) := by
  let δ : Interval → S := a.val.map ∘ endpointGermParameter b r hr hr1
  have hδ := actual_endpoint_germ_embedding M a b r hr hr1
  have heδ : Continuous (e ∘ δ) := by
    apply continuousOn_univ.mp
    exact e.continuousOn.comp hδ.continuous.continuousOn (fun t _ => hsource t)
  have hinj : Function.Injective (e ∘ δ) := by
    intro t u htu
    apply hδ.injective
    exact e.injOn (hsource t) (hsource u) htu
  let F : ℝ → Schoenflies.Plane := (e ∘ δ) ∘ Set.projIcc 0 1 (by norm_num)
  refine ⟨F, (heδ.comp continuous_projIcc).continuousOn, ?_, ?_, ?_, ?_⟩
  · intro s hs t ht hst
    have hh := hinj hst
    have hv := congrArg Subtype.val hh
    simpa only [Set.projIcc_of_mem (by norm_num) hs, Set.projIcc_of_mem (by norm_num) ht] using hv
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Set.projIcc 0 1 (by norm_num) t, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t.val, t.property, ?_⟩
      change e (δ (Set.projIcc 0 1 (by norm_num) t.val)) = e (δ t)
      congr 2
      exact Subtype.ext (by simp [Set.projIcc_of_mem, t.property])
  · simp [F, δ, Set.projIcc]
  · simp [F, δ, Set.projIcc]

#print axioms actual_endpoint_germ_embedding
#print axioms actual_endpoint_germ_chart_arc
end CurveComplex.HyperellipticModel
