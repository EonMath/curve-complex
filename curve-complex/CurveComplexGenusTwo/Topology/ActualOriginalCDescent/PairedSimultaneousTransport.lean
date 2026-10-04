import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

namespace CurveComplex
open Set

theorem AmbientIsotopy.exists_inverse_on_all_sets
    {E : Type} [TopologicalSpace E] (K : AmbientIsotopy E) :
    ∃ J : AmbientIsotopy E,
      ∀ A : Set E, J.finalMap '' (K.finalMap '' A) = A := by
  let zero : Interval := ⟨0, by norm_num⟩
  let one : Interval := ⟨1, by norm_num⟩
  let reverse : Interval → Interval := fun t =>
    ⟨1 - (t : ℝ), by
      rcases t.property with ⟨h0, h1⟩
      constructor <;> linarith⟩
  have reverse_cont : Continuous reverse :=
    (continuous_const.sub continuous_subtype_val).subtype_mk
      (fun t => (reverse t).property)
  have reverse_zero : reverse zero = one :=
    Subtype.ext (by norm_num [reverse, zero, one])
  have reverse_one : reverse one = zero :=
    Subtype.ext (by norm_num [reverse, zero, one])
  obtain ⟨h, hh⟩ := K.homeomorphism_at one
  let J : AmbientIsotopy E := {
    map := ⟨fun p => K.map (reverse p.1, h.symm p.2), by
      exact K.map.continuous.comp
        ((reverse_cont.comp continuous_fst).prodMk
          (h.symm.continuous.comp continuous_snd))⟩
    homeomorphism_at := by
      intro t
      obtain ⟨g, hg⟩ := K.homeomorphism_at (reverse t)
      exact ⟨h.symm.trans g, fun x => by
        simpa [Homeomorph.trans_apply] using (hg (h.symm x))⟩
    at_zero := by
      intro x
      change K.map (reverse zero, h.symm x) = x
      rw [reverse_zero, ← hh]
      exact h.apply_symm_apply x }
  refine ⟨J, ?_⟩
  intro A
  have hKfinal : K.finalMap = h := funext (fun x => (hh x).symm)
  have hJfinal : J.finalMap = h.symm := by
    funext x
    change K.map (reverse one, h.symm x) = h.symm x
    rw [reverse_one]
    exact K.at_zero _
  rw [hKfinal, hJfinal, ← Set.image_image]
  ext x
  simp

theorem simultaneous_paired_relation_transport
    {E : Type} [TopologicalSpace E]
    (a0 a1 b0 b1 : Set E) (H K : AmbientIsotopy E)
    (hH0 : H.finalMap '' a0 = b0)
    (hH1 : H.finalMap '' a1 = b1) :
    (∃ H' : AmbientIsotopy E,
      H'.finalMap '' (K.finalMap '' a0) = b0 ∧
      H'.finalMap '' (K.finalMap '' a1) = b1) ∧
    (∃ H' : AmbientIsotopy E,
      H'.finalMap '' a0 = K.finalMap '' b0 ∧
      H'.finalMap '' a1 = K.finalMap '' b1) := by
  obtain ⟨J, hJ⟩ := K.exists_inverse_on_all_sets
  constructor
  · refine ⟨J.compose H, ?_, ?_⟩
    · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hJ, hH0]
    · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hJ, hH1]
  · refine ⟨H.compose K, ?_, ?_⟩
    · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hH0]
    · rw [AmbientIsotopy.compose_finalMap, Set.image_comp, hH1]

end CurveComplex
