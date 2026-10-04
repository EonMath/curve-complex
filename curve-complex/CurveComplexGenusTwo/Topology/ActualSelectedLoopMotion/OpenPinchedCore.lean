import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.OriginalLoopPuncturedLine
import ClassificationOfSurfaces.Moise.Brouwer

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Invariance of domain makes the strict interior of any injective pinched
band open in the actual sphere; no openness is added as a geometric premise. -/
theorem pinched_band_strict_core_open
    (M : HyperellipticModel E S) (base : S) (N : C(Interval × Interval,S))
    (hends : ∀ w, N (0,w) = base ∧ N (1,w) = base)
    (hinj : ∀ s w s' w', N (s,w) = N (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) :
    IsOpen (N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1)) := by
  let r := originalLoopRealParameter
  let p : Plane → Interval × Interval := fun x =>
    ((r (x 0)).val,(r (x 1)).val)
  have hpcont : Continuous p := by dsimp [p]; fun_prop
  have hpmem (x) : (p x).1 ∈ Set.Ioo (0 : Interval) 1 ∧
      (p x).2 ∈ Set.Ioo (0 : Interval) 1 := ⟨(r (x 0)).property,(r (x 1)).property⟩
  have hNne (x) : N (p x) ≠ base := by
    intro he
    have he' : N (p x) = N (0,0) := he.trans (hends 0).1.symm
    rcases hinj _ _ _ _ he' with h | h
    · exact (ne_of_gt (hpmem x).1.1) h.1
    · rcases h.1 with h | h
      · exact (ne_of_gt (hpmem x).1.1) h
      · exact (ne_of_lt (hpmem x).1.2) h
  let F : Plane → {x : S // x ≠ base} := fun x => ⟨N (p x),hNne x⟩
  have hFc : Continuous F := (N.continuous.comp hpcont).subtype_mk _
  let f : Plane → Plane := (M.puncturedPlane base) ∘ F
  have hfc : Continuous f := (M.puncturedPlane base).continuous.comp hFc
  have hfi : Function.Injective f := by
    intro x y he
    have hN : N (p x) = N (p y) :=
      congrArg Subtype.val ((M.puncturedPlane base).injective he)
    rcases hinj _ _ _ _ hN with h | h
    · have h0 : x 0 = y 0 := r.injective (Subtype.ext h.1)
      have h1 : x 1 = y 1 := r.injective (Subtype.ext h.2)
      ext i
      fin_cases i
      · exact h0
      · exact h1
    · rcases h.1 with h | h
      · exact False.elim ((ne_of_gt (hpmem x).1.1) h)
      · exact False.elim ((ne_of_lt (hpmem x).1.2) h)
  have hfopen : IsOpen (Set.range f) := by
    simpa only [Set.image_univ] using
      LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.invariance_of_domain_open_map
        f Set.univ isOpen_univ hfc.continuousOn hfi.injOn
  let B : Set {x : S // x ≠ base} := (M.puncturedPlane base).symm '' Set.range f
  have hBopen : IsOpen B := (M.puncturedPlane base).symm.isOpenMap _ hfopen
  have hvalopen : IsOpen ((Subtype.val : {x : S // x ≠ base} → S) '' B) := by
    let : T2Space S := M.sphere.symm.t2Space
    exact isClosed_singleton.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap _ hBopen
  have heq : (Subtype.val : {x : S // x ≠ base} → S) '' B =
      N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1) := by
    ext z
    constructor
    · rintro ⟨_,⟨_,⟨x,rfl⟩,rfl⟩,rfl⟩
      refine ⟨p x,hpmem x,?_⟩
      exact congrArg Subtype.val ((M.puncturedPlane base).symm_apply_apply (F x)).symm
    · rintro ⟨⟨s,w⟩,hsw,rfl⟩
      let x : Plane := Plane.mk (r.symm ⟨s,hsw.1⟩) (r.symm ⟨w,hsw.2⟩)
      have hp : p x = (s,w) := by
        apply Prod.ext
        · exact congrArg Subtype.val (r.apply_symm_apply ⟨s,hsw.1⟩)
        · exact congrArg Subtype.val (r.apply_symm_apply ⟨w,hsw.2⟩)
      refine ⟨F x,?_,?_⟩
      · exact ⟨f x,⟨x,rfl⟩,(M.puncturedPlane base).symm_apply_apply (F x)⟩
      · change N (p x) = N (s,w)
        rw [hp]
  exact heq ▸ hvalopen

end CurveComplex.HyperellipticModel
