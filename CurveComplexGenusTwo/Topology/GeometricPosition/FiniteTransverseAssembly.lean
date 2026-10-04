import CurveComplexGenusTwo.Topology.GeometricPosition.OneCurveExtensionStatement
namespace CurveComplex
-- Actual finite class-preserving transverse producer, anonymous proof probe.
theorem finite_transverse_representatives_by_extension (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (I : Type*) [Fintype I] (r₀ : I → EssentialCurve S) :
    ∃ r : I → EssentialCurve S,
      (∀ v, Quotient.mk (essentialCurveSetoid S) (r v) =
        Quotient.mk (essentialCurveSetoid S) (r₀ v)) ∧
      ∀ v w, v ≠ w → Transverse (r v).val (r w).val := by
  classical
  let Rep := I → EssentialCurve S
  let represents (r : Rep) : Prop := ∀ v,
    Quotient.mk (essentialCurveSetoid S) (r v) =
      Quotient.mk (essentialCurveSetoid S) (r₀ v)
  let admissible (r : Rep) : Prop := represents r ∧
    ∀ v w, v ≠ w → Transverse (r v).val (r w).val
  have hraw : ∃ r : Rep, represents r := ⟨r₀,fun _ => rfl⟩
  have hposition : ∃ r : Rep, admissible r := by
    have hbuild (B : Finset I) : ∃ r : Rep, represents r ∧
        ∀ v ∈ B, ∀ w ∈ B, v ≠ w → Transverse (r v).val (r w).val := by
      induction B using Finset.induction_on with
      | empty =>
        obtain ⟨r,hr⟩ := hraw
        exact ⟨r,hr,by simp⟩
      | @insert v B hvB ih =>
        obtain ⟨r,hr,htrans⟩ := ih
        let J := {w : I // w ∈ B}
        obtain ⟨d,hd,hdtrans⟩ := position_extend_transverse_family S J
          (fun j => r j.val) (by
            intro i j hij
            exact htrans i.val i.property j.val j.property
              (fun h => hij (Subtype.ext h))) (r v)
        let r' : Rep := Function.update r v d
        have hrv : r' v = d := by simp [r']
        have hrold (w : I) (hw : w ≠ v) : r' w = r w := Function.update_of_ne hw _ _
        refine ⟨r',?_,?_⟩
        · intro w
          by_cases hw : w = v
          · subst w
            rw [hrv,hd]
            exact hr v
          · rw [hrold w hw]; exact hr w
        · intro x hx y hy hxy
          by_cases hxv : x = v
          · subst x
            have hyv : y ≠ v := Ne.symm hxy
            have hyB : y ∈ B := (Finset.mem_insert.mp hy).resolve_left hyv
            rw [hrv,hrold y hyv]
            exact transverse_symm_of_chart (hdtrans ⟨y,hyB⟩)
          · have hxB : x ∈ B := (Finset.mem_insert.mp hx).resolve_left hxv
            by_cases hyv : y = v
            · subst y
              rw [hrold x hxv,hrv]
              exact hdtrans ⟨x,hxB⟩
            · have hyB : y ∈ B := (Finset.mem_insert.mp hy).resolve_left hyv
              rw [hrold x hxv,hrold y hyv]
              exact htrans x hxB y hyB hxy
    obtain ⟨r,hr,htrans⟩ := hbuild Finset.univ
    exact ⟨r,hr,fun v w hvw => htrans v (Finset.mem_univ _) w (Finset.mem_univ _) hvw⟩
  exact hposition
end CurveComplex

#print axioms CurveComplex.finite_transverse_representatives_by_extension
