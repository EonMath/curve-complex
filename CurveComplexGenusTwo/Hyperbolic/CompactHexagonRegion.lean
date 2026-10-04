import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import Schoenflies.JordanClosed
import Schoenflies.Concatenate

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def hyperbolicPlaneHomeomorph : H2 ≃ₜ Schoenflies.Plane :=
  cayleyHomeomorph.trans ((Homeomorph.unitBall (E := ℂ)).symm.trans
    (Complex.equivRealProdCLM.trans
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 2) ℝ).symm)).toHomeomorph)

theorem regularHexagon_plane_boundary_isJordanCurve (e : H2 ≃ₜ Schoenflies.Plane) :
    Schoenflies.IsJordanCurve (e '' (⋃ i : Fin 6, regularHexagonCandidate.edge i)) := by
  let A : Fin 6 → Set Schoenflies.Plane := fun i => e '' regularHexagonCandidate.edge i
  let v : Fin 6 → Schoenflies.Plane := fun i => e (regularHexagonCandidate.vertex i)
  have harc (i : Fin 6) : Schoenflies.IsArcBetween (A i) (v i) (v (i + 1)) := by
    obtain ⟨f, hf, hi, h0, h1, him⟩ := regularHexagonCandidate.edge_has_parametrization i
    refine ⟨e ∘ f, (e.continuous.comp hf).continuousOn, e.injective.comp_injOn hi, ?_, ?_, ?_⟩
    · simpa only [image_image, Function.comp_def] using congrArg (Set.image e) him
    · simp only [Function.comp_apply, h0]; rfl
    · simp only [Function.comp_apply, h1]; rfl
  have hadj (i : Fin 6) {z : Schoenflies.Plane} (hi : z ∈ A i)
      (hj : z ∈ A (i + 1)) : z = v (i + 1) := by
    obtain ⟨x, hx, rfl⟩ := hi
    obtain ⟨y, hy, hxy⟩ := hj
    have heq : y = x := e.injective hxy
    subst y
    exact congrArg e (regularHexagon_adjacent_edges_intersection i hx hy)
  have hsep (i j : Fin 6) (hij : i ≠ j) (hn : i + 1 ≠ j) (hp : j + 1 ≠ i)
      {z : Schoenflies.Plane} (hi : z ∈ A i) (hj : z ∈ A j) : False := by
    obtain ⟨x, hx, rfl⟩ := hi
    obtain ⟨y, hy, hxy⟩ := hj
    have heq : y = x := e.injective hxy
    subst y
    exact (Set.disjoint_left.mp (regularHexagon_nonadjacent_edges_disjoint i j hij hn hp)) hx hy
  have h01 : Schoenflies.IsArcBetween (A 0 ∪ A 1) (v 0) (v 2) :=
    (harc 0).concatenate (harc 1) (fun z hz0 hz1 => hadj 0 hz0 hz1)
  have h012 : Schoenflies.IsArcBetween ((A 0 ∪ A 1) ∪ A 2) (v 0) (v 3) := by
    apply h01.concatenate (harc 2)
    intro z hz hz2
    rcases hz with hz0 | hz1
    · exact (hsep 0 2 (by decide) (by decide) (by decide) hz0 hz2).elim
    · exact hadj 1 hz1 hz2
  have h0123 : Schoenflies.IsArcBetween (((A 0 ∪ A 1) ∪ A 2) ∪ A 3) (v 0) (v 4) := by
    apply h012.concatenate (harc 3)
    intro z hz hz3
    rcases hz with (hz0 | hz1) | hz2
    · exact (hsep 0 3 (by decide) (by decide) (by decide) hz0 hz3).elim
    · exact (hsep 1 3 (by decide) (by decide) (by decide) hz1 hz3).elim
    · exact hadj 2 hz2 hz3
  have h01234 : Schoenflies.IsArcBetween ((((A 0 ∪ A 1) ∪ A 2) ∪ A 3) ∪ A 4)
      (v 0) (v 5) := by
    apply h0123.concatenate (harc 4)
    intro z hz hz4
    rcases hz with ((hz0 | hz1) | hz2) | hz3
    · exact (hsep 0 4 (by decide) (by decide) (by decide) hz0 hz4).elim
    · exact (hsep 1 4 (by decide) (by decide) (by decide) hz1 hz4).elim
    · exact (hsep 2 4 (by decide) (by decide) (by decide) hz2 hz4).elim
    · exact hadj 3 hz3 hz4
  have hJordan : Schoenflies.IsJordanCurve
      (((((A 0 ∪ A 1) ∪ A 2) ∪ A 3) ∪ A 4) ∪ A 5) := by
    apply Schoenflies.IsJordanCurve.of_two_arcs h01234 (harc 5)
    intro z hz hz5
    rcases hz with (((hz0 | hz1) | hz2) | hz3) | hz4
    · exact Or.inl (hadj 5 hz5 hz0)
    · exact (hsep 1 5 (by decide) (by decide) (by decide) hz1 hz5).elim
    · exact (hsep 2 5 (by decide) (by decide) (by decide) hz2 hz5).elim
    · exact (hsep 3 5 (by decide) (by decide) (by decide) hz3 hz5).elim
    · exact Or.inr (hadj 4 hz4 hz5)
  have hunion : (((((A 0 ∪ A 1) ∪ A 2) ∪ A 3) ∪ A 4) ∪ A 5) = ⋃ i, A i := by
    ext z
    simp only [mem_union, mem_iUnion]
    constructor
    · intro hz
      rcases hz with ((((h0 | h1) | h2) | h3) | h4) | h5
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
      · exact ⟨4, h4⟩
      · exact ⟨5, h5⟩
    · rintro ⟨i, hi⟩
      fin_cases i <;> tauto
  rw [hunion] at hJordan
  simpa only [Set.image_iUnion] using hJordan

noncomputable def regularHexagonRegion : HexagonRegion regularHexagonCandidate := by
  let e := hyperbolicPlaneHomeomorph
  let C := e '' (⋃ i : Fin 6, regularHexagonCandidate.edge i)
  have hC := Schoenflies.jordan_curve_theorem (regularHexagon_plane_boundary_isJordanCurve e)
  have hc : IsCompact (closure (Schoenflies.inside C)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hC.isBounded_inside.closure
  refine {
    interior := e.symm '' Schoenflies.inside C
    open_interior := e.symm.isOpenMap _ hC.isOpen_inside
    connected_interior := hC.isConnected_inside.image _ e.symm.continuous.continuousOn
    nonempty_interior := hC.isConnected_inside.nonempty.image e.symm
    bounded_interior := (hc.image e.symm.continuous).isBounded.subset
      (Set.image_mono subset_closure)
    boundary_is_edges := ?_ }
  rw [← e.symm.image_frontier, hC.frontier_inside]
  simp only [C, Set.image_image, Homeomorph.symm_apply_apply, Function.comp_def, Set.image_id]
  exact Set.image_id _

end CurveComplex.Hyperbolic
