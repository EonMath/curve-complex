import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualArcChartSelection
namespace CurveComplex
open Set Topology Schoenflies Metric

/-- In an actual axis chart, construct a literal vertical strip along a whole
embedded arc contained in that chart. No pre-existing strip is supplied. -/
theorem source_whole_axis_chart_strip
    {S A : Type} [TopologicalSpace S] [T2Space S]
    [TopologicalSpace A] [CompactSpace A]
    (f : C(A,S)) (hf : IsEmbedding f)
    (e : OpenPartialHomeomorph S Plane)
    (hfe : range f ⊆ e.source)
    (haxis : ∀ t, e (f t) 1 = 0)
    (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ N : A × Icc (-1:ℝ) 1 → S,
        IsEmbedding N ∧ range N ⊆ U ∩ e.source ∧
        (∀ t, N (t,⟨0,by norm_num⟩) = f t) ∧
        (∀ z, e (N z) = Plane.mk (e (f z.1) 0) (δ*(z.2:ℝ))) ∧
        (∀ z, N z ∈ range f ↔ (z.2:ℝ) = 0) := by
  let g : C(A,Plane) := ⟨e ∘ f,
    e.continuousOn.comp_continuous f.continuous (fun t => hfe (mem_range_self t))⟩
  have hgi : Function.Injective g := by
    intro t u he
    exact hf.injective (e.injOn (hfe (mem_range_self t)) (hfe (mem_range_self u)) he)
  let V : Set Plane := e.target ∩ e.symm ⁻¹' U
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hgV : range g ⊆ V := by
    rintro x ⟨t,rfl⟩
    refine ⟨e.map_source (hfe (mem_range_self t)),?_⟩
    change e.symm (e (f t)) ∈ U
    rw [e.left_inv (hfe (mem_range_self t))]
    exact hfU (mem_range_self t)
  obtain ⟨δ,hδ,hδV⟩ := (isCompact_range g.continuous).exists_cthickening_subset_open hV hgV
  let P : A × Icc (-1:ℝ) 1 → Plane :=
    fun z => g z.1 + (δ*(z.2:ℝ)) • Plane.mk 0 1
  have hPc : Continuous P := by dsimp [P]; fun_prop
  have hPV (z) : P z ∈ V := by
    apply hδV
    have hh : δ*|(z.2:ℝ)| ≤ δ := by
      have hz := abs_le.mpr z.2.property
      nlinarith
    have hd : dist (P z) (g z.1) ≤ δ := by
      simpa [P,dist_eq_norm,norm_smul,abs_mul,abs_of_pos hδ,
        EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk] using hh
    exact mem_cthickening_of_dist_le _ _ δ _ (mem_range_self z.1) hd
  have hPcoords (z) : P z = Plane.mk (e (f z.1) 0) (δ*(z.2:ℝ)) := by
    ext i
    fin_cases i
    · simp [P,g,Plane.mk]
    · simp [P,g,Plane.mk,haxis]
  have hPi : Function.Injective P := by
    intro z w he
    have hx := congrArg (fun p : Plane => p 0) he
    have hy := congrArg (fun p : Plane => p 1) he
    rw [hPcoords,hPcoords] at hx hy
    change e (f z.1) 0 = e (f w.1) 0 at hx
    change δ*(z.2:ℝ) = δ*(w.2:ℝ) at hy
    have hgz : g z.1 = g w.1 := by
      ext i
      fin_cases i
      · exact hx
      · exact (haxis z.1).trans (haxis w.1).symm
    exact Prod.ext (hgi hgz) (Subtype.ext (mul_left_cancel₀ hδ.ne' hy))
  let N := e.symm ∘ P
  have hNc : Continuous N := e.continuousOn_symm.comp_continuous hPc
    (fun z => (hPV z).1)
  have hNi : Function.Injective N := by
    intro z w he
    exact hPi (e.symm.injOn (hPV z).1 (hPV w).1 he)
  have hNcenter (t) : N (t,⟨0,by norm_num⟩) = f t := by
    simp only [N,Function.comp_apply,P,mul_zero,zero_smul,add_zero]
    exact e.left_inv (hfe (mem_range_self t))
  have hNcoords (z) : e (N z) = Plane.mk (e (f z.1) 0) (δ*(z.2:ℝ)) := by
    change e (e.symm (P z)) = _
    rw [e.right_inv (hPV z).1,hPcoords]
  refine ⟨δ,hδ,N,(hNc.isClosedEmbedding hNi).isEmbedding,?_,hNcenter,hNcoords,?_⟩
  · rintro x ⟨z,rfl⟩
    exact ⟨(hPV z).2,e.map_target (hPV z).1⟩
  · intro z
    constructor
    · rintro ⟨t,ht⟩
      have hh := congrArg (fun x => e x 1) ht
      rw [haxis,hNcoords] at hh
      change 0 = δ*(z.2:ℝ) at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left hδ.ne'
    · intro hz
      refine ⟨z.1,?_⟩
      have hw : z.2 = ⟨0,by norm_num⟩ := Subtype.ext hz
      have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl hw
      rw [he,hNcenter]

end CurveComplex
#print axioms CurveComplex.source_whole_axis_chart_strip
