import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualStripNarrowing

open Set Topology CurveComplex
open scoped Manifold ContDiff

namespace CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

theorem source_finite_disjoint_proper_arc_strips
    (S : Type) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (n : ℕ) (a : Fin n → C(Interval, Q S x R))
    (hemb : ∀ i, IsEmbedding (a i))
    (hend : ∀ i, (a i 0).val ∈ boundaryCircle S x R ∧
      (a i 1).val ∈ boundaryCircle S x R)
    (hinterior : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 →
      (a i t).val ∉ boundaryCircle S x R)
    (hpairwise : ∀ i j, i ≠ j → Disjoint (Set.range (a i)) (Set.range (a j))) :
    ∃ p : Fin n → ProperArc S x R, ∃ E : Fin n →
      C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R),
      (∀ i, (p i).val = a i) ∧
      (∀ i, IsEmbedding (E i) ∧
        (∀ t, E i (t, ⟨0, by norm_num⟩) = a i t) ∧
        (∀ w, E i (0,w) ∈ boundaryQ S x R ∧
          E i (1,w) ∈ boundaryQ S x R) ∧
        (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
          E i (t,w) ∉ boundaryQ S x R) ∧
        IsOpen (E i '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1})) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  letI : NormalSpace S := inferInstance
  let K : Fin n → Set S := fun i => Set.range (fun t => (a i t).val)
  have hKclosed (i : Fin n) : IsClosed (K i) := by
    exact (isCompact_range (continuous_subtype_val.comp (a i).continuous)).isClosed
  have hKdisj (i j : Fin n) (hij : i ≠ j) : Disjoint (K i) (K j) := by
    apply Set.disjoint_left.mpr
    intro z hz_i hz_j
    obtain ⟨u, hu⟩ := hz_i
    obtain ⟨v, hv⟩ := hz_j
    have he : a i u = a j v := Subtype.ext (hu.trans hv.symm)
    exact Set.disjoint_left.mp (hpairwise i j hij) (Set.mem_range_self u)
      (he ▸ Set.mem_range_self v)
  let O : Fin n → Set S := fun i => (⋃ j : {j : Fin n // j ≠ i}, K j.val)ᶜ
  have hOopen (i : Fin n) : IsOpen (O i) := by
    dsimp [O]
    apply isOpen_compl_iff.mpr
    exact isClosed_iUnion_of_finite (fun j => hKclosed j.val)
  have hKO (i : Fin n) : K i ⊆ O i := by
    intro z hz hbad
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hbad
    exact Set.disjoint_left.mp (hKdisj i j.val j.property.symm) hz hj
  have hU (i : Fin n) : ∃ U : Set S, IsOpen U ∧ K i ⊆ U ∧ closure U ⊆ O i :=
    normal_exists_closure_subset (hKclosed i) (hOopen i) (hKO i)
  choose U hUopen hKU hUclosure using hU
  let V : Fin n → Set S := fun i => U i \ ⋃ j : {j : Fin n // j ≠ i}, closure (U j.val)
  have hVopen (i : Fin n) : IsOpen (V i) := by
    dsimp [V]
    exact (hUopen i).sdiff (isClosed_iUnion_of_finite (fun j => isClosed_closure))
  have hKV (i : Fin n) : K i ⊆ V i := by
    intro z hz
    refine ⟨hKU i hz, ?_⟩
    intro hb
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hb
    have hnot : z ∉ closure (U j.val) := by
      intro h
      exact (hUclosure j.val h) (Set.mem_iUnion.mpr ⟨⟨i,j.property.symm⟩,hz⟩)
    exact hnot hj
  have hVdisj (i j : Fin n) (hij : i ≠ j) : Disjoint (V i) (V j) := by
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    exact hzi.2 (Set.mem_iUnion.mpr ⟨⟨j,hij.symm⟩,subset_closure hzj.1⟩)
  let p : Fin n → ProperArc S x R := fun i =>
    ⟨a i, hemb i, (hend i).1, (hend i).2, hinterior i⟩
  have hstrip (i : Fin n) : ∃ E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R),
      IsEmbedding E ∧ (∀ t, E (t,⟨0,by norm_num⟩) = a i t) ∧
      (∀ w, E (0,w) ∈ boundaryQ S x R ∧ E (1,w) ∈ boundaryQ S x R) ∧
      (∀ t ∈ Set.Ioo (0 : Interval) 1, ∀ w,
        E (t,w) ∉ boundaryQ S x R) ∧
      IsOpen (E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1}) ∧
      Set.range E ⊆ Subtype.val ⁻¹' V i := by
    obtain ⟨D,hD,hcenter,hendD,hproperD,hopenD⟩ :=
      source_actual_boundary_proper_arc_strip S x R g hg hS hR htarget (p i)
    have hcenterV (t : Interval) : D (t, ⟨0, by norm_num⟩) ∈
        Subtype.val ⁻¹' V i := by
      rw [hcenter]
      exact hKV i ⟨t,rfl⟩
    obtain ⟨ρ,hρ,N,hN,hNV,hNform,hNcenter⟩ :=
      source_shrink_embedded_strip_in_open D hD
        (Subtype.val ⁻¹' V i) ((hVopen i).preimage continuous_subtype_val) hcenterV
    let E : C(Interval × Set.Icc (-1 : ℝ) 1, Q S x R) :=
      ⟨N, hN.continuous⟩
    refine ⟨E,hN,?_,?_,?_,?_,hNV⟩
    · intro t
      exact (hNcenter t).trans (hcenter t)
    · intro w
      constructor
      · change N (0,w) ∈ boundaryQ S x R
        rw [hNform]
        exact (hendD _).1
      · change N (1,w) ∈ boundaryQ S x R
        rw [hNform]
        exact (hendD _).2
    · intro t ht w
      change N (t,w) ∉ boundaryQ S x R
      rw [hNform]
      exact hproperD t ht _
    · have hW : IsOpen {z : Interval × Set.Icc (-1 : ℝ) 1 |
          -ρ < z.2.val ∧ z.2.val < ρ} :=
        (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
          (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
      obtain ⟨T,hT,himage⟩ := hD.isInducing.image_eq_isOpen_inter_range hW
      have hsmall : IsOpen (D '' {z | -ρ < z.2.val ∧ z.2.val < ρ}) := by
        have heq : D '' {z | -ρ < z.2.val ∧ z.2.val < ρ} =
            T ∩ D '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} := by
          apply Set.Subset.antisymm
          · intro y hy
            have hyT := (himage ▸ hy).1
            obtain ⟨z,hz,rfl⟩ := hy
            exact ⟨hyT,⟨z,⟨by linarith [hz.1,hρ.2],by linarith [hz.2,hρ.2]⟩,rfl⟩⟩
          · rintro y ⟨hy, z,hz,rfl⟩
            rw [himage]
            exact ⟨hy,Set.mem_range_self z⟩
        rw [heq]
        exact hT.inter hopenD
      have himage : E '' {z | (-1 : ℝ) < z.2.val ∧ z.2.val < 1} =
          D '' {z | -ρ < z.2.val ∧ z.2.val < ρ} := by
        apply Set.Subset.antisymm
        · rintro y ⟨z,hz,rfl⟩
          refine ⟨(z.1,⟨ρ*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩),?_,?_⟩
          · dsimp
            constructor <;> nlinarith [hz.1,hz.2,hρ.1]
          · exact (hNform z).symm
        · rintro y ⟨z,hz,rfl⟩
          have hq : (z.2:ℝ)/ρ ∈ Set.Icc (-1:ℝ) 1 := by
            constructor
            · apply (le_div_iff₀ hρ.1).2
              nlinarith [hz.1]
            · apply (div_le_iff₀ hρ.1).2
              simpa only [one_mul] using hz.2.le
          let w : Set.Icc (-1:ℝ) 1 := ⟨(z.2:ℝ)/ρ,hq⟩
          refine ⟨(z.1,w),?_,?_⟩
          · change (-1:ℝ) < (z.2:ℝ)/ρ ∧ (z.2:ℝ)/ρ < 1
            constructor
            · apply (lt_div_iff₀ hρ.1).2
              linarith [hz.1]
            · apply (div_lt_iff₀ hρ.1).2
              simpa only [one_mul] using hz.2
          · change N (z.1,w) = D z
            rw [hNform]
            apply congrArg D
            apply Prod.ext
            · rfl
            apply Subtype.ext
            change ρ * ((z.2:ℝ)/ρ) = (z.2:ℝ)
            field_simp [hρ.1.ne']
      rw [himage]
      exact hsmall
  choose E hE using hstrip
  refine ⟨p,E,?_,?_,?_⟩
  · intro i
    rfl
  · intro i
    exact ⟨(hE i).1,(hE i).2.1,(hE i).2.2.1,(hE i).2.2.2.1,
      (hE i).2.2.2.2.1⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hi : z.val ∈ V i := (hE i).2.2.2.2.2 hzi
    have hj : z.val ∈ V j := (hE j).2.2.2.2.2 hzj
    exact Set.disjoint_left.mp (hVdisj i j hij) hi hj

end CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc

#print axioms CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_finite_disjoint_proper_arc_strips
