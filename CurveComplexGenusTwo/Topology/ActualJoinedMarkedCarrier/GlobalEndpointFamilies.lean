import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualChartArcTools
namespace CurveComplex
open Set Topology Metric Schoenflies
set_option maxHeartbeats 5000000

theorem actual_finite_endpoint_families_common_bank
    {S I : Type} [TopologicalSpace S] [Fintype I]
    (E : OpenPartialHomeomorph S Plane) (D : Set S)
    (L : I → C(Interval,S)) (O : I → Set S) (hO : ∀ i, IsOpen (O i))
    (h0 : ∀ i, L i 0 ∈ E.source ∩ O i)
    (hInside : ∀ i (t : Interval), 0 < t.val → L i t ∈ D)
    (hBank : ∀ i x, x ∈ E.source ∩ O i → (x ∈ D ↔ 0 < E x 1)) :
    ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη1 : η < 1,
    ∃ L' : I → C(Interval,E.source),
      (∀ i (t : Interval), (L' i t : S) = L i
        ⟨η*t.val,mul_nonneg hη.le t.property.1,
          (mul_le_of_le_one_right hη.le t.property.2).trans hη1.le⟩) ∧
      (∀ i, (L' i 0 : S)=L i 0) ∧
      ∀ i (t : Interval), t ≠ 0 → 0 < E (L' i t) 1 := by
  classical
  let A : Set Interval := ⋂ i, L i ⁻¹' (E.source ∩ O i)
  have hA : IsOpen A := isOpen_iInter_of_finite (fun i =>
    (E.open_source.inter (hO i)).preimage (L i).continuous)
  have h0A : (0:Interval) ∈ A := Set.mem_iInter.mpr h0
  obtain ⟨ρ,hρ,hball⟩ := Metric.isOpen_iff.mp hA 0 h0A
  let η := min ρ 1 / 2
  have hη : 0 < η := half_pos (lt_min hρ zero_lt_one)
  have hηρ : η < ρ := by dsimp [η]; linarith [min_le_left ρ 1]
  have hη1 : η < 1 := by dsimp [η]; linarith [min_le_right ρ 1]
  let k : Interval → Interval := fun t =>
    ⟨η*t.val,mul_nonneg hη.le t.property.1,
      (mul_le_of_le_one_right hη.le t.property.2).trans hη1.le⟩
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hkA (t : Interval) : k t ∈ A := hball (by
    change dist (k t) (0:Interval)<ρ
    rw [Subtype.dist_eq,Real.dist_eq]
    change |η*t.val-0|<ρ
    rw [sub_zero,abs_of_nonneg (mul_nonneg hη.le t.property.1)]
    exact (mul_le_of_le_one_right hη.le t.property.2).trans_lt hηρ)
  have hFamily (i : I) (t : Interval) : L i (k t) ∈ E.source ∩ O i :=
    Set.mem_iInter.mp (hkA t) i
  let L' : I → C(Interval,E.source) := fun i =>
    ⟨fun t => ⟨L i (k t),(hFamily i t).1⟩,
      ((L i).continuous.comp hk).subtype_mk _⟩
  refine ⟨η,hη,hη1,L',fun i t => rfl,?_,?_⟩
  · intro i
    have hk0 : k 0=0 := by apply Subtype.ext; simp [k]
    change L i (k 0)=L i 0
    rw [hk0]
  · intro i t ht
    have htp : 0 < t.val := lt_of_le_of_ne t.property.1
      (by intro he; exact ht (Subtype.ext he.symm))
    have hkt : 0 < (k t).val := mul_pos hη htp
    exact (hBank i _ (hFamily i t)).mp (hInside i (k t) hkt)
end CurveComplex

namespace CurveComplex
open Set Topology Schoenflies

theorem actual_corner_endpoint_family_attaches_inside
    {S : Type} [TopologicalSpace S]
    (p : S) (D : Set S) (L : C(Interval,S))
    (hPaths : ∀ t : Interval, 0 < t.val → ∃ f : C(Interval,S),
      IsEmbedding f ∧ f 0=p ∧ f 1=L t ∧ range f \ {p} ⊆ D) :
    ∀ t : Interval, 0 < t.val → L t ∈ D := by
  intro t ht
  obtain ⟨f,hf,hf0,hf1,hInside⟩ := hPaths t ht
  apply hInside
  refine ⟨⟨1,hf1⟩,?_⟩
  intro he
  have he' : f 1=f 0 := hf1.trans ((Set.mem_singleton_iff.mp he).trans hf0.symm)
  have h10 := hf.injective he'
  have hh := congrArg Subtype.val h10
  norm_num at hh
end CurveComplex
