import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedCompactSlice
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedFiniteCompatibleCrosscuts

namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Repairing actual mesh endpoints produces disjoint square crosscuts on the
whole marked arc. Every interior old contact lies in these constructed cores. -/
theorem actual_trimmed_marked_crosscut_assembly
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
    (η : C(Interval,S))
    (hη : ∀ t, η t = a.val.map ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩)
    (hi : Function.Injective η) (n : ℕ) (hn : 0 < n)
    (e : Fin n → OpenPartialHomeomorph S Plane)
    (hemarks : ∀ k, Disjoint (e k).source (M.cover.branch : Set S))
    (hchart : ∀ k t, η (intervalMeshParameter n hn k t) ∈ (e k).source)
    (hends : ∀ k j, η (intervalMeshParameter n hn k 0) ∉ (old j).val.image ∧
      η (intervalMeshParameter n hn k 1) ∉ (old j).val.image)
    (houter : ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 →
      (t:ℝ) ≤ l ∨ u ≤ (t:ℝ) → ∀ j, a.val.map t ∉ (old j).val.image) :
    ∃ α β : Fin n → ℝ, ∃ F : Fin n → OpenPartialHomeomorph S Plane,
      (∀ k, 0 < α k ∧ α k < β k ∧ β k < 1) ∧
      (∀ k, (F k).source ⊆ (e k).source) ∧
      (∀ i j, i ≠ j → Disjoint (F i).source (F j).source) ∧
      (∀ k, Disjoint (F k).source (M.cover.branch : Set S)) ∧
      (∀ k, Plane.closedSquare 0 1 ⊆ (F k).target) ∧
      (∀ k, F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) = Plane.mk (-1) 0 ∧
        F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) = Plane.mk 1 0) ∧
      (∀ k x, x ∈ (F k).source → (x ∈ a.val.image ↔ F k x 1 = 0)) ∧
      (∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ a.val.image =
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k)) ∧
      (∀ k j, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∉ (old j).val.image ∧
        (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∉ (old j).val.image) ∧
      ∀ j, Disjoint
        (arcInterior M a \ ⋃ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
        (old j).val.image := by
  classical
  let arc : Fin n → C(Interval,S) := fun k =>
    ⟨η ∘ intervalMeshParameter n hn k,η.continuous.comp (intervalMeshParameter_continuous n hn k)⟩
  obtain ⟨ε,hε,hεhalf,hcollar⟩ := actual_uniform_piece_off_system_collars M old arc hends
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let A : Fin n → ℝ := fun k => ((k.val:ℝ)+ε)/n
  let B : Fin n → ℝ := fun k => ((k.val:ℝ)+(1-ε))/n
  have hA (k : Fin n) : 0 < A k := div_pos (by positivity) hnR
  have hAB (k : Fin n) : A k < B k := (div_lt_div_iff_of_pos_right hnR).mpr (by linarith)
  have hB (k : Fin n) : B k < 1 := by
    apply (div_lt_one hnR).mpr
    have hk : (k.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast k.isLt
    linarith
  let α : Fin n → ℝ := fun k => l+(u-l)*A k
  let β : Fin n → ℝ := fun k => l+(u-l)*B k
  have hbounds (k : Fin n) : 0 < α k ∧ α k < β k ∧ β k < 1 := by
    have ha := hA k; have hab := hAB k; have hb := hB k
    dsimp [α,β]
    constructor
    · nlinarith
    · constructor <;> nlinarith
  let coreParams : Set Interval := {t | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε}
  have hcore (k : Fin n) : (η ∘ intervalMeshParameter n hn k) '' coreParams =
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
    calc
      _ = η '' (intervalMeshParameter n hn k '' coreParams) := (Set.image_image _ _ _).symm
      _ = η '' (Set.projIcc 0 1 zero_le_one '' Set.Icc (A k) (B k)) := by
        rw [actual_trimmed_interval_mesh_parameter_image n hn k ε hε hεhalf]
      _ = (η ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (A k) (B k) := Set.image_image _ _ _
      _ = _ := actual_compact_interval_slice_image M a l u hl hlu hu η hη
        (A k) (B k) (hA k).le (hAB k).le (hB k).le
  have hsub (k : Fin n) :
      (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (e k).source := by
    rw [← hcore k]
    rintro x ⟨t,_,rfl⟩
    exact hchart k t
  have hdis : ∀ i j : Fin n, i ≠ j → Disjoint
      ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α i) (β i))
      ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α j) (β j)) := by
    intro i j hij
    rw [← hcore i,← hcore j]
    exact actual_trimmed_interval_mesh_disjoint η hi n hn ε hε hεhalf i j hij
  obtain ⟨F,hFsub,hFdis,hFsq,_,hFends,hFflat,hFexact⟩ :=
    actual_marked_finite_compatible_crosscuts M a (Fin n) α β
      (fun k => (hbounds k).2.1) (fun k => (hbounds k).1) (fun k => (hbounds k).2.2)
      e hsub hdis
  have hcompactAvoid := actual_trimmed_interval_mesh_complement M old η n hn ε hcollar
  have hα (k : Fin n) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) =
      η (intervalMeshParameter n hn k ⟨ε,⟨hε.le,by linarith⟩⟩) := by
    simp only [Function.comp_apply]
    rw [Set.projIcc_of_mem zero_le_one ⟨(hbounds k).1.le,by linarith [(hbounds k).2.1,(hbounds k).2.2]⟩,hη]
    rfl
  have hβ (k : Fin n) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) =
      η (intervalMeshParameter n hn k ⟨1-ε,⟨by linarith,by linarith⟩⟩) := by
    simp only [Function.comp_apply]
    rw [Set.projIcc_of_mem zero_le_one ⟨by linarith [(hbounds k).1,(hbounds k).2.1],(hbounds k).2.2.le⟩,hη]
    rfl
  refine ⟨α,β,F,hbounds,hFsub,hFdis,?_,hFsq,hFends,hFflat,hFexact,?_,?_⟩
  · intro k; exact (hemarks k).mono (hFsub k) Set.Subset.rfl
  · intro k j
    rw [hα,hβ]
    exact ⟨hcollar k _ (Or.inl le_rfl) j,hcollar k _ (Or.inr le_rfl) j⟩
  · intro j
    rw [Set.disjoint_left]
    rintro x ⟨hx,hout⟩ hj
    obtain ⟨⟨t,rfl⟩,hnotmark⟩ := hx
    have ht0 : 0 < (t:ℝ) := by
      by_contra hh
      have ht : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt hh) t.property.1)
      subst t; exact hnotmark a.val.start_marked
    have ht1 : (t:ℝ) < 1 := by
      by_contra hh
      have ht : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt hh))
      subst t; exact hnotmark a.val.end_marked
    by_cases htail : (t:ℝ) ≤ l ∨ u ≤ (t:ℝ)
    · exact houter t ht0 ht1 htail j hj
    · have hl0 : l ≤ (t:ℝ) := le_of_not_ge (fun hh => htail (Or.inl hh))
      have hu1 : (t:ℝ) ≤ u := le_of_not_ge (fun hh => htail (Or.inr hh))
      let s : Interval := ⟨((t:ℝ)-l)/(u-l),⟨div_nonneg (by linarith) (by linarith),
        (div_le_one (by linarith : 0 < u-l)).mpr (by linarith)⟩⟩
      have hηt : η s = a.val.map t := by
        rw [hη]
        apply congrArg a.val.map; apply Subtype.ext
        change l+(u-l)*(((t:ℝ)-l)/(u-l)) = (t:ℝ)
        field_simp [ne_of_gt (sub_pos.mpr hlu)]
        ring
      apply Set.disjoint_left.mp (hcompactAvoid j) ⟨⟨s,hηt⟩,?_⟩ hj
      intro hh
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
      exact hout (Set.mem_iUnion.mpr ⟨k,hcore k ▸ hk⟩)

end CurveComplex.HyperellipticModel
