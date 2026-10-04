import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedPreparedFamilyCover

namespace CurveComplex.ArcFinitePosition
open Set

/-- The literal interval mesh, including its two distinct exterior endpoints. -/
noncomputable def intervalMeshParameter (n : ℕ) (hn : 0 < n) (k : Fin n)
    (t : Interval) : Interval :=
  ⟨((k.val : ℝ)+(t:ℝ))/n, by
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1) hnR.le
    · apply (div_le_one hnR).mpr
      have hk : (k.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast k.isLt
      linarith [t.property.2]⟩

 theorem intervalMeshParameter_continuous (n : ℕ) (hn : 0 < n) (k : Fin n) :
    Continuous (intervalMeshParameter n hn k) := by
  unfold intervalMeshParameter
  fun_prop

 theorem intervalMeshParameter_cover (n : ℕ) (hn : 0 < n) (s : Interval) :
    ∃ k : Fin n, ∃ t : Interval, intervalMeshParameter n hn k t = s := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  by_cases hs : (s:ℝ) = 1
  · let k : Fin n := ⟨n-1,Nat.sub_lt hn (by decide)⟩
    refine ⟨k,1,Subtype.ext ?_⟩
    have hk : ((n-1:ℕ):ℝ)+1 = n := by exact_mod_cast (Nat.sub_add_cancel hn)
    change (((n-1:ℕ):ℝ)+1)/n = (s:ℝ)
    rw [hk,div_self hnR.ne',hs]
  · have hs1 : (s:ℝ) < 1 := lt_of_le_of_ne s.property.2 hs
    let k : Fin n := ⟨⌊(n:ℝ)*s⌋₊,(Nat.floor_lt
      (mul_nonneg hnR.le s.property.1)).mpr (by nlinarith)⟩
    let t : Interval := ⟨(n:ℝ)*s-k.val,by
      constructor
      · exact sub_nonneg.mpr (Nat.floor_le (mul_nonneg hnR.le s.property.1))
      · have hh := Nat.lt_floor_add_one ((n:ℝ)*s)
        change (n:ℝ)*s-(⌊(n:ℝ)*s⌋₊:ℝ) ≤ 1
        linarith⟩
    refine ⟨k,t,Subtype.ext ?_⟩
    change ((k.val:ℝ)+((n:ℝ)*s-k.val))/n = (s:ℝ)
    field_simp
    ring

 theorem actual_interval_mesh_cover {S : Type} [TopologicalSpace S]
    (η : C(Interval,S)) (n : ℕ) (hn : 0 < n) :
    Set.range η = ⋃ k, Set.range (η ∘ intervalMeshParameter n hn k) := by
  ext x
  constructor
  · rintro ⟨s,rfl⟩
    obtain ⟨k,t,ht⟩ := intervalMeshParameter_cover n hn s
    exact Set.mem_iUnion.mpr ⟨k,t,by simp [Function.comp_def,ht]⟩
  · intro hx
    obtain ⟨k,t,ht⟩ := Set.mem_iUnion.mp hx
    exact ⟨intervalMeshParameter n hn k t,ht⟩

/-- Uniform trimmed mesh cores are truly disjoint, rather than carrying a
separation assumption. -/
theorem actual_trimmed_interval_mesh_disjoint {S : Type} [TopologicalSpace S]
    (η : C(Interval,S)) (hi : Function.Injective η)
    (n : ℕ) (hn : 0 < n) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∀ k l : Fin n, k ≠ l → Disjoint
      ((η ∘ intervalMeshParameter n hn k) '' {t : Interval | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε})
      ((η ∘ intervalMeshParameter n hn l) '' {t : Interval | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε}) := by
  intro k l hkl
  rw [Set.disjoint_left]
  rintro x ⟨t,ht,rfl⟩ ⟨u,hu,he⟩
  have heq := congrArg Subtype.val (hi he)
  change ((l.val:ℝ)+(u:ℝ))/n = ((k.val:ℝ)+(t:ℝ))/n at heq
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh := (div_left_inj' hnR).mp heq
  rcases lt_or_gt_of_ne (show k.val ≠ l.val from fun h => hkl (Fin.ext h)) with hlt | hgt
  · have hk : (k.val:ℝ)+1 ≤ l.val := by exact_mod_cast hlt
    linarith [ht.2,hu.1]
  · have hl : (l.val:ℝ)+1 ≤ k.val := by exact_mod_cast hgt
    linarith [hu.2,ht.1]

end CurveComplex.ArcFinitePosition

namespace CurveComplex.ArcFinitePosition
open Set

/-- No old contact survives outside the central trimmed mesh cores. -/
theorem actual_trimmed_interval_mesh_complement
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → M.EssentialMarkedArc) (η : C(Interval,S))
    (n : ℕ) (hn : 0 < n) (ε : ℝ)
    (hcollar : ∀ k : Fin n, ∀ t : Interval,
      (t:ℝ) ≤ ε ∨ 1-ε ≤ (t:ℝ) → ∀ j,
      η (intervalMeshParameter n hn k t) ∉ (r j).val.image) :
    ∀ j, Disjoint
      (Set.range η \ ⋃ k : Fin n,
        (η ∘ intervalMeshParameter n hn k) '' {t : Interval | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε})
      (r j).val.image := by
  intro j
  rw [Set.disjoint_left]
  rintro x ⟨⟨s,rfl⟩,hout⟩ hj
  obtain ⟨k,t,ht⟩ := intervalMeshParameter_cover n hn s
  by_cases hcore : ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε
  · apply hout
    exact Set.mem_iUnion.mpr ⟨k,t,hcore,by simp [Function.comp_def,ht]⟩
  · have hcol : (t:ℝ) ≤ ε ∨ 1-ε ≤ (t:ℝ) := by
      rcases lt_or_ge (t:ℝ) ε with hl | hl
      · exact Or.inl hl.le
      · exact Or.inr (le_of_not_ge (fun hh => hcore ⟨hl,hh⟩))
    exact hcollar k t hcol j (ht.symm ▸ hj)

/-- Trimming is expressed in the global interval coordinate, so its outputs
feed the actual interval crosscut theorem without a replacement-data adapter. -/
theorem actual_trimmed_interval_mesh_parameter_image
    (n : ℕ) (hn : 0 < n) (k : Fin n)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) :
    intervalMeshParameter n hn k '' {t : Interval | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε} =
      Set.projIcc 0 1 zero_le_one '' Set.Icc
        (((k.val:ℝ)+ε)/n) (((k.val:ℝ)+(1-ε))/n) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlo : 0 < ((k.val:ℝ)+ε)/n := div_pos (by positivity) hnR
  have hhi : ((k.val:ℝ)+(1-ε))/n < 1 := by
    apply (div_lt_one hnR).mpr
    have hk : (k.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast k.isLt
    linarith
  ext s
  constructor
  · rintro ⟨t,ht,rfl⟩
    refine ⟨((k.val:ℝ)+(t:ℝ))/n,⟨?_,?_⟩,?_⟩
    · exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [ht.1])
    · exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [ht.2])
    · apply Subtype.ext
      exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one (intervalMeshParameter n hn k t).property)
  · rintro ⟨s,hs,rfl⟩
    have hs0 : 0 ≤ s := hlo.le.trans hs.1
    have hs1 : s ≤ 1 := hs.2.trans hhi.le
    have hslow : (k.val:ℝ)+ε ≤ s*n := (div_le_iff₀ hnR).mp hs.1
    have hshigh : s*n ≤ (k.val:ℝ)+(1-ε) := (le_div_iff₀ hnR).mp hs.2
    let t : Interval := ⟨s*n-k.val,by constructor <;> linarith⟩
    refine ⟨t,⟨by dsimp [t]; linarith,by dsimp [t]; linarith⟩,Subtype.ext ?_⟩
    rw [Set.projIcc_of_mem zero_le_one ⟨hs0,hs1⟩]
    change ((k.val:ℝ)+(s*n-k.val))/n = s
    field_simp
    ring

end CurveComplex.ArcFinitePosition

namespace CurveComplex.ArcFinitePosition
open Set

/-- Internal repairs together with the two clear exterior mesh vertices account
for every closed-piece endpoint, including a mesh consisting of one piece. -/
theorem actual_interval_mesh_all_ends_off
    {S : Type} [TopologicalSpace S] {J : Type}
    (η : C(Interval,S)) (H : AmbientIsotopy S) (old : J → Set S)
    (n : ℕ) (hn : 0 < n)
    (hleft : ∀ j, H.finalMap (η 0) ∉ old j)
    (hright : ∀ j, H.finalMap (η 1) ∉ old j)
    (hseam : ∀ k : Fin (n-1), ∀ j,
      H.finalMap (η ⟨((k.val:ℝ)+1)/n,by
        have hnR : (0:ℝ) < n := by exact_mod_cast hn
        constructor
        · positivity
        · apply (div_le_one hnR).mpr
          have hk : k.val+1 ≤ n := by omega
          exact_mod_cast hk⟩) ∉ old j) :
    ∀ k : Fin n, ∀ j,
      H.finalMap (η (intervalMeshParameter n hn k 0)) ∉ old j ∧
      H.finalMap (η (intervalMeshParameter n hn k 1)) ∉ old j := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  intro k j
  constructor
  · by_cases hk : k.val = 0
    · have he : intervalMeshParameter n hn k 0 = 0 := by
        apply Subtype.ext; simp [intervalMeshParameter,hk]
      rw [he]; exact hleft j
    · let q : Fin (n-1) := ⟨k.val-1,by omega⟩
      have hq : (q.val:ℝ)+1 = k.val := by
        exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ k.val by omega))
      have hh := hseam q j
      have hp : intervalMeshParameter n hn k 0 =
          (⟨((q.val:ℝ)+1)/n,by
            constructor
            · positivity
            · apply (div_le_one hnR).mpr
              have hk : q.val+1 ≤ n := by omega
              exact_mod_cast hk⟩ : Interval) := by
        apply Subtype.ext
        change ((k.val:ℝ)+(0:Interval).val)/n = ((q.val:ℝ)+1)/n
        simp [hq]
      rw [hp]
      exact hh
  · by_cases hk : k.val+1 = n
    · have he : intervalMeshParameter n hn k 1 = 1 := by
        apply Subtype.ext
        have hkR : (k.val:ℝ)+1 = n := by exact_mod_cast hk
        change ((k.val:ℝ)+1)/n = 1
        rw [hkR,div_self hnR.ne']
      rw [he]; exact hright j
    · let q : Fin (n-1) := ⟨k.val,by omega⟩
      exact hseam q j

end CurveComplex.ArcFinitePosition
