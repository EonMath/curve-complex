import C0FiniteTriangulatedDisk
import CyclicLayeredRadialInverse

open Set
open scoped BigOperators
namespace CurveComplex.FiniteArcDisk

/-- Recognition of the prescribed cyclic layered triangle complex and its
literal bottom boundary as the original weak-realization disk/sphere pair. -/
theorem cyclic_layered_realization_disk_pair (n : ℕ) (hn : 3 ≤ n) (steps : ℕ)
    (K : AbstractSimplicialComplex (Option (Fin (steps + 1) × Fin n)))
    (hK : ∀ σ, σ ∈ K.faces ↔ σ.Nonempty ∧
      ((∃ j : Fin n, σ ⊆ {none, some (Fin.last steps, j),
        some (Fin.last steps, ⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩)}) ∨
       (∃ (t : Fin steps) (j : Fin n), σ ⊆
        {some (t.castSucc,j), some (t.castSucc,⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩),
         some (t.succ,⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩)}) ∨
       (∃ (t : Fin steps) (j : Fin n), σ ⊆
        {some (t.castSucc,j), some (t.succ,j),
         some (t.succ,⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩)}))) 
    (B : AbstractSimplicialComplex (Fin n))
    (hB : ∀ σ, σ ∈ B.faces ↔ σ.Nonempty ∧
      ∃ j : Fin n, σ ⊆ {j, ⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩})
    (inc : C(RealizationPoint B, RealizationPoint K))
    (hinc : ∀ x v, (inc x).weight v = ∑ j : Fin n,
      if some ((0 : Fin (steps+1)),j) = v then x.weight j else 0) :
    ∃ (diskHome : RealizationPoint K ≃ₜ ClosedDisk)
      (boundaryHome : RealizationPoint B ≃ₜ DiskCircle),
      (∀ x, (boundaryHome x).val = (diskHome (inc x)).val) ∧
      (∀ x : RealizationPoint K,
        x ∈ Set.range inc ↔ ‖(diskHome x).val‖ = 1) := by
  classical
  have finiteCompact {V : Type} [Fintype V] [DecidableEq V]
      (L : AbstractSimplicialComplex V) : CompactSpace (RealizationPoint L) := by
    have he : finiteSupportLocus L Finset.univ = Set.univ := by
      ext x
      simp [finiteSupportLocus]
    exact isCompact_univ_iff.mp (he ▸ isCompact_finiteSupportLocus L Finset.univ)
  let : CompactSpace (RealizationPoint K) := finiteCompact K
  let : CompactSpace (RealizationPoint B) := finiteCompact B
  have sum_weights {V : Type} [Fintype V] [DecidableEq V]
      (L : AbstractSimplicialComplex V) (x : RealizationPoint L) :
      ∑ v, x.weight v = 1 := by
    obtain ⟨σ, _, hz, hs⟩ := x.liesInFace
    rw [← hs]
    exact (Finset.sum_subset (Finset.subset_univ σ) (by
      intro v _ hv
      exact hz v hv)).symm
  let bottom : Fin n → Option (Fin (steps+1) × Fin n) := fun j => some (0,j)
  have bottom_injective : Function.Injective bottom := by
    intro i j h
    exact (Prod.mk.inj (Option.some.inj h)).2
  have inc_bottom (x : RealizationPoint B) (j : Fin n) :
      (inc x).weight (bottom j) = x.weight j := by
    simp only [hinc, bottom, Option.some.injEq, Prod.mk.injEq, true_and,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have inc_off (x : RealizationPoint B) (v) (hv : v ∉ Set.range bottom) :
      (inc x).weight v = 0 := by
    rw [hinc]
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (fun h => hv ⟨j,h⟩)
  have inc_injective : Function.Injective inc := by
    intro x y h
    apply RealizationPoint.ext
    funext j
    have he := congrArg (fun z : RealizationPoint K => z.weight (bottom j)) h
    simpa only [inc_bottom] using he
  have inc_closed : Topology.IsClosedEmbedding inc :=
    inc.continuous.isClosedEmbedding inc_injective
  let next : Fin n → Fin n := fun j => ⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩
  have angular_support (x : RealizationPoint K) :
      ∃ j : Fin n, ∀ t k, k ∉ ({j,next j} : Finset (Fin n)) →
        x.weight (some (t,k)) = 0 := by
    obtain ⟨σ,hσ,hzero,_⟩ := x.liesInFace
    rcases (hK σ).mp hσ with ⟨_,⟨j,hj⟩ | ⟨t,j,hj⟩ | ⟨t,j,hj⟩⟩
    all_goals
      refine ⟨j, ?_⟩
      intro s k hk
      apply hzero
      intro hv
      have h := hj hv
      simp only [Finset.mem_insert,Finset.mem_singleton,Option.some.injEq,
        Prod.mk.injEq,reduceCtorEq] at h
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hk
      aesop
  have range_iff_off (x : RealizationPoint K) :
      x ∈ Set.range inc ↔ ∀ v, v ∉ Set.range bottom → x.weight v = 0 := by
    constructor
    · rintro ⟨y,rfl⟩
      exact inc_off y
    · intro hz
      have hsum : ∑ j, x.weight (bottom j) = 1 := by
        rw [← sum_weights K x]
        exact Finset.sum_bij_ne_zero
          (fun j _ _ => bottom j)
          (by simp)
          (by intro i _ _ j _ _ h; exact bottom_injective h)
          (by
            intro v _ hv
            have hr : v ∈ Set.range bottom := by
              by_contra hn
              exact hv (hz v hn)
            rcases hr with ⟨j,rfl⟩
            exact ⟨j,Finset.mem_univ _,hv,rfl⟩)
          (by simp)
      obtain ⟨j,hj⟩ := angular_support x
      have hface : ({j,next j} : Finset (Fin n)) ∈ B.faces := by
        exact (hB _).mpr ⟨by simp, j, Finset.Subset.refl _⟩
      let y : RealizationPoint B := {
        weight := fun k => x.weight (bottom k)
        nonneg := fun k => x.nonneg _
        liesInFace := ⟨{j,next j},hface,fun k hk => hj 0 k hk,by
          rw [← hsum]
          exact Finset.sum_subset (Finset.subset_univ _) (by
            intro k _ hk
            exact hj 0 k hk)⟩ }
      refine ⟨y,?_⟩
      apply RealizationPoint.ext
      funext v
      by_cases hv : v ∈ Set.range bottom
      · obtain ⟨k,rfl⟩ := hv
        exact inc_bottom y k
      · rw [inc_off y v hv,hz v hv]
  let levelRadius : Fin (steps+1) → ℝ := fun t =>
    1 - (t.val : ℝ) / ((steps : ℝ)+1)
  have denom_pos : 0 < (steps : ℝ)+1 := by positivity
  have levelRadius_pos (t : Fin (steps+1)) : 0 < levelRadius t := by
    dsimp [levelRadius]
    apply sub_pos.mpr
    apply (div_lt_one denom_pos).mpr
    exact_mod_cast t.isLt
  have levelRadius_le (t : Fin (steps+1)) : levelRadius t ≤ 1 := by
    dsimp [levelRadius]
    have : 0 ≤ (t.val : ℝ) / ((steps : ℝ)+1) := by positivity
    linarith
  have levelRadius_eq_one (t : Fin (steps+1)) : levelRadius t = 1 ↔ t = 0 := by
    dsimp [levelRadius]
    rw [sub_eq_self, div_eq_zero_iff]
    have hd : (steps : ℝ)+1 ≠ 0 := ne_of_gt denom_pos
    simp only [hd, or_false, Nat.cast_eq_zero]
    exact (Fin.ext_iff (a := t) (b := 0)).symm
  let vertexRadius : Option (Fin (steps+1) × Fin n) → ℝ :=
    fun v => match v with | none => 0 | some p => levelRadius p.1
  have vertexRadius_nonneg (v) : 0 ≤ vertexRadius v := by
    cases v with
    | none => exact le_rfl
    | some p => exact (levelRadius_pos p.1).le
  have vertexRadius_le (v) : vertexRadius v ≤ 1 := by
    cases v with
    | none => norm_num [vertexRadius]
    | some p => exact levelRadius_le p.1
  have vertexRadius_eq_one (v) : vertexRadius v = 1 ↔ v ∈ Set.range bottom := by
    cases v with
    | none => simp [vertexRadius,bottom]
    | some p =>
      rcases p with ⟨t,j⟩
      change levelRadius t = 1 ↔ _
      rw [levelRadius_eq_one]
      simp [bottom, Prod.mk.injEq,eq_comm]
  let radius : RealizationPoint K → ℝ :=
    fun x => ∑ v, vertexRadius v * x.weight v
  have radius_nonneg (x) : 0 ≤ radius x :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (vertexRadius_nonneg v) (x.nonneg v))
  have radius_le (x) : radius x ≤ 1 := by
    rw [← sum_weights K x]
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_of_le_one_left (x.nonneg v) (vertexRadius_le v)
  have radius_eq_one (x) : radius x = 1 ↔ x ∈ Set.range inc := by
    rw [range_iff_off]
    have hdeficit : ∑ v, (1 - vertexRadius v) * x.weight v = 1 - radius x := by
      simp only [sub_mul,one_mul,Finset.sum_sub_distrib,sum_weights,radius]
    constructor
    · intro h v hv
      have hz : ∑ v, (1 - vertexRadius v) * x.weight v = 0 := by
        rw [hdeficit,h]
        ring
      have he := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ =>
        mul_nonneg (sub_nonneg.mpr (vertexRadius_le v)) (x.nonneg v))).mp hz v
          (Finset.mem_univ _)
      rcases mul_eq_zero.mp he with he | he
      · exact False.elim (hv ((vertexRadius_eq_one v).mp (by linarith)))
      · exact he
    · intro h
      have hz : ∑ v, (1 - vertexRadius v) * x.weight v = 0 := by
        apply Finset.sum_eq_zero
        intro v _
        by_cases hv : v ∈ Set.range bottom
        · rw [(vertexRadius_eq_one v).mpr hv]
          ring
        · rw [h v hv,mul_zero]
      rw [hdeficit] at hz
      linarith
  let coneCoordinates : RealizationPoint K → (Fin n → ℝ) := fun x j =>
    ∑ t : Fin (steps+1), levelRadius t * x.weight (some (t,j))
  have coneCoordinates_continuous : Continuous coneCoordinates := by
    apply continuous_pi
    intro j
    exact continuous_finsetSum _ fun t _ =>
      continuous_const.mul (continuous_weight K (some (t,j)))
  have coneCoordinates_nonneg (x) (j) : 0 ≤ coneCoordinates x j := by
    exact Finset.sum_nonneg fun t _ => mul_nonneg (levelRadius_pos t).le (x.nonneg _)
  have coneCoordinates_sum (x) : ∑ j, coneCoordinates x j = radius x := by
    dsimp [coneCoordinates,radius]
    rw [Fintype.sum_option,Fintype.sum_prod_type,Finset.sum_comm]
    simp [vertexRadius]
  have coneCoordinates_support (x) : ∃ j : Fin n,
      ∀ k, k ∉ ({j,next j} : Finset (Fin n)) → coneCoordinates x k = 0 := by
    obtain ⟨j,hj⟩ := angular_support x
    refine ⟨j,?_⟩
    intro k hk
    apply Finset.sum_eq_zero
    intro t _
    rw [hj t k hk,mul_zero]
  have coneCoordinates_bottom (x : RealizationPoint B) : coneCoordinates (inc x) = x.weight := by
    funext j
    have hz (t : Fin (steps+1)) (ht : t ≠ 0) :
        (inc x).weight (some (t,j)) = 0 := by
      apply inc_off
      simpa [bottom,eq_comm] using ht
    rw [show coneCoordinates (inc x) j =
      ∑ t : Fin (steps+1), levelRadius t * (inc x).weight (some (t,j)) from rfl]
    rw [Finset.sum_eq_single 0]
    · rw [(levelRadius_eq_one 0).mpr rfl,one_mul]
      exact inc_bottom x j
    · intro t _ ht
      rw [hz t ht,mul_zero]
    · simp
  let coneSet : Set (Fin n → ℝ) := {q |
    (∀ j, 0 ≤ q j) ∧ (∑ j, q j) ≤ 1 ∧
      ∃ j : Fin n, ∀ k, k ∉ ({j,next j} : Finset (Fin n)) → q k = 0}
  let coneMap : RealizationPoint K → coneSet := fun x =>
    ⟨coneCoordinates x,coneCoordinates_nonneg x,
      (coneCoordinates_sum x).trans_le (radius_le x),coneCoordinates_support x⟩
  have coneMap_continuous : Continuous coneMap :=
    coneCoordinates_continuous.subtype_mk _
  have coneMap_boundary_exact (x) :
      x ∈ Set.range inc ↔ (∑ j, (coneMap x).val j) = 1 := by
    rw [show (∑ j, (coneMap x).val j) = radius x from coneCoordinates_sum x]
    exact (radius_eq_one x).symm
  have coneMap_bijective_zero (hsteps : steps = 0) : Function.Bijective coneMap := by
    subst steps
    have hcoord (x : RealizationPoint K) (j : Fin n) :
        (coneMap x).val j = x.weight (some (0,j)) := by
      simp [coneMap,coneCoordinates,levelRadius]
    constructor
    · intro x y h
      have hsome (j) : x.weight (some (0,j)) = y.weight (some (0,j)) := by
        simpa only [hcoord] using congrArg (fun z : coneSet => z.val j) h
      have hx := sum_weights K x
      have hy := sum_weights K y
      simp only [Fintype.sum_option,Fintype.sum_prod_type,Fin.sum_univ_succ,
        Fin.sum_univ_zero,add_zero] at hx hy
      have hnone : x.weight none = y.weight none := by
        have hsum : (∑ j, x.weight (some (0,j))) = ∑ j,y.weight (some (0,j)) :=
          Finset.sum_congr rfl (fun j _ => hsome j)
        linarith
      apply RealizationPoint.ext
      funext v
      cases v with
      | none => exact hnone
      | some p =>
        rcases p with ⟨t,j⟩
        have ht : t = 0 := by apply Fin.ext; omega
        simpa only [ht] using hsome j
    · intro q
      obtain ⟨j,hj⟩ := q.property.2.2
      let w : Option (Fin 1 × Fin n) → ℝ := fun v =>
        match v with | none => 1 - ∑ k,q.val k | some p => q.val p.2
      have hw_nonneg (v) : 0 ≤ w v := by
        cases v with
        | none => exact sub_nonneg.mpr q.property.2.1
        | some p => exact q.property.1 p.2
      have hw_sum : ∑ v,w v = 1 := by
        simp only [Fintype.sum_option,Fintype.sum_prod_type,Fin.sum_univ_succ,
          Fin.sum_univ_zero,add_zero,w]
        ring
      let σ : Finset (Option (Fin 1 × Fin n)) :=
        {none,some (0,j),some (0,next j)}
      have hσ : σ ∈ K.faces := by
        apply (hK σ).mpr
        exact ⟨by simp [σ],Or.inl ⟨j,by simp [σ,next]⟩⟩
      have hw_support (v) (hv : v ∉ σ) : w v = 0 := by
        cases v with
        | none => exact False.elim (hv (by simp [σ]))
        | some p =>
          rcases p with ⟨t,k⟩
          have ht : t = 0 := by apply Fin.ext; omega
          apply hj k
          simpa [σ,ht,eq_comm] using hv
      let x : RealizationPoint K := {
        weight := w
        nonneg := hw_nonneg
        liesInFace := ⟨σ,hσ,hw_support,by
          rw [← hw_sum]
          exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hw_support v hv)⟩ }
      refine ⟨x,?_⟩
      apply Subtype.ext
      funext k
      rw [hcoord]
  have cone_chart_of_boundary (b : RealizationPoint B ≃ₜ DiskCircle) :
      ∃ H : coneSet ≃ₜ ClosedDisk,
        ∀ q, ‖(H q).val‖ = ∑ j, q.val j := by
    let radial : EdgeTime × RealizationPoint B → coneSet := fun p =>
      ⟨fun j => (p.1 : ℝ) * p.2.weight j,by
        refine ⟨fun j => mul_nonneg p.1.property.1 (p.2.nonneg j),?_,?_⟩
        · rw [← Finset.mul_sum,sum_weights,mul_one]
          exact p.1.property.2
        · obtain ⟨σ,hσ,hzero,_⟩ := p.2.liesInFace
          obtain ⟨_,j,hj⟩ := (hB σ).mp hσ
          refine ⟨j,?_⟩
          intro k hk
          change p.1.val * p.2.weight k = 0
          rw [hzero k (fun h => hk (hj h)),mul_zero]⟩
    have radial_cont : Continuous radial := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro j
      exact (continuous_subtype_val.comp continuous_fst).mul
        ((continuous_weight B j).comp continuous_snd)
    have radial_sum (p : EdgeTime × RealizationPoint B) :
        ∑ j, (radial p).val j = p.1.val := by
      change ∑ j, p.1.val * p.2.weight j = p.1.val
      rw [← Finset.mul_sum,sum_weights,mul_one]
    have radial_surj : Function.Surjective radial := by
      intro q
      let r : ℝ := ∑ j, q.val j
      have hr : 0 ≤ r := Finset.sum_nonneg (fun j _ => q.property.1 j)
      by_cases hr0 : r = 0
      · refine ⟨(0, realizationVertex B ⟨0,by omega⟩ (B.singleton_mem _)),?_⟩
        apply Subtype.ext
        funext j
        change 0 * _ = q.val j
        rw [zero_mul]
        exact ((Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => q.property.1 k)).mp hr0 j (Finset.mem_univ _)).symm
      · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
        obtain ⟨j,hj⟩ := q.property.2.2
        have hface : ({j,next j} : Finset (Fin n)) ∈ B.faces :=
          (hB _).mpr ⟨by simp,j,Finset.Subset.refl _⟩
        let x : RealizationPoint B := {
          weight := fun k => q.val k / r
          nonneg := fun k => div_nonneg (q.property.1 k) hr
          liesInFace := ⟨{j,next j},hface,by
            intro k hk
            rw [hj k hk,zero_div],by
            have hs : ∑ k, q.val k / r = 1 := by
              rw [← Finset.sum_div]
              exact div_self hr0
            rw [← hs]
            exact Finset.sum_subset (Finset.subset_univ _) (by
              intro k _ hk
              rw [hj k hk,zero_div])⟩ }
        refine ⟨(⟨r,hr,q.property.2.1⟩,x),?_⟩
        apply Subtype.ext
        funext k
        exact mul_div_cancel₀ (q.val k) hr0
    have radial_fibers (p q : EdgeTime × RealizationPoint B) :
        radial p = radial q ↔ p.1 = q.1 ∧ (p.1 = 0 ∨ p.2 = q.2) := by
      constructor
      · intro h
        have ht : p.1 = q.1 := by
          apply Subtype.ext
          simpa only [radial_sum] using congrArg (fun z : coneSet => ∑ j,z.val j) h
        refine ⟨ht,?_⟩
        by_cases hp : p.1 = 0
        · exact Or.inl hp
        · right
          apply RealizationPoint.ext
          funext j
          have h0 : p.1.val ≠ 0 := fun he => hp (Subtype.ext he)
          apply mul_left_cancel₀ h0
          have he := congrArg (fun z : coneSet => z.val j) h
          change p.1.val * p.2.weight j = q.1.val * q.2.weight j at he
          simpa only [← ht] using he
      · rintro ⟨ht,hp | hx⟩
        · apply Subtype.ext
          funext j
          change p.1.val * p.2.weight j = q.1.val * q.2.weight j
          rw [← ht,hp]
          simp
        · cases p
          cases q
          simp_all
    let diskRadial : EdgeTime × RealizationPoint B → ClosedDisk := fun p =>
      ⟨p.1.val • (b p.2).val,by
        rw [mem_closedBall_zero_iff]
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.property.1,
          mem_sphere_zero_iff_norm.mp (b p.2).property,mul_one] using p.1.property.2⟩
    have diskRadial_norm (p : EdgeTime × RealizationPoint B) :
        ‖(diskRadial p).val‖ = p.1.val := by
      change ‖p.1.val • (b p.2).val‖ = p.1.val
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg p.1.property.1,
        mem_sphere_zero_iff_norm.mp (b p.2).property,mul_one]
    have diskRadial_cont : Continuous diskRadial := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp continuous_fst).smul
        (continuous_subtype_val.comp (b.continuous.comp continuous_snd))
    have diskRadial_fibers (p q : EdgeTime × RealizationPoint B) :
        diskRadial p = diskRadial q ↔ p.1 = q.1 ∧ (p.1 = 0 ∨ p.2 = q.2) := by
      constructor
      · intro h
        have ht : p.1 = q.1 := by
          apply Subtype.ext
          simpa only [diskRadial_norm] using congrArg (fun z : ClosedDisk => ‖z.val‖) h
        refine ⟨ht,?_⟩
        by_cases hp : p.1 = 0
        · exact Or.inl hp
        · right
          apply b.injective
          apply Subtype.ext
          have h0 : p.1.val ≠ 0 := fun he => hp (Subtype.ext he)
          apply smul_right_injective DiskPlane h0
          have he := congrArg (fun z : ClosedDisk => z.val) h
          change p.1.val • (b p.2).val = q.1.val • (b q.2).val at he
          simpa only [← ht] using he
      · rintro ⟨ht,hp | hx⟩
        · apply Subtype.ext
          change p.1.val • (b p.2).val = q.1.val • (b q.2).val
          rw [← ht,hp]
          simp
        · cases p
          cases q
          simp_all
    have diskRadial_surj : Function.Surjective diskRadial := by
      intro y
      by_cases hy : y.val = 0
      · refine ⟨(0,realizationVertex B ⟨0,by omega⟩ (B.singleton_mem _)),?_⟩
        apply Subtype.ext
        simp [diskRadial,hy]
      · have hnorm : ‖y.val‖ ≠ 0 := norm_ne_zero_iff.mpr hy
        let z : DiskCircle := ⟨‖y.val‖⁻¹ • y.val,by
          rw [mem_sphere_zero_iff_norm,norm_smul,norm_inv,Real.norm_eq_abs,
            abs_norm,inv_mul_cancel₀ hnorm]⟩
        refine ⟨(⟨‖y.val‖,norm_nonneg _,mem_closedBall_zero_iff.mp y.property⟩,b.symm z),?_⟩
        apply Subtype.ext
        change ‖y.val‖ • (b (b.symm z)).val = y.val
        rw [b.apply_symm_apply]
        change ‖y.val‖ • (‖y.val‖⁻¹ • y.val) = y.val
        rw [smul_smul,mul_inv_cancel₀ hnorm,one_smul]
    let select : coneSet → EdgeTime × RealizationPoint B := Function.surjInv radial_surj
    have select_right (q) : radial (select q) = q := Function.surjInv_eq radial_surj q
    let F : coneSet → ClosedDisk := diskRadial ∘ select
    have F_radial (p) : F (radial p) = diskRadial p := by
      apply (diskRadial_fibers _ _).mpr
      apply (radial_fibers _ _).mp
      exact select_right _
    have F_cont : Continuous F := by
      apply (radial_cont.isClosedMap.isQuotientMap radial_cont radial_surj).continuous_iff.mpr
      have he : F ∘ radial = diskRadial := funext F_radial
      rw [he]
      exact diskRadial_cont
    have F_inj : Function.Injective F := by
      intro q r h
      rw [← select_right q,← select_right r]
      apply (radial_fibers _ _).mpr
      exact (diskRadial_fibers _ _).mp h
    have F_surj : Function.Surjective F := by
      intro y
      obtain ⟨p,hp⟩ := diskRadial_surj y
      exact ⟨radial p,(F_radial p).trans hp⟩
    have cone_compact : CompactSpace coneSet := by
      exact ⟨by
        rw [← Set.range_eq_univ.mpr radial_surj]
        exact isCompact_range radial_cont⟩
    let := cone_compact
    let e : coneSet ≃ ClosedDisk := Equiv.ofBijective F ⟨F_inj,F_surj⟩
    let H : coneSet ≃ₜ ClosedDisk :=
      (show Continuous (e : coneSet → ClosedDisk) from F_cont).homeoOfEquivCompactToT2
    refine ⟨H,?_⟩
    intro q
    change ‖(diskRadial (select q)).val‖ = ∑ j,q.val j
    rw [diskRadial_norm]
    exact (radial_sum (select q)).symm.trans
      (congrArg (fun z : coneSet => ∑ j,z.val j) (select_right q))
  have pair_of_chart
      (H : RealizationPoint K ≃ₜ ClosedDisk)
      (hH : ∀ x, x ∈ Set.range inc ↔ ‖(H x).val‖ = 1) :
      ∃ h : RealizationPoint B ≃ₜ DiskCircle,
        ∀ x, (h x).val = (H (inc x)).val := by
    let f : RealizationPoint B → DiskCircle := fun x =>
      ⟨(H (inc x)).val, by
        apply mem_sphere_zero_iff_norm.mpr
        exact (hH (inc x)).mp ⟨x,rfl⟩⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (H.continuous.comp inc.continuous)
    have hf_inj : Function.Injective f := by
      intro x y h
      apply inc_injective
      apply H.injective
      apply Subtype.ext
      exact congrArg (fun z : DiskCircle => z.val) h
    have hf_surj : Function.Surjective f := by
      intro y
      let z : ClosedDisk := ⟨y.val, Metric.sphere_subset_closedBall y.property⟩
      have hz : H.symm z ∈ Set.range inc := by
        apply (hH _).mpr
        simp [z]
      obtain ⟨x,hx⟩ := hz
      refine ⟨x,?_⟩
      apply Subtype.ext
      change (H (inc x)).val = y.val
      rw [hx,H.apply_symm_apply]
    let e := Equiv.ofBijective f ⟨hf_inj,hf_surj⟩
    exact ⟨(show Continuous (e : RealizationPoint B → DiskCircle) from hf).homeoOfEquivCompactToT2,fun _ => rfl⟩
  -- Unpaid combinatorial inverse for the triangulated annular layers.
  have coneMap_bijective : Function.Bijective coneMap := by
    apply (Function.bijective_iff_existsUnique coneMap).mpr
    intro q
    obtain ⟨x, hx, huniq⟩ := cyclic_layered_radial_coordinates_unique_recovery
      n hn steps K hK q.val q.property.1 q.property.2.1 q.property.2.2
    refine ⟨x, ?_, ?_⟩
    · apply Subtype.ext
      funext j
      exact hx j
    · intro y hy
      apply huniq y
      intro j
      exact congrArg (fun z : coneSet => z.val j) hy
  -- This will follow from the independently owned cyclic boundary parameter.
  have boundary_chart : Nonempty (RealizationPoint B ≃ₜ DiskCircle) := by
    classical
    have affine_boundary (n : ℕ) (hn : 3 ≤ n)
        (B : AbstractSimplicialComplex (Fin n))
        (hB : ∀ σ, σ ∈ B.faces ↔ σ.Nonempty ∧
          ∃ j : Fin n, σ ⊆ {j, ⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩})
        (times : Fin (n+1) → EdgeTime)
        (times_strict : StrictMono (fun k => (times k : ℝ)))
        (times_zero : times 0 = 0)
        (times_one : times (Fin.last n) = 1) :
        ∃ param : C(EdgeTime, RealizationPoint B),
          Function.Surjective param ∧
          (∀ t u : EdgeTime, param t = param u ↔
            t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0)) ∧
          (∀ (k : Fin n) (u : EdgeTime) (v : Fin n),
            (param (Icc.convexComb (times k.castSucc) (times k.succ) u)).weight v =
              (1 - (u : ℝ)) * (if k = v then 1 else 0) +
              (u : ℝ) * (if (⟨(k.val+1)%n, Nat.mod_lt _ (by omega)⟩ : Fin n) = v then 1 else 0)) ∧
          (∀ k : Fin n,
            faceCarrier B {k, ⟨(k.val+1)%n, Nat.mod_lt _ (by omega)⟩} =
              Set.range (fun u : EdgeTime =>
                param (Icc.convexComb (times k.castSucc) (times k.succ) u))) := by
      classical
      let nxt (k : Fin n) : Fin n := ⟨(k.val+1)%n, Nat.mod_lt _ (by omega)⟩
      have hnxt (k : Fin n) : k ≠ nxt k := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [nxt] at hv
        have hk := k.isLt
        by_cases hlast : k.val + 1 = n
        · rw [hlast, Nat.mod_self] at hv
          omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hv
          omega
      have hnxt_val (k : Fin n) :
          (nxt k).val = if k.val + 1 = n then 0 else k.val + 1 := by
        dsimp [nxt]
        split_ifs with h
        · simp [h]
        · exact Nat.mod_eq_of_lt (by omega)
      have hswap (k l : Fin n) : k = nxt l → nxt k = l → False := by
        intro h₁ h₂
        have hk := k.isLt
        have hl := l.isLt
        have h₁v := congrArg Fin.val h₁
        have h₂v := congrArg Fin.val h₂
        rw [hnxt_val] at h₁v h₂v
        split_ifs at h₁v h₂v <;> omega
      have hface (k : Fin n) : ({k, nxt k} : Finset (Fin n)) ∈ B.faces :=
        (hB _).mpr ⟨by simp, k, Finset.Subset.refl _⟩
      let E (k : Fin n) : EdgeTime → RealizationPoint B :=
        faceSegment B {k, nxt k} (hface k)
          (finiteSimplexVertex {k, nxt k} k (by simp))
          (finiteSimplexVertex {k, nxt k} (nxt k) (by simp))
      have hE (k : Fin n) (u : EdgeTime) (v : Fin n) :
          (E k u).weight v = (1 - (u : ℝ)) * (if k = v then 1 else 0) +
            (u : ℝ) * (if nxt k = v then 1 else 0) := by
        by_cases hv : v ∈ ({k, nxt k} : Finset (Fin n))
        · simp only [E, faceSegment, Function.comp_apply, faceInclusion, hv,
            dite_true, finiteSimplexSegment, finiteSimplexVertex]
          simp only [eq_comm]
        · have hk : k ≠ v := by intro h; subst v; simp at hv
          have hnext : nxt k ≠ v := by intro h; subst v; simp at hv
          have hv' : ¬(v = k ∨ v = nxt k) := by simpa using hv
          simp [E, faceSegment, faceInclusion, hv', hk, hnext]
      have hEc (k : Fin n) : Continuous (E k) :=
        faceSegment_continuous B _ (hface k) _ _
      have hEend (k : Fin n) (v : Fin n) :
          (E k 0).weight v = (if k = v then 1 else 0) ∧
          (E k 1).weight v = (if nxt k = v then 1 else 0) := by
        simp [hE]
      let q : Fin n × EdgeTime → EdgeTime := fun z =>
        Icc.convexComb (times z.1.castSucc) (times z.1.succ) z.2
      have hgap (k : Fin n) :
          (times k.castSucc : ℝ) < (times k.succ : ℝ) :=
        times_strict (by simp)
      have hqb (k : Fin n) (u : EdgeTime) :
          (times k.castSucc : ℝ) ≤ (q (k,u) : ℝ) ∧
          (q (k,u) : ℝ) ≤ (times k.succ : ℝ) := by
        dsimp [q]
        exact ⟨Icc.le_convexComb (hgap k).le u, Icc.convexComb_le (hgap k).le u⟩
      have hqsurj : Function.Surjective q := by
        have cover : ∀ m : ℕ, ∀ f : Fin (m+1) → EdgeTime,
            ∀ t : EdgeTime, (f 0 : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ (f (Fin.last m) : ℝ) →
            (∀ k : Fin m, (f k.castSucc : ℝ) ≤ (f k.succ : ℝ)) →
            (0 < m) → ∃ k : Fin m, (f k.castSucc : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (f k.succ : ℝ) := by
          intro m
          induction m with
          | zero => intro f t _ _ _ hm; omega
          | succ m ih =>
            intro f t h₀ h₁ hmono hm
            let last : Fin (m+1) := Fin.last m
            by_cases ht : (f last.castSucc : ℝ) ≤ (t : ℝ)
            · exact ⟨last, ht, by simpa [last] using h₁⟩
            · by_cases hpos : 0 < m
              · obtain ⟨k,hk₀,hk₁⟩ := ih (fun j => f j.castSucc) t h₀
                  (le_of_not_ge ht) (fun j => hmono j.castSucc) hpos
                refine ⟨k.castSucc, hk₀, ?_⟩
                simpa using hk₁
              · have hlast : last.castSucc = 0 := by apply Fin.ext; dsimp [last]; omega
                rw [hlast] at ht
                exact False.elim (ht h₀)
        intro t
        obtain ⟨k,hk₀,hk₁⟩ := cover n times t (by simpa [times_zero] using t.property.1)
          (by simpa [times_one] using t.property.2) (fun k => (hgap k).le) (by omega)
        let u : EdgeTime := ⟨((t : ℝ) - (times k.castSucc : ℝ)) /
          ((times k.succ : ℝ) - (times k.castSucc : ℝ)), by
            constructor
            · exact div_nonneg (sub_nonneg.mpr hk₀) (sub_nonneg.mpr (hgap k).le)
            · apply (div_le_one (sub_pos.mpr (hgap k))).mpr
              exact sub_le_sub_right hk₁ _⟩
        refine ⟨(k,u), ?_⟩
        apply Subtype.ext
        dsimp [q, Icc.convexComb, u]
        field_simp [ne_of_gt (sub_pos.mpr (hgap k))]
        ring
      have hqcompat : ∀ k l : Fin n, ∀ u w : EdgeTime,
          q (k,u) = q (l,w) → E k u = E l w := by
        have ordered (k l : Fin n) (u w : EdgeTime) (hkl : k < l)
            (heq : q (k,u) = q (l,w)) : E k u = E l w := by
          have hmid : (times k.succ : ℝ) ≤ (times l.castSucc : ℝ) :=
            times_strict.monotone (by change k.val + 1 ≤ l.val; change k.val < l.val at hkl; omega)
          have hqb₁ := hqb k u
          have hqb₂ := hqb l w
          have heqr := congrArg Subtype.val heq
          have htimes : (times k.succ : ℝ) = (times l.castSucc : ℝ) := by linarith
          have hind : k.succ = l.castSucc := times_strict.injective htimes
          have hlval : k.val + 1 = l.val := congrArg Fin.val hind
          have hnxtkl : nxt k = l := by
            apply Fin.ext
            dsimp [nxt]
            rw [Nat.mod_eq_of_lt (by omega)]
            exact hlval
          have hu : u = 1 := by
            apply Subtype.ext
            change (u : ℝ) = 1
            have he : (q (k,u) : ℝ) = (times k.succ : ℝ) := by linarith
            dsimp [q, Icc.convexComb] at he
            nlinarith [hgap k]
          have hw : w = 0 := by
            apply Subtype.ext
            change (w : ℝ) = 0
            have he : (q (l,w) : ℝ) = (times l.castSucc : ℝ) := by linarith
            dsimp [q, Icc.convexComb] at he
            nlinarith [hgap l]
          rw [hu, hw]
          apply RealizationPoint.ext
          funext v
          simp [hE, hnxtkl]
        intro k l u w heq
        rcases lt_trichotomy k l with hkl | hkl | hkl
        · exact ordered k l u w hkl heq
        · subst l
          have hu : u = w := by
            apply Subtype.ext
            have he := congrArg Subtype.val heq
            dsimp [q, Icc.convexComb] at he
            nlinarith [hgap k]
          rw [hu]
        · exact (ordered l k w u hkl heq.symm).symm
      obtain ⟨r,hr⟩ := hqsurj.hasRightInverse
      let p : EdgeTime → RealizationPoint B := fun t => E (r t).1 (r t).2
      have hpq (k : Fin n) (u : EdgeTime) : p (q (k,u)) = E k u :=
        hqcompat (r (q (k,u))).1 k (r (q (k,u))).2 u (hr _)
      have hqc : Continuous q := continuous_prod_of_discrete_left.mpr
        (fun k => (Icc.continuous_convexComb (times k.castSucc) (times k.succ)))
      have hpc : Continuous p := by
        apply (hqc.isClosedMap.isQuotientMap hqc hqsurj).continuous_iff.mpr
        have he : p ∘ q = fun z : Fin n × EdgeTime => E z.1 z.2 := by
          funext z
          exact hpq z.1 z.2
        rw [he]
        exact continuous_prod_of_discrete_left.mpr hEc
      have hErange (k : Fin n) : faceCarrier B {k, nxt k} = Set.range (E k) := by
        ext x
        constructor
        · intro hx
          have hzero : ∀ v, v ∉ ({k,nxt k} : Finset (Fin n)) → x.weight v = 0 := hx
          have hsum : x.weight k + x.weight (nxt k) = 1 := by
            obtain ⟨σ,hσ,hz,hs⟩ := x.liesInFace
            have htotal : ∑ v : Fin n, x.weight v = 1 := by
              rw [← hs]
              exact (Finset.sum_subset (Finset.subset_univ σ) (fun v _ hv => hz v hv)).symm
            have hpairsum : ∑ v ∈ ({k,nxt k} : Finset (Fin n)), x.weight v = 1 := by
              rw [← htotal]
              exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hzero v hv)
            simpa [Finset.sum_pair (hnxt k)] using hpairsum
          let u : EdgeTime := ⟨x.weight (nxt k), x.nonneg _, by linarith [x.nonneg k]⟩
          refine ⟨u, ?_⟩
          apply RealizationPoint.ext
          funext v
          rw [hE]
          by_cases hkv : k = v
          · subst v
            simp [u, (hnxt k).symm]
            linarith
          · by_cases hnv : nxt k = v
            · subst v
              simp [u, hnxt k]
            · simp [hkv, hnv]
              exact (hzero v (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact not_or.mpr ⟨Ne.symm hkv, Ne.symm hnv⟩)).symm
        · rintro ⟨u,rfl⟩ v hv
          have hk : k ≠ v := by intro h; subst v; simp at hv
          have hnext : nxt k ≠ v := by intro h; subst v; simp at hv
          simp [hE, hk, hnext]
      have hpsurj : Function.Surjective p := by
        intro x
        obtain ⟨σ,hσ,hz,hs⟩ := x.liesInFace
        obtain ⟨_,k,hk⟩ := (hB σ).mp hσ
        have hx : x ∈ faceCarrier B {k,nxt k} := by
          intro v hv
          exact hz v (fun h => hv (hk h))
        rw [hErange] at hx
        obtain ⟨u,hu⟩ := hx
        exact ⟨q (k,u), (hpq k u).trans hu⟩
      have hEinterior (k l : Fin n) (u w : EdgeTime) (hkl : k ≠ l)
          (heq : E k u = E l w) : u = 0 ∨ u = 1 := by
        by_contra hu
        push Not at hu
        have hu₀ : 0 < (u : ℝ) := by
          by_contra h
          apply hu.1
          apply Subtype.ext
          change (u : ℝ) = 0
          linarith [u.property.1]
        have hu₁ : (u : ℝ) < 1 := by
          by_contra h
          apply hu.2
          apply Subtype.ext
          change (u : ℝ) = 1
          linarith [u.property.2]
        have hkpos : 0 < (E k u).weight k := by
          rw [hE]
          simp only [ite_true, ite_eq_right (hnxt k).symm, mul_one, mul_zero, add_zero]
          exact sub_pos.mpr hu₁
        have hnpos : 0 < (E k u).weight (nxt k) := by simpa [hE, hnxt k] using hu₀
        have hkpair : k = l ∨ k = nxt l := by
          by_contra h
          push Not at h
          rw [heq, hE] at hkpos
          simp [Ne.symm h.1, Ne.symm h.2] at hkpos
        have hnpair : nxt k = l ∨ nxt k = nxt l := by
          by_contra h
          push Not at h
          rw [heq, hE] at hnpos
          simp [Ne.symm h.1, Ne.symm h.2] at hnpos
        rcases hkpair with h | h
        · exact hkl h
        · rcases hnpair with h' | h'
          · exact hswap k l h h'
          · exact hnxt k (h.trans h'.symm)
      let cyc (i : Fin (n+1)) : Fin n := ⟨i.val % n, Nat.mod_lt _ (by omega)⟩
      have hcycval (i : Fin (n+1)) : (cyc i).val = if i.val = n then 0 else i.val := by
        dsimp [cyc]
        split_ifs with h
        · simp [h]
        · exact Nat.mod_eq_of_lt (by omega)
      have hcyc (i j : Fin (n+1)) (h : cyc i = cyc j) :
          i = j ∨ (i = 0 ∧ j = Fin.last n) ∨ (i = Fin.last n ∧ j = 0) := by
        have hi := i.isLt
        have hj := j.isLt
        have hv := congrArg Fin.val h
        rw [hcycval, hcycval] at hv
        by_cases hi' : i.val = n <;> by_cases hj' : j.val = n
        · exact Or.inl (Fin.ext (by omega))
        · have hvj : 0 = j.val := by
            simpa only [ite_eq_left hi', ite_eq_right hj'] using hv
          exact Or.inr (Or.inr ⟨Fin.ext hi', Fin.ext hvj.symm⟩)
        · have hvi : i.val = 0 := by
            simpa only [ite_eq_right hi', ite_eq_left hj'] using hv
          exact Or.inr (Or.inl ⟨Fin.ext hvi, Fin.ext hj'⟩)
        · exact Or.inl (Fin.ext (by
            simpa only [ite_eq_right hi', ite_eq_right hj'] using hv))
      have hendpoint (k : Fin n) (u : EdgeTime) (hu : u = 0 ∨ u = 1) :
          ∃ i : Fin (n+1), q (k,u) = times i ∧
            ∀ v : Fin n, (E k u).weight v = if cyc i = v then 1 else 0 := by
        rcases hu with rfl | rfl
        · refine ⟨k.castSucc, by simp [q], ?_⟩
          have hc : cyc k.castSucc = k := by
            apply Fin.ext
            dsimp [cyc]
            exact Nat.mod_eq_of_lt k.isLt
          intro v
          simp [hE, hc]
        · refine ⟨k.succ, by simp [q], ?_⟩
          intro v
          change (E k 1).weight v = if nxt k = v then 1 else 0
          simp [hE]
      have hEqfib (k l : Fin n) (u w : EdgeTime) (heq : E k u = E l w) :
          q (k,u) = q (l,w) ∨ (q (k,u) = 0 ∧ q (l,w) = 1) ∨
            (q (k,u) = 1 ∧ q (l,w) = 0) := by
        by_cases hkl : k = l
        · subst l
          have hu : u = w := by
            apply Subtype.ext
            have hh := congrArg (fun x : RealizationPoint B => x.weight (nxt k)) heq
            simpa [hE, hnxt k] using hh
          exact Or.inl (by rw [hu])
        · obtain ⟨i,hi,hiw⟩ := hendpoint k u (hEinterior k l u w hkl heq)
          obtain ⟨j,hj,hjw⟩ := hendpoint l w (hEinterior l k w u (Ne.symm hkl) heq.symm)
          have hc : cyc i = cyc j := by
            have hh := congrArg (fun x : RealizationPoint B => x.weight (cyc i)) heq
            rw [hiw, hjw] at hh
            by_contra h
            simp [Ne.symm h] at hh
          rcases hcyc i j hc with h | ⟨hi₀,hj₁⟩ | ⟨hi₁,hj₀⟩
          · exact Or.inl (hi.trans (congrArg times h) |>.trans hj.symm)
          · exact Or.inr (Or.inl ⟨hi.trans (by rw [hi₀,times_zero]),
              hj.trans (by rw [hj₁,times_one])⟩)
          · exact Or.inr (Or.inr ⟨hi.trans (by rw [hi₁,times_one]),
              hj.trans (by rw [hj₀,times_zero])⟩)
      have hpseam : p 0 = p 1 := by
        let k₀ : Fin n := ⟨0,by omega⟩
        let k₁ : Fin n := ⟨n-1,by omega⟩
        have hk₀ : k₀.castSucc = 0 := by apply Fin.ext; rfl
        have hk₁ : k₁.succ = Fin.last n := by apply Fin.ext; dsimp [k₁]; omega
        have hqn₀ : q (k₀,0) = 0 := by simp [q,hk₀,times_zero]
        have hqn₁ : q (k₁,1) = 1 := by simp [q,hk₁,times_one]
        rw [← hqn₀, ← hqn₁, hpq, hpq]
        have hc : nxt k₁ = k₀ := by
          apply Fin.ext
          dsimp [nxt,k₀,k₁]
          rw [show n-1+1=n by omega, Nat.mod_self]
        apply RealizationPoint.ext
        funext v
        simp [hE, hc]
      refine ⟨⟨p,hpc⟩, hpsurj, ?_, ?_, ?_⟩
      · intro t s
        change p t = p s ↔ _
        constructor
        · intro h
          obtain ⟨⟨k,u⟩,ht⟩ := hqsurj t
          obtain ⟨⟨l,w⟩,hs⟩ := hqsurj s
          rw [← ht, ← hs, hpq, hpq] at h
          simpa only [ht,hs] using hEqfib k l u w h
        · rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
          · rfl
          · exact hpseam
          · exact hpseam.symm
      · intro k u v
        exact (congrArg (fun x : RealizationPoint B => x.weight v) (hpq k u)).trans (hE k u v)
      · intro k
        change faceCarrier B {k,nxt k} = _
        rw [hErange]
        congr 1
        funext u
        exact (hpq k u).symm
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    let times : Fin (n+1) → EdgeTime := fun k => ⟨(k.val : ℝ) / n,
      div_nonneg (Nat.cast_nonneg _) hnR.le,
      (div_le_one hnR).mpr (by exact_mod_cast (show k.val ≤ n by omega))⟩
    have htstrict : StrictMono (fun k => (times k : ℝ)) := by
      intro i j hij
      apply (div_lt_div_iff_of_pos_right hnR).mpr
      exact_mod_cast hij
    have ht0 : times 0 = 0 := by apply Subtype.ext; simp [times]
    have ht1 : times (Fin.last n) = 1 := by
      apply Subtype.ext
      simp [times,ne_of_gt hnR]
    obtain ⟨p,hpsurj,hpfib,_,_⟩ := affine_boundary n hn B hB times htstrict ht0 ht1
    let circleQuotient : EdgeTime → AddCircle (1 : ℝ) := fun t => (t.val : AddCircle (1 : ℝ))
    have hqc : Continuous circleQuotient :=
      (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
    have hqsurj : Function.Surjective circleQuotient := by
      intro z
      obtain ⟨t,ht,he⟩ := AddCircle.eq_coe_Ico z
      exact ⟨⟨t,ht.1,ht.2.le⟩,he⟩
    have hqfib (t u : EdgeTime) : circleQuotient t = circleQuotient u ↔
        t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
      have interior (a : EdgeTime) (ha : a ≠ 1) : a.val ∈ Ico (0 : ℝ) 1 :=
        ⟨a.property.1, lt_of_le_of_ne a.property.2 (fun h => ha (Subtype.ext h))⟩
      have h01 : circleQuotient 0 = circleQuotient 1 := by simp [circleQuotient,AddCircle.coe_period]
      constructor
      · intro h
        by_cases ht : t = 1
        · by_cases hu : u = 1
          · exact Or.inl (ht.trans hu.symm)
          · right; right
            refine ⟨ht,?_⟩
            apply Subtype.ext
            apply (AddCircle.coe_eq_zero_iff_of_mem_Ico (interior u hu)).mp
            change circleQuotient u = 0
            rw [← h,ht]
            simp [circleQuotient,AddCircle.coe_period]
        · by_cases hu : u = 1
          · right; left
            refine ⟨?_,hu⟩
            apply Subtype.ext
            apply (AddCircle.coe_eq_zero_iff_of_mem_Ico (interior t ht)).mp
            change circleQuotient t = 0
            rw [h,hu]
            simp [circleQuotient,AddCircle.coe_period]
          · left
            apply Subtype.ext
            apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
              (p := (1 : ℝ)) (a := 0) (by simpa using interior t ht)
              (by simpa using interior u hu)).mp
            exact h
      · rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
        · rfl
        · exact h01
        · exact h01.symm
    let select : RealizationPoint B → EdgeTime := Function.surjInv hpsurj
    have hs (x) : p (select x) = x := Function.surjInv_eq hpsurj x
    let f : RealizationPoint B → AddCircle (1 : ℝ) := circleQuotient ∘ select
    have hfp (t) : f (p t) = circleQuotient t := by
      apply (hqfib _ _).mpr
      apply (hpfib _ _).mp
      exact hs _
    have hfc : Continuous f := by
      apply (p.continuous.isClosedMap.isQuotientMap p.continuous hpsurj).continuous_iff.mpr
      have he : f ∘ p = circleQuotient := funext hfp
      rw [he]
      exact hqc
    have hfi : Function.Injective f := by
      intro x y h
      rw [← hs x,← hs y]
      exact (hpfib _ _).mpr ((hqfib _ _).mp h)
    have hfs : Function.Surjective f := by
      intro z
      obtain ⟨t,ht⟩ := hqsurj z
      exact ⟨p t,(hfp t).trans ht⟩
    let e : RealizationPoint B ≃ AddCircle (1 : ℝ) := Equiv.ofBijective f ⟨hfi,hfs⟩
    let c : RealizationPoint B ≃ₜ AddCircle (1 : ℝ) :=
      (show Continuous (e : RealizationPoint B → AddCircle (1 : ℝ)) from hfc).homeoOfEquivCompactToT2
    let L : ℂ ≃ₗᵢ[ℝ] DiskPlane :=
      Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
    let circleEquiv : Circle ≃ DiskCircle := {
      toFun := fun z => ⟨L z,by rw [mem_sphere_zero_iff_norm,L.norm_map]; exact z.norm_coe⟩
      invFun := fun w => ⟨L.symm w,by
        change L.symm w.val ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm,L.symm.norm_map]
        exact mem_sphere_zero_iff_norm.mp w.property⟩
      left_inv := by intro z; apply Subtype.ext; exact L.symm_apply_apply z.val
      right_inv := by intro w; apply Subtype.ext; exact L.apply_symm_apply w.val }
    have circle_cont : Continuous (circleEquiv : Circle → DiskCircle) := by
      apply Continuous.subtype_mk
      exact L.continuous.comp continuous_subtype_val
    let circleHome : Circle ≃ₜ DiskCircle := circle_cont.homeoOfEquivCompactToT2
    exact ⟨c.trans ((AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).trans circleHome)⟩
  obtain ⟨b⟩ := boundary_chart
  obtain ⟨hc,hcnorm⟩ := cone_chart_of_boundary b
  let e := Equiv.ofBijective coneMap coneMap_bijective
  let ec : RealizationPoint K ≃ₜ coneSet :=
    (show Continuous (e : RealizationPoint K → coneSet) from
      coneMap_continuous).homeoOfEquivCompactToT2
  let H : RealizationPoint K ≃ₜ ClosedDisk := ec.trans hc
  have hH (x) : x ∈ Set.range inc ↔ ‖(H x).val‖ = 1 := by
    change x ∈ Set.range inc ↔ ‖(hc (coneMap x)).val‖ = 1
    rw [hcnorm]
    exact coneMap_boundary_exact x
  obtain ⟨h,hcompat⟩ := pair_of_chart H hH
  exact ⟨H,h,hcompat,hH⟩

set_option maxHeartbeats 2000000

/-- An affine boundary parameter over an arbitrary strict time partition,
with exact circle seam fibers and equality of each edge-carrier range. -/
theorem cyclic_realization_affine_boundary_parameter (n : ℕ) (hn : 3 ≤ n)
    (B : AbstractSimplicialComplex (Fin n))
    (hB : ∀ σ, σ ∈ B.faces ↔ σ.Nonempty ∧
      ∃ j : Fin n, σ ⊆ {j, ⟨(j.val+1)%n, Nat.mod_lt _ (by omega)⟩})
    (times : Fin (n+1) → EdgeTime)
    (times_strict : StrictMono (fun k => (times k : ℝ)))
    (times_zero : times 0 = 0)
    (times_one : times (Fin.last n) = 1) :
    ∃ param : C(EdgeTime, RealizationPoint B),
      Function.Surjective param ∧
      (∀ t u : EdgeTime, param t = param u ↔
        t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0)) ∧
      (∀ (k : Fin n) (u : EdgeTime) (v : Fin n),
        (param (Icc.convexComb (times k.castSucc) (times k.succ) u)).weight v =
          (1 - (u : ℝ)) * (if k = v then 1 else 0) +
          (u : ℝ) * (if (⟨(k.val+1)%n, Nat.mod_lt _ (by omega)⟩ : Fin n) = v then 1 else 0)) ∧
      (∀ k : Fin n,
        faceCarrier B {k, ⟨(k.val+1)%n, Nat.mod_lt _ (by omega)⟩} =
          Set.range (fun u : EdgeTime =>
            param (Icc.convexComb (times k.castSucc) (times k.succ) u))) := by
  classical
  let nxt (k : Fin n) : Fin n := ⟨(k.val+1)%n, Nat.mod_lt _ (by omega)⟩
  have hnxt (k : Fin n) : k ≠ nxt k := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [nxt] at hv
    have hk := k.isLt
    by_cases hlast : k.val + 1 = n
    · rw [hlast, Nat.mod_self] at hv
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hv
      omega
  have hnxt_val (k : Fin n) :
      (nxt k).val = if k.val + 1 = n then 0 else k.val + 1 := by
    dsimp [nxt]
    split_ifs with h
    · simp [h]
    · exact Nat.mod_eq_of_lt (by omega)
  have hswap (k l : Fin n) : k = nxt l → nxt k = l → False := by
    intro h₁ h₂
    have hk := k.isLt
    have hl := l.isLt
    have h₁v := congrArg Fin.val h₁
    have h₂v := congrArg Fin.val h₂
    rw [hnxt_val] at h₁v h₂v
    split_ifs at h₁v h₂v <;> omega
  have hface (k : Fin n) : ({k, nxt k} : Finset (Fin n)) ∈ B.faces :=
    (hB _).mpr ⟨by simp, k, Finset.Subset.refl _⟩
  let E (k : Fin n) : EdgeTime → RealizationPoint B :=
    faceSegment B {k, nxt k} (hface k)
      (finiteSimplexVertex {k, nxt k} k (by simp))
      (finiteSimplexVertex {k, nxt k} (nxt k) (by simp))
  have hE (k : Fin n) (u : EdgeTime) (v : Fin n) :
      (E k u).weight v = (1 - (u : ℝ)) * (if k = v then 1 else 0) +
        (u : ℝ) * (if nxt k = v then 1 else 0) := by
    by_cases hv : v ∈ ({k, nxt k} : Finset (Fin n))
    · simp only [E, faceSegment, Function.comp_apply, faceInclusion, hv,
        dite_true, finiteSimplexSegment, finiteSimplexVertex]
      simp only [eq_comm]
    · have hk : k ≠ v := by intro h; subst v; simp at hv
      have hnext : nxt k ≠ v := by intro h; subst v; simp at hv
      have hv' : ¬(v = k ∨ v = nxt k) := by simpa using hv
      simp [E, faceSegment, faceInclusion, hv', hk, hnext]
  have hEc (k : Fin n) : Continuous (E k) :=
    faceSegment_continuous B _ (hface k) _ _
  have hEend (k : Fin n) (v : Fin n) :
      (E k 0).weight v = (if k = v then 1 else 0) ∧
      (E k 1).weight v = (if nxt k = v then 1 else 0) := by
    simp [hE]
  let q : Fin n × EdgeTime → EdgeTime := fun z =>
    Icc.convexComb (times z.1.castSucc) (times z.1.succ) z.2
  have hgap (k : Fin n) :
      (times k.castSucc : ℝ) < (times k.succ : ℝ) :=
    times_strict (by simp)
  have hqb (k : Fin n) (u : EdgeTime) :
      (times k.castSucc : ℝ) ≤ (q (k,u) : ℝ) ∧
      (q (k,u) : ℝ) ≤ (times k.succ : ℝ) := by
    dsimp [q]
    exact ⟨Icc.le_convexComb (hgap k).le u, Icc.convexComb_le (hgap k).le u⟩
  have hqsurj : Function.Surjective q := by
    have cover : ∀ m : ℕ, ∀ f : Fin (m+1) → EdgeTime,
        ∀ t : EdgeTime, (f 0 : ℝ) ≤ (t : ℝ) → (t : ℝ) ≤ (f (Fin.last m) : ℝ) →
        (∀ k : Fin m, (f k.castSucc : ℝ) ≤ (f k.succ : ℝ)) →
        (0 < m) → ∃ k : Fin m, (f k.castSucc : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (f k.succ : ℝ) := by
      intro m
      induction m with
      | zero => intro f t _ _ _ hm; omega
      | succ m ih =>
        intro f t h₀ h₁ hmono hm
        let last : Fin (m+1) := Fin.last m
        by_cases ht : (f last.castSucc : ℝ) ≤ (t : ℝ)
        · exact ⟨last, ht, by simpa [last] using h₁⟩
        · by_cases hpos : 0 < m
          · obtain ⟨k,hk₀,hk₁⟩ := ih (fun j => f j.castSucc) t h₀
              (le_of_not_ge ht) (fun j => hmono j.castSucc) hpos
            refine ⟨k.castSucc, hk₀, ?_⟩
            simpa using hk₁
          · have hlast : last.castSucc = 0 := by apply Fin.ext; dsimp [last]; omega
            rw [hlast] at ht
            exact False.elim (ht h₀)
    intro t
    obtain ⟨k,hk₀,hk₁⟩ := cover n times t (by simpa [times_zero] using t.property.1)
      (by simpa [times_one] using t.property.2) (fun k => (hgap k).le) (by omega)
    let u : EdgeTime := ⟨((t : ℝ) - (times k.castSucc : ℝ)) /
      ((times k.succ : ℝ) - (times k.castSucc : ℝ)), by
        constructor
        · exact div_nonneg (sub_nonneg.mpr hk₀) (sub_nonneg.mpr (hgap k).le)
        · apply (div_le_one (sub_pos.mpr (hgap k))).mpr
          exact sub_le_sub_right hk₁ _⟩
    refine ⟨(k,u), ?_⟩
    apply Subtype.ext
    dsimp [q, Icc.convexComb, u]
    field_simp [ne_of_gt (sub_pos.mpr (hgap k))]
    ring
  have hqcompat : ∀ k l : Fin n, ∀ u w : EdgeTime,
      q (k,u) = q (l,w) → E k u = E l w := by
    have ordered (k l : Fin n) (u w : EdgeTime) (hkl : k < l)
        (heq : q (k,u) = q (l,w)) : E k u = E l w := by
      have hmid : (times k.succ : ℝ) ≤ (times l.castSucc : ℝ) :=
        times_strict.monotone (by change k.val + 1 ≤ l.val; change k.val < l.val at hkl; omega)
      have hqb₁ := hqb k u
      have hqb₂ := hqb l w
      have heqr := congrArg Subtype.val heq
      have htimes : (times k.succ : ℝ) = (times l.castSucc : ℝ) := by linarith
      have hind : k.succ = l.castSucc := times_strict.injective htimes
      have hlval : k.val + 1 = l.val := congrArg Fin.val hind
      have hnxtkl : nxt k = l := by
        apply Fin.ext
        dsimp [nxt]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact hlval
      have hu : u = 1 := by
        apply Subtype.ext
        change (u : ℝ) = 1
        have he : (q (k,u) : ℝ) = (times k.succ : ℝ) := by linarith
        dsimp [q, Icc.convexComb] at he
        nlinarith [hgap k]
      have hw : w = 0 := by
        apply Subtype.ext
        change (w : ℝ) = 0
        have he : (q (l,w) : ℝ) = (times l.castSucc : ℝ) := by linarith
        dsimp [q, Icc.convexComb] at he
        nlinarith [hgap l]
      rw [hu, hw]
      apply RealizationPoint.ext
      funext v
      simp [hE, hnxtkl]
    intro k l u w heq
    rcases lt_trichotomy k l with hkl | hkl | hkl
    · exact ordered k l u w hkl heq
    · subst l
      have hu : u = w := by
        apply Subtype.ext
        have he := congrArg Subtype.val heq
        dsimp [q, Icc.convexComb] at he
        nlinarith [hgap k]
      rw [hu]
    · exact (ordered l k w u hkl heq.symm).symm
  obtain ⟨r,hr⟩ := hqsurj.hasRightInverse
  let p : EdgeTime → RealizationPoint B := fun t => E (r t).1 (r t).2
  have hpq (k : Fin n) (u : EdgeTime) : p (q (k,u)) = E k u :=
    hqcompat (r (q (k,u))).1 k (r (q (k,u))).2 u (hr _)
  have hqc : Continuous q := continuous_prod_of_discrete_left.mpr
    (fun k => (Icc.continuous_convexComb (times k.castSucc) (times k.succ)))
  have hpc : Continuous p := by
    apply (hqc.isClosedMap.isQuotientMap hqc hqsurj).continuous_iff.mpr
    have he : p ∘ q = fun z : Fin n × EdgeTime => E z.1 z.2 := by
      funext z
      exact hpq z.1 z.2
    rw [he]
    exact continuous_prod_of_discrete_left.mpr hEc
  have hErange (k : Fin n) : faceCarrier B {k, nxt k} = Set.range (E k) := by
    ext x
    constructor
    · intro hx
      have hzero : ∀ v, v ∉ ({k,nxt k} : Finset (Fin n)) → x.weight v = 0 := hx
      have hsum : x.weight k + x.weight (nxt k) = 1 := by
        obtain ⟨σ,hσ,hz,hs⟩ := x.liesInFace
        have htotal : ∑ v : Fin n, x.weight v = 1 := by
          rw [← hs]
          exact (Finset.sum_subset (Finset.subset_univ σ) (fun v _ hv => hz v hv)).symm
        have hpairsum : ∑ v ∈ ({k,nxt k} : Finset (Fin n)), x.weight v = 1 := by
          rw [← htotal]
          exact Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hzero v hv)
        simpa [Finset.sum_pair (hnxt k)] using hpairsum
      let u : EdgeTime := ⟨x.weight (nxt k), x.nonneg _, by linarith [x.nonneg k]⟩
      refine ⟨u, ?_⟩
      apply RealizationPoint.ext
      funext v
      rw [hE]
      by_cases hkv : k = v
      · subst v
        simp [u, (hnxt k).symm]
        linarith
      · by_cases hnv : nxt k = v
        · subst v
          simp [u, hnxt k]
        · simp [hkv, hnv]
          exact (hzero v (by simp only [Finset.mem_insert, Finset.mem_singleton]; exact not_or.mpr ⟨Ne.symm hkv, Ne.symm hnv⟩)).symm
    · rintro ⟨u,rfl⟩ v hv
      have hk : k ≠ v := by intro h; subst v; simp at hv
      have hnext : nxt k ≠ v := by intro h; subst v; simp at hv
      simp [hE, hk, hnext]
  have hpsurj : Function.Surjective p := by
    intro x
    obtain ⟨σ,hσ,hz,hs⟩ := x.liesInFace
    obtain ⟨_,k,hk⟩ := (hB σ).mp hσ
    have hx : x ∈ faceCarrier B {k,nxt k} := by
      intro v hv
      exact hz v (fun h => hv (hk h))
    rw [hErange] at hx
    obtain ⟨u,hu⟩ := hx
    exact ⟨q (k,u), (hpq k u).trans hu⟩
  have hEinterior (k l : Fin n) (u w : EdgeTime) (hkl : k ≠ l)
      (heq : E k u = E l w) : u = 0 ∨ u = 1 := by
    by_contra hu
    push Not at hu
    have hu₀ : 0 < (u : ℝ) := by
      by_contra h
      apply hu.1
      apply Subtype.ext
      change (u : ℝ) = 0
      linarith [u.property.1]
    have hu₁ : (u : ℝ) < 1 := by
      by_contra h
      apply hu.2
      apply Subtype.ext
      change (u : ℝ) = 1
      linarith [u.property.2]
    have hkpos : 0 < (E k u).weight k := by
      rw [hE]
      simp only [ite_true, ite_eq_right (hnxt k).symm, mul_one, mul_zero, add_zero]
      exact sub_pos.mpr hu₁
    have hnpos : 0 < (E k u).weight (nxt k) := by simpa [hE, hnxt k] using hu₀
    have hkpair : k = l ∨ k = nxt l := by
      by_contra h
      push Not at h
      rw [heq, hE] at hkpos
      simp [Ne.symm h.1, Ne.symm h.2] at hkpos
    have hnpair : nxt k = l ∨ nxt k = nxt l := by
      by_contra h
      push Not at h
      rw [heq, hE] at hnpos
      simp [Ne.symm h.1, Ne.symm h.2] at hnpos
    rcases hkpair with h | h
    · exact hkl h
    · rcases hnpair with h' | h'
      · exact hswap k l h h'
      · exact hnxt k (h.trans h'.symm)
  let cyc (i : Fin (n+1)) : Fin n := ⟨i.val % n, Nat.mod_lt _ (by omega)⟩
  have hcycval (i : Fin (n+1)) : (cyc i).val = if i.val = n then 0 else i.val := by
    dsimp [cyc]
    split_ifs with h
    · simp [h]
    · exact Nat.mod_eq_of_lt (by omega)
  have hcyc (i j : Fin (n+1)) (h : cyc i = cyc j) :
      i = j ∨ (i = 0 ∧ j = Fin.last n) ∨ (i = Fin.last n ∧ j = 0) := by
    have hi := i.isLt
    have hj := j.isLt
    have hv := congrArg Fin.val h
    rw [hcycval, hcycval] at hv
    by_cases hi' : i.val = n <;> by_cases hj' : j.val = n
    · exact Or.inl (Fin.ext (by omega))
    · have hvj : 0 = j.val := by
        simpa only [ite_eq_left hi', ite_eq_right hj'] using hv
      exact Or.inr (Or.inr ⟨Fin.ext hi', Fin.ext hvj.symm⟩)
    · have hvi : i.val = 0 := by
        simpa only [ite_eq_right hi', ite_eq_left hj'] using hv
      exact Or.inr (Or.inl ⟨Fin.ext hvi, Fin.ext hj'⟩)
    · exact Or.inl (Fin.ext (by
        simpa only [ite_eq_right hi', ite_eq_right hj'] using hv))
  have hendpoint (k : Fin n) (u : EdgeTime) (hu : u = 0 ∨ u = 1) :
      ∃ i : Fin (n+1), q (k,u) = times i ∧
        ∀ v : Fin n, (E k u).weight v = if cyc i = v then 1 else 0 := by
    rcases hu with rfl | rfl
    · refine ⟨k.castSucc, by simp [q], ?_⟩
      have hc : cyc k.castSucc = k := by
        apply Fin.ext
        dsimp [cyc]
        exact Nat.mod_eq_of_lt k.isLt
      intro v
      simp [hE, hc]
    · refine ⟨k.succ, by simp [q], ?_⟩
      intro v
      change (E k 1).weight v = if nxt k = v then 1 else 0
      simp [hE]
  have hEqfib (k l : Fin n) (u w : EdgeTime) (heq : E k u = E l w) :
      q (k,u) = q (l,w) ∨ (q (k,u) = 0 ∧ q (l,w) = 1) ∨
        (q (k,u) = 1 ∧ q (l,w) = 0) := by
    by_cases hkl : k = l
    · subst l
      have hu : u = w := by
        apply Subtype.ext
        have hh := congrArg (fun x : RealizationPoint B => x.weight (nxt k)) heq
        simpa [hE, hnxt k] using hh
      exact Or.inl (by rw [hu])
    · obtain ⟨i,hi,hiw⟩ := hendpoint k u (hEinterior k l u w hkl heq)
      obtain ⟨j,hj,hjw⟩ := hendpoint l w (hEinterior l k w u (Ne.symm hkl) heq.symm)
      have hc : cyc i = cyc j := by
        have hh := congrArg (fun x : RealizationPoint B => x.weight (cyc i)) heq
        rw [hiw, hjw] at hh
        by_contra h
        simp [Ne.symm h] at hh
      rcases hcyc i j hc with h | ⟨hi₀,hj₁⟩ | ⟨hi₁,hj₀⟩
      · exact Or.inl (hi.trans (congrArg times h) |>.trans hj.symm)
      · exact Or.inr (Or.inl ⟨hi.trans (by rw [hi₀,times_zero]),
          hj.trans (by rw [hj₁,times_one])⟩)
      · exact Or.inr (Or.inr ⟨hi.trans (by rw [hi₁,times_one]),
          hj.trans (by rw [hj₀,times_zero])⟩)
  have hpseam : p 0 = p 1 := by
    let k₀ : Fin n := ⟨0,by omega⟩
    let k₁ : Fin n := ⟨n-1,by omega⟩
    have hk₀ : k₀.castSucc = 0 := by apply Fin.ext; rfl
    have hk₁ : k₁.succ = Fin.last n := by apply Fin.ext; dsimp [k₁]; omega
    have hqn₀ : q (k₀,0) = 0 := by simp [q,hk₀,times_zero]
    have hqn₁ : q (k₁,1) = 1 := by simp [q,hk₁,times_one]
    rw [← hqn₀, ← hqn₁, hpq, hpq]
    have hc : nxt k₁ = k₀ := by
      apply Fin.ext
      dsimp [nxt,k₀,k₁]
      rw [show n-1+1=n by omega, Nat.mod_self]
    apply RealizationPoint.ext
    funext v
    simp [hE, hc]
  refine ⟨⟨p,hpc⟩, hpsurj, ?_, ?_, ?_⟩
  · intro t s
    change p t = p s ↔ _
    constructor
    · intro h
      obtain ⟨⟨k,u⟩,ht⟩ := hqsurj t
      obtain ⟨⟨l,w⟩,hs⟩ := hqsurj s
      rw [← ht, ← hs, hpq, hpq] at h
      simpa only [ht,hs] using hEqfib k l u w h
    · rintro (rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · rfl
      · exact hpseam
      · exact hpseam.symm
  · intro k u v
    exact (congrArg (fun x : RealizationPoint B => x.weight v) (hpq k u)).trans (hE k u v)
  · intro k
    change faceCarrier B {k,nxt k} = _
    rw [hErange]
    congr 1
    funext u
    exact (hpq k u).symm

end CurveComplex.FiniteArcDisk
