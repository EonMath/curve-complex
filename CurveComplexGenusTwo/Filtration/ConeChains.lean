import CurveComplexGenusTwo.Filtration.FiltrationRelative

namespace CurveGenusTwo.Filtration

universe u v

variable {V : Type u} [DecidableEq V]

def IsNonemptyCone (K : FiniteComplex V) : Prop :=
  ∃ apex : V, ({apex} : Finset V) ∈ K ∧
    ∀ σ : Finset V, σ ∈ K → insert apex σ ∈ K

private theorem cone_insert_valid [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (σ : SimplexAt K n) (hna : a ∉ σ.1) :
    insert a σ.1 ∈ K ∧
      ((n + 1 = -1 ∧ insert a σ.1 = ∅) ∨
        (0 ≤ n + 1 ∧ ((insert a σ.1).card : ℤ) = n + 1 + 1)) := by
  have hc := Finset.card_insert_of_notMem hna
  refine ⟨ha σ.1 σ.2.1, Or.inr ?_⟩
  rcases σ.2.2 with h | h
  · have hcard : σ.1.card = 0 := by simp [h.2]
    constructor <;> omega
  · constructor <;> omega

private def cone_insert_simplex [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (σ : SimplexAt K n) (hna : a ∉ σ.1) :
    SimplexAt K (n + 1) :=
  ⟨insert a σ.1, cone_insert_valid K a ha n σ hna⟩

private noncomputable def cone_insert_chain [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) : chains K n →+ chains K (n + 1) :=
  FreeAbelianGroup.lift fun σ =>
    if hna : a ∉ σ.1 then
      (-1 : ℤ) ^ (σ.1.filter (· < a)).card •
        FreeAbelianGroup.of (cone_insert_simplex K a ha n σ hna)
    else 0

private theorem cone_face_valid [LinearOrder V] (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) {v : V} (hv : v ∈ σ.1) :
    σ.1.erase v ∈ K ∧
      ((n - 1 = -1 ∧ σ.1.erase v = ∅) ∨
        (0 ≤ n - 1 ∧ ((σ.1.erase v).card : ℤ) = (n - 1) + 1)) := by
  classical
  have hmem : σ.1.erase v ∈ K := K.down_closed (Finset.erase_subset v σ.1) σ.2.1
  refine ⟨hmem, ?_⟩
  rcases σ.2.2 with hneg | hpos
  · exact False.elim (by simp [hneg.2] at hv)
  · have hcard : (σ.1.erase v).card + 1 = σ.1.card := by
      simpa using Finset.card_erase_add_one hv
    by_cases hn : n = 0
    · left
      constructor
      · omega
      · have hσcard : σ.1.card = 1 := by omega
        exact Finset.card_eq_zero.mp (by omega)
    · right
      constructor <;> omega

private def cone_face_at [LinearOrder V] (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) (v : σ.1) : SimplexAt K (n - 1) :=
  ⟨σ.1.erase v.1, cone_face_valid K n σ v.2⟩

private theorem cone_faceBoundary_eq [LinearOrder V] (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) :
    faceBoundary K n σ = ∑ v ∈ σ.1.attach,
      (-1 : ℤ) ^ (σ.1.filter (· < v.1)).card •
        FreeAbelianGroup.of (cone_face_at K n σ v) := by
  classical
  rw [faceBoundary]
  conv_lhs => rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro v hv
  have hvalid := cone_face_valid K n σ v.2
  have hproof : (⟨σ.1.erase v.1, hvalid⟩ : SimplexAt K (n - 1)) =
      cone_face_at K n σ v := Subtype.ext rfl
  exact (dif_pos hvalid).trans (congrArg
    (fun x : SimplexAt K (n - 1) =>
      (-1 : ℤ) ^ (σ.1.filter (· < v.1)).card • FreeAbelianGroup.of x) hproof)

private theorem cone_boundary_of [LinearOrder V] (K : FiniteComplex V) (n : ℤ)
    (σ : SimplexAt K n) :
    boundary K n (FreeAbelianGroup.of σ) = faceBoundary K n σ := by
  simp [boundary]

private theorem cone_insert_chain_of [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (σ : SimplexAt K n) :
    cone_insert_chain K a ha n (FreeAbelianGroup.of σ) =
      if hna : a ∉ σ.1 then
        (-1 : ℤ) ^ (σ.1.filter (· < a)).card •
          FreeAbelianGroup.of (cone_insert_simplex K a ha n σ hna)
      else 0 := by
  simp [cone_insert_chain]

private theorem cone_sign_swap [LinearOrder V] (s : Finset V) (a v : V)
    (ha : a ∉ s) (hv : v ∈ s) :
    (-1 : ℤ) ^ (s.filter (· < a)).card *
      (-1 : ℤ) ^ ((insert a s).filter (· < v)).card =
    -((-1 : ℤ) ^ (s.filter (· < v)).card *
      (-1 : ℤ) ^ ((s.erase v).filter (· < a)).card) := by
  classical
  by_cases hav : a < v
  · have hfa : a ∈ (insert a s).filter (· < v) := by simp [hav]
    have hfv : v ∉ s.filter (· < a) := by simp [not_lt.mpr (le_of_lt hav)]
    have h1 : ((insert a s).filter (· < v)).card =
        (s.filter (· < v)).card + 1 := by
      rw [Finset.filter_insert, if_pos hav, Finset.card_insert_of_notMem]
      simp [ha]
    have h2 : ((s.erase v).filter (· < a)).card =
        (s.filter (· < a)).card := by
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem hfv]
    rw [h1, h2, ← pow_add, ← pow_add]
    simp [pow_add, mul_comm, mul_left_comm, mul_assoc]
  · have hva : v < a := lt_of_le_of_ne (le_of_not_gt hav) (Ne.symm (by
        intro h; exact ha (h ▸ hv)))
    have h1 : ((insert a s).filter (· < v)).card =
        (s.filter (· < v)).card := by
      rw [Finset.filter_insert, if_neg (not_lt.mpr (le_of_lt hva))]
    have h2 : ((s.erase v).filter (· < a)).card + 1 =
        (s.filter (· < a)).card := by
      rw [Finset.filter_erase]
      exact Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hv, hva⟩)
    rw [h1, ← pow_add, ← pow_add]
    have he : (s.filter (· < a)).card + (s.filter (· < v)).card =
        (s.filter (· < v)).card + ((s.erase v).filter (· < a)).card + 1 := by omega
    rw [he, pow_succ]
    simp [mul_assoc]

private theorem cone_sum_attach_insert [LinearOrder V]
    {G : Type*} [AddCommMonoid G] (s : Finset V) (a : V) (ha : a ∉ s)
    (f : {x // x ∈ insert a s} → G) :
    (∑ v ∈ (insert a s).attach, f v) =
      f ⟨a, Finset.mem_insert_self a s⟩ +
        ∑ v ∈ s.attach, f ⟨v.1, Finset.mem_insert_of_mem v.2⟩ := by
  classical
  rw [Finset.attach_insert]
  rw [Finset.sum_insert]
  · rw [Finset.sum_image]
    · intro x hx y hy hxy
      apply Subtype.ext
      exact congrArg (fun z : {z // z ∈ insert a s} => z.1) hxy
  · simp [ha]

private noncomputable def cone_boundary_next [LinearOrder V] (K : FiniteComplex V)
    (n : ℤ) : chains K (n + 1) →+ chains K n := by
  have hn : n + 1 - 1 = n := by omega
  exact Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
    (boundary K (n + 1))

private theorem cone_cast_apply {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x =
      Eq.mp (congrArg F h) (f x) := by
  cases h
  rfl

private theorem cone_cast_zero {ι : Type*} {F : ι → Type*}
    [∀ i, Zero (F i)] {i j : ι} (h : i = j) :
    Eq.mp (congrArg F h) (0 : F i) = 0 := by
  cases h
  rfl

private theorem cone_cast_zsmul {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    (r : ℤ) (x : F i) :
    Eq.mp (congrArg F h) (r • x) = r • Eq.mp (congrArg F h) x := by
  cases h
  rfl

private theorem cone_cast_sum {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {α : Type*} (s : Finset α) (f : α → F i) :
    Eq.mp (congrArg F h) (∑ x ∈ s, f x) =
      ∑ x ∈ s, Eq.mp (congrArg F h) (f x) := by
  cases h
  rfl

private theorem cone_cast_of {ι : Type*} {G : ι → Type*}
    {i j : ι} (h : i = j) (x : G i) :
    Eq.mp (congrArg (fun k => FreeAbelianGroup (G k)) h) (FreeAbelianGroup.of x) =
      FreeAbelianGroup.of (Eq.mp (congrArg G h) x) := by
  cases h
  rfl

private theorem cone_cast_simplex_val [LinearOrder V] (K : FiniteComplex V)
    {i j : ℤ} (h : i = j) (σ : SimplexAt K i) :
    (Eq.mp (congrArg (SimplexAt K) h) σ).1 = σ.1 := by
  cases h
  rfl

private theorem cone_boundary_next_of [LinearOrder V] (K : FiniteComplex V)
    (n : ℤ) (σ : SimplexAt K (n + 1)) :
    cone_boundary_next K n (FreeAbelianGroup.of σ) =
      Eq.mp (congrArg (chains K) (show n + 1 - 1 = n by omega))
        (faceBoundary K (n + 1) σ) := by
  have hn : n + 1 - 1 = n := by omega
  change (Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
    (boundary K (n + 1))) (FreeAbelianGroup.of σ) = _
  rw [cone_cast_apply hn, cone_boundary_of]

private theorem cone_cast_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) f.range =
      (Eq.mp (congrArg (fun k => A →+ F k) h) f).range := by
  cases h
  rfl

private theorem cone_boundaries_eq_range [LinearOrder V] (K : FiniteComplex V)
    (n : ℤ) : boundaries K n = (cone_boundary_next K n).range := by
  have hn : n + 1 - 1 = n := by omega
  change Eq.mp (congrArg (fun m : ℤ => AddSubgroup (chains K m)) hn)
      (boundary K (n + 1)).range =
    (Eq.mp (congrArg (fun m : ℤ => chains K (n + 1) →+ chains K m) hn)
      (boundary K (n + 1))).range
  exact cone_cast_range hn (boundary K (n + 1))

private noncomputable def cone_insert_prev [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) : chains K (n - 1) →+ chains K n := by
  have hn : n - 1 + 1 = n := by omega
  exact Eq.mp (congrArg (fun m : ℤ => chains K (n - 1) →+ chains K m) hn)
    (cone_insert_chain K a ha (n - 1))

private theorem cone_insert_prev_of_mem [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (τ : SimplexAt K (n - 1)) (ham : a ∈ τ.1) :
    cone_insert_prev K a ha n (FreeAbelianGroup.of τ) = 0 := by
  have hn : n - 1 + 1 = n := by omega
  change (Eq.mp (congrArg (fun m : ℤ => chains K (n - 1) →+ chains K m) hn)
    (cone_insert_chain K a ha (n - 1))) (FreeAbelianGroup.of τ) = 0
  rw [cone_cast_apply hn, cone_insert_chain_of]
  simp [ham]
  exact cone_cast_zero (F := chains K) hn

private theorem cone_insert_prev_of_not_mem [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (τ : SimplexAt K (n - 1)) (hna : a ∉ τ.1) :
    cone_insert_prev K a ha n (FreeAbelianGroup.of τ) =
      (-1 : ℤ) ^ (τ.1.filter (· < a)).card •
        FreeAbelianGroup.of
          (Eq.mp (congrArg (SimplexAt K)
            (show n - 1 + 1 = n by omega))
              (cone_insert_simplex K a ha (n - 1) τ hna)) := by
  have hn : n - 1 + 1 = n := by omega
  change (Eq.mp (congrArg (fun m : ℤ => chains K (n - 1) →+ chains K m) hn)
    (cone_insert_chain K a ha (n - 1))) (FreeAbelianGroup.of τ) =
    (-1 : ℤ) ^ (τ.1.filter (· < a)).card •
      FreeAbelianGroup.of (Eq.mp (congrArg (SimplexAt K) hn)
        (cone_insert_simplex K a ha (n - 1) τ hna))
  rw [cone_cast_apply hn, cone_insert_chain_of, dif_pos hna,
    cone_cast_zsmul, cone_cast_of]
  all_goals first | exact hn | exact congrArg (SimplexAt K) hn

private theorem cone_apex_face_eq [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (σ : SimplexAt K n) (hna : a ∉ σ.1) :
    Eq.mp (congrArg (SimplexAt K) (show n + 1 - 1 = n by omega))
      (cone_face_at K (n + 1) (cone_insert_simplex K a ha n σ hna)
        ⟨a, Finset.mem_insert_self a σ.1⟩) = σ := by
  have hn : n + 1 - 1 = n := by omega
  apply Subtype.ext
  rw [cone_cast_simplex_val K hn]
  simp [cone_face_at, cone_insert_simplex, hna]

private theorem cone_other_face_eq [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (σ : SimplexAt K n) (hna : a ∉ σ.1)
    (v : σ.1) :
    Eq.mp (congrArg (SimplexAt K) (show n + 1 - 1 = n by omega))
      (cone_face_at K (n + 1) (cone_insert_simplex K a ha n σ hna)
        ⟨v.1, Finset.mem_insert_of_mem v.2⟩) =
    Eq.mp (congrArg (SimplexAt K) (show n - 1 + 1 = n by omega))
      (cone_insert_simplex K a ha (n - 1) (cone_face_at K n σ v)
        (by simp [cone_face_at, Finset.mem_erase, hna])) := by
  have hn : n + 1 - 1 = n := by omega
  have hp : n - 1 + 1 = n := by omega
  apply Subtype.ext
  rw [cone_cast_simplex_val K hn, cone_cast_simplex_val K hp]
  exact Finset.erase_insert_of_ne
    (show a ≠ v.1 by intro h; exact hna (h.symm ▸ v.2))

private theorem cone_boundary_insert_formula [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (σ : SimplexAt K n) (hna : a ∉ σ.1) :
    cone_boundary_next K n
      (FreeAbelianGroup.of (cone_insert_simplex K a ha n σ hna)) =
      (-1 : ℤ) ^ (σ.1.filter (· < a)).card • FreeAbelianGroup.of σ +
        ∑ v ∈ σ.1.attach,
          (-1 : ℤ) ^ ((insert a σ.1).filter (· < v.1)).card •
            FreeAbelianGroup.of
              (Eq.mp (congrArg (SimplexAt K)
                (show n + 1 - 1 = n by omega))
                (cone_face_at K (n + 1)
                  (cone_insert_simplex K a ha n σ hna)
                  ⟨v.1, Finset.mem_insert_of_mem v.2⟩)) := by
  classical
  let τ := cone_insert_simplex K a ha n σ hna
  have hτ : τ.1 = insert a σ.1 := rfl
  have hn : n + 1 - 1 = n := by omega
  rw [cone_boundary_next_of, cone_faceBoundary_eq]
  rw [cone_cast_sum (F := chains K) hn]
  simp only [cone_cast_zsmul (F := chains K) hn]
  simp only [cone_cast_of (G := SimplexAt K) hn]
  let f : {x // x ∈ insert a σ.1} → chains K n := fun x =>
    (-1 : ℤ) ^ ((insert a σ.1).filter (· < x.1)).card •
      FreeAbelianGroup.of
        (Eq.mp (congrArg (SimplexAt K) hn)
          (cone_face_at K (n + 1) (cone_insert_simplex K a ha n σ hna) x))
  change (∑ x ∈ (insert a σ.1).attach, f x) = _
  rw [cone_sum_attach_insert σ.1 a hna f]
  have hfa : f ⟨a, Finset.mem_insert_self a σ.1⟩ =
      (-1 : ℤ) ^ (σ.1.filter (· < a)).card • FreeAbelianGroup.of σ := by
    have hval : Eq.mp (congrArg (SimplexAt K) hn)
        (cone_face_at K (n + 1) (cone_insert_simplex K a ha n σ hna)
          ⟨a, Finset.mem_insert_self a σ.1⟩) = σ :=
      cone_apex_face_eq K a ha n σ hna
    change (-1 : ℤ) ^ ((insert a σ.1).filter (· < a)).card •
      FreeAbelianGroup.of (Eq.mp (congrArg (SimplexAt K) hn)
        (cone_face_at K (n + 1) (cone_insert_simplex K a ha n σ hna)
          ⟨a, Finset.mem_insert_self a σ.1⟩)) = _
    rw [hval]
    rw [Finset.filter_insert]
    simp
  rw [hfa]
  rfl

private theorem cone_insert_boundary_formula [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (σ : SimplexAt K n) (hna : a ∉ σ.1) :
    cone_insert_prev K a ha n (boundary K n (FreeAbelianGroup.of σ)) =
      ∑ v ∈ σ.1.attach,
        ((-1 : ℤ) ^ (σ.1.filter (· < v.1)).card *
          (-1 : ℤ) ^ ((σ.1.erase v.1).filter (· < a)).card) •
          FreeAbelianGroup.of
            (Eq.mp (congrArg (SimplexAt K)
              (show n + 1 - 1 = n by omega))
              (cone_face_at K (n + 1)
                (cone_insert_simplex K a ha n σ hna)
                ⟨v.1, Finset.mem_insert_of_mem v.2⟩)) := by
  classical
  rw [cone_boundary_of, cone_faceBoundary_eq, map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_zsmul]
  have hnaface : a ∉ (cone_face_at K n σ v).1 := by
    simp [cone_face_at, Finset.mem_erase, hna]
  rw [cone_insert_prev_of_not_mem K a ha n _ hnaface, smul_smul]
  have hface := cone_other_face_eq K a ha n σ hna v
  rw [hface]
  rfl

private theorem cone_homology_of_homotopy [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (hcontract : ∀ n : ℤ, -1 ≤ n → ∀ c : chains K n,
      cone_boundary_next K n (cone_insert_chain K a ha n c) +
        cone_insert_prev K a ha n (boundary K n c) = c)
    (q : ℤ) (hq : -1 ≤ q) : Subsingleton (reducedHomology K q) := by
  have htop : (boundaries K q).comap (cycles K q).subtype = ⊤ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      change x.1 ∈ boundaries K q
      rw [cone_boundaries_eq_range]
      refine ⟨cone_insert_chain K a ha q x.1, ?_⟩
      have hz : boundary K q x.1 = 0 := x.2
      simpa [hz] using hcontract q hq x.1
  change Subsingleton ((cycles K q) ⧸
    ((boundaries K q).comap (cycles K q).subtype))
  rw [htop]
  exact QuotientAddGroup.subsingleton_quotient_top

private theorem cone_homotopy_generator [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (hn : -1 ≤ n) (σ : SimplexAt K n) :
    cone_boundary_next K n
        (cone_insert_chain K a ha n (FreeAbelianGroup.of σ)) +
      cone_insert_prev K a ha n
        (boundary K n (FreeAbelianGroup.of σ)) =
      FreeAbelianGroup.of σ := by
  classical
  rw [cone_insert_chain_of]
  by_cases ham : a ∈ σ.1
  · rw [cone_boundary_of, cone_faceBoundary_eq]
    simp only [ham, not_true_eq_false, dite_false, map_zero, zero_add]
    rw [map_sum]
    simp_rw [map_zsmul]
    rw [Finset.sum_eq_single (⟨a, ham⟩ : σ.1)]
    · have hna : a ∉ (cone_face_at K n σ ⟨a, ham⟩).1 := by
        simp [cone_face_at]
      rw [cone_insert_prev_of_not_mem K a ha n _ hna]
      have hcard : ((σ.1.erase a).filter (· < a)).card =
          (σ.1.filter (· < a)).card := by
        rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
        simp
      have hval : (Eq.mp (congrArg (SimplexAt K)
          (show n - 1 + 1 = n by omega))
            (cone_insert_simplex K a ha (n - 1)
              (cone_face_at K n σ ⟨a, ham⟩) hna)) = σ := by
        apply Subtype.ext
        have hc := cone_cast_simplex_val K
          (show n - 1 + 1 = n by omega)
          (cone_insert_simplex K a ha (n - 1)
            (cone_face_at K n σ ⟨a, ham⟩) hna)
        rw [hc]
        simp [cone_insert_simplex, cone_face_at, ham]
      rw [show (cone_face_at K n σ ⟨a, ham⟩).1 = σ.1.erase a by rfl,
        hcard, hval, smul_smul]
      simp [← pow_add]
    · intro v hv hneq
      have hva : v.1 ≠ a := by
        intro h
        exact hneq (Subtype.ext h)
      have hamface : a ∈ (cone_face_at K n σ v).1 := by
        simp [cone_face_at, Finset.mem_erase, hva.symm, ham]
      rw [cone_insert_prev_of_mem K a ha n _ hamface]
      simp
    · intro hnot
      exact False.elim (hnot (Finset.mem_attach _ _))
  · simp only [ham, not_false_eq_true, dite_true]
    rw [map_zsmul, cone_boundary_insert_formula K a ha n σ ham,
      cone_insert_boundary_formula K a ha n σ ham]
    rw [smul_add, Finset.smul_sum]
    simp_rw [smul_smul]
    have hsquare : (-1 : ℤ) ^ (σ.1.filter (· < a)).card *
        (-1 : ℤ) ^ (σ.1.filter (· < a)).card = 1 := by
      simp [← pow_add, pow_mul]
    rw [hsquare, one_smul]
    have hcancel : (∑ v ∈ σ.1.attach,
        ((-1 : ℤ) ^ (σ.1.filter (· < a)).card *
          (-1 : ℤ) ^ ((insert a σ.1).filter (· < v.1)).card) •
          FreeAbelianGroup.of
            (Eq.mp (congrArg (SimplexAt K)
              (show n + 1 - 1 = n by omega))
              (cone_face_at K (n + 1)
                (cone_insert_simplex K a ha n σ ham)
                ⟨v.1, Finset.mem_insert_of_mem v.2⟩))) +
        (∑ v ∈ σ.1.attach,
          ((-1 : ℤ) ^ (σ.1.filter (· < v.1)).card *
            (-1 : ℤ) ^ ((σ.1.erase v.1).filter (· < a)).card) •
            FreeAbelianGroup.of
              (Eq.mp (congrArg (SimplexAt K)
                (show n + 1 - 1 = n by omega))
                (cone_face_at K (n + 1)
                  (cone_insert_simplex K a ha n σ ham)
                  ⟨v.1, Finset.mem_insert_of_mem v.2⟩))) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro v hv
      rw [← add_smul]
      have hs := cone_sign_swap σ.1 a v.1 ham v.2
      rw [hs]
      simp
    rw [add_assoc, hcancel]
    simp

private theorem cone_homotopy [LinearOrder V] (K : FiniteComplex V)
    (a : V) (ha : ∀ σ : Finset V, σ ∈ K → insert a σ ∈ K)
    (n : ℤ) (hn : -1 ≤ n) (c : chains K n) :
    cone_boundary_next K n (cone_insert_chain K a ha n c) +
      cone_insert_prev K a ha n (boundary K n c) = c := by
  have hm :
      (cone_boundary_next K n).comp (cone_insert_chain K a ha n) +
        (cone_insert_prev K a ha n).comp (boundary K n) =
          AddMonoidHom.id (chains K n) := by
    apply FreeAbelianGroup.lift_ext
    intro σ
    exact cone_homotopy_generator K a ha n hn σ
  exact DFunLike.congr_fun hm c

theorem nonemptyCone_reducedHomology [LinearOrder V] (K : FiniteComplex V)
    (h : IsNonemptyCone K) (q : ℤ) (hq : -1 ≤ q) :
    Subsingleton (reducedHomology K q) := by
  obtain ⟨a, _, ha⟩ := h
  exact cone_homology_of_homotopy K a ha
    (fun n hn c => cone_homotopy K a ha n hn c) q hq

end CurveGenusTwo.Filtration

