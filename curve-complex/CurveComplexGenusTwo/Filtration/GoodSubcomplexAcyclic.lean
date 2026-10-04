import CurveComplexGenusTwo.Filtration.E1BridgeAssembly
import CurveComplexGenusTwo.Filtration.FinalAbutment
import CurveComplexGenusTwo.Filtration.PageDifferential


namespace CurveGenusTwo.Filtration

universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]

set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false

private theorem cast_equiv_apply_bridge {ι : Type*} {F G : ι → Type*}
    [∀ i, AddCommGroup (F i)] [∀ i, AddCommGroup (G i)]
    {i j : ι} (h : i = j) (e : (k : ι) → F k ≃+ G k) (x : F i) :
    Eq.mp (congrArg G h) (e i x) =
      e j (Eq.mp (congrArg F h) x) := by
  cases h
  rfl

private theorem cast_hom_apply_bridge_apply {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x =
      Eq.mp (congrArg F h) (f x) := by
  cases h
  rfl

private theorem cast_hom_range_bridge {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f).range =
      Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) f.range := by
  cases h
  rfl

noncomputable def signedQuotientRelativeHomologyEquiv
    (K : FiniteComplex V) (a : ArcLabels V B) (p : ℕ) (q : ℤ) :
    let n := (p : ℤ) + q
    let d := Signed.genericQuotientBoundary K a ((p : ℤ) - 1) p (by omega) n
    let u := Signed.genericQuotientBoundaryNextCast K a ((p : ℤ) - 1) p (by omega) n
    d.ker ⧸ (u.range.comap d.ker.subtype) ≃+ firstPage K a p q := by
  let n : ℤ := (p : ℤ) + q
  let d := Classical.choose (relativeQuotient_boundary K a p)
  let e := Classical.choose (Classical.choose_spec (relativeQuotient_boundary K a p))
  have hdesc : ∀ m : ℤ, ∀ c : chains (filtration K a p) m,
      d m (QuotientAddGroup.mk' _ c) =
        QuotientAddGroup.mk' _ (boundary (filtration K a p) m c) :=
    (Classical.choose_spec (Classical.choose_spec
      (relativeQuotient_boundary K a p))).1
  have hcompat : ∀ m : ℤ, ∀ c : relativeQuotient K a p m,
      e (m - 1) (d m c) = relativeBoundary K a p m (e m c) :=
    (Classical.choose_spec (Classical.choose_spec
      (relativeQuotient_boundary K a p))).2
  let DA := Signed.genericQuotientBoundary K a ((p : ℤ) - 1) p (by omega) n
  let UA := Signed.genericQuotientBoundaryNextCast K a ((p : ℤ) - 1) p (by omega) n
  let DB := relativeBoundary K a p n
  let UB : relativeChains K a p (n + 1) →+ relativeChains K a p n :=
    Eq.mp (congrArg (fun m : ℤ =>
      relativeChains K a p (n + 1) →+ relativeChains K a p m)
      (show n + 1 - 1 = n by omega)) (relativeBoundary K a p (n + 1))
  have hD (m : ℤ) :
      Signed.genericQuotientBoundary K a ((p : ℤ) - 1) p (by omega) m = d m := by
    apply AddMonoidHom.ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | _ c =>
      change Signed.genericQuotientBoundary K a ((p : ℤ) - 1) p (by omega) m
          (QuotientAddGroup.mk' _ c) = d m (QuotientAddGroup.mk' _ c)
      rw [hdesc m c]
      rfl
  have hd : ∀ x, e (n - 1) (DA x) = DB (e n x) := by
    intro x
    rw [show DA = d n from hD n]
    exact hcompat n x
  have hu : ∀ x, e n (UA x) = UB (e (n + 1) x) := by
    intro x
    have hn : n + 1 - 1 = n := by omega
    rw [Signed.genericQuotientBoundaryNextCast_apply]
    rw [← cast_equiv_apply_bridge hn e]
    rw [hD (n + 1), hcompat (n + 1) x]
    exact (cast_hom_apply_bridge_apply hn (relativeBoundary K a p (n + 1))
      (e (n + 1) x)).symm
  have hh := chainHomologyEquiv' DA UA DB UB
    (e (n - 1)) (e n) (e (n + 1)) hd hu
  have hrange : UB.range = relativeBoundaries K a p n := by
    unfold UB relativeBoundaries
    rw [cast_hom_range_bridge]
    omega
  rw [hrange] at hh
  change DA.ker ⧸ (UA.range.comap DA.ker.subtype) ≃+
    relativeHomology K a p n at hh
  exact hh

noncomputable def spectralPageFirstPageEquiv
    (K : FiniteComplex V) (a : ArcLabels V B) (p : ℕ) (q : ℤ) :
    spectralPageGroup K a 1 (p : ℤ) q ≃+ firstPage K a p q :=
  (signedAdjacentQuotientHomologyEquiv K a (p : ℤ) q).symm.trans
    (signedQuotientRelativeHomologyEquiv K a p q)

theorem spectralPage_firstPage_split
    (K : FiniteComplex V) (a : ArcLabels V B) (p : ℕ) (q : ℤ) :
    Nonempty (spectralPageGroup K a 1 (p : ℤ) q ≃+
      DirectSum (strata K a p)
        (fun S => reducedHomology (restrictedLink K a S) q)) := by
  obtain ⟨e⟩ := firstPage_split K a p q
  exact ⟨(spectralPageFirstPageEquiv K a p q).trans e⟩

theorem positive_spectralPage_vanishes
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hlinks : ∀ p : ℕ, 1 ≤ p → ∀ S : strata K a p, ∀ q : ℤ,
      -1 ≤ q → Subsingleton (reducedHomology (restrictedLink K a S) q))
    (p : ℕ) (hp : 1 ≤ p) (q : ℤ) (hq : -1 ≤ q) :
    Subsingleton (spectralPageGroup K a 1 (p : ℤ) q) := by
  obtain ⟨e⟩ := spectralPage_firstPage_split K a p q
  letI (S : strata K a p) : Subsingleton
      (reducedHomology (restrictedLink K a S) q) := hlinks p hp S q hq
  have hsum : Subsingleton
      (DirectSum (strata K a p) (fun S =>
        reducedHomology (restrictedLink K a S) q)) := inferInstance
  exact e.injective.subsingleton

end CurveGenusTwo.Filtration


namespace CurveGenusTwo.Filtration

universe u v
variable {V : Type u} {B : Type v} [DecidableEq V] [LinearOrder V]
set_option linter.style.haveILetI false

/-- A bundled version of the proved first-page decomposition. The source
statement and its augmentation conventions remain those of
`spectralPage_firstPage_split`. -/
noncomputable def spectralPage_firstPage_splitEquiv
    (K : FiniteComplex V) (a : ArcLabels V B) (p : ℕ) (q : ℤ) :
    spectralPageGroup K a 1 (p : ℤ) q ≃+
      DirectSum (strata K a p)
        (fun S => reducedHomology (restrictedLink K a S) q) :=
  Classical.choice (spectralPage_firstPage_split K a p q)

private theorem reducedHomology_subsingleton_of_lt_neg_one
    (L : FiniteComplex V) (q : ℤ) (hq : q < -1) :
    Subsingleton (reducedHomology L q) := by
  haveI : IsEmpty (SimplexAt L q) := ⟨by
    intro σ
    rcases σ.2.2 with h | h <;> omega⟩
  haveI : Subsingleton (chains L q) := inferInstance
  haveI : Subsingleton (cycles L q) := inferInstance
  constructor
  intro x y
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    induction y using QuotientAddGroup.induction_on with
    | _ y => exact congrArg (QuotientAddGroup.mk' _) (Subsingleton.elim x y)

private theorem spectralPage_subsingleton_all_rows_of_positive
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hlinks : ∀ p : ℕ, 1 ≤ p → ∀ S : strata K a p, ∀ q : ℤ,
      -1 ≤ q → Subsingleton (reducedHomology (restrictedLink K a S) q))
    (p : ℕ) (hp : 1 ≤ p) (q : ℤ) :
    Subsingleton (spectralPageGroup K a 1 (p : ℤ) q) := by
  by_cases hq : -1 ≤ q
  · exact positive_spectralPage_vanishes K a hlinks p hp q hq
  · letI (S : strata K a p) : Subsingleton
        (reducedHomology (restrictedLink K a S) q) :=
      reducedHomology_subsingleton_of_lt_neg_one _ q (by omega)
    have hsum : Subsingleton
        (DirectSum (strata K a p)
          (fun S => reducedHomology (restrictedLink K a S) q)) := inferInstance
    exact (spectralPage_firstPage_splitEquiv K a p q).injective.subsingleton

private theorem cycle_cast_null_reflect
    (K : FiniteComplex V) (a : ArcLabels V B) (p r : ℤ)
    {m n : ℤ} (h : m = n) (x : spectralCycles K a r p n)
    (hx : (cast (congrArg (fun j : ℤ => ↥(spectralCycles K a r p j)) h.symm) x).1 ∈
      spectralNullChains K a r p m) :
    x.1 ∈ spectralNullChains K a r p n := by
  cases h
  exact hx

/-- If a chain is a page-one cycle in a positive filtration column, its
boundary has a representative one filtration level lower. -/
private theorem lower_boundary_one
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hlinks : ∀ p : ℕ, 1 ≤ p → ∀ S : strata K a p, ∀ q : ℤ,
      -1 ≤ q → Subsingleton (reducedHomology (restrictedLink K a S) q))
    (p : ℕ) (hp : 1 ≤ p) (n : ℤ) (b : chains K n)
    (hb : b ∈ filteredChains K a p n)
    (hdb : boundary K n b ∈ filteredChains K a ((p : ℤ) - 1) (n - 1)) :
    ∃ c : chains K n, c ∈ filteredChains K a ((p : ℤ) - 1) n ∧
      boundary K n c = boundary K n b := by
  let q : ℤ := n - (p : ℤ)
  have hdeg : (p : ℤ) + q = n := by dsimp [q]; omega
  haveI := spectralPage_subsingleton_all_rows_of_positive K a hlinks p hp q
  have hcy : b ∈ spectralCycles K a 1 (p : ℤ) n := ⟨hb, hdb⟩
  let x : spectralCycles K a 1 (p : ℤ) ((p : ℤ) + q) :=
    cast (congrArg (fun j : ℤ => ↥(spectralCycles K a 1 (p : ℤ) j)) hdeg.symm)
      (⟨b, hcy⟩ : spectralCycles K a 1 (p : ℤ) n)
  have hxzero : (QuotientAddGroup.mk' _ x :
      spectralPageGroup K a 1 (p : ℤ) q) = 0 := Subsingleton.elim _ _
  have hxcomap : x ∈ (spectralNullChains K a 1 (p : ℤ) ((p : ℤ) + q)).comap
      (spectralCycles K a 1 (p : ℤ) ((p : ℤ) + q)).subtype :=
    (QuotientAddGroup.eq_zero_iff _).mp hxzero
  have hxnull : x.1 ∈ spectralNullChains K a 1 (p : ℤ) ((p : ℤ) + q) := hxcomap
  have hbnull : b ∈ spectralNullChains K a 1 (p : ℤ) n := by
    exact cycle_cast_null_reflect K a p 1 hdeg ⟨b, hcy⟩ hxnull
  obtain ⟨c, hc, z, heq⟩ :=
    (spectralNullChains_mem_iff K a 1 p n b).mp hbnull
  refine ⟨c, hc, ?_⟩
  have hz : boundary K n (boundaryNextCast K n z.1) = 0 := by
    apply spectralNullChainsCast_boundary_part_le_cycles K a 1 p n
    exact ⟨z, rfl⟩
  rw [← heq, map_add, hz, add_zero]

/-- Twelve applications of page-one vanishing move a bounding chain into the
zero filtration while keeping its boundary fixed. -/
private theorem lower_boundary_to_zero
    (K : FiniteComplex V) (a : ArcLabels V B)
    (hlinks : ∀ p : ℕ, 1 ≤ p → ∀ S : strata K a p, ∀ q : ℤ,
      -1 ≤ q → Subsingleton (reducedHomology (restrictedLink K a S) q))
    (p : ℕ) (hp : p ≤ 12) (n : ℤ) (b : chains K n)
    (hb : b ∈ filteredChains K a p n)
    (hdb : boundary K n b ∈ filteredChains K a 0 (n - 1)) :
    ∃ c : chains K n, c ∈ filteredChains K a 0 n ∧
      boundary K n c = boundary K n b := by
  induction p generalizing b with
  | zero => exact ⟨b, hb, rfl⟩
  | succ p ih =>
    have hdb' : boundary K n b ∈
        filteredChains K a (((p + 1 : ℕ) : ℤ) - 1) (n - 1) :=
      filteredChains_mono K a (by omega) (n - 1) hdb
    obtain ⟨c, hc, hbc⟩ :=
      lower_boundary_one K a hlinks (p + 1) (by omega) n b hb hdb'
    have hc' : c ∈ filteredChains K a p n := by
      simpa only [show (((p + 1 : ℕ) : ℤ) - 1) = (p : ℤ) by omega] using hc
    obtain ⟨d, hd, hcd⟩ := ih (by omega) c hc' (by rw [hbc]; exact hdb)
    exact ⟨d, hd, hcd.trans hbc⟩

omit [LinearOrder V] in
private theorem cast_mem_filtered_iff
    (K : FiniteComplex V) (a : ArcLabels V B) (p : ℤ)
    {m n : ℤ} (h : m = n) (x : chains K m) :
    (cast (congrArg (chains K) h) x ∈ filteredChains K a p n) ↔
      x ∈ filteredChains K a p m := by
  cases h
  rfl

private theorem boundaryNextCast_mem_filtered_iff
    (K : FiniteComplex V) (a : ArcLabels V B) (p q : ℤ)
    (b : chains K (q + 1)) :
    boundaryNextCast K q b ∈ filteredChains K a p q ↔
      boundary K (q + 1) b ∈ filteredChains K a p (q + 1 - 1) := by
  rw [boundaryNextCast_apply]
  have h : q + 1 - 1 = q := by omega
  exact cast_mem_filtered_iff K a p h (boundary K (q + 1) b)

private theorem boundaryNextCast_congr
    (K : FiniteComplex V) (q : ℤ) (b c : chains K (q + 1))
    (h : boundary K (q + 1) b = boundary K (q + 1) c) :
    boundaryNextCast K q b = boundaryNextCast K q c := by
  rw [boundaryNextCast_apply, boundaryNextCast_apply, h]

private theorem freeAbelian_lift_injective_acyclic {α β : Type*}
    (f : α → β) (hf : Function.Injective f) :
    Function.Injective (FreeAbelianGroup.lift
      (fun x : α => FreeAbelianGroup.of (f x))) := by
  classical
  by_cases hα : Nonempty α
  · let g : β → α := fun b =>
      if hb : ∃ a, f a = b then Classical.choose hb else Classical.choice hα
    have hgf : ∀ a : α, g (f a) = a := by
      intro a
      dsimp [g]
      rw [dite_eq_left ⟨a, rfl⟩]
      exact hf (Classical.choose_spec (show ∃ x, f x = f a from ⟨a, rfl⟩))
    let F : FreeAbelianGroup α →+ FreeAbelianGroup β :=
      FreeAbelianGroup.lift (fun a => FreeAbelianGroup.of (f a))
    let G : FreeAbelianGroup β →+ FreeAbelianGroup α :=
      FreeAbelianGroup.lift (fun b => FreeAbelianGroup.of (g b))
    have hcomp : G.comp F = AddMonoidHom.id (FreeAbelianGroup α) := by
      apply FreeAbelianGroup.lift_ext
      intro a
      change G (F (FreeAbelianGroup.of a)) = FreeAbelianGroup.of a
      simp only [F, G, FreeAbelianGroup.lift_apply_of, hgf]
    intro x y hxy
    change F x = F y at hxy
    calc
      x = (G.comp F) x := (congrArg (fun H => H x) hcomp).symm
      _ = (G.comp F) y := congrArg G hxy
      _ = y := congrArg (fun H => H y) hcomp
  · haveI : IsEmpty α := not_nonempty_iff.mp hα
    haveI : Subsingleton (FreeAbelianGroup α) := inferInstance
    intro x y _
    exact Subsingleton.elim x y

omit [DecidableEq V] [LinearOrder V] in
private theorem chainInclusion_injective_acyclic
    (A C : FiniteComplex V) (h : A.simplices ⊆ C.simplices) (n : ℤ) :
    Function.Injective (chainInclusion A C h n) := by
  let f : SimplexAt A n → SimplexAt C n :=
    fun σ => ⟨σ.1, h σ.2.1, σ.2.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : SimplexAt C n => z.1) hxy
  exact freeAbelian_lift_injective_acyclic f hf

/-- Acyclicity of the zero-filtration subcomplex follows by lowering every
ambient bounding chain through the finite filtration. -/
theorem goodSubcomplex_acyclic (K : FiniteComplex V) (a : ArcLabels V B)
    (hcard : ∀ σ : Finset V, σ ∈ K → σ.card ≤ 12)
    (hA : ∀ n : ℤ, -1 ≤ n → Subsingleton (reducedHomology K n))
    (hlinks : ∀ p : ℕ, 1 ≤ p → ∀ S : strata K a p, ∀ q : ℤ,
      -1 ≤ q → Subsingleton (reducedHomology (restrictedLink K a S) q)) :
    ∀ q : ℤ, -1 ≤ q → Subsingleton (reducedHomology (goodSubcomplex K a) q) := by
  intro q hq
  haveI := hA q hq
  constructor
  intro X Y
  have hclass : ∀ z : cycles (goodSubcomplex K a) q,
      (QuotientAddGroup.mk' _ z : reducedHomology (goodSubcomplex K a) q) = 0 := by
    intro z
    let i (m : ℤ) := chainInclusion (goodSubcomplex K a) K
      (by intro σ hσ; exact hσ.1) m
    let x : chains K q := i q z.1
    have hxcy : x ∈ cycles K q :=
      filteredCycle_inclusion_isCycle K a 0 q z.1 z.2
    have hxzero : (QuotientAddGroup.mk' _ (⟨x, hxcy⟩ : cycles K q) :
        reducedHomology K q) = 0 := Subsingleton.elim _ _
    have hxcomap : (⟨x, hxcy⟩ : cycles K q) ∈
        (boundaries K q).comap (cycles K q).subtype :=
      (QuotientAddGroup.eq_zero_iff _).mp hxzero
    have hxbound : x ∈ boundaries K q := hxcomap
    change x ∈ Eq.mp (congrArg (fun m : ℤ => AddSubgroup (chains K m))
      (show q + 1 - 1 = q by omega)) (boundary K (q + 1)).range at hxbound
    rw [← boundaryNextCast_range] at hxbound
    obtain ⟨b, hb⟩ := hxbound
    have hxbottom : x ∈ filteredChains K a 0 q := ⟨z.1, rfl⟩
    have hdb : boundary K (q + 1) b ∈
        filteredChains K a 0 (q + 1 - 1) :=
      (boundaryNextCast_mem_filtered_iff K a 0 q b).mp (by rw [hb]; exact hxbottom)
    have hbtop : b ∈ filteredChains K a 12 (q + 1) := by
      rw [filteredChains_top K a hcard]
      trivial
    obtain ⟨c, hc, hbc⟩ :=
      lower_boundary_to_zero K a hlinks 12 (by omega) (q + 1) b hbtop hdb
    obtain ⟨d, hd⟩ := hc
    have hii : i (q + 1) =
        chainInclusion (filtration K a 0) K
          (by intro σ hσ; exact hσ.1) (q + 1) := by
      apply FreeAbelianGroup.lift_ext
      intro σ
      rfl
    have hd' : i (q + 1) d = c := by
      rw [hii]
      exact hd
    have hdcast : i q (boundaryNextCast (goodSubcomplex K a) q d) = x := by
      calc
        i q (boundaryNextCast (goodSubcomplex K a) q d) =
            boundaryNextCast K q (i (q + 1) d) :=
          (filteredBoundary_inclusion_cast K a 0 q d).symm
        _ = boundaryNextCast K q c := congrArg (boundaryNextCast K q) hd'
        _ = boundaryNextCast K q b := boundaryNextCast_congr K q c b hbc
        _ = x := hb
    have hdx : boundaryNextCast (goodSubcomplex K a) q d = z.1 :=
      chainInclusion_injective_acyclic (goodSubcomplex K a) K
        (by intro σ hσ; exact hσ.1) q hdcast
    have hzbound : z.1 ∈ boundaries (goodSubcomplex K a) q := by
      change z.1 ∈ Eq.mp (congrArg (fun m : ℤ =>
        AddSubgroup (chains (goodSubcomplex K a) m))
        (show q + 1 - 1 = q by omega))
        (boundary (goodSubcomplex K a) (q + 1)).range
      rw [← boundaryNextCast_range]
      exact ⟨d, hdx⟩
    exact (QuotientAddGroup.eq_zero_iff _).2 hzbound
  induction X using QuotientAddGroup.induction_on with
  | _ x =>
    induction Y using QuotientAddGroup.induction_on with
    | _ y => exact (hclass x).trans (hclass y).symm

end CurveGenusTwo.Filtration

#print axioms CurveGenusTwo.Filtration.goodSubcomplex_acyclic
#print axioms CurveGenusTwo.Filtration.spectralPage_firstPage_splitEquiv
