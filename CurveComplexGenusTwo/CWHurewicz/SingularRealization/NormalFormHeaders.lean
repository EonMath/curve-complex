import CurveComplexGenusTwo.CWHurewicz.SingularRealization.GeometryHeaders
import Mathlib.Data.Finset.Sort
open CategoryTheory CategoryTheory.Limits Opposite Convexity Topology
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.SingularApproximation

/-- Actual-simplex normal-form support obligation; exact prototype in SupportProbes.lean. -/
theorem simplex_positive_face_representation (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
    ∃ (m : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (_ : Function.Injective f)
      (u : StdSimplex ℝ (Fin (m + 1))),
      (∀ i, 0 < u.weights i) ∧ StdSimplex.map f u = t := by
  classical
  let s := t.weights.support
  let m := s.card - 1
  have hs : 0 < s.card := Finset.card_pos.mpr t.support_weights_nonempty
  have hm : s.card = m + 1 := by dsimp [m]; omega
  let e : Fin (m + 1) ↪o Fin (n + 1) := s.orderEmbOfFin hm
  let f : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom e.toOrderHom
  have hf : Function.Injective f := e.injective
  have hr : Set.range f = (s : Set (Fin (n + 1))) := s.range_orderEmbOfFin hm
  have ht : t ∈ Set.range (StdSimplex.map f) := StdSimplex.mem_range_map_iff f t |>.mpr (by
    intro i hi
    rw [hr] at hi
    exact Finsupp.notMem_support_iff.mp hi)
  obtain ⟨u, hu⟩ := ht
  refine ⟨m, f, hf, u, ?_, hu⟩
  intro i
  have hi : f i ∈ t.weights.support := by
    exact s.orderEmbOfFin_mem hm i
  have hne : t.weights (f i) ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hpos : 0 < t.weights (f i) := lt_of_le_of_ne (t.weights_nonneg _) (Ne.symm hne)
  rw [← hu, StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective hf] at hpos
  exact hpos

/-- Actual-simplex normal-form support obligation; exact prototype in SupportProbes.lean. -/
theorem simplex_surjective_map_positive {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (hf : Function.Surjective f)
    (u : StdSimplex ℝ α) (hu : ∀ i, 0 < u.weights i) :
    ∀ j, 0 < (StdSimplex.map f u).weights j := by
  classical
  intro j
  have hj : j ∈ (StdSimplex.map f u).weights.support := by
    rw [StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg u.nonneg]
    obtain ⟨i, rfl⟩ := hf j
    exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr (ne_of_gt (hu i)), rfl⟩
  exact lt_of_le_of_ne ((StdSimplex.map f u).weights_nonneg j)
    (Ne.symm (Finsupp.mem_support_iff.mp hj))

/-- Actual-simplex normal-form support obligation; exact prototype in SupportProbes.lean. -/
theorem simplex_positive_faces_same_dim_unique (n m : ℕ) (f g : ⦋m⦌ ⟶ ⦋n⦌)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (u v : StdSimplex ℝ (Fin (m + 1)))
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
    (he : StdSimplex.map f u = StdSimplex.map g v) : f = g ∧ u = v := by
  classical
  have hsu : u.weights.support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, ne_of_gt (hu i)]
  have hsv : v.weights.support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, ne_of_gt (hv i)]
  have hs := congrArg (fun w : StdSimplex ℝ (Fin (n + 1)) => w.weights.support) he
  simp only [StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg u.nonneg,
    Finsupp.support_mapDomain_of_nonneg v.nonneg, hsu, hsv] at hs
  have hr : Set.range f = Set.range g := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using congrArg
      (fun q : Finset (Fin (n + 1)) => (q : Set (Fin (n + 1)))) hs
  have hmonoF : StrictMono f := f.toOrderHom.monotone.strictMono_of_injective hf
  have hmonoG : StrictMono g := g.toOrderHom.monotone.strictMono_of_injective hg
  have hfg : f = g := by
    apply ConcreteCategory.ext
    ext i
    exact congrArg Fin.val (congrFun (hmonoF.eq_of_range_eq hmonoG hr) i)
  refine ⟨hfg, ?_⟩
  rw [← hfg] at he
  apply StdSimplex.ext
  exact Finsupp.mapDomain_injective hf (congrArg StdSimplex.weights he)

/-- Actual-simplex normal-form support obligation; exact prototype in SupportProbes.lean. -/
theorem simplex_nondegenerate_weighted_decomposition_unique (S : SSet.{0}) (l n m : ℕ) (s : S _⦋l⦌)
    (f : ⦋l⦌ ⟶ ⦋n⦌) (g : ⦋l⦌ ⟶ ⦋m⦌) [Epi f] [Epi g]
    (y : S.nonDegenerate n) (z : S.nonDegenerate m)
    (hf : s = S.map f.op y.val) (hg : s = S.map g.op z.val)
    (t : StdSimplex ℝ (Fin (l + 1))) :
    (⟨n, y, StdSimplex.map f t⟩ : Σ k : ℕ, S.nonDegenerate k × StdSimplex ℝ (Fin (k + 1))) =
      ⟨m, z, StdSimplex.map g t⟩ := by
  have hnm := S.unique_nonDegenerate_dim s f y hf g z hg
  subst m
  have hyz := S.unique_nonDegenerate_simplex s f y hf g z hg
  have hfg := S.unique_nonDegenerate_map s f y hf g z hg
  subst z
  subst g
  rfl

/-- Actual-simplex normal-form support obligation; exact prototype in FaceFactorProbes.lean. -/
theorem simplex_support_face_factorization (n p m k : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌)
    (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋p⦌)
    (hg : Function.Injective g)
    (u : StdSimplex ℝ (Fin (m + 1))) (v : StdSimplex ℝ (Fin (k + 1)))
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
    (he : StdSimplex.map a (StdSimplex.map f u) = StdSimplex.map g v) :
    ∃ (b : ⦋m⦌ ⟶ ⦋k⦌), Function.Surjective b ∧ f ≫ a = b ≫ g ∧
      StdSimplex.map b u = v := by
  classical
  have hsu : u.weights.support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, ne_of_gt (hu i)]
  have hsv : v.weights.support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, ne_of_gt (hv i)]
  rw [StdSimplex.map_map] at he
  have hs := congrArg (fun w : StdSimplex ℝ (Fin (p + 1)) => w.weights.support) he
  simp only [StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg u.nonneg,
    Finsupp.support_mapDomain_of_nonneg v.nonneg, hsu, hsv] at hs
  have hr : Set.range (fun i : Fin (m + 1) => a (f i)) = Set.range g := by
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using congrArg
      (fun q : Finset (Fin (p + 1)) => (q : Set (Fin (p + 1)))) hs
  let β : Fin (m + 1) → Fin (k + 1) := fun i => Function.invFun g (a (f i))
  have hβ (i : Fin (m + 1)) : g (β i) = a (f i) := by
    have hi : a (f i) ∈ Set.range g := hr ▸ Set.mem_range_self i
    obtain ⟨j, hj⟩ := hi
    dsimp [β]
    rw [← hj, Function.leftInverse_invFun hg j]
  have hmonoG : StrictMono g := g.toOrderHom.monotone.strictMono_of_injective hg
  let b : ⦋m⦌ ⟶ ⦋k⦌ := SimplexCategory.mkHom {
    toFun := β
    monotone' := by
      intro i j hij
      apply hmonoG.le_iff_le.mp
      rw [hβ i, hβ j]
      exact a.toOrderHom.monotone (f.toOrderHom.monotone hij) }
  have hb : Function.Surjective b := by
    intro j
    have hj : g j ∈ Set.range (fun i : Fin (m + 1) => a (f i)) := hr.symm ▸ Set.mem_range_self j
    obtain ⟨i, hi⟩ := hj
    exact ⟨i, hg ((hβ i).trans hi)⟩
  have hfac : f ≫ a = b ≫ g := by
    apply ConcreteCategory.ext
    ext i
    exact congrArg Fin.val (hβ i).symm
  refine ⟨b, hb, hfac, ?_⟩
  apply StdSimplex.ext
  apply Finsupp.mapDomain_injective hg
  change (StdSimplex.map g (StdSimplex.map b u)).weights = (StdSimplex.map g v).weights
  rw [StdSimplex.map_map]
  have hfun : (fun i => g (b i)) = (fun i => a (f i)) := funext hβ
  rw [hfun, he]

/-- Actual-simplex normal-form support obligation; exact prototype in NormalizationStepProbes.lean. -/
theorem simplex_normalization_step (S : SSet.{0}) (n p m k r q : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌)
    (s : S _⦋p⦌) (t : StdSimplex ℝ (Fin (n + 1)))
    (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋p⦌) (hg : Function.Injective g)
    (u : StdSimplex ℝ (Fin (m + 1))) (v : StdSimplex ℝ (Fin (k + 1)))
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
    (hfu : StdSimplex.map f u = t) (hgv : StdSimplex.map g v = StdSimplex.map a t)
    (α : ⦋m⦌ ⟶ ⦋r⦌) (β : ⦋k⦌ ⟶ ⦋q⦌) [Epi α] [Epi β]
    (y : S.nonDegenerate r) (z : S.nonDegenerate q)
    (hα : S.map f.op (S.map a.op s) = S.map α.op y.val)
    (hβ : S.map g.op s = S.map β.op z.val) :
    (⟨r, y, StdSimplex.map α u⟩ : Σ l : ℕ, S.nonDegenerate l × StdSimplex ℝ (Fin (l + 1))) =
      ⟨q, z, StdSimplex.map β v⟩ := by
  have hfactor (n p m k : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌)
      (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋p⦌) (hg : Function.Injective g)
      (u : StdSimplex ℝ (Fin (m + 1))) (v : StdSimplex ℝ (Fin (k + 1)))
      (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
      (he : StdSimplex.map a (StdSimplex.map f u) = StdSimplex.map g v) :
      ∃ (b : ⦋m⦌ ⟶ ⦋k⦌), Function.Surjective b ∧ f ≫ a = b ≫ g ∧
        StdSimplex.map b u = v := by
    classical
    have hsu : u.weights.support = Finset.univ := by
      ext i
      simp [Finsupp.mem_support_iff, ne_of_gt (hu i)]
    have hsv : v.weights.support = Finset.univ := by
      ext i
      simp [Finsupp.mem_support_iff, ne_of_gt (hv i)]
    rw [StdSimplex.map_map] at he
    have hs := congrArg (fun w : StdSimplex ℝ (Fin (p + 1)) => w.weights.support) he
    simp only [StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg u.nonneg,
      Finsupp.support_mapDomain_of_nonneg v.nonneg, hsu, hsv] at hs
    have hr : Set.range (fun i : Fin (m + 1) => a (f i)) = Set.range g := by
      simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using congrArg
        (fun q : Finset (Fin (p + 1)) => (q : Set (Fin (p + 1)))) hs
    let β : Fin (m + 1) → Fin (k + 1) := fun i => Function.invFun g (a (f i))
    have hβ (i : Fin (m + 1)) : g (β i) = a (f i) := by
      have hi : a (f i) ∈ Set.range g := hr ▸ Set.mem_range_self i
      obtain ⟨j, hj⟩ := hi
      dsimp [β]
      rw [← hj, Function.leftInverse_invFun hg j]
    have hmonoG : StrictMono g := g.toOrderHom.monotone.strictMono_of_injective hg
    let b : ⦋m⦌ ⟶ ⦋k⦌ := SimplexCategory.mkHom {
      toFun := β
      monotone' := by
        intro i j hij
        apply hmonoG.le_iff_le.mp
        rw [hβ i, hβ j]
        exact a.toOrderHom.monotone (f.toOrderHom.monotone hij) }
    have hb : Function.Surjective b := by
      intro j
      have hj : g j ∈ Set.range (fun i : Fin (m + 1) => a (f i)) := hr.symm ▸ Set.mem_range_self j
      obtain ⟨i, hi⟩ := hj
      exact ⟨i, hg ((hβ i).trans hi)⟩
    have hfac : f ≫ a = b ≫ g := by
      apply ConcreteCategory.ext
      ext i
      exact congrArg Fin.val (hβ i).symm
    refine ⟨b, hb, hfac, ?_⟩
    apply StdSimplex.ext
    apply Finsupp.mapDomain_injective hg
    change (StdSimplex.map g (StdSimplex.map b u)).weights = (StdSimplex.map g v).weights
    rw [StdSimplex.map_map]
    have hfun : (fun i => g (b i)) = (fun i => a (f i)) := funext hβ
    rw [hfun, he]
  obtain ⟨b, hb, hfac, hmap⟩ := hfactor n p m k a f g hg u v hu hv (by rw [hfu, hgv])
  let : Epi b := SimplexCategory.epi_iff_surjective.mpr hb
  have hx : S.map f.op (S.map a.op s) = S.map (b ≫ β).op z.val := by
    rw [← comp_apply, ← S.map_comp, ← op_comp, hfac, op_comp, S.map_comp, comp_apply,
      hβ, ← comp_apply, ← S.map_comp, ← op_comp]
  have hdim := S.unique_nonDegenerate_dim (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
  subst q
  have hyz := S.unique_nonDegenerate_simplex (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
  have heq := S.unique_nonDegenerate_map (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
  subst z
  have hcomp : StdSimplex.map (b ≫ β) u =
      StdSimplex.map β (StdSimplex.map b u) := StdSimplex.map_comp u b β
  simp only [heq, hcomp, hmap]

/-- Actual-simplex normal-form support obligation; exact prototype in InvariantNFProbes.lean. -/
theorem simplex_compatible_normalizer_exists (S : SSet.{0}) :
    ∃ ν : (n : ℕ) → S _⦋n⦌ → StdSimplex ℝ (Fin (n + 1)) →
        (Σ k : ℕ, S.nonDegenerate k × StdSimplex ℝ (Fin (k + 1))),
      (∀ (n p : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌) (s : S _⦋p⦌)
        (t : StdSimplex ℝ (Fin (n + 1))), ν n (S.map a.op s) t = ν p s (StdSimplex.map a t)) ∧
      (∀ (n : ℕ) (y : S.nonDegenerate n) (t : StdSimplex ℝ (Fin (n + 1))),
        (∀ i, 0 < t.weights i) → ν n y.val t = ⟨n, y, t⟩) := by
  classical
  have hsupport (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
      ∃ (m : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (_ : Function.Injective f)
        (u : StdSimplex ℝ (Fin (m + 1))),
        (∀ i, 0 < u.weights i) ∧ StdSimplex.map f u = t := by
    classical
    let s := t.weights.support
    let m := s.card - 1
    have hs : 0 < s.card := Finset.card_pos.mpr t.support_weights_nonempty
    have hm : s.card = m + 1 := by dsimp [m]; omega
    let e : Fin (m + 1) ↪o Fin (n + 1) := s.orderEmbOfFin hm
    let f : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom e.toOrderHom
    have hf : Function.Injective f := e.injective
    have hr : Set.range f = (s : Set (Fin (n + 1))) := s.range_orderEmbOfFin hm
    have ht : t ∈ Set.range (StdSimplex.map f) := StdSimplex.mem_range_map_iff f t |>.mpr (by
      intro i hi
      rw [hr] at hi
      exact Finsupp.notMem_support_iff.mp hi)
    obtain ⟨u, hu⟩ := ht
    refine ⟨m, f, hf, u, ?_, hu⟩
    intro i
    have hi : f i ∈ t.weights.support := by
      exact s.orderEmbOfFin_mem hm i
    have hne : t.weights (f i) ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hpos : 0 < t.weights (f i) := lt_of_le_of_ne (t.weights_nonneg _) (Ne.symm hne)
    rw [← hu, StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective hf] at hpos
    exact hpos
  have hnorm (S : SSet.{0}) (n p m k r q : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌)
    (s : S _⦋p⦌) (t : StdSimplex ℝ (Fin (n + 1)))
    (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋p⦌) (hg : Function.Injective g)
    (u : StdSimplex ℝ (Fin (m + 1))) (v : StdSimplex ℝ (Fin (k + 1)))
    (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
    (hfu : StdSimplex.map f u = t) (hgv : StdSimplex.map g v = StdSimplex.map a t)
    (α : ⦋m⦌ ⟶ ⦋r⦌) (β : ⦋k⦌ ⟶ ⦋q⦌) [Epi α] [Epi β]
    (y : S.nonDegenerate r) (z : S.nonDegenerate q)
    (hα : S.map f.op (S.map a.op s) = S.map α.op y.val)
    (hβ : S.map g.op s = S.map β.op z.val) :
    (⟨r, y, StdSimplex.map α u⟩ : Σ l : ℕ, S.nonDegenerate l × StdSimplex ℝ (Fin (l + 1))) =
      ⟨q, z, StdSimplex.map β v⟩ := by
    have hfactor (n p m k : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌)
        (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋p⦌) (hg : Function.Injective g)
        (u : StdSimplex ℝ (Fin (m + 1))) (v : StdSimplex ℝ (Fin (k + 1)))
        (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
        (he : StdSimplex.map a (StdSimplex.map f u) = StdSimplex.map g v) :
        ∃ (b : ⦋m⦌ ⟶ ⦋k⦌), Function.Surjective b ∧ f ≫ a = b ≫ g ∧
          StdSimplex.map b u = v := by
      classical
      have hsu : u.weights.support = Finset.univ := by
        ext i
        simp [Finsupp.mem_support_iff, ne_of_gt (hu i)]
      have hsv : v.weights.support = Finset.univ := by
        ext i
        simp [Finsupp.mem_support_iff, ne_of_gt (hv i)]
      rw [StdSimplex.map_map] at he
      have hs := congrArg (fun w : StdSimplex ℝ (Fin (p + 1)) => w.weights.support) he
      simp only [StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg u.nonneg,
        Finsupp.support_mapDomain_of_nonneg v.nonneg, hsu, hsv] at hs
      have hr : Set.range (fun i : Fin (m + 1) => a (f i)) = Set.range g := by
        simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using congrArg
          (fun q : Finset (Fin (p + 1)) => (q : Set (Fin (p + 1)))) hs
      let β : Fin (m + 1) → Fin (k + 1) := fun i => Function.invFun g (a (f i))
      have hβ (i : Fin (m + 1)) : g (β i) = a (f i) := by
        have hi : a (f i) ∈ Set.range g := hr ▸ Set.mem_range_self i
        obtain ⟨j, hj⟩ := hi
        dsimp [β]
        rw [← hj, Function.leftInverse_invFun hg j]
      have hmonoG : StrictMono g := g.toOrderHom.monotone.strictMono_of_injective hg
      let b : ⦋m⦌ ⟶ ⦋k⦌ := SimplexCategory.mkHom {
        toFun := β
        monotone' := by
          intro i j hij
          apply hmonoG.le_iff_le.mp
          rw [hβ i, hβ j]
          exact a.toOrderHom.monotone (f.toOrderHom.monotone hij) }
      have hb : Function.Surjective b := by
        intro j
        have hj : g j ∈ Set.range (fun i : Fin (m + 1) => a (f i)) := hr.symm ▸ Set.mem_range_self j
        obtain ⟨i, hi⟩ := hj
        exact ⟨i, hg ((hβ i).trans hi)⟩
      have hfac : f ≫ a = b ≫ g := by
        apply ConcreteCategory.ext
        ext i
        exact congrArg Fin.val (hβ i).symm
      refine ⟨b, hb, hfac, ?_⟩
      apply StdSimplex.ext
      apply Finsupp.mapDomain_injective hg
      change (StdSimplex.map g (StdSimplex.map b u)).weights = (StdSimplex.map g v).weights
      rw [StdSimplex.map_map]
      have hfun : (fun i => g (b i)) = (fun i => a (f i)) := funext hβ
      rw [hfun, he]
    obtain ⟨b, hb, hfac, hmap⟩ := hfactor n p m k a f g hg u v hu hv (by rw [hfu, hgv])
    let : Epi b := SimplexCategory.epi_iff_surjective.mpr hb
    have hx : S.map f.op (S.map a.op s) = S.map (b ≫ β).op z.val := by
      rw [← comp_apply, ← S.map_comp, ← op_comp, hfac, op_comp, S.map_comp, comp_apply,
        hβ, ← comp_apply, ← S.map_comp, ← op_comp]
    have hdim := S.unique_nonDegenerate_dim (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
    subst q
    have hyz := S.unique_nonDegenerate_simplex (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
    have heq := S.unique_nonDegenerate_map (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
    subst z
    have hcomp : StdSimplex.map (b ≫ β) u =
        StdSimplex.map β (StdSimplex.map b u) := StdSimplex.map_comp u b β
    simp only [heq, hcomp, hmap]
  have hdata (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
      ∃ d : (Σ m : ℕ, (⦋m⦌ ⟶ ⦋n⦌) × StdSimplex ℝ (Fin (m + 1))),
        Function.Injective d.2.1 ∧ (∀ i, 0 < d.2.2.weights i) ∧ StdSimplex.map d.2.1 d.2.2 = t := by
    obtain ⟨m, f, hf, u, hu, he⟩ := hsupport n t
    exact ⟨⟨m, f, u⟩, hf, hu, he⟩
  let D (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) := (hdata n t).choose
  have hD (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) := (hdata n t).choose_spec
  have hnd (n : ℕ) (s : S _⦋n⦌) :
      ∃ e : (Σ k : ℕ, (⦋n⦌ ⟶ ⦋k⦌) × S.nonDegenerate k),
        Epi e.2.1 ∧ s = S.map e.2.1.op e.2.2.val := by
    obtain ⟨k, a, ha, y, he⟩ := S.exists_nonDegenerate s
    exact ⟨⟨k, a, y⟩, ha, he⟩
  let A (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :=
    (hnd (D n t).1 (S.map (D n t).2.1.op s)).choose
  have hA (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :=
    (hnd (D n t).1 (S.map (D n t).2.1.op s)).choose_spec
  let ν (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :
      (Σ k : ℕ, S.nonDegenerate k × StdSimplex ℝ (Fin (k + 1))) :=
    ⟨(A n s t).1, (A n s t).2.2, StdSimplex.map (A n s t).2.1 (D n t).2.2⟩
  refine ⟨ν, ?_, ?_⟩
  · intro n p a s t
    let : Epi (A n (S.map a.op s) t).2.1 := (hA n (S.map a.op s) t).1
    let : Epi (A p s (StdSimplex.map a t)).2.1 := (hA p s (StdSimplex.map a t)).1
    exact hnorm S n p (D n t).1 (D p (StdSimplex.map a t)).1
      (A n (S.map a.op s) t).1 (A p s (StdSimplex.map a t)).1 a s t
      (D n t).2.1 (D p (StdSimplex.map a t)).2.1
      (hD p (StdSimplex.map a t)).1 (D n t).2.2 (D p (StdSimplex.map a t)).2.2
      (hD n t).2.1 (hD p (StdSimplex.map a t)).2.1
      (hD n t).2.2 (hD p (StdSimplex.map a t)).2.2
      (A n (S.map a.op s) t).2.1 (A p s (StdSimplex.map a t)).2.1
      (A n (S.map a.op s) t).2.2 (A p s (StdSimplex.map a t)).2.2
      (hA n (S.map a.op s) t).2 (hA p s (StdSimplex.map a t)).2
  · intro n y t ht
    let : Epi (A n y.val t).2.1 := (hA n y.val t).1
    have H := hnorm S n n (D n t).1 n (A n y.val t).1 n (𝟙 _) y.val t
      (D n t).2.1 (𝟙 _) (by simpa using Function.injective_id)
      (D n t).2.2 t (hD n t).2.1 ht (hD n t).2.2 (by simp)
      (A n y.val t).2.1 (𝟙 _) (A n y.val t).2.2 y
      (by simpa using (hA n y.val t).2) (by simp)
    change ν n y.val t = ⟨n, y, StdSimplex.map id t⟩ at H
    simpa only [StdSimplex.map_id] using H

/-- Actual-simplex normal-form support obligation; exact prototype in PositiveRepresentationProbes.lean. -/
theorem realization_positive_nondegenerate_representation (S : SSet.{0}) (x : SSet.toTop.obj S) :
    ∃ (n : ℕ) (s : S.nonDegenerate n) (t : StdSimplex ℝ (Fin (n + 1))),
      (∀ i, 0 < t.weights i) ∧
      SSet.toTop.map (SSet.yonedaEquiv.symm s.val) (⦋n⦌.toTopHomeo.symm t) = x := by
  have hsupport (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
      ∃ (m : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (_ : Function.Injective f)
        (u : StdSimplex ℝ (Fin (m + 1))),
        (∀ i, 0 < u.weights i) ∧ StdSimplex.map f u = t := by
    classical
    let s := t.weights.support
    let m := s.card - 1
    have hs : 0 < s.card := Finset.card_pos.mpr t.support_weights_nonempty
    have hm : s.card = m + 1 := by dsimp [m]; omega
    let e : Fin (m + 1) ↪o Fin (n + 1) := s.orderEmbOfFin hm
    let f : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom e.toOrderHom
    have hf : Function.Injective f := e.injective
    have hr : Set.range f = (s : Set (Fin (n + 1))) := s.range_orderEmbOfFin hm
    have ht : t ∈ Set.range (StdSimplex.map f) := StdSimplex.mem_range_map_iff f t |>.mpr (by
      intro i hi
      rw [hr] at hi
      exact Finsupp.notMem_support_iff.mp hi)
    obtain ⟨u, hu⟩ := ht
    refine ⟨m, f, hf, u, ?_, hu⟩
    intro i
    have hi : f i ∈ t.weights.support := by
      exact s.orderEmbOfFin_mem hm i
    have hne : t.weights (f i) ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hpos : 0 < t.weights (f i) := lt_of_le_of_ne (t.weights_nonneg _) (Ne.symm hne)
    rw [← hu, StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective hf] at hpos
    exact hpos
  have hpositive {α β : Type} [Fintype α] [Fintype β] (f : α → β)
      (hf : Function.Surjective f) (u : StdSimplex ℝ α) (hu : ∀ i, 0 < u.weights i) :
      ∀ j, 0 < (StdSimplex.map f u).weights j := by
    classical
    intro j
    have hj : j ∈ (StdSimplex.map f u).weights.support := by
      rw [StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg u.nonneg]
      obtain ⟨i, rfl⟩ := hf j
      exact Finset.mem_image.mpr ⟨i, Finsupp.mem_support_iff.mpr (ne_of_gt (hu i)), rfl⟩
    exact lt_of_le_of_ne ((StdSimplex.map f u).weights_nonneg j)
      (Ne.symm (Finsupp.mem_support_iff.mp hj))
  obtain ⟨n, s, t, ht⟩ :=
    CurveComplexGenusTwo.CWHurewicz.SingularApproximation.realization_simplex_representation S x
  obtain ⟨m, f, hf, u, hu, hmap⟩ := hsupport n.len (n.toTopHomeo t)
  let s' : S _⦋m⦌ := S.map f.op s
  obtain ⟨k, g, hg, y, hy⟩ := S.exists_nonDegenerate s'
  have hsf : SSet.yonedaEquiv.symm s' =
      SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm s :=
    uliftYonedaEquiv_symm_map f.op s
  have hsg : SSet.yonedaEquiv.symm s' =
      SSet.stdSimplex.map g ≫ SSet.yonedaEquiv.symm y.val := by
    rw [hy]
    exact uliftYonedaEquiv_symm_map g.op y.val
  refine ⟨k, y, StdSimplex.map g u,
    hpositive (α := Fin (m + 1)) (β := Fin (k + 1)) g (SimplexCategory.epi_iff_surjective.mp hg) u hu, ?_⟩
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply]
  change (SSet.toTop.map (SSet.stdSimplex.map g) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm y.val)) (⦋m⦌.toTopHomeo.symm u) = x
  rw [← SSet.toTop.map_comp, ← hsg, hsf, SSet.toTop.map_comp]
  change SSet.toTop.map (SSet.yonedaEquiv.symm s)
    (SSet.toTop.map (SSet.stdSimplex.map f) (⦋m⦌.toTopHomeo.symm u)) = x
  rw [← SimplexCategory.toTopHomeo_symm_naturality_apply, hmap,
    Homeomorph.symm_apply_apply]
  exact ht

/-- Actual-simplex normal-form support obligation; exact prototype in InteriorInjectionProbes.lean. -/
theorem realization_nondegenerate_interiors_injective (S : SSet.{0}) :
    Function.Injective
      (fun z : (Σ ns : (Σ n : ℕ, S.nonDegenerate n),
          {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =>
        SSet.toTop.map (SSet.yonedaEquiv.symm z.1.2.val) (⦋z.1.1⦌.toTopHomeo.symm z.2.val)) := by
  have hnormalizer (S : SSet.{0}) :
    ∃ ν : (n : ℕ) → S _⦋n⦌ → StdSimplex ℝ (Fin (n + 1)) →
        (Σ k : ℕ, S.nonDegenerate k × StdSimplex ℝ (Fin (k + 1))),
      (∀ (n p : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌) (s : S _⦋p⦌)
        (t : StdSimplex ℝ (Fin (n + 1))), ν n (S.map a.op s) t = ν p s (StdSimplex.map a t)) ∧
      (∀ (n : ℕ) (y : S.nonDegenerate n) (t : StdSimplex ℝ (Fin (n + 1))),
        (∀ i, 0 < t.weights i) → ν n y.val t = ⟨n, y, t⟩) := by
    classical
    have hsupport (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
        ∃ (m : ℕ) (f : ⦋m⦌ ⟶ ⦋n⦌) (_ : Function.Injective f)
          (u : StdSimplex ℝ (Fin (m + 1))),
          (∀ i, 0 < u.weights i) ∧ StdSimplex.map f u = t := by
      classical
      let s := t.weights.support
      let m := s.card - 1
      have hs : 0 < s.card := Finset.card_pos.mpr t.support_weights_nonempty
      have hm : s.card = m + 1 := by dsimp [m]; omega
      let e : Fin (m + 1) ↪o Fin (n + 1) := s.orderEmbOfFin hm
      let f : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom e.toOrderHom
      have hf : Function.Injective f := e.injective
      have hr : Set.range f = (s : Set (Fin (n + 1))) := s.range_orderEmbOfFin hm
      have ht : t ∈ Set.range (StdSimplex.map f) := StdSimplex.mem_range_map_iff f t |>.mpr (by
        intro i hi
        rw [hr] at hi
        exact Finsupp.notMem_support_iff.mp hi)
      obtain ⟨u, hu⟩ := ht
      refine ⟨m, f, hf, u, ?_, hu⟩
      intro i
      have hi : f i ∈ t.weights.support := by
        exact s.orderEmbOfFin_mem hm i
      have hne : t.weights (f i) ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hpos : 0 < t.weights (f i) := lt_of_le_of_ne (t.weights_nonneg _) (Ne.symm hne)
      rw [← hu, StdSimplex.weights_map, Finsupp.mapDomain_apply_of_injective hf] at hpos
      exact hpos
    have hnorm (S : SSet.{0}) (n p m k r q : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌)
      (s : S _⦋p⦌) (t : StdSimplex ℝ (Fin (n + 1)))
      (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋p⦌) (hg : Function.Injective g)
      (u : StdSimplex ℝ (Fin (m + 1))) (v : StdSimplex ℝ (Fin (k + 1)))
      (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
      (hfu : StdSimplex.map f u = t) (hgv : StdSimplex.map g v = StdSimplex.map a t)
      (α : ⦋m⦌ ⟶ ⦋r⦌) (β : ⦋k⦌ ⟶ ⦋q⦌) [Epi α] [Epi β]
      (y : S.nonDegenerate r) (z : S.nonDegenerate q)
      (hα : S.map f.op (S.map a.op s) = S.map α.op y.val)
      (hβ : S.map g.op s = S.map β.op z.val) :
      (⟨r, y, StdSimplex.map α u⟩ : Σ l : ℕ, S.nonDegenerate l × StdSimplex ℝ (Fin (l + 1))) =
        ⟨q, z, StdSimplex.map β v⟩ := by
      have hfactor (n p m k : ℕ) (a : ⦋n⦌ ⟶ ⦋p⦌)
          (f : ⦋m⦌ ⟶ ⦋n⦌) (g : ⦋k⦌ ⟶ ⦋p⦌) (hg : Function.Injective g)
          (u : StdSimplex ℝ (Fin (m + 1))) (v : StdSimplex ℝ (Fin (k + 1)))
          (hu : ∀ i, 0 < u.weights i) (hv : ∀ i, 0 < v.weights i)
          (he : StdSimplex.map a (StdSimplex.map f u) = StdSimplex.map g v) :
          ∃ (b : ⦋m⦌ ⟶ ⦋k⦌), Function.Surjective b ∧ f ≫ a = b ≫ g ∧
            StdSimplex.map b u = v := by
        classical
        have hsu : u.weights.support = Finset.univ := by
          ext i
          simp [Finsupp.mem_support_iff, ne_of_gt (hu i)]
        have hsv : v.weights.support = Finset.univ := by
          ext i
          simp [Finsupp.mem_support_iff, ne_of_gt (hv i)]
        rw [StdSimplex.map_map] at he
        have hs := congrArg (fun w : StdSimplex ℝ (Fin (p + 1)) => w.weights.support) he
        simp only [StdSimplex.weights_map, Finsupp.support_mapDomain_of_nonneg u.nonneg,
          Finsupp.support_mapDomain_of_nonneg v.nonneg, hsu, hsv] at hs
        have hr : Set.range (fun i : Fin (m + 1) => a (f i)) = Set.range g := by
          simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using congrArg
            (fun q : Finset (Fin (p + 1)) => (q : Set (Fin (p + 1)))) hs
        let β : Fin (m + 1) → Fin (k + 1) := fun i => Function.invFun g (a (f i))
        have hβ (i : Fin (m + 1)) : g (β i) = a (f i) := by
          have hi : a (f i) ∈ Set.range g := hr ▸ Set.mem_range_self i
          obtain ⟨j, hj⟩ := hi
          dsimp [β]
          rw [← hj, Function.leftInverse_invFun hg j]
        have hmonoG : StrictMono g := g.toOrderHom.monotone.strictMono_of_injective hg
        let b : ⦋m⦌ ⟶ ⦋k⦌ := SimplexCategory.mkHom {
          toFun := β
          monotone' := by
            intro i j hij
            apply hmonoG.le_iff_le.mp
            rw [hβ i, hβ j]
            exact a.toOrderHom.monotone (f.toOrderHom.monotone hij) }
        have hb : Function.Surjective b := by
          intro j
          have hj : g j ∈ Set.range (fun i : Fin (m + 1) => a (f i)) := hr.symm ▸ Set.mem_range_self j
          obtain ⟨i, hi⟩ := hj
          exact ⟨i, hg ((hβ i).trans hi)⟩
        have hfac : f ≫ a = b ≫ g := by
          apply ConcreteCategory.ext
          ext i
          exact congrArg Fin.val (hβ i).symm
        refine ⟨b, hb, hfac, ?_⟩
        apply StdSimplex.ext
        apply Finsupp.mapDomain_injective hg
        change (StdSimplex.map g (StdSimplex.map b u)).weights = (StdSimplex.map g v).weights
        rw [StdSimplex.map_map]
        have hfun : (fun i => g (b i)) = (fun i => a (f i)) := funext hβ
        rw [hfun, he]
      obtain ⟨b, hb, hfac, hmap⟩ := hfactor n p m k a f g hg u v hu hv (by rw [hfu, hgv])
      let : Epi b := SimplexCategory.epi_iff_surjective.mpr hb
      have hx : S.map f.op (S.map a.op s) = S.map (b ≫ β).op z.val := by
        rw [← comp_apply, ← S.map_comp, ← op_comp, hfac, op_comp, S.map_comp, comp_apply,
          hβ, ← comp_apply, ← S.map_comp, ← op_comp]
      have hdim := S.unique_nonDegenerate_dim (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
      subst q
      have hyz := S.unique_nonDegenerate_simplex (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
      have heq := S.unique_nonDegenerate_map (S.map f.op (S.map a.op s)) α y hα (b ≫ β) z hx
      subst z
      have hcomp : StdSimplex.map (b ≫ β) u =
          StdSimplex.map β (StdSimplex.map b u) := StdSimplex.map_comp u b β
      simp only [heq, hcomp, hmap]
    have hdata (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) :
        ∃ d : (Σ m : ℕ, (⦋m⦌ ⟶ ⦋n⦌) × StdSimplex ℝ (Fin (m + 1))),
          Function.Injective d.2.1 ∧ (∀ i, 0 < d.2.2.weights i) ∧ StdSimplex.map d.2.1 d.2.2 = t := by
      obtain ⟨m, f, hf, u, hu, he⟩ := hsupport n t
      exact ⟨⟨m, f, u⟩, hf, hu, he⟩
    let D (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) := (hdata n t).choose
    have hD (n : ℕ) (t : StdSimplex ℝ (Fin (n + 1))) := (hdata n t).choose_spec
    have hnd (n : ℕ) (s : S _⦋n⦌) :
        ∃ e : (Σ k : ℕ, (⦋n⦌ ⟶ ⦋k⦌) × S.nonDegenerate k),
          Epi e.2.1 ∧ s = S.map e.2.1.op e.2.2.val := by
      obtain ⟨k, a, ha, y, he⟩ := S.exists_nonDegenerate s
      exact ⟨⟨k, a, y⟩, ha, he⟩
    let A (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :=
      (hnd (D n t).1 (S.map (D n t).2.1.op s)).choose
    have hA (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :=
      (hnd (D n t).1 (S.map (D n t).2.1.op s)).choose_spec
    let ν (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :
        (Σ k : ℕ, S.nonDegenerate k × StdSimplex ℝ (Fin (k + 1))) :=
      ⟨(A n s t).1, (A n s t).2.2, StdSimplex.map (A n s t).2.1 (D n t).2.2⟩
    refine ⟨ν, ?_, ?_⟩
    · intro n p a s t
      let : Epi (A n (S.map a.op s) t).2.1 := (hA n (S.map a.op s) t).1
      let : Epi (A p s (StdSimplex.map a t)).2.1 := (hA p s (StdSimplex.map a t)).1
      exact hnorm S n p (D n t).1 (D p (StdSimplex.map a t)).1
        (A n (S.map a.op s) t).1 (A p s (StdSimplex.map a t)).1 a s t
        (D n t).2.1 (D p (StdSimplex.map a t)).2.1
        (hD p (StdSimplex.map a t)).1 (D n t).2.2 (D p (StdSimplex.map a t)).2.2
        (hD n t).2.1 (hD p (StdSimplex.map a t)).2.1
        (hD n t).2.2 (hD p (StdSimplex.map a t)).2.2
        (A n (S.map a.op s) t).2.1 (A p s (StdSimplex.map a t)).2.1
        (A n (S.map a.op s) t).2.2 (A p s (StdSimplex.map a t)).2.2
        (hA n (S.map a.op s) t).2 (hA p s (StdSimplex.map a t)).2
    · intro n y t ht
      let : Epi (A n y.val t).2.1 := (hA n y.val t).1
      have H := hnorm S n n (D n t).1 n (A n y.val t).1 n (𝟙 _) y.val t
        (D n t).2.1 (𝟙 _) (by simpa using Function.injective_id)
        (D n t).2.2 t (hD n t).2.1 ht (hD n t).2.2 (by simp)
        (A n y.val t).2.1 (𝟙 _) (A n y.val t).2.2 y
        (by simpa using (hA n y.val t).2) (by simp)
      change ν n y.val t = ⟨n, y, StdSimplex.map id t⟩ at H
      simpa only [StdSimplex.map_id] using H
  obtain ⟨ν, hν, hν_reduced⟩ := hnormalizer S
  let F := Presheaf.functorToRepresentables S ⋙ SSet.toTop ⋙ forget TopCat
  let c : F.CoconeTypes := {
    pt := (Σ k : ℕ, S.nonDegenerate k × StdSimplex ℝ (Fin (k + 1)))
    ι j t := ν j.unop.obj.unop.len j.unop.val (j.unop.obj.unop.toTopHomeo t)
    ι_naturality {j k} f := by
      funext t
      let a := f.unop.hom.unop
      have H := hν j.unop.obj.unop.len k.unop.obj.unop.len a k.unop.val
        (j.unop.obj.unop.toTopHomeo t)
      have hval : S.map a.op k.unop.val = j.unop.val := f.unop.map_val
      rw [hval] at H
      change ν k.unop.obj.unop.len k.unop.val
        (k.unop.obj.unop.toTopHomeo (SSet.toTop.map (SSet.stdSimplex.map a) t)) = _
      exact (congrArg (ν k.unop.obj.unop.len k.unop.val)
        (SimplexCategory.toTopHomeo_naturality_apply a t)).trans H.symm }
  rintro ⟨⟨n, y⟩, ⟨t, ht⟩⟩ ⟨⟨m, z⟩, ⟨u, hu⟩⟩ he
  let j : S.Elementsᵒᵖ := op {obj := op ⦋n⦌, val := y.val}
  let k : S.Elementsᵒᵖ := op {obj := op ⦋m⦌, val := z.val}
  have hr :=
    CurveComplexGenusTwo.CWHurewicz.SingularApproximation.realization_simplex_eq_iff S j k
      (⦋n⦌.toTopHomeo.symm t) (⦋m⦌.toTopHomeo.symm u) |>.mp he
  have hcol : F.ιColimitType j (⦋n⦌.toTopHomeo.symm t) =
      F.ιColimitType k (⦋m⦌.toTopHomeo.symm u) := (F.ιColimitType_eq_iff ..).mpr hr
  have hn := congrArg (F.descColimitType c) hcol
  change ν n y.val (⦋n⦌.toTopHomeo (⦋n⦌.toTopHomeo.symm t)) =
    ν m z.val (⦋m⦌.toTopHomeo (⦋m⦌.toTopHomeo.symm u)) at hn
  simp only [Homeomorph.apply_symm_apply, hν_reduced n y t ht, hν_reduced m z u hu] at hn
  have hdim : n = m := congrArg Sigma.fst hn
  subst m
  have hp : (y, t) = (z, u) := eq_of_heq (Sigma.mk.inj hn).2
  have hyz : y = z := congrArg Prod.fst hp
  have htu : t = u := congrArg Prod.snd hp
  subst z
  subst u
  rfl

end CurveComplexGenusTwo.CWHurewicz.SingularApproximation
