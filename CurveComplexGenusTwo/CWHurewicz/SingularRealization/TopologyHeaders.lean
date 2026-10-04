import CurveComplexGenusTwo.CWHurewicz.SingularRealization.GeometryHeaders
import Mathlib.Data.Finset.Sort
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
open CategoryTheory CategoryTheory.Limits Opposite Convexity Topology
open scoped Simplicial
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.SingularApproximation
/-- Closed characteristic maps, T1, and embedded nondegenerate interiors for the actual realization. -/
theorem realization_characteristic_topology (S : SSet.{0}) :
    (∀ (n : ℕ) (s : S _⦋n⦌), IsClosedMap (fun t : StdSimplex ℝ (Fin (n + 1)) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t))) ∧
    T1Space (SSet.toTop.obj S) ∧
    (∀ (n : ℕ) (s : S.nonDegenerate n), IsEmbedding
      (fun t : {t : StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < t.weights i} =>
        SSet.toTop.map (SSet.yonedaEquiv.symm s.val) (⦋n⦌.toTopHomeo.symm t.val))) := by
  have hInjective (S : SSet.{0}) :
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
  have hCompact (S : SSet.{0})
    (hinj : Function.Injective
      (fun z : (Σ ns : (Σ n : ℕ, S.nonDegenerate n),
          {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =>
        SSet.toTop.map (SSet.yonedaEquiv.symm z.1.2.val) (⦋z.1.1⦌.toTopHomeo.symm z.2.val)))
    (n m : ℕ) (s : S _⦋n⦌) (q : S _⦋m⦌) :
    IsCompact (Set.ofPred (fun uv : StdSimplex ℝ (Fin (n + 1)) × StdSimplex ℝ (Fin (m + 1)) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm uv.1) =
        SSet.toTop.map (SSet.yonedaEquiv.symm q) (⦋m⦌.toTopHomeo.symm uv.2))) := by
    classical
    have hrel (S : SSet.{0})
      (hinj : Function.Injective
        (fun z : (Σ ns : (Σ n : ℕ, S.nonDegenerate n),
            {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =>
          SSet.toTop.map (SSet.yonedaEquiv.symm z.1.2.val) (⦋z.1.1⦌.toTopHomeo.symm z.2.val)))
      (n m : ℕ) (s : S _⦋n⦌) (q : S _⦋m⦌)
      (w : StdSimplex ℝ (Fin (n + 1))) (t : StdSimplex ℝ (Fin (m + 1))) :
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm w) =
        SSet.toTop.map (SSet.yonedaEquiv.symm q) (⦋m⦌.toTopHomeo.symm t) ↔
      ∃ (l j r : ℕ) (_ : l ≤ n) (_ : j ≤ m) (_ : r ≤ n)
        (f : ⦋l⦌ ⟶ ⦋n⦌) (g : ⦋j⦌ ⟶ ⦋m⦌)
        (a : ⦋l⦌ ⟶ ⦋r⦌) (b : ⦋j⦌ ⟶ ⦋r⦌) (σ : ⦋r⦌ ⟶ ⦋l⦌)
        (u : StdSimplex ℝ (Fin (l + 1))) (v : StdSimplex ℝ (Fin (j + 1))),
        S.map f.op s = S.map a.op (S.map σ.op (S.map f.op s)) ∧
        S.map g.op q = S.map b.op (S.map σ.op (S.map f.op s)) ∧
        StdSimplex.map a u = StdSimplex.map b v ∧
        StdSimplex.map f u = w ∧ StdSimplex.map g v = t := by
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
      let char (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :=
        SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t)
      have hchar (l n : ℕ) (f : ⦋l⦌ ⟶ ⦋n⦌) (s : S _⦋n⦌)
          (u : StdSimplex ℝ (Fin (l + 1))) :
          char l (S.map f.op s) u = char n s (StdSimplex.map f u) := by
        have he : SSet.yonedaEquiv.symm (S.map f.op s) =
            SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm s := uliftYonedaEquiv_symm_map f.op s
        dsimp [char]
        rw [he, SSet.toTop.map_comp, SimplexCategory.toTopHomeo_symm_naturality_apply]
        rfl
      constructor
      · intro he
        obtain ⟨l, f, hf, u, hu, hfu⟩ := hsupport n w
        obtain ⟨j, g, hg, v, hv, hgv⟩ := hsupport m t
        obtain ⟨r, a, ha, y, hya⟩ := S.exists_nonDegenerate (S.map f.op s)
        obtain ⟨p, b, hb, z, hzb⟩ := S.exists_nonDegenerate (S.map g.op q)
        have hUa : ∀ i : Fin (r + 1), 0 < (StdSimplex.map a u).weights i :=
          hpositive (α := Fin (l + 1)) (β := Fin (r + 1)) a
            (SimplexCategory.epi_iff_surjective.mp ha) u hu
        have hVb : ∀ i : Fin (p + 1), 0 < (StdSimplex.map b v).weights i :=
          hpositive (α := Fin (j + 1)) (β := Fin (p + 1)) b
            (SimplexCategory.epi_iff_surjective.mp hb) v hv
        have hz : char r y.val (StdSimplex.map a u) = char p z.val (StdSimplex.map b v) := by
          rw [← hchar, ← hya, hchar, hfu, ← hchar j p b, ← hzb, hchar, hgv]
          exact he
        have hi :
            (⟨⟨r, y⟩, ⟨StdSimplex.map a u, hUa⟩⟩ : Σ ns : (Σ n : ℕ, S.nonDegenerate n),
              {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =
            ⟨⟨p, z⟩, ⟨StdSimplex.map b v, hVb⟩⟩ := hinj hz
        have hn := congrArg Sigma.fst hi
        have hrp : r = p := congrArg Sigma.fst hn
        subst p
        have hyz : y = z := eq_of_heq (Sigma.mk.inj hn).2
        subst z
        have hw : StdSimplex.map a u = StdSimplex.map b v := congrArg Subtype.val
          (eq_of_heq (Sigma.mk.inj hi).2)
        have hl : l ≤ n := by
          have H := Fintype.card_le_of_injective f hf
          simp only [Fintype.card_fin] at H
          omega
        have hj : j ≤ m := by
          have H := Fintype.card_le_of_injective g hg
          simp only [Fintype.card_fin] at H
          omega
        let : Epi a := ha
        let := isSplitEpi_of_epi a
        let σ : ⦋r⦌ ⟶ ⦋l⦌ := section_ a
        have hrecover : S.map σ.op (S.map f.op s) = y.val := by
          rw [hya, ← comp_apply, ← S.map_comp, ← op_comp, IsSplitEpi.id,
            op_id, S.map_id, id_apply]
        refine ⟨l, j, r, hl, hj, (SimplexCategory.le_of_epi a).trans hl,
          f, g, a, b, σ, u, v, ?_, ?_, hw, hfu, hgv⟩
        · rw [hrecover]
          exact hya
        · rw [hrecover]
          exact hzb
      · rintro ⟨l, j, r, hl, hj, hr, f, g, a, b, σ, u, v, hya, hzb, hw, hfu, hgv⟩
        change char n s w = char m q t
        rw [← hfu, ← hgv, ← hchar l n f, ← hchar j m g, hya, hzb,
          hchar l r a, hchar j r b, hw]
    let I := Σ l : Fin (n + 1), Σ j : Fin (m + 1), Σ r : Fin (n + 1),
      (⦋l.val⦌ ⟶ ⦋n⦌) × (⦋j.val⦌ ⟶ ⦋m⦌) × (⦋l.val⦌ ⟶ ⦋r.val⦌) ×
        (⦋j.val⦌ ⟶ ⦋r.val⦌) × (⦋r.val⦌ ⟶ ⦋l.val⦌)
    let K (i : I) : Set (StdSimplex ℝ (Fin (i.1.val + 1)) × StdSimplex ℝ (Fin (i.2.1.val + 1))) :=
      match i with
      | ⟨l, j, r, f, g, a, b, σ⟩ => Set.ofPred (fun uv =>
          S.map f.op s = S.map a.op (S.map σ.op (S.map f.op s)) ∧
          S.map g.op q = S.map b.op (S.map σ.op (S.map f.op s)) ∧
          StdSimplex.map a uv.1 = StdSimplex.map b uv.2)
    let M (i : I) :
        StdSimplex ℝ (Fin (i.1.val + 1)) × StdSimplex ℝ (Fin (i.2.1.val + 1)) →
          StdSimplex ℝ (Fin (n + 1)) × StdSimplex ℝ (Fin (m + 1)) :=
      match i with
      | ⟨l, j, r, f, g, a, b, σ⟩ => fun uv => (StdSimplex.map f uv.1, StdSimplex.map g uv.2)
    have hK (i : I) : IsCompact (K i) := by
      rcases i with ⟨l, j, r, f, g, a, b, σ⟩
      let : T2Space (StdSimplex ℝ (Fin (r.val + 1))) :=
        (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (r.val + 1))).t2Space
      apply IsClosed.isCompact
      dsimp only [K]
      by_cases ha : S.map f.op s = S.map a.op (S.map σ.op (S.map f.op s))
      · by_cases hb : S.map g.op q = S.map b.op (S.map σ.op (S.map f.op s))
        · simp only [eq_true ha, eq_true hb, true_and]
          exact isClosed_eq ((StdSimplex.continuous_map ℝ a).comp continuous_fst)
            ((StdSimplex.continuous_map ℝ b).comp continuous_snd)
        · simp only [eq_false hb, false_and, and_false, Set.ofPred_false, isClosed_empty]
      · simp only [eq_false ha, false_and, Set.ofPred_false, isClosed_empty]
    have hM (i : I) : Continuous (M i) := by
      rcases i with ⟨l, j, r, f, g, a, b, σ⟩
      exact ((StdSimplex.continuous_map ℝ f).comp continuous_fst).prodMk
        ((StdSimplex.continuous_map ℝ g).comp continuous_snd)
    have hset :
        Set.ofPred (fun uv : StdSimplex ℝ (Fin (n + 1)) × StdSimplex ℝ (Fin (m + 1)) =>
          SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm uv.1) =
            SSet.toTop.map (SSet.yonedaEquiv.symm q) (⦋m⦌.toTopHomeo.symm uv.2)) =
        ⋃ i : I, M i '' K i := by
      ext uv
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image]
      constructor
      · intro he
        obtain ⟨l, j, r, hl, hj, hr, f, g, a, b, σ, u, v, ha, hb, heq, hfu, hgv⟩ :=
          (hrel S hinj n m s q uv.1 uv.2).mp he
        refine ⟨⟨⟨l, Nat.lt_succ_of_le hl⟩, ⟨j, Nat.lt_succ_of_le hj⟩,
          ⟨r, Nat.lt_succ_of_le hr⟩, f, g, a, b, σ⟩, (u, v), ⟨ha, hb, heq⟩, ?_⟩
        exact Prod.ext hfu hgv
      · rintro ⟨⟨l, j, r, f, g, a, b, σ⟩, ⟨u, v⟩, ⟨ha, hb, heq⟩, hmap⟩
        exact (hrel S hinj n m s q uv.1 uv.2).mpr
          ⟨l.val, j.val, r.val, Nat.le_of_lt_succ l.isLt, Nat.le_of_lt_succ j.isLt,
            Nat.le_of_lt_succ r.isLt, f, g, a, b, σ, u, v, ha, hb, heq,
            congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩
    rw [hset]
    exact isCompact_iUnion fun i => (hK i).image (hM i)
  have hClosed (S : SSet.{0})
    (hcompact : ∀ (n m : ℕ) (s : S _⦋n⦌) (q : S _⦋m⦌),
      IsCompact (Set.ofPred (fun uv : StdSimplex ℝ (Fin (n + 1)) × StdSimplex ℝ (Fin (m + 1)) =>
        SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm uv.1) =
          SSet.toTop.map (SSet.yonedaEquiv.symm q) (⦋m⦌.toTopHomeo.symm uv.2))))
    (n : ℕ) (s : S _⦋n⦌) :
    IsClosedMap (fun t : StdSimplex ℝ (Fin (n + 1)) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t)) := by
    intro C hC
    apply CurveComplexGenusTwo.CWHurewicz.SingularApproximation.realization_isClosed_iff S _ |>.mpr
    intro m q
    let : T2Space (StdSimplex ℝ (Fin (m.len + 1))) :=
      (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (m.len + 1))).t2Space
    let D := Set.ofPred (fun uv : StdSimplex ℝ (Fin (m.len + 1)) × StdSimplex ℝ (Fin (n + 1)) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm q) (m.toTopHomeo.symm uv.1) =
        SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm uv.2)) ∩
          (Set.univ ×ˢ C)
    have hD : IsCompact D := (hcompact m.len n q s).inter_right (isClosed_univ.prod hC)
    have H : IsClosed (Prod.fst '' D) := (hD.image continuous_fst).isClosed
    have hset : Set.ofPred (fun w : StdSimplex ℝ (Fin (m.len + 1)) =>
        SSet.toTop.map (SSet.yonedaEquiv.symm q) (m.toTopHomeo.symm w) ∈
          (fun t : StdSimplex ℝ (Fin (n + 1)) =>
            SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t)) '' C) =
        Prod.fst '' D := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_image, D, Set.mem_inter_iff, Set.mem_prod,
        Set.mem_univ, true_and]
      constructor
      · rintro ⟨v, hv, he⟩
        exact ⟨(w, v), ⟨he.symm, hv⟩, rfl⟩
      · rintro ⟨⟨z, v⟩, ⟨he, hv⟩, hz⟩
        change z = w at hz
        subst z
        exact ⟨v, hv, he.symm⟩
    rw [← hset] at H
    have H' := H.preimage m.toTopHomeo.continuous
    convert H' using 1
    ext w
    simp
  have hSingle (S : SSet.{0})
    (hinj : Function.Injective
      (fun z : (Σ ns : (Σ n : ℕ, S.nonDegenerate n),
          {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =>
        SSet.toTop.map (SSet.yonedaEquiv.symm z.1.2.val) (⦋z.1.1⦌.toTopHomeo.symm z.2.val)))
    (n : ℕ) (s : S.nonDegenerate n)
    (w t : StdSimplex ℝ (Fin (n + 1))) (ht : ∀ i, 0 < t.weights i)
    (he : SSet.toTop.map (SSet.yonedaEquiv.symm s.val) (⦋n⦌.toTopHomeo.symm w) =
      SSet.toTop.map (SSet.yonedaEquiv.symm s.val) (⦋n⦌.toTopHomeo.symm t)) : w = t := by
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
    let char (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n + 1))) :=
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t)
    have hchar (l n : ℕ) (f : ⦋l⦌ ⟶ ⦋n⦌) (s : S _⦋n⦌)
        (u : StdSimplex ℝ (Fin (l + 1))) :
        char l (S.map f.op s) u = char n s (StdSimplex.map f u) := by
      have he : SSet.yonedaEquiv.symm (S.map f.op s) =
          SSet.stdSimplex.map f ≫ SSet.yonedaEquiv.symm s := uliftYonedaEquiv_symm_map f.op s
      dsimp [char]
      rw [he, SSet.toTop.map_comp, SimplexCategory.toTopHomeo_symm_naturality_apply]
      rfl
    obtain ⟨l, f, hf, u, hu, hfu⟩ := hsupport n w
    obtain ⟨r, a, ha, y, hya⟩ := S.exists_nonDegenerate (S.map f.op s.val)
    have hv : ∀ i : Fin (r + 1), 0 < (StdSimplex.map a u).weights i :=
      hpositive (α := Fin (l + 1)) (β := Fin (r + 1)) a
        (SimplexCategory.epi_iff_surjective.mp ha) u hu
    have hz : char r y.val (StdSimplex.map a u) = char n s.val t := by
      rw [← hchar, ← hya, hchar, hfu]
      exact he
    have hi :
        (⟨⟨r, y⟩, ⟨StdSimplex.map a u, hv⟩⟩ : Σ ns : (Σ n : ℕ, S.nonDegenerate n),
          {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =
        ⟨⟨n, s⟩, ⟨t, ht⟩⟩ := hinj hz
    have hn := congrArg Sigma.fst hi
    have hrn : r = n := congrArg Sigma.fst hn
    subst r
    have hys : y = s := eq_of_heq (Sigma.mk.inj hn).2
    subst y
    have hw : StdSimplex.map a u = t := congrArg Subtype.val (eq_of_heq (Sigma.mk.inj hi).2)
    have hle : l ≤ n := by
      have H := Fintype.card_le_of_injective f hf
      simp only [Fintype.card_fin] at H
      omega
    let : Epi a := ha
    have hnl : n ≤ l := SimplexCategory.le_of_epi a
    have hln : l = n := Nat.le_antisymm hle hnl
    subst l
    let : Mono f := SimplexCategory.mono_iff_injective.mpr hf
    have hf_id : f = 𝟙 _ := SimplexCategory.eq_id_of_mono f
    have ha_id : a = 𝟙 _ := SimplexCategory.eq_id_of_epi a
    have hw' : u = t := by
      rw [ha_id] at hw
      change StdSimplex.map id u = t at hw
      simpa only [StdSimplex.map_id] using hw
    rw [hf_id] at hfu
    change StdSimplex.map id u = w at hfu
    simpa only [StdSimplex.map_id, hw'] using hfu.symm
  have hGeneric {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (hc : IsClosedMap f) (U : Set X)
    (hs : ∀ (u : U) (x : X), f x = f u.val → x = u.val) :
    IsEmbedding (fun u : U => f u.val) := by
    let F : U → Set.range (fun u : U => f u.val) := fun u => ⟨f u.val, ⟨u, rfl⟩⟩
    have hF : Continuous F := (hf.comp continuous_subtype_val).subtype_mk _
    have hinj : Function.Injective F := by
      intro u v he
      apply Subtype.ext
      exact hs v u.val (congrArg Subtype.val he)
    have hclosed : IsClosedMap F := by
      intro A hA
      obtain ⟨C, hC, hAC⟩ := isClosed_induced_iff.mp hA
      have he : F '' A = Subtype.val ⁻¹' (f '' C) := by
        ext v
        constructor
        · rintro ⟨u, hu, rfl⟩
          have huC : u ∈ Subtype.val ⁻¹' C := hAC.symm ▸ hu
          exact ⟨u.val, huC, rfl⟩
        · rintro ⟨x, hx, hfx⟩
          obtain ⟨u, hu⟩ := v.prop
          have hxu : x = u.val := hs u x (hfx.trans hu.symm)
          subst x
          refine ⟨u, ?_, ?_⟩
          · exact hAC ▸ (show u ∈ Subtype.val ⁻¹' C from hx)
          · exact Subtype.ext hu
      rw [he]
      exact (hc C hC).preimage continuous_subtype_val
    have hemb := IsClosedEmbedding.of_continuous_injective_isClosedMap hF hinj hclosed
    exact IsEmbedding.subtypeVal.comp hemb.isEmbedding
  have hi := hInjective S
  have hc (n : ℕ) (s : S _⦋n⦌) : IsClosedMap (fun t : StdSimplex ℝ (Fin (n + 1)) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t)) :=
    hClosed S (fun n m s q => hCompact S hi n m s q) n s
  refine ⟨hc, ?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    obtain ⟨n, s, t, ht⟩ :=
      CurveComplexGenusTwo.CWHurewicz.SingularApproximation.realization_simplex_representation S x
    let : T2Space (StdSimplex ℝ (Fin (n.len + 1))) :=
      (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n.len + 1))).t2Space
    have H := hc n.len s {n.toTopHomeo t} isClosed_singleton
    simpa only [Set.image_singleton, Homeomorph.symm_apply_apply, ht] using H
  · intro n s
    let f : StdSimplex ℝ (Fin (n + 1)) → SSet.toTop.obj S := fun t =>
      SSet.toTop.map (SSet.yonedaEquiv.symm s.val) (⦋n⦌.toTopHomeo.symm t)
    have hf : Continuous f := (SSet.toTop.map (SSet.yonedaEquiv.symm s.val)).hom.continuous.comp
      ⦋n⦌.toTopHomeo.symm.continuous
    exact hGeneric f hf (hc n s.val) (Set.ofPred (fun t => ∀ i, 0 < t.weights i))
      (fun u w he => hSingle S hi n s w u.val u.prop he)
/-- Every closed characteristic simplex has a closed map into the actual realization. -/
theorem realization_characteristic_isClosedMap (S : SSet.{0}) (n : ℕ) (s : S _⦋n⦌) :
    IsClosedMap (fun t : StdSimplex ℝ (Fin (n + 1)) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm s) (⦋n⦌.toTopHomeo.symm t)) := by
  exact (realization_characteristic_topology S).1 n s
/-- T1 separation of the actual realization; this does not claim Hausdorffness. -/
theorem realization_t1Space (S : SSet.{0}) : T1Space (SSet.toTop.obj S) := by
  exact (realization_characteristic_topology S).2.1
/-- The positive-coordinate interior of each nondegenerate simplex is topologically embedded. -/
theorem realization_nondegenerate_interior_isEmbedding (S : SSet.{0}) (n : ℕ)
    (s : S.nonDegenerate n) : IsEmbedding
      (fun t : {t : StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < t.weights i} =>
        SSet.toTop.map (SSet.yonedaEquiv.symm s.val) (⦋n⦌.toTopHomeo.symm t.val)) := by
  exact (realization_characteristic_topology S).2.2 n s
end CurveComplexGenusTwo.CWHurewicz.SingularApproximation
