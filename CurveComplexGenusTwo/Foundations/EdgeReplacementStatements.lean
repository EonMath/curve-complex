import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

namespace CurveComplex
variable {V : Type*} [DecidableEq V]

/-- Local replacement for source Lemma 7.6: finite triangle fillers yield
an actual path in the subcomplex and a homotopy fixing both endpoints. -/
theorem affine_edge_replacement_of_triangle_fillers
    (K L : AbstractSimplicialComplex V)
    (hKL : ∀ σ, σ ∈ K.faces → σ ∈ L.faces)
    (hfill : ∀ a b : V, ({a, b} : Finset V) ∈ L.faces →
      ({a, b} : Finset V) ∈ K.faces ∨
        ∃ c : V, ({a, b, c} : Finset V) ∈ L.faces ∧
          ({a, c} : Finset V) ∈ K.faces ∧
          ({c, b} : Finset V) ∈ K.faces)
    (x y : RealizationPoint K)
    (p : Path (realizationMap K L hKL x) (realizationMap K L hKL y))
    (hp : IsAffineVertexEdge L p) :
    ∃ q : Path x y, IsFiniteAffineEdgePath K q ∧
      Path.Homotopic p (q.map (realizationMap_continuous K L hKL)) := by
  classical
  have point_ext {M : AbstractSimplicialComplex V} {u v : RealizationPoint M}
      (h : ∀ w, u.weight w = v.weight w) : u = v := by
    cases u; cases v
    simp_all only [RealizationPoint.mk.injEq]
    exact funext h
  have seg_weight (M : AbstractSimplicialComplex V) (σ : Finset V)
      (hσ : σ ∈ M.faces) (a b : V) (ha : a ∈ σ) (hb : b ∈ σ)
      (t : EdgeTime) (v : V) :
      (faceSegment M σ hσ (finiteSimplexVertex σ a ha)
        (finiteSimplexVertex σ b hb) t).weight v =
      (1 - (t : ℝ)) * (if v = a then 1 else 0) +
        (t : ℝ) * (if v = b then 1 else 0) := by
    by_cases hv : v ∈ σ
    · simp [faceSegment, faceInclusion, finiteSimplexSegment, finiteSimplexVertex, hv]
    · have hva : v ≠ a := fun h => hv (h ▸ ha)
      have hvb : v ≠ b := fun h => hv (h ▸ hb)
      simp [faceSegment, faceInclusion, hv, hva, hvb]
  have mkedge (a b : V) (hab : ({a,b} : Finset V) ∈ K.faces)
      (u v : RealizationPoint K)
      (hu : ∀ w, u.weight w = if w = a then 1 else 0)
      (hv : ∀ w, v.weight w = if w = b then 1 else 0) :
      ∃ e : Path u v, IsAffineVertexEdge K e ∧
        ∀ t w, (e t).weight w =
          (1 - (t : ℝ)) * (if w = a then 1 else 0) +
          (t : ℝ) * (if w = b then 1 else 0) := by
    have hu' : u = faceInclusion K {a,b} hab
        (finiteSimplexVertex {a,b} a (by simp)) := by
      apply point_ext; intro w
      rw [hu, finiteSimplexVertex_faceInclusion_weight]
    have hv' : v = faceInclusion K {a,b} hab
        (finiteSimplexVertex {a,b} b (by simp)) := by
      apply point_ext; intro w
      rw [hv, finiteSimplexVertex_faceInclusion_weight]
    let e := ((finiteSegmentPath {a,b}
      (finiteSimplexVertex {a,b} a (by simp))
      (finiteSimplexVertex {a,b} b (by simp))).map
        (continuous_faceInclusion_local K {a,b} hab)).cast hu' hv'
    refine ⟨e, ⟨{a,b}, hab, a, b, by simp, by simp, hu', hv', rfl⟩, ?_⟩
    exact seg_weight K {a,b} hab a b (by simp) (by simp)
  obtain ⟨σ, hσ, a, b, ha, hb, hx, hy, heq⟩ := hp
  have hxw : ∀ w, x.weight w = if w = a then 1 else 0 := by
    intro w
    have hh := congrArg (fun z => z.weight w) hx
    simpa only [realizationMap_weight, finiteSimplexVertex_faceInclusion_weight] using hh
  have hyw : ∀ w, y.weight w = if w = b then 1 else 0 := by
    intro w
    have hh := congrArg (fun z => z.weight w) hy
    simpa only [realizationMap_weight, finiteSimplexVertex_faceInclusion_weight] using hh
  have hpw : ∀ t w, (p t).weight w =
      (1 - (t : ℝ)) * (if w = a then 1 else 0) +
        (t : ℝ) * (if w = b then 1 else 0) := by
    rw [heq]
    exact seg_weight L σ hσ a b ha hb
  have hab : ({a,b} : Finset V) ∈ L.faces :=
    (L.isRelLowerSet_faces hσ).2 (by simp [Finset.insert_subset_iff, ha, hb]) (by simp)
  rcases hfill a b hab with habK | ⟨c, habc, hac, hcb⟩
  · obtain ⟨e, he, hew⟩ := mkedge a b habK x y hxw hyw
    have hpe : p = e.map (realizationMap_continuous K L hKL) := by
      apply DFunLike.ext; intro t; apply point_ext; intro w
      exact (hpw t w).trans (hew t w).symm
    let z : Fin 2 → RealizationPoint K := ![x,y]
    let E : (k : Fin 1) → Path (z k.castSucc) (z k.succ) := fun k =>
      Fin.cases e (fun i => Fin.elim0 i) k
    refine ⟨Path.concat z E, ⟨1, z, E, rfl, rfl, ?_, rfl⟩, ?_⟩
    · intro k; fin_cases k; exact he
    · rw [hpe]
      exact ((Path.Homotopic.concat_one z E).map
        ⟨realizationMap K L hKL, realizationMap_continuous K L hKL⟩).symm
  · have hcK : ({c} : Finset V) ∈ K.faces :=
      (K.isRelLowerSet_faces hac).2 (by simp) (by simp)
    let zc := realizationVertex K c hcK
    obtain ⟨e, he, hew⟩ := mkedge a c hac x zc hxw (realizationVertex_weight K c hcK)
    obtain ⟨f, hf, hfw⟩ := mkedge c b hcb zc y (realizationVertex_weight K c hcK) hyw
    have hxa : realizationMap K L hKL x = faceInclusion L {a,b,c} habc
        (finiteSimplexVertex {a,b,c} a (by simp)) := by
      apply point_ext; intro w
      exact (hxw w).trans (finiteSimplexVertex_faceInclusion_weight L _ habc a (by simp) w).symm
    have hyb : realizationMap K L hKL y = faceInclusion L {a,b,c} habc
        (finiteSimplexVertex {a,b,c} b (by simp)) := by
      apply point_ext; intro w
      exact (hyw w).trans (finiteSimplexVertex_faceInclusion_weight L _ habc b (by simp) w).symm
    have H := Path.Homotopic.pathCast ⟨triangleVertexEdgeHomotopy L {a,b,c} habc a b c
      (by simp) (by simp) (by simp)⟩ hxa hyb
    have hdirect : ((finiteSegmentPath {a,b,c}
        (finiteSimplexVertex {a,b,c} a (by simp))
        (finiteSimplexVertex {a,b,c} b (by simp))).map
        (continuous_faceInclusion_local L {a,b,c} habc)).cast hxa hyb = p := by
      apply DFunLike.ext; intro t; apply point_ext; intro w
      exact (seg_weight L _ habc a b (by simp) (by simp) t w).trans (hpw t w).symm
    have hdetour : (((finiteSegmentPath {a,b,c}
        (finiteSimplexVertex {a,b,c} a (by simp))
        (finiteSimplexVertex {a,b,c} c (by simp))).trans
        (finiteSegmentPath {a,b,c}
        (finiteSimplexVertex {a,b,c} c (by simp))
        (finiteSimplexVertex {a,b,c} b (by simp)))).map
        (continuous_faceInclusion_local L {a,b,c} habc)).cast hxa hyb =
          (e.trans f).map (realizationMap_continuous K L hKL) := by
      apply DFunLike.ext; intro t; apply point_ext; intro w
      simp only [Path.cast_coe, Path.map_coe, Function.comp_apply, Path.trans_apply]
      split_ifs <;> simp only [realizationMap_weight]
      · exact (seg_weight L _ habc a c (by simp) (by simp) _ w).trans (hew _ w).symm
      · exact (seg_weight L _ habc c b (by simp) (by simp) _ w).trans (hfw _ w).symm
    rw [hdirect, hdetour] at H
    let z : Fin 3 → RealizationPoint K := ![x,zc,y]
    let E : (k : Fin 2) → Path (z k.castSucc) (z k.succ) := fun k =>
      Fin.cases e (fun i => Fin.cases f (fun j => Fin.elim0 j) i) k
    refine ⟨Path.concat z E, ⟨2, z, E, rfl, rfl, ?_, rfl⟩, ?_⟩
    · intro k; fin_cases k; exact he; exact hf
    · exact H.trans (((Path.Homotopic.concat_two z E).map
        ⟨realizationMap K L hKL, realizationMap_continuous K L hKL⟩).symm)

/-- Source Lemma 7.6's abstract realization step, at each vertex basepoint.
The assumptions are finite simplicial data, not connectivity or homotopies. -/
theorem fundamentalGroupMap_surjective_of_triangle_fillers
    (K L : AbstractSimplicialComplex V)
    (hKL : ∀ σ, σ ∈ K.faces → σ ∈ L.faces)
    (hvertices : ∀ v : V, ({v} : Finset V) ∈ L.faces →
      ({v} : Finset V) ∈ K.faces)
    (hfill : ∀ a b : V, ({a, b} : Finset V) ∈ L.faces →
      ({a, b} : Finset V) ∈ K.faces ∨
        ∃ c : V, ({a, b, c} : Finset V) ∈ L.faces ∧
          ({a, c} : Finset V) ∈ K.faces ∧
          ({c, b} : Finset V) ∈ K.faces)
    (base : V) (hbase : ({base} : Finset V) ∈ K.faces) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨realizationMap K L hKL, realizationMap_continuous K L hKL⟩ :
          C(RealizationPoint K, RealizationPoint L))
        (realizationVertex K base hbase)) := by
  classical
  have point_ext {M : AbstractSimplicialComplex V} {u v : RealizationPoint M}
      (h : ∀ w, u.weight w = v.weight w) : u = v := by
    cases u; cases v
    simp_all only [RealizationPoint.mk.injEq]
    exact funext h
  let f := realizationMap K L hKL
  have hf : Continuous f := realizationMap_continuous K L hKL
  have finj : Function.Injective f := by
    intro u v h
    apply point_ext; intro w
    exact congrArg (fun z => z.weight w) h
  have liftChain : ∀ (n : ℕ) (z : Fin (n+1) → RealizationPoint L)
      (E : (k : Fin n) → Path (z k.castSucc) (z k.succ)),
      (∀ k, IsAffineVertexEdge L (E k)) →
      ∀ (x y : RealizationPoint K) (hx : f x = z 0) (hy : f y = z (Fin.last n)),
      ∃ q : Path x y, Path.Homotopic ((Path.concat z E).cast hx hy) (q.map hf) := by
    intro n
    induction n with
    | zero =>
      intro z E hE x y hx hy
      have hxy : x = y := finj (hx.trans hy.symm)
      subst y
      refine ⟨Path.refl x, ?_⟩
      have heq : (Path.concat z E).cast hx hy = (Path.refl x).map hf := by
        apply DFunLike.ext; intro t
        simpa only [Path.concat_zero, Path.cast_coe, Path.refl_apply,
          Path.map_coe, Function.comp_apply] using hx.symm
      rw [heq]
    | succ n ih =>
      intro z E hE x y hx hy
      obtain ⟨σ, hσ, a, b, ha, hb, hu, hv, heq⟩ := hE (Fin.last n)
      have haL : ({a} : Finset V) ∈ L.faces :=
        (L.isRelLowerSet_faces hσ).2 (by simpa using ha) (by simp)
      let m := realizationVertex K a (hvertices a haL)
      have hm : f m = z (Fin.last n).castSucc := by
        apply point_ext; intro w
        change m.weight w = (z (Fin.last n).castSucc).weight w
        rw [hu, finiteSimplexVertex_faceInclusion_weight]
        exact realizationVertex_weight K a (hvertices a haL) w
      obtain ⟨q₁, hq₁⟩ := ih (z ∘ Fin.castSucc) (fun k => E k.castSucc)
        (fun k => hE k.castSucc) x m hx hm
      obtain ⟨q₂, _, hq₂⟩ := affine_edge_replacement_of_triangle_fillers K L hKL hfill
        m y ((E (Fin.last n)).cast hm hy)
        (IsAffineVertexEdge.cast L _ (hE (Fin.last n)) hm hy)
      refine ⟨q₁.trans q₂, ?_⟩
      have h := hq₁.hcomp hq₂
      have heq : (Path.concat z E).cast hx hy =
          ((Path.concat (z ∘ Fin.castSucc) (fun k => E k.castSucc)).cast hx hm).trans
            ((E (Fin.last n)).cast hm hy) := by
        rw [Path.concat_succ]
        rfl
      rw [heq, Path.map_trans]
      exact h
  intro g
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
  have hb : f (realizationVertex K base hbase) =
      realizationVertex L base (hKL _ hbase) := by
    apply point_ext; intro w
    change (realizationVertex K base hbase).weight w = _
    rw [realizationVertex_weight, realizationVertex_weight]
  obtain ⟨p', H, hp'⟩ := exists_based_loop_affine_edge_path L base (hKL _ hbase)
    (p.cast hb.symm hb.symm)
  obtain ⟨n, z, E, hx, hy, hE, hp'eq⟩ := hp'
  obtain ⟨q, hq⟩ := liftChain n z E hE
    (realizationVertex K base hbase) (realizationVertex K base hbase)
    (hb.trans hx) (hb.trans hy)
  refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
  change Path.Homotopic.Quotient.mk (q.map hf) = Path.Homotopic.Quotient.mk p
  apply Path.Homotopic.Quotient.eq.mpr
  have H' := H.pathCast hb hb
  rw [hp'eq] at H'
  exact (H'.trans hq).symm
end CurveComplex

#print axioms CurveComplex.affine_edge_replacement_of_triangle_fillers
#print axioms CurveComplex.fundamentalGroupMap_surjective_of_triangle_fillers
