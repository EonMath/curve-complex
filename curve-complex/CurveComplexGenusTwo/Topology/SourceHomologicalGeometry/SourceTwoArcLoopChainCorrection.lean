import CurveComplexGenusTwo.Topology.SourceHomologicalGeometry.SourceHomologicallyNonzeroCurveCanonicalProof

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CategoryTheory CurveComplexGenusTwo.CWHurewicz Convexity PathChains
open CurveComplex.BranchedDoubleCover
open scoped Simplicial
set_option maxHeartbeats 1000000

theorem parameterized_loop_fundamental_chain_correction
    {S : Type} [TopologicalSpace S] (x : S) (l : Path x x) (c : Curve S)
    (hparameter : ∀ t : unitInterval, c.map (Circle.exp (2 * Real.pi * t.val)) = l t) :
    ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 B =
        singularFinsuppPush (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1
          CircleFundamentalCycle.circleBoundaryChain -
        Finsupp.single (edgeSimplex l.toContinuousMap 0 1) 1 := by
  classical
  let t : Fin 9 → unitInterval := fun k => ⟨(k.val : ℝ)/8, by
    constructor
    · positivity
    · have hk : k.val ≤ 8 := by omega
      exact (div_le_one (by norm_num)).mpr (by exact_mod_cast hk)⟩
  have ht0 : t 0 = 0 := by apply Subtype.ext; norm_num [t]
  have ht1 : t (Fin.last 8) = 1 := by apply Subtype.ext; norm_num [t]
  obtain ⟨B,hB⟩ := finite_actual_path_cut_correction l 8 t ht0 ht1
  have hedge (k : Fin 8) :
      ((TopCat.toSSet.map (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩)).app (.op ⦋1⦌))
        (CircleFundamentalCycle.circleSideSimplex k) =
      edgeSimplex (actualSubpath l (t k.castSucc) (t k.succ)).toContinuousMap 0 1 := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    change c.map (Circle.exp (2 * Real.pi * ((k.val : ℝ) + z.weights 1) / 8)) =
      l (intervalAffine (t k.castSucc) (t k.succ) (weightedTime 1 ![0,1] z))
    rw [←hparameter]
    apply congrArg c.map
    apply congrArg Circle.exp
    simp [intervalAffine,weightedTime,t,Fin.sum_univ_two]
    ring
  refine ⟨B,?_⟩
  rw [hB]
  congr 1
  rw [CircleFundamentalCycle.circleBoundaryChain,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [singularFinsuppPush,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
  rw [hedge]


theorem two_arc_loop_fundamental_chain_correction
    {S : Type} [TopologicalSpace S] {x y : S} (p q : Path x y) (c : Curve S)
    (hparameter : ∀ t : unitInterval,
      c.map (Circle.exp (2 * Real.pi * t.val)) = (p.trans q.symm) t) :
    ∃ B : (TopCat.toSSet.obj (TopCat.of S)) _⦋2⦌ →₀ ℤ,
      singularBoundaryFinsupp (TopCat.of S) 1 B =
        singularFinsuppPush (TopCat.ofHom ⟨c.map,c.embedded.continuous⟩) 1
          CircleFundamentalCycle.circleBoundaryChain -
        (Finsupp.single (edgeSimplex p.toContinuousMap 0 1) 1 -
          Finsupp.single (edgeSimplex q.toContinuousMap 0 1) 1) := by
  classical
  let half : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
  let l := p.trans q.symm
  have hleft : edgeSimplex l.toContinuousMap 0 half = edgeSimplex p.toContinuousMap 0 1 := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    change l (weightedTime 1 ![0,half] z) = p (weightedTime 1 ![0,1] z)
    have hbound : (weightedTime 1 ![0,half] z).val ≤ 1/2 := by
      dsimp [weightedTime,half]
      simp only [Fin.sum_univ_two]
      norm_num
    rw [Path.trans_apply, dif_pos hbound]
    apply congrArg p
    apply Subtype.ext
    simp [weightedTime,half,Fin.sum_univ_two]
    ring
  have hright : edgeSimplex l.toContinuousMap half 1 = edgeSimplex q.symm.toContinuousMap 0 1 := by
    apply (TopCat.toSSetObjEquiv (TopCat.of S) (.op ⦋1⦌)).injective
    ext z
    change l (weightedTime 1 ![half,1] z) = q.symm (weightedTime 1 ![0,1] z)
    have htotal : z.weights 0 + z.weights 1 = 1 := by
      have hh := z.total
      rw [Finsupp.sum_fintype] at hh <;> simpa [Fin.sum_univ_two] using hh
    rw [Path.trans_apply]
    split_ifs with hle
    · have hz : z.weights 1 = 0 := by
        dsimp [weightedTime,half] at hle
        simp only [Fin.sum_univ_two] at hle
        norm_num at hle
        linarith [z.weights_nonneg 1]
      have hw : weightedTime 1 ![0,1] z = 0 := by
        apply Subtype.ext
        simp [weightedTime,Fin.sum_univ_two,hz]
      have hv : weightedTime 1 ![half,1] z = half := by
        apply Subtype.ext
        simp [weightedTime,half,Fin.sum_univ_two,hz,show z.weights 0 = 1 by linarith]
      rw [hw]
      have he : (⟨2 * (weightedTime 1 ![half,1] z).val, by constructor <;> linarith [(weightedTime 1 ![half,1] z).property.1]⟩ : unitInterval) = 1 := by
        apply Subtype.ext
        change 2 * (weightedTime 1 ![half,1] z).val = 1
        rw [hv]
        norm_num [half]
      rw [he]
      change p 1 = q.symm 0
      exact p.target.trans q.symm.source.symm
    · apply congrArg q.symm
      apply Subtype.ext
      simp [weightedTime,half,Fin.sum_univ_two]
      linarith
  obtain ⟨A,hA⟩ := parameterized_loop_fundamental_chain_correction x l c hparameter
  let T := Finsupp.single (triangleSimplex l.toContinuousMap 0 half 1) (1:ℤ)
  let R := Finsupp.single (triangleSimplex q.toContinuousMap 0 1 0) (1:ℤ) +
    Finsupp.single (triangleSimplex q.toContinuousMap 0 0 0) (1:ℤ)
  have hT := triangle_boundary l.toContinuousMap 0 half 1
  change singularBoundaryFinsupp (TopCat.of S) 1 T = _ at hT
  rw [hleft,hright,edgeSimplex_path_symm] at hT
  have hR := reverse_edge_boundary q.toContinuousMap 0 1
  change singularBoundaryFinsupp (TopCat.of S) 1 R = _ at hR
  refine ⟨A-T+R,?_⟩
  rw [map_add,map_sub,hA,hT,hR]
  abel

end CurveComplexGenusTwo.SourceTopology
