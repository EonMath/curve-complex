import CurveComplexGenusTwo.CWHurewicz.CWBasic
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.ChartHeaders
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.TopologyHeaders
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.NormalFormHeaders
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.BoundaryHeaders
import Mathlib.AlgebraicTopology.SimplicialSet.Finite
import Mathlib.Topology.CWComplex.Classical.Basic
open CategoryTheory CategoryTheory.Limits Convexity Topology Metric Set
open scoped Simplicial
open CurveComplexGenusTwo.CWHurewicz.SingularApproximation
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
/-- The nondegenerate-cell CW construction on the actual realization has the
literal simplicial skeleton as its lower-dimensional CW skeleton. -/
theorem finite_realization_canonical_skeleton (S : SSet.{0}) [S.Finite] :
    ∃ cw : CWComplex (Set.univ : Set (SSet.toTop.obj S)),
      letI := cw
      T2Space (SSet.toTop.obj S) ∧
      ∀ d : ℕ, skeletonBelow (SSet.toTop.obj S) d =
        Set.range (SSet.toTop.map (S.skeleton d).ι) := by
  classical
  let chart (n : ℕ) := Classical.choose (standardSimplex_diskChart n)
  have chartpos (n : ℕ) := Classical.choose_spec (standardSimplex_diskChart n)
  let characteristic (n : ℕ) (s : S.nonDegenerate n) :
      StdSimplex ℝ (Fin (n + 1)) → SSet.toTop.obj S := fun t =>
    SSet.toTop.map (SSet.yonedaEquiv.symm s.val) (⦋n⦌.toTopHomeo.symm t)
  let disk (n : ℕ) (s : S.nonDegenerate n) : (closedBall (0 : Fin n → ℝ) 1) →
      SSet.toTop.obj S := characteristic n s ∘ chart n
  let extend (n : ℕ) (s : S.nonDegenerate n) : (Fin n → ℝ) → SSet.toTop.obj S :=
    fun x => if hx : x ∈ closedBall 0 1 then disk n s ⟨x, hx⟩ else disk n s ⟨0, by simp⟩
  have hext (n : ℕ) (s : S.nonDegenerate n) (x : closedBall (0 : Fin n → ℝ) 1) :
      extend n s x.val = disk n s x := by simp only [extend, dite_eq_left x.property]
  have hc (n : ℕ) (s : S.nonDegenerate n) : Continuous (disk n s) :=
    (SSet.toTop.map (SSet.yonedaEquiv.symm s.val)).hom.continuous.comp
      (⦋n⦌.toTopHomeo.symm.continuous.comp (chart n).continuous)
  let interiorChart (n : ℕ) : (ball (0 : Fin n → ℝ) 1) →
      {t : StdSimplex ℝ (Fin (n + 1)) // ∀ i, 0 < t.weights i} :=
    fun x => ⟨chart n ⟨x.val, ball_subset_closedBall x.property⟩,
      (chartpos n _).mpr x.property⟩
  have hci (n : ℕ) : IsEmbedding (interiorChart n) := by
    apply IsEmbedding.of_comp
      (Continuous.subtype_mk ((chart n).continuous.comp
        (continuous_subtype_val.subtype_mk _)) _)
      continuous_subtype_val
    have ho : IsEmbedding (fun x : ball (0 : Fin n → ℝ) 1 =>
        (⟨x.val, ball_subset_closedBall x.property⟩ : closedBall (0 : Fin n → ℝ) 1)) := by
      apply IsEmbedding.of_comp (continuous_subtype_val.subtype_mk _) continuous_subtype_val
      exact IsEmbedding.subtypeVal
    exact (chart n).isEmbedding.comp ho
  have hb (n : ℕ) (s : S.nonDegenerate n) : IsEmbedding
      (fun x : ball (0 : Fin n → ℝ) 1 => extend n s x.val) := by
    have h := (realization_nondegenerate_interior_isEmbedding S n s).comp (hci n)
    convert h using 1
    funext x
    exact hext n s ⟨x.val, ball_subset_closedBall x.property⟩
  have hi (n : ℕ) (s : S.nonDegenerate n) : InjOn (extend n s) (ball 0 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val ((hb n s).injective (show
      (fun z : ball (0 : Fin n → ℝ) 1 => extend n s z.val) ⟨x,hx⟩ =
      (fun z : ball (0 : Fin n → ℝ) 1 => extend n s z.val) ⟨y,hy⟩ from hxy))
  let cellmap (n : ℕ) (s : S.nonDegenerate n) :=
    (hi n s).toPartialEquiv (extend n s) (ball 0 1)
  have hsymm (n : ℕ) (s : S.nonDegenerate n) :
      ContinuousOn (cellmap n s).symm (cellmap n s).target := by
    let e := cellmap n s
    have hrange : Set.range (fun x : ball (0 : Fin n → ℝ) 1 => extend n s x.val) = e.target := by
      change _ = extend n s '' ball 0 1
      ext y
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
    let H := (hb n s).toHomeomorph.trans (Homeomorph.setCongr hrange)
    have heq (p : e.target) :
        e.symm p.val = (H.symm p).val := by
      apply hi n s
      · exact e.map_target p.property
      · exact (H.symm p).property
      · exact (e.right_inv p.property).trans (congrArg Subtype.val (H.apply_symm_apply p)).symm
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp H.symm.continuous).congr (fun p => (heq p).symm)
  have himage (n : ℕ) (s : S.nonDegenerate n) :
      extend n s '' closedBall 0 1 = Set.range (characteristic n s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨chart n ⟨x,hx⟩, (hext n s ⟨x,hx⟩).symm⟩
    · rintro ⟨t,rfl⟩
      let x := (chart n).symm t
      exact ⟨x.val,x.property, (hext n s x).trans
        (congrArg (characteristic n s) ((chart n).apply_symm_apply t))⟩
  let cw : CWComplex (Set.univ : Set (SSet.toTop.obj S)) := {
    cell := fun n => ↥(S.nonDegenerate n)
    map := cellmap
    source_eq := by intro n s; rfl
    continuousOn := by
      intro n s
      rw [continuousOn_iff_continuous_domRestrict]
      exact (hc n s).congr (fun x => (hext n s x).symm)
    continuousOn_symm := hsymm
    pairwiseDisjoint' := by
      intro a ha b hb hab
      change Disjoint (extend a.1 a.2 '' ball 0 1) (extend b.1 b.2 '' ball 0 1)
      rw [Set.disjoint_left]
      rintro z ⟨x,hx,rfl⟩ ⟨y,hy,hxy⟩
      have h := realization_nondegenerate_interiors_injective S
        (show
          (fun q : (Σ ns : (Σ n : ℕ, S.nonDegenerate n),
            {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =>
            SSet.toTop.map (SSet.yonedaEquiv.symm q.1.2.val)
              (⦋q.1.1⦌.toTopHomeo.symm q.2.val))
            ⟨a, interiorChart a.1 ⟨x,hx⟩⟩ =
          (fun q : (Σ ns : (Σ n : ℕ, S.nonDegenerate n),
            {t : StdSimplex ℝ (Fin (ns.1 + 1)) // ∀ i, 0 < t.weights i}) =>
            SSet.toTop.map (SSet.yonedaEquiv.symm q.1.2.val)
              (⦋q.1.1⦌.toTopHomeo.symm q.2.val))
            ⟨b, interiorChart b.1 ⟨y,hy⟩⟩ from
          (hext a.1 a.2 ⟨x,ball_subset_closedBall hx⟩).symm.trans
            (hxy.symm.trans (hext b.1 b.2 ⟨y,ball_subset_closedBall hy⟩)))
      exact hab (congrArg (fun q => q.1) h)
    mapsTo' := by
      intro n s
      let I (m : ℕ) : Finset (S.nonDegenerate m) :=
        @Finset.univ _ (Fintype.ofFinite (S.nonDegenerate m))
      refine ⟨I, ?_⟩
      intro x hx
      cases n with
      | zero =>
        have hz : x = 0 := Subsingleton.elim _ _
        have hx0 : dist x 0 = 1 := hx
        rw [hz, dist_self] at hx0
        norm_num at hx0
      | succ n =>
        have hxc := sphere_subset_closedBall hx
        have hnot : ¬ ∀ i, 0 < (chart (n+1) ⟨x,hxc⟩).weights i := by
          rw [chartpos]
          simp only [mem_ball, mem_sphere] at hx ⊢
          rw [hx]
          exact lt_irrefl 1
        obtain ⟨i, v, hvdim, hv⟩ := realization_boundary_finite_nondegenerate_faces
          S n s.val (chart (n+1) ⟨x,hxc⟩) hnot
        let root := (SSet.S.mk (S.δ i s.val)).toN
        have hmem : extend (n+1) s x ∈
            cellmap root.dim ⟨root.simplex,root.nonDegenerate⟩ '' closedBall 0 1 := by
          change extend (n+1) s x ∈ extend root.dim ⟨root.simplex,root.nonDegenerate⟩ '' closedBall 0 1
          rw [himage]
          exact ⟨v, hv.trans (hext (n+1) s ⟨x,hxc⟩).symm⟩
        exact Set.mem_iUnion.mpr ⟨root.dim, Set.mem_iUnion.mpr ⟨by change root.dim ≤ n at hvdim; omega,
          Set.mem_iUnion.mpr ⟨⟨root.simplex,root.nonDegenerate⟩,
            Set.mem_iUnion.mpr ⟨(show (⟨root.simplex,root.nonDegenerate⟩ : S.nonDegenerate root.dim) ∈ I root.dim from by simp [I]),hmem⟩⟩⟩⟩
    closed' := by
      intro A hAC hA
      apply (realization_isClosed_iff_nondegenerate S A).mpr
      intro n s
      have hcA := hA n s
      change IsClosed (A ∩ extend n s '' closedBall 0 1) at hcA
      rw [himage] at hcA
      have hcont : Continuous (characteristic n s) :=
        (SSet.toTop.map (SSet.yonedaEquiv.symm s.val)).hom.continuous.comp
          ⦋n⦌.toTopHomeo.symm.continuous
      have hp : IsClosed (characteristic n s ⁻¹' A) := by
        have he : characteristic n s ⁻¹' (A ∩ range (characteristic n s)) =
            characteristic n s ⁻¹' A := by
          ext t
          simp only [Set.mem_preimage, Set.mem_inter_iff]
          exact ⟨fun ht => ht.1, fun ht => ⟨ht,⟨t,rfl⟩⟩⟩
        rw [← he]
        exact hcA.preimage hcont
      have hpre := hp.preimage ⦋n⦌.toTopHomeo.continuous
      convert hpre using 1
      ext t
      simp [characteristic]
    union' := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨n,s,t,ht⟩ := realization_nondegenerate_representation S x
      apply Set.mem_iUnion.mpr
      refine ⟨n,Set.mem_iUnion.mpr ⟨s,?_⟩⟩
      change x ∈ extend n s '' closedBall 0 1
      rw [himage]
      exact ⟨⦋n⦌.toTopHomeo t, by simpa [characteristic] using ht⟩ }

  have ht := realization_t1Space S
  have hclosed := realization_characteristic_isClosedMap S
  have ht2 : T2Space (SSet.toTop.obj S) := by
    let hreal : T2Space ℝ := inferInstance
    let := ht
    let D := Σ s : S.N, StdSimplex ℝ (Fin (s.dim + 1))
    let f : D → SSet.toTop.obj S := fun z =>
      SSet.toTop.map (SSet.yonedaEquiv.symm z.1.simplex)
        (⦋z.1.dim⦌.toTopHomeo.symm z.2)
    have hf : Continuous f := by
      apply continuous_sigma
      intro s
      exact (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous.comp
        ⦋s.dim⦌.toTopHomeo.symm.continuous
    have hs : Function.Surjective f := by
      intro x
      obtain ⟨n, s, t, ht⟩ := realization_nondegenerate_representation S x
      refine ⟨⟨SSet.N.mk s.val s.property, ⦋n⦌.toTopHomeo t⟩, ?_⟩
      simpa only [f, SSet.N.mk, Homeomorph.symm_apply_apply] using ht
    have hc : IsClosedMap f := by
      intro A hA
      have he : f '' A = ⋃ s : S.N,
          (fun t : StdSimplex ℝ (Fin (s.dim + 1)) => f ⟨s, t⟩) ''
            ((fun t : StdSimplex ℝ (Fin (s.dim + 1)) => (⟨s, t⟩ : D)) ⁻¹' A) := by
        ext y
        simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
        constructor
        · rintro ⟨⟨s, t⟩, ht, rfl⟩
          exact ⟨s, t, ht, rfl⟩
        · rintro ⟨s, t, ht, rfl⟩
          exact ⟨⟨s, t⟩, ht, rfl⟩
      rw [he]
      apply isClosed_iUnion_of_finite
      intro s
      exact hclosed s.dim s.simplex _ (hA.preimage continuous_sigmaMk)
    let hnormal : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
        [NormalSpace X] [T1Space Y] (f : X → Y), Continuous f →
        IsClosedMap f → Function.Surjective f → T2Space Y := by
      intro X Y _ _ _ _ f hf hc hs
  
      rw [t2Space_iff]
      intro x y hxy
      have hd : Disjoint (f ⁻¹' {x}) (f ⁻¹' {y}) := by
        apply Disjoint.preimage
        exact Set.disjoint_singleton.mpr hxy
      obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := normal_separation
        (isClosed_singleton.preimage hf) (isClosed_singleton.preimage hf) hd
      refine ⟨(f '' Uᶜ)ᶜ, (f '' Vᶜ)ᶜ,
        (hc _ hU.isClosed_compl).isOpen_compl,
        (hc _ hV.isClosed_compl).isOpen_compl, ?_, ?_, ?_⟩
      · rintro ⟨a, ha, rfl⟩
        exact ha (hxU (by simp))
      · rintro ⟨a, ha, rfl⟩
        exact ha (hyV (by simp))
      · rw [Set.disjoint_left]
        intro z hzU hzV
        obtain ⟨a, rfl⟩ := hs z
        have haU : a ∈ U := by
          by_contra ha
          exact hzU ⟨a, ha, rfl⟩
        have haV : a ∈ V := by
          by_contra ha
          exact hzV ⟨a, ha, rfl⟩
        exact Set.disjoint_left.mp hUV haU haV
    let : CompactSpace D := inferInstance
    let hpi : ∀ s : S.N, T2Space (Fin (s.dim + 1) → ℝ) := fun s => @Pi.t2Space (Fin (s.dim + 1)) (fun _ => ℝ) _ (fun _ => hreal)
    let hcell : ∀ s : S.N, T2Space (StdSimplex ℝ (Fin (s.dim + 1))) := fun s =>
      @Topology.IsEmbedding.t2Space _ _ _ _ (hpi s) _
        (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (s.dim + 1)))
    let : T2Space D := @Sigma.t2Space S.N (fun s => StdSimplex ℝ (Fin (s.dim + 1))) _ hcell
    let : NormalSpace D := NormalSpace.of_compactSpace_r1Space
    exact hnormal f hf hc hs
  refine ⟨cw, ht2, ?_⟩
  let := cw
  intro d
  change (⋃ n : ℕ, ⋃ (_ : n < d), ⋃ s : S.nonDegenerate n,
    extend n s '' closedBall 0 1) = Set.range (SSet.toTop.map (S.skeleton d).ι)
  ext x
  constructor
  · intro hx
    obtain ⟨n, hs⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hn, hs⟩ := Set.mem_iUnion.mp hs
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hs
    rw [himage] at hs
    obtain ⟨t, rfl⟩ := hs
    let a : (S.skeleton d).toSSet _⦋n⦌ := ⟨s.val, S.mem_skeleton s.val hn⟩
    refine ⟨SSet.toTop.map (SSet.yonedaEquiv.symm a) (⦋n⦌.toTopHomeo.symm t), ?_⟩
    change (SSet.toTop.map (SSet.yonedaEquiv.symm a) ≫
      SSet.toTop.map (S.skeleton d).ι) _ = _
    rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp]
    rfl
  · rintro ⟨p,rfl⟩
    obtain ⟨n,s,t,ht⟩ := realization_nondegenerate_representation (S.skeleton d).toSSet p
    let a : S.nonDegenerate n := ⟨s.val.val,
      ((S.skeleton d).mem_nonDegenerate_iff s.val).mp s.property⟩
    have hn : n < d := (S.mem_skeleton_obj_iff_of_nonDegenerate a d).mp s.val.property
    apply Set.mem_iUnion.mpr
    refine ⟨n,Set.mem_iUnion.mpr ⟨hn,Set.mem_iUnion.mpr ⟨a,?_⟩⟩⟩
    rw [himage]
    refine ⟨⦋n⦌.toTopHomeo t, ?_⟩
    rw [← ht]
    change _ = (SSet.toTop.map (SSet.yonedaEquiv.symm s.val) ≫
      SSet.toTop.map (S.skeleton d).ι) t
    rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp]
    simp [characteristic,a]

end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
