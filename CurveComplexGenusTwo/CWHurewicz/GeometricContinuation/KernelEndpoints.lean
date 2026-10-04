import CurveComplexGenusTwo.CWHurewicz.CWGeometricAlgebra
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.FiniteCarrierProved
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.ReducedSimplexFaceProbe
import CurveComplexGenusTwo.CWHurewicz.CWCellularHomotopyGlue
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.CanonicalSkeletonHeaders
import CurveComplexGenusTwo.CWHurewicz.SingularRealization.ActualLowerSkeletonNull
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.FiniteSubcomplexClosedEmbeddingHeader
import CurveComplexGenusTwo.CWHurewicz.CWBoundaryFaces
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.OrientedSimplexBoundary
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.CollapsedSimplexBoundaryProbe
import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.GenericChainExpansionProbe
import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
import Mathlib.LinearAlgebra.Span.Basic
import CurveComplexGenusTwo.CWHurewicz.SingularApproximation.UniformBoundaryNullCore
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
set_option maxHeartbeats 4000000
open Metric Topology CategoryTheory
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
private theorem kernelCoherentArbitraryRelativeStep {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [T2Space P] [Topology.CWComplex (Set.univ : Set P)]
    (f : C(P, X)) (n : ℕ) (g₀ : C(↥(skeletonBelow P n), X))
    (Hn : ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P n), P)))
      g₀) :
    ∃ g : C(↥(skeletonBelow P (n + 1)), X),
      ∃ Hnext : ContinuousMap.Homotopy
        (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P (n + 1)), P))) g,
        ∀ (t : unitInterval) (z : ↥(skeletonBelow P n)),
          Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
  have hdisk {X : Type} [TopologicalSpace X] (n : ℕ) (f : C(CellDisk n, X))
    (g : C(CellSphere n, X))
    (H : ContinuousMap.Homotopy
      (f.comp (⟨fun b => ⟨b.val, sphere_subset_closedBall b.property⟩,
        continuous_subtype_val.subtype_mk (fun b => sphere_subset_closedBall b.property)⟩ : C(CellSphere n, CellDisk n))) g) :
    ∃ G : C(unitInterval × CellDisk n, X),
      (∀ w : CellDisk n, G (0, w) = f w) ∧
      (∀ (t : unitInterval) (b : CellSphere n),
        G (t, ⟨b.val, sphere_subset_closedBall b.property⟩) = H (t, b)) := by
    have hret (n : ℕ) :
      ∃ r : C(unitInterval × CellDisk n, unitInterval × CellDisk n),
        (∀ p, (r p).1 = 0 ∨ (r p).2.val ∈ sphere (0 : Fin n → ℝ) 1) ∧
        (∀ w : CellDisk n, r (0, w) = (0, w)) ∧
        (∀ (t : unitInterval) (w : CellDisk n),
          w.val ∈ sphere (0 : Fin n → ℝ) 1 → r (t, w) = (t, w)) := by
      let d (p : unitInterval × CellDisk n) : ℝ := max ((2 - p.1.val) / 2) ‖p.2.val‖
      have hnorm (p : unitInterval × CellDisk n) : ‖p.2.val‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using p.2.property
      have hdpos (p : unitInterval × CellDisk n) : 0 < d p := by
        have ht := p.1.property
        have h := le_max_left ((2 - p.1.val) / 2) ‖p.2.val‖
        dsimp [d]
        linarith [ht.2]
      have hdle (p : unitInterval × CellDisk n) : d p ≤ 1 := by
        apply max_le
        · linarith [p.1.property.1]
        · exact hnorm p
      have hdnorm (p : unitInterval × CellDisk n) : ‖p.2.val‖ ≤ d p := le_max_right _ _
      have hdtime (p : unitInterval × CellDisk n) : (2 - p.1.val) / 2 ≤ d p := le_max_left _ _
      let τ (p : unitInterval × CellDisk n) : unitInterval :=
        ⟨2 - (2 - p.1.val) / d p, by
          constructor
          · have h : (2 - p.1.val) / d p ≤ 2 :=
              (div_le_iff₀ (hdpos p)).mpr (by linarith [hdtime p])
            linarith
          · have h : 1 ≤ (2 - p.1.val) / d p :=
              (le_div_iff₀ (hdpos p)).mpr (by linarith [hdle p, p.1.property.2])
            linarith⟩
      let w (p : unitInterval × CellDisk n) : CellDisk n :=
        ⟨(d p)⁻¹ • p.2.val, by
          rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr (hdpos p)), ← div_eq_inv_mul]
          exact (div_le_one (hdpos p)).mpr (hdnorm p)⟩
      have hdcont : Continuous d := by
        exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div_const 2).max
          ((continuous_norm.comp continuous_subtype_val).comp continuous_snd)
      have hτ : Continuous τ := by
        apply Continuous.subtype_mk
        exact continuous_const.sub
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).div hdcont
            (fun p => ne_of_gt (hdpos p)))
      have hw : Continuous w := by
        apply Continuous.subtype_mk
        exact (hdcont.inv₀ (fun p => ne_of_gt (hdpos p))).smul
          (continuous_subtype_val.comp continuous_snd)
      let r : C(unitInterval × CellDisk n, unitInterval × CellDisk n) :=
        ⟨fun p => (τ p, w p), hτ.prodMk hw⟩
      refine ⟨r, ?_, ?_, ?_⟩
      · intro p
        rcases le_total ‖p.2.val‖ ((2 - p.1.val) / 2) with h | h
        · left
          apply Subtype.ext
          change 2 - (2 - p.1.val) / d p = 0
          have hd : d p = (2 - p.1.val) / 2 := max_eq_left h
          rw [hd]
          have hp : 2 - p.1.val ≠ 0 := by linarith [p.1.property.2]
          field_simp
          ring
        · right
          have hd : d p = ‖p.2.val‖ := max_eq_right h
          change (d p)⁻¹ • p.2.val ∈ sphere 0 1
          rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr (hdpos p)), ← hd]
          exact inv_mul_cancel₀ (ne_of_gt (hdpos p))
      · intro z
        have hd : d (0, z) = 1 := by
          dsimp [d]
          rw [show (2 - (0 : ℝ)) / 2 = (1 : ℝ) by norm_num]
          exact max_eq_left (hnorm (0, z))
        apply Prod.ext
        · apply Subtype.ext
          change 2 - (2 - (0 : unitInterval).val) / d (0, z) = (0 : unitInterval).val
          rw [hd]
          norm_num
        · apply Subtype.ext
          change (d (0, z))⁻¹ • z.val = z.val
          rw [hd]
          simp
      · intro t z hz
        have hz' : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp hz
        have hd : d (t, z) = 1 := by
          dsimp [d]
          rw [hz']
          apply max_eq_right
          linarith [t.property.1]
        apply Prod.ext
        · apply Subtype.ext
          change 2 - (2 - t.val) / d (t, z) = t.val
          rw [hd]
          simp
        · apply Subtype.ext
          change (d (t, z))⁻¹ • z.val = z.val
          rw [hd]
          simp
    obtain ⟨r, hrange, hr0, hrs⟩ := hret n
    let A := {p : unitInterval × CellDisk n | p.1 = 0 ∨ p.2.val ∈ sphere (0 : Fin n → ℝ) 1}
    let s : Set A := {a | a.val.1 = 0}
    let t : Set A := {a | a.val.2.val ∈ sphere (0 : Fin n → ℝ) 1}
    let b₀ : C(s, X) := ⟨fun a => f a.val.val.2, by fun_prop⟩
    let b₁ : C(t, X) :=
      ⟨fun a => H (a.val.val.1, ⟨a.val.val.2.val, a.property⟩), by
        apply H.continuous.comp
        apply Continuous.prodMk
        · fun_prop
        · apply Continuous.subtype_mk
          fun_prop⟩
    have h01 (a : A) (hs : a ∈ s) (ht : a ∈ t) : b₀ ⟨a, hs⟩ = b₁ ⟨a, ht⟩ := by
      change f a.val.2 = H (a.val.1, ⟨a.val.2.val, ht⟩)
      rw [hs, H.apply_zero]
      rfl
    let S : Fin 2 → Set A := Fin.cons s (fun _ => t)
    let φ : ∀ j : Fin 2, C(S j, X) := Fin.cons b₀ (fun _ => b₁)
    have hφ : ∀ (i j : Fin 2) (a : A) (hi : a ∈ S i) (hj : a ∈ S j),
        φ i ⟨a, hi⟩ = φ j ⟨a, hj⟩ := by
      intro i j a hi hj
      fin_cases i <;> fin_cases j
      all_goals simp [S, φ] at hi hj ⊢
      all_goals first | rfl | exact h01 a hi hj | exact (h01 a hj hi).symm
    have hS : ⋃ j : Fin 2, S j = Set.univ := by
      ext a
      constructor
      · intro _; trivial
      · intro _
        rcases a.property with h | h
        · exact Set.mem_iUnion.mpr ⟨0, h⟩
        · exact Set.mem_iUnion.mpr ⟨1, h⟩
    let B : A → X := Set.liftCover S (fun j => φ j) hφ hS
    have hcl : ∀ j : Fin 2, IsClosed (S j) := by
      intro j
      fin_cases j
      · exact isClosed_singleton.preimage (by fun_prop)
      · exact isClosed_sphere.preimage (by fun_prop)
    have hcont : ∀ j : Fin 2, ContinuousOn B (S j) := by
      intro j
      rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (fun a : S j => B a.val)
      have heq : (fun a : S j => B a.val) = φ j := by
        funext a
        exact Set.liftCover_coe a
      rw [heq]
      exact (φ j).continuous
    let b : C(A, X) := ⟨B, (locallyFinite_of_finite S).continuous hS hcl hcont⟩
    let rA : C(unitInterval × CellDisk n, A) :=
      ⟨fun p => ⟨r p, hrange p⟩, r.continuous.subtype_mk hrange⟩
    refine ⟨b.comp rA, ?_, ?_⟩
    · intro w
      have he : rA (0, w) = (⟨(0, w), Or.inl rfl⟩ : A) := Subtype.ext (hr0 w)
      change B (rA (0, w)) = f w
      rw [he]
      dsimp only [B]
      rw [Set.liftCover_of_mem (i := (0 : Fin 2)) (hx := by rfl)]
      rfl
    · intro u v
      let w : CellDisk n := ⟨v.val, sphere_subset_closedBall v.property⟩
      have he : rA (u, w) = (⟨(u, w), Or.inr v.property⟩ : A) :=
        Subtype.ext (hrs u w v.property)
      change B (rA (u, w)) = H (u, v)
      rw [he]
      dsimp only [B]
      rw [Set.liftCover_of_mem (i := (1 : Fin 2)) (hx := v.property)]
      rfl
  have hglue {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [T2Space P] [Topology.CWComplex (Set.univ : Set P)]
    (f : C(P, X)) (n : ℕ) (g₀ : C(↥(skeletonBelow P n), X))
    (Hn : ContinuousMap.Homotopy
      ((f).comp
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(skeletonBelow P n), P)))
      g₀)
    (G : ∀ _i : Topology.CWComplex.cell (Set.univ : Set P) n,
      C(unitInterval × CellDisk n, X))
    (hboundary : ∀ i (b : CellSphere n) (t : unitInterval),
      G i (t, ⟨b.val, sphere_subset_closedBall b.property⟩) =
        Hn (t, attaching n i b))
    (hzero : ∀ i (w : CellDisk n),
      G i (0, w) = f (characteristicToStep n i w).val)
    : ∃ g : C(↥(skeletonBelow P (n + 1)), X),
      ∃ Hnext : ContinuousMap.Homotopy
        (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P (n + 1)), P))) g,
        ∀ (t : unitInterval) (z : ↥(skeletonBelow P n)),
          Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
    have hcover (z : ↥(skeletonBelow P (n + 1))) :
        (∃ y : ↥(skeletonBelow P n), skeletonInclusion (Nat.le_succ n) y = z) ∨
        (∃ (i : Topology.CWComplex.cell (Set.univ : Set P) n)
          (w : CellDisk n), characteristicToStep n i w = z) := by
      rcases Set.mem_iUnion.mp z.property with ⟨m, hm⟩
      rcases Set.mem_iUnion.mp hm with ⟨hmn, hm⟩
      rcases Set.mem_iUnion.mp hm with ⟨i, hi⟩
      by_cases hmn' : m < n
      · left
        refine ⟨⟨z.val, Set.mem_iUnion.mpr ⟨m,
          Set.mem_iUnion.mpr ⟨hmn', Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩⟩, ?_⟩
        apply Subtype.ext
        rfl
      · right
        have hmeq : m = n := by omega
        subst m
        rcases hi with ⟨w, hw, heq⟩
        refine ⟨i, ⟨w, hw⟩, ?_⟩
        apply Subtype.ext
        exact heq
    let F : C(↥(skeletonBelow P n), C(unitInterval, X)) :=
      (⟨fun p : ↥(skeletonBelow P n) × unitInterval => Hn (p.2, p.1),
        Hn.continuous.comp continuous_swap⟩ :
        C(↥(skeletonBelow P n) × unitInterval, X)).curry
    let D : ∀ i : Topology.CWComplex.cell (Set.univ : Set P) n,
        C(CellDisk n, C(unitInterval, X)) := fun i =>
      (⟨fun p : CellDisk n × unitInterval => G i (p.2, p.1),
        (G i).continuous.comp continuous_swap⟩ :
        C(CellDisk n × unitInterval, X)).curry
    have hcompat : ∀ i (b : CellSphere n),
        F (attaching n i b) =
          D i ⟨b.val, sphere_subset_closedBall b.property⟩ := by
      intro i b
      apply ContinuousMap.ext
      intro t
      exact (hboundary i b t).symm
    obtain ⟨h, ⟨hold, hcell⟩, _⟩ :=
      cwStepUniversal_of_t2 n F D hcompat
    let K : C(unitInterval × ↥(skeletonBelow P (n + 1)), X) :=
      ⟨fun p => h p.2 p.1,
        (ContinuousMap.continuous_uncurry_of_continuous h).comp continuous_swap⟩
    have Kold (t : unitInterval) (z : ↥(skeletonBelow P n)) :
        K (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
      change (h (skeletonInclusion (Nat.le_succ n) z)) t = Hn (t, z)
      simpa [F] using congrFun (congrArg DFunLike.coe (hold z)) t
    have Kcell (t : unitInterval)
        (i : Topology.CWComplex.cell (Set.univ : Set P) n) (w : CellDisk n) :
        K (t, characteristicToStep n i w) = G i (t, w) := by
      change (h (characteristicToStep n i w)) t = G i (t, w)
      simpa [D] using congrFun (congrArg DFunLike.coe (hcell i w)) t
    have Kzero (z : ↥(skeletonBelow P (n + 1))) : K (0, z) = f z.val := by
      rcases hcover z with ⟨y, rfl⟩ | ⟨i, w, rfl⟩
      · rw [Kold]
        exact Hn.apply_zero y
      · rw [Kcell]
        exact hzero i w
    let g : C(↥(skeletonBelow P (n + 1)), X) :=
      K.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
    refine ⟨g, ⟨K, Kzero, ?_⟩, Kold⟩
    intro z
    rfl
  classical
  have hc (i : Topology.CWComplex.cell (Set.univ : Set P) n) :
      ∃ G : C(unitInterval × CellDisk n, X),
        (∀ (b : CellSphere n) (t : unitInterval),
          G (t, ⟨b.val, sphere_subset_closedBall b.property⟩) = Hn (t, attaching n i b)) ∧
        (∀ w : CellDisk n, G (0, w) = f (characteristicToStep n i w).val) := by
    let fd : C(CellDisk n, X) := f.comp (characteristic n i)
    let Hc : ContinuousMap.Homotopy
        (fd.comp (⟨fun b => ⟨b.val, sphere_subset_closedBall b.property⟩,
          continuous_subtype_val.subtype_mk (fun b => sphere_subset_closedBall b.property)⟩ :
          C(CellSphere n, CellDisk n))) (g₀.comp (attaching n i)) :=
      (Hn.compContinuousMap (attaching n i)).cast (by ext b; rfl) rfl
    obtain ⟨G, hG0, hGs⟩ := hdisk n fd (g₀.comp (attaching n i)) Hc
    refine ⟨G, ?_, ?_⟩
    · intro b t
      have he := hGs t b
      change G (t, ⟨b.val, sphere_subset_closedBall b.property⟩) =
        Hn (t, attaching n i b) at he
      exact he
    · intro w
      exact hG0 w
  choose G hG using hc
  exact hglue f n g₀ Hn G (fun i b t => (hG i).1 b t) (fun i w => (hG i).2 w)


private theorem kernelFiniteRelativeHEP {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [T2Space P] [Topology.CWComplex (Set.univ : Set P)]
    (f : C(P, X)) (n m : ℕ) (hnm : n ≤ m)
    (hall : ∀ z : P, z ∈ skeletonBelow P m)
    (g₀ : C(↥(skeletonBelow P n), X))
    (Hn : ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P n), P))) g₀) :
    ∃ g : C(P, X), ∃ H : ContinuousMap.Homotopy f g,
      ∀ (t : unitInterval) (z : ↥(skeletonBelow P n)), H (t, z.val) = Hn (t, z) := by
  have hs (m : ℕ) (h : n ≤ m) :
      ∃ g : C(↥(skeletonBelow P m), X),
      ∃ H : ContinuousMap.Homotopy
        (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P m), P))) g,
      ∀ (t : unitInterval) (z : ↥(skeletonBelow P n)),
        H (t, skeletonInclusion h z) = Hn (t, z) := by
    induction m, h using Nat.le_induction with
    | base =>
      refine ⟨g₀, Hn, ?_⟩
      intro t z
      rfl
    | @succ m h ih =>
      obtain ⟨g, H, he⟩ := ih
      obtain ⟨g', H', he'⟩ := kernelCoherentArbitraryRelativeStep f m g H
      refine ⟨g', H', ?_⟩
      intro t z
      have hz : skeletonInclusion (Nat.le_trans h (Nat.le_succ m)) z =
          skeletonInclusion (Nat.le_succ m) (skeletonInclusion h z) := by rfl
      rw [hz, he', he]
  obtain ⟨gm, Hm, he⟩ := hs m hnm
  let j : C(P, ↥(skeletonBelow P m)) := ⟨fun z => ⟨z, hall z⟩,
    continuous_id.subtype_mk _⟩
  let g := gm.comp j
  let H := (Hm.compContinuousMap j).cast (by ext z; rfl) rfl
  refine ⟨g, H, ?_⟩
  intro t z
  change Hm (t, j z.val) = Hn (t, z)
  have hz : j z.val = skeletonInclusion hnm z := by rfl
  rw [hz, he]


open SingularApproximation
open scoped Simplicial
private theorem kernelFiniteLowerCollapse {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (S : SSet.{0}) [S.Finite] (k : ℕ) (x : X)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k + 2 → Subsingleton (HomotopyGroup.Pi j X x))
    (f : C(SSet.toTop.obj S, X)) :
    ∃ g : C(SSet.toTop.obj S, X), Nonempty (ContinuousMap.Homotopy f g) ∧
      ∀ a : SSet.toTop.obj (S.skeleton (k + 2)).toSSet,
        g (SSet.toTop.map (S.skeleton (k + 2)).ι a) = x := by
  obtain ⟨cw, ht2, hskel⟩ := finite_realization_canonical_skeleton S
  let := cw
  have := ht2
  let P := SSet.toTop.obj S
  let A := SSet.toTop.obj (S.skeleton (k + 2)).toSSet
  let i : C(A, P) := (SSet.toTop.map (S.skeleton (k + 2)).ι).hom
  have hi := finite_realization_subcomplex_closedEmbedding S (S.skeleton (k + 2))
  let e : A ≃ₜ ↥(skeletonBelow P (k + 2)) :=
    hi.toIsEmbedding.toHomeomorph.trans (Homeomorph.setCongr (hskel (k + 2)).symm)
  have he (a : A) : (e a).val = i a := by rfl
  obtain ⟨HL⟩ := actual_lower_skeleton_map_nullhomotopic S k x hlower f
  have hstart : (f.comp i).comp (⟨e.symm, e.symm.continuous⟩ : C(_, A)) =
      f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P (k + 2)), P)) := by
    ext z
    apply congrArg f
    change i (e.symm z) = z.val
    rw [← he, Homeomorph.apply_symm_apply]
  let Hn : ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P (k + 2)), P)))
      (ContinuousMap.const (↥(skeletonBelow P (k + 2))) x) := (HL.compContinuousMap (⟨e.symm, e.symm.continuous⟩ : C(_, A))).cast
    hstart (by ext z; rfl)
  obtain ⟨d, hd⟩ := S.hasDimensionLT_of_finite
  have := hd
  let m := max (k + 2) d
  have hall (z : P) : z ∈ skeletonBelow P m := by
    rw [hskel m]
    obtain ⟨n, s, t, ht⟩ := realization_nondegenerate_representation S z
    have hn : n < d := SSet.dim_lt_of_nonDegenerate S s d
    let a : (S.skeleton m).toSSet _⦋n⦌ :=
      ⟨s.val, S.mem_skeleton s.val (lt_of_lt_of_le hn (Nat.le_max_right _ _))⟩
    refine ⟨SSet.toTop.map (SSet.yonedaEquiv.symm a) t, ?_⟩
    change (SSet.toTop.map (SSet.yonedaEquiv.symm a) ≫ SSet.toTop.map (S.skeleton m).ι) t = z
    rw [← SSet.toTop.map_comp, SSet.yonedaEquiv_symm_comp]
    exact ht
  obtain ⟨g, H, hH⟩ := kernelFiniteRelativeHEP f (k + 2) m (Nat.le_max_left _ _) hall
    (ContinuousMap.const _ x) Hn
  refine ⟨g, ⟨H⟩, ?_⟩
  intro a
  rw [← H.apply_one (i a)]
  rw [← he, hH, Hn.apply_one]
  rfl
end CurveComplexGenusTwo.CWHurewicz.FiniteSingularCarrier
open CategoryTheory CategoryTheory.Limits Convexity Topology
open scoped Simplicial unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private theorem face_loops_force_lower_skeleton_basepoint {X : Type} [TopologicalSpace X] (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (smap : C(StdSimplex ℝ (Fin (k + 4)), X))
    (f : Fin (k + 4) → GenLoop (Fin (k + 2)) X x)
    (hf : ∀ i a, f i a = smap ((e a).map (SimplexCategory.δ i))) :
    ∀ t (i j : Fin (k + 4)), i ≠ j → t.weights i = 0 → t.weights j = 0 → smap t = x := by
  intro t i j hij hi hj
  have hr : t ∈ Set.range (StdSimplex.map (SimplexCategory.δ i)) :=
    (StdSimplex.mem_range_map_iff (SimplexCategory.δ i) t).mpr (by
      intro z hz
      have hrange : Set.range (SimplexCategory.δ i) = ({i} : Set (Fin (k + 4)))ᶜ := Fin.range_succAbove i
      have hzi : z = i := by simpa only [hrange, Set.mem_compl_iff, Set.mem_singleton_iff, not_not] using hz
      simpa only [hzi] using hi)
  obtain ⟨u, hu⟩ := hr
  have hjrange : j ∈ Set.range i.succAbove := by
    rw [Fin.range_succAbove]
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using Ne.symm hij
  obtain ⟨l, hl⟩ := hjrange
  have hmap : (u.map (SimplexCategory.δ i)).weights (i.succAbove l) = u.weights l := by
    rw [StdSimplex.weights_map]
    exact Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective _ _
  have huz : u.weights l = 0 := by
    rw [← hmap, hl, hu]
    exact hj
  have hub : ¬ ∀ z, 0 < u.weights z := by
    intro h
    have hpos := h l
    rw [huz] at hpos
    exact lt_irrefl _ hpos
  have ha : e.symm u ∈ Cube.boundary (Fin (k + 2)) := by
    apply (he _).mpr
    rwa [e.apply_symm_apply]
  have h := hf i (e.symm u)
  rw [e.apply_symm_apply, hu] at h
  exact h.symm.trans (GenLoop.boundary (f i) _ ha)
-- Actual free-chain map to the based homotopy group, with boundaries killed
-- by the proved geometric simplex relation, rather than an assumed relation.
private theorem chainToPiBoundary {X : Type} [TopologicalSpace X]
    (S : SSet.{0}) (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (phi : S ⟶ TopCat.toSSet.obj (TopCat.of X))
    (hbound : ∀ (s : S _⦋k + 2⦌) (u : StdSimplex ℝ (Fin (k + 3))),
      (¬ ∀ i, 0 < u.weights i) →
        TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k + 2⦌) (phi.app (.op ⦋k + 2⦌) s) u = x) :
    let F : S _⦋k + 2⦌ → GenLoop (Fin (k + 2)) X x := fun s =>
      ⟨(TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k + 2⦌) (phi.app (.op ⦋k + 2⦌) s)).comp
          ⟨e,e.continuous⟩,
        fun a ha => hbound s (e a) ((he a).mp ha)⟩
    ∃ alpha : (S.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 2) →ₗ[ℤ]
        Additive (HomotopyGroup.Pi (k + 2) X x),
      (∀ s, alpha ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) =
        (Additive.ofMul : HomotopyGroup.Pi (k + 2) X x → _) ⟦F s⟧) ∧
      ∀ b : (S.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 3),
        alpha ((S.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 3) (k + 2) b) = 0 := by
  intro F
  let A := ModuleCat.of ℤ (Additive (HomotopyGroup.Pi (k + 2) X x))
  let value (s : S _⦋k + 2⦌) : A :=
    (Additive.ofMul : HomotopyGroup.Pi (k + 2) X x → _) ⟦F s⟧
  let f (s : S _⦋k + 2⦌) : ModuleCat.of ℤ ℤ ⟶ A :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ A (value s))
  let cocone := Cofan.mk A f
  let alpha := (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) (k + 2)).desc cocone
  have hfac (s : S _⦋k + 2⦌) : S.ιChainComplex s ≫ alpha = f s :=
    (S.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) (k + 2)).fac cocone ⟨s⟩
  have hgen (s : S _⦋k + 2⦌) :
      alpha.hom ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) = value s := by
    have h := congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ A => f.hom 1) (hfac s)
    exact h.trans (LinearMap.toSpanSingleton_apply_one ℤ A (value s))
  have hsum (s : S _⦋k + 3⦌) :
      ∑ i : Fin (k + 4), ((-1 : ℤ) ^ i.val) • value (S.δ i s) = 0 := by
    let smap := TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k + 3⦌) (phi.app (.op ⦋k + 3⦌) s)
    have hf (i : Fin (k + 4)) (a) : F (S.δ i s) a = smap ((e a).map (SimplexCategory.δ i)) := by
      have hn := congrArg (fun h : S _⦋k + 3⦌ ⟶ (TopCat.toSSet.obj (TopCat.of X)) _⦋k + 2⦌ => h s)
        (SimplicialObject.δ_naturality phi i)
      change phi.app (.op ⦋k + 2⦌) (S.δ i s) =
        (TopCat.toSSet.obj (TopCat.of X)).δ i (phi.app (.op ⦋k + 3⦌) s) at hn
      change TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k + 2⦌)
        (phi.app (.op ⦋k + 2⦌) (S.δ i s)) (e a) = _
      rw [hn]
      exact TopCat.toSSetObjEquiv_δ_apply _ i (e a)
    have hlow := face_loops_force_lower_skeleton_basepoint k x e he smap
      (fun i => F (S.δ i s)) hf
    have hrelation := oriented_simplex_face_classes_product_eq_one k x e he smap hlow
      (fun i => F (S.δ i s)) hf
    have hadd := congrArg (Additive.ofMul : HomotopyGroup.Pi (k + 2) X x →
      Additive (HomotopyGroup.Pi (k + 2) X x)) hrelation
    change ∑ i : Fin (k + 4), ((-1 : ℤ) ^ i.val) •
      (Additive.ofMul : HomotopyGroup.Pi (k + 2) X x → _) ⟦F (S.δ i s)⟧ = 0
    rw [ofMul_prod, ofMul_one] at hadd
    convert hadd using 1
    apply Finset.sum_congr rfl
    intro i hi
    exact (ofMul_zpow (α := HomotopyGroup.Pi (k + 2) X x) ((-1 : ℤ) ^ i.val)
      (⟦F (S.δ i s)⟧ : HomotopyGroup.Pi (k + 2) X x)).symm
  have hgenerator (s : S _⦋k + 3⦌) :
      alpha.hom ((S.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 3) (k + 2)
        ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)) = 0 := by
    have hd := congrArg (fun h : ModuleCat.of ℤ ℤ ⟶
        (S.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 2) => h.hom 1)
      (S.ιChainComplex_d (ModuleCat.of ℤ ℤ) s)
    change (S.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 3) (k + 2)
        ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) = _ at hd
    rw [hd]
    simp only [ModuleCat.hom_sum,ModuleCat.hom_zsmul,LinearMap.sum_apply]
    change alpha.hom (∑ i : Fin (k + 4),
      (-1 : ℤ) ^ i.val • ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) (S.δ i s)).hom 1)) = 0
    calc
      _ = ∑ i : Fin (k + 4), alpha.hom
          ((-1 : ℤ) ^ i.val • ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) (S.δ i s)).hom 1)) :=
        map_sum alpha.hom _ _
      _ = ∑ i : Fin (k + 4), (-1 : ℤ) ^ i.val • value (S.δ i s) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (map_zsmul alpha.hom ((-1 : ℤ) ^ i.val)
          ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) (S.δ i s)).hom 1)).trans
          (congrArg (fun z : A => ((-1 : ℤ) ^ i.val) • z) (hgen (S.δ i s)))
      _ = 0 := hsum s
  refine ⟨alpha.hom,hgen,?_⟩
  intro b
  change alpha.hom (((S.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 3) (k + 2)).hom b) = 0
  obtain ⟨c,hc⟩ := FiniteSingularCarrier.chain_expansion S (k + 3) b
  rw [hc]
  calc
    _ = ∑ s ∈ c.support, alpha.hom
        (((S.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 3) (k + 2)).hom
          (c s • ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1))) := by
      rw [map_sum]
      exact map_sum alpha.hom _ _
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      let d := ((S.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 3) (k + 2)).hom
      let u := (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1
      exact (congrArg alpha.hom (map_zsmul d (c s) u)).trans
        ((map_zsmul alpha.hom (c s) (d u)).trans
          ((congrArg (fun z : A => c s • z) (hgenerator s)).trans (smul_zero _)))
private theorem collapsedRealizationChainToPi {X : Type} [TopologicalSpace X]
    (S : SSet.{0}) (k : ℕ) (x : X)
    (e : (Fin (k + 2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k + 3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k + 2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (g : C(SSet.toTop.obj S, X))
    (hg : ∀ a : SSet.toTop.obj (S.skeleton (k + 2)).toSSet,
      g (SSet.toTop.map (S.skeleton (k + 2)).ι a) = x) :
    let phi := sSetTopAdj.unit.app S ≫ TopCat.toSSet.map (TopCat.ofHom g)
    ∃ hbound : ∀ (s : S _⦋k + 2⦌) (u : StdSimplex ℝ (Fin (k + 3))),
      (¬ ∀ i, 0 < u.weights i) →
        TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k + 2⦌)
          (phi.app (.op ⦋k + 2⦌) s) u = x,
    let F : S _⦋k + 2⦌ → GenLoop (Fin (k + 2)) X x := fun s =>
      ⟨(TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k + 2⦌)
        (phi.app (.op ⦋k + 2⦌) s)).comp ⟨e,e.continuous⟩,
        fun a ha => hbound s (e a) ((he a).mp ha)⟩
    ∃ alpha : (S.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 2) →ₗ[ℤ]
        Additive (HomotopyGroup.Pi (k + 2) X x),
      (∀ s, alpha ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) =
        (Additive.ofMul : HomotopyGroup.Pi (k + 2) X x → _) ⟦F s⟧) ∧
      ∀ b : (S.chainComplex (ModuleCat.of ℤ ℤ)).X (k + 3),
        alpha ((S.chainComplex (ModuleCat.of ℤ ℤ)).d (k + 3) (k + 2) b) = 0 := by
  intro phi
  have hbound (s : S _⦋k + 2⦌) (u : StdSimplex ℝ (Fin (k + 3)))
      (hu : ¬ ∀ i, 0 < u.weights i) :
      TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k + 2⦌)
        (phi.app (.op ⦋k + 2⦌) s) u = x := by
    change g (TopCat.toSSetObjEquiv (SSet.toTop.obj S) (.op ⦋k + 2⦌)
      ((sSetTopAdj.unit.app S).app (.op ⦋k + 2⦌) s) u) = x
    rw [FiniteSingularCarrier.unit_characteristic_apply]
    exact FiniteSingularCarrier.collapsedSimplex_boundary S (k + 1) x g hg s u hu
  exact ⟨hbound, chainToPiBoundary S k x e he phi hbound⟩

end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
open CategoryTheory Convexity Topology
open scoped Simplicial unitInterval
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private def simplexCharacteristic (S : SSet.{0}) (n : ℕ) (s : S _⦋n⦌) :
    C(StdSimplex ℝ (Fin (n+1)), SSet.toTop.obj S) :=
  (SSet.toTop.map (SSet.yonedaEquiv.symm s)).hom.comp ⟨⦋n⦌.toTopHomeo.symm,by fun_prop⟩
private theorem constantCharacteristic (S : SSet.{0}) (n : ℕ) (v : S _⦋0⦌)
    (t : StdSimplex ℝ (Fin (n+1))) :
    simplexCharacteristic S n (S.map (⦋n⦌.const ⦋0⦌ 0).op v) t =
      SSet.toTop.map (SSet.yonedaEquiv.symm v) default := by
  have hc : SSet.yonedaEquiv.symm (S.map (⦋n⦌.const ⦋0⦌ 0).op v) =
      SSet.const (X := Δ[n]) v := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    rfl
  change SSet.toTop.map (SSet.yonedaEquiv.symm _) (⦋n⦌.toTopHomeo.symm t) = _
  rw [hc, ← SSet.comp_const (SSet.stdSimplex.map (⦋n⦌.const ⦋0⦌ 0)) v,
    ← SSet.yonedaEquiv_symm_zero v, Functor.map_comp]
  apply congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm v))
  exact Subsingleton.elim _ _
private theorem nullhomotopyFromUniformPath {Y : Type} [TopologicalSpace Y]
    (n : ℕ) (hn : 1 ≤ n) (y z : Y) (p : Path y z)
    (f : GenLoop (Fin n) Y y) (g : GenLoop (Fin n) Y z)
    (A : ContinuousMap.Homotopy f.val g.val)
    (Ab : ∀ t a, a ∈ Cube.boundary (Fin n) → A (t,a) = p t)
    (B : GenLoop.Homotopic g GenLoop.const) : GenLoop.Homotopic f GenLoop.const := by
  obtain ⟨B⟩ := B
  let C := A.trans B.toHomotopy
  let path := p.trans (Path.refl z)
  apply SingularApproximation.Next.cubeLoop_nullhomotopy_uniform_boundary_path
    n hn y z path f C.toContinuousMap
  · exact C.map_zero_left
  · exact C.map_one_left
  · intro t a ha
    change (A.trans B.toHomotopy) (t,a) = (p.trans (Path.refl z)) t
    rw [ContinuousMap.Homotopy.trans_apply,Path.trans_apply]
    split_ifs
    · exact Ab _ a ha
    · exact (B.eq_fst _ ha).trans (GenLoop.boundary g a ha)
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
private theorem finiteSphericalSimplexKernel {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (S : SSet.{0}) [S.Finite] (k : ℕ) (x : X)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k+2 → Subsingleton (HomotopyGroup.Pi j X x))
    (e : (Fin (k+2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k+3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k+2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (P : C(SSet.toTop.obj S,X)) (v : S _⦋0⦌) (q : S _⦋k+2⦌)
    (hz : P (SSet.toTop.map (SSet.yonedaEquiv.symm v) default) = x)
    (hq : ∀ t : StdSimplex ℝ (Fin (k+3)), (¬ ∀ i, 0 < t.weights i) →
      simplexCharacteristic S (k+2) q t =
        SSet.toTop.map (SSet.yonedaEquiv.symm v) default)
    (f : GenLoop (Fin (k+2)) X x)
    (hf : f.val = P.comp ((simplexCharacteristic S (k+2) q).comp ⟨e,e.continuous⟩))
    (B : (S.chainComplex (ModuleCat.of ℤ ℤ)).X (k+3))
    (hB : (S.chainComplex (ModuleCat.of ℤ ℤ)).d (k+3) (k+2) B =
      (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) q).hom 1 -
      (S.ιChainComplex (R := ModuleCat.of ℤ ℤ)
        (S.map (⦋k+2⦌.const ⦋0⦌ 0).op v)).hom 1) :
    GenLoop.Homotopic f GenLoop.const := by
  let z := SSet.toTop.map (SSet.yonedaEquiv.symm v) default
  obtain ⟨g,⟨H⟩,hg⟩ := FiniteSingularCarrier.kernelFiniteLowerCollapse S k x hlower P
  have hgz : g z = x := by
    let w : (S.skeleton (k+2)).toSSet _⦋0⦌ := ⟨v,S.mem_skeleton v (by omega)⟩
    have h := hg (SSet.toTop.map (SSet.yonedaEquiv.symm w) default)
    change g ((SSet.toTop.map (SSet.yonedaEquiv.symm w) ≫
      SSet.toTop.map (S.skeleton (k+2)).ι) default) = x at h
    rw [←Functor.map_comp,SSet.yonedaEquiv_symm_comp] at h
    exact h
  let phi := sSetTopAdj.unit.app S ≫ TopCat.toSSet.map (TopCat.ofHom g)
  obtain ⟨hbound,alpha,hgen,hkill⟩ := collapsedRealizationChainToPi S k x e he g hg
  let F (s : S _⦋k+2⦌) : GenLoop (Fin (k+2)) X x :=
    ⟨(TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)
      (phi.app (.op ⦋k+2⦌) s)).comp ⟨e,e.continuous⟩,
      fun a ha => hbound s (e a) ((he a).mp ha)⟩
  have hF (s : S _⦋k+2⦌) : (F s).val =
      g.comp ((simplexCharacteristic S (k+2) s).comp ⟨e,e.continuous⟩) := by
    ext a
    change g (TopCat.toSSetObjEquiv (SSet.toTop.obj S) (.op ⦋k+2⦌)
      ((sSetTopAdj.unit.app S).app (.op ⦋k+2⦌) s) (e a)) = _
    rw [FiniteSingularCarrier.unit_characteristic_apply]
    rfl
  let c := S.map (⦋k+2⦌.const ⦋0⦌ 0).op v
  have hFc : F c = GenLoop.const := by
    ext a
    change F c a = x
    rw [show F c a = g (simplexCharacteristic S (k+2) c (e a)) from
      congrArg (fun h : C((Fin (k+2) → unitInterval),X) => h a) (hF c)]
    rw [constantCharacteristic]
    exact hgz
  have hc : alpha ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) c).hom 1) = 0 := by
    rw [hgen]
    change (Additive.ofMul : HomotopyGroup.Pi (k+2) X x → _) ⟦F c⟧ = 0
    rw [hFc,←HomotopyGroup.one_def]
    rfl
  have hzero := hkill B
  rw [hB,alpha.map_sub,hc,sub_zero,hgen] at hzero
  change (Additive.ofMul : HomotopyGroup.Pi (k+2) X x → _) ⟦F q⟧ = 0 at hzero
  change (⟦F q⟧ : HomotopyGroup.Pi (k+2) X x) = (1 : HomotopyGroup.Pi (k+2) X x) at hzero
  have hnull : GenLoop.Homotopic (F q) GenLoop.const :=
    Quotient.exact (hzero.trans (HomotopyGroup.one_def (N := Fin (k+2)) (X := X) (x := x)))
  let path : Path x x := {
    toFun := fun t => H (t,z)
    continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
    source' := (H.apply_zero z).trans hz
    target' := (H.apply_one z).trans hgz }
  let u := (simplexCharacteristic S (k+2) q).comp (⟨e,e.continuous⟩ : C(_, _))
  let A : ContinuousMap.Homotopy f.val (F q).val :=
    (H.compContinuousMap u).cast hf.symm (hF q).symm
  apply nullhomotopyFromUniformPath (k+2) (by omega) x x path f (F q) A ?_ hnull
  intro t a ha
  change H (t,simplexCharacteristic S (k+2) q (e a)) = H (t,z)
  rw [hq (e a) ((he a).mp ha)]

private theorem characteristicMap (S : SSet.{0}) {n m : ℕ}
    (a : ⦋n⦌ ⟶ ⦋m⦌) (s : S _⦋m⦌) (t : StdSimplex ℝ (Fin (n+1))) :
    simplexCharacteristic S m s (StdSimplex.map a t) =
      simplexCharacteristic S n (S.map a.op s) t := by
  have hy : SSet.stdSimplex.map a ≫ SSet.yonedaEquiv.symm s =
      SSet.yonedaEquiv.symm (S.map a.op s) := (uliftYonedaEquiv_symm_map a.op s).symm
  change SSet.toTop.map (SSet.yonedaEquiv.symm s)
    (⦋m⦌.toTopHomeo.symm (StdSimplex.map a t)) = _
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply]
  change (SSet.toTop.map (SSet.stdSimplex.map a) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm s)) (⦋n⦌.toTopHomeo.symm t) = _
  rw [←Functor.map_comp,hy]
  rfl
private theorem reducedSimplexFillingKernel {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] (k : ℕ) (x : X)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k+2 → Subsingleton (HomotopyGroup.Pi j X x))
    (e : (Fin (k+2) → unitInterval) ≃ₜ StdSimplex ℝ (Fin (k+3)))
    (he : ∀ a, a ∈ Cube.boundary (Fin (k+2)) ↔ ¬ ∀ i, 0 < (e a).weights i)
    (qmap : C(StdSimplex ℝ (Fin (k+3)),X))
    (hq : ∀ t, (¬ ∀ i, 0 < t.weights i) → qmap t=x)
    (f : GenLoop (Fin (k+2)) X x) (hf : f.val=qmap.comp ⟨e,e.continuous⟩)
    (b : (C X).X (k+3))
    (hb : (C X).d (k+3) (k+2) b =
      (singularChainsFinsuppIso (TopCat.of X) (k+2)).inv
        (Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)).symm qmap) 1 -
         Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)).symm
           (ContinuousMap.const _ x)) 1)) : GenLoop.Homotopic f GenLoop.const := by
  classical
  let T := TopCat.toSSet.obj (TopCat.of X)
  let qs : T _⦋k+2⦌ := (TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)).symm qmap
  let co := (singularChainsFinsuppIso (TopCat.of X) (k+3)).hom b
  let D := FiniteSingularCarrier.carrier T (k+3) co
  let A : T.Subcomplex := ⨆ i : Bool, if i then SSet.Subcomplex.ofSimplex qs else D
  have hD : D ≤ A := by simpa [A] using (le_iSup (fun i : Bool =>
    if i then SSet.Subcomplex.ofSimplex qs else D) false)
  have hqA : SSet.Subcomplex.ofSimplex qs ≤ A := by simpa [A] using (le_iSup
    (fun i : Bool => if i then SSet.Subcomplex.ofSimplex qs else D) true)
  have hfinite : SSet.Finite A.toSSet := by
    apply (SSet.finite_iSup_iff _).mpr
    intro i
    cases i
    · exact FiniteSingularCarrier.carrier_finite T (k+3) co
    · change SSet.Finite (SSet.Subcomplex.ofSimplex qs).toSSet
      infer_instance
  letI := hfinite
  let S := A.toSSet
  let Q : S _⦋k+2⦌ := ⟨qs,hqA _ (SSet.Subcomplex.mem_ofSimplex_obj qs)⟩
  let v : S _⦋0⦌ := S.map (⦋0⦌.const ⦋k+2⦌ 0).op Q
  let xv := (TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋0⦌)).symm (ContinuousMap.const _ x)
  have hv : A.ι.app (.op ⦋0⦌) v = xv := by
    apply (TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋0⦌)).injective
    ext t
    change qmap (StdSimplex.map (⦋0⦌.const ⦋k+2⦌ 0) t) = x
    apply hq
    intro hp
    have hz : (StdSimplex.map (⦋0⦌.const ⦋k+2⦌ 0) t).weights (1 : Fin (k+3)) = 0 := by
      rw [StdSimplex.weights_map]
      exact Finsupp.mapDomain_of_notMem_range _ _ (by
        rintro ⟨j,hj⟩
        change (0 : Fin (k+3)) = 1 at hj
        have hh := congrArg Fin.val hj
        have hh1 : ((1 : Fin (k+3)) : ℕ)=1 := by
          rw [Fin.val_one']
          exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_zero,hh1] at hh
        omega)
    have hpos := hp (1 : Fin (k+3))
    rw [hz] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  let c := S.map (⦋k+2⦌.const ⦋0⦌ 0).op v
  have hc : A.ι.app (.op ⦋k+2⦌) c =
      (TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)).symm (ContinuousMap.const _ x) := by
    have hn := congrArg (fun h : S _⦋0⦌ ⟶ T _⦋k+2⦌ => h v)
      (A.ι.naturality (⦋k+2⦌.const ⦋0⦌ 0).op)
    change T.map (⦋k+2⦌.const ⦋0⦌ 0).op (A.ι.app _ v) = A.ι.app _ c at hn
    rw [hv] at hn
    exact hn.symm
  let P := (SSet.toTop.map A.ι ≫ sSetTopAdj.counit.app (TopCat.of X)).hom
  have hu : sSetTopAdj.unit.app S ≫ TopCat.toSSet.map (TopCat.ofHom P) = A.ι := by
    have hn := sSetTopAdj.unit.naturality A.ι
    change A.ι ≫ sSetTopAdj.unit.app T =
      sSetTopAdj.unit.app S ≫ TopCat.toSSet.map (SSet.toTop.map A.ι) at hn
    dsimp [P]
    rw [Functor.map_comp,←Category.assoc,←hn,Category.assoc,
      sSetTopAdj.right_triangle_components,Category.comp_id]
  have hP (n : ℕ) (s : S _⦋n⦌) (t : StdSimplex ℝ (Fin (n+1))) :
      P (simplexCharacteristic S n s t) =
        TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌) (A.ι.app _ s) t := by
    have h := congrArg (fun h : S ⟶ T =>
      TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌) (h.app _ s) t) hu
    change P (TopCat.toSSetObjEquiv (SSet.toTop.obj S) (.op ⦋n⦌)
      ((sSetTopAdj.unit.app S).app _ s) t) = _ at h
    rw [FiniteSingularCarrier.unit_characteristic_apply] at h
    exact h
  have hz : P (SSet.toTop.map (SSet.yonedaEquiv.symm v) default) = x := by
    have h := hP 0 v default
    rw [hv] at h
    exact h
  have hfaces (i : Fin (k+3)) : S.δ i Q = S.map (⦋k+1⦌.const ⦋0⦌ 0).op v := by
    apply Subtype.ext
    change T.δ i qs = T.map (⦋k+1⦌.const ⦋0⦌ 0).op (A.ι.app _ v)
    rw [hv]
    exact reducedSimplex_face (k+1) x qmap hq i
  have hgeom (t : StdSimplex ℝ (Fin (k+3))) (ht : ¬ ∀ i,0<t.weights i) :
      simplexCharacteristic S (k+2) Q t =
        SSet.toTop.map (SSet.yonedaEquiv.symm v) default := by
    obtain ⟨i,u,hu⟩ := SingularApproximation.simplex_boundary_face_representation (k+1) t ht
    rw [←hu,characteristicMap]
    change simplexCharacteristic S (k+1) (S.δ i Q) u = _
    rw [hfaces,constantCharacteristic]
  let inc := SSet.Subcomplex.homOfLE hD
  let B := (SSet.chainComplexMap inc (ModuleCat.of ℤ ℤ)).f (k+3)
    (FiniteSingularCarrier.liftChain T (k+3) co)
  let push := SSet.chainComplexMap A.ι (ModuleCat.of ℤ ℤ)
  have hpush : push.f (k+3) B=b := by
    have hmap : SSet.chainComplexMap inc (ModuleCat.of ℤ ℤ) ≫ push =
        SSet.chainComplexMap D.ι (ModuleCat.of ℤ ℤ) := by
      change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map inc ≫
        ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map A.ι = _
      rw [←Functor.map_comp,SSet.Subcomplex.homOfLE_ι]
    have h := congrArg (fun h => h.f (k+3) (FiniteSingularCarrier.liftChain T (k+3) co)) hmap
    exact h.trans ((FiniteSingularCarrier.liftChain_push (TopCat.of X) (k+3) co).trans
      ((singularChainsFinsuppIso (TopCat.of X) (k+3)).hom_inv_id_apply b))
  have hB : (S.chainComplex (ModuleCat.of ℤ ℤ)).d (k+3) (k+2) B =
      (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) Q).hom 1 -
      (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) c).hom 1 := by
    apply FiniteSingularCarrier.inclusion_component_injective T A (k+2)
    have hd := congrArg (fun h => h B) (push.comm (k+3) (k+2)).symm
    change push.f (k+2) ((S.chainComplex (ModuleCat.of ℤ ℤ)).d (k+3) (k+2) B) =
      (C X).d (k+3) (k+2) (push.f (k+3) B) at hd
    rw [hpush,hb] at hd
    have hgen (s : S _⦋k+2⦌) : (push.f (k+2)).hom
        ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) =
        (T.ιChainComplex (R := ModuleCat.of ℤ ℤ) (A.ι.app _ s)).hom 1 :=
      congrArg (fun h : ModuleCat.of ℤ ℤ ⟶ _ => h.hom 1)
        (SSet.ι_chainComplexMap_f S T A.ι (ModuleCat.of ℤ ℤ) s)
    have hright : push.f (k+2)
        ((S.ιChainComplex (R := ModuleCat.of ℤ ℤ) Q).hom 1 -
         (S.ιChainComplex (R := ModuleCat.of ℤ ℤ) c).hom 1) =
        (T.ιChainComplex (R := ModuleCat.of ℤ ℤ) qs).hom 1 -
        (T.ιChainComplex (R := ModuleCat.of ℤ ℤ) (A.ι.app _ c)).hom 1 :=
      ((push.f (k+2)).hom.map_sub _ _).trans (congrArg₂ (· - ·) (hgen Q) (hgen c))
    rw [hd,hright,hc]
    apply (ModuleCat.mono_iff_injective (singularChainsFinsuppIso (TopCat.of X) (k+2)).hom).mp inferInstance
    rw [Iso.inv_hom_id_apply,map_sub]
    exact (congrArg₂ (· - ·)
      (singularChainsFinsuppIso_generator (TopCat.of X) (k+2) qs)
      (singularChainsFinsuppIso_generator (TopCat.of X) (k+2)
        ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)).symm
          (ContinuousMap.const _ x)))).symm
  apply finiteSphericalSimplexKernel S k x hlower e he P v Q hz hgeom f ?_ B hB
  rw [hf]
  ext a
  exact (hP (k+2) Q (e a)).symm

private theorem kernelCubeDiskChart (n : ℕ) :
  ∃ e : (Fin n → unitInterval) ≃ₜ CellDisk n,
    ∀ a, a ∈ Cube.boundary (Fin n) ↔ (e a).val ∉ ball (0 : Fin n → ℝ) 1 := by
  let f (a : Fin n → unitInterval) : CellDisk n :=
    ⟨fun i => 2 * (a i).val - 1, by
      rw [mem_closedBall, dist_zero_right]
      apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro i
      change abs (2 * (a i).val - 1) ≤ 1
      rw [abs_le]
      constructor <;> linarith [(a i).property.1, (a i).property.2]⟩
  let g (w : CellDisk n) : Fin n → unitInterval := fun i =>
    ⟨(w.val i + 1) / 2, by
      have hw : ‖w.val‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using w.property
      have hi : abs (w.val i) ≤ 1 := norm_le_pi_norm w.val i |>.trans hw
      rw [abs_le] at hi
      constructor <;> linarith [hi.1, hi.2]⟩
  let e : (Fin n → unitInterval) ≃ₜ CellDisk n := {
    toFun := f
    invFun := g
    left_inv := by
      intro a
      funext i
      apply Subtype.ext
      change ((2 * (a i).val - 1) + 1) / 2 = (a i).val
      ring
    right_inv := by
      intro w
      apply Subtype.ext
      funext i
      change 2 * ((w.val i + 1) / 2) - 1 = w.val i
      ring
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro i
      exact ((continuous_subtype_val.comp (continuous_apply i)).const_mul 2).sub continuous_const
    continuous_invFun := by
      apply continuous_pi
      intro i
      apply Continuous.subtype_mk
      exact (((continuous_apply i).comp continuous_subtype_val).add continuous_const).div_const 2 }
  refine ⟨e, ?_⟩
  intro a
  constructor
  · rintro ⟨i, hi | hi⟩ hball
    all_goals
      have hh : ‖(e a).val‖ < 1 := mem_ball_zero_iff.mp hball
      have hcoord := (norm_le_pi_norm (e a).val i).trans_lt hh
      change abs (2 * (a i).val - 1) < 1 at hcoord
      norm_num [hi] at hcoord
  · intro hnot
    by_contra hbound
    apply hnot
    rw [mem_ball_zero_iff]
    apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
    intro i
    have h0 : a i ≠ 0 := fun h => hbound ⟨i, Or.inl h⟩
    have h1 : a i ≠ 1 := fun h => hbound ⟨i, Or.inr h⟩
    have hi0 : 0 < (a i).val := lt_of_le_of_ne (a i).property.1
      (fun h => h0 (Subtype.ext h.symm))
    have hi1 : (a i).val < 1 := lt_of_le_of_ne (a i).property.2
      (fun h => h1 (Subtype.ext h))
    change abs (2 * (a i).val - 1) < 1
    rw [abs_lt]
    constructor <;> linarith
private theorem kernelCubeSimplexChart (n : ℕ) :
    ∃ e : (Fin n → unitInterval) ≃ₜ StdSimplex ℝ (Fin (n+1)),
      ∀ a, a ∈ Cube.boundary (Fin n) ↔ ¬ ∀ i,0<(e a).weights i := by
  obtain ⟨e,he⟩ := kernelCubeDiskChart n
  obtain ⟨h,hh⟩ := SingularApproximation.standardSimplex_diskChart n
  refine ⟨e.trans h,?_⟩
  intro a
  constructor
  · intro ha hp
    exact (he a).mp ha ((hh (e a)).mp hp)
  · intro ha
    apply (he a).mpr
    intro hb
    exact ha ((hh (e a)).mpr hb)


theorem fundamental_filling_to_nullhomotopy {X : Type} [TopologicalSpace X]
    [CWComplex (Set.univ : Set X)] [T2Space X] [PathConnectedSpace X]
    (k : ℕ) (x : X)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k + 2 → Subsingleton (HomotopyGroup.Pi j X x))
    (f : GenLoop (Fin (k + 2)) X x)
    (s : (C (CubeSphere (k + 2))).cycles (k + 2))
    (hs : cycleClass (k + 2) s = AbsolutePacket.fundamentalClass k)
    (b : (C X).X (k + 3))
    (hb : (C X).d (k + 3) (k + 2) b =
      (actualSingularFunctor.map (TopCat.ofHom (loopSphereMap (k + 2) x f))).f
        (k + 2) ((C (CubeSphere (k + 2))).iCycles (k + 2) s)) :
    GenLoop.Homotopic f GenLoop.const := by
  classical
  obtain ⟨e,he⟩ := kernelCubeSimplexChart (k+2)
  let y : CubeSphere (k+2) := Quotient.mk (cubeBoundarySetoid (k+2)) (fun _ => 0)
  let q0 : C(StdSimplex ℝ (Fin (k+3)), CubeSphere (k+2)) :=
    ⟨fun t => Quotient.mk (cubeBoundarySetoid (k+2)) (e.symm t),
      continuous_coinduced_rng.comp e.symm.continuous⟩
  have hq0 (t : StdSimplex ℝ (Fin (k+3))) (ht : ¬ ∀ i,0<t.weights i) : q0 t=y := by
    apply Quotient.sound
    refine Or.inr ⟨(he (e.symm t)).mpr ?_,⟨⟨0,by omega⟩,Or.inl rfl⟩⟩
    simpa using ht
  let p := TopCat.ofHom (loopSphereMap (k+2) x f)
  let phi := actualSingularFunctor.map p
  have hy : loopSphereMap (k+2) x f y=x := by
    rw [AbsolutePacket.sphereMap_mk]
    exact GenLoop.boundary f _ ⟨⟨0,by omega⟩,Or.inl rfl⟩
  let ws := HomologicalComplex.cyclesMap phi (k+2) s
  have his : (C X).iCycles (k+2) ws =
      phi.f (k+2) ((C (CubeSphere (k+2))).iCycles (k+2) s) :=
    congrArg (fun h => h s) (HomologicalComplex.cyclesMap_i phi (k+2))
  have hws : cycleClass (k+2) ws=0 :=
    (cycleClass_zero_iff_boundary (k+2) ws).mpr ⟨b,hb.trans his.symm⟩
  have hgen : (AbsolutePacket.HF (k+2)).map p (AbsolutePacket.fundamentalClass k)=0 := by
    have hn := congrArg (fun h => h s) (HomologicalComplex.homologyπ_naturality phi (k+2))
    change (AbsolutePacket.HF (k+2)).map p (cycleClass (k+2) s) = cycleClass (k+2) ws at hn
    rw [hs,hws] at hn
    exact hn
  obtain ⟨u,hu⟩ := reducedSimplex_cycle (k+1) y q0 hq0
  let sphereIso := SphereProbe.cubeSphereTopIso (k+2) (by omega)
  let coefficient : ℤ := sphereIso.hom (cycleClass (k+2) u)
  have huclass : cycleClass (k+2) u = coefficient • AbsolutePacket.fundamentalClass k := by
    have hi := congrArg (fun h => h (cycleClass (k+2) u)) sphereIso.hom_inv_id
    change sphereIso.inv (sphereIso.hom (cycleClass (k+2) u)) = cycleClass (k+2) u at hi
    have hc : sphereIso.inv coefficient=coefficient • sphereIso.inv 1 := by
      rw [←map_zsmul]
      congr 1
      simp
    exact hi.symm.trans hc
  let w := HomologicalComplex.cyclesMap phi (k+2) u
  have hw : cycleClass (k+2) w=0 := by
    have hn := congrArg (fun h => h u) (HomologicalComplex.homologyπ_naturality phi (k+2))
    change (AbsolutePacket.HF (k+2)).map p (cycleClass (k+2) u) = cycleClass (k+2) w at hn
    rw [huclass,map_zsmul,hgen,zsmul_zero] at hn
    exact hn.symm
  obtain ⟨b',hb'⟩ := (cycleClass_zero_iff_boundary (k+2) w).mp hw
  let qmap := (loopSphereMap (k+2) x f).comp q0
  have hqmap (t) (ht : ¬ ∀ i,0<t.weights i) : qmap t=x := by
    change loopSphereMap (k+2) x f (q0 t)=x
    rw [hq0 t ht,hy]
  have hf : f.val=qmap.comp ⟨e,e.continuous⟩ := by
    ext a
    change f a=loopSphereMap (k+2) x f (Quotient.mk (cubeBoundarySetoid (k+2)) (e.symm (e a)))
    rw [e.symm_apply_apply,AbsolutePacket.sphereMap_mk]
  have hiw : (C X).iCycles (k+2) w =
      (singularChainsFinsuppIso (TopCat.of X) (k+2)).inv
        (Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)).symm qmap) 1 -
         Finsupp.single ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋k+2⦌)).symm
           (ContinuousMap.const _ x)) 1) := by
    have hi := congrArg (fun h => h u) (HomologicalComplex.cyclesMap_i phi (k+2))
    change (C X).iCycles (k+2) w =phi.f (k+2) ((C (CubeSphere (k+2))).iCycles (k+2) u) at hi
    rw [hi,hu,reducedSimplex_push,hy]
  exact reducedSimplexFillingKernel k x hlower e he qmap hqmap f hf b' (hb'.trans hiw)

end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains

namespace CurveComplexGenusTwo.CWHurewicz.CWFirstDegree
open AbsolutePacket
theorem geometric_injective {X : Type} [TopologicalSpace X]
    [Topology.CWComplex (Set.univ : Set X)] [T2Space X] [PathConnectedSpace X]
    (k : ℕ) (x : X)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k + 2 → Subsingleton (HomotopyGroup.Pi j X x)) :
    Function.Injective (hurewiczFunction k x) := by
  have hkernel (a : HomotopyGroup.Pi (k+2) X x)
      (ha : hurewiczFunction k x a=0) : a=(1 : HomotopyGroup.Pi (k+2) X x) := by
    induction a using Quotient.inductionOn with
    | _ f =>
      obtain ⟨s,hs⟩ := CWGeometricChains.fundamentalCycle_exists k
      let phi := actualSingularFunctor.map (TopCat.ofHom (loopSphereMap (k+2) x f))
      let w := HomologicalComplex.cyclesMap phi (k+2) s
      have hw : CWGeometricChains.cycleClass (k+2) w=0 :=
        (CWGeometricChains.pushed_fundamental_cycle_class k x f s hs).trans ha
      obtain ⟨b,hb⟩ := (CWGeometricChains.cycleClass_zero_iff_boundary (k+2) w).mp hw
      have hi : (CWGeometricChains.C X).iCycles (k+2) w =
          phi.f (k+2) ((CWGeometricChains.C (CubeSphere (k+2))).iCycles (k+2) s) :=
        congrArg (fun h => h s) (HomologicalComplex.cyclesMap_i phi (k+2))
      have hnull := CWGeometricChains.fundamental_filling_to_nullhomotopy
        k x hlower f s hs b (hb.trans hi)
      exact (Quotient.sound hnull).trans (HomotopyGroup.one_def (N := Fin (k+2)) (X := X) (x := x)).symm
  have hinj : Function.Injective (hurewiczMap k x) :=
    (injective_iff_map_eq_one (hurewiczMap k x)).mpr (fun a ha => hkernel a ha)
  intro a b hab
  apply hinj
  exact hab

end CurveComplexGenusTwo.CWHurewicz.CWFirstDegree
