import CurveComplexGenusTwo.CWHurewicz.GeometricContinuation.GenericCellularGlueHeader
import CurveComplexGenusTwo.CWHurewicz.CWBoundaryFaces
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
open Metric Topology
open scoped unitInterval Topology.Homotopy
set_option maxHeartbeats 4000000
noncomputable section
namespace CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
open FiniteSingularCarrier
theorem finite_low_dimensional_map_nullhomotopic
    {X P : Type} [TopologicalSpace X] [TopologicalSpace P]
    [CWComplex (Set.univ : Set P)] [T2Space P] [CompactSpace P]
    [PathConnectedSpace X] (k : ℕ) (x : X)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k + 2 → Subsingleton (HomotopyGroup.Pi j X x))
    (hdim : ∀ m : ℕ, k + 2 ≤ m → IsEmpty (Topology.CWComplex.cell (Set.univ : Set P) m))
    (f : C(P, X)) :
    Nonempty (ContinuousMap.Homotopy f (ContinuousMap.const P x)) := by
  have hpositive {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [T2Space P] [Topology.CWComplex (Set.univ : Set P)]
    (f : C(P, X)) (x : X) (k n : ℕ) (hn : 1 ≤ n) (hlt : n < k + 2)
    (hlower : ∀ j : ℕ, 1 ≤ j → j < k + 2 → Subsingleton (HomotopyGroup.Pi j X x))
    (Hn : ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P n), P)))
      ((ContinuousMap.const P x).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P n), P)))) :
    ∃ Hnext : ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P (n + 1)), P)))
      ((ContinuousMap.const P x).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P (n + 1)), P))),
      ∀ (t : unitInterval) (z : ↥(skeletonBelow P n)),
        Hnext (t, skeletonInclusion (Nat.le_succ n) z) = Hn (t, z) := by
    have hfill {X : Type} [TopologicalSpace X] (k n : ℕ) (hn : 1 ≤ n)
      (hlt : n < k + 2) (x : X)
      (hlower : ∀ j : ℕ, 1 ≤ j → j < k + 2 → Subsingleton (HomotopyGroup.Pi j X x))
      (f : C(CellSphere (n + 1), X)) (z : CellSphere (n + 1)) (hz : f z = x) :
      ∃ F : C(CellDisk (n + 1), X), ∀ b : CellSphere (n + 1),
        F ⟨b.val, sphere_subset_closedBall b.property⟩ = f b := by
      have hpoint (a b : CellSphere (n + 1)) :
          ∃ h : CellSphere (n + 1) ≃ₜ CellSphere (n + 1), h a = b := by
        let e := cellSphereEuclideanHomeomorph (n + 1)
        let v := (e a).val
        let w := (e b).val
        have hv : ‖v‖ = 1 := by simp [v]
        have hw : ‖w‖ = 1 := by simp [w]
        let r : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) := Submodule.reflection (ℝ ∙ (v - w))ᗮ
        have hr : r v = w := Submodule.reflection_sub (hv.trans hw.symm)
        let rh : ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≃ₜ
            ↥(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := {
          toFun := fun z => ⟨r z.val, by
            rw [mem_sphere_zero_iff_norm, r.norm_map]
            exact mem_sphere_zero_iff_norm.mp z.property⟩
          invFun := fun z => ⟨r.symm z.val, by
            rw [mem_sphere_zero_iff_norm, r.symm.norm_map]
            exact mem_sphere_zero_iff_norm.mp z.property⟩
          left_inv := fun z => Subtype.ext (r.symm_apply_apply z.val)
          right_inv := fun z => Subtype.ext (r.apply_symm_apply z.val)
          continuous_toFun := (r.continuous.comp continuous_subtype_val).subtype_mk (fun z => by
            change r z.val ∈ sphere 0 1
            rw [mem_sphere_zero_iff_norm, r.norm_map]
            exact mem_sphere_zero_iff_norm.mp z.property)
          continuous_invFun := (r.symm.continuous.comp continuous_subtype_val).subtype_mk (fun z => by
            change r.symm z.val ∈ sphere 0 1
            rw [mem_sphere_zero_iff_norm, r.symm.norm_map]
            exact mem_sphere_zero_iff_norm.mp z.property) }
        refine ⟨e.trans (rh.trans e.symm), ?_⟩
        apply e.injective
        change e (e.symm (rh (e a))) = e b
        rw [Homeomorph.apply_symm_apply]
        apply Subtype.ext
        exact hr
      have hnull (u : C(WhiteheadCubeSphere n, X))
          (hbase : u (Quotient.mk (whiteheadCubeBoundarySetoid n) (fun _ => 0)) = x) :
          ContinuousMap.Homotopic u (ContinuousMap.const (WhiteheadCubeSphere n) x) := by
        let q : C((Fin n → unitInterval), WhiteheadCubeSphere n) :=
          ⟨Quotient.mk (whiteheadCubeBoundarySetoid n), continuous_coinduced_rng⟩
        have hboundary (a : Fin n → unitInterval) (ha : a ∈ Cube.boundary (Fin n)) :
            u (q a) = x := by
          rw [← hbase]
          apply congrArg u
          apply Quotient.sound
          exact Or.inr ⟨ha, ⟨⟨0, by omega⟩, Or.inl rfl⟩⟩
        let p : GenLoop (Fin n) X x := ⟨u.comp q, hboundary⟩
        have hp : GenLoop.Homotopic p (GenLoop.const : GenLoop (Fin n) X x) :=
          Quotient.exact ((hlower n hn hlt).allEq
            (⟦p⟧ : HomotopyGroup.Pi n X x) (⟦GenLoop.const⟧ : HomotopyGroup.Pi n X x))
        obtain ⟨K⟩ := hp
        have hq : IsQuotientMap q := ⟨⟨rfl⟩, Quotient.mk_surjective⟩
        let L : unitInterval × WhiteheadCubeSphere n → X := fun z =>
          Quotient.lift (fun a => K (z.1, a)) (by
            intro a b hab
            rcases hab with hab | ⟨ha, hb⟩
            · exact congrArg (fun c => K (z.1, c)) hab
            · exact (K.eq_fst z.1 ha).trans
                ((GenLoop.boundary p a ha).trans
                  (GenLoop.boundary p b hb).symm) |>.trans
                (K.eq_fst z.1 hb).symm) z.2
        have hL : Continuous L := hq.continuous_lift_prod_right K.continuous
        refine ⟨{ toContinuousMap := ⟨L, hL⟩, map_zero_left := ?_, map_one_left := ?_ }⟩
        · intro z
          induction z using Quotient.inductionOn with
          | _ a => exact K.apply_zero a
        · intro z
          induction z using Quotient.inductionOn with
          | _ a => exact K.apply_one a
      let g₀ := whiteheadCubeSphereCellHomeo n hn
      let q₀ : WhiteheadCubeSphere n :=
        Quotient.mk (whiteheadCubeBoundarySetoid n) (fun _ => 0)
      obtain ⟨h, hh⟩ := hpoint (g₀ q₀) z
      let g := g₀.trans h
      let u : C(WhiteheadCubeSphere n, X) := f.comp ⟨g, g.continuous⟩
      have hu : ContinuousMap.Homotopic u
          (ContinuousMap.const (WhiteheadCubeSphere n) x) := by
        apply hnull u
        change f (h (g₀ q₀)) = x
        rw [hh]
        exact hz
      have hf : ContinuousMap.Homotopic f (ContinuousMap.const (CellSphere (n + 1)) x) := by
        have hh' := hu.comp (ContinuousMap.Homotopic.refl
          (⟨g.symm, g.symm.continuous⟩ : C(CellSphere (n + 1), WhiteheadCubeSphere n)))
        convert hh' using 1 <;> ext b <;> simp [u]
      exact cellSphereMap_extends_cellDisk (n + 1) f x (Classical.choice hf)
    have hbound {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
      [Topology.CWComplex (Set.univ : Set P)] (f : C(P, X)) (x : X) (n : ℕ)
      (Hn : ContinuousMap.Homotopy
        (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P n), P)))
        ((ContinuousMap.const P x).comp
          (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P n), P))))
      (i : Topology.CWComplex.cell (Set.univ : Set P) n) :
      ∃ B : C(↥(cylinderBoundary n), X),
        (∀ w : CellDisk n,
          B ⟨(0, w), cylinderBoundary_zero n w⟩ = f (characteristic n i w)) ∧
        (∀ w : CellDisk n, B ⟨(1, w), cylinderBoundary_one n w⟩ = x) ∧
        (∀ (b : CellSphere n) (t : unitInterval),
          B ⟨(t, ⟨b.val, sphere_subset_closedBall b.property⟩), cylinderBoundary_side n t b⟩ =
            Hn (t, attaching n i b)) := by
      let b₀ : C(↥(cylinderFaceZero n), X) := f.comp (cylinderFaceZeroMap n i)
      let b₁ : C(↥(cylinderFaceOne n), X) := ContinuousMap.const _ x
      let b₂ : C(↥(cylinderFaceSide n), X) :=
        ⟨fun p => Hn (p.val.val.1, attaching n i ⟨p.val.val.2.val, p.property⟩), by
          apply Hn.continuous.comp
          apply Continuous.prodMk
          · exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
          · apply (attaching n i).continuous.comp
            apply Continuous.subtype_mk
            exact (continuous_subtype_val.comp continuous_snd).comp
              (continuous_subtype_val.comp continuous_subtype_val)⟩
      have h01 (a : ↥(cylinderBoundary n)) (ha : a ∈ cylinderFaceZero n)
          (hb : a ∈ cylinderFaceOne n) : b₀ ⟨a, ha⟩ = b₁ ⟨a, hb⟩ := by
        exact (zero_ne_one (ha.symm.trans hb)).elim
      have h02 (a : ↥(cylinderBoundary n)) (ha : a ∈ cylinderFaceZero n)
          (hc : a ∈ cylinderFaceSide n) : b₀ ⟨a, ha⟩ = b₂ ⟨a, hc⟩ := by
        change f (characteristic n i a.val.2) = Hn (a.val.1, attaching n i ⟨a.val.2.val, hc⟩)
        rw [ha, Hn.apply_zero]
        rfl
      have h12 (a : ↥(cylinderBoundary n)) (hb : a ∈ cylinderFaceOne n)
          (hc : a ∈ cylinderFaceSide n) : b₁ ⟨a, hb⟩ = b₂ ⟨a, hc⟩ := by
        change x = Hn (a.val.1, attaching n i ⟨a.val.2.val, hc⟩)
        rw [hb, Hn.apply_one]
        rfl
      let S : Fin 3 → Set ↥(cylinderBoundary n) :=
        Fin.cons (cylinderFaceZero n) (Fin.cons (cylinderFaceOne n) (fun _ => cylinderFaceSide n))
      let φ : ∀ j : Fin 3, C(S j, X) := Fin.cons b₀ (Fin.cons b₁ (fun _ => b₂))
      have hφ : ∀ (j l : Fin 3) (a : ↥(cylinderBoundary n)) (hj : a ∈ S j) (hl : a ∈ S l),
          φ j ⟨a, hj⟩ = φ l ⟨a, hl⟩ := by
        intro j l a hj hl
        fin_cases j <;> fin_cases l
        all_goals simp [S, φ] at hj hl ⊢
        all_goals first | rfl | exact h01 a hj hl | exact (h01 a hl hj).symm |
          exact h02 a hj hl | exact (h02 a hl hj).symm |
          exact h12 a hj hl | exact (h12 a hl hj).symm
      have hS : ⋃ j : Fin 3, S j = Set.univ := by
        ext a
        constructor
        · intro _; trivial
        · intro _
          have ha : a ∈ cylinderFaceZero n ∪ cylinderFaceOne n ∪ cylinderFaceSide n :=
            (cylinderFaces_cover n).symm ▸ Set.mem_univ a
          rcases ha with (ha | ha) | ha
          · exact Set.mem_iUnion.mpr ⟨0, ha⟩
          · exact Set.mem_iUnion.mpr ⟨1, ha⟩
          · exact Set.mem_iUnion.mpr ⟨2, ha⟩
      let B : ↥(cylinderBoundary n) → X := Set.liftCover S (fun j => φ j) hφ hS
      have hcl : ∀ j : Fin 3, IsClosed (S j) := by
        intro j
        fin_cases j <;> simp [S]
        · exact cylinderFaceZero_closed n
        · exact cylinderFaceOne_closed n
        · exact cylinderFaceSide_closed n
      have hcont : ∀ j : Fin 3, ContinuousOn B (S j) := by
        intro j
        rw [continuousOn_iff_continuous_domRestrict]
        change Continuous (fun a : S j => B a.val)
        have heq : (fun a : S j => B a.val) = φ j := by
          funext a
          exact Set.liftCover_coe a
        rw [heq]
        exact (φ j).continuous
      refine ⟨⟨B, (locallyFinite_of_finite S).continuous hS hcl hcont⟩, ?_, ?_, ?_⟩
      · intro w
        change B _ = _
        dsimp only [B]
        rw [Set.liftCover_of_mem (i := (0 : Fin 3)) (hx := by rfl)]
        rfl
      · intro w
        change B _ = _
        dsimp only [B]
        rw [Set.liftCover_of_mem (i := (1 : Fin 3)) (hx := by rfl)]
        rfl
      · intro b t
        change B _ = _
        dsimp only [B]
        rw [Set.liftCover_of_mem (i := (2 : Fin 3)) (hx := b.property)]
        rfl
    have hglue {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
        [T2Space P] [Topology.CWComplex (Set.univ : Set P)]
      (f : C(P, X)) (x₀ : X) (n : ℕ)
      (Hn : ContinuousMap.Homotopy
        ((f).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow P n), P)))
        ((ContinuousMap.const P x₀).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow P n), P))))
      (G : ∀ _i : Topology.CWComplex.cell (Set.univ : Set P) n,
        C(unitInterval × CellDisk n, X))
      (hboundary : ∀ i (b : CellSphere n) (t : unitInterval),
        G i (t, ⟨b.val, sphere_subset_closedBall b.property⟩) =
          Hn (t, attaching n i b))
      (hzero : ∀ i (w : CellDisk n),
        G i (0, w) = f (characteristicToStep n i w).val)
      (hone : ∀ i (w : CellDisk n), G i (1, w) = x₀) :
      ∃ Hnext : ContinuousMap.Homotopy
        ((f).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow P (n + 1)), P)))
        ((ContinuousMap.const P x₀).comp
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(skeletonBelow P (n + 1)), P))),
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
      have Kone (z : ↥(skeletonBelow P (n + 1))) : K (1, z) = x₀ := by
        rcases hcover z with ⟨y, rfl⟩ | ⟨i, w, rfl⟩
        · rw [Kold]
          exact Hn.apply_one y
        · rw [Kcell]
          exact hone i w
      exact ⟨⟨K, Kzero, Kone⟩, Kold⟩
    classical
    have hc (i : Topology.CWComplex.cell (Set.univ : Set P) n) :
        ∃ G : C(unitInterval × CellDisk n, X),
          (∀ (b : CellSphere n) (t : unitInterval),
            G (t, ⟨b.val, sphere_subset_closedBall b.property⟩) = Hn (t, attaching n i b)) ∧
          (∀ w : CellDisk n, G (0, w) = f (characteristicToStep n i w).val) ∧
          (∀ w : CellDisk n, G (1, w) = x) := by
      obtain ⟨B, hB0, hB1, hBs⟩ := hbound f x n Hn i
      let e := cylinderBoundarySphereHomeomorph n
      let u : C(CellSphere (n + 1), X) := B.comp ⟨e.symm, e.symm.continuous⟩
      let w₀ : CellDisk n := ⟨0, by simp⟩
      let a : ↥(cylinderBoundary n) := ⟨(1, w₀), cylinderBoundary_one n w₀⟩
      have hu : u (e a) = x := by
        change B (e.symm (e a)) = x
        rw [Homeomorph.symm_apply_apply]
        exact hB1 w₀
      obtain ⟨F, hF⟩ := hfill k n hn hlt x hlower u (e a) hu
      let G : C(unitInterval × CellDisk n, X) := F.comp (cylinderToDisk n)
      have hb (p : ↥(cylinderBoundary n)) : G p.val = B p := by
        calc
          G p.val = F ⟨(e p).val, sphere_subset_closedBall (e p).property⟩ := rfl
          _ = u (e p) := hF (e p)
          _ = B p := by simp [u]
      refine ⟨G, ?_, ?_, ?_⟩
      · intro b t
        rw [hb ⟨(t, ⟨b.val, sphere_subset_closedBall b.property⟩), cylinderBoundary_side n t b⟩]
        exact hBs b t
      · intro w
        rw [hb ⟨(0, w), cylinderBoundary_zero n w⟩]
        exact hB0 w
      · intro w
        rw [hb ⟨(1, w), cylinderBoundary_one n w⟩]
        exact hB1 w
    choose G hG using hc
    exact hglue f x n Hn G (fun i b t => (hG i).1 b t)
      (fun i w => (hG i).2.1 w) (fun i w => (hG i).2.2 w)
  have hzero {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [T2Space P] [Topology.CWComplex (Set.univ : Set P)] [PathConnectedSpace X]
    (f : C(P, X)) (x : X)
    (Hn : ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P 0), P)))
      ((ContinuousMap.const P x).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P 0), P)))) :
    ∃ Hnext : ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P 1), P)))
      ((ContinuousMap.const P x).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P 1), P))),
      ∀ (t : unitInterval) (z : ↥(skeletonBelow P 0)),
        Hnext (t, skeletonInclusion (Nat.le_succ 0) z) = Hn (t, z) := by
    let w₀ : CellDisk 0 := ⟨0, by simp⟩
    have w_unique (w : CellDisk 0) : w = w₀ := by
      apply Subtype.ext
      funext j
      exact Fin.elim0 j
    let p (i : Topology.CWComplex.cell (Set.univ : Set P) 0) :
        Path (f (characteristicToStep 0 i w₀).val) x :=
      (PathConnectedSpace.joined _ _).somePath
    let G : ∀ _i : Topology.CWComplex.cell (Set.univ : Set P) 0,
        C(unitInterval × CellDisk 0, X) := fun i =>
      ⟨fun q => p i q.1, (p i).continuous.comp continuous_fst⟩
    apply compatible_cell_cylinders_extend_homotopy f x 0 Hn G
    · intro i b t
      have hb : False := by simpa [CellSphere, Pi.norm_def] using b.property
      exact hb.elim
    · intro i w
      rw [w_unique w]
      exact (p i).source
    · intro i w
      exact (p i).target
  have hempty : IsEmpty ↥(skeletonBelow P 0) := ⟨fun z => by
    simpa [skeletonBelow] using z.property⟩
  have HH : ∀ m : ℕ, m ≤ k + 2 → Nonempty (ContinuousMap.Homotopy
      (f.comp (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P m), P)))
      ((ContinuousMap.const P x).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(skeletonBelow P m), P)))) := by
    intro m
    induction m with
    | zero =>
      intro _
      let := hempty
      refine ⟨{
        toContinuousMap := ⟨fun z => isEmptyElim z.2, ?_⟩
        map_zero_left := fun z => isEmptyElim z
        map_one_left := fun z => isEmptyElim z }⟩
      exact continuous_of_discreteTopology
    | succ m ih =>
      intro hm
      obtain ⟨Hn⟩ := ih (by omega)
      by_cases h0 : m = 0
      · subst m
        obtain ⟨Hnext, _⟩ := hzero f x Hn
        exact ⟨Hnext⟩
      · obtain ⟨Hnext, _⟩ := hpositive f x k m (by omega) (by omega) hlower Hn
        exact ⟨Hnext⟩
  have hall (z : P) : z ∈ skeletonBelow P (k + 2) := by
    have hz : z ∈ ⋃ (m : ℕ) (i : Topology.CWComplex.cell (Set.univ : Set P) m),
        Topology.CWComplex.closedCell (C := (Set.univ : Set P)) m i :=
      (Topology.CWComplex.union (C := (Set.univ : Set P))).symm ▸ Set.mem_univ z
    simp only [Set.mem_iUnion] at hz
    obtain ⟨m, i, hi⟩ := hz
    have hm : m < k + 2 := by
      by_contra h
      have := hdim m (by omega)
      exact isEmptyElim i
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨hm, Set.mem_iUnion.mpr ⟨i, hi⟩⟩⟩
  let j : C(P, ↥(skeletonBelow P (k + 2))) :=
    ⟨fun z => ⟨z, hall z⟩, continuous_id.subtype_mk hall⟩
  obtain ⟨Hn⟩ := HH (k + 2) (le_refl _)
  refine ⟨?_⟩
  convert Hn.compContinuousMap j using 1 <;> ext z <;> rfl
end CurveComplexGenusTwo.CWHurewicz.CWGeometricChains
