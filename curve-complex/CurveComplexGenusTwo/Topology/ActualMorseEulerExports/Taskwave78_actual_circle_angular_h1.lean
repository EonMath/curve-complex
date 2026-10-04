import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCircleFundamentalCycle
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleSourceWindingTransport
import CurveComplexGenusTwo.Hyperbolic.ActualHaasBoundary.HaasActualCircleMapWindingHomotopySourceReviewRequest
import CurveComplexGenusTwo.Topology.Orientation.CircleReflection
open CategoryTheory CategoryTheory.Limits Convexity CurveComplexGenusTwo.CWHurewicz
open scoped Simplicial
open scoped unitInterval
open Set Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private noncomputable def actualCircleMapDegree (f : C(Circle,Circle)) : ℤ :=
  Classical.choose (actual_circle_map_winding_homotopy_source f)

-- Exact actual-circle action producer, not an added premise.
private noncomputable def angularEdge (a b : ℝ) : CircleFundamentalCycle.CircleSing 1 :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).symm
    ⟨fun w => Circle.exp (a * w.weights 0 + b * w.weights 1), by fun_prop⟩

private noncomputable def angularTriangle (a b c : ℝ) : CircleFundamentalCycle.CircleSing 2 :=
  (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋2⦌)).symm
    ⟨fun w => Circle.exp (a * w.weights 0 + b * w.weights 1 + c * w.weights 2),
      by fun_prop⟩

private theorem angular_triangle_boundary (a b c : ℝ) :
    singularBoundaryFinsupp (TopCat.of Circle) 1
      (Finsupp.single (angularTriangle a b c) (1 : ℤ)) =
    Finsupp.single (angularEdge b c) 1 - Finsupp.single (angularEdge a c) 1 +
      Finsupp.single (angularEdge a b) 1 := by
  have faces : ∀ i : Fin 3,
      (TopCat.toSSet.obj (TopCat.of Circle)).δ i (angularTriangle a b c) =
        ![angularEdge b c, angularEdge a c, angularEdge a b] i := by
    intro i
    apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).injective
    apply ContinuousMap.ext
    intro w
    fin_cases i
    · change Circle.exp (a * (w.map (0 : Fin 3).succAbove).weights 0 +
        b * (w.map (0 : Fin 3).succAbove).weights 1 +
        c * (w.map (0 : Fin 3).succAbove).weights 2) =
        Circle.exp (b * w.weights 0 + c * w.weights 1)
      simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
        Fin.sum_univ_succ, Fin.succAbove]
    · change Circle.exp (a * (w.map (1 : Fin 3).succAbove).weights 0 +
        b * (w.map (1 : Fin 3).succAbove).weights 1 +
        c * (w.map (1 : Fin 3).succAbove).weights 2) =
        Circle.exp (a * w.weights 0 + c * w.weights 1)
      simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
        Fin.sum_univ_succ, Fin.succAbove]
    · change Circle.exp (a * (w.map (2 : Fin 3).succAbove).weights 0 +
        b * (w.map (2 : Fin 3).succAbove).weights 1 +
        c * (w.map (2 : Fin 3).succAbove).weights 2) =
        Circle.exp (a * w.weights 0 + b * w.weights 1)
      simp [StdSimplex.weights_map, Finsupp.mapDomain, Finsupp.sum_fintype,
        Fin.sum_univ_succ, Fin.succAbove]
  rw [singularBoundaryFinsupp_single]
  simp [Fin.sum_univ_succ, faces, sub_eq_add_neg, add_assoc]

private theorem angular_cycleClass_add (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (a b : K.X 1) (ha : K.d 1 0 a = 0) (hb : K.d 1 0 b = 0) :
    CircleFundamentalCycle.cycleClass K 1 (a + b) (by rw [map_add, ha, hb, add_zero]) =
      CircleFundamentalCycle.cycleClass K 1 a ha +
        CircleFundamentalCycle.cycleClass K 1 b hb := by
  have hs : CircleFundamentalCycle.scalar _ (a + b) =
      CircleFundamentalCycle.scalar _ a + CircleFundamentalCycle.scalar _ b := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro n
    simp [CircleFundamentalCycle.scalar, LinearMap.toSpanSingleton_apply, smul_add]
  have hl : K.liftCycles (CircleFundamentalCycle.scalar _ (a + b)) 0 (by simp)
      (by rw [CircleFundamentalCycle.scalar_naturality, map_add, ha, hb,
        add_zero, CircleFundamentalCycle.scalar_eq_zero]) =
      K.liftCycles (CircleFundamentalCycle.scalar _ a) 0 (by simp)
        (by rw [CircleFundamentalCycle.scalar_naturality, ha,
          CircleFundamentalCycle.scalar_eq_zero]) +
      K.liftCycles (CircleFundamentalCycle.scalar _ b) 0 (by simp)
        (by rw [CircleFundamentalCycle.scalar_naturality, hb,
          CircleFundamentalCycle.scalar_eq_zero]) := by
    apply (cancel_mono (K.iCycles 1)).mp
    simp only [Preadditive.add_comp, K.liftCycles_i]
    exact hs
  unfold CircleFundamentalCycle.cycleClass
  rw [hl]
  simp

private theorem angular_cycleClass_boundary (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (z : K.X 1) (hz : K.d 1 0 z = 0) (w : K.X 2) (hw : K.d 2 1 w = z) :
    CircleFundamentalCycle.cycleClass K 1 z hz = 0 := by
  have h : CircleFundamentalCycle.scalar _ z =
      CircleFundamentalCycle.scalar _ w ≫ K.d 2 1 := by
    rw [CircleFundamentalCycle.scalar_naturality, hw]
  have he := K.liftCycles_homologyπ_eq_zero_of_boundary
    (CircleFundamentalCycle.scalar _ z) 0 (by simp)
    (CircleFundamentalCycle.scalar _ w) h
  exact congrArg (fun f => f (1 : ℤ)) he

private theorem angular_cycleClass_zero (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) :
    CircleFundamentalCycle.cycleClass K 1 0 (by simp) = 0 := by
  have hl : K.liftCycles (CircleFundamentalCycle.scalar (K.X 1) 0) 0 (by simp)
      (by rw [CircleFundamentalCycle.scalar_eq_zero]; simp) = 0 := by
    apply (cancel_mono (K.iCycles 1)).mp
    rw [K.liftCycles_i]
    simp [CircleFundamentalCycle.scalar_eq_zero]
  unfold CircleFundamentalCycle.cycleClass
  rw [hl]
  simp

private theorem angular_cycleClass_neg (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (a : K.X 1) (ha : K.d 1 0 a = 0) :
    CircleFundamentalCycle.cycleClass K 1 (-a) (by rw [map_neg, ha, neg_zero]) =
      -CircleFundamentalCycle.cycleClass K 1 a ha := by
  have h := angular_cycleClass_add K a (-a) ha (by rw [map_neg, ha, neg_zero])
  have h' : CircleFundamentalCycle.cycleClass K 1 a ha +
      CircleFundamentalCycle.cycleClass K 1 (-a) (by rw [map_neg, ha, neg_zero]) = 0 := by
    simpa only [add_neg_cancel, angular_cycleClass_zero] using h.symm
  exact eq_neg_of_add_eq_zero_right h'

private theorem angular_cycleClass_eq_of_boundary (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (a b : K.X 1) (ha : K.d 1 0 a = 0) (hb : K.d 1 0 b = 0)
    (w : K.X 2) (hw : K.d 2 1 w = a - b) :
    CircleFundamentalCycle.cycleClass K 1 a ha =
      CircleFundamentalCycle.cycleClass K 1 b hb := by
  have hzero := angular_cycleClass_boundary K (a - b)
    (by rw [map_sub,ha,hb,sub_self]) w hw
  simp only [sub_eq_add_neg] at hzero
  rw [angular_cycleClass_add K a (-b) ha
    (by rw [map_neg, hb, neg_zero]), angular_cycleClass_neg K b hb] at hzero
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hzero)

private theorem angular_side_edge (i : CurveComplex.Octagon.Side) :
    angularEdge (2 * Real.pi * (i.val : ℝ) / 8)
      (2 * Real.pi * ((i.val : ℝ) + 1) / 8) =
      CircleFundamentalCycle.circleSideSimplex i := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro w
  have hw : w.weights 0 + w.weights 1 = (1 : ℝ) := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_succ] using w.total
  change Circle.exp ((2 * Real.pi * (i.val : ℝ) / 8) * w.weights 0 +
    (2 * Real.pi * ((i.val : ℝ) + 1) / 8) * w.weights 1) =
    Circle.exp (2 * Real.pi * ((i.val : ℝ) + (CircleFundamentalCycle.coord (1 : Fin 2) w : ℝ)) / 8)
  change Circle.exp _ = Circle.exp (2 * Real.pi * ((i.val : ℝ) + w.weights 1) / 8)
  congr 1
  have hw0 : w.weights 0 = 1 - w.weights 1 := by linarith
  rw [hw0]
  ring

private noncomputable def angularNode (s : ℝ) (k : ℕ) : ℝ :=
  s * (2 * Real.pi) * (k : ℝ) / 8

private noncomputable def angularEightChain (s : ℝ) :
    CircleFundamentalCycle.CircleSing 1 →₀ ℤ :=
  ∑ i : Fin 8, Finsupp.single
    (angularEdge (angularNode s i.val) (angularNode s (i.val + 1))) 1

private noncomputable def angularEightFilling (s : ℝ) :
    CircleFundamentalCycle.CircleSing 2 →₀ ℤ :=
  ∑ i : Fin 7, Finsupp.single
    (angularTriangle 0 (angularNode s (i.val + 1))
      (angularNode s (i.val + 2))) 1

private theorem angular_eight_subdivision (s : ℝ) :
    singularBoundaryFinsupp (TopCat.of Circle) 1 (angularEightFilling s) =
      angularEightChain s - Finsupp.single (angularEdge 0 (angularNode s 8)) 1 := by
  simp only [angularEightFilling, angularEightChain, map_sum, angular_triangle_boundary]
  simp only [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Nat.zero_add, Nat.succ_eq_add_one]
  simp only [show angularNode s 0 = 0 by simp [angularNode]]
  norm_num only [zero_add, add_zero]
  abel

private theorem angular_eight_one :
    angularEightChain 1 = CircleFundamentalCycle.circleBoundaryChain := by
  unfold angularEightChain CircleFundamentalCycle.circleBoundaryChain
  apply Finset.sum_congr rfl
  intro i hi
  rw [← angular_side_edge i]
  congr 1 <;> simp [angularNode]

private theorem angular_edge_power (n : ℤ) (a b : ℝ) :
    (TopCat.toSSet.map (TopCat.ofHom
      (⟨fun z : Circle => z ^ n, continuous_zpow n⟩ : C(Circle,Circle)))).app (.op ⦋1⦌)
        (angularEdge a b) = angularEdge ((n : ℝ) * a) ((n : ℝ) * b) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro w
  change (Circle.exp (a * w.weights 0 + b * w.weights 1)) ^ n =
    Circle.exp (((n : ℝ) * a) * w.weights 0 + ((n : ℝ) * b) * w.weights 1)
  rw [← Circle.exp_zsmul]
  simp only [zsmul_eq_mul]
  congr 1
  ring

private theorem angular_eight_power (n : ℤ) :
    singularFinsuppPush (TopCat.ofHom
      (⟨fun z : Circle => z ^ n, continuous_zpow n⟩ : C(Circle,Circle))) 1
      CircleFundamentalCycle.circleBoundaryChain = angularEightChain n := by
  rw [← angular_eight_one]
  simp only [angularEightChain, map_sum, singularFinsuppPush,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, angular_edge_power]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2 <;> simp [angularNode] <;> ring

private theorem angular_eight_cycle (n : ℤ) :
    singularBoundaryFinsupp (TopCat.of Circle) 0 (angularEightChain n) = 0 := by
  rw [← angular_eight_power, singularFinsuppPush_boundary,
    CircleFundamentalCycle.circle_boundary_is_cycle, map_zero]

private theorem angular_full_cycle (n : ℤ) :
    singularBoundaryFinsupp (TopCat.of Circle) 0
      (Finsupp.single (angularEdge 0 (angularNode n 8)) (1 : ℤ)) = 0 := by
  have hd := congrArg (fun f => f (angularEightFilling n))
    ((mvAmbientComplex (TopCat.of Circle)).d_comp_d 2 1 0)
  change singularBoundaryFinsupp (TopCat.of Circle) 0
    (singularBoundaryFinsupp (TopCat.of Circle) 1 (angularEightFilling n)) = 0 at hd
  rw [angular_eight_subdivision, map_sub, angular_eight_cycle] at hd
  simpa using hd

private theorem angular_eight_class_eq_full (n : ℤ) :
    CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
      (angularEightChain n) (angular_eight_cycle n) =
    CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
      (Finsupp.single (angularEdge 0 (angularNode n 8)) 1) (angular_full_cycle n) := by
  apply angular_cycleClass_eq_of_boundary _ _ _ (angular_eight_cycle n)
    (angular_full_cycle n) (angularEightFilling n)
  exact angular_eight_subdivision n

private theorem angular_turn_add (m n : ℤ) :
    angularNode ((m + n : ℤ) : ℝ) 8 = angularNode m 8 + angularNode n 8 := by
  simp [angularNode, Int.cast_add]
  ring

private theorem angular_edge_lap_shift (m : ℤ) (a b : ℝ) :
    angularEdge (angularNode m 8 + a) (angularNode m 8 + b) =
      angularEdge a b := by
  apply (TopCat.toSSetObjEquiv (TopCat.of Circle) (.op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro w
  have hw : w.weights 0 + w.weights 1 = (1 : ℝ) := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_succ] using w.total
  change Circle.exp ((angularNode m 8 + a) * w.weights 0 +
    (angularNode m 8 + b) * w.weights 1) =
      Circle.exp (a * w.weights 0 + b * w.weights 1)
  have he : (angularNode m 8 + a) * w.weights 0 +
      (angularNode m 8 + b) * w.weights 1 =
      angularNode m 8 + (a * w.weights 0 + b * w.weights 1) := by
    calc
      _ = angularNode m 8 * (w.weights 0 + w.weights 1) +
          (a * w.weights 0 + b * w.weights 1) := by ring
      _ = _ := by rw [hw, mul_one]
  rw [he, Circle.exp_add]
  have hm : Circle.exp (angularNode m 8) = 1 := by
    convert Circle.exp_int_mul_two_pi m using 1
    congr 1
    simp [angularNode]
  rw [hm, one_mul]

private theorem angular_full_add_boundary (m n : ℤ) :
    singularBoundaryFinsupp (TopCat.of Circle) 1
      (Finsupp.single
        (angularTriangle 0 (angularNode m 8) (angularNode ((m + n : ℤ) : ℝ) 8)) (1 : ℤ)) =
      Finsupp.single (angularEdge 0 (angularNode m 8)) 1 +
        Finsupp.single (angularEdge 0 (angularNode n 8)) 1 -
        Finsupp.single (angularEdge 0 (angularNode ((m + n : ℤ) : ℝ) 8)) 1 := by
  rw [angular_triangle_boundary]
  have he : angularEdge (angularNode m 8) (angularNode ((m + n : ℤ) : ℝ) 8) =
      angularEdge 0 (angularNode n 8) := by
    rw [angular_turn_add]
    convert angular_edge_lap_shift m 0 (angularNode n 8) using 1 <;> simp
  rw [he]
  abel

private theorem angular_full_class_add (m n : ℤ) :
    CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
      (Finsupp.single (angularEdge 0 (angularNode ((m + n : ℤ) : ℝ) 8)) 1)
      (angular_full_cycle (m + n)) =
    CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
      (Finsupp.single (angularEdge 0 (angularNode m 8)) 1) (angular_full_cycle m) +
    CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
      (Finsupp.single (angularEdge 0 (angularNode n 8)) 1) (angular_full_cycle n) := by
  have hs : singularBoundaryFinsupp (TopCat.of Circle) 0
      (Finsupp.single (angularEdge 0 (angularNode m 8)) (1 : ℤ) +
        Finsupp.single (angularEdge 0 (angularNode n 8)) 1) = 0 := by
    rw [map_add, angular_full_cycle, angular_full_cycle, add_zero]
  have he := angular_cycleClass_eq_of_boundary (mvAmbientComplex (TopCat.of Circle))
    (Finsupp.single (angularEdge 0 (angularNode m 8)) (1 : ℤ) +
      Finsupp.single (angularEdge 0 (angularNode n 8)) 1)
    (Finsupp.single (angularEdge 0 (angularNode ((m + n : ℤ) : ℝ) 8)) 1)
    hs (angular_full_cycle (m + n))
    (Finsupp.single (angularTriangle 0 (angularNode m 8)
      (angularNode ((m + n : ℤ) : ℝ) 8)) 1)
    (angular_full_add_boundary m n)
  rw [angular_cycleClass_add] at he
  exact he.symm

private noncomputable def angularFullClass (n : ℤ) :
    CurveComplexGenusTwo.CWHurewicz.H Circle 1 :=
  (singularHomologyRepresentation (TopCat.of Circle) 1).hom
    (CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
      (Finsupp.single (angularEdge 0 (angularNode n 8)) 1) (angular_full_cycle n))

private theorem angularFullClass_add (m n : ℤ) :
    angularFullClass (m + n) = angularFullClass m + angularFullClass n := by
  unfold angularFullClass
  rw [angular_full_class_add, map_add]

private theorem angularFullClass_zsmul (n : ℤ) :
    angularFullClass n = n • angularFullClass 1 := by
  let F : ℤ →+ CurveComplexGenusTwo.CWHurewicz.H Circle 1 := {
    toFun := angularFullClass
    map_zero' := by
      have h := angularFullClass_add 0 0
      simp only [zero_add] at h
      have he : angularFullClass 0 + angularFullClass 0 =
          (0 : CurveComplexGenusTwo.CWHurewicz.H Circle 1) + angularFullClass 0 := by
        rw [← h, zero_add]
      exact add_right_cancel he
    map_add' := angularFullClass_add }
  have h := map_zsmul F n (1 : ℤ)
  simpa [F] using h

private theorem angularFullClass_one :
    angularFullClass 1 = CircleFundamentalCycle.fundamentalClass := by
  unfold angularFullClass CircleFundamentalCycle.fundamentalClass
  rw [← angular_eight_class_eq_full (1 : ℤ)]
  simpa only [Int.cast_one, angular_eight_one]

private theorem angular_power_image_class (n : ℤ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map
      (TopCat.ofHom (⟨fun z : Circle => z ^ n, continuous_zpow n⟩ : C(Circle,Circle)))
      CircleFundamentalCycle.fundamentalClass = angularFullClass n := by
  let p : TopCat.of Circle ⟶ TopCat.of Circle :=
    TopCat.ofHom (⟨fun z : Circle => z ^ n, continuous_zpow n⟩ : C(Circle,Circle))
  have hn := congrArg
    (fun g => g (CircleFundamentalCycle.cycleClass
      (mvAmbientComplex (TopCat.of Circle)) 1
      CircleFundamentalCycle.circleBoundaryChain
      CircleFundamentalCycle.circle_boundary_is_cycle))
    (singularHomologyRepresentation_naturality p 1)
  have hc := CircleFundamentalCycle.cycleClass_map (singularFinsuppMap p) 1
    CircleFundamentalCycle.circleBoundaryChain
    CircleFundamentalCycle.circle_boundary_is_cycle
    (show singularBoundaryFinsupp (TopCat.of Circle) 0
      ((singularFinsuppMap p).f 1 CircleFundamentalCycle.circleBoundaryChain) = 0 by
      have h := angular_eight_cycle n
      rw [← angular_eight_power n] at h
      convert h using 1 <;> simp [p, singularFinsuppMap_f, mvAmbientComplex])
  have hp : (singularFinsuppMap p).f 1 CircleFundamentalCycle.circleBoundaryChain =
      angularEightChain n := by
    convert angular_eight_power n using 1 <;> simp [p, singularFinsuppMap_f, mvAmbientComplex]
  have hclass : HomologicalComplex.homologyMap (singularFinsuppMap p) 1
      (CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
        CircleFundamentalCycle.circleBoundaryChain
        CircleFundamentalCycle.circle_boundary_is_cycle) =
      CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
        (angularEightChain n) (angular_eight_cycle n) := by
    simpa only [hp] using hc
  change (singularHomologyRepresentation (TopCat.of Circle) 1).hom
      (HomologicalComplex.homologyMap (singularFinsuppMap p) 1
        (CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
          CircleFundamentalCycle.circleBoundaryChain
          CircleFundamentalCycle.circle_boundary_is_cycle)) =
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map p CircleFundamentalCycle.fundamentalClass at hn
  calc
    _ = (singularHomologyRepresentation (TopCat.of Circle) 1).hom
      (HomologicalComplex.homologyMap (singularFinsuppMap p) 1
        (CircleFundamentalCycle.cycleClass (mvAmbientComplex (TopCat.of Circle)) 1
          CircleFundamentalCycle.circleBoundaryChain
          CircleFundamentalCycle.circle_boundary_is_cycle)) := hn.symm
    _ = angularFullClass n := by
      rw [hclass, angular_eight_class_eq_full]
      rfl

private theorem actual_circle_angular_degree_induced_h1_action
    (f : C(Circle,Circle)) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f)
        CircleFundamentalCycle.fundamentalClass =
    actualCircleMapDegree f • CircleFundamentalCycle.fundamentalClass := by
  obtain ⟨H⟩ := Classical.choose_spec (actual_circle_map_winding_homotopy_source f)
  have heq := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (show TopCat.Homotopy (TopCat.ofHom f)
    (TopCat.ofHom (⟨fun z : Circle => z ^ actualCircleMapDegree f,
      continuous_zpow (actualCircleMapDegree f)⟩ : C(Circle,Circle))) from H)
      (ModuleCat.of ℤ ℤ) 1
  have hmap :
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom f) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
        (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom
          (⟨fun z : Circle => z ^ actualCircleMapDegree f,
            continuous_zpow (actualCircleMapDegree f)⟩ : C(Circle,Circle))) := by
    simpa [AlgebraicTopology.singularHomologyFunctor] using heq
  rw [hmap, angular_power_image_class, angularFullClass_zsmul, angularFullClass_one]
