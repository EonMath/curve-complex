import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteTransverseNewArc

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

abbrev ActualCornerInterval := Set.Icc (-1 : ℝ) 1

def actualCornerZero : ActualCornerInterval := ⟨0, by norm_num⟩

/-- Produce an actual compact two-axis crossing rectangle in any prescribed
open source neighborhood. The axes are the original whole arc images, even
for loops. Its center is the prescribed original crossing, and its image
contains no other original crossing. No chart or finite-event receipt is input. -/
theorem actual_marked_crossing_rectangle_in_open
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M) (p : S)
    (hc : ArcSurgery.CrossesInDisk M a b p)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ R : ActualCornerInterval × ActualCornerInterval → S,
      IsEmbedding R ∧ range R ⊆ W ∧
      Disjoint (range R) (M.cover.branch : Set S) ∧
      R (actualCornerZero,actualCornerZero) = p ∧
      (∀ z, R z ∈ a.val.image ↔ (z.2 : ℝ) = 0) ∧
      (∀ z, R z ∈ b.val.image ↔ (z.1 : ℝ) = 0) ∧
      range R ∩ ArcSurgery.crossings M a b = {p} := by
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨U,hU,hpU,hmarks,e,hep,ha,hb⟩ := hc
  let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
  have hV : IsOpen V := (isOpen_lt continuous_fst.abs continuous_const).inter
    (isOpen_lt continuous_snd.abs continuous_const)
  let T : Set U := {u | (u : S) ∈ W}
  have hT : IsOpen T := hW.preimage continuous_subtype_val
  let V0 : Set (ℝ × ℝ) := Subtype.val '' (e '' T)
  have hV0 : IsOpen V0 := hV.isOpenMap_subtype_val _ (e.isOpenMap T hT)
  have hzero : (0 : ℝ × ℝ) ∈ V0 :=
    ⟨e ⟨p,hpU⟩,⟨⟨p,hpU⟩,hpW,rfl⟩,hep⟩
  obtain ⟨r,hr,hrV0⟩ := Metric.isOpen_iff.mp hV0 0 hzero
  let δ : ℝ := r / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r := by dsimp [δ]; linarith
  let z : ActualCornerInterval × ActualCornerInterval → ℝ × ℝ :=
    fun v => (δ*(v.1 : ℝ),δ*(v.2 : ℝ))
  have hzV0 (v) : z v ∈ V0 := by
    apply hrV0
    rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
    dsimp [z]
    rw [abs_mul,abs_mul,abs_of_pos hδ]
    have hx : |(v.1 : ℝ)| ≤ 1 := abs_le.mpr v.1.property
    have hy : |(v.2 : ℝ)| ≤ 1 := abs_le.mpr v.2.property
    exact max_lt (lt_of_le_of_lt (by nlinarith) hδr)
      (lt_of_le_of_lt (by nlinarith) hδr)
  have hV0V : V0 ⊆ V := by rintro x ⟨y,hy,rfl⟩; exact y.property
  let zv : ActualCornerInterval × ActualCornerInterval → V :=
    fun v => ⟨z v,hV0V (hzV0 v)⟩
  let R : ActualCornerInterval × ActualCornerInterval → S :=
    fun v => (e.symm (zv v) : S)
  have hRc : Continuous R := by dsimp [R,zv,z]; fun_prop
  have hcoord (v) : (e ⟨R v,(e.symm (zv v)).property⟩ : ℝ × ℝ) = z v :=
    congrArg Subtype.val (e.apply_symm_apply (zv v))
  have hRi : Function.Injective R := by
    intro v w he
    have hvw := e.symm.injective (Subtype.ext he)
    have hx := congrArg (fun q : V => (q : ℝ × ℝ).1) hvw
    have hy := congrArg (fun q : V => (q : ℝ × ℝ).2) hvw
    exact Prod.ext (Subtype.ext (mul_left_cancel₀ (ne_of_gt hδ) hx))
      (Subtype.ext (mul_left_cancel₀ (ne_of_gt hδ) hy))
  have hRW : range R ⊆ W := by
    rintro x ⟨v,rfl⟩
    obtain ⟨y,⟨u,hu,heu⟩,hy⟩ := hzV0 v
    have hyz : y = zv v := Subtype.ext hy
    change (e.symm (zv v) : S) ∈ W
    rw [← heu.trans hyz,e.symm_apply_apply]
    exact hu
  have hRm : Disjoint (range R) (M.cover.branch : Set S) := by
    apply disjoint_left.mpr
    rintro x ⟨v,rfl⟩ hm
    exact disjoint_left.mp hmarks (e.symm (zv v)).property hm
  have hRp : R (actualCornerZero,actualCornerZero) = p := by
    have hz0 : zv (actualCornerZero,actualCornerZero) = e ⟨p,hpU⟩ := by
      apply Subtype.ext
      rw [hep]
      simp [zv,z,actualCornerZero]
    change (e.symm _ : S) = p
    rw [hz0,e.symm_apply_apply]
  have hRa (v) : R v ∈ a.val.image ↔ (v.2 : ℝ) = 0 := by
    rw [ha,hcoord]
    change δ*(v.2 : ℝ)=0 ↔ (v.2 : ℝ)=0
    exact mul_eq_zero.trans (or_iff_right (ne_of_gt hδ))
  have hRb (v) : R v ∈ b.val.image ↔ (v.1 : ℝ) = 0 := by
    rw [hb,hcoord]
    change δ*(v.1 : ℝ)=0 ↔ (v.1 : ℝ)=0
    exact mul_eq_zero.trans (or_iff_right (ne_of_gt hδ))
  refine ⟨R,(hRc.isClosedEmbedding hRi).isEmbedding,hRW,hRm,hRp,hRa,hRb,?_⟩
  ext x
  constructor
  · rintro ⟨⟨v,rfl⟩,hv⟩
    have hv0 : v = (actualCornerZero,actualCornerZero) :=
      Prod.ext (Subtype.ext ((hRb v).mp hv.2.1)) (Subtype.ext ((hRa v).mp hv.1.1))
    simpa only [hv0,hRp,mem_singleton_iff]
  · intro hx
    have hxp : x=p := mem_singleton_iff.mp hx
    subst x
    have hm : p ∉ M.cover.branch :=
      fun h => disjoint_left.mp hRm ⟨(actualCornerZero,actualCornerZero),hRp⟩ h
    exact ⟨⟨(actualCornerZero,actualCornerZero),hRp⟩,
      ⟨hRp ▸ (hRa _).mpr rfl,hm⟩,hRp ▸ (hRb _).mpr rfl,hm⟩

#print axioms actual_marked_crossing_rectangle_in_open
end CurveComplex.HyperellipticModel
