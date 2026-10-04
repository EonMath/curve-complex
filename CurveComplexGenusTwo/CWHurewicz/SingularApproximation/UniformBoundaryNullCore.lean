import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereProbe
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.Normed.Group.Constructions
noncomputable section
open Topology Set
open scoped unitInterval
namespace CurveComplexGenusTwo.CWHurewicz.SingularApproximation.Next
theorem cubeLoop_nullhomotopy_uniform_boundary_path {Y : Type} [TopologicalSpace Y] (n : ℕ) (hn : 1 ≤ n)
    (y z : Y) (p : Path y z) (f : GenLoop (Fin n) Y y)
    (H : C(I × (Fin n → I),Y))
    (H0 : ∀ a, H (0,a) = f a) (H1 : ∀ a, H (1,a) = z)
    (Hb : ∀ t a, a ∈ Cube.boundary (Fin n) → H (t,a) = p t) :
    GenLoop.Homotopic f (GenLoop.const (N := Fin n) (X := Y) (x := y)) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let v (a : Fin n → I) : Fin n → ℝ := fun i => 2*(a i:ℝ)-1
  let r (a : Fin n → I) := ‖v a‖
  have hr : Continuous r := by unfold r v; fun_prop
  let c : C((Fin n → I),(Fin n → I)) :=
    ⟨fun a i => projIcc 0 1 zero_le_one (2*(a i:ℝ)-1/2),by fun_prop⟩
  have hrle (a : Fin n → I) : r a ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro i
    rw [Real.norm_eq_abs,abs_le]
    dsimp [v]
    constructor <;> nlinarith [(a i).property.1,(a i).property.2]
  have hcb (a : Fin n → I) (ha : 1/2 ≤ r a) : c a ∈ Cube.boundary (Fin n) := by
    obtain ⟨i,hi⟩ := (IsGreatest.pi_norm (v a)).1
    have h : 1/2 ≤ |2*(a i:ℝ)-1| := by
      change ‖v a i‖ = ‖v a‖ at hi
      rw [← Real.norm_eq_abs]
      exact hi.symm ▸ ha
    rcases le_abs.mp h with h|h
    · refine ⟨i,Or.inr ?_⟩
      change projIcc 0 1 zero_le_one _ = 1
      exact projIcc_of_right_le zero_le_one (by linarith)
    · refine ⟨i,Or.inl ?_⟩
      change projIcc 0 1 zero_le_one _ = 0
      exact projIcc_of_le_left zero_le_one (by linarith)
  have hrb (a : Fin n → I) (ha : a ∈ Cube.boundary (Fin n)) : r a = 1 := by
    rcases ha with ⟨i,hi|hi⟩
    all_goals
      apply le_antisymm (hrle a)
      have h := norm_le_pi_norm (v a) i
      dsimp [v] at h
      norm_num [hi,r,v] at h ⊢
      exact h
  let d : C((Fin n → I),I) :=
    ⟨fun a => projIcc 0 1 zero_le_one (2-2*r a),continuous_projIcc.comp (by fun_prop)⟩
  have hdhalf (a) (ha : r a = 1/2) : d a = 1 := by
    apply Subtype.ext
    norm_num [d,ha,coe_projIcc]
  have hdone (a) (ha : r a = 1) : d a = 0 := by
    apply Subtype.ext
    norm_num [d,ha,coe_projIcc]
  have hdinner (a) (ha : r a ≤ 1/2) : d a = 1 := by
    change projIcc 0 1 zero_le_one (2-2*r a) = 1
    exact projIcc_of_right_le zero_le_one (by linarith)
  have hcb' (a) (ha : a ∈ Cube.boundary (Fin n)) : c a ∈ Cube.boundary (Fin n) :=
    hcb a (by rw [hrb a ha]; norm_num)
  let fpad : GenLoop (Fin n) Y y := ⟨f.val.comp c,fun a ha => GenLoop.boundary f _ (hcb' a ha)⟩
  let w : GenLoop (Fin n) Y y := ⟨p.toContinuousMap.comp d,by
    intro a ha
    change p (d a) = y
    rw [hdone a (hrb a ha)]
    exact p.source⟩
  let G (ta : I × (Fin n → I)) :=
    if r ta.2 ≤ 1/2 then H (ta.1,c ta.2) else p (projIcc 0 1 zero_le_one ((ta.1:ℝ)*(d ta.2:ℝ)))
  have hG : Continuous G := by
    apply Continuous.if ?_ (H.continuous.comp (by fun_prop))
      (p.continuous.comp (continuous_projIcc.comp (by fun_prop)))
    intro ta ha
    have he := frontier_le_subset_eq (hr.comp continuous_snd)
      (continuous_const : Continuous (fun _ : I × (Fin n → I) => (1/2:ℝ))) ha
    change r ta.2 = 1/2 at he
    change H (ta.1,c ta.2) = p (projIcc 0 1 zero_le_one ((ta.1:ℝ)*(d ta.2:ℝ)))
    rw [Hb _ _ (hcb ta.2 he.ge),hdhalf ta.2 he]
    simp [projIcc_val]
  have hGb (t : I) (a : Fin n → I) (ha : a ∈ Cube.boundary (Fin n)) : G (t,a) = y := by
    dsimp only [G]
    rw [ite_eq_right (by rw [hrb a ha]; norm_num),hdone a (hrb a ha)]
    simp [p.source,projIcc_left]
  have hGw : GenLoop.Homotopic fpad w := by
    exact ⟨{
      toFun := G
      continuous_toFun := hG
      map_zero_left := by
        intro a
        dsimp only [G]
        split_ifs with ha
        · exact H0 (c a)
        · change p (projIcc 0 1 zero_le_one (((0:I):ℝ) * (d a:ℝ))) = f (c a)
          change p (projIcc 0 1 zero_le_one (0 * (d a:ℝ))) = f (c a)
          simp only [zero_mul]
          have hz : projIcc 0 1 zero_le_one (0:ℝ) = (0:I) := by
            apply Subtype.ext
            norm_num [coe_projIcc]
          rw [hz,p.source]
          exact (GenLoop.boundary f _ (hcb a (le_of_not_ge ha))).symm
      map_one_left := by
        intro a
        dsimp only [G]
        split_ifs with ha
        · change H (1,c a) = p (d a)
          rw [H1,hdinner a ha,p.target]
        · change p (projIcc 0 1 zero_le_one (1*(d a:ℝ))) = p (d a)
          simp [projIcc_val]
      prop' := by
        intro t a ha
        change G (t,a) = fpad a
        exact (hGb t a ha).trans (GenLoop.boundary fpad a ha).symm
    }⟩
  have hw : GenLoop.Homotopic w (GenLoop.const (N := Fin n) (X := Y) (x := y)) := by
    exact ⟨{
      toFun := fun ta => p (projIcc 0 1 zero_le_one ((1-(ta.1:ℝ))*(d ta.2:ℝ)))
      continuous_toFun := p.continuous.comp (continuous_projIcc.comp (by fun_prop))
      map_zero_left := by intro a; simp [projIcc_val]; rfl
      map_one_left := by intro a; simp [projIcc_left]
      prop' := by
        intro t a ha
        change p (projIcc 0 1 zero_le_one ((1-(t:ℝ))*(d a:ℝ))) = p (d a)
        rw [hdone a (hrb a ha)]
        simp [projIcc_left]
    }⟩
  have hfpad : GenLoop.Homotopic f fpad := by
    let d₀ : C(I,I) := ⟨fun t => projIcc 0 1 zero_le_one (2*(t:ℝ)-1/2),
      continuous_projIcc.comp (by fun_prop)⟩
    have hd0 : d₀ 0 = 0 := by apply Subtype.ext; norm_num [d₀,coe_projIcc]
    have hd1 : d₀ 1 = 1 := by apply Subtype.ext; norm_num [d₀,coe_projIcc]
    let A : C(I × (Fin n → I),(Fin n → I)) :=
      ⟨fun ta i => projIcc 0 1 zero_le_one
        ((1-(ta.1:ℝ))*(ta.2 i:ℝ)+(ta.1:ℝ)*(c ta.2 i:ℝ)),by fun_prop⟩
    have A0 (a) : A (0,a) = a := by funext i; simp [A,projIcc_val]
    have A1 (a) : A (1,a) = c a := by funext i; simp [A,projIcc_val]
    have Ab (t : I) (a : Fin n → I) (ha : a ∈ Cube.boundary (Fin n)) :
        A (t,a) ∈ Cube.boundary (Fin n) := by
      rcases ha with ⟨i,hi|hi⟩
      · refine ⟨i,Or.inl ?_⟩
        have hc : c a i = 0 := by change d₀ (a i) = 0; rw [hi,hd0]
        change projIcc 0 1 zero_le_one _ = 0
        simp [hi,hc,projIcc_left]
      · refine ⟨i,Or.inr ?_⟩
        have hc : c a i = 1 := by change d₀ (a i) = 1; rw [hi,hd1]
        change projIcc 0 1 zero_le_one _ = 1
        simp only [hi,hc]
        change projIcc 0 1 zero_le_one ((1-(t:ℝ))*1+(t:ℝ)*1) = 1
        have ht : (1-(t:ℝ))*1+(t:ℝ)*1 = 1 := by ring
        rw [ht]
        exact projIcc_right zero_le_one
    exact ⟨{
      toFun := fun ta => f (A ta)
      continuous_toFun := f.val.continuous.comp A.continuous
      map_zero_left := by intro a; rw [A0]; rfl
      map_one_left := by intro a; rw [A1]; rfl
      prop' := by
        intro t a ha
        exact (GenLoop.boundary f _ (Ab t a ha)).trans (GenLoop.boundary f a ha).symm
    }⟩
  exact hfpad.trans (hGw.trans hw)
end CurveComplexGenusTwo.CWHurewicz.SingularApproximation.Next
