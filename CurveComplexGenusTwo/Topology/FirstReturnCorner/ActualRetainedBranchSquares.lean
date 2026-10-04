import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualRetainedBranchCharts
import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualFiniteCurveReplacement

namespace CurveComplex
open Set Topology Schoenflies

/-- Normalize an actual crossing chart to contain the entire unit repair square,
while retaining its source and both coordinate axes. -/
theorem source_crossing_chart_unit_square
    {S : Type} [TopologicalSpace S]
    (E : OpenPartialHomeomorph S (ℝ × ℝ)) (p : S)
    (hp : p ∈ E.source) (hep : E p = (0,0)) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ δ : ℝ,
      0 < δ ∧ F.source = E.source ∧ Plane.closedSquare 0 1 ⊆ F.target ∧
      F p = 0 ∧ ∀ x, F x 0 = (E x).1 / δ ∧ F x 1 = (E x).2 / δ := by
  have hz : (0 : ℝ × ℝ) ∈ E.target := by
    change (0,0) ∈ E.target
    rw [← hep]
    exact E.map_source hp
  obtain ⟨r,hr,hrE⟩ := Metric.isOpen_iff.mp E.open_target 0 hz
  let δ : ℝ := r/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r := by dsimp [δ]; linarith
  let L : (ℝ × ℝ) ≃ₜ Plane := {
    toEquiv := {
      toFun := fun z => Plane.mk (z.1/δ) (z.2/δ)
      invFun := fun z => (δ*z 0,δ*z 1)
      left_inv := by
        intro z
        apply Prod.ext
        · change δ*(z.1/δ) = z.1
          field_simp [ne_of_gt hδ]
        · change δ*(z.2/δ) = z.2
          field_simp [ne_of_gt hδ]
      right_inv := by
        intro z
        ext j
        fin_cases j
        · change δ*z 0/δ = z 0
          field_simp [ne_of_gt hδ]
        · change δ*z 1/δ = z 1
          field_simp [ne_of_gt hδ] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F := E.trans L.toOpenPartialHomeomorph
  have hFs : F.source = E.source := by simp [F]
  refine ⟨F,δ,hδ,hFs,?_,?_,?_⟩
  · intro z hz
    have hnorm : Plane.supNorm z ≤ 1 := by
      simpa [Plane.closedSquare,Plane.supDist] using hz
    have h0 : |z 0| ≤ 1 := (Plane.abs_zero_le_supNorm z).trans hnorm
    have h1 : |z 1| ≤ 1 := (Plane.abs_one_le_supNorm z).trans hnorm
    have hq : L.symm z ∈ E.target := by
      apply hrE
      rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      simp only [Prod.fst_zero,Prod.snd_zero,sub_zero]
      change max |δ*z 0| |δ*z 1| < r
      rw [abs_mul,abs_mul,abs_of_pos hδ]
      exact max_lt (lt_of_le_of_lt (by nlinarith) hδr)
        (lt_of_le_of_lt (by nlinarith) hδr)
    exact ⟨Set.mem_univ _,hq⟩
  · change L (E p) = 0
    rw [hep]
    ext j
    fin_cases j <;> simp [L,Plane.mk]
  · intro x
    constructor <;> rfl

/-- Produce the actual, pairwise disjoint finite square repair charts for any
chosen first-return surgery branch. The branch/current axes agree throughout
each chart; no abstract chart family is an input. -/
theorem source_retained_branch_square_charts
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∃ E : ↥(source_surgery_retained_crossings B i) → OpenPartialHomeomorph S Plane,
      (∀ p, p.val ∈ (E p).source ∧ E p p.val = 0) ∧
      (∀ p, Plane.closedSquare 0 1 ⊆ (E p).target) ∧
      (∀ p q, p ≠ q → Disjoint (E p).source (E q).source) ∧
      (∀ p, Disjoint (E p).source (Set.range D.first)) ∧
      (∀ p, Disjoint (E p).source (Set.range (B.closing (!i)))) ∧
      (∀ p x, x ∈ (E p).source → (x ∈ a.image ↔ E p x 0 = 0)) ∧
      (∀ p x, x ∈ (E p).source → (x ∈ b.image ↔ E p x 1 = 0)) ∧
      (∀ p x, x ∈ (E p).source → (x ∈ (B.boundary i).image ↔ E p x 1 = 0)) := by
  classical
  obtain ⟨F,hpF,hdis,hfirst,hother,ha,hb,hbranch⟩ :=
    source_retained_branch_crossing_charts D B ht i
  choose E δ hδ hsource hsquare hpzero hcoords using fun p =>
    source_crossing_chart_unit_square (F p) p.val (hpF p).1 (hpF p).2
  have hzero (p) (x : S) (j : Fin 2) :
      E p x j = 0 ↔ (if j = 0 then (F p x).1 else (F p x).2) = 0 := by
    fin_cases j
    · change E p x 0 = 0 ↔ (F p x).1 = 0
      rw [(hcoords p x).1]
      simp [ne_of_gt (hδ p)]
    · change E p x 1 = 0 ↔ (F p x).2 = 0
      rw [(hcoords p x).2]
      simp [ne_of_gt (hδ p)]
  refine ⟨E,(fun p => ⟨(hsource p).symm ▸ (hpF p).1,hpzero p⟩),hsquare,?_,?_,?_,?_,?_,?_⟩
  · intro p q hpq
    rw [hsource p,hsource q]
    exact hdis p q hpq
  · intro p
    rw [hsource p]
    exact hfirst p
  · intro p
    rw [hsource p]
    exact hother p
  · intro p x hx
    rw [hzero p x 0]
    exact ha p x ((hsource p).le hx)
  · intro p x hx
    rw [hzero p x 1]
    exact hb p x ((hsource p).le hx)
  · intro p x hx
    rw [hzero p x 1]
    exact hbranch p x ((hsource p).le hx)

end CurveComplex
#print axioms CurveComplex.source_crossing_chart_unit_square
#print axioms CurveComplex.source_retained_branch_square_charts
