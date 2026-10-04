import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.ProperPairCompactifiedGeometry
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.RelativeHalfRegionFilling

open Set Topology Schoenflies
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
namespace CurveComplex.HyperellipticModel

def twoTriangleRegion (A B : Fin 2 → Set Plane) (P : Set Plane) : Set Plane :=
  closure (inside (A 0 ∪ P ∪ B 0)) ∪ closure (inside (A 1 ∪ P ∪ B 1))

/-- The compact region constructed from an actual proper line pair. -/
structure ProperPairDiagram (F G : C(ℝ,Plane)) where
  pole : Plane
  x : Plane
  y : Plane
  A : Fin 2 → Set Plane
  B : Fin 2 → Set Plane
  P : Set Plane
  poleF : pole ∉ range F
  poleG : pole ∉ range G
  arcA : ∀ i, IsArcBetween (A i) pole x
  arcB : ∀ i, IsArcBetween (B i) pole y
  arcP : IsArcBetween P x y
  meetAP : ∀ i, A i ∩ P = {x}
  meetAB : ∀ i, A i ∩ B i = {pole}
  meetPB : ∀ i, P ∩ B i = {y}
  jordan : ∀ i, IsJordanCurve (A i ∪ P ∪ B i)
  meet : closure (inside (A 0 ∪ P ∪ B 0)) ∩
    closure (inside (A 1 ∪ P ∪ B 1)) = P ∪ {pole}
  boundaryA : A 0 ∪ A 1 = insert pole (invert pole '' range F)
  boundaryB : B 0 ∪ B 1 = insert pole (invert pole '' range G)
  cover : ∀ u v : ℝ, (∀ w ∈ Ioo (0:ℝ) 1,
      AffineMap.lineMap (F u) (G v) w ∉ range F ∪ range G) →
      ∀ w ∈ Icc (0:ℝ) 1,
        AffineMap.lineMap (F u) (G v) w ≠ pole ∧
        invert pole (AffineMap.lineMap (F u) (G v) w) ∈ twoTriangleRegion A B P

theorem proper_pair_diagram_exists
    (F G : C(ℝ,Plane)) (hF : IsClosedEmbedding F) (hG : IsClosedEmbedding G)
    (hdis : Disjoint (range F) (range G)) : Nonempty (ProperPairDiagram F G) := by
  classical
  obtain ⟨a,s,t,haF,haG,hC,hD,hP,hCD,hPC,hPD,hDi,hPi,hcover⟩ :=
    proper_disjoint_lines_nested_tangent_connector F G hF hG hdis
  let C := insert a (invert a '' range F)
  let D := insert a (invert a '' range G)
  let P := invert a '' segment ℝ (F s) (G t)
  let x := invert a (F s)
  let y := invert a (G t)
  have hxC : x ∈ C := Or.inr ⟨F s,mem_range_self s,rfl⟩
  have hyD : y ∈ D := Or.inr ⟨G t,mem_range_self t,rfl⟩
  have hax : a ≠ x := fun h => haF ⟨s,invert_eq_center_iff.mp h.symm⟩
  have hay : a ≠ y := fun h => haG ⟨t,invert_eq_center_iff.mp h.symm⟩
  obtain ⟨A₀,A₁,hA⟩ := exists_isCutPair hC (mem_insert _ _) hxC hax
  obtain ⟨B₀,B₁,hB⟩ := exists_isCutPair hD (mem_insert _ _) hyD hay
  obtain ⟨flip,hJ₀,hJ₁,hmeet,hcover'⟩ :=
    tangent_jordan_connector_half_regions hC hA hB hP hCD hPC hPD hDi hPi
  let A : Fin 2 → Set Plane := ![A₀,A₁]
  let B : Fin 2 → Set Plane := if flip then ![B₁,B₀] else ![B₀,B₁]
  have hAi : ∀ i, IsArcBetween (A i) a x := by
    intro i; fin_cases i
    · exact hA.fst
    · exact hA.snd
  have hBi : ∀ i, IsArcBetween (B i) a y := by
    intro i; cases flip <;> fin_cases i <;> dsimp [B]
    · exact hB.fst
    · exact hB.snd
    · exact hB.snd
    · exact hB.fst
  have hAC : ∀ i, A i ⊆ C := by
    intro i;fin_cases i
    · exact hA.fst_subset
    · exact hA.snd_subset
  have hBD : ∀ i, B i ⊆ D := by
    intro i;cases flip <;> fin_cases i <;> dsimp [B]
    · exact hB.fst_subset
    · exact hB.snd_subset
    · exact hB.snd_subset
    · exact hB.fst_subset
  have hJ : ∀ i, IsJordanCurve (A i ∪ P ∪ B i) := by
    intro i;fin_cases i
    · simpa [A,B,P,ite_apply] using hJ₀
    · simpa [A,B,P,ite_apply] using hJ₁
  have hABnd : A 0 ∪ A 1 = C := hA.union_eq
  have hBBnd : B 0 ∪ B 1 = D := by
    cases flip
    · exact hB.union_eq
    · exact union_comm _ _ |>.trans hB.union_eq
  have hmem (i : Fin 2) : A i ∪ P ∪ B i ⊆ twoTriangleRegion A B P := by
    intro z hz
    have hzcl := frontier_subset_closure ((jordan_curve_theorem (hJ i)).frontier_inside.symm ▸ hz)
    fin_cases i
    · exact Or.inl hzcl
    · exact Or.inr hzcl
  refine ⟨⟨a,x,y,A,B,P,haF,haG,hAi,hBi,hP,?_,?_,?_,hJ,?_,hABnd,hBBnd,?_⟩⟩
  · intro i
    ext z
    constructor
    · intro hz
      exact hPC ▸ (show z ∈ P ∩ C from ⟨hz.2,hAC i hz.1⟩)
    · rintro rfl
      exact ⟨(hAi i).right_mem,hP.left_mem⟩
  · intro i
    ext z
    constructor
    · intro hz
      exact hCD ▸ (show z ∈ C ∩ D from ⟨hAC i hz.1,hBD i hz.2⟩)
    · rintro rfl
      exact ⟨(hAi i).left_mem,(hBi i).left_mem⟩
  · intro i
    ext z
    constructor
    · intro hz
      exact hPD ▸ (show z ∈ P ∩ D from ⟨hz.1,hBD i hz.2⟩)
    · rintro rfl
      exact ⟨hP.right_mem,(hBi i).right_mem⟩
  · simpa [A,B,P,ite_apply] using hmeet
  · intro u v hf w hw
    obtain ⟨hne,hz⟩ := hcover u v hf w hw
    refine ⟨hne,?_⟩
    rcases hz with (hz | hz) | hz
    · change _ ∈ C at hz
      rw [← hABnd] at hz
      rcases hz with hz | hz
      · exact hmem 0 (Or.inl (Or.inl hz))
      · exact hmem 1 (Or.inl (Or.inl hz))
    · change _ ∈ D at hz
      rw [← hBBnd] at hz
      rcases hz with hz | hz
      · exact hmem 0 (Or.inr hz)
      · exact hmem 1 (Or.inr hz)
    · have hh := hcover' hz
      simpa [twoTriangleRegion,A,B,P,ite_apply] using hh

/-- The glued relative Schoenflies construction matches the two full line
boundaries, as sets, and the actual common infinity point. -/
theorem proper_pair_diagram_homeomorphism
    {F G F' G' : C(ℝ,Plane)} (d : ProperPairDiagram F G) (e : ProperPairDiagram F' G') :
    ∃ f g : Plane → Plane,
      IsHomeoOn f g (twoTriangleRegion d.A d.B d.P) (twoTriangleRegion e.A e.B e.P) ∧
      f d.pole = e.pole ∧
      f '' insert d.pole (invert d.pole '' range F) = insert e.pole (invert e.pole '' range F') ∧
      f '' insert d.pole (invert d.pole '' range G) = insert e.pole (invert e.pole '' range G') := by
  obtain ⟨f,g,hfg,hpole,-,hA,hB⟩ := two_triangle_region_homeomorphism
    d.A d.B e.A e.B d.P e.P d.pole d.x d.y e.pole e.x e.y
    d.arcA d.arcB d.arcP e.arcA e.arcB e.arcP
    d.meetAP d.meetAB d.meetPB e.meetAP e.meetAB e.meetPB d.jordan e.jordan d.meet e.meet
  refine ⟨f,g,hfg,hpole,?_,?_⟩
  · rw [← d.boundaryA,← e.boundaryA,image_union,hA,hA]
  · rw [← d.boundaryB,← e.boundaryB,image_union,hB,hB]

end CurveComplex.HyperellipticModel
