import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Schoenflies.Plane

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- An actual old-axis/new-affine graph chart yields the marked-free disk chart
used by relative arc surgery, with the correct axis order. -/
theorem actual_affine_graph_crosses_in_disk
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (e0 : OpenPartialHomeomorph S Plane) (p : S) (hp : p ∈ e0.source)
    (hmarks : Disjoint e0.source (M.cover.branch : Set S))
    (hp0 : e0 p 0 = 0) (m : ℝ)
    (ha : ∀ x ∈ e0.source, x ∈ a.val.image ↔ e0 x 0 = 0)
    (hb : ∀ x ∈ e0.source, x ∈ b.val.image ↔ e0 x 1 = e0 p 1+m*e0 x 0) :
    ArcSurgery.CrossesInDisk M a b p := by
  let L : Plane ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let shear : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := {
    toEquiv := {
      toFun := fun z => (z.1,z.2-e0 p 1-m*z.1)
      invFun := fun z => (z.1,z.2+e0 p 1+m*z.1)
      left_inv := by intro z; apply Prod.ext <;> simp <;> ring
      right_inv := by intro z; apply Prod.ext <;> simp <;> ring }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F := L.trans shear
  let Q := e0.trans F.toOpenPartialHomeomorph
  have hQsource : Q.source = e0.source := by simp [Q,OpenPartialHomeomorph.trans_source]
  have hpQ : p ∈ Q.source := hQsource.symm ▸ hp
  have hQzero : Q p = (0,0) := by
    change (e0 p 0,e0 p 1-e0 p 1-m*e0 p 0) = (0,0)
    simp [hp0]
  have hzero : (0,0) ∈ Q.target := hQzero ▸ Q.map_source hpQ
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (Q.open_target.mem_nhds hzero)
  let D : Set (ℝ × ℝ) := {z | |z.1| < R ∧ |z.2| < R}
  have hD : IsOpen D := by
    change IsOpen ({z : ℝ × ℝ | |z.1| < R} ∩ {z : ℝ × ℝ | |z.2| < R})
    exact (isOpen_lt continuous_fst.abs continuous_const).inter
      (isOpen_lt continuous_snd.abs continuous_const)
  have hDsub : D ⊆ Q.target := by
    intro z hz
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq]
    simpa only [Real.dist_eq,sub_zero] using max_lt hz.1 hz.2
  let P := Q.trans (OpenPartialHomeomorph.ofSet D hD)
  have hPtarget : P.target = D := by
    simp [P,OpenPartialHomeomorph.trans_target,Set.inter_eq_left.mpr hDsub]
  have hpP : p ∈ P.source := by
    change p ∈ Q.source ∧ Q p ∈ D
    exact ⟨hpQ,by rw [hQzero]; change |(0:ℝ)| < R ∧ |(0:ℝ)| < R; simpa using And.intro hR hR⟩
  let scale : D ≃ₜ {z : ℝ × ℝ // |z.1| < 1 ∧ |z.2| < 1} := {
    toEquiv := {
      toFun := fun z => ⟨(z.val.2/R,z.val.1/R),by
        constructor
        · rw [abs_div,abs_of_pos hR]; exact (div_lt_one hR).mpr z.property.2
        · rw [abs_div,abs_of_pos hR]; exact (div_lt_one hR).mpr z.property.1⟩
      invFun := fun z => ⟨(R*z.val.2,R*z.val.1),by
        constructor
        · rw [abs_mul,abs_of_pos hR]; nlinarith [z.property.2]
        · rw [abs_mul,abs_of_pos hR]; nlinarith [z.property.1]⟩
      left_inv := by
        intro z; apply Subtype.ext; apply Prod.ext
        · exact mul_div_cancel₀ z.val.1 hR.ne'
        · exact mul_div_cancel₀ z.val.2 hR.ne'
      right_inv := by intro z; apply Subtype.ext; apply Prod.ext <;> simp [hR.ne'] }
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let e := P.toHomeomorphSourceTarget.trans ((Homeomorph.setCongr hPtarget).trans scale)
  have hsource (x : S) (hx : x ∈ P.source) : x ∈ e0.source :=
    hQsource ▸ hx.1
  refine ⟨P.source,P.open_source,hpP,?_,e,?_,?_,?_⟩
  · exact hmarks.mono hsource Set.Subset.rfl
  · change ((e0 p 1-e0 p 1-m*e0 p 0)/R,e0 p 0/R) = (0,0)
    simp [hp0]
  · intro x
    change x.val ∈ a.val.image ↔ e0 x.val 0/R = 0
    rw [ha x.val (hsource x.val x.property)]
    simp [hR.ne']
  · intro x
    change x.val ∈ b.val.image ↔ (e0 x.val 1-e0 p 1-m*e0 x.val 0)/R = 0
    rw [hb x.val (hsource x.val x.property)]
    simp only [div_eq_zero_iff,hR.ne',or_false]
    constructor <;> intro h <;> linarith

end CurveComplex.HyperellipticModel
