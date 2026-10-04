import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualLocalizedCrossingChart
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualSideInitialAxisRay
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000

theorem actual_unmarked_disk_corner_selected_axis
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (old : J → EssentialMarkedArc M) (a b : EssentialMarkedArc M)
    (B : ActualMarkedTwoSideDisk M a b)
    (htab : ∀ p ∈ ArcSurgery.crossings M a b, CrossesInDisk M a b p)
    (hcorners : ∀ j p, p ∈ ({B.firstCorner,B.secondCorner} : Set S) →
      p ∉ M.cover.branch → p ∉ (old j).val.image)
    (p : S) (hpcorner : p ∈ ({B.firstCorner,B.secondCorner} : Set S))
    (hpmark : p ∉ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ F : OpenPartialHomeomorph S Plane, ∃ ell : ℝ,
      p ∈ F.source ∧ F p=0 ∧ F.source ⊆ W ∧ 0 < ell ∧
      Disjoint F.source (M.cover.branch : Set S) ∧
      (∀ j, Disjoint F.source (old j).val.image) ∧
      (∀ x ∈ F.source, x ∈ b.val.image ↔ F x 1=0) ∧
      (∀ x ∈ F.source, x ∈ a.val.image ↔ F x 0=0) ∧
      ∀ x ∈ Icc (0:ℝ) ell, Plane.mk x 0 ∈ F.target ∧
        F.symm (Plane.mk x 0) ∈ range B.secondSide := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let W' := W ∩ ⋂ j, (old j).val.imageᶜ
  have hW' : IsOpen W' := hW.inter (isOpen_iInter_of_finite (fun j =>
    (isCompact_range (old j).val.continuous).isClosed.isOpen_compl))
  have hpW' : p ∈ W' := ⟨hpW,Set.mem_iInter.mpr (fun j => hcorners j p hpcorner hpmark)⟩
  have hpA : p ∈ a.val.image := by
    rcases hpcorner with he|he
    · exact B.first_on_curve ⟨0,B.first_zero.trans he.symm⟩
    · exact B.first_on_curve ⟨1,B.first_one.trans he.symm⟩
  have hpB : p ∈ b.val.image := by
    rcases hpcorner with he|he
    · exact B.second_on_curve ⟨0,B.second_zero.trans he.symm⟩
    · exact B.second_on_curve ⟨1,B.second_one.trans he.symm⟩
  have hpCross := htab p ⟨⟨hpA,hpmark⟩,hpB,hpmark⟩
  have hpCross' : CrossesInDisk M b a p := by
    obtain ⟨U,hU,hpU,hmark,e,he0,ha,hb⟩ := hpCross
    let Q := {q : ℝ × ℝ // |q.1| < 1 ∧ |q.2| < 1}
    let swap : Q ≃ₜ Q := (Homeomorph.prodComm ℝ ℝ).subtype (fun _ => and_comm)
    refine ⟨U,hU,hpU,hmark,e.trans swap,?_,hb,ha⟩
    change ((e ⟨p,hpU⟩).val.2,(e ⟨p,hpU⟩).val.1)=(0,0)
    rw [he0]
  obtain ⟨G,hpG,hGW,hGp,hmarks,hBaxis,hAaxis⟩ :=
    actual_localized_marked_crossing_chart M b a p hpCross' W' hW' hpW'
  let L : (ℝ × ℝ) ≃ₜ Plane := {
    toFun := fun q => Plane.mk q.1 q.2
    invFun := fun z => (z 0,z 1)
    left_inv := by intro q; rfl
    right_inv := by intro z; ext i; fin_cases i <;> rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F0 := G.transHomeomorph L
  have hF0s : F0.source=G.source := rfl
  have hF0p : F0 p=0 := by
    change Plane.mk (G p).1 (G p).2=0
    rw [hGp]
    ext i
    fin_cases i <;> rfl
  obtain ⟨side,hside,hside0,hSideRange⟩ :
      ∃ side : C(Interval,S), IsEmbedding side ∧ side 0=p ∧ range side=range B.secondSide := by
    rcases hpcorner with he|he
    · exact ⟨B.secondSide,B.second_embedded,B.second_zero.trans he.symm,rfl⟩
    · let q : C(Interval,S) := ⟨B.secondSide ∘ unitInterval.symmHomeomorph,
        B.secondSide.continuous.comp unitInterval.symmHomeomorph.continuous⟩
      refine ⟨q,B.second_embedded.comp unitInterval.symmHomeomorph.isEmbedding,?_,?_⟩
      · change B.secondSide (unitInterval.symmHomeomorph 0)=p
        simpa using B.second_one.trans he.symm
      · ext x
        constructor
        · rintro ⟨t,rfl⟩
          exact ⟨unitInterval.symmHomeomorph t,rfl⟩
        · rintro ⟨t,rfl⟩
          refine ⟨unitInterval.symmHomeomorph.symm t,?_⟩
          change B.secondSide (unitInterval.symmHomeomorph (unitInterval.symmHomeomorph.symm t))=B.secondSide t
          rw [unitInterval.symmHomeomorph.apply_symm_apply]
  obtain ⟨σ,ell,hσ,hell,hRay⟩ := CurveComplex.actual_embedded_side_initial_chart_axis_ray
    side hside F0 (hside0.symm ▸ hpG) (hside0.symm ▸ hF0p)
    (fun t ht => (hBaxis _ ht).mp (B.second_on_curve (hSideRange ▸ Set.mem_range_self t)))
  let N : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (σ*z 0) (z 1)
    invFun := fun z => Plane.mk (σ*z 0) (z 1)
    left_inv := by intro z; ext i; fin_cases i <;> rcases hσ with rfl|rfl <;> simp
    right_inv := by intro z; ext i; fin_cases i <;> rcases hσ with rfl|rfl <;> simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let F := F0.transHomeomorph N
  have hFs : F.source=G.source := rfl
  have hFx0 (x : S) : F x 0=σ*(G x).1 := rfl
  have hFx1 (x : S) : F x 1=(G x).2 := rfl
  have hFp : F p=0 := by
    ext i
    fin_cases i
    · change F p 0=0
      rw [hFx0,hGp]; simp
    · change F p 1=0
      rw [hFx1,hGp]
  refine ⟨F,ell,hpG,hFp,(fun x hx => (hGW hx).1),hell,hmarks,?_,?_,?_,?_⟩
  · intro j
    apply Set.disjoint_left.mpr
    intro x hx ho
    exact Set.mem_iInter.mp (hGW hx).2 j ho
  · intro x hx
    rw [hFx1]
    exact hBaxis x hx
  · intro x hx
    rw [hFx0,hAaxis x hx]
    rcases hσ with rfl|rfl <;> simp
  · intro x hx
    obtain ⟨hxT,hxSide⟩ := hRay x hx
    have hN : N (Plane.mk (σ*x) 0)=Plane.mk x 0 := by
      ext i
      fin_cases i <;> rcases hσ with rfl|rfl <;> simp [N]
    have hFt := F.map_source (F0.map_target hxT)
    change N (F0 (F0.symm (Plane.mk (σ*x) 0))) ∈ F.target at hFt
    rw [F0.right_inv hxT,hN] at hFt
    refine ⟨hFt,?_⟩
    change F0.symm (N.symm (Plane.mk x 0)) ∈ range B.secondSide
    change F0.symm (Plane.mk (σ*x) 0) ∈ range B.secondSide
    exact hSideRange ▸ hxSide
end CurveComplex.HyperellipticModel
