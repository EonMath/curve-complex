import CurveComplexGenusTwo.Dictionary.ActualCircle24Components
import CurveComplexGenusTwo.Topology.ActualMain14FinitePreparation.Main14ActualCircle24GivenUnionComponentPairingLocalNamedPROVED
import CurveComplexGenusTwo.Topology.FrontierCircle.SurfaceInvarianceProbe
import CurveComplexGenusTwo.Topology.ActualSphereExterior.SpherePairAnnulus
import CurveComplexGenusTwo.Topology.ActualSphereExterior.SphereAnnulusPartition

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

private theorem scratch_disk_side_eq
    {S : Type} [TopologicalSpace S]
    (C U A B : Set S)
    (hUopen : IsOpen U) (hUconn : IsConnected U) (hUn : U.Nonempty)
    (hUavoid : Disjoint U C) (hUcl : closure U ⊆ U ∪ C)
    (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hAconn : IsConnected A) (hBconn : IsConnected B)
    (hAB : Disjoint A B) (hcover : A ∪ B = Cᶜ) :
    U = A ∨ U = B := by
  have hUsub : U ⊆ A ∪ B := by
    rw [hcover]
    intro x hxU hxC
    exact Set.disjoint_left.mp hUavoid hxU hxC
  have hAcover : A ⊆ U ∪ (closure U)ᶜ := by
    intro x hxA
    by_cases hx : x ∈ closure U
    · rcases hUcl hx with hxU | hxC
      · exact Or.inl hxU
      · have hxnot : x ∈ Cᶜ := hcover ▸ Or.inl hxA
        exact False.elim (hxnot hxC)
    · exact Or.inr hx
  have hBcover : B ⊆ U ∪ (closure U)ᶜ := by
    intro x hxB
    by_cases hx : x ∈ closure U
    · rcases hUcl hx with hxU | hxC
      · exact Or.inl hxU
      · have hxnot : x ∈ Cᶜ := hcover ▸ Or.inr hxB
        exact False.elim (hxnot hxC)
    · exact Or.inr hx
  have hseparate : Disjoint U (closure U)ᶜ := by
    exact Set.disjoint_left.mpr (fun x hxU hxCl => hxCl (subset_closure hxU))
  rcases hUconn.isPreconnected.subset_or_subset hAopen hBopen hAB hUsub with hUA | hUB
  · rcases hAconn.isPreconnected.subset_or_subset hUopen isClosed_closure.isOpen_compl
      hseparate hAcover with hAU | hAout
    · exact Or.inl (Set.Subset.antisymm hUA hAU)
    · obtain ⟨x,hx⟩ := hUn
      exact False.elim ((hAout (hUA hx)) (subset_closure hx))
  · rcases hBconn.isPreconnected.subset_or_subset hUopen isClosed_closure.isOpen_compl
      hseparate hBcover with hBU | hBout
    · exact Or.inr (Set.Subset.antisymm hUB hBU)
    · obtain ⟨x,hx⟩ := hUn
      exact False.elim ((hBout (hUB hx)) (subset_closure hx))

theorem actual_two_disjoint_circle24_closed_disks_exterior_connected
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (Uc Ud : Set S)
    (fc : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure Uc)
    (fd : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure Ud)
    (hcBoundary : ∀ x, (fc x : S) ∈ c.val.image ↔ ‖x.val‖ = 1)
    (hdBoundary : ∀ x, (fd x : S) ∈ d.val.image ↔ ‖x.val‖ = 1)
    (hcInterior : ∀ x, (fc x : S) ∈ Uc ↔ ‖x.val‖ < 1)
    (hdInterior : ∀ x, (fd x : S) ∈ Ud ↔ ‖x.val‖ < 1)
    (hdisj : Disjoint (closure Uc) (closure Ud)) :
    IsConnected ((closure Uc ∪ closure Ud)ᶜ) := by
  let : ChartedSpace Schoenflies.Plane S := M.sphere.symm.chartedSpace
  have hChartInterior (U : Set S)
      (f : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure U)
      (hInt : ∀ x, (f x : S) ∈ U ↔ ‖x.val‖ < 1) :
      U = interior (closure U) := by
    let g : Metric.closedBall (0 : Schoenflies.Plane) 1 → S :=
      fun z => (f z : S)
    have hg : Topology.IsEmbedding g :=
      Topology.IsEmbedding.subtypeVal.comp f.isEmbedding
    have hgrange : Set.range g = closure U := by
      ext x
      constructor
      · rintro ⟨z,rfl⟩
        exact (f z).property
      · intro hx
        exact ⟨f.symm ⟨x,hx⟩,congrArg Subtype.val (f.apply_symm_apply ⟨x,hx⟩)⟩
    ext x
    constructor
    · intro hx
      let z := f.symm ⟨x,subset_closure hx⟩
      have hzEq : (f z : S) = x :=
        congrArg Subtype.val (f.apply_symm_apply ⟨x,subset_closure hx⟩)
      have hzi : ‖z.val‖ < 1 := (hInt z).mp (hzEq ▸ hx)
      have hzInterior : (z : Schoenflies.Plane) ∈
          interior (Metric.closedBall (0 : Schoenflies.Plane) 1) := by
        rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
        simpa only [Metric.mem_ball, dist_zero_right] using hzi
      rw [← hgrange]
      exact hzEq ▸ (CurveComplex.embedded_planar_region_interior_probe
        _ g hg ⟨z,hzInterior,rfl⟩)
    · intro hx
      have hxCl : x ∈ closure U := interior_subset hx
      let z := f.symm ⟨x,hxCl⟩
      have hzEq : (f z : S) = x :=
        congrArg Subtype.val (f.apply_symm_apply ⟨x,hxCl⟩)
      have hzInterior : (z : Schoenflies.Plane) ∈
          interior (Metric.closedBall (0 : Schoenflies.Plane) 1) :=
        (CurveComplex.embedded_planar_region_interior_iff_probe _ g hg z).mp
          (by change (f z : S) ∈ interior (Set.range g)
              rw [hgrange,hzEq]
              exact hx)
      have hzi : ‖z.val‖ < 1 := by
        rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)] at hzInterior
        simpa only [Metric.mem_ball, dist_zero_right] using hzInterior
      exact hzEq ▸ (hInt z).mpr hzi
  have hUcRegular : Uc = interior (closure Uc) :=
    hChartInterior Uc fc hcInterior
  have hUdRegular : Ud = interior (closure Ud) :=
    hChartInterior Ud fd hdInterior
  have hUcOpen : IsOpen Uc := hUcRegular ▸ isOpen_interior
  have hUdOpen : IsOpen Ud := hUdRegular ▸ isOpen_interior
  have hUcImage : Uc =
      (fun z : Metric.closedBall (0 : Schoenflies.Plane) 1 => (fc z : S)) ''
        {z | ‖z.val‖ < 1} := by
    ext x
    constructor
    · intro hx
      let z := fc.symm ⟨x, subset_closure hx⟩
      have hzEq : (fc z : S) = x :=
        congrArg Subtype.val (fc.apply_symm_apply ⟨x, subset_closure hx⟩)
      exact ⟨z, (hcInterior z).mp (hzEq ▸ hx), hzEq⟩
    · rintro ⟨z,hz,rfl⟩
      exact (hcInterior z).mpr hz
  have hUdImage : Ud =
      (fun z : Metric.closedBall (0 : Schoenflies.Plane) 1 => (fd z : S)) ''
        {z | ‖z.val‖ < 1} := by
    ext x
    constructor
    · intro hx
      let z := fd.symm ⟨x, subset_closure hx⟩
      have hzEq : (fd z : S) = x :=
        congrArg Subtype.val (fd.apply_symm_apply ⟨x, subset_closure hx⟩)
      exact ⟨z, (hdInterior z).mp (hzEq ▸ hx), hzEq⟩
    · rintro ⟨z,hz,rfl⟩
      exact (hdInterior z).mpr hz
  have hDiskInteriorConnected :
      IsConnected
        {z : Metric.closedBall (0 : Schoenflies.Plane) 1 | ‖z.val‖ < 1} := by
    let B := Metric.ball (0 : Schoenflies.Plane) 1
    letI : ConnectedSpace B :=
      isConnected_iff_connectedSpace.mp (Metric.isConnected_ball (by norm_num))
    let g : B → Metric.closedBall (0 : Schoenflies.Plane) 1 :=
      fun z => ⟨z.val, by
        have hz : ‖z.val‖ < 1 := by
          simpa only [B, Metric.mem_ball, dist_zero_right] using z.property
        simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt hz⟩
    have hg : Continuous g := by fun_prop
    have hImage : g '' (Set.univ : Set B) =
        {z : Metric.closedBall (0 : Schoenflies.Plane) 1 | ‖z.val‖ < 1} := by
      ext z
      constructor
      · rintro ⟨b,_,rfl⟩
        simpa only [Set.mem_ofPred_eq, g, B, Metric.mem_ball, dist_zero_right]
          using b.property
      · intro hz
        let b : B := ⟨z.val, by
          simpa only [B, Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq] using hz⟩
        exact ⟨b,Set.mem_univ b,Subtype.ext rfl⟩
    rw [← hImage]
    exact isConnected_univ.image g hg.continuousOn
  have hUcConnected : IsConnected Uc := by
    rw [hUcImage]
    exact hDiskInteriorConnected.image _
      ((continuous_subtype_val.comp fc.continuous).continuousOn)
  have hUdConnected : IsConnected Ud := by
    rw [hUdImage]
    exact hDiskInteriorConnected.image _
      ((continuous_subtype_val.comp fd.continuous).continuousOn)
  have hUcAvoid : Disjoint Uc c.val.image := by
    apply Set.disjoint_left.mpr
    intro x hxU hxC
    let z := fc.symm ⟨x, subset_closure hxU⟩
    have hzEq : (fc z : S) = x :=
      congrArg Subtype.val (fc.apply_symm_apply ⟨x, subset_closure hxU⟩)
    have hzi : ‖z.val‖ < 1 := (hcInterior z).mp (hzEq ▸ hxU)
    have hzb : ‖z.val‖ = 1 := (hcBoundary z).mp (hzEq ▸ hxC)
    linarith
  have hUdAvoid : Disjoint Ud d.val.image := by
    apply Set.disjoint_left.mpr
    intro x hxU hxD
    let z := fd.symm ⟨x, subset_closure hxU⟩
    have hzEq : (fd z : S) = x :=
      congrArg Subtype.val (fd.apply_symm_apply ⟨x, subset_closure hxU⟩)
    have hzi : ‖z.val‖ < 1 := (hdInterior z).mp (hzEq ▸ hxU)
    have hzb : ‖z.val‖ = 1 := (hdBoundary z).mp (hzEq ▸ hxD)
    linarith
  have hUcClosureSub : closure Uc ⊆ Uc ∪ c.val.image := by
    intro x hx
    let z := fc.symm ⟨x,hx⟩
    have hzEq : (fc z : S) = x :=
      congrArg Subtype.val (fc.apply_symm_apply ⟨x,hx⟩)
    by_cases hi : ‖z.val‖ < 1
    · exact Or.inl (hzEq ▸ (hcInterior z).mpr hi)
    · have hzle : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      exact Or.inr (hzEq ▸ (hcBoundary z).mpr (le_antisymm hzle (le_of_not_gt hi)))
  have hUdClosureSub : closure Ud ⊆ Ud ∪ d.val.image := by
    intro x hx
    let z := fd.symm ⟨x,hx⟩
    have hzEq : (fd z : S) = x :=
      congrArg Subtype.val (fd.apply_symm_apply ⟨x,hx⟩)
    by_cases hi : ‖z.val‖ < 1
    · exact Or.inl (hzEq ▸ (hdInterior z).mpr hi)
    · have hzle : ‖z.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
      exact Or.inr (hzEq ▸ (hdBoundary z).mpr (le_antisymm hzle (le_of_not_gt hi)))
  letI : T2Space S := M.sphere.symm.t2Space
  have hUcNonempty : Uc.Nonempty := by
    let z : Metric.closedBall (0 : Schoenflies.Plane) 1 := ⟨0, by simp⟩
    exact ⟨(fc z : S), (hcInterior z).mpr (by simp [z])⟩
  have hUdNonempty : Ud.Nonempty := by
    let z : Metric.closedBall (0 : Schoenflies.Plane) 1 := ⟨0, by simp⟩
    exact ⟨(fd z : S), (hdInterior z).mpr (by simp [z])⟩
  obtain ⟨A,B,hAo,hBo,hAc,hBc,hAB,hABc,_,_,_,_,_,_,hclA,hclB⟩ :=
    M.puncturedCircle_closedSides c.val
  have hUcSide : Uc = A ∨ Uc = B :=
    scratch_disk_side_eq c.val.image Uc A B hUcOpen hUcConnected hUcNonempty
      hUcAvoid hUcClosureSub hAo hBo hAc hBc hAB hABc
  have hUcClosure : closure Uc = Uc ∪ c.val.image := by
    rcases hUcSide with he | he
    · rw [he]; exact hclA
    · rw [he]; exact hclB
  obtain ⟨P,Q,hPo,hQo,hPc,hQc,hPQ,hPQd,_,_,_,_,_,_,hclP,hclQ⟩ :=
    M.puncturedCircle_closedSides d.val
  have hUdSide : Ud = P ∨ Ud = Q :=
    scratch_disk_side_eq d.val.image Ud P Q hUdOpen hUdConnected hUdNonempty
      hUdAvoid hUdClosureSub hPo hQo hPc hQc hPQ hPQd
  have hUdClosure : closure Ud = Ud ∪ d.val.image := by
    rcases hUdSide with he | he
    · rw [he]; exact hclP
    · rw [he]; exact hclQ
  have hcIn : c.val.image ⊆ closure Uc := by
    rw [hUcClosure]
    exact Set.subset_union_right
  have hdIn : d.val.image ⊆ closure Ud := by
    rw [hUdClosure]
    exact Set.subset_union_right
  have hcd : Disjoint c.val.image d.val.image := hdisj.mono hcIn hdIn
  have hbranch : M.cover.branch.Nonempty := by
    apply Finset.card_pos.mp
    rw [M.cover.branch_card]
    norm_num
  obtain ⟨w,hw⟩ := hbranch
  have hwc : w ∉ c.val.image := by
    intro hc
    exact Set.disjoint_left.mp c.val.avoids_branch hc hw
  have hwd : w ∉ d.val.image := by
    intro hd
    exact Set.disjoint_left.mp d.val.avoids_branch hd hw
  obtain ⟨q,hq,hqc,hqd,hqcomp⟩ :=
    scratch_sphere_pair_annulus M c.val.curve d.val.curve w hwc hwd hcd
  obtain ⟨U,V,W,Z,hUo,hVo,hWo,hZo,hUconn,hVconn,hWconn,hZconn,
      hUV,hWZ,hVZ,hcoverc,hcoverd,hclU,hclV,hclW,hclZ,
      hdU,hcW,hqV,hqZ,hB,g,hg,hgmid⟩ :=
    scratch_sphere_annulus_partition M c.val.curve d.val.curve hcd q hq hqc hqd hqcomp
  have hUcV : Uc = V := by
    rcases scratch_disk_side_eq c.val.image Uc U V hUcOpen hUcConnected
        hUcNonempty hUcAvoid hUcClosureSub hUo hVo hUconn hVconn hUV hcoverc
      with he | he
    · have hdNonempty : d.val.image.Nonempty :=
        ⟨d.val.curve.map (Classical.choice inferInstance), Set.mem_range_self _⟩
      obtain ⟨x,hx⟩ := hdNonempty
      have hxUc : x ∈ Uc := he ▸ hdU hx
      exact False.elim (Set.disjoint_left.mp hdisj (subset_closure hxUc) (hdIn hx))
    · exact he
  have hUdZ : Ud = Z := by
    rcases scratch_disk_side_eq d.val.image Ud W Z hUdOpen hUdConnected
        hUdNonempty hUdAvoid hUdClosureSub hWo hZo hWconn hZconn hWZ hcoverd
      with he | he
    · have hcNonempty : c.val.image.Nonempty :=
        ⟨c.val.curve.map (Classical.choice inferInstance), Set.mem_range_self _⟩
      obtain ⟨x,hx⟩ := hcNonempty
      have hxUd : x ∈ Ud := he ▸ hcW hx
      exact False.elim (Set.disjoint_left.mp hdisj (hcIn hx) (subset_closure hxUd))
    · exact he
  let D : Set S := q '' {p : Circle × Interval |
    0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}
  have hD_eq : D = (closure Uc ∪ closure Ud)ᶜ := by
    ext x
    constructor
    · intro hx
      have hxRange : x ∈ Set.range q := by
        obtain ⟨p,hp,hpx⟩ := hx
        exact ⟨p,hpx⟩
      have hxV : x ∉ V := fun hv => Set.disjoint_left.mp hqV hxRange hv
      have hxZ : x ∉ Z := fun hz => Set.disjoint_left.mp hqZ hxRange hz
      have hxCurves : x ∉ c.val.image ∪ d.val.image := hqcomp.2.2.1 hx
      have hxUc : x ∉ closure Uc := by
        rw [hUcClosure,hUcV]
        intro hh
        rcases hh with hv | hc
        · exact hxV hv
        · exact hxCurves (Or.inl hc)
      have hxUd : x ∉ closure Ud := by
        rw [hUdClosure,hUdZ]
        intro hh
        rcases hh with hz | hd
        · exact hxZ hz
        · exact hxCurves (Or.inr hd)
      exact fun hh => hh.elim hxUc hxUd
    · intro hx
      have hxUc : x ∉ closure Uc := fun hh => hx (Or.inl hh)
      have hxUd : x ∉ closure Ud := fun hh => hx (Or.inr hh)
      have hxRange : x ∈ Set.range q := by
        rcases hB.symm ▸ (Set.mem_univ x) with (hqRange | hv) | hz
        · exact hqRange
        · exact False.elim (hxUc (subset_closure (hUcV.symm ▸ hv)))
        · exact False.elim (hxUd (subset_closure (hUdZ.symm ▸ hz)))
      obtain ⟨⟨z,t⟩,ht⟩ := hxRange
      have ht0 : 0 < (t : ℝ) := by
        rcases lt_or_eq_of_le t.property.1 with hp | he
        · exact hp
        · have he0 : t = 0 := Subtype.ext he.symm
          have hc : x ∈ c.val.image := by
            change x ∈ c.val.curve.image
            rw [← hqc]
            exact ⟨z, by simpa only [he0] using ht⟩
          exact False.elim (hxUc (hcIn hc))
      have ht1 : (t : ℝ) < 1 := by
        rcases lt_or_eq_of_le t.property.2 with hp | he
        · exact hp
        · have he1 : t = 1 := Subtype.ext he
          have hd : x ∈ d.val.image := by
            change x ∈ d.val.curve.image
            rw [← hqd]
            exact ⟨z, by simpa only [he1] using ht⟩
          exact False.elim (hxUd (hdIn hd))
      exact ⟨(z,t),⟨ht0,ht1⟩,ht⟩
  rw [← hD_eq]
  exact hqcomp.2.1
end CurveComplex.HyperellipticModel
