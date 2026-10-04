import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualTargetHalfBigonProtectedGraph
import CurveComplexGenusTwo.Topology.IntersectionParity.EmptyDiskSidesStatement

noncomputable section
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Actual ordinary/half-bigon geometry for prescribed marked arcs, INCLUDING
loops. No cleanliness or supported replacement field is included. -/
structure ActualMarkedTwoSideDisk (M : HyperellipticModel E S)
    (a b : EssentialMarkedArc M) where
  firstCorner : S
  secondCorner : S
  firstSide : C(Interval,S)
  secondSide : C(Interval,S)
  first_embedded : IsEmbedding firstSide
  second_embedded : IsEmbedding secondSide
  first_zero : firstSide 0 = firstCorner
  first_one : firstSide 1 = secondCorner
  second_zero : secondSide 0 = firstCorner
  second_one : secondSide 1 = secondCorner
  first_on_curve : range firstSide ⊆ a.val.image
  second_on_curve : range secondSide ⊆ b.val.image
  sides_inter : range firstSide ∩ range secondSide = {firstCorner,secondCorner}
  disk : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)
  disk_embedded : IsEmbedding disk
  boundary_eq : disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
    range firstSide ∪ range secondSide
  marks_are_corners : ∀ p ∈ range disk, p ∈ M.cover.branch → p ∈ ({firstCorner,secondCorner} : Set S)

def ActualMarkedTwoSideDisk.openInterior {M : HyperellipticModel E S}
    {a b : EssentialMarkedArc M} (B : ActualMarkedTwoSideDisk M a b) : Set S :=
  B.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}

/-- An actual transverse marked contact on an empty bigon side must be a
corner. The proof includes marked half-bigons and selected loop arcs; neither
a clean side nor a corner-rounding receipt is assumed. -/
theorem actual_empty_marked_bigon_first_side_clean
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ht : ∀ p ∈ ArcSurgery.crossings M a b, ArcSurgery.CrossesInDisk M b a p)
    (B : ActualMarkedTwoSideDisk M a b)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    range B.firstSide ∩ b.val.image = {B.firstCorner,B.secondCorner} := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    Subtype.connectedSpace (isConnected_sphere
      (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
      0 (by norm_num))
  letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
  letI := (actualSphereSmoothAtlas M).charts
  letI := (actualSphereSmoothAtlas M).manifold
  letI : ClosedSurface S := {}
  apply Set.Subset.antisymm
  · rintro p ⟨hpf, hpb⟩
    by_contra hpnot
    have hpg : p ∉ Set.range B.secondSide := by
      intro h
      exact hpnot (B.sides_inter ▸ (show p ∈ Set.range B.firstSide ∩ Set.range B.secondSide from ⟨hpf,h⟩))
    have hpab : p ∈ a.val.image ∩ b.val.image := ⟨B.first_on_curve hpf,hpb⟩
    have hpBoundary' : p ∈ range B.disk := Set.image_subset_range _ _
      (B.boundary_eq.symm ▸ (show p ∈ range B.firstSide ∪ range B.secondSide from Or.inl hpf))
    have hnotmark : p ∉ M.cover.branch := fun hm => hpnot (B.marks_are_corners p hpBoundary' hm)
    obtain ⟨U,hU,hpU,hmarkfree,h,hpzero,hbaxis,haaxis⟩ := ht p ⟨⟨hpab.1,hnotmark⟩,hpab.2,hnotmark⟩
    let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
    have hV : IsOpen V :=
      (isOpen_lt (continuous_fst.abs) continuous_const).inter
        (isOpen_lt (continuous_snd.abs) continuous_const)
    have haxes (z : S) (hz : z ∈ U) :
        (z ∈ a.val.image ↔ (h ⟨z,hz⟩).val.1 = 0) ∧
        (z ∈ b.val.image ↔ (h ⟨z,hz⟩).val.2 = 0) := ⟨haaxis ⟨z,hz⟩,hbaxis ⟨z,hz⟩⟩
    have hgclosed : IsClosed (Set.range B.secondSide) :=
      by simpa only [Set.image_univ] using (isCompact_univ.image B.secondSide.continuous).isClosed
    let N : Set U := {x | (x : S) ∉ Set.range B.secondSide}
    have hN : IsOpen N := hgclosed.isOpen_compl.preimage continuous_subtype_val
    let O : Set (ℝ × ℝ) := Subtype.val '' (h '' N)
    have hO : IsOpen O := (hV.isOpenEmbedding_subtypeVal).isOpenMap _ (h.isOpenMap _ hN)
    have hzeroO : (0,0) ∈ O := ⟨h ⟨p,hpU⟩, ⟨⟨p,hpU⟩,hpg,rfl⟩,hpzero⟩
    obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO (0,0) hzeroO
    have hpBoundary : p ∈ B.disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [B.boundary_eq]; exact Or.inl hpf
    obtain ⟨w, hw, hwp⟩ := hpBoundary
    have hwn : ‖w.val‖ = 1 := by
      simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using hw
    let radial : C(Interval, Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      ⟨fun t => ⟨t.val • w.val, by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t.property.1, hwn, mul_one]
        exact t.property.2⟩, by fun_prop⟩
    have honecl : (1 : Interval) ∈ closure (Set.Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
      exact ⟨by norm_num,le_rfl⟩
    have hpcl : p ∈ closure B.openInterior := by
      have hcl : (B.disk ∘ radial) '' closure (Set.Ioo (0 : Interval) 1) ⊆
          closure ((B.disk ∘ radial) '' Set.Ioo (0 : Interval) 1) :=
        image_closure_subset_closure_image (B.disk.continuous.comp radial.continuous)
      have him : (B.disk ∘ radial) '' Set.Ioo (0 : Interval) 1 ⊆ B.openInterior := by
        rintro z ⟨t,ht,rfl⟩
        refine ⟨radial t, ?_, rfl⟩
        change t.val • w.val ∈ Metric.ball 0 1
        simp only [Metric.mem_ball,dist_zero_right]
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1,hwn,mul_one] using (show t.val < (1 : ℝ) from ht.2)
      apply closure_mono him
      apply hcl
      refine ⟨1,honecl,?_⟩
      change B.disk (radial 1) = p
      have hr : radial 1 = w := by apply Subtype.ext; simp [radial]
      rw [hr]; exact hwp
    let T := Metric.ball (0 : ℝ × ℝ) ε
    have hTV : T ⊆ V := by
      intro z hz
      obtain ⟨v,hv,he⟩ := hball hz
      exact he ▸ v.property
    let jV : T → V := fun z => ⟨z.val,hTV z.property⟩
    let j : C(T,S) := ⟨fun z => (h.symm (jV z)).val, by fun_prop⟩
    have hjopen : IsOpenMap j := hU.isOpenMap_subtype_val.comp
      (h.symm.isOpenMap.comp (Metric.isOpen_ball.isOpenMap_subtype_val.subtype_mk _))
    let zeroT : T := ⟨0,by change dist (0 : ℝ × ℝ) 0 < ε; simpa only [dist_self] using hε⟩
    have hjzero : j zeroT = p := by
      have heq : jV zeroT = h ⟨p,hpU⟩ := by apply Subtype.ext; exact hpzero.symm
      change (h.symm (jV zeroT)).val = p
      rw [heq,h.symm_apply_apply]
    have hjN (z : T) : j z ∉ Set.range B.secondSide := by
      obtain ⟨v,⟨u,hu,he⟩,hv⟩ := hball z.property
      have heq : jV z = h u := by apply Subtype.ext; exact hv.symm.trans (congrArg Subtype.val he).symm
      change (h.symm (jV z)).val ∉ _
      rw [heq,h.symm_apply_apply]
      exact hu
    let K := Set.range B.disk
    let J : Set T := j ⁻¹' B.openInterior
    have hJopen : IsOpen J := (LocalSurgery.embedded_surface_disk_interior_isOpen B.disk B.disk_embedded).preimage j.continuous
    have hzeroJcl : zeroT ∈ closure J := by
      apply hjopen.preimage_closure_subset_closure_preimage
      change j zeroT ∈ closure B.openInterior
      rwa [hjzero]
    have hKclosed : IsClosed K := by
      simpa only [Set.image_univ] using (isCompact_univ.image B.disk.continuous).isClosed
    have haxis (z : T) (hz : j z ∈ K) (hznot : z ∉ J) : z.val.1 = 0 := by
      obtain ⟨v,hv⟩ := hz
      have hn : ‖v.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using v.property
      have hnnot : ¬ ‖v.val‖ < 1 := by
        intro hnlt
        apply hznot
        exact ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hnlt,hv⟩
      have hb : j z ∈ Set.range B.firstSide ∪ Set.range B.secondSide := by
        rw [← B.boundary_eq]
        exact ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using
          le_antisymm hn (le_of_not_gt hnnot),hv⟩
      have ha : j z ∈ a.val.image := B.first_on_curve (hb.resolve_right (hjN z))
      have hh := (haxes (j z) (h.symm (jV z)).property).1.mp ha
      have heq : h ⟨j z,(h.symm (jV z)).property⟩ = jV z := h.apply_symm_apply _
      simpa only [heq] using hh
    obtain ⟨z,hzall,hzJ⟩ := mem_closure_iff_nhds.mp hzeroJcl Set.univ (by simp)
    have hzaxis : z.val.1 ≠ 0 := by
      intro hz0
      have ha : j z ∈ a.val.image := (haxes (j z) (h.symm (jV z)).property).1.mpr (by
        have heq : h ⟨j z,(h.symm (jV z)).property⟩ = jV z := h.apply_symm_apply _
        simpa only [heq] using hz0)
      exact Set.disjoint_left.mp hempty hzJ (Or.inl ha)
    let σ : ℝ := z.val.1
    let H : Set T := {u | 0 < σ * u.val.1}
    have hzH : z ∈ H := by change 0 < z.val.1 * z.val.1; exact mul_self_pos.mpr hzaxis
    let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := σ • LinearMap.fst ℝ ℝ ℝ
    have hconv : Convex ℝ (T ∩ {u : ℝ × ℝ | 0 < σ * u.1}) :=
      (convex_ball (0 : ℝ × ℝ) ε).inter ((convex_Ioi (0 : ℝ)).linear_preimage L)
    have hHconn : IsPreconnected H := by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      have heq : Subtype.val '' H = T ∩ {u : ℝ × ℝ | 0 < σ * u.1} := by
        ext u
        constructor
        · rintro ⟨v,hv,rfl⟩; exact ⟨v.property,hv⟩
        · rintro ⟨hu,hv⟩; exact ⟨⟨u,hu⟩,hv,rfl⟩
      rw [heq]
      exact hconv.isPreconnected
    letI : PreconnectedSpace H := ⟨by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      simpa only [Set.image_univ,Subtype.range_val] using hHconn⟩
    let JH : Set H := Subtype.val ⁻¹' J
    have hJHeq : JH = (fun u : H => j u.val) ⁻¹' K := by
      ext u
      constructor
      · rintro ⟨v,hv,he⟩; exact ⟨v,he⟩
      · intro hu
        by_contra huJ
        have huaxis := haxis u.val hu huJ
        have hpos := u.property
        change 0 < σ * u.val.val.1 at hpos
        rw [huaxis,mul_zero] at hpos
        exact lt_irrefl 0 hpos
    have hJHclosed : IsClosed JH := by rw [hJHeq]; exact hKclosed.preimage (j.continuous.comp continuous_subtype_val)
    have hJHopen : IsOpen JH := hJopen.preimage continuous_subtype_val
    have hfull : JH = Set.univ := (show IsClopen JH from ⟨hJHclosed,hJHopen⟩).eq_univ
      ⟨⟨z,hzH⟩,hzJ⟩
    let e : T := ⟨(z.val.1,0),by
      have hzball := z.property
      change dist (z.val.1,0) (0 : ℝ × ℝ) < ε
      apply lt_of_le_of_lt ?_ hzball
      rw [Prod.dist_eq,Prod.dist_eq]
      change max (dist z.val.1 0) (dist (0 : ℝ) 0) ≤ max (dist z.val.1 0) (dist z.val.2 0)
      rw [dist_self]
      exact max_le_max le_rfl dist_nonneg⟩
    have heH : e ∈ H := by change 0 < z.val.1 * z.val.1; exact mul_self_pos.mpr hzaxis
    have heJ : e ∈ J := by
      have hm : (⟨e,heH⟩ : H) ∈ JH := hfull.symm ▸ Set.mem_univ _
      exact hm
    have heb : j e ∈ b.val.image := (haxes (j e) (h.symm (jV e)).property).2.mpr (by
      have heq : h ⟨j e,(h.symm (jV e)).property⟩ = jV e := h.apply_symm_apply _
      simpa only [heq] using (show e.val.2 = 0 from rfl))
    exact Set.disjoint_left.mp hempty heJ (Or.inr heb)
  · intro p hp
    rcases Set.mem_insert_iff.mp hp with hp | hp
    · subst p
      exact ⟨⟨0,B.first_zero⟩,B.second_on_curve ⟨0,B.second_zero⟩⟩
    · have hp' : p = B.secondCorner := Set.mem_singleton_iff.mp hp
      subst p
      exact ⟨⟨1,B.first_one⟩,B.second_on_curve ⟨1,B.second_one⟩⟩

#print axioms actual_empty_marked_bigon_first_side_clean
end CurveComplex.HyperellipticModel
