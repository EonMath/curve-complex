import CurveComplexGenusTwo.Topology.IntersectionParity.BigonDiskData

open Set Topology

namespace CurveComplex.LocalSurgery

/-- For a transverse pair, a disk bounded by their subarcs and disjoint from
both curves in its open interior has no extra intersection along either side. -/
theorem empty_two_curve_disk_has_clean_sides
    {S : Type} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
    (a b : EssentialCurve S) (ht : Transverse a.val b.val)
    (B : TwoCurveDisk a.val b.val)
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    Set.range B.firstSide ∩ b.val.image = {B.firstCorner, B.secondCorner} ∧
      Set.range B.secondSide ∩ a.val.image = {B.firstCorner, B.secondCorner} := by
  classical
  have firstClean (a b : EssentialCurve S) (ht : Transverse a.val b.val)
      (B : TwoCurveDisk a.val b.val)
      (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
      Set.range B.firstSide ∩ b.val.image = {B.firstCorner, B.secondCorner} := by
    apply Set.Subset.antisymm
    · rintro p ⟨hpf, hpb⟩
      by_contra hpnot
      have hpg : p ∉ Set.range B.secondSide := by
        intro h
        exact hpnot (B.sides_inter ▸ (show p ∈ Set.range B.firstSide ∩ Set.range B.secondSide from ⟨hpf,h⟩))
      have hpab : p ∈ a.val.image ∩ b.val.image := ⟨B.first_on_curve hpf,hpb⟩
      obtain ⟨U,V,hpU,h,hU,hV,hpzero,haxes⟩ := ht.2 p hpab
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
      have hJopen : IsOpen J := (embedded_surface_disk_interior_isOpen B.disk B.disk_embedded).preimage j.continuous
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
  refine ⟨firstClean a b ht B hempty, ?_⟩
  let D : TwoCurveDisk b.val a.val := {
    firstCorner := B.firstCorner, secondCorner := B.secondCorner,
    corners_ne := B.corners_ne, firstSide := B.secondSide, secondSide := B.firstSide,
    first_embedded := B.second_embedded, second_embedded := B.first_embedded,
    first_zero := B.second_zero, second_zero := B.first_zero,
    first_one := B.second_one, second_one := B.first_one,
    first_on_curve := B.second_on_curve, second_on_curve := B.first_on_curve,
    sides_inter := by rw [Set.inter_comm]; exact B.sides_inter,
    disk := B.disk, disk_embedded := B.disk_embedded,
    boundary_eq := by rw [B.boundary_eq, Set.union_comm] }
  apply firstClean b a (transverse_symm_of_chart ht) D
  simpa only [D, TwoCurveDisk.openInterior, Set.union_comm] using hempty

end CurveComplex.LocalSurgery
