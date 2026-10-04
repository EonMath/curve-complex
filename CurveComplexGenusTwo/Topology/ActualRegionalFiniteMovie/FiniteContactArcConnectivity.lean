import CurveComplexGenusTwo.Topology.TopologicalArcJoin
import Mathlib.Topology.Connected.Basic
import Schoenflies.BoundaryContinuity2
import Schoenflies.Polygonal

open Set Topology Schoenflies

namespace RegionalFinitePosition

theorem segment_axis_contact_finite (x y : Plane) (hx : x 1 ≠ 0) :
    (segment ℝ x y ∩ {z : Plane | z 1 = 0}).Finite := by
  apply Set.Subsingleton.finite
  intro p hp q hq
  rw [segment_eq_image_lineMap] at hp hq
  obtain ⟨s,hs,hsp⟩ := hp.1
  obtain ⟨t,ht,htq⟩ := hq.1
  have hcoord (u : ℝ) : (AffineMap.lineMap x y u) 1 = (1-u)*x 1+u*y 1 := by
    simp [AffineMap.lineMap_apply_module]
  have hp0 : (1-s)*x 1+s*y 1 = 0 := by rw [← hcoord,hsp]; exact hp.2
  have hq0 : (1-t)*x 1+t*y 1 = 0 := by rw [← hcoord,htq]; exact hq.2
  have hxy : y 1-x 1 ≠ 0 := by
    intro h
    have h := sub_eq_zero.mp h
    rw [h] at hp0
    exact hx (by nlinarith)
  have hst : s = t := by
    have h : (s-t)*(y 1-x 1) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hxy)
  exact hsp.symm.trans (hst ▸ htq)

/-- A two-segment planar arc in a ball can be chosen with finite contact
with the horizontal axis, even when both endpoints lie on the axis. -/
theorem ball_finite_axis_arc (o x y : Plane) (r : ℝ)
    (hx : x ∈ Metric.ball o r) (hy : y ∈ Metric.ball o r) (hne : x ≠ y) :
    ∃ C ⊆ Metric.ball o r, IsArcBetween C x y ∧
      (C ∩ {z : Plane | z 1 = 0}).Finite := by
  have hε : 0 < r - dist x o := sub_pos.mpr hx
  have hinf : (Set.Ioo (0 : ℝ) ((r-dist x o)/2)).Infinite :=
    Set.Ioo_infinite (by positivity)
  obtain ⟨t,ht,htbad⟩ := hinf.exists_notMem_finite
    ((Set.finite_singleton (y 1-x 1)).insert (-x 1))
  have htzero : t ≠ -x 1 := fun h => htbad (Or.inl h)
  have hty : t ≠ y 1-x 1 := fun h => htbad (Or.inr (Set.mem_singleton_iff.mpr h))
  let z : Plane := x + Plane.mk 0 t
  have hz1 : z 1 = x 1+t := by simp [z,Plane.mk]
  have hz0 : z 1 ≠ 0 := by rw [hz1]; intro h; exact htzero (by linarith)
  have hzx : z ≠ x := by intro h; have h := congrArg (fun w : Plane => w 1) h; rw [hz1] at h; linarith [ht.1]
  have hzy : z ≠ y := by intro h; have h := congrArg (fun w : Plane => w 1) h; rw [hz1] at h; exact hty (by linarith)
  have hdist : dist z x = t := by
    rw [dist_eq_norm]
    simp [z,EuclideanSpace.norm_eq,Fin.sum_univ_two,Plane.mk,Real.sqrt_sq_eq_abs,
      abs_of_pos ht.1]
  have hz : z ∈ Metric.ball o r := by
    change dist z o < r
    calc
      dist z o ≤ dist z x + dist x o := dist_triangle _ _ _
      _ < r := by rw [hdist]; linarith [ht.2]
  obtain ⟨C,hC,hCarc⟩ := exists_arc_in_union_of_arcs
    (isArcBetween_segment hzx.symm) (isArcBetween_segment hzy) hne
  refine ⟨C,hC.trans (union_subset
    ((convex_ball o r).segment_subset hx hz)
    ((convex_ball o r).segment_subset hz hy)),hCarc,?_⟩
  have hleft : (segment ℝ x z ∩ {w : Plane | w 1 = 0}).Finite := by
    rw [segment_symm]
    exact segment_axis_contact_finite z x hz0
  apply (hleft.union (segment_axis_contact_finite z y hz0)).subset
  intro w hw
  exact (hC hw.1).elim (fun h => Or.inl ⟨h,hw.2⟩) (fun h => Or.inr ⟨h,hw.2⟩)

/-- A chart which places the comparison set in the horizontal axis supplies
the required finite-contact local joining operation. -/
theorem axis_chart_local_finite_contact
    (U A : Set Plane) (x : Plane)
    (E : OpenPartialHomeomorph Plane Plane) (hx : x ∈ E.source)
    (hEU : E.source ⊆ U)
    (haxis : ∀ z ∈ E.source, z ∈ A → E z 1 = 0) :
    ∃ V : Set Plane, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, x ≠ y → ∃ C ⊆ U, IsArcBetween C x y ∧ (C ∩ A).Finite := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (E.open_target.mem_nhds (E.map_source hx))
  let V : Set Plane := E.symm '' Metric.ball (E x) r
  have hV : IsOpen V := E.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
  have hVE : V ⊆ E.source := by
    rintro z ⟨w,hw,rfl⟩
    exact E.map_target (hball hw)
  refine ⟨V,hV,⟨E x,Metric.mem_ball_self hr,E.left_inv hx⟩,hVE.trans hEU,?_⟩
  intro y hy hxy
  have hyE := hVE hy
  have hyball : E y ∈ Metric.ball (E x) r := by
    obtain ⟨w,hw,rfl⟩ := hy
    rwa [E.right_inv (hball hw)]
  have hne : E x ≠ E y := fun h => hxy (E.injOn hx hyE h)
  obtain ⟨D,hD,hDa,hDfin⟩ := ball_finite_axis_arc (E x) (E x) (E y) r
    (Metric.mem_ball_self hr) hyball hne
  have hDT : D ⊆ E.target := hD.trans hball
  refine ⟨E.symm '' D,?_,?_,?_⟩
  · rintro z ⟨w,hw,rfl⟩
    exact hEU (E.map_target (hDT hw))
  · simpa only [E.left_inv hx,E.left_inv hyE] using
      hDa.image_of_injOn hDT E.symm.continuousOn E.symm.injOn
  · apply (hDfin.image E.symm).subset
    rintro z ⟨⟨w,hw,rfl⟩,hzA⟩
    refine ⟨w,⟨hw,?_⟩,rfl⟩
    have hh := haxis (E.symm w) (E.map_target (hDT hw)) hzA
    rwa [E.right_inv (hDT hw)] at hh

/-- Finite-contact arcs join globally when they join locally in a connected
open planar region. Arc union simplification retains the finite contact set. -/
theorem finite_contact_arc_of_local
    (U A : Set Plane) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlocal : ∀ x ∈ U, ∃ V : Set Plane, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, x ≠ y → ∃ C ⊆ U, IsArcBetween C x y ∧ (C ∩ A).Finite)
    (x y : Plane) (hx : x ∈ U) (hy : y ∈ U) (hne : x ≠ y) :
    ∃ C ⊆ U, IsArcBetween C x y ∧ (C ∩ A).Finite := by
  classical
  let R (x y : Plane) : Prop := x = y ∨
    ∃ C ⊆ U, IsArcBetween C x y ∧ (C ∩ A).Finite
  have hrefl (x : Plane) : R x x := Or.inl rfl
  have hsymm {x y : Plane} (h : R x y) : R y x := by
    rcases h with rfl | ⟨C,hCU,hC,hCA⟩
    · exact hrefl _
    · exact Or.inr ⟨C,hCU,hC.reverse,hCA⟩
  have htrans {x y z : Plane} (hxy : R x y) (hyz : R y z) : R x z := by
    by_cases hxz : x = z
    · exact Or.inl hxz
    rcases hxy with rfl | ⟨C,hCU,hC,hCA⟩
    · exact hyz
    rcases hyz with rfl | ⟨D,hDU,hD,hDA⟩
    · exact Or.inr ⟨C,hCU,hC,hCA⟩
    obtain ⟨E,hEsub,hE⟩ := exists_arc_in_union_of_arcs hC hD hxz
    refine Or.inr ⟨E,hEsub.trans (union_subset hCU hDU),hE,?_⟩
    apply (hCA.union hDA).subset
    intro p hp
    exact (hEsub hp.1).elim (fun h => Or.inl ⟨h,hp.2⟩)
      (fun h => Or.inr ⟨h,hp.2⟩)
  let P : Set Plane := {z | z ∈ U ∧ R x z}
  let Q : Set Plane := {z | z ∈ U ∧ ¬ R x z}
  have hP : IsOpen P := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V,hV,hzV,hVU,hVr⟩ := hlocal z hz.1
    refine ⟨V,?_,hV,hzV⟩
    intro w hw
    refine ⟨hVU hw,htrans hz.2 ?_⟩
    by_cases hzw : z = w
    · exact Or.inl hzw
    · exact Or.inr (hVr w hw hzw)
  have hQ : IsOpen Q := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V,hV,hzV,hVU,hVr⟩ := hlocal z hz.1
    refine ⟨V,?_,hV,hzV⟩
    intro w hw
    refine ⟨hVU hw,fun hxw => hz.2 (htrans hxw ?_)⟩
    apply hsymm
    by_cases hzw : z = w
    · exact Or.inl hzw
    · exact Or.inr (hVr w hw hzw)
  have hcover : U ⊆ P ∪ Q := by
    intro z hz
    by_cases hr : R x z
    · exact Or.inl ⟨hz,hr⟩
    · exact Or.inr ⟨hz,hr⟩
  have hdis : Disjoint P Q := Set.disjoint_left.mpr (fun z hz hq => hq.2 hz.2)
  have hUP : U ⊆ P := hconn.subset_left_of_subset_union hP hQ hdis hcover
    ⟨x,hx,hx,hrefl x⟩
  exact ((hUP hy).2).resolve_left hne

#print axioms finite_contact_arc_of_local

theorem finite_contact_arc_with_access
    (U A L R : Set Plane) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hlocal : ∀ x ∈ U, ∃ V : Set Plane, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧
      ∀ y ∈ V, x ≠ y → ∃ C ⊆ U, IsArcBetween C x y ∧ (C ∩ A).Finite)
    (a b u v : Plane) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U)
    (hu : u ∈ U) (hv : v ∈ U)
    (hL : IsArcBetween L a u) (hR : IsArcBetween R b v)
    (hLU : L \ {a} ⊆ U) (hRU : R \ {b} ⊆ U)
    (hLA : (L ∩ A).Finite) (hRA : (R ∩ A).Finite) :
    ∃ C, IsArcBetween C a b ∧ C \ {a,b} ⊆ U ∧ (C ∩ A).Finite := by
  have hav : a ≠ v := fun h => haU (h ▸ hv)
  have build (M : Set Plane) (hM : IsArcBetween M a v)
      (hMU : M \ {a} ⊆ U) (hMA : (M ∩ A).Finite) :
      ∃ C, IsArcBetween C a b ∧ C \ {a,b} ⊆ U ∧ (C ∩ A).Finite := by
    obtain ⟨C,hCsub,hC⟩ := exists_arc_in_union_of_arcs hM hR.reverse hab
    refine ⟨C,hC,?_,?_⟩
    · intro z hz
      rcases hCsub hz.1 with hm | hr
      · exact hMU ⟨hm,fun he => hz.2 (Or.inl (by simpa using he))⟩
      · exact hRU ⟨hr,fun he => hz.2 (Or.inr he)⟩
    · apply (hMA.union hRA).subset
      intro z hz
      exact (hCsub hz.1).elim (fun h => Or.inl ⟨h,hz.2⟩) (fun h => Or.inr ⟨h,hz.2⟩)
  by_cases huv : u = v
  · exact build L (huv ▸ hL) hLU hLA
  obtain ⟨D,hDU,hD,hDA⟩ := finite_contact_arc_of_local U A hU hconn hlocal u v hu hv huv
  obtain ⟨M,hMsub,hM⟩ := exists_arc_in_union_of_arcs hL hD hav
  apply build M hM
  · intro z hz
    rcases hMsub hz.1 with hl | hd
    · exact hLU ⟨hl,hz.2⟩
    · exact hDU hd
  · apply (hLA.union hDA).subset
    intro z hz
    exact (hMsub hz.1).elim (fun h => Or.inl ⟨h,hz.2⟩) (fun h => Or.inr ⟨h,hz.2⟩)

#print axioms finite_contact_arc_with_access

end RegionalFinitePosition
