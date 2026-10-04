import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import Mathlib.Topology.Order.IntermediateValue
open Set Topology Schoenflies
namespace CurveComplex

-- The axis is the ACTUAL disk frontier. Regularity comes from an embedded disk.
-- This determines the exterior half; no arbitrary 'positive means exterior'.
theorem actual_chart_strip_exterior_half
    {S : Type*} [TopologicalSpace S]
    (E : OpenPartialHomeomorph S Plane) (D : Set S) (hD : IsClosed D)
    (hregular : D ⊆ closure (interior D)) (L R ε : ℝ) (hLR : L < R) (hε : 0 < ε)
    (hTarget : {z : Plane | L < z 0 ∧ z 0 < R ∧ -ε < z 1 ∧ z 1 < ε} ⊆ E.target)
    (hFrontier : ∀ z : Plane, L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε →
      (E.symm z ∈ frontier D ↔ z 1 = 0)) :
    ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧ ∀ z : Plane,
      L < z 0 → z 0 < R → -ε < z 1 → z 1 < ε → z 1 ≠ 0 →
      (E.symm z ∉ D ↔ 0 < σ*z 1) := by
  let rect : Set Plane := {z | L < z 0 ∧ z 0 < R ∧ -ε < z 1 ∧ z 1 < ε}
  let pos : Set Plane := {z | L < z 0 ∧ z 0 < R ∧ 0 < z 1 ∧ z 1 < ε}
  let neg : Set Plane := {z | L < z 0 ∧ z 0 < R ∧ -ε < z 1 ∧ z 1 < 0}
  have hPosRect : pos ⊆ rect := fun z hz => ⟨hz.1,hz.2.1,by linarith [hz.2.2.1],hz.2.2.2⟩
  have hNegRect : neg ⊆ rect := fun z hz => ⟨hz.1,hz.2.1,hz.2.2.1,by linarith [hz.2.2.2]⟩
  have hcoord0 : Continuous (fun z : Plane => z 0) := by fun_prop
  have hcoord1 : Continuous (fun z : Plane => z 1) := by fun_prop
  have hRectOpen : IsOpen rect := by
    exact (isOpen_lt continuous_const hcoord0).inter
      ((isOpen_lt hcoord0 continuous_const).inter
        ((isOpen_lt continuous_const hcoord1).inter
          (isOpen_lt hcoord1 continuous_const)))
  have hPlaneConn (a b : ℝ) :
      IsPreconnected {z : Plane | L < z 0 ∧ z 0 < R ∧ a < z 1 ∧ z 1 < b} := by
    have hc : IsPreconnected ((Set.Ioo L R) ×ˢ (Set.Ioo a b)) :=
      isPreconnected_Ioo.prod isPreconnected_Ioo
    have hi := hc.image (fun p : ℝ × ℝ => Plane.mk p.1 p.2) (by fun_prop)
    have he : (fun p : ℝ × ℝ => Plane.mk p.1 p.2) '' ((Set.Ioo L R) ×ˢ (Set.Ioo a b)) =
        {z : Plane | L < z 0 ∧ z 0 < R ∧ a < z 1 ∧ z 1 < b} := by
      ext z
      constructor
      · rintro ⟨p,⟨hp0,hp1⟩,rfl⟩
        exact ⟨hp0.1,hp0.2,hp1.1,hp1.2⟩
      · intro hz
        refine ⟨(z 0,z 1),⟨⟨hz.1,hz.2.1⟩,hz.2.2⟩,?_⟩
        ext i
        fin_cases i <;> rfl
    rwa [he] at hi
  let P := E.symm '' pos
  let N := E.symm '' neg
  have hPConn : IsPreconnected P :=
    (hPlaneConn 0 ε).image E.symm (E.symm.continuousOn.mono (hPosRect.trans hTarget))
  have hNConn : IsPreconnected N :=
    (hPlaneConn (-ε) 0).image E.symm (E.symm.continuousOn.mono (hNegRect.trans hTarget))
  have hAvoid (C : Set Plane) (hCRect : C ⊆ rect) (hCy : ∀ z ∈ C, z 1 ≠ 0) :
      Disjoint (E.symm '' C) (frontier D) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨z,hz,rfl⟩ hx
    have hr := hCRect hz
    exact hCy z hz ((hFrontier z hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).mp hx)
  have hPAvoid := hAvoid pos hPosRect (fun z hz => ne_of_gt hz.2.2.1)
  have hNAvoid := hAvoid neg hNegRect (fun z hz => ne_of_lt hz.2.2.2)
  have hClassify (C : Set S) (hc : IsPreconnected C) (ha : Disjoint C (frontier D)) :
      C ⊆ interior D ∨ C ⊆ Dᶜ := by
    have hcover : C ⊆ interior D ∪ Dᶜ := by
      intro x hx
      by_cases hxD : x ∈ D
      · left
        by_contra hn
        exact Set.disjoint_left.mp ha hx (hD.frontier_eq ▸ ⟨hxD,hn⟩)
      · exact Or.inr hxD
    exact hc.subset_or_subset isOpen_interior hD.isOpen_compl
      (Set.disjoint_left.mpr (fun x hx hn => hn (interior_subset hx))) hcover
  let qplane := Plane.mk ((L+R)/2) 0
  have hqRect : qplane ∈ rect := by
    change L < (L+R)/2 ∧ (L+R)/2 < R ∧ -ε < 0 ∧ 0 < ε
    exact ⟨by linarith only [hLR],by linarith only [hLR],neg_neg_of_pos hε,hε⟩
  let q := E.symm qplane
  have hqFront : q ∈ frontier D :=
    (hFrontier qplane hqRect.1 hqRect.2.1 hqRect.2.2.1 hqRect.2.2.2).mpr rfl
  let O := E.symm '' rect
  have hO : IsOpen O := E.symm.isOpen_image_of_subset_source hRectOpen hTarget
  have hqO : q ∈ O := ⟨qplane,hqRect,rfl⟩
  have hinside : (O ∩ interior D).Nonempty :=
    mem_closure_iff_nhds.mp (hregular (hD.frontier_subset hqFront)) _ (hO.mem_nhds hqO)
  have houtside : (O ∩ Dᶜ).Nonempty := by
    have hnsub : ¬ O ⊆ D := by
      intro hs
      have hqi := interior_maximal hs hO hqO
      exact (hD.frontier_eq ▸ hqFront).2 hqi
    obtain ⟨x,hxO,hxn⟩ := Set.not_subset.mp hnsub
    exact ⟨x,hxO,hxn⟩
  have hSplit (x : S) (hxO : x ∈ O) (hx : x ∉ frontier D) : x ∈ P ∪ N := by
    obtain ⟨z,hz,rfl⟩ := hxO
    have hy : z 1 ≠ 0 := by
      intro he
      exact hx ((hFrontier z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2).mpr he)
    rcases lt_or_gt_of_ne hy with hn | hp
    · exact Or.inr ⟨z,⟨hz.1,hz.2.1,hz.2.2.1,hn⟩,rfl⟩
    · exact Or.inl ⟨z,⟨hz.1,hz.2.1,hp,hz.2.2.2⟩,rfl⟩
  have hNoBothIn (hP : P ⊆ interior D) (hN : N ⊆ interior D) : False := by
    obtain ⟨x,hxO,hxn⟩ := houtside
    have hxf : x ∉ frontier D := fun hf => hxn (hD.frontier_subset hf)
    exact (hSplit x hxO hxf).elim (fun hp => hxn (interior_subset (hP hp)))
      (fun hn => hxn (interior_subset (hN hn)))
  have hNoBothOut (hP : P ⊆ Dᶜ) (hN : N ⊆ Dᶜ) : False := by
    obtain ⟨x,hxO,hxi⟩ := hinside
    have hxf : x ∉ frontier D := by
      intro hf
      exact (hD.frontier_eq ▸ hf).2 hxi
    exact (hSplit x hxO hxf).elim (fun hp => hP hp (interior_subset hxi))
      (fun hn => hN hn (interior_subset hxi))
  rcases hClassify P hPConn hPAvoid with hPI | hPO <;>
    rcases hClassify N hNConn hNAvoid with hNI | hNO
  · exact False.elim (hNoBothIn hPI hNI)
  · refine ⟨-1,Or.inl rfl,?_⟩
    intro z hL hR hlo hhi hy
    rcases lt_or_gt_of_ne hy with hn | hp
    · exact ⟨fun _ => by simpa using neg_pos.mpr hn,
        fun _ => hNO ⟨z,⟨hL,hR,hlo,hn⟩,rfl⟩⟩
    · constructor
      · intro hnot
        exact False.elim (hnot (interior_subset (hPI ⟨z,⟨hL,hR,hp,hhi⟩,rfl⟩)))
      · intro hsign
        simp only [neg_one_mul] at hsign
        linarith only [hsign,hp]
  · refine ⟨1,Or.inr rfl,?_⟩
    intro z hL hR hlo hhi hy
    rcases lt_or_gt_of_ne hy with hn | hp
    · constructor
      · intro hnot
        exact False.elim (hnot (interior_subset (hNI ⟨z,⟨hL,hR,hlo,hn⟩,rfl⟩)))
      · intro hsign
        simp only [one_mul] at hsign
        linarith only [hsign,hn]
    · exact ⟨fun _ => by simpa using hp,fun _ => hPO ⟨z,⟨hL,hR,hp,hhi⟩,rfl⟩⟩
  · exact False.elim (hNoBothOut hPO hNO)
-- Produce a full two-sided strip from the actual compact original-axis arc.
theorem actual_original_axis_selected_curve_clearance
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (E : OpenPartialHomeomorph S Plane) (c : Curve S) (L R : ℝ)
    (haxis : ∀ x ∈ Set.Icc L R, ∃ y : S, y ∈ E.source ∧
      E y = Plane.mk x 0 ∧ y ∉ c.image) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : Plane, z 0 ∈ Set.Icc L R → |z 1| < ε →
      z ∈ E.target ∧ E.symm z ∉ c.image := by
  let xy : Plane ≃ₜ ℝ × ℝ := {
    toFun := fun z => (z 0,z 1)
    invFun := fun z => Plane.mk z.1 z.2
    left_inv := by intro z; ext i; fin_cases i <;> rfl
    right_inv := by intro z; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let P := E '' (E.source ∩ c.imageᶜ)
  have hP : IsOpen P := E.isOpen_image_source_inter
    (isCompact_range c.embedded.continuous).isClosed.isOpen_compl
  let O := xy '' P
  have hO : IsOpen O := xy.isOpenMap _ hP
  let K : Set (ℝ × ℝ) := (fun x : ℝ => (x,0)) '' Set.Icc L R
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKO : K ⊆ O := by
    rintro z ⟨x,hx,rfl⟩
    obtain ⟨y,hyE,hEy,hAvoid⟩ := haxis x hx
    refine ⟨E y,⟨y,⟨hyE,hAvoid⟩,rfl⟩,?_⟩
    rw [hEy]
    rfl
  obtain ⟨ε,hε,hclear⟩ := hK.exists_thickening_subset_open hO hKO
  refine ⟨ε,hε,?_⟩
  intro z hz hy
  have hxy : xy z ∈ O := by
    apply hclear
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(z 0,0),⟨z 0,hz,rfl⟩,?_⟩
    change dist (z 0,z 1) (z 0,0) < ε
    simpa [Prod.dist_eq,Real.dist_eq] using hy
  obtain ⟨v,⟨y,⟨hyE,hAvoid⟩,hEy⟩,hv⟩ := hxy
  have hEyZ : E y = z := hEy.trans (xy.injective hv)
  have hzT : z ∈ E.target := hEyZ ▸ E.map_source hyE
  exact ⟨hzT,by rw [← hEyZ,E.left_inv hyE]; exact hAvoid⟩

theorem actual_finite_boundary_coordinate_enclosing_interval
    (P : Finset ℝ) (hP : P.Nonempty) (hinside : ∀ x ∈ P, -1 < x ∧ x < 1) :
    ∃ L R : ℝ, -1 < L ∧ L < R ∧ R < 1 ∧ ∀ x ∈ P, L < x ∧ x < R := by
  let a := P.min' hP
  let b := P.max' hP
  have ha := hinside a (P.min'_mem hP)
  have hb := hinside b (P.max'_mem hP)
  have hab : a ≤ b := P.min'_le b (P.max'_mem hP)
  let L := (-1+a)/2
  let R := (b+1)/2
  refine ⟨L,R,?_,?_,?_,?_⟩
  · dsimp [L]; linarith only [ha.1]
  · dsimp [L,R]; linarith only [ha.1,hb.2,hab]
  · dsimp [R]; linarith only [hb.2]
  · intro x hx
    have hax := P.min'_le x hx
    have hxb := P.le_max' x hx
    dsimp [L,R]
    exact ⟨by linarith only [ha.1,hax],by linarith only [hb.2,hxb]⟩

theorem actual_finite_boundary_adjacent_contact_gap
    (P : Finset ℝ) (i j : Fin P.card) (hij : j.val = i.val+1) :
    Disjoint (Set.Ioo (P.orderEmbOfFin rfl i) (P.orderEmbOfFin rfl j)) (P : Set ℝ) := by
  apply Set.disjoint_left.mpr
  intro x hx hxp
  let k := (P.orderIsoOfFin rfl).symm ⟨x,hxp⟩
  have hk : P.orderEmbOfFin rfl k = x := by
    have he := congrArg Subtype.val ((P.orderIsoOfFin rfl).apply_symm_apply ⟨x,hxp⟩)
    exact he
  have hik : i < k := (P.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hk]; exact hx.1)
  have hkj : k < j := (P.orderEmbOfFin rfl).lt_iff_lt.mp (by rw [hk]; exact hx.2)
  have hikv : i.val < k.val := hik
  have hkjv : k.val < j.val := hkj
  omega

end CurveComplex
