import CurveComplexGenusTwo.Topology.ActualRegionalAllCrossing.RegionalCrossingReturnCore

open CurveComplex Set Topology Schoenflies

namespace RegionalEmbeddedFamily

/-- A planar chart has connected negative and positive coordinate halves
in an open neighborhood of its origin. -/
theorem contact_plane_chart_has_connected_halves
    {X : Type*} [TopologicalSpace X]
    (K : OpenPartialHomeomorph X Plane) (z : X)
    (hz : z ∈ K.source) (hzero : K z = 0) :
    ∃ N M P : Set X, IsOpen N ∧ z ∈ N ∧ N ⊆ K.source ∧
      IsPreconnected M ∧ IsPreconnected P ∧
      M = N ∩ {x | K x 1 < 0} ∧ P = N ∩ {x | 0 < K x 1} := by
  have hzt : (0 : Plane) ∈ K.target := hzero ▸ K.map_source hz
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp (K.open_target.mem_nhds hzt)
  let Q := Metric.ball (0 : Plane) ρ
  let Qm := Q ∩ {y : Plane | y 1 < 0}
  let Qp := Q ∩ {y : Plane | 0 < y 1}
  let N := K.symm '' Q
  let M := K.symm '' Qm
  let P := K.symm '' Qp
  have hQ : Q ⊆ K.target := hball
  have hmQ : Qm ⊆ Q := Set.inter_subset_left
  have hpQ : Qp ⊆ Q := Set.inter_subset_left
  have hNsource : N ⊆ K.source := by
    rintro _ ⟨y,hy,rfl⟩
    exact K.symm.map_source (hQ hy)
  have hNopen : IsOpen N := K.isOpen_image_symm_of_subset_target Metric.isOpen_ball hQ
  have hzN : z ∈ N := by
    refine ⟨0,by simpa [Q] using hρ,?_⟩
    rw [← hzero,K.left_inv hz]
  have hlinear : IsLinearMap ℝ (fun y : Plane => y 1) :=
    ⟨by intros x y; rfl, by intros c x; rfl⟩
  have hM : IsPreconnected M :=
    ((convex_ball (0 : Plane) ρ).inter (convex_halfSpace_lt hlinear 0)).isPreconnected.image
      K.symm (K.symm.continuousOn.mono (hmQ.trans hQ))
  have hP : IsPreconnected P :=
    ((convex_ball (0 : Plane) ρ).inter (convex_halfSpace_gt hlinear 0)).isPreconnected.image
      K.symm (K.symm.continuousOn.mono (hpQ.trans hQ))
  refine ⟨N,M,P,hNopen,hzN,hNsource,hM,hP,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy.1,rfl⟩,by simpa only [Set.mem_ofPred_eq, K.right_inv (hQ hy.1)] using hy.2⟩
    · rintro ⟨⟨y,hy,he⟩,hneg⟩
      refine ⟨y,⟨hy,?_⟩,he⟩
      change K x 1 < 0 at hneg
      rwa [← he,K.right_inv (hQ hy)] at hneg
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy.1,rfl⟩,by simpa only [Set.mem_ofPred_eq, K.right_inv (hQ hy.1)] using hy.2⟩
    · rintro ⟨⟨y,hy,he⟩,hpos⟩
      refine ⟨y,⟨hy,?_⟩,he⟩
      change 0 < K x 1 at hpos
      rwa [← he,K.right_inv (hQ hy)] at hpos

/-- Coordinate signs force a switch of the genuine global complementary
sides. No choice of a positive global side is assumed. -/
theorem contact_chart_opposite_signs_switch_global_sides
    {X : Type*} [TopologicalSpace X]
    (f : C(Interval,X)) (L U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (hfrontU : frontier U = L) (hfrontV : frontier V = L)
    (K : OpenPartialHomeomorph X Plane) (t a b : Interval)
    (hat : a < t) (htb : t < b)
    (htK : f t ∈ K.source) (hzero : K (f t) = 0)
    (haxis : ∀ x ∈ K.source, x ∈ L ↔ K x 1 = 0)
    (hsigns :
      ((∀ u ∈ Set.Ioo a t, f u ∈ K.source → 0 < K (f u) 1) ∧
        (∀ u ∈ Set.Ioo t b, f u ∈ K.source → K (f u) 1 < 0)) ∨
      ((∀ u ∈ Set.Ioo a t, f u ∈ K.source → K (f u) 1 < 0) ∧
        (∀ u ∈ Set.Ioo t b, f u ∈ K.source → 0 < K (f u) 1))) :
    ∀ l r : Interval, l < t → t < r →
      ∃ u v : Interval, l < u ∧ u < t ∧ t < v ∧ v < r ∧
        ((f u ∈ U ∧ f v ∈ V) ∨ (f u ∈ V ∧ f v ∈ U)) := by
  obtain ⟨N,M,P,hN,htN,hNK,hM,hP,hMeq,hPeq⟩ :=
    contact_plane_chart_has_connected_halves K (f t) htK hzero
  have hsplit : N \ L = M ∪ P := by
    rw [hMeq,hPeq]
    ext x
    constructor
    · rintro ⟨hx,hxL⟩
      have hn : K x 1 ≠ 0 := fun he => hxL ((haxis x (hNK hx)).mpr he)
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact Or.inl ⟨hx,hn⟩
      · exact Or.inr ⟨hx,hn⟩
    · rintro (⟨hx,hn⟩ | ⟨hx,hn⟩)
      · exact ⟨hx,fun hxL => hn.ne ((haxis x (hNK hx)).mp hxL)⟩
      · exact ⟨hx,fun hxL => hn.ne' ((haxis x (hNK hx)).mp hxL)⟩
  have htL : f t ∈ L := (haxis _ htK).mpr (by rw [hzero]; rfl)
  have htU : f t ∈ closure U := frontier_subset_closure (hfrontU.symm ▸ htL)
  have htV : f t ∈ closure V := frontier_subset_closure (hfrontV.symm ▸ htL)
  have hn : f ⁻¹' N ∈ 𝓝 t := f.continuous.continuousAt.preimage_mem_nhds (hN.mem_nhds htN)
  obtain ⟨c,d,htcd,hcd⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨a,hat⟩ ⟨b,htb⟩).mp hn
  intro l r hlt htr
  obtain ⟨u,hu⟩ := exists_between (max_lt (max_lt hlt hat) htcd.1)
  obtain ⟨v,hv⟩ := exists_between (lt_min (lt_min htr htb) htcd.2)
  have hlu : l < u := (le_max_left l a).trans_lt ((le_max_left (max l a) c).trans_lt hu.1)
  have hau : a < u := (le_max_right l a).trans_lt ((le_max_left (max l a) c).trans_lt hu.1)
  have hcu : c < u := (le_max_right (max l a) c).trans_lt hu.1
  have hvr : v < r := hv.2.trans_le ((min_le_left (min r b) d).trans (min_le_left r b))
  have hvb : v < b := hv.2.trans_le ((min_le_left (min r b) d).trans (min_le_right r b))
  have hvd : v < d := hv.2.trans_le (min_le_right (min r b) d)
  have huN : f u ∈ N := hcd ⟨hcu,hu.2.trans htcd.2⟩
  have hvN : f v ∈ N := hcd ⟨htcd.1.trans hv.1,hvd⟩
  refine ⟨u,v,hlu,hu.2,hv.1,hvr,?_⟩
  rcases hsigns with ⟨hp,hm⟩ | ⟨hm,hp⟩
  · have hh := contact_local_connected_arms_opposite_sides L U V N M P (f t) (f v) (f u)
      hU hV hdis hcover hN htN htU htV hsplit hM hP
      (by rw [hMeq]; exact ⟨hvN,hm v ⟨hv.1,hvb⟩ (hNK hvN)⟩)
      (by rw [hPeq]; exact ⟨huN,hp u ⟨hau,hu.2⟩ (hNK huN)⟩)
    exact hh.elim (fun h => Or.inr ⟨h.2,h.1⟩) (fun h => Or.inl ⟨h.2,h.1⟩)
  · exact contact_local_connected_arms_opposite_sides L U V N M P (f t) (f u) (f v)
      hU hV hdis hcover hN htN htU htV hsplit hM hP
      (by rw [hMeq]; exact ⟨huN,hm u ⟨hau,hu.2⟩ (hNK huN)⟩)
      (by rw [hPeq]; exact ⟨hvN,hp v ⟨hv.1,hvb⟩ (hNK hvN)⟩)

end RegionalEmbeddedFamily
