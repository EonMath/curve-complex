import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import Schoenflies.JordanClosed
import ClassificationOfSurfaces.Moise.Brouwer

open scoped Manifold
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain

open Set Topology
set_option linter.style.haveILetI false

namespace CurveComplex.HyperellipticModel

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
  (M : HyperellipticModel E S)

/-- Source Lemma 4.2(i): the complement of the actual arc preimage is connected. -/
theorem nonloop_arc_preimage_complement_connected (a : NonLoopArc M) :
    IsConnected (M.cover.projection ⁻¹' a.image)ᶜ := by
  classical
  have hex : ∃ b : S, b ∈ M.cover.branch ∧ b ∉ a.image := by
    classical
    by_contra h
    have hsub : M.cover.branch ⊆
        {a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩} := by
      intro b hb
      have hba : b ∈ a.image := by
        by_contra hn
        exact h ⟨b, hb, hn⟩
      have hx : b ∈ a.val.image ∩ (M.cover.branch : Set S) := ⟨hba, hb⟩
      rw [a.image_inter_branch] at hx
      simpa using hx
    have hc := Finset.card_le_card hsub
    rw [M.cover.branch_card] at hc
    have hp : ({a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩} : Finset S).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    omega
  obtain ⟨b, hb, hba⟩ := hex
  let D : Set S := a.imageᶜ
  have hD : IsConnected D := by
    change IsConnected a.imageᶜ
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    letI : T2Space S := M.sphere.symm.t2Space
    letI : ConnectedSpace S :=
      M.cover.projection_surjective.connectedSpace M.cover.projection_continuous
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
    let e := stereographic' 2 (M.sphere b)
    have hs (x : S) : M.sphere x ∈ e.source ↔ x ≠ b := by
      simp [e, M.sphere.injective.eq_iff]
    let g : Interval → Schoenflies.Plane := fun t => e (M.sphere (a.val.map t))
    have hsource (t : Interval) : M.sphere (a.val.map t) ∈ e.source := by
      rw [hs]
      intro ht
      exact hba ⟨t, ht⟩
    have hgcont : Continuous g :=
      e.continuousOn.comp_continuous (M.sphere.continuous.comp a.val.continuous) hsource
    have hginj : Function.Injective g := by
      intro t u htu
      apply a.injective
      apply M.sphere.injective
      exact e.injOn (hsource t) (hsource u) htu
    have harc : Schoenflies.IsArc (Set.range g) := by
      let f : ℝ → Schoenflies.Plane := fun t =>
        if ht : t ∈ Set.Icc (0 : ℝ) 1 then g ⟨t, ht⟩ else 0
      have hf (t : Interval) : f t = g t := dite_eq_left t.property
      refine ⟨f, ?_, ?_, ?_⟩
      · rw [continuousOn_iff_continuous_domRestrict]
        convert hgcont using 1
        funext t
        exact hf t
      · intro t ht u hu htu
        exact congrArg Subtype.val (hginj (by
          simpa only [hf ⟨t, ht⟩, hf ⟨u, hu⟩] using htu))
      · ext x
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, (hf ⟨t, ht⟩).symm⟩
        · rintro ⟨t, rfl⟩
          exact ⟨t, t.property, hf t⟩
    let j : Schoenflies.Plane → S := fun z => M.sphere.symm (e.symm z)
    have hjcont : Continuous j := M.sphere.symm.continuous.comp
      (e.symm.continuousOn.comp_continuous continuous_id (by intro x; simp [e]))
    have himg : j '' (Set.range g)ᶜ = a.imageᶜ ∩ {b}ᶜ := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzsrc : e.symm z ∈ e.source := e.map_target (by simp [e])
        have hjne : j z ≠ b := by
          apply (hs (j z)).mp
          simpa [j] using hzsrc
        refine ⟨?_, hjne⟩
        rintro ⟨t, ht⟩
        have heq : e (M.sphere (a.val.map t)) = z := by
          rw [ht]
          simpa [j] using e.right_inv (by simp [e] : z ∈ e.target)
        exact hz ⟨t, heq⟩
      · rintro ⟨hx, hxb⟩
        refine ⟨e (M.sphere x), ?_, ?_⟩
        · rintro ⟨t, ht⟩
          have heq : a.val.map t = x := M.sphere.injective
            (e.injOn (hsource t) ((hs x).mpr hxb) ht)
          exact hx ⟨t, heq⟩
        · dsimp [j]
          rw [e.left_inv ((hs x).mpr hxb), M.sphere.symm_apply_apply]
    have hconn : IsConnected (a.imageᶜ ∩ {b}ᶜ) := by
      rw [← himg]
      exact (Schoenflies.arc_complement harc).image j hjcont.continuousOn
    have hdense : Dense ({b}ᶜ : Set S) := by
      rw [dense_compl_singleton_iff_not_open]
      intro ho
      have hu : ({b} : Set S) = Set.univ :=
        IsClopen.eq_univ ⟨isClosed_singleton, ho⟩ (Set.singleton_nonempty b)
      have hstart : a.val.map ⟨0, by norm_num⟩ = b := by
        have hm : a.val.map ⟨0, by norm_num⟩ ∈ ({b} : Set S) :=
          hu.symm ▸ Set.mem_univ _
        exact hm
      exact hba ⟨⟨0, by norm_num⟩, hstart⟩
    have hcl : a.imageᶜ ⊆ closure (a.imageᶜ ∩ {b}ᶜ) := by
      intro x hx
      rw [mem_closure_iff]
      intro o ho hxo
      obtain ⟨y, hy⟩ := hdense.inter_open_nonempty (o ∩ a.imageᶜ)
        (ho.inter a.image_isCompact.isClosed.isOpen_compl)
        ⟨x, hxo, hx⟩
      exact ⟨y, hy.1.1, hy.1.2, hy.2⟩
    exact hconn.subset_closure Set.inter_subset_left hcl
  have hbD : b ∈ D := hba
  change IsConnected (M.cover.projection ⁻¹' D)
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : T2Space S := M.sphere.symm.t2Space
  have hopen : IsOpenMap M.cover.projection := by
      letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
      letI : T2Space S := M.sphere.symm.t2Space
      have hcl : IsClosedMap M.cover.projection := M.cover.projection_continuous.isClosedMap
      have hq := hcl.isQuotientMap M.cover.projection_continuous M.cover.projection_surjective
      intro U hU
      rw [← hq.isCoinducing.isOpen_preimage]
      have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
          U ∪ M.cover.deck ⁻¹' U := by
        ext x
        constructor
        · rintro ⟨y, hy, hxy⟩
          rcases (M.cover.fiber_pair x y).mp hxy.symm with h | h
          · exact Or.inl (h ▸ hy)
          · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [h] using hy)
        · rintro (hx | hx)
          · exact ⟨x, hx, rfl⟩
          · exact ⟨M.cover.deck x, hx, M.cover.projection_deck x⟩
      rw [heq]
      exact hU.union (hU.preimage M.cover.deck.continuous)
  have hclosed : IsClosedMap M.cover.projection :=
    M.cover.projection_continuous.isClosedMap
  let f := D.restrictPreimage M.cover.projection
  have hfopen : IsOpenMap f := hopen.restrictPreimage D
  have hfclosed : IsClosedMap f := hclosed.restrictPreimage D
  letI : ConnectedSpace D := isConnected_iff_connectedSpace.mp hD
  obtain ⟨w, hw, huniq⟩ := M.cover.branch_fiber_unique hb
  have hwD : w ∈ M.cover.projection ⁻¹' D := by change M.cover.projection w ∈ D; rw [hw]; exact hbD
  letI : Nonempty (M.cover.projection ⁻¹' D) := ⟨⟨w, hwD⟩⟩
  apply isConnected_iff_connectedSpace.mpr
  apply connectedSpace_iff_univ.mpr
  refine ⟨Set.univ_nonempty, ?_⟩
  by_contra h
  obtain ⟨U, V, hU, hV, hnU, hnV, hd, huv⟩ :=
    isClopen_univ.not_isPreconnected_iff.mp h
  have hUi : f '' U = Set.univ :=
    IsClopen.eq_univ ⟨hfclosed U hU.isClosed, hfopen U hU.isOpen⟩ (hnU.image f)
  have hVi : f '' V = Set.univ :=
    IsClopen.eq_univ ⟨hfclosed V hV.isClosed, hfopen V hV.isOpen⟩ (hnV.image f)
  obtain ⟨u, hu, hueq⟩ := (hUi.symm ▸ Set.mem_univ (⟨b, hbD⟩ : D))
  obtain ⟨v, hv, hveq⟩ := (hVi.symm ▸ Set.mem_univ (⟨b, hbD⟩ : D))
  have huval : (u : E) = w := huniq u.val (congrArg Subtype.val hueq)
  have hvval : (v : E) = w := huniq v.val (congrArg Subtype.val hveq)
  have huv' : u = v := Subtype.ext (huval.trans hvval.symm)
  exact Set.disjoint_left.mp hd hu (huv' ▸ hv)

/-- Source Lemma 4.2(i): every curve having the actual arc preimage image is essential. -/
theorem nonloop_arc_preimage_essential (a : NonLoopArc M) (c : Curve E)
    (hc : c.image = M.cover.projection ⁻¹' a.image) : Essential c := by
  have hconn : IsConnected c.imageᶜ := by
    rw [hc]
    exact M.nonloop_arc_preimage_complement_connected a
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  intro hc
  obtain ⟨f, hf, hboundary⟩ := hc
  let P := EuclideanSpace ℝ (Fin 2)
  let B := Metric.closedBall (0 : P) 1
  let O := Metric.ball (0 : P) 1
  let A : Set B := {x | (x : P) ∈ O}
  let C : Set B := {x | (x : P) ∈ Metric.sphere (0 : P) 1}
  have hfnot : ¬ Function.Surjective f := by
    intro hsurj
    let h : B ≃ₜ E := IsHomeomorph.homeomorph f
      (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hf, hsurj⟩)
    obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty (E := P).mpr
      (show (0 : ℝ) ≤ 1 by norm_num)
    let pB : B := ⟨p, Metric.sphere_subset_closedBall hp⟩
    let e := chartAt P (h pB)
    let g : e.target → P := fun y => (h.symm (e.symm y) : P)
    have hgcont : Continuous g := continuous_subtype_val.comp
      (h.symm.continuous.comp
        (e.symm.continuousOn.comp_continuous continuous_subtype_val
          (fun y => y.property)))
    have hginj : Function.Injective g := by
      intro y z hyz
      have hhs : h.symm (e.symm y) = h.symm (e.symm z) := Subtype.ext hyz
      exact Subtype.ext (e.symm.injOn y.property z.property (h.symm.injective hhs))
    have hopen : IsOpen (Set.range g) :=
      isOpen_range_of_isOpen_of_continuous_injective
        (modelWithCornersSelf ℝ P) e.open_target g hgcont hginj
    have hpim : p ∈ Set.range g := by
      refine ⟨⟨e (h pB), e.map_source (mem_chart_source P (h pB))⟩, ?_⟩
      dsimp [g]
      rw [e.left_inv (mem_chart_source P (h pB)), h.symm_apply_apply]
    have hsub : Set.range g ⊆ B := by
      rintro _ ⟨y, rfl⟩
      exact (h.symm (e.symm y)).property
    have hpint : p ∈ interior B := (hopen.subset_interior_iff.mpr hsub) hpim
    rw [interior_closedBall (0 : P) (by norm_num : (1 : ℝ) ≠ 0)] at hpint
    exact (ne_of_lt hpint) hp
  simp only [Function.Surjective, not_forall, not_exists] at hfnot
  obtain ⟨x, hx⟩ := hfnot
  have hnV : (Set.range f)ᶜ.Nonempty := ⟨x, by rintro ⟨y, hy⟩; exact hx y hy⟩
  have hopenV : IsOpen (Set.range f)ᶜ :=
    (isCompact_range f.continuous).isClosed.isOpen_compl
  let g : O → E := fun x => f ⟨x, Metric.ball_subset_closedBall x.property⟩
  have hgcont : Continuous g := f.continuous.comp
    (continuous_subtype_val.subtype_mk _)
  have hginj : Function.Injective g := by
    intro x y hxy
    have heq : (⟨x, Metric.ball_subset_closedBall x.property⟩ : B) =
        ⟨y, Metric.ball_subset_closedBall y.property⟩ := hf.injective hxy
    exact Subtype.ext (congrArg (fun z : B => (z : P)) heq)
  have hgim : Set.range g = f '' A := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, Metric.ball_subset_closedBall x.property⟩, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hopenU : IsOpen (f '' A) := by
    rw [← hgim]
    exact isOpen_range_of_isOpen_of_continuous_injective
      (modelWithCornersSelf ℝ P) Metric.isOpen_ball g hgcont hginj
  have hnU : (f '' A).Nonempty := by
    refine ⟨f ⟨0, by simp⟩, ⟨0, by simp⟩, ?_, rfl⟩
    change dist (0 : P) 0 < 1
    simp
  have hdisj : Disjoint (f '' A) (Set.range f)ᶜ := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨y, hy, rfl⟩ hx
    exact hx ⟨y, rfl⟩
  have hUc : f '' A ⊆ c.imageᶜ := by
    rintro _ ⟨y, hy, rfl⟩ hcy
    rw [← hboundary] at hcy
    obtain ⟨z, hz, hfz⟩ := hcy
    have hzy : z = y := hf.injective hfz
    subst z
    exact (ne_of_lt hy) hz
  have hVc : (Set.range f)ᶜ ⊆ c.imageᶜ := by
    intro y hy hcy
    rw [← hboundary] at hcy
    obtain ⟨z, hz, hfz⟩ := hcy
    exact hy ⟨z, hfz⟩
  have hcover : c.imageᶜ ⊆ f '' A ∪ (Set.range f)ᶜ := by
    intro y hy
    by_cases hr : y ∈ Set.range f
    · obtain ⟨z, rfl⟩ := hr
      left
      refine ⟨z, ?_, rfl⟩
      have hne : (z : P) ∉ Metric.sphere (0 : P) 1 := by
        intro hz
        exact hy (hboundary ▸ Set.mem_image_of_mem f hz)
      have hzle := z.property
      change dist (z : P) 0 ≤ 1 at hzle
      change dist (z : P) 0 < 1
      exact lt_of_le_of_ne hzle hne
    · exact Or.inr hr
  rcases hconn.isPreconnected.subset_or_subset hopenU hopenV hdisj hcover with h | h
  · obtain ⟨x, hx⟩ := hnV
    exact Set.disjoint_left.mp hdisj (h (hVc hx)) hx
  · obtain ⟨x, hx⟩ := hnU
    exact Set.disjoint_left.mp hdisj hx (h (hUc hx))

/-- Source Lemma 4.2(ii): the exact circle preimage has disconnected complement. -/
theorem circle33_preimage_complement_not_connected (a : Circle33 M) :
    ¬ IsConnected (M.cover.projection ⁻¹' a.val.image)ᶜ := by
  intro hconn
  obtain ⟨U, V, hU, hV, _, _, hnU, hnV, hdisj, hcover, _, _⟩ := a.property
  have himg : M.cover.projection '' (M.cover.projection ⁻¹' a.val.image)ᶜ =
      a.val.imageᶜ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := M.cover.projection_surjective y
      exact ⟨x, hy, rfl⟩
  have hdown : IsConnected a.val.imageᶜ := by
    rw [← himg]
    exact hconn.image M.cover.projection M.cover.projection_continuous.continuousOn
  have hsub : a.val.imageᶜ ⊆ U ∪ V := hcover.symm.subset
  rcases hdown.isPreconnected.subset_or_subset hU hV hdisj hsub with h | h
  · obtain ⟨v, hv⟩ := hnV
    have hvc : v ∈ a.val.imageᶜ := hcover ▸ Or.inr hv
    exact Set.disjoint_left.mp hdisj (h hvc) hv
  · obtain ⟨u, hu⟩ := hnU
    have huc : u ∈ a.val.imageᶜ := hcover ▸ Or.inl hu
    exact Set.disjoint_left.mp hdisj hu (h huc)

end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.nonloop_arc_preimage_complement_connected
#print axioms CurveComplex.HyperellipticModel.nonloop_arc_preimage_essential
#print axioms CurveComplex.HyperellipticModel.circle33_preimage_complement_not_connected
