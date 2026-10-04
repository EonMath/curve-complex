import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Dictionary.LiftPreimage
import Mathlib.Topology.Homotopy.Lifting
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


namespace CurveComplex.HyperellipticModel

open Filter Topology

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
  (M : HyperellipticModel E S)

theorem marked_isotopy_preserves_unramified (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (t : Interval) (y : S) (hy : y ∉ M.cover.branch) :
    H.map (t, y) ∉ M.cover.branch := by
  intro hb
  obtain ⟨h, hh⟩ := H.homeomorphism_at t
  have heq : h y = h (H.map (t, y)) := by
    calc
      h y = H.map (t, y) := hh y
      _ = H.map (t, H.map (t, y)) := (hfix t _ hb).symm
      _ = h (H.map (t, y)) := (hh _).symm
  exact hy ((h.injective heq).symm ▸ hb)

/-- Near a branch value the unique fiber forces convergence upstairs. -/
theorem tendsto_branch_of_projection {A : Type} (l : Filter A)
    (f : A → E) (w : E) (hw : M.cover.projection w ∈ M.cover.branch)
    (hf : Tendsto (fun a => M.cover.projection (f a)) l
      (𝓝 (M.cover.projection w))) : Tendsto f l (𝓝 w) := by
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  letI : T2Space S := M.sphere.symm.t2Space
  rw [tendsto_def]
  intro U hU
  obtain ⟨V, hVU, hVopen, hwV⟩ := mem_nhds_iff.mp hU
  have hclosed : IsClosed (M.cover.projection '' Vᶜ) :=
    M.cover.projection_continuous.isClosedMap _ hVopen.isClosed_compl
  have hnot : M.cover.projection w ∉ M.cover.projection '' Vᶜ := by
    rintro ⟨x, hx, hpx⟩
    have hxw : x = w := by
      rcases (M.cover.fiber_pair w x).mp hpx.symm with h | h
      · exact h
      · simpa [(M.cover.fixed_iff_branch w).mpr hw] using h
    exact hx (hxw ▸ hwV)
  have hnhds : (M.cover.projection '' Vᶜ)ᶜ ∈ 𝓝 (M.cover.projection w) :=
    hclosed.isOpen_compl.mem_nhds hnot
  filter_upwards [hf hnhds] with a ha
  apply hVU
  by_contra hnotV
  exact ha ⟨f a, hnotV, rfl⟩

/-- The marked isotopy restricted to the unramified base. -/
def marked_isotopy_unramified_base (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) :
    C(Interval × M.cover.unramifiedTotal, M.cover.unramifiedBase) := by
  let g : Interval × M.cover.unramifiedTotal → S :=
    fun p => H.map (p.1, M.cover.projection p.2.val)
  have hg : Continuous g :=
    H.map.continuous.comp
      (continuous_fst.prodMk
        ((M.cover.projection_continuous.comp continuous_subtype_val).comp continuous_snd))
  have hp (p : Interval × M.cover.unramifiedTotal) :
      g p ∉ M.cover.branch :=
    M.marked_isotopy_preserves_unramified H hfix p.1
      (M.cover.projection p.2.val) p.2.property
  exact ⟨fun p => ⟨g p, hp p⟩, hg.subtype_mk _⟩

theorem marked_isotopy_unramified_base_zero (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (x : M.cover.unramifiedTotal) :
    M.marked_isotopy_unramified_base H hfix (0, x) =
      M.cover.unramifiedProjection x := by
  apply Subtype.ext
  exact H.at_zero _

/-- The actual covering-homotopy lift of a marked isotopy on the unramified total space. -/
noncomputable def marked_isotopy_unramified_lift (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) :
    C(Interval × M.cover.unramifiedTotal, M.cover.unramifiedTotal) := by
  exact M.cover.unramified_isCoveringMap.liftHomotopy
    (M.marked_isotopy_unramified_base H hfix) (ContinuousMap.id _)
    (M.marked_isotopy_unramified_base_zero H hfix)

theorem marked_isotopy_unramified_lift_projection (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (t : Interval) (x : M.cover.unramifiedTotal) :
    M.cover.projection ((M.marked_isotopy_unramified_lift H hfix (t, x)).val) =
      H.map (t, M.cover.projection x.val) := by
  have h := congrFun
    (M.cover.unramified_isCoveringMap.liftHomotopy_lifts
      (M.marked_isotopy_unramified_base H hfix) (ContinuousMap.id _)
      (M.marked_isotopy_unramified_base_zero H hfix)) (t, x)
  exact congrArg Subtype.val h

theorem marked_isotopy_unramified_lift_zero (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (x : M.cover.unramifiedTotal) :
    M.marked_isotopy_unramified_lift H hfix (0, x) = x := by
  exact M.cover.unramified_isCoveringMap.liftHomotopy_zero
    (M.marked_isotopy_unramified_base H hfix) (ContinuousMap.id _)
    (M.marked_isotopy_unramified_base_zero H hfix) x

/-- Extend the lift over a ramification point by fixing its unique fiber. -/
noncomputable def marked_isotopy_total_map (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (p : Interval × E) : E := by
  classical
  exact
  if hx : p.2 ∈ M.cover.ramification then p.2
  else (M.marked_isotopy_unramified_lift H hfix (p.1, ⟨p.2, hx⟩)).val

theorem marked_isotopy_total_map_projection (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (p : Interval × E) :
    M.cover.projection (M.marked_isotopy_total_map H hfix p) =
      H.map (p.1, M.cover.projection p.2) := by
  by_cases hx : p.2 ∈ M.cover.ramification
  · simp only [marked_isotopy_total_map, dif_pos hx]
    exact (hfix p.1 _ hx).symm
  · simp only [marked_isotopy_total_map, dif_neg hx]
    exact M.marked_isotopy_unramified_lift_projection H hfix p.1 ⟨p.2, hx⟩

theorem marked_isotopy_total_map_zero (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (x : E) : M.marked_isotopy_total_map H hfix (0, x) = x := by
  by_cases hx : x ∈ M.cover.ramification
  · simp [marked_isotopy_total_map, hx]
  · simp only [marked_isotopy_total_map, dif_neg hx]
    exact congrArg Subtype.val
      (M.marked_isotopy_unramified_lift_zero H hfix ⟨x, hx⟩)

theorem marked_isotopy_total_map_continuous (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) :
    Continuous (M.marked_isotopy_total_map H hfix) := by
  letI : T2Space S := M.sphere.symm.t2Space
  have hramClosed : IsClosed M.cover.ramification := by
    exact (M.cover.branch.finite_toSet.isClosed).preimage M.cover.projection_continuous
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hx : p.2 ∈ M.cover.ramification
  · have hbase : ContinuousAt (fun q : Interval × E =>
        H.map (q.1, M.cover.projection q.2)) p := by
      exact (H.map.continuous.comp
        (continuous_fst.prodMk
          (M.cover.projection_continuous.comp continuous_snd))).continuousAt
    have hprojection : Tendsto (fun q : Interval × E =>
        M.cover.projection (M.marked_isotopy_total_map H hfix q))
        (𝓝 p) (𝓝 (M.cover.projection p.2)) := by
      have heq : H.map (p.1, M.cover.projection p.2) =
          M.cover.projection p.2 := hfix p.1 _ hx
      simpa only [M.marked_isotopy_total_map_projection H hfix, heq]
        using hbase.tendsto
    have h := M.tendsto_branch_of_projection (𝓝 p)
      (M.marked_isotopy_total_map H hfix) p.2 hx hprojection
    simpa only [ContinuousAt, marked_isotopy_total_map, dif_pos hx] using h
  · let U : Set (Interval × E) := {q | q.2 ∉ M.cover.ramification}
    have hU : IsOpen U := hramClosed.isOpen_compl.preimage continuous_snd
    have hpU : p ∈ U := hx
    have hcont : Continuous (fun q : U =>
        (M.marked_isotopy_unramified_lift H hfix
          (q.val.1, (⟨q.val.2, q.property⟩ : M.cover.unramifiedTotal))).val) := by
      exact continuous_subtype_val.comp
        ((M.marked_isotopy_unramified_lift H hfix).continuous.comp
          ((continuous_fst.comp continuous_subtype_val).prodMk
            ((continuous_snd.comp continuous_subtype_val).subtype_mk _)))
    have hrestrict : U.domRestrict (M.marked_isotopy_total_map H hfix) =
        (fun q : U => (M.marked_isotopy_unramified_lift H hfix
          (q.val.1, (⟨q.val.2, q.property⟩ : M.cover.unramifiedTotal))).val) := by
      funext q
      have hq : q.val.2 ∉ M.cover.ramification := q.property
      simp [marked_isotopy_total_map, hq]
    have hon : ContinuousOn (M.marked_isotopy_total_map H hfix) U := by
      rw [continuousOn_iff_continuous_restrict]
      exact hrestrict.symm ▸ hcont
    exact hon.continuousAt (hU.mem_nhds hpU)

/-- The deck involution restricts to the unramified total space. -/
def unramified_deck (x : M.cover.unramifiedTotal) : M.cover.unramifiedTotal :=
  ⟨M.cover.deck x.val, by
    change M.cover.projection (M.cover.deck x.val) ∉ M.cover.branch
    rw [M.cover.projection_deck]
    exact x.property⟩

theorem unramified_deck_continuous : Continuous M.unramified_deck := by
  exact (M.cover.deck.continuous.comp continuous_subtype_val).subtype_mk _

theorem marked_isotopy_unramified_lift_deck (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (t : Interval) (x : M.cover.unramifiedTotal) :
    M.marked_isotopy_unramified_lift H hfix (t, M.unramified_deck x) =
      M.unramified_deck (M.marked_isotopy_unramified_lift H hfix (t, x)) := by
  let F := M.marked_isotopy_unramified_lift H hfix
  let a : Interval → M.cover.unramifiedTotal := fun s => F (s, M.unramified_deck x)
  let b : Interval → M.cover.unramifiedTotal := fun s => M.unramified_deck (F (s, x))
  have ha : Continuous a := F.continuous.comp (continuous_id.prodMk continuous_const)
  have hb : Continuous b := M.unramified_deck_continuous.comp
    (F.continuous.comp (continuous_id.prodMk continuous_const))
  have hab : M.cover.unramifiedProjection ∘ a =
      M.cover.unramifiedProjection ∘ b := by
    funext s
    apply Subtype.ext
    change M.cover.projection (F (s, M.unramified_deck x)).val =
      M.cover.projection (M.cover.deck (F (s, x)).val)
    rw [M.marked_isotopy_unramified_lift_projection,
      M.cover.projection_deck,
      M.marked_isotopy_unramified_lift_projection]
    exact congrArg (fun y => H.map (s, y)) (M.cover.projection_deck x.val)
  have hzero : a 0 = b 0 := by
    change F (0, M.unramified_deck x) = M.unramified_deck (F (0, x))
    rw [M.marked_isotopy_unramified_lift_zero H hfix (M.unramified_deck x),
      M.marked_isotopy_unramified_lift_zero H hfix x]
  exact congrFun (M.cover.unramified_isCoveringMap.eq_of_comp_eq ha hb hab 0 hzero) t

theorem marked_isotopy_unramified_lift_injective (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (t : Interval) : Function.Injective
      (fun x : M.cover.unramifiedTotal =>
        M.marked_isotopy_unramified_lift H hfix (t, x)) := by
  intro x y hxy
  obtain ⟨h, hh⟩ := H.homeomorphism_at t
  have hp : M.cover.projection x.val = M.cover.projection y.val := by
    apply h.injective
    rw [hh, hh]
    have he := congrArg (fun z : M.cover.unramifiedTotal => M.cover.projection z.val) hxy
    simpa only [M.marked_isotopy_unramified_lift_projection] using he
  rcases (M.cover.fiber_pair x.val y.val).mp hp with hEq | hDeck
  · exact Subtype.ext hEq.symm
  · have hfixU : M.marked_isotopy_unramified_lift H hfix (t, x) =
        M.unramified_deck (M.marked_isotopy_unramified_lift H hfix (t, x)) := by
      calc
        M.marked_isotopy_unramified_lift H hfix (t, x) =
            M.marked_isotopy_unramified_lift H hfix (t, y) := hxy
        _ = M.marked_isotopy_unramified_lift H hfix (t, M.unramified_deck x) := by
          exact congrArg (fun v => M.marked_isotopy_unramified_lift H hfix (t, v))
            (Subtype.ext hDeck.symm).symm
        _ = M.unramified_deck (M.marked_isotopy_unramified_lift H hfix (t, x)) :=
          M.marked_isotopy_unramified_lift_deck H hfix t x
    have hbranch := (M.cover.fixed_iff_branch
      (M.marked_isotopy_unramified_lift H hfix (t, x)).val).mp
      (congrArg Subtype.val hfixU).symm
    exact False.elim ((M.marked_isotopy_unramified_lift H hfix (t, x)).property hbranch)

theorem marked_isotopy_unramified_lift_surjective (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (t : Interval) : Function.Surjective
      (fun x : M.cover.unramifiedTotal =>
        M.marked_isotopy_unramified_lift H hfix (t, x)) := by
  intro z
  obtain ⟨h, hh⟩ := H.homeomorphism_at t
  obtain ⟨x, hx⟩ := M.cover.projection_surjective (h.symm (M.cover.projection z.val))
  have hxu : x ∉ M.cover.ramification := by
    intro hb
    have hbranch : h (M.cover.projection x) ∈ M.cover.branch := by
      rw [hh]
      rw [hfix t _ hb]
      exact hb
    have hzbranch : M.cover.projection z.val ∈ M.cover.branch := by
      simpa [hx] using hbranch
    exact z.property hzbranch
  let xu : M.cover.unramifiedTotal := ⟨x, hxu⟩
  have hp : M.cover.projection
      (M.marked_isotopy_unramified_lift H hfix (t, xu)).val =
      M.cover.projection z.val := by
    rw [M.marked_isotopy_unramified_lift_projection, ← hh, hx]
    exact h.apply_symm_apply _
  rcases (M.cover.fiber_pair
    (M.marked_isotopy_unramified_lift H hfix (t, xu)).val z.val).mp hp with heq | heq
  · exact ⟨xu, Subtype.ext heq.symm⟩
  · refine ⟨M.unramified_deck xu, ?_⟩
    change M.marked_isotopy_unramified_lift H hfix (t, M.unramified_deck xu) = z
    rw [M.marked_isotopy_unramified_lift_deck]
    exact Subtype.ext heq.symm

theorem marked_isotopy_total_map_bijective (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (t : Interval) : Function.Bijective
      (fun x : E => M.marked_isotopy_total_map H hfix (t, x)) := by
  constructor
  · intro x y hxy
    by_cases hx : x ∈ M.cover.ramification
    · by_cases hy : y ∈ M.cover.ramification
      · simpa [marked_isotopy_total_map, hx, hy] using hxy
      · have hnot : M.marked_isotopy_total_map H hfix (t, y) ∉
            M.cover.ramification := by
          simpa [marked_isotopy_total_map, hy] using
            (M.marked_isotopy_unramified_lift H hfix (t, ⟨y, hy⟩)).property
        have hval : M.marked_isotopy_total_map H hfix (t, x) = x := by
          simp [marked_isotopy_total_map, hx]
        change M.marked_isotopy_total_map H hfix (t, x) =
          M.marked_isotopy_total_map H hfix (t, y) at hxy
        rw [hval] at hxy
        exact False.elim (hnot (hxy ▸ hx))
    · by_cases hy : y ∈ M.cover.ramification
      · have hnot : M.marked_isotopy_total_map H hfix (t, x) ∉
            M.cover.ramification := by
          simpa [marked_isotopy_total_map, hx] using
            (M.marked_isotopy_unramified_lift H hfix (t, ⟨x, hx⟩)).property
        have hval : M.marked_isotopy_total_map H hfix (t, y) = y := by
          simp [marked_isotopy_total_map, hy]
        change M.marked_isotopy_total_map H hfix (t, x) =
          M.marked_isotopy_total_map H hfix (t, y) at hxy
        rw [hval] at hxy
        exact False.elim (hnot (hxy.symm ▸ hy))
      · have hu : M.marked_isotopy_unramified_lift H hfix (t, ⟨x, hx⟩) =
            M.marked_isotopy_unramified_lift H hfix (t, ⟨y, hy⟩) := by
          apply Subtype.ext
          simpa [marked_isotopy_total_map, hx, hy] using hxy
        exact congrArg Subtype.val (M.marked_isotopy_unramified_lift_injective H hfix t hu)
  · intro z
    by_cases hz : z ∈ M.cover.ramification
    · exact ⟨z, by simp [marked_isotopy_total_map, hz]⟩
    · obtain ⟨x, hx⟩ := M.marked_isotopy_unramified_lift_surjective H hfix t
        (⟨z, hz⟩ : M.cover.unramifiedTotal)
      refine ⟨x.val, ?_⟩
      simpa [marked_isotopy_total_map, x.property] using congrArg Subtype.val hx

/-- Every marked ambient isotopy lifts to an ambient isotopy of the branched cover. -/
noncomputable def marked_isotopy_lift (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b) :
    AmbientIsotopy E where
  map := ⟨M.marked_isotopy_total_map H hfix,
    M.marked_isotopy_total_map_continuous H hfix⟩
  homeomorphism_at := by
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    intro t
    have hcont : Continuous (fun x : E => M.marked_isotopy_total_map H hfix (t, x)) :=
      (M.marked_isotopy_total_map_continuous H hfix).comp
        (continuous_const.prodMk continuous_id)
    have hhome : IsHomeomorph (fun x : E => M.marked_isotopy_total_map H hfix (t, x)) :=
      isHomeomorph_iff_continuous_bijective.mpr
        ⟨hcont, M.marked_isotopy_total_map_bijective H hfix t⟩
    exact ⟨IsHomeomorph.homeomorph _ hhome, fun x => rfl⟩
  at_zero := M.marked_isotopy_total_map_zero H hfix

theorem marked_isotopy_lift_projection (H : AmbientIsotopy S)
    (hfix : ∀ t b, b ∈ M.cover.branch → H.map (t, b) = b)
    (t : Interval) (x : E) :
    M.cover.projection ((M.marked_isotopy_lift H hfix).map (t, x)) =
      H.map (t, M.cover.projection x) :=
  M.marked_isotopy_total_map_projection H hfix (t, x)

theorem marked_isotopy_preimage {A B : Set S}
    (h : MarkedIsotopyRel M A B) :
    AmbientIsotopy.Rel (M.cover.projection ⁻¹' A)
      (M.cover.projection ⁻¹' B) := by
  obtain ⟨H, hfix, hAB⟩ := h
  refine ⟨M.marked_isotopy_lift H hfix, ?_⟩
  rw [M.lift_preimage H hfix (M.marked_isotopy_lift H hfix)
    (M.marked_isotopy_lift_projection H hfix) A, hAB]

/-- The full inverse image of an arc descends to isotopy classes of curves. -/
noncomputable def nonloop_arc_curveClass_map : NonLoopArcClass M → CurveClass E :=
  Quotient.lift
    (fun a : NonLoopArc M =>
      Quotient.mk (curveSetoid E) (M.nonloop_arc_preimage_curve a).choose)
    (by
      intro a b hab
      apply Quotient.sound
      change AmbientIsotopy.Rel
        (M.nonloop_arc_preimage_curve a).choose.image
        (M.nonloop_arc_preimage_curve b).choose.image
      rw [(M.nonloop_arc_preimage_curve a).choose_spec,
        (M.nonloop_arc_preimage_curve b).choose_spec]
      exact M.marked_isotopy_preimage hab)

end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.marked_isotopy_lift
#print axioms CurveComplex.HyperellipticModel.marked_isotopy_preimage
#print axioms CurveComplex.HyperellipticModel.nonloop_arc_curveClass_map
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)

/-- The chosen actual essential full preimage of a non-loop arc. -/
noncomputable def nonloop_arc_essential_preimage (a : NonLoopArc M) : EssentialCurve E :=
  ⟨(M.nonloop_arc_preimage_curve a).choose,
    M.nonloop_arc_preimage_essential a _ (M.nonloop_arc_preimage_curve a).choose_spec⟩

/-- The actual full-preimage assignment on essential curve classes. -/
noncomputable def nonloop_arc_vertex_map : NonLoopArcClass M → Vertex E :=
  Quotient.lift
    (fun a => Quotient.mk (essentialCurveSetoid E) (M.nonloop_arc_essential_preimage a))
    (by
      intro a b hab
      apply Quotient.sound
      change AmbientIsotopy.Rel
        (M.nonloop_arc_preimage_curve a).choose.image
        (M.nonloop_arc_preimage_curve b).choose.image
      rw [(M.nonloop_arc_preimage_curve a).choose_spec,
        (M.nonloop_arc_preimage_curve b).choose_spec]
      exact M.marked_isotopy_preimage hab)

/-- The selected representative has the full inverse image as its image. -/
theorem nonloop_arc_essential_preimage_image (a : NonLoopArc M) :
    (M.nonloop_arc_essential_preimage a).val.image =
      M.cover.projection ⁻¹' a.image := by
  exact (M.nonloop_arc_preimage_curve a).choose_spec

/-- The public map evaluates to the class of the selected essential preimage. -/
theorem nonloop_arc_vertex_map_mk (a : NonLoopArc M) :
    M.nonloop_arc_vertex_map (Quotient.mk (nonLoopArcSetoid M) a) =
      Quotient.mk (essentialCurveSetoid E) (M.nonloop_arc_essential_preimage a) := by
  rfl

/-- The selected essential full preimage is nonseparating. -/
theorem nonloop_arc_essential_preimage_complement_connected (a : NonLoopArc M) :
    IsConnected (M.nonloop_arc_essential_preimage a).val.imageᶜ := by
  rw [M.nonloop_arc_essential_preimage_image a]
  exact M.nonloop_arc_preimage_complement_connected a

end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.nonloop_arc_essential_preimage
#print axioms CurveComplex.HyperellipticModel.nonloop_arc_vertex_map

#print axioms CurveComplex.HyperellipticModel.nonloop_arc_essential_preimage_image
#print axioms CurveComplex.HyperellipticModel.nonloop_arc_vertex_map_mk
#print axioms CurveComplex.HyperellipticModel.nonloop_arc_essential_preimage_complement_connected
