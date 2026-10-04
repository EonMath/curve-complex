import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import Mathlib.Topology.Order.DenselyOrdered
import CurveComplexGenusTwo.Topology.CrosscutFull
import Mathlib.Topology.Subpath
open Set Topology

namespace CurveComplex.HyperellipticModel.ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem oldLoop_rawSplices_component_partition
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (x : FirstCrossing M anchor F P)
    (hloop : (P.rep x.selected).val.map ⟨0, by norm_num⟩ =
      (P.rep x.selected).val.map ⟨1, by norm_num⟩)
    (hbase : anchor.val.map ⟨0, by norm_num⟩ =
      (P.rep x.selected).val.map ⟨0, by norm_num⟩)
    (raw : Bool → MarkedArc M)
    (htrace : ∀ side, (raw side).image =
      spliceTrace M anchor (P.rep x.selected) x.t x.s side)
    (hstart : ∀ side, (raw side).map ⟨0, by norm_num⟩ =
      anchor.val.map ⟨0, by norm_num⟩)
    (hend : ∀ side, (raw side).map ⟨1, by norm_num⟩ =
      (P.rep x.selected).val.map
        (if side then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩)) :
    ∃ (D : MarkedLoopDiscDecomposition (P.rep x.selected).val)
      (i : Fin 2) (U : Bool → Set S),
      (anchor.val.map '' Set.Ioo (0 : Interval) x.t ⊆ D.side i) ∧
      (∀ side, IsComplementComponent (raw side).image (U side)) ∧
      (∀ side, IsOpen (U side) ∧ frontier (U side) = (raw side).image) ∧
      (∀ side, closure (U side) ⊆ closure (D.side i)) ∧
      (D.side i \ (anchor.val.map '' Set.Icc (0 : Interval) x.t) =
        U false ∪ U true) ∧
      Disjoint (U false) (U true)
 := by
  classical
  have loop01 : (P.rep x.selected).val.map 0 = (P.rep x.selected).val.map 1 := hloop
  have base01 : anchor.val.map 0 = (P.rep x.selected).val.map 0 := hbase
  obtain ⟨D⟩ := markedLoop_disc_decomposition_exists M (P.rep x.selected).val loop01
  have locate : ∃ i : Fin 2,
      anchor.val.map '' Set.Ioo (0 : Interval) x.t ⊆ D.side i ∧
      anchor.val.map '' Set.Icc (0 : Interval) x.t ⊆ closure (D.side i) := by
    let Q : Set S := anchor.val.map '' Set.Ioo (0 : Interval) x.t
    have hQ : IsPreconnected Q :=
      isPreconnected_Ioo.image anchor.val.map anchor.val.continuous.continuousOn
    have hQt : Q ⊆ (P.rep x.selected).val.imageᶜ := by
      rintro p ⟨r, hr, rfl⟩ hp
      have hmark : anchor.val.map r ∉ (M.cover.branch : Set S) := by
        intro hm
        rcases anchor.val.marked_only_at_ends r hm with hm | hm
        · have he : r.val = 0 := congrArg Subtype.val hm
          exact (ne_of_gt hr.1) (Subtype.ext he)
        · have he : r.val = 1 := congrArg Subtype.val hm
          have hh : r.val < x.t.val := hr.2
          have ht := x.t_interior.2
          linarith
      exact x.first x.selected r hr.1 hr.2 ⟨hp, hmark⟩
    have hqu : Q ⊆ D.side 0 ∪ D.side 1 := by
      rw [D.complement]
      exact hQt
    obtain hside | hside := IsPreconnected.subset_or_subset
      (D.discs 0).open_side (D.discs 1).open_side D.disjoint hqu hQ
    · refine ⟨0, hside, ?_⟩
      have he : (0 : Interval) ≠ x.t := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_gt x.t_interior.1) hv.symm
      rw [← closure_Ioo he]
      exact (image_closure_subset_closure_image anchor.val.continuous).trans
        (closure_mono hside)
    · refine ⟨1, hside, ?_⟩
      have he : (0 : Interval) ≠ x.t := by
        intro he
        have hv := congrArg Subtype.val he
        exact (ne_of_gt x.t_interior.1) hv.symm
      rw [← closure_Ioo he]
      exact (image_closure_subset_closure_image anchor.val.continuous).trans
        (closure_mono hside)
  obtain ⟨i, initial_inside, initial_closed⟩ := locate
  let old := P.rep x.selected
  let T := Schoenflies.Plane.closedSquare 0 1
  obtain ⟨h, hi, hc, hf⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Schoenflies.Plane.convex_closedSquare 0 1)
      (by rw [Schoenflies.Plane.interior_closedSquare];
          exact ⟨0, by simp [Schoenflies.Plane.openSquare, Schoenflies.Plane.supNorm]⟩)
      (Schoenflies.Plane.isBounded_closedSquare 0 1)
  have hopen : h '' Schoenflies.Plane.openSquare 0 1 = Metric.ball 0 1 := by
    simpa only [Schoenflies.Plane.interior_closedSquare] using hi
  have hclosed : h '' T = Metric.closedBall 0 1 := by
    simpa [T, Schoenflies.Plane.isClosed_closedSquare] using hc
  have hcurve : h '' Schoenflies.modelCurve = Metric.sphere 0 1 := by
    simpa only [Schoenflies.modelCurve_eq_frontier] using hf
  let q : T ≃ₜ JordanClosedDisk := Homeomorph.sets h (by
    ext z
    change z ∈ T ↔ h z ∈ Metric.closedBall (0 : Schoenflies.Plane) 1
    exact ⟨fun hz => hclosed ▸ Set.mem_image_of_mem h hz, fun hz => by
      obtain ⟨y, hy, he⟩ := hclosed.symm ▸ hz
      exact h.injective he ▸ hy⟩)
  let e : T ≃ₜ closure (D.side i) := q.trans (D.discs i).closedDisk
  let surf : T → S := Subtype.val ∘ e
  have surfi : Function.Injective surf :=
    Subtype.val_injective.comp e.injective
  have he_boundary (z : T) : surf z ∈ old.val.image ↔ z.val ∈ Schoenflies.modelCurve := by
    change ((D.discs i).closedDisk (q z) : S) ∈ old.val.image ↔ _
    rw [(D.discs i).disk_boundary]
    change ‖h z.val‖ = 1 ↔ z.val ∈ Schoenflies.modelCurve
    constructor
    · intro hn
      have hm : h z.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hn
      obtain ⟨y, hy, he⟩ := hcurve.symm ▸ hm
      exact h.injective he ▸ hy
    · intro hz
      have hm : h z.val ∈ Metric.sphere (0 : Schoenflies.Plane) 1 :=
        hcurve ▸ Set.mem_image_of_mem h hz
      simpa [Metric.mem_sphere, dist_zero_right] using hm
  have he_inside (z : T) : surf z ∈ D.side i ↔ z.val ∈ Schoenflies.Plane.openSquare 0 1 := by
    change ((D.discs i).closedDisk (q z) : S) ∈ D.side i ↔ _
    rw [(D.discs i).disk_interior]
    change ‖h z.val‖ < 1 ↔ z.val ∈ Schoenflies.Plane.openSquare 0 1
    constructor
    · intro hn
      have hm : h z.val ∈ Metric.ball (0 : Schoenflies.Plane) 1 := by
        simpa [Metric.mem_ball, dist_zero_right] using hn
      obtain ⟨y, hy, he⟩ := hopen.symm ▸ hm
      exact h.injective he ▸ hy
    · intro hz
      have hm : h z.val ∈ Metric.ball (0 : Schoenflies.Plane) 1 :=
        hopen ▸ Set.mem_image_of_mem h hz
      simpa [Metric.mem_ball, dist_zero_right] using hm
  have old_closed (u : Interval) : old.val.map u ∈ closure (D.side i) := by
    rw [(D.discs i).closure_eq]
    exact Or.inr ⟨u, rfl⟩
  let f : C(Interval, Schoenflies.Plane) :=
    ⟨fun u => (e.symm ⟨old.val.map u, old_closed u⟩ : Schoenflies.Plane),
      continuous_subtype_val.comp
        (e.symm.continuous.comp (old.val.continuous.subtype_mk _))⟩
  have old_back (u : Interval) : surf (e.symm ⟨old.val.map u, old_closed u⟩) = old.val.map u :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have floop : f 0 = f 1 := by
    apply congrArg (fun y : closure (D.side i) => (e.symm y : Schoenflies.Plane))
    exact Subtype.ext loop01
  have finj : ∀ t u : Interval, f t = f u → t = u ∨
      (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0) := by
    intro t u he
    have he' : e.symm ⟨old.val.map t, old_closed t⟩ =
        e.symm ⟨old.val.map u, old_closed u⟩ := Subtype.ext he
    have heold := congrArg Subtype.val (e.symm.injective he')
    exact old.val.injective_except_loop_closure t u heold
  have frange : Set.range f = Schoenflies.modelCurve := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      apply (he_boundary _).mp
      rw [old_back]
      exact ⟨u, rfl⟩
    · intro hz
      let zT : T := ⟨z, Schoenflies.modelCurve_subset_closedSquare hz⟩
      have hzold : surf zT ∈ old.val.image := (he_boundary zT).mpr hz
      obtain ⟨u, hu⟩ := hzold
      refine ⟨u, ?_⟩
      have hclosedEq : (⟨old.val.map u, old_closed u⟩ : closure (D.side i)) = e zT :=
        Subtype.ext hu
      change (e.symm ⟨old.val.map u, old_closed u⟩ : Schoenflies.Plane) = z
      rw [hclosedEq, e.symm_apply_apply]
  have boundary_split : ∀ (f : C(Interval, Schoenflies.Plane)), f 0 = f 1 →
      (∀ t u, f t = f u → t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0)) →
      ∀ (s : Interval), 0 < s.val ∧ s.val < 1 →
      Schoenflies.IsCutPair (Set.range f) (f 0) (f s)
        (f '' Set.Icc (0 : Interval) s) (f '' Set.Icc s (1 : Interval)) := by
    intro f hloop hinj s hs
    let g : ℝ → Schoenflies.Plane := fun t => f (Set.projIcc 0 1 zero_le_one t)
    have hg : Schoenflies.IsLoop g := by
      refine ⟨(f.continuous.comp continuous_projIcc).continuousOn, ?_, ?_⟩
      · simpa [g, Set.projIcc_of_mem] using hloop
      · intro t ht u hu he
        let ti : Interval := ⟨t, ht.1, ht.2.le⟩
        let ui : Interval := ⟨u, hu.1, hu.2.le⟩
        have he' : f ti = f ui := by
          simpa only [g, ti, ui, Set.projIcc_of_mem zero_le_one ⟨ht.1, ht.2.le⟩,
            Set.projIcc_of_mem zero_le_one ⟨hu.1, hu.2.le⟩] using he
        rcases hinj ti ui he' with he | he | he
        · exact congrArg Subtype.val he
        · have he1 : u = 1 := congrArg Subtype.val he.2
          exact False.elim (hu.2.ne he1)
        · have he1 : t = 1 := congrArg Subtype.val he.1
          exact False.elim (ht.2.ne he1)
    have himage (a b : Interval) :
        g '' Set.Icc a.val b.val = f '' Set.Icc a b := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        have htI : t ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
        refine ⟨⟨t, htI⟩, ht, ?_⟩
        simp only [g, Set.projIcc_of_mem zero_le_one htI]
      · rintro ⟨t, ht, rfl⟩
        refine ⟨t.val, ht, ?_⟩
        simp only [g, Set.projIcc_of_mem zero_le_one t.property]
    have hwhole : g '' Set.Icc (0 : ℝ) 1 = Set.range f := by
      have him := himage (0 : Interval) 1
      change g '' Set.Icc (0 : ℝ) 1 = f '' Set.Icc (0 : Interval) 1 at him
      rw [him]
      ext z
      constructor
      · rintro ⟨t, _, rfl⟩; exact ⟨t, rfl⟩
      · rintro ⟨t, rfl⟩; exact ⟨t, t.property, rfl⟩
    have hshort : g '' Set.Icc (0 : ℝ) 0 ∪ g '' Set.Icc s.val 1 =
        f '' Set.Icc s (1 : Interval) := by
      have heq0 : g 0 = g 1 := hg.closes
      rw [Set.Icc_self, Set.image_singleton]
      have him := himage s (1 : Interval)
      change g '' Set.Icc s.val (1 : ℝ) = f '' Set.Icc s (1 : Interval) at him
      rw [him]
      apply Set.union_eq_right.mpr
      intro z hz
      have he : z = g 0 := hz
      rw [he, heq0]
      exact him ▸ (show g 1 ∈ g '' Set.Icc s.val (1 : ℝ) from
        ⟨1, ⟨s.property.2, le_refl _⟩, rfl⟩)
    have hA := hg.middle_IsArcBetween
      (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num) s.property
      (ne_of_lt hs.2) hs.1
    have hB := hg.outside_IsArcBetween
      (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num) s.property
      (by norm_num : (0 : ℝ) ≠ 1) (ne_of_lt hs.2) hs.1
    have hc := Schoenflies.IsLoop.pieces_cover (f := g) (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num) s.property
    have hm := hg.pieces_meet_at_ends
      (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num) s.property
      (by norm_num : (0 : ℝ) ≠ 1) (ne_of_lt hs.2) hs.1
    have hg0 : g 0 = f 0 := by simp [g, Set.projIcc_of_mem]
    have hgs : g s.val = f s := by
      simp only [g, Set.projIcc_of_mem zero_le_one s.property]
    have hleft := himage (0 : Interval) s
    change g '' Set.Icc (0 : ℝ) s.val = f '' Set.Icc (0 : Interval) s at hleft
    rw [hleft, hg0, hgs] at hA
    rw [hshort, hg0, hgs] at hB
    rw [hleft, hshort, hwhole] at hc
    rw [hleft, hshort, hg0, hgs] at hm
    exact ⟨hA, hB.reverse, hc, hm⟩
  have cut := boundary_split f floop finj x.s x.s_interior
  rw [frange] at cut
  let R : Bool → Set Schoenflies.Plane := fun side =>
    if side then f '' Set.Icc x.s (1 : Interval) else f '' Set.Icc (0 : Interval) x.s
  let k := Set.Icc.convexComb (0 : Interval) x.t
  have hk (u : Interval) : (k u).val = u.val * x.t.val := by simp [k]
  have hkcont : Continuous k := by fun_prop
  have hki : Function.Injective k := by
    intro t u he
    have hv := congrArg Subtype.val he
    rw [hk, hk] at hv
    apply Subtype.ext
    exact mul_right_cancel₀ (ne_of_gt x.t_interior.1) hv
  have hkbound (u : Interval) : k u ∈ Set.Icc (0 : Interval) x.t := by
    refine ⟨(k u).property.1, ?_⟩
    change (k u).val ≤ x.t.val
    rw [hk]
    nlinarith [u.property.1, u.property.2, x.t_interior.1]
  have hklt (u : Interval) : (k u).val < 1 :=
    lt_of_le_of_lt (hkbound u).2 x.t_interior.2
  have anchor_closed (u : Interval) : anchor.val.map (k u) ∈ closure (D.side i) :=
    initial_closed ⟨k u, hkbound u, rfl⟩
  let ap : C(Interval, Schoenflies.Plane) :=
    ⟨fun u => (e.symm ⟨anchor.val.map (k u), anchor_closed u⟩ : Schoenflies.Plane),
      continuous_subtype_val.comp (e.symm.continuous.comp
        ((anchor.val.continuous.comp hkcont).subtype_mk _))⟩
  have anchor_back (u : Interval) :
      surf (e.symm ⟨anchor.val.map (k u), anchor_closed u⟩) = anchor.val.map (k u) :=
    congrArg Subtype.val (e.apply_symm_apply _)
  have apinj : Function.Injective ap := by
    intro t u he
    have he' : e.symm ⟨anchor.val.map (k t), anchor_closed t⟩ =
        e.symm ⟨anchor.val.map (k u), anchor_closed u⟩ := Subtype.ext he
    have heold := congrArg Subtype.val (e.symm.injective he')
    rcases anchor.val.injective_except_loop_closure _ _ heold with he | he | he
    · exact hki he
    · have hv := congrArg Subtype.val he.2
      exact False.elim ((ne_of_lt (hklt u)) hv)
    · have hv := congrArg Subtype.val he.1
      exact False.elim ((ne_of_lt (hklt t)) hv)
  have ap0 : ap 0 = f 0 := by
    apply congrArg (fun y : closure (D.side i) => (e.symm y : Schoenflies.Plane))
    apply Subtype.ext
    simpa only [k, Set.Icc.convexComb_zero] using base01
  have ap1 : ap 1 = f x.s := by
    apply congrArg (fun y : closure (D.side i) => (e.symm y : Schoenflies.Plane))
    apply Subtype.ext
    simpa only [k, Set.Icc.convexComb_one] using x.same_point
  have arc_of_inj : ∀ (f : C(Interval, Schoenflies.Plane)), Function.Injective f →
      Schoenflies.IsArcBetween (Set.range f) (f 0) (f 1) := by
    intro f hfi
    let ff : ℝ → Schoenflies.Plane := fun t => f (Set.projIcc 0 1 zero_le_one t)
    refine ⟨ff, (f.continuous.comp continuous_projIcc).continuousOn, ?_, ?_, ?_, ?_⟩
    · intro t ht u hu he
      have he' := congrArg Subtype.val (hfi he)
      simpa only [Set.projIcc_of_mem zero_le_one ht, Set.projIcc_of_mem zero_le_one hu]
        using he'
    · ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨Set.projIcc 0 1 zero_le_one t, rfl⟩
      · rintro ⟨u, rfl⟩
        refine ⟨u.val, u.property, ?_⟩
        change f (Set.projIcc 0 1 zero_le_one u.val) = f u
        congr 1
        exact Subtype.ext (by simp [Set.projIcc_of_mem zero_le_one u.property])
    · simp [ff, Set.projIcc_of_mem]
    · simp [ff, Set.projIcc_of_mem]
  let Ccross := Set.range ap
  have crossArc : Schoenflies.IsArcBetween Ccross (f 0) (f x.s) := by
    have ha := arc_of_inj ap apinj
    rwa [ap0, ap1] at ha
  have crossInterior : Ccross \ {f 0, f x.s} ⊆ Schoenflies.Plane.openSquare 0 1 := by
    rintro z ⟨⟨u, rfl⟩, hn⟩
    have hu0 : 0 < u.val := by
      have hne : u.val ≠ 0 := by
        intro he
        apply hn
        left
        exact (congrArg ap (Subtype.ext he)).trans ap0
      exact lt_of_le_of_ne u.property.1 hne.symm
    have hu1 : u.val < 1 := by
      have hne : u.val ≠ 1 := by
        intro he
        apply hn
        right
        exact (congrArg ap (Subtype.ext he)).trans ap1
      exact lt_of_le_of_ne u.property.2 hne
    change (e.symm ⟨anchor.val.map (k u), anchor_closed u⟩ : Schoenflies.Plane) ∈ _
    apply (he_inside _).mp
    rw [anchor_back]
    apply initial_inside
    refine ⟨k u, ⟨?_, ?_⟩, rfl⟩
    · change 0 < (k u).val
      rw [hk]
      exact mul_pos hu0 x.t_interior.1
    · change (k u).val < x.t.val
      rw [hk]
      nlinarith [x.t_interior.1]
  have partition := Schoenflies.general_crosscut_arbitrary_of_endpoints
    Schoenflies.isJordanCurve_modelCurve crossArc cut
    (by simpa only [Schoenflies.inside_modelCurve] using crossInterior)
  let Half : Bool → Set Interval := fun side =>
    {r | if side then x.s.val ≤ r.val else r.val ≤ x.s.val}
  have Rdef (side : Bool) : R side = f '' Half side := by
    cases side <;> simp only [R, Half, Bool.false_eq_true, ↓reduceIte]
    · congr 1
      ext u
      simp only [Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun hu => hu.2, fun hu => ⟨u.property.1, hu⟩⟩
    · congr 1
      ext u
      simp only [Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun hu => hu.1, fun hu => ⟨hu, u.property.2⟩⟩
  have old_half_trace (side : Bool) :
      surf '' {z : T | z.val ∈ R side} = old.val.map '' Half side := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Rdef] at hz
      obtain ⟨u, hu, hfu⟩ := hz
      have hez : e.symm ⟨old.val.map u, old_closed u⟩ = z := Subtype.ext hfu
      refine ⟨u, hu, ?_⟩
      rw [← hez, old_back]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨e.symm ⟨old.val.map u, old_closed u⟩, ?_, old_back u⟩
      rw [Rdef]
      exact ⟨u, hu, rfl⟩
  have cross_trace : surf '' {z : T | z.val ∈ Ccross} =
      anchor.val.map '' Set.Icc (0 : Interval) x.t := by
    ext y
    constructor
    · rintro ⟨z, ⟨u, hu⟩, rfl⟩
      have hez : e.symm ⟨anchor.val.map (k u), anchor_closed u⟩ = z := Subtype.ext hu
      refine ⟨k u, hkbound u, ?_⟩
      rw [← hez, anchor_back]
    · rintro ⟨r, hr, rfl⟩
      have hkimage : Set.range k = Set.Icc (0 : Interval) x.t := by
        simpa only [k, Set.uIcc_of_le (show (0 : Interval) ≤ x.t from x.t.property.1)]
          using Path.range_subpathAux 0 x.t
      obtain ⟨u, hu⟩ := hkimage.symm ▸ hr
      refine ⟨e.symm ⟨anchor.val.map (k u), anchor_closed u⟩, ⟨u, rfl⟩, ?_⟩
      rw [anchor_back, hu]
  have raw_trace_coords (side : Bool) :
      surf '' {z : T | z.val ∈ R side ∪ Ccross} = (raw side).image := by
    change surf '' ((Subtype.val : T → Schoenflies.Plane) ⁻¹' (R side ∪ Ccross)) = _
    rw [Set.preimage_union, Set.image_union]
    change (surf '' {z : T | z.val ∈ R side}) ∪ (surf '' {z : T | z.val ∈ Ccross}) = _
    rw [old_half_trace, cross_trace, htrace]
    change (old.val.map '' Half side) ∪ (anchor.val.map '' Set.Icc (0 : Interval) x.t) =
      (anchor.val.map '' {r : Interval | r.val ≤ x.t.val}) ∪ (old.val.map '' Half side)
    rw [Set.union_comm]
    congr 2
    ext r
    simp only [Set.mem_Icc, Set.mem_setOf_eq]
    exact ⟨fun hr => hr.2, fun hr => ⟨r.property.1, hr⟩⟩
  have rArc (side : Bool) : Schoenflies.IsArcBetween (R side) (f 0) (f x.s) := by
    cases side
    · exact cut.fst
    · exact cut.snd
  have rSubset (side : Bool) : R side ⊆ Schoenflies.modelCurve := by
    cases side
    · exact cut.fst_subset
    · exact cut.snd_subset
  have raw_jordan (side : Bool) : Schoenflies.IsJordanCurve (R side ∪ Ccross) := by
    apply Schoenflies.isJordanCurve_union (rArc side) crossArc
    intro z hzR hzP
    by_contra hn
    have hn' : z ∉ ({f 0, f x.s} : Set Schoenflies.Plane) := by simpa using hn
    have hin : z ∈ Schoenflies.inside Schoenflies.modelCurve := by
      simpa only [Schoenflies.inside_modelCurve] using crossInterior ⟨hzP, hn'⟩
    exact Schoenflies.inside_subset_compl hin (rSubset side hzR)
  let V : Bool → Set Schoenflies.Plane := fun side => Schoenflies.inside (R side ∪ Ccross)
  have Vpartition : Schoenflies.Plane.openSquare 0 1 \ Ccross = V false ∪ V true := by
    simpa only [V, R, Bool.false_eq_true, ↓reduceIte, Schoenflies.inside_modelCurve]
      using partition.1
  have Vdisjoint : Disjoint (V false) (V true) := by
    simpa only [V, R, Bool.false_eq_true, ↓reduceIte] using partition.2.1
  have Vsubset (side : Bool) : V side ⊆ Schoenflies.Plane.openSquare 0 1 := by
    intro z hz
    have hz' : z ∈ V false ∪ V true := by
      cases side
      · exact Or.inl hz
      · exact Or.inr hz
    exact (Vpartition.symm ▸ hz').1
  have Vclosed (side : Bool) : closure (V side) ⊆ T := by
    apply (Schoenflies.Plane.isClosed_closedSquare (0 : Schoenflies.Plane) 1).closure_subset_iff.mpr
    intro z hz
    exact Schoenflies.mem_closedSquare_zero_one.mpr
      (Schoenflies.mem_openSquare_zero_one.mp (Vsubset side hz)).le
  have Vopen (side : Bool) : IsOpen (V side) := (Schoenflies.jordan_curve_theorem (raw_jordan side)).isOpen_inside
  have Vconnected (side : Bool) : IsConnected (V side) :=
    (Schoenflies.jordan_curve_theorem (raw_jordan side)).isConnected_inside
  have Vfrontier (side : Bool) : frontier (V side) = R side ∪ Ccross :=
    (Schoenflies.jordan_curve_theorem (raw_jordan side)).frontier_inside
  let B : Bool → Set S := fun side => surf '' {z : T | z.val ∈ V side}
  have Binside (side : Bool) : B side ⊆ D.side i := by
    rintro y ⟨z, hz, rfl⟩
    exact (he_inside z).mpr (Vsubset side hz)
  have transfer : ∀ (V : Set Schoenflies.Plane), IsOpen V → V ⊆ T →
      (surf '' {z : T | z.val ∈ V} ⊆ D.side i) →
      IsOpen (surf '' {z : T | z.val ∈ V}) ∧
        closure (surf '' {z : T | z.val ∈ V}) = surf '' {z : T | z.val ∈ closure V} ∧
        frontier (surf '' {z : T | z.val ∈ V}) = surf '' {z : T | z.val ∈ frontier V} := by
    intro V hV hVT hin
    let U := D.side i
    have hU : IsOpen U := (D.discs i).open_side
    have hT : IsClosed T := Schoenflies.Plane.isClosed_closedSquare 0 1
    let f : T → S := Subtype.val ∘ e
    let A : Set T := {x : T | x.val ∈ V}
    let B : Set S := f '' A
    have hA : IsOpen A := hV.preimage continuous_subtype_val
    have heA : IsOpen (e '' A) := e.isOpenMap A hA
    obtain ⟨G, hG, hGA⟩ := isOpen_induced_iff.mp heA
    have hBG : B = G ∩ U := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨?_, hin ⟨x, hx, rfl⟩⟩
        have : e x ∈ e '' A := ⟨x, hx, rfl⟩
        have hmem : e x ∈ Subtype.val ⁻¹' G := hGA.symm ▸ this
        exact hmem
      · rintro ⟨hyG, hyU⟩
        have hey : (⟨y, subset_closure hyU⟩ : closure U) ∈ e '' A :=
          hGA ▸ hyG
        obtain ⟨x, hx, he⟩ := hey
        exact ⟨x, hx, congrArg Subtype.val he⟩
    have hB : IsOpen B := hBG ▸ (hG.inter hU)
    have hvembed : IsClosedEmbedding (Subtype.val : T → Schoenflies.Plane) := hT.isClosedEmbedding_subtypeVal
    have hfembed : IsClosedEmbedding f :=
      isClosed_closure.isClosedEmbedding_subtypeVal.comp e.isClosedEmbedding
    have hVA : (Subtype.val : T → Schoenflies.Plane) '' A = V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hVT hx⟩, hx, rfl⟩
    have hclA : closure A = {x : T | x.val ∈ closure V} := by
      change closure A = (Subtype.val : T → Schoenflies.Plane) ⁻¹' closure V
      rw [← hVA]
      exact hvembed.isEmbedding.closure_eq_preimage_closure_image A
    have hclB : closure B = f '' {x : T | x.val ∈ closure V} := by
      change closure (f '' A) = _
      rw [hfembed.closure_image_eq, hclA]
    refine ⟨hB, hclB, ?_⟩
    change frontier B = _
    rw [frontier, hB.interior_eq, hclB]
    change (f '' {x : T | x.val ∈ closure V}) \ (f '' A) = _
    rw [← Set.image_sdiff hfembed.injective]
    congr 1
    ext x
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, frontier, hV.interior_eq, A]
  have Btop (side : Bool) := transfer (V side) (Vopen side)
    (Set.Subset.trans subset_closure (Vclosed side)) (Binside side)
  have Bopen (side : Bool) : IsOpen (B side) := (Btop side).1
  have Bfrontier (side : Bool) : frontier (B side) = (raw side).image := by
    rw [(Btop side).2.2, Vfrontier]
    exact raw_trace_coords side
  have Bclosed (side : Bool) : closure (B side) ⊆ closure (D.side i) := by
    rw [(Btop side).2.1]
    rintro y ⟨z, hz, rfl⟩
    exact (e z).property
  have Bconnected (side : Bool) : IsConnected (B side) := by
    letI : ConnectedSpace (V side) := isConnected_iff_connectedSpace.mp (Vconnected side)
    let lift : V side → T := fun z => ⟨z.val, Vclosed side (subset_closure z.property)⟩
    have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
    have hrange : Set.range lift = {z : T | z.val ∈ V side} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact w.property
      · intro hz
        exact ⟨⟨z.val,hz⟩, Subtype.ext rfl⟩
    have hconn := isConnected_range hlift
    rw [hrange] at hconn
    exact hconn.image surf (continuous_subtype_val.comp e.continuous).continuousOn
  have component_of_frontier : ∀ (A U : Set S), IsOpen U → IsConnected U →
      frontier U = A → IsComplementComponent A U := by
    intro A U hU hUc hfr
    have hbd : closure U \ U = A := by
      simpa only [frontier, hU.interior_eq] using hfr
    have hsub : U ⊆ Aᶜ := by
      intro x hx hxa
      have hxf : x ∈ closure U \ U := hbd.symm ▸ hxa
      exact hxf.2 hx
    refine ⟨hUc.nonempty, hUc, hsub, ?_⟩
    intro V hVc hUV hVA
    have hcover : V ⊆ U ∪ (closure U)ᶜ := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · right
        intro hxcl
        exact hVA hx (hbd ▸ ⟨hxcl, hxU⟩)
    have hd : Disjoint U (closure U)ᶜ := by
      exact Set.disjoint_left.mpr (fun x hx hxcl => hxcl (subset_closure hx))
    obtain hVU | hVout := IsPreconnected.subset_or_subset
      hU isClosed_closure.isOpen_compl hd hcover hVc.isPreconnected
    · exact Set.Subset.antisymm hVU hUV
    · obtain ⟨x, hx⟩ := hUc.nonempty
      exact False.elim (hVout (hUV hx) (subset_closure hx))
  have Bcomponent (side : Bool) : IsComplementComponent (raw side).image (B side) :=
    component_of_frontier (raw side).image (B side) (Bopen side) (Bconnected side) (Bfrontier side)
  have open_trace : surf '' {z : T | z.val ∈ Schoenflies.Plane.openSquare 0 1} = D.side i := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (he_inside z).mpr hz
    · intro hy
      let z := e.symm ⟨y, subset_closure hy⟩
      have hez : surf z = y := congrArg Subtype.val (e.apply_symm_apply _)
      refine ⟨z, (he_inside z).mp ?_, hez⟩
      rw [hez]
      exact hy
  have Bpartition : D.side i \ (anchor.val.map '' Set.Icc (0 : Interval) x.t) = B false ∪ B true := by
    have hh := congrArg (fun A : Set Schoenflies.Plane =>
      surf '' ((Subtype.val : T → Schoenflies.Plane) ⁻¹' A)) Vpartition
    rw [Set.preimage_sdiff, Set.image_sdiff surfi, Set.preimage_union, Set.image_union] at hh
    change (surf '' {z : T | z.val ∈ Schoenflies.Plane.openSquare 0 1}) \ (surf '' {z : T | z.val ∈ Ccross}) = B false ∪ B true at hh
    rw [open_trace, cross_trace] at hh
    exact hh
  have Bdisjoint : Disjoint (B false) (B true) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨z₀, hz₀, he₀⟩ ⟨z₁, hz₁, he₁⟩
    have hez : z₀ = z₁ := surfi (he₀.trans he₁.symm)
    subst z₁
    exact Set.disjoint_left.mp Vdisjoint hz₀ hz₁
  exact ⟨D, i, B, initial_inside, Bcomponent,
    fun side => ⟨Bopen side, Bfrontier side⟩, Bclosed, Bpartition, Bdisjoint⟩

end CurveComplex.HyperellipticModel.ArcSurgery
