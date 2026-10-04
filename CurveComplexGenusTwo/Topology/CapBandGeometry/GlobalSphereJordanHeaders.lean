import CurveComplexGenusTwo.Foundations.CircleJordanAdapter
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology CurveComplex
namespace CurveComplex.LocalSurgery

/-- A connected Hausdorff charted surface cannot be the image of an embedded circle. -/
theorem charted_connected_surface_embedded_circle_not_surjective
    {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (r : C(Circle,S)) (hr : IsEmbedding r) : ¬Function.Surjective r := by
  classical
  have hgeneral {F : Set S} (hF : F.Finite)
      (hlocal : ∀ p ∈ F, ∃ U : Set S,
        IsOpen U ∧ p ∈ U ∧ IsPathConnected (U \ F)) : IsConnected Fᶜ := by
    classical
    by_cases hFempty : F = ∅
    · simpa [hFempty] using
        (isConnected_univ : IsConnected (Set.univ : Set S))
    have hcomplNonempty : Fᶜ.Nonempty := by
      obtain ⟨p, hpF⟩ := Set.nonempty_iff_ne_empty.mpr hFempty
      obtain ⟨U, _hUopen, _hpU, hpath⟩ := hlocal p hpF
      obtain ⟨x, _hxU, hxF⟩ := hpath.nonempty
      exact ⟨x, hxF⟩
    refine ⟨hcomplNonempty, ?_⟩
    intro u v hu hv hcover hUne hVne
    by_contra hinter
    let A : Set S := Fᶜ ∩ u
    let B : Set S := Fᶜ ∩ v
    have hAopen : IsOpen A := hF.isClosed.isOpen_compl.inter hu
    have hBopen : IsOpen B := hF.isClosed.isOpen_compl.inter hv
    have hABcover : Fᶜ ⊆ A ∪ B := by
      intro x hx
      rcases hcover hx with hxu | hxv
      · exact Or.inl ⟨hx, hxu⟩
      · exact Or.inr ⟨hx, hxv⟩
    have hABdisjoint : Disjoint A B := by
      rw [Set.disjoint_left]
      intro x hxA hxB
      exact hinter ⟨x, hxA.1, hxA.2, hxB.2⟩
    choose U hUopen hpU hUpath using
      fun p : F ↦ hlocal p.1 p.2
    have hside (p : F) :
        U p \ F ⊆ A ∨ U p \ F ⊆ B := by
      obtain ⟨x, hx⟩ := (hUpath p).nonempty
      rcases hABcover hx.2 with hxA | hxB
      · left
        exact (hUpath p).isConnected.isPreconnected.subset_left_of_subset_union
          hAopen hBopen hABdisjoint
          (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxA⟩
      · right
        exact (hUpath p).isConnected.isPreconnected.subset_right_of_subset_union
          hAopen hBopen hABdisjoint
          (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxB⟩
    let Left (p : F) : Prop := U p \ F ⊆ A
    have hright (p : F) (hp : ¬Left p) :
        U p \ F ⊆ B :=
      (hside p).resolve_left hp
    let W (p : F) : Set S := U p \ (F \ {p.1})
    have hWopen (p : F) : IsOpen (W p) := by
      exact (hUopen p).inter (hF.sdiff |>.isClosed.isOpen_compl)
    have hpW (p : F) : p.1 ∈ W p := by
      refine ⟨hpU p, ?_⟩
      rintro ⟨_, hpne⟩
      exact hpne rfl
    have eq_center_of_mem_W_of_mem_F (p : F) {x : S}
        (hxW : x ∈ W p) (hxF : x ∈ F) :
        x = p.1 := by
      by_contra hxp
      apply hxW.2
      exact ⟨hxF, by simpa using hxp⟩
    let L : Set S := {x | ∃ p : F, Left p ∧ x = p.1}
    let R : Set S := {x | ∃ p : F, ¬Left p ∧ x = p.1}
    let A' : Set S := A ∪ L
    let B' : Set S := B ∪ R
    have hA'open : IsOpen A' := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      rcases hx with hxA | ⟨p, hpLeft, rfl⟩
      · exact ⟨A, Set.subset_union_left, hAopen, hxA⟩
      · refine ⟨W p, ?_, hWopen p, hpW p⟩
        intro y hyW
        by_cases hyF : y ∈ F
        · right
          exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
        · left
          exact hpLeft ⟨hyW.1, hyF⟩
    have hB'open : IsOpen B' := by
      rw [isOpen_iff_forall_mem_open]
      intro x hx
      rcases hx with hxB | ⟨p, hpLeft, rfl⟩
      · exact ⟨B, Set.subset_union_left, hBopen, hxB⟩
      · refine ⟨W p, ?_, hWopen p, hpW p⟩
        intro y hyW
        by_cases hyF : y ∈ F
        · right
          exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
        · left
          exact hright p hpLeft ⟨hyW.1, hyF⟩
    have hA'B'disjoint : Disjoint A' B' := by
      rw [Set.disjoint_left]
      intro x hxA' hxB'
      rcases hxA' with hxA | ⟨p, hpLeft, hp⟩
      · rcases hxB' with hxB | ⟨q, _hqLeft, hq⟩
        · exact Set.disjoint_left.mp hABdisjoint hxA hxB
        · exact hxA.1 (hq ▸ q.2)
      · rcases hxB' with hxB | ⟨q, hqLeft, hq⟩
        · exact hxB.1 (hp ▸ p.2)
        · apply hqLeft
          have hpq : p = q := by
            apply Subtype.ext
            exact hp.symm.trans hq
          simpa [hpq] using hpLeft
    have hA'B'cover : (Set.univ : Set S) ⊆ A' ∪ B' := by
      intro x _
      by_cases hxF : x ∈ F
      · let p : F := ⟨x, hxF⟩
        by_cases hpLeft : Left p
        · exact Or.inl (Or.inr ⟨p, hpLeft, rfl⟩)
        · exact Or.inr (Or.inr ⟨p, hpLeft, rfl⟩)
      · rcases hABcover hxF with hxA | hxB
        · exact Or.inl (Or.inl hxA)
        · exact Or.inr (Or.inl hxB)
    have hA'ne : ((Set.univ : Set S) ∩ A').Nonempty := by
      obtain ⟨x, hxF, hxu⟩ := hUne
      exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxu⟩⟩
    have hB'ne : ((Set.univ : Set S) ∩ B').Nonempty := by
      obtain ⟨x, hxF, hxv⟩ := hVne
      exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxv⟩⟩
    obtain ⟨x, _, hxA', hxB'⟩ := isPreconnected_univ
      A' B' hA'open hB'open hA'B'cover hA'ne hB'ne
    exact Set.disjoint_left.mp hA'B'disjoint hxA' hxB'
  have hplane (x : S) : ∃ U : Set S, x ∈ U ∧ IsOpen U ∧
      Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) := by
    let P := EuclideanSpace ℝ (Fin 2)
    let e := chartAt P x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x)
      (e.map_source (mem_chart_source P x))
    let U := e.symm '' Metric.ball (e x) r
    have hsub : Metric.ball (e x) r ⊆ e.symm.source := hball
    have hopen : IsOpen U := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub
    have hx : x ∈ U := ⟨e x, Metric.mem_ball_self hr, e.left_inv (mem_chart_source P x)⟩
    let b := OpenPartialHomeomorph.univBall (e x) r
    have hmap : b '' (Set.univ : Set P) = Metric.ball (e x) r := by
      simpa only [b, OpenPartialHomeomorph.univBall_source,
        OpenPartialHomeomorph.univBall_target (e x) hr] using b.image_source_eq_target
    let g : P ≃ₜ Metric.ball (e x) r :=
      (Homeomorph.Set.univ P).symm.trans
        (b.homeomorphOfImageSubsetSource (by simp [b]) hmap)
    let f : Metric.ball (e x) r ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hsub rfl
    exact ⟨U, hx, hopen, ⟨g.trans f⟩⟩
  have hfinite (F : Set S) (hF : F.Finite) : IsConnected Fᶜ := by
    apply hgeneral hF
    intro x hxF
    obtain ⟨U, hxU, hU, ⟨g⟩⟩ := hplane x
    let f : EuclideanSpace ℝ (Fin 2) → S := fun z => (g z : S)
    have hfin : (f ⁻¹' F).Finite := hF.preimage (by
      intro a _ b _ hab
      exact g.injective (Subtype.ext hab))
    have hp : IsPathConnected (f ⁻¹' F)ᶜ :=
      hfin.countable.isPathConnected_compl_of_one_lt_rank (by
        apply Module.one_lt_rank_of_one_lt_finrank
        simp)
    have himage : f '' (f ⁻¹' F)ᶜ = U \ F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(g z).property, hz⟩
      · rintro ⟨hyU, hyF⟩
        obtain ⟨z, hz⟩ := g.surjective ⟨y, hyU⟩
        refine ⟨z, ?_, congrArg Subtype.val hz⟩
        change f z ∉ F
        simpa [f, hz] using hyF
    refine ⟨U, hU, hxU, ?_⟩
    rw [← himage]
    exact hp.image (continuous_subtype_val.comp g.continuous)
  intro hsurj
  let h : Circle ≃ₜ S := hr.toHomeomorphOfSurjective hsurj
  have hp : IsPreconnected (r ⁻¹' ({r 1, r (-1)} : Set S)ᶜ) :=
    h.isPreconnected_preimage.mpr (hfinite _ ((Set.finite_singleton _).insert _)).isPreconnected
  have heq : r ⁻¹' ({r 1, r (-1)} : Set S)ᶜ = ({1, -1} : Set Circle)ᶜ := by
    ext z
    simp only [mem_preimage, mem_compl_iff, mem_insert_iff, mem_singleton_iff]
    rw [hr.injective.eq_iff, hr.injective.eq_iff]
  rw [heq] at hp
  exact Circle.not_isPreconnected_compl_pair (Circle.neg_ne_self (1 : Circle)).symm hp


/-- Spherical Schoenflies, derived by an actual omitted-point stereographic chart. -/
theorem standard_sphere_embedded_circle_bounds_disc
    (c : Curve (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) : BoundsDisc c := by
  classical
  have homit {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
      (r : C(Circle,S)) (hr : IsEmbedding r) : ¬Function.Surjective r := by
    classical
    have hgeneral {F : Set S} (hF : F.Finite)
        (hlocal : ∀ p ∈ F, ∃ U : Set S,
          IsOpen U ∧ p ∈ U ∧ IsPathConnected (U \ F)) : IsConnected Fᶜ := by
      classical
      by_cases hFempty : F = ∅
      · simpa [hFempty] using
          (isConnected_univ : IsConnected (Set.univ : Set S))
      have hcomplNonempty : Fᶜ.Nonempty := by
        obtain ⟨p, hpF⟩ := Set.nonempty_iff_ne_empty.mpr hFempty
        obtain ⟨U, _hUopen, _hpU, hpath⟩ := hlocal p hpF
        obtain ⟨x, _hxU, hxF⟩ := hpath.nonempty
        exact ⟨x, hxF⟩
      refine ⟨hcomplNonempty, ?_⟩
      intro u v hu hv hcover hUne hVne
      by_contra hinter
      let A : Set S := Fᶜ ∩ u
      let B : Set S := Fᶜ ∩ v
      have hAopen : IsOpen A := hF.isClosed.isOpen_compl.inter hu
      have hBopen : IsOpen B := hF.isClosed.isOpen_compl.inter hv
      have hABcover : Fᶜ ⊆ A ∪ B := by
        intro x hx
        rcases hcover hx with hxu | hxv
        · exact Or.inl ⟨hx, hxu⟩
        · exact Or.inr ⟨hx, hxv⟩
      have hABdisjoint : Disjoint A B := by
        rw [Set.disjoint_left]
        intro x hxA hxB
        exact hinter ⟨x, hxA.1, hxA.2, hxB.2⟩
      choose U hUopen hpU hUpath using
        fun p : F ↦ hlocal p.1 p.2
      have hside (p : F) :
          U p \ F ⊆ A ∨ U p \ F ⊆ B := by
        obtain ⟨x, hx⟩ := (hUpath p).nonempty
        rcases hABcover hx.2 with hxA | hxB
        · left
          exact (hUpath p).isConnected.isPreconnected.subset_left_of_subset_union
            hAopen hBopen hABdisjoint
            (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxA⟩
        · right
          exact (hUpath p).isConnected.isPreconnected.subset_right_of_subset_union
            hAopen hBopen hABdisjoint
            (fun _ hy ↦ hABcover hy.2) ⟨x, hx, hxB⟩
      let Left (p : F) : Prop := U p \ F ⊆ A
      have hright (p : F) (hp : ¬Left p) :
          U p \ F ⊆ B :=
        (hside p).resolve_left hp
      let W (p : F) : Set S := U p \ (F \ {p.1})
      have hWopen (p : F) : IsOpen (W p) := by
        exact (hUopen p).inter (hF.sdiff |>.isClosed.isOpen_compl)
      have hpW (p : F) : p.1 ∈ W p := by
        refine ⟨hpU p, ?_⟩
        rintro ⟨_, hpne⟩
        exact hpne rfl
      have eq_center_of_mem_W_of_mem_F (p : F) {x : S}
          (hxW : x ∈ W p) (hxF : x ∈ F) :
          x = p.1 := by
        by_contra hxp
        apply hxW.2
        exact ⟨hxF, by simpa using hxp⟩
      let L : Set S := {x | ∃ p : F, Left p ∧ x = p.1}
      let R : Set S := {x | ∃ p : F, ¬Left p ∧ x = p.1}
      let A' : Set S := A ∪ L
      let B' : Set S := B ∪ R
      have hA'open : IsOpen A' := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        rcases hx with hxA | ⟨p, hpLeft, rfl⟩
        · exact ⟨A, Set.subset_union_left, hAopen, hxA⟩
        · refine ⟨W p, ?_, hWopen p, hpW p⟩
          intro y hyW
          by_cases hyF : y ∈ F
          · right
            exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
          · left
            exact hpLeft ⟨hyW.1, hyF⟩
      have hB'open : IsOpen B' := by
        rw [isOpen_iff_forall_mem_open]
        intro x hx
        rcases hx with hxB | ⟨p, hpLeft, rfl⟩
        · exact ⟨B, Set.subset_union_left, hBopen, hxB⟩
        · refine ⟨W p, ?_, hWopen p, hpW p⟩
          intro y hyW
          by_cases hyF : y ∈ F
          · right
            exact ⟨p, hpLeft, eq_center_of_mem_W_of_mem_F p hyW hyF⟩
          · left
            exact hright p hpLeft ⟨hyW.1, hyF⟩
      have hA'B'disjoint : Disjoint A' B' := by
        rw [Set.disjoint_left]
        intro x hxA' hxB'
        rcases hxA' with hxA | ⟨p, hpLeft, hp⟩
        · rcases hxB' with hxB | ⟨q, _hqLeft, hq⟩
          · exact Set.disjoint_left.mp hABdisjoint hxA hxB
          · exact hxA.1 (hq ▸ q.2)
        · rcases hxB' with hxB | ⟨q, hqLeft, hq⟩
          · exact hxB.1 (hp ▸ p.2)
          · apply hqLeft
            have hpq : p = q := by
              apply Subtype.ext
              exact hp.symm.trans hq
            simpa [hpq] using hpLeft
      have hA'B'cover : (Set.univ : Set S) ⊆ A' ∪ B' := by
        intro x _
        by_cases hxF : x ∈ F
        · let p : F := ⟨x, hxF⟩
          by_cases hpLeft : Left p
          · exact Or.inl (Or.inr ⟨p, hpLeft, rfl⟩)
          · exact Or.inr (Or.inr ⟨p, hpLeft, rfl⟩)
        · rcases hABcover hxF with hxA | hxB
          · exact Or.inl (Or.inl hxA)
          · exact Or.inr (Or.inl hxB)
      have hA'ne : ((Set.univ : Set S) ∩ A').Nonempty := by
        obtain ⟨x, hxF, hxu⟩ := hUne
        exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxu⟩⟩
      have hB'ne : ((Set.univ : Set S) ∩ B').Nonempty := by
        obtain ⟨x, hxF, hxv⟩ := hVne
        exact ⟨x, Set.mem_univ x, Or.inl ⟨hxF, hxv⟩⟩
      obtain ⟨x, _, hxA', hxB'⟩ := isPreconnected_univ
        A' B' hA'open hB'open hA'B'cover hA'ne hB'ne
      exact Set.disjoint_left.mp hA'B'disjoint hxA' hxB'
    have hplane (x : S) : ∃ U : Set S, x ∈ U ∧ IsOpen U ∧
        Nonempty ((EuclideanSpace ℝ (Fin 2)) ≃ₜ U) := by
      let P := EuclideanSpace ℝ (Fin 2)
      let e := chartAt P x
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x)
        (e.map_source (mem_chart_source P x))
      let U := e.symm '' Metric.ball (e x) r
      have hsub : Metric.ball (e x) r ⊆ e.symm.source := hball
      have hopen : IsOpen U := e.symm.isOpen_image_of_subset_source Metric.isOpen_ball hsub
      have hx : x ∈ U := ⟨e x, Metric.mem_ball_self hr, e.left_inv (mem_chart_source P x)⟩
      let b := OpenPartialHomeomorph.univBall (e x) r
      have hmap : b '' (Set.univ : Set P) = Metric.ball (e x) r := by
        simpa only [b, OpenPartialHomeomorph.univBall_source,
          OpenPartialHomeomorph.univBall_target (e x) hr] using b.image_source_eq_target
      let g : P ≃ₜ Metric.ball (e x) r :=
        (Homeomorph.Set.univ P).symm.trans
          (b.homeomorphOfImageSubsetSource (by simp [b]) hmap)
      let f : Metric.ball (e x) r ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hsub rfl
      exact ⟨U, hx, hopen, ⟨g.trans f⟩⟩
    have hfinite (F : Set S) (hF : F.Finite) : IsConnected Fᶜ := by
      apply hgeneral hF
      intro x hxF
      obtain ⟨U, hxU, hU, ⟨g⟩⟩ := hplane x
      let f : EuclideanSpace ℝ (Fin 2) → S := fun z => (g z : S)
      have hfin : (f ⁻¹' F).Finite := hF.preimage (by
        intro a _ b _ hab
        exact g.injective (Subtype.ext hab))
      have hp : IsPathConnected (f ⁻¹' F)ᶜ :=
        hfin.countable.isPathConnected_compl_of_one_lt_rank (by
          apply Module.one_lt_rank_of_one_lt_finrank
          simp)
      have himage : f '' (f ⁻¹' F)ᶜ = U \ F := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨(g z).property, hz⟩
        · rintro ⟨hyU, hyF⟩
          obtain ⟨z, hz⟩ := g.surjective ⟨y, hyU⟩
          refine ⟨z, ?_, congrArg Subtype.val hz⟩
          change f z ∉ F
          simpa [f, hz] using hyF
      refine ⟨U, hU, hxU, ?_⟩
      rw [← himage]
      exact hp.image (continuous_subtype_val.comp g.continuous)
    intro hsurj
    let h : Circle ≃ₜ S := hr.toHomeomorphOfSurjective hsurj
    have hp : IsPreconnected (r ⁻¹' ({r 1, r (-1)} : Set S)ᶜ) :=
      h.isPreconnected_preimage.mpr (hfinite _ ((Set.finite_singleton _).insert _)).isPreconnected
    have heq : r ⁻¹' ({r 1, r (-1)} : Set S)ᶜ = ({1, -1} : Set Circle)ᶜ := by
      ext z
      simp only [mem_preimage, mem_compl_iff, mem_insert_iff, mem_singleton_iff]
      rw [hr.injective.eq_iff, hr.injective.eq_iff]
    rw [heq] at hp
    exact Circle.not_isPreconnected_compl_pair (Circle.neg_ne_self (1 : Circle)).symm hp
  let E := EuclideanSpace ℝ (Fin 3)
  let P := EuclideanSpace ℝ (Fin 2)
  let Q := Metric.sphere (0 : E) 1
  letI : Fact (Module.finrank ℝ E = 2 + 1) := ⟨by simp [E]⟩
  letI : ConnectedSpace Q := Subtype.connectedSpace (isConnected_sphere (by
    apply Module.one_lt_rank_of_one_lt_finrank
    simp [E]) (0 : E) (by norm_num : (0 : ℝ) ≤ 1))
  let f : C(Circle,Q) := ⟨c.map, c.embedded.continuous⟩
  have hn := homit f c.embedded
  simp only [Function.Surjective, not_forall, not_exists] at hn
  obtain ⟨x, hx⟩ := hn
  let e := stereographic' 2 x
  have hsource (z : Circle) : c.map z ∈ e.source := by
    simp only [e, stereographic'_source, mem_compl_iff, mem_singleton_iff]
    exact fun he => hx z he
  let r : C(Circle,P) := ⟨fun z => e (c.map z),
    e.continuousOn.comp_continuous c.embedded.continuous hsource⟩
  have hr : IsEmbedding r := by
    have hinj : Function.Injective r := by
      intro a b hab
      exact c.embedded.injective (e.injOn (hsource a) (hsource b) hab)
    exact (r.continuous.isClosedEmbedding hinj).isEmbedding
  let cLift : Curve P := ⟨r,hr⟩
  obtain ⟨d, hd, hbd⟩ := jordan_curve_bounds_disc cLift
    (isJordanCurve_range_of_isEmbedding_circle r hr)
  have he : IsOpenEmbedding e.symm := e.symm.isOpenEmbedding (by simp [e])
  let D : C(Metric.closedBall (0 : P) 1,Q) :=
    ⟨fun z => e.symm (d z), he.continuous.comp d.continuous⟩
  refine ⟨D, he.isEmbedding.comp hd, ?_⟩
  change (e.symm ∘ (d : Metric.closedBall (0:P) 1 → P)) '' _ = Set.range c.map
  rw [Set.image_comp, hbd]
  ext y
  constructor
  · rintro ⟨z, ⟨a,rfl⟩,rfl⟩
    exact ⟨a,(e.left_inv (hsource a)).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨r a,⟨a,rfl⟩,e.left_inv (hsource a)⟩


end CurveComplex.LocalSurgery
