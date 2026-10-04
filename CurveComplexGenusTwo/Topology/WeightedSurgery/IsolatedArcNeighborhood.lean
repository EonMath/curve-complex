import CurveComplexGenusTwo.Dictionary.ArcEssentialDefinitions
import CurveComplexGenusTwo.Filtration.Geometry.MarkedArcPrimitives
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.Smoothing.ActualSurfaceInteriorPointStarProof
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
import CurveComplexGenusTwo.Topology.Smoothing.FiniteActualInteriorPointStarsProof
import CurveComplexGenusTwo.Topology.Smoothing.MarkedIntervalCrosscutChartProof

namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A point of one arc interior can be isolated from all other arcs and marks,
using only the given finite pairwise interior-disjoint representative system. -/
theorem finite_arc_system_isolated_neighborhood
    (M : HyperellipticModel E S) {ι : Type*} [Finite ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (i : ι) (p : S) (hp : p ∈ arcInterior M (r i)) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧
      Disjoint U (M.cover.branch : Set S) ∧
      ∀ j, j ≠ i → Disjoint U (r j).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let others : Set S := ⋃ j : {j : ι // j ≠ i}, (r j.val).val.image
  have hclosed : IsClosed others :=
    (markedFamily_graph_compact (fun j : {j : ι // j ≠ i} => (r j.val).val)).isClosed
  have hpothers : p ∉ others := by
    intro hp'
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp'
    exact Set.disjoint_left.mp (hd i j.val (Ne.symm j.property)) hp ⟨hj, hp.2⟩
  refine ⟨(others ∪ (M.cover.branch : Set S))ᶜ,
    (hclosed.union M.cover.branch.finite_toSet.isClosed).isOpen_compl,
    ?_, ?_, ?_⟩
  · exact fun h => h.elim hpothers hp.2
  · exact Set.disjoint_left.mpr (fun _ hx hm => hx (Or.inr hm))
  · intro j hj
    exact Set.disjoint_left.mpr (fun _ hx ha =>
      hx (Or.inl (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, ha⟩)))

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.FiniteStarGeometry
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The original non-loop arc supplies its own global plane chart; interior
star normalization is supported away from every mark and every other arc. -/
theorem actual_disjoint_system_interior_star
    (M : HyperellipticModel E S) {ι : Type*} [Finite ι]
    (r : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j)))
    (i : ι) (hne : (r i).val.map 0 ≠ (r i).val.map 1)
    (τ : Interval) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1) :
    ∃ (e : OpenPartialHomeomorph S Plane) (W : Set S),
      (∀ t, (r i).val.map t ∈ e.source) ∧ IsOpen W ∧
      (r i).val.map τ ∈ W ∧ Disjoint W (M.cover.branch : Set S) ∧
      (∀ j, j ≠ i → Disjoint W (r j).val.image) ∧
      ∃ (γ : Bool → Interval → Plane),
        (∀ t, γ false t = e ((r i).val.map ⟨τ.val * (1-t.val), by
          constructor <;> nlinarith [τ.property.1, τ.property.2, t.property.1, t.property.2]⟩)) ∧
        (∀ t, γ true t = e ((r i).val.map ⟨τ.val + (1-τ.val)*t.val, by
          constructor <;> nlinarith [τ.property.1, τ.property.2, t.property.1, t.property.2]⟩)) ∧
        ∃ R : RadializedStar γ (e ((r i).val.map τ)) (e '' (e.source ∩ W)),
          ∃ q : ℝ, 0 < q ∧ R.vector true = -q • R.vector false ∧
          ∃ (P : AmbientIsotopy Plane) (H : AmbientIsotopy S),
            P.finalMap = R.H ∧
            (∀ t, H.map (t, (r i).val.map τ) = (r i).val.map τ) ∧
            (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
            (∀ j, j ≠ i → ∀ t s, H.map (t,(r j).val.map s) = (r j).val.map s) ∧
            (∀ t x, x ∉ W → H.map (t,x) = x) ∧
            (∀ t s, e (H.map (t,(r i).val.map s)) = P.map (t,e ((r i).val.map s))) ∧
            ∃ b : EssentialMarkedArc M,
              Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) (r i) ∧
              b.val.map = H.finalMap ∘ (r i).val.map ∧
              ∀ j, j ≠ i → Disjoint (arcInterior M b) (arcInterior M (r j)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  let a : NonLoopArc M := ⟨(r i).val, hne⟩
  obtain ⟨p, _, hp⟩ := a.exists_marked_puncture
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e : OpenPartialHomeomorph S Plane :=
    M.sphere.toOpenPartialHomeomorph.trans (stereographic' 2 (M.sphere p))
  have hesource (t : Interval) : (r i).val.map t ∈ e.source := by
    change (r i).val.map t ∈ Set.univ ∩ M.sphere ⁻¹' (stereographic' 2 (M.sphere p)).source
    rw [stereographic'_source]
    refine ⟨Set.mem_univ _, ?_⟩
    intro he
    have heq : (r i).val.map t = p := M.sphere.injective he
    exact hp ⟨t, heq⟩
  have hpoint : (r i).val.map τ ∈ arcInterior M (r i) := by
    refine ⟨Set.mem_range_self _, ?_⟩
    intro hm
    rcases (r i).val.marked_only_at_ends τ hm with h | h
    · have h0 := congrArg Subtype.val h
      change τ.val = 0 at h0
      linarith
    · have h1 := congrArg Subtype.val h
      change τ.val = 1 at h1
      linarith
  obtain ⟨W, hW, hpW, hmarks, hothers⟩ :=
    finite_arc_system_isolated_neighborhood M r hd i ((r i).val.map τ) hpoint
  have hη : Topology.IsClosedEmbedding (r i).val.map :=
    a.val.continuous.isClosedEmbedding a.injective
  obtain ⟨γ, hl, hr, R, q, hq, hopp, P, H, hP, hcenter, hout, hcoord⟩ :=
    actual_surface_interior_interval_point_star_normalization e (r i).val.map hη
      hesource τ hτ0 hτ1 W hW hpW
  have hfix : ∀ t x, x ∈ M.cover.branch → H.map (t,x) = x := by
    intro t x hx
    exact hout t x (fun hxW => Set.disjoint_left.mp hmarks hxW hx)
  have hold : ∀ j, j ≠ i → ∀ t s,
      H.map (t,(r j).val.map s) = (r j).val.map s := by
    intro j hj t s
    exact hout t ((r j).val.map s) (fun hxW =>
      Set.disjoint_left.mp (hothers j hj) hxW (Set.mem_range_self s))
  refine ⟨e, W, hesource, hW, hpW, hmarks, hothers, γ, hl, hr,
    R, q, hq, hopp, P, H, hP, hcenter, hfix, hold, hout, hcoord, ?_⟩
  obtain ⟨h, hh⟩ := H.homeomorphism_at 1
  have hfinal : H.finalMap = h := by
    funext x
    exact (hh x).symm
  have hfixFinal : ∀ x, x ∈ M.cover.branch → h x = x := by
    intro x hx
    rw [← hfinal]
    exact hfix 1 x hx
  let b := (r i).transport h hfixFinal
  refine ⟨b, ?_, ?_, ?_⟩
  · apply Eq.symm
    apply Quotient.sound
    refine ⟨H, hfix, ?_⟩
    change H.finalMap '' (r i).val.image = b.val.image
    rw [hfinal]
    exact (MarkedArc.transport_image (r i).val h hfixFinal).symm
  · change h ∘ (r i).val.map = H.finalMap ∘ (r i).val.map
    rw [hfinal]
  · intro j hj
    rw [arcInterior_transport]
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ hx
    obtain ⟨s, hs⟩ := hx.1
    have hhfixed : h ((r j).val.map s) = (r j).val.map s := by
      rw [← hfinal]
      exact hold j hj 1 s
    have hyEq : y = (r j).val.map s := h.injective (hs.symm.trans hhfixed.symm)
    exact Set.disjoint_left.mp (hd i j (Ne.symm hj)) hy
      ⟨⟨s, hyEq.symm⟩, fun hm => hy.2 hm⟩

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Shared marked endpoints are removed by taking literal middle-third
subarcs. The charts, embeddings and disjoint full ranges are produced from the
actual representative system, not assumed as geometric certificates. -/
theorem actual_finite_middle_third_chart_system
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    ∃ (η : ι → Interval → S) (e : ι → OpenPartialHomeomorph S Plane),
      (∀ i t, η i t = (r i).val.map ⟨(1+t.val)/3, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩) ∧
      (∀ i, Topology.IsClosedEmbedding (η i)) ∧
      (∀ i j, i ≠ j → Disjoint (range (η i)) (range (η j))) ∧
      (∀ i t, η i t ∈ (e i).source) ∧
      ∀ i t, η i t ∈ arcInterior M (r i) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let η : ι → Interval → S := fun i t => (r i).val.map
    ⟨(1+t.val)/3, by constructor <;> nlinarith [t.property.1, t.property.2]⟩
  have hinside (i : ι) (t : Interval) : η i t ∈ arcInterior M (r i) := by
    refine ⟨⟨_, rfl⟩, ?_⟩
    intro hm
    rcases (r i).val.marked_only_at_ends _ hm with h | h
    · have hh := congrArg Subtype.val h
      change (1+t.val)/3 = 0 at hh
      nlinarith [t.property.1]
    · have hh := congrArg Subtype.val h
      change (1+t.val)/3 = 1 at hh
      nlinarith [t.property.2]
  have hemb (i : ι) : Topology.IsClosedEmbedding (η i) := by
    apply Continuous.isClosedEmbedding
    · exact (r i).val.continuous.comp
        (((continuous_const.add continuous_subtype_val).div_const 3).subtype_mk _)
    · intro t u heq
      have hh := congrArg Subtype.val ((NonLoopArc.injective ⟨(r i).val, hne i⟩) heq)
      apply Subtype.ext
      change (1+t.val)/3 = (1+u.val)/3 at hh
      linarith
  have hdis (i j : ι) (hij : i ≠ j) : Disjoint (range (η i)) (range (η j)) := by
    exact (hd i j hij).mono (by rintro _ ⟨t,rfl⟩; exact hinside i t)
      (by rintro _ ⟨t,rfl⟩; exact hinside j t)
  have hpuncture (i : ι) : ∃ p ∈ M.cover.branch, p ∉ (r i).val.image :=
    NonLoopArc.exists_marked_puncture ⟨(r i).val, hne i⟩
  choose p _ hp using hpuncture
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e : ι → OpenPartialHomeomorph S Plane := fun i =>
    M.sphere.toOpenPartialHomeomorph.trans (stereographic' 2 (M.sphere (p i)))
  refine ⟨η,e,fun _ _ => rfl,hemb,hdis,?_,hinside⟩
  intro i t
  change η i t ∈ Set.univ ∩ M.sphere ⁻¹' (stereographic' 2 (M.sphere (p i))).source
  rw [stereographic'_source]
  refine ⟨Set.mem_univ _, ?_⟩
  intro he
  have heq : η i t = p i := M.sphere.injective he
  exact hp i (heq ▸ (hinside i t).1)

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.FiniteStarGeometry
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A finite actual non-loop disjoint arc system admits simultaneous interior
radialization with all marked points fixed and with class-preserving disjoint
representatives. This produces the chart data from the original arcs. -/
theorem actual_finite_disjoint_system_interior_radialization
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    ∃ (η : ι → Interval → S) (e : ι → OpenPartialHomeomorph S Plane),
      (∀ i t, η i t = (r i).val.map ⟨(1+t.val)/3, by
        constructor <;> nlinarith [t.property.1, t.property.2]⟩) ∧
      (∀ i t, η i t ∈ (e i).source) ∧
      ∃ (V : ι → Set S), (∀ i, IsOpen (V i)) ∧
        (∀ i, Disjoint (V i) (M.cover.branch : Set S)) ∧
        (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
        ∃ (γ : ι → Bool → Interval → Plane),
          (∀ i t, γ i false t = e i (η i ⟨(1-t.val)/2, by
            constructor <;> nlinarith [t.property.1, t.property.2]⟩)) ∧
          (∀ i t, γ i true t = e i (η i ⟨(1+t.val)/2, by
            constructor <;> nlinarith [t.property.1, t.property.2]⟩)) ∧
          ∃ R : ∀ i, RadializedStar (γ i) (e i (η i ⟨1/2, by norm_num⟩))
              (e i '' ((e i).source ∩ V i)),
            ∃ q : ι → ℝ, (∀ i, 0 < q i ∧ (R i).vector true = -(q i) • (R i).vector false) ∧
            ∃ (P : ι → AmbientIsotopy Plane) (H : AmbientIsotopy S),
              (∀ i, (P i).finalMap = (R i).H) ∧
              (∀ i t, H.map (t,η i ⟨1/2, by norm_num⟩) = η i ⟨1/2, by norm_num⟩) ∧
              (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
              (∀ i t s, e i (H.map (t,η i s)) = (P i).map (t,e i (η i s))) ∧
              ∃ b : ι → EssentialMarkedArc M,
                (∀ i, Quotient.mk (essentialArcSetoid M) (b i) =
                  Quotient.mk (essentialArcSetoid M) (r i)) ∧
                (∀ i, (b i).val.map = H.finalMap ∘ (r i).val.map) ∧
                ∀ i j, i ≠ j → Disjoint (arcInterior M (b i)) (arcInterior M (b j)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  letI : CompactSpace S := M.sphere.symm.compactSpace
  obtain ⟨η,e,hη,hemb,hdis,hsource,hinside⟩ :=
    actual_finite_middle_third_chart_system M r hne hd
  let τ : ι → Interval := fun _ => ⟨1/2, by norm_num⟩
  let W : Set S := (M.cover.branch : Set S)ᶜ
  have hW : IsOpen W := M.cover.branch.finite_toSet.isClosed.isOpen_compl
  have hpW (i : ι) : η i (τ i) ∈ W := (hinside i (τ i)).2
  obtain ⟨V,hV,hVW,hVV,γ,hl,hr,R,q,hq,P,H,hP,hcenter,hout,hcoord⟩ :=
    finite_actual_surface_interval_point_stars η hemb hdis e hsource τ
      (by intro i; norm_num [τ]) (by intro i; norm_num [τ]) W hW hpW
  have hmarks : ∀ t x, x ∈ M.cover.branch → H.map (t,x) = x := by
    intro t x hx
    exact hout t x (not_not_intro hx)
  refine ⟨η,e,hη,hsource,V,hV,?_,hVV,γ,?_,?_,R,q,hq,P,H,hP,hcenter,hmarks,hcoord,?_⟩
  · intro i
    exact Set.disjoint_left.mpr (fun x hx hm => hVW i hx hm)
  · intro i t
    convert hl i t using 2
    congr 2
    dsimp [τ]
    ring
  · intro i t
    convert hr i t using 2
    congr 2
    dsimp [τ]
    ring
  · obtain ⟨h,hh⟩ := H.homeomorphism_at 1
    have hfinal : H.finalMap = h := funext (fun x => (hh x).symm)
    have hfix : ∀ x, x ∈ M.cover.branch → h x = x := by
      intro x hx
      rw [← hfinal]
      exact hmarks 1 x hx
    let b : ι → EssentialMarkedArc M := fun i => (r i).transport h hfix
    refine ⟨b,?_,?_,?_⟩
    · intro i
      apply Eq.symm
      apply Quotient.sound
      refine ⟨H,hmarks,?_⟩
      change H.finalMap '' (r i).val.image = (b i).val.image
      rw [hfinal]
      exact (MarkedArc.transport_image (r i).val h hfix).symm
    · intro i
      change h ∘ (r i).val.map = H.finalMap ∘ (r i).val.map
      rw [hfinal]
    · intro i j hij
      exact arcInterior_transport_disjoint (r i) (r j) h hfix (hd i j hij)

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Coordinate crosscuts on the original disjoint arc system, with the
ambient support avoiding every mark and every other entire arc image. -/
theorem actual_finite_middle_third_crosscut_charts
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (r : ι → EssentialMarkedArc M)
    (hne : ∀ i, (r i).val.map 0 ≠ (r i).val.map 1)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (r i)) (arcInterior M (r j))) :
    ∃ Echart : ι → OpenPartialHomeomorph S Plane,
      ∀ i,
        Disjoint (Echart i).source (M.cover.branch : Set S) ∧
        (∀ j, j ≠ i → Disjoint (Echart i).source (r j).val.image) ∧
        Plane.closedSquare 0 1 ⊆ (Echart i).target ∧
        ((r i).val.map ∘ Set.projIcc 0 1 zero_le_one) '' Icc (1/3:ℝ) (2/3) ⊆ (Echart i).source ∧
        (∀ x ∈ (Echart i).source, x ∈ (r i).val.image ↔ Echart i x 1 = 0) ∧
        {x : S | x ∈ (Echart i).source ∧ Echart i x ∈ Plane.closedSquare 0 1} ∩
          (r i).val.image = ((r i).val.map ∘ Set.projIcc 0 1 zero_le_one) '' Icc (1/3:ℝ) (2/3) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨η,e,hη,_,_,hsource,hinside⟩ := actual_finite_middle_third_chart_system M r hne hd
  let others (i : ι) : Set S := ⋃ j : {j : ι // j ≠ i}, (r j.val).val.image
  let W (i : ι) : Set S := (others i ∪ (M.cover.branch : Set S))ᶜ
  have hW (i : ι) : IsOpen (W i) := by
    exact ((markedFamily_graph_compact
      (fun j : {j : ι // j ≠ i} => (r j.val).val)).isClosed.union
        M.cover.branch.finite_toSet.isClosed).isOpen_compl
  have hinW (i : ι) (t : Interval) : η i t ∈ W i := by
    intro h
    rcases h with h | h
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      exact Set.disjoint_left.mp (hd i j.val (Ne.symm j.property))
        (hinside i t) ⟨hj,(hinside i t).2⟩
    · exact (hinside i t).2 h
  have hsub (i : ι) : ((r i).val.map ∘ Set.projIcc 0 1 zero_le_one) ''
      Icc (1/3:ℝ) (2/3) ⊆ W i ∩ (e i).source := by
    rintro _ ⟨t,ht,rfl⟩
    let u : Interval := ⟨3*t-1, by constructor <;> nlinarith [ht.1,ht.2]⟩
    have heq : (r i).val.map (Set.projIcc 0 1 zero_le_one t) = η i u := by
      rw [hη]
      apply congrArg (r i).val.map
      rw [Set.projIcc_of_mem zero_le_one (show t ∈ Icc (0:ℝ) 1 from
        ⟨by linarith [ht.1],by linarith [ht.2]⟩)]
      apply Subtype.ext
      dsimp [u]
      ring
    change (r i).val.map (Set.projIcc 0 1 zero_le_one t) ∈ W i ∩ (e i).source
    rw [heq]
    exact ⟨hinW i u,hsource i u⟩
  have hlocal (i : ι) := actual_interval_subarc_crosscut_chart
    (r i).val.map (r i).val.continuous
    (r i).val.injective_except_loop_closure (1/3) (2/3)
    (by norm_num) (by norm_num) (by norm_num) (e i) (W i) (hW i) (hsub i)
  choose Echart hE htarget hsegment hleft hright hline hbox using hlocal
  refine ⟨Echart,?_⟩
  intro i
  refine ⟨?_,?_,htarget i,hsegment i,hline i,hbox i⟩
  · exact Set.disjoint_left.mpr (fun x hx hm => (hE i hx).1 (Or.inr hm))
  · intro j hj
    exact Set.disjoint_left.mpr (fun x hx ha =>
      (hE i hx).1 (Or.inl (Set.mem_iUnion.mpr ⟨⟨j,hj⟩,ha⟩)))

end CurveComplex.HyperellipticModel
