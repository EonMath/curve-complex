import CurveComplexGenusTwo.Hyperbolic.OriginalG1.EssentialCurveEssentialLoop
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualParametrizedClosedGeodesicG1GenusTwo
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.G1EmbeddedTraversalComposablePROVED

namespace CurveComplex.Hyperbolic
open Filter Topology
open scoped Manifold ContDiff UpperHalfPlane
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem essential_curve_geodesic_exists_unique_genus_two
    (H : ClosedHyperbolicMetric E) (c : Curve E) (hc : Essential c) (hE : IsGenus E 2) :
    ∃ g : Curve E,
      Essential g ∧
      FreeHomotopic ⟨c.map, c.embedded.continuous⟩
        ⟨g.map, g.embedded.continuous⟩ ∧
      (letI : MetricSpace E := H.metric; IsClosedGeodesic g.image) ∧
      ∀ h : Curve E,
        FreeHomotopic ⟨c.map, c.embedded.continuous⟩
          ⟨h.map, h.embedded.continuous⟩ →
        (letI : MetricSpace E := H.metric; IsClosedGeodesic h.image) → h.image = g.image := by
  classical
  have homotopic_of_free {f g : C(Circle,E)} (h : FreeHomotopic f g) : f.Homotopic g := by
    obtain ⟨K,h0,h1⟩ := h
    refine ⟨{ toFun := fun p => K (p.2,p.1)
              continuous_toFun := K.continuous.comp (continuous_snd.prodMk continuous_fst)
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · exact h0
    · exact h1
  have essential_nonnull {f : C(Circle,E)} (h : EssentialLoop f) : ¬ f.Nullhomotopic := by
    rintro ⟨x,⟨K⟩⟩
    apply h
    refine ⟨x,⟨fun p => K (p.2,p.1),
      K.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,?_,?_⟩
    · intro z; exact K.map_zero_left z
    · intro z; exact K.map_one_left z
  have null_of_bounds (d : Curve E) (hd : BoundsDisc d) :
      (⟨d.map,d.embedded.continuous⟩ : C(Circle,E)).Nullhomotopic := by
    obtain ⟨f,hf,hboundary⟩ := hd
    let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
    have hlift (z : Circle) : ∃ x : D, f x = d.map z := by
      have hz : d.map z ∈ f '' {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} :=
        hboundary.symm ▸ Set.mem_range_self z
      obtain ⟨x,_,hx⟩ := hz
      exact ⟨x,hx⟩
    let u : Circle → D := fun z => (hlift z).choose
    have hu (z) : f (u z) = d.map z := (hlift z).choose_spec
    have hcu : Continuous u := hf.continuous_iff.mpr (by
      have heq : (f : D → E) ∘ u = d.map := funext hu
      rw [heq]
      exact d.embedded.continuous)
    let U : C(Circle,D) := ⟨u,hcu⟩
    letI : ContractibleSpace D := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).contractibleSpace
      ⟨0,by simp [D]⟩
    have hn := ((id_nullhomotopic D).comp_left U).comp_right f
    have heq : f.comp ((ContinuousMap.id D).comp U) =
        (⟨d.map,d.embedded.continuous⟩ : C(Circle,E)) := by
      ext z
      exact hu z
    rwa [heq] at hn
  have free_of_homotopic {f g : C(Circle,E)} (h : f.Homotopic g) : FreeHomotopic f g := by
    obtain ⟨K⟩ := h
    refine ⟨⟨fun p => K (p.2,p.1),
      K.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,?_,?_⟩
    · intro z; exact K.map_zero_left z
    · intro z; exact K.map_one_left z
  have hcnull := essential_nonnull (essential_curve_is_essential_loop H c hc)
  obtain ⟨g,hhom,hparam,hemb,huniq⟩ :=
    closed_geodesic_exists_unique_parametrized_genus_two H ⟨c.map,c.embedded.continuous⟩
      (essential_curve_is_essential_loop H c hc) hE
  let d : Curve E := ⟨g,hemb c.embedded⟩
  have hd : Essential d := by
    intro hdisc
    obtain ⟨x,hx⟩ := null_of_bounds d hdisc
    apply hcnull
    exact ⟨x,(homotopic_of_free hhom).trans hx⟩
  have hgeo := parametrized_closed_geodesic_has_geodesic_image H g hparam
  refine ⟨d,hd,hhom,hgeo,?_⟩
  intro h hhom_h hgeo_h
  obtain ⟨u,huemb,hhu,hup,himage⟩ :=
    embedded_geodesic_image_has_parametrized_representative H h hgeo_h
  have hcu : FreeHomotopic ⟨c.map,c.embedded.continuous⟩ u :=
    free_of_homotopic ((homotopic_of_free hhom_h).trans (homotopic_of_free hhu))
  exact himage.symm.trans (huniq u hcu hup)


theorem essential_curve_geodesic_exists_unique_parametrized_genus_two
    (H : ClosedHyperbolicMetric E) (c : Curve E) (hc : Essential c) (hE : IsGenus E 2) :
    ∃ g : Curve E,
      Essential g ∧
      FreeHomotopic ⟨c.map, c.embedded.continuous⟩
        ⟨g.map, g.embedded.continuous⟩ ∧
      (letI : MetricSpace E := H.metric;
        IsParametrizedClosedGeodesic ⟨g.map, g.embedded.continuous⟩) ∧
      ∀ h : Curve E,
        FreeHomotopic ⟨c.map, c.embedded.continuous⟩
          ⟨h.map, h.embedded.continuous⟩ →
        (letI : MetricSpace E := H.metric; IsClosedGeodesic h.image) → h.image = g.image := by
  classical
  have homotopic_of_free {f g : C(Circle,E)} (h : FreeHomotopic f g) : f.Homotopic g := by
    obtain ⟨K,h0,h1⟩ := h
    refine ⟨{ toFun := fun p => K (p.2,p.1)
              continuous_toFun := K.continuous.comp (continuous_snd.prodMk continuous_fst)
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · exact h0
    · exact h1
  have essential_nonnull {f : C(Circle,E)} (h : EssentialLoop f) : ¬ f.Nullhomotopic := by
    rintro ⟨x,⟨K⟩⟩
    apply h
    refine ⟨x,⟨fun p => K (p.2,p.1),
      K.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,?_,?_⟩
    · intro z; exact K.map_zero_left z
    · intro z; exact K.map_one_left z
  have null_of_bounds (d : Curve E) (hd : BoundsDisc d) :
      (⟨d.map,d.embedded.continuous⟩ : C(Circle,E)).Nullhomotopic := by
    obtain ⟨f,hf,hboundary⟩ := hd
    let D := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
    have hlift (z : Circle) : ∃ x : D, f x = d.map z := by
      have hz : d.map z ∈ f '' {x | (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} :=
        hboundary.symm ▸ Set.mem_range_self z
      obtain ⟨x,_,hx⟩ := hz
      exact ⟨x,hx⟩
    let u : Circle → D := fun z => (hlift z).choose
    have hu (z) : f (u z) = d.map z := (hlift z).choose_spec
    have hcu : Continuous u := hf.continuous_iff.mpr (by
      have heq : (f : D → E) ∘ u = d.map := funext hu
      rw [heq]
      exact d.embedded.continuous)
    let U : C(Circle,D) := ⟨u,hcu⟩
    letI : ContractibleSpace D := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).contractibleSpace
      ⟨0,by simp [D]⟩
    have hn := ((id_nullhomotopic D).comp_left U).comp_right f
    have heq : f.comp ((ContinuousMap.id D).comp U) =
        (⟨d.map,d.embedded.continuous⟩ : C(Circle,E)) := by
      ext z
      exact hu z
    rwa [heq] at hn
  have free_of_homotopic {f g : C(Circle,E)} (h : f.Homotopic g) : FreeHomotopic f g := by
    obtain ⟨K⟩ := h
    refine ⟨⟨fun p => K (p.2,p.1),
      K.continuous.comp (continuous_snd.prodMk continuous_fst)⟩,?_,?_⟩
    · intro z; exact K.map_zero_left z
    · intro z; exact K.map_one_left z
  have hcnull := essential_nonnull (essential_curve_is_essential_loop H c hc)
  obtain ⟨g,hhom,hparam,hemb,huniq⟩ :=
    closed_geodesic_exists_unique_parametrized_genus_two H ⟨c.map,c.embedded.continuous⟩
      (essential_curve_is_essential_loop H c hc) hE
  let d : Curve E := ⟨g,hemb c.embedded⟩
  have hd : Essential d := by
    intro hdisc
    obtain ⟨x,hx⟩ := null_of_bounds d hdisc
    apply hcnull
    exact ⟨x,(homotopic_of_free hhom).trans hx⟩
  refine ⟨d,hd,hhom,hparam,?_⟩
  intro h hhom_h hgeo_h
  obtain ⟨u,huemb,hhu,hup,himage⟩ :=
    embedded_geodesic_image_has_parametrized_representative H h hgeo_h
  have hcu : FreeHomotopic ⟨c.map,c.embedded.continuous⟩ u :=
    free_of_homotopic ((homotopic_of_free hhom_h).trans (homotopic_of_free hhu))
  exact himage.symm.trans (huniq u hcu hup)


end CurveComplex.Hyperbolic
