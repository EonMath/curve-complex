import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualCompactAxisChartStrip
namespace CurveComplex
open Set Topology Schoenflies Metric

/-- Choose pairwise disjoint positive-radius closed parameter windows in the
specified actual charts. Relative interval balls include marked endpoints. -/
theorem source_finite_axis_parameter_windows
    {S K : Type} [TopologicalSpace S] [Fintype K]
    (f : C(Interval,S)) (θ : K → Interval) (hθ : Function.Injective θ)
    (E : K → OpenPartialHomeomorph S Plane)
    (hpE : ∀ k, f (θ k) ∈ (E k).source) :
    ∃ η : K → ℝ, (∀ k, 0 < η k) ∧
      (∀ k, f '' closedBall (θ k) (η k) ⊆ (E k).source) ∧
      (∀ i j, i ≠ j → Disjoint (closedBall (θ i) (η i)) (closedBall (θ j) (η j))) := by
  classical
  obtain ⟨V,hV,hVdis⟩ := source_finite_compact_open_separation
    (fun k => ({θ k} : Set Interval)) (fun _ => isCompact_singleton)
  have hmake (k) : ∃ η : ℝ, 0 < η ∧ closedBall (θ k) η ⊆
      V k ∩ f ⁻¹' (E k).source := by
    have hop : IsOpen (V k ∩ f ⁻¹' (E k).source) :=
      (hV k).1.inter ((E k).open_source.preimage f.continuous)
    have hm : θ k ∈ V k ∩ f ⁻¹' (E k).source :=
      ⟨(hV k).2 (mem_singleton _),hpE k⟩
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp (hop.mem_nhds hm)
    exact ⟨r/2,half_pos hr,(closedBall_subset_ball (half_lt_self hr)).trans hrsub⟩
  choose η hη hsub using hmake
  refine ⟨η,hη,?_,?_⟩
  · intro k
    exact image_subset_iff.mpr (fun u hu => (hsub k hu).2)
  · intro i j hij
    exact (hVdis i j (disjoint_singleton.mpr (fun he => hij (hθ he)))).mono
      (fun u hu => (hsub i hu).1) (fun u hu => (hsub j hu).1)

/-- Construct finitely many pairwise disjoint LITERAL vertical strips in the
prescribed actual axis charts, with exact original center coordinates. Their
nonzero points avoid the WHOLE original arc, even if the chart has distant
returns. This is a producer; no strip, width, radius or compatibility is input. -/
theorem source_finite_actual_axis_patches
    {S K : Type} [TopologicalSpace S] [T2Space S] [Fintype K]
    (f : C(Interval,S)) (hf : IsEmbedding f)
    (θ : K → Interval) (hθ : Function.Injective θ)
    (E : K → OpenPartialHomeomorph S Plane)
    (hpE : ∀ k, f (θ k) ∈ (E k).source)
    (haxis : ∀ k u, f u ∈ (E k).source → E k (f u) 1 = 0)
    (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U) :
    ∃ η δ : K → ℝ, (∀ k, 0 < η k ∧ 0 < δ k) ∧
      ∃ B : (k : K) → ↥(closedBall (θ k) (η k)) × Icc (-1:ℝ) 1 → S,
        (∀ k, IsEmbedding (B k)) ∧
        (∀ k, range (B k) ⊆ U ∩ (E k).source) ∧
        (∀ k u, B k (u,⟨0,by norm_num⟩) = f u) ∧
        (∀ k z, E k (B k z) = Plane.mk (E k (f z.1) 0) (δ k*(z.2:ℝ))) ∧
        (∀ k z, B k z ∈ range f ↔ (z.2:ℝ) = 0) ∧
        (∀ i j, i ≠ j → Disjoint (range (B i)) (range (B j))) := by
  classical
  obtain ⟨η,hη,hηchart,hηdis⟩ := source_finite_axis_parameter_windows f θ hθ E hpE
  let T : K → Set Interval := fun k => closedBall (θ k) (η k)
  let C : K → Set S := fun k => f '' T k
  have hC (k) : IsCompact (C k) := (isCompact_closedBall _ _).image f.continuous
  obtain ⟨V,hV,hVdis⟩ := source_finite_compact_open_separation C hC
  have hmake (k : K) : ∃ δ : ℝ, 0 < δ ∧
      ∃ B : ↥(T k) × Icc (-1:ℝ) 1 → S,
        IsEmbedding B ∧ range B ⊆ (U ∩ V k) ∩ (E k).source ∧
        (∀ u, B (u,⟨0,by norm_num⟩) = f u) ∧
        (∀ z, E k (B z) = Plane.mk (E k (f z.1) 0) (δ*(z.2:ℝ))) := by
    letI : CompactSpace ↥(T k) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    let g : C(↥(T k),S) := f.restrict (T k)
    have hg : IsEmbedding g := hf.comp IsEmbedding.subtypeVal
    have hge : range g ⊆ (E k).source := by
      rintro x ⟨t,rfl⟩
      exact hηchart k ⟨t,t.property,rfl⟩
    have hgaxis (t) : E k (g t) 1 = 0 := haxis k t (hge (mem_range_self t))
    have hgU : range g ⊆ U ∩ V k := by
      rintro x ⟨t,rfl⟩
      exact ⟨hfU (mem_range_self (t:Interval)),(hV k).2 ⟨t,t.property,rfl⟩⟩
    obtain ⟨δ,hδ,B,hB,hBU,hcenter,hcoords,havoid⟩ := source_whole_axis_chart_strip
      g hg (E k) hge hgaxis (U ∩ V k) (hU.inter (hV k).1) hgU
    exact ⟨δ,hδ,B,hB,hBU,hcenter,hcoords⟩
  choose δ hδ B hB hBU hcenter hcoords using hmake
  refine ⟨η,δ,fun k => ⟨hη k,hδ k⟩,B,hB,?_,hcenter,hcoords,?_,?_⟩
  · exact fun k x hx => ⟨(hBU k hx).1.1,(hBU k hx).2⟩
  · intro k z
    constructor
    · rintro ⟨u,hu⟩
      have hfu : f u ∈ (E k).source := hu ▸ (hBU k (mem_range_self z)).2
      have hh := congrArg (fun x => E k x 1) hu
      rw [haxis k u hfu,hcoords] at hh
      change 0 = δ k*(z.2:ℝ) at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left (hδ k).ne'
    · intro hz0
      have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl (Subtype.ext hz0)
      rw [he,hcenter]
      exact mem_range_self _
  · intro i j hij
    have hCd : Disjoint (C i) (C j) := by
      rw [disjoint_left]
      rintro x ⟨u,hu,rfl⟩ ⟨v,hv,hvu⟩
      have heq := hf.injective hvu
      exact disjoint_left.mp (hηdis i j hij) hu (heq ▸ hv)
    exact (hVdis i j hCd).mono
      (fun x hx => (hBU i hx).1.2) (fun x hx => (hBU j hx).1.2)
end CurveComplex
#print axioms CurveComplex.source_finite_axis_parameter_windows
#print axioms CurveComplex.source_finite_actual_axis_patches
