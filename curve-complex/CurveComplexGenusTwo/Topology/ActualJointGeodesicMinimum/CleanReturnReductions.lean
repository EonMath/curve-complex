import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.PathLiftReductions
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.TwoAnchorUniqueness

namespace CurveComplex.Hyperbolic.JointMinimum

open Set Topology CurveComplex.LocalSurgery

theorem clean_return_impossible_on_developed_cover
    {E : Type} [TopologicalSpace E] (a b : Curve E)
    (u v : E) (huv : u ≠ v) (f g : Path u v)
    (hf : Set.range f ⊆ a.image) (hg : Set.range g ⊆ b.image)
    (hclean : f '' Set.Ioo (0 : Interval) 1 ⊆ b.imageᶜ)
    (hhom : f.Homotopic g)
    (p : H2 → connectedComponent u) (hp : IsCoveringMap p)
    (hpsurj : Function.Surjective p)
    (hconfA : ∀ h : C(Interval, H2), (∀ t, (p (h t)).val ∈ a.image) →
      ∃ L : ℝ → H2, Isometry L ∧ Set.range h ⊆ Set.range L ∧
        Set.range (fun t => (p (L t)).val) = a.image)
    (hconfB : ∀ h : C(Interval, H2), (∀ t, (p (h t)).val ∈ b.image) →
      ∃ L : ℝ → H2, Isometry L ∧ Set.range h ⊆ Set.range L ∧
        Set.range (fun t => (p (L t)).val) = b.image) : False := by
  obtain ⟨F, G, hF, hG, hzero, hone⟩ :=
    homotopic_paths_have_common_endpoint_lifts u v f g hhom p hp hpsurj
  obtain ⟨L, hL, hFL, hLproject⟩ := hconfA F (fun t => by
    rw [hF t]; exact hf ⟨t, rfl⟩)
  obtain ⟨M, hM, hGM, hMproject⟩ := hconfB G (fun t => by
    rw [hG t]; exact hg ⟨t, rfl⟩)
  have hendpoints : F 0 ≠ F 1 := by
    intro heq
    have heq' := congrArg (fun z : H2 => (p z).val) heq
    rw [hF 0, hF 1, f.source, f.target] at heq'
    exact huv heq'
  obtain ⟨s₀, hs₀⟩ := hFL ⟨0, rfl⟩
  obtain ⟨s₁, hs₁⟩ := hFL ⟨1, rfl⟩
  obtain ⟨t₀, ht₀⟩ := hGM ⟨0, rfl⟩
  obtain ⟨t₁, ht₁⟩ := hGM ⟨1, rfl⟩
  have hs : s₀ ≠ s₁ := by
    intro heq
    exact hendpoints (hs₀.symm.trans ((congrArg L heq).trans hs₁))
  have hranges : Set.range L = Set.range M :=
    TwoAnchor.isometric_lines_same_range_of_two_meetings L M hL hM
      s₀ s₁ t₀ t₁ hs (hs₀.trans (hzero.trans ht₀.symm))
        (hs₁.trans (hone.trans ht₁.symm))
  let middle : Interval := ⟨1 / 2, by norm_num⟩
  have hmiddle : middle ∈ Set.Ioo (0 : Interval) 1 := by
    constructor <;> change (_ : ℝ) < _ <;> norm_num [middle]
  have hnot : f middle ∉ b.image := hclean ⟨middle, hmiddle, rfl⟩
  apply hnot
  have hFM : F middle ∈ Set.range M := hranges ▸ hFL ⟨middle, rfl⟩
  obtain ⟨t, ht⟩ := hFM
  rw [← hF middle, ← ht, ← hMproject]
  exact ⟨t, rfl⟩

theorem fixed_comparison_minimum_of_no_clean_return
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (a b : EssentialCurve E) (ht : Transverse a.val b.val)
    (hno : ∀ (u v : E), u ≠ v → ∀ f g : Path u v,
      Set.range f ⊆ a.val.image → Set.range g ⊆ b.val.image →
      f '' Set.Ioo (0 : Interval) 1 ⊆ b.val.imageᶜ → f.Homotopic g → False) :
    (a.val.image ∩ b.val.image).ncard =
      geometricIntersection (Quotient.mk (essentialCurveSetoid E) a)
        (Quotient.mk (essentialCurveSetoid E) b) := by
  rw [Set.ncard_eq_toFinset_card _ ht.1]
  apply Nat.le_antisymm
  · by_contra hn
    obtain ⟨a', haa', ht', hcount⟩ := audited_fixed_comparison_minimum a b ht
    have hlt : ht'.1.toFinset.card < ht.1.toFinset.card := by
      rw [hcount]
      exact Nat.lt_of_not_ge hn
    obtain ⟨u, v, huv, _, _, f, g, _, hf, hg, hclean, hhom⟩ :=
      count_decreasing_isotopy_has_returning_subarc a b a' ht haa' ht' hlt
    exact hno u v huv f g hf hg hclean hhom
  · exact Nat.sInf_le ⟨a, b, rfl, rfl, ht, rfl⟩

end CurveComplex.Hyperbolic.JointMinimum
