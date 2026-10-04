import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualNegativeComplexAxisAdaptedChartKernelRecovery
import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualMarkedSharedAxisSectorNamedKernelRecovery
namespace CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel
open Set Topology CurveComplex.LocalSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actualMarkedNegativeComplexSeamTraceChangesSideInEveryAdaptedChart
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (D : OpenPartialHomeomorph S ℂ)
    (hDaxis : ∀ x∈D.source,‖D x‖<1 → (x∈a.val.image ↔ D x∉Complex.slitPlane))
    (γ : C(Interval,S)) (u : Interval) (hp : γ u∈a.val.image)
    (hpD : γ u∈D.source) (hn : ‖D (γ u)‖<1) (hneg : (D (γ u)).re<0)
    (C : OpenPartialHomeomorph S (ℝ × ℝ)) (hpC : γ u∈C.source)
    (hCaxis : ∀ x∈C.source,x∈a.val.image ↔ (C x).1=0)
    (δ₀ : ℝ) (hδ₀ : 0<δ₀)
    (hDflip : ∀ v w : Interval,u.val-δ₀<v.val → v<u → u<w → w.val<u.val+δ₀ →
      (D (γ v)).im≠0 ∧ (D (γ w)).im≠0 ∧
        ((D (γ v)).im<0 ↔ ¬(D (γ w)).im<0)) :
    ∃ δ : ℝ,0<δ ∧ ∀ v w : Interval,u.val-δ<v.val → v<u → u<w → w.val<u.val+δ →
      γ v∈C.source ∧ γ w∈C.source ∧
      (C (γ v)).1≠0 ∧ (C (γ w)).1≠0 ∧
      ((C (γ v)).1<0 ↔ ¬(C (γ w)).1<0) := by
  obtain ⟨K,hpK,hKaxis,hKfirst,hKsource⟩ :=
    actualNegativeComplexAxisHasAdaptedRealChart a.val.image D (γ u) hpD hn hneg hDaxis
  obtain ⟨U,hU,hpU,hUsub,hSides⟩ :=
    actualMarkedSharedAxisChartsSameSide M a (γ u) hp K C hpK hpC hKaxis hCaxis
  have hpre : γ ⁻¹' U∈𝓝 u := γ.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)
  obtain ⟨d,hd,hnear⟩ := Metric.mem_nhds_iff.mp hpre
  let δ := min δ₀ d
  have hδ : 0<δ := lt_min hδ₀ hd
  have hδ₀le : δ≤δ₀ := min_le_left _ _
  have hδd : δ≤d := min_le_right _ _
  refine ⟨δ,hδ,?_⟩
  intro v w hvlo hvu huw hwhi
  have hγU (t : Interval) (hlo : u.val-δ<t.val) (hhi : t.val<u.val+δ) : γ t∈U := by
    apply hnear
    rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq,abs_lt]
    constructor <;> linarith only [hlo,hhi,hδd]
  have hvuR : v.val<u.val := hvu
  have hvU := hγU v hvlo (by linarith only [hvuR,hδ])
  have huwR : u.val<w.val := huw
  have hwU := hγU w (by linarith only [hδ,huwR]) hwhi
  obtain ⟨hvn,hwn,hflip⟩ := hDflip v w (by linarith only [hvlo,hδ₀le]) hvu huw
    (by linarith only [hwhi,hδ₀le])
  have hvoff : γ v∉a.val.image := by
    intro ha
    have he := (hKaxis _ (hUsub hvU).1).mp ha
    rw [hKfirst] at he
    exact hvn he
  have hwoff : γ w∉a.val.image := by
    intro ha
    have he := (hKaxis _ (hUsub hwU).1).mp ha
    rw [hKfirst] at he
    exact hwn he
  have hCnV : (C (γ v)).1≠0 := fun he => hvoff ((hCaxis _ (hUsub hvU).2).mpr he)
  have hCnW : (C (γ w)).1≠0 := fun he => hwoff ((hCaxis _ (hUsub hwU).2).mpr he)
  have hsame := hSides _ hvU _ hwU hvoff hwoff
  rw [hKfirst,hKfirst] at hsame
  have hnotSame : ¬((C (γ v)).1<0 ↔ (C (γ w)).1<0) := by
    intro he
    have hdeq := hsame.mpr he
    by_cases hv : (D (γ v)).im<0
    · exact (hflip.mp hv) (hdeq.mp hv)
    · have hw : ¬(D (γ w)).im<0 := fun hw => hv (hdeq.mpr hw)
      exact hv (hflip.mpr hw)
  refine ⟨(hUsub hvU).2,(hUsub hwU).2,hCnV,hCnW,?_⟩
  by_cases hv : (C (γ v)).1<0
  · by_cases hw : (C (γ w)).1<0
    · exact False.elim (hnotSame (iff_of_true hv hw))
    · exact iff_of_true hv hw
  · by_cases hw : (C (γ w)).1<0
    · exact iff_of_false hv (not_not_intro hw)
    · exact False.elim (hnotSame (iff_of_false hv hw))
end CurveComplex.HyperellipticModel.H1ActualMarkedSectorKernel
