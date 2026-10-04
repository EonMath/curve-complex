import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMarkedChartZeroGermLift
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual joint movie pasting from two endpoint patches with matching
literal outer seams. Supports are separated by source interval lengths. -/
theorem actual_two_endpoint_movie_pasting
    {S : Type} [TopologicalSpace S]
    (K : C(unitInterval × unitInterval,S))
    (J₀ J₁ : C((unitInterval × unitInterval) × unitInterval,S))
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a+b<1)
    (houter₀ : ∀ s τ,J₀ ((s,τ),1)=K (τ,⟨a,ha.le,by linarith⟩))
    (houter₁ : ∀ s τ,J₁ ((s,τ),1)=K (τ,⟨1-b,by linarith,by linarith⟩)) :
    ∃ c₀ c₁ : C(unitInterval,unitInterval),
      (∀ t,(c₀ t:ℝ)=min 1 ((t:ℝ)/a)) ∧
      (∀ t,(c₁ t:ℝ)=min 1 ((1-(t:ℝ))/b)) ∧
    ∃ W : C((unitInterval × unitInterval) × unitInterval,S),
      (∀ s τ t : unitInterval,(t:ℝ)≤a → W ((s,τ),t)=J₀ ((s,τ),c₀ t)) ∧
      (∀ s τ t : unitInterval,1-b≤(t:ℝ) → W ((s,τ),t)=J₁ ((s,τ),c₁ t)) ∧
      (∀ s τ t : unitInterval,a<(t:ℝ) → (t:ℝ)<1-b → W ((s,τ),t)=K (τ,t)) := by
  classical
  let c₀ : C(unitInterval,unitInterval) :=
    ⟨fun t => ⟨min 1 ((t:ℝ)/a),le_min (by norm_num) (div_nonneg t.property.1 ha.le),
      min_le_left _ _⟩,by fun_prop⟩
  let c₁ : C(unitInterval,unitInterval) :=
    ⟨fun t => ⟨min 1 ((1-(t:ℝ))/b),le_min (by norm_num)
      (div_nonneg (sub_nonneg.mpr t.property.2) hb.le),min_le_left _ _⟩,by fun_prop⟩
  let F₀ : C((unitInterval × unitInterval) × unitInterval,S) :=
    ⟨fun z => J₀ (z.1,c₀ z.2),by fun_prop⟩
  let F₁ : C((unitInterval × unitInterval) × unitInterval,S) :=
    ⟨fun z => J₁ (z.1,c₁ z.2),by fun_prop⟩
  let G : C((unitInterval × unitInterval) × unitInterval,S) :=
    ⟨fun z => K (z.1.2,z.2),by fun_prop⟩
  let R : Set ((unitInterval × unitInterval) × unitInterval) := {z | 1-b≤(z.2:ℝ)}
  let L : Set ((unitInterval × unitInterval) × unitInterval) := {z | (z.2:ℝ)≤a}
  have hrseam (z : (unitInterval × unitInterval) × unitInterval) (hz : (z.2:ℝ)=1-b) : F₁ z=G z := by
    have hc : c₁ z.2=1 := by
      apply Subtype.ext
      change min 1 ((1-(z.2:ℝ))/b)=1
      rw [hz]
      have hh : (1-(1-b))/b=1 := by field_simp; ring
      rw [hh]; simp
    have ht : z.2=⟨1-b,by linarith,by linarith⟩ := Subtype.ext hz
    change J₁ (z.1,c₁ z.2)=K (z.1.2,z.2)
    rw [hc,houter₁,ht]
  have hrcont : Continuous (R.piecewise F₁ G) := by
    apply Continuous.piecewise _ F₁.continuous G.continuous
    intro z hz
    have hh := frontier_le_subset_eq continuous_const
      (continuous_subtype_val.comp continuous_snd) hz
    exact hrseam z hh.symm
  let H : C((unitInterval × unitInterval) × unitInterval,S) := ⟨R.piecewise F₁ G,hrcont⟩
  have hlseam (z : (unitInterval × unitInterval) × unitInterval) (hz : (z.2:ℝ)=a) : F₀ z=H z := by
    have hc : c₀ z.2=1 := by
      apply Subtype.ext
      change min 1 ((z.2:ℝ)/a)=1
      rw [hz,div_self ha.ne']; simp
    have ht : z.2=⟨a,ha.le,by linarith⟩ := Subtype.ext hz
    have hn : z ∉ R := by change ¬1-b≤(z.2:ℝ); rw [hz]; linarith
    change J₀ (z.1,c₀ z.2)=R.piecewise F₁ G z
    rw [Set.piecewise_eq_of_notMem R F₁ G hn,hc,houter₀]
    change K (z.1.2,⟨a,ha.le,by linarith⟩)=K (z.1.2,z.2)
    rw [ht]
  have hwcont : Continuous (L.piecewise F₀ H) := by
    apply Continuous.piecewise _ F₀.continuous H.continuous
    intro z hz
    have hh := frontier_le_subset_eq
      (continuous_subtype_val.comp continuous_snd) continuous_const hz
    exact hlseam z hh
  let W : C((unitInterval × unitInterval) × unitInterval,S) := ⟨L.piecewise F₀ H,hwcont⟩
  refine ⟨c₀,c₁,(fun _ => rfl),(fun _ => rfl),W,?_,?_,?_⟩
  · intro s τ t ht
    exact Set.piecewise_eq_of_mem L F₀ H ht
  · intro s τ t ht
    have hn : ((s,τ),t) ∉ L := by change ¬(t:ℝ)≤a; linarith
    change L.piecewise F₀ H ((s,τ),t)=J₁ ((s,τ),c₁ t)
    rw [Set.piecewise_eq_of_notMem L F₀ H hn]
    exact Set.piecewise_eq_of_mem R F₁ G ht
  · intro s τ t ht₀ ht₁
    change L.piecewise F₀ H ((s,τ),t)=K (τ,t)
    rw [Set.piecewise_eq_of_notMem L F₀ H (not_le.mpr ht₀)]
    exact Set.piecewise_eq_of_notMem R F₁ G (not_le.mpr ht₁)
end CurveComplex.HyperellipticModel
