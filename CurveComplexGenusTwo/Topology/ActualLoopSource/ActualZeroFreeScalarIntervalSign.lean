import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFiniteScalarZeroMesh
namespace CurveComplex.HyperellipticModel
open Set Topology
theorem actual_zero_free_scalar_interval_sign (g : C(Interval,ℝ)) (x y s : Interval)
    (hxs : x < s) (hsy : s < y) (hs : g s < 0)
    (hn : ∀ t, x < t → t < y → g t ≠ 0) :
    ∀ t ∈ Set.Icc x y, g t ≤ 0 := by
  intro t ht
  by_contra hgt
  have htpos : 0 < g t := lt_of_not_ge hgt
  rcases le_total s t with hst | hts
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc hst g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have hzt : z < t := lt_of_le_of_ne hz.2 (by
      intro he; rw [he] at hgz; linarith)
    exact hn z (hxs.trans_le hz.1) (hzt.trans_le ht.2) hgz
  · obtain ⟨z,hz,hgz⟩ := intermediate_value_Icc' hts g.continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (g s) (g t) from ⟨hs.le,htpos.le⟩)
    have htz : t < z := lt_of_le_of_ne hz.1 (by
      intro he; rw [← he] at hgz; linarith)
    exact hn z (ht.1.trans_lt htz) (hz.2.trans_lt hsy) hgz
theorem actual_scalar_interval_sign_constant (g : C(Interval,ℝ))
    (x y s t : Interval) (hs : s ∈ Set.Ioo x y) (ht : t ∈ Set.Ioo x y)
    (hn : ∀ z, x < z → z < y → g z ≠ 0) :
    g s < 0 ↔ g t < 0 := by
  constructor
  · intro h
    exact lt_of_le_of_ne (actual_zero_free_scalar_interval_sign g x y s hs.1 hs.2 h hn t
      ⟨ht.1.le,ht.2.le⟩) (hn t ht.1 ht.2)
  · intro h
    exact lt_of_le_of_ne (actual_zero_free_scalar_interval_sign g x y t ht.1 ht.2 h hn s
      ⟨hs.1.le,hs.2.le⟩) (hn s hs.1 hs.2)
end CurveComplex.HyperellipticModel
