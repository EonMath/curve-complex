import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainProbe

namespace CurveComplex.Hyperbolic
open Set
variable {E : Type} [TopologicalSpace E]

theorem developmentChain_append {F : Set (OpenPartialHomeomorph E H2)}
    {x y z : E} {r s : ENNReal} (h : DevelopmentChain F x y r)
    (k : DevelopmentChain F y z s) : DevelopmentChain F x z (r + s) := by
  induction h with
  | nil => simpa using k
  | cons e he hx hy tail ih =>
    simpa only [add_assoc] using DevelopmentChain.cons e he hx hy (ih k)

theorem developmentChain_reverse {F : Set (OpenPartialHomeomorph E H2)}
    {x y : E} {r : ENNReal} (h : DevelopmentChain F x y r) :
    DevelopmentChain F y x r := by
  induction h with
  | nil x => exact DevelopmentChain.nil x
  | @cons x y z t e he hx hy tail ih =>
    have last : DevelopmentChain F y x (edist (e y) (e x)) := by
      simpa only [add_zero] using DevelopmentChain.cons e he hy hx (DevelopmentChain.nil x)
    simpa only [edist_comm, add_comm] using developmentChain_append ih last

theorem developmentChainEDist_self (F : Set (OpenPartialHomeomorph E H2)) (x : E) :
    developmentChainEDist F x x = 0 := by
  apply le_antisymm
  · exact iInf_le_of_le 0 (iInf_le_of_le (DevelopmentChain.nil x) le_rfl)
  · exact bot_le

theorem developmentChainEDist_le_chain {F : Set (OpenPartialHomeomorph E H2)} {x y : E} {r : ENNReal}
    (h : DevelopmentChain F x y r) : developmentChainEDist F x y ≤ r := by
  exact iInf_le_of_le r (iInf_le_of_le h le_rfl)

theorem developmentChainEDist_comm (F : Set (OpenPartialHomeomorph E H2)) (x y : E) :
    developmentChainEDist F x y = developmentChainEDist F y x := by
  apply le_antisymm
  · apply le_iInf; intro r
    apply le_iInf; intro h
    exact iInf_le_of_le r (iInf_le_of_le (developmentChain_reverse h) le_rfl)
  · apply le_iInf; intro r
    apply le_iInf; intro h
    exact iInf_le_of_le r (iInf_le_of_le (developmentChain_reverse h) le_rfl)

theorem developmentChainEDist_triangle (F : Set (OpenPartialHomeomorph E H2)) (x y z : E) :
    developmentChainEDist F x z ≤ developmentChainEDist F x y + developmentChainEDist F y z := by
  unfold developmentChainEDist
  rw [ENNReal.iInf_add]
  apply le_iInf; intro r
  rw [ENNReal.iInf_add]
  apply le_iInf; intro h
  rw [ENNReal.add_iInf]
  apply le_iInf; intro s
  rw [ENNReal.add_iInf]
  apply le_iInf; intro k
  exact iInf_le_of_le (r + s) (iInf_le_of_le (developmentChain_append h k) le_rfl)

theorem developmentChainEDist_base_lower_bound {B : Type} [PseudoEMetricSpace B] (b : E → B)
    (F : Set (OpenPartialHomeomorph E H2))
    (hb : ∀ e ∈ F, ∀ x ∈ e.source, ∀ y ∈ e.source,
      edist (b x) (b y) ≤ edist (e x) (e y)) (x y : E) :
    edist (b x) (b y) ≤ developmentChainEDist F x y := by
  apply le_iInf; intro r
  apply le_iInf; intro h
  induction h with
  | nil x => simp
  | @cons x y z t e he hx hy tail ih =>
    exact (edist_triangle (b x) (b y) (b z)).trans (add_le_add (hb e he x hx y hy) ih)

end CurveComplex.Hyperbolic
