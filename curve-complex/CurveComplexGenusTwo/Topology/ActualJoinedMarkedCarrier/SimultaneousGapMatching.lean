import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.VerifiedCarrierBridgeComponents
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000

theorem actual_marked_simultaneous_gap_matching
    (M : HyperellipticModel E S) [T2Space S]
    {J G : Type} [Fintype J] [Fintype G]
    (old : J → EssentialMarkedArc M) (b : EssentialMarkedArc M)
    (U : Set S) (V : Set (ℝ × ℝ)) (hV : IsOpen V) (e : U ≃ₜ V)
    (A l r B : G → ℝ)
    (hAl : ∀ g, A g < l g) (hlr : ∀ g, l g < r g) (hrB : ∀ g, r g < B g)
    (haxis : ∀ g x, x ∈ Icc (A g) (B g) → ∃ y : V, y.val=(x,0) ∧
      ∀ j, (e.symm y : S) ∉ (old j).val.image)
    (hbaxis : ∀ u : U, (u : S) ∈ b.val.image ↔ (e u : ℝ × ℝ).2=0)
    (L R : G → C(unitInterval,U))
    (hL : ∀ g, (e (L g 0) : ℝ × ℝ)=(l g,0))
    (hR : ∀ g, (e (R g 0) : ℝ × ℝ)=(r g,0))
    (hside : ∀ g (t : unitInterval), t≠0 →
      0 < (e (L g t) : ℝ × ℝ).2 ∧ 0 < (e (R g t) : ℝ × ℝ).2) :
    ∃ t : unitInterval, 0 < t.val ∧ t.val < 1 ∧
      ∀ g, ∃ f : Path (L g t : S) (R g t : S), IsEmbedding f ∧
        Disjoint (range f) b.val.image ∧
        (∀ j, Disjoint (range f) (old j).val.image) ∧
        ∀ s, ∃ u : U, (u : S)=f s ∧
          (e u : ℝ × ℝ)=(1-s.val) • (e (L g t) : ℝ × ℝ)+s.val • (e (R g t) : ℝ × ℝ) := by
  classical
  have hMatch (g : G) := actual_marked_contact_gap_matching M old b U V hV e
    (A g) (l g) (r g) (B g) (hAl g) (hlr g) (hrB g) (haxis g)
    hbaxis (L g) (R g) (hL g) (hR g) (hside g)
  choose ρ hρ hPaths using hMatch
  let O : Set ℝ := Iio 1 ∩ ⋂ g, Iio (ρ g)
  have hO : IsOpen O := isOpen_Iio.inter (isOpen_iInter_of_finite (fun _ => isOpen_Iio))
  have h0O : (0:ℝ) ∈ O := ⟨by change (0:ℝ)<1; norm_num,Set.mem_iInter.mpr hρ⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO 0 h0O
  have hμ : 0 < ε/2 := half_pos hε
  have hμO : ε/2 ∈ O := hball (by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hμ]
    linarith)
  let t : unitInterval := ⟨ε/2,hμ.le,hμO.1.le⟩
  refine ⟨t,hμ,hμO.1,?_⟩
  intro g
  exact hPaths g t hμ (Set.mem_iInter.mp hμO.2 g)
end CurveComplex.HyperellipticModel
