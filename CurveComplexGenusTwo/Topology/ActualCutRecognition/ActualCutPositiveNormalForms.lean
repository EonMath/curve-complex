import ClassificationOfSurfaces.LeanEval.ChallengeDeps
import CurveComplexGenusTwo.Topology.ActualBoundaryModels.Definitions
import CurveComplexGenusTwo.Topology.ActualCutRecognition.ActualCompactCutClassification
import CurveComplexGenusTwo.Topology.ActualBoundaryModels.PuncturedProductTorus
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage

namespace CurveComplex.Hyperbolic
open Set Topology CategoryTheory
open LeanEval.Topology.ClassificationOfSurfaces
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Classification step in source Lemmas 6.4 and 6.6. Construct the compact
one-boundary models of BOTH literal cut sides and exclude the disc branch
using essentiality of the original c. This precedes rank-two recognition and
must not use rank-two side homology as a premise or a derived theorem. -/
theorem actual_essential_cut_positive_orientable_normal_forms
    (M : HyperellipticModel E S) (c : Curve E) (hc : Essential c)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V)
    (hUconn : IsConnected U) (hVconn : IsConnected V)
    (hUV : Disjoint U V) (hcover : U ∪ V = c.imageᶜ)
    (hfrontU : frontier U = c.image) (hfrontV : frontier V = c.image) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
      Nonempty (U ≃ₜ ActualOneBoundaryOrientableOpenModel p) ∧
      Nonempty (V ≃ₜ ActualOneBoundaryOrientableOpenModel q) := by
  classical
  have hside : ∀ (U V : Set E), IsOpen U → IsOpen V →
      IsConnected U → IsConnected V → Disjoint U V →
      U ∪ V = c.imageᶜ → frontier U = c.image → frontier V = c.image →
      ∃ p : ℕ, 0 < p ∧ Nonempty (U ≃ₜ ActualOneBoundaryOrientableOpenModel p) := by
    intro U V hU hV hUconn hVconn hUV hcover hfrontU hfrontV
    let K := closure U
    have hK : K = U ∪ c.image :=
      (closure_eq_self_union_frontier U).trans (by rw [hfrontU])
    have hUsub : U ⊆ c.imageᶜ := by
      intro z hz
      rw [← hcover]
      exact Or.inl hz
    obtain ⟨p, e, hboundary⟩ :=
      actual_compact_cut_boundary_preserving_orientable_polygon M c hc U V
        hU hV hUconn hVconn hUV hcover hfrontU hfrontV
    have hp : 0 < p := by
      by_contra hn
      have hpzero : p = 0 := by omega
      subst p
      obtain ⟨d, hd⟩ := actual_zero_handle_one_boundary_model_closed_disc
      let f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, E) :=
        ⟨fun x => (e.symm (d x)).val,
          continuous_subtype_val.comp (e.symm.continuous.comp d.continuous)⟩
      apply hc
      refine ⟨f, Topology.IsEmbedding.subtypeVal.comp
        (e.symm.isEmbedding.comp d.isEmbedding), ?_⟩
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        apply (hboundary (e.symm (d x))).mp
        simpa only [e.apply_symm_apply] using (hd x).mpr hx
      · intro hz
        have hzK : z ∈ closure U := by
          change z ∈ K
          rw [hK]
          exact Or.inr hz
        let x := d.symm (e ⟨z, hzK⟩)
        have hdx : d x = e ⟨z, hzK⟩ := d.apply_symm_apply _
        refine ⟨x, ?_, ?_⟩
        · apply (hd x).mp
          rw [hdx]
          exact (hboundary ⟨z, hzK⟩).mpr hz
        · change (e.symm (d x)).val = z
          rw [hdx, e.symm_apply_apply]
    let eInside : U ≃ₜ {x : K // x.val ∉ c.image} := {
      toFun := fun x => ⟨⟨x.val, subset_closure x.property⟩, hUsub x.property⟩
      invFun := fun x => ⟨x.val.val,
        ((show K ⊆ U ∪ c.image by rw [hK]) x.val.property).resolve_right x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    exact ⟨p, hp, ⟨eInside.trans
      (e.subtype (fun x => (not_congr (hboundary x)).symm))⟩⟩
  obtain ⟨p, hp, ep⟩ := hside U V hU hV hUconn hVconn hUV hcover hfrontU hfrontV
  obtain ⟨q, hq, eq⟩ := hside V U hV hU hVconn hUconn hUV.symm
    (by rw [union_comm]; exact hcover) hfrontV hfrontU
  exact ⟨p, q, hp, hq, ep, eq⟩


end CurveComplex.Hyperbolic
