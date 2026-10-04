import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Intersection.FiniteCount
import CurveComplexGenusTwo.Foundations.FoundationsIntersectionPort

import CurveComplexGenusTwo.Topology.ActualGoodFiniteFaceCorrespondence.ActualNonloopMinimumProjectionAdapter
import CurveComplexGenusTwo.Topology.ActualJointGeodesicMinimum.JointEquivariantMinimum

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CurveComplex.HyperellipticModel
variable {S B : Type} [TopologicalSpace S] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  (M : HyperellipticModel S B)

/-- Source Theorem 5.5: an upstairs class minimum is attained by the literal
full preimages of a pair of downstairs representatives of the two named classes.
This states the same-class projection and minimum bridge without selecting an
arbitrary supplied family or treating its count as the class minimum. -/
theorem actual_nonloop_pair_minimum_full_preimages
    (a b : NonLoopArcClass M) (hab : a ≠ b) :
    ∃ p q : NonLoopArc M,
      Quotient.mk (nonLoopArcSetoid M) p = a ∧
      Quotient.mk (nonLoopArcSetoid M) q = b ∧
      Transverse (nonloop_arc_essential_preimage M p).val
        (nonloop_arc_essential_preimage M q).val ∧
      ((nonloop_arc_essential_preimage M p).val.image ∩
        (nonloop_arc_essential_preimage M q).val.image).ncard =
          geometricIntersection (nonloop_arc_vertex_map M a)
            (nonloop_arc_vertex_map M b) := by
  classical
  by_cases hdisjoint : ∃ p q : NonLoopArc M,
      Quotient.mk (nonLoopArcSetoid M) p = a ∧
      Quotient.mk (nonLoopArcSetoid M) q = b ∧ Disjoint p.image q.image
  · obtain ⟨p, q, hp, hq, hd⟩ := hdisjoint
    obtain ⟨ht, hcount⟩ :=
      MinimumProjectionInternal.minimum_of_disjoint_images M a b p q hp hq hd
    exact ⟨p, q, hp, hq, ht, hcount⟩
  obtain ⟨c₀, d₀, hc₀, hd₀, ht₀, hcount₀⟩ :=
    MinimumProjectionInternal.ordinary_minimum_pair M a b hab
  have hdeckc₀ := MinimumProjectionInternal.deck_fixes_named_class_relation M a c₀ hc₀
  have hdeckd₀ := MinimumProjectionInternal.deck_fixes_named_class_relation M b d₀ hd₀
  -- Exact remaining geometry: replace this actual minimizing pair jointly by
  -- invariant representatives while retaining its actual finite count.
  -- Independent invariantization of each curve does not retain this count.
  have hinvariant : ∃ c d : EssentialCurve S,
      Quotient.mk (essentialCurveSetoid S) c = Quotient.mk (essentialCurveSetoid S) c₀ ∧
      Quotient.mk (essentialCurveSetoid S) d = Quotient.mk (essentialCurveSetoid S) d₀ ∧
      M.cover.deck '' c.val.image = c.val.image ∧
      M.cover.deck '' d.val.image = d.val.image ∧
      Transverse c.val d.val ∧
      (c.val.image ∩ d.val.image).ncard = (c₀.val.image ∩ d₀.val.image).ncard := by
    let τ : S ≃ₜ S := M.cover.deck
    have hclasses : Quotient.mk (essentialCurveSetoid S) c₀ ≠
        Quotient.mk (essentialCurveSetoid S) d₀ := by
      rw [hc₀, hd₀]
      exact fun h => hab (MinimumProjectionInternal.vertex_map_injective_release M h)
    have hminimum : (c₀.val.image ∩ d₀.val.image).ncard =
        geometricIntersection (Quotient.mk (essentialCurveSetoid S) c₀)
          (Quotient.mk (essentialCurveSetoid S) d₀) := by
      simpa only [hc₀, hd₀] using hcount₀
    obtain ⟨atlas, hgenus, H, hdeck, _⟩ :=
      CurveComplex.Hyperbolic.actual_induced_closed_hyperbolic_metric M
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) S := atlas
    exact CurveComplex.Hyperbolic.JointMinimum.fixed_classes_have_joint_invariant_minimum_pair
      H hgenus τ hdeck c₀ d₀ hclasses ht₀ hminimum hdeckc₀ hdeckd₀
  obtain ⟨c, d, hc, hd, hcinv, hdinv, ht, hcount⟩ := hinvariant
  exact MinimumProjectionInternal.minimum_of_invariant_pair M a b c d
    (hc.trans hc₀) (hd.trans hd₀) hcinv hdinv ht (hcount.trans hcount₀)


end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.actual_nonloop_pair_minimum_full_preimages
