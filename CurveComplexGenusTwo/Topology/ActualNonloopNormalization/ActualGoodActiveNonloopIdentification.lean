import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Foundations.SourceNonseparating
import CurveComplexGenusTwo.Foundations.SingularComparison
import CurveComplexGenusTwo.Filtration.ActualFiltrationEndpointProgress

/-!
Source: curve-complex-genus-two.pdf, Corollary 5.7, Proposition 6.1,
and Lemma 8.5(iii). This file isolates the finite-face conjunct of
Main12CanonicalBCDNonloopDescentConsumerV11.lean, lines 209--211.

The complexes, quotient classes, endpoint labels and full-preimage map below
are the existing canonical definitions. All new theorem proofs are `sorry`.
The `eArc` equation retains the literal class identification; a bare arbitrary
equivalence between the two vertex types does not retain that identification.
-/

namespace CurveComplexGenusTwo.SourceTopology

open CurveComplex CurveComplex.HyperellipticModel CurveGenusTwo.Filtration

variable {S B : Type} [TopologicalSpace S] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  (M : HyperellipticModel S B)

noncomputable local instance : DecidableEq {a : Vertex S // nonseparatingVertex a} :=
  Classical.decEq _

variable [LinearOrder (EssentialArcClass M)]

/-- The canonical identification used by Main12 must retain the fact that
forgetting non-loopness recovers the literal active essential-arc class.
The existing Main12 construction supplies the equivalence; retaining this
equation is a separate bookkeeping obligation, not the face geometry. -/
theorem actual_good_active_nonloop_identification_exists :
    ∃ eArc :
      ActiveVertex (goodSubcomplex (actualA M) (actualArcLabels M)) ≃
        NonLoopArcClass M,
      ∀ a, nonloopToEssentialClass M (eArc a) = a.val := by
  classical
  let : DecidableEq (EssentialArcClass M) := LinearOrder.toDecidableEq
  let : DecidableEq B := Classical.decEq B
  have hsingleton (v : HyperellipticModel.EssentialArcClass M) : ({v} : Finset _) ∈ HyperellipticModel.actualA M := by
    induction v using Quotient.inductionOn with
    | h a =>
      refine ⟨fun _ => a, ?_, ?_⟩
      · intro w
        exact (Finset.mem_singleton.mp w.property).symm
      · intro w z hne
        exact False.elim (hne (Subtype.ext ((Finset.mem_singleton.mp w.property).trans
          (Finset.mem_singleton.mp z.property).symm)))
  have hactive (v : HyperellipticModel.EssentialArcClass M) :
      ({v} : Finset _) ∈ CurveGenusTwo.Filtration.goodSubcomplex (HyperellipticModel.actualA M) (HyperellipticModel.actualArcLabels M) ↔
      ¬ (HyperellipticModel.actualArcLabels M).isLoop v := by
    change (({v} : Finset _) ∈ HyperellipticModel.actualA M ∧
      (CurveGenusTwo.Filtration.badVertices (HyperellipticModel.actualArcLabels M) {v}).card ≤ (0 : ℤ)) ↔ _
    simp only [hsingleton, true_and]
    have hb : CurveGenusTwo.Filtration.badVertices (HyperellipticModel.actualArcLabels M) {v} =
        if (HyperellipticModel.actualArcLabels M).isLoop v then {v} else ∅ := by
      ext w
      by_cases he : w = v
      · subst w
        split_ifs with hl <;> simp [CurveGenusTwo.Filtration.badVertices, hl]
      · split_ifs <;> simp [CurveGenusTwo.Filtration.badVertices, he]
    rw [hb]
    split_ifs with h <;> simp [h]
  have hrange : ∀ v : HyperellipticModel.EssentialArcClass M,
      (∃ a : HyperellipticModel.NonLoopArcClass M, HyperellipticModel.nonloopToEssentialClass M a = v) ↔
        ¬ (HyperellipticModel.actualArcLabels M).isLoop v := by
    intro v
    induction v using Quotient.inductionOn with
    | h a =>
      constructor
      · rintro ⟨b, hb⟩
        induction b using Quotient.inductionOn with
        | h b =>
          rw [← hb]
          change ¬ (HyperellipticModel.arcEndpoints M b.toEssential).card = 1
          change ¬ ({b.val.map ⟨0, by norm_num⟩, b.val.map ⟨1, by norm_num⟩} : Finset B).card = 1
          rw [Finset.card_pair b.property]
          norm_num
      · intro h
        have hn : a.val.map ⟨0, by norm_num⟩ ≠ a.val.map ⟨1, by norm_num⟩ := by
          intro he
          apply h
          change (HyperellipticModel.arcEndpoints M a).card = 1
          change ({a.val.map ⟨0, by norm_num⟩, a.val.map ⟨1, by norm_num⟩} : Finset B).card = 1
          rw [he]
          rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
          exact Finset.card_singleton _
        exact ⟨Quotient.mk (HyperellipticModel.nonLoopArcSetoid M) ⟨a.val, hn⟩, rfl⟩
  let f : HyperellipticModel.NonLoopArcClass M → CurveGenusTwo.Filtration.ActiveVertex (CurveGenusTwo.Filtration.goodSubcomplex (HyperellipticModel.actualA M) (HyperellipticModel.actualArcLabels M)) :=
    fun a => ⟨HyperellipticModel.nonloopToEssentialClass M a, (hactive _).mpr ((hrange _).mp ⟨a,rfl⟩)⟩
  have hi : Function.Injective f := by
    intro a b h
    exact HyperellipticModel.nonloopToEssentialClass_injective M (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨a, ha⟩ := (hrange v.val).mpr ((hactive v.val).mp v.property)
    exact ⟨a, Subtype.ext ha⟩
  let e := Equiv.ofBijective f ⟨hi, hs⟩
  refine ⟨e.symm, ?_⟩
  intro a
  exact congrArg Subtype.val (e.apply_symm_apply a)

end CurveComplexGenusTwo.SourceTopology

#print axioms CurveComplexGenusTwo.SourceTopology.actual_good_active_nonloop_identification_exists
