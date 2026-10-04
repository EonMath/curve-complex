import OriginalQBoundaryMotionExtension
import CurveComplexGenusTwo.Topology.ActualQTerminalSurgery
import CurveComplexGenusTwo.Foundations.FullSubcomplex
import CurveComplexGenusTwo.Foundations.ConeRealization
import CurveComplexGenusTwo.Topology.IsotopyCurveTransport

/-!
N3 of harer_schoenflies_blueprint/c0_contraction/PLAN.md.
Reuse the actual original Q/B, essential-arc, quotient and simultaneous-face
objects exported by ActualQTerminalSurgery. These are statement scaffolds only.
-/

open Set Topology CurveComplex
open scoped Manifold ContDiff
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P
noncomputable local instance (A : Type*) : DecidableEq A := Classical.decEq A
set_option autoImplicit false

namespace CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers

open OriginalBoundaryArc

variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

/-- One actual family for all distinct quotient vertices in the finite face.
The whole closed interval ranges, including endpoints, are pairwise disjoint. -/
structure SimultaneousRepresentatives (τ : Finset (ArcVertex S x R)) where
  arc : ↥τ → EssentialProperArc S x R
  class_eq : ∀ u : ↥τ, Quot.mk (arcRel S x R) (arc u) = u.val
  disjoint : ∀ u w : ↥τ, u ≠ w →
    Disjoint (Set.range (arc u).val.val) (Set.range (arc w).val.val)

/-- Literal avoidance by one original S-essential representative in interior Q.
This predicate contains no contracted finite curve complex or comparison callback. -/
def actualFamilyCarrier {J : Type*} (a : J → EssentialProperArc S x R)
    (v : Vertex S) : Prop :=
  ∃ d : EssentialCurve S, Quotient.mk (essentialCurveSetoid S) d = v ∧
    d.val.image ⊆ interior ((openDisk S x R)ᶜ) ∧
    ∀ i : J, Disjoint d.val.image (Set.range (fun t : Interval => (a i).val.val t |>.val))

/-- A face carrier uses ONE common simultaneous arc family and ONE essential
S-curve avoiding all its members. -/
def faceCarrier (τ : Finset (ArcVertex S x R)) (v : Vertex S) : Prop :=
  ∃ r : SimultaneousRepresentatives S x R τ,
    actualFamilyCarrier S x R r.arc v

/-- The literal S-image of a subset moved by a Q-isotopy through subtype inclusion. -/
def movedImage (H : AmbientIsotopy (Q S x R)) (C : Set S) : Set S :=
  Subtype.val '' (H.finalMap '' {q : Q S x R | q.val ∈ C})

/-- Definition bridge to the canonical source's simultaneous arc faces. -/
theorem simultaneousRepresentatives_face_iff (τ : Finset (ArcVertex S x R)) :
    τ ∈ (arcComplex S x R).faces ↔
      τ.Nonempty ∧ Nonempty (SimultaneousRepresentatives S x R τ) := by
  constructor
  · rintro ⟨hτ, rep, hclass, hdisjoint⟩
    exact ⟨hτ, ⟨⟨rep, hclass, hdisjoint⟩⟩⟩
  · rintro ⟨hτ, ⟨rep⟩⟩
    exact ⟨hτ, rep.arc, rep.class_eq, rep.disjoint⟩

/-- The source quotient is exactly the actual setwise-B ambient relation,
not only the generated closure of a potentially unevaluated relation. The source
C0 body's hMarkedAmbientRelationEquivalence/hActualArcRelEquivalence pay the
underlying reflexive/symmetric/transitive construction. -/
theorem arc_class_eq_iff_actual_relation (a b : EssentialProperArc S x R) :
    Quot.mk (arcRel S x R) a = Quot.mk (arcRel S x R) b ↔ arcRel S x R a b := by
  have relation_reflexive (a : EssentialProperArc S x R) : arcRel S x R a a := by
    let H : AmbientIsotopy (Q S x R) := {
      map := ⟨fun p => p.2, continuous_snd⟩
      homeomorphism_at := fun _ => ⟨Homeomorph.refl _, fun _ => rfl⟩
      at_zero := fun _ => rfl }
    refine ⟨H, ?_, ?_⟩
    · intro t
      exact Set.image_id _
    · exact Set.image_id _
  have relation_transitive (a b c : EssentialProperArc S x R)
      (hab : arcRel S x R a b) (hbc : arcRel S x R b c) : arcRel S x R a c := by
    obtain ⟨H, hH, hHab⟩ := hab
    obtain ⟨K, hK, hKbc⟩ := hbc
    let L : AmbientIsotopy (Q S x R) := {
      map := ⟨fun p => K.map (p.1, H.map p),
        K.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩
      homeomorphism_at := by
        intro t
        obtain ⟨h, hh⟩ := H.homeomorphism_at t
        obtain ⟨k, hk⟩ := K.homeomorphism_at t
        exact ⟨h.trans k, fun y => by
          change k (h y) = K.map (t, H.map (t, y))
          rw [hk, hh]⟩
      at_zero := by
        intro y
        change K.map (⟨0, by norm_num⟩, H.map (⟨0, by norm_num⟩, y)) = y
        rw [H.at_zero, K.at_zero] }
    refine ⟨L, ?_, ?_⟩
    · intro t
      change (fun y => K.map (t, H.map (t, y))) '' _ = _
      rw [← Set.image_image (fun y => K.map (t, y)) (fun y => H.map (t, y)), hH t, hK t]
    · change (fun y => K.finalMap (H.finalMap y)) '' _ = _
      rw [← Set.image_image, hHab, hKbc]
  have relation_symmetric (a b : EssentialProperArc S x R)
      (hab : arcRel S x R a b) : arcRel S x R b a := by
    obtain ⟨H, hH, hHab⟩ := hab
    obtain ⟨h, hh⟩ := H.homeomorphism_at ⟨1, by norm_num⟩
    let reverse : Interval → Interval := unitInterval.symmHomeomorph
    have hrev0 : reverse 0 = 1 := by apply Subtype.ext; norm_num [reverse]
    have hrev1 : reverse 1 = 0 := by apply Subtype.ext; norm_num [reverse]
    have hc : Continuous reverse := unitInterval.symmHomeomorph.continuous
    have hinv : h.symm '' boundaryQ S x R = boundaryQ S x R := by
      have hb : h '' boundaryQ S x R = boundaryQ S x R := by
        simpa only [hh] using hH ⟨1, by norm_num⟩
      calc
        h.symm '' boundaryQ S x R = h.symm '' (h '' boundaryQ S x R) :=
          congrArg (fun A => h.symm '' A) hb.symm
        _ = boundaryQ S x R := by simp [Set.image_image]
    let K : AmbientIsotopy (Q S x R) := {
      map := ⟨fun p => H.map (reverse p.1, h.symm p.2),
        H.map.continuous.comp ((hc.comp continuous_fst).prodMk
          (h.symm.continuous.comp continuous_snd))⟩
      homeomorphism_at := by
        intro t
        obtain ⟨k, hk⟩ := H.homeomorphism_at (reverse t)
        exact ⟨h.symm.trans k, fun y => by
          change k (h.symm y) = H.map (reverse t, h.symm y)
          exact hk _⟩
      at_zero := by
        intro y
        change H.map (reverse 0, h.symm y) = y
        rw [hrev0]
        change H.map (⟨1, by norm_num⟩, h.symm y) = y
        rw [← hh]
        exact h.apply_symm_apply y }
    refine ⟨K, ?_, ?_⟩
    · intro t
      change (fun y => H.map (reverse t, h.symm y)) '' _ = _
      rw [← Set.image_image (fun y => H.map (reverse t, y)) h.symm, hinv, hH (reverse t)]
    · have hk : K.finalMap = h.symm := by
        funext y
        change H.map (reverse 1, h.symm y) = h.symm y
        rw [hrev1]
        exact H.at_zero _
      rw [hk, ← hHab]
      have hf : H.finalMap = h := (funext hh).symm
      rw [hf]
      simp [Set.image_image]
  have hrel : Equivalence (arcRel S x R) :=
    ⟨relation_reflexive, fun {_ _} => relation_symmetric _ _,
      fun {_ _ _} => relation_transitive _ _ _⟩
  exact Quot.eq.trans hrel.eqvGen_iff

/-- Restriction of a common representative family gives the antitone direction
P_tau ⊆ P_sigma for sigma ⊆ tau. No alignment or geometry premise is needed. -/
theorem faceCarrier_antitone (σ τ : Finset (ArcVertex S x R)) (hστ : σ ⊆ τ) :
    ∀ v : Vertex S, faceCarrier S x R τ v → faceCarrier S x R σ v := by
  intro v hv
  rcases hv with ⟨r, hr⟩
  rcases hr with ⟨d, hdv, hdQ, hdisj⟩
  let rσ : SimultaneousRepresentatives S x R σ :=
    { arc := fun u => r.arc ⟨u.val, hστ u.property⟩
      class_eq := by
        intro u
        exact r.class_eq ⟨u.val, hστ u.property⟩
      disjoint := by
        intro u w huw
        apply r.disjoint ⟨u.val, hστ u.property⟩ ⟨w.val, hστ w.property⟩
        intro heq
        apply huw
        apply Subtype.ext
        exact congrArg (fun q : ↥τ => q.val) heq }
  refine ⟨rσ, d, hdv, hdQ, ?_⟩
  intro i
  exact hdisj ⟨i.val, hστ i.property⟩

/-- N3a consumer: obtain the original-S class using the separately owned
original_Q_boundary_motion_extends_over_chart_disk, then reuse the canonical
position_essential_curve_of_isotopy. The exact moved image is explicitly retained.
A Q-isotopy or free homotopy alone does not justify the S-class equality. -/
theorem original_Q_motion_transports_avoiding_curve
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (J : Type) [Fintype J] (a b : J → EssentialProperArc S x R)
    (H : AmbientIsotopy (Q S x R))
    (hB : ∀ t : Interval, (fun q => H.map (t, q)) '' boundaryQ S x R = boundaryQ S x R)
    (hfinal : ∀ i : J, H.finalMap '' Set.range (a i).val.val = Set.range (b i).val.val)
    (c : EssentialCurve S) (hcQ : c.val.image ⊆ interior ((openDisk S x R)ᶜ))
    (hca : ∀ i : J, Disjoint c.val.image
      (Set.range (fun t : Interval => ((a i).val.val t).val))) :
    ∃ d : EssentialCurve S,
      d.val.image = movedImage S x R H c.val.image ∧
      Quotient.mk (essentialCurveSetoid S) d = Quotient.mk (essentialCurveSetoid S) c ∧
      d.val.image ⊆ interior ((openDisk S x R)ᶜ) ∧
      ∀ i : J, Disjoint d.val.image
        (Set.range (fun t : Interval => ((b i).val.val t).val)) := by
  obtain ⟨E, _, hEQ, _, _, _, hEfinal, hEimage⟩ :=
    original_Q_boundary_motion_extends_over_chart_disk S g hg hS x R hR htarget H hB
  have hcExterior : c.val.image ⊆ (openDisk S x R)ᶜ := hcQ.trans interior_subset
  have hcSubtype : Subtype.val '' {q : Q S x R | q.val ∈ c.val.image} =
      c.val.image := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hy
      exact ⟨⟨y, hcExterior hy⟩, hy, rfl⟩
  have hMoved : E.finalMap '' c.val.image = movedImage S x R H c.val.image := by
    calc
      E.finalMap '' c.val.image =
          E.finalMap '' (Subtype.val '' {q : Q S x R | q.val ∈ c.val.image}) :=
        congrArg (Set.image E.finalMap) hcSubtype.symm
      _ = movedImage S x R H c.val.image := hEimage _
  obtain ⟨d, hdImage, hdClass⟩ := position_essential_curve_of_isotopy E c
  obtain ⟨e, he⟩ := E.homeomorphism_at ⟨1, by norm_num⟩
  have heFinal : (e : S → S) = E.finalMap := funext he
  have hInterior : E.finalMap '' interior ((openDisk S x R)ᶜ) =
      interior ((openDisk S x R)ᶜ) := by
    rw [← heFinal, e.image_interior, heFinal]
    exact congrArg interior (hEQ ⟨1, by norm_num⟩)
  refine ⟨d, hdImage.trans hMoved, hdClass, ?_, ?_⟩
  · rw [hdImage]
    exact (Set.image_mono hcQ).trans hInterior.subset
  · intro i
    have hArc : E.finalMap ''
        Set.range (fun t : Interval => ((a i).val.val t).val) =
        Set.range (fun t : Interval => ((b i).val.val t).val) := by
      have h := hEimage (Set.range (a i).val.val)
      rw [hfinal i] at h
      simpa only [← Set.range_comp, Function.comp_def] using h
    rw [hdImage, ← hArc]
    apply Set.disjoint_image_of_injective _ (hca i)
    rw [← heFinal]
    exact e.injective

end CurveComplexGenusTwo.SourceTopology.OriginalArcFaceCarriers
