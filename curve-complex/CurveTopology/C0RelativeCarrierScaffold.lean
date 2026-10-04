import CurveComplexGenusTwo.Foundations.FullSubcomplex
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import Mathlib.Topology.Homotopy.Contractible

open CurveComplex Set Topology
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P
noncomputable local instance (A : Type*) : DecidableEq A := Classical.decEq A
set_option autoImplicit false

namespace C0RelativeCarrier

/-- Vertices of barycentric subdivision are the actual nonempty source faces. -/
abbrev Face {V : Type*} (D : AbstractSimplicialComplex V) :=
  {σ : Finset V // σ ∈ D.faces}

/-- A barycentric simplex is a nonempty finite inclusion chain of actual faces. -/
def flagFaces {V : Type*} (D : AbstractSimplicialComplex V) : Set (Finset (Face D)) :=
  {Γ | Γ.Nonempty ∧ ∀ σ ∈ Γ, ∀ τ ∈ Γ, σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val}

/-- Structural proof obligation for the explicit flag complex, separated from its data. -/
theorem flagFaces_complex_axioms {V : Type*} (D : AbstractSimplicialComplex V) :
    IsRelLowerSet (flagFaces D) Finset.Nonempty ∧
      ∀ σ : Face D, {σ} ∈ flagFaces D := by
  constructor
  · intro Γ hΓ
    refine ⟨hΓ.1, ?_⟩
    intro Δ hΔΓ hΔ
    refine ⟨hΔ, ?_⟩
    intro σ hσ τ hτ
    exact hΓ.2 σ (hΔΓ hσ) τ (hΔΓ hτ)
  · intro σ
    refine ⟨Finset.singleton_nonempty σ, ?_⟩
    intro τ hτ υ hυ
    have hτeq : τ = σ := Finset.mem_singleton.mp hτ
    have hυeq : υ = σ := Finset.mem_singleton.mp hυ
    subst τ
    subst υ
    exact Or.inl (Finset.Subset.refl σ.val)

/-- The explicit barycentric order complex; no assumed or opaque subdivision object. -/
noncomputable def barycentricSubdivision {V : Type*} (D : AbstractSimplicialComplex V) :
    AbstractSimplicialComplex (Face D) where
  faces := flagFaces D
  isRelLowerSet_faces := (flagFaces_complex_axioms D).1
  singleton_mem := (flagFaces_complex_axioms D).2

/-- The subdivision of a genuine subcomplex L is the full flag complex on its faces.
L may omit singleton vertices of the disk interior. -/
noncomputable abbrev boundarySubdivision {V : Type*} (D : AbstractSimplicialComplex V)
    (L : PreAbstractSimplicialComplex V) :=
  fullSubcomplex (barycentricSubdivision D) (fun σ : Face D => σ.val ∈ L.faces)

/-- Every closed flag simplex is carried by the full carrier of its least face. -/
def FlagwiseSupported {V W : Type*} (D : AbstractSimplicialComplex V)
    (C : AbstractSimplicialComplex W) (P : Face D → W → Prop)
    (f : C(RealizationPoint (barycentricSubdivision D), RealizationPoint C)) : Prop :=
  ∀ (Γ : Finset (Face D)) (hΓ : Γ ∈ (barycentricSubdivision D).faces),
    ∀ σ₀ ∈ Γ, (∀ τ ∈ Γ, σ₀.val ⊆ τ.val) →
      ∀ x : FiniteSimplex Γ,
        f (faceInclusion (barycentricSubdivision D) Γ hΓ x) ∈ fullSupportLocus C (P σ₀)

end C0RelativeCarrier
