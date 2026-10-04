import CurveComplexGenusTwo.Topology.LinkWeakTopology
import CurveComplexGenusTwo.Foundations.VertexEquiv

namespace CurveComplexGenusTwo.Topology

open CurveComplex Set

/-- Adjacency in the simplicial join of two filled Farey complexes. Vertices
on opposite sides are always adjacent. -/
def FareyJoinAdjacent :
    Sum FareySlope FareySlope → Sum FareySlope FareySlope → Prop
  | .inl p, .inl q => FareyAdjacent p q
  | .inr p, .inr q => FareyAdjacent p q
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True

def FareyJoinFace (σ : Finset (Sum FareySlope FareySlope)) : Prop :=
  (σ : Set (Sum FareySlope FareySlope)).Pairwise FareyJoinAdjacent

/-- The filled Farey complex on slopes, including every nonempty flag face. -/
noncomputable def fareyFlagComplex : AbstractSimplicialComplex FareySlope where
  faces := {σ | σ.Nonempty ∧ FareyFace σ}
  isRelLowerSet_faces := by
    intro σ hσ
    constructor
    · exact hσ.1
    · intro τ hsub hne
      exact ⟨hne, hσ.2.mono hsub⟩
  singleton_mem := by
    intro s
    constructor
    · exact Finset.singleton_nonempty s
    · intro x hx y hy hxy
      have hxs : x = s := by simpa using hx
      have hys : y = s := by simpa using hy
      exact False.elim (hxy (hxs.trans hys.symm))

theorem mem_fareyFlagComplex_iff (σ : Finset FareySlope) :
    σ ∈ fareyFlagComplex.faces ↔ σ.Nonempty ∧ FareyFace σ := Iff.rfl

/-- The filled Farey join as a genuine abstract simplicial complex with the
same nonempty-face convention as Mathlib's `AbstractSimplicialComplex`. -/
noncomputable def fareyJoinComplex :
    AbstractSimplicialComplex (Sum FareySlope FareySlope) where
  faces := {σ | σ.Nonempty ∧ FareyJoinFace σ}
  isRelLowerSet_faces := by
    intro σ hσ
    constructor
    · exact hσ.1
    · intro τ hsub hne
      exact ⟨hne, hσ.2.mono hsub⟩
  singleton_mem := by
    intro s
    constructor
    · exact Finset.singleton_nonempty s
    · intro x hx y hy hxy
      have hxs : x = s := by simpa using hx
      have hys : y = s := by simpa using hy
      exact False.elim (hxy (hxs.trans hys.symm))

theorem mem_fareyJoinComplex_iff
    (σ : Finset (Sum FareySlope FareySlope)) :
    σ ∈ fareyJoinComplex.faces ↔ σ.Nonempty ∧ FareyJoinFace σ := Iff.rfl

theorem fareyJoinFace_mono
    {σ τ : Finset (Sum FareySlope FareySlope)}
    (hsub : τ ⊆ σ) (hσ : FareyJoinFace σ) :
    FareyJoinFace τ := hσ.mono hsub

theorem fareyJoinFace_image_union_iff
    (σ₁ σ₂ : Finset FareySlope) :
    FareyJoinFace (σ₁.image Sum.inl ∪ σ₂.image Sum.inr) ↔
      FareyFace σ₁ ∧ FareyFace σ₂ := by
  constructor
  · intro h
    constructor
    · intro p hp q hq hpq
      have hp' : Sum.inl p ∈ σ₁.image Sum.inl ∪ σ₂.image Sum.inr :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      have hq' : Sum.inl q ∈ σ₁.image Sum.inl ∪ σ₂.image Sum.inr :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      exact h hp' hq' (by simpa using hpq)
    · intro p hp q hq hpq
      have hp' : Sum.inr p ∈ σ₁.image Sum.inl ∪ σ₂.image Sum.inr :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      have hq' : Sum.inr q ∈ σ₁.image Sum.inl ∪ σ₂.image Sum.inr :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      exact h hp' hq' (by simpa using hpq)
  · rintro ⟨h₁, h₂⟩ x hx y hy hxy
    change x ∈ (σ₁.image Sum.inl ∪ σ₂.image Sum.inr) at hx
    change y ∈ (σ₁.image Sum.inl ∪ σ₂.image Sum.inr) at hy
    simp only [Finset.mem_union, Finset.mem_image] at hx hy
    rcases hx with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
    · rcases hy with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact h₁ hp hq (by simpa using hxy)
      · trivial
    · rcases hy with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · trivial
      · exact h₂ hp hq (by simpa using hxy)

/-- The slopes on the first side of a finite join face. -/
def fareyJoinLeft (σ : Finset (Sum FareySlope FareySlope)) :
    Finset FareySlope :=
  σ.biUnion (fun s => match s with
    | .inl p => {p}
    | .inr _ => ∅)

/-- The slopes on the second side of a finite join face. -/
def fareyJoinRight (σ : Finset (Sum FareySlope FareySlope)) :
    Finset FareySlope :=
  σ.biUnion (fun s => match s with
    | .inl _ => ∅
    | .inr p => {p})

@[simp] theorem mem_fareyJoinLeft_iff
    (σ : Finset (Sum FareySlope FareySlope)) (p : FareySlope) :
    p ∈ fareyJoinLeft σ ↔ Sum.inl p ∈ σ := by
  simp [fareyJoinLeft, Finset.mem_biUnion]

@[simp] theorem mem_fareyJoinRight_iff
    (σ : Finset (Sum FareySlope FareySlope)) (p : FareySlope) :
    p ∈ fareyJoinRight σ ↔ Sum.inr p ∈ σ := by
  simp [fareyJoinRight, Finset.mem_biUnion]

theorem fareyJoin_parts (σ : Finset (Sum FareySlope FareySlope)) :
    (fareyJoinLeft σ).image Sum.inl ∪
      (fareyJoinRight σ).image Sum.inr = σ := by
  ext s
  cases s with
  | inl p => simp
  | inr p => simp

theorem fareyJoinFace_iff_parts
    (σ : Finset (Sum FareySlope FareySlope)) :
    FareyJoinFace σ ↔
      FareyFace (fareyJoinLeft σ) ∧ FareyFace (fareyJoinRight σ) := by
  conv_lhs => rw [← fareyJoin_parts σ]
  exact fareyJoinFace_image_union_iff _ _

variable {V : Type*} [DecidableEq V]

theorem singleton_linkFace_of_linkFace
    (intersect : V → V → ℕ) (v w : V)
    (σ : Finset V) (hσ : LinkFace intersect v σ)
    (hw : w ∈ σ) : LinkFace intersect v {w} := by
  constructor
  · simpa using (by
      intro he
      exact hσ.1 (he ▸ hw) : v ≠ w)
  · apply hσ.2.mono
    intro u hu
    simp at hu
    rcases hu with huv | huw
    · subst u
      exact Finset.mem_insert_self _ _
    · subst u
      exact Finset.mem_insert_of_mem hw

/-- Exact geometric data required by source Lemma 6.6. The two slope copies
represent curves in the two one-holed tori; `face_iff` is the substantive
intersection/classification theorem, not a topological identification. -/
structure FareyJoinLinkDictionary
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) where
  vertex : Sum FareySlope FareySlope → V
  vertex_link : ∀ s, LinkFace intersect v {vertex s}
  vertex_injective : Function.Injective vertex
  vertex_surjective : ∀ w, LinkFace intersect v {w} →
    ∃ s, vertex s = w
  face_iff : ∀ σ : Finset (Sum FareySlope FareySlope),
    LinkFace intersect v (σ.image vertex) ↔ FareyJoinFace σ

/-- The geometric slope classification gives a bijection onto precisely the
vertices of the separating link. -/
noncomputable def FareyJoinLinkDictionary.linkVertexEquiv
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v) :
    Sum FareySlope FareySlope ≃
      {w : V // LinkFace intersect v {w}} where
  toFun s := ⟨d.vertex s, d.vertex_link s⟩
  invFun w := Classical.choose (d.vertex_surjective w.1 w.2)
  left_inv := by
    intro s
    apply d.vertex_injective
    exact (Classical.choose_spec
      (d.vertex_surjective (d.vertex s) (d.vertex_link s)))
  right_inv := by
    intro w
    apply Subtype.ext
    exact (Classical.choose_spec (d.vertex_surjective w.1 w.2))

@[simp] theorem FareyJoinLinkDictionary.linkVertexEquiv_val
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v)
    (s : Sum FareySlope FareySlope) :
    (d.linkVertexEquiv K intersect v s).val = d.vertex s := rfl

/-- The abstract link complex on the actual link vertices. Its weak
realization will be compared with the subspace realization separately. -/
noncomputable def linkVertexComplex
    (intersect : V → V → ℕ) (v : V) :
    AbstractSimplicialComplex {w : V // LinkFace intersect v {w}} := by
  classical
  refine {
    faces := {σ | σ.Nonempty ∧
      LinkFace intersect v (σ.image Subtype.val)}
    isRelLowerSet_faces := ?_
    singleton_mem := ?_ }
  · intro σ hσ
    constructor
    · exact hσ.1
    · intro τ hτ hne
      refine ⟨hne, ?_⟩
      constructor
      · intro hv
        exact hσ.2.1 ((Finset.image_mono Subtype.val hτ) hv)
      · apply hσ.2.2.mono
        exact Finset.insert_subset_insert _
          (Finset.image_mono Subtype.val hτ)
  · intro w
    simpa using w.2

theorem mem_linkVertexComplex_iff
    (intersect : V → V → ℕ) (v : V)
    (σ : Finset {w : V // LinkFace intersect v {w}}) :
    σ ∈ (linkVertexComplex intersect v).faces ↔
      σ.Nonempty ∧ LinkFace intersect v (σ.image Subtype.val) := Iff.rfl

theorem linkFace_of_face_of_linkVertices
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (σ : Finset V) (hσ : σ ∈ K.faces)
    (hvertices : ∀ w ∈ σ, LinkFace intersect v {w}) :
    LinkFace intersect v σ := by
  have hvnot : v ∉ σ := by
    intro hv
    exact (hvertices v hv).1 (Finset.mem_singleton_self v)
  refine ⟨hvnot, ?_⟩
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with rfl | ha'
  · rcases Finset.mem_insert.mp hb with rfl | hb'
    · exact False.elim (hab rfl)
    · have h := (hvertices b hb').2
      exact h (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (by intro heq; exact (hvertices b hb').1 (by simp [heq]))
  · rcases Finset.mem_insert.mp hb with rfl | hb'
    · have h := (hvertices a ha').2
      exact h (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        (Finset.mem_insert_self _ _) hab
    · exact hcurve σ hσ ha' hb' hab

theorem linkFace_iff_face_on_linkVertices
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V)
    (hcurve : ∀ σ : Finset V, σ ∈ K.faces → CurveFace intersect 1 σ)
    (hfull : ∀ σ : Finset V, σ.Nonempty →
      CurveFace intersect 1 σ → σ ∈ K.faces)
    (σ : Finset {w : V // LinkFace intersect v {w}})
    (hne : σ.Nonempty) :
    LinkFace intersect v (σ.image Subtype.val) ↔
      σ.image Subtype.val ∈ K.faces := by
  constructor
  · intro hlink
    exact hfull _ (Finset.image_nonempty.mpr hne)
      (hlink.2.mono (Finset.subset_insert _ _))
  · intro hK
    apply linkFace_of_face_of_linkVertices K intersect v hcurve _ hK
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨w', _, rfl⟩
    exact w'.2


theorem FareyJoinLinkDictionary.face_iff_linkVertexEquiv
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v)
    (σ : Finset (Sum FareySlope FareySlope)) :
    FareyJoinFace σ ↔
      LinkFace intersect v
        ((σ.image (d.linkVertexEquiv K intersect v)).image Subtype.val) := by
  simpa [Finset.image_image, Function.comp_def] using (d.face_iff σ).symm

/-- The geometric slope dictionary induces an actual homeomorphism of weak
realizations. No topological comparison with a product join is assumed. -/
noncomputable def FareyJoinLinkDictionary.realizationHomeomorph
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v) :
    RealizationPoint fareyJoinComplex ≃ₜ
      RealizationPoint (linkVertexComplex intersect v) := by
  classical
  apply CurveComplex.realizationHomeomorphOfVertexEquiv
    fareyJoinComplex (linkVertexComplex intersect v)
    (d.linkVertexEquiv K intersect v)
  intro σ
  rw [mem_fareyJoinComplex_iff, mem_linkVertexComplex_iff]
  simp only [Finset.image_nonempty]
  exact and_congr_right (fun _ => d.face_iff_linkVertexEquiv K intersect v σ)

theorem FareyJoinLinkDictionary.linkFace_vertices
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v)
    (σ : Finset V) (hσ : LinkFace intersect v σ) :
    ∀ w ∈ σ, ∃ s, d.vertex s = w := by
  intro w hw
  exact d.vertex_surjective w
    (singleton_linkFace_of_linkFace intersect v w σ hσ hw)

/-- The dictionary is a simplicial isomorphism onto the nonempty link faces,
expressed without requiring an abstract complex to contain the empty face. -/
theorem FareyJoinLinkDictionary.face_iff_linkFace
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v)
    (σ : Finset (Sum FareySlope FareySlope)) :
    σ ∈ fareyJoinComplex.faces ↔
      σ.Nonempty ∧ LinkFace intersect v (σ.image d.vertex) := by
  rw [mem_fareyJoinComplex_iff]
  exact and_congr_right (fun _ => (d.face_iff σ).symm)

theorem FareyJoinLinkDictionary.face_iff_K_linkFace
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v)
    (hface : ∀ ρ : Finset V, ρ.Nonempty →
      CurveFace intersect 1 ρ → ρ ∈ K.faces)
    (σ : Finset (Sum FareySlope FareySlope)) :
    σ ∈ fareyJoinComplex.faces ↔
      σ.image d.vertex ∈ K.faces ∧
        LinkFace intersect v (σ.image d.vertex) := by
  rw [d.face_iff_linkFace]
  constructor
  · rintro ⟨hne, hlink⟩
    have hnon : (σ.image d.vertex).Nonempty := Finset.image_nonempty.mpr hne
    exact ⟨hface _ hnon
      (hlink.2.mono (Finset.subset_insert v (σ.image d.vertex))), hlink⟩
  · rintro ⟨hK, hlink⟩
    exact ⟨Finset.image_nonempty.mp (K.isRelLowerSet_faces hK).1, hlink⟩

theorem FareyJoinLinkDictionary.vertex_image_linkFace
    (K : AbstractSimplicialComplex V) (intersect : V → V → ℕ)
    (v : V) (d : FareyJoinLinkDictionary K intersect v)
    (σ : Finset (Sum FareySlope FareySlope))
    (hσ : σ ∈ fareyJoinComplex.faces) :
    LinkFace intersect v (σ.image d.vertex) :=
  ((FareyJoinLinkDictionary.face_iff_linkFace K intersect v d σ).mp hσ).2

end CurveComplexGenusTwo.Topology
