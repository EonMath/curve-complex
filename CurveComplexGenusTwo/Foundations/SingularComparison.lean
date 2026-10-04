import CurveComplexGenusTwo.Foundations.RealizationCW
import CurveComplexGenusTwo.Filtration.ConeChains

open CategoryTheory Topology
open scoped Simplicial

noncomputable section
namespace CurveComplex
variable {V : Type*} [LinearOrder V]

/-- Barycentric coordinates of a finite face in Mathlib's standard simplex. -/
def affineFinite (σ : Finset V) {n : ℕ} (h : σ.card = n + 1)
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) : FiniteSimplex σ := by
  let e : Fin (n + 1) ≃ σ := (σ.orderIsoOfFin h).toEquiv
  refine ⟨fun v => w.weights (e.symm v), ?_, ?_⟩
  · intro v
    exact w.weights_nonneg _
  · rw [← w.total]
    classical
    rw [w.weights.sum_fintype (fun _ r => r) (by simp)]
    symm
    apply Fintype.sum_equiv e
    intro i
    simp

/-- Continuous affine characteristic simplex in the actual weak realization. -/
def affineSingular {K : AbstractSimplicialComplex V}
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ} (h : σ.card = n + 1) :
    C(Convexity.StdSimplex ℝ (Fin (n + 1)), RealizationPoint K) :=
  ⟨fun w => faceInclusion K σ hσ (affineFinite σ h w), by
    apply continuous_faceInclusion K σ hσ |>.comp
    apply Continuous.subtype_mk
    apply continuous_pi
    intro v
    exact Convexity.StdSimplex.continuous_weights_apply (R := ℝ) _⟩

/-- The affine characteristic simplex as a simplex of the singular simplicial set. -/
def affineFaceSimplex (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ} (h : σ.card = n + 1) :
    (TopCat.toSSet.obj (TopCat.of (RealizationPoint K))).obj (Opposite.op ⦋n⦌) :=
  (TopCat.toSSetObjEquiv (TopCat.of (RealizationPoint K)) (Opposite.op ⦋n⦌)).symm
    (affineSingular σ hσ h)

theorem affineFaceSimplex_apply (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ} (h : σ.card = n + 1) :
    (TopCat.toSSetObjEquiv (TopCat.of (RealizationPoint K)) (Opposite.op ⦋n⦌))
      (affineFaceSimplex K σ hσ h) = affineSingular σ hσ h := by
  exact Equiv.apply_symm_apply _ _

theorem affineFaceSimplex_naturality (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n m : ℕ}
    (h : σ.card = m + 1) (f : ⦋n⦌ ⟶ ⦋m⦌) :
    (TopCat.toSSet.obj (TopCat.of (RealizationPoint K))).map f.op
      (affineFaceSimplex K σ hσ h) =
    (TopCat.toSSetObjEquiv (TopCat.of (RealizationPoint K)) (Opposite.op ⦋n⦌)).symm
      ((affineSingular σ hσ h).comp
        ⟨Convexity.StdSimplex.map (⇑f), by fun_prop⟩) := by
  change (TopCat.toSSet.obj (TopCat.of (RealizationPoint K))).map f.op
      ((TopCat.toSSetObjEquiv (TopCat.of (RealizationPoint K))
        (Opposite.op ⦋m⦌)).symm (affineSingular σ hσ h)) = _
  apply TopCat.toSSetObjEquiv_symm_naturality

theorem affineFaceSimplex_delta_apply (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (h : σ.card = n + 2) (i : Fin (n + 2))
    (w : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSetObjEquiv (TopCat.of (RealizationPoint K)) (Opposite.op ⦋n⦌))
      ((TopCat.toSSet.obj (TopCat.of (RealizationPoint K))).δ i
        (affineFaceSimplex K σ hσ h)) w =
      affineSingular σ hσ h (Convexity.StdSimplex.map i.succAbove w) := by
  rw [TopCat.toSSetObjEquiv_δ_apply]
  rw [affineFaceSimplex_apply]

/-- Deleting the `i`th ordered vertex reindexes the remaining ordered vertices
by `i.succAbove`. -/
theorem orderEmbOfFin_erase_succAbove (σ : Finset V) {n : ℕ}
    (hσ : σ.card = n + 2) (i : Fin (n + 2))
    (hErase : (σ.erase (σ.orderEmbOfFin hσ i)).card = n + 1) :
    ∀ j : Fin (n + 1),
      (σ.erase (σ.orderEmbOfFin hσ i)).orderEmbOfFin hErase j =
      σ.orderEmbOfFin hσ (i.succAbove j) := by
  intro j
  have hv : σ.orderEmbOfFin hσ i ∈ σ := σ.orderEmbOfFin_mem hσ i
  have hmem (k : Fin (n + 1)) :
      σ.orderEmbOfFin hσ (i.succAbove k) ∈
        σ.erase (σ.orderEmbOfFin hσ i) := by
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      have h := (σ.orderEmbOfFin hσ).injective heq
      exact (Fin.succAbove_ne i k) h
    · exact σ.orderEmbOfFin_mem hσ _
  have hmono : StrictMono (fun k : Fin (n + 1) =>
      σ.orderEmbOfFin hσ (i.succAbove k)) :=
    (σ.orderEmbOfFin hσ).strictMono.comp (Fin.strictMono_succAbove i)
  have heq := Finset.orderEmbOfFin_unique hErase hmem hmono
  exact congrFun heq.symm j

theorem card_filter_lt_orderEmbOfFin (σ : Finset V) {m : ℕ}
    (hσ : σ.card = m) (i : Fin m) :
    (σ.filter (· < σ.orderEmbOfFin hσ i)).card = i.val := by
  let e : Fin m ≃ σ := (σ.orderIsoOfFin hσ).toEquiv
  have heq : σ.filter (· < σ.orderEmbOfFin hσ i) =
      ((Finset.univ.filter (· < i)).image
        (fun j : Fin m => σ.orderEmbOfFin hσ j)) := by
    ext v
    constructor
    · intro hv
      have hmem : v ∈ σ := (Finset.mem_filter.mp hv).1
      let j := (σ.orderIsoOfFin hσ).symm ⟨v, hmem⟩
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · have hj : σ.orderEmbOfFin hσ j = v := by
          change ((σ.orderIsoOfFin hσ) j).1 = v
          simp [j]
        exact (σ.orderEmbOfFin hσ).lt_iff_lt.mp (by
          rw [hj]
          exact (Finset.mem_filter.mp hv).2)
      · simp [j, Finset.orderEmbOfFin]
    · intro hv
      obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp hv
      rw [← hval]
      exact Finset.mem_filter.mpr ⟨σ.orderEmbOfFin_mem hσ j,
        (σ.orderEmbOfFin hσ).strictMono (Finset.mem_filter.mp hj).2⟩
  rw [heq, Finset.card_image_of_injective _ (σ.orderEmbOfFin hσ).injective]
  simpa using (Fin.card_filter_val_lt (n := m) (m := i.val))

theorem affineSingular_weight_ordered {K : AbstractSimplicialComplex V}
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) (w : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) :
    (affineSingular σ hσ hcard w).weight (σ.orderEmbOfFin hcard j) =
      w.weights j := by
  have hj : σ.orderEmbOfFin hcard j ∈ σ := σ.orderEmbOfFin_mem hcard j
  rw [show affineSingular σ hσ hcard w =
      faceInclusion K σ hσ (affineFinite σ hcard w) from rfl,
    faceInclusion_weight_of_mem K σ hσ _ _ hj]
  change w.weights ((σ.orderIsoOfFin hcard).symm
    ⟨σ.orderEmbOfFin hcard j, hj⟩) = _
  have heq : (⟨σ.orderEmbOfFin hcard j, hj⟩ : σ) =
      σ.orderIsoOfFin hcard j := Subtype.ext rfl
  rw [heq, OrderIso.symm_apply_apply]

theorem affineSingular_weight_outside {K : AbstractSimplicialComplex V}
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 1) (w : Convexity.StdSimplex ℝ (Fin (n + 1)))
    (v : V) (hv : v ∉ σ) :
    (affineSingular σ hσ hcard w).weight v = 0 := by
  exact faceInclusion_weight_of_not_mem K σ hσ (affineFinite σ hcard w) v hv

theorem affineFaceSimplex_delta_eq_erase (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) {n : ℕ}
    (hcard : σ.card = n + 2) (i : Fin (n + 2))
    (hτ : σ.erase (σ.orderEmbOfFin hcard i) ∈ K.faces)
    (hτcard : (σ.erase (σ.orderEmbOfFin hcard i)).card = n + 1) :
    (TopCat.toSSet.obj (TopCat.of (RealizationPoint K))).δ i
      (affineFaceSimplex K σ hσ hcard) =
    affineFaceSimplex K (σ.erase (σ.orderEmbOfFin hcard i)) hτ hτcard := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (RealizationPoint K)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro w
  apply RealizationPoint.ext
  funext v
  rw [affineFaceSimplex_delta_apply, affineFaceSimplex_apply]
  let τ := σ.erase (σ.orderEmbOfFin hcard i)
  by_cases hvσ : v ∈ σ
  · by_cases hvi : v = σ.orderEmbOfFin hcard i
    · subst v
      have hnotτ : σ.orderEmbOfFin hcard i ∉ τ := by simp [τ]
      rw [affineSingular_weight_outside τ hτ hτcard w _ hnotτ]
      let wi := Convexity.StdSimplex.map i.succAbove w
      rw [affineSingular_weight_ordered σ hσ hcard wi i]
      change (Finsupp.mapDomain i.succAbove w.weights) i = 0
      apply Finsupp.mapDomain_of_notMem_range
      intro ⟨j, hj⟩
      exact Fin.succAbove_ne i j hj
    · have hvτ : v ∈ τ := Finset.mem_erase.mpr ⟨hvi, hvσ⟩
      let j := (τ.orderIsoOfFin hτcard).symm ⟨v, hvτ⟩
      have hvj : τ.orderEmbOfFin hτcard j = v := by
        change ((τ.orderIsoOfFin hτcard) j).1 = v
        simp [j]
      rw [← hvj, affineSingular_weight_ordered τ hτ hτcard w j]
      rw [orderEmbOfFin_erase_succAbove σ hcard i hτcard j,
        affineSingular_weight_ordered σ hσ hcard
        (Convexity.StdSimplex.map i.succAbove w) (i.succAbove j)]
      change (Finsupp.mapDomain i.succAbove w.weights) (i.succAbove j) = _
      rw [Finsupp.mapDomain_apply_of_injective (Fin.strictMono_succAbove i).injective]
  · have hvτ : v ∉ τ := fun h => hvσ (Finset.mem_of_mem_erase h)
    rw [affineSingular_weight_outside σ hσ hcard _ v hvσ,
      affineSingular_weight_outside τ hτ hτcard w v hvτ]

end CurveComplex

namespace CurveGenusTwo.Filtration

variable {V : Type*} [DecidableEq V] [LinearOrder V]

/-- Vertices present in a `FiniteComplex`; absent vertices do not create points
in its topological realization. -/
def ActiveVertex (K : FiniteComplex V) := {v : V // ({v} : Finset V) ∈ K}

instance activeVertexLinearOrder (K : FiniteComplex V) :
    LinearOrder (ActiveVertex K) := Subtype.instLinearOrder _

instance activeVertexDecidableEq (K : FiniteComplex V) :
    DecidableEq (ActiveVertex K) := LinearOrder.toDecidableEq

/-- The nonempty simplices of `K`, on precisely its active vertices. -/
def geometricComplex (K : FiniteComplex V) :
    AbstractSimplicialComplex (ActiveVertex K) where
  faces := {τ | τ.Nonempty ∧ τ.image Subtype.val ∈ K}
  isRelLowerSet_faces := by
    intro σ hσ
    constructor
    · exact hσ.1
    · intro τ hsub hτ
      exact ⟨hτ, K.down_closed (Finset.image_subset_image hsub) hσ.2⟩
  singleton_mem := by
    intro v
    constructor
    · exact Finset.singleton_nonempty _
    · have hi : ({v.1} : Finset V) = ({v} : Finset (ActiveVertex K)).image Subtype.val := by
        change ({v.1} : Finset V) = ({v.1} : Finset V)
        rfl
      rw [← hi]
      exact v.2

/-- The actual weak-topology space associated with the original finite complex. -/
abbrev geometricRealization (K : FiniteComplex V) :=
  CurveComplex.RealizationPoint (geometricComplex K)

def activeFace (K : FiniteComplex V) (σ : Finset V) (hσ : σ ∈ K) :
    Finset (ActiveVertex K) := by
  exact σ.attach.map ⟨fun v =>
    (⟨v.1, K.down_closed (Finset.singleton_subset_iff.mpr v.2) hσ⟩ : ActiveVertex K),
    by
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun w : ActiveVertex K => w.1) hxy⟩

theorem activeFace_image_val (K : FiniteComplex V) (σ : Finset V) (hσ : σ ∈ K) :
    (activeFace K σ hσ).image Subtype.val = σ := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    unfold activeFace at hu
    obtain ⟨w, hw, huw⟩ := Finset.mem_map.mp hu
    exact huw ▸ w.2
  · intro hv
    apply Finset.mem_image.mpr
    refine ⟨⟨v, K.down_closed (Finset.singleton_subset_iff.mpr hv) hσ⟩, ?_, rfl⟩
    unfold activeFace
    apply Finset.mem_map.mpr
    exact ⟨⟨v, hv⟩, Finset.mem_attach σ ⟨v, hv⟩, rfl⟩

theorem mem_activeFace_iff (K : FiniteComplex V) (σ : Finset V)
    (hσ : σ ∈ K) (v : ActiveVertex K) :
    v ∈ activeFace K σ hσ ↔ v.1 ∈ σ := by
  constructor
  · intro hv
    have himage : v.1 ∈ (activeFace K σ hσ).image Subtype.val :=
      Finset.mem_image_of_mem _ hv
    rwa [activeFace_image_val] at himage
  · intro hv
    have himage : v.1 ∈ (activeFace K σ hσ).image Subtype.val := by
      rw [activeFace_image_val]
      exact hv
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp himage
    have : w = v := Subtype.ext heq
    exact this ▸ hw

theorem activeFace_erase (K : FiniteComplex V) (σ : Finset V) (hσ : σ ∈ K)
    (v : V) (hv : v ∈ σ) :
    activeFace K (σ.erase v) (K.down_closed (Finset.erase_subset v σ) hσ) =
      (activeFace K σ hσ).erase
        ⟨v, K.down_closed (Finset.singleton_subset_iff.mpr hv) hσ⟩ := by
  classical
  ext w
  rw [mem_activeFace_iff]
  rw [Finset.mem_erase]
  constructor
  · intro hw
    apply Finset.mem_erase.mpr
    exact ⟨fun heq => hw.1 (congrArg (fun u : ActiveVertex K => u.1) heq),
      (mem_activeFace_iff K σ hσ w).2 hw.2⟩
  · intro hw
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
    exact ⟨fun heq => hne (Subtype.ext heq), (mem_activeFace_iff K σ hσ w).1 hmem⟩

theorem activeFace_mem_geometricComplex (K : FiniteComplex V) (σ : Finset V)
    (hσ : σ ∈ K) (hne : σ.Nonempty) :
    activeFace K σ hσ ∈ (geometricComplex K).faces := by
  constructor
  · obtain ⟨v, hv⟩ := hne
    have himage : v ∈ (activeFace K σ hσ).image Subtype.val := by
      rw [activeFace_image_val]
      exact hv
    obtain ⟨w, hw, _⟩ := Finset.mem_image.mp himage
    exact ⟨w, hw⟩
  · rw [activeFace_image_val]
    exact hσ

theorem activeFace_card (K : FiniteComplex V) (σ : Finset V) (hσ : σ ∈ K) :
    (activeFace K σ hσ).card = σ.card := by
  have hi : Function.Injective (Subtype.val : ActiveVertex K → V) := Subtype.val_injective
  calc
    (activeFace K σ hσ).card = ((activeFace K σ hσ).image Subtype.val).card :=
      (Finset.card_image_of_injective _ hi).symm
    _ = σ.card := congrArg Finset.card (activeFace_image_val K σ hσ)

theorem activeFace_orderEmb_val (K : FiniteComplex V)
    (σ : Finset V) (hσ : σ ∈ K) {m : ℕ}
    (hcard : σ.card = m) (i : Fin m) :
    ((activeFace K σ hσ).orderEmbOfFin
      ((activeFace_card K σ hσ).trans hcard) i).1 =
      σ.orderEmbOfFin hcard i := by
  let f : Fin m → V := fun j =>
    ((activeFace K σ hσ).orderEmbOfFin
      ((activeFace_card K σ hσ).trans hcard) j).1
  have hfmem (j : Fin m) : f j ∈ σ := by
    exact (mem_activeFace_iff K σ hσ _).mp
      ((activeFace K σ hσ).orderEmbOfFin_mem _ j)
  have hfmono : StrictMono f := by
    intro j k hjk
    exact ((activeFace K σ hσ).orderEmbOfFin
      ((activeFace_card K σ hσ).trans hcard)).strictMono hjk
  have heq := Finset.orderEmbOfFin_unique hcard hfmem hfmono
  exact congrFun heq i

def positiveFace (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K ((n + 1 : ℕ) : ℤ)) (v : σ.1) :
    SimplexAt K (n : ℤ) := by
  refine ⟨σ.1.erase v.1, ?_⟩
  constructor
  · exact K.down_closed (Finset.erase_subset v.1 σ.1) σ.2.1
  · right
    constructor
    · exact_mod_cast Nat.zero_le n
    · have hσcard : σ.1.card = n + 2 := by
        rcases σ.2.2 with hneg | hpos
        · omega
        · omega
      have herase := Finset.card_erase_add_one v.2
      omega

/-- Every nonnegative generator of the augmented simplicial complex determines
an actual singular simplex of the realization of its nonempty faces. -/
def simplexAtSingular (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n : ℤ)) :
    (TopCat.toSSet.obj (TopCat.of (geometricRealization K))).obj (Opposite.op ⦋n⦌) := by
  letI : LinearOrder (ActiveVertex K) := Subtype.instLinearOrder _
  have hcard : σ.1.card = n + 1 := by
    rcases σ.2.2 with hneg | hpos
    · omega
    · omega
  have hnonempty : σ.1.Nonempty := Finset.card_pos.mp (by omega)
  let τ := activeFace K σ.1 σ.2.1
  have hτ : τ ∈ (geometricComplex K).faces :=
    activeFace_mem_geometricComplex K σ.1 σ.2.1 hnonempty
  have hτcard : τ.card = n + 1 := by
    rw [activeFace_card]
    exact hcard
  exact CurveComplex.affineFaceSimplex (geometricComplex K) τ hτ hτcard

theorem simplexAtSingular_delta (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K ((n + 1 : ℕ) : ℤ)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (geometricRealization K))).δ i
      (simplexAtSingular K (n + 1) σ) =
    simplexAtSingular K n
      (positiveFace K n σ
        ⟨σ.1.orderEmbOfFin (by
          rcases σ.2.2 with hneg | hpos <;> omega) i,
          σ.1.orderEmbOfFin_mem _ i⟩) := by
  let hcard : σ.1.card = n + 2 := by
    rcases σ.2.2 with hneg | hpos <;> omega
  let τ := activeFace K σ.1 σ.2.1
  have hτcard : τ.card = n + 2 := (activeFace_card K σ.1 σ.2.1).trans hcard
  have hτ : τ ∈ (geometricComplex K).faces :=
    activeFace_mem_geometricComplex K σ.1 σ.2.1
      (Finset.card_pos.mp (by omega))
  let v : σ.1 := ⟨σ.1.orderEmbOfFin hcard i, σ.1.orderEmbOfFin_mem hcard i⟩
  have hvactive : τ.orderEmbOfFin hτcard i =
      (⟨v.1, K.down_closed (Finset.singleton_subset_iff.mpr v.2) σ.2.1⟩ :
        ActiveVertex K) := by
    apply Subtype.ext
    exact activeFace_orderEmb_val K σ.1 σ.2.1 hcard i
  have hface : τ.erase (τ.orderEmbOfFin hτcard i) ∈
      (geometricComplex K).faces := by
    have hcarderase : (σ.1.erase v.1).card = n + 1 := by
      have he := Finset.card_erase_add_one v.2
      omega
    rw [hvactive, ← activeFace_erase K σ.1 σ.2.1 v.1 v.2]
    exact activeFace_mem_geometricComplex K (σ.1.erase v.1)
      (K.down_closed (Finset.erase_subset v.1 σ.1) σ.2.1)
      (Finset.card_pos.mp (by omega))
  have hfacecard : (τ.erase (τ.orderEmbOfFin hτcard i)).card = n + 1 := by
    have he := Finset.card_erase_add_one (τ.orderEmbOfFin_mem hτcard i)
    omega
  have hδ := CurveComplex.affineFaceSimplex_delta_eq_erase
    (geometricComplex K) τ hτ hτcard i hface hfacecard
  have hfaceeq :
      activeFace K
          (positiveFace K n σ
            ⟨σ.1.orderEmbOfFin hcard i, σ.1.orderEmbOfFin_mem hcard i⟩).1
          (positiveFace K n σ
            ⟨σ.1.orderEmbOfFin hcard i, σ.1.orderEmbOfFin_mem hcard i⟩).2.1 =
        τ.erase (τ.orderEmbOfFin hτcard i) := by
    change activeFace K (σ.1.erase v.1) _ = _
    rw [activeFace_erase K σ.1 σ.2.1 v.1 v.2, hvactive]
  unfold simplexAtSingular
  simpa only [hfaceeq] using hδ

private theorem comparison_cast_sum {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {α : Type*} (s : Finset α) (f : α → F i) :
    Eq.mp (congrArg F h) (∑ x ∈ s, f x) =
      ∑ x ∈ s, Eq.mp (congrArg F h) (f x) := by
  cases h
  rfl

private theorem comparison_cast_zsmul {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    (r : ℤ) (x : F i) :
    Eq.mp (congrArg F h) (r • x) = r • Eq.mp (congrArg F h) x := by
  cases h
  rfl

private theorem comparison_cast_of {ι : Type*} {G : ι → Type*}
    {i j : ι} (h : i = j) (x : G i) :
    Eq.mp (congrArg (fun k => FreeAbelianGroup (G k)) h)
        (FreeAbelianGroup.of x) =
      FreeAbelianGroup.of (Eq.mp (congrArg G h) x) := by
  cases h
  rfl

private theorem comparison_cast_simplex_val (K : FiniteComplex V)
    {i j : ℤ} (h : i = j) (σ : SimplexAt K i) :
    (Eq.mp (congrArg (SimplexAt K) h) σ).1 = σ.1 := by
  cases h
  rfl

/-- The generator-level canonical simplicial-to-singular comparison. -/
def simplicialToSingularGenerators (K : FiniteComplex V) (n : ℕ) :
    chains K (n : ℤ) →+
      FreeAbelianGroup
        ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))).obj
          (Opposite.op ⦋n⦌)) :=
  FreeAbelianGroup.lift fun σ => FreeAbelianGroup.of (simplexAtSingular K n σ)

theorem simplicialToSingularGenerators_of (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K (n : ℤ)) :
    simplicialToSingularGenerators K n (FreeAbelianGroup.of σ) =
      FreeAbelianGroup.of (simplexAtSingular K n σ) := by
  simp [simplicialToSingularGenerators]

/-- The alternating singular differential on the same simplex basis used by
Mathlib's singular simplicial set. -/
def singularGeneratorBoundary (K : FiniteComplex V) (n : ℕ) :
    FreeAbelianGroup
      ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))).obj
        (Opposite.op ⦋n + 1⦌)) →+
    FreeAbelianGroup
      ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))).obj
        (Opposite.op ⦋n⦌)) :=
  FreeAbelianGroup.lift fun s =>
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      FreeAbelianGroup.of
        ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))).δ i s)

theorem singularGeneratorBoundary_of (K : FiniteComplex V) (n : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.of (geometricRealization K))).obj
      (Opposite.op ⦋n + 1⦌)) :
    singularGeneratorBoundary K n (FreeAbelianGroup.of s) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        FreeAbelianGroup.of
          ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))).δ i s) := by
  simp [singularGeneratorBoundary]

/-- The augmented boundary at a positive simplicial degree, transported to the
corresponding natural-number degree. -/
def positiveBoundary (K : FiniteComplex V) (n : ℕ) :
    chains K ((n + 1 : ℕ) : ℤ) →+ chains K (n : ℤ) := by
  have h : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
  exact Eq.mp
    (congrArg (fun k : ℤ => chains K ((n + 1 : ℕ) : ℤ) →+ chains K k) h)
    (boundary K ((n + 1 : ℕ) : ℤ))

private theorem comparison_cast_apply {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) (x : A) :
    (Eq.mp (congrArg (fun k => A →+ F k) h) f) x =
      Eq.mp (congrArg F h) (f x) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem positiveBoundary_of (K : FiniteComplex V) (n : ℕ)
    (σ : SimplexAt K ((n + 1 : ℕ) : ℤ)) :
    positiveBoundary K n (FreeAbelianGroup.of σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        FreeAbelianGroup.of
          (positiveFace K n σ
            ⟨σ.1.orderEmbOfFin (by
              rcases σ.2.2 with hneg | hpos <;> omega) i,
              σ.1.orderEmbOfFin_mem _ i⟩) := by
  classical
  have hn : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
  have hcard : σ.1.card = n + 2 := by
    rcases σ.2.2 with hneg | hpos <;> omega
  rw [show positiveBoundary K n (FreeAbelianGroup.of σ) =
      Eq.mp (congrArg (chains K) hn)
        (faceBoundary K ((n + 1 : ℕ) : ℤ) σ) by
      change (Eq.mp (congrArg (fun k : ℤ =>
        chains K ((n + 1 : ℕ) : ℤ) →+ chains K k) hn)
        (boundary K ((n + 1 : ℕ) : ℤ))) (FreeAbelianGroup.of σ) = _
      rw [comparison_cast_apply]
      simp [boundary]
      all_goals omega]
  rw [faceBoundary]
  conv_lhs => rw [← Finset.sum_attach]
  rw [comparison_cast_sum hn]
  let e : Fin (n + 2) ≃ σ.1 := (σ.1.orderIsoOfFin hcard).toEquiv
  symm
  apply Fintype.sum_equiv e
  intro i
  have hv : σ.1.orderEmbOfFin hcard i ∈ σ.1 := σ.1.orderEmbOfFin_mem hcard i
  have hvalid : σ.1.erase (σ.1.orderEmbOfFin hcard i) ∈ K ∧
      (((((n + 1 : ℕ) : ℤ) - 1) = -1 ∧
        σ.1.erase (σ.1.orderEmbOfFin hcard i) = ∅) ∨
       (0 ≤ ((n + 1 : ℕ) : ℤ) - 1 ∧
        ((σ.1.erase (σ.1.orderEmbOfFin hcard i)).card : ℤ) =
          (((n + 1 : ℕ) : ℤ) - 1) + 1)) := by
    refine ⟨K.down_closed (Finset.erase_subset _ _) σ.2.1, Or.inr ?_⟩
    have he := Finset.card_erase_add_one hv
    constructor <;> omega
  have he : (e i).1 = σ.1.orderEmbOfFin hcard i := rfl
  have hface :
      Eq.mp (congrArg (SimplexAt K) hn)
          (⟨σ.1.erase (σ.1.orderEmbOfFin hcard i), hvalid⟩ :
            SimplexAt K (((n + 1 : ℕ) : ℤ) - 1)) =
        positiveFace K n σ
          ⟨σ.1.orderEmbOfFin hcard i, hv⟩ := by
    apply Subtype.ext
    exact comparison_cast_simplex_val K hn _
  have hterm :
      Eq.mp (congrArg (chains K) hn)
        ((-1 : ℤ) ^ (σ.1.filter (· < σ.1.orderEmbOfFin hcard i)).card •
          FreeAbelianGroup.of
            (⟨σ.1.erase (σ.1.orderEmbOfFin hcard i), hvalid⟩ :
              SimplexAt K (((n + 1 : ℕ) : ℤ) - 1))) =
      (-1 : ℤ) ^ i.val •
        FreeAbelianGroup.of
          (positiveFace K n σ ⟨σ.1.orderEmbOfFin hcard i, hv⟩) := by
    calc
      Eq.mp (congrArg (chains K) hn)
          ((-1 : ℤ) ^ (σ.1.filter (· < σ.1.orderEmbOfFin hcard i)).card •
            FreeAbelianGroup.of
              (⟨σ.1.erase (σ.1.orderEmbOfFin hcard i), hvalid⟩ :
                SimplexAt K (((n + 1 : ℕ) : ℤ) - 1))) =
          (-1 : ℤ) ^ (σ.1.filter (· < σ.1.orderEmbOfFin hcard i)).card •
            Eq.mp (congrArg (chains K) hn)
              (FreeAbelianGroup.of
                (⟨σ.1.erase (σ.1.orderEmbOfFin hcard i), hvalid⟩ :
                  SimplexAt K (((n + 1 : ℕ) : ℤ) - 1))) :=
        comparison_cast_zsmul (F := chains K) hn
          ((-1 : ℤ) ^ (σ.1.filter (· < σ.1.orderEmbOfFin hcard i)).card)
          (FreeAbelianGroup.of
            (⟨σ.1.erase (σ.1.orderEmbOfFin hcard i), hvalid⟩ :
              SimplexAt K (((n + 1 : ℕ) : ℤ) - 1)))
      _ = (-1 : ℤ) ^ (σ.1.filter (· < σ.1.orderEmbOfFin hcard i)).card •
            FreeAbelianGroup.of
              (positiveFace K n σ ⟨σ.1.orderEmbOfFin hcard i, hv⟩) := by
        have hcastOf :
            Eq.mp (congrArg (chains K) hn)
              (FreeAbelianGroup.of
                (⟨σ.1.erase (σ.1.orderEmbOfFin hcard i), hvalid⟩ :
                  SimplexAt K (((n + 1 : ℕ) : ℤ) - 1))) =
              FreeAbelianGroup.of
                (Eq.mp (congrArg (SimplexAt K) hn)
                  (⟨σ.1.erase (σ.1.orderEmbOfFin hcard i), hvalid⟩ :
                    SimplexAt K (((n + 1 : ℕ) : ℤ) - 1))) :=
          comparison_cast_of (G := SimplexAt K) hn _
        rw [hcastOf, hface]
      _ = _ := by rw [CurveComplex.card_filter_lt_orderEmbOfFin σ.1 hcard i]
  simpa only [he, dif_pos hvalid] using hterm.symm

set_option backward.isDefEq.respectTransparency.types false in
theorem simplicialToSingular_boundary (K : FiniteComplex V) (n : ℕ)
    (c : chains K ((n + 1 : ℕ) : ℤ)) :
    simplicialToSingularGenerators K n (positiveBoundary K n c) =
      singularGeneratorBoundary K n
        (simplicialToSingularGenerators K (n + 1) c) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of σ =>
    rw [positiveBoundary_of, map_sum]
    simp_rw [map_zsmul, simplicialToSingularGenerators_of]
    simp only [singularGeneratorBoundary_of]
    apply Finset.sum_congr rfl
    intro i _
    rw [simplexAtSingular_delta]
  | neg σ h => simp only [map_neg, h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Singular cycles in positive degree, expressed on the standard simplex basis. -/
def singularPositiveCycles (K : FiniteComplex V) (n : ℕ) :
    AddSubgroup (FreeAbelianGroup
      ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))).obj
        (Opposite.op ⦋n + 1⦌))) :=
  (singularGeneratorBoundary K n).ker

def singularPositiveBoundaries (K : FiniteComplex V) (n : ℕ) :
    AddSubgroup (FreeAbelianGroup
      ((TopCat.toSSet.obj (TopCat.of (geometricRealization K))).obj
        (Opposite.op ⦋n + 1⦌))) :=
  (singularGeneratorBoundary K (n + 1)).range

/-- Positive-degree singular homology on the raw singular simplex basis. -/
abbrev singularPositiveHomology (K : FiniteComplex V) (n : ℕ) :=
  (singularPositiveCycles K n) ⧸
    ((singularPositiveBoundaries K n).comap
      (singularPositiveCycles K n).subtype)

private theorem positiveBoundary_apply (K : FiniteComplex V) (n : ℕ)
    (c : chains K ((n + 1 : ℕ) : ℤ)) :
    positiveBoundary K n c =
      Eq.mp (congrArg (chains K)
        (show (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) by omega))
        (boundary K ((n + 1 : ℕ) : ℤ) c) := by
  unfold positiveBoundary
  rw [comparison_cast_apply]
  all_goals omega

private theorem comparison_cast_zero {ι : Type*} {F : ι → Type*}
    [∀ i, Zero (F i)] {i j : ι} (h : i = j) :
    Eq.mp (congrArg F h) (0 : F i) = 0 := by
  cases h
  rfl

def positiveCyclesMap (K : FiniteComplex V) (n : ℕ) :
    cycles K ((n + 1 : ℕ) : ℤ) →+ singularPositiveCycles K n := by
  refine ((simplicialToSingularGenerators K (n + 1)).comp
      (cycles K ((n + 1 : ℕ) : ℤ)).subtype).codRestrict
      (singularPositiveCycles K n) ?_
  intro c
  change singularGeneratorBoundary K n
    (simplicialToSingularGenerators K (n + 1) c.1) = 0
  rw [← simplicialToSingular_boundary, positiveBoundary_apply]
  have hc : boundary K ((n + 1 : ℕ) : ℤ) c.1 = 0 := c.2
  rw [hc]
  rw [comparison_cast_zero]
  simp
  all_goals omega

private theorem comparison_cast_range {ι : Type*} {F : ι → Type*}
    [∀ i, AddCommGroup (F i)] {i j : ι} (h : i = j)
    {A : Type*} [AddCommGroup A] (f : A →+ F i) :
    Eq.mp (congrArg (fun k => AddSubgroup (F k)) h) f.range =
      (Eq.mp (congrArg (fun k => A →+ F k) h) f).range := by
  cases h
  rfl

private theorem boundaries_eq_positiveBoundary_range (K : FiniteComplex V) (n : ℕ) :
    boundaries K ((n + 1 : ℕ) : ℤ) =
      (positiveBoundary K (n + 1)).range := by
  have h : (((n + 1 : ℕ) : ℤ) + 1 - 1) = ((n + 1 : ℕ) : ℤ) := by omega
  have h' : (((n + 1 + 1 : ℕ) : ℤ) - 1) = ((n + 1 : ℕ) : ℤ) := by omega
  change Eq.mp (congrArg (fun k : ℤ => AddSubgroup (chains K k)) h)
      (boundary K (((n + 1 : ℕ) : ℤ) + 1)).range =
    (Eq.mp (congrArg (fun k : ℤ =>
      chains K ((n + 1 + 1 : ℕ) : ℤ) →+ chains K k) h')
      (boundary K ((n + 1 + 1 : ℕ) : ℤ))).range
  exact comparison_cast_range h (boundary K (((n + 1 : ℕ) : ℤ) + 1))

def positiveHomologyComparison (K : FiniteComplex V) (n : ℕ) :
    reducedHomology K ((n + 1 : ℕ) : ℤ) →+
      singularPositiveHomology K n := by
  let S := (cycles K ((n + 1 : ℕ) : ℤ)).subtype
  let T := (singularPositiveCycles K n).subtype
  let R := ((boundaries K ((n + 1 : ℕ) : ℤ)).comap S)
  let f := (QuotientAddGroup.mk' ((singularPositiveBoundaries K n).comap T)).comp
    (positiveCyclesMap K n)
  have hle : R ≤ f.ker := by
    intro c hc
    change c.1 ∈ boundaries K ((n + 1 : ℕ) : ℤ) at hc
    rw [boundaries_eq_positiveBoundary_range K n] at hc
    obtain ⟨z, hz⟩ := hc
    apply (QuotientAddGroup.eq_zero_iff _).2
    change (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n
    change simplicialToSingularGenerators K (n + 1) c.1 ∈
      (singularGeneratorBoundary K (n + 1)).range
    rw [← hz]
    rw [show simplicialToSingularGenerators K (n + 1)
        (positiveBoundary K (n + 1) z) =
      singularGeneratorBoundary K (n + 1)
        (simplicialToSingularGenerators K (n + 2) z) by
      exact simplicialToSingular_boundary K (n + 1) z]
    exact ⟨simplicialToSingularGenerators K (n + 2) z, rfl⟩
  exact QuotientAddGroup.lift R f hle

end CurveGenusTwo.Filtration
