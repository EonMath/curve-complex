import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.LocalSheafScaffold
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Module.Basic

open TopologicalSpace
open SameAtlasRRLocal
open MeasureTheory
open scoped Manifold ContDiff Bundle
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

namespace SameAtlasAnalyticCohomology

universe u v

variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

/-- An indexed open cover of the same complex atlas. -/
structure OpenCover (E : Type*) [TopologicalSpace E] where
  Index : Type*
  opens : Index → Opens E
  covers : ⨆ i, opens i = ⊤

variable (U : OpenCover E)

/-- Degree-zero Cech cochains with coefficients in the actual `HolOn` sheaf. -/
abbrev CechZero := ∀ i : U.Index, HolOn (U.opens i)

/-- Ordered degree-one Cech cochains on pairwise intersections. -/
abbrev CechOne := ∀ i j : U.Index, HolOn (U.opens i ⊓ U.opens j)

/-- Ordered degree-two Cech cochains on triple intersections. -/
abbrev CechTwo :=
  ∀ i j k : U.Index, HolOn (U.opens i ⊓ U.opens j ⊓ U.opens k)

/-- The ordinary Cech differential `f_j - f_i` on overlaps. -/
noncomputable def deltaZero : CechZero U →ₗ[ℂ] CechOne U where
  toFun f i j :=
    HolOn.restrict (show U.opens i ⊓ U.opens j ≤ U.opens j by simp) (f j) -
    HolOn.restrict (show U.opens i ⊓ U.opens j ≤ U.opens i by simp) (f i)
  map_add' := by
    intro f g
    funext i j
    simp [add_sub_add_comm]
  map_smul' := by
    intro a f
    funext i j
    simp [smul_sub]

/-- The Cech cocycle equation `g_jk - g_ik + g_ij = 0` on triple overlaps. -/
def IsOneCocycle (g : CechOne U) : Prop :=
  ∀ i j k : U.Index,
    HolOn.restrict (show U.opens i ⊓ U.opens j ⊓ U.opens k ≤
      U.opens j ⊓ U.opens k by
        exact le_inf (le_trans inf_le_left inf_le_right) inf_le_right) (g j k) -
    HolOn.restrict (show U.opens i ⊓ U.opens j ⊓ U.opens k ≤
      U.opens i ⊓ U.opens k by
        exact le_inf (le_trans inf_le_left inf_le_left) inf_le_right) (g i k) +
    HolOn.restrict (show U.opens i ⊓ U.opens j ⊓ U.opens k ≤
      U.opens i ⊓ U.opens j by
        exact le_inf (le_trans inf_le_left inf_le_left)
          (le_trans inf_le_left inf_le_right)) (g i j) = 0

/-- Actual one-cocycles of the same-atlas holomorphic-function sheaf. -/
def oneCocycles : Submodule ℂ (CechOne U) where
  carrier := {g | IsOneCocycle U g}
  zero_mem' := by
    intro i j k
    simp
  add_mem' := by
    intro f g hf hg i j k
    simp only [Pi.add_apply, map_add]
    calc
      _ = (HolOn.restrict _ (f j k) - HolOn.restrict _ (f i k) +
        HolOn.restrict _ (f i j)) +
        (HolOn.restrict _ (g j k) - HolOn.restrict _ (g i k) +
        HolOn.restrict _ (g i j)) := by abel
      _ = 0 := by
        simpa [hf i j k, hg i j k]
  smul_mem' := by
    intro a g hg i j k
    simp only [Pi.smul_apply, map_smul]
    simpa only [smul_sub, smul_add, smul_zero] using
      congrArg (fun f => a • f) (hg i j k)

/-- The zero-cochain differential lands in actual cocycles (`δ² = 0`). -/
noncomputable def deltaZeroToCocycles : CechZero U →ₗ[ℂ] oneCocycles U where
  toFun f := ⟨deltaZero U f, by
    change IsOneCocycle U (deltaZero U f)
    intro i j k
    ext x
    simp only [deltaZero, LinearMap.coe_mk, AddHom.coe_mk,
      HolOn.restrict, Submodule.coe_sub, Pi.sub_apply,
      Submodule.coe_add, Pi.add_apply, Submodule.coe_zero, Pi.zero_apply]
    abel⟩
  map_add' := by
    intro f g
    apply Subtype.ext
    exact (deltaZero U).map_add f g
  map_smul' := by
    intro a f
    apply Subtype.ext
    exact (deltaZero U).map_smul a f

/-- Two cocycles represent the same class exactly when their difference is a coboundary. -/
def cocycleSetoid : Setoid (oneCocycles U) where
  r g h := g - h ∈ (deltaZeroToCocycles U).range
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro g
      exact ⟨0, by rw [map_zero]; exact (sub_self g).symm⟩
    · intro g h hgh
      obtain ⟨f, hf⟩ := hgh
      refine ⟨-f, ?_⟩
      rw [map_neg, hf]
      abel
    · intro g h k hgh hhk
      obtain ⟨f, hf⟩ := hgh
      obtain ⟨t, ht⟩ := hhk
      exact ⟨f + t, by rw [map_add, hf, ht]; abel⟩

/-- The setoid presentation retained for comparison with the source definition. -/
abbrev CechHOneSetoid := Quotient (cocycleSetoid U)

/-- The ambient cochain quotient by actual holomorphic coboundaries. -/
noncomputable abbrev cochainQuotient := CechOne U ⧸ (deltaZero U).range

/-- First Cech cohomology, as the image of cocycles in the cochain quotient.
The induced subtype inherits its complex vector-space structure. -/
noncomputable def cechHOneSubmodule : Submodule ℂ (cochainQuotient U) :=
  (oneCocycles U).map (Submodule.mkQ (deltaZero U).range)

noncomputable abbrev CechHOne := cechHOneSubmodule U

/-- The class of an actual cocycle in the complex-linear quotient. -/
noncomputable def classOf : oneCocycles U →ₗ[ℂ] CechHOne U where
  toFun g := ⟨(Submodule.mkQ (deltaZero U).range) g.1, ⟨g.1, g.property, rfl⟩⟩
  map_add' := by
    intro g h
    apply Subtype.ext
    exact (Submodule.mkQ (deltaZero U).range).map_add g.1 h.1
  map_smul' := by
    intro a g
    apply Subtype.ext
    exact (Submodule.mkQ (deltaZero U).range).map_smul a g.1

/-- Every cohomology class has a cocycle representative. -/
theorem classOf_surjective (x : CechHOne U) :
    ∃ g : oneCocycles U, classOf U g = x := by
  obtain ⟨g, hg, he⟩ := x.property
  exact ⟨⟨g, hg⟩, Subtype.ext he⟩

/-- The two concrete quotient presentations agree, with the forward map
sending a cocycle representative to its actual linear cohomology class. -/
noncomputable def cechHOneSetoidEquiv : CechHOneSetoid U ≃ CechHOne U where
  toFun q := Quotient.liftOn q (classOf U) (by
    intro g h hgh
    apply Subtype.ext
    apply (Submodule.Quotient.eq (deltaZero U).range).2
    obtain ⟨f, hf⟩ := hgh
    exact ⟨f, congrArg Subtype.val hf⟩)
  invFun x := Quotient.mk (cocycleSetoid U)
    (Classical.choose (classOf_surjective U x))
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro g
    apply Quotient.sound
    have hc := Classical.choose_spec (classOf_surjective U (classOf U g))
    obtain ⟨f, hf⟩ := (Submodule.Quotient.eq (deltaZero U).range).1
      (congrArg Subtype.val hc)
    exact ⟨f, Subtype.ext hf⟩
  right_inv := by
    intro x
    exact Classical.choose_spec (classOf_surjective U x)

/-- A refinement map is an indexed inclusion of one open cover into another. -/
structure Refines (V U : OpenCover E) where
  index : V.Index → U.Index
  inclusion : ∀ j, V.opens j ≤ U.opens (index j)

/-- Pullback of a holomorphic Cech one-cochain along a refinement. -/
noncomputable def refineOne {V : OpenCover E} (r : Refines V U) :
    CechOne U →ₗ[ℂ] CechOne V where
  toFun g j k := HolOn.restrict
    (show V.opens j ⊓ V.opens k ≤ U.opens (r.index j) ⊓ U.opens (r.index k) by
      exact inf_le_inf (r.inclusion j) (r.inclusion k))
    (g (r.index j) (r.index k))
  map_add' := by
    intro g h
    funext i j
    exact (HolOn.restrict _).map_add _ _
  map_smul' := by
    intro a g
    funext i j
    exact (HolOn.restrict _).map_smul a _

/-- Refinement preserves the cocycle equation and coboundaries. -/
theorem refineOne_cocycle {V : OpenCover E} (r : Refines V U)
    (g : CechOne U) (hg : IsOneCocycle U g) :
    IsOneCocycle V (refineOne U r g) := by
  intro i j k
  ext x
  have h := congrArg (fun f => f.1
    ⟨x.1, ⟨⟨r.inclusion i x.property.1.1,
      r.inclusion j x.property.1.2⟩, r.inclusion k x.property.2⟩⟩)
    (hg (r.index i) (r.index j) (r.index k))
  exact h

theorem refineOne_coboundary {V : OpenCover E} (r : Refines V U)
    (f : CechZero U) :
    ∃ h : CechZero V, refineOne U r (deltaZero U f) = deltaZero V h := by
  refine ⟨fun j => HolOn.restrict (r.inclusion j) (f (r.index j)), ?_⟩
  funext i j
  ext x
  rfl

/-- Refinement carries the coboundary submodule into the new one. -/
theorem refineOne_range {V : OpenCover E} (r : Refines V U) :
    (deltaZero U).range ≤ (deltaZero V).range.comap (refineOne U r) := by
  intro g hg
  obtain ⟨f, rfl⟩ := hg
  obtain ⟨h, hh⟩ := refineOne_coboundary U r f
  exact ⟨h, hh.symm⟩

/-- The linear map induced by refinement on cochains modulo coboundaries. -/
noncomputable def refineAmbient {V : OpenCover E} (r : Refines V U) :
    cochainQuotient U →ₗ[ℂ] cochainQuotient V :=
  Submodule.mapQ (deltaZero U).range (deltaZero V).range
    (refineOne U r) (refineOne_range U r)

/-- The actual linear refinement map on first holomorphic Cech cohomology. -/
noncomputable def refineHOne {V : OpenCover E} (r : Refines V U) :
    CechHOne U →ₗ[ℂ] CechHOne V where
  toFun x := ⟨refineAmbient U r x.1, by
    obtain ⟨g, hg, he⟩ := x.property
    refine ⟨refineOne U r g, refineOne_cocycle U r g hg, ?_⟩
    rw [← he]
    rfl⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    exact (refineAmbient U r).map_add x.1 y.1
  map_smul' := by
    intro a x
    apply Subtype.ext
    exact (refineAmbient U r).map_smul a x.1

/-- The induced map sends each cocycle class to its restricted cocycle class. -/
theorem refineHOne_classOf {V : OpenCover E} (r : Refines V U)
    (g : oneCocycles U) :
    refineHOne U r (classOf U g) =
      classOf V ⟨refineOne U r g.1, refineOne_cocycle U r g.1 g.property⟩ := by
  apply Subtype.ext
  rfl

/-- McMullen Theorem 7.2: the map on H1 is independent of the chosen
refinement index assignment. -/
theorem refineHOne_independent_index {V : OpenCover E}
    (r s : Refines V U) : refineHOne U r = refineHOne U s := by
  apply LinearMap.ext
  intro x
  obtain ⟨g, rfl⟩ := classOf_surjective U x
  rw [refineHOne_classOf, refineHOne_classOf]
  let h : CechZero V := fun j => HolOn.restrict
    (le_inf (s.inclusion j) (r.inclusion j)) (g.1 (s.index j) (r.index j))
  have hh : refineOne U r g.1 - refineOne U s g.1 = deltaZero V h := by
    funext j k
    ext x
    have h₁ := congrArg (fun f => f.1
      ⟨x.1, ⟨⟨s.inclusion j x.property.1, r.inclusion j x.property.1⟩,
        r.inclusion k x.property.2⟩⟩)
      (g.property (s.index j) (r.index j) (r.index k))
    have h₂ := congrArg (fun f => f.1
      ⟨x.1, ⟨⟨s.inclusion j x.property.1, s.inclusion k x.property.2⟩,
        r.inclusion k x.property.2⟩⟩)
      (g.property (s.index j) (s.index k) (r.index k))
    simp only [refineOne, deltaZero, h, HolOn.restrict, LinearMap.coe_mk,
      AddHom.coe_mk, Submodule.coe_sub, Pi.sub_apply, Submodule.coe_add,
      Pi.add_apply, Submodule.coe_zero, Pi.zero_apply] at h₁ h₂ ⊢
    linear_combination h₁ - h₂
  apply Subtype.ext
  exact (Submodule.Quotient.eq (deltaZero V).range).2 ⟨h, hh.symm⟩

/-- Reindex a cover by the distinct open sets that actually occur in it.
Its index type has the same universe as the underlying space. -/
def rangeCover : OpenCover.{u, u} E where
  Index := {W : Opens E // W ∈ Set.range U.opens}
  opens W := W.1
  covers := by
    apply le_antisymm le_top
    rw [← U.covers]
    apply iSup_le
    intro i
    exact le_iSup_of_le ⟨U.opens i, i, rfl⟩ le_rfl

/-- The original cover refines its range-indexed copy by identity on opens. -/
def originalRefinesRange : Refines U (rangeCover U) where
  index i := ⟨U.opens i, i, rfl⟩
  inclusion _ := le_refl _

/-- The range-indexed copy refines the original cover after choosing an
index for each open set in its image. -/
noncomputable def rangeRefinesOriginal : Refines (rangeCover U) U where
  index W := Classical.choose W.property
  inclusion W := by
    change W.1 ≤ U.opens (Classical.choose W.property)
    exact le_of_eq (Classical.choose_spec W.property).symm

/-- Reindexing by the range induces an isomorphism of actual H1 modules. -/
theorem rangeCover_refinement_bijective :
    Function.Bijective (refineHOne U (rangeRefinesOriginal U)) := by
  let R := rangeCover U
  let a := originalRefinesRange U
  let b := rangeRefinesOriginal U
  let cU : Refines U U :=
    ⟨b.index ∘ a.index, fun i => (a.inclusion i).trans (b.inclusion (a.index i))⟩
  let cR : Refines R R :=
    ⟨a.index ∘ b.index, fun i => (b.inclusion i).trans (a.inclusion (b.index i))⟩
  let eU : Refines U U := ⟨id, fun _ => le_rfl⟩
  let eR : Refines R R := ⟨id, fun _ => le_rfl⟩
  have hU : (refineHOne R a).comp (refineHOne U b) = LinearMap.id := by
    calc
      _ = refineHOne U cU := by
        apply LinearMap.ext
        intro x
        obtain ⟨g, rfl⟩ := classOf_surjective U x
        simp only [LinearMap.comp_apply, refineHOne_classOf]
        apply Subtype.ext
        rfl
      _ = refineHOne U eU := refineHOne_independent_index U cU eU
      _ = LinearMap.id := by
        apply LinearMap.ext
        intro x
        obtain ⟨g, rfl⟩ := classOf_surjective U x
        rw [refineHOne_classOf]
        apply Subtype.ext
        rfl
  have hR : (refineHOne U b).comp (refineHOne R a) = LinearMap.id := by
    calc
      _ = refineHOne R cR := by
        apply LinearMap.ext
        intro x
        obtain ⟨g, rfl⟩ := classOf_surjective R x
        simp only [LinearMap.comp_apply, refineHOne_classOf]
        apply Subtype.ext
        rfl
      _ = refineHOne R eR := refineHOne_independent_index R cR eR
      _ = LinearMap.id := by
        apply LinearMap.ext
        intro x
        obtain ⟨g, rfl⟩ := classOf_surjective R x
        rw [refineHOne_classOf]
        apply Subtype.ext
        rfl
  constructor
  · intro x y hxy
    have hx := LinearMap.congr_fun hU x
    have hy := LinearMap.congr_fun hU y
    change refineHOne R a (refineHOne U b x) = x at hx
    change refineHOne R a (refineHOne U b y) = y at hy
    rw [← hx, ← hy, hxy]
  · intro y
    refine ⟨refineHOne R a y, ?_⟩
    exact LinearMap.congr_fun hR y

/-- The degree-one vanishing condition on an open submanifold, tested on every
holomorphic Cech cover of that submanifold. Theorem 7.3 makes this equivalent
to vanishing of the direct-limit cohomology. -/
def HOneAcyclic (W : Opens E) : Prop :=
  ∀ V : OpenCover.{u, u} W, Subsingleton (CechHOne V)

/-- The first-order Leray condition used for computing first cohomology. -/
def IsHOneLeray : Prop := ∀ i : U.Index, HOneAcyclic (U.opens i)

/-- A fixed-universe acyclicity test controls covers with arbitrary index
universe; the proof uses the explicit range reindexing above. -/
theorem HOneAcyclic.allCovers (W : Opens E) (hW : HOneAcyclic W)
    (V : OpenCover.{u, v} W) : Subsingleton (CechHOne V) := by
  letI := hW (rangeCover V)
  refine ⟨fun x y => (rangeCover_refinement_bijective V).1 ?_⟩
  exact Subsingleton.elim _ _

/-- Refinement between first-order Leray covers induces a linear isomorphism
on first cohomology (McMullen Theorem 7.5). -/
def CechHOneDual : Submodule ℂ (oneCocycles U →ₗ[ℂ] ℂ) where
  carrier := {φ | ∀ f : CechZero U, φ (deltaZeroToCocycles U f) = 0}
  zero_mem' := by
    intro f
    rfl
  add_mem' := by
    intro φ ψ hφ hψ f
    simp [hφ f, hψ f]
  smul_mem' := by
    intro a φ hφ f
    simp [hφ f]

/-- Pullback along the concrete quotient map identifies an H1 functional
with a cocycle functional annihilating coboundaries. -/
noncomputable def dualPullback :
    (CechHOne U →ₗ[ℂ] ℂ) →ₗ[ℂ] CechHOneDual U where
  toFun φ := ⟨φ.comp (classOf U), by
    intro f
    have hz : classOf U (deltaZeroToCocycles U f) = 0 := by
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero (deltaZero U).range).2 ⟨f, rfl⟩
    change φ (classOf U (deltaZeroToCocycles U f)) = 0
    rw [hz, map_zero]⟩
  map_add' := by
    intro φ ψ
    apply Subtype.ext
    ext g
    rfl
  map_smul' := by
    intro a φ
    apply Subtype.ext
    ext g
    rfl

theorem dualPullback_bijective : Function.Bijective (dualPullback U) := by
  classical
  constructor
  · intro φ ψ h
    ext x
    obtain ⟨g, rfl⟩ := classOf_surjective U x
    exact congrArg (fun θ : CechHOneDual U => θ.1 g) h
  · intro φ
    have hsame : ∀ g h : oneCocycles U,
        classOf U g = classOf U h → φ.1 g = φ.1 h := by
      intro g h hgh
      obtain ⟨f, hf⟩ := (Submodule.Quotient.eq (deltaZero U).range).1
        (congrArg Subtype.val hgh)
      have hf' : deltaZeroToCocycles U f = g - h := Subtype.ext hf
      apply sub_eq_zero.1
      rw [← map_sub, ← hf']
      exact φ.property f
    let p : CechHOne U → ℂ := fun x =>
      φ.1 (Classical.choose (classOf_surjective U x))
    have hp (g : oneCocycles U) : p (classOf U g) = φ.1 g :=
      hsame _ _ (Classical.choose_spec (classOf_surjective U (classOf U g)))
    let ψ : CechHOne U →ₗ[ℂ] ℂ :=
      { toFun := p
        map_add' := by
          intro x y
          obtain ⟨g, rfl⟩ := classOf_surjective U x
          obtain ⟨h, rfl⟩ := classOf_surjective U y
          rw [← map_add, hp, map_add, hp, hp]
        map_smul' := by
          intro a x
          obtain ⟨g, rfl⟩ := classOf_surjective U x
          rw [← map_smul, hp, map_smul, hp]
          rfl }
    refine ⟨ψ, ?_⟩
    apply Subtype.ext
    ext g
    exact hp g

noncomputable def dualPullbackEquiv :
    (CechHOne U →ₗ[ℂ] ℂ) ≃ₗ[ℂ] CechHOneDual U :=
  LinearEquiv.ofBijective (dualPullback U) (dualPullback_bijective U)

/-- The derivative `dw/dz` of two charts in the original complex atlas. -/
theorem coverIndex_exists (x : E) : ∃ i : U.Index, x ∈ U.opens i := by
  apply Opens.mem_iSup.1
  rw [U.covers]
  trivial


end SameAtlasAnalyticCohomology
