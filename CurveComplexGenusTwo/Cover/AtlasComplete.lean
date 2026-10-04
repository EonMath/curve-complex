import ActualCover
import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Analysis.Complex.OpenMapping


namespace AlternatingSphereCover

open scoped Manifold ContDiff

theorem atlas_plane_smooth0 : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞ localPlane := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ :=
    Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
      ((EuclideanSpace.proj 1).prod (EuclideanSpace.proj 2))
  have hL : ContDiff ℝ ∞ (L : EuclideanSpace ℝ (Fin 3) → ℂ) := L.contDiff
  have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      ((↑) : Sphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  convert hL.comp_contMDiff hcoe using 1
  ext x
  apply Complex.ext <;> rfl

noncomputable def firstBranchUp : OpenPartialHomeomorph Total ℂ := by
  classical
  have hb : branchPoint 0 ∈ positivePatch := by
    norm_num [positivePatch, branchPoint, branchVector]
  let A : Set Total := projection ⁻¹' positivePatch
  have hA : IsOpen A := positivePatch_isOpen.preimage projection_continuous
  let x := Classical.choose (projection_surjective (branchPoint 0))
  have hx : projection x = branchPoint 0 :=
    Classical.choose_spec (projection_surjective (branchPoint 0))
  have hxa : x ∈ A := by change projection x ∈ positivePatch; rwa [hx]
  let e : PatchTotal ≃ₜ A := patchToOpen_isHomeomorph.homeomorph patchToOpen
  let a : PatchTotal := e.symm ⟨x, hxa⟩
  letI : Nonempty PatchTotal := ⟨a⟩
  have hpe : Topology.IsOpenEmbedding patchProjection :=
    hA.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let up0 := patchRoot_isOpenEmbedding.toOpenPartialHomeomorph patchRoot
  exact up0.lift_openEmbedding hpe

noncomputable def firstBranchDown : OpenPartialHomeomorph Sphere ℂ := by
  classical
  have hb : branchPoint 0 ∈ positivePatch := by
    norm_num [positivePatch, branchPoint, branchVector]
  letI : Nonempty positivePatch := ⟨⟨branchPoint 0, hb⟩⟩
  let down0 := localPlane_isOpenEmbedding.toOpenPartialHomeomorph
    (fun b : positivePatch => localPlane b.val)
  exact down0.lift_openEmbedding positivePatch_isOpen.isOpenEmbedding_subtypeVal

theorem atlas_down_source0 : firstBranchDown.source = positivePatch := by
  classical
  simp [firstBranchDown, OpenPartialHomeomorph.lift_openEmbedding_source]

theorem atlas_up_source : firstBranchUp.source = projection ⁻¹' positivePatch := by
  classical
  simp only [firstBranchUp, OpenPartialHomeomorph.lift_openEmbedding_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.image_univ]
  ext x
  constructor
  · rintro ⟨a, -, rfl⟩
    exact patchProjection_mem a
  · intro hx
    let A : Set Total := projection ⁻¹' positivePatch
    let e : PatchTotal ≃ₜ A := patchToOpen_isHomeomorph.homeomorph patchToOpen
    let a : PatchTotal := e.symm ⟨x, hx⟩
    refine ⟨a, trivial, ?_⟩
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

theorem atlas_up_apply (a : PatchTotal) : firstBranchUp (patchProjection a) = patchRoot a := by
  classical
  unfold firstBranchUp
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

theorem atlas_down_apply0 (b : positivePatch) : firstBranchDown b.val = localPlane b.val := by
  classical
  unfold firstBranchDown
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

theorem atlas_down_inverse0 (z : ℂ) (hz : z ∈ firstBranchDown.target) :
    (firstBranchDown.symm z).val =
      !₂[Real.sqrt (1 - z.re ^ 2 - z.im ^ 2), z.re, z.im] := by
  classical
  let p : Sphere := firstBranchDown.symm z
  have hsource : firstBranchDown.source = positivePatch := by
    simp [firstBranchDown, OpenPartialHomeomorph.lift_openEmbedding_source]
  have hp : p ∈ positivePatch := by
    rw [← hsource]
    exact firstBranchDown.symm.map_source' hz
  have hcoord : localPlane p = z := by
    have hd : firstBranchDown p = localPlane p := by
      let q : positivePatch := ⟨p, hp⟩
      change firstBranchDown q.val = localPlane q.val
      unfold firstBranchDown
      exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
    rw [← hd]
    exact firstBranchDown.right_inv hz
  have h1 : p.val 1 = z.re := congrArg Complex.re hcoord
  have h2 : p.val 2 = z.im := congrArg Complex.im hcoord
  have hn : p.val 0 ^ 2 + p.val 1 ^ 2 + p.val 2 ^ 2 = 1 := by
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) p.val
    have he : ‖p.val‖ = 1 := by simp
    rw [he] at hn
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm
  have hnonneg : 0 ≤ 1 - z.re ^ 2 - z.im ^ 2 := by
    rw [← h1, ← h2]
    nlinarith [sq_nonneg (p.val 0)]
  have h0 : p.val 0 = Real.sqrt (1 - z.re ^ 2 - z.im ^ 2) := by
    apply (sq_eq_sq₀ (le_of_lt hp.1) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hnonneg, ← h1, ← h2]
    linarith
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2

theorem atlas_up_square (x : Total) (hx : x ∈ firstBranchUp.source) :
    firstBranchDown (projection x) = (firstBranchUp x) ^ 2 := by
  classical
  have hsource : firstBranchUp.source = projection ⁻¹' positivePatch := by
    simp only [firstBranchUp, OpenPartialHomeomorph.lift_openEmbedding_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Set.image_univ]
    ext y
    constructor
    · rintro ⟨a, -, rfl⟩
      exact patchProjection_mem a
    · intro hy
      let A : Set Total := projection ⁻¹' positivePatch
      let e : PatchTotal ≃ₜ A := patchToOpen_isHomeomorph.homeomorph patchToOpen
      let a : PatchTotal := e.symm ⟨y, hy⟩
      refine ⟨a, trivial, ?_⟩
      exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  have hxp : projection x ∈ positivePatch := by
    rw [hsource] at hx
    exact hx
  let A : Set Total := projection ⁻¹' positivePatch
  let e : PatchTotal ≃ₜ A := patchToOpen_isHomeomorph.homeomorph patchToOpen
  let a : PatchTotal := e.symm ⟨x, hxp⟩
  have ha : patchProjection a = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxp⟩)
  rw [← ha]
  have hu : firstBranchUp (patchProjection a) = patchRoot a := by
    unfold firstBranchUp
    exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  have hd (b : positivePatch) : firstBranchDown b.val = localPlane b.val := by
    unfold firstBranchDown
    exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  rw [hu, hd ⟨projection (patchProjection a), patchProjection_mem a⟩]
  exact (patchRoot_sq a).symm

end AlternatingSphereCover

open scoped Manifold ContDiff

namespace AlternatingSphereCover

open scoped ContDiff

def atlasPlaneTarget : Set ℂ :=
  {z | 4 * z.re ^ 2 + 3 * z.im ^ 2 < 3}

noncomputable def atlasSphereLift (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[Real.sqrt (1 - z.re ^ 2 - z.im ^ 2), z.re, z.im]

theorem atlasSphereLift_mem (z : ℂ) (hz : z ∈ atlasPlaneTarget) : atlasSphereLift z ∈ Sphere := by
  have hz' : 4 * z.re ^ 2 + 3 * z.im ^ 2 < 3 := hz
  have hp : 0 < 1 - z.re ^ 2 - z.im ^ 2 := by nlinarith [sq_nonneg z.re]
  have hs := Real.sq_sqrt (le_of_lt hp)
  have hn : ‖atlasSphereLift z‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [atlasSphereLift, Fin.sum_univ_succ, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    nlinarith
  change ‖atlasSphereLift z - 0‖ = 1
  rw [sub_zero]
  nlinarith [norm_nonneg (atlasSphereLift z)]

theorem atlasSphereLift_exists (z : ℂ) (hz : z ∈ atlasPlaneTarget) :
    ∃ p : positivePatch, localPlane p.val = z ∧ p.val.val = atlasSphereLift z := by
  have hz' : 4 * z.re ^ 2 + 3 * z.im ^ 2 < 3 := hz
  have hp : 0 < 1 - z.re ^ 2 - z.im ^ 2 := by nlinarith [sq_nonneg z.re]
  have hs := Real.sq_sqrt (le_of_lt hp)
  have hn : ‖atlasSphereLift z‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [atlasSphereLift, Fin.sum_univ_succ, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    nlinarith
  have hv : atlasSphereLift z ∈ Sphere := by
    change ‖atlasSphereLift z - 0‖ = 1
    rw [sub_zero]
    nlinarith [norm_nonneg (atlasSphereLift z)]
  let p : Sphere := ⟨atlasSphereLift z, hv⟩
  have hpp : p ∈ positivePatch := by
    change 0 < (atlasSphereLift z) 0 ∧
      0 < 3 * ((atlasSphereLift z) 0) ^ 2 - ((atlasSphereLift z) 1) ^ 2
    constructor
    · exact Real.sqrt_pos.2 hp
    · change 0 < 3 * Real.sqrt (1 - z.re ^ 2 - z.im ^ 2) ^ 2 - z.re ^ 2
      nlinarith
  refine ⟨⟨p, hpp⟩, ?_, rfl⟩
  apply Complex.ext <;> rfl

theorem atlasSphereLift_contDiffOn : ContDiffOn ℝ ∞ atlasSphereLift atlasPlaneTarget := by
  have hre : ContDiffOn ℝ ∞ Complex.re atlasPlaneTarget := by
    simpa only [show (Complex.reCLM : ℂ → ℝ) = Complex.re from funext Complex.reCLM_apply] using
      (Complex.reCLM.contDiff.contDiffOn (s := atlasPlaneTarget) (n := ∞))
  have him : ContDiffOn ℝ ∞ Complex.im atlasPlaneTarget := by
    simpa only [show (Complex.imCLM : ℂ → ℝ) = Complex.im from funext Complex.imCLM_apply] using
      (Complex.imCLM.contDiff.contDiffOn (s := atlasPlaneTarget) (n := ∞))
  apply (contDiffOn_piLp (p := 2)).2
  intro i
  fin_cases i
  · change ContDiffOn ℝ ∞ (fun z : ℂ => Real.sqrt (1 - z.re ^ 2 - z.im ^ 2)) atlasPlaneTarget
    apply ContDiffOn.sqrt
    · exact (contDiffOn_const.sub (hre.pow 2)).sub (him.pow 2)
    · intro z hz
      change 4 * z.re ^ 2 + 3 * z.im ^ 2 < 3 at hz
      have hp : 0 < 1 - z.re ^ 2 - z.im ^ 2 := by nlinarith [sq_nonneg z.re]
      exact ne_of_gt hp
  · change ContDiffOn ℝ ∞ (fun z : ℂ => z.re) atlasPlaneTarget
    exact hre
  · change ContDiffOn ℝ ∞ (fun z : ℂ => z.im) atlasPlaneTarget
    exact him


theorem atlasDown_target (z : ℂ) (hz : z ∈ firstBranchDown.target) : z ∈ atlasPlaneTarget := by
  let p : Sphere := firstBranchDown.symm z
  have hsource : firstBranchDown.source = positivePatch := by
    simp [firstBranchDown, OpenPartialHomeomorph.lift_openEmbedding_source]
  have hp : p ∈ positivePatch := by
    rw [← hsource]
    exact firstBranchDown.symm.map_source' hz
  have hcoord : localPlane p = z := by
    have hd : firstBranchDown p = localPlane p := by
      let q : positivePatch := ⟨p, hp⟩
      change firstBranchDown q.val = localPlane q.val
      unfold firstBranchDown
      exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
    rw [← hd]
    exact firstBranchDown.right_inv hz
  have h1 : p.val 1 = z.re := congrArg Complex.re hcoord
  have h2 : p.val 2 = z.im := congrArg Complex.im hcoord
  have hn : p.val 0 ^ 2 + p.val 1 ^ 2 + p.val 2 ^ 2 = 1 := by
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) p.val
    have he : ‖p.val‖ = 1 := by simp
    rw [he] at hn
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm
  change 4 * z.re ^ 2 + 3 * z.im ^ 2 < 3
  have hpatch : 0 < 3 * (p.val 0) ^ 2 - (p.val 1) ^ 2 := hp.2
  rw [← h1, ← h2]
  nlinarith

theorem atlasSphere_smooth (g : ℂ → Sphere) (s : Set ℂ)
    (hg : ContDiffOn ℝ ∞ (fun z => (g z).val) s) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ g s := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  rw [contMDiffOn_iff_target]
  constructor
  · exact Topology.IsInducing.subtypeVal.continuousOn_iff.mpr hg.continuousOn
  · intro v
    let U : _ ≃ₗᵢ[ℝ] _ :=
      (OrthonormalBasis.fromOrthogonalSpanSingleton 2
        (ne_zero_of_mem_unit_sphere (-v))).repr
    have h : ContDiffOn ℝ ω _ Set.univ := U.contDiff.contDiffOn
    have H₁ := (h.comp_inter contDiffOn_stereoToFun).contMDiffOn
    have H₂ : ContMDiffOn 𝓘(ℝ, ℂ)
        𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (fun z => (g z).val) s :=
      hg.contMDiffOn
    convert! (H₁.of_le le_top).comp' H₂ using 1
    ext z
    have hchart : (chartAt (EuclideanSpace ℝ (Fin 2)) v).source = {-v}ᶜ := by
      change (stereographic' 2 (-v)).source = _
      simp
    simp [hchart, sphere_ext_iff, real_inner_comm, innerSL_apply_apply]


theorem atlasDown_inverse (z : ℂ) (hz : z ∈ firstBranchDown.target) :
    (firstBranchDown.symm z).val =
      !₂[Real.sqrt (1 - z.re ^ 2 - z.im ^ 2), z.re, z.im] := by
  classical
  let p : Sphere := firstBranchDown.symm z
  have hsource : firstBranchDown.source = positivePatch := by
    simp [firstBranchDown, OpenPartialHomeomorph.lift_openEmbedding_source]
  have hp : p ∈ positivePatch := by
    rw [← hsource]
    exact firstBranchDown.symm.map_source' hz
  have hcoord : localPlane p = z := by
    have hd : firstBranchDown p = localPlane p := by
      let q : positivePatch := ⟨p, hp⟩
      change firstBranchDown q.val = localPlane q.val
      unfold firstBranchDown
      exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _
    rw [← hd]
    exact firstBranchDown.right_inv hz
  have h1 : p.val 1 = z.re := congrArg Complex.re hcoord
  have h2 : p.val 2 = z.im := congrArg Complex.im hcoord
  have hn : p.val 0 ^ 2 + p.val 1 ^ 2 + p.val 2 ^ 2 = 1 := by
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) p.val
    have he : ‖p.val‖ = 1 := by simp
    rw [he] at hn
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm
  have hnonneg : 0 ≤ 1 - z.re ^ 2 - z.im ^ 2 := by
    rw [← h1, ← h2]
    nlinarith [sq_nonneg (p.val 0)]
  have h0 : p.val 0 = Real.sqrt (1 - z.re ^ 2 - z.im ^ 2) := by
    apply (sq_eq_sq₀ (le_of_lt hp.1) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hnonneg, ← h1, ← h2]
    linarith
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2


 theorem atlasDown_inverse_smooth : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ firstBranchDown.symm firstBranchDown.target := by
  apply atlasSphere_smooth
  have h := atlasSphereLift_contDiffOn.mono (fun z hz => atlasDown_target z hz)
  apply h.congr
  intro z hz
  exact atlasDown_inverse z hz
end AlternatingSphereCover

open scoped Manifold ContDiff

namespace AlternatingSphereCover

noncomputable def totalRotIter : ℕ → Total ≃ₜ Total
  | 0 => Homeomorph.refl Total
  | n + 1 => (totalRotIter n).trans totalRotation

noncomputable def sphereRotIter : ℕ → Sphere ≃ₜ Sphere
  | 0 => Homeomorph.refl Sphere
  | n + 1 => (sphereRotIter n).trans sphereRotation

theorem atlas_rotation_projection (n : ℕ) (x : Total) :
    projection (totalRotIter n x) = sphereRotIter n (projection x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change projection (totalRotation (totalRotIter n x)) =
      sphereRotation (sphereRotIter n (projection x))
    rw [totalRotation_projection, ih]

noncomputable def rotatedBranchUp (n : ℕ) : OpenPartialHomeomorph Total ℂ :=
  (totalRotIter n).symm.toOpenPartialHomeomorph.trans firstBranchUp

noncomputable def rotatedBranchDown (n : ℕ) : OpenPartialHomeomorph Sphere ℂ :=
  (sphereRotIter n).symm.toOpenPartialHomeomorph.trans firstBranchDown

def branchRotationSteps : Fin 6 → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 5
  | 4 => 2
  | 5 => 4

theorem atlas_rotation_branchPoint (i : Fin 6) :
    sphereRotIter (branchRotationSteps i) (branchPoint 0) = branchPoint i := by
  fin_cases i <;>
    simp [branchRotationSteps, sphereRotIter, sphereRotation_branchPoint, nextBranch]

theorem atlas_rotated_square
    (hfirst : ∀ x ∈ firstBranchUp.source,
      firstBranchDown (projection x) = (firstBranchUp x) ^ 2)
    (n : ℕ) (x : Total) (hx : x ∈ (rotatedBranchUp n).source) :
    rotatedBranchDown n (projection x) = (rotatedBranchUp n x) ^ 2 := by
  have hforward (k : ℕ) (y : Total) :
      projection (totalRotIter k y) = sphereRotIter k (projection y) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change projection (totalRotation (totalRotIter k y)) =
        sphereRotation (sphereRotIter k (projection y))
      rw [totalRotation_projection, ih]
  have hcomm : projection ((totalRotIter n).symm x) =
      (sphereRotIter n).symm (projection x) := by
    apply (sphereRotIter n).injective
    rw [(sphereRotIter n).apply_symm_apply, ← hforward]
    exact congrArg projection ((totalRotIter n).apply_symm_apply x)
  have hx' : (totalRotIter n).symm x ∈ firstBranchUp.source := by
    simpa [rotatedBranchUp, OpenPartialHomeomorph.trans_source] using hx
  change firstBranchDown ((sphereRotIter n).symm (projection x)) =
    (firstBranchUp ((totalRotIter n).symm x)) ^ 2
  rw [← hcomm]
  exact hfirst _ hx'


theorem atlas_rotVector_contDiff : ContDiff ℝ ∞ rotVector := by
  have h0 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 0) := by
    let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj 0
    exact L.contDiff
  have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 1) := by
    let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj 1
    exact L.contDiff
  have h2 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 2) := by
    let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj 2
    exact L.contDiff
  apply (contDiff_piLp (p := 2)).2
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) =>
      (v 0 - Real.sqrt 3 * v 1) / 2)
    exact (h0.sub (contDiff_const.mul h1)).div_const 2
  · change ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) =>
      (Real.sqrt 3 * v 0 + v 1) / 2)
    exact ((contDiff_const.mul h0).add h1).div_const 2
  · change ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 2)
    exact h2

theorem atlas_rotation_smooth : ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereRotation : Sphere → Sphere) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      ((↑) : Sphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  have hrot : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun x : Sphere => rotVector x.val) := by
    exact atlas_rotVector_contDiff.comp_contMDiff hcoe
  have hs := hrot.codRestrict_sphere (n := 2) rotVector_mem
  convert hs using 1
  funext x
  rfl

theorem atlas_rotInvVector_contDiff : ContDiff ℝ ∞ rotInvVector := by
  have h0 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 0) := by
    let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj 0
    exact L.contDiff
  have h1 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 1) := by
    let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj 1
    exact L.contDiff
  have h2 : ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 2) := by
    let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := EuclideanSpace.proj 2
    exact L.contDiff
  apply (contDiff_piLp (p := 2)).2
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) =>
      (v 0 + Real.sqrt 3 * v 1) / 2)
    exact (h0.add (contDiff_const.mul h1)).div_const 2
  · change ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) =>
      (-Real.sqrt 3 * v 0 + v 1) / 2)
    exact ((contDiff_const.mul h0).add h1).div_const 2
  · change ContDiff ℝ ∞ (fun v : EuclideanSpace ℝ (Fin 3) => v 2)
    exact h2

theorem atlas_rotation_inverse_smooth : ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereRotation.symm : Sphere → Sphere) := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      ((↑) : Sphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  have hrot : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (fun x : Sphere => rotInvVector x.val) := by
    exact atlas_rotInvVector_contDiff.comp_contMDiff hcoe
  have hs := hrot.codRestrict_sphere (n := 2) rotInvVector_mem
  convert hs using 1
  funext x
  rfl


theorem atlas_rotIter_smooth (n : ℕ) : ContMDiff (𝓡 2) (𝓡 2) ∞ (sphereRotIter n : Sphere → Sphere) := by
  induction n with
  | zero => exact contMDiff_id
  | succ n ih => exact atlas_rotation_smooth.comp ih

theorem atlas_rotIter_inverse_smooth (n : ℕ) : ContMDiff (𝓡 2) (𝓡 2) ∞ ((sphereRotIter n).symm : Sphere → Sphere) := by
  induction n with
  | zero => exact contMDiff_id
  | succ n ih => exact ih.comp atlas_rotation_inverse_smooth



theorem atlas_rotatedDown_inverse_smooth (n : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ (rotatedBranchDown n).symm (rotatedBranchDown n).target := by
  have h := (atlas_rotIter_smooth n).comp_contMDiffOn atlasDown_inverse_smooth
  apply h.mono
  intro z hz
  simpa [rotatedBranchDown, OpenPartialHomeomorph.trans_target] using hz


theorem atlas_localPlane_smooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞ localPlane := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℂ :=
    Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
      ((EuclideanSpace.proj 1).prod (EuclideanSpace.proj 2))
  have hL : ContDiff ℝ ∞ (L : EuclideanSpace ℝ (Fin 3) → ℂ) := L.contDiff
  have hcoe : ContMDiff (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      ((↑) : Sphere → EuclideanSpace ℝ (Fin 3)) := contMDiff_coe_sphere
  convert hL.comp_contMDiff hcoe using 1
  ext x
  apply Complex.ext <;> rfl


theorem atlas_firstDown_source : firstBranchDown.source = positivePatch := by
  classical
  simp [firstBranchDown, OpenPartialHomeomorph.lift_openEmbedding_source]

theorem atlas_firstDown_apply (p : Sphere) (hp : p ∈ positivePatch) :
    firstBranchDown p = localPlane p := by
  classical
  let q : positivePatch := ⟨p, hp⟩
  change firstBranchDown q.val = localPlane q.val
  unfold firstBranchDown
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

theorem atlas_firstDown_smooth :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ firstBranchDown firstBranchDown.source := by
  apply atlas_localPlane_smooth.contMDiffOn.congr
  intro p hp
  exact atlas_firstDown_apply p (atlas_firstDown_source ▸ hp)

theorem atlas_rotatedDown_smooth (n : ℕ) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ (rotatedBranchDown n) (rotatedBranchDown n).source := by
  apply atlas_firstDown_smooth.comp (atlas_rotIter_inverse_smooth n).contMDiffOn
  intro p hp
  simpa [rotatedBranchDown, OpenPartialHomeomorph.trans_source] using hp

end AlternatingSphereCover

open scoped Manifold ContDiff Topology
namespace AlternatingSphereCover

theorem atlas_rotatedUp_source (n : ℕ) :
    (rotatedBranchUp n).source = projection ⁻¹' (rotatedBranchDown n).source := by
  have hcomm (x : Total) : projection ((totalRotIter n).symm x) =
      (sphereRotIter n).symm (projection x) := by
    apply (sphereRotIter n).injective
    rw [(sphereRotIter n).apply_symm_apply, ← atlas_rotation_projection]
    exact congrArg projection ((totalRotIter n).apply_symm_apply x)
  ext x
  simp [rotatedBranchUp, rotatedBranchDown, OpenPartialHomeomorph.trans_source,
    atlas_up_source, atlas_firstDown_source, hcomm]

theorem atlas_rotatedUp_inverse_projection (n : ℕ) (z : ℂ)
    (hz : z ∈ (rotatedBranchUp n).target) :
    projection ((rotatedBranchUp n).symm z) =
      (rotatedBranchDown n).symm (z ^ 2) := by
  let up := rotatedBranchUp n
  let down := rotatedBranchDown n
  have hu : up.symm z ∈ up.source := up.symm.map_source hz
  have hp : projection (up.symm z) ∈ down.source := by
    change up.symm z ∈ projection ⁻¹' down.source
    rw [← atlas_rotatedUp_source n]
    exact hu
  have hs : down (projection (up.symm z)) = z ^ 2 := by
    rw [atlas_rotated_square atlas_up_square n _ hu, up.right_inv hz]
  rw [← hs]
  exact (down.left_inv hp).symm

theorem atlas_rotatedUp_inverse_projection_smooth (n : ℕ) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞
      (projection ∘ (rotatedBranchUp n).symm) (rotatedBranchUp n).target := by
  have hsq : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => z ^ 2) :=
    (contDiff_id.pow 2).contMDiff
  have h := (atlas_rotatedDown_inverse_smooth n).comp hsq.contMDiffOn (s := (rotatedBranchUp n).target) (by
    intro z hz
    have hu := (rotatedBranchUp n).symm.map_source hz
    have hp : projection ((rotatedBranchUp n).symm z) ∈ (rotatedBranchDown n).source :=
      by
        change (rotatedBranchUp n).symm z ∈ (rotatedBranchUp n).source at hu
        rw [atlas_rotatedUp_source] at hu
        exact hu
    have hs := atlas_rotated_square atlas_up_square n _ hu
    rw [(rotatedBranchUp n).right_inv hz] at hs
    change z ^ 2 ∈ (rotatedBranchDown n).target
    rw [← hs]
    exact (rotatedBranchDown n).map_source hp)
  exact h.congr (fun z hz => atlas_rotatedUp_inverse_projection n z hz)
end AlternatingSphereCover

open scoped ContDiff Manifold Topology
namespace AlternatingSphereCover
theorem atlas_sqrt_smooth_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContinuousAt g x)
    (hsq : ∀ᶠ y in 𝓝 x, (g y) ^ 2 = f y) (hnz : g x ≠ 0) :
    ContDiffAt ℝ ∞ g x := by
  let w := g x
  let c : ℂˣ := Units.mk0 (2 * w) (mul_ne_zero (by norm_num) hnz)
  let D : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft c
  have hd : HasFDerivAt (fun z : ℂ => z ^ 2) (D : ℂ →L[ℂ] ℂ) w := by
    convert (hasDerivAt_pow 2 w).hasFDerivAt using 1
    ext z
    simp [D, c]
  have hs : ContDiffAt ℂ ∞ (fun z : ℂ => z ^ 2) w :=
    (contDiff_id.pow 2).contDiffAt
  let e := hs.toOpenPartialHomeomorph (fun z : ℂ => z ^ 2) hd (by simp)
  have hsource : w ∈ e.source := hs.mem_toOpenPartialHomeomorph_source hd (by simp)
  have he : ContDiffAt ℝ ∞ e.symm (w ^ 2) := by
    change ContDiffAt ℝ ∞ (hs.localInverse hd (by simp)) (w ^ 2)
    exact (hs.to_localInverse hd (by simp)).restrict_scalars ℝ
  have hfx : f x = w ^ 2 := (hsq.self_of_nhds).symm
  have hcomp : ContDiffAt ℝ ∞ (e.symm ∘ f) x := by
    apply (hfx ▸ he).comp x hf
  have hmem : g ⁻¹' e.source ∈ 𝓝 x :=
    hg.preimage_mem_nhds (e.open_source.mem_nhds hsource)
  have heq : (e.symm ∘ f) =ᶠ[𝓝 x] g := by
    filter_upwards [hmem, hsq] with y hy hysq
    change e.symm (f y) = g y
    rw [← hysq]
    have : e (g y) = (g y) ^ 2 := rfl
    rw [← this]
    exact e.left_inv hy
  exact hcomp.congr_of_eventuallyEq heq.symm

end AlternatingSphereCover

open scoped Manifold ContDiff Topology
namespace AlternatingSphereCover

theorem atlas_transition_to_branch_at
    (e : OpenPartialHomeomorph Total ℂ) (n : ℕ)
    (hp : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ (projection ∘ e.symm) e.target)
    (z : ℂ) (hz : z ∈ (e.symm.trans (rotatedBranchUp n)).source)
    (hnz : rotatedBranchUp n (e.symm z) ≠ 0) :
    ContDiffAt ℝ ∞ (e.symm.trans (rotatedBranchUp n)) z := by
  let t := e.symm.trans (rotatedBranchUp n)
  have hzt : t.source ∈ 𝓝 z := t.open_source.mem_nhds hz
  have hp' : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞
      (projection ∘ e.symm) t.source := hp.mono (by
    intro y hy
    exact hy.1)
  have hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      ((rotatedBranchDown n) ∘ projection ∘ e.symm) t.source := by
    apply (atlas_rotatedDown_smooth n).comp hp'
    intro y hy
    change projection (e.symm y) ∈ (rotatedBranchDown n).source
    have h := hy.2
    rw [atlas_rotatedUp_source] at h
    exact h
  apply atlas_sqrt_smooth_at (hf.contDiffOn.contDiffAt hzt)
    (t.continuousOn.continuousAt hzt) ?_ hnz
  filter_upwards [hzt] with y hy
  exact (atlas_rotated_square atlas_up_square n (e.symm y) hy.2).symm
end AlternatingSphereCover

open scoped Manifold ContDiff Topology
namespace AlternatingSphereCover

theorem atlas_branch_rot (p : Sphere) : branch (sphereRotation p) ↔ branch p := by
  change branch (sphereRot p) ↔ branch p
  simp only [branch, sphereRot_height, sphereRot_seam, neg_eq_zero]

theorem atlas_branch_rotIter (n : ℕ) (p : Sphere) :
    branch (sphereRotIter n p) ↔ branch p := by
  induction n with
  | zero => rfl
  | succ n ih => exact (atlas_branch_rot _).trans ih

theorem atlas_branch_rotIter_inverse (n : ℕ) (p : Sphere) :
    branch ((sphereRotIter n).symm p) ↔ branch p := by
  have h := atlas_branch_rotIter n ((sphereRotIter n).symm p)
  rw [(sphereRotIter n).apply_symm_apply] at h
  exact h.symm

theorem atlas_patch_branchPoint (i : Fin 6) : branchPoint i ∈ positivePatch ↔ i = 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  fin_cases i <;> norm_num [positivePatch, branchPoint, branchVector] <;> nlinarith

theorem atlas_rotated_patch_branch (i : Fin 6) (p : Sphere)
    (hp : p ∈ (rotatedBranchDown (branchRotationSteps i)).source)
    (hb : branch p) : p = branchPoint i := by
  have hp' : (sphereRotIter (branchRotationSteps i)).symm p ∈ positivePatch := by
    simpa [rotatedBranchDown, atlas_firstDown_source] using hp
  have hb' := (atlas_branch_rotIter_inverse (branchRotationSteps i) p).mpr hb
  obtain ⟨j, hj⟩ := (branch_iff_mem_range _).mp hb'
  have hj0 : j = 0 := (atlas_patch_branchPoint j).mp (hj ▸ hp')
  subst j
  have he := congrArg (sphereRotIter (branchRotationSteps i)) hj
  rw [(sphereRotIter _).apply_symm_apply, atlas_rotation_branchPoint] at he
  exact he.symm

theorem atlas_rotated_branch_center_mem (i : Fin 6) :
    branchPoint i ∈ (rotatedBranchDown (branchRotationSteps i)).source := by
  have hzero : branchPoint 0 ∈ positivePatch := (atlas_patch_branchPoint 0).mpr rfl
  have hrot := atlas_rotation_branchPoint i
  rw [← hrot]
  simpa [rotatedBranchDown, atlas_firstDown_source] using hzero

theorem atlas_up_zero_branch (n : ℕ) (x : Total)
    (hx : x ∈ (rotatedBranchUp n).source) (hz : rotatedBranchUp n x = 0) :
    branch (projection x) := by
  have hp : (sphereRotIter n).symm (projection x) ∈ positivePatch := by
    have hx' : projection x ∈ (rotatedBranchDown n).source := by
      rw [atlas_rotatedUp_source] at hx
      exact hx
    simpa [rotatedBranchDown, atlas_firstDown_source] using hx'
  have hs := atlas_rotated_square atlas_up_square n x hx
  rw [hz, zero_pow (by norm_num : 2 ≠ 0)] at hs
  have hplane : localPlane ((sphereRotIter n).symm (projection x)) = 0 := by
    simpa [rotatedBranchDown, atlas_firstDown_apply _ hp] using hs
  have hre := congrArg Complex.re hplane
  have him := congrArg Complex.im hplane
  apply (atlas_branch_rotIter_inverse n (projection x)).mp
  constructor
  · exact him
  · change _ * (3 * _ ^ 2 - _ ^ 2) = 0
    change ((sphereRotIter n).symm (projection x)).val 1 = 0 at hre
    rw [hre, zero_mul]
end AlternatingSphereCover

set_option maxHeartbeats 1600000
open scoped Manifold ContDiff Topology
namespace AlternatingSphereCover

noncomputable def atlasComplexEuclidean : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.equivRealProdCLM.trans ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 2) ℝ).symm)

noncomputable def atlasRegularDown (p : Sphere) : OpenPartialHomeomorph Sphere ℂ :=
  ((chartAt (EuclideanSpace ℝ (Fin 2)) p).restr (branchFinset : Set Sphere)ᶜ).trans
    atlasComplexEuclidean.symm.toHomeomorph.toOpenPartialHomeomorph

theorem atlas_regularDown_smooth (p : Sphere) :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ (atlasRegularDown p) (atlasRegularDown p).source := by
  have hl : ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ∞ atlasComplexEuclidean.symm :=
    atlasComplexEuclidean.symm.contDiff.contMDiff
  apply (hl.comp_contMDiffOn (contMDiffOn_chart (I := 𝓡 2) (n := ∞))).mono
  intro q hq
  exact hq.1.1

theorem atlas_regularDown_inverse_smooth (p : Sphere) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ (atlasRegularDown p).symm (atlasRegularDown p).target := by
  have hl : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ atlasComplexEuclidean :=
    atlasComplexEuclidean.contDiff.contMDiff
  have hc : ContMDiffOn (𝓡 2) (𝓡 2) ∞
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).symm
      (chartAt (EuclideanSpace ℝ (Fin 2)) p).target := contMDiffOn_chart_symm
  change ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞
    ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm ∘ atlasComplexEuclidean)
    (atlasRegularDown p).target
  apply hc.comp hl.contMDiffOn
  intro z hz
  have hsource := (atlasRegularDown p).symm.map_source hz
  have hdown := (atlasRegularDown p).right_inv hz
  change atlasComplexEuclidean.symm ((chartAt (EuclideanSpace ℝ (Fin 2)) p)
    ((atlasRegularDown p).symm z)) = z at hdown
  have he : (chartAt (EuclideanSpace ℝ (Fin 2)) p) ((atlasRegularDown p).symm z) =
      atlasComplexEuclidean z := by
    exact atlasComplexEuclidean.symm.injective (by simpa using hdown)
  change atlasComplexEuclidean z ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).target
  rw [← he]
  exact (chartAt (EuclideanSpace ℝ (Fin 2)) p).map_source hsource.1.1

theorem atlas_regularDown_source_branchfree (p q : Sphere)
    (hq : q ∈ (atlasRegularDown p).source) : ¬ branch q := by
  have h := interior_subset hq.1.2
  simpa [mem_branchFinset] using h

structure AtlasRegularDatum (x : Total) where
  upstairs : OpenPartialHomeomorph Total ℂ
  downstairs : OpenPartialHomeomorph Sphere ℂ
  mem_source : x ∈ upstairs.source
  down_smooth : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ downstairs downstairs.source
  inverse_smooth : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ downstairs.symm downstairs.target
  projection_mem : ∀ y ∈ upstairs.source, projection y ∈ downstairs.source
  coordinate : ∀ y ∈ upstairs.source, upstairs y = downstairs (projection y)
  branchfree : ∀ y ∈ upstairs.source, ¬ branch (projection y)

noncomputable def atlasRegularDatum (x : Total) (hx : ¬ branch (projection x)) :
    AtlasRegularDatum x := by
  classical
  have hxb : projection x ∈ (branchFinset : Set Sphere)ᶜ := by
    simpa [mem_branchFinset] using hx
  let e := Classical.choose (unbranched_cover.isLocalHomeomorphOn x hxb)
  have he := (Classical.choose_spec (unbranched_cover.isLocalHomeomorphOn x hxb)).1
  have hfe := (Classical.choose_spec (unbranched_cover.isLocalHomeomorphOn x hxb)).2
  let d := atlasRegularDown (projection x)
  have hed : (e : Total → Sphere) = projection := hfe.symm
  have hdx : projection x ∈ d.source := by
    change projection x ∈ ((chartAt (EuclideanSpace ℝ (Fin 2)) (projection x)).restr
      (branchFinset : Set Sphere)ᶜ).source ∩ _
    constructor
    · rw [OpenPartialHomeomorph.restr_source]
      exact ⟨ChartedSpace.mem_chart_source (projection x),
        by simpa only [(branchFinset.finite_toSet.isClosed).isOpen_compl.interior_eq] using hxb⟩
    · trivial
  refine {
    upstairs := e.trans d
    downstairs := d
    mem_source := ⟨he, by simpa [hed] using hdx⟩
    down_smooth := atlas_regularDown_smooth _
    inverse_smooth := atlas_regularDown_inverse_smooth _
    projection_mem := ?_
    coordinate := ?_
    branchfree := ?_ }
  · intro y hy
    simpa [hed] using hy.2
  · intro y hy
    change d (e y) = d (projection y)
    rw [hed]
  · intro y hy
    apply atlas_regularDown_source_branchfree (projection x)
    simpa [hed] using hy.2

end AlternatingSphereCover

open scoped Manifold ContDiff Topology
set_option maxHeartbeats 1600000
namespace AlternatingSphereCover

theorem atlas_regular_inverse_projection (x : Total) (d : AtlasRegularDatum x)
    (z : ℂ) (hz : z ∈ d.upstairs.target) :
    projection (d.upstairs.symm z) = d.downstairs.symm z := by
  have hu := d.upstairs.symm.map_source hz
  have hp := d.projection_mem _ hu
  have he := d.coordinate _ hu
  rw [d.upstairs.right_inv hz] at he
  calc
    projection (d.upstairs.symm z) = d.downstairs.symm (d.downstairs (projection (d.upstairs.symm z))) := (d.downstairs.left_inv hp).symm
    _ = d.downstairs.symm z := congrArg d.downstairs.symm he.symm

theorem atlas_regular_inverse_projection_smooth (x : Total) (d : AtlasRegularDatum x) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ (projection ∘ d.upstairs.symm) d.upstairs.target := by
  have h := d.inverse_smooth.mono (by
    intro z hz
    have hu := d.upstairs.symm.map_source hz
    have hp := d.projection_mem _ hu
    have he := d.coordinate _ hu
    rw [d.upstairs.right_inv hz] at he
    rw [he]
    exact d.downstairs.map_source hp)
  exact h.congr (fun z hz => atlas_regular_inverse_projection x d z hz)

theorem atlas_transition_to_regular_at
    (e : OpenPartialHomeomorph Total ℂ) (x : Total) (d : AtlasRegularDatum x)
    (hp : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞ (projection ∘ e.symm) e.target)
    (z : ℂ) (hz : z ∈ (e.symm.trans d.upstairs).source) :
    ContDiffAt ℝ ∞ (e.symm.trans d.upstairs) z := by
  let t := e.symm.trans d.upstairs
  have hzt : t.source ∈ 𝓝 z := t.open_source.mem_nhds hz
  have h : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (d.downstairs ∘ projection ∘ e.symm) t.source := by
    apply d.down_smooth.comp (hp.mono (fun y hy => hy.1))
    intro y hy
    exact d.projection_mem _ hy.2
  have he : (t : ℂ → ℂ) =ᶠ[𝓝 z] (d.downstairs ∘ projection ∘ e.symm) := by
    filter_upwards [hzt] with y hy
    exact d.coordinate _ hy.2
  exact (h.contDiffOn.contDiffAt hzt).congr_of_eventuallyEq he

noncomputable def atlasBranchIndex (p : Sphere) (hp : branch p) : Fin 6 :=
  Classical.choose ((branch_iff_mem_range p).mp hp)

theorem atlasBranchIndex_eq (p : Sphere) (hp : branch p) :
    branchPoint (atlasBranchIndex p hp) = p :=
  Classical.choose_spec ((branch_iff_mem_range p).mp hp)

noncomputable def atlasComplexChart (x : Total) : OpenPartialHomeomorph Total ℂ := by
  classical
  exact if hx : branch (projection x) then
    rotatedBranchUp (branchRotationSteps (atlasBranchIndex (projection x) hx))
  else (atlasRegularDatum x hx).upstairs

theorem atlasComplexChart_mem (x : Total) : x ∈ (atlasComplexChart x).source := by
  classical
  by_cases hx : branch (projection x)
  · simp only [atlasComplexChart, dif_pos hx]
    rw [atlas_rotatedUp_source]
    change projection x ∈ (rotatedBranchDown (branchRotationSteps (atlasBranchIndex (projection x) hx))).source
    have hc := atlas_rotated_branch_center_mem (atlasBranchIndex (projection x) hx)
    simpa only [atlasBranchIndex_eq] using hc
  · simp only [atlasComplexChart, dif_neg hx]
    exact (atlasRegularDatum x hx).mem_source

theorem atlasComplexChart_projection_smooth (x : Total) :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 2) ∞
      (projection ∘ (atlasComplexChart x).symm) (atlasComplexChart x).target := by
  classical
  by_cases hx : branch (projection x)
  · simp only [atlasComplexChart, dif_pos hx]
    exact atlas_rotatedUp_inverse_projection_smooth _
  · simp only [atlasComplexChart, dif_neg hx]
    exact atlas_regular_inverse_projection_smooth _ _

theorem atlas_transition_same (e : OpenPartialHomeomorph Total ℂ) :
    ContDiffOn ℝ ∞ (e.symm.trans e) (e.symm.trans e).source := by
  apply contDiffOn_id.congr
  intro z hz
  exact e.right_inv hz.1



theorem atlasComplexChart_transitions (x y : Total) :
    ContDiffOn ℝ ∞ ((atlasComplexChart x).symm.trans (atlasComplexChart y))
      ((atlasComplexChart x).symm.trans (atlasComplexChart y)).source := by
  classical
  let e := atlasComplexChart x
  let f := atlasComplexChart y
  let t := e.symm.trans f
  intro z hz
  change z ∈ t.source at hz
  have hz1 : z ∈ e.target := hz.1
  have hz2 : e.symm z ∈ f.source := hz.2
  suffices ContDiffAt ℝ ∞ t z from this.contDiffWithinAt
  by_cases hy : branch (projection y)
  · let j := atlasBranchIndex (projection y) hy
    have hf : f = rotatedBranchUp (branchRotationSteps j) := by
      simp [f, atlasComplexChart, hy, j]
    by_cases hnz : f (e.symm z) ≠ 0
    · have h := atlas_transition_to_branch_at e (branchRotationSteps j)
        (atlasComplexChart_projection_smooth x) z
        (by simpa only [← hf] using hz) (by simpa only [← hf] using hnz)
      simpa only [t, hf] using h
    · have hb : branch (projection (e.symm z)) := by
        apply atlas_up_zero_branch (branchRotationSteps j) _
        · simpa only [← hf] using hz2
        · simpa only [← hf] using not_ne_iff.mp hnz
      by_cases hx : branch (projection x)
      · let i := atlasBranchIndex (projection x) hx
        have he : e = rotatedBranchUp (branchRotationSteps i) := by
          simp [e, atlasComplexChart, hx, i]
        have hp_i : projection (e.symm z) = branchPoint i := by
          apply atlas_rotated_patch_branch i _ _ hb
          have hmem : e.symm z ∈ (rotatedBranchUp (branchRotationSteps i)).source := by
            have hm : e.symm z ∈ e.source := e.symm.map_source hz1
            simpa only [← he] using hm
          rw [atlas_rotatedUp_source] at hmem
          exact hmem
        have hp_j : projection (e.symm z) = branchPoint j := by
          apply atlas_rotated_patch_branch j _ _ hb
          have hmem := hz2
          rw [hf, atlas_rotatedUp_source] at hmem
          exact hmem
        have hij : i = j := branchPoint_injective (hp_i.symm.trans hp_j)
        have hef : e = f := by rw [he, hf, hij]
        have hsame := atlas_transition_same e
        have hsm : ContDiffOn ℝ ∞ t t.source := by simpa only [t, hef] using hsame
        exact hsm.contDiffAt (t.open_source.mem_nhds hz)
      · have he : e = (atlasRegularDatum x hx).upstairs := by
          simp [e, atlasComplexChart, hx]
        have hmem : e.symm z ∈ (atlasRegularDatum x hx).upstairs.source := by
          have hm : e.symm z ∈ e.source := e.symm.map_source hz1
          simpa only [← he] using hm
        exact ((atlasRegularDatum x hx).branchfree _ hmem hb).elim
  · have hf : f = (atlasRegularDatum y hy).upstairs := by
      simp [f, atlasComplexChart, hy]
    have h := atlas_transition_to_regular_at e y (atlasRegularDatum y hy)
      (atlasComplexChart_projection_smooth x) z (by simpa only [← hf] using hz)
    simpa only [t, hf] using h

end AlternatingSphereCover

open scoped Manifold ContDiff Topology
set_option maxHeartbeats 1600000
namespace AlternatingSphereCover

noncomputable def atlasEuclideanChart (x : Total) :
    OpenPartialHomeomorph Total (EuclideanSpace ℝ (Fin 2)) :=
  (atlasComplexChart x).trans atlasComplexEuclidean.toHomeomorph.toOpenPartialHomeomorph

theorem atlasEuclideanChart_mem (x : Total) : x ∈ (atlasEuclideanChart x).source := by
  exact ⟨atlasComplexChart_mem x, trivial⟩

theorem atlasEuclideanChart_transitions (x y : Total) :
    ContDiffOn ℝ ∞ ((atlasEuclideanChart x).symm.trans (atlasEuclideanChart y))
      ((atlasEuclideanChart x).symm.trans (atlasEuclideanChart y)).source := by
  let e := atlasComplexChart x
  let f := atlasComplexChart y
  let t := e.symm.trans f
  let ex := atlasEuclideanChart x
  let fy := atlasEuclideanChart y
  have h : ContDiffOn ℝ ∞ (atlasComplexEuclidean ∘ t ∘ atlasComplexEuclidean.symm)
      (atlasComplexEuclidean.symm ⁻¹' t.source) := by
    apply atlasComplexEuclidean.contDiff.comp_contDiffOn
    exact (atlasComplexChart_transitions x y).comp
      atlasComplexEuclidean.symm.contDiff.contDiffOn (fun z hz => hz)
  change ContDiffOn ℝ ∞ (atlasComplexEuclidean ∘ t ∘ atlasComplexEuclidean.symm)
    (ex.symm.trans fy).source
  apply h.mono
  intro z hz
  change z ∈ (ex.symm.trans fy).source at hz
  have h1 : atlasComplexEuclidean.symm z ∈ e.target := hz.1.2
  have h2 : e.symm (atlasComplexEuclidean.symm z) ∈ f.source := hz.2.1
  exact ⟨h1, h2⟩

end AlternatingSphereCover


/-!
Statement-review scaffold for the actual alternating-sphere quotient.
These declarations are proposed obligations, not proved results. In particular,
the smooth-manifold claim requires transition-map proofs not supplied by the
topological branch charts or the unbranched covering theorem alone.
-/

namespace AlternatingSphereCover

open CurveComplex
open scoped Manifold ContDiff

abbrev Euclidean2 := EuclideanSpace ℝ (Fin 2)

/-- A covering family of concrete Euclidean charts whose transitions are smooth. -/
def CompatibleEuclideanCharts
    (charts : Total → OpenPartialHomeomorph Total Euclidean2) : Prop :=
  (∀ x, x ∈ (charts x).source) ∧
  (∀ x y,
    ContDiffOn ℝ ∞ ((𝓡 2) ∘ (charts x).symm ≫ₕ (charts y) ∘ (𝓡 2).symm)
      ((𝓡 2).symm ⁻¹' ((charts x).symm ≫ₕ (charts y)).source ∩ Set.range (𝓡 2)))

/-- The actual regular and branch charts admit a common compatible selection. -/
theorem actual_compatibleEuclideanCharts :
    ∃ charts : Total → OpenPartialHomeomorph Total Euclidean2,
      CompatibleEuclideanCharts charts := by
  refine ⟨atlasEuclideanChart, atlasEuclideanChart_mem, ?_⟩
  intro x y
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Set.range_id, Set.preimage_id_eq, Set.inter_univ, Function.id_comp, Function.comp_id, id_eq] using
    atlasEuclideanChart_transitions x y

noncomputable def actualCharts : Total → OpenPartialHomeomorph Total Euclidean2 :=
  Classical.choose actual_compatibleEuclideanCharts

/-- The atlas selected from the concrete local Euclidean charts. -/
@[instance_reducible]
noncomputable def actualChartedSpace : ChartedSpace Euclidean2 Total where
  atlas := Set.range actualCharts
  chartAt x := actualCharts x
  mem_chart_source x := (Classical.choose_spec actual_compatibleEuclideanCharts).1 x
  chart_mem_atlas x := ⟨x, rfl⟩

noncomputable local instance : ChartedSpace Euclidean2 Total := actualChartedSpace

/-- Hausdorffness of the actual quotient topology. -/
theorem actual_t2Space : T2Space Total := by
  classical
  refine ⟨?_⟩
  intro x y hxy
  by_cases hbase : projection x = projection y
  · have hnb : ¬ branch (projection x) := by
      intro hb
      obtain ⟨z, hz, hu⟩ := branch_fiber_unique hb
      exact hxy ((hu x rfl).trans (hu y hbase.symm).symm)
    have hmem : projection x ∈ (branchFinset : Set Sphere)ᶜ := by
      simpa [mem_branchFinset] using hnb
    obtain ⟨hdisc, U, hbU, hU, hpU, H, hH⟩ := unbranched_cover (projection x) hmem
    have hxU : x ∈ projection ⁻¹' U := hbU
    have hyU : y ∈ projection ⁻¹' U := by change projection y ∈ U; rwa [← hbase]
    let ix := (H ⟨x, hxU⟩).2
    let iy := (H ⟨y, hyU⟩).2
    have hine : ix ≠ iy := by
      intro heq
      have he : H ⟨x, hxU⟩ = H ⟨y, hyU⟩ := by
        apply Prod.ext
        · exact Subtype.ext (by simpa [hH] using hbase)
        · exact heq
      exact hxy (congrArg Subtype.val (H.injective he))
    let A : Set (projection ⁻¹' U) := H ⁻¹' (Set.univ ×ˢ {ix})
    let B : Set (projection ⁻¹' U) := H ⁻¹' (Set.univ ×ˢ {iy})
    have hA : IsOpen A :=
      (isOpen_univ.prod (isOpen_discrete {ix})).preimage H.continuous
    have hB : IsOpen B :=
      (isOpen_univ.prod (isOpen_discrete {iy})).preimage H.continuous
    refine ⟨Subtype.val '' A, Subtype.val '' B,
      hpU.isOpenMap_subtype_val A hA, hpU.isOpenMap_subtype_val B hB, ?_, ?_, ?_⟩
    · exact ⟨⟨x, hxU⟩, by simp [A, ix], rfl⟩
    · exact ⟨⟨y, hyU⟩, by simp [B, iy], rfl⟩
    · apply Set.disjoint_left.mpr
      rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have hEq : a = b := Subtype.ext hab.symm
      subst b
      have hix : (H a).2 = ix := by simpa [A] using ha.2
      have hiy : (H a).2 = iy := by simpa [B] using hb.2
      exact hine (hix.symm.trans hiy)
  · obtain ⟨A, B, hA, hB, ha, hb, hd⟩ := t2_separation hbase
    refine ⟨projection ⁻¹' A, projection ⁻¹' B,
      hA.preimage projection_continuous, hB.preimage projection_continuous,
      ha, hb, ?_⟩
    exact hd.preimage _

/-- Connectedness of the actual quotient topology. -/
theorem actual_connectedSpace : ConnectedSpace Total := by
  classical
  have branch_local_open (x : Total)
      (c : CurveComplex.SquareBranchChart Total Sphere projection x)
      (A : Set Total) (hA : IsOpen A) :
      IsOpen (projection '' (A ∩ c.upstairs.source)) := by
    let V : Set ℂ := c.upstairs '' (A ∩ c.upstairs.source)
    let W : Set ℂ := (fun z : ℂ => z ^ 2) '' V
    have hV : IsOpen V := by
      simpa only [V, Set.inter_comm] using c.upstairs.isOpen_image_source_inter hA
    have hW : IsOpen W := (Complex.isOpenQuotientMap_pow 2).isOpenMap V hV
    have hWt : W ⊆ c.downstairs.target := by
      rintro w ⟨u, ⟨z, ⟨hzA, hzS⟩, rfl⟩, rfl⟩
      change (c.upstairs z) ^ 2 ∈ c.downstairs.target
      rw [← c.square z hzS]
      exact c.downstairs.map_source' (c.image_mem z hzS)
    have heq : projection '' (A ∩ c.upstairs.source) = c.downstairs.symm '' W := by
      ext b
      constructor
      · rintro ⟨z, ⟨hzA, hzS⟩, rfl⟩
        refine ⟨c.downstairs (projection z), ?_, ?_⟩
        · exact ⟨c.upstairs z, ⟨z, ⟨hzA, hzS⟩, rfl⟩, (c.square z hzS).symm⟩
        · exact c.downstairs.left_inv (c.image_mem z hzS)
      · rintro ⟨w, ⟨u, ⟨z, ⟨hzA, hzS⟩, huz⟩, hwu⟩, hbw⟩
        refine ⟨z, ⟨hzA, hzS⟩, ?_⟩
        rw [← hbw]
        have he : w = c.downstairs (projection z) := by
          calc
            w = u ^ 2 := hwu.symm
            _ = (c.upstairs z) ^ 2 := by rw [huz]
            _ = c.downstairs (projection z) := (c.square z hzS).symm
        rw [he]
        exact (c.downstairs.left_inv (c.image_mem z hzS)).symm
    rw [heq]
    exact c.downstairs.isOpen_image_symm_of_subset_target hW hWt
  have hopen : IsOpenMap projection := by
    intro A hA
    apply isOpen_iff_forall_mem_open.mpr
    rintro b ⟨x, hxA, rfl⟩
    by_cases hb : branch (projection x)
    · obtain ⟨c⟩ := exists_squareBranchChart x hb
      refine ⟨projection '' (A ∩ c.upstairs.source),
        Set.image_mono Set.inter_subset_left, branch_local_open x c A hA, ?_⟩
      exact ⟨x, ⟨hxA, c.upstairs_mem⟩, rfl⟩
    · have hmem : projection x ∈ (branchFinset : Set Sphere)ᶜ := by
        simpa [mem_branchFinset] using hb
      obtain ⟨e, he, hfe⟩ := unbranched_cover.isLocalHomeomorphOn x hmem
      refine ⟨projection '' (A ∩ e.source), Set.image_mono Set.inter_subset_left, ?_, ?_⟩
      · rw [hfe]
        simpa only [Set.inter_comm] using e.isOpen_image_source_inter hA
      · exact ⟨x, ⟨hxA, he⟩, rfl⟩
  letI : CompactSpace Total := total_compact
  have hr : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp only [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  letI : ConnectedSpace Sphere :=
    Subtype.connectedSpace (isConnected_sphere hr 0 (by norm_num))
  rw [connectedSpace_iff_clopen]
  constructor
  · obtain ⟨x, _⟩ := projection_surjective (branchPoint 0)
    exact ⟨x⟩
  intro s hs
  by_cases hempty : s = ∅
  · exact Or.inl hempty
  right
  by_contra hproper
  have hsne : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  have hcne : sᶜ.Nonempty := Set.nonempty_compl.mpr hproper
  have hclosed : IsClosedMap projection := projection_continuous.isClosedMap
  have himg : IsClopen (projection '' s) := ⟨hclosed s hs.1, hopen s hs.2⟩
  have himgc : IsClopen (projection '' sᶜ) :=
    ⟨hclosed sᶜ hs.compl.1, hopen sᶜ hs.compl.2⟩
  have hall : projection '' s = Set.univ := himg.eq_univ (hsne.image projection)
  have hallc : projection '' sᶜ = Set.univ := himgc.eq_univ (hcne.image projection)
  obtain ⟨x, hx, hpx⟩ : ∃ x, x ∈ s ∧ projection x = branchPoint 0 := by
    have h : branchPoint 0 ∈ projection '' s := by rw [hall]; trivial
    exact h
  obtain ⟨y, hy, hpy⟩ : ∃ y, y ∈ sᶜ ∧ projection y = branchPoint 0 := by
    have h : branchPoint 0 ∈ projection '' sᶜ := by rw [hallc]; trivial
    exact h
  have hb : branch (branchPoint 0) :=
    (branch_iff_mem_range _).mpr ⟨0, rfl⟩
  obtain ⟨z, hz, hu⟩ := branch_fiber_unique hb
  have hxy : x = y := (hu x hpx).trans (hu y hpy).symm
  exact hy (hxy ▸ hx)

theorem actual_isManifold : IsManifold (𝓡 2) ∞ Total := by
  apply isManifold_of_contDiffOn (𝓡 2) ∞ Total
  intro e e' he he'
  obtain ⟨x, rfl⟩ := he
  obtain ⟨y, rfl⟩ := he'
  exact (Classical.choose_spec actual_compatibleEuclideanCharts).2 x y

/-- The actual alternating-sphere quotient is a smooth closed surface. -/
theorem actualClosedSurface : ClosedSurface Total :=
  { toT2Space := actual_t2Space
    toCompactSpace := total_compact
    toConnectedSpace := actual_connectedSpace
    toIsManifold := actual_isManifold }

end AlternatingSphereCover

