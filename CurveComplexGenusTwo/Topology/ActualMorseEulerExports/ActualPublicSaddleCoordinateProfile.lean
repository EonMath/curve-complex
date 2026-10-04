import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseStatements
import CurveComplexGenusTwo.CWHurewicz.MVComplex
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Contractible
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualPublicPairHomeomorphTransport

open scoped Manifold
open CategoryTheory CategoryTheory.Limits

private theorem mvAmbientHomologySum_zero_isIso_of_disjoint_homology_zero
    (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hzero : IsZero ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex
      X (U ∩ V)).homology 0)) :
    IsIso (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V 0) := by
  letI : Mono (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V 0) :=
    (CurveComplexGenusTwo.CWHurewicz.mvAmbient_exact_pair
      X U V hU hV hcover 0).mono_g (hzero.eq_of_src _ _)
  letI : Epi (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V 0) :=
    CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum_zero_epi
      X U V hU hV hcover
  exact isIso_of_mono_of_epi _

open scoped Simplicial in
private theorem mvOrdinaryComplex_intersection_homology_zero
    (X : TopCat) (U V : Set X) (hdisjoint : Disjoint U V) (n : ℕ) :
    IsZero ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex
      X (U ∩ V)).homology n) := by
  have hempty : IsEmpty (↥(U ∩ V)) :=
    ⟨fun x => (Set.disjoint_left.mp hdisjoint) x.property.1 x.property.2⟩
  have hsimplex : IsEmpty ((TopCat.toSSet.obj (TopCat.of (↥(U ∩ V)))) _⦋n⦌) :=
    ⟨fun s => hempty.false ((TopCat.toSSetObjEquiv (TopCat.of (↥(U ∩ V))) _ s).1 default)⟩
  letI := hsimplex
  have hzero : IsZero ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex
      X (U ∩ V)).X n) := by
    letI : Subsingleton ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex
        X (U ∩ V)).X n) := by
      change Subsingleton (CurveComplexGenusTwo.CWHurewicz.coverOrdinaryChains X (U ∩ V) n)
      exact ⟨fun f g => Finsupp.ext (fun a => isEmptyElim a)⟩
    exact ModuleCat.isZero_of_subsingleton _
  exact (HomologicalComplex.ExactAt.of_isZero hzero).isZero_homology

private theorem mvAmbientHomologySum_zero_isIso_of_disjoint
    (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hdisjoint : Disjoint U V) :
    IsIso (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V 0) :=
  mvAmbientHomologySum_zero_isIso_of_disjoint_homology_zero
    X U V hU hV hcover
    (mvOrdinaryComplex_intersection_homology_zero X U V hdisjoint 0)

private theorem mvAmbientHomologySum_positive_isIso_of_disjoint
    (X : TopCat) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hdisjoint : Disjoint U V) (n : ℕ) :
    IsIso (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V (n + 1)) := by
  have hnow := mvOrdinaryComplex_intersection_homology_zero X U V hdisjoint (n + 1)
  have hprev := mvOrdinaryComplex_intersection_homology_zero X U V hdisjoint n
  letI : Mono (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V (n + 1)) :=
    (CurveComplexGenusTwo.CWHurewicz.mvAmbient_exact_pair
      X U V hU hV hcover (n + 1)).mono_g (hnow.eq_of_src _ _)
  letI : Epi (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V (n + 1)) :=
    (CurveComplexGenusTwo.CWHurewicz.mvAmbient_exact_ambient
      X U V hU hV hcover n).epi_f (hprev.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private def nestedSubtypeHomeomorph
    (E : Type) [TopologicalSpace E] (S A : Set E) (hAS : A ⊆ S) :
    {x : S | (x : E) ∈ A} ≃ₜ A where
  toFun x := ⟨(x : E), x.property⟩
  invFun x := ⟨⟨x.val, hAS x.property⟩, x.property⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem augmentation_epi_of_nonempty
    (Y : Type) [TopologicalSpace Y] [Nonempty Y] :
    Epi ((TopCat.of Y).singularHomology₀ε (ModuleCat.of ℤ ℤ)) := by
  let RZ := ModuleCat.of ℤ ℤ
  let T := TopCat.of Y
  let y : Y := Classical.choice inferInstance
  let i : ZerothHomotopy T := ZerothHomotopy.mk y
  let s : RZ ⟶ CurveComplexGenusTwo.CWHurewicz.H Y 0 :=
    Sigma.ι (fun _ : ZerothHomotopy T => RZ) i ≫
      (T.singularHomology₀Iso RZ).inv
  have hs : s ≫ T.singularHomology₀ε RZ = 𝟙 RZ := by
    dsimp [s]
    rw [← T.singularHomology₀Iso_sigma_desc_id RZ]
    calc
      ((Sigma.ι (fun _ : ZerothHomotopy T => RZ) i ≫
          (T.singularHomology₀Iso RZ).inv) ≫
          (T.singularHomology₀Iso RZ).hom) ≫
          Sigma.desc (fun _ : ZerothHomotopy T => 𝟙 RZ) =
        (Sigma.ι (fun _ : ZerothHomotopy T => RZ) i ≫
          ((T.singularHomology₀Iso RZ).inv ≫
            (T.singularHomology₀Iso RZ).hom)) ≫
          Sigma.desc (fun _ : ZerothHomotopy T => 𝟙 RZ) := by
            congr 1
      _ = 𝟙 RZ := by simp
  exact epi_of_epi_fac hs

private theorem homologyInclusion_zero_epi_of_nonempty_pathConnected
    (Y : Type) [TopologicalSpace Y] [PathConnectedSpace Y]
    (A : Set Y) [Nonempty A] :
    Epi (CurveComplexGenusTwo.CWHurewicz.homologyInclusion Y A 0) := by
  let RZ := ModuleCat.of ℤ ℤ
  letI : Epi ((TopCat.of A).singularHomology₀ε RZ) :=
    augmentation_epi_of_nonempty A
  letI : IsIso ((TopCat.of Y).singularHomology₀ε RZ) := inferInstance
  have hnat := CircleHomologyComputation.augmentation_naturality
    (CurveComplexGenusTwo.CWHurewicz.pairInclusion Y A)
  change CurveComplexGenusTwo.CWHurewicz.homologyInclusion Y A 0 ≫
    (TopCat.of Y).singularHomology₀ε RZ =
    (TopCat.of A).singularHomology₀ε RZ at hnat
  have heq : CurveComplexGenusTwo.CWHurewicz.homologyInclusion Y A 0 =
      (TopCat.of A).singularHomology₀ε RZ ≫
        (CategoryTheory.asIso ((TopCat.of Y).singularHomology₀ε RZ)).inv := by
    apply (cancel_mono ((TopCat.of Y).singularHomology₀ε RZ)).mp
    simp [hnat, Category.assoc]
  rw [heq]
  infer_instance

private def morseQuadratic (k : Fin 3) (z : ℂ) : ℝ :=
  if k = 0 then z.re ^ 2 + z.im ^ 2
  else if k = 1 then z.re ^ 2 - z.im ^ 2
  else -(z.re ^ 2 + z.im ^ 2)

private theorem morseQuadratic_saddle (z : ℂ) :
    morseQuadratic 1 z = z.re ^ 2 - z.im ^ 2 := by
  simp [morseQuadratic]

private def actualMorseChartSublevel
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (k : Fin 3) (ρ c : ℝ) : Set E :=
  {x | x ∈ (chartAt ℂ p).source ∧
    ‖(chartAt ℂ p) x - (chartAt ℂ p) p‖ ≤ ρ ∧
    morseQuadratic k ((chartAt ℂ p) x - (chartAt ℂ p) p) ≤ c}

private theorem actualMorseChartSublevel_image
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (k : Fin 3) (ρ c : ℝ) :
    (chartAt ℂ p) '' actualMorseChartSublevel E p k ρ c =
    {z | z ∈ (chartAt ℂ p).target ∧
      ‖z - (chartAt ℂ p) p‖ ≤ ρ ∧
      morseQuadratic k (z - (chartAt ℂ p) p) ≤ c} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(chartAt ℂ p).map_source hx.1, hx.2⟩
  · intro hz
    refine ⟨(chartAt ℂ p).symm z, ?_, ?_⟩
    · refine ⟨(chartAt ℂ p).symm.map_source hz.1, ?_, ?_⟩
      · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.1
      · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.2
    · exact (chartAt ℂ p).right_inv hz.1

private noncomputable def actualMorseChartSublevel_homeomorph
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (k : Fin 3) (ρ c : ℝ) :
    actualMorseChartSublevel E p k ρ c ≃ₜ
      {z : ℂ | z ∈ (chartAt ℂ p).target ∧
        ‖z - (chartAt ℂ p) p‖ ≤ ρ ∧
        morseQuadratic k (z - (chartAt ℂ p) p) ≤ c} :=
  (chartAt ℂ p).homeomorphOfImageSubsetSource
    (by intro x hx; exact hx.1)
    (actualMorseChartSublevel_image E p k ρ c)

private theorem contractible_singular_h0_finrank_one
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H X 0) = 1 := by
  let i := CategoryTheory.asIso
    ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))
  calc
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H X 0) =
      Module.finrank ℤ ℤ := i.toLinearEquiv.finrank_eq
    _ = 1 := by simp

private theorem morseQuadratic_saddle_negative_im_ne_zero
    (z : ℂ) (c : ℝ) (hc : c < 0)
    (hz : morseQuadratic 1 z ≤ c) : z.im ≠ 0 := by
  intro him
  rw [morseQuadratic_saddle, him] at hz
  nlinarith [sq_nonneg z.re]

private def saddleUpper (ρ c : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ ρ ∧ morseQuadratic 1 z ≤ c ∧ 0 < z.im}

private theorem saddleUpper_starConvex
    (ρ c : ℝ) (hρ : 0 < ρ) (hanchorq : -(ρ ^ 2) ≤ c) :
    StarConvex ℝ ((ρ : ℂ) * Complex.I) (saddleUpper ρ c) := by
  intro z hz a b ha hb hab
  have hbn : b ≤ 1 := by linarith
  have hanchor_norm : ‖(ρ : ℂ) * Complex.I‖ = ρ := by
    simp [norm_mul, abs_of_pos hρ]
  have hanchor_re : ((ρ : ℂ) * Complex.I).re = 0 := by simp
  have hanchor_im : ((ρ : ℂ) * Complex.I).im = ρ := by simp
  let w : ℂ := a • ((ρ : ℂ) * Complex.I) + b • z
  have hanchor_ball : ((ρ : ℂ) * Complex.I) ∈ Metric.closedBall (0 : ℂ) ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right, hanchor_norm, abs_of_pos hρ]
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
  have hw_ball : w ∈ Metric.closedBall (0 : ℂ) ρ :=
    (convex_closedBall (0 : ℂ) ρ) hanchor_ball hz_ball ha hb hab
  have hw_norm : ‖w‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hw_ball
  have hw_re : w.re = b * z.re := by
    simp [w, Complex.add_re, Complex.smul_re, hanchor_re]
  have hw_im : w.im = a * ρ + b * z.im := by
    simp [w, Complex.add_im, Complex.smul_im, hanchor_im]
  have hzy : z.im ≤ ρ := (Complex.im_le_norm z).trans hz.1
  have hwy : z.im ≤ w.im := by
    rw [hw_im]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hzy)]
  have hwp : 0 < w.im := lt_of_lt_of_le hz.2.2 hwy
  have hbx : b ^ 2 ≤ (1 : ℝ) := by nlinarith [sq_nonneg b]
  have hxsq : w.re ^ 2 ≤ z.re ^ 2 := by
    rw [hw_re]
    nlinarith [mul_nonneg (sub_nonneg.mpr hbx) (sq_nonneg z.re)]
  have hysq : z.im ^ 2 ≤ w.im ^ 2 :=
    (sq_le_sq₀ (le_of_lt hz.2.2) (le_of_lt hwp)).mpr hwy
  have hzq : z.re ^ 2 - z.im ^ 2 ≤ c := by
    simpa only [morseQuadratic_saddle] using hz.2.1
  refine ⟨hw_norm, ?_, hwp⟩
  rw [morseQuadratic_saddle]
  nlinarith

private theorem saddleUpper_contractible
    (ρ c : ℝ) (hρ : 0 < ρ) (hanchorq : -(ρ ^ 2) ≤ c) :
    ContractibleSpace (saddleUpper ρ c) := by
  have hanchor : ((ρ : ℂ) * Complex.I) ∈ saddleUpper ρ c := by
    refine ⟨?_, ?_, ?_⟩
    · simp [abs_of_pos hρ]
    · simpa [morseQuadratic_saddle] using hanchorq
    · simpa using hρ
  exact (saddleUpper_starConvex ρ c hρ hanchorq).contractibleSpace ⟨_, hanchor⟩

private def saddleLower (ρ c : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ ρ ∧ morseQuadratic 1 z ≤ c ∧ z.im < 0}

private def complexNegHomeomorph : ℂ ≃ₜ ℂ where
  toFun := fun z => -z
  invFun := fun z => -z
  left_inv := neg_neg
  right_inv := neg_neg
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

private noncomputable def saddleUpperLowerHomeomorph (ρ c : ℝ) :
    saddleUpper ρ c ≃ₜ saddleLower ρ c :=
  complexNegHomeomorph.subtype (fun z => by
    change z ∈ saddleUpper ρ c ↔ -z ∈ saddleLower ρ c
    constructor
    · intro hz
      have hq : morseQuadratic 1 (-z) = morseQuadratic 1 z := by
        simp [morseQuadratic_saddle]
      exact ⟨by simpa using hz.1, by simpa [hq] using hz.2.1, by simpa using hz.2.2⟩
    · intro hz
      have hq : morseQuadratic 1 (-z) = morseQuadratic 1 z := by
        simp [morseQuadratic_saddle]
      exact ⟨by simpa using hz.1, by simpa [hq] using hz.2.1, by simpa using hz.2.2⟩)

private theorem saddleLower_contractible
    (ρ c : ℝ) (hρ : 0 < ρ) (hanchorq : -(ρ ^ 2) ≤ c) :
    ContractibleSpace (saddleLower ρ c) := by
  letI := saddleUpper_contractible ρ c hρ hanchorq
  exact (saddleUpperLowerHomeomorph ρ c).symm.contractibleSpace

private def actualSaddleUpper
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) : Set E :=
  {x | x ∈ actualMorseChartSublevel E p 1 ρ c ∧
    0 < ((chartAt ℂ p) x - (chartAt ℂ p) p).im}

private def actualSaddleLower
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) : Set E :=
  {x | x ∈ actualMorseChartSublevel E p 1 ρ c ∧
    ((chartAt ℂ p) x - (chartAt ℂ p) p).im < 0}

private theorem actualSaddleUpper_image
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) :
    (chartAt ℂ p) '' actualSaddleUpper E p ρ c =
    {z | z ∈ (chartAt ℂ p).target ∧
      ‖z - (chartAt ℂ p) p‖ ≤ ρ ∧
      morseQuadratic 1 (z - (chartAt ℂ p) p) ≤ c ∧
      0 < (z - (chartAt ℂ p) p).im} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(chartAt ℂ p).map_source hx.1.1,
      hx.1.2.1, hx.1.2.2, hx.2⟩
  · intro hz
    refine ⟨(chartAt ℂ p).symm z, ?_, (chartAt ℂ p).right_inv hz.1⟩
    refine ⟨?_, ?_⟩
    · refine ⟨(chartAt ℂ p).symm.map_source hz.1, ?_, ?_⟩
      · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.1
      · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.2.1
    · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.2.2

private noncomputable def actualSaddleUpper_homeomorph
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    actualSaddleUpper E p ρ c ≃ₜ saddleUpper ρ c :=
  ((chartAt ℂ p).homeomorphOfImageSubsetSource
    (by intro x hx; exact hx.1.1)
    (actualSaddleUpper_image E p ρ c)).trans <|
    (Homeomorph.addLeft (-(chartAt ℂ p) p)).subtype (fun z => by
      change (z ∈ (chartAt ℂ p).target ∧
        ‖z - (chartAt ℂ p) p‖ ≤ ρ ∧
        morseQuadratic 1 (z - (chartAt ℂ p) p) ≤ c ∧
        0 < (z - (chartAt ℂ p) p).im) ↔
        -(chartAt ℂ p) p + z ∈ saddleUpper ρ c
      have hz : -(chartAt ℂ p) p + z = z - (chartAt ℂ p) p := by abel
      rw [hz]
      constructor
      · intro h
        exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
      · intro h
        have hb : z ∈ Metric.closedBall ((chartAt ℂ p) p) ρ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using h.1
        exact ⟨htarget hb, h.1, h.2.1, h.2.2⟩)

private theorem actualSaddleUpper_contractible
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 < ρ) (hc : -(ρ ^ 2) ≤ c)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    ContractibleSpace (actualSaddleUpper E p ρ c) := by
  letI := saddleUpper_contractible ρ c hρ hc
  exact (actualSaddleUpper_homeomorph E p ρ c htarget).contractibleSpace

private theorem actualSaddleLower_image
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) :
    (chartAt ℂ p) '' actualSaddleLower E p ρ c =
    {z | z ∈ (chartAt ℂ p).target ∧
      ‖z - (chartAt ℂ p) p‖ ≤ ρ ∧
      morseQuadratic 1 (z - (chartAt ℂ p) p) ≤ c ∧
      (z - (chartAt ℂ p) p).im < 0} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(chartAt ℂ p).map_source hx.1.1,
      hx.1.2.1, hx.1.2.2, hx.2⟩
  · intro hz
    refine ⟨(chartAt ℂ p).symm z, ?_, (chartAt ℂ p).right_inv hz.1⟩
    refine ⟨?_, ?_⟩
    · refine ⟨(chartAt ℂ p).symm.map_source hz.1, ?_, ?_⟩
      · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.1
      · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.2.1
    · simpa [(chartAt ℂ p).right_inv hz.1] using hz.2.2.2

private noncomputable def actualSaddleLower_homeomorph
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    actualSaddleLower E p ρ c ≃ₜ saddleLower ρ c :=
  ((chartAt ℂ p).homeomorphOfImageSubsetSource
    (by intro x hx; exact hx.1.1)
    (actualSaddleLower_image E p ρ c)).trans <|
    (Homeomorph.addLeft (-(chartAt ℂ p) p)).subtype (fun z => by
      change (z ∈ (chartAt ℂ p).target ∧
        ‖z - (chartAt ℂ p) p‖ ≤ ρ ∧
        morseQuadratic 1 (z - (chartAt ℂ p) p) ≤ c ∧
        (z - (chartAt ℂ p) p).im < 0) ↔
        -(chartAt ℂ p) p + z ∈ saddleLower ρ c
      have hz : -(chartAt ℂ p) p + z = z - (chartAt ℂ p) p := by abel
      rw [hz]
      constructor
      · intro h
        exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
      · intro h
        have hb : z ∈ Metric.closedBall ((chartAt ℂ p) p) ρ := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using h.1
        exact ⟨htarget hb, h.1, h.2.1, h.2.2⟩)

private theorem actualSaddleLower_contractible
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 < ρ) (hc : -(ρ ^ 2) ≤ c)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    ContractibleSpace (actualSaddleLower E p ρ c) := by
  letI := saddleLower_contractible ρ c hρ hc
  exact (actualSaddleLower_homeomorph E p ρ c htarget).contractibleSpace

private theorem actualSaddleUpper_openInSublevel
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) :
    IsOpen {x : actualMorseChartSublevel E p 1 ρ c |
      (x : E) ∈ actualSaddleUpper E p ρ c} := by
  have hcont : Continuous (fun x : actualMorseChartSublevel E p 1 ρ c =>
      ((chartAt ℂ p) (x : E) - (chartAt ℂ p) p).im) := by
    have hchart : Continuous (fun x : actualMorseChartSublevel E p 1 ρ c =>
        (chartAt ℂ p) (x : E)) :=
      (chartAt ℂ p).continuousOn.comp_continuous continuous_subtype_val
        (fun x => x.property.1)
    exact Complex.continuous_im.comp (hchart.sub continuous_const)
  have hopen : IsOpen {x : actualMorseChartSublevel E p 1 ρ c |
      (0 : ℝ) < ((chartAt ℂ p) (x : E) - (chartAt ℂ p) p).im} :=
    isOpen_lt continuous_const hcont
  convert hopen using 1
  ext x
  simp [actualSaddleUpper, x.property]

private theorem actualSaddleLower_openInSublevel
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) :
    IsOpen {x : actualMorseChartSublevel E p 1 ρ c |
      (x : E) ∈ actualSaddleLower E p ρ c} := by
  have hchart : Continuous (fun x : actualMorseChartSublevel E p 1 ρ c =>
      (chartAt ℂ p) (x : E)) :=
    (chartAt ℂ p).continuousOn.comp_continuous continuous_subtype_val
      (fun x => x.property.1)
  have hcont : Continuous (fun x : actualMorseChartSublevel E p 1 ρ c =>
      ((chartAt ℂ p) (x : E) - (chartAt ℂ p) p).im) :=
    Complex.continuous_im.comp (hchart.sub continuous_const)
  have hopen : IsOpen {x : actualMorseChartSublevel E p 1 ρ c |
      ((chartAt ℂ p) (x : E) - (chartAt ℂ p) p).im < 0} :=
    isOpen_lt hcont continuous_const
  convert hopen using 1
  ext x
  simp [actualSaddleLower, x.property]

private theorem actualSaddle_negative_open_cover
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hc : c < 0) :
    {x : actualMorseChartSublevel E p 1 ρ c |
      (x : E) ∈ actualSaddleUpper E p ρ c} ∪
    {x : actualMorseChartSublevel E p 1 ρ c |
      (x : E) ∈ actualSaddleLower E p ρ c} = Set.univ := by
  ext x
  have hne := morseQuadratic_saddle_negative_im_ne_zero
    ((chartAt ℂ p) (x : E) - (chartAt ℂ p) p) c hc x.property.2.2
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  rcases lt_trichotomy (((chartAt ℂ p) (x : E) - (chartAt ℂ p) p).im) 0 with h | h | h
  · exact Or.inr ⟨x.property, h⟩
  · exact (hne h).elim
  · exact Or.inl ⟨x.property, h⟩

private theorem actualSaddle_negative_open_disjoint
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) :
    Disjoint
      {x : actualMorseChartSublevel E p 1 ρ c |
        (x : E) ∈ actualSaddleUpper E p ρ c}
      {x : actualMorseChartSublevel E p 1 ρ c |
        (x : E) ∈ actualSaddleLower E p ρ c} := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact (not_lt_of_ge (le_of_lt hx.2)) hy.2

private theorem actualMorseChartSublevel_saddle_negative_h0_finrank_two
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 < ρ) (hc : -(ρ ^ 2) ≤ c) (hneg : c < 0)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H
      (actualMorseChartSublevel E p 1 ρ c) 0) = 2 := by
  let S := actualMorseChartSublevel E p 1 ρ c
  let U : Set S := {x | (x : E) ∈ actualSaddleUpper E p ρ c}
  let V : Set S := {x | (x : E) ∈ actualSaddleLower E p ρ c}
  let X := TopCat.of S
  have hU : IsOpen U := actualSaddleUpper_openInSublevel E p ρ c
  have hV : IsOpen V := actualSaddleLower_openInSublevel E p ρ c
  have hcover : U ∪ V = Set.univ := actualSaddle_negative_open_cover E p ρ c hneg
  have hdisjoint : Disjoint U V := actualSaddle_negative_open_disjoint E p ρ c
  have hAU : actualSaddleUpper E p ρ c ⊆ S := fun _ hx => hx.1
  have hAV : actualSaddleLower E p ρ c ⊆ S := fun _ hx => hx.1
  letI := actualSaddleUpper_contractible E p ρ c hρ hc htarget
  letI : ContractibleSpace U := (nestedSubtypeHomeomorph E S
    (actualSaddleUpper E p ρ c) hAU).contractibleSpace
  letI := actualSaddleLower_contractible E p ρ c hρ hc htarget
  letI : ContractibleSpace V := (nestedSubtypeHomeomorph E S
    (actualSaddleLower E p ρ c) hAV).contractibleSpace
  have hUone : Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H U 0) = 1 := by
    exact contractible_singular_h0_finrank_one U
  have hVone : Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H V 0) = 1 := by
    exact contractible_singular_h0_finrank_one V
  have hOU : Module.finrank ℤ
      ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0) = 1 := by
    rw [(CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X U 0).toLinearEquiv.finrank_eq,
      hUone]
  have hOV : Module.finrank ℤ
      ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0) = 1 := by
    rw [(CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X V 0).toLinearEquiv.finrank_eq,
      hVone]
  let iU := (CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X U 0) ≪≫
    CategoryTheory.asIso ((TopCat.of U).singularHomology₀ε (ModuleCat.of ℤ ℤ))
  let iV := (CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X V 0) ≪≫
    CategoryTheory.asIso ((TopCat.of V).singularHomology₀ε (ModuleCat.of ℤ ℤ))
  letI : Module.Free ℤ
      ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0) :=
    Module.Free.of_equiv iU.toLinearEquiv.symm
  letI : Module.Free ℤ
      ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0) :=
    Module.Free.of_equiv iV.toLinearEquiv.symm
  letI : Module.Finite ℤ
      ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0) :=
    Module.Finite.equiv iU.toLinearEquiv.symm
  letI : Module.Finite ℤ
      ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0) :=
    Module.Finite.equiv iV.toLinearEquiv.symm
  letI := mvAmbientHomologySum_zero_isIso_of_disjoint X U V hU hV hcover hdisjoint
  let i := CategoryTheory.asIso
    (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V 0)
  calc
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H S 0) =
        Module.finrank ℤ ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).homology 0) :=
      (CurveComplexGenusTwo.CWHurewicz.singularHomologyRepresentation X 0).toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℤ ((CurveComplexGenusTwo.CWHurewicz.mvPairComplex X U V).homology 0) :=
      i.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank ℤ
        (((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0) ×
         ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0)) :=
      (CurveComplexGenusTwo.CWHurewicz.mvPairHomologyEquiv X U V 0).finrank_eq
    _ = Module.finrank ℤ
        ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0) +
        Module.finrank ℤ
        ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0) :=
      by
        convert (Module.finrank_prod (R := ℤ)
          (M := ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0))
          (M' := ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0))) using 1
        all_goals
          congr 1
          exact Subsingleton.elim _ _
    _ = 2 := by rw [hOU, hOV]

private theorem actualMorseChartSublevel_saddle_negative_h0_finite
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 < ρ) (hc : -(ρ ^ 2) ≤ c) (hneg : c < 0)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    Module.Finite ℤ (CurveComplexGenusTwo.CWHurewicz.H
      (actualMorseChartSublevel E p 1 ρ c) 0) := by
  let S := actualMorseChartSublevel E p 1 ρ c
  let U : Set S := {x | (x : E) ∈ actualSaddleUpper E p ρ c}
  let V : Set S := {x | (x : E) ∈ actualSaddleLower E p ρ c}
  let X := TopCat.of S
  have hAU : actualSaddleUpper E p ρ c ⊆ S := fun _ hx => hx.1
  have hAV : actualSaddleLower E p ρ c ⊆ S := fun _ hx => hx.1
  letI := actualSaddleUpper_contractible E p ρ c hρ hc htarget
  letI : ContractibleSpace U := (nestedSubtypeHomeomorph E S
    (actualSaddleUpper E p ρ c) hAU).contractibleSpace
  letI := actualSaddleLower_contractible E p ρ c hρ hc htarget
  letI : ContractibleSpace V := (nestedSubtypeHomeomorph E S
    (actualSaddleLower E p ρ c) hAV).contractibleSpace
  have hU : IsOpen U := actualSaddleUpper_openInSublevel E p ρ c
  have hV : IsOpen V := actualSaddleLower_openInSublevel E p ρ c
  have hcover : U ∪ V = Set.univ := actualSaddle_negative_open_cover E p ρ c hneg
  have hdisjoint : Disjoint U V := actualSaddle_negative_open_disjoint E p ρ c
  letI := mvAmbientHomologySum_zero_isIso_of_disjoint X U V hU hV hcover hdisjoint
  let eU : ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0) ≃ₗ[ℤ] ℤ :=
    ((CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X U 0) ≪≫
      CategoryTheory.asIso ((TopCat.of U).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv
  let eV : ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0) ≃ₗ[ℤ] ℤ :=
    ((CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X V 0) ≪≫
      CategoryTheory.asIso ((TopCat.of V).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv
  let ep :
      (((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology 0) ×
       ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology 0)) ≃ₗ[ℤ] ℤ × ℤ := by
    convert eU.prodCongr eV using 1
    all_goals exact Subsingleton.elim _ _
  let e : CurveComplexGenusTwo.CWHurewicz.H S 0 ≃ₗ[ℤ] ℤ × ℤ :=
    (((CurveComplexGenusTwo.CWHurewicz.singularHomologyRepresentation X 0).toLinearEquiv.symm).trans
      ((CategoryTheory.asIso
        (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V 0)).toLinearEquiv.symm)).trans
      ((CurveComplexGenusTwo.CWHurewicz.mvPairHomologyEquiv X U V 0).trans ep)
  exact Module.Finite.equiv e.symm

private theorem actualMorseChartSublevel_saddle_negative_positive_homology_zero
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 < ρ) (hc : -(ρ ^ 2) ≤ c) (hneg : c < 0)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target)
    (n : ℕ) :
    IsZero (CurveComplexGenusTwo.CWHurewicz.H
      (actualMorseChartSublevel E p 1 ρ c) (n + 1)) := by
  let S := actualMorseChartSublevel E p 1 ρ c
  let U : Set S := {x | (x : E) ∈ actualSaddleUpper E p ρ c}
  let V : Set S := {x | (x : E) ∈ actualSaddleLower E p ρ c}
  let X := TopCat.of S
  have hAU : actualSaddleUpper E p ρ c ⊆ S := fun _ hx => hx.1
  have hAV : actualSaddleLower E p ρ c ⊆ S := fun _ hx => hx.1
  letI := actualSaddleUpper_contractible E p ρ c hρ hc htarget
  letI : ContractibleSpace U := (nestedSubtypeHomeomorph E S
    (actualSaddleUpper E p ρ c) hAU).contractibleSpace
  letI := actualSaddleLower_contractible E p ρ c hρ hc htarget
  letI : ContractibleSpace V := (nestedSubtypeHomeomorph E S
    (actualSaddleLower E p ρ c) hAV).contractibleSpace
  have hUzero : IsZero ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology (n + 1)) :=
    (CircleHomologyComputation.contractible_positive_homology U (n + 1) (by omega)).of_iso
      (CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X U (n + 1))
  have hVzero : IsZero ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology (n + 1)) :=
    (CircleHomologyComputation.contractible_positive_homology V (n + 1) (by omega)).of_iso
      (CurveComplexGenusTwo.CWHurewicz.ordinaryHomologyRepresentation X V (n + 1))
  letI : Subsingleton ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X U).homology (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hUzero
  letI : Subsingleton ((CurveComplexGenusTwo.CWHurewicz.mvOrdinaryComplex X V).homology (n + 1)) :=
    ModuleCat.isZero_iff_subsingleton.mp hVzero
  have hpair : IsZero ((CurveComplexGenusTwo.CWHurewicz.mvPairComplex X U V).homology (n + 1)) := by
    letI : Subsingleton ((CurveComplexGenusTwo.CWHurewicz.mvPairComplex X U V).homology (n + 1)) :=
      ⟨fun a b => (CurveComplexGenusTwo.CWHurewicz.mvPairHomologyEquiv
        X U V (n + 1)).injective (Subsingleton.elim _ _)⟩
    exact ModuleCat.isZero_of_subsingleton _
  have hU : IsOpen U := actualSaddleUpper_openInSublevel E p ρ c
  have hV : IsOpen V := actualSaddleLower_openInSublevel E p ρ c
  have hcover : U ∪ V = Set.univ := actualSaddle_negative_open_cover E p ρ c hneg
  have hdisjoint : Disjoint U V := actualSaddle_negative_open_disjoint E p ρ c
  letI := mvAmbientHomologySum_positive_isIso_of_disjoint X U V hU hV hcover hdisjoint n
  have hambient : IsZero ((CurveComplexGenusTwo.CWHurewicz.mvAmbientComplex X).homology (n + 1)) :=
    hpair.of_iso (CategoryTheory.asIso
      (CurveComplexGenusTwo.CWHurewicz.mvAmbientHomologySum X U V (n + 1))).symm
  exact hambient.of_iso
    (CurveComplexGenusTwo.CWHurewicz.singularHomologyRepresentation X (n + 1)).symm

private def saddleNonnegativeSlice (ρ c : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ ρ ∧ morseQuadratic 1 z ≤ c}

private theorem saddleNonnegativeSlice_starConvex
    (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c) :
    StarConvex ℝ 0 (saddleNonnegativeSlice ρ c) := by
  intro z hz a b ha hb hab
  have hbn : b ≤ 1 := by linarith
  have hzball : z ∈ Metric.closedBall (0 : ℂ) ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
  have hzeroball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ρ := by
    simpa [Metric.mem_closedBall] using hρ
  have hwball := (convex_closedBall (0 : ℂ) ρ) hzeroball hzball ha hb hab
  have hwnorm : ‖a • (0 : ℂ) + b • z‖ ≤ ρ := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hwball
  have hb2 : b ^ 2 ≤ (1 : ℝ) := by nlinarith
  have hq : morseQuadratic 1 (a • (0 : ℂ) + b • z) =
      b ^ 2 * morseQuadratic 1 z := by
    simp [morseQuadratic_saddle, Complex.smul_re, Complex.smul_im]
    ring
  refine ⟨hwnorm, ?_⟩
  rw [hq]
  have hzq : morseQuadratic 1 z ≤ c := hz.2
  by_cases hqnonneg : 0 ≤ morseQuadratic 1 z
  · nlinarith [mul_nonneg (sub_nonneg.mpr hb2) hqnonneg]
  · have hqneg : morseQuadratic 1 z < 0 := lt_of_not_ge hqnonneg
    exact (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) hqneg.le).trans hc

private theorem saddleNonnegativeSlice_contractible
    (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c) :
    ContractibleSpace (saddleNonnegativeSlice ρ c) := by
  have hzero : (0 : ℂ) ∈ saddleNonnegativeSlice ρ c := by
    simp [saddleNonnegativeSlice, hρ, hc, morseQuadratic_saddle]
  exact (saddleNonnegativeSlice_starConvex ρ c hρ hc).contractibleSpace ⟨_, hzero⟩

private noncomputable def actualMorseChartSublevel_saddle_nonnegative_homeomorph
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    actualMorseChartSublevel E p 1 ρ c ≃ₜ saddleNonnegativeSlice ρ c := by
  let center := (chartAt ℂ p) p
  let e := actualMorseChartSublevel_homeomorph E p 1 ρ c
  refine e.trans
    { toFun := fun z => ⟨z.val - center, z.property.2⟩
      invFun := fun z => ⟨z.val + center, ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · have hball : z.val + center ∈ Metric.closedBall center ρ := by
      simpa [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_right] using z.property.1
    refine ⟨htarget hball, ?_, ?_⟩
    · simpa [center] using z.property.1
    · simpa [center] using z.property.2
  · intro z
    apply Subtype.ext
    simp [center]
  · intro z
    apply Subtype.ext
    simp [center]
  · exact (continuous_subtype_val.sub continuous_const).subtype_mk _
  · exact (continuous_subtype_val.add continuous_const).subtype_mk _

private theorem actualMorseChartSublevel_saddle_nonnegative_contractible
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    ContractibleSpace (actualMorseChartSublevel E p 1 ρ c) := by
  letI : ContractibleSpace (saddleNonnegativeSlice ρ c) :=
    saddleNonnegativeSlice_contractible ρ c hρ hc
  exact (actualMorseChartSublevel_saddle_nonnegative_homeomorph
    E p ρ c htarget).contractibleSpace

private theorem actualMorseChartSublevel_saddle_upper_h0_finrank_one
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H
      (actualMorseChartSublevel E p 1 ρ c) 0) = 1 := by
  letI := actualMorseChartSublevel_saddle_nonnegative_contractible E p ρ c hρ hc htarget
  exact contractible_singular_h0_finrank_one _

private theorem actualMorseChartSublevel_saddle_upper_positive_homology_zero
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ c : ℝ) (hρ : 0 ≤ ρ) (hc : 0 ≤ c)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target)
    (n : ℕ) (hn : 0 < n) :
    IsZero (CurveComplexGenusTwo.CWHurewicz.H
      (actualMorseChartSublevel E p 1 ρ c) n) := by
  letI := actualMorseChartSublevel_saddle_nonnegative_contractible E p ρ c hρ hc htarget
  exact CircleHomologyComputation.contractible_positive_homology _ n hn

private theorem actualMorseChartSublevel_mono_level
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (k : Fin 3) (ρ cLow cHigh : ℝ) (hlevel : cLow ≤ cHigh) :
    actualMorseChartSublevel E p k ρ cLow ⊆
      actualMorseChartSublevel E p k ρ cHigh := by
  intro x hx
  exact ⟨hx.1, hx.2.1, hx.2.2.trans hlevel⟩

private theorem actualMorseChart_saddle_relative_pair_H0_exact
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ cLow cHigh : ℝ) (hρ : 0 < ρ)
    (hminus : -(ρ ^ 2) ≤ cLow) (hneg : cLow < 0)
    (hplus : 0 ≤ cHigh)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    let R := actualMorseChartSublevel E p 1 ρ cHigh
    let L := actualMorseChartSublevel E p 1 ρ cLow
    let A : Set R := {x | (x : E) ∈ L}
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H A 0) = 2 ∧
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H R 0) = 1 ∧
    (∃ hzero : CurveComplexGenusTwo.CWHurewicz.relativeConnecting R A 0 ≫
        CurveComplexGenusTwo.CWHurewicz.homologyInclusion R A 0 = 0,
      (⟨CurveComplexGenusTwo.CWHurewicz.relativeConnecting R A 0,
        CurveComplexGenusTwo.CWHurewicz.homologyInclusion R A 0,
        hzero⟩ : ShortComplex (ModuleCat ℤ)).Exact) := by
  dsimp
  have hlevels : cLow ≤ cHigh := le_trans hneg.le hplus
  let R := actualMorseChartSublevel E p 1 ρ cHigh
  let L := actualMorseChartSublevel E p 1 ρ cLow
  let A : Set R := {x | (x : E) ∈ L}
  have hLR : L ⊆ R := actualMorseChartSublevel_mono_level E p 1 ρ cLow cHigh hlevels
  let e : A ≃ₜ L := nestedSubtypeHomeomorph E R L hLR
  have hA : Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H A 0) = 2 := by
    calc
      Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H A 0) =
          Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H L 0) :=
        (CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv 0).toLinearEquiv.finrank_eq
      _ = 2 := actualMorseChartSublevel_saddle_negative_h0_finrank_two
        E p ρ cLow hρ hminus hneg htarget
  have hR : Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H R 0) = 1 :=
    actualMorseChartSublevel_saddle_upper_h0_finrank_one
      E p ρ cHigh hρ.le hplus htarget
  obtain ⟨hz, hexact⟩ := CurveComplexGenusTwo.CWHurewicz.pairHomology_exact_at_subspace R A 0
  exact ⟨hA, hR, hz, hexact⟩

private theorem actualMorseChart_saddle_H0_inclusion_epi
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ cLow cHigh : ℝ) (hρ : 0 < ρ)
    (hminus : -(ρ ^ 2) ≤ cLow) (hneg : cLow < 0)
    (hplus : 0 ≤ cHigh)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    let R := actualMorseChartSublevel E p 1 ρ cHigh
    let L := actualMorseChartSublevel E p 1 ρ cLow
    let A : Set R := {x | (x : E) ∈ L}
    Epi (CurveComplexGenusTwo.CWHurewicz.homologyInclusion R A 0) := by
  dsimp
  have hlevels : cLow ≤ cHigh := le_trans hneg.le hplus
  let R := actualMorseChartSublevel E p 1 ρ cHigh
  let L := actualMorseChartSublevel E p 1 ρ cLow
  let A : Set R := {x | (x : E) ∈ L}
  have hLR : L ⊆ R := actualMorseChartSublevel_mono_level E p 1 ρ cLow cHigh hlevels
  letI : ContractibleSpace R :=
    actualMorseChartSublevel_saddle_nonnegative_contractible E p ρ cHigh hρ.le hplus htarget
  letI : PathConnectedSpace R := inferInstance
  letI : ContractibleSpace (actualSaddleUpper E p ρ cLow) :=
    actualSaddleUpper_contractible E p ρ cLow hρ hminus htarget
  letI : Nonempty A := by
    obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (actualSaddleUpper E p ρ cLow)
    let u := e.invFun ()
    exact ⟨⟨⟨u.val, hLR u.property.1⟩, u.property.1⟩⟩
  exact homologyInclusion_zero_epi_of_nonempty_pathConnected R A

private theorem relative_H1_finrank_one_of_exact_H0
    (R : Type) [TopologicalSpace R] (A : Set R)
    (hAfinite : Module.Finite ℤ (CurveComplexGenusTwo.CWHurewicz.H A 0))
    (hA : Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H A 0) = 2)
    (hR : Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H R 0) = 1)
    (hzero : IsZero (CurveComplexGenusTwo.CWHurewicz.H R 1))
    (hepi : Epi (CurveComplexGenusTwo.CWHurewicz.homologyInclusion R A 0)) :
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 1) = 1 := by
  letI := hAfinite
  let f := (CurveComplexGenusTwo.CWHurewicz.homologyInclusion R A 0).hom
  have hsurj : Function.Surjective f :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  letI : Module ℤ (LinearMap.ker f) := (LinearMap.ker f).module
  have hker : Module.finrank ℤ (LinearMap.ker f) = 1 := by
    letI : Module ℤ ((CurveComplexGenusTwo.CWHurewicz.H A 0) ⧸ LinearMap.ker f) :=
      Submodule.Quotient.module (LinearMap.ker f)
    have hq := (LinearMap.ker f).finrank_quotient_add_finrank
    have hqeq : Module.finrank ℤ
        ((CurveComplexGenusTwo.CWHurewicz.H A 0) ⧸ LinearMap.ker f) =
        Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.H R 0) := by
      convert (f.quotKerEquivOfSurjective hsurj).finrank_eq using 1
      all_goals congr 1; exact Subsingleton.elim _ _
    rw [hqeq, hR, hA] at hq
    have hq' : 1 + Module.finrank ℤ (LinearMap.ker f) = 2 := by
      convert hq using 1
    omega
  have hrelzero : IsZero (CurveComplexGenusTwo.CWHurewicz.H R 1) := hzero
  obtain ⟨_, he1⟩ := CurveComplexGenusTwo.CWHurewicz.pairHomology_exact_at_relative R A 0
  have hmono : Mono (CurveComplexGenusTwo.CWHurewicz.relativeConnecting R A 0) :=
    he1.mono_g (hrelzero.eq_of_src _ _)
  obtain ⟨_, he0⟩ := CurveComplexGenusTwo.CWHurewicz.pairHomology_exact_at_subspace R A 0
  have hrange : LinearMap.range (CurveComplexGenusTwo.CWHurewicz.relativeConnecting R A 0).hom =
      LinearMap.ker f := he0.moduleCat_range_eq_ker
  have hinj : Function.Injective (CurveComplexGenusTwo.CWHurewicz.relativeConnecting R A 0).hom :=
    (ModuleCat.mono_iff_injective _).mp hmono
  calc
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 1) =
        Module.finrank ℤ
          (LinearMap.range (CurveComplexGenusTwo.CWHurewicz.relativeConnecting R A 0).hom) :=
      by
        convert (LinearMap.finrank_range_of_inj hinj).symm using 1
        all_goals congr 1; exact Subsingleton.elim _ _
    _ = 1 := by
      rw [hrange]
      convert hker using 1
      all_goals
        congr 1
        exact Subsingleton.elim _ _

private theorem actualMorseChart_saddle_relative_H1_finrank_one
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ cLow cHigh : ℝ) (hρ : 0 < ρ)
    (hminus : -(ρ ^ 2) ≤ cLow) (hneg : cLow < 0)
    (hplus : 0 ≤ cHigh)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    let R := actualMorseChartSublevel E p 1 ρ cHigh
    let L := actualMorseChartSublevel E p 1 ρ cLow
    let A : Set R := {x | (x : E) ∈ L}
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 1) = 1 := by
  dsimp
  have hlevels : cLow ≤ cHigh := le_trans hneg.le hplus
  let R := actualMorseChartSublevel E p 1 ρ cHigh
  let L := actualMorseChartSublevel E p 1 ρ cLow
  let A : Set R := {x | (x : E) ∈ L}
  have hLR : L ⊆ R := actualMorseChartSublevel_mono_level E p 1 ρ cLow cHigh hlevels
  let e : A ≃ₜ L := nestedSubtypeHomeomorph E R L hLR
  letI : Module.Finite ℤ (CurveComplexGenusTwo.CWHurewicz.H L 0) :=
    actualMorseChartSublevel_saddle_negative_h0_finite
      E p ρ cLow hρ hminus hneg htarget
  have hAfinite : Module.Finite ℤ (CurveComplexGenusTwo.CWHurewicz.H A 0) :=
    Module.Finite.equiv
      (CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv 0).toLinearEquiv.symm
  obtain ⟨hA, hR, _, _⟩ := actualMorseChart_saddle_relative_pair_H0_exact
    E p ρ cLow cHigh hρ hminus hneg hplus htarget
  have hzero : IsZero (CurveComplexGenusTwo.CWHurewicz.H R 1) :=
    actualMorseChartSublevel_saddle_upper_positive_homology_zero
      E p ρ cHigh hρ.le hplus htarget 1 (by norm_num)
  have hepi := actualMorseChart_saddle_H0_inclusion_epi
    E p ρ cLow cHigh hρ hminus hneg hplus htarget
  exact relative_H1_finrank_one_of_exact_H0 R A hAfinite hA hR hzero hepi

private theorem actualMorseChart_saddle_relative_high_zero
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ cLow cHigh : ℝ) (hρ : 0 < ρ)
    (hminus : -(ρ ^ 2) ≤ cLow) (hneg : cLow < 0)
    (hplus : 0 ≤ cHigh)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target)
    (n : ℕ) :
    let R := actualMorseChartSublevel E p 1 ρ cHigh
    let L := actualMorseChartSublevel E p 1 ρ cLow
    let A : Set R := {x | (x : E) ∈ L}
    IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A (n + 2)) := by
  dsimp
  have hlevels : cLow ≤ cHigh := le_trans hneg.le hplus
  let R := actualMorseChartSublevel E p 1 ρ cHigh
  let L := actualMorseChartSublevel E p 1 ρ cLow
  let A : Set R := {x | (x : E) ∈ L}
  have hLR : L ⊆ R := actualMorseChartSublevel_mono_level E p 1 ρ cLow cHigh hlevels
  let e : A ≃ₜ L := nestedSubtypeHomeomorph E R L hLR
  have hAz (j : ℕ) (hj : 0 < j) : IsZero (CurveComplexGenusTwo.CWHurewicz.H A j) :=
    (by
      have hLj : IsZero (CurveComplexGenusTwo.CWHurewicz.H L j) := by
        have hpred : j - 1 + 1 = j := Nat.sub_add_cancel hj
        simpa only [hpred] using
          (actualMorseChartSublevel_saddle_negative_positive_homology_zero
            E p ρ cLow hρ hminus hneg htarget (j - 1))
      exact hLj.of_iso
        (CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv j))
  have hRz : IsZero (CurveComplexGenusTwo.CWHurewicz.H R (n + 2)) :=
    actualMorseChartSublevel_saddle_upper_positive_homology_zero
      E p ρ cHigh hρ.le hplus htarget (n + 2) (by omega)
  letI : IsIso (CurveComplexGenusTwo.CWHurewicz.homologyToRelative R A (n + 2)) :=
    CurveComplexGenusTwo.CWHurewicz.homologyToRelative_isIso_of_subspace_zero
      R A (n + 1) (hAz (n + 2) (by omega)) (hAz (n + 1) (by omega))
  exact hRz.of_iso
    (CategoryTheory.asIso (CurveComplexGenusTwo.CWHurewicz.homologyToRelative R A (n + 2))).symm

private theorem relative_H0_zero_of_H0_inclusion_epi
    (R : Type) [TopologicalSpace R] (A : Set R)
    (hepi : Epi (CurveComplexGenusTwo.CWHurewicz.homologyInclusion R A 0)) :
    IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 0) := by
  let S := CurveComplexGenusTwo.CWHurewicz.pairHomologyShortComplex R A
  have hS := CurveComplexGenusTwo.CWHurewicz.pairHomologyShortExact R A
  letI : Epi (S.g.f 0) := by
    dsimp [S, CurveComplexGenusTwo.CWHurewicz.pairHomologyShortComplex]
    infer_instance
  have hrelEpi : Epi (CurveComplexGenusTwo.CWHurewicz.homologyToRelative R A 0) := by
    exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by simp)
  obtain ⟨hcomp, _⟩ := CurveComplexGenusTwo.CWHurewicz.pairHomology_exact_at_absolute R A 0
  have hzero : CurveComplexGenusTwo.CWHurewicz.homologyToRelative R A 0 = 0 :=
    (cancel_epi (CurveComplexGenusTwo.CWHurewicz.homologyInclusion R A 0)).mp
      (by simpa using hcomp)
  exact IsZero.of_epi_eq_zero
    (CurveComplexGenusTwo.CWHurewicz.homologyToRelative R A 0) hzero

private theorem actualMorseChart_saddle_relative_H0_zero
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ cLow cHigh : ℝ) (hρ : 0 < ρ)
    (hminus : -(ρ ^ 2) ≤ cLow) (hneg : cLow < 0)
    (hplus : 0 ≤ cHigh)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    let R := actualMorseChartSublevel E p 1 ρ cHigh
    let L := actualMorseChartSublevel E p 1 ρ cLow
    let A : Set R := {x | (x : E) ∈ L}
    IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 0) := by
  dsimp
  let R := actualMorseChartSublevel E p 1 ρ cHigh
  let L := actualMorseChartSublevel E p 1 ρ cLow
  let A : Set R := {x | (x : E) ∈ L}
  have hepi := actualMorseChart_saddle_H0_inclusion_epi
    E p ρ cLow cHigh hρ hminus hneg hplus htarget
  exact relative_H0_zero_of_H0_inclusion_epi R A hepi

private def saddleRelativeProfile
    (E : Type) [TopologicalSpace E] (R L : Set E) : Prop :=
  let A : Set R := {x | (x : E) ∈ L}
  IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 0) ∧
  Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 1) = 1 ∧
  ∀ n : ℕ, IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A (n + 2))

private theorem actualMorseChart_saddle_relative_profile
    (E : Type) [TopologicalSpace E] [ChartedSpace ℂ E]
    (p : E) (ρ cLow cHigh : ℝ) (hρ : 0 < ρ)
    (hminus : -(ρ ^ 2) ≤ cLow) (hneg : cLow < 0) (hplus : 0 ≤ cHigh)
    (htarget : Metric.closedBall ((chartAt ℂ p) p) ρ ⊆ (chartAt ℂ p).target) :
    saddleRelativeProfile E
      (actualMorseChartSublevel E p 1 ρ cHigh)
      (actualMorseChartSublevel E p 1 ρ cLow) :=
  ⟨actualMorseChart_saddle_relative_H0_zero
      E p ρ cLow cHigh hρ hminus hneg hplus htarget,
    actualMorseChart_saddle_relative_H1_finrank_one
      E p ρ cLow cHigh hρ hminus hneg hplus htarget,
    actualMorseChart_saddle_relative_high_zero
      E p ρ cLow cHigh hρ hminus hneg hplus htarget⟩


set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Public specialization of the existing checked saddle topology to the
literal real two-dimensional coordinate model. Its underlying private proof
bodies are preserved byte-for-byte from ActualMorseChartGeometry.lean. -/
theorem actual_saddle_coordinate_pair_relative_profile
    (ρ a b : ℝ) (hρ : 0 < ρ) (hminus : -(ρ ^ 2) ≤ a)
    (ha : a < 0) (hb : 0 ≤ b) :
    let R := {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ b};
    let A : Set R := {z | z.1.re ^ 2 - z.1.im ^ 2 ≤ a};
    IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 0) ∧
      Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A 1) = 1 ∧
      ∀ n : ℕ, IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology R A (n + 2)) := by
  have hp := actualMorseChart_saddle_relative_profile ℂ (0 : ℂ) ρ a b hρ hminus ha hb
    (by simp [chartAt_self_eq])
  let X := actualMorseChartSublevel ℂ (0 : ℂ) 1 ρ b
  let Y := actualMorseChartSublevel ℂ (0 : ℂ) 1 ρ a
  let A : Set X := {x | x.1 ∈ Y}
  let R := {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ b}
  let B : Set R := {z | z.1.re ^ 2 - z.1.im ^ 2 ≤ a}
  have hset : (X : Set ℂ) = (R : Set ℂ) := by
    ext z
    simp [X, R, actualMorseChartSublevel, chartAt_self_eq, morseQuadratic_saddle]
  let e : X ≃ₜ R := Homeomorph.setCongr hset
  have he : ∀ x : X, x ∈ A ↔ e x ∈ B := by
    intro x
    change x.1 ∈ Y ↔ x.1.re ^ 2 - x.1.im ^ 2 ≤ a
    have hn : ‖x.1‖ ≤ ρ := by
      have hx := x.2
      simpa [X, actualMorseChartSublevel, chartAt_self_eq, morseQuadratic_saddle]
        using hx.2.1
    simp [Y, actualMorseChartSublevel, chartAt_self_eq, morseQuadratic_saddle, hn]
  let f : C(X, R) := ⟨e, e.continuous⟩
  have hf : ∀ x ∈ A, f x ∈ B := fun x hx => (he x).mp hx
  have hi (n : ℕ) : IsIso
      (CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap A B f hf n) :=
    actual_pairRelativeHomologyMap_homeomorph_isIso X R A B e he n
  have iso (n : ℕ) : CurveComplexGenusTwo.CWHurewicz.relativeHomology X A n ≅
      CurveComplexGenusTwo.CWHurewicz.relativeHomology R B n := by
    letI := hi n
    exact asIso (CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap A B f hf n)
  change IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology X A 0) ∧
    Module.finrank ℤ (CurveComplexGenusTwo.CWHurewicz.relativeHomology X A 1) = 1 ∧
    ∀ n : ℕ, IsZero (CurveComplexGenusTwo.CWHurewicz.relativeHomology X A (n + 2)) at hp
  refine ⟨hp.1.of_iso (iso 0).symm, ?_, fun n => (hp.2.2 n).of_iso (iso (n + 2)).symm⟩
  rw [← (iso 1).toLinearEquiv.finrank_eq, hp.2.1]


theorem actual_saddle_coordinate_upper_contractible
    (ρ b : ℝ) (hρ : 0 ≤ ρ) (hb : 0 ≤ b) :
    ContractibleSpace {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ b} := by
  have heq : saddleNonnegativeSlice ρ b =
      {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ b} := by
    ext z
    simp only [saddleNonnegativeSlice, Set.mem_setOf_eq, morseQuadratic_saddle]
  letI := saddleNonnegativeSlice_contractible ρ b hρ hb
  exact (Homeomorph.setCongr heq).symm.contractibleSpace

set_option backward.isDefEq.respectTransparency false in
theorem actual_saddle_coordinate_lower_h0_finite
    (ρ a : ℝ) (hρ : 0 < ρ) (hminus : -(ρ ^ 2) ≤ a) (ha : a < 0) :
    Module.Finite ℤ (CurveComplexGenusTwo.CWHurewicz.H
      {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ a} 0) := by
  let X := actualMorseChartSublevel ℂ (0 : ℂ) 1 ρ a
  let R := {z : ℂ | ‖z‖ ≤ ρ ∧ z.re ^ 2 - z.im ^ 2 ≤ a}
  have hset : (X : Set ℂ) = (R : Set ℂ) := by
    ext z
    simp [X, R, actualMorseChartSublevel, chartAt_self_eq, morseQuadratic_saddle]
  let e : X ≃ₜ R := Homeomorph.setCongr hset
  letI : Module.Finite ℤ (CurveComplexGenusTwo.CWHurewicz.H X 0) :=
    actualMorseChartSublevel_saddle_negative_h0_finite ℂ (0 : ℂ) ρ a hρ hminus ha
      (by simp [chartAt_self_eq])
  exact Module.Finite.equiv
    (CircleHomologyComputation.homotopyHomologyIso e.toHomotopyEquiv 0).toLinearEquiv

