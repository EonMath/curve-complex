import CurveComplexGenusTwo.Topology.ActualThreeArcCount.ComponentNullhomotopy
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.CWHurewicz.SingularRepresentation
import CurveComplexGenusTwo.CWHurewicz.HomotopyHomologyIso

open CurveComplex Set Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
open scoped Manifold ContDiff
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private abbrev DiskCore : Set UnitDisk :=
  {z | z.val ∈ Metric.ball (0 : Plane) 1}
private abbrev ClosedAnnulus : Set Plane :=
  Metric.closedBall (0 : Plane) 2 \ Metric.ball (0 : Plane) 1
private abbrev AnnulusCore : Set ClosedAnnulus :=
  {z | z.val ∈ Metric.ball (0 : Plane) 2 \ Metric.closedBall (0 : Plane) 1}
private abbrev InnerCircle : Set ClosedAnnulus :=
  {z | z.val ∈ Metric.sphere (0 : Plane) 1}

/-- An actual exterior complementary region with a compact disk model.
The boundary of the model may identify cut sides; the open disk maps
homeomorphically onto the region itself. -/
def DiskRegion {S : Type} [TopologicalSpace S]
    (Q : Set S) (U : Set S) : Prop :=
  ∃ d : C(UnitDisk, ↥Q),
    (Set.range (fun z : UnitDisk => (d z).val) = closure U) ∧
    Topology.IsEmbedding (fun z : ↥DiskCore => d z.val) ∧
    Set.range (fun z : ↥DiskCore => (d z.val).val) = U

/-- An actual annular complementary region. Its inner boundary is the single
original boundary circle, rather than a newly created cut boundary. -/
def BoundaryAnnulusRegion {S : Type} [TopologicalSpace S]
    (Q B U : Set S) : Prop :=
  ∃ d : C(ClosedAnnulus, ↥Q),
    (Set.range (fun z : ClosedAnnulus => (d z).val) = closure U) ∧
    Topology.IsEmbedding (fun z : ↥AnnulusCore => d z.val) ∧
    Set.range (fun z : ↥AnnulusCore => (d z.val).val) = U ∧
    Set.range (fun z : ↥InnerCircle => (d z.val).val) = B


private abbrev RZ := ModuleCat.of ℤ ℤ

private theorem diskRegion_contractible
    {S : Type} [TopologicalSpace S] (Q U : Set S)
    (h : DiskRegion Q U) : ContractibleSpace U := by
  obtain ⟨d, -, hd, hrange⟩ := h
  let e : DiskCore ≃ₜ U :=
    (Topology.IsEmbedding.subtypeVal.comp hd).toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  let hcore : DiskCore ≃ₜ Metric.ball (0 : Plane) 1 :=
    (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr (by
        ext z
        simp only [Set.mem_range]
        constructor
        · rintro ⟨w, rfl⟩
          exact w.property
        · intro hz
          exact ⟨⟨⟨z, Metric.ball_subset_closedBall hz⟩, hz⟩, rfl⟩))
  letI : ContractibleSpace DiskCore :=
    hcore.contractibleSpace_iff.mpr (Metric.contractibleSpace_ball (by norm_num))
  exact e.contractibleSpace_iff.mp inferInstance


private def annulusScale (t : unitInterval) (z : ClosedAnnulus) : ℝ :=
  1 - (t : ℝ) + (t : ℝ) * ‖z.val‖⁻¹

private lemma annulus_norm_bounds (z : ClosedAnnulus) : 1 ≤ ‖z.val‖ ∧ ‖z.val‖ ≤ 2 := by
  have h := z.property
  simpa only [ClosedAnnulus, Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
    dist_zero_right, not_lt, and_comm] using h

private lemma annulusScale_pos (t : unitInterval) (z : ClosedAnnulus) :
    0 < annulusScale t z := by
  have hn := (annulus_norm_bounds z).1
  have hnpos : 0 < ‖z.val‖ := by linarith
  have hi : 0 < ‖z.val‖⁻¹ := inv_pos.mpr hnpos
  have ht0 := t.property.1
  have ht1 := t.property.2
  dsimp [annulusScale]
  by_cases h : (t : ℝ) = 0
  · simp [h]
  · have hm := mul_pos (lt_of_le_of_ne ht0 (Ne.symm h)) hi
    linarith

private lemma annulusScale_norm (t : unitInterval) (z : ClosedAnnulus) :
    ‖annulusScale t z • z.val‖ = (1 - (t : ℝ)) * ‖z.val‖ + (t : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (annulusScale_pos t z)]
  dsimp [annulusScale]
  have hn : ‖z.val‖ ≠ 0 := by have := (annulus_norm_bounds z).1; linarith
  field_simp

private def annulusDeform (p : unitInterval × ClosedAnnulus) : ClosedAnnulus :=
  ⟨annulusScale p.1 p.2 • p.2.val, by
    have hn := annulus_norm_bounds p.2
    have ht0 := p.1.property.1
    have ht1 := p.1.property.2
    simp only [ClosedAnnulus, Set.mem_sdiff, Metric.mem_closedBall,
      Metric.mem_ball, dist_zero_right, not_lt]
    rw [annulusScale_norm]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hn.1),
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr hn.2)]⟩

private lemma annulusDeform_continuous : Continuous annulusDeform := by
  apply Continuous.subtype_mk
  have ht : Continuous fun p : unitInterval × ClosedAnnulus => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : unitInterval × ClosedAnnulus => p.2.val :=
    continuous_subtype_val.comp continuous_snd
  exact ((continuous_const.sub ht).add (ht.mul (hz.norm.inv₀
    (fun p => by have := (annulus_norm_bounds p.2).1; linarith)))).smul hz

private def innerRetract : C(ClosedAnnulus, ↥InnerCircle) :=
  ⟨fun z => ⟨annulusDeform (1, z), by
    change annulusScale 1 z • z.val ∈ Metric.sphere (0 : Plane) 1
    rw [Metric.mem_sphere, dist_zero_right]
    simp [annulusScale_norm]⟩,
    by apply Continuous.subtype_mk; exact annulusDeform_continuous.comp (continuous_const.prodMk continuous_id)⟩

private def annulusInnerHomotopy : ContinuousMap.Homotopy
    (ContinuousMap.id ClosedAnnulus)
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥InnerCircle, ClosedAnnulus)).comp innerRetract) where
  toFun := annulusDeform
  continuous_toFun := annulusDeform_continuous
  map_zero_left := by
    intro z
    apply Subtype.ext
    simp [annulusDeform, annulusScale]
  map_one_left := by intro z; rfl

/-- The inclusion of a disk region is nullhomotopic in the ambient space. -/
theorem diskRegion_inclusion_nullhomotopic
    {S : Type} [TopologicalSpace S] (Q U : Set S) (h : DiskRegion Q U) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, S)).Nullhomotopic := by
  letI : ContractibleSpace U := diskRegion_contractible Q U h
  simpa only [ContinuousMap.comp_id] using
    (id_nullhomotopic U).comp_right
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, S))

/-- A boundary annulus retracts in the ambient space into the specified original
boundary. This uses its literal inner-circle image, not an abstract annulus type. -/
theorem boundaryAnnulusRegion_inclusion_homotopic_into_boundary
    {S : Type} [TopologicalSpace S] (Q B U : Set S)
    (h : BoundaryAnnulusRegion Q B U) :
    ∃ f : C(↥U, ↥B), ContinuousMap.Homotopic
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, S))
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(↥B, S)).comp f) := by
  obtain ⟨d, -, hd, hrange, hb⟩ := h
  let e : AnnulusCore ≃ₜ U :=
    (Topology.IsEmbedding.subtypeVal.comp hd).toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  let k : C(↥U, ClosedAnnulus) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(AnnulusCore, ClosedAnnulus)).comp
      ⟨e.symm, e.symm.continuous⟩
  let dS : C(ClosedAnnulus, S) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Q, S)).comp d
  let j : C(InnerCircle, ↥B) :=
    ⟨fun z => ⟨(d z.val).val, by rw [← hb]; exact ⟨z, rfl⟩⟩,
      by fun_prop⟩
  let f := (j.comp innerRetract).comp k
  refine ⟨f, ?_⟩
  have hleft : (dS.comp (ContinuousMap.id ClosedAnnulus)).comp k =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, S)) := by
    ext z
    exact congrArg Subtype.val (e.apply_symm_apply z)
  have hright :
      (dS.comp ((⟨Subtype.val, continuous_subtype_val⟩ :
        C(InnerCircle, ClosedAnnulus)).comp innerRetract)).comp k =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥B, S)).comp f := by
    ext z
    rfl
  have hh := ((ContinuousMap.Homotopy.refl dS).comp annulusInnerHomotopy).compContinuousMap k
  rw [hleft, hright] at hh
  exact ⟨hh⟩

/-- Capping the specified boundary kills every loop in an allowed annular region. -/
theorem boundaryAnnulusRegion_inclusion_nullhomotopic
    {S : Type} [TopologicalSpace S] (Q B U : Set S)
    (h : BoundaryAnnulusRegion Q B U)
    (hB : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥B, S)).Nullhomotopic) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, S)).Nullhomotopic := by
  obtain ⟨f, hf⟩ := boundaryAnnulusRegion_inclusion_homotopic_into_boundary Q B U h
  obtain ⟨p, hp⟩ := hB.comp_left f
  exact ⟨p, hf.trans hp⟩

/-- The literal chart circle contracts through its original chart disk. -/
theorem chartBoundary_inclusion_nullhomotopic
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 ≤ R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥((chartAt Plane x).symm '' Metric.sphere ((chartAt Plane x) x) R), S)).Nullhomotopic := by
  let E := chartAt Plane x
  let K := Metric.closedBall (E x) R
  let B := E.symm '' Metric.sphere (E x) R
  let d : C(↥K, S) := ⟨fun z => E.symm z.val, by
    apply E.continuousOn_symm.comp_continuous continuous_subtype_val
    intro z
    exact htarget z.property⟩
  have hd : IsEmbedding d := (d.continuous.isClosedEmbedding (by
    intro a b hab
    exact Subtype.ext (E.symm.injOn (htarget a.property) (htarget b.property) hab))).isEmbedding
  have hB : B ⊆ Set.range d := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨⟨z, Metric.sphere_subset_closedBall hz⟩, rfl⟩
  let e := hd.toHomeomorph
  let k : C(↥B, ↥K) :=
    (⟨e.symm, e.symm.continuous⟩ : C(↥(Set.range d), ↥K)).comp
      ⟨fun z => ⟨z.val, hB z.property⟩, by fun_prop⟩
  letI : ContractibleSpace K := Metric.contractibleSpace_closedBall hR
  have hh := ((id_nullhomotopic K).comp_right d).comp_left k
  have heq : (d.comp (ContinuousMap.id K)).comp k =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥B, S)) := by
    ext z
    exact congrArg Subtype.val (e.apply_symm_apply ⟨z.val, hB z.property⟩)
  rw [heq] at hh
  exact hh

/-- Positive-degree singular homology detects no class carried by a nullhomotopic map. -/
theorem positiveHomologyMap_eq_zero_of_nullhomotopic
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : f.Nullhomotopic) (n : ℕ) (hn : 0 < n) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj RZ).map
      (TopCat.ofHom f) = 0 := by
  obtain ⟨p, ⟨h⟩⟩ := hf
  let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) n).obj RZ
  have hh := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom f) (g := TopCat.ofHom (ContinuousMap.const X p)) h RZ n
  change F.map (TopCat.ofHom f) = F.map (TopCat.ofHom (ContinuousMap.const X p)) at hh
  rw [hh]
  let c : TopCat.of X ⟶ TopCat.of Unit := TopCat.ofHom (ContinuousMap.const X ())
  let q : TopCat.of Unit ⟶ TopCat.of Y := TopCat.ofHom (ContinuousMap.const Unit p)
  have heq : TopCat.ofHom (ContinuousMap.const X p) = c ≫ q := rfl
  rw [heq, F.map_comp]
  have hz := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n RZ (TopCat.of Unit) (Nat.ne_zero_of_lt hn)
  have hq : F.map q = 0 := hz.eq_of_src _ _
  rw [hq, comp_zero]

/-- Every standard complementary region has zero positive-degree homology image
in the closed source; the annular case uses the actual original chart cap. -/
theorem standardRegion_positive_homologyInclusion_eq_zero
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (x : S) (R : ℝ) (hR : 0 ≤ R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target)
    (Q U : Set S)
    (h : DiskRegion Q U ∨ BoundaryAnnulusRegion Q
      ((chartAt Plane x).symm '' Metric.sphere ((chartAt Plane x) x) R) U)
    (n : ℕ) (hn : 0 < n) : homologyInclusion S U n = 0 := by
  apply positiveHomologyMap_eq_zero_of_nullhomotopic _ _ n hn
  rcases h with hd | ha
  · exact diskRegion_inclusion_nullhomotopic Q U hd
  · exact boundaryAnnulusRegion_inclusion_nullhomotopic Q _ U ha
      (chartBoundary_inclusion_nullhomotopic S x R hR htarget)

/-- The entire open complement has nullhomotopic inclusion when each of its
actual components is standard. This does not require a finite component list. -/
theorem standardComplement_inclusion_nullhomotopic
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    [PathConnectedSpace S]
    (x : S) (R : ℝ) (hR : 0 ≤ R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target)
    (Q A : Set S) (hA : IsClosed A)
    (hstandard : ∀ U : Set S, CurveComplex.HyperellipticModel.IsComplementComponent A U →
      DiskRegion Q U ∨ BoundaryAnnulusRegion Q
        ((chartAt Plane x).symm '' Metric.sphere ((chartAt Plane x) x) R) U) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Aᶜ, S)).Nullhomotopic := by
  letI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace Plane S
  letI : LocallyConnectedSpace ↥(Aᶜ) := hA.isOpen_compl.locallyConnectedSpace
  apply nullhomotopic_of_connectedComponent_restrictions
  intro y
  let U := connectedComponentIn Aᶜ y.val
  have hU : CurveComplex.HyperellipticModel.IsComplementComponent A U :=
    CurveComplex.HyperellipticModel.complementComponent_iff_componentIn.mpr
      ⟨y.val, y.property, rfl⟩
  have hn : (⟨Subtype.val, continuous_subtype_val⟩ : C(↥U, S)).Nullhomotopic := by
    rcases hstandard U hU with hd | ha
    · exact diskRegion_inclusion_nullhomotopic Q U hd
    · exact boundaryAnnulusRegion_inclusion_nullhomotopic Q _ U ha
        (chartBoundary_inclusion_nullhomotopic S x R hR htarget)
  let k : C(connectedComponent y, ↥U) :=
    ⟨fun z => ⟨z.val.val, by
      dsimp only [U]
      rw [connectedComponentIn_eq_image y.property]
      exact ⟨z.val, z.property, rfl⟩⟩, by fun_prop⟩
  exact hn.comp_left k

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
