import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseCircleFundamentalCycle
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz CircleFundamentalCycle CircleHomologyComputation
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CircleReflectionProof

def invMap : C(Circle,Circle) := ⟨fun z => z⁻¹, continuous_inv⟩
lemma inv_east (z : Circle) (hz : z ∈ U) : z⁻¹ ∈ U := by
  change z ≠ 1 at hz
  change z⁻¹ ≠ 1
  simpa using hz
lemma inv_west (z : Circle) (hz : z ∈ V) : z⁻¹ ∈ V := by
  change z ≠ -1 at hz
  change z⁻¹ ≠ -1
  intro h
  apply hz
  have hh := congrArg Inv.inv h
  simpa using hh

def invOn (A : Set X) (h : ∀ z ∈ A, z⁻¹ ∈ A) : TopCat.of A ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun z => ⟨z.val⁻¹,h z.val z.property⟩,
    (continuous_inv.comp continuous_subtype_val).subtype_mk _⟩
def invEast := invOn U inv_east
def invWest := invOn V inv_west
def invOverlap := invOn (U ∩ V) (fun z h => ⟨inv_east z h.1, inv_west z h.2⟩)

lemma push_inv (A : Set X) (h : ∀ z ∈ A, z⁻¹ ∈ A) (n : ℕ)
    (c : coverOrdinaryChains X A n) :
    coverOrdinaryPush X A n (singularFinsuppPush (invOn A h) n c) =
      singularFinsuppPush (TopCat.ofHom invMap) n (coverOrdinaryPush X A n c) := by
  classical
  simp only [coverOrdinaryPush,singularFinsuppPush,Finsupp.lmapDomain_apply,
    ← Finsupp.mapDomain_comp]
  congr 1

def imageEast := singularFinsuppPush invEast 1 eastOrdinaryChain
def imageWest := singularFinsuppPush invWest 1 westOrdinaryChain
def imageOverlap := singularFinsuppPush invOverlap 0 overlapOrdinaryChain
def imagePair : (mvPairComplex X U V).X 1 := (imageEast,imageWest)
def imageSmall : (mvSmallComplex X U V).X 1 := coverOrdinarySum X U V 1 imagePair
def imageChain := singularFinsuppPush (TopCat.ofHom invMap) 1 circleBoundaryChain

lemma imageSmall_val : imageSmall.val = imageChain := by
  change coverOrdinaryPush X U 1 imageEast + coverOrdinaryPush X V 1 imageWest = _
  rw [imageEast,imageWest,invEast,invWest,push_inv,push_inv,eastOrdinaryChain_push,westOrdinaryChain_push,
    ← map_add,parts_sum]
  rfl

lemma imageChain_cycle : singularBoundaryFinsupp X 0 imageChain = 0 := by
  rw [imageChain,singularFinsuppPush_boundary,circle_boundary_is_cycle,map_zero]

lemma imageSmall_cycle : (mvSmallComplex X U V).d 1 0 imageSmall = 0 := by
  apply Subtype.ext
  change singularBoundaryFinsupp X 0 imageSmall.val = 0
  rw [imageSmall_val]
  exact imageChain_cycle

lemma imagePair_boundary : (mvDifference X U V).f 0 imageOverlap =
    (mvPairComplex X U V).d 1 0 imagePair := by
  apply (coverOrdinaryPairEquiv X U V 0).injective
  apply Prod.ext <;> apply Subtype.ext
  · change coverOrdinaryPush X U 0 (coverOrdinaryDifference X U V 0 imageOverlap).1 =
      coverOrdinaryPush X U 0 (singularBoundaryFinsupp (TopCat.of U) 0 imageEast)
    rw [coverOrdinaryDifference_push_fst,← coverOrdinaryPush_boundary,
      imageOverlap,imageEast,invOverlap,invEast,push_inv,push_inv,overlapOrdinaryChain_push,
      eastOrdinaryChain_push,singularFinsuppPush_boundary,east_boundary]
  · change coverOrdinaryPush X V 0 (coverOrdinaryDifference X U V 0 imageOverlap).2 =
      coverOrdinaryPush X V 0 (singularBoundaryFinsupp (TopCat.of V) 0 imageWest)
    rw [coverOrdinaryDifference_push_snd,← coverOrdinaryPush_boundary,
      imageOverlap,imageWest,invOverlap,invWest,push_inv,push_inv,overlapOrdinaryChain_push,
      westOrdinaryChain_push,singularFinsuppPush_boundary,west_boundary,map_neg]

lemma imageSmall_connecting :
    mvConnecting X U V 0 (cycleClass (mvSmallComplex X U V) 1 imageSmall imageSmall_cycle) =
      cycleClass (mvOrdinaryComplex X (U ∩ V)) 0 imageOverlap
        (by rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl) := by
  have h := (mvShortExact X U V).δ_eq 1 0 (by simp)
    (scalar _ imageSmall) (by dsimp only [mvShortComplex]; rw [scalar_naturality,imageSmall_cycle,scalar_eq_zero])
    (scalar _ imagePair) (by dsimp only [mvShortComplex]; rw [scalar_naturality]; rfl)
    (scalar _ imageOverlap) (by dsimp only [mvShortComplex]; rw [scalar_naturality,scalar_naturality,imagePair_boundary])
    0 (by simp)
  exact congrArg (fun f => f (1:ℤ)) h

lemma image_connecting :
    mvAmbientConnecting X U V CircleCoverGeometry.eastArc_open CircleCoverGeometry.westArc_open
      CircleCoverGeometry.arcs_cover 0 (cycleClass (mvAmbientComplex X) 1 imageChain imageChain_cycle) =
      cycleClass (mvOrdinaryComplex X (U ∩ V)) 0 imageOverlap
        (by rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl) := by
  have hm := cycleClass_map (mvSmallInclusion X U V) 1 imageSmall imageSmall_cycle
    (show (mvAmbientComplex X).d 1 (1-1) ((mvSmallInclusion X U V).f 1 imageSmall) = 0 by
      change singularBoundaryFinsupp X 0 imageSmall.val = 0
      rw [imageSmall_val]; exact imageChain_cycle)
  have he : cycleClass (mvAmbientComplex X) 1 imageChain imageChain_cycle =
      HomologicalComplex.homologyMap (mvSmallInclusion X U V) 1
        (cycleClass (mvSmallComplex X U V) 1 imageSmall imageSmall_cycle) := by
    simpa only [show (mvSmallInclusion X U V).f 1 imageSmall = imageChain from imageSmall_val] using hm.symm
  rw [he]
  exact (congrArg (fun f => f (cycleClass (mvSmallComplex X U V) 1 imageSmall imageSmall_cycle))
    (mvAmbientConnecting_comparison X U V CircleCoverGeometry.eastArc_open
      CircleCoverGeometry.westArc_open CircleCoverGeometry.arcs_cover 0)).trans imageSmall_connecting

lemma inverse_upper_lower (p : ↥(U ∩ V)) (hp : p.val ∈ CircleCoverGeometry.upperArc) :
    (invOverlap p).val ∈ CircleCoverGeometry.lowerArc := by
  change 0 < (p.val : ℂ).im at hp
  change ((p.val⁻¹ : Circle) : ℂ).im < 0
  rw [Circle.coe_inv_eq_conj, Complex.conj_im]
  exact neg_neg_of_pos hp
lemma inverse_lower_upper (p : ↥(U ∩ V)) (hp : p.val ∈ CircleCoverGeometry.lowerArc) :
    (invOverlap p).val ∈ CircleCoverGeometry.upperArc := by
  change (p.val : ℂ).im < 0 at hp
  change 0 < ((p.val⁻¹ : Circle) : ℂ).im
  rw [Circle.coe_inv_eq_conj, Complex.conj_im]
  exact neg_pos.mpr hp
lemma inverse_point_simplex (p : ↥(U ∩ V)) :
    (TopCat.toSSet.map invOverlap).app (.op ⦋0⦌) (pointSimplex p) =
      pointSimplex (invOverlap p) := by
  apply (TopCat.toSSetObjEquiv _ (.op ⦋0⦌)).injective
  rfl
lemma imageOverlap_coordinates :
    overlapCoordinatesIso.hom ((ordinaryHomologyIso X (U ∩ V) 0).hom
      (cycleClass (mvOrdinaryComplex X (U ∩ V)) 0 imageOverlap
        (by rw [HomologicalComplex.shape _ _ _ (by simp)]; rfl))) = (1,-1) := by
  rw [← zeroClassMap_apply]
  change overlapCoordinatesIso.hom ((singularHomologyRepresentation (TopCat.of ↥(U ∩ V)) 0).hom
    (zeroClassMap (mvAmbientComplex (TopCat.of ↥(U ∩ V))) imageOverlap)) = _
  have he : imageOverlap = Finsupp.single (pointSimplex (invOverlap lowerPoint)) 1 -
      Finsupp.single (pointSimplex (invOverlap upperPoint)) 1 := by
    simp only [imageOverlap,overlapOrdinaryChain,map_sub,singularFinsuppPush,
      Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    change Finsupp.single ((TopCat.toSSet.map invOverlap).app (.op ⦋0⦌) (pointSimplex lowerPoint)) 1 - Finsupp.single ((TopCat.toSSet.map invOverlap).app (.op ⦋0⦌) (pointSimplex upperPoint)) 1 = _
    rw [inverse_point_simplex,inverse_point_simplex]
  rw [he,map_sub,map_sub,singular_point_class,singular_point_class,map_sub]
  have hl := congrArg (fun f => f (1:ℤ)) (overlapPoint_coordinates (invOverlap lowerPoint))
  have hu := congrArg (fun f => f (1:ℤ)) (overlapPoint_coordinates (invOverlap upperPoint))
  rw [overlapMap_upper _ (inverse_lower_upper lowerPoint lowerPoint_lower)] at hl
  rw [overlapMap_lower _ (inverse_upper_lower upperPoint upperPoint_upper)] at hu
  change overlapCoordinatesIso.hom (pointClass _ (pointSimplex (invOverlap lowerPoint)) 1) = (1,0) at hl
  change overlapCoordinatesIso.hom (pointClass _ (pointSimplex (invOverlap upperPoint)) 1) = (0,1) at hu
  rw [hl,hu]
  rfl

lemma image_fundamental : (HF 1).map (TopCat.ofHom invMap) fundamentalClass =
    (singularHomologyRepresentation X 1).hom
      (cycleClass (mvAmbientComplex X) 1 imageChain imageChain_cycle) := by
  have hn := congrArg (fun f => f (cycleClass (mvAmbientComplex X) 1 circleBoundaryChain circle_boundary_is_cycle))
    (singularHomologyRepresentation_naturality (TopCat.ofHom invMap) 1)
  have hm := cycleClass_map (singularFinsuppMap (TopCat.ofHom invMap)) 1
    circleBoundaryChain circle_boundary_is_cycle
    (show (mvAmbientComplex X).d 1 (1-1) ((singularFinsuppMap (TopCat.ofHom invMap)).f 1 circleBoundaryChain) = 0 by
      rw [singularFinsuppMap_f]
      change singularBoundaryFinsupp X 0 imageChain = 0
      exact imageChain_cycle)
  simp only [singularFinsuppMap_f] at hm
  exact hn.symm.trans (congrArg (singularHomologyRepresentation X 1).hom hm)

lemma inverse_fundamental_coordinate :
    circleH1Iso.hom ((HF 1).map (TopCat.ofHom invMap) fundamentalClass) = 1 := by
  rw [image_fundamental]
  change (overlapCoordinatesIso.hom ((ordinaryHomologyIso X (U ∩ V) 0).hom
    (mvAmbientConnecting X U V CircleCoverGeometry.eastArc_open CircleCoverGeometry.westArc_open
      CircleCoverGeometry.arcs_cover 0
      ((singularHomologyRepresentation X 1).inv ((singularHomologyRepresentation X 1).hom
        (cycleClass (mvAmbientComplex X) 1 imageChain imageChain_cycle)))))).1 = 1
  rw [Iso.hom_inv_id_apply,image_connecting,imageOverlap_coordinates]

lemma inverse_fundamental : (HF 1).map (TopCat.ofHom invMap) fundamentalClass = -fundamentalClass := by
  apply circleH1Iso.toLinearEquiv.injective
  change circleH1Iso.hom ((HF 1).map (TopCat.ofHom invMap) fundamentalClass) = circleH1Iso.hom (-fundamentalClass)
  rw [inverse_fundamental_coordinate,map_neg,fundamentalClass_coordinate]
  rfl

lemma inverse_homology : (HF 1).map (TopCat.ofHom invMap) = -(𝟙 (H Circle 1)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨n,rfl⟩ := fundamentalClass_generates x
  change ((HF 1).map (TopCat.ofHom invMap)).hom (n • fundamentalClass) = -(n • fundamentalClass)
  rw [map_zsmul,inverse_fundamental]
  exact zsmul_neg _ _
end CircleReflectionProof

open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.GenusOrientationCandidate

/-- The actual inverse map on the unit circle. -/
noncomputable def circleInverse : C(Circle,Circle) := ⟨fun z => z⁻¹, continuous_inv⟩

/-- The inverse map negates the actual first integral singular homology object. -/
theorem circleInverse_homologyMap_eq_neg_id :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).map (TopCat.ofHom circleInverse)) =
      -(𝟙 (H Circle 1)) := by
  exact CircleReflectionProof.inverse_homology

end CurveComplex.GenusOrientationCandidate
