import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import CurveComplexGenusTwo.Foundations.FiniteSupportTopology
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteLabelMovie

/-!
N1 of `harer_schoenflies_blueprint/c0_contraction/PLAN.md` (wave 83).
This is a generic existence assertion, with a fully specified disk object,
not a construction/proof or a surface-specific contraction assumption.
-/

open Set
open scoped BigOperators

namespace CurveComplex.FiniteArcDisk

abbrev DiskPlane := EuclideanSpace ℝ (Fin 2)
abbrev ClosedDisk := ↥(Metric.closedBall (0 : DiskPlane) 1)
abbrev DiskCircle := ↥(Metric.sphere (0 : DiskPlane) 1)

/-- A finite cyclic domain word, its exact affine target edges, and its literal
closed `Path.concat`. Zero edges and repeated labels are allowed. -/
structure CyclicAffineWord
    {ι W : Type*} [DecidableEq ι] [DecidableEq W]
    (A : AbstractSimplicialComplex ι) (K : AbstractSimplicialComplex W)
    (initial : ι → W) where
  edgeCount : ℕ
  vertex : Fin (edgeCount + 1) → ι
  vertex_closed : vertex (Fin.last edgeCount) = vertex 0
  edge_face : ∀ k : Fin edgeCount,
    ({vertex k.castSucc, vertex k.succ} : Finset ι) ∈ A.faces
  point : Fin (edgeCount + 1) → RealizationPoint K
  point_eq : ∀ k, point k =
    realizationVertex K (initial (vertex k)) (K.singleton_mem _)
  edge : (k : Fin edgeCount) → Path (point k.castSucc) (point k.succ)
  edge_weight : ∀ (k : Fin edgeCount) (t : EdgeTime) (w : W),
    (edge k t).weight w =
      (1 - (t : ℝ)) * (if initial (vertex k.castSucc) = w then 1 else 0) +
      (t : ℝ) * (if initial (vertex k.succ) = w then 1 else 0)
  point_closed : point (Fin.last edgeCount) = point 0
  loop : Path (point 0) (point 0)
  loop_eq : loop = (Path.concat point edge).cast rfl point_closed.symm

/-- A genuine finite triangulated disk, with a genuine boundary subcomplex.
The boundary vertex subtype is necessary: an abstract complex on all disk
vertices would force every interior singleton into the boundary. -/
structure FiniteDiskModel where
  vertexCount : ℕ
  complex : AbstractSimplicialComplex (Fin vertexCount)
  boundaryVertices : Finset (Fin vertexCount)
  boundary : AbstractSimplicialComplex ↥boundaryVertices
  boundary_faces : ∀ σ : Finset ↥boundaryVertices, σ ∈ boundary.faces →
    σ.image Subtype.val ∈ complex.faces
  face_card : ∀ σ : Finset (Fin vertexCount), σ ∈ complex.faces → σ.card ≤ 3
  boundary_face_card : ∀ σ : Finset ↥boundaryVertices, σ ∈ boundary.faces →
    σ.card ≤ 2
  boundaryInclusion : C(RealizationPoint boundary, RealizationPoint complex)
  boundaryInclusion_weight : ∀ (x : RealizationPoint boundary) (v : Fin vertexCount),
    (boundaryInclusion x).weight v =
      ∑ b : ↥boundaryVertices, if b.val = v then x.weight b else 0
  boundaryInclusion_closedEmbedding : Topology.IsClosedEmbedding boundaryInclusion
  diskHome : RealizationPoint complex ≃ₜ ClosedDisk
  boundaryHome : RealizationPoint boundary ≃ₜ DiskCircle
  boundaryHome_compat : ∀ x : RealizationPoint boundary,
    (boundaryHome x).val = (diskHome (boundaryInclusion x)).val
  boundary_exact : ∀ x : RealizationPoint complex,
    x ∈ Set.range boundaryInclusion ↔ ‖(diskHome x).val‖ = 1
  closed_faces : ∀ σ : Finset (Fin vertexCount), σ ∈ complex.faces →
    IsClosed (faceCarrier complex σ)
  faces_cover : ∀ x : RealizationPoint complex,
    ∃ σ : Finset (Fin vertexCount), σ ∈ complex.faces ∧ x ∈ faceCarrier complex σ

/-- The actual disk label map and boundary data consumed by relative carrier
filling. All maps use the project weak realization topology. -/
structure LabelledDisk
    {ι W : Type*} [DecidableEq ι] [DecidableEq W]
    (A : AbstractSimplicialComplex ι) (K : AbstractSimplicialComplex W)
    (initial : ι → W) (word : CyclicAffineWord A K initial)
    (allowedLabel : W → Prop) where
  disk : FiniteDiskModel
  label : Fin disk.vertexCount → W
  label_allowed : ∀ v, allowedLabel (label v)
  label_faces : ∀ σ : Finset (Fin disk.vertexCount), σ ∈ disk.complex.faces →
    σ.image label ∈ K.faces
  label_image_card : ∀ σ : Finset (Fin disk.vertexCount), σ ∈ disk.complex.faces →
    (σ.image label).card ≤ 3
  realizationMap : C(RealizationPoint disk.complex, RealizationPoint K)
  realizationMap_weight : ∀ x w,
    (realizationMap x).weight w =
      ∑ v : Fin disk.vertexCount, if label v = w then x.weight v else 0
  boundaryParam : C(EdgeTime, RealizationPoint disk.boundary)
  boundaryParam_surjective : Function.Surjective boundaryParam
  boundaryParam_fibers : ∀ t u : EdgeTime,
    boundaryParam t = boundaryParam u ↔
      t = u ∨ (t = 0 ∧ u = 1) ∨ (t = 1 ∧ u = 0)
  boundary_seam : boundaryParam 0 = boundaryParam 1
  reparam : EdgeTime ≃ₜ EdgeTime
  reparam_zero : reparam 0 = 0
  reparam_one : reparam 1 = 1
  reparamHomotopy : ContinuousMap.HomotopyRel
    (ContinuousMap.id EdgeTime) ⟨reparam, reparam.continuous⟩ ({0, 1} : Set EdgeTime)
  boundary_word : ∀ t : EdgeTime,
    realizationMap (disk.boundaryInclusion (boundaryParam t)) = word.loop (reparam t)
  /- `Path.concat` starts with a constant path. These m+1 blocks preserve that
  initial constant segment, followed by all m original edges in their order. -/
  wordTimes : Fin (word.edgeCount + 2) → EdgeTime
  wordTimes_strict : StrictMono (fun k => (wordTimes k : ℝ))
  wordTimes_zero : wordTimes 0 = 0
  wordTimes_one : wordTimes (Fin.last (word.edgeCount + 1)) = 1
  wordPieceTime : (k : Fin (word.edgeCount + 1)) →
    Path (wordTimes k.castSucc) (wordTimes k.succ)
  wordPieceTime_affine : ∀ (k : Fin (word.edgeCount + 1)) (t : EdgeTime),
    (wordPieceTime k t : ℝ) =
      (1 - (t : ℝ)) * (wordTimes k.castSucc : ℝ) +
      (t : ℝ) * (wordTimes k.succ : ℝ)
  wordPiece_constant : ∀ t : EdgeTime, word.loop (wordPieceTime 0 t) = word.point 0
  wordPiece_edge : ∀ (k : Fin word.edgeCount) (t : EdgeTime),
    word.loop (wordPieceTime k.succ t) = word.edge k t
  boundaryBlock : Fin (word.edgeCount + 1) → Finset (Finset ↥disk.boundaryVertices)
  boundaryBlock_faces : ∀ k σ, σ ∈ boundaryBlock k → σ ∈ disk.boundary.faces
  boundaryBlock_constant : ∀ σ, σ ∈ boundaryBlock 0 →
    (σ.image (fun b => label b.val)) ⊆ {initial (word.vertex 0)}
  boundaryBlock_edge : ∀ (k : Fin word.edgeCount) σ, σ ∈ boundaryBlock k.succ →
    (σ.image (fun b => label b.val)) ⊆
      {initial (word.vertex k.castSucc), initial (word.vertex k.succ)}
  boundaryBlock_exact : ∀ k : Fin (word.edgeCount + 1),
    (⋃ σ ∈ boundaryBlock k, faceCarrier disk.boundary σ) =
      Set.range (fun t : EdgeTime => boundaryParam (reparam.symm (wordPieceTime k t)))
  boundary_face_word : ∀ σ : Finset ↥disk.boundaryVertices, σ ∈ disk.boundary.faces →
    (σ.image (fun b => label b.val)) ⊆ {initial (word.vertex 0)} ∨
    ∃ k : Fin word.edgeCount,
      (σ.image (fun b => label b.val)) ⊆
        {initial (word.vertex k.castSucc), initial (word.vertex k.succ)}

end CurveComplex.FiniteArcDisk
