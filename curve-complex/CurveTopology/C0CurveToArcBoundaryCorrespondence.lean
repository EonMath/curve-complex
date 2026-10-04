import CurveComplexGenusTwo.Topology.ActualQTerminalSurgery
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.EdgeHomotopy
import C0FiniteTriangulatedDisk
import RegionalUnpositionedFiniteLabelDescent

set_option maxHeartbeats 0

/-! N5 of the wave-83 C₀ blueprint. Only the final existence assertion is a
proof obligation. Every regional relation is setwise on B and full frontier. -/
open Set
namespace CurveComplex.C0BoundaryCorrespondence
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
open CurveComplex.FiniteArcDisk

noncomputable section
variable (S : Type) [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (x : S) (R : ℝ)

/-- The source's literal regional proper arc, with all frontier excluded inside. -/
def RegionProperArc (F : Set S) :=
  {a : C(Interval, ↥F) // Topology.IsEmbedding a ∧
    (a 0).val ∈ boundaryCircle S x R ∧ (a 1).val ∈ boundaryCircle S x R ∧
    ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}

def regionBoundaryParallel (F : Set S) (a : RegionProperArc S x R F) : Prop :=
  ∃ b : C(Interval, ↥F), Topology.IsEmbedding b ∧
    (∀ t, (b t).val ∈ boundaryCircle S x R) ∧
    ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1, ↥F),
      Topology.IsEmbedding d ∧
      d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
        Set.range a.val ∪ Set.range b

abbrev IntrinsicEssentialArc (F : Set S) :=
  {a : RegionProperArc S x R F // ¬ regionBoundaryParallel S x R F a}

def intrinsicArcRel (F : Set S) (a b : IntrinsicEssentialArc S x R F) : Prop :=
  ∃ H : AmbientIsotopy ↥F,
    (∀ t, (fun y => H.map (t, y)) '' {y | y.val ∈ boundaryCircle S x R} =
      {y | y.val ∈ boundaryCircle S x R}) ∧
    (∀ t, (fun y => H.map (t, y)) '' {y | y.val ∈ frontier F} =
      {y | y.val ∈ frontier F}) ∧
    H.finalMap '' Set.range a.val.val = Set.range b.val.val

abbrev IntrinsicArcVertex (F : Set S) := Quot (intrinsicArcRel S x R F)
local instance (F : Set S) : DecidableEq (IntrinsicArcVertex S x R F) := Classical.decEq _
local instance : DecidableEq (ArcVertex S x R) := Classical.decEq _
local instance : DecidableEq (Vertex S) := Classical.decEq _

def intrinsicArcFaces (F : Set S) : Set (Finset (IntrinsicArcVertex S x R F)) :=
  {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc S x R F,
    (∀ u, Quot.mk (intrinsicArcRel S x R F) (rep u) = u.val) ∧
    ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}

/-- Compatibility is on distinct curve classes, not loop occurrences. -/
def Compatible (Fv : Finset (Vertex S)) (σ : Finset ↥Fv) : Prop :=
  ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j → geometricIntersection i.val j.val = 0

/-- The source's actual regional common-family predicate. -/
def RegionArcSystem (F : Set S) (τ : Finset (ArcVertex S x R)) : Prop :=
  τ.Nonempty ∧ ∃ rep : ↥τ → EssentialProperArc S x R,
    (∀ u, Quot.mk (arcRel S x R) (rep u) = u.val) ∧
    (∀ u, (∀ t, ((rep u).val.val t).val ∈ F) ∧
      ∀ t ∈ Set.Ioo (0 : Interval) 1, ((rep u).val.val t).val ∉ frontier F) ∧
    ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)

/-- Geometry already produced in the current source body. The finite retained
frontier family is part of the geometry, not an assumed arc contraction. -/
structure ActualBorderedRegions (Fv : Finset (Vertex S)) where
  representative : ↥Fv → EssentialCurve S
  representative_class : ∀ w, Quotient.mk (essentialCurveSetoid S) (representative w) = w.val
  representative_disjoint : ∀ u w, u ≠ w → geometricIntersection u.val w.val = 0 →
    Disjoint (representative u).val.image (representative w).val.image
  representative_interior : ∀ w, (representative w).val.image ⊆ interior (openDisk S x R)ᶜ
  region : Finset ↥Fv → Set S
  compact : ∀ σ, IsCompact (region σ)
  connected : ∀ σ, IsConnected (region σ)
  contains_boundary : ∀ σ, boundaryCircle S x R ⊆ region σ
  outside : ∀ σ, region σ ⊆ (openDisk S x R)ᶜ
  regular_closed : ∀ σ, closure (interior (region σ)) = region σ
  boundary_on_frontier : ∀ σ, boundaryCircle S x R ⊆ frontier (region σ)
  antitone : ∀ σ τ, σ ⊆ τ → region τ ⊆ region σ
  avoids_original : ∀ σ w, w ∈ σ → Disjoint (region σ) (representative w).val.image
  frontierCount : Finset ↥Fv → ℕ
  frontierCurve : (σ : Finset ↥Fv) → Fin (frontierCount σ) → EssentialCurve S
  frontier_disjoint : ∀ σ, Compatible S Fv σ → ∀ i j, i ≠ j →
    Disjoint (frontierCurve σ i).val.image (frontierCurve σ j).val.image
  frontier_boundary_disjoint : ∀ σ i,
    Disjoint (frontierCurve σ i).val.image (boundaryCircle S x R)
  frontier_exact : ∀ σ, Compatible S Fv σ → frontier (region σ) =
    boundaryCircle S x R ∪ ⋃ i, (frontierCurve σ i).val.image
  frontier_nonempty : ∀ σ, σ.Nonempty → Compatible S Fv σ → 0 < frontierCount σ

/-- Inclusion and reflection are exactly on *actual region-supported families*.
No inverse localization of an arbitrary Q isotopy is asserted. -/
structure RegionalArcComparison {Fv : Finset (Vertex S)}
    (G : ActualBorderedRegions S x R Fv) where
  complex : (σ : Finset ↥Fv) → AbstractSimplicialComplex (IntrinsicArcVertex S x R (G.region σ))
  faces_exact : ∀ σ, (complex σ).faces = intrinsicArcFaces S x R (G.region σ)
  includedArc : (σ : Finset ↥Fv) → Compatible S Fv σ →
    IntrinsicEssentialArc S x R (G.region σ) → EssentialProperArc S x R
  included_literal : ∀ σ hσ a t, ((includedArc σ hσ a).val.val t).val = (a.val.val t).val
  classMap : (σ : Finset ↥Fv) → Compatible S Fv σ →
    IntrinsicArcVertex S x R (G.region σ) → ArcVertex S x R
  classMap_mk : ∀ σ hσ a, classMap σ hσ (Quot.mk (intrinsicArcRel S x R (G.region σ)) a) =
    Quot.mk (arcRel S x R) (includedArc σ hσ a)
  faceMap : ∀ σ hσ μ, μ ∈ (complex σ).faces →
    μ.image (classMap σ hσ) ∈ (arcComplex S x R).faces ∧
      RegionArcSystem S x R (G.region σ) (μ.image (classMap σ hσ))
  faceReflection : ∀ σ hσ τ, RegionArcSystem S x R (G.region σ) τ ↔
    ∃ μ ∈ (complex σ).faces, μ.image (classMap σ hσ) = τ
  essential_restrict : ∀ σ (a : EssentialProperArc S x R),
    (∀ t, (a.val.val t).val ∈ G.region σ) →
    (∀ t ∈ Set.Ioo (0 : Interval) 1, (a.val.val t).val ∉ frontier (G.region σ)) →
    ∃ b : IntrinsicEssentialArc S x R (G.region σ), ∀ t, (b.val.val t).val = (a.val.val t).val
  proper_monotone : ∀ σ τ, σ ⊆ τ → ∀ a : EssentialProperArc S x R,
    ((∀ t, (a.val.val t).val ∈ G.region τ) ∧
      ∀ t ∈ Set.Ioo (0 : Interval) 1, (a.val.val t).val ∉ frontier (G.region τ)) →
    (∀ t, (a.val.val t).val ∈ G.region σ) ∧
      ∀ t ∈ Set.Ioo (0 : Interval) 1, (a.val.val t).val ∉ frontier (G.region σ)
  essential_nonempty : ∀ σ, σ.Nonempty → Compatible S Fv σ →
    Nonempty (IntrinsicEssentialArc S x R (G.region σ))

/-- The existing alignment contract, specialized to distinct quotient vertices
of a single face; all boundary motion is setwise. This upstream contract is
recorded explicitly, and is not a successful surgery or curve contraction. -/
def FaceSystemAlignment : Prop :=
  ∀ (τ : Finset (ArcVertex S x R)) (a b : ↥τ → EssentialProperArc S x R),
    (∀ u, Quot.mk (arcRel S x R) (a u) = u.val) →
    (∀ u, Quot.mk (arcRel S x R) (b u) = u.val) →
    (∀ u w, u ≠ w → Disjoint (Set.range (a u).val.val) (Set.range (a w).val.val)) →
    (∀ u w, u ≠ w → Disjoint (Set.range (b u).val.val) (Set.range (b w).val.val)) →
    ∃ H : AmbientIsotopy (Q S x R),
      (∀ t, (fun y => H.map (t, y)) '' boundaryQ S x R = boundaryQ S x R) ∧
      ∀ u, H.finalMap '' Set.range (a u).val.val = Set.range (b u).val.val

/-- N3's literal Pτ. A single common family witnesses all incidences. -/
def FaceCurveCarrier (τ : Finset (ArcVertex S x R)) (v : Vertex S) : Prop :=
  τ.Nonempty ∧ ∃ rep : ↥τ → EssentialProperArc S x R,
    (∀ u, Quot.mk (arcRel S x R) (rep u) = u.val) ∧
    (∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)) ∧
    ∃ d : EssentialCurve S, Quotient.mk (essentialCurveSetoid S) d = v ∧
      d.val.image ⊆ interior (openDisk S x R)ᶜ ∧
      ∀ u, Disjoint d.val.image (Set.range (fun t => ((rep u).val.val t).val))

/-- The exact finite support definition already used by the source consumer. -/
def loopSupport (v : Vertex S) (n : ℕ)
    (z : Fin (n + 1) → RealizationPoint (curveComplex S 0)) : Finset (Vertex S) :=
  insert v (Finset.univ.biUnion fun k => supportFinset (curveComplex S 0) (z k))

/-- Finite boundary correspondence only: there is no disk or contraction field.
Each original edge has its regional intrinsic arc; each original curve vertex
has an intrinsic finite arc block. Offsets retain every occurrence in order. -/
structure BoundaryCorrespondence {Fv : Finset (Vertex S)}
    (G : ActualBorderedRegions S x R Fv) (C : RegionalArcComparison S x R G)
    (v : Vertex S) (n : ℕ) (z : Fin (n + 1) → RealizationPoint (curveComplex S 0))
    (E : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (p : Path (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v))
      (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v))) where
  curveWord : CyclicAffineWord (curveComplex S 0) (curveComplex S 0) id
  curve_count : curveWord.edgeCount = n
  curve_nonempty : 0 < curveWord.edgeCount
  curve_point_exact : ∀ k : Fin (n + 1),
    curveWord.point (Fin.cast (congrArg (fun m => m + 1) curve_count.symm) k) = z k
  curve_edge_exact : ∀ k : Fin n,
    (curveWord.edge (Fin.cast curve_count.symm k)).toContinuousMap = (E k).toContinuousMap
  curve_loop_exact : curveWord.loop.toContinuousMap = p.toContinuousMap
  curve_base : curveWord.vertex 0 = v
  curve_support : ∀ k, curveWord.vertex k ∈ Fv
  curve_edge_compatible : ∀ k : Fin curveWord.edgeCount,
    Compatible S Fv {⟨curveWord.vertex k.castSucc, curve_support k.castSucc⟩,
      ⟨curveWord.vertex k.succ, curve_support k.succ⟩}
  curve_vertex_compatible : ∀ k : Fin curveWord.edgeCount,
    Compatible S Fv {⟨curveWord.vertex k.castSucc, curve_support k.castSucc⟩}
  edgeArc : (k : Fin curveWord.edgeCount) → IntrinsicEssentialArc S x R
    (G.region {⟨curveWord.vertex k.castSucc, curve_support k.castSucc⟩,
      ⟨curveWord.vertex k.succ, curve_support k.succ⟩})
  junction : Fin (curveWord.edgeCount + 1) → ArcVertex S x R
  junction_closed : junction (Fin.last curveWord.edgeCount) = junction 0
  junction_edgeArc : ∀ k : Fin curveWord.edgeCount, junction k.succ =
    C.classMap _ (curve_edge_compatible k)
      (Quot.mk (intrinsicArcRel S x R _) (edgeArc k))
  junction_left : ∀ k : Fin curveWord.edgeCount,
    FaceCurveCarrier S x R {junction k.succ} (curveWord.vertex k.castSucc)
  junction_right : ∀ k : Fin curveWord.edgeCount,
    FaceCurveCarrier S x R {junction k.succ} (curveWord.vertex k.succ)
  blockLength : Fin curveWord.edgeCount → ℕ
  intrinsicBlock : (k : Fin curveWord.edgeCount) → Fin (blockLength k + 1) →
    IntrinsicArcVertex S x R (G.region {⟨curveWord.vertex k.castSucc, curve_support k.castSucc⟩})
  intrinsicBlock_faces : ∀ (k : Fin curveWord.edgeCount) (j : Fin (blockLength k)),
    {intrinsicBlock k j.castSucc, intrinsicBlock k j.succ} ∈
      (C.complex {⟨curveWord.vertex k.castSucc, curve_support k.castSucc⟩}).faces
  block : (k : Fin curveWord.edgeCount) → Fin (blockLength k + 1) → ArcVertex S x R
  block_inclusion : ∀ k j, block k j = C.classMap _ (curve_vertex_compatible k) (intrinsicBlock k j)
  block_start : ∀ k, block k 0 = junction k.castSucc
  block_end : ∀ k, block k (Fin.last (blockLength k)) = junction k.succ
  block_vertex_carrier : ∀ k j,
    FaceCurveCarrier S x R {block k j} (curveWord.vertex k.castSucc)
  block_edge_carrier : ∀ k (j : Fin (blockLength k)),
    FaceCurveCarrier S x R {block k j.castSucc, block k j.succ} (curveWord.vertex k.castSucc)
  block_vertex_system : ∀ k j, RegionArcSystem S x R
    (G.region {⟨curveWord.vertex k.castSucc, curve_support k.castSucc⟩}) {block k j}
  block_edge_system : ∀ k (j : Fin (blockLength k)), RegionArcSystem S x R
    (G.region {⟨curveWord.vertex k.castSucc, curve_support k.castSucc⟩})
      {block k j.castSucc, block k j.succ}
  arcDomainCount : ℕ
  arcDomain : AbstractSimplicialComplex (Fin arcDomainCount)
  arcLabel : Fin arcDomainCount → ArcVertex S x R
  arcLabel_faces : ∀ τ, τ ∈ arcDomain.faces → τ.image arcLabel ∈ (arcComplex S x R).faces
  arcWord : CyclicAffineWord arcDomain (arcComplex S x R) arcLabel
  offset : Fin (curveWord.edgeCount + 1) → ℕ
  offset_zero : offset 0 = 0
  offset_step : ∀ k : Fin curveWord.edgeCount,
    offset k.succ = offset k.castSucc + blockLength k
  offset_last : offset (Fin.last curveWord.edgeCount) = arcWord.edgeCount
  block_occurrences : ∀ k (j : Fin (blockLength k + 1)),
    ∃ i : Fin (arcWord.edgeCount + 1), i.val = offset k.castSucc + j.val ∧
      arcLabel (arcWord.vertex i) = block k j

/-- N5 consumes the *existing* hp witness and source geometry, and manufactures
boundary data. N0 positioning/descent are proof dependencies, not premises here.
The zero-edge branch retains literal reflexivity of the original path. -/
theorem source_c0_curve_to_arc_boundary_correspondence
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (v : Vertex S)
    (p : Path (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v))
      (realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v)))
    (hp : IsFiniteAffineEdgePath (curveComplex S 0) p)
    (n : ℕ) (z : Fin (n + 1) → RealizationPoint (curveComplex S 0))
    (E : (k : Fin n) → Path (z k.castSucc) (z k.succ))
    (hx : realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v) = z 0)
    (hy : realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v) = z (Fin.last n))
    (hAffine : ∀ k, IsAffineVertexEdge (curveComplex S 0) (E k))
    (hpEq : p = (Path.concat z E).cast hx hy)
    (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (G : ActualBorderedRegions S x R (loopSupport S v n z))
    (C : RegionalArcComparison S x R G)
    (alignment : FaceSystemAlignment S x R) :
    (n = 0 ∧ p = Path.refl _) ∨
      Nonempty (BoundaryCorrespondence S x R G C v n z E p) := by
  classical
  by_cases hn : n = 0
  · subst n
    left
    refine ⟨rfl, ?_⟩
    rw [hpEq]
    apply DFunLike.ext
    intro t
    rw [Path.concat_zero]
    change z 0 = realizationVertex (curveComplex S 0) v ((curveComplex S 0).singleton_mem v)
    exact hx.symm
  right
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have carrier : ∀ (σ : Finset ↥(loopSupport S v n z))
      (w : ↥(loopSupport S v n z)), w ∈ σ →
      ∀ τ, RegionArcSystem S x R (G.region σ) τ →
        FaceCurveCarrier S x R τ w.val := by
    intro σ w hw τ hτ
    obtain ⟨hne, rep, hclass, hregion, hd⟩ := hτ
    refine ⟨hne, rep, hclass, hd, G.representative w,
      G.representative_class w, G.representative_interior w, ?_⟩
    intro u
    apply (G.avoids_original σ w hw).symm.mono_right
    rintro y ⟨t, rfl⟩
    exact (hregion u).1 t
  have included_system : ∀ σ (hσ : Compatible S (loopSupport S v n z) σ)
      (a : IntrinsicEssentialArc S x R (G.region σ)),
      RegionArcSystem S x R (G.region σ)
        {C.classMap σ hσ (Quot.mk (intrinsicArcRel S x R _) a)} := by
    intro σ hσ a
    simpa only [Finset.image_singleton] using
      (C.faceMap σ hσ _ ((C.complex σ).singleton_mem
        (Quot.mk (intrinsicArcRel S x R _) a))).2
  have restrict_class : ∀ σ τ (hσ : Compatible S (loopSupport S v n z) σ)
      (hτ : Compatible S (loopSupport S v n z) τ), σ ⊆ τ →
      ∀ a : IntrinsicEssentialArc S x R (G.region τ),
      ∃ b : IntrinsicEssentialArc S x R (G.region σ),
        C.classMap σ hσ (Quot.mk (intrinsicArcRel S x R _) b) =
          C.classMap τ hτ (Quot.mk (intrinsicArcRel S x R _) a) := by
    intro σ τ hσ hτ hστ a
    let aq := C.includedArc τ hτ a
    have hin : (∀ t, (aq.val.val t).val ∈ G.region τ) ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (aq.val.val t).val ∉ frontier (G.region τ) := by
      constructor
      · intro t
        rw [C.included_literal]
        exact (a.val.val t).property
      · intro t ht
        rw [C.included_literal]
        exact a.val.property.2.2.2 t ht
    obtain ⟨b, hb⟩ := C.essential_restrict σ aq
      (C.proper_monotone σ τ hστ aq hin).1
      (C.proper_monotone σ τ hστ aq hin).2
    refine ⟨b, ?_⟩
    rw [C.classMap_mk, C.classMap_mk]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    apply DFunLike.ext
    intro t
    apply Subtype.ext
    exact (C.included_literal σ hσ b t).trans (hb t)
  let K := curveComplex S 0
  have in_vertex : ∀ (σ : Finset (Vertex S)) (hσ : σ ∈ K.faces)
      (a : Vertex S) (ha : a ∈ σ),
      faceInclusion K σ hσ (finiteSimplexVertex σ a ha) =
        realizationVertex K a (K.singleton_mem a) := by
    intro σ hσ a ha
    apply RealizationPoint.ext
    funext w
    rw [finiteSimplexVertex_faceInclusion_weight, realizationVertex_weight]
  have vertex_injective : Function.Injective
      (fun a => realizationVertex K a (K.singleton_mem a)) := by
    intro a b hab
    have hw := congrArg (fun q : RealizationPoint K => q.weight a) hab
    rw [realizationVertex_weight, realizationVertex_weight] at hw
    by_contra h
    simp [h] at hw
  have z_vertex : ∀ k : Fin (n + 1),
      ∃ a : Vertex S, z k = realizationVertex K a (K.singleton_mem a) := by
    intro k
    by_cases hk : k.val < n
    · let j : Fin n := ⟨k.val, hk⟩
      obtain ⟨σ, hσ, a, b, ha, hb, hs, ht, he⟩ := hAffine j
      refine ⟨a, ?_⟩
      have hj : j.castSucc = k := Fin.ext rfl
      rw [← hj]
      exact hs.trans (in_vertex σ hσ a ha)
    · let j : Fin n := ⟨n - 1, by omega⟩
      obtain ⟨σ, hσ, a, b, ha, hb, hs, ht, he⟩ := hAffine j
      refine ⟨b, ?_⟩
      have hj : j.succ = k := Fin.ext (by dsimp [j]; omega)
      rw [← hj]
      exact ht.trans (in_vertex σ hσ b hb)
  choose vertex hvertex using z_vertex
  have vclosed : vertex (Fin.last n) = vertex 0 := by
    apply vertex_injective
    exact (hvertex _).symm.trans ((hy.symm.trans hx).trans (hvertex _))
  have vbase : vertex 0 = v := by
    apply vertex_injective
    exact (hvertex 0).symm.trans hx.symm
  have vsupport : ∀ k, vertex k ∈ loopSupport S v n z := by
    intro k
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [mem_supportFinset_iff, hvertex, realizationVertex_weight]
    simp
  have vface : ∀ k : Fin n, {vertex k.castSucc, vertex k.succ} ∈ K.faces := by
    intro k
    obtain ⟨σ, hσ, a, b, ha, hb, hs, ht, he⟩ := hAffine k
    have hal : vertex k.castSucc = a := vertex_injective
      ((hvertex _).symm.trans (hs.trans (in_vertex σ hσ a ha)))
    have hbl : vertex k.succ = b := vertex_injective
      ((hvertex _).symm.trans (ht.trans (in_vertex σ hσ b hb)))
    rw [hal, hbl]
    exact (K.isRelLowerSet_faces hσ).2 (by simp [Finset.insert_subset_iff, ha, hb])
      (Finset.insert_nonempty _ _)
  have eweight : ∀ (k : Fin n) (t : EdgeTime) (w : Vertex S),
      (E k t).weight w =
        (1 - (t : ℝ)) * (if vertex k.castSucc = w then 1 else 0) +
        (t : ℝ) * (if vertex k.succ = w then 1 else 0) := by
    intro k t w
    obtain ⟨σ, hσ, a, b, ha, hb, hs, ht, he⟩ := hAffine k
    have hal : vertex k.castSucc = a := vertex_injective
      ((hvertex _).symm.trans (hs.trans (in_vertex σ hσ a ha)))
    have hbl : vertex k.succ = b := vertex_injective
      ((hvertex _).symm.trans (ht.trans (in_vertex σ hσ b hb)))
    rw [hal, hbl, he]
    change (faceInclusion (curveComplex S 0) σ hσ
      (finiteSimplexSegment σ (finiteSimplexVertex σ a ha)
        (finiteSimplexVertex σ b hb) t)).weight w = _
    by_cases hw : w ∈ σ
    · simp [faceInclusion,
        finiteSimplexSegment, finiteSimplexVertex, hw, eq_comm]
    · have hwa : w ≠ a := fun e => hw (e.symm ▸ ha)
      have hwb : w ≠ b := fun e => hw (e.symm ▸ hb)
      simp [faceInclusion,
        finiteSimplexSegment, finiteSimplexVertex, hw, hwa, hwb, eq_comm]
  have zclosed : z (Fin.last n) = z 0 := hy.symm.trans hx
  let curveWord : CyclicAffineWord K K id := {
    edgeCount := n
    vertex := vertex
    vertex_closed := vclosed
    edge_face := vface
    point := z
    point_eq := hvertex
    edge := E
    edge_weight := eweight
    point_closed := zclosed
    loop := (Path.concat z E).cast rfl zclosed.symm
    loop_eq := rfl }
  have curve_loop_exact : curveWord.loop.toContinuousMap = p.toContinuousMap := by
    rw [hpEq]
    rfl
  have edge_compatible : ∀ k : Fin n,
      Compatible S (loopSupport S v n z)
        {⟨vertex k.castSucc, vsupport k.castSucc⟩, ⟨vertex k.succ, vsupport k.succ⟩} := by
    intro k u hu w hw huw
    have hs : ∀ a : ↥(loopSupport S v n z),
        a ∈ ({⟨vertex k.castSucc, vsupport k.castSucc⟩,
          ⟨vertex k.succ, vsupport k.succ⟩} : Finset ↥(loopSupport S v n z)) →
        a.val ∈ ({vertex k.castSucc, vertex k.succ} : Finset (Vertex S)) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
      rcases ha with rfl | rfl <;> simp
    have hf := (vface k).2 u.val (hs u hu) w.val (hs w hw)
      (fun he => huw (Subtype.ext he))
    exact Nat.eq_zero_of_le_zero hf
  have vertex_compatible : ∀ k : Fin n,
      Compatible S (loopSupport S v n z) {⟨vertex k.castSucc, vsupport k.castSucc⟩} := by
    intro k u hu w hw huw
    exact False.elim (huw ((Finset.mem_singleton.mp hu).trans
      (Finset.mem_singleton.mp hw).symm))
  have edge_nonempty : ∀ k : Fin n,
      Nonempty (IntrinsicEssentialArc S x R
        (G.region {⟨vertex k.castSucc, vsupport k.castSucc⟩,
          ⟨vertex k.succ, vsupport k.succ⟩})) := by
    intro k
    exact C.essential_nonempty _ (Finset.insert_nonempty _ _) (edge_compatible k)
  let edgeArc := fun k => Classical.choice (edge_nonempty k)
  let edgeLabel : Fin n → ArcVertex S x R := fun k =>
    C.classMap _ (edge_compatible k) (Quot.mk (intrinsicArcRel S x R _) (edgeArc k))
  have edge_left : ∀ k : Fin n,
      FaceCurveCarrier S x R {edgeLabel k} (vertex k.castSucc) := by
    intro k
    exact carrier _ ⟨_, vsupport k.castSucc⟩ (by simp) _
      (included_system _ (edge_compatible k) (edgeArc k))
  have edge_right : ∀ k : Fin n,
      FaceCurveCarrier S x R {edgeLabel k} (vertex k.succ) := by
    intro k
    exact carrier _ ⟨_, vsupport k.succ⟩ (by simp) _
      (included_system _ (edge_compatible k) (edgeArc k))
  let lastEdge : Fin n := ⟨n - 1, by omega⟩
  let junction : Fin (n + 1) → ArcVertex S x R := Fin.cases (edgeLabel lastEdge) edgeLabel
  have junction_succ : ∀ k : Fin n, junction k.succ = edgeLabel k := by
    intro k
    simp [junction]
  have junction_closed : junction (Fin.last n) = junction 0 := by
    have hl : (Fin.last n) = lastEdge.succ := Fin.ext (by dsimp [lastEdge]; omega)
    rw [hl, junction_succ]
    rfl
  have outgoing : ∀ k : Fin n,
      ∃ b : IntrinsicEssentialArc S x R
          (G.region {⟨vertex k.castSucc, vsupport k.castSucc⟩}),
        C.classMap _ (vertex_compatible k) (Quot.mk (intrinsicArcRel S x R _) b) =
          junction k.succ := by
    intro k
    rw [junction_succ]
    exact restrict_class _ _ (vertex_compatible k) (edge_compatible k)
      (by simp) (edgeArc k)
  have incoming : ∀ k : Fin n,
      ∃ b : IntrinsicEssentialArc S x R
          (G.region {⟨vertex k.castSucc, vsupport k.castSucc⟩}),
        C.classMap _ (vertex_compatible k) (Quot.mk (intrinsicArcRel S x R _) b) =
          junction k.castSucc := by
    intro k
    let prev : Fin n := ⟨if k.val = 0 then n - 1 else k.val - 1, by
      split_ifs <;> omega⟩
    have hprev_vertex : vertex prev.succ = vertex k.castSucc := by
      by_cases hk : k.val = 0
      · have hp : prev.succ = Fin.last n := Fin.ext (by simp [prev, hk]; omega)
        have hz : k.castSucc = 0 := Fin.ext hk
        rw [hp, hz]
        exact vclosed
      · have hp : prev.succ = k.castSucc := Fin.ext (by simp [prev, hk]; omega)
        rw [hp]
    have hprev_junction : junction k.castSucc = edgeLabel prev := by
      by_cases hk : k.val = 0
      · have hz : k.castSucc = 0 := Fin.ext hk
        have hp : prev = lastEdge := Fin.ext (by simp [prev, lastEdge, hk])
        rw [hz, hp]
        rfl
      · have hp : prev.succ = k.castSucc := Fin.ext (by simp [prev, hk]; omega)
        rw [← hp, junction_succ]
    rw [hprev_junction]
    apply restrict_class _ _ (vertex_compatible k) (edge_compatible prev)
      _ (edgeArc prev)
    intro w hw
    have he : w = ⟨vertex k.castSucc, vsupport k.castSucc⟩ := Finset.mem_singleton.mp hw
    rw [he]
    have he' : (⟨vertex k.castSucc, vsupport k.castSucc⟩ : ↥(loopSupport S v n z)) =
        ⟨vertex prev.succ, vsupport prev.succ⟩ := Subtype.ext hprev_vertex.symm
    rw [he']
    simp
  have path_from_movie : ∀ σ
      (u w : IntrinsicArcVertex S x R (G.region σ))
      (steps : ℕ) (labels : ℕ → IntrinsicArcVertex S x R (G.region σ)),
      labels 0 = u →
      (∀ t < steps, {labels t, labels (t + 1)} ∈ (C.complex σ).faces) →
      {labels steps, w} ∈ (C.complex σ).faces →
      ∃ (m : ℕ) (nodes : Fin (m + 1) → IntrinsicArcVertex S x R (G.region σ)),
        nodes 0 = u ∧ nodes (Fin.last m) = w ∧
        ∀ j : Fin m, {nodes j.castSucc, nodes j.succ} ∈ (C.complex σ).faces := by
    intro σ u w steps labels hzero hstep hend
    let nodes : Fin (steps + 2) → IntrinsicArcVertex S x R (G.region σ) :=
      Fin.lastCases w (fun i : Fin (steps + 1) => labels i.val)
    refine ⟨steps + 1, nodes, ?_, ?_, ?_⟩
    · have hz : (0 : Fin (steps + 2)) = (0 : Fin (steps + 1)).castSucc := rfl
      rw [hz]
      change Fin.lastCases w (fun i : Fin (steps + 1) => labels i.val)
        (0 : Fin (steps + 1)).castSucc = u
      rw [Fin.lastCases_castSucc]
      exact hzero
    · simp [nodes]
    · intro j
      have hl : nodes j.castSucc = labels j.val := by simp [nodes]
      rw [hl]
      by_cases hj : j.val < steps
      · let i : Fin (steps + 1) := ⟨j.val + 1, by omega⟩
        have hi : j.succ = i.castSucc := Fin.ext rfl
        rw [hi]
        change {labels j.val, (Fin.lastCases w
          (fun q : Fin (steps + 1) => labels q.val) i.castSucc)} ∈ (C.complex σ).faces
        rw [Fin.lastCases_castSucc]
        exact hstep j.val hj
      · have he : j.val = steps := by omega
        have hi : j.succ = Fin.last (steps + 1) := Fin.ext (by simp [he])
        rw [hi, he]
        simpa [nodes] using hend
  have regional_path : ∀ (w : ↥(loopSupport S v n z))
      (a b : IntrinsicEssentialArc S x R (G.region {w})),
      ∃ (m : ℕ) (nodes : Fin (m + 1) → IntrinsicArcVertex S x R (G.region {w})),
        nodes 0 = Quot.mk (intrinsicArcRel S x R (G.region {w})) a ∧
        nodes (Fin.last m) = Quot.mk (intrinsicArcRel S x R (G.region {w})) b ∧
        ∀ j : Fin m, {nodes j.castSucc, nodes j.succ} ∈ (C.complex {w}).faces := by
    intro w a b
    have hσ : Compatible S (loopSupport S v n z) {w} := by
      intro u hu q hq huq
      exact False.elim (huq ((Finset.mem_singleton.mp hu).trans
        (Finset.mem_singleton.mp hq).symm))
    have hlabels : ∀ μ : Finset Unit,
        μ ∈ (⊤ : AbstractSimplicialComplex Unit).faces →
        μ.image (fun _ => Quot.mk (intrinsicArcRel S x R (G.region {w})) a) ∈
          intrinsicArcFaces S x R (G.region {w}) := by
      intro μ hμ
      have hne : μ.Nonempty := hμ
      rw [Finset.image_const hne]
      rw [← C.faces_exact]
      exact (C.complex {w}).singleton_mem _
    obtain ⟨steps, labels, hzero, hvalid, hstep, hend⟩ :=
      regional_original_finite_label_descent_exists S g hg hS x R hR htarget
        (G.region {w}) (G.compact {w}) (G.connected {w}) (G.contains_boundary {w})
        (G.outside {w}) (G.regular_closed {w}) (Fin (G.frontierCount {w}))
        (G.frontierCurve {w}) (G.frontier_disjoint {w} hσ)
        (G.frontier_boundary_disjoint {w}) (G.frontier_exact {w} hσ)
        Unit (⊤ : AbstractSimplicialComplex Unit)
        (fun _ => Quot.mk (intrinsicArcRel S x R (G.region {w})) a) b hlabels
    apply path_from_movie {w} _ _ steps (fun t => labels t ())
    · exact congrFun hzero ()
    · intro t ht
      have hs := hstep t ht {()} ((⊤ : AbstractSimplicialComplex Unit).singleton_mem ())
      change _ ∈ intrinsicArcFaces S x R (G.region {w}) at hs
      rw [← C.faces_exact] at hs
      apply ((C.complex {w}).isRelLowerSet_faces hs).2 _ (Finset.insert_nonempty _ _)
      intro q hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨(), Finset.mem_singleton_self (), rfl⟩)
      · have hq' := Finset.mem_singleton.mp hq
        subst q
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨(), Finset.mem_singleton_self (), rfl⟩)
    · have he := hend {()} ((⊤ : AbstractSimplicialComplex Unit).singleton_mem ())
      change _ ∈ intrinsicArcFaces S x R (G.region {w}) at he
      rw [← C.faces_exact] at he
      apply ((C.complex {w}).isRelLowerSet_faces he).2 _ (Finset.insert_nonempty _ _)
      intro q hq
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        exact Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨(), Finset.mem_singleton_self (), rfl⟩)
      · have hq' := Finset.mem_singleton.mp hq
        subst q
        exact Finset.mem_insert_self _ _
  choose aIn hIn using incoming
  choose aOut hOut using outgoing
  have paths : ∀ k : Fin n, ∃ (m : ℕ)
      (nodes : Fin (m + 1) → IntrinsicArcVertex S x R
        (G.region {⟨vertex k.castSucc, vsupport k.castSucc⟩})),
      nodes 0 = Quot.mk (intrinsicArcRel S x R _) (aIn k) ∧
      nodes (Fin.last m) = Quot.mk (intrinsicArcRel S x R _) (aOut k) ∧
      ∀ j : Fin m, {nodes j.castSucc, nodes j.succ} ∈
        (C.complex {⟨vertex k.castSucc, vsupport k.castSucc⟩}).faces := by
    intro k
    exact regional_path _ (aIn k) (aOut k)
  choose blockLength intrinsicBlock hbStart hbEnd hbFaces using paths
  let block := fun k j => C.classMap _ (vertex_compatible k) (intrinsicBlock k j)
  have block_start : ∀ k, block k 0 = junction k.castSucc := by
    intro k
    change C.classMap _ _ (intrinsicBlock k 0) = _
    rw [hbStart]
    exact hIn k
  have block_end : ∀ k, block k (Fin.last (blockLength k)) = junction k.succ := by
    intro k
    change C.classMap _ _ (intrinsicBlock k _) = _
    rw [hbEnd]
    exact hOut k
  have block_vertex_system : ∀ k j, RegionArcSystem S x R
      (G.region {⟨vertex k.castSucc, vsupport k.castSucc⟩}) {block k j} := by
    intro k j
    simpa only [Finset.image_singleton] using (C.faceMap _ (vertex_compatible k) _
      ((C.complex _).singleton_mem (intrinsicBlock k j))).2
  have block_edge_system : ∀ k (j : Fin (blockLength k)), RegionArcSystem S x R
      (G.region {⟨vertex k.castSucc, vsupport k.castSucc⟩})
      {block k j.castSucc, block k j.succ} := by
    intro k j
    simpa only [Finset.image_insert, Finset.image_singleton] using
      (C.faceMap _ (vertex_compatible k) _ (hbFaces k j)).2
  have block_vertex_carrier : ∀ k j,
      FaceCurveCarrier S x R {block k j} (vertex k.castSucc) := by
    intro k j
    exact carrier _ ⟨_, vsupport k.castSucc⟩ (by simp) _ (block_vertex_system k j)
  have block_edge_carrier : ∀ k (j : Fin (blockLength k)),
      FaceCurveCarrier S x R {block k j.castSucc, block k j.succ} (vertex k.castSucc) := by
    intro k j
    exact carrier _ ⟨_, vsupport k.castSucc⟩ (by simp) _ (block_edge_system k j)
  have block_vertex_face : ∀ k j, {block k j} ∈ (arcComplex S x R).faces := by
    intro k j
    exact (arcComplex S x R).singleton_mem _
  have block_edge_face : ∀ k (j : Fin (blockLength k)),
      {block k j.castSucc, block k j.succ} ∈ (arcComplex S x R).faces := by
    intro k j
    simpa only [Finset.image_insert, Finset.image_singleton] using
      (C.faceMap _ (vertex_compatible k) _ (hbFaces k j)).1
  have concatenate : ∀ (A B : ℕ)
      (f : Fin (A + 1) → ArcVertex S x R) (b : Fin (B + 1) → ArcVertex S x R),
      f (Fin.last A) = b 0 →
      (∀ j : Fin A, {f j.castSucc, f j.succ} ∈ (arcComplex S x R).faces) →
      (∀ j : Fin B, {b j.castSucc, b j.succ} ∈ (arcComplex S x R).faces) →
      ∃ nodes : Fin (A + B + 1) → ArcVertex S x R,
        (∀ j : Fin (A + 1), ∀ h, nodes ⟨j.val, h⟩ = f j) ∧
        (∀ j : Fin (B + 1), ∀ h, nodes ⟨A + j.val, h⟩ = b j) ∧
        ∀ j : Fin (A + B), {nodes j.castSucc, nodes j.succ} ∈ (arcComplex S x R).faces := by
    intro A B f b hjoin hf hb
    let nodes : Fin (A + B + 1) → ArcVertex S x R := fun i =>
      if h : i.val ≤ A then f ⟨i.val, by omega⟩ else b ⟨i.val - A, by omega⟩
    have first : ∀ j : Fin (A + 1), ∀ h, nodes ⟨j.val, h⟩ = f j := by
      intro j h
      simp [nodes, show j.val ≤ A by omega]
    have second : ∀ j : Fin (B + 1), ∀ h, nodes ⟨A + j.val, h⟩ = b j := by
      intro j h
      by_cases hj : j.val = 0
      · have hzero : j = 0 := Fin.ext hj
        subst j
        simp only [nodes, Fin.val_zero, Nat.add_zero, le_refl, dite_true]
        convert hjoin using 1
        congr 1
      · simp [nodes, show ¬ A + j.val ≤ A by omega]
    refine ⟨nodes, first, second, ?_⟩
    intro j
    by_cases hj : j.val < A
    · let i : Fin A := ⟨j.val, hj⟩
      have hl : nodes j.castSucc = f i.castSucc := first i.castSucc _
      have hr : nodes j.succ = f i.succ := first i.succ _
      rw [hl, hr]
      exact hf i
    · let i : Fin B := ⟨j.val - A, by omega⟩
      have hl : nodes j.castSucc = b i.castSucc := by
        have he : A + i.castSucc.val = j.castSucc.val := by dsimp [i]; omega
        have hbound : A + i.castSucc.val < A + B + 1 := by omega
        simpa only [he] using second i.castSucc hbound
      have hr : nodes j.succ = b i.succ := by
        have he : A + i.succ.val = j.succ.val := by dsimp [i]; omega
        have hbound : A + i.succ.val < A + B + 1 := by omega
        simpa only [he] using second i.succ hbound
      rw [hl, hr]
      exact hb i
  let lengthNat : ℕ → ℕ := fun k => if h : k < n then blockLength ⟨k, h⟩ else 0
  let offsetNat : ℕ → ℕ := fun k => (Finset.range k).sum lengthNat
  have offsetNat_zero : offsetNat 0 = 0 := by simp [offsetNat]
  have offsetNat_step : ∀ k, offsetNat (k + 1) = offsetNat k + lengthNat k := by
    intro k
    exact Finset.sum_range_succ _ _
  have offsetNat_mono : Monotone offsetNat := monotone_nat_of_le_succ (by
    intro k
    rw [offsetNat_step]
    omega)
  have flatten : ∀ m (hm : m ≤ n), ∃ nodes : Fin (offsetNat m + 1) → ArcVertex S x R,
      nodes 0 = junction 0 ∧
      nodes (Fin.last (offsetNat m)) = junction ⟨m, by omega⟩ ∧
      (∀ j : Fin (offsetNat m), {nodes j.castSucc, nodes j.succ} ∈ (arcComplex S x R).faces) ∧
      ∀ (k : Fin n), k.val < m → ∀ j : Fin (blockLength k + 1),
        ∃ i : Fin (offsetNat m + 1), i.val = offsetNat k.val + j.val ∧ nodes i = block k j := by
    intro m
    induction m with
    | zero =>
      intro hm
      refine ⟨fun _ => junction 0, rfl, ?_, ?_, ?_⟩
      · change junction 0 = junction ⟨0, _⟩
        exact congrArg junction (Fin.ext rfl)
      · intro j
        have := j.isLt
        have hz := offsetNat_zero
        omega
      · intro k hk
        omega
    | succ m ih =>
      intro hm
      obtain ⟨f, hfzero, hflast, hffaces, hfocc⟩ := ih (by omega)
      let k : Fin n := ⟨m, by omega⟩
      have step : offsetNat (m + 1) = offsetNat m + blockLength k := by
        rw [offsetNat_step]
        simp [lengthNat, k, show m < n by omega]
      have hjoin : f (Fin.last (offsetNat m)) = block k 0 := by
        rw [hflast, block_start]
        rfl
      obtain ⟨nodes, hfirst, hsecond, hfaces⟩ :=
        concatenate (offsetNat m) (blockLength k) f (block k) hjoin hffaces (block_edge_face k)
      let finalNodes : Fin (offsetNat (m + 1) + 1) → ArcVertex S x R :=
        fun i => nodes (Fin.cast (congrArg (fun q => q + 1) step) i)
      refine ⟨finalNodes, ?_, ?_, ?_, ?_⟩
      · change nodes ⟨0, _⟩ = _
        exact (hfirst 0 _).trans hfzero
      · change nodes ⟨offsetNat (m + 1), _⟩ = _
        have hh := hsecond (Fin.last (blockLength k)) (by omega)
        have hk : k.succ = (⟨m + 1, by omega⟩ : Fin (n + 1)) := Fin.ext rfl
        simpa only [Fin.val_last, step, hk] using hh.trans (block_end k)
      · intro j
        let i : Fin (offsetNat m + blockLength k) := ⟨j.val, by rw [← step]; exact j.isLt⟩
        exact hfaces i
      · intro l hl j
        by_cases hlt : l.val < m
        · obtain ⟨i, hi, hlabel⟩ := hfocc l hlt j
          refine ⟨⟨i.val, by rw [step]; omega⟩, hi, ?_⟩
          exact (hfirst i _).trans hlabel
        · have he : l = k := Fin.ext (by dsimp [k]; omega)
          subst l
          refine ⟨⟨offsetNat m + j.val, by rw [step]; omega⟩, rfl, ?_⟩
          exact hsecond j _
  obtain ⟨flat, flat_zero, flat_last, flat_faces, flat_occ⟩ := flatten n le_rfl
  let total := offsetNat n
  have flat_closed : flat (Fin.last total) = flat 0 := by
    exact flat_last.trans (junction_closed.trans flat_zero.symm)
  let arcVertex : Fin (total + 1) → Fin (total + 1) :=
    fun i => if i = Fin.last total then 0 else i
  have arcVertex_closed : arcVertex (Fin.last total) = arcVertex 0 := by
    simp [arcVertex]
  have arcVertex_label : ∀ i, flat (arcVertex i) = flat i := by
    intro i
    by_cases hi : i = Fin.last total
    · subst i
      simpa only [arcVertex, ite_eq_left rfl] using flat_closed.symm
    · simp [arcVertex, hi]
  let L := arcComplex S x R
  let arcDomain : AbstractSimplicialComplex (Fin (total + 1)) := {
    faces := {τ | τ.Nonempty ∧ τ.image flat ∈ L.faces}
    isRelLowerSet_faces := by
      intro τ hτ
      refine ⟨hτ.1, ?_⟩
      intro μ hμτ hne
      exact ⟨hne, (L.isRelLowerSet_faces hτ.2).2
        (Finset.image_subset_image hμτ) (hne.image flat)⟩
    singleton_mem := by
      intro i
      exact ⟨Finset.singleton_nonempty _, by simpa only [Finset.image_singleton] using L.singleton_mem (flat i)⟩ }
  have arcDomain_faces : ∀ τ, τ ∈ arcDomain.faces → τ.image flat ∈ L.faces := by
    intro τ hτ
    exact hτ.2
  have arc_edge_face : ∀ j : Fin total,
      {arcVertex j.castSucc, arcVertex j.succ} ∈ arcDomain.faces := by
    intro j
    refine ⟨Finset.insert_nonempty _ _, ?_⟩
    simp only [Finset.image_insert, Finset.image_singleton, arcVertex_label]
    exact flat_faces j
  let arcPoint : Fin (total + 1) → RealizationPoint L :=
    fun i => realizationVertex L (flat i) (L.singleton_mem _)
  have arcPoint_eq : ∀ i, arcPoint i = realizationVertex L (flat (arcVertex i)) (L.singleton_mem _) := by
    intro i
    rw [arcVertex_label]
  have arcPoint_closed : arcPoint (Fin.last total) = arcPoint 0 := by
    change realizationVertex L (flat (Fin.last total)) _ = realizationVertex L (flat 0) _
    rw [flat_closed]
  have arc_in_vertex : ∀ (σ : Finset (ArcVertex S x R)) (hσ : σ ∈ L.faces)
      (a : ArcVertex S x R) (ha : a ∈ σ),
      realizationVertex L a (L.singleton_mem a) =
        faceInclusion L σ hσ (finiteSimplexVertex σ a ha) := by
    intro σ hσ a ha
    apply RealizationPoint.ext
    funext w
    rw [finiteSimplexVertex_faceInclusion_weight, realizationVertex_weight]
  let arcEdge : (j : Fin total) → Path (arcPoint j.castSucc) (arcPoint j.succ) := fun j =>
    ((finiteSegmentPath {flat j.castSucc, flat j.succ}
      (finiteSimplexVertex _ (flat j.castSucc) (by simp))
      (finiteSimplexVertex _ (flat j.succ) (by simp))).map
        (continuous_faceInclusion_local L _ (flat_faces j))).cast
      (arc_in_vertex _ (flat_faces j) _ (by simp))
      (arc_in_vertex _ (flat_faces j) _ (by simp))
  have arc_edge_weight : ∀ (j : Fin total) (t : EdgeTime) (w : ArcVertex S x R),
      (arcEdge j t).weight w =
        (1 - (t : ℝ)) * (if flat (arcVertex j.castSucc) = w then 1 else 0) +
        (t : ℝ) * (if flat (arcVertex j.succ) = w then 1 else 0) := by
    intro j t w
    rw [arcVertex_label, arcVertex_label]
    change (faceInclusion L {flat j.castSucc, flat j.succ} (flat_faces j)
      (finiteSimplexSegment _ (finiteSimplexVertex _ (flat j.castSucc) _)
        (finiteSimplexVertex _ (flat j.succ) _) t)).weight w = _
    by_cases hw : w ∈ ({flat j.castSucc, flat j.succ} : Finset (ArcVertex S x R))
    · simp [faceInclusion, finiteSimplexSegment, finiteSimplexVertex, eq_comm]
      intro hwa hwb
      simp [hwa, hwb]
    · have hwa : w ≠ flat j.castSucc := by
        intro he
        exact hw (he.symm ▸ Finset.mem_insert_self _ _)
      have hwb : w ≠ flat j.succ := by
        intro he
        exact hw (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      simp [faceInclusion, finiteSimplexSegment, finiteSimplexVertex, hwa, hwb, eq_comm]
  let arcWord : CyclicAffineWord arcDomain L flat := {
    edgeCount := total
    vertex := arcVertex
    vertex_closed := arcVertex_closed
    edge_face := arc_edge_face
    point := arcPoint
    point_eq := arcPoint_eq
    edge := arcEdge
    edge_weight := arc_edge_weight
    point_closed := arcPoint_closed
    loop := (Path.concat arcPoint arcEdge).cast rfl arcPoint_closed.symm
    loop_eq := rfl }
  let offset : Fin (n + 1) → ℕ := fun k => offsetNat k.val
  have offset_zero : offset 0 = 0 := offsetNat_zero
  have offset_step : ∀ k : Fin n, offset k.succ = offset k.castSucc + blockLength k := by
    intro k
    change offsetNat (k.val + 1) = offsetNat k.val + blockLength k
    rw [offsetNat_step]
    simp [lengthNat, k.isLt]
  have occurrences : ∀ k (j : Fin (blockLength k + 1)),
      ∃ i : Fin (arcWord.edgeCount + 1), i.val = offset k.castSucc + j.val ∧
        flat (arcWord.vertex i) = block k j := by
    intro k j
    obtain ⟨i, hindex, hlabel⟩ := flat_occ k k.isLt j
    refine ⟨i, hindex, ?_⟩
    exact (arcVertex_label i).trans hlabel
  refine ⟨{
    curveWord := curveWord
    curve_count := rfl
    curve_nonempty := hnpos
    curve_point_exact := ?_
    curve_edge_exact := ?_
    curve_loop_exact := curve_loop_exact
    curve_base := vbase
    curve_support := vsupport
    curve_edge_compatible := edge_compatible
    curve_vertex_compatible := vertex_compatible
    edgeArc := edgeArc
    junction := junction
    junction_closed := junction_closed
    junction_edgeArc := junction_succ
    junction_left := ?_
    junction_right := ?_
    blockLength := blockLength
    intrinsicBlock := intrinsicBlock
    intrinsicBlock_faces := hbFaces
    block := block
    block_inclusion := fun _ _ => rfl
    block_start := block_start
    block_end := block_end
    block_vertex_carrier := block_vertex_carrier
    block_edge_carrier := block_edge_carrier
    block_vertex_system := block_vertex_system
    block_edge_system := block_edge_system
    arcDomainCount := total + 1
    arcDomain := arcDomain
    arcLabel := flat
    arcLabel_faces := arcDomain_faces
    arcWord := arcWord
    offset := offset
    offset_zero := offset_zero
    offset_step := offset_step
    offset_last := rfl
    block_occurrences := occurrences }⟩
  · intro k
    rfl
  · intro k
    rfl
  · intro k
    rw [junction_succ]
    exact edge_left k
  · intro k
    rw [junction_succ]
    exact edge_right k

end
end CurveComplex.C0BoundaryCorrespondence
