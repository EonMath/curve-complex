import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace CurveComplex.LocalSurgery
open Set Topology Schoenflies

/-- Subdivide an actual finite family of embedded compatible planar arcs twice,
then construct its finite proper labeled drawing. The family and its existing
finite vertices are inputs; this does not construct a contact family from a movie,
select a cancellation cap, or assert any boundary degree. -/
theorem actual_finite_compatible_planar_arc_family_drawing
    {A : Type*} [Finite A]
    (V : Set Plane) (hV : V.Finite) (p : A → C(Interval,Plane))
    (hp : ∀ e, IsEmbedding (p e))
    (hstart : ∀ e, p e 0∈V) (hend : ∀ e, p e 1∈V)
    (hclear : ∀ e t, t∈Set.Ioo (0 : Interval) 1 → p e t∉V)
    (hcompatible : ∀ e f t u, t∈Set.Ioo (0 : Interval) 1 →
      u∈Set.Ioo (0 : Interval) 1 → p e t=p f u → e=f) :
    ∃ (G : Graph Plane (A × Fin 3)) (draw : (A × Fin 3) → ℝ → Plane),
      G.vertexSet.Finite ∧ G.edgeSet=Set.univ ∧ Graph.IsDrawing G draw ∧
      (∀ e, Set.range (p e)=⋃ j : Fin 3,Graph.edgeArc draw (e,j)) ∧
      V⊆G.vertexSet ∧
      G.vertexSet⊆V ∪ ⋃ e,Set.range (p e) := by
  classical
  let actualContactVertices := V
  have hActualContactVerticesFinite : actualContactVertices.Finite := hV
  let actualNegativeFaceIntervals := A
  let actualGlobalContactArcs := p
  have hActualContactArcStartInVertices : ∀ e,actualGlobalContactArcs e 0∈actualContactVertices := hstart
  have hActualContactArcEndInVertices : ∀ e,actualGlobalContactArcs e 1∈actualContactVertices := hend
  have hActualGlobalContactArcEmbedding : ∀ e,IsEmbedding (actualGlobalContactArcs e) := hp
  have hActualGlobalContactArcInteriorAvoidVertices : ∀ e t,t∈Set.Ioo (0 : Interval) 1 →
      actualGlobalContactArcs e t∉actualContactVertices := hclear
  have hActualGlobalContactArcInteriorsDisjoint : ∀ e f t u,t∈Set.Ioo (0 : Interval) 1 →
      u∈Set.Ioo (0 : Interval) 1 → actualGlobalContactArcs e t=actualGlobalContactArcs f u → e=f := hcompatible
  have hActualGlobalContactArcInteriorAvoidEndpoints (e f : actualNegativeFaceIntervals) (t v : Interval)
      (ht : t∈Set.Ioo (0 : Interval) 1) (hv : v=0 ∨ v=1) :
      actualGlobalContactArcs e t≠actualGlobalContactArcs f v := by
    intro he
    have hmem : actualGlobalContactArcs f v∈actualContactVertices := by
      rcases hv with rfl | rfl
      · exact hActualContactArcStartInVertices f
      · exact hActualContactArcEndInVertices f
    exact hActualGlobalContactArcInteriorAvoidVertices e t ht (he.symm ▸ hmem)
  have hActualContactArcCollisionClassification (e f : actualNegativeFaceIntervals) (t u : Interval)
      (he : actualGlobalContactArcs e t=actualGlobalContactArcs f u) :
      (e=f ∧ t=u) ∨ ((t=0 ∨ t=1) ∧ (u=0 ∨ u=1)) := by
    by_cases ht : t=0 ∨ t=1
    · by_cases hu : u=0 ∨ u=1
      · exact Or.inr ⟨ht,hu⟩
      · have huI : u∈Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne u.property.1 (fun h => hu (Or.inl h.symm)),
            lt_of_le_of_ne u.property.2 (fun h => hu (Or.inr h))⟩
        exact False.elim (hActualGlobalContactArcInteriorAvoidEndpoints f e u t huI ht he.symm)
    · have htI : t∈Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (fun h => ht (Or.inl h.symm)),
          lt_of_le_of_ne t.property.2 (fun h => ht (Or.inr h))⟩
      by_cases hu : u=0 ∨ u=1
      · exact False.elim (hActualGlobalContactArcInteriorAvoidEndpoints e f t u htI hu he)
      · have huI : u∈Set.Ioo (0 : Interval) 1 :=
          ⟨lt_of_le_of_ne u.property.1 (fun h => hu (Or.inl h.symm)),
            lt_of_le_of_ne u.property.2 (fun h => hu (Or.inr h))⟩
        have hef := hActualGlobalContactArcInteriorsDisjoint e f t u htI huI he
        subst f
        exact Or.inl ⟨rfl,(hActualGlobalContactArcEmbedding e).injective he⟩
  let actualIntervalSegment (x y : Interval) : C(Interval,Interval) := {
    toFun := fun t => ⟨(1-t.val)*x.val+t.val*y.val,by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property.1)
          (mul_nonneg t.property.1 y.property.1)
      · nlinarith only [t.property.1,t.property.2,x.property.2,y.property.2]⟩
    continuous_toFun := by fun_prop }
  have actualIntervalSegmentInjective (x y : Interval) (hxy : x<y) :
      Function.Injective (actualIntervalSegment x y) := by
    intro t u he
    have hh := congrArg Subtype.val he
    change (1-t.val)*x.val+t.val*y.val=(1-u.val)*x.val+u.val*y.val at hh
    have hxyR : x.val<y.val := hxy
    apply Subtype.ext
    nlinarith only [hh,hxyR]
  have actualIntervalSegmentBounds (x y : Interval) (hxy : x<y) (t : Interval) :
      x≤actualIntervalSegment x y t ∧ actualIntervalSegment x y t≤y := by
    have hxyR : x.val<y.val := hxy
    change x.val≤(1-t.val)*x.val+t.val*y.val ∧ (1-t.val)*x.val+t.val*y.val≤y.val
    constructor <;> nlinarith only [hxyR,t.property.1,t.property.2]
  have actualIntervalSegmentSurjectiveOnBounds (x y t : Interval)
      (ht : t∈Set.Icc x y) : ∃ w : Interval,actualIntervalSegment x y w=t := by
    have h0 : actualIntervalSegment x y 0=x := by
      apply Subtype.ext
      change (1-(0 : ℝ))*x.val+(0 : ℝ)*y.val=x.val
      ring
    have h1 : actualIntervalSegment x y 1=y := by
      apply Subtype.ext
      change (1-(1 : ℝ))*x.val+(1 : ℝ)*y.val=y.val
      ring
    have ht' : t∈Set.Icc (actualIntervalSegment x y 0) (actualIntervalSegment x y 1) := by
      rwa [h0,h1]
    obtain ⟨w,hw,he⟩ := intermediate_value_Icc (show (0 : Interval)≤1 by norm_num)
      (actualIntervalSegment x y).continuous.continuousOn ht'
    exact ⟨w,he⟩
  let actualParameterSquarePlane : C(Plane,Plane) := ContinuousMap.id Plane
  have hActualParameterSquarePlaneInjective : Function.Injective actualParameterSquarePlane := fun _ _ h => h
  have hActualParameterSquarePlaneEmbedding : IsEmbedding actualParameterSquarePlane := IsEmbedding.id
  let actualContactPlaneVertices := actualParameterSquarePlane '' actualContactVertices
  letI : Fintype actualNegativeFaceIntervals := Fintype.ofFinite _
  letI : Fintype actualContactVertices := hActualContactVerticesFinite.fintype
  let zeroVertex := Sum actualContactVertices (actualNegativeFaceIntervals × Fin 2)
  letI : Fintype zeroVertex := Fintype.ofFinite zeroVertex
  let zeroLeftVertex (e : actualNegativeFaceIntervals) : zeroVertex :=
    Sum.inl ⟨actualGlobalContactArcs e 0,hActualContactArcStartInVertices e⟩
  let zeroRightVertex (e : actualNegativeFaceIntervals) : zeroVertex :=
    Sum.inl ⟨actualGlobalContactArcs e 1,hActualContactArcEndInVertices e⟩
  let zeroDirectedIncidence : zeroVertex → zeroVertex → Prop := fun v w => ∃ e : actualNegativeFaceIntervals,
    (v = zeroLeftVertex e ∧ w = Sum.inr (e,0)) ∨
    (v = Sum.inr (e,0) ∧ w = Sum.inr (e,1)) ∨
    (v = Sum.inr (e,1) ∧ w = zeroRightVertex e)
  let actualZeroGraph : SimpleGraph zeroVertex := SimpleGraph.fromRel zeroDirectedIncidence
  have zeroGraphLeftAdj (e : actualNegativeFaceIntervals) :
      actualZeroGraph.Adj (zeroLeftVertex e) (Sum.inr (e,0)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inl ⟨rfl,rfl⟩⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  have zeroGraphMiddleAdj (e : actualNegativeFaceIntervals) :
      actualZeroGraph.Adj (Sum.inr (e,0)) (Sum.inr (e,1)) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩⟩
    intro he
    have hh := congrArg Prod.snd (Sum.inr.inj he)
    norm_num at hh
  have zeroGraphRightAdj (e : actualNegativeFaceIntervals) :
      actualZeroGraph.Adj (Sum.inr (e,1)) (zeroRightVertex e) := by
    refine ⟨?_,Or.inl ⟨e,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩⟩
    intro he
    simp [zeroLeftVertex,zeroRightVertex] at he
  have zeroSubdivisionNeighborsLeft (e : actualNegativeFaceIntervals) :
      actualZeroGraph.neighborFinset (Sum.inr (e,0)) =
        {zeroLeftVertex e,Sum.inr (e,1)} := by
    ext v
    rcases v with p | ⟨e',j⟩
    · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
        zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
    · fin_cases j <;>
        simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  have zeroSubdivisionNeighborsRight (e : actualNegativeFaceIntervals) :
      actualZeroGraph.neighborFinset (Sum.inr (e,1)) =
        {Sum.inr (e,0),zeroRightVertex e} := by
    ext v
    rcases v with p | ⟨e',j⟩
    · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
        zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
    · fin_cases j <;>
        simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,zeroLeftVertex,zeroRightVertex,zeroVertex,
        Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] <;> exact eq_comm
  let leftIncidentEdges (p : actualContactVertices) : Finset actualNegativeFaceIntervals :=
    Finset.univ.filter (fun e => Sum.inl p = zeroLeftVertex e)
  let rightIncidentEdges (p : actualContactVertices) : Finset actualNegativeFaceIntervals :=
    Finset.univ.filter (fun e => Sum.inl p = zeroRightVertex e)
  have zeroEndpointNeighbors (p : actualContactVertices) :
      actualZeroGraph.neighborFinset (Sum.inl p) =
        (leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) ∪
        (rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
    ext v
    rcases v with q | ⟨e,j⟩
    · simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
        zeroDirectedIncidence,leftIncidentEdges,rightIncidentEdges,
        zeroLeftVertex,zeroRightVertex,zeroVertex]
    · fin_cases j <;>
        simp [SimpleGraph.mem_neighborFinset,actualZeroGraph,SimpleGraph.fromRel_adj,
          zeroDirectedIncidence,leftIncidentEdges,rightIncidentEdges,
          zeroLeftVertex,zeroRightVertex,zeroVertex,
          Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq]
  have zeroEndpointDegreeExact (p : actualContactVertices) :
      actualZeroGraph.degree (Sum.inl p) =
        (leftIncidentEdges p).card + (rightIncidentEdges p).card := by
    change (actualZeroGraph.neighborFinset (Sum.inl p)).card = _
    rw [zeroEndpointNeighbors]
    have hd : Disjoint
        ((leftIncidentEdges p).image (fun e => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)))
        ((rightIncidentEdges p).image (fun e => (Sum.inr (e,(1 : Fin 2)) : zeroVertex))) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨f,hf,h⟩ := Finset.mem_image.mp hw
      have hh := congrArg (fun v : actualNegativeFaceIntervals × Fin 2 => v.2) (Sum.inr.inj h)
      norm_num at hh
    rw [Finset.card_union_of_disjoint hd]
    have hi0 : Function.Injective (fun e : actualNegativeFaceIntervals => (Sum.inr (e,(0 : Fin 2)) : zeroVertex)) := by
      intro e f h
      exact congrArg Prod.fst (Sum.inr.inj h)
    have hi1 : Function.Injective (fun e : actualNegativeFaceIntervals => (Sum.inr (e,(1 : Fin 2)) : zeroVertex)) := by
      intro e f h
      exact congrArg Prod.fst (Sum.inr.inj h)
    rw [Finset.card_image_of_injective _ hi0,Finset.card_image_of_injective _ hi1]
  have zeroSubdivisionDegrees (e : actualNegativeFaceIntervals) :
      actualZeroGraph.degree (Sum.inr (e,0)) = 2 ∧
      actualZeroGraph.degree (Sum.inr (e,1)) = 2 := by
    change (actualZeroGraph.neighborFinset (Sum.inr (e,0))).card = 2 ∧
      (actualZeroGraph.neighborFinset (Sum.inr (e,1))).card = 2
    rw [zeroSubdivisionNeighborsLeft,zeroSubdivisionNeighborsRight]
    simp [zeroLeftVertex,zeroRightVertex]
  let privateParameter : Fin 2 → Interval := fun j =>
    if j=0 then ⟨1/3,by norm_num⟩ else ⟨2/3,by norm_num⟩
  have privateParameterInterior (j : Fin 2) :
      privateParameter j∈Set.Ioo (0 : Interval) 1 := by
    change 0<(privateParameter j).val ∧ (privateParameter j).val<1
    fin_cases j <;> norm_num [privateParameter]
  have privateParameterInjective : Function.Injective privateParameter := by
    intro j k he
    have hh := congrArg Subtype.val he
    fin_cases j <;> fin_cases k <;> first | rfl | (norm_num [privateParameter] at hh)
  let zeroVertexPosition : zeroVertex → Plane := fun v =>
    match v with
    | Sum.inl p => p.val
    | Sum.inr (e,j) => actualGlobalContactArcs e (privateParameter j)
  have zeroVertexPositionInjective : Function.Injective zeroVertexPosition := by
    intro v w he
    rcases v with p | ⟨e,j⟩ <;> rcases w with q | ⟨f,k⟩
    · exact congrArg Sum.inl (Subtype.ext he)
    · change p.val=actualGlobalContactArcs f (privateParameter k) at he
      have hh : actualGlobalContactArcs f (privateParameter k)∈actualContactVertices :=
        he ▸ p.property
      exact False.elim (hActualGlobalContactArcInteriorAvoidVertices f _ (privateParameterInterior k) hh)
    · change actualGlobalContactArcs e (privateParameter j)=q.val at he
      have hh : actualGlobalContactArcs e (privateParameter j)∈actualContactVertices :=
        he.symm ▸ q.property
      exact False.elim (hActualGlobalContactArcInteriorAvoidVertices e _ (privateParameterInterior j) hh)
    · have hef : e=f := hActualGlobalContactArcInteriorsDisjoint e f _ _
        (privateParameterInterior j) (privateParameterInterior k) he
      subst f
      have hjk := privateParameterInjective ((hActualGlobalContactArcEmbedding e).injective he)
      subst k
      rfl
  let actualPlanarVertexPosition (v : zeroVertex) : Schoenflies.Plane :=
    actualParameterSquarePlane (zeroVertexPosition v)
  have actualPlanarVertexPositionInjective : Function.Injective actualPlanarVertexPosition :=
    hActualParameterSquarePlaneInjective.comp zeroVertexPositionInjective
  have actualPrivateParametersOrdered :
      (0 : Interval)<privateParameter 0 ∧ privateParameter 0<privateParameter 1 ∧
        privateParameter 1<(1 : Interval) := by
    change 0<(privateParameter 0).val ∧ (privateParameter 0).val<(privateParameter 1).val ∧
      (privateParameter 1).val<1
    norm_num [privateParameter]
  let actualSegmentStartParameter (q : actualNegativeFaceIntervals × Fin 3) : Interval :=
    if q.2=0 then 0 else if q.2=1 then privateParameter 0 else privateParameter 1
  let actualSegmentEndParameter (q : actualNegativeFaceIntervals × Fin 3) : Interval :=
    if q.2=0 then privateParameter 0 else if q.2=1 then privateParameter 1 else 1
  let actualSegmentStartVertex (q : actualNegativeFaceIntervals × Fin 3) : zeroVertex :=
    if q.2=0 then zeroLeftVertex q.1 else if q.2=1 then Sum.inr (q.1,0) else Sum.inr (q.1,1)
  let actualSegmentEndVertex (q : actualNegativeFaceIntervals × Fin 3) : zeroVertex :=
    if q.2=0 then Sum.inr (q.1,0) else if q.2=1 then Sum.inr (q.1,1) else zeroRightVertex q.1
  have actualSegmentParameterOrder (q : actualNegativeFaceIntervals × Fin 3) :
      actualSegmentStartParameter q<actualSegmentEndParameter q := by
    rcases q with ⟨e,j⟩
    fin_cases j
    · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.1
    · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.1
    · simpa [actualSegmentStartParameter,actualSegmentEndParameter] using actualPrivateParametersOrdered.2.2
  let actualSegmentSquarePath (q : actualNegativeFaceIntervals × Fin 3) :
      Path (actualGlobalContactArcs q.1 (actualSegmentStartParameter q))
        (actualGlobalContactArcs q.1 (actualSegmentEndParameter q)) := {
    toFun := fun t => actualGlobalContactArcs q.1
      (actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q) t)
    continuous_toFun := (actualGlobalContactArcs q.1).continuous.comp
      (actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q)).continuous
    source' := by
      apply congrArg (actualGlobalContactArcs q.1)
      apply Subtype.ext
      change (1-(0 : ℝ))*(actualSegmentStartParameter q).val+0*(actualSegmentEndParameter q).val=
        (actualSegmentStartParameter q).val
      ring
    target' := by
      apply congrArg (actualGlobalContactArcs q.1)
      apply Subtype.ext
      change (1-(1 : ℝ))*(actualSegmentStartParameter q).val+1*(actualSegmentEndParameter q).val=
        (actualSegmentEndParameter q).val
      ring }
  have actualSegmentSquarePathEmbedding (q : actualNegativeFaceIntervals × Fin 3) :
      IsEmbedding (actualSegmentSquarePath q) :=
    (hActualGlobalContactArcEmbedding q.1).comp
      (((actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q)).continuous.isClosedEmbedding (actualIntervalSegmentInjective _ _ (actualSegmentParameterOrder q))).isEmbedding)
  have actualSegmentSquarePathRange (q : actualNegativeFaceIntervals × Fin 3) :
      Set.range (actualSegmentSquarePath q)⊆actualGlobalContactArcs q.1 ''
        Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q) := by
    rintro z ⟨t,rfl⟩
    refine ⟨actualIntervalSegment (actualSegmentStartParameter q) (actualSegmentEndParameter q) t,?_,rfl⟩
    exact actualIntervalSegmentBounds _ _ (actualSegmentParameterOrder q) t
  have actualSegmentStartPosition (q : actualNegativeFaceIntervals × Fin 3) :
      zeroVertexPosition (actualSegmentStartVertex q)=
        actualGlobalContactArcs q.1 (actualSegmentStartParameter q) := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> simp [actualSegmentStartVertex,actualSegmentStartParameter,
      zeroVertexPosition,zeroLeftVertex] <;> rfl
  have actualSegmentEndPosition (q : actualNegativeFaceIntervals × Fin 3) :
      zeroVertexPosition (actualSegmentEndVertex q)=
        actualGlobalContactArcs q.1 (actualSegmentEndParameter q) := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> simp [actualSegmentEndVertex,actualSegmentEndParameter,
      zeroVertexPosition,zeroRightVertex] <;> rfl
  let actualSegmentPlanarPath (q : actualNegativeFaceIntervals × Fin 3) :
      Path (actualParameterSquarePlane (actualGlobalContactArcs q.1 (actualSegmentStartParameter q)))
        (actualParameterSquarePlane (actualGlobalContactArcs q.1 (actualSegmentEndParameter q))) :=
    (actualSegmentSquarePath q).map actualParameterSquarePlane.continuous
  have actualSegmentPlanarPathEmbedding (q : actualNegativeFaceIntervals × Fin 3) :
      IsEmbedding (actualSegmentPlanarPath q) :=
    hActualParameterSquarePlaneEmbedding.comp (actualSegmentSquarePathEmbedding q)
  have actualSegmentPlanarSource (q : actualNegativeFaceIntervals × Fin 3) :
      actualSegmentPlanarPath q 0=actualPlanarVertexPosition (actualSegmentStartVertex q) := by
    rw [Path.source]
    exact congrArg actualParameterSquarePlane (actualSegmentStartPosition q).symm
  have actualSegmentPlanarTarget (q : actualNegativeFaceIntervals × Fin 3) :
      actualSegmentPlanarPath q 1=actualPlanarVertexPosition (actualSegmentEndVertex q) := by
    rw [Path.target]
    exact congrArg actualParameterSquarePlane (actualSegmentEndPosition q).symm
  let actualPlanarGraph : Graph Schoenflies.Plane (actualNegativeFaceIntervals × Fin 3) := {
    vertexSet := Set.range actualPlanarVertexPosition
    edgeSet := Set.univ
    IsLink := fun q x y =>
      (x = actualSegmentPlanarPath q 0 ∧ y = actualSegmentPlanarPath q 1) ∨
      (x = actualSegmentPlanarPath q 1 ∧ y = actualSegmentPlanarPath q 0)
    isLink_symm := by
      intro q hq
      constructor
      intro x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact Or.inr ⟨hy,hx⟩
      · exact Or.inl ⟨hy,hx⟩
    eq_or_eq_of_isLink_of_isLink := by
      intro q x y z w hx hz
      rcases hx with ⟨hx,hy⟩ | ⟨hx,hy⟩ <;>
        rcases hz with ⟨hz,hw⟩ | ⟨hz,hw⟩
      · exact Or.inl (hx.trans hz.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inr (hx.trans hw.symm)
      · exact Or.inl (hx.trans hz.symm)
    edge_mem_iff_exists_isLink := by
      intro q
      constructor
      · intro hq
        exact ⟨actualSegmentPlanarPath q 0,actualSegmentPlanarPath q 1,Or.inl ⟨rfl,rfl⟩⟩
      · intro hq
        exact Set.mem_univ _
    left_mem_of_isLink := by
      intro q x y h
      rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
      · exact ⟨actualSegmentStartVertex q,(actualSegmentPlanarSource q).symm.trans hx.symm⟩
      · exact ⟨actualSegmentEndVertex q,(actualSegmentPlanarTarget q).symm.trans hx.symm⟩ }
  let actualPlanarDrawing (q : actualNegativeFaceIntervals × Fin 3) : ℝ → Schoenflies.Plane :=
    (actualSegmentPlanarPath q).extend
  have actualPlanarEdgeParameter (q : actualNegativeFaceIntervals × Fin 3) :
      ContinuousOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      Set.InjOn (actualPlanarDrawing q) (Set.Icc (0 : ℝ) 1) ∧
      actualPlanarGraph.IsLink q (actualPlanarDrawing q 0) (actualPlanarDrawing q 1) := by
    refine ⟨(actualSegmentPlanarPath q).continuous_extend.continuousOn,?_,?_⟩
    · intro s hs t ht he
      change (actualSegmentPlanarPath q).extend s = (actualSegmentPlanarPath q).extend t at he
      rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
      exact congrArg Subtype.val ((actualSegmentPlanarPathEmbedding q).injective he)
    · change (actualPlanarDrawing q 0 = actualSegmentPlanarPath q 0 ∧
        actualPlanarDrawing q 1 = actualSegmentPlanarPath q 1) ∨ _
      exact Or.inl ⟨by simp [actualPlanarDrawing],by simp [actualPlanarDrawing]⟩
  have actualZeroVertexOnEdgeBreakpoint (v : zeroVertex) (e : actualNegativeFaceIntervals)
      (t : Interval) (he : zeroVertexPosition v=actualGlobalContactArcs e t) :
      t=0 ∨ t=privateParameter 0 ∨ t=privateParameter 1 ∨ t=1 := by
    rcases v with p | ⟨f,j⟩
    · by_cases ht0 : t=0
      · exact Or.inl ht0
      by_cases ht1 : t=1
      · exact Or.inr (Or.inr (Or.inr ht1))
      have ht : t∈Set.Ioo (0 : Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
      change p.val=actualGlobalContactArcs e t at he
      exact False.elim (hActualGlobalContactArcInteriorAvoidVertices e t ht (he ▸ p.property))
    · change actualGlobalContactArcs f (privateParameter j)=actualGlobalContactArcs e t at he
      rcases hActualContactArcCollisionClassification f e _ t he with ⟨hfe,ht⟩ | ⟨hf,ht⟩
      · fin_cases j
        · exact Or.inr (Or.inl ht.symm)
        · exact Or.inr (Or.inr (Or.inl ht.symm))
      · rcases hf with hf | hf
        · exact False.elim ((ne_of_gt (privateParameterInterior j).1) hf)
        · exact False.elim ((ne_of_lt (privateParameterInterior j).2) hf)
  have actualSegmentStartValue (q : actualNegativeFaceIntervals × Fin 3) :
      (actualSegmentStartParameter q).val=CurveComplex.LocalSurgery.actualThreeSegmentStart q.2 := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> norm_num [actualSegmentStartParameter,privateParameter,
      CurveComplex.LocalSurgery.actualThreeSegmentStart]
  have actualSegmentEndValue (q : actualNegativeFaceIntervals × Fin 3) :
      (actualSegmentEndParameter q).val=CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2 := by
    rcases q with ⟨e,j⟩
    fin_cases j <;> norm_num [actualSegmentEndParameter,privateParameter,
      CurveComplex.LocalSurgery.actualThreeSegmentEnd]
  have actualSegmentBreakpointIsEndpoint (q : actualNegativeFaceIntervals × Fin 3) (u : Interval)
      (hu : u∈Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hb : u=0 ∨ u=privateParameter 0 ∨ u=privateParameter 1 ∨ u=1) :
      u=actualSegmentStartParameter q ∨ u=actualSegmentEndParameter q := by
    have hreal : u.val∈Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart q.2)
        (CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2) := by
      rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
      exact hu
    have hbReal : u.val=0 ∨ u.val=1/3 ∨ u.val=2/3 ∨ u.val=1 := by
      rcases hb with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by norm_num [privateParameter]))
      · exact Or.inr (Or.inr (Or.inl (by norm_num [privateParameter])))
      · exact Or.inr (Or.inr (Or.inr rfl))
    rcases CurveComplex.LocalSurgery.actualThreeSegment_breakpoint_is_endpoint q.2 u.val hreal hbReal with h | h
    · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
    · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
  have actualDistinctSegmentParameterIntersection (q r : actualNegativeFaceIntervals × Fin 3)
      (hj : q.2 ≠ r.2) (u : Interval)
      (hu : u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q))
      (hv : u ∈ Set.Icc (actualSegmentStartParameter r) (actualSegmentEndParameter r)) :
      (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
        (u = actualSegmentStartParameter r ∨ u = actualSegmentEndParameter r) := by
    have huReal : u.val ∈ Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart q.2) (CurveComplex.LocalSurgery.actualThreeSegmentEnd q.2) := by
      rw [←actualSegmentStartValue q,←actualSegmentEndValue q]
      exact hu
    have hvReal : u.val ∈ Set.Icc (CurveComplex.LocalSurgery.actualThreeSegmentStart r.2) (CurveComplex.LocalSurgery.actualThreeSegmentEnd r.2) := by
      rw [←actualSegmentStartValue r,←actualSegmentEndValue r]
      exact hv
    obtain ⟨hq,hr⟩ := CurveComplex.LocalSurgery.actualThreeSegment_distinct_intersection q.2 r.2 hj u.val huReal hvReal
    constructor
    · rcases hq with h | h
      · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue q).symm))
      · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue q).symm))
    · rcases hr with h | h
      · exact Or.inl (Subtype.ext (h.trans (actualSegmentStartValue r).symm))
      · exact Or.inr (Subtype.ext (h.trans (actualSegmentEndValue r).symm))
  have actualPlanarEdgeArcParameter (q : actualNegativeFaceIntervals × Fin 3) (z : Schoenflies.Plane)
      (hz : z ∈ Graph.edgeArc actualPlanarDrawing q) :
      ∃ u ∈ Set.Icc (actualSegmentStartParameter q) (actualSegmentEndParameter q),
        actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = z := by
    obtain ⟨s,hs,he⟩ := hz
    change (actualSegmentPlanarPath q).extend s = z at he
    rw [Path.extend_apply _ hs] at he
    obtain ⟨u,hu,hup⟩ := actualSegmentSquarePathRange q ⟨⟨s,hs⟩,rfl⟩
    exact ⟨u,hu,(congrArg actualParameterSquarePlane hup).trans he⟩
  have actualSegmentEndpointPlanarPosition (q : actualNegativeFaceIntervals × Fin 3) (u : Interval)
      (hu : u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) :
      actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = actualSegmentPlanarPath q 0 ∨
        actualParameterSquarePlane (actualGlobalContactArcs q.1 u) = actualSegmentPlanarPath q 1 := by
    rcases hu with rfl | rfl
    · exact Or.inl (Path.source _).symm
    · exact Or.inr (Path.target _).symm
  have actualSegmentVertexOnArcIsEndpoint (q : actualNegativeFaceIntervals × Fin 3) (v : zeroVertex)
      (hv : actualPlanarVertexPosition v ∈ Graph.edgeArc actualPlanarDrawing q) :
      actualPlanarVertexPosition v = actualSegmentPlanarPath q 0 ∨
        actualPlanarVertexPosition v = actualSegmentPlanarPath q 1 := by
    obtain ⟨u,hu,he⟩ := actualPlanarEdgeArcParameter q _ hv
    have hpoint : zeroVertexPosition v = actualGlobalContactArcs q.1 u :=
      (hActualParameterSquarePlaneInjective he).symm
    have hb := actualZeroVertexOnEdgeBreakpoint v q.1 u hpoint
    have hend := actualSegmentBreakpointIsEndpoint q u hu hb
    rw [←he]
    exact actualSegmentEndpointPlanarPosition q u hend
  have actualDistinctSegmentArcIntersection (q r : actualNegativeFaceIntervals × Fin 3)
      (hqr : q ≠ r) (z : Schoenflies.Plane)
      (hq : z ∈ Graph.edgeArc actualPlanarDrawing q)
      (hr : z ∈ Graph.edgeArc actualPlanarDrawing r) :
      (z = actualSegmentPlanarPath q 0 ∨ z = actualSegmentPlanarPath q 1) ∧
        (z = actualSegmentPlanarPath r 0 ∨ z = actualSegmentPlanarPath r 1) := by
    obtain ⟨u,hu,hup⟩ := actualPlanarEdgeArcParameter q z hq
    obtain ⟨v,hv,hvp⟩ := actualPlanarEdgeArcParameter r z hr
    have he : actualGlobalContactArcs q.1 u = actualGlobalContactArcs r.1 v :=
      hActualParameterSquarePlaneInjective (hup.trans hvp.symm)
    have hends : (u = actualSegmentStartParameter q ∨ u = actualSegmentEndParameter q) ∧
        (v = actualSegmentStartParameter r ∨ v = actualSegmentEndParameter r) := by
      rcases hActualContactArcCollisionClassification q.1 r.1 u v he with ⟨hedge,huv⟩ | ⟨hu0,hv0⟩
      · have hj : q.2 ≠ r.2 := by
          intro hj
          exact hqr (Prod.ext hedge hj)
        subst v
        exact actualDistinctSegmentParameterIntersection q r hj u hu hv
      · have hbu : u = 0 ∨ u = privateParameter 0 ∨ u = privateParameter 1 ∨ u = 1 := by
          rcases hu0 with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inr (Or.inr h1))
        have hbv : v = 0 ∨ v = privateParameter 0 ∨ v = privateParameter 1 ∨ v = 1 := by
          rcases hv0 with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inr (Or.inr h1))
        exact ⟨actualSegmentBreakpointIsEndpoint q u hu hbu,
          actualSegmentBreakpointIsEndpoint r v hv hbv⟩
    constructor
    · rw [←hup]
      exact actualSegmentEndpointPlanarPosition q u hends.1
    · rw [←hvp]
      exact actualSegmentEndpointPlanarPosition r v hends.2
  have actualPlanarDrawingIsDrawing : Graph.IsDrawing actualPlanarGraph actualPlanarDrawing := by
    refine ⟨?_,?_,?_⟩
    · intro q hq
      exact actualPlanarEdgeParameter q
    · intro q x y z hlink hz hze
      obtain ⟨v,rfl⟩ := hz
      have hend := actualSegmentVertexOnArcIsEndpoint q v hze
      change (_ = actualSegmentPlanarPath q 0 ∧ _ = actualSegmentPlanarPath q 1) ∨
        (_ = actualSegmentPlanarPath q 1 ∧ _ = actualSegmentPlanarPath q 0) at hlink
      rcases hlink with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hend
      · exact hend.elim Or.inr Or.inl
    · intro q r hq hr hqr z hze hzr
      obtain ⟨hqend,hrend⟩ := actualDistinctSegmentArcIntersection q r hqr z hze hzr
      have hver : z ∈ actualPlanarGraph.vertexSet := by
        rcases hqend with h0 | h1
        · exact ⟨actualSegmentStartVertex q,(actualSegmentPlanarSource q).symm.trans h0.symm⟩
        · exact ⟨actualSegmentEndVertex q,(actualSegmentPlanarTarget q).symm.trans h1.symm⟩
      refine ⟨hver,?_,?_⟩
      · rcases hqend with h0 | h1
        · exact ⟨actualSegmentPlanarPath q 1,Or.inl ⟨h0,rfl⟩⟩
        · exact ⟨actualSegmentPlanarPath q 0,Or.inr ⟨h1,rfl⟩⟩
      · rcases hrend with h0 | h1
        · exact ⟨actualSegmentPlanarPath r 1,Or.inl ⟨h0,rfl⟩⟩
        · exact ⟨actualSegmentPlanarPath r 0,Or.inr ⟨h1,rfl⟩⟩
  have actualThreeSubedgeParameterCover (e : actualNegativeFaceIntervals) (t : Interval) :
      ∃ j : Fin 3,t∈Set.Icc (actualSegmentStartParameter (e,j))
        (actualSegmentEndParameter (e,j)) := by
    by_cases h0 : t≤privateParameter 0
    · refine ⟨0,?_⟩
      simpa [actualSegmentStartParameter,actualSegmentEndParameter] using
        (show t∈Set.Icc (0 : Interval) (privateParameter 0) from ⟨t.property.1,h0⟩)
    by_cases h1 : t≤privateParameter 1
    · refine ⟨1,?_⟩
      simpa [actualSegmentStartParameter,actualSegmentEndParameter] using
        (show t∈Set.Icc (privateParameter 0) (privateParameter 1) from ⟨(lt_of_not_ge h0).le,h1⟩)
    · refine ⟨2,?_⟩
      simpa [actualSegmentStartParameter,actualSegmentEndParameter] using
        (show t∈Set.Icc (privateParameter 1) (1 : Interval) from ⟨(lt_of_not_ge h1).le,t.property.2⟩)
  have actualContactPlanarArcThreeSubedgeCoverage (e : actualNegativeFaceIntervals) :
      Set.range (fun t : Interval => actualParameterSquarePlane (actualGlobalContactArcs e t))=
        ⋃ j : Fin 3,Graph.edgeArc actualPlanarDrawing (e,j) := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩
      obtain ⟨j,hj⟩ := actualThreeSubedgeParameterCover e t
      obtain ⟨w,hw⟩ := actualIntervalSegmentSurjectiveOnBounds
        (actualSegmentStartParameter (e,j)) (actualSegmentEndParameter (e,j)) t hj
      apply Set.mem_iUnion.mpr
      refine ⟨j,w.val,w.property,?_⟩
      change (actualSegmentPlanarPath (e,j)).extend w.val=
        actualParameterSquarePlane (actualGlobalContactArcs e t)
      rw [Path.extend_apply _ w.property]
      change actualParameterSquarePlane (actualGlobalContactArcs e
        (actualIntervalSegment (actualSegmentStartParameter (e,j)) (actualSegmentEndParameter (e,j)) w))=
          actualParameterSquarePlane (actualGlobalContactArcs e t)
      rw [hw]
    · intro hz
      obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨u,hu,he⟩ := actualPlanarEdgeArcParameter (e,j) z hj
      exact ⟨u,he⟩
  have actualContactPlanarGraphVerticesFinite : actualPlanarGraph.vertexSet.Finite := Set.finite_range _
  have actualOriginalPlanarContactVerticesRetained : actualContactPlaneVertices⊆actualPlanarGraph.vertexSet := by
    rintro z ⟨v,hv,rfl⟩
    exact ⟨Sum.inl ⟨v,hv⟩,rfl⟩
  refine ⟨actualPlanarGraph,actualPlanarDrawing,actualContactPlanarGraphVerticesFinite,rfl,
    actualPlanarDrawingIsDrawing,?_,?_,?_⟩
  · intro e
    exact actualContactPlanarArcThreeSubedgeCoverage e
  · intro z hz
    exact actualOriginalPlanarContactVerticesRetained ⟨z,hz,rfl⟩
  · rintro z ⟨v,rfl⟩
    rcases v with q | ⟨e,j⟩
    · exact Or.inl q.property
    · exact Or.inr (Set.mem_iUnion.mpr ⟨e,privateParameter j,rfl⟩)

end CurveComplex.LocalSurgery
