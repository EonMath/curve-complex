import RegionalIntrinsicFiniteDomainSimultaneousPositionReviewRequest
import RegionalIntrinsicFiniteLabelDescentScaffold

open CurveComplex Set Topology
open scoped Manifold ContDiff BigOperators
attribute [local instance] c0LabelDescentPropDecidable

theorem regional_original_finite_label_descent_exists
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F) (hFconnected : IsConnected F)
    (hbase : (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆ F)
    (houtside : F ⊆ ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R)ᶜ)
    (hregular : closure (interior F) = F)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (c i).val.image (c j).val.image)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image
      ((chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R))
    (hfrontier : frontier F =
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
        Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ∪
          ⋃ i, (c i).val.image) :
    let boundaryCircle : Set S := (chartAt (EuclideanSpace ℝ (Fin 2)) x).symm ''
      Metric.sphere ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R
    let RegionProperArc :=
      {a : C(Interval,↥F) // Topology.IsEmbedding a ∧
        (a ⟨0,by norm_num⟩).val ∈ boundaryCircle ∧
        (a ⟨1,by norm_num⟩).val ∈ boundaryCircle ∧
        ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F}
    let regionBoundaryParallel (a : RegionProperArc) : Prop :=
      ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ boundaryCircle) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range a.val ∪ Set.range b
    let IntrinsicEssentialArc :=
      {a : RegionProperArc // ¬ regionBoundaryParallel a}
    let intrinsicArcRel (a b : IntrinsicEssentialArc) : Prop :=
      ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ boundaryCircle} =
          {y | y.val ∈ boundaryCircle}) ∧
        (∀ t, (fun y => H.map (t,y)) '' {y | y.val ∈ frontier F} =
          {y | y.val ∈ frontier F}) ∧
        H.finalMap '' Set.range a.val.val = Set.range b.val.val
    let IntrinsicArcVertex := Quot (intrinsicArcRel)
    let intrinsicArcFaces : Set (Finset (IntrinsicArcVertex)) :=
      {τ | τ.Nonempty ∧ ∃ rep : ↥τ → IntrinsicEssentialArc,
        (∀ u, Quot.mk (intrinsicArcRel) (rep u) = u.val) ∧
        ∀ u w, u ≠ w → Disjoint (Set.range (rep u).val.val) (Set.range (rep w).val.val)}
    let intrinsicArcComplex : AbstractSimplicialComplex (IntrinsicArcVertex) := {
      faces := intrinsicArcFaces
      isRelLowerSet_faces := by
        intro τ hτ
        refine ⟨hτ.1,?_⟩
        intro μ hμτ hne
        obtain ⟨rep,hclass,hd⟩ := hτ.2
        refine ⟨hne,(fun u => rep ⟨u.val,hμτ u.property⟩),?_,?_⟩
        · intro u
          exact hclass ⟨u.val,hμτ u.property⟩
        · intro u w huw
          apply hd
          intro he
          exact huw (Subtype.ext (congrArg (fun z : ↥τ => z.val) he))
      singleton_mem := by
        intro u
        obtain ⟨a,ha⟩ := Quot.exists_rep u
        refine ⟨Finset.singleton_nonempty u,(fun _ => a),?_,?_⟩
        · intro z
          exact ha.trans (Finset.mem_singleton.mp z.property).symm
        · intro z w hzw
          exact False.elim (hzw (Subtype.ext
            ((Finset.mem_singleton.mp z.property).trans (Finset.mem_singleton.mp w.property).symm))) }
    ∀ (ι : Type) [Fintype ι] (K : AbstractSimplicialComplex ι)
      (labels0 : ι → IntrinsicArcVertex) (givenAnchor : IntrinsicEssentialArc),
      (∀ σ : Finset ι, σ ∈ K.faces → σ.image labels0 ∈ intrinsicArcComplex.faces) →
      ∃ (n : ℕ) (labels : ℕ → ι → IntrinsicArcVertex),
        labels 0 = labels0 ∧
        (∀ t ≤ n, ∀ σ : Finset ι, σ ∈ K.faces →
          σ.image (labels t) ∈ intrinsicArcComplex.faces) ∧
        (∀ t < n, ∀ σ : Finset ι, σ ∈ K.faces →
          σ.image (labels t) ∪ σ.image (labels (t+1)) ∈ intrinsicArcComplex.faces) ∧
        (∀ σ : Finset ι, σ ∈ K.faces →
          insert (Quot.mk intrinsicArcRel givenAnchor) (σ.image (labels n)) ∈
            intrinsicArcComplex.faces) := by
  classical
  intro B Proper Parallel Arc rel V faces L ι inst K labels0 givenAnchor hfaces
  -- The exact existing positioning obligation remains separately owned.
  have hposition : ∃ (a : ι → Arc) (anchor : Arc),
      (∀ i, Quot.mk rel (a i) = labels0 i) ∧
      Quot.mk rel anchor = Quot.mk rel givenAnchor ∧
      (∀ σ : Finset ι, σ ∈ K.faces → ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
        Disjoint (Set.range (a i).val.val) (Set.range (a j).val.val)) ∧
      (∀ i, anchor.val.val 0 ∉ Set.range (a i).val.val) ∧
      (∀ i, anchor.val.val 1 ∉ Set.range (a i).val.val) ∧
      (∀ i, (Set.range anchor.val.val ∩ Set.range (a i).val.val).Finite) := by
    exact regional_original_intrinsic_finite_domain_simultaneous_position
      S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
      J c hdisjoint hbaseDisjoint hfrontier ι K labels0 givenAnchor hfaces
  obtain ⟨a,anchor,hclass,hanchor,hclique,hzero,hone,hfinite⟩ := hposition
  obtain ⟨n,labels,hlabel0,hvalid,hcommon,hcone⟩ :=
    regional_original_positioned_finite_label_descent_exists S g hg hS x R hR htarget
      F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint
      hfrontier ι K a anchor hclique hzero hone hfinite
  refine ⟨n,labels,?_,hvalid,hcommon,?_⟩
  · exact hlabel0.trans (funext hclass)
  · intro σ hσ
    rw [← hanchor]
    exact hcone σ hσ
