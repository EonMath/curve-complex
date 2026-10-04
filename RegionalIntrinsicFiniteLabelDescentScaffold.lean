import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalIntrinsicFiniteDomainNullhomotopy
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.GenericRealization

open CurveComplex Set Topology
open scoped Manifold ContDiff BigOperators
noncomputable local instance c0LabelDescentPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! Statement-only N0 candidates. The 22 regional arguments and eight local lets,
including their pre-existing structural witnesses, are copied verbatim from the
canonical paid nullhomotopy and the protected regional contractibility scaffold.
No new theorem proof is supplied. The unpositioned wrapper depends on existing
protected positioning task wave80_regional_original_intrinsic_finite_domain_simultaneous_position.
-/

/-- Positioned finite label descent: exactly the paid finite-domain geometric input. -/
theorem regional_original_positioned_finite_label_descent_exists
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
      (a : ι → IntrinsicEssentialArc) (anchor : IntrinsicEssentialArc),
      (∀ σ : Finset ι, σ ∈ K.faces → ∀ i ∈ σ, ∀ j ∈ σ, i ≠ j →
        Disjoint (Set.range (a i).val.val) (Set.range (a j).val.val)) →
      (∀ i, anchor.val.val 0 ∉ Set.range (a i).val.val) →
      (∀ i, anchor.val.val 1 ∉ Set.range (a i).val.val) →
      (∀ i, (Set.range anchor.val.val ∩ Set.range (a i).val.val).Finite) →
      ∃ (n : ℕ) (labels : ℕ → ι → IntrinsicArcVertex),
        labels 0 = (fun i => Quot.mk intrinsicArcRel (a i)) ∧
        (∀ t ≤ n, ∀ σ : Finset ι, σ ∈ K.faces →
          σ.image (labels t) ∈ intrinsicArcComplex.faces) ∧
        (∀ t < n, ∀ σ : Finset ι, σ ∈ K.faces →
          σ.image (labels t) ∪ σ.image (labels (t+1)) ∈ intrinsicArcComplex.faces) ∧
        (∀ σ : Finset ι, σ ∈ K.faces →
          insert (Quot.mk intrinsicArcRel anchor) (σ.image (labels n)) ∈
            intrinsicArcComplex.faces) := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  intro B Proper Parallel Arc rel V faces L ι inst K a anchor hclique hzero hone hfinite
  let adjacent : ι → ι → Prop := fun i j => i ≠ j ∧
    ∃ σ : Finset ι, σ ∈ K.faces ∧ i ∈ σ ∧ j ∈ σ
  have hs : ∀ i j, adjacent i j → adjacent j i := by
    intro i j hij
    obtain ⟨σ,hσ,his,hjs⟩ := hij.2
    exact ⟨hij.1.symm,σ,hσ,hjs,his⟩
  have hi : ∀ i, ¬ adjacent i i := fun i h => h.1 rfl
  have hd : ∀ i j, adjacent i j →
      Disjoint (Set.range (a i).val.val) (Set.range (a j).val.val) := by
    intro i j hij
    obtain ⟨σ,hσ,his,hjs⟩ := hij.2
    exact hclique σ hσ i his j hjs hij.1
  obtain ⟨n,seq,hn,hseq0,hvalid,hsteps,hend⟩ :=
    regional_original_finite_graph_full_contact_descent S g hg hS x R hR htarget
      F hFcompact hbase houtside J c hbaseDisjoint hfrontier anchor.val.val
      (fun i => (a i).val.val) anchor.val.property.1 (fun i => (a i).val.property.1)
      ⟨anchor.val.property.2.1,anchor.val.property.2.2.1⟩
      (fun i => ⟨(a i).val.property.2.1,(a i).val.property.2.2.1⟩)
      anchor.val.property.2.2.2 (fun i => (a i).val.property.2.2.2)
      anchor.property (fun i => (a i).property) adjacent hs hi hd hzero hone hfinite
  let arcs : ℕ → ι → Arc := fun t i =>
    ⟨⟨seq (min t n) i,(hvalid (min t n) (Nat.min_le_right t n)).1 i |>.1⟩,
      (hvalid (min t n) (Nat.min_le_right t n)).1 i |>.2⟩
  let labels : ℕ → ι → V := fun t i => Quot.mk rel (arcs t i)
  have harr : ∀ t ≤ n, ∀ i, (arcs t i).val.val = seq t i := by
    intro t ht i
    simp [arcs,Nat.min_eq_left ht]
  have hlabel0 : labels 0 = fun i => Quot.mk rel (a i) := by
    funext i
    change Quot.mk rel (arcs 0 i) = Quot.mk rel (a i)
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    simpa [arcs] using congrFun hseq0 i
  have hgraph : ∀ t ≤ n, ∀ i j, adjacent i j →
      Disjoint (Set.range (arcs t i).val.val) (Set.range (arcs t j).val.val) := by
    intro t ht i j hij
    rw [harr t ht i,harr t ht j]
    exact (hvalid t ht).2.1 i j hij
  have hfaces : ∀ t ≤ n, ∀ σ : Finset ι, σ ∈ K.faces → σ.image (labels t) ∈ L.faces := by
    intro t ht σ hσ
    have hresult := regional_indexed_quotient_clique_face Arc rel (fun arc => arc.val.val)
      (arcs t) σ (K.isRelLowerSet_faces hσ).1
      (fun i his j hjs hij => hgraph t ht i j ⟨hij,σ,hσ,his,hjs⟩)
    exact hresult
  have hcommon : ∀ t < n, ∀ σ : Finset ι, σ ∈ K.faces →
      σ.image (labels t) ∪ σ.image (labels (t+1)) ∈ L.faces := by
    intro t ht
    obtain ⟨k,s,copy,G,heq,hcp,hce,hbc,hco,hcontain,hlt,hGB,hGF,hmove,hfix⟩ := hsteps t ht
    let copyArc : Arc := ⟨⟨copy,hcp⟩,hce⟩
    have hcopyLabel : Quot.mk rel copyArc = Quot.mk rel (arcs t k) := by
      apply Eq.symm
      apply Quot.sound
      refine ⟨G,hGB,hGF,?_⟩
      rw [harr t (by omega) k]
      exact hmove
    have hupdate : labels (t+1) = Function.update (labels t) k (labels (t+1) k) := by
      funext i
      by_cases hik : i = k
      · subst i
        simp
      · rw [Function.update_of_ne hik]
        change Quot.mk rel (arcs (t+1) i) = Quot.mk rel (arcs t i)
        congr 1
        apply Subtype.ext
        apply Subtype.ext
        rw [harr (t+1) (by omega) i,harr t (by omega) i,heq]
        simp [hik]
    have hstar : ∀ σ : Finset ι, σ ∈ K.faces → k ∈ σ →
        insert (labels (t+1) k) (σ.image (labels t)) ∈ L.faces := by
      intro σ hσ hk
      have hres := regional_indexed_graph_quotient_common_face Arc rel
        (fun arc => arc.val.val) (arcs t) adjacent (hgraph t (by omega)) k
        (arcs (t+1) k) copyArc hcopyLabel
        (fun i hij => by rw [harr t (by omega) i]; exact hco i hij)
        (by rw [harr (t+1) (by omega) k]; exact hbc)
        (fun i hij => by
          rw [harr (t+1) (by omega) k,harr t (by omega) i]
          have hdi := (hvalid (t+1) (by omega)).2.1 k i hij
          rw [heq,Function.update_of_ne hij.1.symm] at hdi
          simpa using hdi)
        σ hk (fun i his j hjs hij => ⟨hij,σ,hσ,his,hjs⟩)
      exact hres
    rw [hupdate]
    exact regional_indexed_label_replacement_contiguous K L (labels t) k
      (labels (t+1) k) (hfaces t (by omega)) hstar
  have hcone : ∀ σ : Finset ι, σ ∈ K.faces →
      insert (Quot.mk rel anchor) (σ.image (labels n)) ∈ L.faces := by
    intro σ hσ
    have hres := regional_indexed_quotient_clique_anchor_face Arc rel
      (fun arc => arc.val.val) (arcs n) anchor σ
      (fun i his j hjs hij => hgraph n le_rfl i j ⟨hij,σ,hσ,his,hjs⟩)
      (fun i his => by rw [harr n le_rfl i]; exact (hend i).symm)
    exact hres
  exact ⟨n,labels,hlabel0,hfaces,hcommon,hcone⟩

#print axioms regional_original_positioned_finite_label_descent_exists
