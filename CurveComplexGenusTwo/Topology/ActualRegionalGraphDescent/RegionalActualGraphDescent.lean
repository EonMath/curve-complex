import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteGraphTiedStepReviewRequest
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFiniteMeasureTermination
import CurveComplexGenusTwo.Topology.ActualRegionalGraphDescent.RegionalFullBudgetInteriorContact
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalFiniteFullContactCommonStep

open CurveComplex Set Topology
open scoped BigOperators
open CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem regional_original_finite_graph_full_contact_descent
    (S : Type) [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    (F : Set S) (hFcompact : IsCompact F)
    (hbase : boundaryCircle S x R ⊆ F)
    (houtside : F ⊆ (openDisk S x R)ᶜ)
    (J : Type) [Fintype J] (c : J → EssentialCurve S)
    (hbaseDisjoint : ∀ i, Disjoint (c i).val.image (boundaryCircle S x R))
    (hfrontier : frontier F = boundaryCircle S x R ∪ ⋃ i, (c i).val.image)
    {ι : Type} [Fintype ι]
    (anchor : C(Interval,↥F)) (a : ι → C(Interval,↥F))
    (hanchorEmb : Topology.IsEmbedding anchor)
    (haEmb : ∀ i, Topology.IsEmbedding (a i))
    (hanchorEnds : (anchor 0).val ∈ boundaryCircle S x R ∧
      (anchor 1).val ∈ boundaryCircle S x R)
    (haEnds : ∀ i, ((a i) 0).val ∈ boundaryCircle S x R ∧
      ((a i) 1).val ∈ boundaryCircle S x R)
    (hanchorProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
      (anchor t).val ∉ frontier F)
    (haProper : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 →
      ((a i) t).val ∉ frontier F)
    (hanchorEssential : ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range anchor ∪ Set.range v)
    (haEssential : ∀ i, ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
      (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
      ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
        Topology.IsEmbedding D ∧
        D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
          Set.range (a i) ∪ Set.range v)
    (adjacent : ι → ι → Prop)
    (hadjSymm : ∀ i j, adjacent i j → adjacent j i) (hadjIrrefl : ∀ i, ¬ adjacent i i)
    (hface : ∀ i j, adjacent i j → Disjoint (Set.range (a i)) (Set.range (a j)))
    (hstart : ∀ i, anchor 0 ∉ Set.range (a i))
    (hterminal : ∀ i, anchor 1 ∉ Set.range (a i))
    (hfinite : ∀ i, (Set.range anchor ∩ Set.range (a i)).Finite) :
    let essential : C(Interval,↥F) → Prop := fun arc =>
      ¬ ∃ v : C(Interval,↥F), Topology.IsEmbedding v ∧
        (∀ t, (v t).val ∈ boundaryCircle S x R) ∧
        ∃ D : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding D ∧
          D '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range arc ∪ Set.range v
    let proper : C(Interval,↥F) → Prop := fun arc =>
      Topology.IsEmbedding arc ∧ (arc 0).val ∈ boundaryCircle S x R ∧
      (arc 1).val ∈ boundaryCircle S x R ∧
      ∀ t ∈ Set.Ioo (0 : Interval) 1, (arc t).val ∉ frontier F
    let valid : (ι → C(Interval,↥F)) → Prop := fun b =>
      (∀ i, proper (b i) ∧ essential (b i)) ∧
      (∀ i j, adjacent i j → Disjoint (Set.range (b i)) (Set.range (b j))) ∧
      (∀ i, (Set.range (b i) ∩ Set.range anchor).Finite) ∧
      (∀ i, anchor 0 ∉ Set.range (b i)) ∧ (∀ i, anchor 1 ∉ Set.range (b i))
    let step : (ι → C(Interval,↥F)) → (ι → C(Interval,↥F)) → Prop := fun b d =>
      ∃ (k : ι) (s : Interval) (copy : C(Interval,↥F)) (G : AmbientIsotopy ↥F),
        d = Function.update b k (d k) ∧ proper copy ∧ essential copy ∧
        Disjoint (Set.range (d k)) (Set.range copy) ∧
        (∀ i, adjacent k i → Disjoint (Set.range copy) (Set.range (b i))) ∧
        Set.range (d k) ∩ Set.range anchor ⊆
          (Set.range (b k) ∩ Set.range anchor) \ {b k s} ∧
        (Set.range (d k) ∩ Set.range anchor).ncard <
          (Set.range (b k) ∩ Set.range anchor).ncard ∧
        (∀ t, (fun y => G.map (t,y)) '' {y : ↥F | y.val ∈ boundaryCircle S x R} =
          {y : ↥F | y.val ∈ boundaryCircle S x R}) ∧
        (∀ t, (fun y => G.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
          {y : ↥F | y.val ∈ frontier F}) ∧
        G.finalMap '' Set.range (b k) = Set.range copy ∧
        (∀ i t z, adjacent k i → G.map (t,b i z) = b i z)
    ∃ (n : ℕ) (seq : ℕ → ι → C(Interval,↥F)),
      n ≤ ∑ i, (Set.range (a i) ∩ Set.range anchor).ncard ∧ seq 0 = a ∧
      (∀ i ≤ n, valid (seq i)) ∧
      (∀ i < n, step (seq i) (seq (i+1))) ∧
      (∀ i, Disjoint (Set.range (seq n i)) (Set.range anchor)) := by
  classical
  intro essential proper valid step
  let State := {b : ι → C(Interval,↥F) // valid b}
  let measure : State → ℕ := fun b => ∑ i, (Set.range (b.val i) ∩ Set.range anchor).ncard
  let relation : State → State → Prop := fun b d => step b.val d.val
  have hinitial : valid a := by
    refine ⟨?_,hface,?_,hstart,hterminal⟩
    · intro i
      exact ⟨⟨haEmb i,(haEnds i).1,(haEnds i).2,haProper i⟩,haEssential i⟩
    · intro i
      simpa [Set.inter_comm] using hfinite i
  have hdrop : ∀ b d : State, relation b d → measure d < measure b := by
    intro b d hd
    obtain ⟨k,s,copy,G,heq,hcp,hce,hbc,hco,hcontain,hlt,hGB,hGF,hmove,hfix⟩ := hd
    change (∑ i, (Set.range (d.val i) ∩ Set.range anchor).ncard) <
      ∑ i, (Set.range (b.val i) ∩ Set.range anchor).ncard
    rw [heq]
    exact regional_indexed_representative_update_full_budget b.val anchor (d.val k) k hlt
  have hnext : ∀ b : State, 0 < measure b → ∃ d : State, relation b d := by
    intro b hb
    have hbprop := b.property
    obtain ⟨harcs,hgraph,hfin,hzero,hone⟩ := hbprop
    have hBF : boundaryCircle S x R ⊆ frontier F := by
      rw [hfrontier]
      exact Set.subset_union_left
    have hpos := regional_positive_full_budget_interior_contact anchor b.val hanchorProper
      hBF (fun i => ⟨(harcs i).1.2.1,(harcs i).1.2.2.1⟩) hzero hone hb
    obtain ⟨r,k,s,hr,hs,hfirst,hcontact,right,new,copy,hrawEss,hnewEmb,hcopyEmb,
      hnew0,hnew1,hcopy0,hcopy1,hnewProper,hcopyProper,hnewEss,hcopyEss,
      hnewCopy,hnewOther,hcopyOther,hcontain,hnewFinite,hlt,
      H,G,hHB,hHF,hHmove,hHfix,hHcopy,hGB,hGF,hGmove,hGfix⟩ :=
      regional_original_finite_graph_tied_full_contact_common_step S g hg hS x R hR htarget
        F hFcompact hbase houtside J c hbaseDisjoint hfrontier anchor b.val
        hanchorEmb (fun i => (harcs i).1.1) hanchorEnds
        (fun i => ⟨(harcs i).1.2.1,(harcs i).1.2.2.1⟩)
        hanchorProper (fun i => (harcs i).1.2.2.2)
        hanchorEssential (fun i => (harcs i).2)
        adjacent hadjSymm hadjIrrefl hgraph hzero
        (fun i => by simpa [Set.inter_comm] using hfin i) hpos
    let d : ι → C(Interval,↥F) := Function.update b.val k new
    have hcontactInv := regional_indexed_update_contact_invariants b.val anchor new k s
      hfin hzero hone hcontain
    have hdValid : valid d := by
      refine ⟨?_,?_,hcontactInv.1,hcontactInv.2.1,hcontactInv.2.2⟩
      · intro i
        by_cases hik : i = k
        · subst i
          simpa [d] using
            (show proper new ∧ essential new from
              ⟨⟨hnewEmb,hnew0,hnew1,hnewProper⟩,hnewEss⟩)
        · simpa [d,Function.update,hik] using harcs i
      · exact regional_indexed_graph_update_disjoint adjacent hadjSymm hadjIrrefl
          b.val k new hgraph hnewOther
    refine ⟨⟨d,hdValid⟩,k,s,copy,G,?_,⟨hcopyEmb,hcopy0,hcopy1,hcopyProper⟩,
      hcopyEss,?_,hcopyOther,?_,?_,hGB,hGF,hGmove,hGfix⟩
    · simp [d]
    · simpa [d] using hnewCopy
    · simpa [d] using hcontain
    · simpa [d] using hlt
  obtain ⟨n,hn,seq,hseq0,hseqn,hseqStep⟩ :=
    regional_finite_measure_descent_terminates measure relation hdrop hnext ⟨a,hinitial⟩
  refine ⟨n,(fun i => (seq i).val),hn,?_,?_,hseqStep,?_⟩
  · exact congrArg Subtype.val hseq0
  · intro i hi
    exact (seq i).property
  · exact regional_zero_full_budget_disjoint (seq n).val anchor
      (seq n).property.2.2.1 hseqn

#print axioms regional_original_finite_graph_full_contact_descent
