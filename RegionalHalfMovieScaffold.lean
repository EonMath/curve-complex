import RegionalWeightedHalfFanProof
import RegionalHalfGuidingGeometryScaffold
import RegionalHalfProfileRealization
import HalfMoviePrivateSupport

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P


open private half_profile_localized_ambient_move from HalfMoviePrivateSupport
set_option maxHeartbeats 4000000

/-- M1/M2 (half): exactly the existing local hgeometry movie/count interface. M0 is a proof dependency, not a final-movie assumption. -/
theorem regional_half_disk_supported_movie_geometry
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
    ∀ (ι : Type) [Fintype ι] (r : ι → IntrinsicEssentialArc)
      (α : IntrinsicEssentialArc),
      FamilyInvariant (fun i => (r i).val.val) α.val.val →
      (∀ i j : Option ι, i ≠ j →
        RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
          (augmented (fun i => (r i).val.val) α.val.val i)
          (augmented (fun i => (r i).val.val) α.val.val j)) →
      ∀ v w : ι, v ≠ w →
      ∀ d : PairedHalfBigonDisk F {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F} (r v).val.val (r w).val.val,
      ∀ V : Set ↥F, IsOpen V → range d.disk ⊆ V →
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ boundaryCircle}) →
        let C₀ : Set ↥F := {d.first 1}
        let removed := fun j : ι => ((range d.first \ C₀) ∩ range (r j).val.val).ncard
        let guiding := fun j : ι => ((range d.second \ C₀) ∩ range (r j).val.val).ncard
        let offset := fun j : ι =>
          ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
            (C₀ ∩ range (r j).val.val).ncard
        (∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j else 0) ≤
          (∑ j : ι, if j ≠ v ∧ j ≠ w then removed j else 0) →
        ∃ H : AmbientIsotopy ↥F,
      (∀ t y, y ∉ V → H.map (t,y) = y) ∧
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ boundaryCircle} =
        {y : ↥F | y.val ∈ boundaryCircle}) ∧
      (∀ t, (fun y => H.map (t,y)) '' {y : ↥F | y.val ∈ frontier F} =
        {y : ↥F | y.val ∈ frontier F}) ∧
      (∀ j, j ≠ v →
        H.finalMap ((r v).val.val 0) ≠ (r j).val.val 0 ∧
        H.finalMap ((r v).val.val 0) ≠ (r j).val.val 1 ∧
        H.finalMap ((r v).val.val 1) ≠ (r j).val.val 0 ∧
        H.finalMap ((r v).val.val 1) ≠ (r j).val.val 1) ∧
      α.val.val 0 ∉ H.finalMap '' range (r v).val.val ∧
      α.val.val 1 ∉ H.finalMap '' range (r v).val.val ∧
      (∀ j, j ≠ v →
        (H.finalMap '' range (r v).val.val ∩ range (r j).val.val).Finite) ∧
      (H.finalMap '' range (r v).val.val ∩ range α.val.val).Finite ∧
      (∀ j, j ≠ v → j ≠ w →
        (H.finalMap '' range (r v).val.val ∩ range (r j).val.val).ncard ≤
          guiding j + offset j) ∧
      (H.finalMap '' range (r v).val.val ∩ range (r w).val.val).ncard + 1 ≤
        (range (r v).val.val ∩ range (r w).val.val).ncard := by
  classical
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset hcheap
  let : ClosedSurface S := Classical.choice hS.2.1
  have hBF : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact Set.subset_union_left
  obtain ⟨hfan, _⟩ := regional_paired_half_disk_finite_fan_carrier
    S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
    J c hdisjoint hbaseDisjoint hfrontier ι r α hinv hcross v w hvw d V hV hdV havoid
  obtain ⟨fan⟩ := hfan
  obtain ⟨gap⟩ := regional_half_disk_forbidden_endpoint_gap
    S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
    J c hdisjoint hbaseDisjoint hfrontier ι r α hinv hcross v w hvw d V hV hdV havoid
  -- Use the same actual M0 fan and endpoint gap in the sealed original187 constructor.
  have hchain : Nonempty (RegionalHalfSignedGuidingChain F
      {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F}
      (fun i => (r i).val.val) α.val.val v w d V fan gap) := by
    exact regional_half_signed_guiding_chain
      S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
      J c hdisjoint hbaseDisjoint hfrontier ι r α hinv hcross v w hvw d V hV hdV havoid
      hcheap fan gap
  obtain ⟨chain⟩ := hchain
  let ρ : Ioo (0 : ℝ) chain.bound :=
    ⟨chain.bound / 2, by constructor <;> linarith [chain.bound_pos]⟩
  obtain ⟨E,hE,hcenter,hend,hint,hopen,ε,hε,hqrange,hactive,hzero,
      ν,hνstart,hνend,hν,sweep,hsweep⟩ :=
    regional_half_guiding_chain_profile_realization
      S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular
      J c hdisjoint hbaseDisjoint hfrontier ι r α hinv hcross v w hvw d V hV hdV havoid
      hcheap fan gap chain ρ
  obtain ⟨H,hHB,hHT,hHrange,hHV,hband,houtsideE⟩ :=
    half_profile_localized_ambient_move F boundaryCircle hFcompact hBF E hE hend hint
      hopen ε (fun t => (hε t).1) (fun t => (hε t).2) V hactive
  have hcenterRange : range (fun t : Interval => E (t,⟨0,by norm_num⟩)) =
      range (r v).val.val := by
    congr 1
    funext t
    exact hcenter t
  have hfinalRange : H.finalMap '' range (r v).val.val = range (chain.q ρ) := by
    rw [← hcenterRange,hHrange]
    exact hqrange.symm
  have hendpoint (t : Interval) (ht : t = 0 ∨ t = 1) :
      H.finalMap ((r v).val.val t) = chain.q ρ 0 ∨
        H.finalMap ((r v).val.val t) = chain.q ρ 1 := by
    have htB : ((r v).val.val t).val ∈ boundaryCircle := by
      rcases ht with rfl | rfl
      · exact (r v).val.property.2.1
      · exact (r v).val.property.2.2.1
    have hHtB : (H.finalMap ((r v).val.val t)).val ∈ boundaryCircle := by
      have hm : H.finalMap ((r v).val.val t) ∈
          (fun y => H.map (1,y)) '' {y : ↥F | y.val ∈ boundaryCircle} :=
        ⟨(r v).val.val t,htB,rfl⟩
      rw [hHB 1] at hm
      exact hm
    have hm : H.finalMap ((r v).val.val t) ∈ range (chain.q ρ) := by
      rw [← hfinalRange]
      exact ⟨(r v).val.val t,⟨t,rfl⟩,rfl⟩
    obtain ⟨u,hu⟩ := hm
    by_cases hu0 : u = 0
    · exact Or.inl (hu0 ▸ hu.symm)
    by_cases hu1 : u = 1
    · exact Or.inr (hu1 ▸ hu.symm)
    have hui : u ∈ Ioo (0 : Interval) 1 :=
      ⟨bot_lt_iff_ne_bot.mpr hu0,lt_top_iff_ne_top.mpr hu1⟩
    exact False.elim (chain.q_proper ρ u hui (hu.symm ▸ hBF hHtB))
  refine ⟨H,hHV,hHB,hHT,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j hj
    obtain ⟨h00,h01,h10,h11⟩ := chain.endpoint_safe ρ j hj
    have he0 := hendpoint 0 (Or.inl rfl)
    have he1 := hendpoint 1 (Or.inr rfl)
    constructor
    · rcases he0 with h | h
      · exact h ▸ h00
      · exact h ▸ h10
    constructor
    · rcases he0 with h | h
      · exact h ▸ h01
      · exact h ▸ h11
    constructor
    · rcases he1 with h | h
      · exact h ▸ h00
      · exact h ▸ h10
    · rcases he1 with h | h
      · exact h ▸ h01
      · exact h ▸ h11
  · rw [hfinalRange]
    exact chain.observer_zero_excluded ρ
  · rw [hfinalRange]
    exact chain.observer_one_excluded ρ
  · intro j hj
    rw [hfinalRange]
    exact chain.family_contacts_finite ρ j hj
  · rw [hfinalRange]
    exact chain.observer_contacts_finite ρ
  · intro j hjv hjw
    rw [hfinalRange]
    exact chain.third_count ρ j hjv hjw
  · rw [hfinalRange]
    exact chain.selected_count_drop ρ
