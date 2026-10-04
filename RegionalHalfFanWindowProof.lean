import RegionalWeightedMovieDefinitions
import RegionalNormalizationChordScaffold

open CurveComplex Set Topology Schoenflies RegionalTotalDecrease RegionalWeightedMovies RegionalChordNormalization
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxHeartbeats 4000000
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Exact half M0 fan-window transport: the already-paid event, endpoint,
accounting and continuous whole-trace pieces stay in the caller; this is the remaining window,
selected-axis-sign and in-V isolated-chart construction. -/
theorem regional_paired_half_disk_fan_window_geometry
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
        let a : Option ι → C(Interval,↥F) :=
          augmented (fun i => (r i).val.val) α.val.val
        let events : Set ↥F :=
          contactSites F a {some v,some w} (range d.first ∪ range d.second) V
        ∃ window : ∀ p : ↥events, IncidentFanWindow F a V p.val,
            (∀ p q : ↥events, p ≠ q →
              Disjoint (RegionalChordNormalization.chartPull F (window p).chart
                (Metric.closedBall (0 : Plane) 1))
                (RegionalChordNormalization.chartPull F (window q).chart
                (Metric.closedBall (0 : Plane) 1))) ∧
            (∀ p : ↥events, ∀ i, i ∈ ({some v,some w} : Set (Option ι)) →
              ∀ hip : p.val ∈ range (a i),
              ∃ A : IncidentFanWindow F a V p.val,
                RegionalChordNormalization.chartPull F A.chart
                    (Metric.closedBall (0 : Plane) 1) ⊆
                  RegionalChordNormalization.chartPull F (window p).chart
                    (Metric.ball (0 : Plane) 1) ∧
                incidentPorts a p.val A.chart A.left A.right
                    (⟨i,hip⟩,false) 1 = 0 ∧
                incidentPorts a p.val A.chart A.left A.right
                    (⟨i,hip⟩,true) 1 = 0 ∧
                ∀ j : incidentIndex a p.val, j.val ≠ i →
                  ((0 < incidentPorts a p.val A.chart A.left A.right (j,false) 1 ∧
                    incidentPorts a p.val A.chart A.left A.right (j,true) 1 < 0) ∨
                   (incidentPorts a p.val A.chart A.left A.right (j,false) 1 < 0 ∧
                    0 < incidentPorts a p.val A.chart A.left A.right (j,true) 1))) ∧
            (∀ p : ↥events, ∀ i j, i ≠ j →
              (i ∈ ({some v,some w} : Set (Option ι)) ∨
                j ∈ ({some v,some w} : Set (Option ι))) →
              ∀ u t : Interval, u ∈ Ioo (0 : Interval) 1 →
                t ∈ Ioo (0 : Interval) 1 →
                a i u = p.val → a j t = p.val →
                ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F
                    (a i) (a j) u t,
                  C.OppositeSides ∧
                  {y : ↥F | y.val ∈ C.chart.source ∧
                    C.chart y.val ∈ Plane.closedSquare 0 1} ⊆ V) := by
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  intro boundaryCircle RegionProperArc regionBoundaryParallel IntrinsicEssentialArc
    intrinsicArcRel IntrinsicArcVertex intrinsicArcFaces intrinsicArcComplex
    ι inst r α hinv hcross v w hvw d V hV hdV havoid
    C₀ removed guiding offset a events
  have hfinite (i j : Option ι) (hij : i ≠ j) :
      (range (a i) ∩ range (a j)).Finite := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hinv.2.2.2.2 j
    | some i =>
      cases j with
      | none => exact (hinv.2.2.2.2 i).subset (fun p hp => ⟨hp.2,hp.1⟩)
      | some j => exact hinv.1 i j (fun h => hij (congrArg some h))
  have hBFront : boundaryCircle ⊆ frontier F := by
    dsimp only [boundaryCircle]
    rw [hfrontier]
    exact Set.subset_union_left
  have hproper (i : Option ι) : Topology.IsEmbedding (a i) ∧
      ((a i) 0).val ∈ boundaryCircle ∧ ((a i) 1).val ∈ boundaryCircle ∧
      ∀ t ∈ Ioo (0 : Interval) 1, ((a i) t).val ∉ frontier F := by
    cases i with
    | none => exact α.val.property
    | some i => exact (r i).val.property
  have hends (i j : Option ι) (hij : i ≠ j) :
      a i 0 ≠ a j 0 ∧ a i 0 ≠ a j 1 ∧
      a i 1 ≠ a j 0 ∧ a i 1 ≠ a j 1 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j =>
        exact ⟨(fun h => hinv.2.2.1 j ⟨0,h.symm⟩),
          (fun h => hinv.2.2.1 j ⟨1,h.symm⟩),
          (fun h => hinv.2.2.2.1 j ⟨0,h.symm⟩),
          (fun h => hinv.2.2.2.1 j ⟨1,h.symm⟩)⟩
    | some i =>
      cases j with
      | none =>
        exact ⟨(fun h => hinv.2.2.1 i ⟨0,h⟩),
          (fun h => hinv.2.2.2.1 i ⟨0,h⟩),
          (fun h => hinv.2.2.1 i ⟨1,h⟩),
          (fun h => hinv.2.2.2.1 i ⟨1,h⟩)⟩
      | some j => exact hinv.2.1 i j (fun h => hij (congrArg some h))
  have hend_clear (i j : Option ι) (hij : i ≠ j) :
      a i 0 ∉ range (a j) ∧ a i 1 ∉ range (a j) := by
    have hc (t : Interval) (ht : ((a j) t).val ∈ frontier F) : t = 0 ∨ t = 1 := by
      by_cases ht0 : t = 0
      · exact Or.inl ht0
      · by_cases ht1 : t = 1
        · exact Or.inr ht1
        · exact False.elim ((hproper j).2.2.2 t
            ⟨lt_of_le_of_ne bot_le (Ne.symm ht0),lt_of_le_of_ne le_top ht1⟩ ht)
    constructor
    · rintro ⟨t,ht⟩
      have hb : ((a j) t).val ∈ frontier F := by
        rw [ht]
        exact hBFront (hproper i).2.1
      obtain h0 | h1 := hc t hb
      · exact (hends i j hij).1 (by rw [← ht,h0])
      · exact (hends i j hij).2.1 (by rw [← ht,h1])
    · rintro ⟨t,ht⟩
      have hb : ((a j) t).val ∈ frontier F := by
        rw [ht]
        exact hBFront (hproper i).2.2.1
      obtain h0 | h1 := hc t hb
      · exact (hends i j hij).2.2.1 (by rw [← ht,h0])
      · exact (hends i j hij).2.2.2 (by rw [← ht,h1])
  have hcontact_params (i j : Option ι) (hij : i ≠ j)
      (u t : Interval) (hut : a i u = a j t) :
      u ∈ Ioo (0 : Interval) 1 ∧ t ∈ Ioo (0 : Interval) 1 := by
    have hu0 : u ≠ 0 := fun h => (hend_clear i j hij).1 ⟨t,hut.symm.trans (congrArg (a i) h)⟩
    have hu1 : u ≠ 1 := fun h => (hend_clear i j hij).2 ⟨t,hut.symm.trans (congrArg (a i) h)⟩
    have ht0 : t ≠ 0 := fun h => (hend_clear j i hij.symm).1 ⟨u,hut.trans (congrArg (a j) h)⟩
    have ht1 : t ≠ 1 := fun h => (hend_clear j i hij.symm).2 ⟨u,hut.trans (congrArg (a j) h)⟩
    exact ⟨⟨lt_of_le_of_ne bot_le hu0.symm,lt_of_le_of_ne le_top hu1⟩,
      ⟨lt_of_le_of_ne bot_le (Ne.symm ht0),lt_of_le_of_ne le_top ht1⟩⟩
  have hcontact_interior (i j : Option ι) (hij : i ≠ j)
      (p : ↥F) (hip : p ∈ range (a i)) (hjp : p ∈ range (a j)) :
      p.val ∈ interior F := by
    obtain ⟨u,hu⟩ := hip
    obtain ⟨t,ht⟩ := hjp
    have hparams := hcontact_params i j hij u t (hu.trans ht.symm)
    apply (mem_interior_iff_notMem_frontier p.property).mpr
    rw [← hu]
    exact (hproper i).2.2.2 u hparams.1
  have hevents : (contactSites F a {some v,some w}
      (range d.first ∪ range d.second) V).Finite := by
    let allContacts : Set ↥F := ⋃ i : Option ι, ⋃ j : Option ι,
      if i = j then ∅ else range (a i) ∩ range (a j)
    have hall : allContacts.Finite := by
      apply Set.finite_iUnion
      intro i
      apply Set.finite_iUnion
      intro j
      split
      · exact Set.finite_empty
      · exact hfinite i j ‹i ≠ j›
    apply hall.subset
    intro p hp
    obtain ⟨hpV,hps,i,hi,j,hij,hpij⟩ := hp
    exact Set.mem_iUnion₂.mpr ⟨i,j,by simpa only [if_neg hij] using hpij⟩
  let allContacts : Set ↥F := ⋃ i : Option ι, ⋃ j : Option ι,
    if i = j then ∅ else range (a i) ∩ range (a j)
  have hall : allContacts.Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.finite_iUnion
    intro j
    split
    · exact Set.finite_empty
    · exact hfinite i j ‹i ≠ j›
  have heventParam (p : ↥events) (i : Option ι) (hi : p.val ∈ range (a i)) :
      ∃ t ∈ Ioo (0 : Interval) 1, a i t = p.val := by
    obtain ⟨hpV,hps,k,hk,j,hkj,hpk,hpj⟩ := p.property
    obtain ⟨t,ht⟩ := hi
    by_cases hik : i = k
    · subst k
      obtain ⟨u,hu⟩ := hpj
      exact ⟨t,(hcontact_params i j hkj t u (ht.trans hu.symm)).1,ht⟩
    · obtain ⟨u,hu⟩ := hpk
      exact ⟨t,(hcontact_params i k hik t u (ht.trans hu.symm)).1,ht⟩
  have heventInterior (p : ↥events) : p.val.val ∈ interior F := by
    obtain ⟨hpV,hps,k,hk,j,hkj,hpk,hpj⟩ := p.property
    exact hcontact_interior k j hkj p.val hpk hpj
  have heventInc (p : ↥events) :
      ∃ i j, i ≠ j ∧ p.val ∈ range (a i) ∩ range (a j) := by
    obtain ⟨hpV,hps,k,hk,j,hkj,hpk,hpj⟩ := p.property
    exact ⟨k,j,hkj,hpk,hpj⟩
  obtain ⟨W,hW,hWV⟩ := isOpen_induced_iff.mp hV
  let contacts : Set S := Subtype.val '' allContacts
  have hcFinite : contacts.Finite := hall.image _
  have hsitesFinite : (Subtype.val '' events : Set S).Finite := hevents.image _
  obtain ⟨sep,hsep,hsepDisjoint⟩ := hsitesFinite.t2_separation
  have hlocal (p : ↥events) : ∃ N : Set S, IsOpen N ∧ p.val.val ∈ N ∧
      closure N ⊆ (Subtype.val '' V ∩ interior F) ∩ sep p.val.val ∧
      (∀ i j, i ≠ j → ∀ y ∈ range (a i) ∩ range (a j), y.val ∈ N → y = p.val) := by
    let O : Set S := ((W ∩ interior F) ∩ sep p.val.val) \ (contacts \ {p.val.val})
    have hO : IsOpen O := ((hW.inter isOpen_interior).inter (hsep _).2).sdiff
      (hcFinite.sdiff.isClosed)
    have hpW : p.val.val ∈ W := by
      have hpV : p.val ∈ V := p.property.1
      rw [← hWV] at hpV
      exact hpV
    have hpO : p.val.val ∈ O :=
      ⟨⟨⟨hpW,heventInterior p⟩,(hsep _).1⟩,fun h => h.2 (mem_singleton _)⟩
    obtain ⟨K,hpK,hK,hKO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hpO)
    obtain ⟨N,hNK,hN,hpN⟩ := mem_nhds_iff.mp hpK
    have hNO : closure N ⊆ O := (closure_minimal hNK hK).trans hKO
    refine ⟨N,hN,hpN,?_,?_⟩
    · intro y hy
      have hh := hNO hy
      refine ⟨⟨?_,hh.1.1.2⟩,hh.1.2⟩
      refine ⟨⟨y,interior_subset hh.1.1.2⟩,?_,rfl⟩
      rw [← hWV]
      exact hh.1.1.1
    · intro i j hij y hy hyN
      have hyO := hNO (subset_closure hyN)
      have hyc : y.val ∈ contacts := ⟨y,mem_iUnion₂.mpr
        ⟨i,j,by simpa only [if_neg hij] using hy⟩,rfl⟩
      apply Subtype.ext
      by_contra hyn
      exact hyO.2 ⟨hyc,hyn⟩
  choose N hN hpN hNclosure hOnly using hlocal
  have hfan (p : ↥events) : ∃ A : IncidentFanWindow F a V p.val,
      A.chart.source ⊆ N p := by
    obtain ⟨e,l,rr,τ,hes,hp,hball,hcuts,hcenter,hclosed,hopen,hradial,hclear,hsphere,hinj⟩ :=
      regional_finite_incident_whole_trace_disk S g hg hS x R hR htarget F hFcompact
        hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
        (Option ι) a (fun i => (hproper i).1) hfinite p.val (heventInc p)
        (heventParam p) (N p) (hN p) (hpN p)
        (fun y hy => (hNclosure p (subset_closure hy)).1.2) (hOnly p)
    refine ⟨{ chart := e
              source_closure := ?_
              contact_in_source := hp.1
              contact_zero := hp.2
              disk_in_target := hball
              left := l
              right := rr
              center := τ
              cuts := hcuts
              at_center := hcenter
              whole_closed := hclosed
              whole_open := hopen
              radial_trace := hradial
              nonincident_clear := hclear
              ports_on_sphere := hsphere
              ports_injective := hinj },hes⟩
    exact fun y hy => (hNclosure p (closure_mono hes hy)).1
  choose window hwindowN using hfan
  have hfanAxis {S κ : Type} [TopologicalSpace S] {F : Set S}
      (a : κ → C(Interval,↥F)) (p : ↥F) (V : Set ↥F)
      (A : IncidentFanWindow F a V p) (seed : incidentIndex a p)
      (hleft : incidentPorts a p A.chart A.left A.right (seed,false) 1 = 0)
      (hright : incidentPorts a p A.chart A.left A.right (seed,true) 1 = 0)
      (hcover : ∀ z ∈ Metric.sphere (0:Plane) 1, z 1 = 0 →
        z = incidentPorts a p A.chart A.left A.right (seed,false) ∨
        z = incidentPorts a p A.chart A.left A.right (seed,true)) :
      ∀ y : ↥F, y.val ∈ A.chart.source → A.chart y.val ∈ Metric.closedBall (0:Plane) 1 →
        (y ∈ range (a seed.val) ↔ A.chart y.val 1 = 0) := by
    let port := incidentPorts a p A.chart A.left A.right
    have hradialZero (z : Plane)
        (hz : z ∈ segment ℝ (port (seed,false)) 0 ∪ segment ℝ 0 (port (seed,true))) : z 1 = 0 := by
      rw [segment_symm ℝ (port (seed,false)) 0] at hz
      rcases hz with hz | hz
      · rw [segment_eq_image'] at hz
        obtain ⟨q,hq,rfl⟩ := hz
        change (0:ℝ) + q * (port (seed,false) 1 - 0) = 0
        rw [hleft];ring
      · rw [segment_eq_image'] at hz
        obtain ⟨q,hq,rfl⟩ := hz
        change (0:ℝ) + q * (port (seed,true) 1 - 0) = 0
        rw [hright];ring
    have hradialCover (z : Plane) (hz : z ∈ Metric.closedBall (0:Plane) 1) (ha : z 1 = 0) :
        z ∈ segment ℝ (port (seed,false)) 0 ∪ segment ℝ 0 (port (seed,true)) := by
      by_cases hz0 : z = 0
      · left;rw [hz0];exact right_mem_segment ℝ _ _
      have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      let u := ‖z‖⁻¹ • z
      have hu : u ∈ Metric.sphere (0:Plane) 1 := by
        rw [Metric.mem_sphere,dist_zero_right]
        change ‖‖z‖⁻¹ • z‖ = 1
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
      have hua : u 1 = 0 := by change ‖z‖⁻¹ * z 1 = 0;rw [ha,mul_zero]
      have hcoef : ‖z‖ ∈ Icc (0:ℝ) 1 :=
        ⟨norm_nonneg _,by simpa only [Metric.mem_closedBall,dist_zero_right] using hz⟩
      have hzu : ‖z‖ • u = z := by dsimp [u];rw [smul_smul,mul_inv_cancel₀ hn.ne',one_smul]
      rcases hcover u hu hua with he | he
      · left;rw [segment_symm,segment_eq_image']
        refine ⟨‖z‖,hcoef,?_⟩
        change u = port (seed,false) at he
        rw [he] at hzu
        simpa only [sub_zero,zero_add] using hzu
      · right;rw [segment_eq_image']
        refine ⟨‖z‖,hcoef,?_⟩
        change u = port (seed,true) at he
        rw [he] at hzu
        simpa only [sub_zero,zero_add] using hzu
    intro y hys hyb
    constructor
    · intro hyr
      have hy : y ∈ (a seed.val) '' Icc (A.left seed) (A.right seed) := by
        rw [← A.whole_closed seed]
        exact ⟨⟨hys,hyb⟩,hyr⟩
      obtain ⟨t,ht,rfl⟩ := hy
      apply hradialZero
      rw [← A.radial_trace seed]
      exact ⟨t,ht,rfl⟩
    · intro hya
      have hm := hradialCover (A.chart y.val) hyb hya
      rw [← A.radial_trace seed] at hm
      obtain ⟨t,ht,he⟩ := hm
      have hs : ((a seed.val) t).val ∈ A.chart.source := by
        have hh : (a seed.val) t ∈ (a seed.val) '' Icc (A.left seed) (A.right seed) := ⟨t,ht,rfl⟩
        rw [← A.whole_closed seed] at hh
        exact hh.1.1
      exact ⟨t,Subtype.ext (A.chart.injOn hs hys he)⟩
  have hsideBridge (H : OpenPartialHomeomorph Plane Plane)
      (h0 : (0:Plane) ∈ H.source) (hz : H 0 = 0)
      (ha : ∀ z ∈ H.source, z 1 = 0 ↔ H z 1 = 0) :
      ∃ (P : Plane ≃ₜ (ℝ × ℝ)) (r : ℝ),
        (∀ z, (P z).1 = z 1) ∧ P 0 = (0,0) ∧ 0 < r ∧
        (∀ z, P z ∈ Metric.ball (0,0) r → z ∈ H.source) ∧
        ∃ ε : ZMod 2, ∀ z, P z ∈ Metric.ball (0,0) r → z 1 ≠ 0 →
          (if 0 < H z 1 then (1 : ZMod 2) else 0) =
            (if 0 < z 1 then (1 : ZMod 2) else 0) + ε := by
    let P : Plane ≃ₜ (ℝ × ℝ) :=
      ((EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans
        (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).toHomeomorph).trans
        (Homeomorph.prodComm ℝ ℝ)
    have hPf (z : Plane) : (P z).1 = z 1 := rfl
    have hPz : P 0 = (0,0) := rfl
    have hPiz : P.symm (0,0) = 0 := by rw [← hPz,P.symm_apply_apply]
    let T := P.symm.toOpenPartialHomeomorph.trans (H.transHomeomorph P)
    have hTs : (0,0) ∈ T.source := by
      rw [OpenPartialHomeomorph.trans_source]
      exact ⟨Set.mem_univ _,by change P.symm (0,0) ∈ H.source;rw [hPiz];exact h0⟩
    have hTz : T (0,0) = (0,0) := by
      change P (H (P.symm (0,0))) = (0,0)
      rw [hPiz,hz,hPz]
    have hTa (z : ℝ × ℝ) (hs : z ∈ T.source) : z.1 = 0 ↔ (T z).1 = 0 := by
      rw [OpenPartialHomeomorph.trans_source] at hs
      have hsH : P.symm z ∈ H.source := hs.2
      change z.1 = 0 ↔ (P (H (P.symm z))).1 = 0
      have hfi : (P.symm z) 1 = z.1 := by
        have hh := hPf (P.symm z)
        rw [P.apply_symm_apply] at hh
        exact hh.symm
      rw [hPf,← hfi]
      exact ha _ hsH
    obtain ⟨r,hr,hball,ε,hrel⟩ :=
      CurveComplex.LocalSurgery.local_axis_transition_side_constant T hTs hTz hTa
    refine ⟨P,r,hPf,hPz,hr,?_,ε,?_⟩
    · intro z hz
      have hs := hball hz
      rw [OpenPartialHomeomorph.trans_source] at hs
      have hsH : P.symm (P z) ∈ H.source := hs.2
      simpa only [P.symm_apply_apply] using hsH
    · intro z hz hn
      have hh := hrel (P z) hz (by rw [hPf];exact hn)
      change (if 0 < (P (H (P.symm (P z)))).1 then (1:ZMod 2) else 0) =
        (if 0 < (P z).1 then (1:ZMod 2) else 0)+ε at hh
      simpa only [P.symm_apply_apply,hPf] using hh
  have hunitAxis (z : Plane) (hz : z ∈ Metric.sphere (0:Plane) 1) (ha : z 1 = 0) :
      z = Plane.mk 1 0 ∨ z = Plane.mk (-1) 0 := by
    have hn : |z 0| = 1 := by
      have hnorm : ‖z‖ = |z 0| := by
        rw [EuclideanSpace.norm_eq]
        simp [Fin.sum_univ_two,ha,Real.norm_eq_abs,Real.sqrt_sq_eq_abs]
      simpa only [Metric.mem_sphere,dist_zero_right,hnorm] using hz
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hn with h | h
    · left;apply PiLp.ext;intro k;fin_cases k;exact h;exact ha
    · right;apply PiLp.ext;intro k;fin_cases k;exact h;exact ha
  have haxisProducer (ep : ↥events) (N : Set S) (hN : IsOpen N)
      (hpN : ep.val.val ∈ N)
      (hNclosure : closure N ⊆ Subtype.val '' V ∩ interior F)
      (hOnly : ∀ i j, i ≠ j → ∀ y ∈ range (a i) ∩ range (a j),
        y.val ∈ N → y = ep.val)
      (seed : incidentIndex a ep.val) :
      ∃ A : IncidentFanWindow F a V ep.val, A.chart.source ⊆ N ∧
        incidentPorts a ep.val A.chart A.left A.right (seed,false) 1 = 0 ∧
        incidentPorts a ep.val A.chart A.left A.right (seed,true) 1 = 0 := by
    let p := ep.val
    have hEmb (i : Option ι) : IsEmbedding (a i) := (hproper i).1
    have hParam := heventParam ep
    have hNF : N ⊆ interior F := fun y hy => (hNclosure (subset_closure hy)).2
    let Inc := {i : Option ι // p ∈ range (a i)}
    letI : Fintype Inc := Fintype.ofFinite Inc
    let Away := {i : Option ι // p ∉ range (a i)}
    letI : Fintype Away := Fintype.ofFinite Away
    let f : Inc → C(Interval,S) := fun j =>
      ⟨fun t => (a j.val t).val, continuous_subtype_val.comp (a j.val).continuous⟩
    have hf (j : Inc) : IsEmbedding (f j) :=
      IsEmbedding.subtypeVal.comp (hEmb j.val)
    choose center hci hcenter using (fun j : Inc => hParam j.val j.property)
    have hfc (j : Inc) : f j (center j) = p.val := congrArg Subtype.val (hcenter j)
    let e₀ := chartAt Plane p.val
    let Q := (e₀.restr N).trans (Homeomorph.subRight (e₀ p.val)).toOpenPartialHomeomorph
    have hQs : Q.source = e₀.source ∩ N := by
      simp [Q,OpenPartialHomeomorph.trans_source,OpenPartialHomeomorph.restr_source,hN.interior_eq]
    have hpQ : p.val ∈ Q.source := by rw [hQs];exact ⟨mem_chart_source _ _,hpN⟩
    have hQp : Q p.val = 0 := by change e₀ p.val - e₀ p.val = 0;exact sub_self _
    let U := Q.source
    have hU : IsOpen U := Q.open_source
    have hpU : p.val ∈ U := hpQ
    have hwindow (j : Inc) : ∃ l d : Interval,
        0 < l ∧ l < center j ∧ center j < d ∧ d < 1 ∧
        ∀ t ∈ Set.Icc l d, f j t ∈ U := by
      have hn : (f j) ⁻¹' U ∈ nhds (center j) :=
        (hU.preimage (f j).continuous).mem_nhds (by change f j (center j) ∈ U; rw [hfc];exact hpU)
      obtain ⟨l₀,d₀,hl,hd⟩ :=
        (mem_nhds_iff_exists_Ioo_subset' ⟨0,(hci j).1⟩ ⟨1,(hci j).2⟩).mp hn
      obtain ⟨l,hll,hls⟩ := exists_between hl.1
      obtain ⟨d,hsd,hdd⟩ := exists_between hl.2
      refine ⟨l,d,(show (0:Interval) ≤ l₀ from bot_le).trans_lt hll,hls,hsd,
        hdd.trans_le (show d₀ ≤ (1:Interval) from le_top),?_⟩
      intro t ht
      exact hd ⟨hll.trans_le ht.1,ht.2.trans_lt hdd⟩
    choose left right hleft0 hleft hright hright1 hwindow using hwindow
    let tip : Inc × Bool → Interval := fun j => if j.2 then right j.1 else left j.1
    let param : Inc × Bool → C(Interval,Interval) := fun j => {
      toFun := fun t => ⟨(center j.1).val + ((tip j).val - (center j.1).val) * t.val,by
        have hc := (center j.1).property
        have ht := (tip j).property
        have h := t.property
        constructor
        · have ha : 0 ≤ (1-t.val)*(center j.1).val := mul_nonneg (by linarith [h.2]) hc.1
          have hb : 0 ≤ t.val*(tip j).val := mul_nonneg h.1 ht.1
          nlinarith
        · have ha : 0 ≤ (1-t.val)*(1-(center j.1).val) := mul_nonneg (by linarith [h.2]) (by linarith [hc.2])
          have hb : 0 ≤ t.val*(1-(tip j).val) := mul_nonneg h.1 (by linarith [ht.2])
          nlinarith⟩
      continuous_toFun := by fun_prop }
    have hparam0 (j : Inc × Bool) : param j 0 = center j.1 := Subtype.ext (by
      change (center j.1).val + ((tip j).val - (center j.1).val)*0 = (center j.1).val
      ring)
    have hparam1 (j : Inc × Bool) : param j 1 = tip j := Subtype.ext (by
      change (center j.1).val + ((tip j).val - (center j.1).val)*1 = (tip j).val
      ring)
    have htipne (j : Inc × Bool) : tip j ≠ center j.1 := by
      rcases j with ⟨j,k⟩
      cases k
      · exact (hleft j).ne
      · exact (hright j).ne.symm
    have hparami (j : Inc × Bool) : Function.Injective (param j) := by
      intro t u he
      apply Subtype.ext
      have heq := congrArg Subtype.val he
      change (center j.1).val + ((tip j).val - (center j.1).val)*t.val =
        (center j.1).val + ((tip j).val - (center j.1).val)*u.val at heq
      have hne : (tip j).val - (center j.1).val ≠ 0 := sub_ne_zero.mpr (fun hh =>
        htipne j (Subtype.ext hh))
      exact mul_left_cancel₀ hne (add_left_cancel heq)
    have hparamK (j : Inc × Bool) (t : Interval) :
        param j t ∈ Set.Icc (left j.1) (right j.1) := by
      rcases j with ⟨j,k⟩
      cases k
      · change (left j).val ≤ (center j).val + ((left j).val - (center j).val)*t.val ∧
          (center j).val + ((left j).val - (center j).val)*t.val ≤ (right j).val
        have hl : (left j).val < (center j).val := hleft j
        have hr : (center j).val < (right j).val := hright j
        constructor <;> nlinarith [t.property.1,t.property.2]
      · change (left j).val ≤ (center j).val + ((right j).val - (center j).val)*t.val ∧
          (center j).val + ((right j).val - (center j).val)*t.val ≤ (right j).val
        have hl : (left j).val < (center j).val := hleft j
        have hr : (center j).val < (right j).val := hright j
        constructor <;> nlinarith [t.property.1,t.property.2]
    let β : Inc × Bool → C(Interval,S) := fun j => (f j.1).comp (param j)
    have hβ (j : Inc × Bool) : IsEmbedding (β j) :=
      (hf j.1).comp (((param j).continuous.isClosedEmbedding (hparami j)).isEmbedding)
    have hβ0 (j : Inc × Bool) : β j 0 = p.val := by
      change f j.1 (param j 0) = p
      rw [hparam0,hfc]
    have hβU (j : Inc × Bool) (t : Interval) : β j t ∈ U :=
      hwindow j.1 _ (hparamK j t)
    have hβmeet (i j : Inc × Bool) (hij : i ≠ j) :
        Set.range (β i) ∩ Set.range (β j) = {p.val} := by
      apply Set.Subset.antisymm
      · rintro y ⟨⟨t,rfl⟩,⟨u,heu⟩⟩
        have he : f j.1 (param j u) = f i.1 (param i t) := heu
        have hpval : β i t = p.val := by
          by_cases hj : j.1 = i.1
          · have hpar : param j u = param i t := (hf i.1).injective (hj ▸ he)
            have hk : j.2 ≠ i.2 := fun hh => hij (Prod.ext hj hh).symm
            have hpt : param i t = center i.1 := by
              apply Subtype.ext
              rcases i with ⟨i,k⟩
              rcases j with ⟨j,l⟩
              dsimp only at hj hk
              subst j
              cases k <;> cases l
              · exact (hk rfl).elim
              · have ht : (param (i,false) t).val ≤ (center i).val := by
                  change (center i).val + ((left i).val - (center i).val)*t.val ≤ (center i).val
                  have hl : (left i).val < (center i).val := hleft i
                  nlinarith [t.property.1]
                have hu : (center i).val ≤ (param (i,true) u).val := by
                  change (center i).val ≤ (center i).val + ((right i).val - (center i).val)*u.val
                  have hr : (center i).val < (right i).val := hright i
                  nlinarith [u.property.1]
                exact le_antisymm ht ((congrArg Subtype.val hpar) ▸ hu)
              · have ht : (center i).val ≤ (param (i,true) t).val := by
                  change (center i).val ≤ (center i).val + ((right i).val - (center i).val)*t.val
                  have hr : (center i).val < (right i).val := hright i
                  nlinarith [t.property.1]
                have hu : (param (i,false) u).val ≤ (center i).val := by
                  change (center i).val + ((left i).val - (center i).val)*u.val ≤ (center i).val
                  have hl : (left i).val < (center i).val := hleft i
                  nlinarith [u.property.1]
                exact le_antisymm ((congrArg Subtype.val hpar) ▸ hu) ht
              · exact (hk rfl).elim
            change f i.1 (param i t) = p.val
            rw [hpt,hfc]
          · have haeq : a j.1.val (param j u) = a i.1.val (param i t) := Subtype.ext he
            have hyQ : β i t ∈ Q.source := hβU i t
            have hyN : (a i.1.val (param i t)).val ∈ N := (hQs ▸ hyQ).2
            have hy : a i.1.val (param i t) = p :=
              hOnly i.1.val j.1.val (fun hij => hj (Subtype.ext hij.symm))
                (a i.1.val (param i t)) ⟨mem_range_self _,⟨param j u,haeq⟩⟩ hyN
            exact congrArg Subtype.val hy
        exact Set.mem_singleton_iff.mpr hpval
      · rintro y rfl
        exact ⟨⟨0,hβ0 i⟩,⟨0,hβ0 j⟩⟩
    let Far₀ : Set S := ⋃ j : Inc, f j '' (Set.Ioo (left j) (right j))ᶜ
    let Far₁ : Set S := ⋃ j : Away, range (fun t : Interval => (a j.val t).val)
    let Far : Set S := Far₀ ∪ Far₁
    have hFar : IsClosed Far := by
      apply IsClosed.union
      · exact isClosed_iUnion_of_finite (fun j =>
          ((isCompact_univ.of_isClosed_subset isOpen_Ioo.isClosed_compl (Set.subset_univ _)).image
            (f j).continuous).isClosed)
      · exact isClosed_iUnion_of_finite (fun j =>
          (isCompact_range (continuous_subtype_val.comp (a j.val).continuous)).isClosed)
    have hpFar : p.val ∉ Far := by
      rintro (hh | hh)
      · obtain ⟨j,t,ht,he⟩ := Set.mem_iUnion.mp hh
        have heq : t = center j := (hf j).injective (he.trans (hfc j).symm)
        exact ht (heq.symm ▸ ⟨hleft j,hright j⟩)
      · obtain ⟨j,t,he⟩ := Set.mem_iUnion.mp hh
        exact j.property ⟨t,Subtype.ext he⟩
    let Vstar := Q '' (Q.source \ Far)
    have hVstar : IsOpen Vstar := Q.isOpen_image_of_subset_source
      (Q.open_source.sdiff hFar) Set.diff_subset
    have hzeroV : (0:Plane) ∈ Vstar := ⟨p.val,⟨hpQ,hpFar⟩,hQp⟩
    let γ : Inc × Bool → Interval → Plane := fun j => Q ∘ β j
    have hγ (j : Inc × Bool) : IsClosedEmbedding (γ j) := by
      apply (Q.continuousOn.comp_continuous (β j).continuous
        (fun t => (hβU j t))).isClosedEmbedding
      intro t u he
      exact (hβ j).injective (Q.injOn (hβU j t) (hβU j u) he)
    have hγ0 (j : Inc × Bool) : γ j 0 = 0 := by
      change Q (β j 0) = 0
      rw [hβ0,hQp]
    have hγmeet (i j : Inc × Bool) (hij : i ≠ j) :
        Set.range (γ i) ∩ Set.range (γ j) = {0} := by
      apply Set.Subset.antisymm
      · rintro z ⟨⟨t,rfl⟩,⟨u,he⟩⟩
        have hβeq : β j u = β i t := Q.injOn (hβU j u) (hβU i t) he
        have hp : β i t = p.val := Set.mem_singleton_iff.mp
          (hβmeet i j hij ▸ (show β i t ∈ Set.range (β i) ∩ Set.range (β j) from
            ⟨Set.mem_range_self _,⟨u,hβeq⟩⟩))
        change Q (β i t) = 0
        rw [hp,hQp]
      · rintro z rfl
        exact ⟨⟨0,hγ0 i⟩,⟨0,hγ0 j⟩⟩
    obtain ⟨R,hop⟩ := prescribed_pair_finite_actual_star_radialization_zero
      γ hγ hγ0 hγmeet (seed,false) (seed,true)
      (fun he => Bool.false_ne_true (congrArg Prod.snd he)) Vstar hVstar hzeroV
    have hparamRange (j : Inc × Bool) : Set.range (param j) =
        Set.uIcc (center j.1) (tip j) := by
      rw [← Set.image_univ, unitInterval.univ_eq_Icc]
      rcases j with ⟨j,k⟩
      cases k
      · have hant : AntitoneOn (param (j,false)) (Set.Icc (0:Interval) 1) := by
          intro t ht u hu htu
          change (center j).val + ((left j).val - (center j).val)*u.val ≤
            (center j).val + ((left j).val - (center j).val)*t.val
          have hh : (left j).val < (center j).val := hleft j
          have htu : t.val ≤ u.val := htu
          nlinarith
        rw [ContinuousOn.image_Icc_of_antitoneOn (show (0:Interval) ≤ 1 by norm_num)
          (param (j,false)).continuous.continuousOn hant,hparam0,hparam1]
        exact (Set.uIcc_of_ge (hleft j).le).symm
      · have hmono : MonotoneOn (param (j,true)) (Set.Icc (0:Interval) 1) := by
          intro t ht u hu htu
          change (center j).val + ((right j).val - (center j).val)*t.val ≤
            (center j).val + ((right j).val - (center j).val)*u.val
          have hh : (center j).val < (right j).val := hright j
          have htu : t.val ≤ u.val := htu
          nlinarith
        rw [ContinuousOn.image_Icc_of_monotoneOn (show (0:Interval) ≤ 1 by norm_num)
          (param (j,true)).continuous.continuousOn hmono,hparam0,hparam1]
        exact (Set.uIcc_of_le (hright j).le).symm
    have hwholeCover (j : Inc) : Set.range (f j) ⊆
        Far ∪ (Set.range (β (j,false)) ∪ Set.range (β (j,true))) := by
      rintro y ⟨t,rfl⟩
      by_cases ht : t ∈ Set.Ioo (left j) (right j)
      · right
        by_cases htc : t ≤ center j
        · left
          have hh : t ∈ Set.range (param (j,false)) := by
            rw [hparamRange]
            change t ∈ Set.uIcc (center j) (left j)
            rw [Set.uIcc_of_ge (hleft j).le]
            exact ⟨ht.1.le,htc⟩
          obtain ⟨u,rfl⟩ := hh
          exact ⟨u,rfl⟩
        · right
          have hh : t ∈ Set.range (param (j,true)) := by
            rw [hparamRange]
            change t ∈ Set.uIcc (center j) (right j)
            rw [Set.uIcc_of_le (hright j).le]
            exact ⟨(lt_of_not_ge htc).le,ht.2.le⟩
          obtain ⟨u,rfl⟩ := hh
          exact ⟨u,rfl⟩
      · left
        exact Or.inl (Set.mem_iUnion.mpr ⟨j,t,ht,rfl⟩)
    have hLinear (v : Plane) (hv : v ≠ 0) :
        ∃ T : Plane ≃L[ℝ] Plane, T v = Plane.mk 1 0 := by
      let L : ℂ ≃L[ℝ] Plane := Complex.equivRealProdCLM.trans
        ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm)
      let ζ : ℂ := L.symm v
      have hζ : ζ ≠ 0 := by
        intro hz
        apply hv
        have hh := congrArg L hz
        simpa [ζ] using hh
      let M : ℂ ≃L[ℂ] ℂ :=
        (LinearEquiv.smulOfNeZero ℂ ℂ ζ⁻¹ (inv_ne_zero hζ)).toContinuousLinearEquiv
      let T : Plane ≃L[ℝ] Plane := L.symm.trans ((M.restrictScalars ℝ).trans L)
      refine ⟨T,?_⟩
      change L (ζ⁻¹ * ζ) = Plane.mk 1 0
      rw [inv_mul_cancel₀ hζ]
      rfl
    obtain ⟨T,hTv⟩ := hLinear (R.vector (seed,false)) (R.vector_nonzero _)
    let Q₀ := Q.transHomeomorph (R.H.trans T.toHomeomorph)
    have hQ₀s : Q₀.source = Q.source := rfl
    have hQ₀val (x : S) : Q₀ x = T (R.H (Q x)) := rfl
    have hQ₀p : Q₀ p.val = 0 := by rw [hQ₀val,hQp,R.fixes_center,map_zero]
    have hopenT : IsOpen (T.symm ⁻¹' Metric.ball (0:Plane) R.coreRadius) :=
      Metric.isOpen_ball.preimage T.symm.continuous
    have hzeroT : (0:Plane) ∈ T.symm ⁻¹' Metric.ball (0:Plane) R.coreRadius := by
      rw [Set.mem_preimage,map_zero,Metric.mem_ball,dist_self]
      exact R.core_pos
    obtain ⟨ρ,hρ,hρcore⟩ := Metric.isOpen_iff.mp hopenT 0 hzeroT
    have hscale : ∃ σ : ℝ, ∃ E : OpenPartialHomeomorph S Plane,
        0 < σ ∧ E.source = Q₀.source ∧ E p.val = 0 ∧
        Metric.closedBall (0:Plane) 1 ⊆ E.target ∧
        (∀ x, E x = σ⁻¹ • Q₀ x) ∧
        ∀ x ∈ E.source, E x ∈ Metric.closedBall (0:Plane) 1 →
          ‖Q₀ x‖ < ρ := by
      have hzTarget : (0:Plane) ∈ Q₀.target := hQ₀p ▸ Q₀.map_source hpQ
      obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp Q₀.open_target 0 hzTarget
      let σ : ℝ := min δ ρ / 2
      have hσ : 0 < σ := half_pos (lt_min hδ hρ)
      have hσδ : σ < δ := (half_lt_self (lt_min hδ hρ)).trans_le (min_le_left _ _)
      have hσcore : σ < ρ := (half_lt_self (lt_min hδ hρ)).trans_le (min_le_right _ _)
      let H : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero σ⁻¹ (inv_ne_zero (ne_of_gt hσ))
      let E := Q₀.transHomeomorph H
      have hvalue (x : S) : E x = σ⁻¹ • Q₀ x := rfl
      have hinv (z : Plane) : H.symm z = σ • z := by change (σ⁻¹)⁻¹ • z = σ • z;rw [inv_inv]
      have hsmall (z : Plane) (hz : z ∈ Metric.closedBall (0:Plane) 1) :
          ‖H.symm z‖ ≤ σ := by
        rw [hinv,norm_smul,Real.norm_eq_abs,abs_of_pos hσ]
        have hz' : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz
        nlinarith
      refine ⟨σ,E,hσ,rfl,?_,?_,hvalue,?_⟩
      · change H (Q₀ p.val) = 0
        rw [hQ₀p]
        simp [H,Homeomorph.smulOfNeZero]
      · intro z hz
        change H.symm z ∈ Q₀.target
        apply hball
        rw [Metric.mem_ball,dist_zero_right]
        exact (hsmall z hz).trans_lt hσδ
      · intro x hx hz
        have he : H.symm (E x) = Q₀ x := H.symm_apply_apply _
        rw [← he]
        exact (hsmall (E x) hz).trans_lt hσcore
    obtain ⟨σ,E,hσ,hEs,hEp,hEBall,hEval,hEsmall⟩ := hscale
    have hEQ : E.source = Q.source := hEs
    have hCore (x : S) (hx : x ∈ E.source)
        (hxs : E x ∈ Metric.closedBall (0:Plane) 1) :
        R.H (Q x) ∈ Metric.closedBall (0:Plane) R.coreRadius := by
      have hh := hρcore (show Q₀ x ∈ Metric.ball (0:Plane) ρ from by
        simpa only [Metric.mem_ball,dist_zero_right] using hEsmall x hx hxs)
      change T.symm (T (R.H (Q x))) ∈ Metric.ball (0:Plane) R.coreRadius at hh
      rw [T.symm_apply_apply] at hh
      exact Metric.ball_subset_closedBall hh
    have hFarClear (x : S) (hx : x ∈ E.source)
        (hxs : E x ∈ Metric.closedBall (0:Plane) 1) : x ∉ Far := by
      intro hfar
      have hxQ : x ∈ Q.source := hEQ ▸ hx
      have hxnotV : Q x ∉ Vstar := by
        rintro ⟨y,hy,he⟩
        exact hy.2 ((Q.injOn hy.1 hxQ he).symm ▸ hfar)
      have hxout : Q x ∉ Metric.ball (0:Plane) R.supportRadius := by
        intro hin
        exact hxnotV (R.support_subset (Metric.ball_subset_closedBall hin))
      have hfix := R.fixes_exterior (Q x) hxout
      have hsmall := hCore x hx hxs
      rw [hfix] at hsmall
      exact hxnotV (R.support_subset
        (Metric.closedBall_subset_closedBall R.core_lt_support.le hsmall))
    let M : Inc × Bool → Interval → Plane := fun j t => E (β j t)
    let w : Inc × Bool → Plane := fun j => σ⁻¹ • T (R.vector j)
    have hM (j : Inc × Bool) : Continuous (M j) := E.continuousOn.comp_continuous
      (β j).continuous (fun t => hEQ.symm ▸ (hβU j t))
    have hMi (j : Inc × Bool) : Function.Injective (M j) := by
      intro t u he
      exact (hβ j).injective (E.injOn (hEQ.symm ▸ (hβU j t))
        (hEQ.symm ▸ (hβU j u)) he)
    have hM0 (j : Inc × Bool) : M j 0 = 0 := by change E (β j 0) = 0;rw [hβ0,hEp]
    have hMval (j : Inc × Bool) (t : Interval) : M j t = σ⁻¹ • T (R.H (γ j t)) :=
      hEval _
    have hwne (j : Inc × Bool) : w j ≠ 0 :=
      smul_ne_zero (inv_ne_zero (ne_of_gt hσ)) (fun h => R.vector_nonzero j (T.injective (h.trans (map_zero T).symm)))
    have hRay (j : Inc × Bool) (t : Interval) (ht : t ≤ R.cut j) :
        M j t ∈ segment ℝ (0:Plane) (w j) := by
      have hh : R.H (γ j t) ∈ segment ℝ (0:Plane) (R.vector j) := by
        simpa only [R.prefix_image,zero_add] using
          (show R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.armPrefix γ j (R.cut j) from
            ⟨γ j t,⟨t,ht,rfl⟩,rfl⟩)
      rw [segment_eq_image'] at hh ⊢
      obtain ⟨q,hq,he⟩ := hh
      refine ⟨q,hq,?_⟩
      rw [hMval,← he]
      simp only [sub_zero,smul_zero,zero_add,map_smul]
      dsimp [w]
      rw [smul_smul,smul_smul,mul_comm]
    have hNormPos (j : Inc × Bool) : 0 < ‖w j‖ := norm_pos_iff.mpr (hwne j)
    let z : Inc × Bool → Interval → ℝ := fun j t => norm (M j t)
    have hz (j : Inc × Bool) : Continuous (z j) := continuous_norm.comp (hM j)
    have hzi (j : Inc × Bool) : Set.InjOn (z j) (Set.Icc (0:Interval) (R.cut j)) := by
      intro t ht u hu he
      have htRay := hRay j t ht.2
      have huRay := hRay j u hu.2
      rw [segment_eq_image'] at htRay huRay
      obtain ⟨q,hq,hqt⟩ := htRay
      obtain ⟨d,hd,hdu⟩ := huRay
      simp only [sub_zero,smul_zero,zero_add] at hqt hdu
      have hqd : q = d := by
        change norm (M j t) = norm (M j u) at he
        rw [← hqt,← hdu] at he
        have hsq : norm (q • w j) = q * norm (w j) := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.1]
        have hsd : norm (d • w j) = d * norm (w j) := by
          rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd.1]
        rw [hsq,hsd] at he
        exact mul_right_cancel₀ (ne_of_gt (hNormPos j)) he
      exact hMi j (hqt.symm.trans ((hqd ▸ hdu)))
    have hz0 (j : Inc × Bool) : z j 0 = 0 := by change norm (M j 0) = 0;rw [hM0];norm_num [norm]
    have hzcut (j : Inc × Bool) : 1 < z j (R.cut j) := by
      by_contra hn
      have hsq : M j (R.cut j) ∈ Metric.closedBall (0:Plane) 1 :=
        by simpa only [Metric.mem_closedBall,dist_zero_right] using (not_lt.mp hn)
      have hh := hCore (β j (R.cut j)) (hEQ.symm ▸ (hβU j _)) hsq
      have ht : R.H (γ j (R.cut j)) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
        ⟨γ j (R.cut j),⟨R.cut j,(show (R.cut j).val ≤ (R.cut j).val from le_rfl),rfl⟩,rfl⟩
      exact Set.disjoint_left.mp (R.excludes_tails j) ht hh
    have hzmono (j : Inc × Bool) : StrictMonoOn (z j) (Set.Icc (0:Interval) (R.cut j)) :=
      ContinuousOn.strictMonoOn_of_injOn_Icc (show (0:Interval) ≤ R.cut j from bot_le)
        (by rw [hz0];linarith [hzcut j]) (hz j).continuousOn (hzi j)
    have hcutExists (j : Inc × Bool) : ∃ t : Interval,
        0 < t ∧ t < R.cut j ∧ z j t = 1 := by
      obtain ⟨t,ht,he⟩ := intermediate_value_Icc
        (show (0:Interval) ≤ R.cut j from bot_le) (hz j).continuousOn
        (show (1:ℝ) ∈ Set.Icc (z j 0) (z j (R.cut j)) from
          ⟨by rw [hz0];norm_num,(hzcut j).le⟩)
      have ht0 : 0 < t := by
        apply lt_of_le_of_ne ht.1
        intro heq
        rw [← heq,hz0] at he
        norm_num at he
      have htt : t < R.cut j := by
        apply lt_of_le_of_ne ht.2
        intro heq
        rw [heq] at he
        linarith [hzcut j]
      exact ⟨t,ht0,htt,he⟩
    choose cut hcut0 hcutR hcutz using hcutExists
    have hMsquare (j : Inc × Bool) (t : Interval) :
        M j t ∈ Metric.closedBall (0:Plane) 1 ↔ t ≤ cut j := by
      constructor
      · intro hsq
        have htR : t < R.cut j := by
          by_contra hn
          have htail : R.H (γ j t) ∈ R.H '' CurveComplex.FiniteStarGeometry.tail γ j (R.cut j) :=
            ⟨γ j t,⟨t,(show (R.cut j).val ≤ t.val from not_lt.mp hn),rfl⟩,rfl⟩
          exact Set.disjoint_left.mp (R.excludes_tails j) htail
            (hCore _ (hEQ.symm ▸ (hβU j t)) hsq)
        by_contra hn
        have hh := hzmono j ⟨bot_le,(hcutR j).le⟩ ⟨bot_le,htR.le⟩ (not_le.mp hn)
        rw [hcutz] at hh
        exact (not_lt_of_ge (show ‖M j t‖ ≤ 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using hsq)) hh
      · intro ht
        rw [Metric.mem_closedBall,dist_zero_right]
        exact (hzmono j).monotoneOn ⟨bot_le,ht.trans (hcutR j).le⟩
          ⟨bot_le,(hcutR j).le⟩ ht |>.trans_eq (hcutz j)
    have hMopen (j : Inc × Bool) (t : Interval) (ht : t < cut j) :
        M j t ∈ Metric.ball (0:Plane) 1 := by
      rw [Metric.mem_ball,dist_zero_right]
      exact (hzmono j ⟨bot_le,ht.le.trans (hcutR j).le⟩
        ⟨bot_le,(hcutR j).le⟩ ht).trans_eq (hcutz j)
    have hEinterior : {x : S | x ∈ E.source ∧ E x ∈ Metric.closedBall (0:Plane) 1} ⊆ interior F := by
      intro x hx
      exact hNF ((hQs ▸ (hEQ ▸ hx.1)).2)
    have hBranchImage (j : Inc × Bool) : M j '' Set.Icc (0:Interval) (cut j) =
        segment ℝ (0:Plane) (M j (cut j)) := by
      have hformula (t : Interval) (ht : t ≤ cut j) :
          M j t = ((z j t) / norm (w j)) • w j := by
        have hh := hRay j t (ht.trans (hcutR j).le)
        rw [segment_eq_image'] at hh
        obtain ⟨q,hq,he⟩ := hh
        simp only [sub_zero,zero_add] at he
        have hzq : z j t = q * norm (w j) := by
          change norm (M j t) = _
          rw [← he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hq.1]
        rw [hzq,mul_div_cancel_right₀ _ (ne_of_gt (hNormPos j))]
        exact he.symm
      have hcutval : M j (cut j) = (norm (w j))⁻¹ • w j := by
        rw [hformula _ le_rfl,hcutz,one_div]
      apply Set.Subset.antisymm
      · rintro q ⟨t,ht,rfl⟩
        rw [segment_eq_image']
        refine ⟨z j t,⟨norm_nonneg _,?_⟩,?_⟩
        · exact (show ‖M j t‖ ≤ 1 by simpa only [Metric.mem_closedBall,dist_zero_right] using ((hMsquare j t).mpr ht.2))
        · simp only [sub_zero,zero_add]
          rw [hcutval,hformula t ht.2,smul_smul,div_eq_mul_inv]
      · intro q hq
        rw [segment_eq_image'] at hq
        obtain ⟨d,hd,he⟩ := hq
        simp only [sub_zero,zero_add] at he
        obtain ⟨t,ht,hzt⟩ := intermediate_value_Icc
          (show (0:Interval) ≤ cut j from bot_le) (hz j).continuousOn
          (show d ∈ Set.Icc (z j 0) (z j (cut j)) by rw [hz0,hcutz];exact hd)
        refine ⟨t,ht,?_⟩
        rw [hformula t ht.2,hzt,← he,hcutval,div_eq_mul_inv]
        exact (smul_smul d (norm (w j))⁻¹ (w j)).symm
    let edge : Inc × Bool → Interval := fun j => param j (cut j)
    have hedge (j : Inc) :
        0 < edge (j,false) ∧ edge (j,false) < center j ∧
        center j < edge (j,true) ∧ edge (j,true) < 1 := by
      have hc0f : 0 < (cut (j,false)).val := hcut0 _
      have hc1f : (cut (j,false)).val < 1 := by
        have hh : (cut (j,false)).val < (R.cut (j,false)).val := hcutR _
        exact hh.trans_le (R.cut _).property.2
      have hc0t : 0 < (cut (j,true)).val := hcut0 _
      have hc1t : (cut (j,true)).val < 1 := by
        have hh : (cut (j,true)).val < (R.cut (j,true)).val := hcutR _
        exact hh.trans_le (R.cut _).property.2
      have hl0 : 0 < (left j).val := hleft0 j
      have hl : (left j).val < (center j).val := hleft j
      have hr : (center j).val < (right j).val := hright j
      have hr1 : (right j).val < 1 := hright1 j
      change 0 < (center j).val + ((left j).val-(center j).val)*(cut (j,false)).val ∧
        (center j).val + ((left j).val-(center j).val)*(cut (j,false)).val < (center j).val ∧
        (center j).val < (center j).val + ((right j).val-(center j).val)*(cut (j,true)).val ∧
        (center j).val + ((right j).val-(center j).val)*(cut (j,true)).val < 1
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor <;> nlinarith
    have hparamSub (j : Inc × Bool) : param j '' Set.Icc (0:Interval) (cut j) =
        Set.uIcc (center j.1) (edge j) := by
      rcases j with ⟨j,k⟩
      cases k
      · have hant : AntitoneOn (param (j,false)) (Set.Icc (0:Interval) (cut (j,false))) := by
          intro t ht u hu htu
          change (center j).val + ((left j).val-(center j).val)*u.val ≤
            (center j).val + ((left j).val-(center j).val)*t.val
          have htu : t.val ≤ u.val := htu
          have hl : (left j).val < (center j).val := hleft j
          nlinarith
        rw [ContinuousOn.image_Icc_of_antitoneOn (show (0:Interval) ≤ cut (j,false) from bot_le)
          (param (j,false)).continuous.continuousOn hant,hparam0]
        exact (Set.uIcc_of_ge (hedge j).2.1.le).symm
      · have hmono : MonotoneOn (param (j,true)) (Set.Icc (0:Interval) (cut (j,true))) := by
          intro t ht u hu htu
          change (center j).val + ((right j).val-(center j).val)*t.val ≤
            (center j).val + ((right j).val-(center j).val)*u.val
          have htu : t.val ≤ u.val := htu
          have hr : (center j).val < (right j).val := hright j
          nlinarith
        rw [ContinuousOn.image_Icc_of_monotoneOn (show (0:Interval) ≤ cut (j,true) from bot_le)
          (param (j,true)).continuous.continuousOn hmono,hparam0]
        exact (Set.uIcc_of_le (hedge j).2.2.1.le).symm
    have htrace (j : Inc) : {x : S | x ∈ E.source ∧ E x ∈ Metric.closedBall (0:Plane) 1} ∩
        Set.range (f j) = f j '' Set.Icc (edge (j,false)) (edge (j,true)) := by
      have hsplit : Set.Icc (edge (j,false)) (edge (j,true)) =
          Set.uIcc (center j) (edge (j,false)) ∪ Set.uIcc (center j) (edge (j,true)) := by
        rw [Set.uIcc_of_ge (hedge j).2.1.le,Set.uIcc_of_le (hedge j).2.2.1.le]
        ext t
        simp only [Set.mem_Icc,Set.mem_union]
        constructor
        · intro ht
          rcases le_total t (center j) with hc | hc
          · exact Or.inl ⟨ht.1,hc⟩
          · exact Or.inr ⟨hc,ht.2⟩
        · rintro (ht | ht)
          · exact ⟨ht.1,ht.2.trans (hedge j).2.2.1.le⟩
          · exact ⟨(hedge j).2.1.le.trans ht.1,ht.2⟩
      rw [hsplit,Set.image_union,← hparamSub (j,false),← hparamSub (j,true),
        Set.image_image,Set.image_image]
      change _ = β (j,false) '' Set.Icc (0:Interval) (cut (j,false)) ∪
        β (j,true) '' Set.Icc (0:Interval) (cut (j,true))
      apply Set.Subset.antisymm
      · intro x hx
        have hg := (hwholeCover j hx.2).resolve_left (hFarClear x hx.1.1 hx.1.2)
        rcases hg with ⟨t,rfl⟩ | ⟨t,rfl⟩
        · left;exact ⟨t,⟨bot_le,(hMsquare (j,false) t).mp hx.1.2⟩,rfl⟩
        · right;exact ⟨t,⟨bot_le,(hMsquare (j,true) t).mp hx.1.2⟩,rfl⟩
      · intro x hx
        rcases hx with ⟨t,ht,rfl⟩ | ⟨t,ht,rfl⟩
        · exact ⟨⟨hEQ.symm ▸ (hβU (j,false) t),(hMsquare _ _).mpr ht.2⟩,
            ⟨param (j,false) t,rfl⟩⟩
        · exact ⟨⟨hEQ.symm ▸ (hβU (j,true) t),(hMsquare _ _).mpr ht.2⟩,
            ⟨param (j,true) t,rfl⟩⟩
    have htraceImage (j : Inc) : (fun t : Interval => E (f j t)) ''
        Set.Icc (edge (j,false)) (edge (j,true)) =
        segment ℝ (0:Plane) (M (j,false) (cut (j,false))) ∪
        segment ℝ (0:Plane) (M (j,true) (cut (j,true))) := by
      have hh := congrArg (fun X : Set S => E '' X) (htrace j)
      have hsplit : Set.Icc (edge (j,false)) (edge (j,true)) =
          Set.uIcc (center j) (edge (j,false)) ∪ Set.uIcc (center j) (edge (j,true)) := by
        rw [Set.uIcc_of_ge (hedge j).2.1.le,Set.uIcc_of_le (hedge j).2.2.1.le]
        ext t
        simp only [Set.mem_Icc,Set.mem_union]
        constructor
        · intro ht
          rcases le_total t (center j) with hc | hc
          · exact Or.inl ⟨ht.1,hc⟩
          · exact Or.inr ⟨hc,ht.2⟩
        · rintro (ht | ht)
          · exact ⟨ht.1,ht.2.trans (hedge j).2.2.1.le⟩
          · exact ⟨(hedge j).2.1.le.trans ht.1,ht.2⟩
      rw [hsplit,Set.image_union,← hparamSub (j,false),← hparamSub (j,true),
        Set.image_image,Set.image_image]
      change M (j,false) '' Set.Icc (0:Interval) (cut (j,false)) ∪
        M (j,true) '' Set.Icc (0:Interval) (cut (j,true)) = _
      rw [hBranchImage,hBranchImage]
    have hSubtypeTrace (j : Inc) :
        chartPull F E (Metric.closedBall (0:Plane) 1) ∩ range (a j.val) =
        a j.val '' Icc (edge (j,false)) (edge (j,true)) := by
      ext y
      constructor
      · intro hy
        have hval : y.val ∈ {x : S | x ∈ E.source ∧ E x ∈ Metric.closedBall (0:Plane) 1} ∩
            range (f j) := by
          refine ⟨hy.1,?_⟩
          obtain ⟨t,rfl⟩ := hy.2
          exact ⟨t,rfl⟩
        obtain ⟨t,ht,he⟩ := htrace j ▸ hval
        exact ⟨t,ht,Subtype.ext he⟩
      · rintro ⟨t,ht,rfl⟩
        have hh := (htrace j).symm ▸ (show f j t ∈ f j ''
          Icc (edge (j,false)) (edge (j,true)) from ⟨t,ht,rfl⟩)
        exact ⟨hh.1,mem_range_self _⟩
    have hSphere (j : Inc × Bool) : M j (cut j) ∈ Metric.sphere (0:Plane) 1 := by
      simpa only [Metric.mem_sphere,dist_zero_right] using hcutz j
    have hInside (j : Inc) : ∀ t ∈ Ioo (edge (j,false)) (edge (j,true)),
        E (a j.val t).val ∈ Metric.ball (0:Plane) 1 := by
      intro t ht
      by_cases htc : t ≤ center j
      · have hh : t ∈ param (j,false) '' Icc (0:Interval) (cut (j,false)) := by
          rw [hparamSub,Set.uIcc_of_ge (hedge j).2.1.le]
          exact ⟨ht.1.le,htc⟩
        obtain ⟨u,hu,he⟩ := hh
        have huc : u < cut (j,false) := by
          apply lt_of_le_of_ne hu.2
          intro heq
          have htEq : t = edge (j,false) := he.symm.trans (congrArg (param (j,false)) heq)
          exact ht.1.ne htEq.symm
        have hh := hMopen (j,false) u huc
        change E (a j.val (param (j,false) u)).val ∈ _ at hh
        rwa [he] at hh
      · have hh : t ∈ param (j,true) '' Icc (0:Interval) (cut (j,true)) := by
          rw [hparamSub,Set.uIcc_of_le (hedge j).2.2.1.le]
          exact ⟨(lt_of_not_ge htc).le,ht.2.le⟩
        obtain ⟨u,hu,he⟩ := hh
        have huc : u < cut (j,true) := by
          apply lt_of_le_of_ne hu.2
          intro heq
          have htEq : t = edge (j,true) := he.symm.trans (congrArg (param (j,true)) heq)
          exact ht.2.ne htEq
        have hh := hMopen (j,true) u huc
        change E (a j.val (param (j,true) u)).val ∈ _ at hh
        rwa [he] at hh
    have hOpenTrace (j : Inc) :
        chartPull F E (Metric.ball (0:Plane) 1) ∩ range (a j.val) =
        a j.val '' Ioo (edge (j,false)) (edge (j,true)) := by
      apply Set.Subset.antisymm
      · intro y hy
        have hyD : y ∈ chartPull F E (Metric.closedBall (0:Plane) 1) ∩ range (a j.val) :=
          ⟨⟨hy.1.1,Metric.ball_subset_closedBall hy.1.2⟩,hy.2⟩
        obtain ⟨t,ht,rfl⟩ := (hSubtypeTrace j) ▸ hyD
        have hleftNe : t ≠ edge (j,false) := by
          intro he
          have hh := hy.1.2
          rw [he] at hh
          exact (Metric.sphere_disjoint_ball : Disjoint (Metric.sphere (0:Plane) 1)
            (Metric.ball (0:Plane) 1)) |>.le_bot ⟨hSphere (j,false),hh⟩
        have hrightNe : t ≠ edge (j,true) := by
          intro he
          have hh := hy.1.2
          rw [he] at hh
          exact (Metric.sphere_disjoint_ball : Disjoint (Metric.sphere (0:Plane) 1)
            (Metric.ball (0:Plane) 1)) |>.le_bot ⟨hSphere (j,true),hh⟩
        exact ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm hleftNe),lt_of_le_of_ne ht.2 hrightNe⟩,rfl⟩
      · rintro y ⟨t,ht,rfl⟩
        have hh := (hSubtypeTrace j).symm ▸ (show a j.val t ∈ a j.val ''
          Icc (edge (j,false)) (edge (j,true)) from ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩)
        exact ⟨⟨hh.1.1,hInside j t ht⟩,mem_range_self _⟩
    have hAway (j : Option ι) (hj : p ∉ range (a j)) :
        Disjoint (chartPull F E (Metric.closedBall (0:Plane) 1)) (range (a j)) := by
      apply disjoint_left.mpr
      rintro y hy ⟨t,ht⟩
      apply hFarClear y.val hy.1 hy.2
      right
      exact mem_iUnion.mpr ⟨⟨j,hj⟩,t,congrArg Subtype.val ht⟩
    have hPortInjective : Function.Injective (fun j : Inc × Bool => M j (cut j)) := by
      intro i j he
      by_contra hij
      have hβeq : β i (cut i) = β j (cut j) := E.injOn
        (hEQ.symm ▸ (hβU i (cut i))) (hEQ.symm ▸ (hβU j (cut j))) he
      have hp : β i (cut i) = p.val := Set.mem_singleton_iff.mp
        (hβmeet i j hij ▸ (show β i (cut i) ∈ range (β i) ∩ range (β j) from
          ⟨mem_range_self _,⟨cut j,hβeq.symm⟩⟩))
      have hz : M i (cut i) = 0 := by change E (β i (cut i)) = 0;rw [hp,hEp]
      have hn := hcutz i
      change ‖M i (cut i)‖ = 1 at hn
      rw [hz,norm_zero] at hn
      norm_num at hn
    have haxisPort (k : Bool) : M (seed,k) (cut (seed,k)) 1 = 0 := by
      have hh := hRay (seed,k) (cut (seed,k)) (hcutR _).le
      rw [segment_eq_image'] at hh
      obtain ⟨q,hq,he⟩ := hh
      simp only [sub_zero,smul_zero,zero_add] at he
      rw [← he]
      change q * (σ⁻¹ * T (R.vector (seed,k)) 1) = 0
      cases k
      · rw [hTv];simp [Plane.mk]
      · rw [hop,map_neg,hTv];simp [Plane.mk]
    refine ⟨{ chart := E
              source_closure := ?_
              contact_in_source := hEQ.symm ▸ hpQ
              contact_zero := hEp
              disk_in_target := hEBall
              left := fun j => edge (j,false)
              right := fun j => edge (j,true)
              center := center
              cuts := hedge
              at_center := hcenter
              whole_closed := hSubtypeTrace
              whole_open := hOpenTrace
              radial_trace := ?_
              nonincident_clear := hAway
              ports_on_sphere := ?_
              ports_injective := ?_ },?_,?_,?_⟩
    · apply (closure_mono (show E.source ⊆ N from by
        intro y hy
        exact (hQs ▸ (hEQ ▸ hy)).2)).trans hNclosure
    · intro j
      change (fun t : Interval => E (f j t)) '' Icc (edge (j,false)) (edge (j,true)) =
        segment ℝ (M (j,false) (cut (j,false))) 0 ∪ segment ℝ 0 (M (j,true) (cut (j,true)))
      rw [segment_symm ℝ (M (j,false) (cut (j,false))) 0]
      exact htraceImage j
    · rintro ⟨j,k⟩
      cases k <;> exact hSphere _
    · change Function.Injective (fun j : Inc × Bool =>
        E ((a j.1.val) (if j.2 then edge (j.1,true) else edge (j.1,false))).val)
      intro z q he
      apply hPortInjective
      rcases z with ⟨j,k⟩
      rcases q with ⟨l,m⟩
      cases k <;> cases m <;> exact he
    · intro y hy
      exact (hQs ▸ (hEQ ▸ hy)).2
    · exact haxisPort false
    · exact haxisPort true
  have hballSquare : ∃ H : Plane ≃ₜ Plane, H 0 = 0 ∧
      H '' Metric.closedBall (0:Plane) 1 = Plane.closedSquare 0 1 ∧
      H '' Metric.ball (0:Plane) 1 = Plane.openSquare 0 1 ∧
      (∀ z, (0 < H z 1 ↔ 0 < z 1) ∧ (H z 1 = 0 ↔ z 1 = 0)) ∧
      (∀ z, H '' segment ℝ (0:Plane) z = segment ℝ (0:Plane) (H z)) := by
    let s := Metric.closedBall (0:Plane) 1
    let t := Plane.closedSquare 0 1
    have hsc : Convex ℝ s := convex_closedBall 0 1
    have htc : Convex ℝ t := Plane.convex_closedSquare 0 1
    have hs0 : s ∈ nhds (0:Plane) := Metric.closedBall_mem_nhds 0 (by norm_num)
    have ht0 : t ∈ nhds (0:Plane) := by
      rw [← mem_interior_iff_mem_nhds]
      change (0:Plane) ∈ interior (Plane.closedSquare 0 1)
      rw [Plane.interior_closedSquare]
      simp [mem_openSquare_zero_one,Plane.supNorm]
    have hsb : Bornology.IsVonNBounded ℝ s := NormedSpace.isVonNBounded_of_isBounded ℝ Metric.isBounded_closedBall
    have htb : Bornology.IsVonNBounded ℝ t :=
      NormedSpace.isVonNBounded_of_isBounded ℝ (Plane.isBounded_closedSquare 0 1)
    let H := gaugeRescaleHomeomorph s t hsc hs0 hsb htc ht0 htb
    have hHz : H 0 = 0 := gaugeRescale_zero _ _
    have hHclosed : H '' s = t := by
      have hh := image_gaugeRescaleHomeomorph_closure hsc hs0 hsb htc ht0 htb
      rw [show closure s = s from Metric.isClosed_closedBall.closure_eq,
        show closure t = t from (Plane.isClosed_closedSquare 0 1).closure_eq] at hh
      exact hh
    have hHopen : H '' Metric.ball (0:Plane) 1 = Plane.openSquare 0 1 := by
      have hh := image_gaugeRescaleHomeomorph_interior hsc hs0 hsb htc ht0 htb
      simpa only [s,t,interior_closedBall _ (by norm_num : (1:ℝ) ≠ 0),Plane.interior_closedSquare] using hh
    refine ⟨H,hHz,hHclosed,hHopen,?_,?_⟩
    · intro z
      by_cases hz : z = 0
      · simp [hz,hHz]
      have hsp : 0 < gauge s z := (gauge_pos (absorbent_nhds_zero hs0) hsb).mpr hz
      have htp : 0 < gauge t z := (gauge_pos (absorbent_nhds_zero ht0) htb).mpr hz
      have hratio : 0 < gauge s z / gauge t z := div_pos hsp htp
      change (0 < (gauge s z / gauge t z) * z 1 ↔ 0 < z 1) ∧
        ((gauge s z / gauge t z) * z 1 = 0 ↔ z 1 = 0)
      rw [mul_pos_iff_of_pos_left hratio,mul_eq_zero,or_iff_right hratio.ne']
      exact ⟨Iff.rfl,Iff.rfl⟩
    · intro z
      rw [segment_eq_image',segment_eq_image',Set.image_image]
      apply Set.image_congr
      intro q hq
      simp only [Function.comp_apply,sub_zero,zero_add]
      exact gaugeRescale_smul s t hq.1 z
  have haxisComplete (p : ↥events) (i : Option ι) (hip : p.val ∈ range (a i)) :
      ∃ A : IncidentFanWindow F a V p.val,
        chartPull F A.chart (Metric.closedBall (0:Plane) 1) ⊆
          chartPull F (window p).chart (Metric.ball (0:Plane) 1) ∧
        incidentPorts a p.val A.chart A.left A.right (⟨i,hip⟩,false) 1 = 0 ∧
        incidentPorts a p.val A.chart A.left A.right (⟨i,hip⟩,true) 1 = 0 ∧
        ∀ j : incidentIndex a p.val, j.val ≠ i →
          ((0 < incidentPorts a p.val A.chart A.left A.right (j,false) 1 ∧
            incidentPorts a p.val A.chart A.left A.right (j,true) 1 < 0) ∨
           (incidentPorts a p.val A.chart A.left A.right (j,false) 1 < 0 ∧
            0 < incidentPorts a p.val A.chart A.left A.right (j,true) 1)) := by
    let E := (window p).chart
    let O : Set S := E.source ∩ E ⁻¹' Metric.ball (0:Plane) 1
    have hO : IsOpen O := E.isOpen_inter_preimage Metric.isOpen_ball
    have hpO : p.val.val ∈ O := by
      refine ⟨(window p).contact_in_source,?_⟩
      change E p.val.val ∈ Metric.ball (0:Plane) 1
      rw [(window p).contact_zero]
      exact Metric.mem_ball_self (by norm_num)
    obtain ⟨K,hpK,hK,hKO⟩ := exists_mem_nhds_isClosed_subset (hO.mem_nhds hpO)
    obtain ⟨M,hMK,hM,hpM⟩ := mem_nhds_iff.mp hpK
    have hMO : closure M ⊆ O := (closure_minimal hMK hK).trans hKO
    have hMclosure : closure M ⊆ Subtype.val '' V ∩ interior F := by
      intro y hy
      exact (window p).source_closure (subset_closure (hMO hy).1)
    have hMOnly : ∀ j k, j ≠ k → ∀ y ∈ range (a j) ∩ range (a k),
        y.val ∈ M → y = p.val := by
      intro j k hjk y hy hyM
      exact hOnly p j k hjk y hy (hwindowN p (hMO (subset_closure hyM)).1)
    obtain ⟨A,hAM,hleftAxis,hrightAxis⟩ :=
      haxisProducer p M hM hpM hMclosure hMOnly ⟨i,hip⟩
    refine ⟨A,?_,hleftAxis,hrightAxis,?_⟩
    · intro y hy
      exact hMO (subset_closure (hAM hy.1))
    · intro j hji
      let port := incidentPorts a p.val A.chart A.left A.right
      have hselNe : port (⟨i,hip⟩,false) ≠ port (⟨i,hip⟩,true) := fun h =>
        Bool.false_ne_true (congrArg Prod.snd (A.ports_injective h))
      have hcover (z : Plane) (hz : z ∈ Metric.sphere (0:Plane) 1) (ha : z 1 = 0) :
          z = port (⟨i,hip⟩,false) ∨ z = port (⟨i,hip⟩,true) := by
        have hl := hunitAxis _ (A.ports_on_sphere (⟨i,hip⟩,false)) hleftAxis
        have hr := hunitAxis _ (A.ports_on_sphere (⟨i,hip⟩,true)) hrightAxis
        have hh := hunitAxis z hz ha
        rcases hl with hl | hl <;> rcases hr with hr | hr
        · exact (hselNe (hl.trans hr.symm)).elim
        · rcases hh with hh | hh
          · exact Or.inl (hh.trans hl.symm)
          · exact Or.inr (hh.trans hr.symm)
        · rcases hh with hh | hh
          · exact Or.inr (hh.trans hr.symm)
          · exact Or.inl (hh.trans hl.symm)
        · exact (hselNe (hl.trans hr.symm)).elim
      have hportNe (k : Bool) : port (j,k) 1 ≠ 0 := by
        intro hz
        rcases hcover _ (A.ports_on_sphere (j,k)) hz with he | he
        · exact hji (congrArg (fun z : incidentIndex a p.val × Bool => z.1.val)
            (A.ports_injective he))
        · exact hji (congrArg (fun z : incidentIndex a p.val × Bool => z.1.val)
            (A.ports_injective he))
      have htraceSource (t : Interval) (ht : t ∈ Icc (A.left j) (A.right j)) :
          ((a j.val) t).val ∈ A.chart.source := by
        have hm : (a j.val) t ∈ (a j.val) '' Icc (A.left j) (A.right j) := ⟨t,ht,rfl⟩
        rw [← A.whole_closed j] at hm
        exact hm.1.1
      have htraceNe (t : Interval) (ht : t ∈ Icc (A.left j) (A.right j))
          (hc : t ≠ A.center j) : A.chart ((a j.val) t).val 1 ≠ 0 := by
        intro hz
        have hm : A.chart ((a j.val) t).val ∈
            (fun t => A.chart ((a j.val) t).val) '' Icc (A.left j) (A.right j) := ⟨t,ht,rfl⟩
        rw [A.radial_trace j,segment_symm ℝ (port (j,false)) 0] at hm
        have hzero : A.chart ((a j.val) t).val = 0 := by
          rcases hm with hm | hm
          · rw [segment_eq_image'] at hm
            obtain ⟨q,hq,he⟩ := hm
            simp only [sub_zero,smul_zero,zero_add] at he
            have he1 := congrArg (fun z : Plane => z 1) he
            change q * port (j,false) 1 = A.chart ((a j.val) t).val 1 at he1
            have hq0 := (mul_eq_zero.mp (he1.trans hz)).resolve_right (hportNe false)
            rw [hq0,zero_smul] at he
            exact he.symm
          · rw [segment_eq_image'] at hm
            obtain ⟨q,hq,he⟩ := hm
            simp only [sub_zero,smul_zero,zero_add] at he
            have he1 := congrArg (fun z : Plane => z 1) he
            change q * port (j,true) 1 = A.chart ((a j.val) t).val 1 at he1
            have hq0 := (mul_eq_zero.mp (he1.trans hz)).resolve_right (hportNe true)
            rw [hq0,zero_smul] at he
            exact he.symm
        have hcenterSource := htraceSource (A.center j) ⟨(A.cuts j).2.1.le,(A.cuts j).2.2.1.le⟩
        have hc0 : A.chart ((a j.val) (A.center j)).val = 0 := by
          rw [A.at_center];exact A.contact_zero
        have heq := A.chart.injOn (htraceSource t ht) hcenterSource (hzero.trans hc0.symm)
        exact hc ((hproper j.val).1.injective (Subtype.ext heq))
      let seed : incidentIndex a p.val := ⟨i,hip⟩
      have hAAxis := hfanAxis a p.val V A seed hleftAxis hrightAxis hcover
      obtain ⟨C,hCross⟩ := hcross i j.val hji.symm (A.center seed) (A.center j)
        ⟨(A.cuts seed).1.trans (A.cuts seed).2.1,
          (A.cuts seed).2.2.1.trans (A.cuts seed).2.2.2⟩
        ⟨(A.cuts j).1.trans (A.cuts j).2.1,
          (A.cuts j).2.2.1.trans (A.cuts j).2.2.2⟩
        ((A.at_center seed).trans (A.at_center j).symm)
      have hCSource : p.val.val ∈ C.chart.source := by
        have hm : (a i) (A.center seed) ∈
            (a i) '' Icc C.aLeft C.aRight :=
          ⟨A.center seed,⟨C.a_cuts.2.1.le,C.a_cuts.2.2.1.le⟩,rfl⟩
        rw [← C.whole_a_trace] at hm
        rw [A.at_center seed] at hm
        exact hm.1.1
      have hCZero : C.chart p.val.val = 0 := by
        have hh : C.chart ((a i) (A.center seed)).val = 0 := C.contact_at_origin
        rw [A.at_center seed] at hh
        exact hh
      have hCAxis (y : ↥F) (hs : y.val ∈ C.chart.source)
          (hb : C.chart y.val ∈ Plane.closedSquare 0 1) :
          y ∈ range (a i) ↔ C.chart y.val 1 = 0 := by
        constructor
        · intro hy
          have hm : y ∈ (a i) '' Icc C.aLeft C.aRight := by
            rw [← C.whole_a_trace];exact ⟨⟨hs,hb⟩,hy⟩
          obtain ⟨t,ht,rfl⟩ := hm
          have hh : C.chart ((a i) t).val ∈
              (fun t => C.chart ((a i) t).val) '' Icc C.aLeft C.aRight := ⟨t,ht,rfl⟩
          rw [C.anchor_diameter] at hh
          exact hh.2
        · intro hz
          have hm : C.chart y.val ∈
              (fun t => C.chart ((a i) t).val) '' Icc C.aLeft C.aRight := by
            rw [C.anchor_diameter];exact ⟨hb,hz⟩
          obtain ⟨t,ht,he⟩ := hm
          have hts : ((a i) t).val ∈ C.chart.source := by
            have hh : (a i) t ∈ (a i) '' Icc C.aLeft C.aRight := ⟨t,ht,rfl⟩
            rw [← C.whole_a_trace] at hh
            exact hh.1.1
          exact ⟨t,Subtype.ext (C.chart.injOn hts hs he)⟩
      let OA : Set S := A.chart.source ∩ A.chart ⁻¹' Metric.ball (0:Plane) 1
      let OC : Set S := C.chart.source ∩ C.chart ⁻¹' Plane.openSquare 0 1
      have hOA : IsOpen OA := A.chart.isOpen_inter_preimage Metric.isOpen_ball
      have hOC : IsOpen OC := C.chart.isOpen_inter_preimage (Plane.isOpen_openSquare _ _)
      let EA := A.chart.restr OA
      let EC := C.chart.restr OC
      have hEAs : EA.source = A.chart.source ∩ OA := A.chart.restr_source' _ hOA
      have hECs : EC.source = C.chart.source ∩ OC := C.chart.restr_source' _ hOC
      have hpEA : p.val.val ∈ EA.source := by
        rw [hEAs];refine ⟨A.contact_in_source,A.contact_in_source,?_⟩
        change A.chart p.val.val ∈ Metric.ball (0:Plane) 1
        rw [A.contact_zero];exact Metric.mem_ball_self (by norm_num)
      have hpEC : p.val.val ∈ EC.source := by
        rw [hECs];refine ⟨hCSource,hCSource,?_⟩
        change C.chart p.val.val ∈ Plane.openSquare 0 1
        rw [hCZero];simp [mem_openSquare_zero_one,Plane.supNorm]
      have hEAZero : EA p.val.val = 0 := A.contact_zero
      have hECZero : EC p.val.val = 0 := hCZero
      let H := EC.symm.trans EA
      have hH0 : (0:Plane) ∈ H.source := by
        rw [OpenPartialHomeomorph.trans_source]
        refine ⟨hECZero ▸ EC.map_source hpEC,?_⟩
        change EC.symm 0 ∈ EA.source
        have hinv : EC.symm 0 = p.val.val := by
          rw [← hECZero]
          exact EC.left_inv hpEC
        rw [hinv]
        exact hpEA
      have hHz : H 0 = 0 := by
        change EA (EC.symm 0) = 0
        have hinv : EC.symm 0 = p.val.val := by
          rw [← hECZero]
          exact EC.left_inv hpEC
        rw [hinv]
        exact hEAZero
      have hHAxis (z : Plane) (hz : z ∈ H.source) : z 1 = 0 ↔ H z 1 = 0 := by
        rw [OpenPartialHomeomorph.trans_source] at hz
        have hyA : EC.symm z ∈ EA.source := hz.2
        rw [hEAs] at hyA
        have hyC : EC.symm z ∈ EC.source := EC.map_target hz.1
        rw [hECs] at hyC
        have hyF : EC.symm z ∈ F := interior_subset
          (A.source_closure (subset_closure hyA.1)).2
        let y : ↥F := ⟨EC.symm z,hyF⟩
        have hC := hCAxis y hyC.1 (Plane.openSquare_subset_closedSquare 0 1 hyC.2.2)
        have hA := hAAxis y hyA.1 (Metric.ball_subset_closedBall hyA.2.2)
        have hECinv : C.chart y.val = z := EC.right_inv hz.1
        rw [hECinv] at hC
        exact hC.symm.trans hA
      obtain ⟨P,δ,hPfst,hPzero,hδ,hδH,ε,hrelative⟩ := hsideBridge H hH0 hHz hHAxis
      let Ω : Set S := EA.source ∩
        (EC.source ∩ EC ⁻¹' (P ⁻¹' Metric.ball (0,0) δ))
      have hΩ : IsOpen Ω := EA.open_source.inter
        (EC.isOpen_inter_preimage (Metric.isOpen_ball.preimage P.continuous))
      have hpΩ : p.val.val ∈ Ω := by
        refine ⟨hpEA,hpEC,?_⟩
        change P (EC p.val.val) ∈ Metric.ball (0,0) δ
        rw [hECZero,hPzero];exact Metric.mem_ball_self hδ
      let b : Interval → S := fun u => ((a j.val) u).val
      have hbCont : Continuous b := continuous_subtype_val.comp (a j.val).continuous
      have hbCenter : b (A.center j) = p.val.val := congrArg Subtype.val (A.at_center j)
      have hbN : b ⁻¹' Ω ∈ nhds (A.center j) :=
        (hΩ.preimage hbCont).mem_nhds (by rw [Set.mem_preimage,hbCenter];exact hpΩ)
      obtain ⟨l₀,r₀,hl₀,hr₀⟩ :=
        (mem_nhds_iff_exists_Ioo_subset' ⟨0,(A.cuts j).1.trans (A.cuts j).2.1⟩
          ⟨1,(A.cuts j).2.2.1.trans (A.cuts j).2.2.2⟩).mp hbN
      obtain ⟨l,hlLower,hlCenter⟩ := exists_between
        (max_lt hl₀.1 (max_lt (A.cuts j).2.1 C.b_cuts.2.1))
      obtain ⟨rr,hrCenter,hrUpper⟩ := exists_between
        (lt_min hl₀.2 (lt_min (A.cuts j).2.2.1 C.b_cuts.2.2.1))
      have hlA : A.left j < l := (le_max_left _ _).trans_lt
        ((le_max_right _ _).trans_lt hlLower)
      have hlC : C.bLeft < l := (le_max_right _ _).trans_lt
        ((le_max_right _ _).trans_lt hlLower)
      have hrA : rr < A.right j := hrUpper.trans_le
        ((min_le_right _ _).trans (min_le_left _ _))
      have hrC : rr < C.bRight := hrUpper.trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
      have hlΩ : b l ∈ Ω := hr₀
        ⟨(le_max_left _ _).trans_lt hlLower,hlCenter.trans hl₀.2⟩
      have hrΩ : b rr ∈ Ω := hr₀
        ⟨hl₀.1.trans hrCenter,hrUpper.trans_le (min_le_left _ _)⟩
      have hClNe : C.chart (b l) 1 ≠ 0 := by
        rcases hCross with hc | hc
        · exact (hc.1 l ⟨hlC,hlCenter⟩).ne'
        · exact (hc.1 l ⟨hlC,hlCenter⟩).ne
      have hCrNe : C.chart (b rr) 1 ≠ 0 := by
        rcases hCross with hc | hc
        · exact (hc.2 rr ⟨hrCenter,hrC⟩).ne
        · exact (hc.2 rr ⟨hrCenter,hrC⟩).ne'
      have hHC (u : Interval) (hu : b u ∈ Ω) : H (EC (b u)) = A.chart (b u) := by
        change EA (EC.symm (EC (b u))) = A.chart (b u)
        rw [EC.left_inv hu.2.1]
        rfl
      have hrelL := hrelative (EC (b l)) hlΩ.2.2 hClNe
      have hrelR := hrelative (EC (b rr)) hrΩ.2.2 hCrNe
      rw [hHC l hlΩ] at hrelL
      rw [hHC rr hrΩ] at hrelR
      have hlabelNe :
          (if 0 < A.chart (b l) 1 then (1:ZMod 2) else 0) ≠
            (if 0 < A.chart (b rr) 1 then (1:ZMod 2) else 0) := by
        rw [hrelL,hrelR]
        intro he
        have heq := add_right_cancel he
        rcases hCross with hc | hc
        · have hlp : 0 < C.chart (b l) 1 := hc.1 l ⟨hlC,hlCenter⟩
          have hrn : C.chart (b rr) 1 < 0 := hc.2 rr ⟨hrCenter,hrC⟩
          change (if 0 < C.chart (b l) 1 then (1:ZMod 2) else 0) =
            (if 0 < C.chart (b rr) 1 then (1:ZMod 2) else 0) at heq
          simp only [if_pos hlp,if_neg (not_lt_of_ge hrn.le)] at heq
          exact one_ne_zero heq
        · have hln : C.chart (b l) 1 < 0 := hc.1 l ⟨hlC,hlCenter⟩
          have hrp : 0 < C.chart (b rr) 1 := hc.2 rr ⟨hrCenter,hrC⟩
          change (if 0 < C.chart (b l) 1 then (1:ZMod 2) else 0) =
            (if 0 < C.chart (b rr) 1 then (1:ZMod 2) else 0) at heq
          simp only [if_neg (not_lt_of_ge hln.le),if_pos hrp] at heq
          exact zero_ne_one heq
      have hsignConstant (l r : Interval) (hlr : l ≤ r)
          (hsub : Icc l r ⊆ Icc (A.left j) (A.right j))
          (hc : A.center j ∉ Icc l r) :
          (0 < A.chart (b l) 1 ↔ 0 < A.chart (b r) 1) := by
        let f : Interval → ℝ := fun u => A.chart (b u) 1
        have hf : ContinuousOn f (Icc l r) := by
          have hcont := A.chart.continuousOn.comp hbCont.continuousOn
            (fun u hu => htraceSource u (hsub hu))
          exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp_continuousOn hcont
        have hne (u : Interval) (hu : u ∈ Icc l r) : f u ≠ 0 :=
          htraceNe u (hsub hu) (fun he => hc (he ▸ hu))
        have hno (u v : Interval) (hu : u ∈ Icc l r) (hv : v ∈ Icc l r)
            (hun : f u < 0) (hvp : 0 < f v) : False := by
          obtain ⟨w,hw,hw0⟩ := isPreconnected_Icc.intermediate_value hu hv hf ⟨hun.le,hvp.le⟩
          exact hne w hw hw0
        constructor <;> intro hp <;> by_contra hn
        · exact hno r l ⟨hlr,le_rfl⟩ ⟨le_rfl,hlr⟩
            (lt_of_le_of_ne (le_of_not_gt hn) (hne r ⟨hlr,le_rfl⟩)) hp
        · exact hno l r ⟨le_rfl,hlr⟩ ⟨hlr,le_rfl⟩
            (lt_of_le_of_ne (le_of_not_gt hn) (hne l ⟨le_rfl,hlr⟩)) hp
      have hLeftSign := hsignConstant (A.left j) l hlA.le
        (fun u hu => ⟨hu.1,hu.2.trans (hlCenter.trans (A.cuts j).2.2.1).le⟩)
        (fun hc => (not_le_of_gt hlCenter) hc.2)
      have hRightSign := hsignConstant rr (A.right j) hrA.le
        (fun u hu => ⟨((A.cuts j).2.1.trans hrCenter).le.trans hu.1,hu.2⟩)
        (fun hc => (not_le_of_gt hrCenter) hc.1)
      have hportLabelNe :
          (if 0 < port (j,false) 1 then (1:ZMod 2) else 0) ≠
            (if 0 < port (j,true) 1 then (1:ZMod 2) else 0) := by
        have heL : (0 < port (j,false) 1) ↔ 0 < A.chart (b l) 1 := hLeftSign
        have heR : (0 < port (j,true) 1) ↔ 0 < A.chart (b rr) 1 := hRightSign.symm
        intro he
        apply hlabelNe
        simpa only [← heL,← heR] using he
      by_cases hlp : 0 < port (j,false) 1
      · left;refine ⟨hlp,?_⟩
        have hrnp : ¬0 < port (j,true) 1 := by
          intro hrp
          exact hportLabelNe (by simp [hlp,hrp])
        exact lt_of_le_of_ne (le_of_not_gt hrnp) (hportNe true)
      · right;refine ⟨lt_of_le_of_ne (le_of_not_gt hlp) (hportNe false),?_⟩
        change 0 < port (j,true) 1
        by_contra hrnp
        exact hportLabelNe (by simp [hlp,hrnp])
  refine ⟨window,?_,?_,?_⟩
  · intro p q hpq
    apply disjoint_left.mpr
    intro y hyp hyq
    have hpsep := (hNclosure p (subset_closure (hwindowN p hyp.1))).2
    have hqsep := (hNclosure q (subset_closure (hwindowN q hyq.1))).2
    have hpSite : p.val.val ∈ Subtype.val '' events := ⟨p.val,p.property,rfl⟩
    have hqSite : q.val.val ∈ Subtype.val '' events := ⟨q.val,q.property,rfl⟩
    have hpqS : p.val.val ≠ q.val.val := fun h => hpq (Subtype.ext (Subtype.ext h))
    exact disjoint_left.mp (hsepDisjoint hpSite hqSite hpqS) hpsep hqsep
  · intro p i hi hip
    exact haxisComplete p i hip
  · intro p i j hij hselected u t hu ht hi hj
    have hip : p.val ∈ range (a i) := ⟨u,hi⟩
    have hjp : p.val ∈ range (a j) := ⟨t,hj⟩
    let ii : incidentIndex a p.val := ⟨i,hip⟩
    let jj : incidentIndex a p.val := ⟨j,hjp⟩
    obtain ⟨A,hAnested,hleftAxis,hrightAxis,hSigns⟩ := haxisComplete p i hip
    have hui : A.center ii = u := (hproper i).1.injective ((A.at_center ii).trans hi.symm)
    have htj : A.center jj = t := (hproper j).1.injective ((A.at_center jj).trans hj.symm)
    let port := incidentPorts a p.val A.chart A.left A.right
    have hPortSigns := hSigns jj hij.symm
    have hportNe (k : Bool) : port (jj,k) 1 ≠ 0 := by
      cases k
      · rcases hPortSigns with hs | hs
        · exact hs.1.ne'
        · exact hs.1.ne
      · rcases hPortSigns with hs | hs
        · exact hs.2.ne
        · exact hs.2.ne'
    have hselNe : port (ii,false) ≠ port (ii,true) := fun h =>
      Bool.false_ne_true (congrArg Prod.snd (A.ports_injective h))
    have hcover (z : Plane) (hz : z ∈ Metric.sphere (0:Plane) 1) (ha : z 1 = 0) :
        z = port (ii,false) ∨ z = port (ii,true) := by
      have hl := hunitAxis _ (A.ports_on_sphere (ii,false)) hleftAxis
      have hr := hunitAxis _ (A.ports_on_sphere (ii,true)) hrightAxis
      have hh := hunitAxis z hz ha
      rcases hl with hl | hl <;> rcases hr with hr | hr
      · exact (hselNe (hl.trans hr.symm)).elim
      · rcases hh with hh | hh
        · exact Or.inl (hh.trans hl.symm)
        · exact Or.inr (hh.trans hr.symm)
      · rcases hh with hh | hh
        · exact Or.inr (hh.trans hr.symm)
        · exact Or.inl (hh.trans hl.symm)
      · exact (hselNe (hl.trans hr.symm)).elim
    have hAAxis := hfanAxis a p.val V A ii hleftAxis hrightAxis hcover
    obtain ⟨H,hHz,hHclosed,hHopen,hHsign,hHsegment⟩ := hballSquare
    have hHclosedIff (z : Plane) : H z ∈ Plane.closedSquare 0 1 ↔
        z ∈ Metric.closedBall (0:Plane) 1 := by
      rw [← hHclosed]
      exact H.injective.mem_set_image
    have hHopenIff (z : Plane) : H z ∈ Plane.openSquare 0 1 ↔
        z ∈ Metric.ball (0:Plane) 1 := by
      rw [← hHopen]
      exact H.injective.mem_set_image
    have hHneg (z : Plane) : H z 1 < 0 ↔ z 1 < 0 := by
      have hp := (hHsign z).1
      have h0 := (hHsign z).2
      constructor
      · intro hn
        have hzp : ¬0 < z 1 := fun hz => (not_lt_of_ge hn.le) (hp.mpr hz)
        have hz0 : z 1 ≠ 0 := fun hz => hn.ne (h0.mpr hz)
        exact lt_of_le_of_ne (le_of_not_gt hzp) hz0
      · intro hn
        have hzp : ¬0 < H z 1 := fun hz => (not_lt_of_ge hn.le) (hp.mp hz)
        have hz0 : H z 1 ≠ 0 := fun hz => hn.ne (h0.mp hz)
        exact lt_of_le_of_ne (le_of_not_gt hzp) hz0
    let E := A.chart.transHomeomorph H
    have hEs : E.source = A.chart.source := rfl
    have hEval (y : S) : E y = H (A.chart y) := rfl
    have hPull : {y : ↥F | y.val ∈ E.source ∧ E y.val ∈ Plane.closedSquare 0 1} =
        chartPull F A.chart (Metric.closedBall (0:Plane) 1) := by
      ext y
      change (y.val ∈ A.chart.source ∧ H (A.chart y.val) ∈ Plane.closedSquare 0 1) ↔ _
      rw [hHclosedIff]
      rfl
    have hSquare : Plane.closedSquare 0 1 ⊆ E.target := by
      intro z hz
      obtain ⟨w,hw,he⟩ := (hHclosed.symm ▸ hz)
      change H.symm z ∈ A.chart.target
      rw [← he,H.symm_apply_apply]
      exact A.disk_in_target hw
    have htraceSourceI (s : Interval) (hs : s ∈ Icc (A.left ii) (A.right ii)) :
        ((a i) s).val ∈ A.chart.source := by
      have hm : (a i) s ∈ (a i) '' Icc (A.left ii) (A.right ii) := ⟨s,hs,rfl⟩
      rw [← A.whole_closed ii] at hm
      exact hm.1.1
    have htraceBallI (s : Interval) (hs : s ∈ Icc (A.left ii) (A.right ii)) :
        A.chart ((a i) s).val ∈ Metric.closedBall (0:Plane) 1 := by
      have hm : (a i) s ∈ (a i) '' Icc (A.left ii) (A.right ii) := ⟨s,hs,rfl⟩
      rw [← A.whole_closed ii] at hm
      exact hm.1.2
    have hAnchor : (fun s : Interval => E ((a i) s).val) '' Icc (A.left ii) (A.right ii) =
        {z : Plane | z ∈ Plane.closedSquare 0 1 ∧ z 1 = 0} := by
      apply Subset.antisymm
      · rintro z ⟨s,hs,rfl⟩
        refine ⟨(hHclosedIff _).mpr (htraceBallI s hs),?_⟩
        apply (hHsign _).2.mpr
        exact (hAAxis _ (htraceSourceI s hs) (htraceBallI s hs)).mp (mem_range_self _)
      · intro z hz
        obtain ⟨w,hw,he⟩ := hHclosed.symm ▸ hz.1
        have hw0 : w 1 = 0 := (hHsign w).2.mp (he.symm ▸ hz.2)
        have hwT : w ∈ A.chart.target := A.disk_in_target hw
        let y : ↥F := ⟨A.chart.symm w,interior_subset
          (A.source_closure (subset_closure (A.chart.map_target hwT))).2⟩
        have hys : y.val ∈ A.chart.source := A.chart.map_target hwT
        have hyv : A.chart y.val = w := A.chart.right_inv hwT
        have hyball : A.chart y.val ∈ Metric.closedBall (0:Plane) 1 := hyv.symm ▸ hw
        have hyr : y ∈ range (a i) := (hAAxis y hys hyball).mpr (hyv.symm ▸ hw0)
        have hm : y ∈ (a i) '' Icc (A.left ii) (A.right ii) := by
          rw [← A.whole_closed ii];exact ⟨⟨hys,hyball⟩,hyr⟩
        obtain ⟨s,hs,hes⟩ := hm
        refine ⟨s,hs,?_⟩
        change H (A.chart ((a i) s).val) = z
        rw [hes,hyv,he]
    let b : Interval → S := fun s => ((a j) s).val
    have hbCont : Continuous b := continuous_subtype_val.comp (a j).continuous
    have htraceSource (t : Interval) (ht : t ∈ Icc (A.left jj) (A.right jj)) :
        ((a j) t).val ∈ A.chart.source := by
      have hm : (a j) t ∈ (a j) '' Icc (A.left jj) (A.right jj) := ⟨t,ht,rfl⟩
      rw [← A.whole_closed jj] at hm
      exact hm.1.1
    have htraceNe (t : Interval) (ht : t ∈ Icc (A.left jj) (A.right jj))
        (hc : t ≠ A.center jj) : A.chart ((a j) t).val 1 ≠ 0 := by
      intro hz
      have hm : A.chart ((a j) t).val ∈
          (fun t => A.chart ((a j) t).val) '' Icc (A.left jj) (A.right jj) := ⟨t,ht,rfl⟩
      rw [A.radial_trace jj,segment_symm ℝ (port (jj,false)) 0] at hm
      have hzero : A.chart ((a j) t).val = 0 := by
        rcases hm with hm | hm
        · rw [segment_eq_image'] at hm
          obtain ⟨q,hq,he⟩ := hm
          simp only [sub_zero,smul_zero,zero_add] at he
          have he1 := congrArg (fun z : Plane => z 1) he
          change q * port (jj,false) 1 = A.chart ((a j) t).val 1 at he1
          have hq0 := (mul_eq_zero.mp (he1.trans hz)).resolve_right (hportNe false)
          rw [hq0,zero_smul] at he
          exact he.symm
        · rw [segment_eq_image'] at hm
          obtain ⟨q,hq,he⟩ := hm
          simp only [sub_zero,smul_zero,zero_add] at he
          have he1 := congrArg (fun z : Plane => z 1) he
          change q * port (jj,true) 1 = A.chart ((a j) t).val 1 at he1
          have hq0 := (mul_eq_zero.mp (he1.trans hz)).resolve_right (hportNe true)
          rw [hq0,zero_smul] at he
          exact he.symm
      have hcenterSource := htraceSource (A.center jj) ⟨(A.cuts jj).2.1.le,(A.cuts jj).2.2.1.le⟩
      have hc0 : A.chart ((a j) (A.center jj)).val = 0 := by
        rw [show (a j) (A.center jj) = p.val from A.at_center jj];exact A.contact_zero
      have heq := A.chart.injOn (htraceSource t ht) hcenterSource (hzero.trans hc0.symm)
      exact hc ((hproper j).1.injective (Subtype.ext heq))
    have hsignConstant (l r : Interval) (hlr : l ≤ r)
        (hsub : Icc l r ⊆ Icc (A.left jj) (A.right jj))
        (hc : A.center jj ∉ Icc l r) :
        (0 < A.chart (b l) 1 ↔ 0 < A.chart (b r) 1) := by
      let f : Interval → ℝ := fun u => A.chart (b u) 1
      have hf : ContinuousOn f (Icc l r) := by
        have hcont := A.chart.continuousOn.comp hbCont.continuousOn
          (fun u hu => htraceSource u (hsub hu))
        exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp_continuousOn hcont
      have hne (u : Interval) (hu : u ∈ Icc l r) : f u ≠ 0 :=
        htraceNe u (hsub hu) (fun he => hc (he ▸ hu))
      have hno (u v : Interval) (hu : u ∈ Icc l r) (hv : v ∈ Icc l r)
          (hun : f u < 0) (hvp : 0 < f v) : False := by
        obtain ⟨w,hw,hw0⟩ := isPreconnected_Icc.intermediate_value hu hv hf ⟨hun.le,hvp.le⟩
        exact hne w hw hw0
      constructor <;> intro hp <;> by_contra hn
      · exact hno r l ⟨hlr,le_rfl⟩ ⟨le_rfl,hlr⟩
          (lt_of_le_of_ne (le_of_not_gt hn) (hne r ⟨hlr,le_rfl⟩)) hp
      · exact hno l r ⟨le_rfl,hlr⟩ ⟨hlr,le_rfl⟩
          (lt_of_le_of_ne (le_of_not_gt hn) (hne l ⟨le_rfl,hlr⟩)) hp
    have hBefore (s : Interval) (hs : s ∈ Ioo (A.left jj) (A.center jj)) :
        (0 < port (jj,false) 1 ↔ 0 < A.chart (b s) 1) := by
      exact hsignConstant (A.left jj) s hs.1.le
        (fun q hq => ⟨hq.1,hq.2.trans (hs.2.trans (A.cuts jj).2.2.1).le⟩)
        (fun hq => (not_le_of_gt hs.2) hq.2)
    have hAfter (s : Interval) (hs : s ∈ Ioo (A.center jj) (A.right jj)) :
        (0 < port (jj,true) 1 ↔ 0 < A.chart (b s) 1) := by
      exact (hsignConstant s (A.right jj) hs.2.le
        (fun q hq => ⟨((A.cuts jj).2.1.trans hs.1).le.trans hq.1,hq.2⟩)
        (fun hq => (not_le_of_gt hs.1) hq.1)).symm
    have hOpposite :
        ((∀ s ∈ Ioo (A.left jj) t, 0 < E (b s) 1) ∧
          (∀ s ∈ Ioo t (A.right jj), E (b s) 1 < 0)) ∨
        ((∀ s ∈ Ioo (A.left jj) t, E (b s) 1 < 0) ∧
          (∀ s ∈ Ioo t (A.right jj), 0 < E (b s) 1)) := by
      rw [← htj]
      rcases hPortSigns with hp | hp
      · left;constructor
        · intro s hs
          exact (hHsign _).1.mpr ((hBefore s hs).mp hp.1)
        · intro s hs
          apply (hHneg _).mpr
          have hn : ¬0 < A.chart (b s) 1 := fun hz =>
            (not_lt_of_ge hp.2.le) ((hAfter s hs).mpr hz)
          exact lt_of_le_of_ne (le_of_not_gt hn)
            (htraceNe s ⟨((A.cuts jj).2.1.trans hs.1).le,hs.2.le⟩ hs.1.ne')
      · right;constructor
        · intro s hs
          apply (hHneg _).mpr
          have hn : ¬0 < A.chart (b s) 1 := fun hz =>
            (not_lt_of_ge hp.1.le) ((hBefore s hs).mpr hz)
          exact lt_of_le_of_ne (le_of_not_gt hn)
            (htraceNe s ⟨hs.1.le,(hs.2.trans (A.cuts jj).2.2.1).le⟩ hs.2.ne)
        · intro s hs
          exact (hHsign _).1.mpr ((hAfter s hs).mp hp.2)
    have hBoundary (k : Bool) : E ((a j)
        (if k then A.right jj else A.left jj)).val ∈ modelCurve := by
      have hs : port (jj,k) ∈ Metric.sphere (0:Plane) 1 := A.ports_on_sphere _
      rw [modelCurve_eq_frontier,frontier,
        (Plane.isClosed_closedSquare 0 1).closure_eq,Plane.interior_closedSquare]
      change H (port (jj,k)) ∈ Plane.closedSquare 0 1 ∧
        H (port (jj,k)) ∉ Plane.openSquare 0 1
      refine ⟨(hHclosedIff _).mpr (Metric.sphere_subset_closedBall hs),?_⟩
      intro h
      have hb := (hHopenIff _).mp h
      have hn : ‖port (jj,k)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hs
      have hlt : ‖port (jj,k)‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hb
      linarith
    let C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F (a i) (a j) u t := {
      chart := E
      aLeft := A.left ii
      aRight := A.right ii
      bLeft := A.left jj
      bRight := A.right jj
      r_interior := hu
      s_interior := ht
      contact := hi.trans hj.symm
      a_cuts := by simpa only [hui] using A.cuts ii
      b_cuts := by simpa only [htj] using A.cuts jj
      square_in_target := hSquare
      closed_support_interior := fun y hy =>
        (A.source_closure (subset_closure (show y ∈ A.chart.source from hy.1))).2
      whole_a_trace := by rw [hPull];exact A.whole_closed ii
      whole_b_trace := by rw [hPull];exact A.whole_closed jj
      anchor_diameter := hAnchor
      contact_at_origin := by change H (A.chart ((a i) u).val) = 0;rw [hi,A.contact_zero,hHz]
      b_open_inside := by
        intro s hs
        apply (hHopenIff _).mpr
        have hm : (a j) s ∈ (a j) '' Ioo (A.left jj) (A.right jj) := ⟨s,hs,rfl⟩
        rw [← A.whole_open jj] at hm
        exact hm.1.2
      b_left_boundary := hBoundary false
      b_right_boundary := hBoundary true
      only_contact := by
        intro s hs
        constructor
        · intro hr
          have hm : (a j) s ∈ (a j) '' Icc (A.left jj) (A.right jj) := ⟨s,hs,rfl⟩
          rw [← A.whole_closed jj] at hm
          have hzero := (hAAxis _ hm.1.1 hm.1.2).mp hr
          by_contra hst
          exact htraceNe s hs (fun he => hst (he.trans htj)) hzero
        · intro he
          rw [he,hj]
          exact hip }
    refine ⟨C,hOpposite,?_⟩
    intro y hy
    obtain ⟨z,hz,he⟩ := (A.source_closure (subset_closure hy.1)).1
    exact (Subtype.ext he) ▸ hz
