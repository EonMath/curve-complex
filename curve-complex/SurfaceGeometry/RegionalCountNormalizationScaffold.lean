import RegionalDecreaseSupport
import RegionalNormalizationChordScaffold
import RegionalNormalizationAccounting

open CurveComplex Set Topology RegionalTotalDecrease
open scoped BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- PLAN A: individual frontier-fixed F movies normalize the whole augmented
finite family, with each original distinct-pair count nonincreasing. -/
theorem regional_finite_family_count_nonincreasing_crossing_normalization
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
      ∃ (r' : ι → IntrinsicEssentialArc) (α' : IntrinsicEssentialArc)
        (H : ι → AmbientIsotopy ↥F) (Hα : AmbientIsotopy ↥F),
        (∀ i, ClassMovie {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F}
          (r i).val.val (r' i).val.val (H i)) ∧
        ClassMovie {y | y.val ∈ boundaryCircle} {y | y.val ∈ frontier F}
          α.val.val α'.val.val Hα ∧
        (∀ i t y, y.val ∈ frontier F → (H i).map (t,y) = y) ∧
        (∀ t y, y.val ∈ frontier F → Hα.map (t,y) = y) ∧
        (∀ i, (r' i).val.val 0 = (r i).val.val 0 ∧
          (r' i).val.val 1 = (r i).val.val 1) ∧
        (α'.val.val 0 = α.val.val 0 ∧ α'.val.val 1 = α.val.val 1) ∧
        (∀ i, Quot.mk intrinsicArcRel (r' i) = Quot.mk intrinsicArcRel (r i)) ∧
        Quot.mk intrinsicArcRel α' = Quot.mk intrinsicArcRel α ∧
        FamilyInvariant (fun i => (r' i).val.val) α'.val.val ∧
        (∀ i j : Option ι, i ≠ j →
          (range (augmented (fun i => (r' i).val.val) α'.val.val i) ∩
            range (augmented (fun i => (r' i).val.val) α'.val.val j)).Finite) ∧
        (∀ i j : Option ι, i ≠ j →
          RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
            (augmented (fun i => (r' i).val.val) α'.val.val i)
            (augmented (fun i => (r' i).val.val) α'.val.val j)) ∧
        (∀ i j : Option ι, i ≠ j →
          (range (augmented (fun i => (r' i).val.val) α'.val.val i) ∩
            range (augmented (fun i => (r' i).val.val) α'.val.val j)).ncard ≤
          (range (augmented (fun i => (r i).val.val) α.val.val i) ∩
            range (augmented (fun i => (r i).val.val) α.val.val j)).ncard) := by
  set_option maxHeartbeats 3000000 in
    classical
    intro B Proper Parallel Arc rel Vertex Faces Complex ι inst r α hInv
    have hBF : B ⊆ frontier F := by
      rw [hfrontier]
      exact Set.subset_union_left
    let old : Option ι → C(Interval,↥F) := augmented (fun i => (r i).val.val) α.val.val
    have holdFinite : ∀ i j : Option ι, i ≠ j →
        (range (old i) ∩ range (old j)).Finite := by
      intro i j hij
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact hInv.2.2.2.2 j
      | some i =>
        cases j with
        | none =>
          change (range (r i).val.val ∩ range α.val.val).Finite
          rw [inter_comm]
          exact hInv.2.2.2.2 i
        | some j => exact hInv.1 i j (fun he => hij (congrArg some he))
    let oldArc : Option ι → Arc := fun i => i.elim α r
    have holdArc (i : Option ι) : (oldArc i).val.val = old i := by
      cases i <;> rfl
    have oldBoundaryRange (a : Arc) (p : ↥F) (hp : p.val ∈ frontier F)
        (h0 : p ≠ a.val.val 0) (h1 : p ≠ a.val.val 1) : p ∉ range a.val.val := by
      rintro ⟨t,ht⟩
      by_cases ht0 : t = 0
      · exact h0 (ht.symm.trans (congrArg a.val.val ht0))
      by_cases ht1 : t = 1
      · exact h1 (ht.symm.trans (congrArg a.val.val ht1))
      exact a.val.property.2.2.2 t
        ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ (ht.symm ▸ hp)
    have holdClear : ∀ i j : Option ι, i ≠ j →
        old i 0 ∉ range (old j) ∧ old i 1 ∉ range (old j) := by
      intro i j hij
      cases i with
      | none =>
        cases j with
        | none => exact (hij rfl).elim
        | some j => exact ⟨hInv.2.2.1 j,hInv.2.2.2.1 j⟩
      | some i =>
        cases j with
        | none =>
          change (r i).val.val 0 ∉ range α.val.val ∧
            (r i).val.val 1 ∉ range α.val.val
          constructor
          · apply oldBoundaryRange α _ (hBF (r i).val.property.2.1)
            · exact fun he => hInv.2.2.1 i ⟨0,he⟩
            · exact fun he => hInv.2.2.2.1 i ⟨0,he⟩
          · apply oldBoundaryRange α _ (hBF (r i).val.property.2.2.1)
            · exact fun he => hInv.2.2.1 i ⟨1,he⟩
            · exact fun he => hInv.2.2.2.1 i ⟨1,he⟩
        | some j =>
          have hij' : i ≠ j := fun he => hij (congrArg some he)
          obtain ⟨h00,h01,h10,h11⟩ := hInv.2.1 i j hij'
          change (r i).val.val 0 ∉ range (r j).val.val ∧
            (r i).val.val 1 ∉ range (r j).val.val
          exact ⟨oldBoundaryRange (r j) _ (hBF (r i).val.property.2.1) h00 h01,
            oldBoundaryRange (r j) _ (hBF (r i).val.property.2.2.1) h10 h11⟩
    have contactInterior (i j : Option ι) (hij : i ≠ j) (u v : Interval)
        (huv : old i u = old j v) :
        u ∈ Ioo (0 : Interval) 1 ∧ v ∈ Ioo (0 : Interval) 1 ∧
          (old i u).val ∈ interior F := by
      have hu0 : u ≠ 0 := fun he => (holdClear i j hij).1 ⟨v,huv.symm.trans (congrArg (old i) he)⟩
      have hu1 : u ≠ 1 := fun he => (holdClear i j hij).2 ⟨v,huv.symm.trans (congrArg (old i) he)⟩
      have hv0 : v ≠ 0 := fun he => (holdClear j i hij.symm).1 ⟨u,huv.trans (congrArg (old j) he)⟩
      have hv1 : v ≠ 1 := fun he => (holdClear j i hij.symm).2 ⟨u,huv.trans (congrArg (old j) he)⟩
      have hu : u ∈ Ioo (0 : Interval) 1 :=
        ⟨bot_lt_iff_ne_bot.mpr hu0,lt_top_iff_ne_top.mpr hu1⟩
      have hv : v ∈ Ioo (0 : Interval) 1 :=
        ⟨bot_lt_iff_ne_bot.mpr hv0,lt_top_iff_ne_top.mpr hv1⟩
      refine ⟨hu,hv,?_⟩
      apply (mem_interior_iff_notMem_frontier (old i u).property).mpr
      rw [← holdArc i]
      exact (oldArc i).val.property.2.2.2 u hu
    letI : ClosedSurface S := Classical.choice hS.2.1
    have contactCharts (i j : Option ι) (hij : i ≠ j) (u v : Interval)
        (huv : old i u = old j v) :
        ∃ C : RegionalEmbeddedFamily.RegionalIsolatedContactChart F (old i) (old j) u v,
          C.SameSide ∨ C.OppositeSides := by
      obtain ⟨hu,hv,hp⟩ := contactInterior i j hij u v huv
      have hi : IsEmbedding (old i) := holdArc i ▸ (oldArc i).val.property.1
      have hj : IsEmbedding (old j) := holdArc j ▸ (oldArc j).val.property.1
      exact RegionalEmbeddedFamily.regional_finite_contact_has_isolated_contact_chart
        F (old i) (old j) hi hj (holdFinite i j hij) u v hu hv huv hp
    let transport (K : AmbientIsotopy ↥F) (a : C(Interval,↥F)) : C(Interval,↥F) :=
      ⟨fun t => K.map (1,a t),
        K.map.continuous.comp (continuous_const.prodMk a.continuous)⟩
    -- Disjoint contact disks support individual movies. Their actual final
    -- whole traces supply both crossing charts and the original pair budget.
    have normalize : ∃ K : Option ι → AmbientIsotopy ↥F,
        (∀ i t y, y.val ∈ frontier F → (K i).map (t,y) = y) ∧
        (∀ i j : Option ι, i ≠ j →
          (range (transport (K i) (old i)) ∩ range (transport (K j) (old j))).Finite) ∧
        (∀ i j : Option ι, i ≠ j →
          RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
            (transport (K i) (old i)) (transport (K j) (old j))) ∧
        (∀ i j : Option ι, i ≠ j →
          (range (transport (K i) (old i)) ∩ range (transport (K j) (old j))).ncard ≤
            (range (old i) ∩ range (old j)).ncard) := by
      have holdEmbedding (i : Option ι) : IsEmbedding (old i) :=
        holdArc i ▸ (oldArc i).val.property.1
      let P : Set ↥F := ⋃ i, ⋃ j, if i = j then ∅ else range (old i) ∩ range (old j)
      have hPfinite : P.Finite := by
        convert RegionalNormalizationAccounting.finite_distinct_contact_locus old holdFinite using 1
        dsimp only [P]
        apply congrArg (fun A : Option ι → Set ↥F => ⋃ i, A i)
        funext i
        apply congrArg (fun A : Option ι → Set ↥F => ⋃ j, A j)
        funext j
        split_ifs <;> rfl
      letI : Fintype ↥P := hPfinite.fintype
      have hcontact (p : ↥F) (hp : p ∈ P) :
          ∃ i j : Option ι, i ≠ j ∧ p ∈ range (old i) ∩ range (old j) := by
        obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hi
        by_cases hij : i = j
        · simp only [if_pos hij,Set.mem_empty_iff_false] at hj
        · exact ⟨i,j,hij,by simpa only [if_neg hij] using hj⟩
      have hparam (p : ↥P) (i : Option ι) (hi : p.val ∈ range (old i)) :
          ∃ t ∈ Ioo (0 : Interval) 1, old i t = p.val := by
        obtain ⟨j,k,hjk,hpj,hpk⟩ := hcontact p.val p.property
        obtain ⟨u,hu⟩ := hi
        by_cases hij : i = j
        · obtain ⟨v,hv⟩ := hpk
          exact ⟨u,(contactInterior i k (hij ▸ hjk) u v (hu.trans hv.symm)).1,hu⟩
        · obtain ⟨v,hv⟩ := hpj
          exact ⟨u,(contactInterior i j hij u v (hu.trans hv.symm)).1,hu⟩
      have hPinterior (p : ↥P) : p.val.val ∈ interior F := by
        obtain ⟨i,j,hij,⟨u,hu⟩,⟨v,hv⟩⟩ := hcontact p.val p.property
        exact hu ▸ (contactInterior i j hij u v (hu.trans hv.symm)).2.2
      obtain ⟨V,hV,hVdis⟩ := (hPfinite.image Subtype.val).t2_separation
      let N (p : ↥P) : Set S := V p.val.val ∩ interior F
      have hNopen (p : ↥P) : IsOpen (N p) := (hV _).2.inter isOpen_interior
      have hpN (p : ↥P) : p.val.val ∈ N p := ⟨(hV _).1,hPinterior p⟩
      have hNF (p : ↥P) : N p ⊆ interior F := Set.inter_subset_right
      have hNdis (p q : ↥P) (hpq : p ≠ q) : Disjoint (N p) (N q) := by
        apply (hVdis (Set.mem_image_of_mem _ p.property)
          (Set.mem_image_of_mem _ q.property)
          (fun he => hpq (Subtype.ext (Subtype.ext he)))).mono
        · exact Set.inter_subset_left
        · exact Set.inter_subset_left
      have honly (p : ↥P) (i j : Option ι) (hij : i ≠ j)
          (y : ↥F) (hy : y ∈ range (old i) ∩ range (old j))
          (hyN : y.val ∈ N p) : y = p.val := by
        have hyP : y ∈ P := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
          ⟨j,by simpa only [if_neg hij] using hy⟩⟩
        by_contra hne
        have hd := hNdis p ⟨y,hyP⟩ (fun he => hne (congrArg Subtype.val he).symm)
        exact Set.disjoint_left.mp hd hyN (hpN ⟨y,hyP⟩)
      have disks (p : ↥P) :=
        regional_finite_incident_whole_trace_disk S g hg hS x R hR htarget F
          hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
          (Option ι) old holdEmbedding holdFinite p.val (hcontact p.val p.property)
          (hparam p) (N p) (hNopen p) (hpN p) (hNF p) (honly p)
      choose e l rt τ hdisk using disks
      let Inc (p : ↥P) := {i : Option ι // p.val ∈ range (old i)}
      let D (p : ↥P) : Set ↥F := RegionalChordNormalization.chartPull F (e p)
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      let U (p : ↥P) : Set ↥F := RegionalChordNormalization.chartPull F (e p)
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      let port (p : ↥P) (z : Inc p × Bool) : EuclideanSpace ℝ (Fin 2) :=
        e p ((old z.1.val) (if z.2 then rt p z.1 else l p z.1)).val
      have hDsubset (p : ↥P) : D p ⊆ {y | y.val ∈ N p} := by
        intro y hy
        exact (hdisk p).1 hy.1
      have hUsubset (p : ↥P) : U p ⊆ D p := by
        intro y hy
        exact ⟨hy.1,Metric.ball_subset_closedBall hy.2⟩
      have hUdis (p q : ↥P) (hpq : p ≠ q) : Disjoint (U p) (U q) := by
        rw [Set.disjoint_left]
        intro y hy hz
        exact Set.disjoint_left.mp (hNdis p q hpq)
          (hDsubset p (hUsubset p hy)) (hDsubset q (hUsubset q hz))
      have hpU (p : ↥P) : p.val ∈ U p := by
        refine ⟨(hdisk p).2.1.1,?_⟩
        rw [(hdisk p).2.1.2]
        exact Metric.mem_ball_self (by norm_num)
      have chordGeometry (p : ↥P) :=
        finite_round_disk_chord_geometry S g hg hS x R hR htarget F
          hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
          (Inc p) (port p) (hdisk p).2.2.2.2.2.2.2.2.2.1 (hdisk p).2.2.2.2.2.2.2.2.2.2
      have crosscutMovies (p : ↥P) (i : Inc p) :
          ∃ M : AmbientIsotopy ↥F,
            (∀ t y, y ∉ U p → M.map (t,y) = y) ∧
            M.finalMap '' (old i.val '' Icc (l p i) (rt p i)) =
              RegionalChordNormalization.chartPull F (e p)
                (segment ℝ (port p (i,false)) (port p (i,true))) ∧
            D p ∩ range (transport M (old i.val)) =
              RegionalChordNormalization.chartPull F (e p)
                (segment ℝ (port p (i,false)) (port p (i,true))) ∧
            range (transport M (old i.val)) \ U p = range (old i.val) \ U p ∧
            range (transport M (old i.val)) = (range (old i.val) \ U p) ∪
              RegionalChordNormalization.chartPull F (e p)
                (segment ℝ (port p (i,false)) (port p (i,true))) ∧
            (∀ t y, y.val ∈ frontier F → M.map (t,y) = y) := by
        obtain ⟨hEs,hEp,hEt,hedge,hcenter,hD,hU,hrad,haway,hsphere,hports⟩ := hdisk p
        have hlr : l p i < rt p i := lt_trans (hedge i).2.1 (hedge i).2.2.1
        let clock := CurveComplex.BranchedDoubleCover.intervalAffine (l p i) (rt p i)
        have hclockcont : Continuous clock := by
          apply Continuous.subtype_mk
          fun_prop
        have hclockmem (t : Interval) : clock t ∈ Icc (l p i) (rt p i) :=
          CurveComplex.BranchedDoubleCover.intervalAffine_mem_Icc hlr.le t
        have hclockinj : Function.Injective clock := by
          intro u v huv
          apply Subtype.ext
          have hh := congrArg Subtype.val huv
          change (1 - (u : ℝ)) * (l p i : ℝ) + (u : ℝ) * (rt p i : ℝ) =
            (1 - (v : ℝ)) * (l p i : ℝ) + (v : ℝ) * (rt p i : ℝ) at hh
          have he : ((rt p i : ℝ) - (l p i : ℝ)) * (u : ℝ) =
              ((rt p i : ℝ) - (l p i : ℝ)) * (v : ℝ) := by nlinarith [hh]
          exact mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_gt (show (l p i : ℝ) < (rt p i : ℝ) from hlr))) he
        have hclockonto (t : Interval) (ht : t ∈ Icc (l p i) (rt p i)) :
            ∃ u : Interval, clock u = t := by
          have hden : 0 < (rt p i : ℝ) - (l p i : ℝ) := sub_pos.mpr hlr
          let u : Interval := ⟨((t : ℝ) - (l p i : ℝ)) /
            ((rt p i : ℝ) - (l p i : ℝ)),
            ⟨div_nonneg (sub_nonneg.mpr ht.1) hden.le,
              (div_le_iff₀ hden).mpr (by
                simpa only [one_mul] using
                  (sub_le_sub_right (show (t : ℝ) ≤ (rt p i : ℝ) from ht.2) (l p i : ℝ)))⟩⟩
          refine ⟨u,?_⟩
          apply Subtype.ext
          change (1 - ((t : ℝ) - (l p i : ℝ)) / ((rt p i : ℝ) - (l p i : ℝ))) *
            (l p i : ℝ) + (((t : ℝ) - (l p i : ℝ)) /
              ((rt p i : ℝ) - (l p i : ℝ))) * (rt p i : ℝ) = (t : ℝ)
          field_simp
          <;> ring
        have hsource (t : Interval) (ht : t ∈ Icc (l p i) (rt p i)) :
            (old i.val t).val ∈ (e p).source := by
          have hm : old i.val t ∈ D p ∩ range (old i.val) := by
            rw [hD i]
            exact ⟨t,ht,rfl⟩
          exact hm.1.1
        let f : C(Interval,EuclideanSpace ℝ (Fin 2)) :=
          ⟨fun t => e p (old i.val (clock t)).val,
            (e p).continuousOn.comp_continuous
              (continuous_subtype_val.comp ((old i.val).continuous.comp hclockcont))
              (fun t => hsource _ (hclockmem t))⟩
        have hfinj : Function.Injective f := by
          intro u v huv
          apply hclockinj
          apply (holdEmbedding i.val).injective
          apply Subtype.ext
          exact (e p).injOn (hsource _ (hclockmem u)) (hsource _ (hclockmem v)) huv
        have hfrange : range f = (fun t => e p (old i.val t).val) '' Icc (l p i) (rt p i) := by
          ext z
          constructor
          · rintro ⟨u,rfl⟩
            exact ⟨clock u,hclockmem u,rfl⟩
          · rintro ⟨t,ht,rfl⟩
            obtain ⟨u,hu⟩ := hclockonto t ht
            exact ⟨u,by change e p (old i.val (clock u)).val = _; rw [hu]⟩
        have hf0 : f 0 = port p (i,false) := by
          change e p (old i.val (clock 0)).val = e p (old i.val (l p i)).val
          congr 3
          apply Subtype.ext
          simp [clock,CurveComplex.BranchedDoubleCover.intervalAffine]
        have hf1 : f 1 = port p (i,true) := by
          change e p (old i.val (clock 1)).val = e p (old i.val (rt p i)).val
          congr 3
          apply Subtype.ext
          simp [clock,CurveComplex.BranchedDoubleCover.intervalAffine]
        have hA : Schoenflies.IsArcBetween
            ((fun t => e p (old i.val t).val) '' Icc (l p i) (rt p i))
            (port p (i,false)) (port p (i,true)) := by
          let fc : ℝ → EuclideanSpace ℝ (Fin 2) := f ∘ Set.projIcc 0 1 zero_le_one
          have hfc : Continuous fc := f.continuous.comp continuous_projIcc
          have he (t : Interval) : fc t = f t := by
            simp [fc,Set.projIcc_of_mem zero_le_one t.property]
          refine ⟨fc,hfc.continuousOn,?_,?_,(he 0).trans hf0,(he 1).trans hf1⟩
          · intro t ht u hu hh
            exact congrArg Subtype.val (hfinj (by
              simpa only [← he] using hh : f ⟨t,ht⟩ = f ⟨u,hu⟩))
          · rw [← hfrange]
            ext z
            constructor
            · rintro ⟨t,ht,rfl⟩
              exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
            · rintro ⟨t,rfl⟩
              exact ⟨t,t.property,he t⟩
        have hAi : ((fun t => e p (old i.val t).val) '' Icc (l p i) (rt p i)) \ {port p (i,false),port p (i,true)} ⊆
              Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
          rintro z ⟨⟨t,ht,rfl⟩,hne⟩
          have ht0 : t ≠ l p i := by
            intro hh
            exact hne (by simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; left; simp [port,hh])
          have ht1 : t ≠ rt p i := by
            intro hh
            exact hne (by simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; right; simp [port,hh])
          have hm : old i.val t ∈ U p ∩ range (old i.val) := by
            rw [hU i]
            exact ⟨t,⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),lt_of_le_of_ne ht.2 ht1⟩,rfl⟩
          exact hm.1.2
        have hpne : port p (i,false) ≠ port p (i,true) := by
          intro hh
          have h := congrArg Prod.snd (hports hh)
          exact Bool.false_ne_true h
        exact regional_round_crosscut_supported_chord_movie S g hg hS x R hR htarget F
          hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
          (old i.val) (holdEmbedding i.val) (e p) (fun y hy => hNF p (hEs hy)) hEt
          (l p i) (rt p i) hlr (hD i) (hU i) (hsphere (i,false)) (hsphere (i,true))
          hpne hA hAi
      choose Mcut hMcut using crosscutMovies
      let M (p : ↥P) (i : Option ι) : AmbientIsotopy ↥F :=
        if hi : p.val ∈ range (old i) then Mcut p ⟨i,hi⟩ else AmbientIsotopy.identity ↥F
      have hMfix (p : ↥P) (i : Option ι) (t : Interval) (y : ↥F) (hy : y ∉ U p) :
          (M p i).map (t,y) = y := by
        dsimp only [M]
        split_ifs with hi
        · exact (hMcut p ⟨i,hi⟩).1 t y hy
        · rfl
      have hMfront (p : ↥P) (i : Option ι) (t : Interval) (y : ↥F)
          (hy : y.val ∈ frontier F) : (M p i).map (t,y) = y := by
        dsimp only [M]
        split_ifs with hi
        · exact (hMcut p ⟨i,hi⟩).2.2.2.2.2 t y hy
        · rfl
      have hinjective (H : AmbientIsotopy ↥F) (t : Interval) :
          Function.Injective (fun y => H.map (t,y)) := by
        obtain ⟨h,hh⟩ := H.homeomorphism_at t
        exact (funext hh) ▸ h.injective
      have hpreserve (p q : ↥P) (i : Option ι) (t : Interval) (y : ↥F) :
          (M q i).map (t,y) ∈ U p ↔ y ∈ U p := by
        by_cases hpq : p = q
        · subst q
          constructor
          · intro hy
            by_contra hh
            rw [hMfix p i t y hh] at hy
            exact hh hy
          · intro hy
            by_contra hh
            have he := hMfix p i t ((M p i).map (t,y)) hh
            have heq : (M p i).map (t,y) = y :=
              (hinjective (M p i) t) he
            exact hh (heq.symm ▸ hy)
        · have hf (z : ↥F) (hz : z ∈ U p) : (M q i).map (t,z) = z :=
            hMfix q i t z (fun hh => Set.disjoint_left.mp (hUdis p q hpq) hz hh)
          constructor
          · intro hy
            have heq := (hinjective (M q i) t) (hf _ hy)
            exact heq ▸ hy
          · intro hy
            rw [hf y hy]
            exact hy
      let compose (L : List ↥P) (i : Option ι) : AmbientIsotopy ↥F :=
        AmbientIsotopy.finiteCompose (L.map (fun p => M p i))
      have hcompose_preserve (L : List ↥P) (i : Option ι) (p : ↥P)
          (t : Interval) (y : ↥F) :
          (compose L i).map (t,y) ∈ U p ↔ y ∈ U p := by
        induction L generalizing y with
        | nil => rfl
        | cons q L ih =>
          change (compose L i).map (t,(M q i).map (t,y)) ∈ U p ↔ y ∈ U p
          rw [ih,hpreserve]
      have hcompose_patch (L : List ↥P) (hL : L.Nodup) (i : Option ι) (p : ↥P)
          (t : Interval) (y : ↥F) (hy : y ∈ U p) :
          (compose L i).map (t,y) = if p ∈ L then (M p i).map (t,y) else y := by
        induction L generalizing y with
        | nil => simp [compose,AmbientIsotopy.finiteCompose,AmbientIsotopy.identity]
        | cons q L ih =>
          have hqL : q ∉ L := (List.nodup_cons.mp hL).1
          have hLn : L.Nodup := (List.nodup_cons.mp hL).2
          change (compose L i).map (t,(M q i).map (t,y)) = _
          by_cases hqp : q = p
          · subst q
            rw [ih hLn _ ((hpreserve p p i t y).mpr hy)]
            simp only [List.mem_cons_self,ite_true,ite_eq_right hqL]
          · have hyq : y ∉ U q := fun hh => Set.disjoint_left.mp (hUdis p q (Ne.symm hqp)) hy hh
            rw [hMfix q i t y hyq,ih hLn y hy]
            simp only [List.mem_cons,Ne.symm hqp,false_or]
      let K (i : Option ι) : AmbientIsotopy ↥F := compose (Finset.univ.toList) i
      have hKpatch (i : Option ι) (p : ↥P) (t : Interval) (y : ↥F) (hy : y ∈ U p) :
          (K i).map (t,y) = (M p i).map (t,y) := by
        simpa only [Finset.mem_toList,Finset.mem_univ,ite_true] using
          hcompose_patch Finset.univ.toList (Finset.nodup_toList _) i p t y hy
      have hKoutside (i : Option ι) (t : Interval) (y : ↥F) (hy : y ∉ ⋃ p, U p) :
          (K i).map (t,y) = y := by
        apply AmbientIsotopy.finiteCompose_fixes _ ((⋃ p, U p)ᶜ)
        · intro H hH t z hz
          obtain ⟨p,_,rfl⟩ := List.mem_map.mp hH
          exact hMfix p i t z (fun hh => hz (Set.mem_iUnion.mpr ⟨p,hh⟩))
        · exact hy
      have hKfront (i : Option ι) (t : Interval) (y : ↥F)
          (hy : y.val ∈ frontier F) : (K i).map (t,y) = y := by
        apply AmbientIsotopy.finiteCompose_fixes _ {z : ↥F | z.val ∈ frontier F}
        · intro H hH t z hz
          obtain ⟨p,_,rfl⟩ := List.mem_map.mp hH
          exact hMfront p i t z hz
        · exact hy
      let new (i : Option ι) : C(Interval,↥F) := transport (K i) (old i)
      have hlocal (p : ↥P) (i : Option ι) :
          U p ∩ range (new i) = U p ∩ range (transport (M p i) (old i)) := by
        ext z
        constructor
        · rintro ⟨hz,⟨u,hu⟩⟩
          have hy : old i u ∈ U p :=
            (hcompose_preserve Finset.univ.toList i p 1 (old i u)).mp (hu ▸ hz)
          exact ⟨hz,⟨u,(hKpatch i p 1 (old i u) hy).symm.trans hu⟩⟩
        · rintro ⟨hz,⟨u,hu⟩⟩
          have hy : old i u ∈ U p := (hpreserve p p i 1 (old i u)).mp (hu ▸ hz)
          exact ⟨hz,⟨u,(hKpatch i p 1 (old i u) hy).trans hu⟩⟩
      have hout (i : Option ι) (z : ↥F) (hz : z ∉ ⋃ p, U p) :
          z ∈ range (new i) ↔ z ∈ range (old i) := by
        constructor
        · rintro ⟨u,hu⟩
          have heq : old i u = z :=
            hinjective (K i) 1 (hu.trans (hKoutside i 1 z hz).symm)
          exact ⟨u,heq⟩
        · rintro ⟨u,hu⟩
          exact ⟨u,by change (K i).map (1,old i u) = z; rw [hu,hKoutside i 1 z hz]⟩
      have hlocalAway (p : ↥P) (i : Option ι) (hi : p.val ∉ range (old i)) :
          Disjoint (U p) (range (new i)) := by
        rw [Set.disjoint_left]
        intro z hz hn
        have hm := (show z ∈ U p ∩ range (transport (M p i) (old i)) from
          hlocal p i ▸ ⟨hz,hn⟩).2
        have hmid : M p i = AmbientIsotopy.identity ↥F := by simp only [M,dite_eq_right hi]
        rw [hmid] at hm
        change z ∈ range (old i) at hm
        exact Set.disjoint_left.mp ((hdisk p).2.2.2.2.2.2.2.2.1 i hi) (hUsubset p hz) hm
      have hlocalChord (p : ↥P) (i : Inc p) :
          U p ∩ range (new i.val) = U p ∩
            RegionalChordNormalization.chartPull F (e p)
              (segment ℝ (port p (i,false)) (port p (i,true))) := by
        rw [hlocal p i.val]
        have hmi : M p i.val = Mcut p i := by
          dsimp only [M]
          rw [dif_pos i.property]
        rw [hmi]
        have hd := (hMcut p i).2.2.1
        ext z
        constructor
        · rintro ⟨hz,hn⟩
          exact ⟨hz,hd ▸ ⟨hUsubset p hz,hn⟩⟩
        · rintro ⟨hz,hn⟩
          exact ⟨hz,(show z ∈ D p ∩ range (transport (Mcut p i) (old i.val)) from hd.symm ▸ hn).2⟩
      have hcover (i j : Option ι) (hij : i ≠ j) (z : ↥F)
          (hz : z ∈ range (new i) ∩ range (new j)) :
          ∃ p : ↥P, p.val ∈ range (old i) ∩ range (old j) ∧ z ∈ U p := by
        by_cases hzu : z ∈ ⋃ p, U p
        · obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hzu
          have hi : p.val ∈ range (old i) := by
            by_contra hh
            exact Set.disjoint_left.mp (hlocalAway p i hh) hp hz.1
          have hj : p.val ∈ range (old j) := by
            by_contra hh
            exact Set.disjoint_left.mp (hlocalAway p j hh) hp hz.2
          exact ⟨p,⟨hi,hj⟩,hp⟩
        · have ho : z ∈ range (old i) ∩ range (old j) :=
            ⟨(hout i z hzu).mp hz.1,(hout j z hzu).mp hz.2⟩
          have hzP : z ∈ P := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
            ⟨j,by simpa only [ite_eq_right hij] using ho⟩⟩
          exact (hzu (Set.mem_iUnion.mpr ⟨⟨z,hzP⟩,hpU ⟨z,hzP⟩⟩)).elim
      have hlocalUnique (i j : Option ι) (hij : i ≠ j) (p : ↥P)
          (hp : p.val ∈ range (old i) ∩ range (old j)) :
          (U p ∩ (range (new i) ∩ range (new j))).Subsingleton := by
        intro z hz w hw
        let ii : Inc p := ⟨i,hp.1⟩
        let jj : Inc p := ⟨j,hp.2⟩
        have hc (v : ↥F) (hv : v ∈ U p ∩ (range (new i) ∩ range (new j))) :
            e p v.val ∈ segment ℝ (port p (ii,false)) (port p (ii,true)) ∩
              segment ℝ (port p (jj,false)) (port p (jj,true)) := by
          exact ⟨(show v ∈ U p ∩ RegionalChordNormalization.chartPull F (e p)
            (segment ℝ (port p (ii,false)) (port p (ii,true))) from
              hlocalChord p ii ▸ ⟨hv.1,hv.2.1⟩).2.2,
            (show v ∈ U p ∩ RegionalChordNormalization.chartPull F (e p)
            (segment ℝ (port p (jj,false)) (port p (jj,true))) from
              hlocalChord p jj ▸ ⟨hv.1,hv.2.2⟩).2.2⟩
        apply Subtype.ext
        apply (e p).injOn hz.1.1 hw.1.1
        exact (chordGeometry p).2.2.1 ii jj (fun hh => hij (congrArg Subtype.val hh)) (hc z hz) (hc w hw)
      have hbudget (i j : Option ι) (hij : i ≠ j) :
          (range (new i) ∩ range (new j)).Finite ∧
            (range (new i) ∩ range (new j)).ncard ≤ (range (old i) ∩ range (old j)).ncard := by
        let O := range (old i) ∩ range (old j)
        have hOP (p : ↥O) : p.val ∈ P := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
          ⟨j,by simpa only [ite_eq_right hij] using p.property⟩⟩
        let Q (p : ↥O) : Set ↥F := U ⟨p.val,hOP p⟩ ∩ (range (new i) ∩ range (new j))
        apply RegionalNormalizationAccounting.finite_ncard_le_of_contact_patch_cover
          O O (range (new i) ∩ range (new j)) Q (holdFinite i j hij) Set.Subset.rfl
        · intro z hz
          obtain ⟨p,hp,hzp⟩ := hcover i j hij z hz
          exact Or.inr (Set.mem_iUnion.mpr ⟨⟨p.val,hp⟩,⟨hzp,hz⟩⟩)
        · intro p
          exact hlocalUnique i j hij ⟨p.val,hOP p⟩ p.property
      have hnewEmbedding (i : Option ι) : IsEmbedding (new i) := by
        obtain ⟨h,hh⟩ := (K i).homeomorphism_at 1
        have heq : new i = (⟨h,h.continuous⟩ : C(↥F,↥F)).comp (old i) := by
          apply ContinuousMap.ext
          intro t
          exact (hh (old i t)).symm
        rw [heq]
        exact h.isEmbedding.comp (holdEmbedding i)
      have hcross : ∀ i j : Option ι, i ≠ j →
          RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F (new i) (new j) := by
        intro i j hij u v hu hv huv
        obtain ⟨p,hp,hzu⟩ := hcover i j hij (new i u) ⟨mem_range_self _,⟨v,huv.symm⟩⟩
        let ii : Inc p := ⟨i,hp.1⟩
        let jj : Inc p := ⟨j,hp.2⟩
        let z : EuclideanSpace ℝ (Fin 2) := e p (new i u).val
        have hc : z ∈ segment ℝ (port p (ii,false)) (port p (ii,true)) ∩
            segment ℝ (port p (jj,false)) (port p (jj,true)) := by
          exact ⟨(show new i u ∈ U p ∩ RegionalChordNormalization.chartPull F (e p)
            (segment ℝ (port p (ii,false)) (port p (ii,true))) from
              hlocalChord p ii ▸ ⟨hzu,mem_range_self _⟩).2.2,
            (show new i u ∈ U p ∩ RegionalChordNormalization.chartPull F (e p)
            (segment ℝ (port p (jj,false)) (port p (jj,true))) from
              hlocalChord p jj ▸ ⟨hzu,⟨v,huv.symm⟩⟩).2.2⟩
        obtain ⟨hzball,hzi,hzj,T,hTi,hTj⟩ := (chordGeometry p).2.2.2 ii jj
          (fun he => hij (congrArg Subtype.val he)) z hc
        rw [openSegment_eq_image'] at hzi hzj
        obtain ⟨ti,hti,hzi⟩ := hzi
        obtain ⟨tj,htj,hzj⟩ := hzj
        let E₀ : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2)) :=
          (e p).trans (((Homeomorph.subRight z).trans T.toHomeomorph).toOpenPartialHomeomorph)
        have hE₀s : E₀.source = (e p).source := by
          simp [E₀,OpenPartialHomeomorph.trans_source]
        let box : Set (EuclideanSpace ℝ (Fin 2)) :=
          {w | w 0 ∈ Ioo (-ti) (1-ti) ∧ w 1 ∈ Ioo (-tj) (1-tj)}
        have hbox : IsOpen box := by
          apply IsOpen.inter
          · exact isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous
          · exact isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous
        let Ns : Set S := ((e p).source ∩ (e p) ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) ∩
          (E₀.source ∩ E₀ ⁻¹' box)
        have hNs : IsOpen Ns :=
          ((e p).isOpen_inter_preimage Metric.isOpen_ball).inter (E₀.isOpen_inter_preimage hbox)
        let E := E₀.restr Ns
        have hEs : E.source = E₀.source ∩ Ns := E₀.restr_source' Ns hNs
        have hEInterior : E.source ⊆ interior F := by
          intro y hy
          rw [hEs,hE₀s] at hy
          exact hNF p ((hdisk p).1 hy.1)
        have hEp : (new i u).val ∈ E.source := by
          rw [hEs]
          refine ⟨hE₀s.symm ▸ hzu.1,⟨⟨hzu.1,hzball⟩,hE₀s.symm ▸ hzu.1,?_⟩⟩
          change T (z-z) ∈ box
          simp only [sub_self,map_zero]
          dsimp [box]
          constructor
          · exact ⟨by linarith [hti.1], by linarith [hti.2]⟩
          · exact ⟨by linarith [htj.1], by linarith [htj.2]⟩
        have hEz : E (new i u).val = 0 := by
          change T (z-z) = 0
          simp
        have hLineAxis (b : Bool) (a d : EuclideanSpace ℝ (Fin 2)) (t : ℝ)
            (hdir : T (d-a) = if b then Schoenflies.Plane.mk 0 1 else Schoenflies.Plane.mk 1 0)
            (hcenter : a + t • (d-a) = z) (w : EuclideanSpace ℝ (Fin 2))
            (hbound : T (w-z) (if b then 1 else 0) ∈ Ioo (-t) (1-t)) :
            w ∈ segment ℝ a d ↔ T (w-z) (if b then 0 else 1) = 0 := by
          constructor
          · intro hw
            rw [segment_eq_image'] at hw
            obtain ⟨s,hs,he⟩ := hw
            have hdiff : w-z = (s-t) • (d-a) := by
              rw [← he,← hcenter]
              module
            rw [hdiff,T.map_smul,hdir]
            cases b <;> simp [Schoenflies.Plane.mk]
          · intro hoff
            let q : ℝ := T (w-z) (if b then 1 else 0)
            have hvec : T (w-z) = q •
                (if b then Schoenflies.Plane.mk 0 1 else Schoenflies.Plane.mk 1 0) := by
              ext k
              fin_cases k <;> cases b <;> simp [q,Schoenflies.Plane.mk] at hoff ⊢ <;> assumption
            have hdiff : w-z = q • (d-a) := T.injective (by rw [T.map_smul,hdir]; exact hvec)
            have he : a + (q+t) • (d-a) = w := by
              rw [sub_eq_iff_eq_add] at hdiff
              rw [hdiff,← hcenter]
              module
            rw [segment_eq_image']
            exact ⟨q+t,⟨by linarith [hbound.1],by linarith [hbound.2]⟩,he⟩
        have haxisA (y : ↥F) (hy : y.val ∈ E.source) :
            y ∈ range (new i) ↔ E y.val 1 = 0 := by
          rw [hEs] at hy
          have hyU : y ∈ U p := hy.2.1
          have htrace : y ∈ range (new i) ↔
              e p y.val ∈ segment ℝ (port p (ii,false)) (port p (ii,true)) := by
            constructor
            · intro hh
              exact (show y ∈ U p ∩ RegionalChordNormalization.chartPull F (e p)
                (segment ℝ (port p (ii,false)) (port p (ii,true))) from
                hlocalChord p ii ▸ ⟨hyU,hh⟩).2.2
            · intro hh
              exact (show y ∈ U p ∩ range (new i) from
                (hlocalChord p ii).symm ▸ ⟨hyU,hyU.1,hh⟩).2
          rw [htrace]
          exact hLineAxis false _ _ ti hTi hzi _ hy.2.2.2.1
        have haxisB (y : ↥F) (hy : y.val ∈ E.source) :
            y ∈ range (new j) ↔ E y.val 0 = 0 := by
          rw [hEs] at hy
          have hyU : y ∈ U p := hy.2.1
          have htrace : y ∈ range (new j) ↔
              e p y.val ∈ segment ℝ (port p (jj,false)) (port p (jj,true)) := by
            constructor
            · intro hh
              exact (show y ∈ U p ∩ RegionalChordNormalization.chartPull F (e p)
                (segment ℝ (port p (jj,false)) (port p (jj,true))) from
                hlocalChord p jj ▸ ⟨hyU,hh⟩).2.2
            · intro hh
              exact (show y ∈ U p ∩ range (new j) from
                (hlocalChord p jj).symm ▸ ⟨hyU,hyU.1,hh⟩).2
          rw [htrace]
          exact hLineAxis true _ _ tj hTj hzj _ hy.2.2.2.2
        exact regional_local_coordinate_axes_cross S g hg hS x R hR htarget F
          hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier
          (new i) (new j) (hnewEmbedding i) (hnewEmbedding j) u v hu hv huv E
          hEInterior hEp hEz haxisA haxisB
      exact ⟨K,hKfront,(fun i j hij => (hbudget i j hij).1),hcross,
        (fun i j hij => (hbudget i j hij).2)⟩
    obtain ⟨K,hKfix,hKfinite,hKcross,hKcount⟩ := normalize
    have fixedImage (i : Option ι) (t : Interval) (U : Set ↥F)
        (hU : U ⊆ {y | y.val ∈ frontier F}) :
        (fun y => (K i).map (t,y)) '' U = U := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        simpa only [hKfix i t z (hU hz)] using hz
      · intro hy
        exact ⟨y,hy,hKfix i t y (hU hy)⟩
    have movie (i : Option ι) (a : C(Interval,↥F)) :
        ClassMovie {y | y.val ∈ B} {y | y.val ∈ frontier F}
          a (transport (K i) a) (K i) := by
      refine ⟨fun t => fixedImage i t _ (fun y hy => hBF hy),
        fun t => fixedImage i t _ Set.Subset.rfl,?_⟩
      exact (Set.range_comp _ _).symm
    have copy (i : Option ι) (a : Arc) : ∃ b : Arc,
        b.val.val = transport (K i) a.val.val ∧
        b.val.val 0 = a.val.val 0 ∧ b.val.val 1 = a.val.val 1 := by
      obtain ⟨e,he⟩ := (K i).homeomorphism_at 1
      have htransport : transport (K i) a.val.val =
          (⟨e,e.continuous⟩ : C(↥F,↥F)).comp a.val.val := by
        apply ContinuousMap.ext
        intro t
        exact (he (a.val.val t)).symm
      have hefix (y : ↥F) (hy : y.val ∈ frontier F) : e y = y :=
        (he y).trans (hKfix i 1 y hy)
      have heinvfix (y : ↥F) (hy : y.val ∈ frontier F) : e.symm y = y := by
        apply e.injective
        exact (e.apply_symm_apply y).trans (hefix y hy).symm
      have hb0 : transport (K i) a.val.val 0 = a.val.val 0 :=
        hKfix i 1 _ (hBF a.val.property.2.1)
      have hb1 : transport (K i) a.val.val 1 = a.val.val 1 :=
        hKfix i 1 _ (hBF a.val.property.2.2.1)
      have hbI : ∀ t ∈ Ioo (0 : Interval) 1,
          ((transport (K i) a.val.val) t).val ∉ frontier F := by
        intro t ht hh
        have heq : (transport (K i) a.val.val) t = a.val.val t := by
          apply e.injective
          calc
            e ((transport (K i) a.val.val) t) = (transport (K i) a.val.val) t := hefix _ hh
            _ = e (a.val.val t) := by rw [htransport]; rfl
        exact a.val.property.2.2.2 t ht (heq ▸ hh)
      have hbE : ¬ Parallel (⟨transport (K i) a.val.val,
          htransport ▸ e.isEmbedding.comp a.val.property.1,
          hb0 ▸ a.val.property.2.1,hb1 ▸ a.val.property.2.2.1,hbI⟩ : Proper) := by
        rintro ⟨v,hv,hvB,d,hd,hboundary⟩
        let v0 : C(Interval,↥F) := (⟨e.symm,e.symm.continuous⟩ : C(↥F,↥F)).comp v
        let d0 : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F) :=
          (⟨e.symm,e.symm.continuous⟩ : C(↥F,↥F)).comp d
        apply a.property
        refine ⟨v0,e.symm.isEmbedding.comp hv,?_,d0,e.symm.isEmbedding.comp hd,?_⟩
        · intro t
          change (e.symm (v t)).val ∈ B
          rw [heinvfix (v t) (hBF (hvB t))]
          exact hvB t
        · have heq := congrArg (fun U : Set ↥F => e.symm '' U) hboundary
          rw [Set.image_union] at heq
          have hfirst : e.symm '' range (transport (K i) a.val.val) = range a.val.val := by
            rw [htransport,← Set.range_comp]
            apply congrArg Set.range
            funext t
            exact e.symm_apply_apply _
          rw [hfirst,← Set.range_comp,← Set.image_comp] at heq
          exact heq
      refine ⟨⟨⟨transport (K i) a.val.val,
        htransport ▸ e.isEmbedding.comp a.val.property.1,
        hb0 ▸ a.val.property.2.1,hb1 ▸ a.val.property.2.2.1,hbI⟩,hbE⟩,rfl,hb0,hb1⟩
    choose copies hcopies hcopies0 hcopies1 using copy
    let r' : ι → Arc := fun i => copies (some i) (r i)
    let α' : Arc := copies none α
    have haug (i : Option ι) :
        augmented (fun i => (r' i).val.val) α'.val.val i = transport (K i) (old i) := by
      cases i with
      | none => exact hcopies none α
      | some i => exact hcopies (some i) (r i)
    have hr0 (i : ι) : (r' i).val.val 0 = (r i).val.val 0 := hcopies0 _ _
    have hr1 (i : ι) : (r' i).val.val 1 = (r i).val.val 1 := hcopies1 _ _
    have hα0 : α'.val.val 0 = α.val.val 0 := hcopies0 _ _
    have hα1 : α'.val.val 1 = α.val.val 1 := hcopies1 _ _
    have boundaryRange (a : Arc) (p : ↥F) (hp : p.val ∈ frontier F)
        (h0 : p ≠ a.val.val 0) (h1 : p ≠ a.val.val 1) : p ∉ range a.val.val := by
      rintro ⟨t,ht⟩
      by_cases ht0 : t = 0
      · exact h0 (ht.symm.trans (congrArg a.val.val ht0))
      by_cases ht1 : t = 1
      · exact h1 (ht.symm.trans (congrArg a.val.val ht1))
      exact a.val.property.2.2.2 t
        ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ (ht.symm ▸ hp)
    have hnewInv : FamilyInvariant (fun i => (r' i).val.val) α'.val.val := by
      refine ⟨?_,?_,?_,?_,?_⟩
      · intro i j hij
        simpa only [← haug (some i),← haug (some j),augmented,Option.elim_some] using
          hKfinite (some i) (some j) (fun he => hij (Option.some.inj he))
      · intro i j hij
        simpa only [hr0,hr1] using hInv.2.1 i j hij
      · intro i
        apply boundaryRange (r' i) (α'.val.val (0 : Interval)) (hBF α'.val.property.2.1)
        · rw [hα0,hr0]
          exact fun h => hInv.2.2.1 i ⟨0,h.symm⟩
        · rw [hα0,hr1]
          exact fun h => hInv.2.2.1 i ⟨1,h.symm⟩
      · intro i
        apply boundaryRange (r' i) (α'.val.val (1 : Interval)) (hBF α'.val.property.2.2.1)
        · rw [hα1,hr0]
          exact fun h => hInv.2.2.2.1 i ⟨0,h.symm⟩
        · rw [hα1,hr1]
          exact fun h => hInv.2.2.2.1 i ⟨1,h.symm⟩
      · intro i
        simpa only [← haug none,← haug (some i),augmented,Option.elim_none,Option.elim_some] using
          hKfinite none (some i) (by simp)
    have hrmovie (i : ι) : ClassMovie {y | y.val ∈ B} {y | y.val ∈ frontier F}
        (r i).val.val (r' i).val.val (K (some i)) := by
      rw [hcopies (some i) (r i)]
      exact movie _ _
    have hαmovie : ClassMovie {y | y.val ∈ B} {y | y.val ∈ frontier F}
        α.val.val α'.val.val (K none) := by
      rw [hcopies none α]
      exact movie _ _
    refine ⟨r',α',(fun i => K (some i)),K none,hrmovie,hαmovie,
      (fun i => hKfix (some i)),hKfix none,(fun i => ⟨hr0 i,hr1 i⟩),
      ⟨hα0,hα1⟩,?_,?_,hnewInv,?_,?_,?_⟩
    · intro i
      exact (Quot.sound (show rel (r i) (r' i) from ⟨K (some i),hrmovie i⟩)).symm
    · exact (Quot.sound (show rel α α' from ⟨K none,hαmovie⟩)).symm
    · intro i j hij
      simpa only [haug] using hKfinite i j hij
    · intro i j hij
      simpa only [haug] using hKcross i j hij
    · intro i j hij
      simpa only [haug] using hKcount i j hij
