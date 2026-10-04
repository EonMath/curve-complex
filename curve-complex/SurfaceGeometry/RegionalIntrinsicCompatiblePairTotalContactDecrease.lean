import RegionalWeightedCancellationProgress
import RegionalPairedDiskComplete
import RegionalCountNormalizationScaffold
import CurveComplexGenusTwo.Topology.ActualRegionalCompatibleReturn.RegionalCompatibleNullProgress
import RegionalOrdinaryMovieScaffold
import CurveComplexGenusTwo.Topology.ActualRegionalContactCleanup.RegionalBoundaryParallelTransport
open CurveComplex Set Topology
open scoped Manifold ContDiff BigOperators
noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P
set_option maxHeartbeats 4000000 in
theorem regional_original_intrinsic_compatible_pair_total_contact_decrease
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
    ∀ (ι : Type) [Fintype ι] (a : ι → IntrinsicEssentialArc)
      (anchor : IntrinsicEssentialArc) (k l : ι), k ≠ l →
      (∃ u v : IntrinsicEssentialArc,
        Quot.mk intrinsicArcRel u = Quot.mk intrinsicArcRel (a k) ∧
        Quot.mk intrinsicArcRel v = Quot.mk intrinsicArcRel (a l) ∧
        Disjoint (Set.range u.val.val) (Set.range v.val.val)) →
      (∀ i j, i ≠ j → (Set.range (a i).val.val ∩ Set.range (a j).val.val).Finite) →
      (∀ i j, i ≠ j → (a i).val.val 0 ≠ (a j).val.val 0 ∧
        (a i).val.val 0 ≠ (a j).val.val 1 ∧
        (a i).val.val 1 ≠ (a j).val.val 0 ∧
        (a i).val.val 1 ≠ (a j).val.val 1) →
      (∀ i, anchor.val.val 0 ∉ Set.range (a i).val.val) →
      (∀ i, anchor.val.val 1 ∉ Set.range (a i).val.val) →
      (∀ i, (Set.range anchor.val.val ∩ Set.range (a i).val.val).Finite) →
      0 < (Set.range (a k).val.val ∩ Set.range (a l).val.val).ncard →
      ∃ (b : ι → IntrinsicEssentialArc) (newAnchor : IntrinsicEssentialArc),
        (∀ i, Quot.mk intrinsicArcRel (b i) = Quot.mk intrinsicArcRel (a i)) ∧
        Quot.mk intrinsicArcRel newAnchor = Quot.mk intrinsicArcRel anchor ∧
        (∀ i j, i ≠ j → (Set.range (b i).val.val ∩ Set.range (b j).val.val).Finite) ∧
        (∀ i j, i ≠ j → (b i).val.val 0 ≠ (b j).val.val 0 ∧
          (b i).val.val 0 ≠ (b j).val.val 1 ∧
          (b i).val.val 1 ≠ (b j).val.val 0 ∧
          (b i).val.val 1 ≠ (b j).val.val 1) ∧
        (∀ i, newAnchor.val.val 0 ∉ Set.range (b i).val.val) ∧
        (∀ i, newAnchor.val.val 1 ∉ Set.range (b i).val.val) ∧
        (∀ i, (Set.range newAnchor.val.val ∩ Set.range (b i).val.val).Finite) ∧
        (∑ i : ι, ∑ j : ι, if i = j then 0 else
          (Set.range (b i).val.val ∩ Set.range (b j).val.val).ncard) <
        (∑ i : ι, ∑ j : ι, if i = j then 0 else
          (Set.range (a i).val.val ∩ Set.range (a j).val.val).ncard) := by
  classical
  intro B Proper Parallel Arc rel Vertex Faces Complex ι inst a anchor k l
    hkl hcompatible hfinite hends hanchor0 hanchor1 hanchorFinite hpositive
  let : ClosedSurface S := Classical.choice hS.2.1
  have hBF : B ⊆ frontier F := by
    rw [hfrontier]
    exact Set.subset_union_left
  have regional_two_strata_ambient_image_equivalence (P Q : Set ↥F) :
      Equivalence (fun A B : Set ↥F => ∃ H : AmbientIsotopy ↥F,
        (∀ t, (fun y => H.map (t,y)) '' P = P) ∧
        (∀ t, (fun y => H.map (t,y)) '' Q = Q) ∧
        H.finalMap '' A = B) := by
    let zero : Interval := ⟨0,by norm_num⟩
    let one : Interval := ⟨1,by norm_num⟩
    let reverse : Interval → Interval := fun t =>
      ⟨1 - (t : ℝ), by constructor <;> linarith [t.property.1,t.property.2]⟩
    have reverse_cont : Continuous reverse :=
      (continuous_const.sub continuous_subtype_val).subtype_mk _
    have reverse_zero : reverse zero = one := Subtype.ext (by norm_num [reverse,zero,one])
    have reverse_one : reverse one = zero := Subtype.ext (by norm_num [reverse,zero,one])
    constructor
    · intro A
      refine ⟨{ map := ⟨fun p => p.2, continuous_snd⟩
                homeomorphism_at := fun _ => ⟨Homeomorph.refl ↥F,fun _ => rfl⟩
                at_zero := fun _ => rfl },?_,?_,?_⟩
      · intro t; exact Set.image_id P
      · intro t; exact Set.image_id Q
      · exact Set.image_id A
    · intro A B hab
      obtain ⟨H,hP,hQ,hH⟩ := hab
      obtain ⟨h,hh⟩ := H.homeomorphism_at one
      have hfinal : (h : ↥F → ↥F) = H.finalMap := funext hh
      let K : AmbientIsotopy ↥F := {
        map := ⟨fun p => H.map (reverse p.1,h.symm p.2), by
          exact H.map.continuous.comp
            ((reverse_cont.comp continuous_fst).prodMk
              (h.symm.continuous.comp continuous_snd))⟩
        homeomorphism_at := by
          intro t
          obtain ⟨g,hg⟩ := H.homeomorphism_at (reverse t)
          exact ⟨h.symm.trans g,fun y => hg (h.symm y)⟩
        at_zero := by
          intro y
          change H.map (reverse zero,h.symm y) = y
          rw [reverse_zero,←hh]
          exact h.apply_symm_apply y }
      have hpres (T : Set ↥F) (hT : ∀ t, (fun y => H.map (t,y)) '' T = T) :
          ∀ t, (fun y => K.map (t,y)) '' T = T := by
        have hTfinal : h '' T = T := by
          exact (congrArg (fun f : ↥F → ↥F => f '' T) (funext hh)).trans (hT one)
        have hTsymm : h.symm '' T = T := by
          calc
            h.symm '' T = h.symm '' (h '' T) := congrArg _ hTfinal.symm
            _ = T := by simp only [Set.image_image,Homeomorph.symm_apply_apply,Set.image_id']
        intro t
        change (fun y => H.map (reverse t,h.symm y)) '' T = T
        calc
          (fun y => H.map (reverse t,h.symm y)) '' T =
              (fun y => H.map (reverse t,y)) '' (h.symm '' T) :=
            (Set.image_image (fun y => H.map (reverse t,y)) h.symm T).symm
          _ = T := by rw [hTsymm,hT]
      refine ⟨K,hpres P hP,hpres Q hQ,?_⟩
      have hKfinal : K.finalMap = h.symm := by
        funext y
        change H.map (reverse one,h.symm y) = h.symm y
        rw [reverse_one]
        exact H.at_zero _
      rw [hKfinal,←hH,←hfinal]
      simp only [Set.image_image,Homeomorph.symm_apply_apply,Set.image_id']
    · intro A B C hab hbc
      obtain ⟨H,hHP,hHQ,hH⟩ := hab
      obtain ⟨K,hKP,hKQ,hK⟩ := hbc
      let L : AmbientIsotopy ↥F := {
        map := ⟨fun p => K.map (p.1,H.map (p.1,p.2)), by
          exact K.map.continuous.comp
            (continuous_fst.prodMk (H.map.continuous))⟩
        homeomorphism_at := by
          intro t
          obtain ⟨h,hh⟩ := H.homeomorphism_at t
          obtain ⟨k,hk⟩ := K.homeomorphism_at t
          exact ⟨h.trans k,fun y => by simp [Homeomorph.trans_apply,hh,hk]⟩
        at_zero := by
          intro y
          exact (congrArg (fun z => K.map (zero,z)) (H.at_zero y)).trans (K.at_zero y) }
      have hpres (T : Set ↥F)
          (hHT : ∀ t, (fun y => H.map (t,y)) '' T = T)
          (hKT : ∀ t, (fun y => K.map (t,y)) '' T = T) :
          ∀ t, (fun y => L.map (t,y)) '' T = T := by
        intro t
        change (fun y => K.map (t,H.map (t,y))) '' T = T
        calc
          (fun y => K.map (t,H.map (t,y))) '' T =
              (fun y => K.map (t,y)) '' ((fun y => H.map (t,y)) '' T) :=
            (Set.image_image (fun y => K.map (t,y)) (fun y => H.map (t,y)) T).symm
          _ = T := by rw [hHT,hKT]
      refine ⟨L,hpres P hHP hKP,hpres Q hHQ hKQ,?_⟩
      change (K.finalMap ∘ H.finalMap) '' A = C
      rw [Set.image_comp,hH,hK]
  have regional_proper_boundary_point_avoids_arc_range (F B : Set S) (hBF : B ⊆ frontier F)
      (a : C(Interval,↥F))
      (hproper : ∀ t ∈ Set.Ioo (0 : Interval) 1, (a t).val ∉ frontier F)
      (p : ↥F) (hp : p.val ∈ B) (hp0 : p ≠ a 0) (hp1 : p ≠ a 1) :
      p ∉ Set.range a := by
    rintro ⟨t,ht⟩
    have ht0 : t ≠ 0 := by intro he; exact hp0 (ht.symm.trans (congrArg a he))
    have ht1 : t ≠ 1 := by intro he; exact hp1 (ht.symm.trans (congrArg a he))
    exact hproper t ⟨bot_lt_iff_ne_bot.mpr ht0,lt_top_iff_ne_top.mpr ht1⟩ (ht ▸ hBF hp)
  
  have regional_positive_contact_has_interior_parameters (a b : C(Interval,↥F))
      (ha0 : a 0 ∉ Set.range b) (ha1 : a 1 ∉ Set.range b)
      (hb0 : b 0 ∉ Set.range a) (hb1 : b 1 ∉ Set.range a)
      (hpositive : 0 < (Set.range a ∩ Set.range b).ncard) :
      ∃ r s : Interval, r ∈ Set.Ioo (0 : Interval) 1 ∧
        s ∈ Set.Ioo (0 : Interval) 1 ∧ a r = b s := by
    obtain ⟨p,⟨r,hr⟩,s,hs⟩ := Set.nonempty_of_ncard_ne_zero (ne_of_gt hpositive)
    have hrs : a r = b s := hr.trans hs.symm
    have hr0 : r ≠ 0 := by intro he; exact ha0 ⟨s,hrs.symm.trans (congrArg a he)⟩
    have hr1 : r ≠ 1 := by intro he; exact ha1 ⟨s,hrs.symm.trans (congrArg a he)⟩
    have hs0 : s ≠ 0 := by intro he; exact hb0 ⟨r,hrs.trans (congrArg b he)⟩
    have hs1 : s ≠ 1 := by intro he; exact hb1 ⟨r,hrs.trans (congrArg b he)⟩
    exact ⟨r,s,⟨bot_lt_iff_ne_bot.mpr hr0,lt_top_iff_ne_top.mpr hr1⟩,
      ⟨bot_lt_iff_ne_bot.mpr hs0,lt_top_iff_ne_top.mpr hs1⟩,hrs⟩
  have regional_symmetric_ordered_energy_row_drop
      (A B : ι → ι → ℕ) (k : ι)
      (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
      (hAkk : A k k = 0) (hBkk : B k k = 0)
      (hfixed : ∀ i j, i ≠ k → j ≠ k → B i j = A i j)
      (hrow : (∑ j, B k j) < ∑ j, A k j) :
      (∑ i, ∑ j, B i j) < ∑ i, ∑ j, A i j := by
    have hdecomp (C : ι → ι → ℕ) (hCsym : ∀ i j, C i j = C j i)
        (hCkk : C k k = 0) :
        (∑ i, ∑ j, C i j) =
        2 * (∑ j, C k j) + ∑ i, ∑ j, if i = k ∨ j = k then 0 else C i j := by
      have hpoint (i j : ι) : C i j =
          (if i = k then C k j else 0) + (if j = k then C i k else 0) +
          (if i = k ∨ j = k then 0 else C i j) := by
        by_cases hi : i = k <;> by_cases hj : j = k <;> simp [hi,hj,hCkk]
      calc
        (∑ i, ∑ j, C i j) = ∑ i, ∑ j,
            ((if i = k then C k j else 0) + (if j = k then C i k else 0) +
            (if i = k ∨ j = k then 0 else C i j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact hpoint i j
        _ = (∑ j, C k j) + (∑ i, C i k) +
            ∑ i, ∑ j, if i = k ∨ j = k then 0 else C i j := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j => if i = k then C k j else 0)]
          simp
        _ = 2 * (∑ j, C k j) + ∑ i, ∑ j, if i = k ∨ j = k then 0 else C i j := by
          have hcols : (∑ i, C i k) = ∑ i, C k i := by
            apply Finset.sum_congr rfl
            intro i _
            exact hCsym i k
          rw [hcols]
          omega
    have hothers : (∑ i, ∑ j, if i = k ∨ j = k then 0 else B i j) =
        ∑ i, ∑ j, if i = k ∨ j = k then 0 else A i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with h
      · rfl
      · exact hfixed i j (fun hi => h (Or.inl hi)) (fun hj => h (Or.inr hj))
    rw [hdecomp A hAsym hAkk,hdecomp B hBsym hBkk,hothers]
    omega
  have ordinary_step (r : ι → Arc) (α : Arc)
      (hinv : RegionalTotalDecrease.FamilyInvariant (fun i => (r i).val.val) α.val.val)
      (hcross : ∀ i j : Option ι, i ≠ j →
        RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
          (RegionalTotalDecrease.augmented (fun i => (r i).val.val) α.val.val i)
          (RegionalTotalDecrease.augmented (fun i => (r i).val.val) α.val.val j))
      (v w : ι) (hvw : v ≠ w)
      (d : RegionalTotalDecrease.PairedBigonDisk F {y | y.val ∈ frontier F}
        (r v).val.val (r w).val.val)
      (V : Set ↥F) (hV : IsOpen V) (hdV : range d.disk ⊆ V)
      (hVinside : ∀ y ∈ closure V, y.val ∈ interior F)
      (havoid : Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ B}))
      (hcheap : (∑ j : ι, if j ≠ v ∧ j ≠ w then
        ((range d.second \ {d.first 0,d.first 1}) ∩ range (r j).val.val).ncard else 0) ≤
        ∑ j : ι, if j ≠ v ∧ j ≠ w then
        ((range d.first \ {d.first 0,d.first 1}) ∩ range (r j).val.val).ncard else 0) :
      ∃ b : ι → Arc,
        (∀ i, Quot.mk rel (b i) = Quot.mk rel (r i)) ∧
        RegionalTotalDecrease.FamilyInvariant (fun i => (b i).val.val) α.val.val ∧
        (∑ i : ι, ∑ j : ι, if i = j then 0 else
          (range (b i).val.val ∩ range (b j).val.val).ncard) <
        ∑ i : ι, ∑ j : ι, if i = j then 0 else
          (range (r i).val.val ∩ range (r j).val.val).ncard := by
    obtain ⟨H,houtsideMove,hfrontMove,hfiniteMove,hanchorMove,hrowMove,hpairMove⟩ :=
      regional_ordinary_disk_supported_movie_geometry S g hg hS x R hR htarget
        F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint
        hfrontier ι r α hinv hcross v w hvw d V hV hdV hVinside havoid hcheap
    obtain ⟨hcarrier,hfirstAnchor,hsecondAnchor,hpartition⟩ :=
      regional_paired_disk_finite_fan_carrier S g hg hS x R hR htarget
        F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint
        hfrontier ι r α hinv hcross v w hvw d V hV hdV hVinside havoid
    obtain ⟨e,he⟩ := H.homeomorphism_at (1 : Interval)
    have hfinal : (e : ↥F → ↥F) = H.finalMap := funext he
    have hpres (T : Set ↥F) (hT : ∀ y ∈ T, y.val ∈ frontier F) :
        ∀ t, (fun y => H.map (t,y)) '' T = T := by
      intro t
      apply Set.Subset.antisymm
      · rintro y ⟨z,hz,rfl⟩
        simpa only [hfrontMove t z (hT z hz)] using hz
      · intro y hy
        exact ⟨y,hy,hfrontMove t y (hT y hy)⟩
    have hpresB := hpres {y : ↥F | y.val ∈ B} (fun y hy => hBF hy)
    have hpresF := hpres {y : ↥F | y.val ∈ frontier F} (fun _ hy => hy)
    have hfix (y : ↥F) (hy : y.val ∈ frontier F) : e y = y :=
      (he y).trans (hfrontMove 1 y hy)
    let moved : C(Interval,↥F) :=
      ⟨fun t => e ((r v).val.val t), e.continuous.comp (r v).val.val.continuous⟩
    have hmovedRange : H.finalMap '' range (r v).val.val = range moved := by
      rw [← Set.range_comp]
      apply congrArg Set.range
      exact funext (fun t => (he ((r v).val.val t)).symm)
    have hmoved0 : moved 0 = (r v).val.val 0 :=
      hfix _ (hBF (r v).val.property.2.1)
    have hmoved1 : moved 1 = (r v).val.val 1 :=
      hfix _ (hBF (r v).val.property.2.2.1)
    have hmovedProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
        (moved t).val ∉ frontier F := by
      intro t ht hy
      have hh : e ((r v).val.val t) = (r v).val.val t :=
        e.injective (hfix (moved t) hy)
      exact (r v).val.property.2.2.2 t ht (hh ▸ hy)
    have hmovedEssential : ¬ Parallel
        ⟨moved,e.isEmbedding.comp (r v).val.property.1,
          hmoved0 ▸ (r v).val.property.2.1,
          hmoved1 ▸ (r v).val.property.2.2.1,hmovedProper⟩ :=
      (regional_essential_arc_ambient_transport F B (r v).val.val moved H
        (hpresB 1) hmovedRange).mp (r v).property
    let newArc : Arc := ⟨⟨moved,e.isEmbedding.comp (r v).val.property.1,
      hmoved0 ▸ (r v).val.property.2.1,
      hmoved1 ▸ (r v).val.property.2.2.1,hmovedProper⟩,hmovedEssential⟩
    let b : ι → Arc := Function.update r v newArc
    have hb0 (i : ι) : (b i).val.val 0 = (r i).val.val 0 := by
      by_cases hi : i = v
      · subst i; simpa only [b,Function.update_self,newArc] using hmoved0
      · simp only [b,Function.update_of_ne hi]
    have hb1 (i : ι) : (b i).val.val 1 = (r i).val.val 1 := by
      by_cases hi : i = v
      · subst i; simpa only [b,Function.update_self,newArc] using hmoved1
      · simp only [b,Function.update_of_ne hi]
    have hbClass (i : ι) : Quot.mk rel (b i) = Quot.mk rel (r i) := by
      by_cases hi : i = v
      · subst i
        simp only [b,Function.update_self]
        exact (Quot.sound (show rel (r v) newArc from
          ⟨H,hpresB,hpresF,hmovedRange⟩)).symm
      · simp only [b,Function.update_of_ne hi]
    have hbFinite : ∀ i j, i ≠ j →
        (range (b i).val.val ∩ range (b j).val.val).Finite := by
      intro i j hij
      by_cases hi : i = v
      · subst i
        have hj : j ≠ v := Ne.symm hij
        simpa only [b,Function.update_self,Function.update_of_ne hj,
          newArc,← hmovedRange] using hfiniteMove j hj
      · by_cases hj : j = v
        · subst j
          simp only [b,Function.update_self,Function.update_of_ne hi]
          change (range (r i).val.val ∩ range moved).Finite
          rw [Set.inter_comm,← hmovedRange]
          exact hfiniteMove i hi
        · simpa only [b,Function.update_of_ne hi,Function.update_of_ne hj]
            using hinv.1 i j hij
    have hbAvoid (p : ↥F) (hp : p.val ∈ B)
        (hpold : ∀ i, p ∉ range (r i).val.val) : ∀ i, p ∉ range (b i).val.val := by
      intro i
      by_cases hi : i = v
      · subst i
        simp only [b,Function.update_self]
        rintro ⟨t,ht⟩
        change e ((r v).val.val t) = p at ht
        have hh : (r v).val.val t = p := e.injective (ht.trans (hfix p (hBF hp)).symm)
        exact hpold v ⟨t,hh⟩
      · simpa only [b,Function.update_of_ne hi] using hpold i
    have hbAnchorFinite (i : ι) : (range α.val.val ∩ range (b i).val.val).Finite := by
      by_cases hi : i = v
      · subst i
        simp only [b,Function.update_self]
        change (range α.val.val ∩ range moved).Finite
        rw [Set.inter_comm,← hmovedRange]
        exact hanchorMove
      · simpa only [b,Function.update_of_ne hi] using hinv.2.2.2.2 i
    have hbInvariant : RegionalTotalDecrease.FamilyInvariant
        (fun i => (b i).val.val) α.val.val := by
      refine ⟨hbFinite,?_,?_,?_,hbAnchorFinite⟩
      · intro i j hij
        simpa only [hb0,hb1] using hinv.2.1 i j hij
      · exact hbAvoid _ α.val.property.2.1 hinv.2.2.1
      · exact hbAvoid _ α.val.property.2.2.1 hinv.2.2.2.1
    let oldRow (j : ι) : ℕ := (range (r v).val.val ∩ range (r j).val.val).ncard
    let newRow (j : ι) : ℕ := (H.finalMap '' range (r v).val.val ∩ range (r j).val.val).ncard
    let removed (j : ι) : ℕ := ((range d.first \ {d.first 0,d.first 1}) ∩ range (r j).val.val).ncard
    let guiding (j : ι) : ℕ := ((range d.second \ {d.first 0,d.first 1}) ∩ range (r j).val.val).ncard
    let offset (j : ι) : ℕ :=
      ((range (r v).val.val \ range d.first) ∩ range (r j).val.val).ncard +
      ({d.first 0,d.first 1} ∩ range (r j).val.val).ncard
    have htail : (∑ j : ι, if j ≠ v ∧ j ≠ w then newRow j else 0) ≤
        ∑ j : ι, if j ≠ v ∧ j ≠ w then oldRow j else 0 := by
      calc
        _ ≤ ∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j + offset j else 0 := by
          apply Finset.sum_le_sum
          intro j _
          split_ifs with hj
          · exact hrowMove j hj.1 hj.2
          · rfl
        _ = (∑ j : ι, if j ≠ v ∧ j ≠ w then guiding j else 0) +
            ∑ j : ι, if j ≠ v ∧ j ≠ w then offset j else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs <;> simp
        _ ≤ (∑ j : ι, if j ≠ v ∧ j ≠ w then removed j else 0) +
            ∑ j : ι, if j ≠ v ∧ j ≠ w then offset j else 0 :=
          Nat.add_le_add_right hcheap _
        _ = ∑ j : ι, if j ≠ v ∧ j ≠ w then oldRow j else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          split_ifs with hj
          · exact (hpartition j hj.1 hj.2).2.2.2.2.2.2.2.2.symm
          · simp
    have hsplit (f : ι → ℕ) :
        (∑ j : ι, if v = j then 0 else f j) =
          f w + ∑ j : ι, if j ≠ v ∧ j ≠ w then f j else 0 := by
      have hpoint (j : ι) : (if v = j then 0 else f j) =
          (if j = w then f w else 0) + (if j ≠ v ∧ j ≠ w then f j else 0) := by
        by_cases hjv : j = v
        · subst j; simp [hvw]
        · by_cases hjw : j = w
          · subst j; simp [hvw]
          · simp [hjv,Ne.symm hjv,hjw]
      simp_rw [hpoint]
      rw [Finset.sum_add_distrib]
      simp
    have hrow : (∑ j : ι, if v = j then 0 else newRow j) <
        ∑ j : ι, if v = j then 0 else oldRow j := by
      rw [hsplit newRow,hsplit oldRow]
      have hpair : newRow w + 2 ≤ oldRow w := hpairMove
      omega
    refine ⟨b,hbClass,hbInvariant,?_⟩
    apply regional_symmetric_ordered_energy_row_drop
      (fun i j => if i = j then 0 else (range (r i).val.val ∩ range (r j).val.val).ncard)
      (fun i j => if i = j then 0 else (range (b i).val.val ∩ range (b j).val.val).ncard) v
    · intro i j
      by_cases hij : i = j
      · subst j; rfl
      · simp only [hij,Ne.symm hij,ite_false]
        exact congrArg Set.ncard (Set.inter_comm _ _)
    · intro i j
      by_cases hij : i = j
      · subst j; rfl
      · simp only [hij,Ne.symm hij,ite_false]
        exact congrArg Set.ncard (Set.inter_comm _ _)
    · simp
    · simp
    · intro i j hi hj
      simp only [b,Function.update_of_ne hi,Function.update_of_ne hj]
    · convert hrow using 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : v = j
      · simp [hj]
      · simp only [hj,ite_false,b,Function.update_self,
          Function.update_of_ne (Ne.symm hj)]
        change (range moved ∩ range (r j).val.val).ncard = newRow j
        rw [← hmovedRange]
  have ordinary_orient (q : ι → Arc) (v w : ι) (hvw : v ≠ w)
      (d : RegionalTotalDecrease.PairedBigonDisk F {y | y.val ∈ frontier F}
        (q v).val.val (q w).val.val) :
      ∃ (v' w' : ι) (hvw' : v' ≠ w')
        (d' : RegionalTotalDecrease.PairedBigonDisk F {y | y.val ∈ frontier F}
          (q v').val.val (q w').val.val),
        d'.disk = d.disk ∧
        (∑ j : ι, if j ≠ v' ∧ j ≠ w' then
          ((range d'.second \ {d'.first 0,d'.first 1}) ∩ range (q j).val.val).ncard else 0) ≤
        ∑ j : ι, if j ≠ v' ∧ j ≠ w' then
          ((range d'.first \ {d'.first 0,d'.first 1}) ∩ range (q j).val.val).ncard else 0 := by
    rcases le_total
      (∑ j : ι, if j ≠ v ∧ j ≠ w then
        ((range d.second \ {d.first 0,d.first 1}) ∩ range (q j).val.val).ncard else 0)
      (∑ j : ι, if j ≠ v ∧ j ≠ w then
        ((range d.first \ {d.first 0,d.first 1}) ∩ range (q j).val.val).ncard else 0)
      with hcheap | hcheap
    · exact ⟨v,w,hvw,d,rfl,hcheap⟩
    · let ds : RegionalTotalDecrease.PairedBigonDisk F {y | y.val ∈ frontier F}
          (q w).val.val (q v).val.val := {
        first := d.second
        second := d.first
        first_embedded := d.second_embedded
        second_embedded := d.first_embedded
        aStart := d.bStart
        aFinish := d.bFinish
        bStart := d.aStart
        bFinish := d.aFinish
        a_distinct := d.b_distinct
        b_distinct := d.a_distinct
        first_eq := d.second_eq
        second_eq := d.first_eq
        zero_eq := d.zero_eq.symm
        one_eq := d.one_eq.symm
        corners_distinct := by rw [← d.zero_eq,← d.one_eq]; exact d.corners_distinct
        corners_off_frontier := ⟨d.zero_eq ▸ d.corners_off_frontier.1,
          d.one_eq ▸ d.corners_off_frontier.2⟩
        sides_inter := by rw [inter_comm,d.sides_inter,d.zero_eq,d.one_eq]
        disk := d.disk
        disk_embedded := d.disk_embedded
        boundary_image := d.boundary_image.trans (union_comm _ _)
        whole_first := d.whole_second
        whole_second := d.whole_first
        ambient_interior := d.ambient_interior
        strict_interior_clear := fun z hz => ⟨(d.strict_interior_clear z hz).2,
          (d.strict_interior_clear z hz).1⟩ }
      refine ⟨w,v,hvw.symm,ds,rfl,?_⟩
      simpa only [ds,← d.zero_eq,← d.one_eq,and_comm] using hcheap
  have half_orient (q : ι → Arc) (v w : ι) (hvw : v ≠ w)
      (d : RegionalTotalDecrease.PairedHalfBigonDisk F {y | y.val ∈ B}
        {y | y.val ∈ frontier F} (q v).val.val (q w).val.val) :
      ∃ (v' w' : ι) (hvw' : v' ≠ w')
        (d' : RegionalTotalDecrease.PairedHalfBigonDisk F {y | y.val ∈ B}
          {y | y.val ∈ frontier F} (q v').val.val (q w').val.val),
        d'.disk = d.disk ∧
        (∑ j : ι, if j ≠ v' ∧ j ≠ w' then
          ((range d'.second \ {d'.first 1}) ∩ range (q j).val.val).ncard else 0) ≤
        ∑ j : ι, if j ≠ v' ∧ j ≠ w' then
          ((range d'.first \ {d'.first 1}) ∩ range (q j).val.val).ncard else 0 := by
    rcases le_total
      (∑ j : ι, if j ≠ v ∧ j ≠ w then
        ((range d.second \ {d.first 1}) ∩ range (q j).val.val).ncard else 0)
      (∑ j : ι, if j ≠ v ∧ j ≠ w then
        ((range d.first \ {d.first 1}) ∩ range (q j).val.val).ncard else 0)
      with hcheap | hcheap
    · exact ⟨v,w,hvw,d,rfl,hcheap⟩
    · let revSide : C(Interval,↥F) :=
        ⟨fun t => d.boundarySide (unitInterval.symm t),
          d.boundarySide.continuous.comp unitInterval.continuous_symm⟩
      have hrevRange : range revSide = range d.boundarySide := by
        apply Subset.antisymm
        · rintro y ⟨t,rfl⟩; exact mem_range_self _
        · rintro y ⟨t,rfl⟩
          exact ⟨unitInterval.symm t,by simp [revSide]⟩
      let ds : RegionalTotalDecrease.PairedHalfBigonDisk F {y | y.val ∈ B}
          {y | y.val ∈ frontier F} (q w).val.val (q v).val.val := {
        first := d.second
        second := d.first
        boundarySide := revSide
        first_embedded := d.second_embedded
        second_embedded := d.first_embedded
        boundary_embedded := d.boundary_embedded.comp unitInterval.symmHomeomorph.isEmbedding
        aStart := d.bStart
        aFinish := d.bFinish
        bStart := d.aStart
        bFinish := d.aFinish
        a_distinct := d.b_distinct
        b_distinct := d.a_distinct
        first_eq := d.second_eq
        second_eq := d.first_eq
        first_zero := d.second_zero
        second_zero := d.first_zero
        boundary_endpoints_distinct := d.boundary_endpoints_distinct.symm
        corner_eq := d.corner_eq.symm
        corner_off_frontier := d.corner_eq ▸ d.corner_off_frontier
        first_interior := d.second_interior
        second_interior := d.first_interior
        boundary_in_B := fun t => d.boundary_in_B _
        boundary_zero := by simpa only [revSide,ContinuousMap.coe_mk,unitInterval.symm_zero] using d.boundary_one
        boundary_one := by simpa only [revSide,ContinuousMap.coe_mk,unitInterval.symm_one] using d.boundary_zero
        sides_inter := by rw [inter_comm,d.sides_inter,d.corner_eq]
        first_boundary_inter := by rw [hrevRange]; exact d.second_boundary_inter
        second_boundary_inter := by rw [hrevRange]; exact d.first_boundary_inter
        loop := d.loop
        loop_image := by rw [hrevRange,union_comm (range d.second) (range d.first)]; exact d.loop_image
        disk := d.disk
        disk_embedded := d.disk_embedded
        boundary_image := by rw [hrevRange,union_comm (range d.second) (range d.first)]; exact d.boundary_image
        whole_first := d.whole_second
        whole_second := d.whole_first
        whole_frontier := d.whole_frontier.trans hrevRange.symm
        strict_interior_clear := fun z hz => ⟨(d.strict_interior_clear z hz).2.1,
          (d.strict_interior_clear z hz).1,(d.strict_interior_clear z hz).2.2⟩ }
      refine ⟨w,v,hvw.symm,ds,rfl,?_⟩
      simpa only [ds,← d.corner_eq,and_comm] using hcheap
  have ordinary_support (u v : Arc)
      (d : RegionalTotalDecrease.PairedBigonDisk F {y | y.val ∈ frontier F}
        u.val.val v.val.val) :
      ∃ V : Set ↥F, IsOpen V ∧ range d.disk ⊆ V ∧
        (∀ y ∈ closure V, y.val ∈ interior F) ∧
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ B}) := by
    have hK : IsCompact (range d.disk) := isCompact_range d.disk.continuous
    have hO : IsOpen {y : ↥F | y.val ∈ interior F} :=
      isOpen_interior.preimage continuous_subtype_val
    obtain ⟨V,hV,hKV,hclV⟩ := hK.exists_isOpen_closure_subset
      (hO.mem_nhdsSet.mpr d.ambient_interior)
    refine ⟨V,hV,hKV,hclV,?_⟩
    apply disjoint_left.mpr
    intro y hy hyT
    exact disjoint_left.mp (disjoint_interior_frontier (s := F)) (hclV hy) hyT.1
  have half_support (u v : Arc)
      (d : RegionalTotalDecrease.PairedHalfBigonDisk F {y | y.val ∈ B}
        {y | y.val ∈ frontier F} u.val.val v.val.val) :
      ∃ V : Set ↥F, IsOpen V ∧ range d.disk ⊆ V ∧
        Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ B}) := by
    let other : Set ↥F := ⋃ j : J, {y : ↥F | y.val ∈ (c j).val.image}
    have hOtherEq : ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ B}) = other := by
      ext y
      constructor
      · rintro ⟨hyT,hyB⟩
        rw [hfrontier] at hyT
        rcases hyT with hy | hy
        · exact (hyB hy).elim
        · obtain ⟨j,hj⟩ := mem_iUnion.mp hy
          exact mem_iUnion.mpr ⟨j,hj⟩
      · intro hy
        obtain ⟨j,hj⟩ := mem_iUnion.mp hy
        refine ⟨?_,?_⟩
        · rw [hfrontier]; exact Or.inr (mem_iUnion.mpr ⟨j,hj⟩)
        · exact fun hyB => disjoint_left.mp (hbaseDisjoint j) hj hyB
    have hOtherClosed : IsClosed other := by
      apply isClosed_iUnion_of_finite
      intro j
      exact (isCompact_range (c j).val.embedded.continuous).isClosed.preimage continuous_subtype_val
    have hO : IsOpen otherᶜ := hOtherClosed.isOpen_compl
    have hKO : range d.disk ⊆ otherᶜ := by
      intro y hy hyOther
      have hyT : y ∈ {y : ↥F | y.val ∈ frontier F} := (hOtherEq.symm ▸ hyOther).1
      have hySide : y ∈ range d.boundarySide := d.whole_frontier ▸ ⟨hy,hyT⟩
      obtain ⟨t,rfl⟩ := hySide
      exact (hOtherEq.symm ▸ hyOther).2 (d.boundary_in_B t)
    have hK : IsCompact (range d.disk) := isCompact_range d.disk.continuous
    obtain ⟨V,hV,hKV,hclV⟩ := hK.exists_isOpen_closure_subset (hO.mem_nhdsSet.mpr hKO)
    refine ⟨V,hV,hKV,?_⟩
    rw [hOtherEq]
    exact disjoint_left.mpr (fun y hy hyOther => hclV hy hyOther)
  have hclassExact (u v : Arc) :
      Quot.mk rel u = Quot.mk rel v ↔ rel u v :=
    by
      rw [Quot.eq]
      exact ((regional_two_strata_ambient_image_equivalence
        {y : ↥F | y.val ∈ B} {y : ↥F | y.val ∈ frontier F}).comap
        (fun w : Arc => Set.range w.val.val)).eqvGen_iff
  by_cases hordinaryReady :
      ∃ (r : ι → Arc) (α : Arc),
        (∀ i, Quot.mk rel (r i) = Quot.mk rel (a i)) ∧
        Quot.mk rel α = Quot.mk rel anchor ∧
        RegionalTotalDecrease.FamilyInvariant (fun i => (r i).val.val) α.val.val ∧
        ((∑ i : ι, ∑ j : ι, if i = j then 0 else
          (range (r i).val.val ∩ range (r j).val.val).ncard) ≤
          ∑ i : ι, ∑ j : ι, if i = j then 0 else
          (range (a i).val.val ∩ range (a j).val.val).ncard) ∧
        (∀ i j : Option ι, i ≠ j →
          RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
            (RegionalTotalDecrease.augmented (fun i => (r i).val.val) α.val.val i)
            (RegionalTotalDecrease.augmented (fun i => (r i).val.val) α.val.val j)) ∧
        ∃ (v w : ι) (hvw : v ≠ w)
          (d : RegionalTotalDecrease.PairedBigonDisk F {y | y.val ∈ frontier F}
            (r v).val.val (r w).val.val) (V : Set ↥F),
          IsOpen V ∧ range d.disk ⊆ V ∧
          (∀ y ∈ closure V, y.val ∈ interior F) ∧
          Disjoint (closure V) ({y : ↥F | y.val ∈ frontier F} \ {y | y.val ∈ B}) ∧
          (∑ j : ι, if j ≠ v ∧ j ≠ w then
            ((range d.second \ {d.first 0,d.first 1}) ∩ range (r j).val.val).ncard else 0) ≤
          ∑ j : ι, if j ≠ v ∧ j ≠ w then
            ((range d.first \ {d.first 0,d.first 1}) ∩ range (r j).val.val).ncard else 0
  · obtain ⟨r,α,hrClass,hαClass,hrInv,hrEnergy,hcross,
      v,w,hvw,d,V,hV,hdV,hVinside,havoid,hcheap⟩ := hordinaryReady
    obtain ⟨b,hbClass,hbInv,hbEnergy⟩ :=
      ordinary_step r α hrInv hcross v w hvw d V hV hdV hVinside havoid hcheap
    exact ⟨b,α,(fun i => (hbClass i).trans (hrClass i)),hαClass,
      hbInv.1,hbInv.2.1,hbInv.2.2.1,hbInv.2.2.2.1,hbInv.2.2.2.2,
      lt_of_lt_of_le hbEnergy hrEnergy⟩
  ·
    have hInv : RegionalTotalDecrease.FamilyInvariant
        (fun i => (a i).val.val) anchor.val.val :=
      ⟨hfinite,hends,hanchor0,hanchor1,hanchorFinite⟩
    obtain ⟨r,α,Hr,Hα,hrMovie,hαMovie,hrFix,hαFix,hrEnds,hαEnds,
      hrClass,hαClass,hrInv,hrAugFinite,hcross,hcounts⟩ :=
      regional_finite_family_count_nonincreasing_crossing_normalization S g hg hS x R hR htarget
        F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint
        hfrontier ι a anchor hInv
    let oldC (i j : ι) : ℕ := if i = j then 0 else
      (range (a i).val.val ∩ range (a j).val.val).ncard
    let newC (i j : ι) : ℕ := if i = j then 0 else
      (range (r i).val.val ∩ range (r j).val.val).ncard
    have hpointLe (i j : ι) : newC i j ≤ oldC i j := by
      by_cases hij : i = j
      · subst j; simp [oldC,newC]
      · simp only [oldC,newC,hij,ite_false]
        exact hcounts (some i) (some j) (fun h => hij (Option.some.inj h))
    have hrowLe (i : ι) : (∑ j : ι, newC i j) ≤ ∑ j : ι, oldC i j :=
      Finset.sum_le_sum (fun j _ => hpointLe i j)
    have hrEnergy : (∑ i : ι, ∑ j : ι, newC i j) ≤
        ∑ i : ι, ∑ j : ι, oldC i j :=
      Finset.sum_le_sum (fun i _ => hrowLe i)
    by_cases hstrict : (∑ i : ι, ∑ j : ι, newC i j) <
        ∑ i : ι, ∑ j : ι, oldC i j
    · exact ⟨r,α,hrClass,hαClass,hrInv.1,hrInv.2.1,hrInv.2.2.1,
        hrInv.2.2.2.1,hrInv.2.2.2.2,hstrict⟩
    have henergyEq : (∑ i : ι, ∑ j : ι, newC i j) =
        ∑ i : ι, ∑ j : ι, oldC i j :=
      le_antisymm hrEnergy (Nat.le_of_not_gt hstrict)
    have hrowEq : (∑ j : ι, newC k j) = ∑ j : ι, oldC k j :=
      (Finset.sum_eq_sum_iff_of_le (fun i _ => hrowLe i)).mp henergyEq k (Finset.mem_univ k)
    have hselectedEq : (range (r k).val.val ∩ range (r l).val.val).ncard =
        (range (a k).val.val ∩ range (a l).val.val).ncard := by
      have he := (Finset.sum_eq_sum_iff_of_le (fun j _ => hpointLe k j)).mp
        hrowEq l (Finset.mem_univ l)
      simpa only [newC,oldC,hkl,ite_false] using he
    have hrPositive : 0 < (range (r k).val.val ∩ range (r l).val.val).ncard := by
      rw [hselectedEq]
      exact hpositive
    have hrCompatible : ∃ u v : Arc,
        Quot.mk rel u = Quot.mk rel (r k) ∧
        Quot.mk rel v = Quot.mk rel (r l) ∧
        Disjoint (range u.val.val) (range v.val.val) := by
      obtain ⟨u,v,hu,hv,huv⟩ := hcompatible
      exact ⟨u,v,hu.trans (hrClass k).symm,hv.trans (hrClass l).symm,huv⟩
    obtain ⟨u,v,hu,hv,huv⟩ := hrCompatible
    obtain ⟨H,hHB,hHF,hmove⟩ := (hclassExact u (r k)).mp hu
    obtain ⟨e,he⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hfinal : (e : ↥F → ↥F) = H.finalMap := funext he
    let moved : C(Interval,↥F) :=
      ⟨fun t => e (v.val.val t),e.continuous.comp v.val.val.continuous⟩
    have hMoved : H.finalMap '' Set.range v.val.val = Set.range moved := by
      rw [←Set.range_comp]
      apply congrArg Set.range
      funext t
      exact (he (v.val.val t)).symm
    have hBFinal : e '' {y : ↥F | y.val ∈ B} = {y : ↥F | y.val ∈ B} := by
      rw [hfinal]
      exact hHB ⟨1,by norm_num⟩
    have hFFinal : e '' {y : ↥F | y.val ∈ frontier F} =
        {y : ↥F | y.val ∈ frontier F} := by
      rw [hfinal]
      exact hHF ⟨1,by norm_num⟩
    have hmoved0 : (moved ⟨0,by norm_num⟩).val ∈ B := by
      have hh : e (v.val.val ⟨0,by norm_num⟩) ∈
          e '' {y : ↥F | y.val ∈ B} := ⟨_,v.val.property.2.1,rfl⟩
      rw [hBFinal] at hh
      exact hh
    have hmoved1 : (moved ⟨1,by norm_num⟩).val ∈ B := by
      have hh : e (v.val.val ⟨1,by norm_num⟩) ∈
          e '' {y : ↥F | y.val ∈ B} := ⟨_,v.val.property.2.2.1,rfl⟩
      rw [hBFinal] at hh
      exact hh
    have hmovedProper : ∀ t ∈ Set.Ioo (0 : Interval) 1,
        (moved t).val ∉ frontier F := by
      intro t ht hh
      have hh' : e (v.val.val t) ∈ e '' {y : ↥F | y.val ∈ frontier F} :=
        hFFinal.symm ▸ hh
      obtain ⟨y,hy,hye⟩ := hh'
      exact v.val.property.2.2.2 t ht (e.injective hye ▸ hy)
    have hmovedEssential : ¬ ∃ b : C(Interval,↥F), Topology.IsEmbedding b ∧
        (∀ t, (b t).val ∈ B) ∧
        ∃ d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,↥F),
          Topology.IsEmbedding d ∧
          d '' {z | z.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} =
            Set.range moved ∪ Set.range b :=
      (regional_essential_arc_ambient_transport F B v.val.val moved H
        (hHB ⟨1,by norm_num⟩) hMoved).mp v.property
    let comparison : Arc := ⟨⟨moved,e.isEmbedding.comp v.val.property.1,
      hmoved0,hmoved1,hmovedProper⟩,hmovedEssential⟩
    have hcomparisonClass : Quot.mk rel comparison = Quot.mk rel (r l) :=
      (Quot.sound (show rel v comparison from ⟨H,hHB,hHF,hMoved⟩)).symm.trans hv
    have hcomparisonDisjoint :
        Disjoint (Set.range (r k).val.val) (Set.range comparison.val.val) := by
      apply Set.disjoint_left.mpr
      intro y hyk hyv
      have hyu : y ∈ e '' Set.range u.val.val := by
        rw [hfinal,hmove]
        exact hyk
      obtain ⟨p,hpu,hpe⟩ := hyu
      obtain ⟨t,ht⟩ := hyv
      have hpv : p = v.val.val t := e.injective (hpe.trans ht.symm)
      exact Set.disjoint_left.mp huv hpu (hpv.symm ▸ Set.mem_range_self t)
    obtain ⟨K,hKB,hKF,hKmove⟩ :=
      (hclassExact (r l) comparison).mp hcomparisonClass.symm
    have hcomparisonMovie : RegionalTotalDecrease.ClassMovie
        {y : ↥F | y.val ∈ B} {y : ↥F | y.val ∈ frontier F}
        (r l).val.val comparison.val.val K := ⟨hKB,hKF,hKmove⟩
    have hselectedCross : RegionalEmbeddedFamily.RegionalAllInteriorContactsCross F
        (r k).val.val (r l).val.val :=
      hcross (some k) (some l) (fun he => hkl (Option.some.inj he))
    have hnullBoundary :=
      regional_compatible_crossing_pair_has_F_null_boundary S g hg hS x R hR htarget
        F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint
        hfrontier (r k) (r l) comparison (hrInv.2.1 k l hkl)
        (hrInv.1 k l hkl) hrPositive hselectedCross K hcomparisonMovie hcomparisonDisjoint
    have hpairedCleanDisk :
        Nonempty (RegionalTotalDecrease.PairedBigonDisk F {y | y.val ∈ frontier F}
          (r k).val.val (r l).val.val) ∨
        Nonempty (RegionalTotalDecrease.PairedHalfBigonDisk F {y | y.val ∈ B}
          {y | y.val ∈ frontier F} (r k).val.val (r l).val.val) := by
      exact regional_F_null_boundary_has_paired_clean_disk S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier (r k) (r l) (hrInv.2.1 k l hkl) (hrInv.1 k l hkl) hselectedCross hnullBoundary
    rcases hpairedCleanDisk with hd | hd
    · obtain ⟨d⟩ := hd
      obtain ⟨v,w,hvw,ds,hSameDisk,hcheap⟩ := ordinary_orient r k l hkl d
      obtain ⟨V,hV,hdV,hVinside,havoid⟩ := ordinary_support (r v) (r w) ds
      exact (hordinaryReady ⟨r,α,hrClass,hαClass,hrInv,hrEnergy,hcross,
        v,w,hvw,ds,V,hV,hdV,hVinside,havoid,hcheap⟩).elim
    · obtain ⟨d⟩ := hd
      obtain ⟨v,w,hvw,ds,hSameDisk,hcheap⟩ := half_orient r k l hkl d
      obtain ⟨V,hV,hdV,havoid⟩ := half_support (r v) (r w) ds
      let C₀ : Set ↥F := {ds.first 1}
      let removed := fun j : ι => ((range ds.first \ C₀) ∩ range (r j).val.val).ncard
      let guiding := fun j : ι => ((range ds.second \ C₀) ∩ range (r j).val.val).ncard
      let offset := fun j : ι =>
        ((range (r v).val.val \ range ds.first) ∩ range (r j).val.val).ncard +
          (C₀ ∩ range (r j).val.val).ncard
      have hhalfReplacement :
        ∃ (q : Arc) (H : AmbientIsotopy ↥F),
          RegionalTotalDecrease.ClassMovie {y | y.val ∈ B} {y | y.val ∈ frontier F}
            (r v).val.val q.val.val H ∧
          (∀ t y, y ∉ V → H.map (t,y) = y) ∧
          Quot.mk rel q = Quot.mk rel (r v) ∧
          RegionalTotalDecrease.FamilyInvariant (fun j => (Function.update r v q j).val.val) α.val.val ∧
          (∀ j, j ≠ v → (range q.val.val ∩ range (r j).val.val).Finite) ∧
          (range q.val.val ∩ range α.val.val).Finite ∧
          (∀ j, j ≠ v → j ≠ w →
            ((range ds.first \ C₀) ∩ range (r j).val.val).Finite ∧
            ((range ds.second \ C₀) ∩ range (r j).val.val).Finite ∧
            ((range (r v).val.val \ range ds.first) ∩ range (r j).val.val).Finite ∧
            (C₀ ∩ range (r j).val.val).Finite ∧
            (range (r v).val.val ∩ range (r j).val.val).ncard = removed j + offset j ∧
            (range q.val.val ∩ range (r j).val.val).ncard ≤ guiding j + offset j) ∧
          (range q.val.val ∩ range (r w).val.val).ncard + 1 ≤
            (range (r v).val.val ∩ range (r w).val.val).ncard ∧
          (∑ j : ι, if v = j then 0 else
            (range q.val.val ∩ range (r j).val.val).ncard) <
            (∑ j : ι, if v = j then 0 else
              (range (r v).val.val ∩ range (r j).val.val).ncard) := by
        exact regional_weighted_paired_half_bigon_replacement S g hg hS x R hR htarget F hFcompact hFconnected hbase houtside hregular J c hdisjoint hbaseDisjoint hfrontier ι r α hrInv hcross v w hvw ds V hV hdV havoid hcheap
      obtain ⟨q,H,hMovie,hOutside,hqClass,hbInv,hqFinite,hqAnchorFinite,
        hrowBounds,hselectedDrop,hrowDrop⟩ := hhalfReplacement
      let b : ι → Arc := Function.update r v q
      have hbClass (i : ι) : Quot.mk rel (b i) = Quot.mk rel (a i) := by
        by_cases hi : i = v
        · subst i
          simpa only [b,Function.update_self] using hqClass.trans (hrClass v)
        · simpa only [b,Function.update_of_ne hi] using hrClass i
      have hbEnergy : (∑ i : ι, ∑ j : ι, if i = j then 0 else
          (range (b i).val.val ∩ range (b j).val.val).ncard) <
          ∑ i : ι, ∑ j : ι, if i = j then 0 else
          (range (r i).val.val ∩ range (r j).val.val).ncard := by
        apply regional_symmetric_ordered_energy_row_drop
          (fun i j => if i = j then 0 else (range (r i).val.val ∩ range (r j).val.val).ncard)
          (fun i j => if i = j then 0 else (range (b i).val.val ∩ range (b j).val.val).ncard) v
        · intro i j
          by_cases hij : i = j
          · subst j; rfl
          · simp only [hij,Ne.symm hij,ite_false]
            exact congrArg Set.ncard (Set.inter_comm _ _)
        · intro i j
          by_cases hij : i = j
          · subst j; rfl
          · simp only [hij,Ne.symm hij,ite_false]
            exact congrArg Set.ncard (Set.inter_comm _ _)
        · simp
        · simp
        · intro i j hi hj
          simp only [b,Function.update_of_ne hi,Function.update_of_ne hj]
        · convert hrowDrop using 1
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : v = j
          · simp [hj]
          · simp only [hj,ite_false,b,Function.update_self,Function.update_of_ne (Ne.symm hj)]
      exact ⟨b,α,hbClass,hαClass,hbInv.1,hbInv.2.1,hbInv.2.2.1,
        hbInv.2.2.2.1,hbInv.2.2.2.2,lt_of_lt_of_le hbEnergy hrEnergy⟩
