import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.OriginalFinitePositionSourceConsumer
import CurveComplexGenusTwo.Dictionary.Circle33CanonicalEssential
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import CurveComplexGenusTwo.Topology.WeightedSurgery.RawSpliceHelperHeaders
import CurveComplexGenusTwo.Topology.Smoothing.FiniteSupportedPatchAssemblyProof
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlidePlane
import CurveComplexGenusTwo.Topology.IntersectionParity.CutTransition
import Mathlib.Topology.Order.IntermediateValue
import Schoenflies.Subarc
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.CompletedJordan
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import Schoenflies.ModelCurve
import Schoenflies.JordanSchoenflies
import Mathlib.Topology.MetricSpace.HausdorffDistance
import CurveComplexGenusTwo.Topology.ActualArcSurgery.ActualOriginalOutermostSurgeryProof
import CurveComplexGenusTwo.Filtration.ConeChains
import CurveComplexGenusTwo.Filtration.CarriedFilling
open Set Topology Schoenflies Metric Filter
open CurveComplex
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CurveComplex.HyperellipticModel
namespace ArcSurgery
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance pendingConsumerDecidableEq (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

theorem position_count_eq_intrinsic (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (v : {v // v ∈ F}) :
    (crossings M anchor (P.rep v)).ncard = intersectionNumber M anchor v.val := by
  apply le_antisymm
  · apply le_csInf
    · exact ⟨_, P.rep v, P.represents v, P.finite v, rfl⟩
    · rintro n ⟨b, hb, hf, rfl⟩
      exact P.minimal v b hb hf
  · exact Nat.sInf_le ⟨P.rep v, P.represents v, P.finite v, rfl⟩

theorem firstCrossing_exists (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F)
    (h : ∃ v, (crossings M anchor (P.rep v)).Nonempty) :
    Nonempty (FirstCrossing M anchor F P) := by
  classical
  let C : Set S := ⋃ v, crossings M anchor (P.rep v)
  have hC : C.Finite := Set.finite_iUnion fun v => P.finite v
  have hnot : ∀ p ∈ C, p ∉ (M.cover.branch : Set S) := by
    intro p hp
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hp
    exact hv.1.2
  have hI : Set.InjOn anchor.val.map (anchor.val.map ⁻¹' C) := by
    intro t ht u hu he
    rcases anchor.val.injective_except_loop_closure t u he with he | he | he
    · exact he
    · exact False.elim (hnot _ ht (he.1 ▸ anchor.val.start_marked))
    · exact False.elim (hnot _ ht (he.1 ▸ anchor.val.end_marked))
  have hT : (anchor.val.map ⁻¹' C).Finite := hC.preimage hI
  have hne : (anchor.val.map ⁻¹' C).Nonempty := by
    obtain ⟨v, p, hp⟩ := h
    obtain ⟨t, ht⟩ := hp.1.1
    exact ⟨t, Set.mem_iUnion.mpr ⟨v, ht ▸ hp⟩⟩
  obtain ⟨t, ht, hmin⟩ := hT.exists_minimal hne
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp ht
  obtain ⟨s, hs⟩ := hv.2.1
  have interior : ∀ (a : MarkedArc M) (r : Interval),
      a.map r ∉ (M.cover.branch : Set S) → 0 < r.val ∧ r.val < 1 := by
    intro a r hr
    constructor
    · have hz : r ≠ ⟨0, by norm_num⟩ := by
        intro he
        exact hr (he ▸ a.start_marked)
      have : r.val ≠ 0 := by intro he; exact hz (Subtype.ext he)
      exact lt_of_le_of_ne r.property.1 (Ne.symm this)
    · have hz : r ≠ ⟨1, by norm_num⟩ := by
        intro he
        exact hr (he ▸ a.end_marked)
      have : r.val ≠ 1 := by intro he; exact hz (Subtype.ext he)
      exact lt_of_le_of_ne r.property.2 this
  refine ⟨⟨v, t, s, interior anchor.val t hv.1.2,
    interior (P.rep v).val s (hs ▸ hv.2.2), hs.symm, ?_⟩⟩
  intro w r hr hrt hmem
  have hrnot : anchor.val.map r ∉ (M.cover.branch : Set S) := hmem.2
  have hrC : r ∈ anchor.val.map ⁻¹' C := by
    exact Set.mem_iUnion.mpr ⟨w, ⟨⟨⟨r, rfl⟩, hrnot⟩, hmem⟩⟩
  have he : t ≤ r := hmin hrC (le_of_lt hrt)
  exact (not_lt_of_ge he) hrt

/-- Termination on intrinsic class complexity after discarding duplicate classes.
This is the well-founded measure for a finite sequence of surgeries. -/
theorem surgery_complexity_decreases (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
    (P : FinitePosition M anchor F) (x : FirstCrossing M anchor F P)
    (R : SurgeryPair M anchor F P x) :
    complexity M anchor (F.erase x.selected.val ∪ replacementClasses M anchor F P x R) <
      complexity M anchor F := by
  classical
  let f := intersectionNumber M anchor
  have hnew : (∑ v ∈ replacementClasses M anchor F P x R, f v) < f x.selected.val := by
    calc
      _ ≤ ∑ side ∈ R.retained.attach, f (vertex M (R.pushed side)) :=
        Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
      _ ≤ ∑ side ∈ R.retained.attach, (crossings M anchor (R.pushed side)).ncard := by
        apply Finset.sum_le_sum
        intro side hside
        apply csInf_le (OrderBot.bddBelow _)
        exact ⟨R.pushed side, rfl, R.finite side, rfl⟩
      _ < (crossings M anchor (P.rep x.selected)).ncard := R.total_decreases
      _ = f x.selected.val := position_count_eq_intrinsic M anchor F P x.selected
  have he := Finset.sum_erase_add F f x.selected.property
  have hu := Finset.sum_sdiff (f := f)
    (Finset.subset_union_left : F.erase x.selected.val ⊆
      F.erase x.selected.val ∪ replacementClasses M anchor F P x R)
  rw [Finset.union_sdiff_left] at hu
  have hs := Finset.sum_le_sum_of_subset (f := f)
    (Finset.sdiff_subset : replacementClasses M anchor F P x R \ F.erase x.selected.val ⊆ _)
  unfold complexity
  change (∑ v ∈ F.erase x.selected.val ∪ replacementClasses M anchor F P x R, f v) < ∑ v ∈ F, f v
  omega

theorem finiteContraction_exists (M : HyperellipticModel E S)
    (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M)) :
    Nonempty (FiniteContraction M anchor F)  := by
  classical
  have down {τ υ : Finset (EssentialArcClass M)} (hsub : τ ⊆ υ)
      (hυ : IsArcSimplex M υ) : IsArcSimplex M τ := by
    obtain ⟨rep, hrep, hdisj⟩ := hυ
    refine ⟨fun v => rep ⟨v.val, hsub v.property⟩, fun v => hrep _, ?_⟩
    intro v w hne
    apply hdisj
    exact fun he => hne (Subtype.ext (Subtype.mk.inj he))
  suffices ∀ n F, complexity M anchor F = n → Nonempty (FiniteContraction M anchor F) by
    exact this _ F rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro F hn
    obtain ⟨P⟩ := finitePosition_exists M anchor F
    by_cases hc : ∃ v, (crossings M anchor (P.rep v)).Nonempty
    · obtain ⟨x⟩ := firstCrossing_exists M anchor F P hc
      obtain ⟨R⟩ := outermostSurgery_exists M anchor F P x
      let G := F.erase x.selected.val ∪ replacementClasses M anchor F P x R
      have hdec : complexity M anchor G < n := by
        rw [← hn]
        exact surgery_complexity_decreases M anchor F P x R
      obtain ⟨C⟩ := ih (complexity M anchor G) hdec G rfl
      obtain ⟨b, hb⟩ := R.nonempty
      let newv := vertex M (R.pushed ⟨b, hb⟩)
      let step (v : EssentialArcClass M) := if v = x.selected.val then newv else v
      have hnew : newv ∈ replacementClasses M anchor F P x R :=
        Finset.mem_image.mpr ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩
      have hsupport (σ : Finset (EssentialArcClass M)) (hF : σ ⊆ F) : σ.image step ⊆ G := by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        by_cases he : w = x.selected.val
        · simp only [step, if_pos he]
          exact Finset.mem_union_right _ hnew
        · simp only [step, if_neg he]
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hF hw⟩)
      have hcont (σ : Finset (EssentialArcClass M)) (hF : σ ⊆ F)
          (hσ : IsArcSimplex M σ) : IsArcSimplex M (σ ∪ σ.image step) := by
        by_cases hx : x.selected.val ∈ σ
        · apply down _ (surgery_common_simplex M anchor F P x R σ hF hσ hx)
          intro v hv
          rcases Finset.mem_union.mp hv with hv | hv
          · exact Finset.mem_union_left _ hv
          · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
            by_cases he : w = x.selected.val
            · simp only [step, if_pos he]
              exact Finset.mem_union_right _ hnew
            · simp only [step, if_neg he]
              exact Finset.mem_union_left _ hw
        · have he : σ.image step = σ := by
            calc
              σ.image step = σ.image id := by
                apply Finset.image_congr
                intro v hv
                simp [step, show v ≠ x.selected.val from fun h => hx (h ▸ hv)]
              _ = σ := Finset.image_id
          simpa [he] using hσ
      have hsimp (σ : Finset (EssentialArcClass M)) (hF : σ ⊆ F)
          (hσ : IsArcSimplex M σ) : IsArcSimplex M (σ.image step) :=
        down Finset.subset_union_right (hcont σ hF hσ)
      refine ⟨{
        stages := C.stages + 1
        map := Fin.cases id (fun j v => C.map j (step v))
        starts := ?_
        simplicial := ?_
        contiguous := ?_
        ends_in_star := ?_ }⟩
      · intro v hv
        rfl
      · intro i σ hF hσ
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hσ
        · simpa only [Fin.cases_succ, Finset.image_image, Function.comp_def] using
            C.simplicial j (σ.image step) (hsupport σ hF) (hsimp σ hF hσ)
      · intro i hi σ hF hσ
        cases i with
        | zero =>
          change IsArcSimplex M (σ.image id ∪
            σ.image (fun v => C.map ⟨0, by omega⟩ (step v)))
          have he : σ.image (fun v => C.map ⟨0, by omega⟩ (step v)) = σ.image step := by
            apply Finset.image_congr
            intro v hv
            exact C.starts (step v) (hsupport σ hF (Finset.mem_image.mpr ⟨v, hv, rfl⟩))
          simpa only [he, Finset.image_id] using hcont σ hF hσ
        | succ j =>
          change IsArcSimplex M
            (σ.image (fun v => C.map ⟨j, by omega⟩ (step v)) ∪
             σ.image (fun v => C.map ⟨j + 1, by omega⟩ (step v)))
          simpa only [Finset.image_image, Function.comp_def] using
            C.contiguous j (by omega) (σ.image step) (hsupport σ hF) (hsimp σ hF hσ)
      · intro σ hF hσ
        change IsArcSimplex M (insert (vertex M anchor)
          (σ.image (fun v => C.map ⟨C.stages, by omega⟩ (step v))))
        simpa only [Finset.image_image, Function.comp_def] using
          C.ends_in_star (σ.image step) (hsupport σ hF) (hsimp σ hF hσ)
    · have hz (v : {v // v ∈ F}) :
          Disjoint (arcInterior M anchor) (arcInterior M (P.rep v)) := by
        rw [Set.disjoint_iff_inter_eq_empty]
        exact Set.not_nonempty_iff_eq_empty.mp (fun hv => hc ⟨v, hv⟩)
      refine ⟨{
        stages := 0
        map := fun _ v => v
        starts := fun _ _ => rfl
        simplicial := ?_
        contiguous := ?_
        ends_in_star := ?_ }⟩
      · intro i σ hF hσ
        simpa using hσ
      · intro i hi
        omega
      · intro σ hF hσ
        simp only [Finset.image_id']
        let T := insert (vertex M anchor) σ
        have old (v : {v // v ∈ T}) (hv : v.val ≠ vertex M anchor) : v.val ∈ σ :=
          (Finset.mem_insert.mp v.property).resolve_left hv
        let rep (v : {v // v ∈ T}) : EssentialMarkedArc M :=
          if hv : v.val = vertex M anchor then anchor else P.rep ⟨v.val, hF (old v hv)⟩
        refine ⟨rep, ?_, ?_⟩
        · intro v
          by_cases hv : v.val = vertex M anchor
          · simpa [rep, hv, vertex]
          · simpa [rep, hv, vertex] using P.represents ⟨v.val, hF (old v hv)⟩
        · intro v w hvw
          have hval : v.val ≠ w.val := fun h => hvw (Subtype.ext h)
          by_cases hv : v.val = vertex M anchor <;> by_cases hw : w.val = vertex M anchor
          · exact False.elim (hval (hv.trans hw.symm))
          · simp only [rep, dite_eq_left hv, dite_eq_right hw]
            exact hz ⟨w.val, hF (old w hw)⟩
          · simp only [rep, dite_eq_right hv, dite_eq_left hw]
            exact (hz ⟨v.val, hF (old v hv)⟩).symm
          · simp only [rep, dite_eq_right hv, dite_eq_right hw]
            apply P.simplex_disjoint
            · exact fun h => hval (Subtype.mk.inj h)
            · apply down _ hσ
              intro q hq
              simp only [Finset.mem_insert, Finset.mem_singleton] at hq
              rcases hq with hq | hq
              · simpa [hq] using old v hv
              · simpa [hq] using old w hw


theorem essentialAnchor_exists (M : HyperellipticModel E S) :
  Nonempty (EssentialMarkedArc M) := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp
    (show 1 < M.cover.branch.card by rw [M.cover.branch_card]; norm_num)
  have hconn : IsConnected (Set.univ : Set S) := by
    letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Subtype.connectedSpace (isConnected_sphere
        (E := EuclideanSpace ℝ (Fin 3)) (by
          rw [← Module.finrank_eq_rank]
          norm_num)
        0 (r := 1) (by norm_num))
    have hc := isConnected_univ.image M.sphere.symm M.sphere.symm.continuous.continuousOn
    simpa only [Set.image_univ, M.sphere.symm.surjective.range_eq] using hc
  obtain ⟨a, _⟩ := nonloop_arc_inside_marked_region M Set.univ
    isOpen_univ hconn p q hp hq (Set.mem_univ _) (Set.mem_univ _) hpq
  exact ⟨⟨a.val, Or.inl a.property⟩⟩
theorem actualArc_cycle_fills (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)] (n : ℤ)
    (z : chains (actualA M) n) (hz : boundary (actualA M) n z = 0) :
    ∃ b : chains (actualA M) (n + 1),
      (show n + 1 - 1 = n from by omega) ▸
        boundary (actualA M) (n + 1) b = z  := by
  classical
  -- Inline copy of the checked approved bridge avoids an import cycle.
  have fill_supported :
      letI : DecidableEq (EssentialArcClass M) := LinearOrder.toDecidableEq
      ∀ (anchor : EssentialMarkedArc M) (F : Finset (EssentialArcClass M))
        (C : FiniteContraction M anchor F) (n : ℤ) (z : chains (actualA M) n),
        boundary (actualA M) n z = 0 →
        (∀ σ ∈ (FreeAbelianGroup.toFinsupp z).support, σ.val ⊆ F) →
        ∃ b : chains (actualA M) (n + 1),
          (show n + 1 - 1 = n by omega) ▸ boundary (actualA M) (n + 1) b = z := by
    intro anchor F C n z hz hsupport
    classical
    letI : DecidableEq (EssentialArcClass M) := LinearOrder.toDecidableEq
    have coneFill (K L : FiniteComplex (EssentialArcClass M))
        (hLK : L.simplices ⊆ K.simplices) (hcone : IsNonemptyCone L)
        (q : ℤ) (hq : 0 ≤ q) (c : chains K (q - 1))
        (hc : boundary K (q - 1) c = 0)
        (hcarried : c ∈ (chainInclusion L K hLK (q - 1)).range) :
        ∃ d : chains L q, boundary K q (chainInclusion L K hLK q d) = c := by
      obtain ⟨a, ha⟩ := hcarried
      have haCycle : a ∈ cycles L (q - 1) := by
        change boundary L (q - 1) a = 0
        apply carrierChainInclusion_injective L K hLK (q - 1 - 1)
        have hcomm := DFunLike.congr_fun (chainInclusion_boundary L K hLK (q - 1)) a
        change boundary K (q - 1) (chainInclusion L K hLK (q - 1) a) =
          chainInclusion L K hLK (q - 1 - 1) (boundary L (q - 1) a) at hcomm
        rw [ha, hc] at hcomm
        simpa only [map_zero] using hcomm.symm
      letI := nonemptyCone_reducedHomology L hcone (q - 1) (by omega)
      have hzero : (QuotientAddGroup.mk ⟨a, haCycle⟩ : reducedHomology L (q - 1)) = 0 :=
        Subsingleton.elim _ _
      have hb : a ∈ boundaries L (q - 1) :=
        (QuotientAddGroup.eq_zero_iff (⟨a, haCycle⟩ : cycles L (q - 1))).mp hzero
      have hb' : a ∈ (boundary L q).range := by
        change a ∈ boundaries L (q - 1) at hb
        have aux (i j : ℤ) (e : i = j) :
            Eq.mp (congrArg (fun m => AddSubgroup (chains L (m - 1))) e)
              (boundary L i).range = (boundary L j).range := by
          cases e
          rfl
        have he : boundaries L (q - 1) = (boundary L q).range :=
          aux (q - 1 + 1) q (by omega)
        rw [he] at hb
        exact hb
      obtain ⟨d, hd⟩ := hb'
      refine ⟨d, ?_⟩
      have hcomm := DFunLike.congr_fun (chainInclusion_boundary L K hLK q) d
      change boundary K q (chainInclusion L K hLK q d) =
        chainInclusion L K hLK (q - 1) (boundary L q d) at hcomm
      rw [hd, ha] at hcomm
      exact hcomm
    have extend (A B : FiniteComplex (EssentialArcClass M)) (n : ℤ) (hn : 0 ≤ n)
        (carrier : Finset (EssentialArcClass M) → FiniteComplex (EssentialArcClass M))
        (incl : ∀ σ, (carrier σ).simplices ⊆ B.simplices)
        (fill : ∀ (σ : SimplexAt A n) (c : chains B (n - 1)),
          boundary B (n - 1) c = 0 →
          c ∈ (chainInclusion (carrier σ.val) B (incl σ.val) (n - 1)).range →
          ∃ d : chains (carrier σ.val) n,
            boundary B n (chainInclusion _ B (incl σ.val) n d) = c)
        (f : chains A (n - 1) →+ chains B (n - 1))
        (hcycle : ∀ c, boundary B (n - 1) (f (boundary A n c)) = 0)
        (hcarried : ∀ (σ : SimplexAt A n) (τ : SimplexAt A (n - 1)),
          τ.val ⊆ σ.val → f (FreeAbelianGroup.of τ) ∈
            (chainInclusion (carrier σ.val) B (incl σ.val) (n - 1)).range) :
        ∃ F : chains A n →+ chains B n,
          (∀ c, boundary B n (F c) = f (boundary A n c)) ∧
          (∀ σ, F (FreeAbelianGroup.of σ) ∈
            (chainInclusion (carrier σ.val) B (incl σ.val) n).range) := by
      classical
      have fillings (σ : SimplexAt A n) : ∃ d : chains (carrier σ.val) n,
          boundary B n (chainInclusion _ B (incl σ.val) n d) =
            f (boundary A n (FreeAbelianGroup.of σ)) := by
        apply fill σ _ (hcycle _)
        simp only [AddMonoidHom.comp_apply, boundary, FreeAbelianGroup.lift_apply_of, faceBoundary, map_sum]
        apply AddSubgroup.sum_mem
        intro v hv
        split_ifs with hvalid
        · rw [map_zsmul]
          apply AddSubgroup.zsmul_mem
          exact hcarried σ ⟨σ.val.erase v, hvalid⟩ (Finset.erase_subset _ _)
        · simp only [map_zero]
          exact AddSubgroup.zero_mem _
      choose d hd using fillings
      let F : chains A n →+ chains B n := FreeAbelianGroup.lift fun σ =>
        chainInclusion _ B (incl σ.val) n (d σ)
      refine ⟨F, ?_, ?_⟩
      · have he : (boundary B n).comp F = f.comp (boundary A n) := by
          apply FreeAbelianGroup.lift_ext
          intro σ
          simp only [AddMonoidHom.comp_apply, F, FreeAbelianGroup.lift_apply_of]
          exact hd σ
        exact fun c => DFunLike.congr_fun he c
      · intro σ
        exact ⟨d σ, by simp only [F, FreeAbelianGroup.lift_apply_of]⟩
    have homoextend (A B : FiniteComplex (EssentialArcClass M)) (n : ℤ)
        (carrier : Finset (EssentialArcClass M) → FiniteComplex (EssentialArcClass M))
        (incl : ∀ σ, (carrier σ).simplices ⊆ B.simplices)
        (fill : ∀ (σ : SimplexAt A n) (c : chains B n), boundary B n c = 0 →
          c ∈ (chainInclusion (carrier σ.val) B (incl σ.val) n).range →
          ∃ d : chains (carrier σ.val) (n + 1),
            (show n + 1 - 1 = n by omega) ▸
              boundary B (n + 1) (chainInclusion _ B (incl σ.val) (n + 1) d) = c)
        (f g : chains A n →+ chains B n)
        (fprev gprev : chains A (n - 1) →+ chains B (n - 1))
        (H : chains A (n - 1) →+ chains B n)
        (Hprev : chains A (n - 1 - 1) →+ chains B (n - 1))
        (hf : ∀ c, boundary B n (f c) = fprev (boundary A n c))
        (hg : ∀ c, boundary B n (g c) = gprev (boundary A n c))
        (hH : ∀ c, boundary B n (H c) = gprev c - fprev c - Hprev (boundary A (n - 1) c))
        (hfc : ∀ σ, f (FreeAbelianGroup.of σ) ∈
          (chainInclusion (carrier σ.val) B (incl σ.val) n).range)
        (hgc : ∀ σ, g (FreeAbelianGroup.of σ) ∈
          (chainInclusion (carrier σ.val) B (incl σ.val) n).range)
        (hHc : ∀ (σ : SimplexAt A n) (τ : SimplexAt A (n - 1)), τ.val ⊆ σ.val →
          H (FreeAbelianGroup.of τ) ∈ (chainInclusion (carrier σ.val) B (incl σ.val) n).range) :
        ∃ Hnext : chains A n →+ chains B (n + 1),
          (∀ c, (show n + 1 - 1 = n by omega) ▸ boundary B (n + 1) (Hnext c) =
            g c - f c - H (boundary A n c)) ∧
          (∀ σ, Hnext (FreeAbelianGroup.of σ) ∈
            (chainInclusion (carrier σ.val) B (incl σ.val) (n + 1)).range) := by
      classical
      let D : chains A n →+ chains B n := g - f - H.comp (boundary A n)
      have hcycle (c : chains A n) : boundary B n (D c) = 0 := by
        change boundary B n (g c - f c - H (boundary A n c)) = 0
        rw [map_sub, map_sub, hg, hf, hH]
        have hb : boundary A (n - 1) (boundary A n c) = 0 :=
          DFunLike.congr_fun (boundary_boundary A n) c
        rw [hb, map_zero]
        abel
      have hcarried (σ : SimplexAt A n) : D (FreeAbelianGroup.of σ) ∈
          (chainInclusion (carrier σ.val) B (incl σ.val) n).range := by
        apply AddSubgroup.sub_mem _ (AddSubgroup.sub_mem _ (hgc σ) (hfc σ))
        simp only [AddMonoidHom.comp_apply, boundary, FreeAbelianGroup.lift_apply_of, faceBoundary, map_sum]
        apply AddSubgroup.sum_mem
        intro v hv
        split_ifs with hvalid
        · rw [map_zsmul]
          apply AddSubgroup.zsmul_mem
          exact hHc σ ⟨σ.val.erase v, hvalid⟩ (Finset.erase_subset _ _)
        · simp only [map_zero]
          exact AddSubgroup.zero_mem _
      choose d hd using fun σ => fill σ (D (FreeAbelianGroup.of σ)) (hcycle _) (hcarried σ)
      let Hnext : chains A n →+ chains B (n + 1) := FreeAbelianGroup.lift fun σ =>
        chainInclusion _ B (incl σ.val) (n + 1) (d σ)
      refine ⟨Hnext, ?_, ?_⟩
      · have hcast {m k : ℤ} (he : m = k) (v : chains B m) :
            chainsDegreeCast B he v = he ▸ v := by
          cases he
          rfl
        let bn : chains B (n + 1) →+ chains B n :=
          (chainsDegreeCast B (show n + 1 - 1 = n by omega)).toAddMonoidHom.comp
            (boundary B (n + 1))
        have he : bn.comp Hnext = D := by
          apply FreeAbelianGroup.lift_ext
          intro σ
          simpa only [bn, Hnext, AddMonoidHom.comp_apply, FreeAbelianGroup.lift_apply_of,
            AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, hcast] using hd σ
        intro c
        have hc := DFunLike.congr_fun he c
        simpa only [bn, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
          AddMonoidHom.coe_coe, hcast, D, AddMonoidHom.sub_apply] using hc
      · intro σ
        exact ⟨d σ, by simp only [Hnext, FreeAbelianGroup.lift_apply_of]⟩
    have coneCast (K L : FiniteComplex (EssentialArcClass M))
        (hLK : L.simplices ⊆ K.simplices) (hcone : IsNonemptyCone L)
        (p q : ℤ) (he : p - 1 = q) (hp : 0 ≤ p)
        (c : chains K q) (hc : boundary K q c = 0)
        (hcar : c ∈ (chainInclusion L K hLK q).range) :
        ∃ d : chains L p, (he ▸ boundary K p (chainInclusion L K hLK p d)) = c := by
      subst q
      simpa only [] using coneFill K L hLK hcone p hp c hc hcar
    have extendCast (A B : FiniteComplex (EssentialArcClass M))
        (p q : ℤ) (he : p - 1 = q) (hp : 0 ≤ p)
        (carrier : Finset (EssentialArcClass M) → FiniteComplex (EssentialArcClass M))
        (incl : ∀ σ, (carrier σ).simplices ⊆ B.simplices)
        (fill : ∀ (σ : SimplexAt A p) (c : chains B q), boundary B q c = 0 →
          c ∈ (chainInclusion (carrier σ.val) B (incl σ.val) q).range →
          ∃ d : chains (carrier σ.val) p,
            (he ▸ boundary B p (chainInclusion _ B (incl σ.val) p d)) = c)
        (f : chains A q →+ chains B q)
        (hcycle : ∀ c, boundary B q (f (he ▸ boundary A p c)) = 0)
        (hcarried : ∀ (σ : SimplexAt A p) (τ : SimplexAt A q), τ.val ⊆ σ.val →
          f (FreeAbelianGroup.of τ) ∈ (chainInclusion (carrier σ.val) B (incl σ.val) q).range) :
        ∃ F : chains A p →+ chains B p,
          (∀ c, (he ▸ boundary B p (F c)) = f (he ▸ boundary A p c)) ∧
          (∀ σ, F (FreeAbelianGroup.of σ) ∈
            (chainInclusion (carrier σ.val) B (incl σ.val) p).range) := by
      subst q
      simpa only [] using extend A B p hp carrier incl fill f hcycle hcarried
    have homoCast (A B : FiniteComplex (EssentialArcClass M))
        (p q r : ℤ) (he : p - 1 = q) (he2 : q - 1 = r)
        (carrier : Finset (EssentialArcClass M) → FiniteComplex (EssentialArcClass M))
        (incl : ∀ σ, (carrier σ).simplices ⊆ B.simplices)
        (fill : ∀ (σ : SimplexAt A p) (c : chains B p), boundary B p c = 0 →
          c ∈ (chainInclusion (carrier σ.val) B (incl σ.val) p).range →
          ∃ d : chains (carrier σ.val) (p + 1),
            ((show p + 1 - 1 = p by omega) ▸ boundary B (p + 1)
              (chainInclusion _ B (incl σ.val) (p + 1) d)) = c)
        (f g : chains A p →+ chains B p)
        (fp gp : chains A q →+ chains B q)
        (H : chains A q →+ chains B p) (Hp : chains A r →+ chains B q)
        (hf : ∀ c, (he ▸ boundary B p (f c)) = fp (he ▸ boundary A p c))
        (hg : ∀ c, (he ▸ boundary B p (g c)) = gp (he ▸ boundary A p c))
        (hh : ∀ c, (he ▸ boundary B p (H c)) = gp c - fp c - Hp (he2 ▸ boundary A q c))
        (hfc : ∀ σ, f (FreeAbelianGroup.of σ) ∈
          (chainInclusion (carrier σ.val) B (incl σ.val) p).range)
        (hgc : ∀ σ, g (FreeAbelianGroup.of σ) ∈
          (chainInclusion (carrier σ.val) B (incl σ.val) p).range)
        (hHc : ∀ (σ : SimplexAt A p) (τ : SimplexAt A q), τ.val ⊆ σ.val →
          H (FreeAbelianGroup.of τ) ∈ (chainInclusion (carrier σ.val) B (incl σ.val) p).range) :
        ∃ Hnext : chains A p →+ chains B (p + 1),
          (∀ c, ((show p + 1 - 1 = p by omega) ▸ boundary B (p + 1) (Hnext c)) =
            g c - f c - H (he ▸ boundary A p c)) ∧
          (∀ σ, Hnext (FreeAbelianGroup.of σ) ∈
            (chainInclusion (carrier σ.val) B (incl σ.val) (p + 1)).range) := by
      subst q
      subst r
      simpa only [] using homoextend A B p carrier incl fill f g fp gp H Hp hf hg hh hfc hgc hHc
    have squared (A : FiniteComplex (EssentialArcClass M)) (p q : ℤ)
        (he : p - 1 = q) (c : chains A p) : boundary A q (he ▸ boundary A p c) = 0 := by
      subst q
      exact DFunLike.congr_fun (boundary_boundary A p) c
    by_cases hn : n < -1
    · have hempty : IsEmpty (SimplexAt (actualA M) n) := ⟨fun σ => by
        rcases σ.property.2 with h | h <;> omega⟩
      haveI := hempty
      have hz0 : z = 0 := Subsingleton.elim _ _
      refine ⟨0, ?_⟩
      rw [map_zero, hz0]
      have cz {i j : ℤ} (h : i = j) : h ▸ (0 : chains (actualA M) i) = (0 : chains (actualA M) j) := by
        cases h
        rfl
      exact cz _
    · by_cases he : n = -1
      · subst n
        let a := vertex M anchor
        let L : FiniteComplex (EssentialArcClass M) := {
          simplices := {τ | τ ⊆ {a}}
          down_closed := by
            intro σ τ hsub hτ
            exact hsub.trans hτ }
        have hs : IsArcSimplex M {a} := by
          refine ⟨fun _ => anchor, ?_, ?_⟩
          · intro v
            exact (Finset.mem_singleton.mp v.property).symm
          · intro v w hne
            exact False.elim (hne (Subtype.ext
              ((Finset.mem_singleton.mp v.property).trans (Finset.mem_singleton.mp w.property).symm)))
        have hLK : L.simplices ⊆ (actualA M).simplices := by
          intro τ hτ
          obtain ⟨rep, hrep, hdis⟩ := hs
          exact ⟨fun v => rep ⟨v.val, hτ v.property⟩,
            fun v => hrep _, fun v w hne => hdis _ _
              (fun h => hne (Subtype.ext (Subtype.mk.inj h)))⟩
        have hcone : IsNonemptyCone L := by
          refine ⟨a, Finset.Subset.refl _, ?_⟩
          intro τ hτ
          exact Finset.insert_subset (Finset.mem_singleton_self _) hτ
        have all (σ : SimplexAt (actualA M) (-1)) : σ.val ∈ L := by
          have hσ : σ.val = ∅ := by
            rcases σ.property.2 with h | h
            · exact h.2
            · omega
          change σ.val ⊆ {a}
          rw [hσ]
          exact Finset.empty_subset _
        let r : chains (actualA M) (-1) →+ chains L (-1) :=
          FreeAbelianGroup.lift fun σ =>
            FreeAbelianGroup.of ⟨σ.val, all σ, σ.property.2⟩
        have hr : (chainInclusion L (actualA M) hLK (-1)).comp r = AddMonoidHom.id _ := by
          apply FreeAbelianGroup.lift_ext
          intro σ
          rfl
        have hcarried : z ∈ (chainInclusion L (actualA M) hLK (-1)).range :=
          ⟨r z, DFunLike.congr_fun hr z⟩
        obtain ⟨d, hd⟩ := coneFill (actualA M) L hLK hcone 0 (by omega) z hz hcarried
        refine ⟨chainInclusion L (actualA M) hLK 0 d, ?_⟩
        simpa using hd
      · have hnpos : 0 ≤ n := by omega
        have down {τ υ : Finset (EssentialArcClass M)} (hsub : τ ⊆ υ)
            (hυ : IsArcSimplex M υ) : IsArcSimplex M τ := by
          obtain ⟨rep, hrep, hdisj⟩ := hυ
          refine ⟨fun v => rep ⟨v.val, hsub v.property⟩, fun v => hrep _, ?_⟩
          intro v w hne
          apply hdisj
          exact fun he => hne (Subtype.ext (Subtype.mk.inj he))
        let K := actualA M
        let A : FiniteComplex (EssentialArcClass M) := {
          simplices := {σ | σ ⊆ F ∧ IsArcSimplex M σ}
          down_closed := by
            intro σ τ hsub hσ
            exact ⟨hsub.trans hσ.1, down hsub hσ.2⟩ }
        have hAK : A.simplices ⊆ K.simplices := fun _ h => h.2
        let carrier (s : Finset (EssentialArcClass M)) : FiniteComplex (EssentialArcClass M) := {
          simplices := {τ | τ ⊆ s ∧ IsArcSimplex M s}
          down_closed := by
            intro σ τ hsub hσ
            exact ⟨hsub.trans hσ.1, hσ.2⟩ }
        have incl (s : Finset (EssentialArcClass M)) : (carrier s).simplices ⊆ K.simplices :=
          fun _ h => down h.1 h.2
        have cmono {s t : Finset (EssentialArcClass M)} (hsub : s ⊆ t)
            (ht : IsArcSimplex M t) : (carrier s).simplices ⊆ (carrier t).simplices :=
          fun _ h => ⟨h.1.trans hsub, ht⟩
        have ccone (s : Finset (EssentialArcClass M)) (hs : IsArcSimplex M s)
            (hne : s.Nonempty) : IsNonemptyCone (carrier s) := by
          obtain ⟨v, hv⟩ := hne
          refine ⟨v, ⟨Finset.singleton_subset_iff.mpr hv, hs⟩, ?_⟩
          intro τ hτ
          exact ⟨Finset.insert_subset hv hτ.1, hs⟩
        have rangeMono {s t : Finset (EssentialArcClass M)} (hsub : s ⊆ t)
            (ht : IsArcSimplex M t) (q : ℤ) :
            (chainInclusion (carrier s) K (incl s) q).range ≤
              (chainInclusion (carrier t) K (incl t) q).range := by
          have he : (chainInclusion (carrier t) K (incl t) q).comp
              (chainInclusion (carrier s) (carrier t) (cmono hsub ht) q) =
                chainInclusion (carrier s) K (incl s) q := by
            apply FreeAbelianGroup.lift_ext
            intro σ
            rfl
          rintro c ⟨d, rfl⟩
          exact ⟨chainInclusion (carrier s) (carrier t) (cmono hsub ht) q d,
            DFunLike.congr_fun he d⟩
        let image (i : Fin (C.stages + 1)) (σ : Finset (EssentialArcClass M)) := σ.image (C.map i)
        let unionImage (i : Fin C.stages) (σ : Finset (EssentialArcClass M)) :=
          image ⟨i.val, by omega⟩ σ ∪ image ⟨i.val + 1, by omega⟩ σ
        have hImage (i : Fin (C.stages + 1)) (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ A) :
            IsArcSimplex M (image i σ) := by
          convert C.simplicial i σ hσ.1 hσ.2 using 1
          ext v
          simp only [image, Finset.mem_image]
        have hUnion (i : Fin C.stages) (σ : Finset (EssentialArcClass M)) (hσ : σ ∈ A) :
            IsArcSimplex M (unionImage i σ) := by
          convert C.contiguous i.val i.isLt σ hσ.1 hσ.2 using 1
          ext v
          simp only [unionImage, image, Finset.mem_union, Finset.mem_image]
        have imono (i : Fin (C.stages + 1)) {σ τ : Finset (EssentialArcClass M)} (h : σ ⊆ τ) :
            image i σ ⊆ image i τ := Finset.image_subset_image h
        have umono (i : Fin C.stages) {σ τ : Finset (EssentialArcClass M)} (h : σ ⊆ τ) :
            unionImage i σ ⊆ unionImage i τ := Finset.union_subset_union (imono _ h) (imono _ h)
        let Good (p q : ℤ) : Prop :=
          ∃ level : q - 1 = p,
          ∃ fp : Fin (C.stages + 1) → chains A p →+ chains K p,
          ∃ fc : Fin (C.stages + 1) → chains A q →+ chains K q,
          ∃ Hp : Fin C.stages → chains A p →+ chains K q,
          ∃ Hc : Fin C.stages → chains A q →+ chains K (q + 1),
            (∀ i c, (level ▸ boundary K q (fc i c)) = fp i (level ▸ boundary A q c)) ∧
            (∀ i σ, fc i (FreeAbelianGroup.of σ) ∈
              (chainInclusion (carrier (image i σ.val)) K (incl _) q).range) ∧
            (∀ i σ, fp i (FreeAbelianGroup.of σ) ∈
              (chainInclusion (carrier (image i σ.val)) K (incl _) p).range) ∧
            (∀ i σ, Hp i (FreeAbelianGroup.of σ) ∈
              (chainInclusion (carrier (unionImage i σ.val)) K (incl _) q).range) ∧
            (∀ i σ, Hc i (FreeAbelianGroup.of σ) ∈
              (chainInclusion (carrier (unionImage i σ.val)) K (incl _) (q + 1)).range) ∧
            (∀ i c, (show q + 1 - 1 = q by omega) ▸ boundary K (q + 1) (Hc i c) =
              fc ⟨i.val + 1, by omega⟩ c - fc ⟨i.val, by omega⟩ c - Hp i (level ▸ boundary A q c)) ∧
            fc ⟨0, by omega⟩ = chainInclusion A K hAK q ∧
            fp ⟨0, by omega⟩ = chainInclusion A K hAK p
        have base : Good (-1 - 1) (-1) := by
          refine ⟨rfl, (fun _ => chainInclusion A K hAK (-1 - 1)),
            (fun _ => chainInclusion A K hAK (-1)), (fun _ => 0), (fun _ => 0), ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
          · intro i c
            exact DFunLike.congr_fun (chainInclusion_boundary A K hAK (-1)) c
          · intro i σ
            have hem : σ.val = ∅ := by
              rcases σ.property.2 with h | h
              · exact h.2
              · omega
            have him : image i σ.val = ∅ := by simp [image, hem]
            refine ⟨FreeAbelianGroup.of ⟨σ.val, ?_, σ.property.2⟩, rfl⟩
            exact ⟨by simp [hem, him], hImage i σ.val σ.property.1⟩
          · intro i σ
            rcases σ.property.2 with h | h <;> omega
          · intro i σ
            exact AddSubgroup.zero_mem _
          · intro i σ
            exact AddSubgroup.zero_mem _
          · intro i c
            simp only [AddMonoidHom.zero_apply, map_zero, sub_self, sub_zero]
        have next (p q : ℤ) (hq : -1 ≤ q) (hgood : Good p q) : Good q (q + 1) := by
          obtain ⟨level, fp, fc, Hp, Hc, hcomm, hfc, hfp, hHp, hHc, hhom, hfc0, hfp0⟩ := hgood
          have nonemptyσ (σ : SimplexAt A (q + 1)) : σ.val.Nonempty := by
            rcases σ.property.2 with h | h
            · omega
            · apply Finset.card_pos.mp
              omega
          have each (i : Fin (C.stages + 1)) :
              ∃ f : chains A (q + 1) →+ chains K (q + 1),
                (∀ c : chains A (q + 1), ((show q + 1 - 1 = q by omega) ▸ boundary K (q + 1) (f c)) = fc i ((show q + 1 - 1 = q by omega) ▸ boundary A (q + 1) c)) ∧
                (∀ σ, f (FreeAbelianGroup.of σ) ∈
                  (chainInclusion (carrier (image i σ.val)) K (incl _) (q + 1)).range) ∧
                (i = ⟨0, by omega⟩ → f = chainInclusion A K hAK (q + 1)) := by
            by_cases hi : i = ⟨0, by omega⟩
            · subst i
              refine ⟨chainInclusion A K hAK (q + 1), ?_, ?_, fun _ => rfl⟩
              · intro c
                rw [hfc0]
                have hx := DFunLike.congr_fun (chainInclusion_boundary A K hAK (q + 1)) c
                have hcast {r t : ℤ} (he : r = t) (v : chains A r) :
                    (he ▸ chainInclusion A K hAK r v) = chainInclusion A K hAK t (he ▸ v) := by
                  cases he
                  rfl
                have hy := congrArg (fun v : chains K (q + 1 - 1) =>
                  (show q + 1 - 1 = q by omega) ▸ v) hx
                simpa only [AddMonoidHom.comp_apply, hcast] using hy
              · intro σ
                have him : image ⟨0, by omega⟩ σ.val = σ.val := by
                  calc
                    _ = σ.val.image id := by
                      apply Finset.image_congr
                      intro v hv
                      exact C.starts v (σ.property.1.1 hv)
                    _ = σ.val := Finset.image_id
                refine ⟨FreeAbelianGroup.of ⟨σ.val, ?_, σ.property.2⟩, rfl⟩
                exact ⟨by rw [him], hImage _ _ σ.property.1⟩
            · have ex := extendCast A K (q + 1) q (by omega) (by omega)
                (fun σ => carrier (image i σ)) (fun σ => incl (image i σ))
              have ex' : ∃ f : chains A (q + 1) →+ chains K (q + 1),
                  (∀ c : chains A (q + 1), ((show q + 1 - 1 = q by omega) ▸ boundary K (q + 1) (f c)) = fc i ((show q + 1 - 1 = q by omega) ▸ boundary A (q + 1) c)) ∧
                  (∀ σ, f (FreeAbelianGroup.of σ) ∈
                    (chainInclusion (carrier (image i σ.val)) K (incl _) (q + 1)).range) := by
                refine ex ?_ (fc i) ?_ ?_
                · intro σ c hc hcar
                  have cf := coneCast K (carrier (image i σ.val)) (incl _)
                    (ccone _ (hImage _ _ σ.property.1) (Finset.image_nonempty.mpr (nonemptyσ σ)))
                    (q + 1) q (by omega) (by omega)
                  exact cf c hc hcar
                · intro c
                  have hb := squared A (q + 1) q (by omega) c
                  apply (chainsDegreeCast K level).injective
                  have ht {r t : ℤ} (h : r = t) (v : chains K r) : chainsDegreeCast K h v = h ▸ v := by
                    cases h
                    rfl
                  have zc {r t : ℤ} (h : r = t) : h ▸ (0 : chains A r) = (0 : chains A t) := by
                    cases h
                    rfl
                  rw [ht, hcomm, hb, map_zero, zc, map_zero]
                · intro σ τ hsub
                  exact rangeMono (imono i hsub) (hImage _ _ σ.property.1) q (hfc i τ)
              obtain ⟨f, hf, hcarry⟩ := ex'
              exact ⟨f, hf, hcarry, fun h => (hi h).elim⟩
          choose fn hncomm hncarry hnzero using each
          have hn0 : fn ⟨0, by omega⟩ = chainInclusion A K hAK (q + 1) := hnzero _ rfl
          have eachH (i : Fin C.stages) :
              ∃ Hn : chains A (q + 1) →+ chains K (q + 1 + 1),
                (∀ c : chains A (q + 1), ((show q + 1 + 1 - 1 = q + 1 by omega) ▸ boundary K (q + 1 + 1) (Hn c)) =
                  fn ⟨i.val + 1, by omega⟩ c - fn ⟨i.val, by omega⟩ c -
                    Hc i ((show q + 1 - 1 = q by omega) ▸ boundary A (q + 1) c)) ∧
                (∀ σ, Hn (FreeAbelianGroup.of σ) ∈
                  (chainInclusion (carrier (unionImage i σ.val)) K (incl _) (q + 1 + 1)).range) := by
            have hex := homoCast A K (q + 1) q p (by omega) level
              (fun σ => carrier (unionImage i σ)) (fun σ => incl (unionImage i σ))
            refine hex ?_ (fn ⟨i.val, by omega⟩) (fn ⟨i.val + 1, by omega⟩)
              (fc ⟨i.val, by omega⟩) (fc ⟨i.val + 1, by omega⟩) (Hc i) (Hp i) ?_ ?_ ?_ ?_ ?_ ?_
            · intro σ c hc hcar
              have hun : (unionImage i σ.val).Nonempty := by
                obtain ⟨v, hv⟩ := nonemptyσ σ
                exact ⟨C.map ⟨i.val, by omega⟩ v,
                  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)⟩
              have cf := coneCast K (carrier (unionImage i σ.val)) (incl _)
                (ccone _ (hUnion _ _ σ.property.1) hun) (q + 1 + 1) (q + 1) (by omega) (by omega)
              simpa only [add_sub_cancel_right] using cf c hc hcar
            · intro c
              simpa only [add_sub_cancel_right] using hncomm ⟨i.val, by omega⟩ c
            · intro c
              simpa only [add_sub_cancel_right] using hncomm ⟨i.val + 1, by omega⟩ c
            · intro c
              simpa only [add_sub_cancel_right] using hhom i c
            · intro σ
              exact rangeMono Finset.subset_union_left (hUnion _ _ σ.property.1) (q + 1)
                (hncarry ⟨i.val, by omega⟩ σ)
            · intro σ
              exact rangeMono Finset.subset_union_right (hUnion _ _ σ.property.1) (q + 1)
                (hncarry ⟨i.val + 1, by omega⟩ σ)
            · intro σ τ hsub
              exact rangeMono (umono i hsub) (hUnion _ _ σ.property.1) (q + 1) (hHc i τ)
          choose Hn hHn hnHcarry using eachH
          refine ⟨(by omega), fc, fn, Hc, Hn, ?_, hncarry, hfc, hHc, hnHcarry, ?_, hn0, hfc0⟩
          · intro i c
            simpa only [add_sub_cancel_right] using hncomm i c
          · intro i c
            simpa only [add_sub_cancel_right] using hHn i c
        have builds (k : ℕ) : Good (-1 + (k : ℤ) - 1) (-1 + (k : ℤ)) := by
          induction k with
          | zero => simpa using base
          | succ k ih =>
            have hc : -1 + ((k + 1 : ℕ) : ℤ) = (-1 + (k : ℤ)) + 1 := by omega
            have hp : -1 + ((k + 1 : ℕ) : ℤ) - 1 = -1 + (k : ℤ) := by omega
            rw [hp, hc]
            exact next _ _ (by omega) ih
        have hncast : -1 + ((n + 1).toNat : ℤ) = n := by
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        have gn : Good (n - 1) n := hncast ▸ builds (n + 1).toNat
        obtain ⟨level, fp, fc, Hp, Hc, hcomm, hfc, hfp, hHp, hHc, hhom, hfc0, hfp0⟩ := gn
        have hlevel : level = rfl := Subsingleton.elim _ _
        rw [hlevel] at hcomm hhom
        have supportedRange (L : FiniteComplex (EssentialArcClass M))
            (hLK : L.simplices ⊆ K.simplices) (q : ℤ) (c : chains K q)
            (hs : ∀ σ ∈ (FreeAbelianGroup.toFinsupp c).support, σ.val ∈ L) :
            c ∈ (chainInclusion L K hLK q).range := by
          have hre : c = ∑ σ ∈ (FreeAbelianGroup.toFinsupp c).support,
              (FreeAbelianGroup.toFinsupp c) σ • FreeAbelianGroup.of σ := by
            conv_lhs => rw [← Finsupp.toFreeAbelianGroup_toFinsupp c]
            simp only [Finsupp.toFreeAbelianGroup, Finsupp.liftAddHom_apply]
            rfl
          rw [hre]
          apply AddSubgroup.sum_mem
          intro σ hσ
          apply AddSubgroup.zsmul_mem
          exact ⟨FreeAbelianGroup.of ⟨σ.val, hs σ hσ, σ.property.2⟩, rfl⟩
        obtain ⟨za, hza⟩ := supportedRange A hAK n z
          (fun σ hσ => ⟨hsupport σ hσ, σ.property.1⟩)
        have hzA : boundary A n za = 0 := by
          apply carrierChainInclusion_injective A K hAK (n - 1)
          have h := DFunLike.congr_fun (chainInclusion_boundary A K hAK n) za
          change boundary K n (chainInclusion A K hAK n za) =
            chainInclusion A K hAK (n - 1) (boundary A n za) at h
          rw [hza, hz] at h
          simpa only [map_zero] using h.symm
        let a := vertex M anchor
        let star : FiniteComplex (EssentialArcClass M) := {
          simplices := {τ | IsArcSimplex M (insert a τ)}
          down_closed := by
            intro σ τ hsub hσ
            exact down (Finset.insert_subset_insert a hsub) hσ }
        have hstarK : star.simplices ⊆ K.simplices :=
          fun _ h => down (Finset.subset_insert _ _) h
        have has : IsArcSimplex M {a} := by
          refine ⟨fun _ => anchor, ?_, ?_⟩
          · intro v
            exact (Finset.mem_singleton.mp v.property).symm
          · intro v w hne
            exact False.elim (hne (Subtype.ext
              ((Finset.mem_singleton.mp v.property).trans (Finset.mem_singleton.mp w.property).symm)))
        have hstarcone : IsNonemptyCone star := by
          refine ⟨a, ?_, ?_⟩
          · change IsArcSimplex M (insert a {a})
            simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self a)] using has
          · intro τ hτ
            change IsArcSimplex M (insert a (insert a τ))
            change IsArcSimplex M (insert a τ) at hτ
            simpa only [Finset.insert_idem] using hτ
        let last : Fin (C.stages + 1) := ⟨C.stages, by omega⟩
        have hfinalcycle : boundary K n (fc last za) = 0 := by
          have h := hcomm last za
          change boundary K n (fc last za) = fp last (boundary A n za) at h
          rw [hzA, map_zero] at h
          exact h
        have genFinal (σ : SimplexAt A n) : fc last (FreeAbelianGroup.of σ) ∈
            (chainInclusion star K hstarK n).range := by
          have he : IsArcSimplex M (insert a (image last σ.val)) := by
            convert C.ends_in_star σ.val σ.property.1.1 σ.property.1.2 using 1
            ext v
            simp only [last, a, image, Finset.mem_insert, Finset.mem_image]
          have hcs : (carrier (image last σ.val)).simplices ⊆ star.simplices :=
            fun _ h => down (Finset.insert_subset_insert a h.1) he
          have hi : (chainInclusion star K hstarK n).comp
              (chainInclusion (carrier (image last σ.val)) star hcs n) =
                chainInclusion (carrier (image last σ.val)) K (incl _) n := by
            apply FreeAbelianGroup.lift_ext
            intro τ
            rfl
          obtain ⟨d, hd⟩ := hfc last σ
          exact ⟨chainInclusion (carrier (image last σ.val)) star hcs n d,
            (DFunLike.congr_fun hi d).trans hd⟩
        have finalRange (c : chains A n) : fc last c ∈ (chainInclusion star K hstarK n).range := by
          induction c using FreeAbelianGroup.induction_on with
          | zero => simp only [map_zero]; exact AddSubgroup.zero_mem _
          | of σ => exact genFinal σ
          | neg σ hσ => simpa only [map_neg] using AddSubgroup.neg_mem _ hσ
          | add c d hc hd => simpa only [map_add] using AddSubgroup.add_mem _ hc hd
        have cf := coneCast K star hstarK hstarcone (n + 1) n (by omega) (by omega)
        obtain ⟨d, hd⟩ := cf (fc last za) hfinalcycle (finalRange za)
        have hcast {r t : ℤ} (he : r = t) (v : chains K r) :
            chainsDegreeCast K he v = he ▸ v := by cases he; rfl
        let bn : chains K (n + 1) →+ chains K n :=
          (chainsDegreeCast K (show n + 1 - 1 = n by omega)).toAddMonoidHom.comp (boundary K (n + 1))
        have hbn (b : chains K (n + 1)) : bn b = (show n + 1 - 1 = n by omega) ▸ boundary K (n + 1) b := by
          simp only [bn, AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
            AddMonoidHom.coe_coe, hcast]
        have hstep (i : Fin C.stages) : bn (Hc i za) =
            fc ⟨i.val + 1, by omega⟩ za - fc ⟨i.val, by omega⟩ za := by
          rw [hbn]
          simpa only [hzA, map_zero, sub_zero] using hhom i za
        have htel : (∑ i : Fin C.stages,
            (fc ⟨i.val + 1, by omega⟩ za - fc ⟨i.val, by omega⟩ za)) =
            fc last za - fc ⟨0, by omega⟩ za := by
          rw [Finset.sum_sub_distrib]
          change (∑ i : Fin C.stages, fc i.succ za) - (∑ i : Fin C.stages, fc i.castSucc za) = _
          have h1 := Fin.sum_univ_succ (fun i : Fin (C.stages + 1) => fc i za)
          have h2 := Fin.sum_univ_castSucc (fun i : Fin (C.stages + 1) => fc i za)
          have he : (∑ i : Fin C.stages, fc i.succ za) + fc ⟨0, by omega⟩ za =
              (∑ i : Fin C.stages, fc i.castSucc za) + fc last za := by
            have e1 : (∑ i : Fin C.stages, fc i.succ za) + fc ⟨0, by omega⟩ za =
                ∑ i : Fin (C.stages + 1), fc i za := by
              exact (add_comm _ _).trans h1.symm
            exact e1.trans h2
          exact sub_eq_sub_iff_add_eq_add.mpr (he.trans (add_comm _ _))
        have hsum : bn (∑ i : Fin C.stages, Hc i za) = fc last za - z := by
          rw [map_sum]
          simp_rw [hstep]
          rw [htel, hfc0, hza]
        refine ⟨chainInclusion star K hstarK (n + 1) d - ∑ i : Fin C.stages, Hc i za, ?_⟩
        rw [← hbn, map_sub, hsum]
        have hdf : bn (chainInclusion star K hstarK (n + 1) d) = fc last za := by
          rw [hbn]
          simpa only [add_sub_cancel_right] using hd
        rw [hdf]
        exact sub_sub_cancel _ _
  obtain ⟨anchor⟩ := essentialAnchor_exists M
  let F : Finset (EssentialArcClass M) :=
    (FreeAbelianGroup.toFinsupp z).support.biUnion (fun σ => σ.val)
  have hsupport (σ : SimplexAt (actualA M) n)
      (hσ : σ ∈ (FreeAbelianGroup.toFinsupp z).support) : σ.val ⊆ F := by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨σ, hσ, hv⟩
  obtain ⟨C⟩ := finiteContraction_exists M anchor F
  have independent (q : ℤ) (d e : DecidableEq (EssentialArcClass M)) :
      @boundary (EssentialArcClass M) d ‹LinearOrder (EssentialArcClass M)› (actualA M) q =
        @boundary (EssentialArcClass M) e ‹LinearOrder (EssentialArcClass M)› (actualA M) q := by
    have he : d = e := Subsingleton.elim _ _
    cases he
    rfl
  have hz' : @boundary (EssentialArcClass M) LinearOrder.toDecidableEq
      ‹LinearOrder (EssentialArcClass M)› (actualA M) n z = 0 := by
    rw [← independent n (Classical.decEq _) LinearOrder.toDecidableEq]
    exact hz
  obtain ⟨b, hb⟩ := fill_supported anchor F C n z hz' hsupport
  refine ⟨b, ?_⟩
  rw [independent (n + 1) (Classical.decEq _) LinearOrder.toDecidableEq]
  exact hb

end ArcSurgery
open CurveGenusTwo.Filtration
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actualA_reducedHomology_zero (M : HyperellipticModel E S)
    [LinearOrder (EssentialArcClass M)]
    (n : ℤ) : Subsingleton (reducedHomology (actualA M) n) := by
  have mem_cast_range {A : Type} [AddCommGroup A] {i j : ℤ}
      (h : i = j) (f : A →+ chains (actualA M) i) (b : A) :
      h ▸ f b ∈ Eq.mp (congrArg (fun k => AddSubgroup (chains (actualA M) k)) h) f.range := by
    cases h
    exact ⟨b, rfl⟩
  have htop : (boundaries (actualA M) n).comap (cycles (actualA M) n).subtype = ⊤ := by
    apply top_unique
    intro z _
    change z.val ∈ boundaries (actualA M) n
    have hz : boundary (actualA M) n z.val = 0 := z.property
    have independent (q : ℤ) (d e : DecidableEq (EssentialArcClass M)) :
        @boundary (EssentialArcClass M) d ‹LinearOrder (EssentialArcClass M)› (actualA M) q =
        @boundary (EssentialArcClass M) e ‹LinearOrder (EssentialArcClass M)› (actualA M) q := by
      have he : d = e := Subsingleton.elim _ _
      cases he
      rfl
    have hzC : @boundary (EssentialArcClass M) (ArcSurgery.pendingConsumerDecidableEq M)
        ‹LinearOrder (EssentialArcClass M)› (actualA M) n z.val = 0 := by
      rw [independent n (ArcSurgery.pendingConsumerDecidableEq M) LinearOrder.toDecidableEq]
      exact hz
    obtain ⟨b, hbC⟩ := ArcSurgery.actualArc_cycle_fills M n z.val hzC
    have hb : (show n + 1 - 1 = n by omega) ▸ boundary (actualA M) (n + 1) b = z.val := by
      rw [independent (n + 1) (ArcSurgery.pendingConsumerDecidableEq M) LinearOrder.toDecidableEq] at hbC
      exact hbC
    unfold boundaries
    have hn : n + 1 - 1 = n := by omega
    rw [← hb]
    exact mem_cast_range hn (boundary (actualA M) (n + 1)) b
  change Subsingleton ((cycles (actualA M) n) ⧸
    ((boundaries (actualA M) n).comap (cycles (actualA M) n).subtype))
  rw [htop]
  exact QuotientAddGroup.subsingleton_quotient_top
end CurveComplex.HyperellipticModel
#print axioms CurveComplex.HyperellipticModel.actualA_reducedHomology_zero
