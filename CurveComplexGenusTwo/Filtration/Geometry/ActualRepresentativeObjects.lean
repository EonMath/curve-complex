import CurveComplexGenusTwo.Filtration.Geometry.ActualObjects
import CurveComplexGenusTwo.Filtration.Geometry.MarkedArcPrimitives
import CurveComplexGenusTwo.Filtration.Geometry.NonloopPuncture
import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance integrationLocalInstance_ActualRepresentativeObjects_1 (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _

/-- Original simultaneous representatives retain their literal endpoint labels. -/
theorem markedArcEndset_eq_classEndpoints (M : HyperellipticModel E S)
    (a : EssentialMarkedArc M) :
    markedArcEndset a.val = classEndpoints M (Quotient.mk (essentialArcSetoid M) a) := by
  rfl

/-- Actual object geometry uses only members of the given simplex and its given family. -/
def actualObjectTrace (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (O : Finset (EssentialArcClass M)) : Set S :=
  ⋃ v : {v // v ∈ σ}, ⋃ (_ : v.val ∈ O), (r v).val.image

theorem actualObjectTrace_subset_graph (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (O : Finset (EssentialArcClass M)) :
    actualObjectTrace M r O ⊆ ⋃ v, (r v).val.image := by
  rintro x hx
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
  obtain ⟨_, hx⟩ := Set.mem_iUnion.mp hv
  exact Set.mem_iUnion.mpr ⟨v, hx⟩

theorem actualObjectTrace_compact (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (O : Finset (EssentialArcClass M)) :
    IsCompact (actualObjectTrace M r O) := by
  classical
  apply isCompact_iUnion
  intro v
  apply isCompact_iUnion
  intro _
  exact markedArc_image_compact (r v).val

theorem actualObjectTrace_loop (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    {v : EssentialArcClass M} (hv : v ∈ σ) :
    actualObjectTrace M r {v} = (r ⟨v, hv⟩).val.image := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hwv, hx⟩ := Set.mem_iUnion.mp hw
    have he : w = ⟨v, hv⟩ := Subtype.ext (Finset.mem_singleton.mp hwv)
    simpa [he] using hx
  · intro hx
    exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, Set.mem_iUnion.mpr ⟨by simp, hx⟩⟩

theorem actualObjectTrace_endpoint_connected (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (v : EssentialArcClass M)
    (hne : (actualEndpointFibre M σ v).Nonempty) :
    IsConnected (actualObjectTrace M r (actualEndpointFibre M σ v)) := by
  classical
  obtain ⟨w, hw⟩ := hne
  have hwσ := actualEndpointFibre_subset M σ v hw
  let I := {u : {u // u ∈ σ} // u.val ∈ actualEndpointFibre M σ v}
  letI : Nonempty I := ⟨⟨⟨w, hwσ⟩, hw⟩⟩
  let rw : I → MarkedArc M := fun u => (r u.val).val
  let b : S := (r ⟨w, hwσ⟩).val.map ⟨0, by norm_num⟩
  have hb : b ∈ classEndpoints M v := by
    have he : markedArcEndset (r ⟨w, hwσ⟩).val = classEndpoints M w := by
      rw [markedArcEndset_eq_classEndpoints, hr]
    have hwEnds := (Finset.mem_filter.mp hw).2.2
    rw [← hwEnds, ← he]
    simp [b, markedArcEndset]
  have hcommon : ∀ u : I, b ∈ markedArcEndset (rw u) := by
    intro u
    change b ∈ markedArcEndset (r u.val).val
    rw [markedArcEndset_eq_classEndpoints, hr]
    rw [(Finset.mem_filter.mp u.property).2.2]
    exact hb
  have hc := markedFamily_graph_connected_of_common_endpoint rw b hcommon
  have heq : (⋃ u : I, (rw u).image) =
      actualObjectTrace M r (actualEndpointFibre M σ v) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨u.val, Set.mem_iUnion.mpr ⟨u.property, hu⟩⟩
    · intro hx
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
      obtain ⟨huO, hx⟩ := Set.mem_iUnion.mp hu
      exact Set.mem_iUnion.mpr ⟨⟨u, huO⟩, hx⟩
  rw [← heq]
  exact hc

/-- A non-loop original class forces each of its actual representatives to have distinct ends. -/
theorem actualRepresentative_nonloop (M : HyperellipticModel E S)
    (a : EssentialMarkedArc M) (hclass : ¬ (actualArcLabels M).isLoop
      (Quotient.mk (essentialArcSetoid M) a)) :
    a.val.map 0 ≠ a.val.map 1 := by
  classical
  have hc := (actualArcLabels M).nonloop_endpoint_card _ hclass
  change (classEndpoints M (Quotient.mk (essentialArcSetoid M) a)).card = 2 at hc
  rw [← markedArcEndset_eq_classEndpoints] at hc
  intro he
  change ({a.val.map 0, a.val.map 1} : Finset S).card = 2 at hc
  rw [he] at hc
  simp at hc

/-- Removing any mark from an actual parallel object leaves it connected at the other endpoint. -/
theorem actualObjectTrace_endpoint_remove_mark_connected (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (v : EssentialArcClass M) (hne : (actualEndpointFibre M σ v).Nonempty)
    (b : S) (hb : b ∈ M.cover.branch) :
    IsConnected (actualObjectTrace M r (actualEndpointFibre M σ v) \ {b}) := by
  classical
  obtain ⟨w, hw⟩ := hne
  have hwσ := actualEndpointFibre_subset M σ v hw
  have hwloop : ¬ (actualArcLabels M).isLoop w := (Finset.mem_filter.mp hw).2.1
  have hwEnds : classEndpoints M w = classEndpoints M v := (Finset.mem_filter.mp hw).2.2
  have hcard : (classEndpoints M v).card = 2 := by
    rw [← hwEnds]
    exact (actualArcLabels M).nonloop_endpoint_card w hwloop
  obtain ⟨c, hcv, hcb⟩ := Finset.exists_mem_ne (by omega : 1 < (classEndpoints M v).card) b
  let I := {u : {u // u ∈ σ} // u.val ∈ actualEndpointFibre M σ v}
  letI : Nonempty I := ⟨⟨⟨w, hwσ⟩, hw⟩⟩
  let F : I → Set S := fun u => (r u.val).val.image \ {b}
  have hF : ∀ u : I, IsConnected (F u) := by
    intro u
    have hcl : ¬ (actualArcLabels M).isLoop
        (Quotient.mk (essentialArcSetoid M) (r u.val)) := by
      rw [hr]
      exact (Finset.mem_filter.mp u.property).2.1
    exact nonloop_image_remove_mark_connected M
      ⟨(r u.val).val, actualRepresentative_nonloop M (r u.val) hcl⟩ b hb
  have hcF : ∀ u : I, c ∈ F u := by
    intro u
    refine ⟨?_, hcb⟩
    have hcends : c ∈ markedArcEndset (r u.val).val := by
      rw [markedArcEndset_eq_classEndpoints, hr,
        (Finset.mem_filter.mp u.property).2.2]
      exact hcv
    have hcimage : c ∈ (r u.val).val.image ∩ (M.cover.branch : Set S) := by
      rw [markedArc_image_inter_branch]
      exact hcends
    exact hcimage.1
  have hconn : IsConnected (⋃ u : I, F u) := by
    apply IsConnected.iUnion_of_reflTransGen hF
    intro u z
    exact Relation.ReflTransGen.single ⟨c, hcF u, hcF z⟩
  have heq : (⋃ u : I, F u) =
      actualObjectTrace M r (actualEndpointFibre M σ v) \ {b} := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
      exact ⟨Set.mem_iUnion.mpr ⟨u.val, Set.mem_iUnion.mpr ⟨u.property, hu.1⟩⟩, hu.2⟩
    · rintro ⟨hx, hxb⟩
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
      obtain ⟨huO, hx⟩ := Set.mem_iUnion.mp hu
      exact Set.mem_iUnion.mpr ⟨⟨u, huO⟩, hx, hxb⟩
  rw [← heq]
  exact hconn


/-- Corollary 9.3 for the actual selected representatives, not an abstract graph. -/
theorem actualObjectTrace_connected (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    {O : Finset (EssentialArcClass M)} (hO : O ∈ actualObjectFamily M σ) :
    IsConnected (actualObjectTrace M r O) := by
  classical
  simp only [actualObjectFamily, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hO
  rcases hO with ⟨v, ⟨hv, _⟩, rfl⟩ | ⟨v, ⟨_, _, hcard⟩, rfl⟩
  · rw [actualObjectTrace_loop M r hv]
    exact markedArc_image_connected (r ⟨v, hv⟩).val
  · apply actualObjectTrace_endpoint_connected M r hr v
    exact Finset.card_pos.mp (by omega)


/-- Every actual source object stays connected after removing a possible intersection mark. -/
theorem actualObjectTrace_remove_mark_connected (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    {O : Finset (EssentialArcClass M)} (hO : O ∈ actualObjectFamily M σ)
    (b : S) (hb : b ∈ M.cover.branch) :
    IsConnected (actualObjectTrace M r O \ {b}) := by
  classical
  simp only [actualObjectFamily, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hO
  rcases hO with ⟨v, ⟨hv, _⟩, rfl⟩ | ⟨v, ⟨_, _, hcard⟩, rfl⟩
  · rw [actualObjectTrace_loop M r hv]
    exact markedArc_image_remove_mark_connected M (r ⟨v, hv⟩).val b hb
  · apply actualObjectTrace_endpoint_remove_mark_connected M r hr v _ b hb
    exact Finset.card_pos.mp (by omega)

/-- Actual object traces are recovered as closures of their punctured traces. -/
theorem actualObjectTrace_puncture_dense (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (O : Finset (EssentialArcClass M)) (b : S) :
    actualObjectTrace M r O ⊆ closure (actualObjectTrace M r O \ {b}) := by
  intro x hx
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hvO, hx⟩ := Set.mem_iUnion.mp hv
  have hd := markedArc_puncture_dense M (r v).val b hx
  apply closure_mono _ hd
  intro y hy
  exact ⟨Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hvO, hy.1⟩⟩, hy.2⟩


theorem actualObjectTrace_endpoint_mark (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (v : EssentialArcClass M) {x : S}
    (hx : x ∈ actualObjectTrace M r (actualEndpointFibre M σ v))
    (hb : x ∈ M.cover.branch) : x ∈ classEndpoints M v := by
  classical
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx
  obtain ⟨huO, hx⟩ := Set.mem_iUnion.mp hu
  have hend : x ∈ markedArcEndset (r u).val := by
    change x ∈ (markedArcEndset (r u).val : Set S)
    rw [← markedArc_image_inter_branch]
    exact ⟨hx, hb⟩
  rw [markedArcEndset_eq_classEndpoints, hr,
    (Finset.mem_filter.mp huO).2.2] at hend
  exact hend

theorem actualObjectTrace_singleton_mark (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    {v : EssentialArcClass M} (hv : v ∈ σ) {x : S}
    (hx : x ∈ actualObjectTrace M r {v}) (hb : x ∈ M.cover.branch) :
    x ∈ classEndpoints M v := by
  classical
  rw [actualObjectTrace_loop M r hv] at hx
  have hend : x ∈ markedArcEndset (r ⟨v, hv⟩).val := by
    change x ∈ (markedArcEndset (r ⟨v, hv⟩).val : Set S)
    rw [← markedArc_image_inter_branch]
    exact ⟨hx, hb⟩
  rw [markedArcEndset_eq_classEndpoints, hr] at hend
  exact hend

/-- Full actual Corollary 9.3 intersection assertion for the original representative graph. -/
theorem actualDistinctObjectTraces_intersection (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ u z, u ≠ z → Disjoint (arcInterior M (r u)) (arcInterior M (r z)))
    {O P : Finset (EssentialArcClass M)}
    (hO : O ∈ actualObjectFamily M σ) (hP : P ∈ actualObjectFamily M σ) (hne : O ≠ P) :
    (actualObjectTrace M r O ∩ actualObjectTrace M r P).Subsingleton ∧
      actualObjectTrace M r O ∩ actualObjectTrace M r P ⊆ (M.cover.branch : Set S) := by
  classical
  have hclassDisj := actualObjectFamily_distinct_disjoint M σ hO hP hne
  have hmarks : actualObjectTrace M r O ∩ actualObjectTrace M r P ⊆
      (M.cover.branch : Set S) := by
    intro x hx
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hx.1
    obtain ⟨huO, hxU⟩ := Set.mem_iUnion.mp hu
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx.2
    obtain ⟨hzP, hxZ⟩ := Set.mem_iUnion.mp hz
    have hneuz : u ≠ z := by
      intro he
      exact Finset.disjoint_left.mp hclassDisj huO (he.symm ▸ hzP)
    by_contra hb
    exact Set.disjoint_left.mp (hd u z hneuz) ⟨hxU, hb⟩ ⟨hxZ, hb⟩
  refine ⟨?_, hmarks⟩
  intro x hx y hy
  have hxB := hmarks hx
  have hyB := hmarks hy
  simp only [actualObjectFamily, Finset.mem_union, Finset.mem_image,
    Finset.mem_filter] at hO hP
  rcases hO with ⟨v, ⟨hv, hvloop⟩, rfl⟩ | ⟨v, ⟨_, hvloop, _⟩, rfl⟩
  · have hcard : (classEndpoints M v).card ≤ 1 := by
      change (classEndpoints M v).card = 1 at hvloop
      omega
    exact Finset.card_le_one.mp hcard x (actualObjectTrace_singleton_mark M r hr hv hx.1 hxB)
      y (actualObjectTrace_singleton_mark M r hr hv hy.1 hyB)
  · rcases hP with ⟨w, ⟨hw, hwloop⟩, rfl⟩ | ⟨w, ⟨_, hwloop, _⟩, rfl⟩
    · have hcard : (classEndpoints M w).card ≤ 1 := by
        change (classEndpoints M w).card = 1 at hwloop
        omega
      exact Finset.card_le_one.mp hcard x (actualObjectTrace_singleton_mark M r hr hw hx.2 hxB)
        y (actualObjectTrace_singleton_mark M r hr hw hy.2 hyB)
    · by_contra hxy
      have hvcard : (classEndpoints M v).card = 2 :=
        (actualArcLabels M).nonloop_endpoint_card v hvloop
      have hwcard : (classEndpoints M w).card = 2 :=
        (actualArcLabels M).nonloop_endpoint_card w hwloop
      have heV : ({x, y} : Finset S) = classEndpoints M v := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact actualObjectTrace_endpoint_mark M r hr v hx.1 hxB
          · exact actualObjectTrace_endpoint_mark M r hr v hy.1 hyB
        · simp [hvcard, hxy]
      have heW : ({x, y} : Finset S) = classEndpoints M w := by
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact actualObjectTrace_endpoint_mark M r hr w hx.2 hxB
          · exact actualObjectTrace_endpoint_mark M r hr w hy.2 hyB
        · simp [hwcard, hxy]
      apply hne
      have he : classEndpoints M v = classEndpoints M w := heV.symm.trans heW
      simp only [actualEndpointFibre, he]


/-- Source Lemma 9.8 on the original actual finite graph: another object lies in a unique gap closure. -/
theorem actualOtherObject_in_unique_gap (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ u z, u ≠ z → Disjoint (arcInterior M (r u)) (arcInterior M (r z)))
    {O P : Finset (EssentialArcClass M)}
    (hO : O ∈ actualObjectFamily M σ) (hP : P ∈ actualObjectFamily M σ) (hne : O ≠ P) :
    ∃! U : Set S, IsComplementComponent (actualObjectTrace M r O) U ∧
      actualObjectTrace M r P \ actualObjectTrace M r O ⊆ U ∧
      actualObjectTrace M r P ⊆ closure U := by
  classical
  let A := actualObjectTrace M r O
  let B := actualObjectTrace M r P
  obtain ⟨hi, hmark⟩ := actualDistinctObjectTraces_intersection M r hr hd hO hP hne
  have hBconn : IsConnected B := actualObjectTrace_connected M r hr hP
  have hc : IsConnected (B \ A) ∧ B ⊆ closure (B \ A) := by
    by_cases hex : (B ∩ A).Nonempty
    · obtain ⟨b, hb⟩ := hex
      have hbmark : b ∈ M.cover.branch := hmark ⟨hb.2, hb.1⟩
      have hpunc : IsConnected (B \ {b}) :=
        actualObjectTrace_remove_mark_connected M r hr hP b hbmark
      have hdense : B ⊆ closure (B \ {b}) := actualObjectTrace_puncture_dense M r P b
      have hsub : B \ {b} ⊆ B \ A := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        intro hxA
        exact hx.2 (hi ⟨hxA, hx.1⟩ ⟨hb.2, hb.1⟩)
      exact ⟨hpunc.subset_closure hsub (fun _ hx => hdense hx.1),
        hdense.trans (closure_mono hsub)⟩
    · have heq : B \ A = B := by
        ext x
        constructor
        · exact And.left
        · intro hx
          exact ⟨hx, fun hxA => hex ⟨x, hx, hxA⟩⟩
      rw [heq]
      exact ⟨hBconn, subset_closure⟩
  exact connected_object_in_unique_gap hc.1 hc.2


/-- Source Lemma 9.11's free-gap/face conclusion on actual original representatives. -/
theorem actual_free_gap_is_face (M : HyperellipticModel E S)
    {σ : Finset (EssentialArcClass M)}
    (hbad : CurveGenusTwo.Filtration.badVertices (actualArcLabels M) σ = σ)
    (r : {v // v ∈ σ} → EssentialMarkedArc M)
    (hr : ∀ v, Quotient.mk (essentialArcSetoid M) (r v) = v.val)
    (hd : ∀ u z, u ≠ z → Disjoint (arcInterior M (r u)) (arcInterior M (r z)))
    {O : Finset (EssentialArcClass M)} (hO : O ∈ actualObjectFamily M σ)
    {U : Set S} (hU : IsComplementComponent (actualObjectTrace M r O) U)
    (hfree : ∀ P ∈ actualObjectFamily M σ, P ≠ O →
      ¬ actualObjectTrace M r P ⊆ closure U) :
    IsComplementComponent (⋃ v, (r v).val.image) U := by
  classical
  have hdisj : Disjoint U (⋃ v, (r v).val.image) := by
    apply Set.disjoint_left.mpr
    intro x hxU hxG
    obtain ⟨v, hxv⟩ := Set.mem_iUnion.mp hxG
    obtain ⟨P, hP, hvP⟩ := actualObjectFamily_cover M σ hbad v.property
    have hxP : x ∈ actualObjectTrace M r P :=
      Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hvP, hxv⟩⟩
    by_cases he : P = O
    · exact hU.2.2.1 hxU (he ▸ hxP)
    · obtain ⟨V, ⟨hV, hPV, hPcl⟩, _⟩ :=
        actualOtherObject_in_unique_gap M r hr hd hO hP (Ne.symm he)
      have hxV : x ∈ V := hPV ⟨hxP, hU.2.2.1 hxU⟩
      have hUV : U = V := by
        by_contra hne
        exact Set.disjoint_left.mp (complementComponents_disjoint hU hV hne) hxU hxV
      exact hfree P hP he (hUV.symm ▸ hPcl)
  exact complementComponent_of_graph_enlargement hU
    (actualObjectTrace_subset_graph M r O) hdisj


end CurveComplex.HyperellipticModel
