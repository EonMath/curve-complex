import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryStripFinitePosition

namespace CoherentEndpointMotion
open CurveComplex Set Topology Schoenflies RegionalFinitePosition

/- The checked strip-square construction, with its literal carrier inclusion
retained for supported motion. All geometric hypotheses are unchanged. -/
theorem strip_square_package_with_carrier
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (F : Set S) (b : C(Interval, ↥F))
    (E : C(Interval × Set.Icc (-1:ℝ) 1, ↥F)) (hE : IsEmbedding E)
    (hcenter : ∀ t, E (t,⟨0,by norm_num⟩) = b t)
    (hend : ∀ w, (E (0,w)).val ∈ frontier F ∧ (E (1,w)).val ∈ frontier F)
    (hint : ∀ t ∈ Ioo (0:Interval) 1, ∀ w, (E (t,w)).val ∉ frontier F)
    (hopen : IsOpen (E '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1})) :
    ∃ D : C(Square, ↥F), IsEmbedding D ∧
      (∀ s, D (horizontalPoint s) = b s) ∧
      (∀ z : Square, z.val ∈ Plane.openSquare 0 1 → (D z).val ∉ frontier F) ∧
      (∀ z : Square, |z.val 1| < 1 → (D z).val ∉ frontier F →
        z.val ∈ Plane.openSquare 0 1) ∧
      IsOpen (D '' {z : Square | |z.val 1| < 1}) ∧
      range D ⊆ range E ∧
      ∃ P : OpenPartialHomeomorph Plane S,
        P.source = Plane.openSquare 0 1 ∧
        ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → P z.val = (D z).val := by
  letI : CompactSpace Square := isCompact_iff_compactSpace.mp (Schoenflies.isCompact_closedSquare (0 : Plane) (1 : ℝ))
  let D : C(Square, ↥F) := ⟨E ∘ squareToStrip,E.continuous.comp squareToStrip_continuous⟩
  have hD : IsEmbedding D := hE.comp
    (squareToStrip_continuous.isClosedEmbedding squareToStrip_injective).isEmbedding
  have hDcenter (s : Interval) : D (horizontalPoint s) = b s := by
    change E (squareToStrip (horizontalPoint s)) = b s
    rw [squareToStrip_horizontal,hcenter]
  have hi (z : Square) (hz : z.val ∈ Plane.openSquare 0 1) :
      (squareToStrip z).1 ∈ Ioo (0:Interval) 1 := by
    have hz0 : |z.val 0| < 1 := lt_of_le_of_lt (le_max_left _ _) (mem_openSquare_zero_one.mp hz)
    have hz0 := abs_lt.mp hz0
    constructor
    · change (0:ℝ) < (z.val 0+1)/2
      linarith [hz0.1]
    · change (z.val 0+1)/2 < (1:ℝ)
      linarith [hz0.2]
  have hDclear (z : Square) (hz : z.val ∈ Plane.openSquare 0 1) :
      (D z).val ∉ frontier F := hint _ (hi z hz) _
  have hback (z : Square) (hz1 : |z.val 1| < 1) (hz : (D z).val ∉ frontier F) :
      z.val ∈ Plane.openSquare 0 1 := by
    have hn0 : (squareToStrip z).1 ≠ 0 := by
      intro h
      apply hz
      change (E (squareToStrip z)).val ∈ frontier F
      have he : squareToStrip z = (0,(squareToStrip z).2) := Prod.ext h rfl
      rw [he]
      exact (hend _).1
    have hn1 : (squareToStrip z).1 ≠ 1 := by
      intro h
      apply hz
      change (E (squareToStrip z)).val ∈ frontier F
      have he : squareToStrip z = (1,(squareToStrip z).2) := Prod.ext h rfl
      rw [he]
      exact (hend _).2
    have h0 : (0:ℝ) < (squareToStrip z).1 := bot_lt_iff_ne_bot.mpr hn0
    have h1 : ((squareToStrip z).1:ℝ) < 1 := lt_top_iff_ne_top.mpr hn1
    apply mem_openSquare_zero_one.mpr
    change max |z.val 0| |z.val 1| < 1
    rw [max_lt_iff,abs_lt]
    exact ⟨⟨by dsimp [squareToStrip] at h0; linarith,
      by dsimp [squareToStrip] at h1; linarith⟩,hz1⟩
  have himage : D '' {z : Square | |z.val 1| < 1} =
      E '' {z | (-1:ℝ) < z.2.val ∧ z.2.val < 1} := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨squareToStrip z,abs_lt.mp hz,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨w,rfl⟩ := squareToStrip_surjective z
      exact ⟨w,abs_lt.mpr hz,rfl⟩
  let eS : Interval × Set.Icc (-1:ℝ) 1 → S := fun z => (E z).val
  let bS : C(Interval,S) := ⟨fun t => (b t).val,continuous_subtype_val.comp b.continuous⟩
  obtain ⟨Q,hQs,hQt,hQco,hQaxis⟩ := source_embedded_strip_interior_chart eS
    (IsEmbedding.subtypeVal.comp hE) bS (fun t => congrArg Subtype.val (hcenter t))
  let P := normalizePlane.toOpenPartialHomeomorph.trans Q.symm
  refine ⟨D,hD,hDcenter,hDclear,hback,by rw [himage]; exact hopen,?_,P,?_,?_⟩
  · rintro y ⟨z,rfl⟩
    exact ⟨squareToStrip z,rfl⟩
  · ext z
    simp only [P,OpenPartialHomeomorph.trans_source,Homeomorph.toOpenPartialHomeomorph_source,
      mem_inter_iff,mem_univ,true_and,mem_preimage,OpenPartialHomeomorph.symm_source]
    rw [hQt]
    change (0 < (z 0+1)/2 ∧ (z 0+1)/2 < 1 ∧ -1 < z 1 ∧ z 1 < 1) ↔ _
    rw [mem_openSquare_zero_one]
    change _ ↔ max |z 0| |z 1| < 1
    rw [max_lt_iff,abs_lt,abs_lt]
    constructor
    · rintro ⟨h0,h1,hw0,hw1⟩
      exact ⟨⟨by linarith,by linarith⟩,hw0,hw1⟩
    · rintro ⟨⟨h0,h1⟩,hw0,hw1⟩
      exact ⟨by linarith,by linarith,hw0,hw1⟩
  · intro z hz
    have hz0 := hi z hz
    have hz1 : -1 < z.val 1 ∧ z.val 1 < 1 := abs_lt.mp
      (lt_of_le_of_lt (le_max_right _ _) (mem_openSquare_zero_one.mp hz))
    have hcoord := hQco (squareToStrip z) hz0.1 hz0.2 hz1.1 hz1.2
    have hsource : eS (squareToStrip z) ∈ Q.source := by
      rw [hQs]
      exact ⟨squareToStrip z,⟨hz0.1,hz0.2,hz1.1,hz1.2⟩,rfl⟩
    change Q.symm (normalizePlane z.val) = eS (squareToStrip z)
    change Q.symm (Plane.mk (squareToStrip z).1 (squareToStrip z).2) = _
    rw [← hcoord]
    exact Q.left_inv hsource


/-- Narrow the literal signed collar into an open set while retaining its
center, properness, and relative openness. -/
theorem proper_signed_strip_narrow_in_open
    {X : Type} [TopologicalSpace X] [T2Space X]
    (B U : Set X) (hU : IsOpen U) (b : C(Interval,X)) (hbU : range b ⊆ U)
    (E : C(Interval × Icc (-1:ℝ) 1,X)) (hE : IsEmbedding E)
    (hcenter : ∀ s, E (s,⟨0,by norm_num⟩) = b s)
    (hend : ∀ w, E (0,w) ∈ B ∧ E (1,w) ∈ B)
    (hint : ∀ s ∈ Ioo (0:Interval) 1, ∀ w, E (s,w) ∉ B)
    (hopen : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1})) :
    ∃ N : C(Interval × Icc (-1:ℝ) 1,X), IsEmbedding N ∧
      (∀ s, N (s,⟨0,by norm_num⟩) = b s) ∧
      (∀ w, N (0,w) ∈ B ∧ N (1,w) ∈ B) ∧
      (∀ s ∈ Ioo (0:Interval) 1, ∀ w, N (s,w) ∉ B) ∧
      IsOpen (N '' {z | -1 < z.2.val ∧ z.2.val < 1}) ∧ range N ⊆ U := by
  obtain ⟨ρ,hρ,N,hN,hNU,hNform,hNcenter⟩ := source_shrink_embedded_strip_in_open
    E hE U hU (fun s => by rw [hcenter]; exact hbU (Set.mem_range_self s))
  let N' : C(Interval × Icc (-1:ℝ) 1,X) := ⟨N,hN.continuous⟩
  have hNend : ∀ w, N' (0,w) ∈ B ∧ N' (1,w) ∈ B := by
    intro w
    change N (0,w) ∈ B ∧ N (1,w) ∈ B
    rw [hNform,hNform]
    exact hend _
  have hNint : ∀ s ∈ Ioo (0:Interval) 1, ∀ w, N' (s,w) ∉ B := by
    intro s hs w
    change N (s,w) ∉ B
    rw [hNform]
    exact hint s hs _
  have hW : IsOpen {z : Interval × Icc (-1:ℝ) 1 | -ρ < z.2.val ∧ z.2.val < ρ} :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  obtain ⟨O,hO,himage⟩ := hE.isInducing.image_eq_isOpen_inter_range hW
  have hsmall : IsOpen (E '' {z | -ρ < z.2.val ∧ z.2.val < ρ}) := by
    have heq : E '' {z | -ρ < z.2.val ∧ z.2.val < ρ} =
        O ∩ E '' {z | -1 < z.2.val ∧ z.2.val < 1} := by
      apply Set.Subset.antisymm
      · rintro y hy
        have hyO := (himage ▸ hy).1
        obtain ⟨z,hz,rfl⟩ := hy
        exact ⟨hyO,⟨z,⟨by linarith [hz.1,hρ.2],by linarith [hz.2,hρ.2]⟩,rfl⟩⟩
      · rintro y ⟨hy,z,hz,rfl⟩
        rw [himage]
        exact ⟨hy,Set.mem_range_self z⟩
    rw [heq]
    exact hO.inter hopen
  have himage : N' '' {z | -1 < z.2.val ∧ z.2.val < 1} =
      E '' {z | -ρ < z.2.val ∧ z.2.val < ρ} := by
    apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨(z.1,⟨ρ*(z.2:ℝ),by
        constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩),?_,?_⟩
      · dsimp
        constructor <;> nlinarith [hz.1,hz.2,hρ.1]
      · exact (hNform z).symm
    · rintro y ⟨z,hz,rfl⟩
      have hw : (z.2:ℝ)/ρ ∈ Icc (-1:ℝ) 1 := by
        constructor
        · apply (le_div_iff₀ hρ.1).2
          nlinarith [hz.1]
        · apply (div_le_iff₀ hρ.1).2
          simpa only [one_mul] using hz.2.le
      let w : Icc (-1:ℝ) 1 := ⟨(z.2:ℝ)/ρ,hw⟩
      refine ⟨(z.1,w),?_,?_⟩
      · change -1 < (z.2:ℝ)/ρ ∧ (z.2:ℝ)/ρ < 1
        constructor
        · apply (lt_div_iff₀ hρ.1).2
          linarith [hz.1]
        · apply (div_lt_iff₀ hρ.1).2
          simpa only [one_mul] using hz.2
      · change N (z.1,w) = E z
        rw [hNform]
        apply congrArg E
        apply Prod.ext
        · rfl
        apply Subtype.ext
        change ρ*((z.2:ℝ)/ρ) = (z.2:ℝ)
        field_simp [hρ.1.ne']
  exact ⟨N',hN,(fun s => (hNcenter s).trans (hcenter s)),hNend,hNint,
    by rw [himage]; exact hsmall,hNU⟩


theorem original_proper_arcs_separated_endpoints_graph_relative_finite_ambient_position
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    let Q : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R}
    ∀ (a b : C(Interval,↥Q)), IsEmbedding a → IsEmbedding b →
      (a 0 ∈ B ∧ a 1 ∈ B ∧ b 0 ∈ B ∧ b 1 ∈ B) →
      (∀ s ∈ Ioo (0:Interval) 1, a s ∉ B ∧ b s ∉ B) →
      Disjoint ({a 0,a 1} : Set ↥Q) {b 0,b 1} →
      ∀ G : Set ↥Q, IsClosed G → Disjoint (range b) G →
      ∃ q : C(Interval,↥Q), ∃ H : AmbientIsotopy ↥Q,
        IsEmbedding q ∧ q 0 = b 0 ∧ q 1 = b 1 ∧
        (∀ s ∈ Ioo (0:Interval) 1, q s ∉ B) ∧
        (∀ t y, y ∈ B → H.map (t,y) = y) ∧
        H.finalMap '' range b = range q ∧ (range a ∩ range q).Finite ∧
        (∀ t y, y ∈ G → H.map (t,y) = y) := by
  classical
  intro Q B a b ha hb hends hi hsep G hG hbg
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hfront : frontier Q = (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R :=
    chart_deleted_disk_complement_frontier (chartAt Plane x)
      ((chartAt Plane x) x) R hR htarget
  let pa : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨a,ha,hends.1,hends.2.1,fun s hs => (hi s hs).1⟩
  let pb : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
    ⟨b,hb,hends.2.2.1,hends.2.2.2,fun s hs => (hi s hs).2⟩
  obtain ⟨Ea,hEa,hEacenter,hEaend,hEaint,hEaopen⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget pa
  obtain ⟨Eb0,hEb0,hEb0center,hEb0end,hEb0int,hEb0open⟩ :=
    CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
      S x R g hg hS hR htarget pb
  have hbG : range b ⊆ Gᶜ := fun y hy h => Set.disjoint_left.mp hbg hy h
  obtain ⟨Eb,hEb,hEbcenter,hEbend,hEbint,hEbopen,hEbG⟩ :=
    proper_signed_strip_narrow_in_open B Gᶜ hG.isOpen_compl b hbG
      Eb0 hEb0 hEb0center hEb0end hEb0int hEb0open
  have hEbclear : ∀ s ∈ Ioo (0:Interval) 1, ∀ w, (Eb (s,w)).val ∉ frontier Q := by
    intro s hs w
    rw [hfront]
    exact hEbint s hs w
  obtain ⟨D,hD,hcenter,hclear,hback,hopen,hcarrier,P,hPs,hP⟩ :=
    strip_square_package_with_carrier Q b Eb hEb hEbcenter
      (fun w => by rw [hfront]; exact hEbend w) hEbclear hEbopen
  let aS : C(Interval,S) := ⟨fun s => (a s).val,continuous_subtype_val.comp a.continuous⟩
  obtain ⟨A,hAs,hAt,hAcoord,hAaxis⟩ := source_embedded_strip_interior_chart
    (fun z => (Ea z).val) (IsEmbedding.subtypeVal.comp hEa) aS
    (fun s => congrArg Subtype.val (hEacenter s))
  have hAa : ∀ s ∈ Ioo (0:Interval) 1, (a s).val ∈ A.source := by
    intro s hs
    rw [hAs]
    exact ⟨(s,⟨0,by norm_num⟩),⟨hs.1,hs.2,by norm_num,by norm_num⟩,
      congrArg Subtype.val (hEacenter s)⟩
  have haends : (a 0).val ∈ frontier Q ∧ (a 1).val ∈ frontier Q := by
    rw [hfront]
    exact ⟨hends.1,hends.2.1⟩
  have hbends : (b 0).val ∈ frontier Q ∧ (b 1).val ∈ frontier Q := by
    rw [hfront]
    exact ⟨hends.2.2.1,hends.2.2.2⟩
  have hbi : ∀ s ∈ Ioo (0:Interval) 1, (b s).val ∉ frontier Q := by
    intro s hs
    rw [hfront]
    exact (hi s hs).2
  have hlocal := square_obstacle_local_axis Q D a hclear haends.1 haends.2
    P hPs hP A hAa (fun z hz hza => (hAaxis z hz).mp hza)
  have hno (y : ↥Q) (hyB : y ∈ B) (hyend : y ∈ ({b 0,b 1} : Set ↥Q)) :
      y ∉ range a := by
    rintro ⟨s,hs⟩
    by_cases hs0 : s = 0
    · exact Set.disjoint_left.mp hsep
        (hs ▸ (show a s ∈ {a 0,a 1} from Or.inl (congrArg a hs0))) hyend
    by_cases hs1 : s = 1
    · exact Set.disjoint_left.mp hsep
        (hs ▸ (show a s ∈ {a 0,a 1} from Or.inr (congrArg a hs1))) hyend
    exact (hi s ⟨bot_lt_iff_ne_bot.mpr hs0,lt_top_iff_ne_top.mpr hs1⟩).1
      (hs.symm ▸ hyB)
  obtain ⟨C,hC,hCi,hCA⟩ := square_finite_crosscut_from_separated_endpoints Q D hD
    a b hb hbi (hno (b 0) hends.2.2.1 (Or.inl rfl))
    (hno (b 1) hends.2.2.2 (Or.inr rfl)) hcenter hback hopen hlocal
  obtain ⟨q,H,hq,hq0,hq1,hqi,hHF,hmove,hfinite,hHoutside⟩ :=
    embedded_square_finite_position_ambient_motion Q a b D hD hcenter hclear hopen C
      hC hCi hCA hb hbends hbi
  refine ⟨q,H,hq,hq0,hq1,?_,?_,hmove,hfinite,?_⟩
  · intro s hs
    change (q s).val ∉ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R
    rw [← hfront]
    exact hqi s hs
  · intro t y hy
    exact hHF t y (hfront.symm ▸ hy)
  · intro t y hy
    apply hHoutside
    intro hyD
    exact hEbG (hcarrier hyD) hy

end CoherentEndpointMotion
