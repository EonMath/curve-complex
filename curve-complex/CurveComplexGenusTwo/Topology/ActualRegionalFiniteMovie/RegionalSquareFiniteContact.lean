import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalStripSquare
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.FiniteContactArcConnectivity
import CurveComplexGenusTwo.Topology.ActualRegionalFiniteMovie.RegionalOriginalEndpointFixedPushOff

open CurveComplex Set Topology Schoenflies

namespace RegionalFinitePosition

def squareObstacle {S : Type*} [TopologicalSpace S] {F : Set S}
    (D : C(Square, ↥F)) (a : C(Interval, ↥F)) : Set Plane :=
  {z | ∃ hz : z ∈ Plane.closedSquare 0 1, D ⟨z,hz⟩ ∈ Set.range a}

theorem squareObstacle_closed {S : Type*} [TopologicalSpace S] [T2Space S]
    {F : Set S} (D : C(Square, ↥F)) (a : C(Interval, ↥F)) :
    IsClosed (squareObstacle D a) := by
  letI : CompactSpace Square := isCompact_iff_compactSpace.mp (Schoenflies.isCompact_closedSquare (0 : Plane) (1 : ℝ))
  have hclosed : IsClosed (D ⁻¹' Set.range a) :=
    (isCompact_range a.continuous).isClosed.preimage D.continuous
  have heq : squareObstacle D a = Subtype.val '' (D ⁻¹' Set.range a) := by
    ext z
    constructor
    · rintro ⟨hz,ha⟩
      exact ⟨⟨z,hz⟩,ha,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.property,hw⟩
  rw [heq]
  exact (hclosed.isCompact.image continuous_subtype_val).isClosed

theorem square_access_of_clean_arc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (F : Set S) (D : C(Square, ↥F)) (hD : IsEmbedding D)
    (hback : ∀ z : Square, |z.val 1| < 1 → (D z).val ∉ frontier F →
      z.val ∈ Plane.openSquare 0 1)
    (hopen : IsOpen (D '' {z : Square | |z.val 1| < 1}))
    (a k : C(Interval, ↥F)) (hk : IsEmbedding k)
    (hkclear : ∀ s ∈ Ioo (0:Interval) 1, (k s).val ∉ frontier F)
    (hkfin : (Set.range a ∩ Set.range k).Finite)
    (p : Square) (hp : |p.val 1| < 1) (hk0 : k 0 = D p) :
    ∃ u L, u ∈ Plane.openSquare 0 1 ∧ IsArcBetween L p.val u ∧
      L \ {p.val} ⊆ Plane.openSquare 0 1 ∧ (L ∩ squareObstacle D a).Finite := by
  let W := D '' {z : Square | |z.val 1| < 1}
  have hkW : k 0 ∈ W := hk0 ▸ ⟨p,hp,rfl⟩
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp
    ((hopen.preimage k.continuous).mem_nhds hkW)
  let ε : ℝ := min δ 1 / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by dsimp [ε]; linarith [min_le_left δ 1]
  have hε1 : ε < 1 := by dsimp [ε]; linarith [min_le_right δ 1]
  let τ (s : Interval) : Interval := ⟨ε*(s:ℝ),by
    constructor
    · exact mul_nonneg hε.le s.property.1
    · nlinarith [s.property.2]⟩
  have hτc : Continuous τ := by apply Continuous.subtype_mk; fun_prop
  have hτi : Function.Injective τ := by
    intro s t h
    apply Subtype.ext
    exact mul_left_cancel₀ hε.ne' (congrArg Subtype.val h)
  have hτ0 : τ 0 = 0 := Subtype.ext (by simp [τ])
  have hτ1 (s : Interval) : (τ s:ℝ) < 1 := by
    change ε*(s:ℝ) < 1
    nlinarith [s.property.2]
  have hτW (s : Interval) : k (τ s) ∈ W := by
    apply hδW
    change dist (τ s) (0:Interval) < δ
    rw [Subtype.dist_eq,Real.dist_eq]
    change |ε*(s:ℝ)-0| < δ
    rw [sub_zero,abs_of_nonneg (mul_nonneg hε.le s.property.1)]
    nlinarith [s.property.2]
  have hrange (s : Interval) : k (τ s) ∈ Set.range D := by
    obtain ⟨z,hz,he⟩ := hτW s
    exact ⟨z,he⟩
  let lift : C(Interval,Square) :=
    ⟨fun s => hD.toHomeomorph.symm ⟨k (τ s),hrange s⟩,
      hD.toHomeomorph.symm.continuous.comp ((k.continuous.comp hτc).subtype_mk _)⟩
  have hlift (s : Interval) : D (lift s) = k (τ s) := by
    exact congrArg Subtype.val (hD.toHomeomorph.apply_symm_apply ⟨k (τ s),hrange s⟩)
  have hlift0 : lift 0 = p := hD.injective (by rw [hlift,hτ0,hk0])
  have hliftI : Function.Injective lift := by
    intro s t h
    apply hτi
    apply hk.injective
    rw [← hlift,← hlift,h]
  have hliftopen (s : Interval) (hs : s ≠ 0) : (lift s).val ∈ Plane.openSquare 0 1 := by
    apply hback
    · obtain ⟨z,hz,he⟩ := hτW s
      have heq : z = lift s := hD.injective (he.trans (hlift s).symm)
      exact heq ▸ hz
    · rw [hlift]
      apply hkclear
      constructor
      · change (0:ℝ) < ε*(s:ℝ)
        exact mul_pos hε (bot_lt_iff_ne_bot.mpr hs)
      · exact hτ1 s
  let f : C(Interval,Plane) := ⟨fun s => (lift s).val,continuous_subtype_val.comp lift.continuous⟩
  have hfI : Function.Injective f := fun s t h => hliftI (Subtype.ext h)
  have hfE : IsEmbedding f := (f.continuous.isClosedEmbedding hfI).isEmbedding
  have hArc := RegionalEmbeddedFamily.planar_embedded_path_isArcBetween f hfE
  have hf0 : f 0 = p.val := congrArg Subtype.val hlift0
  refine ⟨f 1,Set.range f,hliftopen 1 (by norm_num),by rwa [hf0] at hArc,?_,?_⟩
  · rintro z ⟨⟨s,rfl⟩,hz⟩
    apply hliftopen
    intro he
    exact hz (by simpa [he,hf0])
  · have hfin : {z : Square | D z ∈ Set.range a ∩ Set.range k}.Finite :=
      hkfin.preimage hD.injective.injOn
    apply (hfin.image (fun z : Square => z.val)).subset
    rintro z ⟨⟨s,rfl⟩,⟨hz,ha⟩⟩
    refine ⟨lift s,⟨ha,?_⟩,rfl⟩
    rw [hlift]
    exact Set.mem_range_self (τ s)

#print axioms square_access_of_clean_arc

theorem square_obstacle_local_axis
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (D : C(Square, ↥F)) (a : C(Interval, ↥F))
    (hclear : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 →
      (D z).val ∉ frontier F)
    (ha0 : (a 0).val ∈ frontier F) (ha1 : (a 1).val ∈ frontier F)
    (P : OpenPartialHomeomorph Plane S)
    (hPs : P.source = Plane.openSquare 0 1)
    (hP : ∀ z : Square, z.val ∈ Plane.openSquare 0 1 → P z.val = (D z).val)
    (Q : OpenPartialHomeomorph S Plane)
    (hQa : ∀ s ∈ Ioo (0:Interval) 1, (a s).val ∈ Q.source)
    (hQaxis : ∀ z ∈ Q.source, z ∈ Set.range (fun s => (a s).val) → Q z 1 = 0) :
    ∀ x ∈ Plane.openSquare 0 1, ∃ V : Set Plane,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Plane.openSquare 0 1 ∧
      ∀ y ∈ V, x ≠ y → ∃ C ⊆ Plane.openSquare 0 1,
        IsArcBetween C x y ∧ (C ∩ squareObstacle D a).Finite := by
  intro x hx
  by_cases hxA : x ∈ squareObstacle D a
  · obtain ⟨hxS,s,hs⟩ := hxA
    have hs0 : s ≠ 0 := by
      intro he
      exact hclear ⟨x,hxS⟩ hx (by rw [← hs,he]; exact ha0)
    have hs1 : s ≠ 1 := by
      intro he
      exact hclear ⟨x,hxS⟩ hx (by rw [← hs,he]; exact ha1)
    have hsI : s ∈ Ioo (0:Interval) 1 :=
      ⟨bot_lt_iff_ne_bot.mpr hs0,lt_top_iff_ne_top.mpr hs1⟩
    let E := P.trans Q
    have hxE : x ∈ E.source := by
      change x ∈ P.source ∩ P ⁻¹' Q.source
      refine ⟨hPs.symm ▸ hx,?_⟩
      change P x ∈ Q.source
      rw [hP ⟨x,hxS⟩ hx,← hs]
      exact hQa s hsI
    apply axis_chart_local_finite_contact (Plane.openSquare 0 1) (squareObstacle D a) x E hxE
    · intro z hz
      exact hPs ▸ hz.1
    · intro z hz hzA
      obtain ⟨hzS,t,ht⟩ := hzA
      change Q (P z) 1 = 0
      apply hQaxis _ hz.2
      refine ⟨t,?_⟩
      change (a t).val = P z
      exact (congrArg Subtype.val ht).trans (hP ⟨z,hzS⟩ (hPs ▸ hz.1)).symm
  · let W := Plane.openSquare 0 1 ∩ (squareObstacle D a)ᶜ
    have hW : IsOpen W := (Plane.isOpen_openSquare 0 1).inter
      (squareObstacle_closed D a).isOpen_compl
    let E := OpenPartialHomeomorph.ofSet W hW
    apply axis_chart_local_finite_contact (Plane.openSquare 0 1) (squareObstacle D a) x E
      (show x ∈ W from ⟨hx,hxA⟩)
    · exact Set.inter_subset_left
    · intro z hz hzA
      exact (hz.2 hzA).elim

theorem square_finite_crosscut_of_clean_access
    {S : Type} [TopologicalSpace S] [T2Space S]
    (F : Set S) (D : C(Square, ↥F)) (hD : IsEmbedding D)
    (a k : C(Interval, ↥F)) (hk : IsEmbedding k)
    (hkclear : ∀ s ∈ Ioo (0:Interval) 1, (k s).val ∉ frontier F)
    (hkfin : (Set.range a ∩ Set.range k).Finite)
    (hk0 : k 0 = D (horizontalPoint 0)) (hk1 : k 1 = D (horizontalPoint 1))
    (hback : ∀ z : Square, |z.val 1| < 1 → (D z).val ∉ frontier F →
      z.val ∈ Plane.openSquare 0 1)
    (hopen : IsOpen (D '' {z : Square | |z.val 1| < 1}))
    (hlocal : ∀ x ∈ Plane.openSquare 0 1, ∃ V : Set Plane,
      IsOpen V ∧ x ∈ V ∧ V ⊆ Plane.openSquare 0 1 ∧
      ∀ y ∈ V, x ≠ y → ∃ C ⊆ Plane.openSquare 0 1,
        IsArcBetween C x y ∧ (C ∩ squareObstacle D a).Finite) :
    ∃ C : Set Plane, IsArcBetween C (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
      C \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
      {z : Square | z.val ∈ C ∧ D z ∈ Set.range a}.Finite := by
  obtain ⟨u,L,hu,hL,hLU,hLA⟩ := square_access_of_clean_arc F D hD hback hopen a k hk
    hkclear hkfin (horizontalPoint 0) (by norm_num [horizontalPoint,Plane.mk]) hk0
  let kr : C(Interval, ↥F) := ⟨fun s => k (unitInterval.symm s),
    k.continuous.comp unitInterval.continuous_symm⟩
  have hkr : IsEmbedding kr := by
    apply (kr.continuous.isClosedEmbedding ?_).isEmbedding
    intro s t h
    exact unitInterval.symm_bijective.injective (hk.injective h)
  have hkrClear : ∀ s ∈ Ioo (0:Interval) 1, (kr s).val ∉ frontier F := by
    intro s hs
    apply hkclear
    change 0 < unitInterval.symm s ∧ unitInterval.symm s < 1
    constructor
    · change (0:ℝ) < 1-(s:ℝ)
      have h : (s:ℝ) < 1 := hs.2
      linarith
    · change (1:ℝ)-(s:ℝ) < 1
      have h : (0:ℝ) < s := hs.1
      linarith
  have hkrange : Set.range kr = Set.range k := by
    ext z
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨unitInterval.symm s,rfl⟩
    · rintro ⟨s,rfl⟩
      refine ⟨unitInterval.symm s,?_⟩
      change k (unitInterval.symm (unitInterval.symm s)) = k s
      rw [unitInterval.symm_symm]
  have hkr0 : kr 0 = D (horizontalPoint 1) := by simpa [kr] using hk1
  obtain ⟨v,R,hv,hR,hRU,hRA⟩ := square_access_of_clean_arc F D hD hback hopen a kr hkr
    hkrClear (by rwa [hkrange]) (horizontalPoint 1) (by norm_num [horizontalPoint,Plane.mk]) hkr0
  have hp0 : (horizontalPoint 0).val = Plane.mk (-1) 0 := by ext i; fin_cases i <;> norm_num [horizontalPoint,Plane.mk]
  have hp1 : (horizontalPoint 1).val = Plane.mk 1 0 := by ext i; fin_cases i <;> norm_num [horizontalPoint,Plane.mk]
  rw [hp0] at hL hLU
  rw [hp1] at hR hRU
  obtain ⟨C,hC,hCi,hCA⟩ := finite_contact_arc_with_access (Plane.openSquare 0 1)
    (squareObstacle D a) L R (Plane.isOpen_openSquare 0 1)
    (Plane.convex_openSquare 0 1).isPreconnected hlocal
    (Plane.mk (-1) 0) (Plane.mk 1 0) u v
    (by intro h; have h := congrArg (fun z : Plane => z 0) h; norm_num [Plane.mk] at h)
    (by norm_num [mem_openSquare_zero_one,Plane.supNorm,Plane.mk])
    (by norm_num [mem_openSquare_zero_one,Plane.supNorm,Plane.mk]) hu hv hL hR hLU hRU hLA hRA
  refine ⟨C,hC,hCi,?_⟩
  apply (hCA.preimage Subtype.val_injective.injOn).subset
  intro z hz
  exact ⟨hz.1,⟨z.property,hz.2⟩⟩

#print axioms square_finite_crosscut_of_clean_access

end RegionalFinitePosition
