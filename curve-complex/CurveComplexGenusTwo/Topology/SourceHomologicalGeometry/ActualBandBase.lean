import CurveComplexGenusTwo.Foundations.RemainderArcStatements
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold

open Topology Set
namespace CurveComplex

theorem exists_oneCrossingBandBase
    {S : Type} [TopologicalSpace S] [T2Space S]
    (a b : Curve S) (htrans : Transverse a b)
    (hcard : htrans.1.toFinset.card = 1) :
    Nonempty (OneCrossingBandBase a b) := by
  classical
  have noRealEmbedding (f : Circle → ℝ) (hf : Continuous f)
      (hi : Function.Injective f) : False := by
    have ordered (x y : Circle) (hxy : f x < f y) : False := by
      let t : ℝ := (f x + f y) / 2
      have hxt : f x < t := by dsimp [t]; linarith
      have hty : t < f y := by dsimp [t]; linarith
      have ht : t ∈ Set.range f :=
        (isConnected_range hf).Icc_subset ⟨x,rfl⟩ ⟨y,rfl⟩ ⟨hxt.le,hty.le⟩
      obtain ⟨z,hz⟩ := ht
      have hxz : x ≠ z := by intro h; subst x; linarith
      have hyz : y ≠ z := by intro h; subst y; linarith
      have hc := (Circle.isPathConnected_compl_singleton z).isConnected.image f hf.continuousOn
      have hxin : f x ∈ f '' ({z}ᶜ : Set Circle) := ⟨x,hxz,rfl⟩
      have hyin : f y ∈ f '' ({z}ᶜ : Set Circle) := ⟨y,hyz,rfl⟩
      obtain ⟨w,hw,hew⟩ := hc.Icc_subset hxin hyin ⟨hxt.le,hty.le⟩
      exact hw (hi (hew.trans hz.symm))
    have hne : f (1 : Circle) ≠ f (-1 : Circle) := by
      intro heq
      have h := hi heq
      have h' := congrArg (fun z : Circle => (z : ℂ)) h
      norm_num at h'
    rcases lt_or_gt_of_ne hne with h | h
    · exact ordered 1 (-1) h
    · exact ordered (-1) 1 h
  obtain ⟨p,hpab,hcross,hunique⟩ :=
    unique_crossing_chart_of_count_one a b htrans hcard
  obtain ⟨U,V,hp,h,hU,hV,hzero,haxes,ρ,hρ,hlarge⟩ :=
    exists_closed_disk_in_crossing_chart hcross
  let ε : ℝ := ρ / 2
  have hε : 0 < ε := half_pos hρ
  have hbig : Metric.closedBall ((0,0):ℝ×ℝ) (2*ε) ⊆ V := by
    have heq : 2*ε = ρ := by dsimp [ε]; ring
    rw [heq]
    exact hlarge
  have hball : Metric.closedBall ((0,0):ℝ×ℝ) ε ⊆ V :=
    (Metric.closedBall_subset_closedBall (by dsimp [ε]; linarith)).trans hlarge
  let D := Metric.closedBall ((0,0) : ℝ × ℝ) ε
  let d : D → S := fun z => (h.symm (Set.inclusion hball z)).val
  have hd : Topology.IsEmbedding d :=
    Topology.IsEmbedding.subtypeVal.comp
      (h.symm.isEmbedding.comp (Topology.IsEmbedding.inclusion hball))
  have hchart (z : D) : h ⟨d z, (h.symm (Set.inclusion hball z)).property⟩ =
      Set.inclusion hball z := h.apply_symm_apply _
  have haaxis (z : D) : d z ∈ a.image ↔ z.val.1 = 0 := by
    rw [(haxes (d z) (h.symm (Set.inclusion hball z)).property).1, hchart]
  have hbaxis (z : D) : d z ∈ b.image ↔ z.val.2 = 0 := by
    rw [(haxes (d z) (h.symm (Set.inclusion hball z)).property).2, hchart]
  have haoutside : ¬ a.image ⊆ Set.range d := by
    intro hall
    let f : Circle → D := fun t => hd.toHomeomorph.symm ⟨a.map t,hall ⟨t,rfl⟩⟩
    have hf : Continuous f := hd.toHomeomorph.symm.continuous.comp
      (a.embedded.continuous.subtype_mk _)
    have hdf (t : Circle) : d (f t) = a.map t := by
      exact congrArg Subtype.val (hd.toHomeomorph.apply_symm_apply _)
    have hfzero (t : Circle) : (f t).val.1 = 0 :=
      (haaxis (f t)).mp (hdf t ▸ Set.mem_range_self t)
    apply noRealEmbedding (fun t => (f t).val.2) (continuous_snd.comp
      (continuous_subtype_val.comp hf))
    intro x y hxy
    apply a.embedded.injective
    rw [← hdf x, ← hdf y]
    congr 1
    apply Subtype.ext
    exact Prod.ext ((hfzero x).trans (hfzero y).symm) hxy
  have hboutside : ¬ b.image ⊆ Set.range d := by
    intro hall
    let f : Circle → D := fun t => hd.toHomeomorph.symm ⟨b.map t,hall ⟨t,rfl⟩⟩
    have hf : Continuous f := hd.toHomeomorph.symm.continuous.comp
      (b.embedded.continuous.subtype_mk _)
    have hdf (t : Circle) : d (f t) = b.map t := by
      exact congrArg Subtype.val (hd.toHomeomorph.apply_symm_apply _)
    have hfzero (t : Circle) : (f t).val.2 = 0 :=
      (hbaxis (f t)).mp (hdf t ▸ Set.mem_range_self t)
    apply noRealEmbedding (fun t => (f t).val.1) (continuous_fst.comp
      (continuous_subtype_val.comp hf))
    intro x y hxy
    apply b.embedded.injective
    rw [← hdf x, ← hdf y]
    congr 1
    apply Subtype.ext
    exact Prod.ext hxy ((hfzero x).trans (hfzero y).symm)
  let W : Set V := {z | z.val ∈ Metric.ball ((0,0) : ℝ × ℝ) ε}
  let O : Set S := ((↑) : U → S) '' (h.symm '' W)
  have hO : IsOpen O := hU.isOpenMap_subtype_val _
    (h.symm.isOpenMap _ (Metric.isOpen_ball.preimage continuous_subtype_val))
  have hOD : O ⊆ Set.range d := by
    rintro x ⟨w,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨⟨z.val,Metric.ball_subset_closedBall hz⟩,rfl⟩
  have hdO (z : D) : d z ∈ O ↔ z.val ∈ Metric.ball ((0,0) : ℝ × ℝ) ε := by
    constructor
    · rintro ⟨w,⟨y,hy,hyw⟩,hw⟩
      have hh : h.symm y = h.symm (Set.inclusion hball z) := by
        apply Subtype.ext
        exact (congrArg Subtype.val hyw).trans hw
      have hh' : y = Set.inclusion hball z := h.symm.injective hh
      rw [hh'] at hy
      exact hy
    · intro hz
      exact ⟨h.symm (Set.inclusion hball z),⟨Set.inclusion hball z,hz,rfl⟩,rfl⟩
  let lo : D := ⟨(0,-ε),by simp [D,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,
    abs_of_pos hε,hε.le]⟩
  let hi : D := ⟨(0,ε),by simp [D,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,
    abs_of_pos hε,hε.le]⟩
  have hlohi : d lo ≠ d hi := by
    intro heq
    have hh := congrArg (fun z : D => z.val.2) (hd.injective heq)
    dsimp [lo,hi] at hh
    linarith
  have hloO : d lo ∉ O := by
    rw [hdO]
    simp [lo,Metric.mem_ball,dist_eq_norm,Prod.norm_def,abs_of_pos hε]
  have hhiO : d hi ∉ O := by
    rw [hdO]
    simp [hi,Metric.mem_ball,dist_eq_norm,Prod.norm_def,abs_of_pos hε]
  let A₁ := a.image ∩ Set.range d
  let A₂ := a.image \ O
  have hA₁ : IsCompact A₁ :=
    (isCompact_range a.embedded.continuous).inter (isCompact_range hd.continuous)
  have hA₂ : IsCompact A₂ := (isCompact_range a.embedded.continuous).diff hO
  have hAcov : A₁ ∪ A₂ = a.image := by
    ext z
    constructor
    · rintro (hz | hz) <;> exact hz.1
    · intro hz
      by_cases hzo : z ∈ O
      · exact Or.inl ⟨hz,hOD hzo⟩
      · exact Or.inr ⟨hz,hzo⟩
  have hAmeet : A₁ ∩ A₂ = {d lo,d hi} := by
    ext x
    constructor
    · rintro ⟨⟨hxa,z,rfl⟩,_,hxO⟩
      have hz0 : z.val.1 = 0 := (haaxis z).mp hxa
      have hzle : |z.val.2| ≤ ε := by
        have hh : dist z.val (0,0) ≤ ε := z.property
        simpa [dist_eq_norm,Prod.norm_def,hz0] using hh
      have hznot : ¬ |z.val.2| < ε := by
        intro hh
        apply hxO
        rw [hdO]
        simpa [Metric.mem_ball,dist_eq_norm,Prod.norm_def,hz0] using hh
      have hzeq : |z.val.2| = ε := le_antisymm hzle (le_of_not_gt hznot)
      have hsign : z.val.2 = ε ∨ z.val.2 = -ε := (abs_eq hε.le).mp hzeq
      rcases hsign with hpos | hneg
      · right; congr 1; apply Subtype.ext; exact Prod.ext hz0 hpos
      · left; congr 1; apply Subtype.ext; exact Prod.ext hz0 hneg
    · rintro (rfl | rfl)
      · exact ⟨⟨(haaxis lo).mpr rfl,Set.mem_range_self lo⟩,(haaxis lo).mpr rfl,hloO⟩
      · exact ⟨⟨(haaxis hi).mpr rfl,Set.mem_range_self hi⟩,(haaxis hi).mpr rfl,hhiO⟩
  have hA₁n : (A₁ \ {d lo,d hi}).Nonempty := by
    let mid : D := ⟨(0,0),by simp [D,Metric.mem_closedBall,hε.le]⟩
    refine ⟨d mid,⟨(haaxis mid).mpr rfl,Set.mem_range_self mid⟩,?_⟩
    rintro (hh | hh)
    · have heq := congrArg (fun z : D => z.val.2) (hd.injective hh)
      dsimp [mid,lo] at heq; linarith
    · have heq := congrArg (fun z : D => z.val.2) (hd.injective hh)
      dsimp [mid,hi] at heq; linarith
  have hA₂n : (A₂ \ {d lo,d hi}).Nonempty := by
    obtain ⟨x,hxa,hxd⟩ := Set.not_subset.mp haoutside
    refine ⟨x,⟨hxa,fun hxO => hxd (hOD hxO)⟩,?_⟩
    rintro (rfl | rfl) <;> exact hxd (Set.mem_range_self _)
  obtain ⟨innerA,outerA,hinnerA,houterA,hrinnerA,hrouterA⟩ :=
    curve_closed_split_has_embedded_paths a A₁ A₂ (d lo) (d hi) hlohi
      hA₁ hA₂ hAcov hAmeet hA₁n hA₂n
  let blo : D := ⟨(-ε,0),by simp [D,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,
    abs_of_pos hε,hε.le]⟩
  let bhi : D := ⟨(ε,0),by simp [D,Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,
    abs_of_pos hε,hε.le]⟩
  have hblobhi : d blo ≠ d bhi := by
    intro heq
    have hh := congrArg (fun z : D => z.val.1) (hd.injective heq)
    dsimp [blo,bhi] at hh
    linarith
  have hbloO : d blo ∉ O := by
    rw [hdO]
    simp [blo,Metric.mem_ball,dist_eq_norm,Prod.norm_def,abs_of_pos hε]
  have hbhiO : d bhi ∉ O := by
    rw [hdO]
    simp [bhi,Metric.mem_ball,dist_eq_norm,Prod.norm_def,abs_of_pos hε]
  let B₁ := b.image ∩ Set.range d
  let B₂ := b.image \ O
  have hB₁ : IsCompact B₁ :=
    (isCompact_range b.embedded.continuous).inter (isCompact_range hd.continuous)
  have hB₂ : IsCompact B₂ := (isCompact_range b.embedded.continuous).diff hO
  have hBcov : B₁ ∪ B₂ = b.image := by
    ext z
    constructor
    · rintro (hz | hz) <;> exact hz.1
    · intro hz
      by_cases hzo : z ∈ O
      · exact Or.inl ⟨hz,hOD hzo⟩
      · exact Or.inr ⟨hz,hzo⟩
  have hBmeet : B₁ ∩ B₂ = {d blo,d bhi} := by
    ext x
    constructor
    · rintro ⟨⟨hxa,z,rfl⟩,_,hxO⟩
      have hz0 : z.val.2 = 0 := (hbaxis z).mp hxa
      have hzle : |z.val.1| ≤ ε := by
        have hh : dist z.val (0,0) ≤ ε := z.property
        simpa [dist_eq_norm,Prod.norm_def,hz0] using hh
      have hznot : ¬ |z.val.1| < ε := by
        intro hh
        apply hxO
        rw [hdO]
        simpa [Metric.mem_ball,dist_eq_norm,Prod.norm_def,hz0] using hh
      have hzeq : |z.val.1| = ε := le_antisymm hzle (le_of_not_gt hznot)
      have hsign : z.val.1 = ε ∨ z.val.1 = -ε := (abs_eq hε.le).mp hzeq
      rcases hsign with hpos | hneg
      · right; congr 1; apply Subtype.ext; exact Prod.ext hpos hz0
      · left; congr 1; apply Subtype.ext; exact Prod.ext hneg hz0
    · rintro (rfl | rfl)
      · exact ⟨⟨(hbaxis blo).mpr rfl,Set.mem_range_self blo⟩,(hbaxis blo).mpr rfl,hbloO⟩
      · exact ⟨⟨(hbaxis bhi).mpr rfl,Set.mem_range_self bhi⟩,(hbaxis bhi).mpr rfl,hbhiO⟩
  have hB₁n : (B₁ \ {d blo,d bhi}).Nonempty := by
    let mid : D := ⟨(0,0),by simp [D,Metric.mem_closedBall,hε.le]⟩
    refine ⟨d mid,⟨(hbaxis mid).mpr rfl,Set.mem_range_self mid⟩,?_⟩
    rintro (hh | hh)
    · have heq := congrArg (fun z : D => z.val.1) (hd.injective hh)
      dsimp [mid,blo] at heq; linarith
    · have heq := congrArg (fun z : D => z.val.1) (hd.injective hh)
      dsimp [mid,bhi] at heq; linarith
  have hB₂n : (B₂ \ {d blo,d bhi}).Nonempty := by
    obtain ⟨x,hxa,hxd⟩ := Set.not_subset.mp hboutside
    refine ⟨x,⟨hxa,fun hxO => hxd (hOD hxO)⟩,?_⟩
    rintro (rfl | rfl) <;> exact hxd (Set.mem_range_self _)
  obtain ⟨innerB,outerB,hinnerB,houterB,hrinnerB,hrouterB⟩ :=
    curve_closed_split_has_embedded_paths b B₁ B₂ (d blo) (d bhi) hblobhi
      hB₁ hB₂ hBcov hBmeet hB₁n hB₂n
  have hpO : p ∈ O := by
    refine ⟨⟨p,hp⟩,⟨h ⟨p,hp⟩,?_,h.symm_apply_apply _⟩,rfl⟩
    change (h ⟨p,hp⟩).val ∈ Metric.ball ((0,0) : ℝ × ℝ) ε
    rw [hzero]
    simp [Metric.mem_ball,hε]
  have houter_disj : Disjoint (Set.range outerA) (Set.range outerB) := by
    rw [hrouterA,hrouterB,Set.disjoint_left]
    intro x hxa hxb
    have hx : x = p := hunique x ⟨hxa.1,hxb.1⟩
    exact hxa.2 (hx.symm ▸ hpO)
  have houterA_attach : Set.range outerA ∩ Set.range d = {d lo,d hi} := by
    rw [hrouterA,← hAmeet]
    ext x
    simp only [A₁,A₂,Set.mem_inter_iff,Set.mem_sdiff]
    tauto
  have houterB_attach : Set.range outerB ∩ Set.range d = {d blo,d bhi} := by
    rw [hrouterB,← hBmeet]
    ext x
    simp only [B₁,B₂,Set.mem_inter_iff,Set.mem_sdiff]
    tauto
  have hOimage : O = d '' {z : D | z.val ∈ Metric.ball ((0,0) : ℝ × ℝ) ε} := by
    ext x
    constructor
    · intro hx
      obtain ⟨z,rfl⟩ := hOD hx
      exact ⟨z,(hdO z).mp hx,rfl⟩
    · rintro ⟨z,hz,rfl⟩
      exact (hdO z).mpr hz
  let E : Fin 4 → EndRectangle → S := fun i z =>
    (h.symm ⟨crossingEndRectangle ε i z,
      hbig (crossingEndRectangle_mem_large_square hε i z)⟩).val
  have hEC (i : Fin 4) : Continuous (E i) :=
    continuous_subtype_val.comp (h.symm.continuous.comp
      ((crossingEndRectangle_continuous ε i).subtype_mk _))
  have hEI (i : Fin 4) : Function.Injective (E i) := by
    intro z w he
    apply (crossingEndRectangle_isEmbedding hε i).injective
    exact congrArg Subtype.val (h.symm.injective (Subtype.ext he))
  have hE (i : Fin 4) : Topology.IsEmbedding (E i) :=
    ((hEC i).isClosedEmbedding (hEI i)).isEmbedding
  have hdisj : Pairwise (fun i j => Disjoint (Set.range (E i)) (Set.range (E j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,he⟩
    have he' := congrArg Subtype.val (h.symm.injective (Subtype.ext he))
    exact Set.disjoint_left.mp (crossingEndRectangle_pairwise_disjoint hε hij)
      (Set.mem_range_self z) ⟨w,he'⟩
  have hEsquare (i : Fin 4) (z : EndRectangle) :
      E i z ∈ Set.range d ↔ (z.2:ℝ) ≤ 0 := by
    constructor
    · rintro ⟨w,he⟩
      have he' := congrArg Subtype.val (h.symm.injective (Subtype.ext he))
      apply (crossingEndRectangle_square_iff hε i z).mp
      change (w : ℝ × ℝ) = crossingEndRectangle ε i z at he'
      rw [← he']
      exact w.property
    · intro hz
      exact ⟨⟨crossingEndRectangle ε i z,
        (crossingEndRectangle_square_iff hε i z).mpr hz⟩, rfl⟩
  have hEaxes (i : Fin 4) (z : EndRectangle) :
      (E i z ∈ a.image ↔ (i = 0 ∨ i = 2) ∧ (z.1:ℝ) = 0) ∧
      (E i z ∈ b.image ↔ (i = 1 ∨ i = 3) ∧ (z.1:ℝ) = 0) := by
    have he := haxes (E i z)
      (h.symm ⟨crossingEndRectangle ε i z,
        hbig (crossingEndRectangle_mem_large_square hε i z)⟩).property
    have hcoord : (h ⟨E i z,
        (h.symm ⟨crossingEndRectangle ε i z,
          hbig (crossingEndRectangle_mem_large_square hε i z)⟩).property⟩ : ℝ × ℝ) =
        crossingEndRectangle ε i z := congrArg Subtype.val (h.apply_symm_apply _)
    rw [hcoord] at he
    exact ⟨he.1.trans (crossingEndRectangle_axes hε i z).1,
      he.2.trans (crossingEndRectangle_axes hε i z).2⟩
  have hport2 : d (squarePort ε hε 2 ⟨0,by norm_num⟩) = d lo := by
    congr 1; apply Subtype.ext; simp [squarePort,crossingEndRectangle,lo]
  have hport0 : d (squarePort ε hε 0 ⟨0,by norm_num⟩) = d hi := by
    congr 1; apply Subtype.ext; simp [squarePort,crossingEndRectangle,hi]
  have hport3 : d (squarePort ε hε 3 ⟨0,by norm_num⟩) = d blo := by
    congr 1; apply Subtype.ext; simp [squarePort,crossingEndRectangle,blo]
  have hport1 : d (squarePort ε hε 1 ⟨0,by norm_num⟩) = d bhi := by
    congr 1; apply Subtype.ext; simp [squarePort,crossingEndRectangle,bhi]
  exact ⟨{
    radius := ε
    radius_pos := hε
    square := d
    square_embedded := hd
    openSquare := O
    openSquare_open := hO
    openSquare_eq := hOimage
    firstArc := outerA.cast hport2 hport0
    secondArc := outerB.cast hport3 hport1
    firstArc_embedded := houterA
    secondArc_embedded := houterB
    firstArc_range := hrouterA
    secondArc_range := hrouterB
    arcs_disjoint := houter_disj
    first_axis := haaxis
    second_axis := hbaxis
    ends := E
    ends_embedded := hE
    ends_disjoint := hdisj
    ends_square := hEsquare
    ends_seam := fun _ _ => rfl
    ends_axes := hEaxes }⟩

end CurveComplex

#print axioms CurveComplex.exists_oneCrossingBandBase
