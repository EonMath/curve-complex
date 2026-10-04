import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerCrossingAxesScaffold
import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerQuadrantHelpers

open CurveComplex Set Topology Schoenflies

namespace ActualHarerCornerGeometry

/-- PLAN.md A2: at a genuine original corner, the SAME clean actual disk
occupies the quadrant determined by the two ORIGINAL parameter orders.
All original comparison-disk inputs through hcross are retained verbatim.
No occupied-sector, exterior-bank, attached-tail or comparison-disk premise
is supplied. The axes below are the separate A1 producer output. -/
theorem actual_clean_corner_axis_chart_constructs_signed_disk_quadrant
    (S : Type) [TopologicalSpace S]
    [ChartedSpace Plane S] [ClosedSurface S]
    (F : Set S) (I J : Type) [Finite I] [Finite J]
    (a : I → C(Interval, ↥F)) (b : J → C(Interval, ↥F))
    (ha : ∀ i, IsEmbedding (a i))
    (hb : ∀ j, IsEmbedding (b j))
    (hadisjoint : ∀ i k, i ≠ k →
      Disjoint (Set.range (a i)) (Set.range (a k)))
    (hbdisjoint : ∀ j k, j ≠ k →
      Disjoint (Set.range (b j)) (Set.range (b k)))
    (hfinite : ((⋃ i, Set.range (a i)) ∩ (⋃ j, Set.range (b j))).Finite)
    (ha0 : ∀ i, (a i 0).val ∈ frontier F)
    (ha1 : ∀ i, (a i 1).val ∈ frontier F)
    (hb0 : ∀ j, (b j 0).val ∈ frontier F)
    (hb1 : ∀ j, (b j 1).val ∈ frontier F)
    (haClear : ∀ i t, t ∈ Set.Ioo (0 : Interval) 1 →
      (a i t).val ∉ frontier F)
    (hbClear : ∀ j t, t ∈ Set.Ioo (0 : Interval) 1 →
      (b j t).val ∉ frontier F)
    (i : I) (j : J) (q g : C(Interval, S))
    (hq : IsEmbedding q) (hg : IsEmbedding g)
    (hqa : Set.range q ⊆ Set.range (fun t : Interval => (a i t).val))
    (hgb : Set.range g ⊆ Set.range (fun t : Interval => (b j t).val))
    (hzero : q 0 = g 0) (hone : q 1 = g 1)
    (d : C(Metric.closedBall (0 : Plane) 1, S))
    (hd : IsEmbedding d)
    (hboundary : d '' {z | z.val ∈ Metric.sphere (0 : Plane) 1} =
      Set.range q ∪ Set.range g)
    (hdF : Set.range d ⊆ F)
    (hempty : Disjoint (d '' {z | z.val ∈ Metric.ball (0 : Plane) 1})
      ((⋃ k, Set.range (fun t : Interval => (a k t).val)) ∪
        (⋃ k, Set.range (fun t : Interval => (b k t).val))))
    (hgenuine : q 0 ∉ frontier F ∨ q 1 ∉ frontier F)
    (hcleanA : range d∩(⋃ k,range (fun t:Interval => (a k t).val))=range q)
    (hcleanB : range d∩(⋃ k,range (fun t:Interval => (b k t).val))=range g)
    (hcross : ∀ v:Interval,(v=0 ∨ v=1) → q v∉frontier F →
      ∃ (s t l h : Interval) (Q : OpenPartialHomeomorph S Plane) (ε : ℝ),
        s∈Ioo (0:Interval) 1 ∧ t∈Ioo (0:Interval) 1 ∧
        (a i s).val=q v ∧ (b j t).val=q v ∧ l<s ∧ s<h ∧
        (ε=(-1:ℝ) ∨ ε=1) ∧ q v∈Q.source ∧ Q.source⊆interior F ∧
        (∀ y:↥F,y.val∈Q.source → (y∈range (b j) ↔ Q y.val 1=0)) ∧
        (∀ w∈Icc l h,(a i w).val∈Q.source) ∧
        (∀ w∈Ico l s,ε*(Q ((a i w).val)) 1<0) ∧
        (∀ w∈Ioc s h,0<ε*(Q ((a i w).val)) 1))
    (v : Interval) (hv : v = 0 ∨ v = 1) (hvGenuine : q v ∉ frontier F)
    (s₀ s₁ t₀ t₁ : Interval)
    (hs₀ : (a i s₀).val = q 0) (hs₁ : (a i s₁).val = q 1)
    (ht₀ : (b j t₀).val = g 0) (ht₁ : (b j t₁).val = g 1)
    (l h : Interval) (E : OpenPartialHomeomorph S Plane)
    (hE : OrderedWholePairAxes
      (fun w : Interval => (a i w).val) (fun w : Interval => (b j w).val)
      (endpointParameter v s₀ s₁) (endpointParameter v t₀ t₁) l h E)
    (hEF : E.source ⊆ interior F)
    (hOtherA : ∀ k, k ≠ i →
      Disjoint E.source (range (fun w : Interval => (a k w).val)))
    (hOtherB : ∀ k, k ≠ j →
      Disjoint E.source (range (fun w : Interval => (b k w).val))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ Plane.closedSquare 0 r ⊆ E.target ∧
      ∀ z : Plane, |z 0| < r → |z 1| < r →
        (E.symm z ∈ range q ↔
          z 1 = 0 ∧ 0 ≤ inwardParameterSign v s₀ s₁ * z 0) ∧
        (E.symm z ∈ range g ↔
          z 0 = 0 ∧ 0 ≤ inwardParameterSign v t₀ t₁ * z 1) ∧
        (E.symm z ∈ range d ↔
          0 ≤ inwardParameterSign v s₀ s₁ * z 0 ∧
            0 ≤ inwardParameterSign v t₀ t₁ * z 1) ∧
        (0 < -inwardParameterSign v t₀ t₁ * z 1 →
          E.symm z ∉ range d ∧
          (z 0 = 0 → ∃ w : Interval,
            (b j w).val = E.symm z ∧
            (inwardParameterSign v t₀ t₁ = 1 → w < endpointParameter v t₀ t₁) ∧
            (inwardParameterSign v t₀ t₁ = -1 → endpointParameter v t₀ t₁ < w))) := by
  classical
  let f : C(Interval,S) := ⟨fun u => (a i u).val,continuous_subtype_val.comp (a i).continuous⟩
  let m : C(Interval,S) := ⟨fun u => (b j u).val,continuous_subtype_val.comp (b j).continuous⟩
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp (ha i)
  have hm : IsEmbedding m := IsEmbedding.subtypeVal.comp (hb j)
  have hfc : f (endpointParameter v s₀ s₁) = q v := by
    rcases hv with rfl|rfl
    · simpa [f,endpointParameter] using hs₀
    · simpa [f,endpointParameter] using hs₁
  have hmc : m (endpointParameter v t₀ t₁) = q v := by
    rcases hv with rfl|rfl
    · simpa [m,endpointParameter] using ht₀.trans hzero.symm
    · simpa [m,endpointParameter] using ht₁.trans hone.symm
  have hqg : q v = g v := by rcases hv with rfl|rfl <;> assumption
  have hmp : m (endpointParameter v t₀ t₁) ∈ E.source := by
    rw [hmc,← hfc]
    exact hE.center_mem
  obtain ⟨Wq,hWq,hpWq,hWqE,hqGerm⟩ := endpoint_ordered_subarc_germ f q hf hq hqa s₀ s₁ hs₀ hs₁
    v hv E 0 1 hE.anchor_axis hE.center_mem (fun u hu => (hE.anchor_order u hu).2)
  obtain ⟨Wg,hWg,hpWg,hWgE,hgGerm⟩ := endpoint_ordered_subarc_germ m g hm hg hgb t₀ t₁ ht₀ ht₁
    v hv E 1 0 hE.moving_axis hmp hE.moving_order
  let W := Wq ∩ Wg
  have hW : IsOpen W := hWq.inter hWg
  have hWE : W ⊆ E.source := fun x hx => hWqE hx.1
  have hpW : q v ∈ W := ⟨hpWq,hqg.symm ▸ hpWg⟩
  have hEp : E (q v) = 0 := hfc ▸ hE.center_zero
  have hEW : IsOpen (E '' W) := E.isOpen_image_of_subset_source hW hWE
  have h0EW : (0:Plane) ∈ E '' W := ⟨q v,hpW,hEp⟩
  obtain ⟨r,hr,hr1,hrW⟩ := small_closed_square_in_open (E '' W) hEW h0EW
  have hrE : Plane.closedSquare 0 r ⊆ E.target := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hrW hz
    exact E.map_source (hWE hx)
  have hsq (z : Plane) (hx : |z 0| < r) (hy : |z 1| < r) : z ∈ Plane.closedSquare 0 r := by
    simp only [Plane.closedSquare,Plane.supDist,Plane.supNorm,sub_zero,mem_setOf_eq,max_le_iff]
    exact ⟨hx.le,hy.le⟩
  have hbackW (z : Plane) (hx : |z 0| < r) (hy : |z 1| < r) : E.symm z ∈ W := by
    obtain ⟨x,hxW,hEx⟩ := hrW (hsq z hx hy)
    rw [←hEx,E.left_inv (hWE hxW)]
    exact hxW
  have hqz (z : Plane) (hx : |z 0| < r) (hy : |z 1| < r) :
      E.symm z ∈ range q ↔ z 1 = 0 ∧ 0 ≤ inwardParameterSign v s₀ s₁*z 0 := by
    have hh := hqGerm (E.symm z) (hbackW z hx hy).1
    rwa [E.right_inv (hrE (hsq z hx hy))] at hh
  have hgz (z : Plane) (hx : |z 0| < r) (hy : |z 1| < r) :
      E.symm z ∈ range g ↔ z 0 = 0 ∧ 0 ≤ inwardParameterSign v t₀ t₁*z 1 := by
    have hh := hgGerm (E.symm z) (hbackW z hx hy).2
    rwa [E.right_inv (hrE (hsq z hx hy))] at hh
  let σ := inwardParameterSign v s₀ s₁
  let τ := inwardParameterSign v t₀ t₁
  have hσ : σ = -1 ∨ σ = 1 := by dsimp [σ,inwardParameterSign]; split_ifs <;> simp
  have hτ : τ = -1 ∨ τ = 1 := by dsimp [τ,inwardParameterSign]; split_ifs <;> simp
  have hσsq : σ*σ = 1 := by rcases hσ with hσ|hσ <;> norm_num [hσ]
  have hFront : frontier (range d) = range q ∪ range g := by
    rw [embedded_disk_frontier_image d hd,hboundary]
  have hFrontz (z : Plane) (hx : |z 0| < r) (hy : |z 1| < r) :
      E.symm z ∈ frontier (range d) ↔ (z 1 = 0 ∧ 0 ≤ σ*z 0) ∨ (z 0 = 0 ∧ 0 ≤ τ*z 1) := by
    rw [hFront,mem_union,hqz z hx hy,hgz z hx hy]
  have hnegative : E.symm (Plane.mk (σ*(-r/2)) 0) ∉ range d := by
    let z := Plane.mk (σ*(-r/2)) 0
    have hx : |z 0| < r := by
      change |σ*(-r/2)| < r
      rcases hσ with hσ|hσ <;> rw [hσ] <;> simp only [neg_one_mul,one_mul,abs_neg]
      all_goals rw [abs_of_neg (by linarith : -r/2 < 0)]; linarith
    have hy : |z 1| < r := by simpa [z] using hr
    have hzE : E.symm z ∈ E.source := E.map_target (hrE (hsq z hx hy))
    have hzf : E.symm z ∈ range (fun w : Interval => (a i w).val) := by
      apply (hE.anchor_axis _ hzE).mpr
      rw [E.right_inv (hrE (hsq z hx hy))]
      rfl
    intro hzD
    have hzq : E.symm z ∈ range q := hcleanA ▸ ⟨hzD,mem_iUnion.mpr ⟨i,hzf⟩⟩
    have hsign := ((hqz z hx hy).mp hzq).2
    change 0 ≤ σ*(σ*(-r/2)) at hsign
    rw [←mul_assoc,hσsq,one_mul] at hsign
    linarith
  have hDisk := signed_corner_closed_regular_set E (range d)
    (isCompact_range d.continuous).isClosed
    (by rw [CurveComplex.actual_embedded_disk_closure_interior d hd])
    r σ τ hr hσ hτ (fun z hx hy => hrE (hsq z hx hy)) hFrontz hnegative
  refine ⟨r,hr,hr1,hrE,?_⟩
  intro z hx hy
  refine ⟨hqz z hx hy,hgz z hx hy,hDisk z hx hy,?_⟩
  intro hout
  have hτneg : τ*z 1 < 0 := by change 0 < -τ*z 1 at hout; nlinarith
  refine ⟨fun hzD => not_le_of_gt hτneg ((hDisk z hx hy).mp hzD).2,?_⟩
  intro hx0
  have hzE : E.symm z ∈ E.source := E.map_target (hrE (hsq z hx hy))
  have hzm : E.symm z ∈ range (fun w : Interval => (b j w).val) := by
    apply (hE.moving_axis _ hzE).mpr
    rw [E.right_inv (hrE (hsq z hx hy)),hx0]
  obtain ⟨w,hw⟩ := hzm
  change (b j w).val = E.symm z at hw
  have hworder := hE.moving_order w (hw.symm ▸ hzE)
  rw [hw,E.right_inv (hrE (hsq z hx hy))] at hworder
  refine ⟨w,hw,?_,?_⟩
  · intro hτone
    apply hworder.1.mp
    change inwardParameterSign v t₀ t₁*z 1 < 0 at hτneg
    simpa [hτone] using hτneg
  · intro hτnegone
    apply hworder.2.mp
    change inwardParameterSign v t₀ t₁*z 1 < 0 at hτneg
    simp only [hτnegone,neg_one_mul] at hτneg
    linarith

end ActualHarerCornerGeometry
