import CurveComplexGenusTwo.Dictionary.Circle24.RectangleExteriorArcs
import CurveComplexGenusTwo.Dictionary.Circle24.ActualPrescribedOuterEdges
import CurveComplexGenusTwo.Dictionary.Circle24.ActualPrescribedSquareSeam
open Set Topology
namespace CurveComplex
set_option maxHeartbeats 9000000

private theorem reverse_endpoint_only_collision {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x)
    (hcoll : ∀ s t, p s=p t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) :
    ∀ s t, p.symm s=p.symm t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0) := by
  intro s t he
  rcases hcoll (unitInterval.symm s) (unitInterval.symm t) he with h | ⟨h0,h1⟩ | ⟨h1,h0⟩
  · exact Or.inl (unitInterval.symm_inj.mp h)
  · exact Or.inr (Or.inr ⟨unitInterval.symm_eq_zero.mp h0,unitInterval.symm_eq_one.mp h1⟩)
  · exact Or.inr (Or.inl ⟨unitInterval.symm_eq_one.mp h1,unitInterval.symm_eq_zero.mp h0⟩)

/-- Once-around boundary loops of both actual cut rectangles, with a shared
first-half seam parameter. The seam is the actual straight segment, not an
unidentified existential arc. -/
theorem rectangle_cut_boundary_loops_exterior (a k b c d : ℝ)
    (hak : a<k) (hkb : k<b) (hcd : c<d) :
    ∃ β₀ : C(Interval,Icc a k ×ˢ Icc c d),
    ∃ β₁ : C(Interval,Icc k b ×ˢ Icc c d),
      β₀ 0=β₀ 1 ∧ β₁ 0=β₁ 1 ∧
      (∀ s t, β₀ s=β₀ t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
      (∀ s t, β₁ s=β₁ t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0)) ∧
      Set.range β₀={z | z.val ∈ frontier (Icc a k ×ˢ Icc c d)} ∧
      Set.range β₁={z | z.val ∈ frontier (Icc k b ×ˢ Icc c d)} ∧
      (∀ t : Interval, (β₀ (halfInterval t)).val=Path.segment (k,c) (k,d) t) ∧
      (∀ t : Interval, (β₁ (halfInterval t)).val=Path.segment (k,c) (k,d) t) ∧
      Set.range (fun t : Interval => (β₀ (lateInterval t)).val) ∪
        Set.range (fun t : Interval => (β₁ (lateInterval t)).val)=frontier (Icc a b ×ˢ Icc c d) := by
  obtain ⟨P,Q,χ,hR₀,hR₁,hRo,hc₀,hc₁,hco,hχ,hχr,hχi,hPr,hQr⟩ :=
    rectangle_cut_package_vertical_exterior a k b c d hak hkb hcd
  let p₀ := (P.trans χ.symm).symm
  let p₁ := χ.trans Q
  have he₀ : p₀=χ.trans P.symm := by simp [p₀]
  have hr₀ : Set.range p₀=frontier (Icc a k ×ˢ Icc c d) := by
    change Set.range (P.trans χ.symm).symm=_
    rw [Path.symm_range,hR₀]
  have hp₀ (t) : p₀ t ∈ Icc a k ×ˢ Icc c d :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset (hr₀ ▸ Set.mem_range_self t)
  have hp₁ (t) : p₁ t ∈ Icc k b ×ˢ Icc c d :=
    (isClosed_Icc.prod isClosed_Icc).frontier_subset (hR₁ ▸ Set.mem_range_self t)
  let β₀ : C(Interval,Icc a k ×ˢ Icc c d) := ⟨fun t => ⟨p₀ t,hp₀ t⟩,p₀.continuous.subtype_mk _⟩
  let β₁ : C(Interval,Icc k b ×ˢ Icc c d) := ⟨fun t => ⟨p₁ t,hp₁ t⟩,p₁.continuous.subtype_mk _⟩
  have hrange {R : Set (ℝ × ℝ)} {x : ℝ × ℝ} (p : Path x x)
      (hp : ∀ t, p t ∈ R) (hr : Set.range p=frontier R) :
      Set.range (fun t => (⟨p t,hp t⟩ : R))={z | z.val ∈ frontier R} := by
    ext z
    constructor
    · rintro ⟨t,rfl⟩; exact hr ▸ Set.mem_range_self t
    · intro hz
      obtain ⟨t,ht⟩ := hr.symm ▸ hz
      exact ⟨t,Subtype.ext ht⟩
  have hhalf {x y : ℝ × ℝ} (R : Path x y) (T : Path y x) (t : Interval) :
      (R.trans T) (halfInterval t)=R t := by
    rw [Path.trans_apply,dite_eq_left (by dsimp [halfInterval]; linarith [t.property.2])]
    apply congrArg R
    apply Subtype.ext
    dsimp [halfInterval]
    ring
  refine ⟨β₀,β₁,Subtype.ext (p₀.source.trans p₀.target.symm),
    Subtype.ext (p₁.source.trans p₁.target.symm),?_,?_,hrange p₀ hp₀ hr₀,hrange p₁ hp₁ hR₁,?_,?_,?_⟩
  · intro s t he
    exact reverse_endpoint_only_collision (P.trans χ.symm) hc₀ s t (congrArg Subtype.val he)
  · intro s t he
    exact hc₁ s t (congrArg Subtype.val he)
  · intro t
    change p₀ (halfInterval t)=_
    rw [he₀,hhalf,hχ]
  · intro t
    change p₁ (halfInterval t)=_
    rw [hhalf,hχ]

  · have hlate {x y : ℝ × ℝ} (R : Path x y) (T : Path y x) (t : Interval) :
        (R.trans T) (lateInterval t)=T t := by
      have hh := Path.extend_trans_of_half_le R T (t:=(lateInterval t).val)
        (by dsimp [lateInterval]; linarith [t.property.1])
      rw [Path.extend_apply] at hh
      have he : 2*(lateInterval t).val-1=t.val := by dsimp [lateInterval]; ring
      rw [he,Path.extend_apply] at hh
      exact hh
    have hl₀ (t : Interval) : (β₀ (lateInterval t)).val=P.symm t := by
      change p₀ (lateInterval t)=_
      rw [he₀,hlate]
    have hl₁ (t : Interval) : (β₁ (lateInterval t)).val=Q t := by
      exact hlate χ Q t
    change Set.range (fun t : Interval => (β₀ (lateInterval t)).val) ∪
      Set.range (fun t : Interval => (β₁ (lateInterval t)).val)=_
    simp_rw [hl₀,hl₁]
    rw [Path.symm_range,hPr,hQr]
    have hfront : frontier (Icc a b ×ˢ Icc c d)=
      {z : ℝ × ℝ | (a≤z.1 ∧ z.1≤b ∧ (z.2=c ∨ z.2=d)) ∨
        ((z.1=a ∨ z.1=b) ∧ c≤z.2 ∧ z.2≤d)} := by
      ext z
      simp only [frontier,closure_prod_eq,closure_Icc,interior_prod_eq,interior_Icc,
        mem_sdiff,mem_prod,mem_Icc,mem_Ioo,mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨hx0,hx1⟩,⟨hy0,hy1⟩⟩,hn⟩
        by_cases hxc : z.1=a ∨ z.1=b
        · exact Or.inr ⟨hxc,hy0,hy1⟩
        · have hx : a<z.1 ∧ z.1<b := by push Not at hxc; exact ⟨lt_of_le_of_ne hx0 (Ne.symm hxc.1),lt_of_le_of_ne hx1 hxc.2⟩
          left
          refine ⟨hx0,hx1,?_⟩
          by_cases hyc : z.2=c
          · exact Or.inl hyc
          · right
            by_contra hyd
            exact hn ⟨hx,⟨lt_of_le_of_ne hy0 (Ne.symm hyc),lt_of_le_of_ne hy1 hyd⟩⟩
      · rintro (⟨hx0,hx1,hy | hy⟩ | ⟨hx | hx,hy0,hy1⟩)
        · exact ⟨⟨⟨hx0,hx1⟩,⟨by rw [hy],by rw [hy]; exact hcd.le⟩⟩,by intro h; rw [hy] at h; exact (lt_irrefl c) h.2.1⟩
        · exact ⟨⟨⟨hx0,hx1⟩,⟨by rw [hy]; exact hcd.le,by rw [hy]⟩⟩,by intro h; rw [hy] at h; exact (lt_irrefl d) h.2.2⟩
        · exact ⟨⟨⟨by rw [hx],by rw [hx]; exact hak.le.trans hkb.le⟩,⟨hy0,hy1⟩⟩,by intro h; rw [hx] at h; exact (lt_irrefl a) h.1.1⟩
        · exact ⟨⟨⟨by rw [hx]; exact hak.le.trans hkb.le,by rw [hx]⟩,⟨hy0,hy1⟩⟩,by intro h; rw [hx] at h; exact (lt_irrefl b) h.1.2⟩

    rw [hfront]
    ext z
    simp only [mem_union,mem_ofPred_eq]
    constructor
    · rintro ((⟨hx0,hxk,hy⟩ | ⟨hx,hy⟩) | (⟨hxk,hx1,hy⟩ | ⟨hx,hy⟩))
      · exact Or.inl ⟨hx0,hxk.trans hkb.le,hy⟩
      · exact Or.inr ⟨Or.inl hx,hy⟩
      · exact Or.inl ⟨hak.le.trans hxk,hx1,hy⟩
      · exact Or.inr ⟨Or.inr hx,hy⟩
    · rintro (⟨hx0,hx1,hy⟩ | ⟨hx | hx,hy⟩)
      · rcases le_total z.1 k with hk | hk
        · exact Or.inl (Or.inl ⟨hx0,hk,hy⟩)
        · exact Or.inr (Or.inl ⟨hk,hx1,hy⟩)
      · exact Or.inl (Or.inr ⟨hx,hy⟩)
      · exact Or.inr (Or.inr ⟨hx,hy⟩)

end CurveComplex
#print axioms CurveComplex.rectangle_cut_boundary_loops_exterior
