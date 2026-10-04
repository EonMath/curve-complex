import PatchContracts
import BranchData

namespace AlternatingSphereCover
/-- Exact image of the root coordinate on the selected branch patch. -/
def rootTarget : Set ℂ := {u | 4 * (u^2).re^2 + 3 * (u^2).im^2 < 3}

theorem rootTarget_isOpen : IsOpen rootTarget := by
  apply isOpen_lt _ continuous_const
  fun_prop

theorem rawRoot_mem_rootTarget_iff (x : Raw) (hx : 0 ≤ x.val.1.val 0) :
    rawRoot x ∈ rootTarget ↔ x.val.1 ∈ positivePatch := by
  have hn : x.val.1.val 0 ^ 2 + x.val.1.val 1 ^ 2 + x.val.1.val 2 ^ 2 = 1 := by
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x.val.1.val
    have he : ‖x.val.1.val‖ = 1 := by simp
    rw [he] at hn
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm
  change 4 * (rawRoot x ^ 2).re ^ 2 + 3 * (rawRoot x ^ 2).im ^ 2 < 3 ↔ _
  rw [rawRoot_sq]
  change 4 * x.val.1.val 1 ^ 2 + 3 * x.val.1.val 2 ^ 2 < 3 ↔
    0 < x.val.1.val 0 ∧ 0 < 3 * x.val.1.val 0 ^ 2 - x.val.1.val 1 ^ 2
  constructor
  · intro h
    constructor
    · by_contra h'
      have hz : x.val.1.val 0 = 0 := le_antisymm (le_of_not_gt h') hx
      nlinarith [sq_nonneg (x.val.1.val 1)]
    · nlinarith
  · rintro ⟨_, h⟩
    nlinarith

theorem patchRoot_mem_rootTarget (x : PatchTotal) : patchRoot x ∈ rootTarget := by
  induction x using Quotient.inductionOn with
  | h x => exact (rawRoot_mem_rootTarget_iff x.val (le_of_lt x.property.1)).mpr x.property

theorem rawRoot_surjective_on_cap (u : ℂ) (hu : u ∈ rootTarget) :
    ∃ x : Raw, 0 ≤ x.val.1.val 0 ∧ rawRoot x = u := by
  let a := (u^2).re
  let b := (u^2).im
  have hu' : 4*a^2+3*b^2 < 3 := hu
  have hr : 0 < 1 - a^2-b^2 := by nlinarith [sq_nonneg a]
  let v : EuclideanSpace ℝ (Fin 3) := !₂[Real.sqrt (1-a^2-b^2), a, b]
  have hv : v ∈ Sphere := by
    have hs := Real.sq_sqrt (le_of_lt hr)
    have hn : ‖v‖^2=1 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [v, Fin.sum_univ_succ, PiLp.toLp_apply, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs,
        Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      nlinarith
    change ‖v-0‖=1
    rw [sub_zero]
    nlinarith [norm_nonneg v]
  let p : Sphere := ⟨v,hv⟩
  have hp : 0 ≤ p.val 0 := Real.sqrt_nonneg _
  have hpz : localPlane p = u^2 := by apply Complex.ext <;> rfl
  obtain ⟨x, hxp⟩ : ∃ x : Raw, x.val.1=p := by
    by_cases hb : 0 ≤ height p
    · exact ⟨⟨(p,true,false),hb⟩,rfl⟩
    · exact ⟨⟨(p,false,false),le_of_not_ge hb⟩,rfl⟩
  have hs : rawRoot x ^ 2 = u^2 := (rawRoot_sq x).trans (hxp ▸ hpz)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
  · exact ⟨x,hxp ▸ hp,h⟩
  · refine ⟨rawDeck x,hxp ▸ hp,?_⟩
    rw [rawRoot_deck,h,neg_neg]

theorem patchRoot_isOpenEmbedding : Topology.IsOpenEmbedding patchRoot := by
  have hh : Continuous (fun p : Sphere × Bool × Bool => height p.1) :=
    height_continuous.comp continuous_fst
  have hcraw : IsClosed {p : Sphere × Bool × Bool |
      if p.2.1 then 0 ≤ height p.1 else height p.1 ≤ 0} := by
    have he : {p : Sphere × Bool × Bool |
        if p.2.1 then 0 ≤ height p.1 else height p.1 ≤ 0} =
        {p | p.2.1 = false ∧ height p.1 ≤ 0} ∪
        {p | p.2.1 = true ∧ 0 ≤ height p.1} := by
      ext p
      cases h : p.2.1 <;> simp [h]
    rw [he]
    exact ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      (isClosed_le hh continuous_const)).union
      ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      (isClosed_le continuous_const hh))
  letI : CompactSpace Raw := isCompact_iff_compactSpace.mp hcraw.isCompact
  let Cap := {x : Raw // 0 ≤ x.val.1.val 0}
  have hcap : IsClosed {x : Raw | 0 ≤ x.val.1.val 0} :=
    isClosed_le continuous_const (by fun_prop)
  letI : CompactSpace Cap := isCompact_iff_compactSpace.mp hcap.isCompact
  let f : Cap → ℂ := fun x => rawRoot x.val
  have hf : Continuous f := rawRoot_continuous.comp continuous_subtype_val
  let q : (f ⁻¹' rootTarget) → PatchTotal := fun x =>
    Quotient.mk patchSetoid ⟨x.val.val,
      (rawRoot_mem_rootTarget_iff x.val.val x.val.property).mp x.property⟩
  have hq : Continuous q := by
    apply continuous_quotient_mk'.comp
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  let g : PatchTotal → rootTarget := fun x => ⟨patchRoot x,patchRoot_mem_rootTarget x⟩
  have hg : Continuous g := patchRoot_continuous.subtype_mk _
  have hr : Function.Surjective (rootTarget.restrictPreimage f) := by
    intro u
    obtain ⟨x,hx,he⟩ := rawRoot_surjective_on_cap u.val u.property
    refine ⟨⟨⟨x,hx⟩,?_⟩,?_⟩
    · change rawRoot x ∈ rootTarget
      rw [he]
      exact u.property
    · exact Subtype.ext he
  have hquot : Topology.IsQuotientMap (rootTarget.restrictPreimage f) :=
    (hf.isClosedMap.restrictPreimage rootTarget).isQuotientMap hf.restrictPreimage hr
  have hgquot : Topology.IsQuotientMap g :=
    Topology.IsQuotientMap.of_comp hq hg hquot
  have hgi : Function.Injective g := by
    intro x y h
    exact patchRoot_injective (congrArg Subtype.val h)
  have hgHome : IsHomeomorph g := isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hgquot,hgi⟩
  exact rootTarget_isOpen.isOpenEmbedding_subtypeVal.comp hgHome.isOpenEmbedding

/-- The downstairs coordinate on the same sphere patch. -/
theorem localPlane_isOpenEmbedding :
    Topology.IsOpenEmbedding (fun x : positivePatch => localPlane x.val) := by
  let V : Set ℂ := {z | 4*z.re^2+3*z.im^2<3}
  have hV : IsOpen V := isOpen_lt (by fun_prop) continuous_const
  have hn (p : Sphere) : p.val 0^2+p.val 1^2+p.val 2^2=1 := by
    have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) p.val
    have he : ‖p.val‖=1 := by simp
    rw [he] at hn
    simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm
  have heq (p : Sphere) (hp : 0≤p.val 0) : localPlane p ∈ V ↔ p ∈ positivePatch := by
    change 4*p.val 1^2+3*p.val 2^2<3 ↔ 0<p.val 0 ∧ 0<3*p.val 0^2-p.val 1^2
    constructor
    · intro h
      constructor
      · by_contra h'
        have hz : p.val 0=0 := le_antisymm (le_of_not_gt h') hp
        nlinarith [hn p,sq_nonneg (p.val 1)]
      · nlinarith [hn p]
    · intro h
      nlinarith [hn p,h.2]
  let Cap := {p : Sphere // 0≤p.val 0}
  have hcap : IsClosed {p : Sphere | 0≤p.val 0} := isClosed_le continuous_const (by fun_prop)
  letI : CompactSpace Cap := isCompact_iff_compactSpace.mp hcap.isCompact
  let f : Cap → ℂ := fun p => localPlane p.val
  have hf : Continuous f := localPlane_continuous.comp continuous_subtype_val
  let q : (f ⁻¹' V) → positivePatch := fun p => ⟨p.val.val,(heq p.val.val p.val.property).mp p.property⟩
  have hq : Continuous q := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  let g : positivePatch → V := fun p => ⟨localPlane p.val,(heq p.val (le_of_lt p.property.1)).mpr p.property⟩
  have hg : Continuous g := (localPlane_continuous.comp continuous_subtype_val).subtype_mk _
  have hr : Function.Surjective (V.restrictPreimage f) := by
    intro z
    have hz : 4*z.val.re^2+3*z.val.im^2<3 := z.property
    have hpos : 0<1-z.val.re^2-z.val.im^2 := by nlinarith [sq_nonneg z.val.re]
    let v : EuclideanSpace ℝ (Fin 3) := !₂[Real.sqrt (1-z.val.re^2-z.val.im^2),z.val.re,z.val.im]
    have hv : v ∈ Sphere := by
      have hs := Real.sq_sqrt (le_of_lt hpos)
      have hn : ‖v‖^2=1 := by
        rw [PiLp.norm_sq_eq_of_L2]
        simp only [v, Fin.sum_univ_succ, PiLp.toLp_apply, Matrix.cons_val_zero,
          Matrix.cons_val_succ, Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs,
          Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        nlinarith
      change ‖v-0‖=1
      rw [sub_zero]
      nlinarith [norm_nonneg v]
    let p : Sphere := ⟨v,hv⟩
    have hp : 0≤p.val 0 := Real.sqrt_nonneg _
    have hpz : localPlane p=z.val := by apply Complex.ext <;> rfl
    refine ⟨⟨⟨p,hp⟩,?_⟩,?_⟩
    · change localPlane p ∈ V
      rw [hpz]
      exact z.property
    · exact Subtype.ext hpz
  have hquot : Topology.IsQuotientMap (V.restrictPreimage f) :=
    (hf.isClosedMap.restrictPreimage V).isQuotientMap hf.restrictPreimage hr
  have hgquot : Topology.IsQuotientMap g := Topology.IsQuotientMap.of_comp hq hg hquot
  have hi : Function.Injective g := by
    intro x y h
    have h1 := congrArg (fun z : V => z.val.re) h
    have h2 := congrArg (fun z : V => z.val.im) h
    change x.val.val 1=y.val.val 1 at h1
    change x.val.val 2=y.val.val 2 at h2
    have h0 : x.val.val 0=y.val.val 0 := by
      apply (sq_eq_sq₀ (le_of_lt x.property.1) (le_of_lt y.property.1)).mp
      have hx := hn x.val
      have hy := hn y.val
      rw [h1,h2] at hx
      linarith
    apply Subtype.ext
    apply Subtype.ext
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  have hgHome : IsHomeomorph g := isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hgquot,hi⟩
  exact hV.isOpenEmbedding_subtypeVal.comp hgHome.isOpenEmbedding

/-- A genuine square chart at the first actual branch point. -/
theorem squareBranchChart_at_first (x : Total) (hx : projection x = branchPoint 0) :
    Nonempty (CurveComplex.SquareBranchChart Total Sphere projection x) := by
  classical
  have hb : branchPoint 0 ∈ positivePatch := by
    norm_num [positivePatch,branchPoint,branchVector]
  have hxb : projection x ∈ positivePatch := hx ▸ hb
  let A : Set Total := projection ⁻¹' positivePatch
  have hA : IsOpen A := positivePatch_isOpen.preimage projection_continuous
  let e : PatchTotal ≃ₜ A := patchToOpen_isHomeomorph.homeomorph patchToOpen
  let a : PatchTotal := e.symm ⟨x,hxb⟩
  have ha : patchProjection a=x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hxb⟩)
  letI : Nonempty PatchTotal := ⟨a⟩
  letI : Nonempty positivePatch := ⟨⟨branchPoint 0,hb⟩⟩
  have hpe : Topology.IsOpenEmbedding patchProjection :=
    hA.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
  let up0 := patchRoot_isOpenEmbedding.toOpenPartialHomeomorph patchRoot
  let down0 := localPlane_isOpenEmbedding.toOpenPartialHomeomorph
    (fun b : positivePatch => localPlane b.val)
  let up : OpenPartialHomeomorph Total ℂ := up0.lift_openEmbedding hpe
  let down : OpenPartialHomeomorph Sphere ℂ :=
    down0.lift_openEmbedding positivePatch_isOpen.isOpenEmbedding_subtypeVal
  have hu (a' : PatchTotal) : up (patchProjection a')=patchRoot a' := by
    exact OpenPartialHomeomorph.lift_openEmbedding_apply up0 hpe
  have hd (b : positivePatch) : down b.val=localPlane b.val := by
    exact OpenPartialHomeomorph.lift_openEmbedding_apply down0
      positivePatch_isOpen.isOpenEmbedding_subtypeVal
  have hs (a' : PatchTotal) : down (projection (patchProjection a'))=(up (patchProjection a'))^2 := by
    rw [hu,hd ⟨projection (patchProjection a'),patchProjection_mem a'⟩]
    exact (patchRoot_sq a').symm
  refine ⟨{
    upstairs := up
    downstairs := down
    upstairs_mem := ?_
    downstairs_mem := ?_
    upstairs_center := ?_
    downstairs_center := ?_
    image_mem := ?_
    square := ?_ }⟩
  · change x ∈ patchProjection '' up0.source
    exact ⟨a,Set.mem_univ _,ha⟩
  · change projection x ∈ Subtype.val '' down0.source
    exact ⟨⟨projection x,hxb⟩,Set.mem_univ _,rfl⟩
  · have hzero : (up x)^2=0 := by
      rw [←ha,←hs,ha,hx,hd ⟨branchPoint 0,hb⟩]
      norm_num [localPlane,branchPoint,branchVector] <;> rfl
    exact eq_zero_of_pow_eq_zero hzero
  · rw [hx,hd ⟨branchPoint 0,hb⟩]
    norm_num [localPlane,branchPoint,branchVector] <;> rfl
  · intro y hy
    change y ∈ patchProjection '' up0.source at hy
    obtain ⟨a',_,rfl⟩ := hy
    change projection (patchProjection a') ∈ Subtype.val '' down0.source
    exact ⟨⟨_,patchProjection_mem a'⟩,Set.mem_univ _,rfl⟩
  · intro y hy
    change y ∈ patchProjection '' up0.source at hy
    obtain ⟨a',_,rfl⟩ := hy
    exact hs a'

end AlternatingSphereCover
