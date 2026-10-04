import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMaxSquareRadialQuotient
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Actual joint cone construction for a whole boundary movie. Joint
continuity follows from the constructed compact radial quotient, not assumed
slice-by-slice filling or a presumed cell-extension homotopy. -/
theorem actual_parameterized_square_convex_cone_filling
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C(Interval × {z : ℝ × ℝ // ‖z‖=1},V)) (v : C(Interval,V)) :
    ∃ G : C(Interval × {z : ℝ × ℝ // ‖z‖≤1},V),
      (∀ σ (z : {z : ℝ × ℝ // ‖z‖=1}),G (σ,⟨z.val,z.property.le⟩)=f (σ,z)) ∧
      (∀ (σ r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}),
        ∃ u : {z : ℝ × ℝ // ‖z‖≤1},u.val=(1-r.val) • z.val ∧
          (G (σ,u)).val=(1-r.val) • (f (σ,z)).val+r.val • (v σ).val) := by
  classical
  have hQ : IsCompact {z : ℝ × ℝ | ‖z‖≤1} := by
    convert (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1)) using 1
    ext z
    simp only [mem_ofPred_eq,mem_prod,mem_Icc,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le]
  have hB : IsClosed {z : ℝ × ℝ | ‖z‖=1} :=
    isClosed_eq (continuous_fst.norm.max continuous_snd.norm) continuous_const
  let : CompactSpace {z : ℝ × ℝ // ‖z‖=1} :=
    isCompact_iff_compactSpace.mp (hQ.of_isClosed_subset hB (fun z hz => hz.le))
  obtain ⟨q,hsurj,hfiber,hq⟩ := actual_max_square_radial_quotient
  let domain := (Interval × Interval) × {z : ℝ × ℝ // ‖z‖=1}
  let qp : C(domain,Interval × {z : ℝ × ℝ // ‖z‖≤1}) :=
    ⟨fun a => (a.1.1,q (a.1.2,a.2)),by fun_prop⟩
  have hpsurj : Function.Surjective qp := by
    rintro ⟨σ,u⟩
    obtain ⟨⟨r,z⟩,he⟩ := hsurj u
    exact ⟨((σ,r),z),Prod.ext rfl he⟩
  let K : C(domain,V) :=
    ⟨fun a => ⟨(1-a.1.2.val) • (f (a.1.1,a.2)).val+a.1.2.val • (v a.1.1).val,
      hV (f (a.1.1,a.2)).property (v a.1.1).property
        (sub_nonneg.mpr a.1.2.property.2) a.1.2.property.1 (by ring)⟩,by fun_prop⟩
  have hrespect (a b : domain) (he : qp a=qp b) : K a=K b := by
    have hσ : a.1.1=b.1.1 := congrArg (fun x : Interval × {z : ℝ × ℝ // ‖z‖≤1} => x.1) he
    have hqq : q (a.1.2,a.2)=q (b.1.2,b.2) := congrArg Prod.snd he
    rcases hfiber _ _ hqq with hab | ⟨har,hbr⟩
    · have hr : a.1.2=b.1.2 := congrArg Prod.fst hab
      have hz : a.2=b.2 := congrArg (fun x : Interval × {z : ℝ × ℝ // ‖z‖=1} => x.2) hab
      apply Subtype.ext
      change (1-a.1.2.val) • (f (a.1.1,a.2)).val+a.1.2.val • (v a.1.1).val=
        (1-b.1.2.val) • (f (b.1.1,b.2)).val+b.1.2.val • (v b.1.1).val
      rw [hσ,hr,hz]
    · change a.1.2=1 at har
      change b.1.2=1 at hbr
      apply Subtype.ext
      simp [K,har,hbr,hσ]
  let Gfun : (Interval × {z : ℝ × ℝ // ‖z‖≤1}) → V :=
    fun z => K (Function.surjInv hpsurj z)
  have hGq (a : domain) : Gfun (qp a)=K a :=
    hrespect _ a (Function.surjInv_eq hpsurj (qp a))
  have hquot := qp.continuous.isClosedMap.isQuotientMap qp.continuous hpsurj
  have hGcont : Continuous Gfun := hquot.continuous_iff.mpr (by
    have he : Gfun ∘ qp=K := funext hGq
    rw [he]
    exact K.continuous)
  let G : C(Interval × {z : ℝ × ℝ // ‖z‖≤1},V) := ⟨Gfun,hGcont⟩
  have hformula (σ r : Interval) (z : {z : ℝ × ℝ // ‖z‖=1}) :
      (G (σ,q (r,z))).val=(1-r.val) • (f (σ,z)).val+r.val • (v σ).val :=
    congrArg Subtype.val (hGq ((σ,r),z))
  refine ⟨G,?_,?_⟩
  · intro σ z
    have he : q (0,z)=⟨z.val,z.property.le⟩ := by
      apply Subtype.ext
      rw [hq]
      simp
    apply Subtype.ext
    have hh := hformula σ 0 z
    rw [he] at hh
    change (G (σ,⟨z.val,z.property.le⟩)).val=(1-(0:ℝ)) • (f (σ,z)).val+(0:ℝ) • (v σ).val at hh
    simpa only [sub_zero,one_smul,zero_smul,add_zero] using hh
  · intro σ r z
    exact ⟨q (r,z),hq _,hformula σ r z⟩
end CurveComplex.HyperellipticModel
