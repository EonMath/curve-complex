import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedEndpointClearance
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedArcReverse

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Actual finite disjoint old representatives and a new non-loop source arc
produce class-preserving representatives with BOTH new endpoint collars clear.
The second supported move fixes the entire first collar pointwise. -/
theorem actual_finite_system_both_endpoint_clearance
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) (hne : a.val.map 0 ≠ a.val.map 1) :
    ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
      ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
      (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 →
        (t:ℝ) ≤ δ ∨ 1-δ ≤ (t:ℝ) → ∀ i, b.val.map t ∉ (old' i).val.image := by
  classical
  letI := C.charts
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨old0,b0,δ0,hδ0,hδ0half,hclassOld0,hd0,hclassB0,hb00,hb01,hclear0⟩ :=
    actual_finite_system_initial_endpoint_clearance M C old hd a
  obtain ⟨H,r,hr,hrhalf,w,hmarks,_,hstar⟩ := actual_endpoint_star_normalization M C
    ι old0 hd0 (b0.val.map 1) b0.val.end_marked Set.univ isOpen_univ (Set.mem_univ _)
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
  let old1 := fun i => (old0 i).transport g hfix
  let a1 := b0.transport g hfix
  have h10 : a1.val.map 0 = b0.val.map 0 := hfix _ b0.val.start_marked
  have h11 : a1.val.map 1 = b0.val.map 1 := hfix _ b0.val.end_marked
  have hclass (c : EssentialMarkedArc M) :
      Quotient.mk (essentialArcSetoid M) (c.transport g hfix) = Quotient.mk (essentialArcSetoid M) c := by
    apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image c.val g hfix).symm
  have hne1 : a1.val.map 0 ≠ a1.val.map 1 := by rw [h10,h11,hb00,hb01]; exact hne
  have hclear1 (t : Interval) (ht0 : 0 < (t:ℝ)) (htδ : (t:ℝ) ≤ δ0) (i : ι) :
      a1.val.map t ∉ (old1 i).val.image := by
    intro hx
    change a1.val.map t ∈ ((old0 i).val.transport g hfix).image at hx
    rw [MarkedArc.transport_image] at hx
    obtain ⟨x,hx,he⟩ := hx
    have he' : x = b0.val.map t := g.injective he
    exact hclear0 t ht0 htδ i (he' ▸ hx)
  let prefixCarrier : Set S := a1.val.map '' {t : Interval | (t:ℝ) ≤ δ0}
  have hprefixCarrier : IsClosed prefixCarrier :=
    ((isClosed_le continuous_subtype_val continuous_const).isCompact.image a1.val.continuous).isClosed
  have hend : a1.val.map 1 ∉ prefixCarrier := by
    rintro ⟨t,ht,he⟩
    rcases a1.val.injective_except_loop_closure t 1 he with hh | ⟨h0,h1⟩ | ⟨h1,h0⟩
    · subst t; change (1:ℝ) ≤ δ0 at ht; linarith
    · subst t; exact hne1 he
    · have hh := congrArg Subtype.val h0
      norm_num at hh
  let W : Set S := prefixCarrierᶜ
  have hW : IsOpen W := hprefixCarrier.isOpen_compl
  have hold : ∀ i b, (if b then (old1 i).val.map 1 else (old1 i).val.map 0) = a1.reverse.val.map 0 →
      w (i,b) ≠ 0 ∧
      segment ℝ ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0))
        ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0)+w (i,b)) ⊆
          (chartAt Plane (a1.reverse.val.map 0)).target ∧
      Set.range ((old1 i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
        (chartAt Plane (a1.reverse.val.map 0)).symm ''
          segment ℝ ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0))
            ((chartAt Plane (a1.reverse.val.map 0)) (a1.reverse.val.map 0)+w (i,b)) := by
    intro i b hb
    have hp : a1.reverse.val.map 0 = b0.val.map 1 := by simp [h11]
    have he : (if b then (old0 i).val.map 1 else (old0 i).val.map 0) = b0.val.map 1 := by
      have h0 : (old1 i).val.map 0 = (old0 i).val.map 0 := hfix _ (old0 i).val.start_marked
      have h1 : (old1 i).val.map 1 = (old0 i).val.map 1 := hfix _ (old0 i).val.end_marked
      simpa only [h0,h1,hp] using hb
    obtain ⟨hw,hwt,hwr⟩ := hstar i b he
    refine ⟨hw,by simpa only [hp] using hwt,?_⟩
    rw [hp]
    change Set.range (g ∘ ((old0 i).val.map ∘ endpointGermParameter b r hr _)) = _
    rw [Set.range_comp,← hfinal]
    exact hwr
  obtain ⟨z,δ1,hδ1,hδ1half,hzclass,hz0,hz1,hzout,hzclear⟩ :=
    actual_initial_germ_clearance_against_normalized_old_star M C old1 a1.reverse
      r hr hrhalf w hold W hW (by simpa [W] using hend)
  let δ : ℝ := min δ0 δ1
  have hδ : 0 < δ := lt_min hδ0 hδ1
  have hδhalf : δ < 1/2 := (min_le_left _ _).trans_lt hδ0half
  refine ⟨old1,z.reverse,δ,hδ,hδhalf,?_,?_,?_,?_,?_,?_⟩
  · intro i; exact (hclass (old0 i)).trans (hclassOld0 i)
  · intro i j hij
    exact arcInterior_transport_disjoint (old0 i) (old0 j) g hfix (hd0 i j hij)
  · exact z.reverse_class.trans (hzclass.trans (a1.reverse_class.trans ((hclass b0).trans hclassB0)))
  · simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_zero] using
      hz1.trans (by simpa using h10.trans hb00)
  · simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_one] using
      hz0.trans (by simpa using h11.trans hb01)
  · intro t ht0 ht1 hcol i
    change z.val.map (unitInterval.symm t) ∉ (old1 i).val.image
    rcases hcol with hstart | hendcol
    · have htδ0 : (t:ℝ) ≤ δ0 := hstart.trans (min_le_left _ _)
      have houtside : a1.reverse.val.map (unitInterval.symm t) ∉ W := by
        change a1.val.map (unitInterval.symm (unitInterval.symm t)) ∉ prefixCarrierᶜ
        rw [unitInterval.symm_symm]
        exact fun hh => hh ⟨t,htδ0,rfl⟩
      rw [hzout _ houtside]
      simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_symm] using hclear1 t ht0 htδ0 i
    · apply hzclear
      · change 0 < 1-(t:ℝ); linarith
      · change 1-(t:ℝ) ≤ δ1
        have := min_le_right δ0 δ1
        dsimp [δ] at hendcol
        linarith

end CurveComplex.HyperellipticModel
