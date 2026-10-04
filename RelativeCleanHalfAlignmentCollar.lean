import RelativeCleanHalfAlignmentHelpers
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeBoundaryNullGeometry
import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerCornerGeometryDefinitions
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip
import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.ActualHarerOptionalCollapseGluingProof
import CurveComplexGenusTwo.Topology.ActualFreeBoundaryProviders.FreeStripCrosscutMotion
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualInternalCollarCalibration
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceStripGluing
import CurveComplexGenusTwo.Topology.ActualHarerCrossingAxes.ActualHarerQuadrantHelpers
import Lean.Util.CollectAxioms

open Set Topology CurveComplex Schoenflies

namespace CoherentEndpointMotion.RelativeCleanHalfAlignment

set_option maxHeartbeats 16000000
set_option maxRecDepth 10000

theorem original_clean_half_disk_constructs_relative_collar
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆ (chartAt Plane x).target) :
    let Q : Set S := ((chartAt Plane x).symm '' Metric.ball ((chartAt Plane x) x) R)ᶜ
    let B : Set ↥Q := {y | y.val ∈ (chartAt Plane x).symm ''
      Metric.sphere ((chartAt Plane x) x) R}
    ∀ (a q : C(Interval, ↥Q)) (d : CleanHalfLocalData S Q B a q),
      Nonempty (RelativeHalfCollar d) := by
  classical
  intro Q B a q d
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hgeometry : ∃ (H : C(Interval × Interval,↥Q))
      (eta : C(Interval,Interval × Interval)),
      IsEmbedding H ∧
      (∀ u, H (u,0) = d.sideArc u) ∧
      (∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      range H ⊆ d.W ∧
      range H ∩ range d.e = range d.sideArc ∧
      ((eta 1).2 = 1 ∧ (eta 1).1 ∈ Ioo (0 : Interval) 1) ∧
      (∀ u ∈ Ioo (0 : Interval) 1,
        eta u ∈ Ioo (0 : Interval) 1 ×ˢ Ioo (0 : Interval) 1) ∧
      (∀ u : Interval,
        H (eta u) = q (d.xi (Set.Icc.convexComb d.s d.t u))) ∧
      Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range H) := by
    let exact_exterior_half : ∀     (X : Type) [TopologicalSpace X] [T2Space X]
    (B : Set X) (D : C(Interval × Interval,X)) (hD : IsEmbedding D)
    (E : C(Interval × Icc (-1:ℝ) 1,X)) (hE : IsEmbedding E)
    (hc : ∀ t, E (t,⟨0,by norm_num⟩) = D (t,0))
    (hEB : ∀ z, E z ∈ B ↔ z.1 = 0 ∨ z.1 = 1)
    (hopen : IsOpen (E '' {z | -1 < z.2.val ∧ z.2.val < 1})),
    ∃ L : C(Interval × Interval,X), IsEmbedding L ∧
      (∀ t, L (t,0) = D (t,0)) ∧ range L ⊆ range E ∧
      range L ∩ range D = range (fun t : Interval => D (t,0)) ∧
      (∀ z, L z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
        ∀ (z : Interval × Interval) (w : Icc (-1:ℝ) 1),
          (w:ℝ) = ρ*(σ*(z.2:ℝ)) → L z = E (z.1,w) := by
      intro X _ _ B D hD E hE hc hEB hopen
      let U : Set X := E '' {z | -1 < z.2.val ∧ z.2.val < 1}
      have hprod : (univ : Set Interval) ×ˢ ({0} : Set Interval) ⊆ D ⁻¹' U := by
        rintro ⟨t,w⟩ ⟨_,hw⟩
        obtain rfl := mem_singleton_iff.mp hw
        exact ⟨(t,⟨0,by norm_num⟩),by norm_num,hc t⟩
      obtain ⟨A,V,hA,hV,hIA,h0V,hAV⟩ :=
        generalized_tube_lemma isCompact_univ isCompact_singleton
          (hopen.preimage D.continuous) hprod
      obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton _))
      let δ : ℝ := min (r/2) (1/2)
      have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
      have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
      have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
      let scale : Interval × Interval → Interval × Interval := fun z =>
        (z.1,⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ,hδ1]⟩)
      have hsc : Continuous scale := by dsimp [scale]; fun_prop
      have hthin (z : Interval × Interval) : D (scale z) ∈ U := by
        apply hAV
        refine ⟨hIA (mem_univ _),hrV ?_⟩
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |δ*(z.2:ℝ)-0| < r
        rw [sub_zero,abs_of_nonneg (mul_nonneg hδ.le z.2.property.1)]
        exact (mul_le_of_le_one_right hδ.le z.2.property.2).trans_lt hδr
      let e := hE.toHomeomorph
      let k : C(Interval × Interval,Interval × Icc (-1:ℝ) 1) :=
        ⟨fun z => e.symm ⟨D (scale z),image_subset_range E _ (hthin z)⟩,
          e.symm.continuous.comp ((D.continuous.comp hsc).subtype_mk _)⟩
      have hEk (z) : E (k z) = D (scale z) :=
        congrArg Subtype.val (e.apply_symm_apply _)
      have hn (z : Interval × Interval) (hz : 0 < z.2) : ((k z).2:ℝ) ≠ 0 := by
        intro he
        have hw : (k z).2 = (⟨0,by norm_num⟩ : Icc (-1:ℝ) 1) := Subtype.ext he
        have hm : E (k z) = D ((k z).1,0) := by
          rw [show k z = ((k z).1,⟨0,by norm_num⟩) from Prod.ext rfl hw,hc]
        have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ))
          (hD.injective (hm.symm.trans (hEk z)))
        change 0 = δ*(z.2:ℝ) at hh
        have hz' : (0:ℝ) < z.2 := hz
        exact (mul_pos hδ hz').ne' hh.symm
      have hp : IsPreconnected ((univ : Set Interval) ×ˢ Ioi (0:Interval)) :=
        isPreconnected_univ.prod isPreconnected_Ioi
      have hside := hp.mapsTo_Ioi_or_Iio
        (show Continuous (fun z => ((k z).2:ℝ)) from
          continuous_subtype_val.comp (continuous_snd.comp k.continuous)).continuousOn
        (fun z hz => hn z hz.2)
      let F : Set X := D '' {z | δ ≤ (z.2:ℝ)}
      have hF : IsClosed F := ((isClosed_le continuous_const
        (continuous_subtype_val.comp continuous_snd)).isCompact.image D.continuous).isClosed
      have hcenterF (t : Interval) : E (t,⟨0,by norm_num⟩) ∉ F := by
        rw [hc]
        rintro ⟨z,hz,he⟩
        have hh := congrArg (fun z : Interval × Interval => (z.2:ℝ)) (hD.injective he)
        change (z.2:ℝ) = 0 at hh
        change δ ≤ (z.2:ℝ) at hz
        rw [hh] at hz
        linarith
      obtain ⟨ρ,hρ,N,hN,hNF,hNform,hNcenter⟩ :=
        source_shrink_embedded_strip_in_open E hE Fᶜ hF.isOpen_compl hcenterF
      have build (σ : ℝ) (hσ : σ = -1 ∨ σ = 1)
          (hopp : ∀ z, 0 < z.2 → σ*((k z).2:ℝ) < 0) :
          ∃ L : C(Interval × Interval,X), IsEmbedding L ∧
            (∀ t, L (t,0) = D (t,0)) ∧ range L ⊆ range E ∧
            range L ∩ range D = range (fun t : Interval => D (t,0)) ∧
            (∀ z, L z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
          ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧
            ∀ (z : Interval × Interval) (w : Icc (-1:ℝ) 1),
              (w:ℝ) = ρ*(σ*(z.2:ℝ)) → L z = E (z.1,w) := by
        have hσn : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
        have hσ2 : σ*σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
        let m : Interval × Interval → Interval × Icc (-1:ℝ) 1 := fun z =>
          (z.1,⟨σ*(z.2:ℝ),by rcases hσ with rfl | rfl <;>
            constructor <;> linarith [z.2.property.1,z.2.property.2]⟩)
        have hmc : Continuous m := by dsimp [m]; fun_prop
        have hmi : Function.Injective m := by
          intro z v he
          apply Prod.ext
          · simpa only [m] using congrArg Prod.fst he
          · apply Subtype.ext
            exact mul_left_cancel₀ hσn (congrArg (fun z => (z.2:ℝ)) he)
        let L : C(Interval × Interval,X) := ⟨N ∘ m,hN.continuous.comp hmc⟩
        have hL : IsEmbedding L := hN.comp (hmc.isClosedEmbedding hmi).isEmbedding
        have hL0 (t : Interval) : L (t,0) = D (t,0) := by
          change N (m (t,0)) = _
          rw [show m (t,0) = (t,⟨0,by norm_num⟩) from Prod.ext rfl (Subtype.ext (mul_zero σ)),hNcenter,hc]
        have hform (z) : L z = E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
            rcases hσ with rfl | rfl <;> constructor <;>
            nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) := hNform (m z)
        have hmeet (z : Interval × Interval) (hz : L z ∈ range D) : z.2 = 0 := by
          obtain ⟨v,hv⟩ := hz
          have hvδ : (v.2:ℝ) < δ := lt_of_not_ge (fun hh =>
            (hNF (mem_range_self (m z))) ⟨v,hh,hv⟩)
          let w : Interval := ⟨(v.2:ℝ)/δ,⟨div_nonneg v.2.property.1 hδ.le,
            (div_le_one hδ).mpr hvδ.le⟩⟩
          have hs : scale (v.1,w) = v := by
            apply Prod.ext
            · rfl
            apply Subtype.ext
            change δ*((v.2:ℝ)/δ) = (v.2:ℝ)
            field_simp [hδ.ne']
          have he : E (k (v.1,w)) = E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
              rcases hσ with rfl | rfl <;> constructor <;>
              nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) := by
            exact (hEk _).trans ((congrArg D hs).trans (hv.trans (hform z)))
          have hk := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he)
          by_cases hw0 : v.2 = 0
          · have hv0 : v = (v.1,0) := by
              apply Prod.ext
              · rfl
              · exact hw0
            have he' : E (z.1,⟨ρ*(σ*(z.2:ℝ)),by
                rcases hσ with rfl | rfl <;> constructor <;>
                nlinarith [hρ.1,hρ.2,z.2.property.1,z.2.property.2]⟩) = E (v.1,⟨0,by norm_num⟩) := by
              exact (hform z).symm.trans (hv.symm.trans
                ((congrArg D hv0).trans (hc v.1).symm))
            have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hE.injective he')
            apply Subtype.ext
            change (z.2:ℝ) = 0
            change ρ*(σ*(z.2:ℝ)) = 0 at hh
            exact ((mul_eq_zero.mp hh).resolve_left hρ.1.ne' |> mul_eq_zero.mp).resolve_left hσn
          · have hvpos : (0:ℝ) < v.2 := lt_of_le_of_ne v.2.property.1
              (fun he => hw0 (Subtype.ext he.symm))
            have hwpos : (0:Interval) < w := div_pos hvpos hδ
            have hh := hopp (v.1,w) hwpos
            rw [hk] at hh
            have hnon : 0 ≤ σ*(ρ*(σ*(z.2:ℝ))) := by
              rcases hσ with rfl | rfl <;> nlinarith [hρ.1,z.2.property.1]
            exact False.elim (not_lt_of_ge hnon hh)
        refine ⟨L,hL,hL0,?_,?_,?_,ρ,hρ.1,hρ.2,σ,hσ,?_⟩
        · rintro y ⟨z,rfl⟩
          rw [hform]
          exact mem_range_self _
        · ext y
          constructor
          · rintro ⟨⟨z,rfl⟩,hz⟩
            have h0 := hmeet z hz
            exact ⟨z.1,(hL0 z.1).symm.trans (congrArg L (Prod.ext rfl h0.symm))⟩
          · rintro ⟨t,rfl⟩
            exact ⟨⟨(t,0),hL0 t⟩,mem_range_self (t,0)⟩
        · intro z
          rw [hform,hEB]
        · intro z w hw
          exact (hform z).trans (congrArg E (Prod.ext rfl (Subtype.ext hw.symm)))
      rcases hside with hside | hside
      · apply build (-1) (Or.inl rfl)
        intro z hz
        have hh := hside ⟨mem_univ _,hz⟩
        change 0 < ((k z).2:ℝ) at hh
        linarith
      · apply build 1 (Or.inr rfl)
        intro z hz
        have hh := hside ⟨mem_univ _,hz⟩
        change ((k z).2:ℝ) < 0 at hh
        simpa only [one_mul] using hh
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `exact_exterior_half
      let some value := localDecl.value? | Lean.throwError "Missing local exact_exterior_half value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected exact_exterior_half axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS exact_exterior_half: {found.toList}"
    let patch_side_clocks : ∀     (A ε : ℝ) (hA : 0 < A) (hAr : A < d.radius)
    (P : C(Interval × Interval,↥Q)) (hP : IsEmbedding P)
    (hsrc : ∀ z, (P z).val ∈ d.cornerChart.source)
    (hside : ∀ z, P z ∈ range d.sideArc ↔ z.2 = 0)
    (hleft : ∀ w, d.cornerChart (P (0,w)).val = Plane.mk (d.sigma*A) (-d.tau*ε*(w:ℝ)))
    (hright : ∀ w, d.cornerChart (P (1,w)).val = Plane.mk (-d.sigma*ε*(w:ℝ)) (d.tau*A)),
    ∃ c α β : Interval, 0 < α ∧ α < c ∧ c < β ∧ β < 1 ∧
      d.sideArc c = d.M.first 1 ∧ d.sideArc α = P (0,0) ∧ d.sideArc β = P (1,0) ∧
      range (fun u : Interval => P (u,0)) = d.sideArc '' Icc α β := by
      intro A ε hA hAr P hP hsrc hside hleft hright
    
      let side_clocks :
          ∃ c ∈ Ioo (0 : Interval) 1, d.sideArc c = d.M.first 1 ∧
            range d.M.first = d.sideArc '' Icc 0 c ∧
            range d.M.second = d.sideArc '' Icc c 1 := by
        obtain ⟨c,hc,hsidec⟩ := actual_side_corner_parameter d
        have hfirst : range d.M.first ⊆ range d.sideArc := by
          rw [d.side_range]
          exact subset_union_left
        have hsecond : range d.M.second ⊆ range d.sideArc := by
          rw [d.side_range]
          exact subset_union_right
        have hf := ActualHarerCornerGeometry.embedded_subarc_parameter_interval d.sideArc d.M.first d.side_embedded
          d.M.first_embedded hfirst 0 c d.side_zero hsidec
        have hs := ActualHarerCornerGeometry.embedded_subarc_parameter_interval d.sideArc d.M.second d.side_embedded
          d.M.second_embedded hsecond 1 c d.side_one (hsidec.trans d.M.corner_eq)
        refine ⟨c,hc,hsidec,?_,?_⟩
        · simpa only [uIcc_of_le hc.1.le] using hf.2
        · simpa only [uIcc_of_ge hc.2.le] using hs.2
      obtain ⟨c,hc,hcside,hfirst,hsecond⟩ := side_clocks
      obtain ⟨α,hα⟩ := (hside (0,0)).mpr rfl
      obtain ⟨β,hβ⟩ := (hside (1,0)).mpr rfl
      have hσ : d.sigma*d.sigma = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hτ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have haσ : |d.sigma| = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have haτ : |d.tau| = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hp0 : d.cornerChart (P (0,0)).val = Plane.mk (d.sigma*A) 0 := by simpa using hleft 0
      have hp1 : d.cornerChart (P (1,0)).val = Plane.mk 0 (d.tau*A) := by simpa using hright 0
      have hC0 : d.cornerChart (d.M.first 1).val = 0 := by rw [← d.a_corner]; exact d.axes.center_zero
      have hfirstport : P (0,0) ∈ range d.M.first := by
        have hx : |(Plane.mk (d.sigma*A) 0) 0| < d.radius := by
          simpa [Plane.mk,abs_mul,haσ,abs_of_pos hA] using hAr
        have hy : |(Plane.mk (d.sigma*A) 0) 1| < d.radius := by simpa [Plane.mk] using d.radius_bounds.1
        have hm := (d.same_disk_quadrant _ hx hy).1.mpr (by
          constructor
          · simp [Plane.mk]
          · simpa [Plane.mk,← mul_assoc,hσ] using hA.le)
        rw [← hp0,d.cornerChart.left_inv (hsrc (0,0))] at hm
        obtain ⟨v,hv⟩ := hm
        exact ⟨v,Subtype.ext hv⟩
      have hsecondport : P (1,0) ∈ range d.M.second := by
        have hx : |(Plane.mk 0 (d.tau*A)) 0| < d.radius := by simpa [Plane.mk] using d.radius_bounds.1
        have hy : |(Plane.mk 0 (d.tau*A)) 1| < d.radius := by
          simpa [Plane.mk,abs_mul,haτ,abs_of_pos hA] using hAr
        have hm := (d.same_disk_quadrant _ hx hy).2.1.mpr (by
          constructor
          · simp [Plane.mk]
          · simpa [Plane.mk,← mul_assoc,hτ] using hA.le)
        rw [← hp1,d.cornerChart.left_inv (hsrc (1,0))] at hm
        obtain ⟨v,hv⟩ := hm
        exact ⟨v,Subtype.ext hv⟩
      have hαc : α ≤ c := by
        rw [hfirst] at hfirstport
        obtain ⟨u,hu,he⟩ := hfirstport
        have heq := d.side_embedded.injective (he.trans hα.symm)
        exact heq ▸ hu.2
      have hcβ : c ≤ β := by
        rw [hsecond] at hsecondport
        obtain ⟨u,hu,he⟩ := hsecondport
        have heq := d.side_embedded.injective (he.trans hβ.symm)
        exact heq ▸ hu.1
      have hαne : α ≠ c := by
        intro he
        have hp : P (0,0) = d.M.first 1 := hα.symm.trans ((congrArg d.sideArc he).trans hcside)
        have hh := congrArg (fun z : Plane => z 0) (hp0.symm.trans ((congrArg (fun y : ↥Q => d.cornerChart y.val) hp).trans hC0))
        have hh' : d.sigma*A = 0 := by simpa [Plane.mk] using hh
        rcases d.signs.1 with hs | hs <;> rw [hs] at hh' <;> linarith
      have hβne : c ≠ β := by
        intro he
        have hp : P (1,0) = d.M.first 1 := hβ.symm.trans ((congrArg d.sideArc he.symm).trans hcside)
        have hh := congrArg (fun z : Plane => z 1) (hp1.symm.trans ((congrArg (fun y : ↥Q => d.cornerChart y.val) hp).trans hC0))
        have hh' : d.tau*A = 0 := by simpa [Plane.mk] using hh
        rcases d.signs.2 with hs | hs <;> rw [hs] at hh' <;> linarith
      have hα0 : α ≠ 0 := by
        intro he
        have hp : P (0,0) = d.M.boundarySide 0 := hα.symm.trans
          ((congrArg d.sideArc he).trans (d.side_zero.trans d.M.boundary_zero.symm))
        exact Set.disjoint_left.mp d.axis_beta_clear (hsrc (0,0)) ⟨0,congrArg Subtype.val hp.symm⟩
      have hβ1 : β ≠ 1 := by
        intro he
        have hp : P (1,0) = d.M.boundarySide 1 := hβ.symm.trans
          ((congrArg d.sideArc he).trans (d.side_one.trans d.M.boundary_one.symm))
        exact Set.disjoint_left.mp d.axis_beta_clear (hsrc (1,0)) ⟨1,congrArg Subtype.val hp.symm⟩
      have hαc' : α < c := lt_of_le_of_ne hαc hαne
      have hcβ' : c < β := lt_of_le_of_ne hcβ hβne
      let seam : C(Interval,↥Q) := ⟨fun u => P (u,0),P.continuous.comp (continuous_id.prodMk continuous_const)⟩
      have hemb : IsEmbedding seam := hP.comp
        ((continuous_id.prodMk continuous_const).isClosedEmbedding (by
          intro u v he
          exact congrArg Prod.fst he)).isEmbedding
      have hs : range seam ⊆ range d.sideArc := by
        rintro y ⟨u,rfl⟩
        exact (hside (u,0)).mpr rfl
      have hclock := ActualHarerCornerGeometry.embedded_subarc_parameter_interval d.sideArc seam d.side_embedded hemb hs α β hα hβ
      refine ⟨c,α,β,bot_lt_iff_ne_bot.mpr hα0,hαc',hcβ',lt_top_iff_ne_top.mpr hβ1,hcside,hα,hβ,?_⟩
      simpa only [uIcc_of_le (hαc'.trans hcβ').le,seam,ContinuousMap.coe_mk] using hclock.2
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `patch_side_clocks
      let some value := localDecl.value? | Lean.throwError "Missing local patch_side_clocks value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected patch_side_clocks axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS patch_side_clocks: {found.toList}"
    let first_port_exterior : ∀ (hBclosed : IsClosed B)
    (A : ℝ) (hA : 0 < A) (hAr : A < d.radius)
    (α : Interval) (hα : α ∈ Ioo (0:Interval) 1)
    (hsrc : (d.sideArc α).val ∈ d.cornerChart.source)
    (hcoord : d.cornerChart (d.sideArc α).val = Plane.mk (d.sigma*A) 0),
    ∃ H : C(Interval × Interval,↥Q), IsEmbedding H ∧
      (∀ u, H (u,0) = d.sideArc u) ∧
      (∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      range H ⊆ d.W ∧ range H ∩ range d.e = range d.sideArc ∧
      ∃ lam η : ℝ, 0 < lam ∧ 0 < η ∧
        ∀ (u w : Interval), |(u:ℝ)-(α:ℝ)| < η →
          (H (u,w)).val ∈ d.cornerChart.source ∧
          d.cornerChart (H (u,w)).val =
            Plane.mk (d.cornerChart (d.sideArc u).val 0) (-d.tau*lam*(w:ℝ)) ∧
          0 < d.sigma*d.cornerChart (H (u,w)).val 0 ∧
          |d.cornerChart (H (u,w)).val 0| < d.radius ∧
          |d.cornerChart (H (u,w)).val 1| < d.radius := by
      intro hBclosed A hA hAr α hα hsrc hcoord
    
      let chartQ : OpenPartialHomeomorph ↥Q Plane := {
        toPartialEquiv := {
          toFun := fun y => d.cornerChart y.val
          invFun := fun z => if hz : z ∈ d.cornerChart.target then
            ⟨d.cornerChart.symm z,interior_subset (d.axis_interior (d.cornerChart.map_target hz))⟩
            else d.sideArc α
          source := (Subtype.val : ↥Q → S) ⁻¹' d.cornerChart.source
          target := d.cornerChart.target
          map_source' := fun _ hy => d.cornerChart.map_source hy
          map_target' := by
            intro z hz
            simp only [dif_pos hz,mem_preimage]
            exact d.cornerChart.map_target hz
          left_inv' := by
            intro y hy
            apply Subtype.ext
            simp only [dif_pos (d.cornerChart.map_source hy)]
            exact d.cornerChart.left_inv hy
          right_inv' := by
            intro z hz
            simp only [dif_pos hz]
            exact d.cornerChart.right_inv hz
        }
        open_source := d.cornerChart.open_source.preimage continuous_subtype_val
        open_target := d.cornerChart.open_target
        continuousOn_toFun := d.cornerChart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
        continuousOn_invFun := by
          apply IsInducing.subtypeVal.continuousOn_iff.mpr
          apply d.cornerChart.continuousOn_symm.congr
          intro z hz
          simp only [Function.comp_apply,dif_pos hz]
      }
      have hσ : d.sigma*d.sigma = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have haσ : |d.sigma| = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hside_disk : range d.sideArc ⊆ range d.e := by
        rw [d.side_range]
        rintro y (hy | hy)
        · exact (d.disk_a_trace.symm ▸ hy).1
        · exact (d.disk_q_trace.symm ▸ hy).1
      obtain ⟨E,hE,hEc,hEB,hEopen,hEW⟩ := actual_signed_side_strip_in_W d
      let O : Set Plane := {z | 0 < d.sigma*z 0 ∧ |z 0| < d.radius ∧ |z 1| < d.radius}
      have hO : IsOpen O := by
        exact (isOpen_lt continuous_const (show Continuous (fun z : Plane => d.sigma*z 0) by fun_prop)).inter
          ((isOpen_lt (show Continuous (fun z : Plane => |z 0|) by fun_prop) continuous_const).inter
            (isOpen_lt (show Continuous (fun z : Plane => |z 1|) by fun_prop) continuous_const))
      let T : Set ↥Q := (chartQ.source ∩ chartQ ⁻¹' O) ∩ (Bᶜ ∩ d.W)
      have hT : IsOpen T := (chartQ.isOpen_inter_preimage hO).inter
        (hBclosed.isOpen_compl.inter d.W_open)
      let C0 := chartQ.restrOpen T hT
      let translate : Plane ≃ₜ Plane := {
        toFun := fun z => Plane.mk (z 0-d.sigma*A) (z 1)
        invFun := fun z => Plane.mk (z 0+d.sigma*A) (z 1)
        left_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
        right_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop
      }
      let D := C0.transHomeomorph translate
      have hDsource : D.source = chartQ.source ∩ T := rfl
      have hDfun (y : ↥Q) : D y = Plane.mk (d.cornerChart y.val 0-d.sigma*A) (d.cornerChart y.val 1) := rfl
      have hαD : d.sideArc α ∈ D.source := by
        rw [hDsource]
        refine ⟨hsrc,⟨⟨hsrc,?_⟩,d.side_interior α hα,hEW ?_⟩⟩
        · change 0 < d.sigma*(d.cornerChart (d.sideArc α).val) 0 ∧
            |(d.cornerChart (d.sideArc α).val) 0| < d.radius ∧
            |(d.cornerChart (d.sideArc α).val) 1| < d.radius
          rw [hcoord]
          simpa [Plane.mk,← mul_assoc,hσ,abs_mul,haσ,abs_of_pos hA] using ⟨hA,hAr,d.radius_bounds.1⟩
        · exact ⟨(α,⟨0,by norm_num⟩),hEc α⟩
      have hD0 : D (d.sideArc α) = 0 := by
        rw [hDfun,hcoord]
        simp [Plane.mk]
      have haxis (u : Interval) (hu : d.sideArc u ∈ D.source) : D (d.sideArc u) 1 = 0 := by
        have husrc : (d.sideArc u).val ∈ d.cornerChart.source := hu.1
        have hsmall := hu.2.1.2
        change 0 < d.sigma*(d.cornerChart (d.sideArc u).val) 0 ∧
          |(d.cornerChart (d.sideArc u).val) 0| < d.radius ∧
          |(d.cornerChart (d.sideArc u).val) 1| < d.radius at hsmall
        have hval : d.cornerChart.symm (d.cornerChart (d.sideArc u).val) = (d.sideArc u).val :=
          d.cornerChart.left_inv husrc
        have hsides := (d.same_disk_quadrant _ hsmall.2.1 hsmall.2.2)
        have hm := mem_range_self (f := d.sideArc) u
        rw [d.side_range] at hm
        rcases hm with ⟨v,hv⟩ | ⟨v,hv⟩
        · have hfirst : d.cornerChart.symm (d.cornerChart (d.sideArc u).val) ∈
              range (fun w => (d.M.first w).val) := ⟨v,(congrArg Subtype.val hv).trans hval.symm⟩
          simpa [hDfun,Plane.mk] using (hsides.1.mp hfirst).1
        · have hsecond : d.cornerChart.symm (d.cornerChart (d.sideArc u).val) ∈
              range (fun w => (d.M.second w).val) := ⟨v,(congrArg Subtype.val hv).trans hval.symm⟩
          have hx := (hsides.2.1.mp hsecond).1
          rw [hx,mul_zero] at hsmall
          exact False.elim ((lt_irrefl 0) hsmall.1)
      let V : Set ↥Q := D.source
      have hVo : IsOpen V := D.open_source
      have hVB : V ⊆ Bᶜ := fun y hy => hy.2.2.1
      have hVW : V ⊆ d.W := fun y hy => hy.2.2.2
      obtain ⟨ω,hω,sgn,δ,η,Ψ,hsgn,hδ,hη,hΨside,hΨoutside,hΨcal⟩ :=
        source_internal_collar_calibration d.sideArc d.side_embedded E hE hEc α hα
          D hαD hD0 haxis univ V isOpen_univ hVo (subset_univ _) hαD (subset_univ _)
      let scale : Interval × Icc (-1:ℝ) 1 → Interval × Icc (-1:ℝ) 1 :=
        fun z => (z.1,⟨ω*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hω.1,hω.2]⟩)
      have hsc : Continuous scale := by dsimp [scale]; fun_prop
      have hsi : Function.Injective scale := by
        intro z w he
        apply Prod.ext
        · simpa only [scale] using congrArg Prod.fst he
        · apply Subtype.ext
          exact mul_left_cancel₀ hω.1.ne' (congrArg (fun p : Interval × Icc (-1:ℝ) 1 => (p.2:ℝ)) he)
      let N : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨E ∘ scale,E.continuous.comp hsc⟩
      have hN : IsEmbedding N := hE.comp (hsc.isClosedEmbedding hsi).isEmbedding
      have hform (z) : N z = E (z.1,⟨ω*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hω.1,hω.2]⟩) := rfl
      let Ecal : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨Ψ ∘ N,Ψ.continuous.comp N.continuous⟩
      have hEcal : IsEmbedding Ecal := Ψ.isEmbedding.comp hN
      have hEcalc (u) : Ecal (u,⟨0,by norm_num⟩) = d.sideArc u := by
        change Ψ (E (u,⟨ω*0,_⟩)) = _
        simpa only [mul_zero,hEc] using hΨside u
      have hΨB (y : ↥Q) : Ψ y ∈ B ↔ y ∈ B := by
        constructor
        · intro hy
          have he := hΨoutside (Ψ y) (fun hv => hVB hv hy)
          have hh : y = Ψ y := Ψ.injective he.symm
          exact hh ▸ hy
        · intro hy
          rw [hΨoutside y (fun hv => hVB hv hy)]
          exact hy
      have hEcalB (z) : Ecal z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
        change Ψ (N z) ∈ B ↔ _
        rw [hΨB,hform,hEB]
      have hEcalW : range Ecal ⊆ d.W := by
        rintro y ⟨z,rfl⟩
        have hnW : N z ∈ d.W := hEW (mem_range_self (scale z))
        by_contra he
        have hfix : Ψ (Ecal z) = Ecal z := hΨoutside _ (fun hv => he (hVW hv))
        have hh : N z = Ecal z := Ψ.injective hfix.symm
        exact he (hh ▸ hnW)
      have hNopen : IsOpen (N '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
        -- A narrower signed strip has an open band by the same inducing argument.
        let V : Set (Interval × Icc (-1:ℝ) 1) := {z | -ω < z.2.val ∧ z.2.val < ω}
        have hV : IsOpen V := (isOpen_lt continuous_const
          (continuous_subtype_val.comp continuous_snd)).inter
            (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
        obtain ⟨A,hA,hEA⟩ := hE.isInducing.image_eq_isOpen_inter_range hV
        have hVsub : V ⊆ {z | -1 < z.2.val ∧ z.2.val < 1} := by
          intro z hz
          exact ⟨lt_of_le_of_lt (by linarith [hω.2]) hz.1,hz.2.trans_le hω.2⟩
        have hEq : E '' V = A ∩ E '' {z | -1 < z.2.val ∧ z.2.val < 1} := by
          apply Subset.antisymm
          · intro y hy
            exact ⟨(hEA ▸ hy).1,image_mono hVsub hy⟩
          · intro y hy
            rw [hEA]
            exact ⟨hy.1,image_subset_range E _ hy.2⟩
        have hImage : N '' {z | -1 < z.2.val ∧ z.2.val < 1} = E '' V := by
          ext y
          constructor
          · rintro ⟨z,hz,rfl⟩
            refine ⟨(z.1,⟨ω*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hω.1,hω.2]⟩),?_,(hform z).symm⟩
            change -ω < ω*z.2 ∧ ω*z.2 < ω
            constructor <;> nlinarith [hz.1,hz.2,hω.1]
          · rintro ⟨z,hz,rfl⟩
            let w : Icc (-1:ℝ) 1 := ⟨z.2.val/ω,by
              constructor
              · apply (le_div_iff₀ hω.1).mpr; linarith [hz.1]
              · apply (div_le_iff₀ hω.1).mpr; linarith [hz.2]⟩
            have hw : -1 < w.val ∧ w.val < 1 := by
              dsimp [w]
              constructor
              · apply (lt_div_iff₀ hω.1).mpr; linarith [hz.1]
              · apply (div_lt_iff₀ hω.1).mpr; linarith [hz.2]
            refine ⟨(z.1,w),hw,?_⟩
            change N (z.1,w) = _
            rw [hform]
            apply congrArg E
            apply Prod.ext
            · rfl
            · apply Subtype.ext
              change ω*(z.2.val/ω) = z.2.val
              field_simp [hω.1.ne']
        rw [hImage,hEq]
        exact hA.inter hEopen
      have hEcalopen : IsOpen (Ecal '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
        have heq : Ecal '' {z | -1 < z.2.val ∧ z.2.val < 1} =
            Ψ '' (N '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
          simpa only [Ecal,ContinuousMap.coe_mk] using image_comp Ψ N {z | -1 < z.2.val ∧ z.2.val < 1}
        rw [heq]
        exact Ψ.isOpenMap _ hNopen
      obtain ⟨P,hP,hPr,hPt,hPo⟩ :=
        ActualHarerDiskGluing.actual_two_side_disk_constructs_prescribed_edge_square
          d.sideArc d.M.boundarySide d.e d.side_embedded d.M.boundary_embedded d.e_embedded
          (d.side_zero.trans d.M.boundary_zero.symm) (d.side_one.trans d.M.boundary_one.symm)
          (actual_two_side_boundary d) (fun u v he => (actual_side_beta_collision d u v).mp he)
      let flip := (Homeomorph.refl Interval).prodCongr unitInterval.symmHomeomorph
      let Disk : C(Interval × Interval,↥Q) := ⟨P ∘ flip,P.continuous.comp flip.continuous⟩
      have hDisk : IsEmbedding Disk := hP.comp flip.isEmbedding
      have hDiskcenter (u) : Disk (u,0) = d.sideArc u := by
        change P (u,unitInterval.symm 0) = _
        rw [unitInterval.symm_zero,hPt]
      have hDiskr : range Disk = range d.e := by
        change range (P ∘ flip) = _
        rw [flip.surjective.range_comp,hPr]
      obtain ⟨H,hH,hc,hHE,hinter,hB,ρ,hρ0,hρ1,bank,hbank,hHform⟩ :=
        exact_exterior_half ↥Q B Disk hDisk Ecal hEcal
          (fun u => (hEcalc u).trans (hDiskcenter u).symm) hEcalB hEcalopen
      have hseam (u) : H (u,0) = d.sideArc u := (hc u).trans (hDiskcenter u)
      have hmeet : range H ∩ range d.e = range d.sideArc := by
        rw [← hDiskr,hinter]
        congr 1
        funext u
        exact hDiskcenter u
      have hcal (u w : Interval) (hu : |(u:ℝ)-(α:ℝ)| < η) :
          H (u,w) ∈ D.source ∧
          D (H (u,w)) = Plane.mk (D (d.sideArc u) 0) (sgn*δ*(ρ*(bank*(w:ℝ)))) := by
        let ww : Icc (-1:ℝ) 1 := ⟨ρ*(bank*(w:ℝ)),by
          rcases hbank with rfl | rfl <;> constructor <;> nlinarith [w.property.1,w.property.2,hρ0,hρ1]⟩
        rw [hHform (u,w) ww rfl]
        exact hΨcal u ww hu
      have hnonD : H (α,1) ∉ range d.e := by
        intro he
        have hh : H (α,1) ∈ range d.sideArc := hmeet ▸ ⟨mem_range_self _,he⟩
        obtain ⟨v,hv⟩ := hh
        have heq := hH.injective ((hseam v).trans hv)
        have hf := congrArg Prod.snd heq
        exact one_ne_zero hf.symm
      have hbankeq : sgn*bank = -d.tau := by
        have hcal1 := hcal α 1 (by simpa using hη)
        have hcoord1 : d.cornerChart (H (α,1)).val = Plane.mk (d.sigma*A) (sgn*δ*(ρ*bank)) := by
          apply PiLp.ext
          intro i
          fin_cases i
          · have hh := congrArg (fun z : Plane => z 0) hcal1.2
            change d.cornerChart (H (α,1)).val 0-d.sigma*A =
              d.cornerChart (d.sideArc α).val 0-d.sigma*A at hh
            rw [hcoord] at hh
            change d.cornerChart (H (α,1)).val 0-d.sigma*A = d.sigma*A-d.sigma*A at hh
            change d.cornerChart (H (α,1)).val 0 = d.sigma*A
            exact sub_left_inj.mp hh
          · have hh := congrArg (fun z : Plane => z 1) hcal1.2
            simpa [hDfun,Plane.mk] using hh
        have hs := hcal1.1.2.1.2
        change 0 < d.sigma*(d.cornerChart (H (α,1)).val) 0 ∧
          |(d.cornerChart (H (α,1)).val) 0| < d.radius ∧
          |(d.cornerChart (H (α,1)).val) 1| < d.radius at hs
        have hnot : ¬ (0 ≤ d.sigma*(d.cornerChart (H (α,1)).val) 0 ∧
            0 ≤ d.tau*(d.cornerChart (H (α,1)).val) 1) := by
          intro hh
          have hmem := (d.same_disk_quadrant _ hs.2.1 hs.2.2).2.2.mpr hh
          rw [d.cornerChart.left_inv hcal1.1.1] at hmem
          obtain ⟨v,hv⟩ := hmem
          exact hnonD ⟨v,Subtype.ext hv⟩
        have hneg : d.tau*(sgn*δ*(ρ*bank)) < 0 := by
          apply lt_of_not_ge
          intro hh
          apply hnot
          exact ⟨hs.1.le,by simpa [hcoord1,Plane.mk] using hh⟩
        rcases hsgn with hs | hs <;> rcases hbank with hb | hb <;>
          rcases d.signs.2 with ht | ht <;> rw [hs,hb,ht] at hneg ⊢ <;>
          norm_num at hneg ⊢ <;> nlinarith only [hneg,mul_pos hδ hρ0]
      refine ⟨H,hH,hseam,hB,hHE.trans hEcalW,hmeet,δ*ρ,η,mul_pos hδ hρ0,hη,?_⟩
      intro u w hu
      have hh := hcal u w hu
      refine ⟨hh.1.1,?_,?_,?_,?_⟩
      · apply PiLp.ext
        intro i
        fin_cases i
        · have he := congrArg (fun z : Plane => z 0) hh.2
          simp [hDfun,Plane.mk] at he
          simpa [Plane.mk] using he
        · have he := congrArg (fun z : Plane => z 1) hh.2
          simp only [hDfun,Plane.mk,PiLp.toLp_apply,Matrix.cons_val_one,Matrix.head_cons] at he
          have hmul : sgn*δ*(ρ*(bank*(w:ℝ))) = -d.tau*(δ*ρ)*(w:ℝ) := by
            calc
              _ = (sgn*bank)*(δ*ρ)*(w:ℝ) := by ring
              _ = _ := by rw [hbankeq]
          simpa [Plane.mk,hmul] using he
      · exact hh.1.2.1.2.1
      · exact hh.1.2.1.2.2.1
      · exact hh.1.2.1.2.2.2
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `first_port_exterior
      let some value := localDecl.value? | Lean.throwError "Missing local first_port_exterior value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected first_port_exterior axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS first_port_exterior: {found.toList}"
    let second_port_exterior : ∀ (hBclosed : IsClosed B)
    (A : ℝ) (hA : 0 < A) (hAr : A < d.radius)
    (β : Interval) (hβ : β ∈ Ioo (0:Interval) 1)
    (hsrc : (d.sideArc β).val ∈ d.cornerChart.source)
    (hcoord : d.cornerChart (d.sideArc β).val = Plane.mk 0 (d.tau*A)),
    ∃ H : C(Interval × Interval,↥Q), IsEmbedding H ∧
      (∀ u, H (u,0) = d.sideArc u) ∧
      (∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      range H ⊆ d.W ∧ range H ∩ range d.e = range d.sideArc ∧
      ∃ lam η : ℝ, 0 < lam ∧ 0 < η ∧
        ∀ (u w : Interval), |(u:ℝ)-(β:ℝ)| < η →
          (H (u,w)).val ∈ d.cornerChart.source ∧
          d.cornerChart (H (u,w)).val =
            Plane.mk (-d.sigma*lam*(w:ℝ)) (d.cornerChart (d.sideArc u).val 1) ∧
          0 < d.tau*d.cornerChart (H (u,w)).val 1 ∧
          |d.cornerChart (H (u,w)).val 1| < d.radius ∧
          |d.cornerChart (H (u,w)).val 0| < d.radius := by
      intro hBclosed A hA hAr β hβ hsrc hcoord
    
      let chartQ : OpenPartialHomeomorph ↥Q Plane := {
        toPartialEquiv := {
          toFun := fun y => d.cornerChart y.val
          invFun := fun z => if hz : z ∈ d.cornerChart.target then
            ⟨d.cornerChart.symm z,interior_subset (d.axis_interior (d.cornerChart.map_target hz))⟩
            else d.sideArc β
          source := (Subtype.val : ↥Q → S) ⁻¹' d.cornerChart.source
          target := d.cornerChart.target
          map_source' := fun _ hy => d.cornerChart.map_source hy
          map_target' := by
            intro z hz
            simp only [dif_pos hz,mem_preimage]
            exact d.cornerChart.map_target hz
          left_inv' := by
            intro y hy
            apply Subtype.ext
            simp only [dif_pos (d.cornerChart.map_source hy)]
            exact d.cornerChart.left_inv hy
          right_inv' := by
            intro z hz
            simp only [dif_pos hz]
            exact d.cornerChart.right_inv hz
        }
        open_source := d.cornerChart.open_source.preimage continuous_subtype_val
        open_target := d.cornerChart.open_target
        continuousOn_toFun := d.cornerChart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
        continuousOn_invFun := by
          apply IsInducing.subtypeVal.continuousOn_iff.mpr
          apply d.cornerChart.continuousOn_symm.congr
          intro z hz
          simp only [Function.comp_apply,dif_pos hz]
      }
      have hσ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have haσ : |d.tau| = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hside_disk : range d.sideArc ⊆ range d.e := by
        rw [d.side_range]
        rintro y (hy | hy)
        · exact (d.disk_a_trace.symm ▸ hy).1
        · exact (d.disk_q_trace.symm ▸ hy).1
      obtain ⟨E,hE,hEc,hEB,hEopen,hEW⟩ := actual_signed_side_strip_in_W d
      let O : Set Plane := {z | 0 < d.tau*z 1 ∧ |z 1| < d.radius ∧ |z 0| < d.radius}
      have hO : IsOpen O := by
        exact (isOpen_lt continuous_const (show Continuous (fun z : Plane => d.tau*z 1) by fun_prop)).inter
          ((isOpen_lt (show Continuous (fun z : Plane => |z 1|) by fun_prop) continuous_const).inter
            (isOpen_lt (show Continuous (fun z : Plane => |z 0|) by fun_prop) continuous_const))
      let T : Set ↥Q := (chartQ.source ∩ chartQ ⁻¹' O) ∩ (Bᶜ ∩ d.W)
      have hT : IsOpen T := (chartQ.isOpen_inter_preimage hO).inter
        (hBclosed.isOpen_compl.inter d.W_open)
      let C0 := chartQ.restrOpen T hT
      let translate : Plane ≃ₜ Plane := {
        toFun := fun z => Plane.mk (z 1-d.tau*A) (z 0)
        invFun := fun z => Plane.mk (z 1) (z 0+d.tau*A)
        left_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
        right_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop
      }
      let D := C0.transHomeomorph translate
      have hDsource : D.source = chartQ.source ∩ T := rfl
      have hDfun (y : ↥Q) : D y = Plane.mk (d.cornerChart y.val 1-d.tau*A) (d.cornerChart y.val 0) := rfl
      have hβD : d.sideArc β ∈ D.source := by
        rw [hDsource]
        refine ⟨hsrc,⟨⟨hsrc,?_⟩,d.side_interior β hβ,hEW ?_⟩⟩
        · change 0 < d.tau*(d.cornerChart (d.sideArc β).val) 1 ∧
            |(d.cornerChart (d.sideArc β).val) 1| < d.radius ∧
            |(d.cornerChart (d.sideArc β).val) 0| < d.radius
          rw [hcoord]
          simpa [Plane.mk,← mul_assoc,hσ,abs_mul,haσ,abs_of_pos hA] using ⟨hA,hAr,d.radius_bounds.1⟩
        · exact ⟨(β,⟨0,by norm_num⟩),hEc β⟩
      have hD0 : D (d.sideArc β) = 0 := by
        rw [hDfun,hcoord]
        simp [Plane.mk]
      have haxis (u : Interval) (hu : d.sideArc u ∈ D.source) : D (d.sideArc u) 1 = 0 := by
        have husrc : (d.sideArc u).val ∈ d.cornerChart.source := hu.1
        have hsmall := hu.2.1.2
        change 0 < d.tau*(d.cornerChart (d.sideArc u).val) 1 ∧
          |(d.cornerChart (d.sideArc u).val) 1| < d.radius ∧
          |(d.cornerChart (d.sideArc u).val) 0| < d.radius at hsmall
        have hval : d.cornerChart.symm (d.cornerChart (d.sideArc u).val) = (d.sideArc u).val :=
          d.cornerChart.left_inv husrc
        have hsides := (d.same_disk_quadrant _ hsmall.2.2 hsmall.2.1)
        have hm := mem_range_self (f := d.sideArc) u
        rw [d.side_range] at hm
        rcases hm with ⟨v,hv⟩ | ⟨v,hv⟩
        · have hfirst : d.cornerChart.symm (d.cornerChart (d.sideArc u).val) ∈
              range (fun w => (d.M.first w).val) := ⟨v,(congrArg Subtype.val hv).trans hval.symm⟩
          have hy := (hsides.1.mp hfirst).1
          rw [hy,mul_zero] at hsmall
          exact False.elim ((lt_irrefl 0) hsmall.1)
        · have hsecond : d.cornerChart.symm (d.cornerChart (d.sideArc u).val) ∈
              range (fun w => (d.M.second w).val) := ⟨v,(congrArg Subtype.val hv).trans hval.symm⟩
          simpa [hDfun,Plane.mk] using (hsides.2.1.mp hsecond).1
      let V : Set ↥Q := D.source
      have hVo : IsOpen V := D.open_source
      have hVB : V ⊆ Bᶜ := fun y hy => hy.2.2.1
      have hVW : V ⊆ d.W := fun y hy => hy.2.2.2
      obtain ⟨ω,hω,sgn,δ,η,Ψ,hsgn,hδ,hη,hΨside,hΨoutside,hΨcal⟩ :=
        source_internal_collar_calibration d.sideArc d.side_embedded E hE hEc β hβ
          D hβD hD0 haxis univ V isOpen_univ hVo (subset_univ _) hβD (subset_univ _)
      let scale : Interval × Icc (-1:ℝ) 1 → Interval × Icc (-1:ℝ) 1 :=
        fun z => (z.1,⟨ω*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hω.1,hω.2]⟩)
      have hsc : Continuous scale := by dsimp [scale]; fun_prop
      have hsi : Function.Injective scale := by
        intro z w he
        apply Prod.ext
        · simpa only [scale] using congrArg Prod.fst he
        · apply Subtype.ext
          exact mul_left_cancel₀ hω.1.ne' (congrArg (fun p : Interval × Icc (-1:ℝ) 1 => (p.2:ℝ)) he)
      let N : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨E ∘ scale,E.continuous.comp hsc⟩
      have hN : IsEmbedding N := hE.comp (hsc.isClosedEmbedding hsi).isEmbedding
      have hform (z) : N z = E (z.1,⟨ω*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hω.1,hω.2]⟩) := rfl
      let Ecal : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨Ψ ∘ N,Ψ.continuous.comp N.continuous⟩
      have hEcal : IsEmbedding Ecal := Ψ.isEmbedding.comp hN
      have hEcalc (u) : Ecal (u,⟨0,by norm_num⟩) = d.sideArc u := by
        change Ψ (E (u,⟨ω*0,_⟩)) = _
        simpa only [mul_zero,hEc] using hΨside u
      have hΨB (y : ↥Q) : Ψ y ∈ B ↔ y ∈ B := by
        constructor
        · intro hy
          have he := hΨoutside (Ψ y) (fun hv => hVB hv hy)
          have hh : y = Ψ y := Ψ.injective he.symm
          exact hh ▸ hy
        · intro hy
          rw [hΨoutside y (fun hv => hVB hv hy)]
          exact hy
      have hEcalB (z) : Ecal z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
        change Ψ (N z) ∈ B ↔ _
        rw [hΨB,hform,hEB]
      have hEcalW : range Ecal ⊆ d.W := by
        rintro y ⟨z,rfl⟩
        have hnW : N z ∈ d.W := hEW (mem_range_self (scale z))
        by_contra he
        have hfix : Ψ (Ecal z) = Ecal z := hΨoutside _ (fun hv => he (hVW hv))
        have hh : N z = Ecal z := Ψ.injective hfix.symm
        exact he (hh ▸ hnW)
      have hNopen : IsOpen (N '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
        -- A narrower signed strip has an open band by the same inducing argument.
        let V : Set (Interval × Icc (-1:ℝ) 1) := {z | -ω < z.2.val ∧ z.2.val < ω}
        have hV : IsOpen V := (isOpen_lt continuous_const
          (continuous_subtype_val.comp continuous_snd)).inter
            (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
        obtain ⟨A,hA,hEA⟩ := hE.isInducing.image_eq_isOpen_inter_range hV
        have hVsub : V ⊆ {z | -1 < z.2.val ∧ z.2.val < 1} := by
          intro z hz
          exact ⟨lt_of_le_of_lt (by linarith [hω.2]) hz.1,hz.2.trans_le hω.2⟩
        have hEq : E '' V = A ∩ E '' {z | -1 < z.2.val ∧ z.2.val < 1} := by
          apply Subset.antisymm
          · intro y hy
            exact ⟨(hEA ▸ hy).1,image_mono hVsub hy⟩
          · intro y hy
            rw [hEA]
            exact ⟨hy.1,image_subset_range E _ hy.2⟩
        have hImage : N '' {z | -1 < z.2.val ∧ z.2.val < 1} = E '' V := by
          ext y
          constructor
          · rintro ⟨z,hz,rfl⟩
            refine ⟨(z.1,⟨ω*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hω.1,hω.2]⟩),?_,(hform z).symm⟩
            change -ω < ω*z.2 ∧ ω*z.2 < ω
            constructor <;> nlinarith [hz.1,hz.2,hω.1]
          · rintro ⟨z,hz,rfl⟩
            let w : Icc (-1:ℝ) 1 := ⟨z.2.val/ω,by
              constructor
              · apply (le_div_iff₀ hω.1).mpr; linarith [hz.1]
              · apply (div_le_iff₀ hω.1).mpr; linarith [hz.2]⟩
            have hw : -1 < w.val ∧ w.val < 1 := by
              dsimp [w]
              constructor
              · apply (lt_div_iff₀ hω.1).mpr; linarith [hz.1]
              · apply (div_lt_iff₀ hω.1).mpr; linarith [hz.2]
            refine ⟨(z.1,w),hw,?_⟩
            change N (z.1,w) = _
            rw [hform]
            apply congrArg E
            apply Prod.ext
            · rfl
            · apply Subtype.ext
              change ω*(z.2.val/ω) = z.2.val
              field_simp [hω.1.ne']
        rw [hImage,hEq]
        exact hA.inter hEopen
      have hEcalopen : IsOpen (Ecal '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
        have heq : Ecal '' {z | -1 < z.2.val ∧ z.2.val < 1} =
            Ψ '' (N '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
          simpa only [Ecal,ContinuousMap.coe_mk] using image_comp Ψ N {z | -1 < z.2.val ∧ z.2.val < 1}
        rw [heq]
        exact Ψ.isOpenMap _ hNopen
      obtain ⟨P,hP,hPr,hPt,hPo⟩ :=
        ActualHarerDiskGluing.actual_two_side_disk_constructs_prescribed_edge_square
          d.sideArc d.M.boundarySide d.e d.side_embedded d.M.boundary_embedded d.e_embedded
          (d.side_zero.trans d.M.boundary_zero.symm) (d.side_one.trans d.M.boundary_one.symm)
          (actual_two_side_boundary d) (fun u v he => (actual_side_beta_collision d u v).mp he)
      let flip := (Homeomorph.refl Interval).prodCongr unitInterval.symmHomeomorph
      let Disk : C(Interval × Interval,↥Q) := ⟨P ∘ flip,P.continuous.comp flip.continuous⟩
      have hDisk : IsEmbedding Disk := hP.comp flip.isEmbedding
      have hDiskcenter (u) : Disk (u,0) = d.sideArc u := by
        change P (u,unitInterval.symm 0) = _
        rw [unitInterval.symm_zero,hPt]
      have hDiskr : range Disk = range d.e := by
        change range (P ∘ flip) = _
        rw [flip.surjective.range_comp,hPr]
      obtain ⟨H,hH,hc,hHE,hinter,hB,ρ,hρ0,hρ1,bank,hbank,hHform⟩ :=
        exact_exterior_half ↥Q B Disk hDisk Ecal hEcal
          (fun u => (hEcalc u).trans (hDiskcenter u).symm) hEcalB hEcalopen
      have hseam (u) : H (u,0) = d.sideArc u := (hc u).trans (hDiskcenter u)
      have hmeet : range H ∩ range d.e = range d.sideArc := by
        rw [← hDiskr,hinter]
        congr 1
        funext u
        exact hDiskcenter u
      have hcal (u w : Interval) (hu : |(u:ℝ)-(β:ℝ)| < η) :
          H (u,w) ∈ D.source ∧
          D (H (u,w)) = Plane.mk (D (d.sideArc u) 0) (sgn*δ*(ρ*(bank*(w:ℝ)))) := by
        let ww : Icc (-1:ℝ) 1 := ⟨ρ*(bank*(w:ℝ)),by
          rcases hbank with rfl | rfl <;> constructor <;> nlinarith [w.property.1,w.property.2,hρ0,hρ1]⟩
        rw [hHform (u,w) ww rfl]
        exact hΨcal u ww hu
      have hnonD : H (β,1) ∉ range d.e := by
        intro he
        have hh : H (β,1) ∈ range d.sideArc := hmeet ▸ ⟨mem_range_self _,he⟩
        obtain ⟨v,hv⟩ := hh
        have heq := hH.injective ((hseam v).trans hv)
        have hf := congrArg Prod.snd heq
        exact one_ne_zero hf.symm
      have hbankeq : sgn*bank = -d.sigma := by
        have hcal1 := hcal β 1 (by simpa using hη)
        have hcoord1 : d.cornerChart (H (β,1)).val = Plane.mk (sgn*δ*(ρ*bank)) (d.tau*A) := by
          apply PiLp.ext
          intro i
          fin_cases i
          · have hh := congrArg (fun z : Plane => z 1) hcal1.2
            simpa [hDfun,Plane.mk] using hh
          · have hh := congrArg (fun z : Plane => z 0) hcal1.2
            change d.cornerChart (H (β,1)).val 1-d.tau*A =
              d.cornerChart (d.sideArc β).val 1-d.tau*A at hh
            rw [hcoord] at hh
            change d.cornerChart (H (β,1)).val 1-d.tau*A = d.tau*A-d.tau*A at hh
            change d.cornerChart (H (β,1)).val 1 = d.tau*A
            exact sub_left_inj.mp hh
        have hs := hcal1.1.2.1.2
        change 0 < d.tau*(d.cornerChart (H (β,1)).val) 1 ∧
          |(d.cornerChart (H (β,1)).val) 1| < d.radius ∧
          |(d.cornerChart (H (β,1)).val) 0| < d.radius at hs
        have hnot : ¬ (0 ≤ d.sigma*(d.cornerChart (H (β,1)).val) 0 ∧
            0 ≤ d.tau*(d.cornerChart (H (β,1)).val) 1) := by
          intro hh
          have hmem := (d.same_disk_quadrant _ hs.2.2 hs.2.1).2.2.mpr hh
          rw [d.cornerChart.left_inv hcal1.1.1] at hmem
          obtain ⟨v,hv⟩ := hmem
          exact hnonD ⟨v,Subtype.ext hv⟩
        have hneg : d.sigma*(sgn*δ*(ρ*bank)) < 0 := by
          apply lt_of_not_ge
          intro hh
          apply hnot
          exact ⟨by simpa [hcoord1,Plane.mk] using hh,hs.1.le⟩
        rcases hsgn with hg | hg <;> rcases hbank with hb | hb <;>
          rcases d.signs.1 with ht | ht <;> rw [hg,hb,ht] at hneg ⊢ <;>
          norm_num at hneg ⊢ <;> nlinarith only [hneg,mul_pos hδ hρ0]
      refine ⟨H,hH,hseam,hB,hHE.trans hEcalW,hmeet,δ*ρ,η,mul_pos hδ hρ0,hη,?_⟩
      intro u w hu
      have hh := hcal u w hu
      refine ⟨hh.1.1,?_,?_,?_,?_⟩
      · apply PiLp.ext
        intro i
        fin_cases i
        · have he := congrArg (fun z : Plane => z 1) hh.2
          simp only [hDfun,Plane.mk,PiLp.toLp_apply,Matrix.cons_val_one,Matrix.head_cons] at he
          have hmul : sgn*δ*(ρ*(bank*(w:ℝ))) = -d.sigma*(δ*ρ)*(w:ℝ) := by
            calc
              _ = (sgn*bank)*(δ*ρ)*(w:ℝ) := by ring
              _ = _ := by rw [hbankeq]
          simpa [Plane.mk,hmul] using he
        · have he := congrArg (fun z : Plane => z 0) hh.2
          simp [hDfun,Plane.mk] at he
          simpa [Plane.mk] using he
      · exact hh.1.2.1.2.1
      · exact hh.1.2.1.2.2.1
      · exact hh.1.2.1.2.2.2
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `second_port_exterior
      let some value := localDecl.value? | Lean.throwError "Missing local second_port_exterior value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected second_port_exterior axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS second_port_exterior: {found.toList}"
    let side_future_clear : ∀ (b : Interval), d.s < b → ∃ H : C(Interval × Interval,↥Q), IsEmbedding H ∧
      (∀ u, H (u,0) = d.sideArc u) ∧
      (∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      range H ⊆ d.W ∧ range H ∩ range d.e = range d.sideArc ∧
      Disjoint (range H) ((fun u => q (d.xi u)) '' Ici b) := by
      intro b hb
      let Future : Set ↥Q := (fun u => q (d.xi u)) '' Ici b
      have hFutureclosed : IsClosed Future := (isClosed_Ici.isCompact.image
        (q.continuous.comp d.xi.continuous)).isClosed
      have hafter_disk (u : Interval) (hu : d.s < u) : q (d.xi u) ∉ range d.e := by
        intro hd
        have hm : q (d.xi u) ∈ range d.M.second := d.disk_q_trace ▸ ⟨hd,mem_range_self _⟩
        rw [d.second_trace] at hm
        obtain ⟨v,hv,he⟩ := hm
        have hEq : v = u := d.xi.injective (d.q_embedded.injective he)
        exact not_le_of_gt hu (hEq ▸ hv.2)
      have hside_disk : range d.sideArc ⊆ range d.e := by
        rw [d.side_range]
        rintro y (hy | hy)
        · exact (d.disk_a_trace.symm ▸ hy).1
        · exact (d.disk_q_trace.symm ▸ hy).1
      obtain ⟨E,hE,hEc,hEB,hEopen,hEW⟩ := actual_signed_side_strip_in_W d
      let U : Set ↥Q := d.W ∩ Futureᶜ
      have hU : IsOpen U := d.W_open.inter hFutureclosed.isOpen_compl
      have hcU (u : Interval) : E (u,⟨0,by norm_num⟩) ∈ U := by
        refine ⟨hEW (mem_range_self _),?_⟩
        rw [hEc]
        rintro ⟨v,hv,he⟩
        change q (d.xi v) = d.sideArc u at he
        apply hafter_disk v (hb.trans_le hv)
        rw [he]
        exact hside_disk (mem_range_self u)
      obtain ⟨ρ,hρ,N,hN,hNW,hform,hcenter⟩ := source_shrink_embedded_strip_in_open E hE U hU hcU
      let E' : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨N,hN.continuous⟩
      have hNB (z) : E' z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
        change N z ∈ B ↔ _
        rw [hform]
        exact hEB _
      have hNopen : IsOpen (E' '' {z | -1 < z.2.val ∧ z.2.val < 1}) := by
        -- A narrower signed strip has an open band by the same inducing argument.
        let V : Set (Interval × Icc (-1:ℝ) 1) := {z | -ρ < z.2.val ∧ z.2.val < ρ}
        have hV : IsOpen V := (isOpen_lt continuous_const
          (continuous_subtype_val.comp continuous_snd)).inter
            (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
        obtain ⟨A,hA,hEA⟩ := hE.isInducing.image_eq_isOpen_inter_range hV
        have hVsub : V ⊆ {z | -1 < z.2.val ∧ z.2.val < 1} := by
          intro z hz
          exact ⟨lt_of_le_of_lt (by linarith [hρ.2]) hz.1,hz.2.trans_le hρ.2⟩
        have hEq : E '' V = A ∩ E '' {z | -1 < z.2.val ∧ z.2.val < 1} := by
          apply Subset.antisymm
          · intro y hy
            exact ⟨(hEA ▸ hy).1,image_mono hVsub hy⟩
          · intro y hy
            rw [hEA]
            exact ⟨hy.1,image_subset_range E _ hy.2⟩
        have hImage : E' '' {z | -1 < z.2.val ∧ z.2.val < 1} = E '' V := by
          ext y
          constructor
          · rintro ⟨z,hz,rfl⟩
            refine ⟨(z.1,⟨ρ*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩),?_,(hform z).symm⟩
            change -ρ < ρ*z.2 ∧ ρ*z.2 < ρ
            constructor <;> nlinarith [hz.1,hz.2,hρ.1]
          · rintro ⟨z,hz,rfl⟩
            let w : Icc (-1:ℝ) 1 := ⟨z.2.val/ρ,by
              constructor
              · apply (le_div_iff₀ hρ.1).mpr; linarith [hz.1]
              · apply (div_le_iff₀ hρ.1).mpr; linarith [hz.2]⟩
            have hw : -1 < w.val ∧ w.val < 1 := by
              dsimp [w]
              constructor
              · apply (lt_div_iff₀ hρ.1).mpr; linarith [hz.1]
              · apply (div_lt_iff₀ hρ.1).mpr; linarith [hz.2]
            refine ⟨(z.1,w),hw,?_⟩
            change N (z.1,w) = _
            rw [hform]
            apply congrArg E
            apply Prod.ext
            · rfl
            · apply Subtype.ext
              change ρ*(z.2.val/ρ) = z.2.val
              field_simp [hρ.1.ne']
        rw [hImage,hEq]
        exact hA.inter hEopen
      obtain ⟨P,hP,hPr,hPt,hPo⟩ :=
        ActualHarerDiskGluing.actual_two_side_disk_constructs_prescribed_edge_square
          d.sideArc d.M.boundarySide d.e d.side_embedded d.M.boundary_embedded d.e_embedded
          (d.side_zero.trans d.M.boundary_zero.symm) (d.side_one.trans d.M.boundary_one.symm)
          (actual_two_side_boundary d) (fun u v he => (actual_side_beta_collision d u v).mp he)
      let flip := (Homeomorph.refl Interval).prodCongr unitInterval.symmHomeomorph
      let D : C(Interval × Interval,↥Q) := ⟨P ∘ flip,P.continuous.comp flip.continuous⟩
      have hD : IsEmbedding D := hP.comp flip.isEmbedding
      have hDcenter (u) : D (u,0) = d.sideArc u := by
        change P (u,unitInterval.symm 0) = _
        rw [unitInterval.symm_zero,hPt]
      have hDr : range D = range d.e := by
        change range (P ∘ flip) = _
        rw [flip.surjective.range_comp,hPr]
      obtain ⟨H,hH,hc,hHE,hinter,hB⟩ := actual_disk_side_exterior_half_from_strip B D hD E' hN
        (fun u => ((hcenter u).trans (hEc u)).trans (hDcenter u).symm) hNB hNopen
      refine ⟨H,hH,fun u => (hc u).trans (hDcenter u),hB,hHE.trans (fun y hy => (hNW hy).1),?_,?_⟩
      rw [← hDr,hinter]
      congr 1
      funext u
      exact hDcenter u
      exact disjoint_left.mpr (fun y hy hf => (hNW (hHE hy)).2 hf)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `side_future_clear
      let some value := localDecl.value? | Lean.throwError "Missing side future-clear proof value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do
          found := found.insert ax
      let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected side_future_clear axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS side_future_clear: {found.toList}"
    let calibrated_branch : ∀ (b : Interval), d.s < b ∧ b < d.t → (q (d.xi b)).val ∈ d.cornerChart.source →
    ∃ N : C(Interval × Icc (-1:ℝ) 1,↥Q), IsEmbedding N ∧
      (∃ sgn lam η : ℝ, (sgn = -1 ∨ sgn = 1) ∧ 0 < lam ∧ 0 < η ∧
        (∀ w : Icc (-1:ℝ) 1, (N (0,w)).val ∈ d.cornerChart.source ∧
          d.cornerChart (N (0,w)).val =
            Plane.mk (sgn*lam*(w:ℝ)) (d.cornerChart (q (d.xi b)).val 1)) ∧
        (∀ z : Interval × Icc (-1:ℝ) 1,
          |(d.xi (Icc.convexComb b d.t z.1):ℝ)-(d.xi b:ℝ)| < η →
          (N z).val ∈ d.cornerChart.source ∧
          d.cornerChart (N z).val =
            Plane.mk (sgn*lam*(z.2:ℝ)) (d.cornerChart (q (d.xi (Icc.convexComb b d.t z.1))).val 1))) ∧
      (∀ u, N (u,⟨0,by norm_num⟩) = q (d.xi (Icc.convexComb b d.t u))) ∧
      range N ⊆ d.W ∧ Disjoint (range N) (range d.e) ∧
      (∀ z, N z ∉ B) ∧
      range N ∩ range q = (fun u => q (d.xi u)) '' Icc b d.t ∧
      Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range N) := by
      intro b hb hbsource
      have hclock_interior (u : Interval) (hu : u ∈ Ioo (0:Interval) 1) :
          d.xi u ∈ Ioo (0:Interval) 1 := by
        rcases d.xi_original_clock with hx | hx
        · rw [hx]
          exact hu
        · rw [hx]
          change 0 < (1-(u:ℝ)) ∧ (1-(u:ℝ)) < 1
          have h0 : (0:ℝ) < u := hu.1
          have h1 : (u:ℝ) < 1 := hu.2
          constructor <;> linarith
      have hafter_disk (u : Interval) (hu : d.s < u) : q (d.xi u) ∉ range d.e := by
        intro hd
        have hm : q (d.xi u) ∈ range d.M.second := d.disk_q_trace ▸ ⟨hd,mem_range_self _⟩
        rw [d.second_trace] at hm
        obtain ⟨v,hv,he⟩ := hm
        have hEq : v = u := d.xi.injective (d.q_embedded.injective he)
        exact not_le_of_gt hu (hEq ▸ hv.2)
      let pa : CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.ProperArc S x R :=
        ⟨q,d.q_embedded,d.q_ends.1,d.q_ends.2,d.q_interior⟩
      obtain ⟨E,hE,hEc,hEends,hEint,hEopen⟩ :=
        CurveComplexGenusTwo.SourceTopology.OriginalBoundaryArc.source_actual_boundary_proper_arc_strip
          S x R g hg hS hR htarget pa
      have hBclosed : IsClosed B := by
        exact ((isCompact_sphere ((chartAt Plane x) x) R).image_of_continuousOn
          ((chartAt Plane x).continuousOn_symm.mono
            (Metric.sphere_subset_closedBall.trans htarget))).isClosed.preimage continuous_subtype_val
      let chartQ : OpenPartialHomeomorph ↥Q Plane := {
        toPartialEquiv := {
          toFun := fun y => d.cornerChart y.val
          invFun := fun z => if hz : z ∈ d.cornerChart.target then
            ⟨d.cornerChart.symm z,interior_subset (d.axis_interior (d.cornerChart.map_target hz))⟩
            else q (d.xi b)
          source := (Subtype.val : ↥Q → S) ⁻¹' d.cornerChart.source
          target := d.cornerChart.target
          map_source' := fun _ hy => d.cornerChart.map_source hy
          map_target' := by
            intro z hz
            simp only [dif_pos hz,mem_preimage]
            exact d.cornerChart.map_target hz
          left_inv' := by
            intro y hy
            apply Subtype.ext
            simp only [dif_pos (d.cornerChart.map_source hy)]
            exact d.cornerChart.left_inv hy
          right_inv' := by
            intro z hz
            simp only [dif_pos hz]
            exact d.cornerChart.right_inv hz
        }
        open_source := d.cornerChart.open_source.preimage continuous_subtype_val
        open_target := d.cornerChart.open_target
        continuousOn_toFun := d.cornerChart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
        continuousOn_invFun := by
          apply IsInducing.subtypeVal.continuousOn_iff.mpr
          apply d.cornerChart.continuousOn_symm.congr
          intro z hz
          simp only [Function.comp_apply,dif_pos hz]
      }
      let c : ℝ := d.cornerChart (q (d.xi b)).val 1
      let swapTranslate : Plane ≃ₜ Plane := {
        toFun := fun z => Plane.mk (z 1-c) (z 0)
        invFun := fun z => Plane.mk (z 1) (z 0+c)
        left_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
        right_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop
      }
      let D := chartQ.transHomeomorph swapTranslate
      have hDsource : D.source = (Subtype.val : ↥Q → S) ⁻¹' d.cornerChart.source := rfl
      have hDfun (y : ↥Q) : D y = Plane.mk (d.cornerChart y.val 1-c) (d.cornerChart y.val 0) := rfl
      have haxis (u : Interval) (hu : q u ∈ D.source) : D (q u) 1 = 0 := by
        have hz := (d.axes.moving_axis (q u).val hu).mp (mem_range_self u)
        simpa [hDfun,Plane.mk] using hz
      have hD0 : D (q (d.xi b)) = 0 := by
        apply PiLp.ext
        intro i
        fin_cases i
        · simp [hDfun,Plane.mk,c]
        · simpa [Plane.mk] using haxis (d.xi b) hbsource
      let V : Set ↥Q := D.source ∩ d.W ∩ (range d.e)ᶜ ∩ Bᶜ
      have hV : IsOpen V := ((D.open_source.inter d.W_open).inter
        (isCompact_range d.e.continuous).isClosed.isOpen_compl).inter hBclosed.isOpen_compl
      have hbV : q (d.xi b) ∈ V := by
        exact ⟨⟨⟨hbsource,d.tail_in_W ⟨b,⟨bot_le,hb.2.le⟩,rfl⟩⟩,
          hafter_disk b hb.1⟩,d.q_interior _ (hclock_interior b
            ⟨d.tail_order.1.trans hb.1,hb.2.trans d.tail_order.2.2⟩)⟩
      obtain ⟨ω,hω,sgn,δ,η,Ψ,hsgn,hδ,hη,hΨq,hΨoutside,hΨcal⟩ :=
        source_internal_collar_calibration q d.q_embedded E hE hEc (d.xi b)
          (hclock_interior b ⟨d.tail_order.1.trans hb.1,hb.2.trans d.tail_order.2.2⟩)
          D hbsource hD0 haxis univ V isOpen_univ hV (subset_univ _) hbV (subset_univ _)
      let scale : Interval × Icc (-1:ℝ) 1 → Interval × Icc (-1:ℝ) 1 :=
        fun z => (z.1,⟨ω*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hω.1,hω.2]⟩)
      have hscalec : Continuous scale := by dsimp [scale]; fun_prop
      have hscalei : Function.Injective scale := by
        intro z w he
        apply Prod.ext
        · simpa only [scale] using congrArg Prod.fst he
        · apply Subtype.ext
          exact mul_left_cancel₀ hω.1.ne' (congrArg (fun p : Interval × Icc (-1:ℝ) 1 => (p.2:ℝ)) he)
      let Ecal : Interval × Icc (-1:ℝ) 1 → ↥Q := Ψ ∘ E ∘ scale
      have hEcal : IsEmbedding Ecal := Ψ.isEmbedding.comp (hE.comp (hscalec.isClosedEmbedding hscalei).isEmbedding)
      have hEcalc (u) : Ecal (u,⟨0,by norm_num⟩) = q u := by
        change Ψ (E (u,⟨ω*0,_⟩)) = _
        simpa only [mul_zero,hEc] using hΨq u
      have hEcalint (u : Interval) (hu : u ∈ Ioo (0:Interval) 1) (w : Icc (-1:ℝ) 1) :
          Ecal (u,w) ∉ B := by
        intro heB
        have hfix : Ψ (Ecal (u,w)) = Ecal (u,w) := hΨoutside _ (fun h => h.2 heB)
        have he : E (scale (u,w)) = Ecal (u,w) := Ψ.injective hfix.symm
        exact hEint u hu _ (he ▸ heB)
      have hcal (w : Icc (-1:ℝ) 1) : Ecal (d.xi b,w) ∈ D.source ∧
          D (Ecal (d.xi b,w)) = Plane.mk 0 (sgn*δ*(w:ℝ)) := by
        have hh := hΨcal (d.xi b) w (by simpa using hη)
        rw [hD0] at hh
        exact hh
    
      let clock : C(Interval,Interval) :=
        ⟨fun u => d.xi (Icc.convexComb b d.t u),
          d.xi.continuous.comp (Icc.continuous_convexComb b d.t)⟩
      have hclock : IsEmbedding clock := by
        apply (clock.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply Subtype.ext
        have hbt : (b:ℝ) < d.t := hb.2
        have he' := congrArg (fun z : Interval => (z:ℝ)) (d.xi.injective he)
        simp only [Icc.coe_convexComb] at he'
        nlinarith
      let N₀ : C(Interval × Icc (-1:ℝ) 1,↥Q) :=
        ⟨fun z => Ecal (clock z.1,z.2),hEcal.continuous.comp (clock.continuous.prodMap continuous_id)⟩
      have hN₀ : IsEmbedding N₀ := hEcal.comp (hclock.prodMap IsEmbedding.id)
      have hN₀c (u) : N₀ (u,⟨0,by norm_num⟩) = q (clock u) := hEcalc (clock u)
      have hconvex (u : Interval) : Icc.convexComb b d.t u ∈ Icc b d.t :=
        ⟨Icc.le_convexComb hb.2.le u,Icc.convexComb_le hb.2.le u⟩
      let U : Set ↥Q := d.W ∩ (range d.e)ᶜ
      have hU : IsOpen U := d.W_open.inter (isCompact_range d.e.continuous).isClosed.isOpen_compl
      have hNU (u) : N₀ (u,⟨0,by norm_num⟩) ∈ U := by
        rw [hN₀c]
        exact ⟨d.tail_in_W ⟨Icc.convexComb b d.t u,⟨bot_le,(hconvex u).2⟩,rfl⟩,
          hafter_disk _ (hb.1.trans_le (hconvex u).1)⟩
      obtain ⟨ρ,hρ,N,hN,hNU,hform,hNc⟩ := source_shrink_embedded_strip_in_open N₀ hN₀ U hU hNU
      let N' : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨N,hN.continuous⟩
      have hN'center (u) : N' (u,⟨0,by norm_num⟩) = q (clock u) := (hNc u).trans (hN₀c u)
      have hformula (z : Interval × Icc (-1:ℝ) 1) :
          N' z = Ecal (clock z.1,⟨ρ*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩) := hform z
      have htrace : range N' ∩ range q = (fun u => q (d.xi u)) '' Icc b d.t := by
        ext y
        constructor
        · rintro ⟨⟨z,rfl⟩,⟨v,hv⟩⟩
          have hEq := hEcal.injective ((hEcalc v).trans (hv.trans (hformula z)))
          have hc : v = clock z.1 := congrArg Prod.fst hEq
          refine ⟨Icc.convexComb b d.t z.1,hconvex z.1,?_⟩
          exact (congrArg q hc).symm.trans hv
        · rintro ⟨v,hv,rfl⟩
          have hm : v ∈ range (Icc.convexComb b d.t) := by
            rw [Path.range_subpathAux,uIcc_of_le hb.2.le]
            exact hv
          obtain ⟨u,hu⟩ := hm
          refine ⟨⟨(u,⟨0,by norm_num⟩),?_⟩,mem_range_self _⟩
          exact (hN'center u).trans (congrArg (fun z => q (d.xi z)) hu)
      have hN'B (z) : N' z ∉ B := by
        rw [hformula]
        apply hEcalint
        apply hclock_interior
        exact ⟨d.tail_order.1.trans (hb.1.trans_le (hconvex z.1).1),
          (hconvex z.1).2.trans_lt d.tail_order.2.2⟩
      have hfut : Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range N') := by
        apply disjoint_left.mpr
        rintro y ⟨u,hu,rfl⟩ hn
        have hm : q (d.xi u) ∈ (fun u => q (d.xi u)) '' Icc b d.t := htrace ▸ ⟨hn,mem_range_self _⟩
        obtain ⟨v,hv,he⟩ := hm
        have hEq : v = u := d.xi.injective (d.q_embedded.injective he)
        exact not_le_of_gt hu (hEq ▸ hv.2)
      have hgate (w : Icc (-1:ℝ) 1) : (N' (0,w)).val ∈ d.cornerChart.source ∧
          d.cornerChart (N' (0,w)).val = Plane.mk (sgn*(δ*ρ)*(w:ℝ)) c := by
        have hclock0 : clock 0 = d.xi b := by simp [clock]
        rw [hformula,hclock0]
        have hh := hcal ⟨ρ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hρ.1,hρ.2]⟩
        refine ⟨hh.1,?_⟩
        have hx := congrArg (fun p : Plane => p 1) hh.2
        have hy := congrArg (fun p : Plane => p 0) hh.2
        simp [hDfun,Plane.mk] at hx hy
        apply PiLp.ext
        intro i
        fin_cases i
        · change d.cornerChart (Ecal (d.xi b,⟨ρ*(w:ℝ),_⟩)).val 0 = _
          simpa [Plane.mk,mul_assoc] using hx
        · change d.cornerChart (Ecal (d.xi b,⟨ρ*(w:ℝ),_⟩)).val 1 = c
          linarith
      have hfullcal (z : Interval × Icc (-1:ℝ) 1)
          (hz : |(d.xi (Icc.convexComb b d.t z.1):ℝ)-(d.xi b:ℝ)| < η) :
          (N' z).val ∈ d.cornerChart.source ∧
          d.cornerChart (N' z).val =
            Plane.mk (sgn*(δ*ρ)*(z.2:ℝ)) (d.cornerChart (q (d.xi (Icc.convexComb b d.t z.1))).val 1) := by
        let w : Icc (-1:ℝ) 1 := ⟨ρ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩
        have hh := hΨcal (clock z.1) w hz
        change Ecal (clock z.1,w) ∈ D.source ∧
          D (Ecal (clock z.1,w)) = Plane.mk (D (q (clock z.1)) 0) (sgn*δ*(w:ℝ)) at hh
        rw [hformula]
        refine ⟨hh.1,?_⟩
        have hx := congrArg (fun p : Plane => p 1) hh.2
        have hy := congrArg (fun p : Plane => p 0) hh.2
        simp [hDfun,Plane.mk] at hx hy
        apply PiLp.ext
        intro i
        fin_cases i
        · simpa [Plane.mk,w,mul_assoc] using hx
        · simpa [Plane.mk,clock] using hy
      refine ⟨N',hN,⟨sgn,δ*ρ,η,hsgn,mul_pos hδ hρ.1,hη,hgate,hfullcal⟩,

        fun u => hN'center u,?_,?_,hN'B,htrace,hfut⟩
      · intro y hy
        exact (hNU hy).1
      · exact disjoint_left.mpr (fun y hy hd => (hNU hy).2 hd)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `calibrated_branch
      let some value := localDecl.value? | Lean.throwError "Missing proof value for local calibrated_branch"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do
          found := found.insert ax
      let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected local calibrated_branch axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS calibrated_branch: {found.toList}"
    let corner_patch : ∃ A ε : ℝ, 0 < ε ∧ ε < A ∧ A < d.radius ∧
      ∃ P : C(Interval × Interval,↥Q), IsEmbedding P ∧
        range P ⊆ d.W ∧ range P ⊆ (Subtype.val : ↥Q → S) ⁻¹' d.cornerChart.source ∧
        (∀ z, P z ∉ B) ∧
        (∀ z, P z ∈ range d.e ↔ z.2 = 0) ∧
        (∀ z, P z ∈ range d.sideArc ↔ z.2 = 0) ∧
        (∀ w, d.cornerChart (P (0,w)).val = Plane.mk (d.sigma*A) (-d.tau*ε*(w:ℝ))) ∧
        (∀ w, d.cornerChart (P (1,w)).val = Plane.mk (-d.sigma*ε*(w:ℝ)) (d.tau*A)) ∧
        (∀ w, d.cornerChart (P (⟨1/2,by norm_num⟩,w)).val =
          Plane.mk (-d.sigma*ε*(w:ℝ)) (-d.tau*ε*(w:ℝ))) ∧
        (∀ z, -ε ≤ d.sigma*d.cornerChart (P z).val 0 ∧
          d.sigma*d.cornerChart (P z).val 0 ≤ A ∧
          -ε ≤ d.tau*d.cornerChart (P z).val 1 ∧
          d.tau*d.cornerChart (P z).val 1 ≤ A ∧
          (d.sigma*d.cornerChart (P z).val 0 ≤ 0 ∨ d.tau*d.cornerChart (P z).val 1 ≤ 0)) ∧
        (∀ z, ∃ v : Interval,
          d.cornerChart (P z).val =
            Plane.mk (d.sigma*(A*(v:ℝ)-ε*(z.2:ℝ)*(1-(v:ℝ)))) (-d.tau*ε*(z.2:ℝ)) ∨
          d.cornerChart (P z).val =
            Plane.mk (-d.sigma*ε*(z.2:ℝ)) (d.tau*(A*(v:ℝ)-ε*(z.2:ℝ)*(1-(v:ℝ))))) ∧
        (range (fun z : Interval × Interval => d.cornerChart (P z).val) =
          {p : Plane | -ε ≤ d.sigma*p 0 ∧ d.sigma*p 0 ≤ A ∧
            -ε ≤ d.tau*p 1 ∧ d.tau*p 1 ≤ A ∧ (d.sigma*p 0 ≤ 0 ∨ d.tau*p 1 ≤ 0)}) ∧
        ∃ b : Interval, d.s < b ∧ b < d.t ∧
          (fun u => q (d.xi u)) '' Icc d.s b ⊆ range P ∧
          Disjoint ((fun u => q (d.xi u)) '' Ioi b) (range P) ∧
          ∃ k : Interval, k ∈ Ioo (0:Interval) 1 ∧ P (k,1) = q (d.xi b) ∧
            d.cornerChart (q (d.xi b)).val = Plane.mk 0 (-d.tau*ε) := by
    
      have planarPatch : ∀ (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε),
        ∃ P : C(Interval × Interval,Plane), IsEmbedding P ∧
          (∀ w, P (0,w) = Plane.mk A (-ε*(w:ℝ))) ∧
          (∀ w, P (1,w) = Plane.mk (-ε*(w:ℝ)) A) ∧
          (∀ w, P (⟨1/2,by norm_num⟩,w) = Plane.mk (-ε*(w:ℝ)) (-ε*(w:ℝ))) ∧
          range P = {z : Plane | -ε ≤ z 0 ∧ z 0 ≤ A ∧
            -ε ≤ z 1 ∧ z 1 ≤ A ∧ (z 0 ≤ 0 ∨ z 1 ≤ 0)} ∧
          (∀ z, ∃ v : Interval,
            P z = Plane.mk (A*(v:ℝ)-ε*(z.2:ℝ)*(1-(v:ℝ))) (-ε*(z.2:ℝ)) ∨
            P z = Plane.mk (-ε*(z.2:ℝ)) (A*(v:ℝ)-ε*(z.2:ℝ)*(1-(v:ℝ)))) := by
        intro A ε hA hε
        classical
        let L : Interval × Interval → Plane :=
          fun z => Plane.mk (A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ))) (-ε*(z.2:ℝ))
        let R : Interval × Interval → Plane :=
          fun z => Plane.mk (-ε*(z.2:ℝ)) (A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)))
        have hLc : Continuous L := by dsimp [L]; fun_prop
        have hRc : Continuous R := by dsimp [R]; fun_prop
        have hLi : Function.Injective L := by
          intro z w he
          have h₁ := congrArg (fun p : Plane => p 1) he
          have h₀ := congrArg (fun p : Plane => p 0) he
          simp [L,Plane.mk] at h₁ h₀
          have h2 : (z.2:ℝ) = w.2 := h₁.resolve_right hε.ne'
          have h1 : (z.1:ℝ) = w.1 := by
            rw [h2] at h₀
            have hp : 0 < A+ε*(w.2:ℝ) := by nlinarith [w.2.property.1]
            have hd : (A+ε*(w.2:ℝ))*((z.1:ℝ)-(w.1:ℝ)) = 0 := by nlinarith
            have hd' := (mul_eq_zero.mp hd).resolve_left hp.ne'
            linarith
          exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
        have hRi : Function.Injective R := by
          intro z w he
          have h₀ := congrArg (fun p : Plane => p 0) he
          have h₁ := congrArg (fun p : Plane => p 1) he
          simp [R,Plane.mk] at h₁ h₀
          have h2 : (z.2:ℝ) = w.2 := h₀.resolve_right hε.ne'
          have h1 : (z.1:ℝ) = w.1 := by
            rw [h2] at h₁
            have hp : 0 < A+ε*(w.2:ℝ) := by nlinarith [w.2.property.1]
            have hd : (A+ε*(w.2:ℝ))*((z.1:ℝ)-(w.1:ℝ)) = 0 := by nlinarith
            have hd' := (mul_eq_zero.mp hd).resolve_left hp.ne'
            linarith
          exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
        have hL : IsEmbedding L := (hLc.isClosedEmbedding hLi).isEmbedding
        have hR : IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
        have hseam (w : Interval) : L (0,w) = R (0,w) := by simp [L,R]
        have hmeet : range L ∩ range R = range (fun w => L (0,w)) := by
          ext p
          constructor
          · rintro ⟨⟨z,hz⟩,⟨w,hw⟩⟩
            have he := hz.trans hw.symm
            have h₀ := congrArg (fun p : Plane => p 0) he
            have h₁ := congrArg (fun p : Plane => p 1) he
            simp [L,R,Plane.mk] at h₀ h₁
            have hl : -ε*(z.2:ℝ) ≤ A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) := by
              have hh := mul_nonneg (show 0 ≤ A+ε*(z.2:ℝ) by nlinarith [z.2.property.1]) z.1.property.1
              nlinarith only [hh]
            have hr : -ε*(w.2:ℝ) ≤ A*(w.1:ℝ)-ε*(w.2:ℝ)*(1-(w.1:ℝ)) := by
              have hh := mul_nonneg (show 0 ≤ A+ε*(w.2:ℝ) by nlinarith [w.2.property.1]) w.1.property.1
              nlinarith only [hh]
            have hdiag : A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) = -ε*(z.2:ℝ) := by linarith
            have hz0 : (z.1:ℝ) = 0 := by
              have hp : 0 < A+ε*(z.2:ℝ) := by nlinarith [z.2.property.1]
              have hd : (A+ε*(z.2:ℝ))*(z.1:ℝ) = 0 := by nlinarith only [hdiag]
              exact (mul_eq_zero.mp hd).resolve_left hp.ne'
            refine ⟨z.2,?_⟩
            rw [← hz]
            apply congrArg L
            exact Prod.ext (Subtype.ext hz0.symm) rfl
          · rintro ⟨w,rfl⟩
            exact ⟨mem_range_self _,⟨(0,w),(hseam w).symm⟩⟩
        obtain ⟨F,hF,hF0,hF1,hFm,hFr,hrows⟩ :=
          source_glue_two_surface_strips L R hL hR hseam hmeet
        refine ⟨⟨F,hF.continuous⟩,hF,?_,?_,?_,?_,hrows⟩
        · intro w
          simpa [L] using hF0 w
        · intro w
          simpa [R] using hF1 w
        · intro w
          simpa [L] using hFm w
        · change range F = _
          rw [hFr]
          ext p
          constructor
          · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
            · change -ε ≤ A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) ∧
                A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) ≤ A ∧
                -ε ≤ -ε*(z.2:ℝ) ∧ -ε*(z.2:ℝ) ≤ A ∧
                (A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) ≤ 0 ∨ -ε*(z.2:ℝ) ≤ 0)
              have hneg : 0 ≤ ε*(z.2:ℝ)*(1-(z.1:ℝ)) := by
                exact mul_nonneg (mul_nonneg hε.le z.2.property.1) (sub_nonneg.mpr z.1.property.2)
              have hlow := mul_nonneg (show 0 ≤ A+ε*(z.2:ℝ) by nlinarith [z.2.property.1]) z.1.property.1
              refine ⟨?_,?_,?_,?_,Or.inr ?_⟩ <;>
                nlinarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]
            · change -ε ≤ -ε*(z.2:ℝ) ∧ -ε*(z.2:ℝ) ≤ A ∧
                -ε ≤ A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) ∧
                A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) ≤ A ∧
                (-ε*(z.2:ℝ) ≤ 0 ∨ A*(z.1:ℝ)-ε*(z.2:ℝ)*(1-(z.1:ℝ)) ≤ 0)
              have hneg : 0 ≤ ε*(z.2:ℝ)*(1-(z.1:ℝ)) := by
                exact mul_nonneg (mul_nonneg hε.le z.2.property.1) (sub_nonneg.mpr z.1.property.2)
              have hlow := mul_nonneg (show 0 ≤ A+ε*(z.2:ℝ) by nlinarith [z.2.property.1]) z.1.property.1
              refine ⟨?_,?_,?_,?_,Or.inl ?_⟩ <;>
                nlinarith [z.1.property.1,z.1.property.2,z.2.property.1,z.2.property.2]
          · intro hp
            change -ε ≤ p 0 ∧ p 0 ≤ A ∧ -ε ≤ p 1 ∧ p 1 ≤ A ∧ (p 0 ≤ 0 ∨ p 1 ≤ 0) at hp
            by_cases hyx : p 1 ≤ p 0
            · have hy : p 1 ≤ 0 := by rcases hp.2.2.2.2 with hx | hy <;> linarith
              let w : Interval := ⟨-p 1/ε,by
                constructor
                · exact div_nonneg (neg_nonneg.mpr hy) hε.le
                · apply (div_le_iff₀ hε).mpr; linarith [hp.2.2.1]⟩
              have hw : -ε*(w:ℝ) = p 1 := by dsimp [w]; field_simp <;> ring
              have hden : 0 < A-p 1 := by linarith
              let v : Interval := ⟨(p 0-p 1)/(A-p 1),by
                constructor
                · exact div_nonneg (sub_nonneg.mpr hyx) hden.le
                · apply (div_le_iff₀ hden).mpr; linarith [hp.2.1]⟩
              refine Or.inl ⟨(v,w),?_⟩
              apply PiLp.ext
              intro i
              fin_cases i
              · change A*(v:ℝ)-ε*(w:ℝ)*(1-(v:ℝ)) = p 0
                have hyw : ε*(w:ℝ) = -p 1 := by linarith
                rw [hyw]
                dsimp [v]
                field_simp
                ring
              · exact hw
            · have hxy : p 0 ≤ p 1 := (lt_of_not_ge hyx).le
              have hx : p 0 ≤ 0 := by rcases hp.2.2.2.2 with hx | hy <;> linarith
              let w : Interval := ⟨-p 0/ε,by
                constructor
                · exact div_nonneg (neg_nonneg.mpr hx) hε.le
                · apply (div_le_iff₀ hε).mpr; linarith [hp.1]⟩
              have hw : -ε*(w:ℝ) = p 0 := by dsimp [w]; field_simp <;> ring
              have hden : 0 < A-p 0 := by linarith
              let v : Interval := ⟨(p 1-p 0)/(A-p 0),by
                constructor
                · exact div_nonneg (sub_nonneg.mpr hxy) hden.le
                · apply (div_le_iff₀ hden).mpr; linarith [hp.2.2.2.1]⟩
              refine Or.inr ⟨(v,w),?_⟩
              apply PiLp.ext
              intro i
              fin_cases i
              · exact hw
              · change A*(v:ℝ)-ε*(w:ℝ)*(1-(v:ℝ)) = p 1
                have hxw : ε*(w:ℝ) = -p 0 := by linarith
                rw [hxw]
                dsimp [v]
                field_simp
                ring
      let chartQ : OpenPartialHomeomorph ↥Q Plane := {
        toPartialEquiv := {
          toFun := fun y => d.cornerChart y.val
          invFun := fun z => if hz : z ∈ d.cornerChart.target then
            ⟨d.cornerChart.symm z,interior_subset (d.axis_interior (d.cornerChart.map_target hz))⟩
            else d.M.first 1
          source := (Subtype.val : ↥Q → S) ⁻¹' d.cornerChart.source
          target := d.cornerChart.target
          map_source' := fun _ hy => d.cornerChart.map_source hy
          map_target' := by
            intro z hz
            simp only [dif_pos hz,mem_preimage]
            exact d.cornerChart.map_target hz
          left_inv' := by
            intro y hy
            apply Subtype.ext
            simp only [dif_pos (d.cornerChart.map_source hy)]
            exact d.cornerChart.left_inv hy
          right_inv' := by
            intro z hz
            simp only [dif_pos hz]
            exact d.cornerChart.right_inv hz
        }
        open_source := d.cornerChart.open_source.preimage continuous_subtype_val
        open_target := d.cornerChart.open_target
        continuousOn_toFun := d.cornerChart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
        continuousOn_invFun := by
          apply IsInducing.subtypeVal.continuousOn_iff.mpr
          apply d.cornerChart.continuousOn_symm.congr
          intro z hz
          simp only [Function.comp_apply,dif_pos hz]
      }
    
      have hcenterQ : d.M.first 1 ∈ chartQ.source := by
        change (d.M.first 1).val ∈ d.cornerChart.source
        rw [← d.a_corner]
        exact d.axes.center_mem
      have hcenter0 : chartQ (d.M.first 1) = 0 := by
        change d.cornerChart (d.M.first 1).val = 0
        rw [← d.a_corner]
        exact d.axes.center_zero
      have hside_disk : range d.sideArc ⊆ range d.e := by
        rw [d.side_range]
        rintro y (hy | hy)
        · exact (d.disk_a_trace.symm ▸ hy).1
        · exact (d.disk_q_trace.symm ▸ hy).1
      have hcenterW : d.M.first 1 ∈ d.W := d.disk_in_W (hside_disk (d.side_range.symm ▸ Or.inl (mem_range_self 1)))
      let qo : C(Interval,↥Q) := ⟨fun u => q (d.xi u),q.continuous.comp d.xi.continuous⟩
      have hqo : IsEmbedding qo := d.q_embedded.comp d.xi.isEmbedding
      let Future : Set ↥Q := qo '' Ici d.t
      have hFutureclosed : IsClosed Future := (isClosed_Ici.isCompact.image qo.continuous).isClosed
      have hcenterFuture : d.M.first 1 ∉ Future := by
        rintro ⟨u,hu,he⟩
        have heq : u = d.s := hqo.injective (he.trans d.q_corner.symm)
        exact not_le_of_gt d.tail_order.2.1 (heq ▸ hu)
      have hBclosed : IsClosed B := by
        exact ((isCompact_sphere ((chartAt Plane x) x) R).image_of_continuousOn
          ((chartAt Plane x).continuousOn_symm.mono
            (Metric.sphere_subset_closedBall.trans htarget))).isClosed.preimage continuous_subtype_val
      let O : Set Plane := chartQ.target ∩ chartQ.symm ⁻¹' (d.W ∩ (Futureᶜ ∩ Bᶜ))
      have hO : IsOpen O := chartQ.isOpen_inter_preimage_symm
        (d.W_open.inter (hFutureclosed.isOpen_compl.inter hBclosed.isOpen_compl))
      have h0O : (0:Plane) ∈ O := by
        refine ⟨hcenter0 ▸ chartQ.map_source hcenterQ,?_⟩
        change chartQ.symm 0 ∈ d.W ∩ (Futureᶜ ∩ Bᶜ)
        rw [← hcenter0,chartQ.left_inv hcenterQ]
        exact ⟨hcenterW,hcenterFuture,d.M.corner_off_boundary⟩
      obtain ⟨r,hr,hrr,hsmall⟩ := Plane.exists_openSquare_subset hO h0O d.radius_bounds.1
      let A : ℝ := r/2
      let ε : ℝ := r/4
      have hA : 0 < A := by dsimp [A]; positivity
      have hε : 0 < ε := by dsimp [ε]; positivity
      have heA : ε < A := by dsimp [ε,A]; linarith
      have hAcut : A < r := by dsimp [A]; linarith
      have hεcut : ε < r := heA.trans hAcut
      have hAr : A < d.radius := by dsimp [A]; linarith
      have hsignsigma : d.sigma*d.sigma = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hsigntau : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have habssigma : |d.sigma| = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have habstau : |d.tau| = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      let signMap : Plane → Plane := fun z => Plane.mk (d.sigma*z 0) (d.tau*z 1)
      have hsignc : Continuous signMap := by dsimp [signMap]; fun_prop
      have hsigni : Function.Injective signMap := by
        intro z w he
        apply PiLp.ext
        intro i
        fin_cases i
        · have hh := congrArg (fun p : Plane => d.sigma*p 0) he
          simpa [signMap,Plane.mk,← mul_assoc,hsignsigma] using hh
        · have hh := congrArg (fun p : Plane => d.tau*p 1) he
          simpa [signMap,Plane.mk,← mul_assoc,hsigntau] using hh
      obtain ⟨P0,hP0,hP00,hP01,hP0m,hP0r,hP0rows⟩ := planarPatch A ε hA hε
      have hcoord (z : Interval × Interval) :
          -ε ≤ P0 z 0 ∧ P0 z 0 ≤ A ∧ -ε ≤ P0 z 1 ∧ P0 z 1 ≤ A ∧
          (P0 z 0 ≤ 0 ∨ P0 z 1 ≤ 0) := by
        have hh := mem_range_self (f := P0) z
        rw [hP0r] at hh
        exact hh
      have hsignO (z : Interval × Interval) : signMap (P0 z) ∈ O := by
        apply hsmall
        change Plane.supDist (signMap (P0 z)) 0 < r
        simp only [Plane.supDist,Plane.supNorm,sub_zero,signMap,Plane.mk,PiLp.toLp_apply,
          Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
        rw [abs_mul,abs_mul,habssigma,habstau,one_mul,one_mul]
        apply max_lt
        · apply abs_lt.mpr
          constructor <;> linarith [(hcoord z).1,(hcoord z).2.1]
        · apply abs_lt.mpr
          constructor <;> linarith [(hcoord z).2.2.1,(hcoord z).2.2.2.1]
      let P : C(Interval × Interval,↥Q) :=
        ⟨fun z => chartQ.symm (signMap (P0 z)),chartQ.continuousOn_symm.comp_continuous
          (hsignc.comp P0.continuous) (fun z => (hsignO z).1)⟩
      have hP : IsEmbedding P := (P.continuous.isClosedEmbedding (by
        intro z w he
        exact hP0.injective (hsigni (chartQ.symm.injOn (hsignO z).1 (hsignO w).1 he)))).isEmbedding
      have hchart (z : Interval × Interval) : d.cornerChart (P z).val = signMap (P0 z) :=
        chartQ.right_inv (hsignO z).1
      have habs0 (z) : |signMap (P0 z) 0| < d.radius := by
        change |d.sigma*P0 z 0| < _
        rw [abs_mul,habssigma,one_mul]
        apply abs_lt.mpr
        constructor <;> linarith [(hcoord z).1,(hcoord z).2.1]
      have habs1 (z) : |signMap (P0 z) 1| < d.radius := by
        change |d.tau*P0 z 1| < _
        rw [abs_mul,habstau,one_mul]
        apply abs_lt.mpr
        constructor <;> linarith [(hcoord z).2.2.1,(hcoord z).2.2.2.1]
      have hsigncoords0 (z) : d.sigma*signMap (P0 z) 0 = P0 z 0 := by simp [signMap,Plane.mk,← mul_assoc,hsignsigma]
      have hsigncoords1 (z) : d.tau*signMap (P0 z) 1 = P0 z 1 := by simp [signMap,Plane.mk,← mul_assoc,hsigntau]
      have hval (z) : (P z).val = d.cornerChart.symm (signMap (P0 z)) := by
        have hsrc : (P z).val ∈ d.cornerChart.source := chartQ.map_target (hsignO z).1
        rw [← hchart z,d.cornerChart.left_inv hsrc]
      have hw0 (z) : (0 ≤ P0 z 0 ∧ 0 ≤ P0 z 1) ↔ z.2 = 0 := by
        obtain ⟨v,hv | hv⟩ := hP0rows z
        · rw [hv]
          change (0 ≤ A*(v:ℝ)-ε*(z.2:ℝ)*(1-(v:ℝ)) ∧ 0 ≤ -ε*(z.2:ℝ)) ↔ z.2 = 0
          constructor
          · intro hh
            apply Subtype.ext
            change (z.2:ℝ) = 0
            nlinarith [z.2.property.1]
          · intro hh
            simp only [hh,Icc.coe_zero,mul_zero,zero_mul,sub_zero,neg_zero]
            exact ⟨mul_nonneg hA.le v.property.1,le_rfl⟩
        · rw [hv]
          change (0 ≤ -ε*(z.2:ℝ) ∧ 0 ≤ A*(v:ℝ)-ε*(z.2:ℝ)*(1-(v:ℝ))) ↔ z.2 = 0
          constructor
          · intro hh
            apply Subtype.ext
            change (z.2:ℝ) = 0
            nlinarith [z.2.property.1]
          · intro hh
            simp only [hh,Icc.coe_zero,mul_zero,zero_mul,sub_zero,neg_zero]
            exact ⟨le_rfl,mul_nonneg hA.le v.property.1⟩
      have hdisk (z) : P z ∈ range d.e ↔ z.2 = 0 := by
        have hh := (d.same_disk_quadrant (signMap (P0 z)) (habs0 z) (habs1 z)).2.2
        rw [← hval z,hsigncoords0,hsigncoords1] at hh
        have himage : (P z).val ∈ range (fun u => (d.e u).val) ↔ P z ∈ range d.e := by
          constructor
          · rintro ⟨u,he⟩; exact ⟨u,Subtype.ext he⟩
          · rintro ⟨u,he⟩; exact ⟨u,congrArg Subtype.val he⟩
        exact himage.symm.trans (hh.trans (hw0 z))
      have hside (z) : P z ∈ range d.sideArc ↔ z.2 = 0 := by
        constructor
        · intro hz
          exact (hdisk z).mp (hside_disk hz)
        · intro hz
          have hnonneg := (hw0 z).mpr hz
          obtain ⟨v,hv | hv⟩ := hP0rows z
          · have hy : P0 z 1 = 0 := by rw [hv,hz]; simp [Plane.mk]
            have hh := (d.same_disk_quadrant (signMap (P0 z)) (habs0 z) (habs1 z)).1
            have hmem : (P z).val ∈ range (fun u => (d.M.first u).val) := by
              rw [hval,hh]
              refine ⟨?_,?_⟩
              · simp [signMap,Plane.mk,hy]
              · rw [hsigncoords0]; exact hnonneg.1
            obtain ⟨u,hu⟩ := hmem
            rw [d.side_range]
            exact Or.inl ⟨u,Subtype.ext hu⟩
          · have hx : P0 z 0 = 0 := by rw [hv,hz]; simp [Plane.mk]
            have hh := (d.same_disk_quadrant (signMap (P0 z)) (habs0 z) (habs1 z)).2.1
            have hmem : (P z).val ∈ range (fun u => (d.M.second u).val) := by
              rw [hval,hh]
              refine ⟨?_,?_⟩
              · simp [signMap,Plane.mk,hx]
              · rw [hsigncoords1]; exact hnonneg.2
            obtain ⟨u,hu⟩ := hmem
            rw [d.side_range]
            exact Or.inr ⟨u,Subtype.ext hu⟩
      have hgammaplane (v : Interval) : Plane.mk 0 (-d.tau*ε*(v:ℝ)) ∈ O := by
        apply hsmall
        change Plane.supDist (Plane.mk 0 (-d.tau*ε*(v:ℝ))) 0 < r
        simp only [Plane.supDist,Plane.supNorm,sub_zero,Plane.mk,PiLp.toLp_apply,
          Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,abs_zero,abs_mul,abs_neg,habstau,one_mul,abs_of_pos hε,abs_of_nonneg v.property.1]
        exact max_lt hr (lt_of_le_of_lt (mul_le_of_le_one_right hε.le v.property.2) hεcut)
      let gamma : C(Interval,↥Q) := ⟨fun v => chartQ.symm (Plane.mk 0 (-d.tau*ε*(v:ℝ))),
        chartQ.continuousOn_symm.comp_continuous (by fun_prop) (fun v => (hgammaplane v).1)⟩
      have hgammachart (v) : d.cornerChart (gamma v).val = Plane.mk 0 (-d.tau*ε*(v:ℝ)) :=
        chartQ.right_inv (hgammaplane v).1
      have hgammacorner : gamma 0 = qo d.s := by
        change chartQ.symm (Plane.mk 0 (-d.tau*ε*(0:Interval))) = q (d.xi d.s)
        have hzero : Plane.mk 0 (-d.tau*ε*(0:Interval)) = (0:Plane) := by simp [Plane.mk]
        rw [hzero,← hcenter0,chartQ.left_inv hcenterQ,d.q_corner]
      have htaune : d.tau ≠ 0 := by
        intro hn
        rw [hn] at hsigntau
        norm_num at hsigntau
      have hgammai : Function.Injective gamma := by
        intro u v he
        have hh : (-d.tau*ε)*(u:ℝ) = (-d.tau*ε)*(v:ℝ) := by
          simpa [hgammachart,Plane.mk] using congrArg (fun y : ↥Q => d.cornerChart y.val 1) he
        exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr htaune) hε.ne') hh)
      have hgamma : IsEmbedding gamma := (gamma.continuous.isClosedEmbedding hgammai).isEmbedding
      have hgammaq : range gamma ⊆ range qo := by
        rintro y ⟨v,rfl⟩
        have hsrc : (gamma v).val ∈ d.cornerChart.source := chartQ.map_target (hgammaplane v).1
        have hx : d.cornerChart (gamma v).val 0 = 0 := by simp [hgammachart,Plane.mk]
        obtain ⟨u,hu⟩ := (d.axes.moving_axis _ hsrc).mpr hx
        refine ⟨d.xi.symm u,?_⟩
        apply Subtype.ext
        simpa [qo] using hu
      obtain ⟨b,hb⟩ := hgammaq (mem_range_self 1)
      have hg1notdisk : gamma 1 ∉ range d.e := by
        intro hm
        have hz0 : |(Plane.mk 0 (-d.tau*ε)) 0| < d.radius := by simpa [Plane.mk] using d.radius_bounds.1
        have hz1 : |(Plane.mk 0 (-d.tau*ε)) 1| < d.radius := by
          simpa [Plane.mk,abs_mul,habstau,abs_of_pos hε] using heA.trans hAr
        have hh := (d.same_disk_quadrant (Plane.mk 0 (-d.tau*ε)) hz0 hz1).2.2
        have hvalgamma : (gamma 1).val = d.cornerChart.symm (Plane.mk 0 (-d.tau*ε)) := by
          have hsrc : (gamma 1).val ∈ d.cornerChart.source := chartQ.map_target (hgammaplane 1).1
          have hh := d.cornerChart.left_inv hsrc
          rw [hgammachart] at hh
          simpa using hh.symm
        obtain ⟨u,hu⟩ := hm
        have hmval : d.cornerChart.symm (Plane.mk 0 (-d.tau*ε)) ∈ range (fun u => (d.e u).val) :=
          ⟨u,(congrArg Subtype.val hu).trans hvalgamma⟩
        have hineq := (hh.mp hmval).2
        simp [Plane.mk,← mul_assoc,hsigntau] at hineq
        linarith
      have hs_b : d.s < b := by
        by_contra hn
        have hble : b ≤ d.s := le_of_not_gt hn
        have hsec : qo b ∈ range d.M.second := d.second_trace.symm ▸ ⟨b,⟨bot_le,hble⟩,rfl⟩
        have hbdisk : qo b ∈ range d.e := (d.disk_q_trace.symm ▸ hsec).1
        exact hg1notdisk (hb ▸ hbdisk)
      have hb_t : b < d.t := by
        by_contra hn
        have hfuture : gamma 1 ∈ Future := ⟨b,le_of_not_gt hn,hb⟩
        exact (hgammaplane 1).2.2.1 hfuture
      have hgammarange : range gamma = qo '' Icc d.s b := by
        obtain ⟨_,hrange⟩ := ActualHarerCornerGeometry.embedded_subarc_parameter_interval
          qo gamma hqo hgamma hgammaq d.s b hgammacorner.symm hb
        rwa [uIcc_of_le hs_b.le] at hrange
      have hgammaP : range gamma ⊆ range P := by
        rintro y ⟨v,rfl⟩
        have hp : Plane.mk 0 (-ε*(v:ℝ)) ∈ range P0 := by
          rw [hP0r]
          simp only [mem_setOf_eq,Plane.mk,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
          refine ⟨by linarith,by linarith,?_,?_,Or.inl le_rfl⟩ <;>
            nlinarith [v.property.1,v.property.2]
        obtain ⟨z,hz⟩ := hp
        refine ⟨z,?_⟩
        change chartQ.symm (signMap (P0 z)) = _
        rw [hz]
        apply congrArg chartQ.symm
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [signMap,Plane.mk] <;> ring
      have hfutureP : Disjoint (qo '' Ioi b) (range P) := by
        apply disjoint_left.mpr
        rintro y ⟨u,hu,rfl⟩ ⟨z,hz⟩
        have hsrc : (P z).val ∈ d.cornerChart.source := chartQ.map_target (hsignO z).1
        have haxis0 : d.cornerChart (P z).val 0 = 0 :=
          (d.axes.moving_axis _ hsrc).mp ⟨d.xi u,(congrArg Subtype.val hz).symm⟩
        have hmodel0 : P0 z 0 = 0 := by
          have hh := congrArg (fun p : Plane => d.sigma*p 0) (hchart z)
          simp [haxis0,signMap,Plane.mk,← mul_assoc,hsignsigma] at hh
          exact hh.symm
        have hmodel1 : P0 z 1 < 0 := by
          by_contra hn
          have hwzero := (hw0 z).mp ⟨hmodel0.ge,le_of_not_gt hn⟩
          have heD : P z ∈ range d.e := (hdisk z).mpr hwzero
          have hQe : qo u ∈ range d.e := hz ▸ heD
          have hsrange : qo u ∈ range d.M.second := d.disk_q_trace ▸ ⟨hQe,mem_range_self (d.xi u)⟩
          rw [d.second_trace] at hsrange
          obtain ⟨v,hv,he⟩ := hsrange
          have hvu : v = u := hqo.injective he
          exact not_le_of_gt (hs_b.trans hu) (hvu ▸ hv.2)
        let v : Interval := ⟨-(P0 z 1)/ε,by
          constructor
          · exact div_nonneg (neg_nonneg.mpr hmodel1.le) hε.le
          · apply (div_le_iff₀ hε).mpr; linarith [(hcoord z).2.2.1]⟩
        have hegamma : gamma v = qo u := by
          rw [← hz]
          change chartQ.symm _ = chartQ.symm _
          apply congrArg chartQ.symm
          apply PiLp.ext
          intro i
          fin_cases i
          · simp [signMap,Plane.mk,hmodel0]
          · change -d.tau*ε*(v:ℝ) = d.tau*P0 z 1
            dsimp [v]
            field_simp <;> ring
        have hparam : qo u ∈ qo '' Icc d.s b := hgammarange ▸ ⟨v,hegamma⟩
        obtain ⟨w,hw,he⟩ := hparam
        have hwu : w = u := hqo.injective he
        exact not_le_of_gt hu (hwu ▸ hw.2)
      obtain ⟨k,hk⟩ := hgammaP (mem_range_self 1)
      have hkchart : signMap (P0 k) = Plane.mk 0 (-d.tau*ε) := by
        have hh := (hchart k).symm.trans (congrArg (fun y : ↥Q => d.cornerChart y.val) hk)
        simpa [hgammachart] using hh
      have hkwidth : k.2 = 1 := by
        obtain ⟨v,hv | hv⟩ := hP0rows k
        · have hh : (-d.tau*ε)*(k.2:ℝ) = (-d.tau*ε)*1 := by
            simpa [hv,signMap,Plane.mk,mul_assoc] using congrArg (fun p : Plane => p 1) hkchart
          exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr htaune) hε.ne') hh)
        · have hmodelzero : P0 k 0 = 0 := by
            simpa [signMap,Plane.mk,← mul_assoc,hsignsigma] using
              congrArg (fun p : Plane => d.sigma*p 0) hkchart
          have hh : -ε*(k.2:ℝ) = 0 := by simpa [hv,Plane.mk] using hmodelzero
          have hw : (k.2:ℝ) = 0 := (mul_eq_zero.mp hh).resolve_left (neg_ne_zero.mpr hε.ne')
          have hh1 := congrArg (fun p : Plane => d.tau*p 1) hkchart
          simp [hv,signMap,Plane.mk,hw,← mul_assoc,hsigntau] at hh1
          nlinarith [v.property.1]
      have hkinterior : k.1 ∈ Ioo (0:Interval) 1 := by
        constructor
        · apply lt_of_le_of_ne (bot_le : 0 ≤ k.1)
          intro hzero
          have hh := congrArg (fun y : ↥Q => d.sigma*d.cornerChart y.val 0) hk
          rw [show k = (0,k.2) from Prod.ext hzero.symm rfl] at hh
          rw [hchart,hP00] at hh
          simp [signMap,Plane.mk,← mul_assoc,hsignsigma,hgammachart] at hh
          linarith
        · apply lt_of_le_of_ne (le_top : k.1 ≤ 1)
          intro hone
          have hh := congrArg (fun y : ↥Q => d.tau*d.cornerChart y.val 1) hk
          rw [show k = (1,k.2) from Prod.ext hone rfl] at hh
          rw [hchart,hP01] at hh
          simp [signMap,Plane.mk,← mul_assoc,hsigntau,hgammachart] at hh
          linarith
    
      refine ⟨A,ε,hε,heA,hAr,P,hP,?_,?_,?_,hdisk,hside,?_,?_,?_,?_,?_,?_,
        b,hs_b,hb_t,?_,hfutureP,k.1,hkinterior,?_,?_⟩
      · rintro y ⟨z,rfl⟩
        exact (hsignO z).2.1
      · rintro y ⟨z,rfl⟩
        exact chartQ.map_target (hsignO z).1
      · intro z
        exact (hsignO z).2.2.2
      · intro w
        rw [hchart,hP00]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [signMap,Plane.mk] <;> ring
      · intro w
        rw [hchart,hP01]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [signMap,Plane.mk] <;> ring
      · intro w
        rw [hchart,hP0m]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [signMap,Plane.mk] <;> ring
    
      · intro z
        rw [hchart]
        simpa only [hsigncoords0,hsigncoords1] using hcoord z
      · intro z
        obtain ⟨v,hv | hv⟩ := hP0rows z
        · refine ⟨v,Or.inl ?_⟩
          rw [hchart,hv]
          apply PiLp.ext
          intro i
          fin_cases i <;> simp [signMap,Plane.mk] <;> ring
        · refine ⟨v,Or.inr ?_⟩
          rw [hchart,hv]
          apply PiLp.ext
          intro i
          fin_cases i <;> simp [signMap,Plane.mk] <;> ring
      · ext p
        constructor
        · rintro ⟨z,rfl⟩
          change -ε ≤ d.sigma*d.cornerChart (P z).val 0 ∧ d.sigma*d.cornerChart (P z).val 0 ≤ A ∧
            -ε ≤ d.tau*d.cornerChart (P z).val 1 ∧ d.tau*d.cornerChart (P z).val 1 ≤ A ∧
            (d.sigma*d.cornerChart (P z).val 0 ≤ 0 ∨ d.tau*d.cornerChart (P z).val 1 ≤ 0)
          rw [hchart]
          simpa only [hsigncoords0,hsigncoords1] using hcoord z
        · intro hp
          let model : Plane := Plane.mk (d.sigma*p 0) (d.tau*p 1)
          have hm : model ∈ range P0 := by
            rw [hP0r]
            simpa [model,Plane.mk] using hp
          obtain ⟨z,hz⟩ := hm
          have hsignp : signMap model = p := by
            apply PiLp.ext
            intro i
            fin_cases i <;> simp [signMap,model,Plane.mk,← mul_assoc,hsignsigma,hsigntau]
          exact ⟨z,(hchart z).trans ((congrArg signMap hz).trans hsignp)⟩
      · change qo '' Icc d.s b ⊆ range P
        rw [← hgammarange]
        exact hgammaP
      · have hkp : k = (k.1,1) := Prod.ext rfl hkwidth
        rw [← hkp]
        exact hk.trans hb.symm
      · have he := congrArg (fun y : ↥Q => d.cornerChart y.val) hb
        change d.cornerChart (qo b).val = _
        simpa [hgammachart] using he
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `corner_patch
      let some value := localDecl.value? | Lean.throwError "Missing proof value for local corner_patch"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do
          found := found.insert ax
      let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected local corner_patch axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS corner_patch: {found.toList}"
    obtain ⟨A,eps,heps,hepsA,hAr,P,hP,hPW,hPsource,hPB,hPe,hPside,hP0,hP1,hPm,hPbox,hProws,hPwhole,
      b,hsb,hbt,hprefix,hfutureP,k,hk,hkq,hbchart⟩ := corner_patch
    obtain ⟨c,α,β,hα0,hαc,hcβ,hβ1,hcside,hαP,hβP,hPclock⟩ :=
      patch_side_clocks A eps (heps.trans hepsA) hAr P hP
        (fun z => hPsource (mem_range_self z)) hPside hP0 hP1
    have hBclosed : IsClosed B := by
      exact ((isCompact_sphere ((chartAt Plane x) x) R).image_of_continuousOn
        ((chartAt Plane x).continuousOn_symm.mono
          (Metric.sphere_subset_closedBall.trans htarget))).isClosed.preimage continuous_subtype_val
    have hαsrc : (d.sideArc α).val ∈ d.cornerChart.source := by
      rw [hαP]
      exact hPsource (mem_range_self (0,0))
    have hβsrc : (d.sideArc β).val ∈ d.cornerChart.source := by
      rw [hβP]
      exact hPsource (mem_range_self (1,0))
    have hαcoord : d.cornerChart (d.sideArc α).val = Plane.mk (d.sigma*A) 0 := by
      rw [hαP]
      simpa using hP0 0
    have hβcoord : d.cornerChart (d.sideArc β).val = Plane.mk 0 (d.tau*A) := by
      rw [hβP]
      simpa using hP1 0
    let first_ray_interval : ∀ x ∈ Icc (0:ℝ) A,
      d.cornerChart.symm (Plane.mk (d.sigma*x) 0) ∈
        (fun u : Interval => (d.sideArc u).val) '' Icc α c := by
      have hA : 0 < A := heps.trans hepsA
    
      have hσ : d.sigma*d.sigma = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hσn : d.sigma ≠ 0 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have haσ : |d.sigma| = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      let line : C(Interval,Plane) := ⟨fun u => Plane.mk (d.sigma*(A*(1-(u:ℝ)))) 0,by fun_prop⟩
      have habs (u : Interval) : |line u 0| < d.radius := by
        change |d.sigma*(A*(1-(u:ℝ)))| < d.radius
        rw [abs_mul,haσ,one_mul,abs_of_nonneg (mul_nonneg hA.le (sub_nonneg.mpr u.property.2))]
        nlinarith only [u.property.1,hA,hAr]
      have hy (u) : |line u 1| < d.radius := by simpa [line,Plane.mk] using d.radius_bounds.1
      have htarget (u : Interval) : line u ∈ d.cornerChart.target := by
        apply d.small_square
        change Plane.supDist (line u) 0 ≤ d.radius
        simpa [Plane.supDist,Plane.supNorm,sub_zero] using
          (max_lt (habs u) (hy u)).le
      let γ : C(Interval,S) := ⟨fun u => d.cornerChart.symm (line u),
        d.cornerChart.continuousOn_symm.comp_continuous line.continuous htarget⟩
      have hγ : IsEmbedding γ := by
        apply (γ.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        have hp := d.cornerChart.symm.injOn (htarget u) (htarget v) he
        have hh := congrArg (fun z : Plane => z 0) hp
        change d.sigma*(A*(1-(u:ℝ))) = d.sigma*(A*(1-(v:ℝ))) at hh
        have h1 := mul_left_cancel₀ hσn hh
        have h2 := mul_left_cancel₀ hA.ne' h1
        apply Subtype.ext
        linarith only [h2]
      let side : C(Interval,S) := ⟨fun u => (d.sideArc u).val,continuous_subtype_val.comp d.sideArc.continuous⟩
      have hside : IsEmbedding side := IsEmbedding.subtypeVal.comp d.side_embedded
      have hsub : range γ ⊆ range side := by
        rintro y ⟨u,rfl⟩
        have hm := (d.same_disk_quadrant (line u) (habs u) (hy u)).1.mpr (by
          constructor
          · simp [line,Plane.mk]
          · change 0 ≤ d.sigma*(d.sigma*(A*(1-(u:ℝ))))
            rw [← mul_assoc,hσ,one_mul]
            exact mul_nonneg hA.le (sub_nonneg.mpr u.property.2))
        obtain ⟨v,hv⟩ := hm
        have hs : d.M.first v ∈ range d.sideArc := d.side_range.symm ▸ Or.inl (mem_range_self v)
        obtain ⟨w,hw⟩ := hs
        exact ⟨w,(congrArg Subtype.val hw).trans hv⟩
      have hγ0 : side α = γ 0 := by
        change (d.sideArc α).val = d.cornerChart.symm (line 0)
        have hline : line 0 = Plane.mk (d.sigma*A) 0 := by simp [line,Plane.mk]
        rw [hline,← hαcoord,d.cornerChart.left_inv hαsrc]
      have hcenterSrc : (d.M.first 1).val ∈ d.cornerChart.source := by
        rw [← d.a_corner]
        exact d.axes.center_mem
      have hcenterZero : d.cornerChart (d.M.first 1).val = 0 := by
        rw [← d.a_corner]
        exact d.axes.center_zero
      have hγ1 : side c = γ 1 := by
        change (d.sideArc c).val = d.cornerChart.symm (line 1)
        rw [hcside,show line 1 = 0 from by simp [line,Plane.mk],← hcenterZero,d.cornerChart.left_inv hcenterSrc]
      have hrange := ActualHarerCornerGeometry.embedded_subarc_parameter_interval side γ hside hγ hsub α c hγ0 hγ1
      intro x hx
      let v : Interval := ⟨1-x/A,by
        have hdiv : x/A ≤ 1 := (div_le_one hA).mpr hx.2
        have hdiv0 : 0 ≤ x/A := div_nonneg hx.1 hA.le
        constructor <;> linarith⟩
      have hv : γ v = d.cornerChart.symm (Plane.mk (d.sigma*x) 0) := by
        apply congrArg d.cornerChart.symm
        apply PiLp.ext
        intro i
        fin_cases i
        · change d.sigma*(A*(1-(1-x/A))) = d.sigma*x
          field_simp
          <;> ring
        · simp [line,Plane.mk]
      have hm : d.cornerChart.symm (Plane.mk (d.sigma*x) 0) ∈ range γ := ⟨v,hv⟩
      rw [hrange.2,uIcc_of_le hαc.le] at hm
      exact hm
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `first_ray_interval
      let some value := localDecl.value? | Lean.throwError "Missing local first_ray_interval value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected first_ray_interval axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS first_ray_interval: {found.toList}"
    let second_ray_interval : ∀ x ∈ Icc (0:ℝ) A,
      d.cornerChart.symm (Plane.mk 0 (d.tau*x)) ∈
        (fun u : Interval => (d.sideArc u).val) '' Icc c β := by
      have hA : 0 < A := heps.trans hepsA
    
      have hσ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hσn : d.tau ≠ 0 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have haσ : |d.tau| = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      let line : C(Interval,Plane) := ⟨fun u => Plane.mk 0 (d.tau*(A*(u:ℝ))),by fun_prop⟩
      have habs (u : Interval) : |line u 1| < d.radius := by
        change |d.tau*(A*(u:ℝ))| < d.radius
        rw [abs_mul,haσ,one_mul,abs_of_nonneg (mul_nonneg hA.le u.property.1)]
        nlinarith only [u.property.2,hA,hAr]
      have hy (u) : |line u 0| < d.radius := by simpa [line,Plane.mk] using d.radius_bounds.1
      have htarget (u : Interval) : line u ∈ d.cornerChart.target := by
        apply d.small_square
        change Plane.supDist (line u) 0 ≤ d.radius
        simpa [Plane.supDist,Plane.supNorm,sub_zero] using
          (max_lt (hy u) (habs u)).le
      let γ : C(Interval,S) := ⟨fun u => d.cornerChart.symm (line u),
        d.cornerChart.continuousOn_symm.comp_continuous line.continuous htarget⟩
      have hγ : IsEmbedding γ := by
        apply (γ.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        have hp := d.cornerChart.symm.injOn (htarget u) (htarget v) he
        have hh := congrArg (fun z : Plane => z 1) hp
        change d.tau*(A*(u:ℝ)) = d.tau*(A*(v:ℝ)) at hh
        have h1 := mul_left_cancel₀ hσn hh
        have h2 := mul_left_cancel₀ hA.ne' h1
        apply Subtype.ext
        linarith only [h2]
      let side : C(Interval,S) := ⟨fun u => (d.sideArc u).val,continuous_subtype_val.comp d.sideArc.continuous⟩
      have hside : IsEmbedding side := IsEmbedding.subtypeVal.comp d.side_embedded
      have hsub : range γ ⊆ range side := by
        rintro y ⟨u,rfl⟩
        have hm := (d.same_disk_quadrant (line u) (hy u) (habs u)).2.1.mpr (by
          constructor
          · simp [line,Plane.mk]
          · change 0 ≤ d.tau*(d.tau*(A*(u:ℝ)))
            rw [← mul_assoc,hσ,one_mul]
            exact mul_nonneg hA.le u.property.1)
        obtain ⟨v,hv⟩ := hm
        have hs : d.M.second v ∈ range d.sideArc := d.side_range.symm ▸ Or.inr (mem_range_self v)
        obtain ⟨w,hw⟩ := hs
        exact ⟨w,(congrArg Subtype.val hw).trans hv⟩
      have hcenterSrc : (d.M.first 1).val ∈ d.cornerChart.source := by
        rw [← d.a_corner]
        exact d.axes.center_mem
      have hcenterZero : d.cornerChart (d.M.first 1).val = 0 := by
        rw [← d.a_corner]
        exact d.axes.center_zero
      have hγ0 : side c = γ 0 := by
        change (d.sideArc c).val = d.cornerChart.symm (line 0)
        rw [hcside,show line 0 = 0 from by simp [line,Plane.mk],← hcenterZero,d.cornerChart.left_inv hcenterSrc]
      have hγ1 : side β = γ 1 := by
        change (d.sideArc β).val = d.cornerChart.symm (line 1)
        have hline : line 1 = Plane.mk 0 (d.tau*A) := by simp [line,Plane.mk]
        rw [hline,← hβcoord,d.cornerChart.left_inv hβsrc]
      have hrange := ActualHarerCornerGeometry.embedded_subarc_parameter_interval side γ hside hγ hsub c β hγ0 hγ1
      intro x hx
      let v : Interval := ⟨x/A,⟨div_nonneg hx.1 hA.le,(div_le_one hA).mpr hx.2⟩⟩
      have hv : γ v = d.cornerChart.symm (Plane.mk 0 (d.tau*x)) := by
        apply congrArg d.cornerChart.symm
        apply PiLp.ext
        intro i
        fin_cases i
        · simp [line,Plane.mk]
        · change d.tau*(A*(x/A)) = d.tau*x
          field_simp
          <;> ring
      have hm : d.cornerChart.symm (Plane.mk 0 (d.tau*x)) ∈ range γ := ⟨v,hv⟩
      rw [hrange.2,uIcc_of_le hcβ.le] at hm
      exact hm
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `second_ray_interval
      let some value := localDecl.value? | Lean.throwError "Missing local second_ray_interval value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected second_ray_interval axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS second_ray_interval: {found.toList}"
    obtain ⟨HL,hHL,hHLc,hHLB,hHLW,hHLmeet,lamL,ηL,hlamL,hηL,hHLcal⟩ :=
      first_port_exterior hBclosed A (heps.trans hepsA) hAr α
        ⟨hα0,hαc.trans (hcβ.trans hβ1)⟩ hαsrc hαcoord
    obtain ⟨HR,hHR,hHRc,hHRB,hHRW,hHRmeet,lamR,ηR,hlamR,hηR,hHRcal⟩ :=
      second_port_exterior hBclosed A (heps.trans hepsA) hAr β
        ⟨hα0.trans (hαc.trans hcβ),hβ1⟩ hβsrc hβcoord
    let near_port_side_orders :
      (∀ u : Interval, u ≤ α → |(u:ℝ)-(α:ℝ)| < ηL →
        A ≤ d.sigma*d.cornerChart (d.sideArc u).val 0 ∧
          (d.sigma*d.cornerChart (d.sideArc u).val 0 = A → u = α)) ∧
      (∀ u : Interval, β ≤ u → |(u:ℝ)-(β:ℝ)| < ηR →
        A ≤ d.tau*d.cornerChart (d.sideArc u).val 1 ∧
          (d.tau*d.cornerChart (d.sideArc u).val 1 = A → u = β)) := by
      have hσ : d.sigma*d.sigma = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hτ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      constructor
      · intro u hu huη
        have hc := hHLcal u 0 huη
        have hsrc : (d.sideArc u).val ∈ d.cornerChart.source := by simpa only [hHLc] using hc.1
        have hline : d.cornerChart (d.sideArc u).val = Plane.mk (d.cornerChart (d.sideArc u).val 0) 0 := by
          simpa only [hHLc,Icc.coe_zero,mul_zero] using hc.2.1
        let x : ℝ := d.sigma*d.cornerChart (d.sideArc u).val 0
        have hx : 0 < x := by simpa only [hHLc] using hc.2.2.1
        have force (hxA : x ≤ A) : u = α := by
          have hm := first_ray_interval x ⟨hx.le,hxA⟩
          have hmark : Plane.mk (d.sigma*x) 0 = d.cornerChart (d.sideArc u).val := by
            calc
              _ = Plane.mk (d.cornerChart (d.sideArc u).val 0) 0 := by
                apply PiLp.ext
                intro i
                fin_cases i
                · change d.sigma*(d.sigma*d.cornerChart (d.sideArc u).val 0) = d.cornerChart (d.sideArc u).val 0
                  rw [← mul_assoc,hσ,one_mul]
                · simp [Plane.mk]
              _ = _ := hline.symm
          rw [hmark,d.cornerChart.left_inv hsrc] at hm
          obtain ⟨v,hv,he⟩ := hm
          have hvu : v = u := d.side_embedded.injective (Subtype.ext he)
          exact le_antisymm hu (hvu ▸ hv.1)
        refine ⟨?_,fun he => force he.le⟩
        by_contra he
        have hxA : x < A := lt_of_not_ge he
        have hux := force hxA.le
        have hxe : x = A := by
          dsimp [x]
          rw [hux,hαcoord]
          simp [Plane.mk,← mul_assoc,hσ]
        rw [hxe] at hxA
        exact (lt_irrefl A) hxA
      · intro u hu huη
        have hc := hHRcal u 0 huη
        have hsrc : (d.sideArc u).val ∈ d.cornerChart.source := by simpa only [hHRc] using hc.1
        have hline : d.cornerChart (d.sideArc u).val = Plane.mk 0 (d.cornerChart (d.sideArc u).val 1) := by
          simpa only [hHRc,Icc.coe_zero,mul_zero] using hc.2.1
        let x : ℝ := d.tau*d.cornerChart (d.sideArc u).val 1
        have hx : 0 < x := by simpa only [hHRc] using hc.2.2.1
        have force (hxA : x ≤ A) : u = β := by
          have hm := second_ray_interval x ⟨hx.le,hxA⟩
          have hmark : Plane.mk 0 (d.tau*x) = d.cornerChart (d.sideArc u).val := by
            calc
              _ = Plane.mk 0 (d.cornerChart (d.sideArc u).val 1) := by
                apply PiLp.ext
                intro i
                fin_cases i
                · simp [Plane.mk]
                · change d.tau*(d.tau*d.cornerChart (d.sideArc u).val 1) = d.cornerChart (d.sideArc u).val 1
                  rw [← mul_assoc,hτ,one_mul]
              _ = _ := hline.symm
          rw [hmark,d.cornerChart.left_inv hsrc] at hm
          obtain ⟨v,hv,he⟩ := hm
          have hvu : v = u := d.side_embedded.injective (Subtype.ext he)
          exact le_antisymm (hvu ▸ hv.2) hu
        refine ⟨?_,fun he => force he.le⟩
        by_contra he
        have hxA : x < A := lt_of_not_ge he
        have hux := force hxA.le
        have hxe : x = A := by
          dsimp [x]
          rw [hux,hβcoord]
          simp [Plane.mk,← mul_assoc,hτ]
        rw [hxe] at hxA
        exact (lt_irrefl A) hxA
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `near_port_side_orders
      let some value := localDecl.value? | Lean.throwError "Missing local near_port_side_orders value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected near_port_side_orders axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS near_port_side_orders: {found.toList}"
    let matched_physical_faces : ∀ ε' : ℝ, 0 < ε' → ε' ≤ eps → ε' ≤ lamL → ε' ≤ lamR →
      ∃ Pc L R : C(Interval × Interval,↥Q),
        IsEmbedding Pc ∧ IsEmbedding L ∧ IsEmbedding R ∧
        range Pc ⊆ d.W ∧ range L ⊆ d.W ∧ range R ⊆ d.W ∧
        (∀ u, Pc (u,0) = P (u,0)) ∧
        (∀ u, L (u,0) = d.sideArc (Icc.convexComb 0 α u)) ∧
        (∀ u, R (u,0) = d.sideArc (Icc.convexComb β 1 u)) ∧
        (∀ z, Pc z ∈ range d.e ↔ z.2 = 0) ∧
        (∀ z, L z ∈ range d.e ↔ z.2 = 0) ∧
        (∀ z, R z ∈ range d.e ↔ z.2 = 0) ∧
        (∀ z, L z ∈ B ↔ z.1 = 0) ∧ (∀ z, R z ∈ B ↔ z.1 = 1) ∧
        (∀ w, L (1,w) = Pc (0,w)) ∧ (∀ w, R (0,w) = Pc (1,w)) ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = (ε'/eps)*(z.2:ℝ) → Pc z = P (z.1,w)) ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = (ε'/lamL)*(z.2:ℝ) →
          L z = HL (Icc.convexComb 0 α z.1,w)) ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = (ε'/lamR)*(z.2:ℝ) →
          R z = HR (Icc.convexComb β 1 z.1,w)) := by
      intro ε' he' he'P he'L he'R
      let shrink (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 1) : C(Interval,Interval) :=
        ⟨fun w => ⟨κ*(w:ℝ),by constructor <;> nlinarith [w.property.1,w.property.2,hκ.1,hκ.2]⟩,
          by fun_prop⟩
      have hshrink (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 1) : IsEmbedding (shrink κ hκ) := by
        apply ((shrink κ hκ).continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply Subtype.ext
        exact mul_left_cancel₀ hκ.1.ne' (congrArg (fun w : Interval => (w:ℝ)) he)
      have hzshrink (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 1) : shrink κ hκ 0 = 0 := by
        apply Subtype.ext
        simp [shrink]
      have hezshrink (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 1) (w : Interval) :
          shrink κ hκ w = 0 ↔ w = 0 := by
        exact ⟨fun he => (hshrink κ hκ).injective (he.trans (hzshrink κ hκ).symm),
          fun he => he ▸ hzshrink κ hκ⟩
      let κP := ε'/eps
      let κL := ε'/lamL
      let κR := ε'/lamR
      have hκP : 0 < κP ∧ κP ≤ 1 := ⟨div_pos he' heps,(div_le_one heps).mpr he'P⟩
      have hκL : 0 < κL ∧ κL ≤ 1 := ⟨div_pos he' hlamL,(div_le_one hlamL).mpr he'L⟩
      have hκR : 0 < κR ∧ κR ≤ 1 := ⟨div_pos he' hlamR,(div_le_one hlamR).mpr he'R⟩
      let cl : C(Interval,Interval) := ⟨Icc.convexComb 0 α,Icc.continuous_convexComb 0 α⟩
      let cr : C(Interval,Interval) := ⟨Icc.convexComb β 1,Icc.continuous_convexComb β 1⟩
      have hcl : IsEmbedding cl := by
        apply (cl.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply Subtype.ext
        have he' := congrArg (fun w : Interval => (w:ℝ)) he
        change (Icc.convexComb 0 α u:ℝ) = (Icc.convexComb 0 α v:ℝ) at he'
        simp only [Icc.coe_convexComb,Icc.coe_zero] at he'
        have ha : (0:ℝ) < α := hα0
        nlinarith only [he',ha]
      have hcr : IsEmbedding cr := by
        apply (cr.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply Subtype.ext
        have he' := congrArg (fun w : Interval => (w:ℝ)) he
        change (Icc.convexComb β 1 u:ℝ) = (Icc.convexComb β 1 v:ℝ) at he'
        simp only [Icc.coe_convexComb,Icc.coe_one] at he'
        have hb : (β:ℝ) < 1 := hβ1
        nlinarith only [he',hb]
      have hcl0 : cl 0 = 0 := Icc.convexComb_zero _ _
      have hcl1 : cl 1 = α := Icc.convexComb_one _ _
      have hcr0 : cr 0 = β := Icc.convexComb_zero _ _
      have hcr1 : cr 1 = 1 := Icc.convexComb_one _ _
      let pcmap := (ContinuousMap.id Interval).prodMap (shrink κP hκP)
      let lcmap := cl.prodMap (shrink κL hκL)
      let rcmap := cr.prodMap (shrink κR hκR)
      let Pc : C(Interval × Interval,↥Q) := P.comp pcmap
      let L : C(Interval × Interval,↥Q) := HL.comp lcmap
      let R : C(Interval × Interval,↥Q) := HR.comp rcmap
      have hPc : IsEmbedding Pc := hP.comp (IsEmbedding.id.prodMap (hshrink κP hκP))
      have hL : IsEmbedding L := hHL.comp (hcl.prodMap (hshrink κL hκL))
      have hR : IsEmbedding R := hHR.comp (hcr.prodMap (hshrink κR hκR))
      have hL0 (u) : L (u,0) = d.sideArc (cl u) := by
        change HL (cl u,shrink κL hκL 0) = _
        rw [hzshrink κL hκL,hHLc]
      have hR0 (u) : R (u,0) = d.sideArc (cr u) := by
        change HR (cr u,shrink κR hκR 0) = _
        rw [hzshrink κR hκR,hHRc]
      have hsideD : range d.sideArc ⊆ range d.e := by
        rw [d.side_range]
        rintro y (hy | hy)
        · exact (d.disk_a_trace.symm ▸ hy).1
        · exact (d.disk_q_trace.symm ▸ hy).1
      have pointDisk (H : C(Interval × Interval,↥Q)) (hH : IsEmbedding H)
          (hc : ∀ u, H (u,0) = d.sideArc u)
          (hm : range H ∩ range d.e = range d.sideArc) (z) :
          H z ∈ range d.e ↔ z.2 = 0 := by
        constructor
        · intro he
          have hmz : H z ∈ range d.sideArc := hm ▸
            (show H z ∈ range H ∩ range d.e from ⟨mem_range_self z,he⟩)
          obtain ⟨v,hv⟩ := hmz
          have hh := hH.injective ((hc v).trans hv)
          exact (congrArg Prod.snd hh).symm
        · intro he
          rw [show z = (z.1,0) from Prod.ext rfl he,hc]
          exact hsideD (mem_range_self _)
      have hL1 (w) : L (1,w) = HL (α,shrink κL hκL w) := congrArg HL (Prod.ext hcl1 rfl)
      have hR1 (w) : R (0,w) = HR (β,shrink κR hκR w) := congrArg HR (Prod.ext hcr0 rfl)
      refine ⟨Pc,L,R,hPc,hL,hR,?_,?_,?_,?_,hL0,hR0,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · rintro y ⟨z,rfl⟩
        exact hPW (mem_range_self (pcmap z))
      · rintro y ⟨z,rfl⟩
        exact hHLW (mem_range_self (lcmap z))
      · rintro y ⟨z,rfl⟩
        exact hHRW (mem_range_self (rcmap z))
      · intro u
        change P (u,shrink κP hκP 0) = _
        rw [hzshrink κP hκP]
      · intro z
        change P (z.1,shrink κP hκP z.2) ∈ range d.e ↔ _
        rw [hPe,hezshrink κP hκP]
      · intro z
        change HL (cl z.1,shrink κL hκL z.2) ∈ range d.e ↔ _
        rw [pointDisk HL hHL hHLc hHLmeet,hezshrink κL hκL]
      · intro z
        change HR (cr z.1,shrink κR hκR z.2) ∈ range d.e ↔ _
        rw [pointDisk HR hHR hHRc hHRmeet,hezshrink κR hκR]
      · intro z
        change HL (cl z.1,shrink κL hκL z.2) ∈ B ↔ _
        rw [hHLB]
        constructor
        · rintro (he | he)
          · exact hcl.injective (he.trans hcl0.symm)
          · have hh : cl z.1 ≤ α := Icc.convexComb_le (bot_le : (0:Interval) ≤ α) _
            exact False.elim (not_le_of_gt (hαc.trans (hcβ.trans hβ1)) (he ▸ hh))
        · intro he
          exact Or.inl (he ▸ hcl0)
      · intro z
        change HR (cr z.1,shrink κR hκR z.2) ∈ B ↔ _
        rw [hHRB]
        constructor
        · rintro (he | he)
          · have hh : β ≤ cr z.1 := Icc.le_convexComb (le_top : β ≤ (1:Interval)) _
            exact False.elim (not_le_of_gt (hα0.trans (hαc.trans hcβ)) (he ▸ hh))
          · exact hcr.injective (he.trans hcr1.symm)
        · intro he
          exact Or.inr (he ▸ hcr1)
      · intro w
        rw [hL1]
        have hl := hHLcal α (shrink κL hκL w) (by simpa using hηL)
        apply Subtype.ext
        apply d.cornerChart.injOn hl.1 (hPsource (mem_range_self (0,shrink κP hκP w)))
        change d.cornerChart (HL (α,shrink κL hκL w)).val =
          d.cornerChart (P (0,shrink κP hκP w)).val
        rw [hl.2.1,hP0,hαcoord]
        apply PiLp.ext
        intro i
        fin_cases i
        · simp [Plane.mk]
        · simp [Plane.mk,shrink,κP,κL]
          field_simp
          <;> ring
      · intro w
        rw [hR1]
        have hr := hHRcal β (shrink κR hκR w) (by simpa using hηR)
        apply Subtype.ext
        apply d.cornerChart.injOn hr.1 (hPsource (mem_range_self (1,shrink κP hκP w)))
        change d.cornerChart (HR (β,shrink κR hκR w)).val =
          d.cornerChart (P (1,shrink κP hκP w)).val
        rw [hr.2.1,hP1,hβcoord]
        apply PiLp.ext
        intro i
        fin_cases i
        · simp [Plane.mk,shrink,κP,κR]
          field_simp
          <;> ring
        · simp [Plane.mk]
      · intro z w hw
        change P (z.1,shrink κP hκP z.2) = _
        apply congrArg P
        exact Prod.ext rfl (Subtype.ext hw.symm)
      · intro z w hw
        change HL (Icc.convexComb 0 α z.1,shrink κL hκL z.2) = _
        apply congrArg HL
        exact Prod.ext rfl (Subtype.ext hw.symm)
      · intro z w hw
        change HR (Icc.convexComb β 1 z.1,shrink κR hκR z.2) = _
        apply congrArg HR
        exact Prod.ext rfl (Subtype.ext hw.symm)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `matched_physical_faces
      let some value := localDecl.value? | Lean.throwError "Missing local matched_physical_faces value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected matched_physical_faces axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS matched_physical_faces: {found.toList}"
    let faceWidth : ℝ := min eps (min lamL lamR)/2
    have hfaceWidth : 0 < faceWidth := by
      exact half_pos (lt_min heps (lt_min hlamL hlamR))
    have hfaceP : faceWidth ≤ eps := by
      dsimp [faceWidth]
      linarith [min_le_left eps (min lamL lamR)]
    have hfaceL : faceWidth ≤ lamL := by
      dsimp [faceWidth]
      have h := (min_le_right eps (min lamL lamR)).trans (min_le_left lamL lamR)
      linarith
    have hfaceR : faceWidth ≤ lamR := by
      dsimp [faceWidth]
      have h := (min_le_right eps (min lamL lamR)).trans (min_le_right lamL lamR)
      linarith
    obtain ⟨Pc,Lface,Rface,hPc,hLface,hRface,hPcW,hLfaceW,hRfaceW,
      hPcseam,hLfaceseam,hRfaceseam,hPcdisk,hLdisk,hRdisk,hLfaceB,hRfaceB,
      hleftmatch,hrightmatch,hPcform,hLfaceform,hRfaceform⟩ :=
      matched_physical_faces faceWidth hfaceWidth hfaceP hfaceL hfaceR
    have hPcclock : range (fun u : Interval => Pc (u,0)) = d.sideArc '' Icc α β := by
      rw [show (fun u : Interval => Pc (u,0)) = (fun u : Interval => P (u,0)) from funext hPcseam]
      exact hPclock
    have hLclock : range (fun u : Interval => Lface (u,0)) = d.sideArc '' Icc 0 α := by
      rw [show (fun u : Interval => Lface (u,0)) = d.sideArc ∘ Icc.convexComb 0 α from funext hLfaceseam]
      rw [Set.range_comp,Path.range_subpathAux,uIcc_of_le hα0.le]
    have hRclock : range (fun u : Interval => Rface (u,0)) = d.sideArc '' Icc β 1 := by
      rw [show (fun u : Interval => Rface (u,0)) = d.sideArc ∘ Icc.convexComb β 1 from funext hRfaceseam]
      rw [Set.range_comp,Path.range_subpathAux,uIcc_of_le hβ1.le]
    have hseam_union : range (fun u : Interval => Lface (u,0)) ∪
        range (fun u : Interval => Pc (u,0)) ∪ range (fun u : Interval => Rface (u,0)) =
        range d.sideArc := by
      rw [hLclock,hPcclock,hRclock]
      ext y
      constructor
      · rintro ((⟨u,hu,rfl⟩ | ⟨u,hu,rfl⟩) | ⟨u,hu,rfl⟩) <;> exact mem_range_self _
      · rintro ⟨u,rfl⟩
        by_cases huα : u ≤ α
        · exact Or.inl (Or.inl ⟨u,⟨bot_le,huα⟩,rfl⟩)
        by_cases huβ : u ≤ β
        · exact Or.inl (Or.inr ⟨u,⟨(lt_of_not_ge huα).le,huβ⟩,rfl⟩)
        · exact Or.inr ⟨u,⟨(lt_of_not_ge huβ).le,le_top⟩,rfl⟩
    let remaining_center_clear :
      (∀ u : Interval, Lface (u,0) ∉ (fun v => q (d.xi v)) '' Ici d.s) ∧
      (∀ u : Interval, Rface (u,0) ∉ (fun v => q (d.xi v)) '' Ici d.s) ∧
      (∀ u v : Interval, Lface (u,0) ≠ Rface (v,0)) := by
      have hfirstsub : range d.M.first ⊆ range d.sideArc := by
        rw [d.side_range]
        exact subset_union_left
      have hsecondsub : range d.M.second ⊆ range d.sideArc := by
        rw [d.side_range]
        exact subset_union_right
      have hf := ActualHarerCornerGeometry.embedded_subarc_parameter_interval
        d.sideArc d.M.first d.side_embedded d.M.first_embedded hfirstsub 0 c d.side_zero hcside
      have hs := ActualHarerCornerGeometry.embedded_subarc_parameter_interval
        d.sideArc d.M.second d.side_embedded d.M.second_embedded hsecondsub 1 c d.side_one
          (hcside.trans d.M.corner_eq)
      have hfirst : range d.M.first = d.sideArc '' Icc 0 c := by
        simpa only [uIcc_of_le (hα0.trans hαc).le] using hf.2
      have hsecond : range d.M.second = d.sideArc '' Icc c 1 := by
        simpa only [uIcc_of_ge (hcβ.trans hβ1).le] using hs.2
      refine ⟨?_,?_,?_⟩
      · intro u hu
        obtain ⟨v,hv,he⟩ := hu
        have hy : Lface (u,0) ∈ d.sideArc '' Icc 0 α := hLclock ▸ mem_range_self u
        obtain ⟨w,hw,hew⟩ := hy
        have hm : Lface (u,0) ∈ range d.M.first := by
          rw [hfirst]
          exact ⟨w,⟨hw.1,hw.2.trans hαc.le⟩,hew⟩
        have ha : Lface (u,0) ∈ range a := d.M.first_on_a hm
        have hd : Lface (u,0) ∈ range d.e := (d.disk_a_trace.symm ▸ hm).1
        have hq : Lface (u,0) ∈ range q := ⟨d.xi v,he⟩
        have hcpoint : Lface (u,0) = d.M.first 1 := mem_singleton_iff.mp
          (d.clean_contact ▸ (show Lface (u,0) ∈ range d.e ∩ (range a ∩ range q) from ⟨hd,ha,hq⟩))
        have hwe : w = c := d.side_embedded.injective (hew.trans (hcpoint.trans hcside.symm))
        exact not_le_of_gt hαc (hwe ▸ hw.2)
      · intro u hu
        obtain ⟨v,hv,he⟩ := hu
        have hy : Rface (u,0) ∈ d.sideArc '' Icc β 1 := hRclock ▸ mem_range_self u
        obtain ⟨w,hw,hew⟩ := hy
        have hm : Rface (u,0) ∈ range d.M.second := by
          rw [hsecond]
          exact ⟨w,⟨hcβ.le.trans hw.1,hw.2⟩,hew⟩
        rw [d.second_trace] at hm
        obtain ⟨v0,hv0,he0⟩ := hm
        have hv0v : v0 = v := d.xi.injective (d.q_embedded.injective (he0.trans he.symm))
        have hvs : v = d.s := le_antisymm (hv0v ▸ hv0.2) hv
        have hcpoint : Rface (u,0) = d.M.first 1 := he.symm.trans
          ((congrArg (fun v => q (d.xi v)) hvs).trans d.q_corner)
        have hwe : w = c := d.side_embedded.injective (hew.trans (hcpoint.trans hcside.symm))
        exact not_le_of_gt hcβ (hwe ▸ hw.1)
      · intro u v he
        obtain ⟨w,hw,hew⟩ := hLclock ▸ mem_range_self u
        obtain ⟨z,hz,hez⟩ := hRclock ▸ mem_range_self v
        have hwz : w = z := d.side_embedded.injective (hew.trans (he.trans hez.symm))
        have hba : β ≤ α := (hwz.symm ▸ hz.1).trans hw.2
        exact not_le_of_gt (hαc.trans hcβ) hba
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `remaining_center_clear
      let some value := localDecl.value? | Lean.throwError "Missing local remaining_center_clear value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected remaining_center_clear axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS remaining_center_clear: {found.toList}"
    let remaining_band_clear : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ u v w z : Interval, (w:ℝ) ≤ δ → (z:ℝ) ≤ δ →
        Lface (u,w) ≠ Rface (v,z) ∧
        Lface (u,w) ∉ (fun a => q (d.xi a)) '' Ici d.s ∧
        Rface (v,z) ∉ (fun a => q (d.xi a)) '' Ici d.s := by
      let Future : Set ↥Q := (fun a => q (d.xi a)) '' Ici d.s
      have hFc : IsClosed Future := (isClosed_Ici.isCompact.image
        (q.continuous.comp d.xi.continuous)).isClosed
      let U : Set (↥Q × ↥Q) := {y | y.1 ≠ y.2 ∧ y.1 ∉ Future ∧ y.2 ∉ Future}
      have hU : IsOpen U := (isOpen_ne_fun continuous_fst continuous_snd).inter
        ((hFc.isOpen_compl.preimage continuous_fst).inter (hFc.isOpen_compl.preimage continuous_snd))
      let F : C((Interval × Interval) × (Interval × Interval),↥Q × ↥Q) :=
        ⟨fun z => (Lface (z.1.1,z.2.1),Rface (z.1.2,z.2.2)),by fun_prop⟩
      have hbase : (univ : Set (Interval × Interval)) ×ˢ ({(0,0)} : Set (Interval × Interval)) ⊆ F ⁻¹' U := by
        rintro ⟨⟨u,v⟩,w⟩ ⟨_,hw⟩
        obtain rfl := mem_singleton_iff.mp hw
        exact ⟨remaining_center_clear.2.2 u v,remaining_center_clear.1 u,remaining_center_clear.2.1 v⟩
      obtain ⟨A,V,hA,hV,hUA,h0V,hAV⟩ := generalized_tube_lemma
        isCompact_univ isCompact_singleton (hU.preimage F.continuous) hbase
      obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV (0,0) (h0V (mem_singleton _))
      let δ : ℝ := min (r/2) (1/2)
      have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
      have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
      have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
      refine ⟨δ,hδ,hδ1,?_⟩
      intro u v w z hw hz
      have hwidth : (w,z) ∈ V := by
        apply hrV
        rw [Metric.mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
        change max |(w:ℝ)-0| |(z:ℝ)-0| < r
        rw [sub_zero,sub_zero,abs_of_nonneg w.property.1,abs_of_nonneg z.property.1]
        exact (max_le hw hz).trans_lt hδr
      have hh : ((u,v),(w,z)) ∈ F ⁻¹' U := hAV ⟨hUA (mem_univ (u,v)),hwidth⟩
      exact hh
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `remaining_band_clear
      let some value := localDecl.value? | Lean.throwError "Missing local remaining_band_clear value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected remaining_band_clear axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS remaining_band_clear: {found.toList}"
    let narrowed_matched_pieces : ∃ Pc2 L2 R2 : C(Interval × Interval,↥Q),
      IsEmbedding Pc2 ∧ IsEmbedding L2 ∧ IsEmbedding R2 ∧
      range Pc2 ⊆ d.W ∧ range L2 ⊆ d.W ∧ range R2 ⊆ d.W ∧
      (∀ u, Pc2 (u,0) = P (u,0)) ∧
      (∀ u, L2 (u,0) = d.sideArc (Icc.convexComb 0 α u)) ∧
      (∀ u, R2 (u,0) = d.sideArc (Icc.convexComb β 1 u)) ∧
      (∀ z, Pc2 z ∈ range d.e ↔ z.2 = 0) ∧
      (∀ z, L2 z ∈ range d.e ↔ z.2 = 0) ∧
      (∀ z, R2 z ∈ range d.e ↔ z.2 = 0) ∧
      (∀ z, L2 z ∈ B ↔ z.1 = 0) ∧ (∀ z, R2 z ∈ B ↔ z.1 = 1) ∧
      (∀ w, L2 (1,w) = Pc2 (0,w)) ∧ (∀ w, R2 (0,w) = Pc2 (1,w)) ∧
      Disjoint (range L2) (range R2) ∧
      Disjoint (range L2) ((fun v => q (d.xi v)) '' Ici d.s) ∧
      Disjoint (range R2) ((fun v => q (d.xi v)) '' Ici d.s) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = δ*(z.2:ℝ) → Pc2 z = Pc (z.1,w)) ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = δ*(z.2:ℝ) → L2 z = Lface (z.1,w)) ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = δ*(z.2:ℝ) → R2 z = Rface (z.1,w)) := by
      obtain ⟨δ,hδ,hδ1,hband⟩ := remaining_band_clear
      let sh : C(Interval,Interval) := ⟨fun w => ⟨δ*(w:ℝ),by
        constructor <;> nlinarith [w.property.1,w.property.2,hδ,hδ1]⟩,by fun_prop⟩
      have hsh : IsEmbedding sh := by
        apply (sh.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply Subtype.ext
        exact mul_left_cancel₀ hδ.ne' (congrArg (fun w : Interval => (w:ℝ)) he)
      have hsh0 : sh 0 = 0 := by apply Subtype.ext; simp [sh]
      have hshz (w) : sh w = 0 ↔ w = 0 :=
        ⟨fun he => hsh.injective (he.trans hsh0.symm),fun he => he ▸ hsh0⟩
      have hshδ (w : Interval) : (sh w:ℝ) ≤ δ := by
        change δ*(w:ℝ) ≤ δ
        exact mul_le_of_le_one_right hδ.le w.property.2
      let sk := (ContinuousMap.id Interval).prodMap sh
      have hsk : IsEmbedding sk := IsEmbedding.id.prodMap hsh
      let Pc2 := Pc.comp sk
      let L2 := Lface.comp sk
      let R2 := Rface.comp sk
      have hPc2 : IsEmbedding Pc2 := hPc.comp hsk
      have hL2 : IsEmbedding L2 := hLface.comp hsk
      have hR2 : IsEmbedding R2 := hRface.comp hsk
      refine ⟨Pc2,L2,R2,hPc2,hL2,hR2,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,δ,hδ,hδ1,?_,?_,?_⟩
      · rintro y ⟨z,rfl⟩
        exact hPcW (mem_range_self (sk z))
      · rintro y ⟨z,rfl⟩
        exact hLfaceW (mem_range_self (sk z))
      · rintro y ⟨z,rfl⟩
        exact hRfaceW (mem_range_self (sk z))
      · intro u
        change Pc (u,sh 0) = _
        rw [hsh0,hPcseam]
      · intro u
        change Lface (u,sh 0) = _
        rw [hsh0,hLfaceseam]
      · intro u
        change Rface (u,sh 0) = _
        rw [hsh0,hRfaceseam]
      · intro z
        change Pc (z.1,sh z.2) ∈ range d.e ↔ _
        rw [hPcdisk,hshz]
      · intro z
        change Lface (z.1,sh z.2) ∈ range d.e ↔ _
        rw [hLdisk,hshz]
      · intro z
        change Rface (z.1,sh z.2) ∈ range d.e ↔ _
        rw [hRdisk,hshz]
      · intro z
        exact hLfaceB (sk z)
      · intro z
        exact hRfaceB (sk z)
      · intro w
        exact hleftmatch (sh w)
      · intro w
        exact hrightmatch (sh w)
      · apply disjoint_left.mpr
        rintro y ⟨u,rfl⟩ ⟨v,he⟩
        exact (hband u.1 v.1 (sh u.2) (sh v.2) (hshδ _) (hshδ _)).1 he.symm
      · apply disjoint_left.mpr
        rintro y ⟨u,rfl⟩ hy
        exact (hband u.1 0 (sh u.2) 0 (hshδ _) hδ.le).2.1 hy
      · apply disjoint_left.mpr
        rintro y ⟨v,rfl⟩ hy
        exact (hband 0 v.1 0 (sh v.2) hδ.le (hshδ _)).2.2 hy
      · intro z w hw
        change Pc (z.1,sh z.2) = _
        apply congrArg Pc
        exact Prod.ext rfl (Subtype.ext hw.symm)
      · intro z w hw
        change Lface (z.1,sh z.2) = _
        apply congrArg Lface
        exact Prod.ext rfl (Subtype.ext hw.symm)
      · intro z w hw
        change Rface (z.1,sh z.2) = _
        apply congrArg Rface
        exact Prod.ext rfl (Subtype.ext hw.symm)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `narrowed_matched_pieces
      let some value := localDecl.value? | Lean.throwError "Missing local narrowed_matched_pieces value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected narrowed_matched_pieces axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS narrowed_matched_pieces: {found.toList}"
    obtain ⟨Pseed,Lseed,Rseed,hPseed,hLseed,hRseed,hPseedW,hLseedW,hRseedW,
      hPseedseam,hLseedseam,hRseedseam,hPseeddisk,hLseeddisk,hRseeddisk,hLseedB,hRseedB,
      hLseedface,hRseedface,hLRclear,hLseedfuture,hRseedfuture,
      seedFactor,hSeedFactor,hSeedFactor1,hPseedform,hLseedform,hRseedform⟩ := narrowed_matched_pieces
    let seedκP : ℝ := (faceWidth/eps)*seedFactor
    let seedκL : ℝ := (faceWidth/lamL)*seedFactor
    let seedκR : ℝ := (faceWidth/lamR)*seedFactor
    have hseedκP : 0 < seedκP ∧ seedκP ≤ 1 := by
      have hr : 0 < faceWidth/eps := div_pos hfaceWidth heps
      have hr1 : faceWidth/eps ≤ 1 := (div_le_one heps).mpr hfaceP
      exact ⟨mul_pos hr hSeedFactor,by dsimp [seedκP]; nlinarith only [hr.le,hr1,hSeedFactor.le,hSeedFactor1]⟩
    have hseedκL : 0 < seedκL ∧ seedκL ≤ 1 := by
      have hr : 0 < faceWidth/lamL := div_pos hfaceWidth hlamL
      have hr1 : faceWidth/lamL ≤ 1 := (div_le_one hlamL).mpr hfaceL
      exact ⟨mul_pos hr hSeedFactor,by dsimp [seedκL]; nlinarith only [hr.le,hr1,hSeedFactor.le,hSeedFactor1]⟩
    have hseedκR : 0 < seedκR ∧ seedκR ≤ 1 := by
      have hr : 0 < faceWidth/lamR := div_pos hfaceWidth hlamR
      have hr1 : faceWidth/lamR ≤ 1 := (div_le_one hlamR).mpr hfaceR
      exact ⟨mul_pos hr hSeedFactor,by dsimp [seedκR]; nlinarith only [hr.le,hr1,hSeedFactor.le,hSeedFactor1]⟩
    let seed_width_formulas :
      (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = seedκP*(z.2:ℝ) → Pseed z = P (z.1,w)) ∧
      (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = seedκL*(z.2:ℝ) →
        Lseed z = HL (Icc.convexComb 0 α z.1,w)) ∧
      (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = seedκR*(z.2:ℝ) →
        Rseed z = HR (Icc.convexComb β 1 z.1,w)) := by
      constructor
      · intro z w hw
        let w0 : Interval := ⟨seedFactor*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hSeedFactor,hSeedFactor1]⟩
        exact (hPseedform z w0 rfl).trans (hPcform (z.1,w0) w (hw.trans (by dsimp [seedκP,w0]; ring)))
      constructor
      · intro z w hw
        let w0 : Interval := ⟨seedFactor*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hSeedFactor,hSeedFactor1]⟩
        exact (hLseedform z w0 rfl).trans (hLfaceform (z.1,w0) w (hw.trans (by dsimp [seedκL,w0]; ring)))
      · intro z w hw
        let w0 : Interval := ⟨seedFactor*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hSeedFactor,hSeedFactor1]⟩
        exact (hRseedform z w0 rfl).trans (hRfaceform (z.1,w0) w (hw.trans (by dsimp [seedκR,w0]; ring)))
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `seed_width_formulas
      let some value := localDecl.value? | Lean.throwError "Missing local seed_width_formulas value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected seed_width_formulas axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS seed_width_formulas: {found.toList}"
    have hPseed_box (z : Interval × Interval) :
        d.sigma*d.cornerChart (Pseed z).val 0 ≤ A ∧ d.tau*d.cornerChart (Pseed z).val 1 ≤ A := by
      let w : Interval := ⟨seedκP*(z.2:ℝ),by
        constructor <;> nlinarith [z.2.property.1,z.2.property.2,hseedκP.1,hseedκP.2]⟩
      rw [seed_width_formulas.1 z w rfl]
      exact ⟨(hPbox (z.1,w)).2.1,(hPbox (z.1,w)).2.2.2.1⟩
    let near_patch_contact :
      (∀ z v : Interval × Interval, |(Icc.convexComb 0 α z.1:ℝ)-(α:ℝ)| < ηL →
        (Lseed z = Pseed v ↔ z.1 = 1 ∧ v = (0,z.2))) ∧
      (∀ z v : Interval × Interval, |(Icc.convexComb β 1 z.1:ℝ)-(β:ℝ)| < ηR →
        (Rseed z = Pseed v ↔ z.1 = 0 ∧ v = (1,z.2))) := by
      constructor
      · intro z v hnear
        constructor
        · intro he
          let w : Interval := ⟨seedκL*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hseedκL.1,hseedκL.2]⟩
          have hform := seed_width_formulas.2.1 z w rfl
          have hcal := hHLcal (Icc.convexComb 0 α z.1) w hnear
          have hx : d.cornerChart (Lseed z).val 0 =
              d.cornerChart (d.sideArc (Icc.convexComb 0 α z.1)).val 0 := by
            rw [hform]
            simpa [Plane.mk] using congrArg (fun p : Plane => p 0) hcal.2.1
          have hxle : d.sigma*d.cornerChart (d.sideArc (Icc.convexComb 0 α z.1)).val 0 ≤ A := by
            rw [← hx,he]
            exact (hPseed_box v).1
          have horder := near_port_side_orders.1 (Icc.convexComb 0 α z.1)
            (Icc.convexComb_le hα0.le _) hnear
          have ht := horder.2 (le_antisymm hxle horder.1)
          have hparam : z.1 = 1 := by
            apply Subtype.ext
            have hval := congrArg (fun x : Interval => (x:ℝ)) ht
            simp only [Icc.coe_convexComb,Icc.coe_zero] at hval
            have ha : (0:ℝ) < α := hα0
            change (z.1:ℝ) = 1
            nlinarith only [hval,ha]
          refine ⟨hparam,?_⟩
          have hz : z = (1,z.2) := Prod.ext hparam rfl
          apply (hPseed.injective ?_).symm
          rw [← hLseedface,← hz]
          exact he
        · rintro ⟨hz,rfl⟩
          rw [show z = (1,z.2) from Prod.ext hz rfl]
          exact hLseedface z.2
      · intro z v hnear
        constructor
        · intro he
          let w : Interval := ⟨seedκR*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hseedκR.1,hseedκR.2]⟩
          have hform := seed_width_formulas.2.2 z w rfl
          have hcal := hHRcal (Icc.convexComb β 1 z.1) w hnear
          have hx : d.cornerChart (Rseed z).val 1 =
              d.cornerChart (d.sideArc (Icc.convexComb β 1 z.1)).val 1 := by
            rw [hform]
            simpa [Plane.mk] using congrArg (fun p : Plane => p 1) hcal.2.1
          have hxle : d.tau*d.cornerChart (d.sideArc (Icc.convexComb β 1 z.1)).val 1 ≤ A := by
            rw [← hx,he]
            exact (hPseed_box v).2
          have horder := near_port_side_orders.2 (Icc.convexComb β 1 z.1)
            (Icc.le_convexComb hβ1.le _) hnear
          have ht := horder.2 (le_antisymm hxle horder.1)
          have hparam : z.1 = 0 := by
            apply Subtype.ext
            have hval := congrArg (fun x : Interval => (x:ℝ)) ht
            simp only [Icc.coe_convexComb,Icc.coe_one] at hval
            have hb : (β:ℝ) < 1 := hβ1
            change (z.1:ℝ) = 0
            nlinarith only [hval,hb]
          refine ⟨hparam,?_⟩
          have hz : z = (0,z.2) := Prod.ext hparam rfl
          apply (hPseed.injective ?_).symm
          rw [← hRseedface,← hz]
          exact he
        · rintro ⟨hz,rfl⟩
          rw [show z = (0,z.2) from Prod.ext hz rfl]
          exact hRseedface z.2
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `near_patch_contact
      let some value := localDecl.value? | Lean.throwError "Missing local near_patch_contact value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected near_patch_contact axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS near_patch_contact: {found.toList}"
    let half_tube_bound : ∀ (M : C(Interval × Interval,↥Q)) (K : Set Interval), IsCompact K →
      ∀ U : Set ↥Q, IsOpen U → (∀ u ∈ K, M (u,0) ∈ U) →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
          ∀ z : Interval × Interval, z.1 ∈ K → (z.2:ℝ) ≤ δ → M z ∈ U := by
      intro M K hK U hU hcenter
      have hbase : K ×ˢ ({0} : Set Interval) ⊆ M ⁻¹' U := by
        rintro ⟨u,w⟩ ⟨hu,hw⟩
        obtain rfl := mem_singleton_iff.mp hw
        exact hcenter u hu
      obtain ⟨A,V,hA,hV,hKA,h0V,hAV⟩ := generalized_tube_lemma
        hK isCompact_singleton (hU.preimage M.continuous) hbase
      obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV 0 (h0V (mem_singleton _))
      let δ : ℝ := min (r/2) (1/2)
      have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
      have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
      have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
      refine ⟨δ,hδ,hδ1,?_⟩
      intro z hz hw
      have hwidth : z.2 ∈ V := by
        apply hrV
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |(z.2:ℝ)-0| < r
        rw [sub_zero,abs_of_nonneg z.2.property.1]
        exact hw.trans_lt hδr
      exact (show z ∈ M ⁻¹' U from hAV ⟨hKA hz,hwidth⟩)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `half_tube_bound
      let some value := localDecl.value? | Lean.throwError "Missing local half_tube_bound value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected half_tube_bound axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS half_tube_bound: {found.toList}"
    let far_patch_avoidance : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ z : Interval × Interval, ¬ |(Icc.convexComb 0 α z.1:ℝ)-(α:ℝ)| < ηL →
        (z.2:ℝ) ≤ δ → Lseed z ∉ range P) ∧
      (∀ z : Interval × Interval, ¬ |(Icc.convexComb β 1 z.1:ℝ)-(β:ℝ)| < ηR →
        (z.2:ℝ) ≤ δ → Rseed z ∉ range P) := by
      let KL : Set Interval := {u | ηL ≤ |(Icc.convexComb 0 α u:ℝ)-(α:ℝ)|}
      let KR : Set Interval := {u | ηR ≤ |(Icc.convexComb β 1 u:ℝ)-(β:ℝ)|}
      have hKL : IsCompact KL := by
        apply IsClosed.isCompact
        dsimp [KL]
        exact isClosed_le continuous_const (by fun_prop)
      have hKR : IsCompact KR := by
        apply IsClosed.isCompact
        dsimp [KR]
        exact isClosed_le continuous_const (by fun_prop)
      have hU : IsOpen (range P)ᶜ := (isCompact_range P.continuous).isClosed.isOpen_compl
      have hLC (u : Interval) (hu : u ∈ KL) : Lseed (u,0) ∉ range P := by
        rintro ⟨v,hv⟩
        have hPD : P v ∈ range d.e := by rw [hv]; exact (hLseeddisk (u,0)).mpr rfl
        have hv0 : v.2 = 0 := (hPe v).mp hPD
        have hpv : (v.1,(0 : Interval)) = v := Prod.ext rfl hv0.symm
        have hmid : Lseed (u,0) ∈ d.sideArc '' Icc α β := hPclock ▸
          (show Lseed (u,0) ∈ range (fun v : Interval => P (v,0)) from
            ⟨v.1,(congrArg P hpv).trans hv⟩)
        obtain ⟨w,hw,he⟩ := hmid
        have hwt := d.side_embedded.injective (he.trans (hLseedseam u))
        have ht : Icc.convexComb 0 α u = α := le_antisymm
          (Icc.convexComb_le hα0.le u) (hwt ▸ hw.1)
        change ηL ≤ |(Icc.convexComb 0 α u:ℝ)-(α:ℝ)| at hu
        rw [ht,sub_self,abs_zero] at hu
        exact not_le_of_gt hηL hu
      have hRC (u : Interval) (hu : u ∈ KR) : Rseed (u,0) ∉ range P := by
        rintro ⟨v,hv⟩
        have hPD : P v ∈ range d.e := by rw [hv]; exact (hRseeddisk (u,0)).mpr rfl
        have hv0 : v.2 = 0 := (hPe v).mp hPD
        have hpv : (v.1,(0 : Interval)) = v := Prod.ext rfl hv0.symm
        have hmid : Rseed (u,0) ∈ d.sideArc '' Icc α β := hPclock ▸
          (show Rseed (u,0) ∈ range (fun v : Interval => P (v,0)) from
            ⟨v.1,(congrArg P hpv).trans hv⟩)
        obtain ⟨w,hw,he⟩ := hmid
        have hwt := d.side_embedded.injective (he.trans (hRseedseam u))
        have ht : Icc.convexComb β 1 u = β := le_antisymm
          (hwt ▸ hw.2) (Icc.le_convexComb hβ1.le u)
        change ηR ≤ |(Icc.convexComb β 1 u:ℝ)-(β:ℝ)| at hu
        rw [ht,sub_self,abs_zero] at hu
        exact not_le_of_gt hηR hu
      obtain ⟨δL,hδL,hδL1,hLcap⟩ := half_tube_bound Lseed KL hKL (range P)ᶜ hU hLC
      obtain ⟨δR,hδR,hδR1,hRcap⟩ := half_tube_bound Rseed KR hKR (range P)ᶜ hU hRC
      let δ : ℝ := min δL δR/2
      have hm : 0 < min δL δR := lt_min hδL hδR
      have hδLle : δ ≤ δL := (half_lt_self hm).le.trans (min_le_left _ _)
      have hδRle : δ ≤ δR := (half_lt_self hm).le.trans (min_le_right _ _)
      refine ⟨δ,half_pos hm,hδLle.trans hδL1,?_,?_⟩
      · intro z hz hw
        exact hLcap z (le_of_not_gt hz) (hw.trans hδLle)
      · intro z hz hw
        exact hRcap z (le_of_not_gt hz) (hw.trans hδRle)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `far_patch_avoidance
      let some value := localDecl.value? | Lean.throwError "Missing local far_patch_avoidance value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected far_patch_avoidance axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS far_patch_avoidance: {found.toList}"
    let exact_three_pieces : ∃ P3 L3 R3 : C(Interval × Interval,↥Q),
      IsEmbedding P3 ∧ IsEmbedding L3 ∧ IsEmbedding R3 ∧
      range P3 ⊆ d.W ∧ range L3 ⊆ d.W ∧ range R3 ⊆ d.W ∧
      (∀ u, P3 (u,0) = P (u,0)) ∧
      (∀ u, L3 (u,0) = d.sideArc (Icc.convexComb 0 α u)) ∧
      (∀ u, R3 (u,0) = d.sideArc (Icc.convexComb β 1 u)) ∧
      (∀ z, P3 z ∈ range d.e ↔ z.2 = 0) ∧
      (∀ z, L3 z ∈ range d.e ↔ z.2 = 0) ∧
      (∀ z, R3 z ∈ range d.e ↔ z.2 = 0) ∧
      (∀ z, L3 z ∈ B ↔ z.1 = 0) ∧ (∀ z, R3 z ∈ B ↔ z.1 = 1) ∧
      (∀ w, L3 (1,w) = P3 (0,w)) ∧ (∀ w, R3 (0,w) = P3 (1,w)) ∧
      Disjoint (range L3) (range R3) ∧
      Disjoint (range L3) ((fun v => q (d.xi v)) '' Ici d.s) ∧
      Disjoint (range R3) ((fun v => q (d.xi v)) '' Ici d.s) ∧
      (∀ z v : Interval × Interval, L3 z = P3 v ↔ z.1 = 1 ∧ v = (0,z.2)) ∧
      (∀ z v : Interval × Interval, R3 z = P3 v ↔ z.1 = 0 ∧ v = (1,z.2)) ∧
      ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = θ*(z.2:ℝ) → P3 z = Pseed (z.1,w)) ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = θ*(z.2:ℝ) → L3 z = Lseed (z.1,w)) ∧
        (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = θ*(z.2:ℝ) → R3 z = Rseed (z.1,w)) := by
      obtain ⟨θ,hθ,hθ1,hLcap,hRcap⟩ := far_patch_avoidance
      let sh : C(Interval,Interval) := ⟨fun w => ⟨θ*(w:ℝ),by
        constructor <;> nlinarith [w.property.1,w.property.2,hθ,hθ1]⟩,by fun_prop⟩
      have hsh : IsEmbedding sh := by
        apply (sh.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply Subtype.ext
        exact mul_left_cancel₀ hθ.ne' (congrArg (fun w : Interval => (w:ℝ)) he)
      have hsh0 : sh 0 = 0 := by apply Subtype.ext; simp [sh]
      have hshz (w) : sh w = 0 ↔ w = 0 :=
        ⟨fun he => hsh.injective (he.trans hsh0.symm),fun he => he ▸ hsh0⟩
      have hshθ (w : Interval) : (sh w:ℝ) ≤ θ := by
        change θ*(w:ℝ) ≤ θ
        exact mul_le_of_le_one_right hθ.le w.property.2
      let sk := (ContinuousMap.id Interval).prodMap sh
      have hsk : IsEmbedding sk := IsEmbedding.id.prodMap hsh
      let P3 := Pseed.comp sk
      let L3 := Lseed.comp sk
      let R3 := Rseed.comp sk
      have hP3 : IsEmbedding P3 := hPseed.comp hsk
      have hL3 : IsEmbedding L3 := hLseed.comp hsk
      have hR3 : IsEmbedding R3 := hRseed.comp hsk
      have hLP3 (w) : L3 (1,w) = P3 (0,w) := hLseedface (sh w)
      have hRP3 (w) : R3 (0,w) = P3 (1,w) := hRseedface (sh w)
      have hPP : range Pseed ⊆ range P := by
        rintro y ⟨z,rfl⟩
        let w : Interval := ⟨seedκP*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hseedκP.1,hseedκP.2]⟩
        exact ⟨(z.1,w),(seed_width_formulas.1 z w rfl).symm⟩
      have hLP (z v : Interval × Interval) : L3 z = P3 v ↔ z.1 = 1 ∧ v = (0,z.2) := by
        constructor
        · intro he
          by_cases hn : |(Icc.convexComb 0 α z.1:ℝ)-(α:ℝ)| < ηL
          · have hh := (near_patch_contact.1 (sk z) (sk v) hn).mp he
            refine ⟨hh.1,Prod.ext ?_ ?_⟩
            · have hh1 : (sk v).1 = 0 := congrArg (fun p : Interval × Interval => p.1) hh.2
              exact hh1
            · exact hsh.injective (congrArg Prod.snd hh.2)
          · exact False.elim ((hLcap (sk z) hn (hshθ z.2)) (hPP ⟨sk v,he.symm⟩))
        · rintro ⟨hz,rfl⟩
          rw [show z = (1,z.2) from Prod.ext hz rfl]
          exact hLP3 z.2
      have hRP (z v : Interval × Interval) : R3 z = P3 v ↔ z.1 = 0 ∧ v = (1,z.2) := by
        constructor
        · intro he
          by_cases hn : |(Icc.convexComb β 1 z.1:ℝ)-(β:ℝ)| < ηR
          · have hh := (near_patch_contact.2 (sk z) (sk v) hn).mp he
            refine ⟨hh.1,Prod.ext ?_ ?_⟩
            · have hh1 : (sk v).1 = 1 := congrArg (fun p : Interval × Interval => p.1) hh.2
              exact hh1
            · exact hsh.injective (congrArg Prod.snd hh.2)
          · exact False.elim ((hRcap (sk z) hn (hshθ z.2)) (hPP ⟨sk v,he.symm⟩))
        · rintro ⟨hz,rfl⟩
          rw [show z = (0,z.2) from Prod.ext hz rfl]
          exact hRP3 z.2
      refine ⟨P3,L3,R3,hP3,hL3,hR3,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hLP3,hRP3,
        ?_,?_,?_,hLP,hRP,θ,hθ,hθ1,?_,?_,?_⟩
      · rintro y ⟨z,rfl⟩
        exact hPseedW (mem_range_self (sk z))
      · rintro y ⟨z,rfl⟩
        exact hLseedW (mem_range_self (sk z))
      · rintro y ⟨z,rfl⟩
        exact hRseedW (mem_range_self (sk z))
      · intro u
        change Pseed (u,sh 0) = _
        rw [hsh0,hPseedseam]
      · intro u
        change Lseed (u,sh 0) = _
        rw [hsh0,hLseedseam]
      · intro u
        change Rseed (u,sh 0) = _
        rw [hsh0,hRseedseam]
      · intro z
        change Pseed (z.1,sh z.2) ∈ range d.e ↔ _
        rw [hPseeddisk,hshz]
      · intro z
        change Lseed (z.1,sh z.2) ∈ range d.e ↔ _
        rw [hLseeddisk,hshz]
      · intro z
        change Rseed (z.1,sh z.2) ∈ range d.e ↔ _
        rw [hRseeddisk,hshz]
      · intro z
        exact hLseedB (sk z)
      · intro z
        exact hRseedB (sk z)
      · exact hLRclear.mono (by rintro y ⟨z,rfl⟩; exact mem_range_self (sk z))
          (by rintro y ⟨z,rfl⟩; exact mem_range_self (sk z))
      · exact hLseedfuture.mono_left (by rintro y ⟨z,rfl⟩; exact mem_range_self (sk z))
      · exact hRseedfuture.mono_left (by rintro y ⟨z,rfl⟩; exact mem_range_self (sk z))
      · intro z w hw
        change Pseed (z.1,sh z.2) = _
        exact congrArg Pseed (Prod.ext rfl (Subtype.ext hw.symm))
      · intro z w hw
        change Lseed (z.1,sh z.2) = _
        exact congrArg Lseed (Prod.ext rfl (Subtype.ext hw.symm))
      · intro z w hw
        change Rseed (z.1,sh z.2) = _
        exact congrArg Rseed (Prod.ext rfl (Subtype.ext hw.symm))
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `exact_three_pieces
      let some value := localDecl.value? | Lean.throwError "Missing local exact_three_pieces value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected exact_three_pieces axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS exact_three_pieces: {found.toList}"
    obtain ⟨P3,L3,R3,hP3,hL3,hR3,hP3W,hL3W,hR3W,hP3seam,hL3seam,hR3seam,
      hP3disk,hL3disk,hR3disk,hL3B,hR3B,hL3face,hR3face,hL3R3,hL3future,hR3future,
      hL3P3,hR3P3,patchFactor,hPatchFactor,hPatchFactor1,hP3form,hL3form,hR3form⟩ := exact_three_pieces
    let glued_seed_strip : ∃ T : C(Interval × Interval,↥Q), IsEmbedding T ∧
      range T = range L3 ∪ range P3 ∪ range R3 ∧
      (∀ w, T (0,w) = L3 (0,w)) ∧ (∀ w, T (1,w) = R3 (1,w)) ∧
      ∀ z, ∃ u : Interval,
        T z = L3 (u,z.2) ∨ T z = P3 (u,z.2) ∨ T z = R3 (u,z.2) := by
      let flip := unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl Interval)
      let LF : C(Interval × Interval,↥Q) := ⟨L3 ∘ flip,L3.continuous.comp flip.continuous⟩
      have hLF : IsEmbedding LF := hL3.comp flip.isEmbedding
      have hLFrange : range LF = range L3 := by
        ext y
        constructor
        · rintro ⟨z,rfl⟩
          exact ⟨flip z,rfl⟩
        · rintro ⟨z,rfl⟩
          exact ⟨flip.symm z,by simp [LF]⟩
      have hLFgate (w) : LF (0,w) = P3 (0,w) := by
        change L3 (unitInterval.symm 0,w) = _
        rw [unitInterval.symm_zero,hL3face]
      have hLFmeet : range LF ∩ range P3 = range (fun w => LF (0,w)) := by
        ext y
        constructor
        · rintro ⟨⟨z,hz⟩,⟨v,hv⟩⟩
          have hh := (hL3P3 (flip z) v).mp (hz.trans hv.symm)
          refine ⟨z.2,?_⟩
          change L3 (unitInterval.symm 0,z.2) = y
          rw [unitInterval.symm_zero]
          have he : (1,z.2) = flip z := Prod.ext hh.1.symm rfl
          exact (congrArg L3 he).trans hz
        · rintro ⟨w,rfl⟩
          exact ⟨mem_range_self _,⟨(0,w),(hLFgate w).symm⟩⟩
      obtain ⟨F,hF,hF0,hF1,hFm,hFrange,hFrow⟩ :=
        source_glue_two_surface_strips LF P3 hLF hP3 hLFgate hLFmeet
      let FC : C(Interval × Interval,↥Q) := ⟨F,hF.continuous⟩
      have hFCrange : range FC = range L3 ∪ range P3 := by
        exact hFrange.trans (congrArg (fun U : Set ↥Q => U ∪ range P3) hLFrange)
      have hFC0 (w) : FC (0,w) = L3 (0,w) := by
        rw [show FC (0,w) = LF (1,w) from hF0 w]
        change L3 (unitInterval.symm 1,w) = _
        rw [unitInterval.symm_one]
      have hFCrow (z) : ∃ u : Interval, FC z = L3 (u,z.2) ∨ FC z = P3 (u,z.2) := by
        obtain ⟨u,hu | hu⟩ := hFrow z
        · exact ⟨unitInterval.symm u,Or.inl hu⟩
        · exact ⟨u,Or.inr hu⟩
      let FF : C(Interval × Interval,↥Q) := ⟨FC ∘ flip,FC.continuous.comp flip.continuous⟩
      have hFF : IsEmbedding FF := hF.comp flip.isEmbedding
      have hFFrange : range FF = range FC := by
        ext y
        constructor
        · rintro ⟨z,rfl⟩
          exact ⟨flip z,rfl⟩
        · rintro ⟨z,rfl⟩
          exact ⟨flip.symm z,by simp [FF]⟩
      have hFFgate (w) : FF (0,w) = R3 (0,w) := by
        change FC (unitInterval.symm 0,w) = _
        rw [unitInterval.symm_zero]
        exact (hF1 w).trans (hR3face w).symm
      have hFFmeet : range FF ∩ range R3 = range (fun w => FF (0,w)) := by
        ext y
        constructor
        · rintro ⟨hfy,⟨z,hz⟩⟩
          rw [hFFrange,hFCrange] at hfy
          rcases hfy with hly | ⟨v,hv⟩
          · exact False.elim (Set.disjoint_left.mp hL3R3 hly ⟨z,hz⟩)
          · have hh := (hR3P3 z v).mp (hz.trans hv.symm)
            refine ⟨z.2,?_⟩
            change FF (0,z.2) = y
            rw [hFFgate]
            exact (congrArg R3 (show (0,z.2) = z from Prod.ext hh.1.symm rfl)).trans hz
        · rintro ⟨w,rfl⟩
          exact ⟨mem_range_self _,⟨(0,w),(hFFgate w).symm⟩⟩
      obtain ⟨T,hT,hT0,hT1,hTm,hTrange,hTrow⟩ :=
        source_glue_two_surface_strips FF R3 hFF hR3 hFFgate hFFmeet
      refine ⟨⟨T,hT.continuous⟩,hT,?_,?_,hT1,?_⟩
      · change range T = range L3 ∪ range P3 ∪ range R3
        rw [hTrange,hFFrange,hFCrange]
      · intro w
        change T (0,w) = L3 (0,w)
        rw [hT0]
        change FC (unitInterval.symm 1,w) = _
        rw [unitInterval.symm_one,hFC0]
      · intro z
        obtain ⟨u,hu | hu⟩ := hTrow z
        · obtain ⟨v,hv | hv⟩ := hFCrow (flip (u,z.2))
          · exact ⟨v,Or.inl (hu.trans hv)⟩
          · exact ⟨v,Or.inr (Or.inl (hu.trans hv))⟩
        · exact ⟨u,Or.inr (Or.inr hu)⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `glued_seed_strip
      let some value := localDecl.value? | Lean.throwError "Missing local glued_seed_strip value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected glued_seed_strip axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS glued_seed_strip: {found.toList}"
    obtain ⟨Tseed,hTseed,hTseedrange,hTseed0,hTseed1,hTseedrow⟩ := glued_seed_strip
    have hseed_seam_union : range (fun u : Interval => Lseed (u,0)) ∪
        range (fun u : Interval => Pseed (u,0)) ∪ range (fun u : Interval => Rseed (u,0)) =
        range d.sideArc := by
      rw [show (fun u : Interval => Lseed (u,0)) = (fun u => Lface (u,0)) from
        funext (fun u => (hLseedseam u).trans (hLfaceseam u).symm),
        show (fun u : Interval => Pseed (u,0)) = (fun u => Pc (u,0)) from
        funext (fun u => (hPseedseam u).trans (hPcseam u).symm),
        show (fun u : Interval => Rseed (u,0)) = (fun u => Rface (u,0)) from
        funext (fun u => (hRseedseam u).trans (hRfaceseam u).symm)]
      exact hseam_union
    let whole_seed_collar : ∃ Hseed : C(Interval × Interval,↥Q), IsEmbedding Hseed ∧
      (∀ u, Hseed (u,0) = d.sideArc u) ∧
      (∀ z, Hseed z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
      range Hseed ⊆ d.W ∧ (∀ z, Hseed z ∈ range d.e ↔ z.2 = 0) ∧
      range Hseed = range L3 ∪ range P3 ∪ range R3 ∧
      ∀ z, ∃ u : Interval, Hseed z = L3 (u,z.2) ∨ Hseed z = P3 (u,z.2) ∨ Hseed z = R3 (u,z.2) := by
      have hP3P : range P3 ⊆ range P := by
        rintro y ⟨z,rfl⟩
        let w : Interval := ⟨patchFactor*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hPatchFactor,hPatchFactor1]⟩
        let v : Interval := ⟨seedκP*(w:ℝ),by
          constructor <;> nlinarith [w.property.1,w.property.2,hseedκP.1,hseedκP.2]⟩
        refine ⟨(z.1,v),?_⟩
        exact ((hP3form z w rfl).trans (seed_width_formulas.1 (z.1,w) v rfl)).symm
      have hTW : range Tseed ⊆ d.W := by
        rw [hTseedrange]
        exact union_subset (union_subset hL3W hP3W) hR3W
      have hTD (z) : Tseed z ∈ range d.e ↔ z.2 = 0 := by
        obtain ⟨u,hu | hu | hu⟩ := hTseedrow z
        · rw [hu,hL3disk]
        · rw [hu,hP3disk]
        · rw [hu,hR3disk]
      have hTB (z) : Tseed z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
        constructor
        · intro hz
          obtain ⟨u,hu | hu | hu⟩ := hTseedrow z
          · have hu0 : u = 0 := (hL3B (u,z.2)).mp (hu ▸ hz)
            have he : Tseed z = Tseed (0,z.2) := by rw [hu,hu0,hTseed0]
            exact Or.inl (congrArg Prod.fst (hTseed.injective he))
          · exact False.elim (hPB (Classical.choose (hP3P (mem_range_self (u,z.2))))
              ((Classical.choose_spec (hP3P (mem_range_self (u,z.2)))).symm ▸ (hu ▸ hz)))
          · have hu1 : u = 1 := (hR3B (u,z.2)).mp (hu ▸ hz)
            have he : Tseed z = Tseed (1,z.2) := by rw [hu,hu1,hTseed1]
            exact Or.inr (congrArg Prod.fst (hTseed.injective he))
        · rintro (hz | hz)
          · rw [show z = (0,z.2) from Prod.ext hz rfl,hTseed0]
            exact (hL3B (0,z.2)).mpr rfl
          · rw [show z = (1,z.2) from Prod.ext hz rfl,hTseed1]
            exact (hR3B (1,z.2)).mpr rfl
      let f : C(Interval,↥Q) := ⟨fun u => Tseed (u,0),by fun_prop⟩
      have hf : IsEmbedding f := hTseed.comp
        ((show Continuous (fun u : Interval => (u,(0:Interval))) from by fun_prop).isClosedEmbedding
          (fun u v he => congrArg Prod.fst he)).isEmbedding
      have hpiece_seams : range (fun u : Interval => L3 (u,0)) ∪
          range (fun u : Interval => P3 (u,0)) ∪ range (fun u : Interval => R3 (u,0)) =
          range d.sideArc := by
        rw [show (fun u : Interval => L3 (u,0)) = (fun u => Lseed (u,0)) from
          funext (fun u => (hL3seam u).trans (hLseedseam u).symm),
          show (fun u : Interval => P3 (u,0)) = (fun u => Pseed (u,0)) from
          funext (fun u => (hP3seam u).trans (hPseedseam u).symm),
          show (fun u : Interval => R3 (u,0)) = (fun u => Rseed (u,0)) from
          funext (fun u => (hR3seam u).trans (hRseedseam u).symm)]
        exact hseed_seam_union
      have hfrange : range f = range d.sideArc := by
        rw [← hpiece_seams]
        ext y
        constructor
        · rintro ⟨u,rfl⟩
          obtain ⟨v,hv | hv | hv⟩ := hTseedrow (u,0)
          · exact Or.inl (Or.inl ⟨v,hv.symm⟩)
          · exact Or.inl (Or.inr ⟨v,hv.symm⟩)
          · exact Or.inr ⟨v,hv.symm⟩
        · intro hy
          have ht : y ∈ range Tseed := by
            rw [hTseedrange]
            rcases hy with (⟨u,rfl⟩ | ⟨u,rfl⟩) | ⟨u,rfl⟩
            · exact Or.inl (Or.inl (mem_range_self (u,0)))
            · exact Or.inl (Or.inr (mem_range_self (u,0)))
            · exact Or.inr (mem_range_self (u,0))
          have hd : y ∈ range d.e := by
            rcases hy with (⟨u,rfl⟩ | ⟨u,rfl⟩) | ⟨u,rfl⟩
            · exact (hL3disk (u,0)).mpr rfl
            · exact (hP3disk (u,0)).mpr rfl
            · exact (hR3disk (u,0)).mpr rfl
          obtain ⟨z,hz⟩ := ht
          have hz0 : z.2 = 0 := (hTD z).mp (hz.symm ▸ hd)
          exact ⟨z.1,(congrArg Tseed (show (z.1,(0:Interval)) = z from Prod.ext rfl hz0.symm)).trans hz⟩
      let clk : Interval ≃ₜ Interval := hf.toHomeomorph.trans
        ((Homeomorph.setCongr hfrange).trans d.side_embedded.toHomeomorph.symm)
      have hclk (u) : Tseed (u,0) = d.sideArc (clk u) := by
        have hh := d.side_embedded.toHomeomorph.apply_symm_apply
          ((Homeomorph.setCongr hfrange) (hf.toHomeomorph u))
        exact (congrArg (fun v : range d.sideArc => (v:↥Q)) hh).symm
      have hclk0 : clk 0 = 0 := by
        apply d.side_embedded.injective
        exact (hclk 0).symm.trans ((hTseed0 0).trans
          ((hL3seam 0).trans (congrArg d.sideArc (Icc.convexComb_zero 0 α))))
      have hclk1 : clk 1 = 1 := by
        apply d.side_embedded.injective
        exact (hclk 1).symm.trans ((hTseed1 0).trans
          ((hR3seam 1).trans (congrArg d.sideArc (Icc.convexComb_one β 1))))
      have hci0 : clk.symm 0 = 0 := clk.injective ((clk.apply_symm_apply 0).trans hclk0.symm)
      have hci1 : clk.symm 1 = 1 := clk.injective ((clk.apply_symm_apply 1).trans hclk1.symm)
      let changeClock := clk.symm.prodCongr (Homeomorph.refl Interval)
      let H : C(Interval × Interval,↥Q) := ⟨Tseed ∘ changeClock,Tseed.continuous.comp changeClock.continuous⟩
      have hH : IsEmbedding H := hTseed.comp changeClock.isEmbedding
      have hHrange : range H = range Tseed := by
        ext y
        constructor
        · rintro ⟨z,rfl⟩
          exact ⟨changeClock z,rfl⟩
        · rintro ⟨z,rfl⟩
          exact ⟨changeClock.symm z,by simp [H]⟩
      refine ⟨H,hH,?_,?_,hHrange ▸ hTW,?_,hHrange.trans hTseedrange,fun z => hTseedrow (changeClock z)⟩
      · intro u
        change Tseed (clk.symm u,0) = _
        rw [hclk,clk.apply_symm_apply]
      · intro z
        change Tseed (clk.symm z.1,z.2) ∈ B ↔ _
        rw [hTB]
        constructor
        · rintro (he | he)
          · exact Or.inl (clk.symm.injective (he.trans hci0.symm))
          · exact Or.inr (clk.symm.injective (he.trans hci1.symm))
        · rintro (he | he)
          · exact Or.inl (he ▸ hci0)
          · exact Or.inr (he ▸ hci1)
      · intro z
        exact hTD (changeClock z)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `whole_seed_collar
      let some value := localDecl.value? | Lean.throwError "Missing local whole_seed_collar value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected whole_seed_collar axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS whole_seed_collar: {found.toList}"
    obtain ⟨Hseed,hHseed,hHseedseam,hHseedB,hHseedW,hHseedD,hHseedrange,hHseedrow⟩ := whole_seed_collar
    let patchκ : ℝ := seedκP*patchFactor
    have hpatchκ : 0 < patchκ ∧ patchκ ≤ 1 :=
      ⟨mul_pos hseedκP.1 hPatchFactor,(mul_le_mul hseedκP.2 hPatchFactor1 hPatchFactor.le (by norm_num)).trans (by norm_num)⟩
    let patchWidth : ℝ := eps*patchκ
    have hpatchWidth : 0 < patchWidth := mul_pos heps hpatchκ.1
    have hpatchWidthle : patchWidth ≤ eps := mul_le_of_le_one_right heps.le hpatchκ.2
    let final_patch_geometry :
      (∀ (z : Interval × Interval) (w : Interval), (w:ℝ) = patchκ*(z.2:ℝ) → P3 z = P (z.1,w)) ∧
      (∀ w, d.cornerChart (P3 (0,w)).val = Plane.mk (d.sigma*A) (-d.tau*patchWidth*(w:ℝ))) ∧
      (∀ w, d.cornerChart (P3 (1,w)).val = Plane.mk (-d.sigma*patchWidth*(w:ℝ)) (d.tau*A)) ∧
      (∀ z, ∃ v : Interval,
        d.cornerChart (P3 z).val =
          Plane.mk (d.sigma*(A*(v:ℝ)-patchWidth*(z.2:ℝ)*(1-(v:ℝ)))) (-d.tau*patchWidth*(z.2:ℝ)) ∨
        d.cornerChart (P3 z).val =
          Plane.mk (-d.sigma*patchWidth*(z.2:ℝ)) (d.tau*(A*(v:ℝ)-patchWidth*(z.2:ℝ)*(1-(v:ℝ))))) := by
      have hfull (z : Interval × Interval) (w : Interval) (hw : (w:ℝ) = patchκ*(z.2:ℝ)) : P3 z = P (z.1,w) := by
        let mid : Interval := ⟨patchFactor*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hPatchFactor,hPatchFactor1]⟩
        apply (hP3form z mid rfl).trans
        apply seed_width_formulas.1 (z.1,mid) w
        rw [hw]
        dsimp [patchκ,mid]
        ring
      refine ⟨hfull,?_,?_,?_⟩
      · intro w
        let old : Interval := ⟨patchκ*(w:ℝ),by
          constructor <;> nlinarith [w.property.1,w.property.2,hpatchκ.1,hpatchκ.2]⟩
        rw [hfull (0,w) old rfl,hP0]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [Plane.mk,old,patchWidth] <;> ring
      · intro w
        let old : Interval := ⟨patchκ*(w:ℝ),by
          constructor <;> nlinarith [w.property.1,w.property.2,hpatchκ.1,hpatchκ.2]⟩
        rw [hfull (1,w) old rfl,hP1]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [Plane.mk,old,patchWidth] <;> ring
      · intro z
        let old : Interval := ⟨patchκ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hpatchκ.1,hpatchκ.2]⟩
        rw [hfull z old rfl]
        obtain ⟨v,hv | hv⟩ := hProws (z.1,old)
        · refine ⟨v,Or.inl ?_⟩
          rw [hv]
          apply PiLp.ext
          intro i
          fin_cases i
          · change d.sigma*(A*(v:ℝ)-eps*(old:ℝ)*(1-(v:ℝ))) =
              d.sigma*(A*(v:ℝ)-patchWidth*(z.2:ℝ)*(1-(v:ℝ)))
            dsimp [old,patchWidth]
            ring
          · change -d.tau*eps*(old:ℝ) = -d.tau*patchWidth*(z.2:ℝ)
            dsimp [old,patchWidth]
            ring
        · refine ⟨v,Or.inr ?_⟩
          rw [hv]
          apply PiLp.ext
          intro i
          fin_cases i
          · change -d.sigma*eps*(old:ℝ) = -d.sigma*patchWidth*(z.2:ℝ)
            dsimp [old,patchWidth]
            ring
          · change d.tau*(A*(v:ℝ)-eps*(old:ℝ)*(1-(v:ℝ))) =
              d.tau*(A*(v:ℝ)-patchWidth*(z.2:ℝ)*(1-(v:ℝ)))
            dsimp [old,patchWidth]
            ring
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `final_patch_geometry
      let some value := localDecl.value? | Lean.throwError "Missing local final_patch_geometry value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected final_patch_geometry axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS final_patch_geometry: {found.toList}"
    obtain ⟨hP3literal,hP30,hP31,hP3rows⟩ := final_patch_geometry
    let final_patch_range : range (fun z : Interval × Interval => d.cornerChart (P3 z).val) =
      {p : Plane | -patchWidth ≤ d.sigma*p 0 ∧ d.sigma*p 0 ≤ A ∧
        -patchWidth ≤ d.tau*p 1 ∧ d.tau*p 1 ≤ A ∧
        (d.sigma*p 0 ≤ 0 ∨ d.tau*p 1 ≤ 0)} := by
      have hσ : d.sigma*d.sigma = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hτ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hA : 0 < A := heps.trans hepsA
      ext p
      constructor
      · rintro ⟨z,rfl⟩
        obtain ⟨v,hv | hv⟩ := hP3rows z
        all_goals
          have hAv : 0 ≤ A*(v:ℝ) := mul_nonneg hA.le v.property.1
          have hAvA : A*(v:ℝ) ≤ A := mul_le_of_le_one_right hA.le v.property.2
          have hw : 0 ≤ patchWidth*(z.2:ℝ) := mul_nonneg hpatchWidth.le z.2.property.1
          have hwE : patchWidth*(z.2:ℝ) ≤ patchWidth :=
            mul_le_of_le_one_right hpatchWidth.le z.2.property.2
          have hpart : 0 ≤ patchWidth*(z.2:ℝ)*(1-(v:ℝ)) := mul_nonneg hw (by linarith only [v.property.2])
          have hpartE : patchWidth*(z.2:ℝ)*(1-(v:ℝ)) ≤ patchWidth :=
            (mul_le_of_le_one_right hw (by linarith only [v.property.1])).trans hwE
          change -patchWidth ≤ d.sigma*d.cornerChart (P3 z).val 0 ∧
            d.sigma*d.cornerChart (P3 z).val 0 ≤ A ∧
            -patchWidth ≤ d.tau*d.cornerChart (P3 z).val 1 ∧
            d.tau*d.cornerChart (P3 z).val 1 ≤ A ∧
            (d.sigma*d.cornerChart (P3 z).val 0 ≤ 0 ∨ d.tau*d.cornerChart (P3 z).val 1 ≤ 0)
          rw [hv]
          simp [Plane.mk,← mul_assoc,hσ,hτ]
        · exact ⟨by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],Or.inr (by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE])⟩
        · exact ⟨by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE],Or.inl (by linarith only [hAv,hAvA,hw,hwE,hpart,hpartE])⟩
      · intro hp
        have hold : p ∈ range (fun z : Interval × Interval => d.cornerChart (P z).val) := by
          rw [hPwhole]
          exact ⟨(neg_le_neg hpatchWidthle).trans hp.1,hp.2.1,
            (neg_le_neg hpatchWidthle).trans hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2⟩
        obtain ⟨z,hz⟩ := hold
        have hcap : (z.2:ℝ) ≤ patchκ := by
          obtain ⟨v,hv | hv⟩ := hProws z
          · have hh : -eps*(z.2:ℝ) = d.tau*p 1 := by
              have he := congrArg (fun p : Plane => d.tau*p 1) (hv.symm.trans hz)
              simpa [Plane.mk,← mul_assoc,hτ] using he
            have hm : eps*(z.2:ℝ) ≤ eps*patchκ := by
              have hlow := hp.2.2.1
              dsimp [patchWidth] at hlow
              linarith only [hh,hlow]
            nlinarith only [hm,heps]
          · have hh : -eps*(z.2:ℝ) = d.sigma*p 0 := by
              have he := congrArg (fun p : Plane => d.sigma*p 0) (hv.symm.trans hz)
              simpa [Plane.mk,← mul_assoc,hσ] using he
            have hm : eps*(z.2:ℝ) ≤ eps*patchκ := by
              have hlow := hp.1
              dsimp [patchWidth] at hlow
              linarith only [hh,hlow]
            nlinarith only [hm,heps]
        let w : Interval := ⟨(z.2:ℝ)/patchκ,by
          constructor
          · exact div_nonneg z.2.property.1 hpatchκ.1.le
          · exact (div_le_one hpatchκ.1).mpr hcap⟩
        have hw : (z.2:ℝ) = patchκ*(w:ℝ) := by dsimp [w]; field_simp [hpatchκ.1.ne'] <;> ring
        exact ⟨(z.1,w),(congrArg (fun y : ↥Q => d.cornerChart y.val)
          (hP3literal (z.1,w) z.2 hw)).trans hz⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `final_patch_range
      let some value := localDecl.value? | Lean.throwError "Missing local final_patch_range value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected final_patch_range axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS final_patch_range: {found.toList}"
    let narrowed_patch_gate : ∃ bNew : Interval, d.s < bNew ∧ bNew < d.t ∧
      Disjoint ((fun u => q (d.xi u)) '' Ioi bNew) (range P3) ∧
      ∃ γ : C(Interval,↥Q), IsEmbedding γ ∧ γ 0 = q (d.xi d.s) ∧ γ 1 = q (d.xi bNew) ∧
        (∀ v, (γ v).val ∈ d.cornerChart.source ∧
          d.cornerChart (γ v).val = Plane.mk 0 (-d.tau*patchWidth*(v:ℝ))) ∧
        range γ = (fun u => q (d.xi u)) '' Icc d.s bNew ∧
        (∀ v : Interval, ∃ u : Interval, P3 (u,v) = γ v) ∧
        ∃ kNew : Interval, kNew ∈ Ioo (0:Interval) 1 ∧ P3 (kNew,1) = q (d.xi bNew) := by
      let chartQ : OpenPartialHomeomorph ↥Q Plane := {
        toPartialEquiv := {
          toFun := fun y => d.cornerChart y.val
          invFun := fun z => if hz : z ∈ d.cornerChart.target then
            ⟨d.cornerChart.symm z,interior_subset (d.axis_interior (d.cornerChart.map_target hz))⟩
            else d.M.first 1
          source := (Subtype.val : ↥Q → S) ⁻¹' d.cornerChart.source
          target := d.cornerChart.target
          map_source' := fun _ hy => d.cornerChart.map_source hy
          map_target' := by
            intro z hz
            simp only [dif_pos hz,mem_preimage]
            exact d.cornerChart.map_target hz
          left_inv' := by
            intro y hy
            apply Subtype.ext
            simp only [dif_pos (d.cornerChart.map_source hy)]
            exact d.cornerChart.left_inv hy
          right_inv' := by
            intro z hz
            simp only [dif_pos hz]
            exact d.cornerChart.right_inv hz
        }
        open_source := d.cornerChart.open_source.preimage continuous_subtype_val
        open_target := d.cornerChart.open_target
        continuousOn_toFun := d.cornerChart.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
        continuousOn_invFun := by
          apply IsInducing.subtypeVal.continuousOn_iff.mpr
          apply d.cornerChart.continuousOn_symm.congr
          intro z hz
          simp only [Function.comp_apply,dif_pos hz]
      }
    
      have hσ : d.sigma*d.sigma = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hτ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hτabs : |d.tau| = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hτne : d.tau ≠ 0 := by intro h; rw [h] at hτ; norm_num at hτ
      have hepsr : eps < d.radius := hepsA.trans hAr
      have hline (v : Interval) : Plane.mk 0 (-d.tau*eps*(v:ℝ)) ∈ chartQ.target := by
        apply d.small_square
        simp only [Plane.closedSquare,Plane.supDist,Plane.supNorm,mem_setOf_eq,sub_zero,
          Plane.mk,PiLp.toLp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
          abs_zero,abs_mul,abs_neg,hτabs,one_mul,abs_of_pos heps,abs_of_nonneg v.property.1]
        exact max_le d.radius_bounds.1.le ((mul_le_of_le_one_right heps.le v.property.2).trans hepsr.le)
      let qo : C(Interval,↥Q) := ⟨fun u => q (d.xi u),q.continuous.comp d.xi.continuous⟩
      have hqo : IsEmbedding qo := d.q_embedded.comp d.xi.isEmbedding
      let γold : C(Interval,↥Q) := ⟨fun v => chartQ.symm (Plane.mk 0 (-d.tau*eps*(v:ℝ))),
        chartQ.continuousOn_symm.comp_continuous (by fun_prop) hline⟩
      have hγoldchart (v) : d.cornerChart (γold v).val = Plane.mk 0 (-d.tau*eps*(v:ℝ)) :=
        chartQ.right_inv (hline v)
      have hγoldsource (v) : (γold v).val ∈ d.cornerChart.source := chartQ.map_target (hline v)
      have hγold : IsEmbedding γold := by
        apply (γold.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        have hh : (-d.tau*eps)*(u:ℝ) = (-d.tau*eps)*(v:ℝ) := by
          simpa [hγoldchart,Plane.mk] using congrArg (fun y : ↥Q => d.cornerChart y.val 1) he
        exact Subtype.ext (mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hτne) heps.ne') hh)
      have hγold0 : γold 0 = qo d.s := by
        have hsrc : d.M.first 1 ∈ chartQ.source := by
          change (d.M.first 1).val ∈ d.cornerChart.source
          rw [← d.a_corner]
          exact d.axes.center_mem
        have hc0 : chartQ (d.M.first 1) = 0 := by
          change d.cornerChart (d.M.first 1).val = 0
          rw [← d.a_corner]
          exact d.axes.center_zero
        change chartQ.symm (Plane.mk 0 (-d.tau*eps*(0:Interval))) = _
        have hzero : Plane.mk 0 (-d.tau*eps*(0:Interval)) = (0:Plane) := by simp [Plane.mk]
        rw [hzero,← hc0,chartQ.left_inv hsrc]
        exact d.q_corner.symm
      have hγold1 : γold 1 = qo b := by
        have hbsource : qo b ∈ chartQ.source := by
          change (q (d.xi b)).val ∈ d.cornerChart.source
          rw [← hkq]
          exact hPsource (mem_range_self (k,1))
        change chartQ.symm (Plane.mk 0 (-d.tau*eps*(1:Interval))) = _
        have hone : Plane.mk 0 (-d.tau*eps*(1:Interval)) = Plane.mk 0 (-d.tau*eps) := by simp [Plane.mk]
        rw [hone,← hbchart]
        exact chartQ.left_inv hbsource
      have hγoldq : range γold ⊆ range qo := by
        rintro y ⟨v,rfl⟩
        obtain ⟨u,hu⟩ := (d.axes.moving_axis _ (hγoldsource v)).mpr
          (show d.cornerChart (γold v).val 0 = 0 from by simp [hγoldchart,Plane.mk])
        refine ⟨d.xi.symm u,Subtype.ext ?_⟩
        simpa [qo] using hu
      have hγoldrange : range γold = qo '' Icc d.s b := by
        obtain ⟨_,hh⟩ := ActualHarerCornerGeometry.embedded_subarc_parameter_interval
          qo γold hqo hγold hγoldq d.s b hγold0.symm hγold1.symm
        rwa [uIcc_of_le hsb.le] at hh
      let sh : C(Interval,Interval) := ⟨fun v => ⟨patchκ*(v:ℝ),by
        constructor <;> nlinarith [v.property.1,v.property.2,hpatchκ.1,hpatchκ.2]⟩,by fun_prop⟩
      have hsh : IsEmbedding sh := by
        apply (sh.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        exact Subtype.ext (mul_left_cancel₀ hpatchκ.1.ne' (congrArg (fun w : Interval => (w:ℝ)) he))
      have hsh0 : sh 0 = 0 := by apply Subtype.ext; simp [sh]
      let γ : C(Interval,↥Q) := γold.comp sh
      have hγ : IsEmbedding γ := hγold.comp hsh
      have hγ0 : γ 0 = qo d.s := by change γold (sh 0) = _; rw [hsh0,hγold0]
      have hγsource (v) : (γ v).val ∈ d.cornerChart.source := hγoldsource (sh v)
      have hγchart (v) : d.cornerChart (γ v).val = Plane.mk 0 (-d.tau*patchWidth*(v:ℝ)) := by
        change d.cornerChart (γold (sh v)).val = _
        rw [hγoldchart]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [Plane.mk,sh,patchWidth] <;> ring
      have hγoldmem (v) : γ v ∈ qo '' Icc d.s b := hγoldrange ▸ (show γ v ∈ range γold from ⟨sh v,rfl⟩)
      obtain ⟨bNew,hbNew,hbNewγ⟩ := hγoldmem 1
      have hbNewne : bNew ≠ d.s := by
        intro he
        have hi : (1:Interval) = 0 := hγ.injective (hbNewγ.symm.trans (he ▸ hγ0.symm))
        have hh : (1:ℝ) = 0 := congrArg (fun w : Interval => (w:ℝ)) hi
        norm_num at hh
      have hsNew : d.s < bNew := lt_of_le_of_ne hbNew.1 hbNewne.symm
      have hNewt : bNew < d.t := hbNew.2.trans_lt hbt
      have hγq : range γ ⊆ range qo := by
        rintro y ⟨v,rfl⟩
        exact image_subset_range qo _ (hγoldmem v)
      have hγrange : range γ = qo '' Icc d.s bNew := by
        obtain ⟨_,hh⟩ := ActualHarerCornerGeometry.embedded_subarc_parameter_interval
          qo γ hqo hγ hγq d.s bNew hγ0.symm hbNewγ
        rwa [uIcc_of_le hsNew.le] at hh
      have hγP (v : Interval) : ∃ u : Interval, P3 (u,v) = γ v := by
        obtain ⟨z,hz⟩ := hprefix (hγoldmem v)
        have hc : d.cornerChart (P z).val = Plane.mk 0 (-d.tau*patchWidth*(v:ℝ)) :=
          (congrArg (fun y : ↥Q => d.cornerChart y.val) hz).trans (hγchart v)
        have hw : (z.2:ℝ) = patchκ*(v:ℝ) := by
          obtain ⟨u,hu | hu⟩ := hProws z
          · have hh := congrArg (fun p : Plane => d.tau*p 1) hc
            rw [hu] at hh
            simp [Plane.mk,← mul_assoc,hτ] at hh
            have hm : eps*(z.2:ℝ) = eps*(patchκ*(v:ℝ)) := by
              dsimp [patchWidth] at hh
              nlinarith only [hh]
            exact mul_left_cancel₀ heps.ne' hm
          · have hhx := congrArg (fun p : Plane => d.sigma*p 0) hc
            rw [hu] at hhx
            simp [Plane.mk,← mul_assoc,hσ] at hhx
            have hw0 : (z.2:ℝ) = 0 := congrArg (fun w : Interval => (w:ℝ))
              (hhx.resolve_left heps.ne')
            have hhy := congrArg (fun p : Plane => d.tau*p 1) hc
            rw [hu] at hhy
            simp [Plane.mk,hw0,← mul_assoc,hτ] at hhy
            have hAu : 0 ≤ A*(u:ℝ) := mul_nonneg (heps.trans hepsA).le u.property.1
            have hv0 : (v:ℝ) = 0 := by nlinarith only [hhy,hAu,hpatchWidth,v.property.1]
            rw [hw0,hv0,mul_zero]
        exact ⟨z.1,(hP3literal (z.1,v) z.2 hw).trans hz⟩
      have hP3P : range P3 ⊆ range P := by
        rintro y ⟨z,rfl⟩
        let w : Interval := ⟨patchκ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hpatchκ.1,hpatchκ.2]⟩
        exact ⟨(z.1,w),(hP3literal z w rfl).symm⟩
      have hfuture : Disjoint (qo '' Ioi bNew) (range P3) := by
        apply disjoint_left.mpr
        rintro y ⟨u,hu,rfl⟩ ⟨z,hz⟩
        have hsrc : (P3 z).val ∈ d.cornerChart.source := hPsource (hP3P (mem_range_self z))
        have hx : d.cornerChart (P3 z).val 0 = 0 :=
          (d.axes.moving_axis _ hsrc).mp ⟨d.xi u,(congrArg Subtype.val hz).symm⟩
        obtain ⟨v,hv | hv⟩ := hP3rows z
        · have heγ : P3 z = γ z.2 := by
            apply Subtype.ext
            apply d.cornerChart.injOn hsrc (hγsource z.2)
            rw [hγchart]
            apply PiLp.ext
            intro i
            fin_cases i
            · simpa [Plane.mk] using hx
            · simpa [Plane.mk] using congrArg (fun p : Plane => p 1) hv
          have hm : qo u ∈ qo '' Icc d.s bNew := hγrange ▸ (show qo u ∈ range γ from ⟨z.2,heγ.symm.trans hz⟩)
          obtain ⟨w,hw,he⟩ := hm
          have hwu : w = u := hqo.injective he
          exact not_le_of_gt hu (hwu ▸ hw.2)
        · have hxx := congrArg (fun p : Plane => d.sigma*p 0) hv
          simp [hx,Plane.mk,← mul_assoc,hσ] at hxx
          have hw0 : z.2 = 0 := hxx.resolve_left hpatchWidth.ne'
          have hqe : qo u ∈ range d.e := hz ▸ (hP3disk z).mpr hw0
          have hm : qo u ∈ range d.M.second := d.disk_q_trace ▸ ⟨hqe,mem_range_self (d.xi u)⟩
          rw [d.second_trace] at hm
          obtain ⟨w,hw,he⟩ := hm
          have hwu : w = u := hqo.injective he
          exact not_le_of_gt (hsNew.trans hu) (hwu ▸ hw.2)
      obtain ⟨kNew,hkγ⟩ := hγP 1
      have hkinter : kNew ∈ Ioo (0:Interval) 1 := by
        constructor
        · apply lt_of_le_of_ne (bot_le : 0 ≤ kNew)
          intro he
          change (0 : Interval) = kNew at he
          have hh := congrArg (fun y : ↥Q => d.sigma*d.cornerChart y.val 0) hkγ
          rw [he.symm,hP30] at hh
          simp [hγchart,Plane.mk,← mul_assoc,hσ] at hh
          linarith [heps.trans hepsA]
        · apply lt_of_le_of_ne (le_top : kNew ≤ 1)
          intro he
          change kNew = (1 : Interval) at he
          have hh := congrArg (fun y : ↥Q => d.tau*d.cornerChart y.val 1) hkγ
          rw [he,hP31] at hh
          simp [hγchart,Plane.mk,← mul_assoc,hτ] at hh
          linarith [heps.trans hepsA]
      exact ⟨bNew,hsNew,hNewt,hfuture,γ,hγ,hγ0,hbNewγ.symm,
        fun v => ⟨hγsource v,hγchart v⟩,hγrange,hγP,kNew,hkinter,hkγ.trans hbNewγ.symm⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `narrowed_patch_gate
      let some value := localDecl.value? | Lean.throwError "Missing local narrowed_patch_gate value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected narrowed_patch_gate axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS narrowed_patch_gate: {found.toList}"
    obtain ⟨bNew,hsNew,hNewt,hP3future,γNew,hγNew,hγNew0,hγNew1,hγNewChart,hγNewRange,
      hγNewP3,kNew,hkNew,hkNewq⟩ := narrowed_patch_gate
    let seed_future_q_clear : Disjoint ((fun u => q (d.xi u)) '' Ioi bNew) (range Hseed) := by
      apply disjoint_left.mpr
      rintro y ⟨u,hu,rfl⟩ hh
      rw [hHseedrange] at hh
      rcases hh with (hL | hP) | hR
      · exact disjoint_left.mp hL3future hL ⟨u,(hsNew.trans hu).le,rfl⟩
      · exact disjoint_left.mp hP3future ⟨u,hu,rfl⟩ hP
      · exact disjoint_left.mp hR3future hR ⟨u,(hsNew.trans hu).le,rfl⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `seed_future_q_clear
      let some value := localDecl.value? | Lean.throwError "Missing local seed_future_q_clear value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected seed_future_q_clear axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS seed_future_q_clear: {found.toList}"
    have hNewsource : (q (d.xi bNew)).val ∈ d.cornerChart.source := by
      rw [← hγNew1]
      exact (hγNewChart 1).1
    obtain ⟨Nnew,hNnew,hNnewgate,hNnewcenter,hNnewW,hNnewD,hNnewB,hNnewtrace,hNnewfuture⟩ :=
      calibrated_branch bNew ⟨hsNew,hNewt⟩ hNewsource
    obtain ⟨branchSign,branchLam,branchNear,hBranchSign,hBranchLam,hBranchNear,hNnew0,hNnewCal⟩ := hNnewgate
    let branch_without_arms : ∃ Narm : C(Interval × Icc (-1:ℝ) 1,↥Q), IsEmbedding Narm ∧
      (∀ u, Narm (u,⟨0,by norm_num⟩) = q (d.xi (Icc.convexComb bNew d.t u))) ∧
      range Narm ⊆ d.W ∧ Disjoint (range Narm) (range d.e) ∧ (∀ z, Narm z ∉ B) ∧
      range Narm ∩ range q = (fun u => q (d.xi u)) '' Icc bNew d.t ∧
      Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range Narm) ∧
      Disjoint (range Narm) (range L3) ∧ Disjoint (range Narm) (range R3) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
        (∀ (z : Interval × Icc (-1:ℝ) 1) (w : Icc (-1:ℝ) 1),
          (w:ℝ) = ρ*(z.2:ℝ) → Narm z = Nnew (z.1,w)) ∧
        (∀ z : Interval × Icc (-1:ℝ) 1,
          |(d.xi (Icc.convexComb bNew d.t z.1):ℝ)-(d.xi bNew:ℝ)| < branchNear →
          (Narm z).val ∈ d.cornerChart.source ∧
          d.cornerChart (Narm z).val =
            Plane.mk (branchSign*(branchLam*ρ)*(z.2:ℝ))
              (d.cornerChart (q (d.xi (Icc.convexComb bNew d.t z.1))).val 1)) := by
      let U : Set ↥Q := (range L3)ᶜ ∩ (range R3)ᶜ
      have hU : IsOpen U := (isCompact_range L3.continuous).isClosed.isOpen_compl.inter
        (isCompact_range R3.continuous).isClosed.isOpen_compl
      have hconv (u : Interval) : Icc.convexComb bNew d.t u ∈ Icc bNew d.t :=
        ⟨Icc.le_convexComb hNewt.le u,Icc.convexComb_le hNewt.le u⟩
      have hcU (u : Interval) : Nnew (u,⟨0,by norm_num⟩) ∈ U := by
        rw [hNnewcenter]
        have hfuture : q (d.xi (Icc.convexComb bNew d.t u)) ∈
            (fun v => q (d.xi v)) '' Ici d.s :=
          ⟨Icc.convexComb bNew d.t u,hsNew.le.trans (hconv u).1,rfl⟩
        exact ⟨fun h => disjoint_left.mp hL3future h hfuture,
          fun h => disjoint_left.mp hR3future h hfuture⟩
      obtain ⟨ρ,hρ,N,hN,hNU,hform,hcenter⟩ := source_shrink_embedded_strip_in_open Nnew hNnew U hU hcU
      let Narm : C(Interval × Icc (-1:ℝ) 1,↥Q) := ⟨N,hN.continuous⟩
      have hsub : range Narm ⊆ range Nnew := by
        rintro y ⟨z,rfl⟩
        exact ⟨(z.1,⟨ρ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩),
          (hform z).symm⟩
      have hc (u) : Narm (u,⟨0,by norm_num⟩) = q (d.xi (Icc.convexComb bNew d.t u)) :=
        (hcenter u).trans (hNnewcenter u)
      have htrace : range Narm ∩ range q = (fun u => q (d.xi u)) '' Icc bNew d.t := by
        apply Subset.antisymm
        · intro y hy
          exact hNnewtrace ▸ (show y ∈ range Nnew ∩ range q from ⟨hsub hy.1,hy.2⟩)
        · rintro y ⟨v,hv,rfl⟩
          have hm : v ∈ range (Icc.convexComb bNew d.t) := by
            rw [Path.range_subpathAux,uIcc_of_le hNewt.le]
            exact hv
          obtain ⟨u,hu⟩ := hm
          exact ⟨⟨(u,⟨0,by norm_num⟩),(hc u).trans (congrArg (fun v => q (d.xi v)) hu)⟩,
            mem_range_self _⟩
      have hNB (z) : Narm z ∉ B := by
        intro h
        obtain ⟨w,hw⟩ := hsub (mem_range_self z)
        exact hNnewB w (hw.symm ▸ h)
      refine ⟨Narm,hN,hc,hsub.trans hNnewW,hNnewD.mono_left hsub,hNB,
        htrace,hNnewfuture.mono_right hsub,?_,?_,ρ,hρ.1,hρ.2,?_,?_⟩
      · exact disjoint_left.mpr (fun y hy hl => (hNU hy).1 hl)
      · exact disjoint_left.mpr (fun y hy hr => (hNU hy).2 hr)
      · intro z w hw
        apply (hform z).trans
        exact congrArg Nnew (Prod.ext rfl (Subtype.ext hw.symm))
      · intro z hz
        rw [show Narm z = Nnew (z.1,⟨ρ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩) from hform z]
        have hh := hNnewCal (z.1,⟨ρ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hρ.1,hρ.2]⟩) hz
        refine ⟨hh.1,?_⟩
        rw [hh.2]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [Plane.mk] <;> ring
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `branch_without_arms
      let some value := localDecl.value? | Lean.throwError "Missing local branch_without_arms value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected branch_without_arms axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS branch_without_arms: {found.toList}"
    obtain ⟨Narm,hNarm,hNarmcenter,hNarmW,hNarmD,hNarmB,hNarmtrace,hNarmfuture,
      hNarmL,hNarmR,armFactor,hArmFactor,hArmFactor1,hNarmform,hNarmCal⟩ := branch_without_arms
    let near_branch_only_gate : ∃ η : ℝ, 0 < η ∧ η ≤ branchNear ∧
      ∀ z : Interval × Icc (-1:ℝ) 1,
        |(d.xi (Icc.convexComb bNew d.t z.1):ℝ)-(d.xi bNew:ℝ)| < η →
        Narm z ∈ range P3 → z.1 = 0 := by
      have hτ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      let f : Interval → ℝ := fun u => -d.tau*d.cornerChart (q u).val 1
      have hqc : ContinuousAt (fun u : Interval => (q u).val) (d.xi bNew) :=
        (continuous_subtype_val.comp q.continuous).continuousAt
      have hc : ContinuousAt (fun u : Interval => d.cornerChart (q u).val) (d.xi bNew) :=
        ContinuousAt.comp (f := fun u : Interval => (q u).val) (g := d.cornerChart)
          (d.cornerChart.continuousAt hNewsource) hqc
      have hf : ContinuousAt f (d.xi bNew) := continuousAt_const.mul
        ((show Continuous (fun p : Plane => p 1) from by fun_prop).continuousAt.comp hc)
      have hfb : f (d.xi bNew) = patchWidth := by
        change -d.tau*d.cornerChart (q (d.xi bNew)).val 1 = patchWidth
        rw [← hγNew1,(hγNewChart 1).2]
        simp [Plane.mk,← mul_assoc,hτ]
      obtain ⟨r,hr,hfr⟩ := Metric.continuousAt_iff.mp hf (patchWidth/2) (half_pos hpatchWidth)
      let η : ℝ := min branchNear r/2
      have hm : 0 < min branchNear r := lt_min hBranchNear hr
      have hη : 0 < η := half_pos hm
      have hηB : η ≤ branchNear := (half_lt_self hm).le.trans (min_le_left _ _)
      have hηr : η ≤ r := (half_lt_self hm).le.trans (min_le_right _ _)
      refine ⟨η,hη,hηB,?_⟩
      intro z hz hmem
      let vclock : Interval := d.xi (Icc.convexComb bNew d.t z.1)
      have hdist : dist vclock (d.xi bNew) < r := by
        rw [Subtype.dist_eq,Real.dist_eq]
        exact hz.trans_le hηr
      have hpos : 0 < f vclock := by
        have hh := hfr hdist
        rw [Real.dist_eq,hfb] at hh
        have hh' := (abs_lt.mp hh).1
        linarith [hpatchWidth]
      have hnear : |(d.xi (Icc.convexComb bNew d.t z.1):ℝ)-(d.xi bNew:ℝ)| < branchNear :=
        hz.trans_le hηB
      have hcal := hNarmCal z hnear
      have hcent := hNarmCal (z.1,⟨0,by norm_num⟩) hnear
      rw [hNarmcenter] at hcent
      have hsrc : (q vclock).val ∈ d.cornerChart.source := hcent.1
      have hx : d.cornerChart (q vclock).val 0 = 0 :=
        (d.axes.moving_axis _ hsrc).mp (mem_range_self vclock)
      obtain ⟨p,hp⟩ := hmem
      have hbox : d.cornerChart (P3 p).val ∈
          {p : Plane | -patchWidth ≤ d.sigma*p 0 ∧ d.sigma*p 0 ≤ A ∧
            -patchWidth ≤ d.tau*p 1 ∧ d.tau*p 1 ≤ A ∧
            (d.sigma*p 0 ≤ 0 ∨ d.tau*p 1 ≤ 0)} :=
        final_patch_range ▸ (show d.cornerChart (P3 p).val ∈ range
          (fun p : Interval × Interval => d.cornerChart (P3 p).val) from ⟨p,rfl⟩)
      have hbound : f vclock ≤ patchWidth := by
        rw [hp,hcal.2] at hbox
        have hh := hbox.2.2.1
        simp [Plane.mk] at hh
        dsimp [f,vclock]
        linarith only [hh]
      let v : Interval := ⟨f vclock/patchWidth,by
        constructor
        · exact (div_pos hpos hpatchWidth).le
        · exact (div_le_one hpatchWidth).mpr hbound⟩
      have heγ : q vclock = γNew v := by
        apply Subtype.ext
        apply d.cornerChart.injOn hsrc (hγNewChart v).1
        rw [(hγNewChart v).2]
        apply PiLp.ext
        intro i
        fin_cases i
        · simpa [Plane.mk] using hx
        · change d.cornerChart (q vclock).val 1 = -d.tau*patchWidth*(v:ℝ)
          dsimp [v,f]
          field_simp [hpatchWidth.ne']
          rcases d.signs.2 with ht | ht <;> rw [ht] <;> ring
      have hm : q vclock ∈ (fun u => q (d.xi u)) '' Icc d.s bNew :=
        hγNewRange ▸ (show q vclock ∈ range γNew from ⟨v,heγ.symm⟩)
      obtain ⟨w,hw,he⟩ := hm
      have hwc : w = Icc.convexComb bNew d.t z.1 := d.xi.injective (d.q_embedded.injective he)
      have hcle : (Icc.convexComb bNew d.t z.1:ℝ) ≤ (bNew:ℝ) := hwc ▸ hw.2
      simp only [Icc.coe_convexComb] at hcle
      have ht : (bNew:ℝ) < d.t := hNewt
      apply Subtype.ext
      change (z.1:ℝ) = 0
      nlinarith only [hcle,ht,z.1.property.1]
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `near_branch_only_gate
      let some value := localDecl.value? | Lean.throwError "Missing local near_branch_only_gate value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected near_branch_only_gate axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS near_branch_only_gate: {found.toList}"
    obtain ⟨branchGateNear,hBranchGateNear,hBranchGateNearB,hNearBranchGate⟩ := near_branch_only_gate
    let signed_tube_bound : ∀ (M : C(Interval × Icc (-1:ℝ) 1,↥Q)) (K : Set Interval), IsCompact K →
      ∀ U : Set ↥Q, IsOpen U → (∀ u ∈ K, M (u,⟨0,by norm_num⟩) ∈ U) →
        ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
          ∀ z : Interval × Icc (-1:ℝ) 1, z.1 ∈ K → |(z.2:ℝ)| ≤ δ → M z ∈ U := by
      intro M K hK U hU hcenter
      let w0 : Icc (-1:ℝ) 1 := ⟨0,by norm_num⟩
      have hbase : K ×ˢ ({w0} : Set (Icc (-1:ℝ) 1)) ⊆ M ⁻¹' U := by
        rintro ⟨u,w⟩ ⟨hu,hw⟩
        obtain rfl := mem_singleton_iff.mp hw
        exact hcenter u hu
      obtain ⟨A,V,hA,hV,hKA,h0V,hAV⟩ := generalized_tube_lemma
        hK isCompact_singleton (hU.preimage M.continuous) hbase
      obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV w0 (h0V (mem_singleton _))
      let δ : ℝ := min (r/2) (1/2)
      have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
      have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
      have hδr : δ < r := (min_le_left _ _).trans_lt (by linarith)
      refine ⟨δ,hδ,hδ1,?_⟩
      intro z hz hw
      have hwidth : z.2 ∈ V := by
        apply hrV
        rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
        change |(z.2:ℝ)-0| < r
        rw [sub_zero]
        exact hw.trans_lt hδr
      exact (show z ∈ M ⁻¹' U from hAV ⟨hKA hz,hwidth⟩)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `signed_tube_bound
      let some value := localDecl.value? | Lean.throwError "Missing local signed_tube_bound value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected signed_tube_bound axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS signed_tube_bound: {found.toList}"
    let far_branch_avoid_seed : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ z : Interval × Icc (-1:ℝ) 1,
        ¬ |(d.xi (Icc.convexComb bNew d.t z.1):ℝ)-(d.xi bNew:ℝ)| < branchGateNear →
        |(z.2:ℝ)| ≤ δ → Narm z ∉ range Hseed := by
      let K : Set Interval := {u | branchGateNear ≤
        |(d.xi (Icc.convexComb bNew d.t u):ℝ)-(d.xi bNew:ℝ)|}
      have hK : IsCompact K := by
        apply IsClosed.isCompact
        dsimp [K]
        exact isClosed_le continuous_const (by fun_prop)
      have hU : IsOpen (range Hseed)ᶜ := (isCompact_range Hseed.continuous).isClosed.isOpen_compl
      have hcenter (u : Interval) (hu : u ∈ K) : Narm (u,⟨0,by norm_num⟩) ∉ range Hseed := by
        have hu0 : u ≠ 0 := by
          intro he
          change branchGateNear ≤ |(d.xi (Icc.convexComb bNew d.t u):ℝ)-(d.xi bNew:ℝ)| at hu
          rw [he,Icc.convexComb_zero,sub_self,abs_zero] at hu
          exact not_le_of_gt hBranchGateNear hu
        have hu0' : (0:ℝ) < u := lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm))
        have hclock : bNew < Icc.convexComb bNew d.t u := by
          change (bNew:ℝ) < (Icc.convexComb bNew d.t u:ℝ)
          simp only [Icc.coe_convexComb]
          have ht : (bNew:ℝ) < d.t := hNewt
          nlinarith only [ht,hu0']
        rw [hNarmcenter]
        exact disjoint_left.mp seed_future_q_clear ⟨Icc.convexComb bNew d.t u,hclock,rfl⟩
      obtain ⟨δ,hδ,hδ1,hcap⟩ := signed_tube_bound Narm K hK (range Hseed)ᶜ hU hcenter
      exact ⟨δ,hδ,hδ1,fun z hz hw => hcap z (le_of_not_gt hz) hw⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `far_branch_avoid_seed
      let some value := localDecl.value? | Lean.throwError "Missing local far_branch_avoid_seed value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected far_branch_avoid_seed axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS far_branch_avoid_seed: {found.toList}"
    obtain ⟨farWidth,hFarWidth,hFarWidth1,hFarBranchClear⟩ := far_branch_avoid_seed
    let patch_free_rail : ∀ p : Plane, d.sigma*p 0 ∈ Icc (-patchWidth) A →
      d.tau*p 1 = -patchWidth →
      ∃ u : Interval, d.cornerChart (P3 (u,1)).val = p := by
      intro p hx hy
      have hτ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hm : p ∈ range (fun z : Interval × Interval => d.cornerChart (P3 z).val) := by
        rw [final_patch_range]
        exact ⟨hx.1,hx.2,hy ▸ le_rfl,hy ▸ (by linarith [heps.trans hepsA,hpatchWidth]),
          Or.inr (hy ▸ (by linarith [hpatchWidth]))⟩
      obtain ⟨z,hz⟩ := hm
      have hw : z.2 = 1 := by
        obtain ⟨v,hv | hv⟩ := hP3rows z
        · have hh := congrArg (fun p : Plane => d.tau*p 1) (hv.symm.trans hz)
          simp [Plane.mk,← mul_assoc,hτ,hy] at hh
          apply Subtype.ext
          change (z.2:ℝ) = 1
          nlinarith only [hh,hpatchWidth]
        · have hh := congrArg (fun p : Plane => d.tau*p 1) (hv.symm.trans hz)
          simp [Plane.mk,← mul_assoc,hτ,hy] at hh
          have hAv : 0 ≤ A*(v:ℝ) := mul_nonneg (heps.trans hepsA).le v.property.1
          have hcross : 0 ≤ patchWidth*(z.2:ℝ)*(v:ℝ) :=
            mul_nonneg (mul_nonneg hpatchWidth.le z.2.property.1) v.property.1
          apply Subtype.ext
          change (z.2:ℝ) = 1
          nlinarith only [hh,hAv,hcross,hpatchWidth,z.2.property.2]
      exact ⟨z.1,(congrArg (fun v : Interval × Interval => d.cornerChart (P3 v).val)
        (show (z.1,(1:Interval)) = z from Prod.ext rfl hw.symm)).trans hz⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `patch_free_rail
      let some value := localDecl.value? | Lean.throwError "Missing local patch_free_rail value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected patch_free_rail axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS patch_free_rail: {found.toList}"
    let seed_patch_preserves_width : ∀ z v : Interval × Interval,
      Hseed z = P3 v → z.2 = v.2 := by
      intro z v he
      obtain ⟨u,hu | hu | hu⟩ := hHseedrow z
      · exact (congrArg Prod.snd ((hL3P3 (u,z.2) v).mp (hu.symm.trans he)).2).symm
      · have hh : (u,z.2) = v := hP3.injective (hu.symm.trans he)
        cases hh
        rfl
      · exact (congrArg Prod.snd ((hR3P3 (u,z.2) v).mp (hu.symm.trans he)).2).symm
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `seed_patch_preserves_width
      let some value := localDecl.value? | Lean.throwError "Missing local seed_patch_preserves_width value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected seed_patch_preserves_width axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS seed_patch_preserves_width: {found.toList}"
    let actual_branch_gate : ∃ Ncap : C(Interval × Icc (-1:ℝ) 1,↥Q), IsEmbedding Ncap ∧
      (∀ u, Ncap (u,⟨0,by norm_num⟩) = q (d.xi (Icc.convexComb bNew d.t u))) ∧
      range Ncap ⊆ range Narm ∧
      (∀ w : Icc (-1:ℝ) 1, ∃ u : Interval, u ∈ Ioo (0:Interval) 1 ∧ Hseed (u,1) = Ncap (0,w)) ∧
      (∀ z : Interval × Icc (-1:ℝ) 1, ∀ v : Interval × Interval,
        Ncap z = Hseed v → z.1 = 0 ∧ v.2 = 1) ∧
      range Ncap ∩ range Hseed = range (fun w : Icc (-1:ℝ) 1 => Ncap (0,w)) := by
      let lam : ℝ := branchLam*armFactor
      have hlam : 0 < lam := mul_pos hBranchLam hArmFactor
      let m : ℝ := min patchWidth A
      have hm : 0 < m := lt_min hpatchWidth (heps.trans hepsA)
      let cap : ℝ := min farWidth (min 1 (m/(2*lam)))
      have hcap : 0 < cap := lt_min hFarWidth (lt_min (by norm_num) (div_pos hm (by positivity)))
      let ρ : ℝ := cap/2
      have hρ : 0 < ρ := half_pos hcap
      have hρcap : ρ ≤ cap := (half_lt_self hcap).le
      have hρfar : ρ ≤ farWidth := hρcap.trans (min_le_left _ _)
      have hρ1 : ρ ≤ 1 := hρcap.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hρphys : ρ ≤ m/(2*lam) := hρcap.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hlρ : 0 < lam*ρ := mul_pos hlam hρ
      have hlρm : lam*ρ < m := by
        have hh : ρ*(2*lam) ≤ m := (le_div_iff₀ (by positivity)).mp hρphys
        nlinarith only [hh,hm]
      let sh : C(Icc (-1:ℝ) 1,Icc (-1:ℝ) 1) := ⟨fun w => ⟨ρ*(w:ℝ),by
        constructor <;> nlinarith [w.property.1,w.property.2,hρ,hρ1]⟩,by fun_prop⟩
      have hsh : IsEmbedding sh := by
        apply (sh.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        exact Subtype.ext (mul_left_cancel₀ hρ.ne' (congrArg (fun w : Icc (-1:ℝ) 1 => (w:ℝ)) he))
      have hsh0 : sh ⟨0,by norm_num⟩ = ⟨0,by norm_num⟩ := by apply Subtype.ext; simp [sh]
      let sk := (ContinuousMap.id Interval).prodMap sh
      let Ncap : C(Interval × Icc (-1:ℝ) 1,↥Q) := Narm.comp sk
      have hNcap : IsEmbedding Ncap := hNarm.comp (IsEmbedding.id.prodMap hsh)
      have hsub : range Ncap ⊆ range Narm := by
        rintro y ⟨z,rfl⟩
        exact mem_range_self (sk z)
      have hNB (z) : Ncap z ∉ B := hNarmB (sk z)
      have hσabs : |d.sigma| = 1 := by rcases d.signs.1 with h | h <;> rw [h] <;> norm_num
      have hsignabs : |branchSign| = 1 := by rcases hBranchSign with h | h <;> rw [h] <;> norm_num
      have hτ : d.tau*d.tau = 1 := by rcases d.signs.2 with h | h <;> rw [h] <;> norm_num
      have hPsrc (z : Interval × Interval) : (P3 z).val ∈ d.cornerChart.source := by
        let w : Interval := ⟨patchκ*(z.2:ℝ),by
          constructor <;> nlinarith [z.2.property.1,z.2.property.2,hpatchκ.1,hpatchκ.2]⟩
        rw [hP3literal z w rfl]
        exact hPsource (mem_range_self (z.1,w))
      have hgate (w : Icc (-1:ℝ) 1) : (Ncap (0,w)).val ∈ d.cornerChart.source ∧
          d.cornerChart (Ncap (0,w)).val = Plane.mk (branchSign*(lam*ρ)*(w:ℝ)) (-d.tau*patchWidth) := by
        have hn : |(d.xi (Icc.convexComb bNew d.t (0:Interval)):ℝ)-(d.xi bNew:ℝ)| < branchNear := by
          simp only [Icc.convexComb_zero,sub_self,abs_zero]
          exact hBranchNear
        have hh := hNarmCal (0,sh w) hn
        refine ⟨hh.1,?_⟩
        change d.cornerChart (Narm (0,sh w)).val = _
        rw [hh.2,Icc.convexComb_zero,← hγNew1,(hγNewChart 1).2]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp [Plane.mk,sh,lam] <;> ring
      have hcover (w : Icc (-1:ℝ) 1) :
          ∃ u : Interval, u ∈ Ioo (0:Interval) 1 ∧ Hseed (u,1) = Ncap (0,w) := by
        have hab : |d.sigma*(branchSign*(lam*ρ)*(w:ℝ))| < m := by
          calc
            _ = (lam*ρ)*|(w:ℝ)| := by
              rw [abs_mul,abs_mul,abs_mul,hσabs,hsignabs,abs_of_pos hlρ]
              ring
            _ ≤ lam*ρ := mul_le_of_le_one_right hlρ.le (abs_le.mpr w.property)
            _ < m := hlρm
        have hx : d.sigma*d.cornerChart (Ncap (0,w)).val 0 ∈ Icc (-patchWidth) A := by
          rw [(hgate w).2]
          simp only [Plane.mk,PiLp.toLp_apply,Matrix.cons_val_zero]
          exact ⟨(neg_le_neg (min_le_left patchWidth A)).trans (abs_lt.mp hab).1.le,
            (abs_lt.mp hab).2.le.trans (min_le_right patchWidth A)⟩
        have hy : d.tau*d.cornerChart (Ncap (0,w)).val 1 = -patchWidth := by
          rw [(hgate w).2]
          simp [Plane.mk,← mul_assoc,hτ]
        obtain ⟨u,hu⟩ := patch_free_rail (d.cornerChart (Ncap (0,w)).val) hx hy
        have heP : P3 (u,1) = Ncap (0,w) :=
          Subtype.ext (d.cornerChart.injOn (hPsrc (u,1)) (hgate w).1 hu)
        have hmem : Ncap (0,w) ∈ range Hseed := by
          rw [hHseedrange]
          exact Or.inl (Or.inr ⟨(u,1),heP⟩)
        obtain ⟨v,hv⟩ := hmem
        have hv1 : v.2 = 1 := seed_patch_preserves_width v (u,1) (hv.trans heP.symm)
        have hvends : ¬ (v.1 = 0 ∨ v.1 = 1) :=
          fun he => hNB (0,w) (hv ▸ (hHseedB v).mpr he)
        have hvi : v.1 ∈ Ioo (0:Interval) 1 :=
          ⟨lt_of_le_of_ne (bot_le : 0 ≤ v.1) (fun he => hvends (Or.inl he.symm)),
            lt_of_le_of_ne (le_top : v.1 ≤ 1) (fun he => hvends (Or.inr he))⟩
        exact ⟨v.1,hvi,(congrArg Hseed (show (v.1,(1:Interval)) = v from Prod.ext rfl hv1.symm)).trans hv⟩
      have hkernel (z : Interval × Icc (-1:ℝ) 1) (v : Interval × Interval)
          (he : Ncap z = Hseed v) : z.1 = 0 ∧ v.2 = 1 := by
        have hPmem : Ncap z ∈ range P3 := by
          have hh := mem_range_self (f := Hseed) v
          rw [hHseedrange] at hh
          rcases hh with (hl | hp) | hr
          · exact False.elim (disjoint_left.mp hNarmL (hsub (mem_range_self z)) (he.symm ▸ hl))
          · exact he.symm ▸ hp
          · exact False.elim (disjoint_left.mp hNarmR (hsub (mem_range_self z)) (he.symm ▸ hr))
        have hz0 : z.1 = 0 := by
          by_cases hn : |(d.xi (Icc.convexComb bNew d.t z.1):ℝ)-(d.xi bNew:ℝ)| < branchGateNear
          · exact hNearBranchGate (sk z) hn hPmem
          · have hw : |((sk z).2:ℝ)| ≤ farWidth := by
              change |ρ*(z.2:ℝ)| ≤ farWidth
              rw [abs_mul,abs_of_pos hρ]
              exact (mul_le_of_le_one_right hρ.le (abs_le.mpr z.2.property)).trans hρfar
            exact False.elim (hFarBranchClear (sk z) hn hw ⟨v,he.symm⟩)
        obtain ⟨u,hu,hugate⟩ := hcover z.2
        have hN : Ncap z = Ncap (0,z.2) := congrArg Ncap (Prod.ext hz0 rfl)
        have hH : Hseed v = Hseed (u,1) := he.symm.trans (hN.trans hugate.symm)
        exact ⟨hz0,congrArg Prod.snd (hHseed.injective hH)⟩
      refine ⟨Ncap,hNcap,?_,hsub,hcover,hkernel,?_⟩
      · intro u
        change Narm (u,sh ⟨0,by norm_num⟩) = _
        rw [hsh0,hNarmcenter]
      · ext y
        constructor
        · rintro ⟨⟨z,hz⟩,⟨v,hv⟩⟩
          have hh := hkernel z v (hz.trans hv.symm)
          exact ⟨z.2,(congrArg Ncap (show (0,z.2) = z from Prod.ext hh.1.symm rfl)).trans hz⟩
        · rintro ⟨w,rfl⟩
          obtain ⟨u,hu,hugate⟩ := hcover w
          exact ⟨mem_range_self (0,w),⟨(u,1),hugate⟩⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_branch_gate
      let some value := localDecl.value? | Lean.throwError "Missing local actual_branch_gate value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_branch_gate axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_branch_gate: {found.toList}"
    obtain ⟨Ncap,hNcap,hNcapcenter,hNcapNarm,hNcapcover,hNcapkernel,hNcapmeet⟩ := actual_branch_gate
    let actual_seed_disk_and_gate :
      ∃ Dseed : C(Metric.closedBall (0:Plane) 1,↥Q), IsEmbedding Dseed ∧
        range Dseed = range Hseed ∧
        Dseed '' {z | z.val ∈ Metric.sphere (0:Plane) 1} = Hseed '' ActualHarerDiskGluing.squareBoundary ∧
      ∃ qGate : C(Interval,↥Q), IsEmbedding qGate ∧
        range qGate = range (fun w : Icc (-1:ℝ) 1 => Ncap (0,w)) ∧
        (∀ (u : Interval) (w : Icc (-1:ℝ) 1), (w:ℝ) = 2*(u:ℝ)-1 → qGate u = Ncap (0,w)) ∧
      ∃ gateClock : C(Interval,Interval), IsEmbedding gateClock ∧
        (∀ u, gateClock u ∈ Ioo (0:Interval) 1) ∧
        (∀ u, Hseed (gateClock u,1) = qGate u) ∧
        gateClock 0 ≠ gateClock 1 ∧ range gateClock = uIcc (gateClock 0) (gateClock 1) ∧
      ∃ strip : C(Interval × Interval,↥Q), IsEmbedding strip ∧
        range strip = range Ncap ∧ (∀ u, strip (u,0) = qGate u) ∧
        (∀ (z : Interval × Interval) (w : Icc (-1:ℝ) 1), (w:ℝ) = 2*(z.1:ℝ)-1 → strip z = Ncap (z.2,w)) ∧
        range strip ∩ range Dseed = range qGate := by
      obtain ⟨j,hj⟩ := ActualHarerDiskGluing.unit_disk_square_boundary_homeomorph
      let Dseed : C(Metric.closedBall (0:Plane) 1,↥Q) := ⟨Hseed ∘ j,Hseed.continuous.comp j.continuous⟩
      have hDseed : IsEmbedding Dseed := hHseed.comp j.isEmbedding
      have hDrange : range Dseed = range Hseed := j.surjective.range_comp Hseed
      have hDbd : Dseed '' {z | z.val ∈ Metric.sphere (0:Plane) 1} =
          Hseed '' ActualHarerDiskGluing.squareBoundary := by
        change (Hseed ∘ j) '' {z | z.val ∈ Metric.sphere (0:Plane) 1} = _
        rw [image_comp,hj]
      let wl : C(Interval,Icc (-1:ℝ) 1) := ⟨fun u => ⟨2*(u:ℝ)-1,by
        constructor <;> linarith [u.property.1,u.property.2]⟩,by fun_prop⟩
      have hwl : IsEmbedding wl := by
        apply (wl.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply Subtype.ext
        have hh := congrArg (fun w : Icc (-1:ℝ) 1 => (w:ℝ)) he
        change 2*(u:ℝ)-1 = 2*(v:ℝ)-1 at hh
        linarith only [hh]
      have hwlonto : Function.Surjective wl := by
        intro w
        let u : Interval := ⟨((w:ℝ)+1)/2,by constructor <;> linarith [w.property.1,w.property.2]⟩
        exact ⟨u,Subtype.ext (by dsimp [wl,u]; ring)⟩
      let qGate : C(Interval,↥Q) := ⟨fun u => Ncap (0,wl u),by fun_prop⟩
      have hqGate : IsEmbedding qGate := hNcap.comp
        ((isEmbedding_prodMkRight (0:Interval)).comp hwl)
      have hqRange : range qGate = range (fun w : Icc (-1:ℝ) 1 => Ncap (0,w)) :=
        hwlonto.range_comp (fun w => Ncap (0,w))
      have hqSeed (u) : qGate u ∈ range Hseed := by
        obtain ⟨v,hv,hve⟩ := hNcapcover (wl u)
        exact ⟨(v,1),hve⟩
      let lift : C(Interval,Interval × Interval) :=
        ⟨fun u => hHseed.toHomeomorph.symm ⟨qGate u,hqSeed u⟩,
          hHseed.toHomeomorph.symm.continuous.comp (qGate.continuous.subtype_mk _)⟩
      have hLift (u) : Hseed (lift u) = qGate u := congrArg Subtype.val
        (hHseed.toHomeomorph.apply_symm_apply ⟨qGate u,hqSeed u⟩)
      have hLiftWidth (u) : (lift u).2 = 1 :=
        (hNcapkernel (0,wl u) (lift u) (hLift u).symm).2
      let gateClock : C(Interval,Interval) := ⟨fun u => (lift u).1,by fun_prop⟩
      have hclock (u) : Hseed (gateClock u,1) = qGate u :=
        (congrArg Hseed (show (gateClock u,(1:Interval)) = lift u from Prod.ext rfl (hLiftWidth u).symm)).trans (hLift u)
      have hgClock : IsEmbedding gateClock := by
        apply (gateClock.continuous.isClosedEmbedding ?_).isEmbedding
        intro u v he
        apply hqGate.injective
        rw [← hclock u,← hclock v,he]
      have hNB (z) : Ncap z ∉ B := by
        intro he
        obtain ⟨w,hw⟩ := hNcapNarm (mem_range_self z)
        exact hNarmB w (hw.symm ▸ he)
      have hclockInterior (u) : gateClock u ∈ Ioo (0:Interval) 1 := by
        have hend : ¬ (gateClock u = 0 ∨ gateClock u = 1) :=
          fun he => hNB (0,wl u) ((hclock u) ▸ (hHseedB (gateClock u,1)).mpr he)
        exact ⟨lt_of_le_of_ne (bot_le : 0 ≤ gateClock u) (fun he => hend (Or.inl he.symm)),
          lt_of_le_of_ne (le_top : gateClock u ≤ 1) (fun he => hend (Or.inr he))⟩
      let idClock : C(Interval,Interval) := ContinuousMap.id Interval
      have hclockRange (u : Interval) : gateClock u ∈ range idClock := ⟨gateClock u,rfl⟩
      obtain ⟨hne,hrange⟩ := ActualHarerCornerGeometry.embedded_subarc_parameter_interval
        idClock gateClock IsEmbedding.id hgClock (by rintro y ⟨u,rfl⟩; exact hclockRange u)
        (gateClock 0) (gateClock 1) rfl rfl
      have hcrange : range gateClock = uIcc (gateClock 0) (gateClock 1) := by
        simpa only [idClock,ContinuousMap.coe_id,Set.image_id] using hrange
      let shift : C(Interval × Interval,Interval × Icc (-1:ℝ) 1) :=
        ⟨fun z => (z.2,wl z.1),by fun_prop⟩
      have hshift : IsEmbedding shift := by
        apply (shift.continuous.isClosedEmbedding ?_).isEmbedding
        intro z v he
        apply Prod.ext
        · exact hwl.injective (congrArg Prod.snd he)
        · exact congrArg Prod.fst he
      have hshiftonto : Function.Surjective shift := by
        intro z
        obtain ⟨u,hu⟩ := hwlonto z.2
        exact ⟨(u,z.1),Prod.ext rfl hu⟩
      let strip : C(Interval × Interval,↥Q) := Ncap.comp shift
      have hstrip : IsEmbedding strip := hNcap.comp hshift
      have hStripRange : range strip = range Ncap := hshiftonto.range_comp Ncap
      refine ⟨Dseed,hDseed,hDrange,hDbd,qGate,hqGate,hqRange,?_,gateClock,hgClock,
        hclockInterior,hclock,hne,hcrange,strip,hstrip,hStripRange,fun u => rfl,?_,?_⟩
      · intro u w hw
        have hh : wl u = w := Subtype.ext hw.symm
        exact congrArg (fun v => Ncap (0,v)) hh
      · intro z w hw
        have hh : wl z.1 = w := Subtype.ext hw.symm
        exact congrArg (fun v => Ncap (z.2,v)) hh
      · rw [hStripRange,hDrange,hNcapmeet,← hqRange]
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_seed_disk_and_gate
      let some value := localDecl.value? | Lean.throwError "Missing local actual_seed_disk_and_gate value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_seed_disk_and_gate axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_seed_disk_and_gate: {found.toList}"
    obtain ⟨Dseed,hDseed,hDseedrange,hDseedbd,qGate,hqGate,hqGateRange,hqGateLiteral,gateClock,hGateClock,
      hGateClockInterior,hGateClockEq,hGateClockNe,hGateClockRange,attachStrip,hAttachStrip,hAttachRange,hAttachCenter,hAttachLiteral,hAttachMeet⟩ :=
        actual_seed_disk_and_gate
    let parameter_boundary_complement
   : ∀ (α β : Interval), 0 < α → α < β → β < 1 →
      ∃ G : C(Interval,Interval × Interval), IsEmbedding G ∧ G 0 = (α,1) ∧ G 1 = (β,1) ∧
        range G = {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ (z.2 = 1 ∧ (z.1 ≤ α ∨ β ≤ z.1))} := by
      intro α β hα0 hαβ hβ1
      let join : ∀ (L R : C(Interval,Interval × Interval)), IsEmbedding L → IsEmbedding R →
          L 1 = R 0 → range L ∩ range R = {L 1} →
          ∃ F : C(Interval,Interval × Interval), IsEmbedding F ∧ F 0 = L 0 ∧ F 1 = R 1 ∧
            range F = range L ∪ range R := by
        intro L R hL hR hend hmeet
        let p : Interval × PUnit ≃ₜ Interval := Homeomorph.prodPUnit Interval
        let flip : Interval × PUnit ≃ₜ Interval := p.trans unitInterval.symmHomeomorph
        let LF : Interval × PUnit → Interval × Interval := L ∘ flip
        let RF : Interval × PUnit → Interval × Interval := R ∘ p
        have hLF : IsEmbedding LF := hL.comp flip.isEmbedding
        have hRF : IsEmbedding RF := hR.comp p.isEmbedding
        have hLFr : range LF = range L := flip.surjective.range_comp L
        have hRFr : range RF = range R := p.surjective.range_comp R
        have hLzero (w : PUnit) : LF (0,w) = L 1 := by
          change L (unitInterval.symm 0) = L 1
          rw [unitInterval.symm_zero]
        have hseam (w : PUnit) : LF (0,w) = RF (0,w) := (hLzero w).trans hend
        have hmeet' : range LF ∩ range RF = range (fun w : PUnit => LF (0,w)) := by
          rw [hLFr,hRFr,hmeet]
          ext y
          constructor
          · intro hy
            obtain rfl := mem_singleton_iff.mp hy
            exact ⟨PUnit.unit,hLzero _⟩
          · rintro ⟨w,hw⟩
            exact mem_singleton_iff.mpr (hw.symm.trans (hLzero w))
        obtain ⟨G,hG,hG0,hG1,hGm,hGr,hGrow⟩ :=
          source_glue_two_surface_strips LF RF hLF hRF hseam hmeet'
        let F : C(Interval,Interval × Interval) := ⟨fun u => G (u,PUnit.unit),by fun_prop⟩
        have hF : IsEmbedding F := hG.comp (isEmbedding_prodMkLeft PUnit.unit)
        have hFr : range F = range G := by
          ext y
          constructor
          · rintro ⟨u,rfl⟩
            exact ⟨(u,PUnit.unit),rfl⟩
          · rintro ⟨⟨u,w⟩,he⟩
            cases w
            exact ⟨u,he⟩
        refine ⟨F,hF,?_,?_,hFr.trans (hGr.trans (congrArg₂ Set.union hLFr hRFr))⟩
        · change G (0,PUnit.unit) = L 0
          rw [hG0]
          change L (unitInterval.symm 1) = L 0
          rw [unitInterval.symm_one]
        · exact hG1 PUnit.unit
      obtain ⟨cl,hcl,hcl0,hcl1,hclr,hclf⟩ := source_affine_subinterval 0 α hα0
      obtain ⟨cr,hcr,hcr0,hcr1,hcrr,hcrf⟩ := source_affine_subinterval β 1 hβ1
      let PL : C(Interval,Interval × Interval) := ⟨fun u => (cl (unitInterval.symm u),1),by fun_prop⟩
      let V0 : C(Interval,Interval × Interval) := ⟨fun u => (0,unitInterval.symm u),by fun_prop⟩
      let BT : C(Interval,Interval × Interval) := ⟨fun u => (u,0),by fun_prop⟩
      let V1 : C(Interval,Interval × Interval) := ⟨fun u => (1,u),by fun_prop⟩
      let PR : C(Interval,Interval × Interval) := ⟨fun u => (cr (unitInterval.symm u),1),by fun_prop⟩
      have hPL : IsEmbedding PL := (isEmbedding_prodMkLeft (1:Interval)).comp (hcl.comp unitInterval.symmHomeomorph.isEmbedding)
      have hV0 : IsEmbedding V0 := (isEmbedding_prodMkRight (0:Interval)).comp unitInterval.symmHomeomorph.isEmbedding
      have hBT : IsEmbedding BT := isEmbedding_prodMkLeft (0:Interval)
      have hV1 : IsEmbedding V1 := isEmbedding_prodMkRight (1:Interval)
      have hPR : IsEmbedding PR := (isEmbedding_prodMkLeft (1:Interval)).comp (hcr.comp unitInterval.symmHomeomorph.isEmbedding)
      have hPL0 : PL 0 = (α,1) := by simp [PL,hcl1]
      have hPL1 : PL 1 = (0,1) := by simp [PL,hcl0]
      have hV00 : V0 0 = (0,1) := by simp [V0]
      have hV01 : V0 1 = (0,0) := by simp [V0]
      have hBT0 : BT 0 = (0,0) := rfl
      have hBT1 : BT 1 = (1,0) := rfl
      have hV10 : V1 0 = (1,0) := rfl
      have hV11 : V1 1 = (1,1) := rfl
      have hPR0 : PR 0 = (1,1) := by simp [PR,hcr1]
      have hPR1 : PR 1 = (β,1) := by simp [PR,hcr0]
      have hPLchar (z : Interval × Interval) : z ∈ range PL ↔ z.2 = 1 ∧ z.1 ≤ α := by
        constructor
        · rintro ⟨u,rfl⟩
          exact ⟨rfl,(hclr ▸ mem_range_self (unitInterval.symm u)).2⟩
        · rintro ⟨hy,hx⟩
          have hm : z.1 ∈ range cl := hclr ▸ (show z.1 ∈ Icc 0 α from ⟨bot_le,hx⟩)
          obtain ⟨u,hu⟩ := hm
          exact ⟨unitInterval.symm u,Prod.ext (by simpa [PL] using hu) hy.symm⟩
      have hV0char (z : Interval × Interval) : z ∈ range V0 ↔ z.1 = 0 := by
        constructor
        · rintro ⟨u,rfl⟩
          rfl
        · intro hx
          exact ⟨unitInterval.symm z.2,Prod.ext hx.symm (by simp [V0])⟩
      have hBTchar (z : Interval × Interval) : z ∈ range BT ↔ z.2 = 0 := by
        constructor
        · rintro ⟨u,rfl⟩
          rfl
        · intro hy
          exact ⟨z.1,Prod.ext rfl hy.symm⟩
      have hV1char (z : Interval × Interval) : z ∈ range V1 ↔ z.1 = 1 := by
        constructor
        · rintro ⟨u,rfl⟩
          rfl
        · intro hx
          exact ⟨z.2,Prod.ext hx.symm rfl⟩
      have hPRchar (z : Interval × Interval) : z ∈ range PR ↔ z.2 = 1 ∧ β ≤ z.1 := by
        constructor
        · rintro ⟨u,rfl⟩
          exact ⟨rfl,(hcrr ▸ mem_range_self (unitInterval.symm u)).1⟩
        · rintro ⟨hy,hx⟩
          have hm : z.1 ∈ range cr := hcrr ▸ (show z.1 ∈ Icc β 1 from ⟨hx,le_top⟩)
          obtain ⟨u,hu⟩ := hm
          exact ⟨unitInterval.symm u,Prod.ext (by simpa [PR] using hu) hy.symm⟩
      have h01 : (0:Interval) ≠ 1 := by
        intro he
        have hh : (0:ℝ) = 1 := congrArg (fun u : Interval => (u:ℝ)) he
        norm_num at hh
      have hmeet0 : range PL ∩ range V0 = {PL 1} := by
        rw [hPL1]
        ext z
        constructor
        · rintro ⟨hl,hv⟩
          exact mem_singleton_iff.mpr (Prod.ext ((hV0char z).mp hv) ((hPLchar z).mp hl).1)
        · intro hz
          obtain rfl := mem_singleton_iff.mp hz
          exact ⟨(hPLchar _).mpr ⟨rfl,hα0.le⟩,(hV0char _).mpr rfl⟩
      obtain ⟨F0,hF0,hF00,hF01,hF0r⟩ := join PL V0 hPL hV0 (hPL1.trans hV00.symm) hmeet0
      have hF01' : F0 1 = (0,0) := hF01.trans hV01
      have hmeet1 : range F0 ∩ range BT = {F0 1} := by
        rw [hF0r,hF01']
        ext z
        constructor
        · rintro ⟨hl | hv,hb⟩
          · exact False.elim (h01 (((hBTchar z).mp hb).symm.trans ((hPLchar z).mp hl).1))
          · exact mem_singleton_iff.mpr (Prod.ext ((hV0char z).mp hv) ((hBTchar z).mp hb))
        · intro hz
          obtain rfl := mem_singleton_iff.mp hz
          exact ⟨Or.inr ((hV0char _).mpr rfl),(hBTchar _).mpr rfl⟩
      obtain ⟨F1,hF1,hF10,hF11,hF1r⟩ := join F0 BT hF0 hBT (hF01'.trans hBT0.symm) hmeet1
      have hF11' : F1 1 = (1,0) := hF11.trans hBT1
      have hmeet2 : range F1 ∩ range V1 = {F1 1} := by
        rw [hF1r,hF0r,hF11']
        ext z
        constructor
        · rintro ⟨(hl | hv) | hb,hr⟩
          · have hh : (1:Interval) ≤ α := ((hV1char z).mp hr) ▸ ((hPLchar z).mp hl).2
            exact False.elim (not_le_of_gt (hαβ.trans hβ1) hh)
          · exact False.elim (h01 (((hV0char z).mp hv).symm.trans ((hV1char z).mp hr)))
          · exact mem_singleton_iff.mpr (Prod.ext ((hV1char z).mp hr) ((hBTchar z).mp hb))
        · intro hz
          obtain rfl := mem_singleton_iff.mp hz
          exact ⟨Or.inr ((hBTchar _).mpr rfl),(hV1char _).mpr rfl⟩
      obtain ⟨F2,hF2,hF20,hF21,hF2r⟩ := join F1 V1 hF1 hV1 (hF11'.trans hV10.symm) hmeet2
      have hF21' : F2 1 = (1,1) := hF21.trans hV11
      have hmeet3 : range F2 ∩ range PR = {F2 1} := by
        rw [hF2r,hF1r,hF0r,hF21']
        ext z
        constructor
        · rintro ⟨((hl | hv) | hb) | hr,hp⟩
          · have hh : β ≤ α := ((hPRchar z).mp hp).2.trans ((hPLchar z).mp hl).2
            exact False.elim (not_le_of_gt hαβ hh)
          · have hh : β ≤ (0:Interval) := ((hV0char z).mp hv) ▸ ((hPRchar z).mp hp).2
            exact False.elim (not_le_of_gt (hα0.trans hαβ) hh)
          · exact False.elim (h01 (((hBTchar z).mp hb).symm.trans ((hPRchar z).mp hp).1))
          · exact mem_singleton_iff.mpr (Prod.ext ((hV1char z).mp hr) ((hPRchar z).mp hp).1)
        · intro hz
          obtain rfl := mem_singleton_iff.mp hz
          exact ⟨Or.inr ((hV1char _).mpr rfl),(hPRchar _).mpr ⟨rfl,hβ1.le⟩⟩
      obtain ⟨G,hG,hG0,hG1,hGr⟩ := join F2 PR hF2 hPR (hF21'.trans hPR0.symm) hmeet3
      refine ⟨G,hG,hG0.trans (hF20.trans (hF10.trans (hF00.trans hPL0))),hG1.trans hPR1,?_⟩
      rw [hGr,hF2r,hF1r,hF0r]
      ext z
      simp only [mem_union,mem_setOf_eq,hPLchar,hV0char,hBTchar,hV1char,hPRchar]
      tauto
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `parameter_boundary_complement
      let some value := localDecl.value? | Lean.throwError "Missing local parameter_boundary_complement value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected parameter_boundary_complement axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS parameter_boundary_complement: {found.toList}"
    let join_actual_arcs : ∀ (L R : C(Interval,↥Q)), IsEmbedding L → IsEmbedding R →
        L 1 = R 0 → range L ∩ range R = {L 1} →
        ∃ F : C(Interval,↥Q), IsEmbedding F ∧ F 0 = L 0 ∧ F 1 = R 1 ∧
          range F = range L ∪ range R := by
      intro L R hL hR hend hmeet
      let p : Interval × PUnit ≃ₜ Interval := Homeomorph.prodPUnit Interval
      let flip : Interval × PUnit ≃ₜ Interval := p.trans unitInterval.symmHomeomorph
      let LF : Interval × PUnit → ↥Q := L ∘ flip
      let RF : Interval × PUnit → ↥Q := R ∘ p
      have hLF : IsEmbedding LF := hL.comp flip.isEmbedding
      have hRF : IsEmbedding RF := hR.comp p.isEmbedding
      have hLFr : range LF = range L := flip.surjective.range_comp L
      have hRFr : range RF = range R := p.surjective.range_comp R
      have hLzero (w : PUnit) : LF (0,w) = L 1 := by
        change L (unitInterval.symm 0) = L 1
        rw [unitInterval.symm_zero]
      have hseam (w : PUnit) : LF (0,w) = RF (0,w) := (hLzero w).trans hend
      have hmeet' : range LF ∩ range RF = range (fun w : PUnit => LF (0,w)) := by
        rw [hLFr,hRFr,hmeet]
        ext y
        constructor
        · intro hy
          obtain rfl := mem_singleton_iff.mp hy
          exact ⟨PUnit.unit,hLzero _⟩
        · rintro ⟨w,hw⟩
          exact mem_singleton_iff.mpr (hw.symm.trans (hLzero w))
      obtain ⟨G,hG,hG0,hG1,hGm,hGr,hGrow⟩ :=
        source_glue_two_surface_strips LF RF hLF hRF hseam hmeet'
      let F : C(Interval,↥Q) := ⟨fun u => G (u,PUnit.unit),by fun_prop⟩
      have hF : IsEmbedding F := hG.comp (isEmbedding_prodMkLeft PUnit.unit)
      have hFr : range F = range G := by
        ext y
        constructor
        · rintro ⟨u,rfl⟩
          exact ⟨(u,PUnit.unit),rfl⟩
        · rintro ⟨⟨u,w⟩,he⟩
          cases w
          exact ⟨u,he⟩
      refine ⟨F,hF,?_,?_,hFr.trans (hGr.trans (congrArg₂ Set.union hLFr hRFr))⟩
      · change G (0,PUnit.unit) = L 0
        rw [hG0]
        change L (unitInterval.symm 1) = L 0
        rw [unitInterval.symm_one]
      · exact hG1 PUnit.unit
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `join_actual_arcs
      let some value := localDecl.value? | Lean.throwError "Missing local join_actual_arcs value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected join_actual_arcs axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS join_actual_arcs: {found.toList}"
    let actual_seed_boundary_pair : ∃ gSeed : C(Interval,↥Q), IsEmbedding gSeed ∧
        qGate 0 = gSeed 0 ∧ qGate 1 = gSeed 1 ∧
        Dseed '' {z | z.val ∈ Metric.sphere (0:Plane) 1} = range qGate ∪ range gSeed ∧
        (∀ s t : Interval, qGate s = gSeed t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) ∧
        range gSeed = Hseed '' {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨
          (z.2 = 1 ∧ (z.1 ≤ min (gateClock 0) (gateClock 1) ∨ max (gateClock 0) (gateClock 1) ≤ z.1))} := by
      let α : Interval := min (gateClock 0) (gateClock 1)
      let β : Interval := max (gateClock 0) (gateClock 1)
      have hα0 : 0 < α := lt_min (hGateClockInterior 0).1 (hGateClockInterior 1).1
      have hβ1 : β < 1 := max_lt (hGateClockInterior 0).2 (hGateClockInterior 1).2
      have hαβ : α < β := min_lt_max.mpr hGateClockNe
      obtain ⟨G,hG,hG0,hG1,hGr⟩ :
          ∃ G : C(Interval,Interval × Interval), IsEmbedding G ∧
            G 0 = (gateClock 0,1) ∧ G 1 = (gateClock 1,1) ∧
            range G = {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ (z.2 = 1 ∧ (z.1 ≤ α ∨ β ≤ z.1))} := by
        obtain ⟨G,hG,hG0,hG1,hGr⟩ := parameter_boundary_complement α β hα0 hαβ hβ1
        by_cases hab : gateClock 0 < gateClock 1
        · have ha : α = gateClock 0 := min_eq_left hab.le
          have hb : β = gateClock 1 := max_eq_right hab.le
          exact ⟨G,hG,hG0.trans (Prod.ext ha rfl),hG1.trans (Prod.ext hb rfl),hGr⟩
        · have hba : gateClock 1 < gateClock 0 := lt_of_le_of_ne (le_of_not_gt hab) hGateClockNe.symm
          have ha : α = gateClock 1 := min_eq_right hba.le
          have hb : β = gateClock 0 := max_eq_left hba.le
          let GR : C(Interval,Interval × Interval) := ⟨G ∘ unitInterval.symm,by fun_prop⟩
          refine ⟨GR,hG.comp unitInterval.symmHomeomorph.isEmbedding,?_,?_,?_⟩
          · change G (unitInterval.symm 0) = _
            rw [unitInterval.symm_zero,hG1,hb]
          · change G (unitInterval.symm 1) = _
            rw [unitInterval.symm_one,hG0,ha]
          · exact (unitInterval.symmHomeomorph.surjective.range_comp G).trans hGr
      have hclockBounds (u : Interval) : α ≤ gateClock u ∧ gateClock u ≤ β := by
        have hh : gateClock u ∈ uIcc (gateClock 0) (gateClock 1) := hGateClockRange ▸ mem_range_self u
        exact hh
      let gSeed : C(Interval,↥Q) := Hseed.comp G
      have hgSeed : IsEmbedding gSeed := hHseed.comp hG
      have hg0 : qGate 0 = gSeed 0 := by
        change qGate 0 = Hseed (G 0)
        rw [hG0]
        exact (hGateClockEq 0).symm
      have hg1 : qGate 1 = gSeed 1 := by
        change qGate 1 = Hseed (G 1)
        rw [hG1]
        exact (hGateClockEq 1).symm
      have hboundary : Dseed '' {z | z.val ∈ Metric.sphere (0:Plane) 1} = range qGate ∪ range gSeed := by
        rw [hDseedbd]
        ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          change z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨ z.2 = 1 at hz
          by_cases hc : z.2 = 1 ∧ z.1 ∈ Icc α β
          · left
            have hm : z.1 ∈ range gateClock := hGateClockRange ▸ hc.2
            obtain ⟨u,hu⟩ := hm
            exact ⟨u,(hGateClockEq u).symm.trans (congrArg Hseed (Prod.ext hu hc.1.symm))⟩
          · right
            have hm : z ∈ range G := by
              rw [hGr]
              rcases hz with h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl h))
              · refine Or.inr (Or.inr (Or.inr ⟨h,?_⟩))
                by_cases hl : z.1 ≤ α
                · exact Or.inl hl
                · right
                  by_contra hb
                  exact hc ⟨h,(not_le.mp hl).le,(not_le.mp hb).le⟩
            obtain ⟨u,hu⟩ := hm
            exact ⟨u,congrArg Hseed hu⟩
        · rintro (⟨u,rfl⟩ | ⟨u,rfl⟩)
          · exact ⟨(gateClock u,1),Or.inr (Or.inr (Or.inr rfl)),hGateClockEq u⟩
          · refine ⟨G u,?_,rfl⟩
            have hh : G u ∈ range G := mem_range_self u
            rw [hGr] at hh
            rcases hh with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h.1))
      have hcollision (s t : Interval) (he : qGate s = gSeed t) :
          (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
        have hp : (gateClock s,1) = G t := hHseed.injective ((hGateClockEq s).trans he)
        have hm : (gateClock s,1) ∈ range G := ⟨t,hp.symm⟩
        rw [hGr] at hm
        have hend : gateClock s = gateClock 0 ∨ gateClock s = gateClock 1 := by
          rcases hm with h | h | h | h
          · exact False.elim ((ne_of_gt (hGateClockInterior s).1) h)
          · exact False.elim ((ne_of_lt (hGateClockInterior s).2) h)
          · have hh : (1:Interval) ≠ 0 := by
              intro he
              have hh : (1:ℝ) = 0 := congrArg (fun u : Interval => (u:ℝ)) he
              norm_num at hh
            exact False.elim (hh h)
          · have ha : gateClock s = α ∨ gateClock s = β := h.2.elim
              (fun hh => Or.inl (le_antisymm hh (hclockBounds s).1))
              (fun hh => Or.inr (le_antisymm (hclockBounds s).2 hh))
            by_cases hab : gateClock 0 ≤ gateClock 1
            · rcases ha with ha | hb
              · exact Or.inl (ha.trans (min_eq_left hab))
              · exact Or.inr (hb.trans (max_eq_right hab))
            · rcases ha with ha | hb
              · exact Or.inr (ha.trans (min_eq_right (le_of_not_ge hab)))
              · exact Or.inl (hb.trans (max_eq_left (le_of_not_ge hab)))
        rcases hend with h | h
        · left
          refine ⟨hGateClock.injective h,hG.injective ?_⟩
          have hh : (gateClock s,(1:Interval)) = (gateClock 0,1) := Prod.ext h rfl
          exact (hp.symm.trans hh).trans hG0.symm
        · right
          refine ⟨hGateClock.injective h,hG.injective ?_⟩
          have hh : (gateClock s,(1:Interval)) = (gateClock 1,1) := Prod.ext h rfl
          exact (hp.symm.trans hh).trans hG1.symm
      refine ⟨gSeed,hgSeed,hg0,hg1,hboundary,hcollision,?_⟩
      change range (Hseed ∘ G) = _
      simp only [Set.range_comp,hGr,α,β]
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_seed_boundary_pair
      let some value := localDecl.value? | Lean.throwError "Missing local actual_seed_boundary_pair value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_seed_boundary_pair axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_seed_boundary_pair: {found.toList}"
    obtain ⟨gSeed,hgSeed,hgSeed0,hgSeed1,hSeedBoundary,hSeedCollision,hSeedComplementRange⟩ := actual_seed_boundary_pair
    let actual_attached_disk : ∃ Dcap : C(Metric.closedBall (0:Plane) 1,↥Q), IsEmbedding Dcap ∧
        range Dcap = range Hseed ∪ range Ncap ∧
        Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} =
          range gSeed ∪ range (fun u : Interval => attachStrip (0,u)) ∪
            range (fun u : Interval => attachStrip (1,u)) ∪
            range (fun u : Interval => attachStrip (u,1)) := by
      have hkernel (t u t' u' : Interval) : attachStrip (t,u) = attachStrip (t',u') ↔
          t = t' ∧ (u = u' ∨ ActualHarerDiskGluing.collapsedEndpoint false false t) := by
        constructor
        · intro he
          have hh : (t,u) = (t',u') := hAttachStrip.injective he
          exact ⟨congrArg Prod.fst hh,Or.inl (congrArg Prod.snd hh)⟩
        · rintro ⟨rfl,he | hc⟩
          · exact congrArg attachStrip (Prod.ext rfl he)
          · simp [ActualHarerDiskGluing.collapsedEndpoint] at hc
      obtain ⟨Dcap,hDcap,hDcaprange,hDcapbd⟩ :=
        ActualHarerDiskGluing.actual_disk_attach_half_collar_with_optional_endpoint_collapse
          qGate gSeed Dseed hqGate hgSeed hDseed hgSeed0 hgSeed1 hSeedBoundary hSeedCollision
          attachStrip false false (by simp) hAttachCenter hkernel hAttachMeet
      exact ⟨Dcap,hDcap,by simpa only [hDseedrange,hAttachRange] using hDcaprange,hDcapbd⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_attached_disk
      let some value := localDecl.value? | Lean.throwError "Missing local actual_attached_disk value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_attached_disk axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_attached_disk: {found.toList}"
    obtain ⟨Dcap,hDcap,hDcaprange,hDcapbd⟩ := actual_attached_disk
    let ordered_actual_gate : ∃ (gcLo gcHi : Interval) (c : C(Interval,Interval))
        (Astrip : C(Interval × Interval,↥Q)),
        0 < gcLo ∧ gcLo < gcHi ∧ gcHi < 1 ∧ gcLo = min (gateClock 0) (gateClock 1) ∧
        gcHi = max (gateClock 0) (gateClock 1) ∧ IsEmbedding Astrip ∧ range Astrip = range attachStrip ∧
        c 0 = gcLo ∧ c 1 = gcHi ∧ (∀ u, Astrip (u,0) = Hseed (c u,1)) ∧
        (∀ t u v w, Astrip (t,u) = Hseed (v,w) ↔ u = 0 ∧ v = c t ∧ w = 1) ∧
        ((∀ z, Astrip z = attachStrip z) ∨ (∀ z, Astrip z = attachStrip (unitInterval.symm z.1,z.2))) := by
      have hme : range attachStrip ∩ range Hseed = range qGate := by
        rw [← hDseedrange]
        exact hAttachMeet
      have hcross (t u v w : Interval) : attachStrip (t,u) = Hseed (v,w) ↔
          u = 0 ∧ v = gateClock t ∧ w = 1 := by
        constructor
        · intro he
          have hm : attachStrip (t,u) ∈ range qGate := hme ▸
            (show attachStrip (t,u) ∈ range attachStrip ∩ range Hseed from ⟨mem_range_self (t,u),⟨(v,w),he.symm⟩⟩)
          obtain ⟨r,hr⟩ := hm
          have hp : (r,(0:Interval)) = (t,u) := hAttachStrip.injective ((hAttachCenter r).trans hr)
          have hw : u = 0 := (congrArg Prod.snd hp).symm
          have hz0 : (t,u) = (t,(0:Interval)) := Prod.ext rfl hw
          have hq : Hseed (v,w) = Hseed (gateClock t,1) :=
            (he.symm.trans (congrArg attachStrip hz0)).trans ((hAttachCenter t).trans (hGateClockEq t).symm)
          have hz : (v,w) = (gateClock t,1) := hHseed.injective hq
          exact ⟨hw,congrArg Prod.fst hz,congrArg Prod.snd hz⟩
        · rintro ⟨rfl,rfl,rfl⟩
          exact (hAttachCenter t).trans (hGateClockEq t).symm
      by_cases hab : gateClock 0 < gateClock 1
      · exact ⟨gateClock 0,gateClock 1,gateClock,attachStrip,(hGateClockInterior 0).1,hab,(hGateClockInterior 1).2,(min_eq_left hab.le).symm,
          (max_eq_right hab.le).symm,hAttachStrip,rfl,rfl,rfl,
          fun u => (hAttachCenter u).trans (hGateClockEq u).symm,hcross,Or.inl (fun z => rfl)⟩
      · have hba : gateClock 1 < gateClock 0 := lt_of_le_of_ne (le_of_not_gt hab) hGateClockNe.symm
        let p : Interval × Interval ≃ₜ Interval × Interval :=
          unitInterval.symmHomeomorph.prodCongr (Homeomorph.refl Interval)
        let A : C(Interval × Interval,↥Q) := ⟨attachStrip ∘ p,by fun_prop⟩
        let c : C(Interval,Interval) := ⟨gateClock ∘ unitInterval.symm,by fun_prop⟩
        refine ⟨gateClock 1,gateClock 0,c,A,(hGateClockInterior 1).1,hba,(hGateClockInterior 0).2,(min_eq_right hba.le).symm,
          (max_eq_left hba.le).symm,hAttachStrip.comp p.isEmbedding,
          p.surjective.range_comp attachStrip,?_,?_,?_,?_,?_⟩
        · change gateClock (unitInterval.symm 0) = gateClock 1
          rw [unitInterval.symm_zero]
        · change gateClock (unitInterval.symm 1) = gateClock 0
          rw [unitInterval.symm_one]
        · intro u
          exact (hAttachCenter (unitInterval.symm u)).trans (hGateClockEq (unitInterval.symm u)).symm
        · intro t u v w
          exact hcross (unitInterval.symm t) u v w
        · exact Or.inr (fun z => rfl)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `ordered_actual_gate
      let some value := localDecl.value? | Lean.throwError "Missing local ordered_actual_gate value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected ordered_actual_gate axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS ordered_actual_gate: {found.toList}"
    obtain ⟨gateLo,gateHi,gateClockOrdered,stripOrdered,hGateLo0,hGateLoHi,hGateHi1,
      hGateLoMin,hGateHiMax,hStripOrdered,hStripOrderedRange,hGateOrdered0,hGateOrdered1,
      hStripOrderedCenter,hStripOrderedKernel,hOrderedShape⟩ := ordered_actual_gate
    let actual_free_boundary_arc : ∃ free : C(Interval,↥Q), IsEmbedding free ∧
        free 0 = Hseed (0,1) ∧ free 1 = Hseed (1,1) ∧
        range free =
          Hseed '' {z | z.2 = 1 ∧ z.1 ≤ gateLo} ∪ range (fun u : Interval => stripOrdered (0,u)) ∪
            range (fun u : Interval => stripOrdered (u,1)) ∪ range (fun u : Interval => stripOrdered (1,u)) ∪
            Hseed '' {z | z.2 = 1 ∧ gateHi ≤ z.1} := by
      obtain ⟨cl,hcl,hcl0,hcl1,hclr,hclf⟩ := source_affine_subinterval 0 gateLo hGateLo0
      obtain ⟨cr,hcr,hcr0,hcr1,hcrr,hcrf⟩ := source_affine_subinterval gateHi 1 hGateHi1
      let PL : C(Interval,↥Q) := ⟨fun u => Hseed (cl u,1),by fun_prop⟩
      let V0 : C(Interval,↥Q) := ⟨fun u => stripOrdered (0,u),by fun_prop⟩
      let AF : C(Interval,↥Q) := ⟨fun u => stripOrdered (u,1),by fun_prop⟩
      let V1 : C(Interval,↥Q) := ⟨fun u => stripOrdered (1,unitInterval.symm u),by fun_prop⟩
      let PR : C(Interval,↥Q) := ⟨fun u => Hseed (cr u,1),by fun_prop⟩
      have hPL : IsEmbedding PL := hHseed.comp ((isEmbedding_prodMkLeft (1:Interval)).comp hcl)
      have hV0 : IsEmbedding V0 := hStripOrdered.comp (isEmbedding_prodMkRight (0:Interval))
      have hAF : IsEmbedding AF := hStripOrdered.comp (isEmbedding_prodMkLeft (1:Interval))
      have hV1 : IsEmbedding V1 := hStripOrdered.comp
        ((isEmbedding_prodMkRight (1:Interval)).comp unitInterval.symmHomeomorph.isEmbedding)
      have hPR : IsEmbedding PR := hHseed.comp ((isEmbedding_prodMkLeft (1:Interval)).comp hcr)
      have hPL0 : PL 0 = Hseed (0,1) := by simp [PL,hcl0]
      have hPL1 : PL 1 = Hseed (gateLo,1) := by simp [PL,hcl1]
      have hV00 : V0 0 = Hseed (gateLo,1) := (hStripOrderedCenter 0).trans (congrArg Hseed (Prod.ext hGateOrdered0 rfl))
      have hV01 : V0 1 = stripOrdered (0,1) := rfl
      have hAF0 : AF 0 = stripOrdered (0,1) := rfl
      have hAF1 : AF 1 = stripOrdered (1,1) := rfl
      have hV10 : V1 0 = stripOrdered (1,1) := by simp [V1]
      have hV11 : V1 1 = Hseed (gateHi,1) := by
        change stripOrdered (1,unitInterval.symm 1) = _
        rw [unitInterval.symm_one,hStripOrderedCenter,hGateOrdered1]
      have hPR0 : PR 0 = Hseed (gateHi,1) := by simp [PR,hcr0]
      have hPR1 : PR 1 = Hseed (1,1) := by simp [PR,hcr1]
      have hclBound (u : Interval) : cl u ≤ gateLo := (hclr ▸ mem_range_self u).2
      have hcrBound (u : Interval) : gateHi ≤ cr u := (hcrr ▸ mem_range_self u).1
      have h01 : (0:Interval) ≠ 1 := by
        intro he
        have hh : (0:ℝ) = 1 := congrArg (fun u : Interval => (u:ℝ)) he
        norm_num at hh
      have hmeet0 : range PL ∩ range V0 = {PL 1} := by
        ext y
        constructor
        · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
          have he : stripOrdered (0,t) = Hseed (cl s,1) := ht.trans hs.symm
          have hc := (hStripOrderedKernel 0 t (cl s) 1).mp he
          apply mem_singleton_iff.mpr
          exact ht.symm.trans ((congrArg (fun u => stripOrdered (0,u)) hc.1).trans (hV00.trans hPL1.symm))
        · intro hy
          obtain rfl := mem_singleton_iff.mp hy
          exact ⟨mem_range_self 1,⟨0,hV00.trans hPL1.symm⟩⟩
      obtain ⟨F0,hF0,hF00,hF01,hF0r⟩ := join_actual_arcs PL V0 hPL hV0 (hPL1.trans hV00.symm) hmeet0
      have hF01' : F0 1 = stripOrdered (0,1) := hF01.trans hV01
      have hmeet1 : range F0 ∩ range AF = {F0 1} := by
        rw [hF0r,hF01']
        ext y
        constructor
        · rintro ⟨(⟨s,hs⟩ | ⟨s,hs⟩),⟨t,ht⟩⟩
          · have he : stripOrdered (t,1) = Hseed (cl s,1) := ht.trans hs.symm
            exact False.elim (h01 ((hStripOrderedKernel t 1 (cl s) 1).mp he).1.symm)
          · have he : (0,s) = (t,1) := hStripOrdered.injective (hs.trans ht.symm)
            have hw : s = 1 := congrArg Prod.snd he
            exact mem_singleton_iff.mpr (hs.symm.trans (congrArg (fun u => stripOrdered (0,u)) hw))
        · intro hy
          obtain rfl := mem_singleton_iff.mp hy
          exact ⟨Or.inr (mem_range_self 1),mem_range_self 0⟩
      obtain ⟨F1,hF1,hF10,hF11,hF1r⟩ := join_actual_arcs F0 AF hF0 hAF (hF01'.trans hAF0.symm) hmeet1
      have hF11' : F1 1 = stripOrdered (1,1) := hF11.trans hAF1
      have hmeet2 : range F1 ∩ range V1 = {F1 1} := by
        rw [hF1r,hF0r,hF11']
        ext y
        constructor
        · rintro ⟨((⟨s,hs⟩ | ⟨s,hs⟩) | ⟨s,hs⟩),⟨t,ht⟩⟩
          · have he : stripOrdered (1,unitInterval.symm t) = Hseed (cl s,1) := ht.trans hs.symm
            have hc := (hStripOrderedKernel 1 (unitInterval.symm t) (cl s) 1).mp he
            have hb : cl s = gateHi := hc.2.1.trans hGateOrdered1
            exact False.elim (not_le_of_gt hGateLoHi (hb ▸ hclBound s))
          · have he : ((0:Interval),s) = (1,unitInterval.symm t) := hStripOrdered.injective (hs.trans ht.symm)
            exact False.elim (h01 (congrArg Prod.fst he))
          · have he : (s,1) = (1,unitInterval.symm t) := hStripOrdered.injective (hs.trans ht.symm)
            have hu : s = 1 := congrArg Prod.fst he
            exact mem_singleton_iff.mpr (hs.symm.trans (congrArg (fun u => stripOrdered (u,1)) hu))
        · intro hy
          obtain rfl := mem_singleton_iff.mp hy
          exact ⟨Or.inr (mem_range_self 1),⟨0,hV10⟩⟩
      obtain ⟨F2,hF2,hF20,hF21,hF2r⟩ := join_actual_arcs F1 V1 hF1 hV1 (hF11'.trans hV10.symm) hmeet2
      have hF21' : F2 1 = Hseed (gateHi,1) := hF21.trans hV11
      have hmeet3 : range F2 ∩ range PR = {F2 1} := by
        rw [hF2r,hF1r,hF0r,hF21']
        ext y
        constructor
        · rintro ⟨(((⟨s,hs⟩ | ⟨s,hs⟩) | ⟨s,hs⟩) | ⟨s,hs⟩),⟨t,ht⟩⟩
          · have he : (cl s,(1:Interval)) = (cr t,1) := hHseed.injective (hs.trans ht.symm)
            have hx : cl s = cr t := congrArg Prod.fst he
            exact False.elim (not_le_of_gt hGateLoHi ((hcrBound t).trans (hx ▸ hclBound s)))
          · have he : stripOrdered (0,s) = Hseed (cr t,1) := hs.trans ht.symm
            have hc := (hStripOrderedKernel 0 s (cr t) 1).mp he
            have ha : cr t = gateLo := hc.2.1.trans hGateOrdered0
            exact False.elim (not_le_of_gt hGateLoHi (ha ▸ hcrBound t))
          · have he : stripOrdered (s,1) = Hseed (cr t,1) := hs.trans ht.symm
            exact False.elim (h01 ((hStripOrderedKernel s 1 (cr t) 1).mp he).1.symm)
          · have he : stripOrdered (1,unitInterval.symm s) = Hseed (cr t,1) := hs.trans ht.symm
            have hc := (hStripOrderedKernel 1 (unitInterval.symm s) (cr t) 1).mp he
            exact mem_singleton_iff.mpr (hs.symm.trans
              ((congrArg (fun u => stripOrdered (1,u)) hc.1).trans ((hStripOrderedCenter 1).trans (congrArg Hseed (Prod.ext hGateOrdered1 rfl)))))
        · intro hy
          obtain rfl := mem_singleton_iff.mp hy
          exact ⟨Or.inr ⟨1,hV11⟩,⟨0,hPR0⟩⟩
      obtain ⟨free,hfree,hfree0,hfree1,hfreer⟩ := join_actual_arcs F2 PR hF2 hPR (hF21'.trans hPR0.symm) hmeet3
      have hprefix : range PL = Hseed '' {z | z.2 = 1 ∧ z.1 ≤ gateLo} := by
        ext y
        constructor
        · rintro ⟨u,rfl⟩
          exact ⟨(cl u,1),⟨rfl,hclBound u⟩,rfl⟩
        · rintro ⟨z,⟨hy,hx⟩,he⟩
          obtain ⟨u,hu⟩ : z.1 ∈ range cl := hclr ▸ (show z.1 ∈ Icc 0 gateLo from ⟨bot_le,hx⟩)
          exact ⟨u,(congrArg Hseed (Prod.ext hu hy.symm)).trans he⟩
      have hsuffix : range PR = Hseed '' {z | z.2 = 1 ∧ gateHi ≤ z.1} := by
        ext y
        constructor
        · rintro ⟨u,rfl⟩
          exact ⟨(cr u,1),⟨rfl,hcrBound u⟩,rfl⟩
        · rintro ⟨z,⟨hy,hx⟩,he⟩
          obtain ⟨u,hu⟩ : z.1 ∈ range cr := hcrr ▸ (show z.1 ∈ Icc gateHi 1 from ⟨hx,le_top⟩)
          exact ⟨u,(congrArg Hseed (Prod.ext hu hy.symm)).trans he⟩
      have hV1range : range V1 = range (fun u : Interval => stripOrdered (1,u)) :=
        unitInterval.symmHomeomorph.surjective.range_comp (fun u => stripOrdered (1,u))
      refine ⟨free,hfree,hfree0.trans (hF20.trans (hF10.trans (hF00.trans hPL0))),hfree1.trans hPR1,?_⟩
      rw [hfreer,hF2r,hF1r,hF0r,hprefix,hsuffix,hV1range]
      rfl
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_free_boundary_arc
      let some value := localDecl.value? | Lean.throwError "Missing local actual_free_boundary_arc value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_free_boundary_arc axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_free_boundary_arc: {found.toList}"
    obtain ⟨freeBoundary,hFreeBoundary,hFreeBoundary0,hFreeBoundary1,hFreeBoundaryRange⟩ := actual_free_boundary_arc
    let extend_actual_boundary : ∀ (Rbound : C(ActualHarerDiskGluing.squareBoundary,↥Q)),
        IsEmbedding Rbound →
        range Rbound = Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} →
        ∃ H : C(Interval × Interval,↥Q), IsEmbedding H ∧ range H = range Dcap ∧
          (∀ z (hz : z ∈ ActualHarerDiskGluing.squareBoundary), H z = Rbound ⟨z,hz⟩) := by
      intro Rbound hRbound hRboundrange
      classical
      obtain ⟨j,hj⟩ := ActualHarerDiskGluing.unit_disk_square_boundary_homeomorph
      let inc : C(Metric.sphere (0:Plane) 1,Metric.closedBall (0:Plane) 1) :=
        ⟨fun z => ⟨z.val,Metric.sphere_subset_closedBall z.property⟩,by fun_prop⟩
      let jc : C(Metric.sphere (0:Plane) 1,ActualHarerDiskGluing.squareBoundary) :=
        ⟨fun z => ⟨j (inc z),hj ▸ (show j (inc z) ∈ j '' {z | z.val ∈ Metric.sphere (0:Plane) 1}
            from ⟨inc z,z.property,rfl⟩)⟩,by fun_prop⟩
      have hjci : Function.Injective jc := by
        intro z w he
        have hh : inc z = inc w := j.injective (congrArg Subtype.val he)
        have hv : (inc z).val = (inc w).val := congrArg (fun v : Metric.closedBall (0:Plane) 1 => v.val) hh
        exact Subtype.ext hv
      have hjcs : Function.Surjective jc := by
        intro z
        have hm : z.val ∈ j '' {w | w.val ∈ Metric.sphere (0:Plane) 1} := hj.symm ▸ z.property
        obtain ⟨w,hw,he⟩ := hm
        exact ⟨⟨w.val,hw⟩,Subtype.ext he⟩
      let a : C(Metric.sphere (0:Plane) 1,↥Q) := Rbound.comp jc
      have hai : Function.Injective a := hRbound.injective.comp hjci
      have haRange : range a = Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} :=
        (hjcs.range_comp Rbound).trans hRboundrange
      have haD (z) : a z ∈ range Dcap := by
        obtain ⟨w,hw,he⟩ := haRange ▸ mem_range_self z
        exact ⟨w,he⟩
      let lift : C(Metric.sphere (0:Plane) 1,Metric.closedBall (0:Plane) 1) :=
        ⟨fun z => hDcap.toHomeomorph.symm ⟨a z,haD z⟩,
          hDcap.toHomeomorph.symm.continuous.comp (a.continuous.subtype_mk _)⟩
      have hlift (z) : Dcap (lift z) = a z := congrArg Subtype.val
        (hDcap.toHomeomorph.apply_symm_apply ⟨a z,haD z⟩)
      have hliftSphere (z) : (lift z).val ∈ Metric.sphere (0:Plane) 1 := by
        obtain ⟨w,hw,he⟩ := haRange ▸ mem_range_self z
        exact hDcap.injective ((hlift z).trans he.symm) ▸ hw
      let n : C(Metric.sphere (0:Plane) 1,Metric.sphere (0:Plane) 1) :=
        ⟨fun z => ⟨(lift z).val,hliftSphere z⟩,by fun_prop⟩
      have hni : Function.Injective n := by
        intro z w he
        apply hai
        rw [← hlift z,← hlift w]
        have hv : (n z).val = (n w).val := congrArg (fun v : Metric.sphere (0:Plane) 1 => v.val) he
        have hl : lift z = lift w := Subtype.ext hv
        exact congrArg Dcap hl
      have hns : Function.Surjective n := by
        intro z
        let w : Metric.closedBall (0:Plane) 1 := ⟨z.val,Metric.sphere_subset_closedBall z.property⟩
        have hm : Dcap w ∈ range a := haRange.symm ▸ (show Dcap w ∈ Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1}
          from ⟨w,z.property,rfl⟩)
        obtain ⟨p,hp⟩ := hm
        have hl : lift p = w := hDcap.injective ((hlift p).trans hp)
        have hv : (lift p).val = w.val := congrArg (fun v : Metric.closedBall (0:Plane) 1 => v.val) hl
        exact ⟨p,Subtype.ext hv⟩
      let e : Metric.sphere (0:Plane) 1 ≃ₜ Metric.sphere (0:Plane) 1 :=
        n.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective n ⟨hni,hns⟩)
      obtain ⟨F,hF⟩ := jordan_schoenflies_of_homeomorph
        RegionalEmbeddedFamily.unit_sphere_isJordanCurve RegionalEmbeddedFamily.unit_sphere_isJordanCurve e
      have hFsphere : F '' Metric.sphere (0:Plane) 1 = Metric.sphere (0:Plane) 1 := by
        ext z
        constructor
        · rintro ⟨x,hx,rfl⟩
          rw [hF ⟨x,hx⟩]
          exact (e ⟨x,hx⟩).property
        · intro hz
          refine ⟨e.symm ⟨z,hz⟩,(e.symm ⟨z,hz⟩).property,?_⟩
          rw [hF (e.symm ⟨z,hz⟩)]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)
      have hFclosed : F '' Metric.closedBall (0:Plane) 1 = Metric.closedBall (0:Plane) 1 := by
        calc
          F '' Metric.closedBall (0:Plane) 1 =
              F '' (inside (Metric.sphere (0:Plane) 1) ∪ Metric.sphere (0:Plane) 1) := by
            rw [RegionalEmbeddedFamily.inside_unit_sphere,Metric.ball_union_sphere]
          _ = inside (F '' Metric.sphere (0:Plane) 1) ∪ F '' Metric.sphere (0:Plane) 1 := by
            rw [image_union,CurveComplex.jordan_inside_homeomorph_image]
          _ = Metric.closedBall (0:Plane) 1 := by
            rw [hFsphere,RegionalEmbeddedFamily.inside_unit_sphere,Metric.ball_union_sphere]
      let K : C(Metric.closedBall (0:Plane) 1,Metric.closedBall (0:Plane) 1) :=
        ⟨fun z => ⟨F z.val,by
          have hm : F z.val ∈ F '' Metric.closedBall (0:Plane) 1 := ⟨z.val,z.property,rfl⟩
          exact (congrArg (fun U : Set Plane => F z.val ∈ U) hFclosed).mp hm⟩,by fun_prop⟩
      have hKi : Function.Injective K := by
        intro z w he
        exact Subtype.ext (F.injective (congrArg Subtype.val he))
      have hKs : Function.Surjective K := by
        intro z
        have hm : z.val ∈ F '' Metric.closedBall (0:Plane) 1 := hFclosed.symm ▸ z.property
        obtain ⟨w,hw,he⟩ := hm
        exact ⟨⟨w,hw⟩,Subtype.ext he⟩
      let J : C(Interval × Interval,Metric.closedBall (0:Plane) 1) := ⟨j.symm,j.symm.continuous⟩
      let H : C(Interval × Interval,↥Q) := Dcap.comp (K.comp J)
      have hH : IsEmbedding H := hDcap.comp
        (((K.continuous.isClosedEmbedding hKi).isEmbedding).comp j.symm.isEmbedding)
      have hHr : range H = range Dcap := (hKs.comp j.symm.surjective).range_comp Dcap
      refine ⟨H,hH,hHr,?_⟩
      intro z hz
      have hzSphere : (j.symm z).val ∈ Metric.sphere (0:Plane) 1 := by
        obtain ⟨w,hw,he⟩ := hj.symm ▸ hz
        have hh : j.symm z = w := j.injective ((j.apply_symm_apply z).trans he.symm)
        exact hh ▸ hw
      let p : Metric.sphere (0:Plane) 1 := ⟨(j.symm z).val,hzSphere⟩
      have hjc : jc p = ⟨z,hz⟩ := Subtype.ext (j.apply_symm_apply z)
      have hfp : F p.val = (lift p).val := hF p
      have hk : K (j.symm z) = lift p := Subtype.ext hfp
      change Dcap (K (j.symm z)) = Rbound ⟨z,hz⟩
      rw [hk,hlift]
      change Rbound (jc p) = Rbound ⟨z,hz⟩
      rw [hjc]
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `extend_actual_boundary
      let some value := localDecl.value? | Lean.throwError "Missing local extend_actual_boundary value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected extend_actual_boundary axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS extend_actual_boundary: {found.toList}"
    let actual_four_boundary_carrier :
        Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} =
          range (fun u : Interval => Hseed (u,0)) ∪ range (fun u : Interval => Hseed (0,u)) ∪
            range freeBoundary ∪ range (fun u : Interval => Hseed (1,u)) := by
      have hcomp : range gSeed = Hseed '' {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 = 0 ∨
          (z.2 = 1 ∧ (z.1 ≤ gateLo ∨ gateHi ≤ z.1))} := by
        simpa only [← hGateLoMin,← hGateHiMax] using hSeedComplementRange
      have hcr : range gSeed =
          range (fun u : Interval => Hseed (u,0)) ∪ range (fun u : Interval => Hseed (0,u)) ∪
            Hseed '' {z | z.2 = 1 ∧ z.1 ≤ gateLo} ∪ Hseed '' {z | z.2 = 1 ∧ gateHi ≤ z.1} ∪
              range (fun u : Interval => Hseed (1,u)) := by
        rw [hcomp]
        ext y
        constructor
        · rintro ⟨z,hz,he⟩
          rcases hz with hx | hx | hy | ⟨hy,hx | hx⟩
          · have hp : ((0:Interval),z.2) = z := Prod.ext hx.symm rfl
            exact Or.inl (Or.inl (Or.inl (Or.inr ⟨z.2,(congrArg Hseed hp).trans he⟩)))
          · have hp : ((1:Interval),z.2) = z := Prod.ext hx.symm rfl
            exact Or.inr ⟨z.2,(congrArg Hseed hp).trans he⟩
          · have hp : (z.1,(0:Interval)) = z := Prod.ext rfl hy.symm
            exact Or.inl (Or.inl (Or.inl (Or.inl ⟨z.1,(congrArg Hseed hp).trans he⟩)))
          · exact Or.inl (Or.inl (Or.inr ⟨z,⟨hy,hx⟩,he⟩))
          · exact Or.inl (Or.inr ⟨z,⟨hy,hx⟩,he⟩)
        · rintro ((((⟨u,rfl⟩ | ⟨u,rfl⟩) | ⟨z,hz,rfl⟩) | ⟨z,hz,rfl⟩) | ⟨u,rfl⟩)
          · exact ⟨(u,0),Or.inr (Or.inr (Or.inl rfl)),rfl⟩
          · exact ⟨(0,u),Or.inl rfl,rfl⟩
          · exact ⟨z,Or.inr (Or.inr (Or.inr ⟨hz.1,Or.inl hz.2⟩)),rfl⟩
          · exact ⟨z,Or.inr (Or.inr (Or.inr ⟨hz.1,Or.inr hz.2⟩)),rfl⟩
          · exact ⟨(1,u),Or.inr (Or.inl rfl),rfl⟩
      have hfaces :
          range (fun u : Interval => stripOrdered (0,u)) ∪ range (fun u : Interval => stripOrdered (1,u)) ∪
            range (fun u : Interval => stripOrdered (u,1)) =
          range (fun u : Interval => attachStrip (0,u)) ∪ range (fun u : Interval => attachStrip (1,u)) ∪
            range (fun u : Interval => attachStrip (u,1)) := by
        rcases hOrderedShape with he | he
        · have h0 : range (fun u : Interval => stripOrdered (0,u)) = range (fun u : Interval => attachStrip (0,u)) := by
            congr 1
            funext u
            exact he (0,u)
          have h1 : range (fun u : Interval => stripOrdered (1,u)) = range (fun u : Interval => attachStrip (1,u)) := by
            congr 1
            funext u
            exact he (1,u)
          have hf : range (fun u : Interval => stripOrdered (u,1)) = range (fun u : Interval => attachStrip (u,1)) := by
            congr 1
            funext u
            exact he (u,1)
          rw [h0,h1,hf]
        · have h0 : range (fun u : Interval => stripOrdered (0,u)) = range (fun u : Interval => attachStrip (1,u)) := by
            congr 1
            funext u
            simpa only [unitInterval.symm_zero] using he (0,u)
          have h1 : range (fun u : Interval => stripOrdered (1,u)) = range (fun u : Interval => attachStrip (0,u)) := by
            congr 1
            funext u
            simpa only [unitInterval.symm_one] using he (1,u)
          have hf : range (fun u : Interval => stripOrdered (u,1)) = range (fun u : Interval => attachStrip (u,1)) := by
            calc
              range (fun u : Interval => stripOrdered (u,1)) =
                  range ((fun u : Interval => attachStrip (u,1)) ∘ unitInterval.symm) := by
                congr 1
                funext u
                exact he (u,1)
              _ = _ := unitInterval.symmHomeomorph.surjective.range_comp (fun u : Interval => attachStrip (u,1))
          rw [h0,h1,hf,union_comm (range (fun u : Interval => attachStrip (1,u)))]
      rw [hDcapbd,hcr,hFreeBoundaryRange]
      ext y
      have hf := congrArg (fun U : Set ↥Q => y ∈ U) hfaces
      simp only [mem_union] at hf ⊢
      clear * - hf
      tauto
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_four_boundary_carrier
      let some value := localDecl.value? | Lean.throwError "Missing local actual_four_boundary_carrier value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_four_boundary_carrier axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_four_boundary_carrier: {found.toList}"
    let actual_four_edge_graph :
        (∀ s t, Hseed (s,0) = Hseed (0,t) ↔ s = 0 ∧ t = 0) ∧
        (∀ s t, Hseed (s,0) = Hseed (1,t) ↔ s = 1 ∧ t = 0) ∧
        (∀ s t, freeBoundary s = Hseed (0,t) ↔ s = 0 ∧ t = 1) ∧
        (∀ s t, freeBoundary s = Hseed (1,t) ↔ s = 1 ∧ t = 1) ∧
        (∀ s t, Hseed (s,0) ≠ freeBoundary t) ∧
        (∀ s t, Hseed (0,s) ≠ Hseed (1,t)) := by
      have h01 : (0:Interval) ≠ 1 := by
        intro he
        have hh : (0:ℝ) = 1 := congrArg (fun u : Interval => (u:ℝ)) he
        norm_num at hh
      have htopLeft (s t : Interval) (he : freeBoundary s = Hseed (0,t)) : s = 0 ∧ t = 1 := by
        have hm : freeBoundary s ∈ range freeBoundary := mem_range_self s
        rw [hFreeBoundaryRange] at hm
        rcases hm with (((⟨z,hz,hze⟩ | ⟨u,hu⟩) | ⟨u,hu⟩) | ⟨u,hu⟩) | ⟨z,hz,hze⟩
        · have hp : z = (0,t) := hHseed.injective (hze.trans he)
          have ht : t = 1 := (congrArg Prod.snd hp).symm.trans hz.1
          refine ⟨hFreeBoundary.injective ?_,ht⟩
          exact (he.trans (congrArg (fun v => Hseed (0,v)) ht)).trans hFreeBoundary0.symm
        · have hh := (hStripOrderedKernel 0 u 0 t).mp (hu.trans he)
          exact False.elim (hGateLo0.ne' (hh.2.1.trans hGateOrdered0).symm)
        · have hh := (hStripOrderedKernel u 1 0 t).mp (hu.trans he)
          exact False.elim (h01 hh.1.symm)
        · have hh := (hStripOrderedKernel 1 u 0 t).mp (hu.trans he)
          exact False.elim ((hGateLo0.trans hGateLoHi).ne' (hh.2.1.trans hGateOrdered1).symm)
        · have hp : z = (0,t) := hHseed.injective (hze.trans he)
          have ht : t = 1 := (congrArg Prod.snd hp).symm.trans hz.1
          refine ⟨hFreeBoundary.injective ?_,ht⟩
          exact (he.trans (congrArg (fun v => Hseed (0,v)) ht)).trans hFreeBoundary0.symm
      have htopRight (s t : Interval) (he : freeBoundary s = Hseed (1,t)) : s = 1 ∧ t = 1 := by
        have hm : freeBoundary s ∈ range freeBoundary := mem_range_self s
        rw [hFreeBoundaryRange] at hm
        rcases hm with (((⟨z,hz,hze⟩ | ⟨u,hu⟩) | ⟨u,hu⟩) | ⟨u,hu⟩) | ⟨z,hz,hze⟩
        · have hp : z = (1,t) := hHseed.injective (hze.trans he)
          have ht : t = 1 := (congrArg Prod.snd hp).symm.trans hz.1
          refine ⟨hFreeBoundary.injective ?_,ht⟩
          exact (he.trans (congrArg (fun v => Hseed (1,v)) ht)).trans hFreeBoundary1.symm
        · have hh := (hStripOrderedKernel 0 u 1 t).mp (hu.trans he)
          exact False.elim ((hGateLoHi.trans hGateHi1).ne (hGateOrdered0.symm.trans hh.2.1.symm))
        · have hh := (hStripOrderedKernel u 1 1 t).mp (hu.trans he)
          exact False.elim (h01 hh.1.symm)
        · have hh := (hStripOrderedKernel 1 u 1 t).mp (hu.trans he)
          exact False.elim (hGateHi1.ne (hGateOrdered1.symm.trans hh.2.1.symm))
        · have hp : z = (1,t) := hHseed.injective (hze.trans he)
          have ht : t = 1 := (congrArg Prod.snd hp).symm.trans hz.1
          refine ⟨hFreeBoundary.injective ?_,ht⟩
          exact (he.trans (congrArg (fun v => Hseed (1,v)) ht)).trans hFreeBoundary1.symm
      have hbottomFree (s t : Interval) (he : Hseed (s,0) = freeBoundary t) : False := by
        have hm : freeBoundary t ∈ range freeBoundary := mem_range_self t
        rw [hFreeBoundaryRange] at hm
        rcases hm with (((⟨z,hz,hze⟩ | ⟨u,hu⟩) | ⟨u,hu⟩) | ⟨u,hu⟩) | ⟨z,hz,hze⟩
        · have hp : z = (s,(0:Interval)) := hHseed.injective (hze.trans he.symm)
          exact h01 ((congrArg Prod.snd hp).symm.trans hz.1)
        · exact h01 ((hStripOrderedKernel 0 u s 0).mp (hu.trans he.symm)).2.2
        · exact h01 ((hStripOrderedKernel u 1 s 0).mp (hu.trans he.symm)).2.2
        · exact h01 ((hStripOrderedKernel 1 u s 0).mp (hu.trans he.symm)).2.2
        · have hp : z = (s,(0:Interval)) := hHseed.injective (hze.trans he.symm)
          exact h01 ((congrArg Prod.snd hp).symm.trans hz.1)
      refine ⟨?_,?_,?_,?_,hbottomFree,?_⟩
      · intro s t
        constructor
        · intro he
          have hp : (s,(0:Interval)) = (0,t) := hHseed.injective he
          exact ⟨congrArg Prod.fst hp,(congrArg Prod.snd hp).symm⟩
        · rintro ⟨rfl,rfl⟩
          rfl
      · intro s t
        constructor
        · intro he
          have hp : (s,(0:Interval)) = (1,t) := hHseed.injective he
          exact ⟨congrArg Prod.fst hp,(congrArg Prod.snd hp).symm⟩
        · rintro ⟨rfl,rfl⟩
          rfl
      · intro s t
        exact ⟨htopLeft s t,by rintro ⟨rfl,rfl⟩; exact hFreeBoundary0⟩
      · intro s t
        exact ⟨htopRight s t,by rintro ⟨rfl,rfl⟩; exact hFreeBoundary1⟩
      · intro s t he
        have hp : ((0:Interval),s) = (1,t) := hHseed.injective he
        exact h01 (congrArg Prod.fst hp)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_four_edge_graph
      let some value := localDecl.value? | Lean.throwError "Missing local actual_four_edge_graph value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_four_edge_graph axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_four_edge_graph: {found.toList}"
    let leftBoundary : C(Interval,↥Q) := ⟨fun u => Hseed (0,u),by fun_prop⟩
    let rightBoundary : C(Interval,↥Q) := ⟨fun u => Hseed (1,u),by fun_prop⟩
    have hLeftBoundary : IsEmbedding leftBoundary := hHseed.comp (isEmbedding_prodMkRight (0:Interval))
    have hRightBoundary : IsEmbedding rightBoundary := hHseed.comp (isEmbedding_prodMkRight (1:Interval))
    let actual_boundary_map : ∃ Rbound : C(ActualHarerDiskGluing.squareBoundary,↥Q), IsEmbedding Rbound ∧
        range Rbound = Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} ∧
        (∀ u, Rbound ⟨(u,0),Or.inr (Or.inr (Or.inl rfl))⟩ = d.sideArc u) ∧
        (∀ u, Rbound ⟨(0,u),Or.inl rfl⟩ = leftBoundary u) ∧
        (∀ u, Rbound ⟨(u,1),Or.inr (Or.inr (Or.inr rfl))⟩ = freeBoundary u) ∧
        (∀ u, Rbound ⟨(1,u),Or.inr (Or.inl rfl)⟩ = rightBoundary u) := by
      have hbl (s t : Interval) : d.sideArc s = leftBoundary t ↔ s = 0 ∧ t = 0 := by
        rw [← hHseedseam s]
        exact actual_four_edge_graph.1 s t
      have hbr (s t : Interval) : d.sideArc s = rightBoundary t ↔ s = 1 ∧ t = 0 := by
        rw [← hHseedseam s]
        exact actual_four_edge_graph.2.1 s t
      have htl (s t : Interval) : freeBoundary s = leftBoundary t ↔ s = 0 ∧ t = 1 :=
        actual_four_edge_graph.2.2.1 s t
      have htr (s t : Interval) : freeBoundary s = rightBoundary t ↔ s = 1 ∧ t = 1 :=
        actual_four_edge_graph.2.2.2.1 s t
      have hbt (s t : Interval) : d.sideArc s ≠ freeBoundary t := by
        rw [← hHseedseam s]
        exact actual_four_edge_graph.2.2.2.2.1 s t
      have hlr (s t : Interval) : leftBoundary s ≠ rightBoundary t :=
        actual_four_edge_graph.2.2.2.2.2 s t
      have hbottomRange : range (fun u : Interval => Hseed (u,0)) = range d.sideArc := by
        congr 1
        funext u
        exact hHseedseam u
      have hActualBoundaryUnion : Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} =
          range d.sideArc ∪ range leftBoundary ∪ range freeBoundary ∪ range rightBoundary := by
        simpa only [leftBoundary,rightBoundary,ContinuousMap.coe_mk,hbottomRange] using actual_four_boundary_carrier
      let mm : C((Interval ⊕ Interval) ⊕ (Interval ⊕ Interval),Interval × Interval) :=
        ⟨Sum.elim (Sum.elim (fun u => (u,0)) (fun u => (0,u)))
          (Sum.elim (fun u => (u,1)) (fun u => (1,u))),by fun_prop⟩
      have hmm (z : (Interval ⊕ Interval) ⊕ (Interval ⊕ Interval)) : mm z ∈ ActualHarerDiskGluing.squareBoundary := by
        rcases z with (u | u) | (u | u)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inr rfl))
        · exact Or.inr (Or.inl rfl)
      let m : C((Interval ⊕ Interval) ⊕ (Interval ⊕ Interval),ActualHarerDiskGluing.squareBoundary) :=
        ⟨fun z => ⟨mm z,hmm z⟩,mm.continuous.subtype_mk _⟩
      let n : C((Interval ⊕ Interval) ⊕ (Interval ⊕ Interval),↥Q) :=
        ⟨Sum.elim (Sum.elim (d.sideArc) leftBoundary) (Sum.elim freeBoundary rightBoundary),by fun_prop⟩
      have hms : Function.Surjective m := by
        intro z
        rcases z.property with hx | hx | hy | hy
        · exact ⟨Sum.inl (Sum.inr z.val.2),Subtype.ext (Prod.ext hx.symm rfl)⟩
        · exact ⟨Sum.inr (Sum.inr z.val.2),Subtype.ext (Prod.ext hx.symm rfl)⟩
        · exact ⟨Sum.inl (Sum.inl z.val.1),Subtype.ext (Prod.ext rfl hy.symm)⟩
        · exact ⟨Sum.inr (Sum.inl z.val.1),Subtype.ext (Prod.ext rfl hy.symm)⟩
      have h01 : (0:Interval) ≠ 1 := by
        intro he
        have hh : (0:ℝ) = 1 := congrArg (fun u : Interval => (u:ℝ)) he
        norm_num at hh
      have hlb s t : leftBoundary s = (d.sideArc) t ↔ s = 0 ∧ t = 0 := by
        rw [eq_comm,hbl]
        exact and_comm
      have hrb s t : rightBoundary s = (d.sideArc) t ↔ s = 0 ∧ t = 1 := by
        rw [eq_comm,hbr]
        exact and_comm
      have hlt s t : leftBoundary s = freeBoundary t ↔ s = 1 ∧ t = 0 := by
        rw [eq_comm,htl]
        exact and_comm
      have hrt s t : rightBoundary s = freeBoundary t ↔ s = 1 ∧ t = 1 := by
        rw [eq_comm,htr]
        exact and_comm
      have htb s t : freeBoundary s ≠ (d.sideArc) t := fun h => hbt t s h.symm
      have hrl s t : rightBoundary s ≠ leftBoundary t := fun h => hlr t s h.symm
      have hker (x y : (Interval ⊕ Interval) ⊕ (Interval ⊕ Interval)) : m x = m y ↔ n x = n y := by
        rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | (y | y)
        all_goals simp only [m,mm,n,ContinuousMap.coe_mk,Sum.elim_inl,Sum.elim_inr,
          Subtype.mk.injEq,Prod.mk.injEq,d.side_embedded.injective.eq_iff,hLeftBoundary.injective.eq_iff,
          hFreeBoundary.injective.eq_iff,hRightBoundary.injective.eq_iff,hbl,hbr,htl,htr,hlb,hrb,hlt,hrt,
          hbt,htb,hlr,hrl,h01,h01.symm,and_true,true_and,eq_self_iff_true]
        all_goals try simp only [eq_comm]
        all_goals clear * -
        all_goals tauto
      obtain ⟨R,hR,hRr,hRe⟩ := ActualHarerDiskGluing.compact_kernel_transport m n hms hker
      have hnr : range n = range (d.sideArc) ∪ range leftBoundary ∪ range freeBoundary ∪ range rightBoundary := by
        ext y
        constructor
        · rintro ⟨(u | u) | (u | u),rfl⟩
          · exact Or.inl (Or.inl (Or.inl (mem_range_self u)))
          · exact Or.inl (Or.inl (Or.inr (mem_range_self u)))
          · exact Or.inl (Or.inr (mem_range_self u))
          · exact Or.inr (mem_range_self u)
        · rintro (((⟨u,rfl⟩ | ⟨u,rfl⟩) | ⟨u,rfl⟩) | ⟨u,rfl⟩)
          · exact ⟨Sum.inl (Sum.inl u),rfl⟩
          · exact ⟨Sum.inl (Sum.inr u),rfl⟩
          · exact ⟨Sum.inr (Sum.inl u),rfl⟩
          · exact ⟨Sum.inr (Sum.inr u),rfl⟩
      exact ⟨R,hR,(hRr.trans hnr).trans hActualBoundaryUnion.symm,fun u => hRe (Sum.inl (Sum.inl u)),
        fun u => hRe (Sum.inl (Sum.inr u)),fun u => hRe (Sum.inr (Sum.inl u)),
        fun u => hRe (Sum.inr (Sum.inr u))⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_boundary_map
      let some value := localDecl.value? | Lean.throwError "Missing local actual_boundary_map value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_boundary_map axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_boundary_map: {found.toList}"
    obtain ⟨Rbound,hRbound,hRboundRange,hRboundBottom,hRboundLeft,hRboundFree,hRboundRight⟩ := actual_boundary_map
    have hP3seed : range P3 ⊆ range Hseed := by
      intro y hy
      rw [hHseedrange]
      exact Or.inl (Or.inr hy)
    have hNcapW : range Ncap ⊆ d.W := hNcapNarm.trans hNarmW
    have hNcapD : Disjoint (range Ncap) (range d.e) := hNarmD.mono_left hNcapNarm
    have hNcapB (z) : Ncap z ∉ B := by
      intro hb
      obtain ⟨w,hw⟩ := hNcapNarm (mem_range_self z)
      exact hNarmB w (hw.symm ▸ hb)
    have hNcapFuture : Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range Ncap) :=
      hNarmfuture.mono_right hNcapNarm
    have hHseedFuture : Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range Hseed) :=
      seed_future_q_clear.mono_left (by rintro y ⟨u,hu,he⟩; exact ⟨u,hNewt.trans hu,he⟩)
    let normalized_actual_collar : ∃ H : C(Interval × Interval,↥Q), IsEmbedding H ∧
        range H = range Dcap ∧
        (∀ u, H (u,0) = d.sideArc u) ∧ (∀ z, H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1) ∧
        range H ⊆ d.W ∧ range H ∩ range d.e = range d.sideArc ∧
        H '' ActualHarerDiskGluing.squareBoundary = Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} ∧
        Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range H) := by
      obtain ⟨H,hH,hHrange,hHboundary⟩ := extend_actual_boundary Rbound hRbound hRboundRange
      have hseam (u : Interval) : H (u,0) = d.sideArc u :=
        (hHboundary (u,0) (Or.inr (Or.inr (Or.inl rfl)))).trans (hRboundBottom u)
      have hleft (u : Interval) : H (0,u) = Hseed (0,u) :=
        (hHboundary (0,u) (Or.inl rfl)).trans (hRboundLeft u)
      have hright (u : Interval) : H (1,u) = Hseed (1,u) :=
        (hHboundary (1,u) (Or.inr (Or.inl rfl))).trans (hRboundRight u)
      have hcarrier : range H = range Hseed ∪ range Ncap := hHrange.trans hDcaprange
      have hBiff (z : Interval × Interval) : H z ∈ B ↔ z.1 = 0 ∨ z.1 = 1 := by
        constructor
        · intro hb
          have hm : H z ∈ range Hseed ∪ range Ncap := hcarrier ▸ mem_range_self z
          rcases hm with ⟨v,hv⟩ | ⟨v,hv⟩
          · rcases (hHseedB v).mp (hv.symm ▸ hb) with hx | hx
            · have hp : v = ((0:Interval),v.2) := Prod.ext hx rfl
              have hh : H z = H (0,v.2) :=
                (hv.symm.trans (congrArg Hseed hp)).trans (hleft v.2).symm
              exact Or.inl (congrArg Prod.fst (hH.injective hh))
            · have hp : v = ((1:Interval),v.2) := Prod.ext hx rfl
              have hh : H z = H (1,v.2) :=
                (hv.symm.trans (congrArg Hseed hp)).trans (hright v.2).symm
              exact Or.inr (congrArg Prod.fst (hH.injective hh))
          · exact False.elim (hNcapB v (hv.symm ▸ hb))
        · rintro (hx | hx)
          · have hp : z = ((0:Interval),z.2) := Prod.ext hx rfl
            rw [hp,hleft]
            exact (hHseedB (0,z.2)).mpr (Or.inl rfl)
          · have hp : z = ((1:Interval),z.2) := Prod.ext hx rfl
            rw [hp,hright]
            exact (hHseedB (1,z.2)).mpr (Or.inr rfl)
      have hW : range H ⊆ d.W := by
        rw [hcarrier]
        exact union_subset hHseedW hNcapW
      have hmeet : range H ∩ range d.e = range d.sideArc := by
        rw [hcarrier]
        ext y
        constructor
        · rintro ⟨(⟨v,hv⟩ | hn),he⟩
          · have hw : v.2 = 0 := (hHseedD v).mp (hv.symm ▸ he)
            have hp : (v.1,(0:Interval)) = v := Prod.ext rfl hw.symm
            exact ⟨v.1,((hHseedseam v.1).symm.trans (congrArg Hseed hp)).trans hv⟩
          · exact False.elim (disjoint_left.mp hNcapD hn he)
        · rintro ⟨u,rfl⟩
          have hD : Hseed (u,0) ∈ range d.e := (hHseedD (u,0)).mpr rfl
          exact ⟨Or.inl ⟨(u,0),hHseedseam u⟩,hHseedseam u ▸ hD⟩
      have hfuture : Disjoint ((fun u => q (d.xi u)) '' Ioi d.t) (range H) := by
        rw [hcarrier]
        exact hHseedFuture.union_right hNcapFuture
      have hboundary : H '' ActualHarerDiskGluing.squareBoundary =
          Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} := by
        rw [← hRboundRange]
        ext y
        constructor
        · rintro ⟨z,hz,he⟩
          exact ⟨⟨z,hz⟩,(hHboundary z hz).symm.trans he⟩
        · rintro ⟨z,he⟩
          exact ⟨z.val,z.property,(hHboundary z.val z.property).trans he⟩
      exact ⟨H,hH,hHrange,hseam,hBiff,hW,hmeet,hboundary,hfuture⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `normalized_actual_collar
      let some value := localDecl.value? | Lean.throwError "Missing local normalized_actual_collar value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected normalized_actual_collar axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS normalized_actual_collar: {found.toList}"
    obtain ⟨H,hH,hHrange,hHseam,hHB,hHW,hHe,hWholeBoundary,hHfuture⟩ := normalized_actual_collar
    let actual_free_boundary_q_trace :
        (∀ u ∈ Ioo d.s d.t, q (d.xi u) ∉ range freeBoundary) ∧
          q (d.xi d.t) ∈ range freeBoundary := by
      let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
      have hm0 : mid ≠ 0 := by
        intro he
        have hh := congrArg (fun u : Interval => (u:ℝ)) he
        norm_num [mid] at hh
      have hm1 : mid ≠ 1 := by
        intro he
        have hh := congrArg (fun u : Interval => (u:ℝ)) he
        norm_num [mid] at hh
      have hsymmMid : unitInterval.symm mid = mid := by
        apply Subtype.ext
        change 1-(mid:ℝ) = (mid:ℝ)
        norm_num [mid]
      have hAttachZero (v : Interval) : attachStrip (mid,v) = Ncap (v,⟨0,by norm_num⟩) :=
        hAttachLiteral (mid,v) ⟨0,by norm_num⟩ (by norm_num [mid])
      have hOrderedZero (v : Interval) : stripOrdered (mid,v) = Ncap (v,⟨0,by norm_num⟩) := by
        rcases hOrderedShape with he | he
        · exact (he (mid,v)).trans (hAttachZero v)
        · have hh := he (mid,v)
          rw [hsymmMid] at hh
          exact hh.trans (hAttachZero v)
      have hMidClockBounds : gateLo < gateClock mid ∧ gateClock mid < gateHi := by
        have hb : gateLo ≤ gateClock mid ∧ gateClock mid ≤ gateHi := by
          rw [hGateLoMin,hGateHiMax]
          have hm : gateClock mid ∈ uIcc (gateClock 0) (gateClock 1) := hGateClockRange ▸ mem_range_self mid
          exact hm
        have hnlo : gateClock mid ≠ gateLo := by
          intro he
          by_cases hc : gateClock 0 ≤ gateClock 1
          · have hh : gateClock mid = gateClock 0 := he.trans (hGateLoMin.trans (min_eq_left hc))
            exact hm0 (hGateClock.injective hh)
          · have hh : gateClock mid = gateClock 1 := he.trans (hGateLoMin.trans (min_eq_right (le_of_not_ge hc)))
            exact hm1 (hGateClock.injective hh)
        have hnhi : gateClock mid ≠ gateHi := by
          intro he
          by_cases hc : gateClock 0 ≤ gateClock 1
          · have hh : gateClock mid = gateClock 1 := he.trans (hGateHiMax.trans (max_eq_right hc))
            exact hm1 (hGateClock.injective hh)
          · have hh : gateClock mid = gateClock 0 := he.trans (hGateHiMax.trans (max_eq_left (le_of_not_ge hc)))
            exact hm0 (hGateClock.injective hh)
        exact ⟨lt_of_le_of_ne hb.1 hnlo.symm,lt_of_le_of_ne hb.2 hnhi⟩
      have hOldCenter : Hseed (gateClock mid,1) = q (d.xi bNew) := by
        calc
          Hseed (gateClock mid,1) = qGate mid := hGateClockEq mid
          _ = attachStrip (mid,0) := (hAttachCenter mid).symm
          _ = Ncap (0,⟨0,by norm_num⟩) := hAttachZero 0
          _ = q (d.xi bNew) := by simpa only [Icc.convexComb_zero] using hNcapcenter 0
      have hQinj : Function.Injective (fun u => q (d.xi u)) := d.q_embedded.injective.comp d.xi.injective
      have hBefore (u : Interval) (hu : d.s ≤ u ∧ u < bNew) : q (d.xi u) ∉ range freeBoundary := by
        obtain ⟨v,hv⟩ : q (d.xi u) ∈ range γNew := hγNewRange.symm ▸ ⟨u,⟨hu.1,hu.2.le⟩,rfl⟩
        have hv1 : v ≠ 1 := by
          intro he
          have hq : q (d.xi bNew) = q (d.xi u) := hγNew1.symm.trans (he ▸ hv)
          exact (ne_of_gt hu.2) (hQinj hq)
        obtain ⟨k,hk⟩ := hγNewP3 v
        have hpSeed : q (d.xi u) ∈ range Hseed := hP3seed ⟨(k,v),hk.trans hv⟩
        obtain ⟨z,hz⟩ := hpSeed
        have hzWidth : z.2 = v := seed_patch_preserves_width z (k,v) (hz.trans (hk.trans hv).symm)
        intro hm
        rw [hFreeBoundaryRange] at hm
        rcases hm with (((⟨w,hw,hwe⟩ | ⟨r,hr⟩) | ⟨r,hr⟩) | ⟨r,hr⟩) | ⟨w,hw,hwe⟩
        · have he : z = w := hHseed.injective (hz.trans hwe.symm)
          exact hv1 (hzWidth.symm.trans ((congrArg Prod.snd he).trans hw.1))
        · rcases hOrderedShape with hs | hs
          · have ha : attachStrip (0,r) = Ncap (r,⟨-1,by norm_num⟩) := hAttachLiteral (0,r) _ (by norm_num)
            have hN := ha.symm.trans ((hs (0,r)).symm.trans (hr.trans hz.symm))
            exact hv1 (hzWidth.symm.trans (hNcapkernel _ z hN).2)
          · have ha : attachStrip (1,r) = Ncap (r,⟨1,by norm_num⟩) := hAttachLiteral (1,r) _ (by norm_num)
            have hs' : stripOrdered (0,r) = attachStrip (1,r) := by simpa only [unitInterval.symm_zero] using hs (0,r)
            have hN := ha.symm.trans (hs'.symm.trans (hr.trans hz.symm))
            exact hv1 (hzWidth.symm.trans (hNcapkernel _ z hN).2)
        · rcases hOrderedShape with hs | hs
          · have ha : attachStrip (r,1) = Ncap (1,⟨2*(r:ℝ)-1,by constructor <;> linarith [r.property.1,r.property.2]⟩) :=
              hAttachLiteral (r,1) _ rfl
            have hN := ha.symm.trans ((hs (r,1)).symm.trans (hr.trans hz.symm))
            exact hv1 (hzWidth.symm.trans (hNcapkernel _ z hN).2)
          · have ha : attachStrip (unitInterval.symm r,1) =
                Ncap (1,⟨2*((unitInterval.symm r):ℝ)-1,by constructor <;> linarith [(unitInterval.symm r).property.1,(unitInterval.symm r).property.2]⟩) :=
              hAttachLiteral (unitInterval.symm r,1) _ rfl
            have hN := ha.symm.trans ((hs (r,1)).symm.trans (hr.trans hz.symm))
            exact hv1 (hzWidth.symm.trans (hNcapkernel _ z hN).2)
        · rcases hOrderedShape with hs | hs
          · have ha : attachStrip (1,r) = Ncap (r,⟨1,by norm_num⟩) := hAttachLiteral (1,r) _ (by norm_num)
            have hN := ha.symm.trans ((hs (1,r)).symm.trans (hr.trans hz.symm))
            exact hv1 (hzWidth.symm.trans (hNcapkernel _ z hN).2)
          · have ha : attachStrip (0,r) = Ncap (r,⟨-1,by norm_num⟩) := hAttachLiteral (0,r) _ (by norm_num)
            have hs' : stripOrdered (1,r) = attachStrip (0,r) := by simpa only [unitInterval.symm_one] using hs (1,r)
            have hN := ha.symm.trans (hs'.symm.trans (hr.trans hz.symm))
            exact hv1 (hzWidth.symm.trans (hNcapkernel _ z hN).2)
        · have he : z = w := hHseed.injective (hz.trans hwe.symm)
          exact hv1 (hzWidth.symm.trans ((congrArg Prod.snd he).trans hw.1))
      have hAfter (u : Interval) (hu : bNew ≤ u ∧ u < d.t) : q (d.xi u) ∉ range freeBoundary := by
        obtain ⟨v,hv⟩ : u ∈ range (Icc.convexComb bNew d.t) := by
          rw [Path.range_subpathAux,uIcc_of_le hNewt.le]
          exact ⟨hu.1,hu.2.le⟩
        have hv1 : v ≠ 1 := by
          intro he
          have hh : d.t = u := by simpa only [he,Icc.convexComb_one] using hv
          exact (ne_of_gt hu.2) hh
        have hec : stripOrdered (mid,v) = q (d.xi u) :=
          (hOrderedZero v).trans ((hNcapcenter v).trans (congrArg (fun u => q (d.xi u)) hv))
        have hNotOldTop (z : Interval × Interval) (hz : z.2 = 1 ∧ (z.1 ≤ gateLo ∨ gateHi ≤ z.1))
            (he : Hseed z = q (d.xi u)) : False := by
          by_cases huNew : bNew < u
          · exact disjoint_left.mp seed_future_q_clear ⟨u,huNew,rfl⟩ ⟨z,he⟩
          · have huu : u = bNew := le_antisymm (le_of_not_gt huNew) hu.1
            have hp : z = (gateClock mid,1) := hHseed.injective (he.trans ((huu ▸ hOldCenter).symm))
            have hx : z.1 = gateClock mid := congrArg Prod.fst hp
            rcases hz.2 with hlo | hhi
            · exact not_le_of_gt hMidClockBounds.1 (hx ▸ hlo)
            · exact not_le_of_gt hMidClockBounds.2 (hx ▸ hhi)
        intro hm
        rw [hFreeBoundaryRange] at hm
        rcases hm with (((⟨z,hz,he⟩ | ⟨r,hr⟩) | ⟨r,hr⟩) | ⟨r,hr⟩) | ⟨z,hz,he⟩
        · exact hNotOldTop z ⟨hz.1,Or.inl hz.2⟩ he
        · have hp : (mid,v) = (0,r) := hStripOrdered.injective (hec.trans hr.symm)
          exact hm0 (congrArg Prod.fst hp)
        · have hp : (mid,v) = (r,1) := hStripOrdered.injective (hec.trans hr.symm)
          exact hv1 (congrArg Prod.snd hp)
        · have hp : (mid,v) = (1,r) := hStripOrdered.injective (hec.trans hr.symm)
          exact hm1 (congrArg Prod.fst hp)
        · exact hNotOldTop z ⟨hz.1,Or.inr hz.2⟩ he
      refine ⟨?_,?_⟩
      · intro u hu
        by_cases hn : u < bNew
        · exact hBefore u ⟨hu.1.le,hn⟩
        · exact hAfter u ⟨le_of_not_gt hn,hu.2⟩
      · rw [hFreeBoundaryRange]
        exact Or.inl (Or.inl (Or.inr ⟨mid,(hOrderedZero 1).trans (by simpa only [Icc.convexComb_one] using hNcapcenter 1)⟩))
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `actual_free_boundary_q_trace
      let some value := localDecl.value? | Lean.throwError "Missing local actual_free_boundary_q_trace value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected actual_free_boundary_q_trace axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS actual_free_boundary_q_trace: {found.toList}"
    let literal_q_geometry :
        (∀ u ∈ Icc d.s d.t, q (d.xi u) ∈ range Dcap) ∧
          q (d.xi d.t) ∈ Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} ∧
          q (d.xi d.t) ∉ B ∧ q (d.xi d.t) ∉ range d.e ∧
          (∀ u ∈ Ioo d.s d.t, q (d.xi u) ∉ Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1}) := by
      have hclock_interior (u : Interval) (hu : u ∈ Ioo (0:Interval) 1) : d.xi u ∈ Ioo (0:Interval) 1 := by
        rcases d.xi_original_clock with hx | hx
        · rw [hx]
          exact hu
        · rw [hx]
          change 0 < (1-(u:ℝ)) ∧ (1-(u:ℝ)) < 1
          have h0 : (0:ℝ) < u := hu.1
          have h1 : (u:ℝ) < 1 := hu.2
          constructor <;> linarith
      have hafter_disk (u : Interval) (hu : d.s < u) : q (d.xi u) ∉ range d.e := by
        intro hd
        have hm : q (d.xi u) ∈ range d.M.second := d.disk_q_trace ▸ ⟨hd,mem_range_self _⟩
        rw [d.second_trace] at hm
        obtain ⟨v,hv,he⟩ := hm
        have hEq : v = u := d.xi.injective (d.q_embedded.injective he)
        exact not_le_of_gt hu (hEq ▸ hv.2)
      have hcoverage (u : Interval) (hu : u ∈ Icc d.s d.t) : q (d.xi u) ∈ range Dcap := by
        rw [hDcaprange]
        by_cases hn : u ≤ bNew
        · left
          obtain ⟨v,hv⟩ : q (d.xi u) ∈ range γNew := hγNewRange.symm ▸ ⟨u,⟨hu.1,hn⟩,rfl⟩
          obtain ⟨k,hk⟩ := hγNewP3 v
          exact hP3seed ⟨(k,v),hk.trans hv⟩
        · right
          obtain ⟨v,hv⟩ : u ∈ range (Icc.convexComb bNew d.t) := by
            rw [Path.range_subpathAux,uIcc_of_le hNewt.le]
            exact ⟨(not_le.mp hn).le,hu.2⟩
          exact ⟨(v,⟨0,by norm_num⟩),(hNcapcenter v).trans (congrArg (fun u => q (d.xi u)) hv)⟩
      have hqB (u : Interval) (hu : u ∈ Ioo d.s d.t) : q (d.xi u) ∉ B :=
        d.q_interior (d.xi u) (hclock_interior u ⟨d.tail_order.1.trans hu.1,hu.2.trans d.tail_order.2.2⟩)
      have hstrict (u : Interval) (hu : u ∈ Ioo d.s d.t) :
          q (d.xi u) ∉ Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} := by
        rw [actual_four_boundary_carrier]
        rintro (((⟨v,hv⟩ | ⟨v,hv⟩) | hf) | ⟨v,hv⟩)
        · exact hafter_disk u hu.1 (hv ▸ (hHseedD (v,0)).mpr rfl)
        · exact hqB u hu (hv ▸ (hHseedB (0,v)).mpr (Or.inl rfl))
        · exact actual_free_boundary_q_trace.1 u hu hf
        · exact hqB u hu (hv ▸ (hHseedB (1,v)).mpr (Or.inr rfl))
      refine ⟨hcoverage,?_,?_,hafter_disk d.t d.tail_order.2.1,hstrict⟩
      · rw [actual_four_boundary_carrier]
        exact Or.inl (Or.inr actual_free_boundary_q_trace.2)
      · exact d.q_interior (d.xi d.t) (hclock_interior d.t
          ⟨d.tail_order.1.trans d.tail_order.2.1,d.tail_order.2.2⟩)
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `literal_q_geometry
      let some value := localDecl.value? | Lean.throwError "Missing local literal_q_geometry value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected literal_q_geometry axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS literal_q_geometry: {found.toList}"
    obtain ⟨hQcoverage,hQtBoundary,hQtB,hQtE,hQstrict⟩ := literal_q_geometry
    let literal_eta_lift : ∃ eta : C(Interval,Interval × Interval),
        ((eta 1).2 = 1 ∧ (eta 1).1 ∈ Ioo (0:Interval) 1) ∧
        (∀ u ∈ Ioo (0:Interval) 1, eta u ∈ Ioo (0:Interval) 1 ×ˢ Ioo (0:Interval) 1) ∧
        (∀ u, H (eta u) = q (d.xi (Icc.convexComb d.s d.t u))) := by
      let Lliteral : C(Interval,↥Q) := ⟨fun u => q (d.xi (Icc.convexComb d.s d.t u)),by fun_prop⟩
      have hLrange (u : Interval) : Lliteral u ∈ range H := by
        rw [hHrange]
        exact hQcoverage (Icc.convexComb d.s d.t u)
          ⟨Icc.le_convexComb d.tail_order.2.1.le u,Icc.convexComb_le d.tail_order.2.1.le u⟩
      have hH0 (u : Interval) : H (u,0) ∈ range d.e := by
        have hD : d.sideArc u ∈ range d.e := hHseedseam u ▸ (hHseedD (u,0)).mpr rfl
        exact (hHseam u).symm ▸ hD
      have hL1 : Lliteral 1 ∈ Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} := by
        simpa only [Lliteral,ContinuousMap.coe_mk,Icc.convexComb_one] using hQtBoundary
      have hLB : Lliteral 1 ∉ B := by
        simpa only [Lliteral,ContinuousMap.coe_mk,Icc.convexComb_one] using hQtB
      have hLE : Lliteral 1 ∉ range d.e := by
        simpa only [Lliteral,ContinuousMap.coe_mk,Icc.convexComb_one] using hQtE
      have hLi (u : Interval) (hu : u ∈ Ioo (0:Interval) 1) :
          Lliteral u ∉ Dcap '' {z | z.val ∈ Metric.sphere (0:Plane) 1} := by
        apply hQstrict (Icc.convexComb d.s d.t u)
        have hs : (d.s:ℝ) < d.t := d.tail_order.2.1
        have hu0 : (0:ℝ) < u := hu.1
        have hu1 : (u:ℝ) < 1 := hu.2
        have hp0 : 0 < ((d.t:ℝ)-d.s)*(u:ℝ) := mul_pos (sub_pos.mpr hs) hu0
        have hp1 : 0 < ((d.t:ℝ)-d.s)*(1-(u:ℝ)) := mul_pos (sub_pos.mpr hs) (sub_pos.mpr hu1)
        change (d.s:ℝ) < (Icc.convexComb d.s d.t u:ℝ) ∧ (Icc.convexComb d.s d.t u:ℝ) < d.t
        simp only [Set.Icc.coe_convexComb]
        constructor <;> nlinarith only [hp0,hp1]
      let eta : C(Interval,Interval × Interval) :=
        ⟨fun u => hH.toHomeomorph.symm ⟨Lliteral u,hLrange u⟩,
          hH.toHomeomorph.symm.continuous.comp (Lliteral.continuous.subtype_mk _)⟩
      have he (u) : H (eta u) = Lliteral u := congrArg Subtype.val
        (hH.toHomeomorph.apply_symm_apply ⟨Lliteral u,hLrange u⟩)
      have hlong (u : Interval) (hu : H (eta u) ∉ B) : (eta u).1 ∈ Ioo (0:Interval) 1 := by
        have hn : ¬ ((eta u).1 = 0 ∨ (eta u).1 = 1) := fun h => hu ((hHB (eta u)).mpr h)
        exact ⟨lt_of_le_of_ne (bot_le : 0 ≤ (eta u).1) (fun h => hn (Or.inl h.symm)),
          lt_of_le_of_ne (le_top : (eta u).1 ≤ 1) (fun h => hn (Or.inr h))⟩
      have hbd1 : eta 1 ∈ ActualHarerDiskGluing.squareBoundary := by
        obtain ⟨z,hz,heq⟩ : Lliteral 1 ∈ H '' ActualHarerDiskGluing.squareBoundary := hWholeBoundary.symm ▸ hL1
        have hh : z = eta 1 := hH.injective (heq.trans (he 1).symm)
        exact hh ▸ hz
      have hη1 : (eta 1).2 = 1 ∧ (eta 1).1 ∈ Ioo (0:Interval) 1 := by
        have hB : H (eta 1) ∉ B := (he 1).symm ▸ hLB
        have hE : H (eta 1) ∉ (range d.e) := (he 1).symm ▸ hLE
        have hl := hlong 1 hB
        refine ⟨?_,hl⟩
        rcases hbd1 with hx | hx | hy | hy
        · exact False.elim ((ne_of_gt hl.1) hx)
        · exact False.elim ((ne_of_lt hl.2) hx)
        · have hp : eta 1 = ((eta 1).1,(0:Interval)) := Prod.ext rfl hy
          exact False.elim (hE (hp.symm ▸ hH0 (eta 1).1))
        · exact hy
      have hinner (u : Interval) (hu : u ∈ Ioo (0:Interval) 1) :
          eta u ∈ Ioo (0:Interval) 1 ×ˢ Ioo (0:Interval) 1 := by
        have hn : eta u ∉ ActualHarerDiskGluing.squareBoundary := by
          intro hm
          exact hLi u hu (he u ▸ (hWholeBoundary ▸ mem_image_of_mem H hm))
        have hn0 : (eta u).1 ≠ 0 := fun h => hn (Or.inl h)
        have hn1 : (eta u).1 ≠ 1 := fun h => hn (Or.inr (Or.inl h))
        have hm0 : (eta u).2 ≠ 0 := fun h => hn (Or.inr (Or.inr (Or.inl h)))
        have hm1 : (eta u).2 ≠ 1 := fun h => hn (Or.inr (Or.inr (Or.inr h)))
        exact ⟨⟨lt_of_le_of_ne (bot_le : 0 ≤ (eta u).1) hn0.symm,
          lt_of_le_of_ne (le_top : (eta u).1 ≤ 1) hn1⟩,
          ⟨lt_of_le_of_ne (bot_le : 0 ≤ (eta u).2) hm0.symm,
          lt_of_le_of_ne (le_top : (eta u).2 ≤ 1) hm1⟩⟩
      exact ⟨eta,hη1,hinner,he⟩
    run_tac Lean.Elab.Tactic.withMainContext do
      let localDecl ← Lean.Meta.getLocalDeclFromUserName `literal_eta_lift
      let some value := localDecl.value? | Lean.throwError "Missing local literal_eta_lift value"
      let value ← Lean.instantiateMVars value
      let mut found : Lean.NameSet := {}
      for n in value.getUsedConstants do
        for ax in (← Lean.collectAxioms n) do found := found.insert ax
      let allowed : List Lean.Name := [`propext,`Classical.choice,`Quot.sound]
      for ax in found.toList do
        unless allowed.contains ax do
          Lean.throwError "Unexpected literal_eta_lift axiom: {ax}"
      Lean.logInfo m!"LOCAL_ATOM_AXIOMS literal_eta_lift: {found.toList}"
    obtain ⟨eta,hetaone,hetainterior,hetaexact⟩ := literal_eta_lift
    exact ⟨H,eta,hH,hHseam,hHB,hHW,hHe,hetaone,hetainterior,hetaexact,hHfuture⟩

  obtain ⟨H,eta,hH,hseam,hB,hW,hmeet,hetaone,hetainterior,hexact,hfuture⟩ := hgeometry
  exact assemble_actual_relative_collar d H eta hH hseam hB hW hmeet
    hetaone hetainterior hexact hfuture

end CoherentEndpointMotion.RelativeCleanHalfAlignment
