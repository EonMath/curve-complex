import CurveComplexGenusTwo.Topology.Smoothing.ActualEndpointGerms
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarNormalizationProof
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
import CurveComplexGenusTwo.Topology.WeightedSurgery.SupportedEndpointRotation

namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- A constructed neighborhood meets each whole actual arc only in its incident
closed endpoint germs. Both loop incidences are retained. -/
theorem actual_finite_endpoint_germ_neighborhood
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (a : ι → EssentialMarkedArc M) (p : S) (hp : p ∈ M.cover.branch)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ U : Set S, IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧
      ∀ i x, x ∈ (a i).val.image → x ∈ U →
      ∃ b : Bool,
        (if b then (a i).val.map 1 else (a i).val.map 0) = p ∧
        x ∈ Set.range ((a i).val.map ∘ endpointGermParameter b r hr (by linarith)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let B : ι → Set Interval := fun i =>
    {t | ((a i).val.map 0 ≠ p ∨ r ≤ (t:ℝ)) ∧
      ((a i).val.map 1 ≠ p ∨ (t:ℝ) ≤ 1-r)}
  have hBclosed (i : ι) : IsClosed (B i) := by
    have hc : Continuous (fun t : Interval => (t:ℝ)) := continuous_subtype_val
    by_cases h0 : (a i).val.map 0 = p <;>
      by_cases h1 : (a i).val.map 1 = p
    · simpa only [B,h0,h1,ne_eq,not_true_eq_false,false_or,Set.setOf_and] using
        (isClosed_le continuous_const hc).inter
          (isClosed_le hc continuous_const)
    · simpa only [B,h0,ne_eq,not_true_eq_false,false_or,h1,not_false_eq_true,true_or,and_true] using
        (isClosed_le continuous_const continuous_subtype_val : IsClosed {t : Interval | r ≤ (t:ℝ)})
    · simpa only [B,h0,h1,ne_eq,not_true_eq_false,false_or,not_false_eq_true,true_or,true_and] using
        (isClosed_le continuous_subtype_val continuous_const : IsClosed {t : Interval | (t:ℝ) ≤ 1-r})
    · simpa [B,h0,h1] using (isClosed_univ : IsClosed (Set.univ : Set Interval))
  let K : Set S := ⋃ i, (a i).val.map '' B i
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite (fun i =>
    ((hBclosed i).isCompact.image (a i).val.continuous).isClosed)
  have hpK : p ∉ K := by
    intro hh
    obtain ⟨i,t,ht,he⟩ := Set.mem_iUnion.mp hh
    have hm : (a i).val.map t ∈ M.cover.branch := he.symm ▸ hp
    rcases (a i).val.marked_only_at_ends t hm with h0 | h1
    · subst t
      have he0 : (a i).val.map 0 = p := he
      have hh : r ≤ (0:ℝ) := ht.1.resolve_left (not_not_intro he0)
      linarith
    · subst t
      have he1 : (a i).val.map 1 = p := he
      have hh : (1:ℝ) ≤ 1-r := ht.2.resolve_left (not_not_intro he1)
      linarith
  refine ⟨W ∩ Kᶜ,hW.inter hKclosed.isOpen_compl,⟨hpW,hpK⟩,inter_subset_left,?_⟩
  intro i x hx hxU
  obtain ⟨t,rfl⟩ := hx
  have htB : t ∉ B i := fun ht => hxU.2 (Set.mem_iUnion.mpr ⟨i,t,ht,rfl⟩)
  have ht' : ((a i).val.map 0 = p ∧ (t:ℝ) < r) ∨
      ((a i).val.map 1 = p ∧ 1-r < (t:ℝ)) := by
    change ¬ (((a i).val.map 0 ≠ p ∨ r ≤ (t:ℝ)) ∧
      ((a i).val.map 1 ≠ p ∨ (t:ℝ) ≤ 1-r)) at htB
    rw [not_and_or] at htB
    rcases htB with hh | hh
    · push_neg at hh; exact Or.inl hh
    · push_neg at hh; exact Or.inr hh
  rcases ht' with ⟨h0,ht⟩ | ⟨h1,ht⟩
  · let u : Interval := ⟨(t:ℝ)/r,⟨div_nonneg t.property.1 hr.le,
      (div_le_one hr).mpr ht.le⟩⟩
    refine ⟨false,h0,u,?_⟩
    apply congrArg (a i).val.map
    apply Subtype.ext
    change r*((t:ℝ)/r) = (t:ℝ)
    field_simp
  · let u : Interval := ⟨(1-(t:ℝ))/r,⟨div_nonneg (by linarith [t.property.2]) hr.le,
      (div_le_one hr).mpr (by linarith)⟩⟩
    refine ⟨true,h1,u,?_⟩
    apply congrArg (a i).val.map
    apply Subtype.ext
    change 1-r*((1-(t:ℝ))/r) = (t:ℝ)
    field_simp
    ring

end CurveComplex.HyperellipticModel

namespace CurveComplex.ArcFinitePosition
open Set Schoenflies

lemma complex_offset_mem_segment (o v z : Plane)
    (hz : z ∈ segment ℝ o (o+v)) :
    planeComplexLinearEquiv (z-o) ∈ segment ℝ (0:ℂ) (planeComplexLinearEquiv v) := by
  rw [segment_eq_image_lineMap] at hz ⊢
  obtain ⟨t,ht,rfl⟩ := hz
  refine ⟨t,ht,?_⟩
  simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add]
  rw [show (1-t) • o + t • (o+v) - o = t • v by
    rw [smul_add]; module]
  exact (planeComplexLinearEquiv.map_smul t v).symm

end CurveComplex.ArcFinitePosition

namespace CurveComplex.HyperellipticModel
open Set Metric Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The actual supported rotation clears a new initial germ from the complete
old system, using only the literal radial germs produced by star normalization.
The positive cleared parameter prefix and the new quotient representative are
constructed; no finite-position or replacement witness is assumed. -/
theorem actual_initial_germ_clearance_from_normalized_stars
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (e0 : OpenPartialHomeomorph S Plane) (hp0 : a.val.map 0 ∈ e0.source)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (w : ι × Bool → Plane)
    (hold : ∀ i b, (if b then (old i).val.map 1 else (old i).val.map 0) = a.val.map 0 →
      w (i,b) ≠ 0 ∧ segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+w (i,b)) ⊆ e0.target ∧
      Set.range ((old i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
        e0.symm '' segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+w (i,b)))
    (s : ℝ) (hs : 0 < s) (hshalf : s < 1/2) (v : Plane) (hv : v ≠ 0)
    (hvtarget : segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+v) ⊆ e0.target)
    (hnew : Set.range (a.val.map ∘ endpointGermParameter false s hs (by linarith)) =
      e0.symm '' segment ℝ (e0 (a.val.map 0)) (e0 (a.val.map 0)+v))
    (W : Set S) (hW : IsOpen W) (hpW : a.val.map 0 ∈ W) :
    ∃ b : EssentialMarkedArc M, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
      ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) ≤ δ → ∀ i, b.val.map t ∉ (old i).val.image := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let p := a.val.map 0
  let J := {j : ι × Bool // (if j.2 then (old j.1).val.map 1 else (old j.1).val.map 0) = p}
  letI : Fintype J := Fintype.ofFinite J
  have hvC : planeComplexLinearEquiv v ≠ 0 := fun he => hv (planeComplexLinearEquiv.injective (by simpa using he))
  have hwC (j : J) : planeComplexLinearEquiv (w j.val) ≠ 0 := by
    intro he
    exact (hold j.val.1 j.val.2 j.property).1
      (planeComplexLinearEquiv.injective (by simpa using he))
  obtain ⟨θ,_,hsep⟩ := finite_star_rotation_direction
    (planeComplexLinearEquiv v) hvC (fun j : J => planeComplexLinearEquiv (w j.val)) hwC
  obtain ⟨e,R,H,hpe,_,he0,hee,hR,hmarks,houtside,hstay,_,hinner⟩ :=
    actual_marked_endpoint_rotation_in_chart M p a.val.start_marked e0 hp0 θ
      W hW hpW
  obtain ⟨U,hU,hpU,_,hUold⟩ := actual_finite_endpoint_germ_neighborhood M old p
    a.val.start_marked r hr hrhalf e0.source e0.open_source hp0
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
  let b := a.transport g hfix
  have hb (t : Interval) : b.val.map t = H.finalMap (a.val.map t) := by
    change g (a.val.map t) = H.finalMap (a.val.map t); rw [hfinal]
  let core : Set S := e.source ∩ e ⁻¹' {z : Plane | ‖planeComplexLinearEquiv (z-e p)‖ < R/2}
  have hcore : IsOpen core := e.isOpen_inter_preimage (isOpen_lt (by fun_prop) continuous_const)
  have hpcore : p ∈ core := ⟨hpe,by simp only [Set.mem_preimage,Set.mem_setOf_eq,sub_self,map_zero,norm_zero]; positivity⟩
  let Q : Set Interval := a.val.map ⁻¹' (core ∩ g ⁻¹' U)
  have hQ : IsOpen Q := (hcore.inter (hU.preimage g.continuous)).preimage a.val.continuous
  have h0Q : (0:Interval) ∈ Q := ⟨hpcore,by
    change g p ∈ U
    rw [hfix p a.val.start_marked]
    exact hpU⟩
  obtain ⟨η,hη,hball⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds h0Q)
  let δ : ℝ := min η (min s (1/2)) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδη : δ < η := by have := min_le_left η (min s (1/2)); dsimp [δ]; linarith
  have hδs : δ < s := by have := (min_le_right η (min s (1/2))).trans (min_le_left s (1/2)); dsimp [δ]; linarith
  have hδhalf : δ < 1/2 := by have := (min_le_right η (min s (1/2))).trans (min_le_right s (1/2)); dsimp [δ]; linarith
  refine ⟨b,δ,hδ,hδhalf,?_,hfix _ a.val.start_marked,hfix _ a.val.end_marked,?_,?_⟩
  · apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image a.val g hfix).symm
  · intro t ht
    rw [hb]
    exact houtside 1 _ ht
  · intro t ht0 htδ i hcontact
    have htQ : t ∈ Q := hball (by
      rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
      change |(t:ℝ)-0| < η
      rw [sub_zero,abs_of_pos ht0]
      exact htδ.trans_lt hδη)
    have hxU : b.val.map t ∈ U := by change g (a.val.map t) ∈ U; exact htQ.2
    obtain ⟨terminal,hincident,hxgerm⟩ := hUold i (b.val.map t) hcontact hxU
    let j : J := ⟨(i,terminal),hincident⟩
    have hyNew : a.val.map t ∈ Set.range (a.val.map ∘ endpointGermParameter false s hs (by linarith)) := by
      let u : Interval := ⟨(t:ℝ)/s,⟨div_nonneg t.property.1 hs.le,(div_le_one hs).mpr (htδ.trans hδs.le)⟩⟩
      refine ⟨u,?_⟩
      apply congrArg a.val.map; apply Subtype.ext
      change s*((t:ℝ)/s) = (t:ℝ)
      field_simp
    obtain ⟨z,hz,hzy⟩ := hnew ▸ hyNew
    have hcoordNew : e0 (a.val.map t) ∈ segment ℝ (e0 p) (e0 p+v) := by
      rw [← hzy,e0.right_inv (hvtarget hz)]; exact hz
    have hcoordOld : e0 (b.val.map t) ∈ segment ℝ (e0 p) (e0 p+w (i,terminal)) := by
      obtain ⟨z,hz,hzx⟩ := (hold i terminal hincident).2.2 ▸ hxgerm
      rw [← hzx,e0.right_inv ((hold i terminal hincident).2.1 hz)]; exact hz
    have hxsource : b.val.map t ∈ e.source := by rw [hb]; exact hstay 1 _ htQ.1.1
    have hxne : b.val.map t ≠ p := by
      intro he
      have hm : b.val.map t ∈ M.cover.branch := he.symm ▸ a.val.start_marked
      rcases b.val.marked_only_at_ends t hm with h0 | h1
      · subst t; exact (lt_irrefl (0:ℝ)) ht0
      · subst t; have : (1:ℝ) ≤ δ := htδ; linarith
    have hnonzero : planeComplexLinearEquiv (e0 (b.val.map t)-e0 p) ≠ 0 := by
      intro he
      have heq : e0 (b.val.map t) = e0 p := sub_eq_zero.mp
        (planeComplexLinearEquiv.injective (by simpa using he))
      exact hxne (e0.injOn (he0 hxsource) hp0 heq)
    have hrot := hinner (a.val.map t) htQ.1.1 htQ.1.2.le
    rw [← hb,hee,hee,hee] at hrot
    have hnewseg : planeComplexLinearEquiv (e0 (b.val.map t)-e0 p) ∈
        segment ℝ (0:ℂ) ((Circle.exp θ : ℂ)*planeComplexLinearEquiv v) := by
      rw [hrot]
      have hh := complex_offset_mem_segment (e0 p) v (e0 (a.val.map t)) hcoordNew
      rw [segment_eq_image_lineMap] at hh ⊢
      obtain ⟨q,hq,hqe⟩ := hh
      refine ⟨q,hq,?_⟩
      rw [← hqe]
      simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add,Complex.real_smul]
      ring
    have holdseg := complex_offset_mem_segment (e0 p) (w (i,terminal))
      (e0 (b.val.map t)) hcoordOld
    exact Set.disjoint_left.mp (hsep j) ⟨hnewseg,by simpa using hnonzero⟩
      ⟨holdseg,by simpa using hnonzero⟩

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- The new radial germ required for clearance is itself produced by the
actual singleton star normalization; it is not additional geometric input. -/
theorem actual_initial_germ_clearance_against_normalized_old_star
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
    (a : EssentialMarkedArc M)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (w : ι × Bool → Plane)
    (hold : letI := C.charts
      ∀ i b, (if b then (old i).val.map 1 else (old i).val.map 0) = a.val.map 0 →
      w (i,b) ≠ 0 ∧
      segment ℝ ((chartAt Plane (a.val.map 0)) (a.val.map 0))
        ((chartAt Plane (a.val.map 0)) (a.val.map 0)+w (i,b)) ⊆ (chartAt Plane (a.val.map 0)).target ∧
      Set.range ((old i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
        (chartAt Plane (a.val.map 0)).symm ''
          segment ℝ ((chartAt Plane (a.val.map 0)) (a.val.map 0))
            ((chartAt Plane (a.val.map 0)) (a.val.map 0)+w (i,b)))
    (W : Set S) (hW : IsOpen W) (hpW : a.val.map 0 ∈ W) :
    ∃ b : EssentialMarkedArc M, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
      ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) ≤ δ → ∀ i, b.val.map t ∉ (old i).val.image := by
  letI := C.charts
  obtain ⟨H,s,hs,hshalf,v,hmarks,houtside,hstar⟩ := actual_endpoint_star_normalization M C
    PUnit (fun _ => a) (by intro i j hij; exact (hij (Subsingleton.elim i j)).elim)
    (a.val.map 0) a.val.start_marked W hW hpW
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
  let a1 := a.transport g hfix
  have h10 : a1.val.map 0 = a.val.map 0 := hfix _ a.val.start_marked
  have h11 : a1.val.map 1 = a.val.map 1 := hfix _ a.val.end_marked
  have hclass1 : Quotient.mk (essentialArcSetoid M) a1 = Quotient.mk (essentialArcSetoid M) a := by
    apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image a.val g hfix).symm
  obtain ⟨hv,hvt,hvrange⟩ := hstar PUnit.unit false rfl
  have hrange : Set.range (a1.val.map ∘ endpointGermParameter false s hs (by linarith)) =
      (chartAt Plane (a1.val.map 0)).symm ''
      segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
        ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+v (PUnit.unit,false)) := by
    rw [h10]
    change Set.range (g ∘ (a.val.map ∘ endpointGermParameter false s hs _)) = _
    rw [Set.range_comp,← hfinal]
    exact hvrange
  obtain ⟨b,δ,hδ,hδhalf,hclass,hb0,hb1,hout,hclear⟩ :=
    actual_initial_germ_clearance_from_normalized_stars M old a1
      (chartAt Plane (a1.val.map 0)) (mem_chart_source Plane _) r hr hrhalf w
      (by simpa only [h10] using hold) s hs hshalf (v (PUnit.unit,false)) hv
      (by simpa only [h10] using hvt) hrange W hW (h10.symm ▸ hpW)
  refine ⟨b,δ,hδ,hδhalf,hclass.trans hclass1,hb0.trans h10,hb1.trans h11,?_,hclear⟩
  intro t ht
  have h1t : a1.val.map t = a.val.map t := by
    change g (a.val.map t) = a.val.map t
    rw [← hfinal]
    exact houtside 1 _ ht
  exact (hout t (h1t.symm ▸ ht)).trans h1t

end CurveComplex.HyperellipticModel

namespace CurveComplex.HyperellipticModel
open Set Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Initial endpoint clearance from actual source arcs. Both old and new radial
stars are constructed by the proved normalization producer. The old system
retains every class and remains pairwise interior disjoint. -/
theorem actual_finite_system_initial_endpoint_clearance
    (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
    {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
    (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
    (a : EssentialMarkedArc M) :
    ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
      ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
      (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
      (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
      Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
      b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
      ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) ≤ δ → ∀ i, b.val.map t ∉ (old' i).val.image := by
  letI := C.charts
  obtain ⟨H,r,hr,hrhalf,w,hmarks,_,hstar⟩ := actual_endpoint_star_normalization M C
    ι old hd (a.val.map 0) a.val.start_marked Set.univ isOpen_univ (Set.mem_univ _)
  obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
  have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
  have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
    intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
  let old' := fun i => (old i).transport g hfix
  let a1 := a.transport g hfix
  have h10 : a1.val.map 0 = a.val.map 0 := hfix _ a.val.start_marked
  have h11 : a1.val.map 1 = a.val.map 1 := hfix _ a.val.end_marked
  have hclass (c : EssentialMarkedArc M) :
      Quotient.mk (essentialArcSetoid M) (c.transport g hfix) = Quotient.mk (essentialArcSetoid M) c := by
    apply Eq.symm; apply Quotient.sound
    refine ⟨H,hmarks,?_⟩
    rw [hfinal]
    exact (MarkedArc.transport_image c.val g hfix).symm
  have hold : ∀ i b, (if b then (old' i).val.map 1 else (old' i).val.map 0) = a1.val.map 0 →
      w (i,b) ≠ 0 ∧
      segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
        ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+w (i,b)) ⊆ (chartAt Plane (a1.val.map 0)).target ∧
      Set.range ((old' i).val.map ∘ endpointGermParameter b r hr (by linarith)) =
        (chartAt Plane (a1.val.map 0)).symm ''
          segment ℝ ((chartAt Plane (a1.val.map 0)) (a1.val.map 0))
            ((chartAt Plane (a1.val.map 0)) (a1.val.map 0)+w (i,b)) := by
    intro i b hb
    have he : (if b then (old i).val.map 1 else (old i).val.map 0) = a.val.map 0 := by
      have h0 : (old' i).val.map 0 = (old i).val.map 0 := hfix _ (old i).val.start_marked
      have h1 : (old' i).val.map 1 = (old i).val.map 1 := hfix _ (old i).val.end_marked
      simpa only [h0,h1,h10] using hb
    obtain ⟨hw,hwt,hwr⟩ := hstar i b he
    refine ⟨hw,by simpa only [h10] using hwt,?_⟩
    rw [h10]
    change Set.range (g ∘ ((old i).val.map ∘ endpointGermParameter b r hr _)) = _
    rw [Set.range_comp,← hfinal]
    exact hwr
  obtain ⟨b,δ,hδ,hδhalf,hbclass,hb0,hb1,_,hclear⟩ :=
    actual_initial_germ_clearance_against_normalized_old_star M C old' a1
      r hr hrhalf w hold Set.univ isOpen_univ (Set.mem_univ _)
  refine ⟨old',b,δ,hδ,hδhalf,(fun i => hclass (old i)),?_,
    hbclass.trans (hclass a),hb0.trans h10,hb1.trans h11,hclear⟩
  intro i j hij
  exact arcInterior_transport_disjoint (old i) (old j) g hfix (hd i j hij)

end CurveComplex.HyperellipticModel
