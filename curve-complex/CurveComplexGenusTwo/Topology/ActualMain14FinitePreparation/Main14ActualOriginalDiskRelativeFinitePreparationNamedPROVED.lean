import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.ArcCounts.NonloopClassConversion
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualFiniteTransverseNewArc
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly

open Lean Elab Tactic in
elab "audit_main14_original_relative_finite_base3 " ts:tacticSeq : tactic => do
  let g ← getMainGoal
  evalTacticSeq ts
  let pf ← instantiateMVars (mkMVar g)
  let mut found : NameSet := {}
  for c in pf.getUsedConstants do
    for ax in ← collectAxioms c do
      found := found.insert ax
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom in original relative finite preparation: {ax}"
  logInfo m!"Original relative finite preparation proof axiom audit: {found.toList}"
namespace CurveComplex.HyperellipticModel
open Set Schoenflies CurveComplex.ArcFinitePosition
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

set_option maxHeartbeats 1800000
theorem actual_two_mark_disk_relative_finite_transverse_preparation
(M : HyperellipticModel E S) (a b : NonLoopArc M)
(N : ArcNeighborhood a) (hb : b.image ⊆ interior N.closedSet)
(hends : ({a.val.map 0,a.val.map 1}:Set S) = {b.val.map 0,b.val.map 1}) :
∃ a' b' : NonLoopArc M, ∃ H K : AmbientIsotopy S,
  (∀ t x, x ∉ interior N.closedSet → H.map (t,x)=x) ∧
  (∀ t x, x ∉ interior N.closedSet → K.map (t,x)=x) ∧
  (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
  (∀ t x, x ∈ M.cover.branch → K.map (t,x)=x) ∧
  H.finalMap '' a.image=a'.image ∧ K.finalMap '' b.image=b'.image ∧
  a'.image ⊆ interior N.closedSet ∧ b'.image ⊆ interior N.closedSet ∧
  (ArcSurgery.crossings M a'.toEssential b'.toEssential).Finite ∧
  (∀ p ∈ ArcSurgery.crossings M a'.toEssential b'.toEssential,
    ArcSurgery.CrossesInDisk M a'.toEssential b'.toEssential p) := by
  audit_main14_original_relative_finite_base3
    have hContacts
        (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
        (old : ι → EssentialMarkedArc M)
        (hclasses : ∀ i, ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (old i)))
        (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
        (a : EssentialMarkedArc M)
        (ha : ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) a))
        (V : Set S) (hV : IsOpen V) (haV : Set.range a.val.map ⊆ V) :
        ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
          ∃ H K : AmbientIsotopy S,
          (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
          (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
          Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
          (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
          (∀ t x, x ∉ V → H.map (t,x)=x) ∧
          (∀ t x, x ∈ M.cover.branch → K.map (t,x)=x) ∧
          (∀ t x, x ∉ V → K.map (t,x)=x) ∧
          (∀ i, (old' i).val.image = H.finalMap '' (old i).val.image) ∧
          b.val.image = K.finalMap '' a.val.image ∧ b.val.image ⊆ V ∧
          ∀ i, (arcInterior M b ∩ (old' i).val.image).Finite ∧
            ∀ p ∈ arcInterior M b ∩ (old' i).val.image, ArcSurgery.CrossesInDisk M (old' i) b p := by
      have hPrepared
          (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
          {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
          (hclasses : ∀ i, ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) (old i)))
          (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
          (a : EssentialMarkedArc M) (ha : a.val.map 0 ≠ a.val.map 1)
          (V : Set S) (hV : IsOpen V) (haV : Set.range a.val.map ⊆ V) :
          ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
          ∃ H K : AmbientIsotopy S,
          ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ hδhalf : δ < 1/2,
            (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
            (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
            Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
            (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
            (∀ t x, x ∉ V → H.map (t,x)=x) ∧
            (∀ t x, x ∈ M.cover.branch → K.map (t,x)=x) ∧
            (∀ t x, x ∉ V → K.map (t,x)=x) ∧
            (∀ i t, (old' i).val.map t = H.finalMap ((old i).val.map t)) ∧
            (∀ t, b.val.map t = K.finalMap (a.val.map t)) ∧
            Set.range b.val.map ⊆ V ∧
            (∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 → (t:ℝ) ≤ δ ∨ 1-δ ≤ (t:ℝ) →
              ∀ i, b.val.map t ∉ (old' i).val.image) ∧
            ∃ η : C(Interval,S),
            (∀ t, η t = b.val.map ⟨δ+(1-2*δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
            Topology.IsClosedEmbedding η ∧ ∃ n : ℕ, ∃ hn : 0 < n,
            ∃ e : Fin n → OpenPartialHomeomorph S Plane, ∃ label : Fin n → Option ι,
              (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
              (∀ k j x, x ∈ (e k).source →
                (x ∈ (old' j).val.image ↔ label k = some j ∧ e k x 0 = 0)) ∧
              (∀ k t, η (intervalMeshParameter n hn k t) ∈ (e k).source) ∧
              ∀ k j, η (intervalMeshParameter n hn k 0) ∉ (old' j).val.image ∧
                η (intervalMeshParameter n hn k 1) ∉ (old' j).val.image := by
        have hBoth
            (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
            {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
            (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
            (a : EssentialMarkedArc M) (hne : a.val.map 0 ≠ a.val.map 1)
            (V : Set S) (hV : IsOpen V) (haV : Set.range a.val.map ⊆ V) :
            ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
              ∃ H K : AmbientIsotopy S,
              ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
              (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
              (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
              Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
              b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
              (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
              (∀ t x, x ∉ V → H.map (t,x)=x) ∧
              (∀ t x, x ∈ M.cover.branch → K.map (t,x)=x) ∧
              (∀ t x, x ∉ V → K.map (t,x)=x) ∧
              (∀ i t, (old' i).val.map t = H.finalMap ((old i).val.map t)) ∧
              (∀ t, b.val.map t = K.finalMap (a.val.map t)) ∧
              ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 →
                (t:ℝ) ≤ δ ∨ 1-δ ≤ (t:ℝ) → ∀ i, b.val.map t ∉ (old' i).val.image := by
          have hInitial
              (M : HyperellipticModel E S) (C : SphereSmoothAtlas S)
              {ι : Type} [Fintype ι] (old : ι → EssentialMarkedArc M)
              (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
              (a : EssentialMarkedArc M)
              (V : Set S) (hV : IsOpen V) (hpV : a.val.map 0 ∈ V) :
              ∃ old' : ι → EssentialMarkedArc M, ∃ b : EssentialMarkedArc M,
                ∃ H K : AmbientIsotopy S,
                ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
                (∀ i, Quotient.mk (essentialArcSetoid M) (old' i) = Quotient.mk (essentialArcSetoid M) (old i)) ∧
                (∀ i j, i ≠ j → Disjoint (arcInterior M (old' i)) (arcInterior M (old' j))) ∧
                Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
                b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
                (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
                (∀ t x, x ∉ V → H.map (t,x)=x) ∧
                (∀ t x, x ∈ M.cover.branch → K.map (t,x)=x) ∧
                (∀ t x, x ∉ V → K.map (t,x)=x) ∧
                (∀ i t, (old' i).val.map t = H.finalMap ((old i).val.map t)) ∧
                (∀ t, b.val.map t = K.finalMap (a.val.map t)) ∧
                ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) ≤ δ → ∀ i, b.val.map t ∉ (old' i).val.image := by
            have hOldStar
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
                ∃ b : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
                  Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
                  b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
                  (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
                  (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
                  (∀ t x, x ∉ W → H.map (t,x)=x) ∧
                  (∀ t, b.val.map t = H.finalMap (a.val.map t)) ∧
                  ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) ≤ δ → ∀ i, b.val.map t ∉ (old i).val.image := by
              have hNormalized
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
                  ∃ b : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
                    Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
                    b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
                    (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
                    (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
                    (∀ t x, x ∉ W → H.map (t,x)=x) ∧
                    (∀ t, b.val.map t = H.finalMap (a.val.map t)) ∧
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
                refine ⟨b,H,δ,hδ,hδhalf,?_,hfix _ a.val.start_marked,hfix _ a.val.end_marked,?_,hmarks,houtside,hb,?_⟩
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
              obtain ⟨b,K,δ,hδ,hδhalf,hclass,hb0,hb1,hout,hKmarks,hKout,hmap,hclear⟩ :=
                hNormalized M old a1
                  (chartAt Plane (a1.val.map 0)) (mem_chart_source Plane _) r hr hrhalf w
                  (by simpa only [h10] using hold) s hs hshalf (v (PUnit.unit,false)) hv
                  (by simpa only [h10] using hvt) hrange W hW (h10.symm ▸ hpW)
              refine ⟨b,H.compose K,δ,hδ,hδhalf,hclass.trans hclass1,hb0.trans h10,hb1.trans h11,?_,?_,?_,?_,hclear⟩
              · intro t ht
                have h1t : a1.val.map t = a.val.map t := by
                  change g (a.val.map t) = a.val.map t
                  rw [← hfinal]
                  exact houtside 1 _ ht
                exact (hout t (h1t.symm ▸ ht)).trans h1t
              · intro t x hx
                change K.map (t,H.map (t,x))=x
                rw [hmarks t x hx,hKmarks t x hx]
              · intro t x hx
                change K.map (t,H.map (t,x))=x
                rw [houtside t x hx,hKout t x hx]
              · intro t
                change b.val.map t = K.finalMap (H.finalMap (a.val.map t))
                rw [hmap]
                congr 1
                change g (a.val.map t) = H.finalMap (a.val.map t)
                rw [hfinal]
            letI := C.charts
            obtain ⟨H,r,hr,hrhalf,w,hmarks,houtside,hstar⟩ := actual_endpoint_star_normalization M C
              ι old hd (a.val.map 0) a.val.start_marked V hV hpV
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
            obtain ⟨b,K,δ,hδ,hδhalf,hbclass,hb0,hb1,_,hKmarks,hKoutside,hmap,hclear⟩ :=
              hOldStar M C old' a1
                r hr hrhalf w hold V hV (h10.symm ▸ hpV)
            refine ⟨old',b,H,H.compose K,δ,hδ,hδhalf,(fun i => hclass (old i)),?_,
              hbclass.trans (hclass a),hb0.trans h10,hb1.trans h11,hmarks,houtside,?_,?_,?_,?_,hclear⟩
            · intro i j hij
              exact arcInterior_transport_disjoint (old i) (old j) g hfix (hd i j hij)
            · intro t x hx
              change K.map (t,H.map (t,x))=x
              rw [hmarks t x hx,hKmarks t x hx]
            · intro t x hx
              change K.map (t,H.map (t,x))=x
              rw [houtside t x hx,hKoutside t x hx]
            · intro i t
              change g ((old i).val.map t)=H.finalMap ((old i).val.map t)
              rw [hfinal]
            · intro t
              change b.val.map t = K.finalMap (H.finalMap (a.val.map t))
              rw [hmap]
              congr 1
              change g (a.val.map t)=H.finalMap (a.val.map t)
              rw [hfinal]
          have hOldStar
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
              ∃ b : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
                Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
                b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
                (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
                (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
                (∀ t x, x ∉ W → H.map (t,x)=x) ∧
                (∀ t, b.val.map t = H.finalMap (a.val.map t)) ∧
                ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) ≤ δ → ∀ i, b.val.map t ∉ (old i).val.image := by
            have hNormalized
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
                ∃ b : EssentialMarkedArc M, ∃ H : AmbientIsotopy S, ∃ δ : ℝ, 0 < δ ∧ δ < 1/2 ∧
                  Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
                  b.val.map 0 = a.val.map 0 ∧ b.val.map 1 = a.val.map 1 ∧
                  (∀ t, a.val.map t ∉ W → b.val.map t = a.val.map t) ∧
                  (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
                  (∀ t x, x ∉ W → H.map (t,x)=x) ∧
                  (∀ t, b.val.map t = H.finalMap (a.val.map t)) ∧
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
              refine ⟨b,H,δ,hδ,hδhalf,?_,hfix _ a.val.start_marked,hfix _ a.val.end_marked,?_,hmarks,houtside,hb,?_⟩
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
            obtain ⟨b,K,δ,hδ,hδhalf,hclass,hb0,hb1,hout,hKmarks,hKout,hmap,hclear⟩ :=
              hNormalized M old a1
                (chartAt Plane (a1.val.map 0)) (mem_chart_source Plane _) r hr hrhalf w
                (by simpa only [h10] using hold) s hs hshalf (v (PUnit.unit,false)) hv
                (by simpa only [h10] using hvt) hrange W hW (h10.symm ▸ hpW)
            refine ⟨b,H.compose K,δ,hδ,hδhalf,hclass.trans hclass1,hb0.trans h10,hb1.trans h11,?_,?_,?_,?_,hclear⟩
            · intro t ht
              have h1t : a1.val.map t = a.val.map t := by
                change g (a.val.map t) = a.val.map t
                rw [← hfinal]
                exact houtside 1 _ ht
              exact (hout t (h1t.symm ▸ ht)).trans h1t
            · intro t x hx
              change K.map (t,H.map (t,x))=x
              rw [hmarks t x hx,hKmarks t x hx]
            · intro t x hx
              change K.map (t,H.map (t,x))=x
              rw [houtside t x hx,hKout t x hx]
            · intro t
              change b.val.map t = K.finalMap (H.finalMap (a.val.map t))
              rw [hmap]
              congr 1
              change g (a.val.map t) = H.finalMap (a.val.map t)
              rw [hfinal]
          classical
          letI := C.charts
          letI : T2Space S := M.sphere.symm.t2Space
          obtain ⟨old0,b0,H0,K0,δ0,hδ0,hδ0half,hclassOld0,hd0,hclassB0,hb00,hb01,hH0marks,hH0out,hK0marks,hK0out,hOld0map,hB0map,hclear0⟩ :=
            hInitial M C old hd a V hV (haV (Set.mem_range_self 0))
          obtain ⟨H,r,hr,hrhalf,w,hmarks,houtside,hstar⟩ := actual_endpoint_star_normalization M C
            ι old0 hd0 (b0.val.map 1) b0.val.end_marked V hV (hb01.symm ▸ haV (Set.mem_range_self 1))
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
          let W : Set S := prefixCarrierᶜ ∩ V
          have hW : IsOpen W := hprefixCarrier.isOpen_compl.inter hV
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
          obtain ⟨z,K,δ1,hδ1,hδ1half,hzclass,hz0,hz1,hzout,hKmarks,hKout,hZmap,hzclear⟩ :=
            hOldStar M C old1 a1.reverse
              r hr hrhalf w hold W hW (by
                refine ⟨by simpa using hend,?_⟩
                simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_zero,h11,hb01] using haV (Set.mem_range_self 1))
          let δ : ℝ := min δ0 δ1
          have hδ : 0 < δ := lt_min hδ0 hδ1
          have hδhalf : δ < 1/2 := (min_le_left _ _).trans_lt hδ0half
          refine ⟨old1,z.reverse,H0.compose H,(K0.compose H).compose K,δ,hδ,hδhalf,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
          · intro i; exact (hclass (old0 i)).trans (hclassOld0 i)
          · intro i j hij
            exact arcInterior_transport_disjoint (old0 i) (old0 j) g hfix (hd0 i j hij)
          · exact z.reverse_class.trans (hzclass.trans (a1.reverse_class.trans ((hclass b0).trans hclassB0)))
          · simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_zero] using
              hz1.trans (by simpa using h10.trans hb00)
          · simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_one] using
              hz0.trans (by simpa using h11.trans hb01)
          · intro t x hx
            change H.map (t,H0.map (t,x))=x
            rw [hH0marks t x hx,hmarks t x hx]
          · intro t x hx
            change H.map (t,H0.map (t,x))=x
            rw [hH0out t x hx,houtside t x hx]
          · intro t x hx
            change K.map (t,H.map (t,K0.map (t,x)))=x
            rw [hK0marks t x hx,hmarks t x hx,hKmarks t x hx]
          · intro t x hx
            change K.map (t,H.map (t,K0.map (t,x)))=x
            rw [hK0out t x hx,houtside t x hx]
            exact hKout t x (fun hw => hx hw.2)
          · intro i t
            change g ((old0 i).val.map t)=H.finalMap (H0.finalMap ((old i).val.map t))
            rw [hOld0map,←hfinal]
          · intro t
            change z.val.map (unitInterval.symm t)=K.finalMap (H.finalMap (K0.finalMap (a.val.map t)))
            rw [hZmap]
            change K.finalMap (g (b0.val.map (unitInterval.symm (unitInterval.symm t))))=_
            rw [unitInterval.symm_symm,hB0map,←hfinal]
          · intro t ht0 ht1 hcol i
            change z.val.map (unitInterval.symm t) ∉ (old1 i).val.image
            rcases hcol with hstart | hendcol
            · have htδ0 : (t:ℝ) ≤ δ0 := hstart.trans (min_le_left _ _)
              have houtside : a1.reverse.val.map (unitInterval.symm t) ∉ W := by
                change a1.val.map (unitInterval.symm (unitInterval.symm t)) ∉ prefixCarrierᶜ ∩ V
                rw [unitInterval.symm_symm]
                exact fun hh => hh.1 ⟨t,htδ0,rfl⟩
              rw [hzout _ houtside]
              simpa only [EssentialMarkedArc.reverse_map,unitInterval.symm_symm] using hclear1 t ht0 htδ0 i
            · apply hzclear
              · change 0 < 1-(t:ℝ); linarith
              · change 1-(t:ℝ) ≤ δ1
                have := min_le_right δ0 δ1
                dsimp [δ] at hendcol
                linarith
        have hSeam
            (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
            (old : ι → EssentialMarkedArc M)
            (hne : ∀ i, (old i).val.map 0 ≠ (old i).val.map 1)
            (hd : ∀ i j, i ≠ j → Disjoint (arcInterior M (old i)) (arcInterior M (old j)))
            (a : EssentialMarkedArc M) (ha : a.val.map 0 ≠ a.val.map 1)
            (V : Set S) (hV : IsOpen V) (haV : Set.range a.val.map ⊆ V)
            (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1) :
            ∃ η : C(Interval,S),
              (∀ t, η t = a.val.map ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
              Topology.IsClosedEmbedding η ∧
              ∃ n : ℕ, ∃ hn : 0 < n,
              ∃ e : Fin n → OpenPartialHomeomorph S Plane, ∃ label : Fin n → Option ι,
              ∃ H : AmbientIsotopy S, ∃ b : EssentialMarkedArc M,
                (∀ k, Disjoint (e k).source (M.cover.branch : Set S)) ∧
                (∀ k j x, x ∈ (e k).source →
                  (x ∈ (old j).val.image ↔ label k = some j ∧ e k x 0 = 0)) ∧
                Quotient.mk (essentialArcSetoid M) b = Quotient.mk (essentialArcSetoid M) a ∧
                (∀ t, b.val.map t = H.finalMap (a.val.map t)) ∧
                (∀ t : Interval, (t:ℝ) ≤ l ∨ u ≤ (t:ℝ) → b.val.map t = a.val.map t) ∧
                (∀ k t, H.finalMap (η (intervalMeshParameter n hn k t)) ∈ (e k).source) ∧
                (∀ k : Fin (n-1), ∀ j,
                  H.finalMap (η ⟨((k.val:ℝ)+1)/n,by
                    have hnR : (0:ℝ) < n := by exact_mod_cast hn
                    constructor
                    · positivity
                    · apply (div_le_one hnR).mpr
                      have hk : k.val+1 ≤ n := by omega
                      exact_mod_cast hk⟩) ∉ (old j).val.image) ∧
                (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
                (∀ t x, x ∉ V → H.map (t,x)=x) ∧ Set.range b.val.map ⊆ V := by
          classical
          letI : T2Space S := M.sphere.symm.t2Space
          obtain ⟨η,hη,hi,n,hn,e,label,hemarks,hlabel,hchart⟩ :=
            actual_new_arc_compact_interior_chart_subdivision M old hne hd a ha l u hl hlu hu
          have hnR : (0:ℝ) < n := by exact_mod_cast hn
          let σ : Fin (n-1) → Interval := fun k => ⟨((k.val:ℝ)+1)/n,by
            constructor
            · positivity
            · apply (div_le_one hnR).mpr
              have hk : k.val+1 ≤ n := by omega
              exact_mod_cast hk⟩
          have hσ0 (k : Fin (n-1)) : 0 < (σ k:ℝ) := div_pos (by positivity) hnR
          have hσ1 (k : Fin (n-1)) : (σ k:ℝ) < 1 := by
            apply (div_lt_one hnR).mpr
            have hk : k.val+1 < n := by omega
            exact_mod_cast hk
          let p : Fin (n-1) → S := fun k => η (σ k)
          have hpi : Function.Injective p := by
            intro k j he
            have hh := congrArg Subtype.val (hi.injective he)
            change ((k.val:ℝ)+1)/n = ((j.val:ℝ)+1)/n at hh
            have hh' := (div_left_inj' hnR.ne').mp hh
            apply Fin.ext
            exact Nat.cast_injective (by linarith : (k.val:ℝ) = j.val)
          have hpm (k : Fin (n-1)) : p k ∉ M.cover.branch := by
            rw [show p k = η (σ k) from rfl,hη]
            intro hm
            rcases a.val.marked_only_at_ends _ hm with he | he
            · have hh := congrArg Subtype.val he
              change l+(u-l)*(σ k:ℝ) = 0 at hh
              nlinarith [hσ0 k]
            · have hh := congrArg Subtype.val he
              change l+(u-l)*(σ k:ℝ) = 1 at hh
              nlinarith [hσ1 k]
          let tailParameters : Set Interval := {t | (t:ℝ) ≤ l ∨ u ≤ (t:ℝ)}
          let tails : Set S := a.val.map '' tailParameters
          have htailClosed : IsClosed tailParameters :=
            (isClosed_le continuous_subtype_val continuous_const).union
              (isClosed_le continuous_const continuous_subtype_val)
          have htails : IsClosed tails := (htailClosed.isCompact.image a.val.continuous).isClosed
          have hpTail (k : Fin (n-1)) : p k ∉ tails := by
            rintro ⟨t,ht,he⟩
            rw [show p k = η (σ k) from rfl,hη] at he
            have heq := congrArg Subtype.val (NonLoopArc.injective ⟨a.val,ha⟩ he)
            change (t:ℝ) = l+(u-l)*(σ k:ℝ) at heq
            rcases ht with ht | ht <;> nlinarith [hσ0 k,hσ1 k]
          let arc : Fin n → C(Interval,S) := fun k =>
            ⟨η ∘ intervalMeshParameter n hn k,η.continuous.comp (intervalMeshParameter_continuous n hn k)⟩
          have hpiece (k : Fin n) : Set.range (arc k) ⊆ (e k).source := by
            rintro x ⟨t,rfl⟩
            apply hchart k
            · change (k.val:ℝ)/n ≤ ((k.val:ℝ)+(t:ℝ))/n
              exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [t.property.1])
            · change ((k.val:ℝ)+(t:ℝ))/n ≤ (k.val+1:ℝ)/n
              exact (div_le_div_iff_of_pos_right hnR).mpr (by linarith [t.property.2])
          have hpV (k : Fin (n-1)) : p k ∈ V := by
            change η (σ k) ∈ V
            rw [hη]
            exact haV (Set.mem_range_self _)
          obtain ⟨U,H,_,_,hUW,_,havoid,hmarks,hout,hpreserve⟩ :=
            actual_localized_marked_seam_repair M old hne hd p hpi hpm arc e hpiece
              (fun _ => tailsᶜ ∩ V) (fun _ => htails.isOpen_compl.inter hV)
              (fun k => ⟨hpTail k,hpV k⟩)
          have htailfix (t : Interval) (x : S) (hx : x ∈ tails) : H.map (t,x) = x := by
            apply hout t x
            intro hh
            obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
            exact (hUW k hk).1 hx
          have hVfix (t : Interval) (x : S) (hx : x ∉ V) : H.map (t,x)=x := by
            apply hout t x
            intro hxU
            obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hxU
            exact hx (hUW k hk).2
          obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
          have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
          have hfix : ∀ x, x ∈ M.cover.branch → g x = x := by
            intro x hx; rw [← hfinal]; exact hmarks ⟨1,by norm_num⟩ x hx
          have hgV : Set.MapsTo g V V := by
            intro x hx
            by_contra hn
            have hgg : g (g x)=g x :=
              (congrFun hfinal (g x)).symm.trans (hVfix 1 (g x) hn)
            have hxx := g.injective hgg
            rw [hxx] at hn
            exact hn hx
          let b := a.transport g hfix
          refine ⟨η,hη,hi,n,hn,e,label,H,b,hemarks,hlabel,?_,?_,?_,?_,havoid,hmarks,hVfix,?_⟩
          · apply Eq.symm; apply Quotient.sound
            refine ⟨H,hmarks,?_⟩
            rw [hfinal]
            exact (MarkedArc.transport_image a.val g hfix).symm
          · intro t; change g (a.val.map t) = H.finalMap (a.val.map t); rw [hfinal]
          · intro t ht
            change g (a.val.map t) = a.val.map t
            rw [← hfinal]
            exact htailfix 1 _ ⟨t,ht,rfl⟩
          · intro k t
            exact hpreserve k 1 ⟨η (intervalMeshParameter n hn k t),Set.mem_range_self t,rfl⟩
        
          · rintro x ⟨t,rfl⟩
            exact hgV (haV (Set.mem_range_self t))
        classical
        letI : T2Space S := M.sphere.symm.t2Space
        obtain ⟨old',a0,H0,K0,d,hdpos,hdhalf,hclassOld,hdisOld,hclassA,hA0,hA1,hH0marks,hH0out,hK0marks,hK0out,hOldmap,hAmap,hclear⟩ :=
          hBoth M C old hd a ha V hV haV
        have hA0V : Set.range a0.val.map ⊆ V := by
          obtain ⟨g,hg⟩ := K0.homeomorphism_at 1
          have he : K0.finalMap = g := funext (fun x => (hg x).symm)
          rintro x ⟨t,rfl⟩
          rw [hAmap,he]
          by_contra hn
          have hgg : g (g (a.val.map t))=g (a.val.map t) := by
            exact (congrFun he (g (a.val.map t))).symm.trans (hK0out 1 _ hn)
          have hxx := g.injective hgg
          rw [hxx] at hn
          exact hn (haV (Set.mem_range_self t))
        have hneOld (i : ι) : (old' i).val.map 0 ≠ (old' i).val.map 1 :=
          actualRepresentative_nonloop M (old' i) (by rw [hclassOld i]; exact hclasses i)
        have hneA : a0.val.map 0 ≠ a0.val.map 1 := by rw [hA0,hA1]; exact ha
        let δ : ℝ := d/2
        have hδ : 0 < δ := by dsimp [δ]; positivity
        have hδhalf : δ < 1/2 := by dsimp [δ]; linarith
        have hlu : δ < 1-δ := by linarith
        have hu : 1-δ < 1 := by linarith
        obtain ⟨η,hη,hi,n,hn,e,label,H,b,hemarks,hlabel,hclassB,hb,htails,hpiece,hseam,hHmarks,hHout,hbV⟩ :=
          hSeam M old' hneOld hdisOld a0 hneA V hV hA0V
            δ (1-δ) hδ hlu hu
        obtain ⟨g,hg⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
        have hfinal : H.finalMap = g := funext (fun x => (hg x).symm)
        let ν : C(Interval,S) := ⟨g ∘ η,g.continuous.comp η.continuous⟩
        have hν (t : Interval) : ν t = H.finalMap (η t) := by change g (η t) = _; rw [hfinal]
        have hνliteral (t : Interval) :
            ν t = b.val.map ⟨δ+(1-2*δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩ := by
          rw [hν,hη,← hb]
          apply congrArg b.val.map
          apply Subtype.ext
          change δ+((1-δ)-δ)*(t:ℝ) = δ+(1-2*δ)*(t:ℝ)
          ring
        have hνembed : Topology.IsClosedEmbedding ν := ν.continuous.isClosedEmbedding
          (g.injective.comp hi.injective)
        have hends := actual_interval_mesh_all_ends_off η H (fun i => (old' i).val.image) n hn
          (by
            intro i
            have ht : (⟨δ,⟨hδ.le,by linarith⟩⟩ : Interval).val ≤ δ := le_rfl
            have hh := hclear ⟨δ,⟨hδ.le,by linarith⟩⟩ hδ (by linarith) (Or.inl (by dsimp [δ]; linarith)) i
            have hη0 : η 0 = a0.val.map ⟨δ,⟨hδ.le,by linarith⟩⟩ := by simpa using hη 0
            rw [hη0,← hb,htails _ (Or.inl ht)]
            exact hh)
          (by
            intro i
            have ht : 1-δ ≤ (⟨1-δ,⟨by linarith,hu.le⟩⟩ : Interval).val := le_rfl
            have hh := hclear ⟨1-δ,⟨by linarith,hu.le⟩⟩ (by linarith) hu
              (Or.inr (by dsimp [δ]; linarith)) i
            have hη1 : η 1 = a0.val.map ⟨1-δ,⟨by linarith,hu.le⟩⟩ := by
              rw [hη]
              apply congrArg a0.val.map; apply Subtype.ext
              change δ+((1-δ)-δ)*1 = 1-δ
              ring
            rw [hη1,← hb,htails _ (Or.inr ht)]
            exact hh) hseam
        refine ⟨old',b,H0,K0.compose H,δ,hδ,hδhalf,hclassOld,hdisOld,hclassB.trans hclassA,
          hH0marks,hH0out,?_,?_,hOldmap,?_,hbV,?_,
          ν,hνliteral,hνembed,n,hn,e,label,hemarks,hlabel,?_,?_⟩
        · intro t x hx
          change H.map (t,K0.map (t,x))=x
          rw [hK0marks t x hx,hHmarks t x hx]
        · intro t x hx
          change H.map (t,K0.map (t,x))=x
          rw [hK0out t x hx,hHout t x hx]
        · intro t
          change b.val.map t=H.finalMap (K0.finalMap (a.val.map t))
          rw [hb,hAmap]
        · intro t ht0 ht1 hcol i
          rw [htails t hcol]
          apply hclear t ht0 ht1
          rcases hcol with hc | hc
          · exact Or.inl (hc.trans (by dsimp [δ]; linarith))
          · exact Or.inr (by dsimp [δ] at hc; linarith)
        · intro k t; rw [hν]; exact hpiece k t
        · intro k j
          simpa only [hν] using hends k j
      have hCrosscuts
          (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
          (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
          (V : Set S) (hV : IsOpen V) (haV : Set.range a.val.map ⊆ V)
          (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
          (η : C(Interval,S))
          (hη : ∀ t, η t = a.val.map ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩)
          (hi : Function.Injective η) (n : ℕ) (hn : 0 < n)
          (e : Fin n → OpenPartialHomeomorph S Plane)
          (hemarks : ∀ k, Disjoint (e k).source (M.cover.branch : Set S))
          (hchart : ∀ k t, η (intervalMeshParameter n hn k t) ∈ (e k).source)
          (hends : ∀ k j, η (intervalMeshParameter n hn k 0) ∉ (old j).val.image ∧
            η (intervalMeshParameter n hn k 1) ∉ (old j).val.image)
          (houter : ∀ t : Interval, 0 < (t:ℝ) → (t:ℝ) < 1 →
            (t:ℝ) ≤ l ∨ u ≤ (t:ℝ) → ∀ j, a.val.map t ∉ (old j).val.image) :
          ∃ α β : Fin n → ℝ, ∃ F : Fin n → OpenPartialHomeomorph S Plane,
            (∀ k, 0 < α k ∧ α k < β k ∧ β k < 1) ∧
            (∀ k, (F k).source ⊆ (e k).source) ∧
            (∀ k, (F k).source ⊆ V) ∧
            (∀ i j, i ≠ j → Disjoint (F i).source (F j).source) ∧
            (∀ k, Disjoint (F k).source (M.cover.branch : Set S)) ∧
            (∀ k, Plane.closedSquare 0 1 ⊆ (F k).target) ∧
            (∀ k, F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) = Plane.mk (-1) 0 ∧
              F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) = Plane.mk 1 0) ∧
            (∀ k x, x ∈ (F k).source → (x ∈ a.val.image ↔ F k x 1 = 0)) ∧
            (∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ a.val.image =
              (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k)) ∧
            (∀ k j, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∉ (old j).val.image ∧
              (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∉ (old j).val.image) ∧
            ∀ j, Disjoint
              (arcInterior M a \ ⋃ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
              (old j).val.image := by
        let e' : Fin n → OpenPartialHomeomorph S Plane := fun k => (e k).restrOpen V hV
        have hm (k : Fin n) : Disjoint (e' k).source (M.cover.branch : Set S) :=
          (hemarks k).mono (fun _ hx => hx.1) Set.Subset.rfl
        have hc (k : Fin n) (t : Interval) : η (intervalMeshParameter n hn k t) ∈ (e' k).source := by
          refine ⟨hchart k t,?_⟩
          rw [hη]
          exact haV (Set.mem_range_self _)
        obtain ⟨α,β,F,hbounds,hsub,hdis,hmarks,hsq,hflatends,hflat,hexact,hoff,hrest⟩ :=
          actual_trimmed_marked_crosscut_assembly M old a l u hl hlu hu η hη hi n hn
            e' hm hc hends houter
        exact ⟨α,β,F,hbounds,(fun k x hx => (hsub k hx).1),
          (fun k x hx => (hsub k hx).2),hdis,hmarks,hsq,hflatends,hflat,hexact,hoff,hrest⟩
      have hRedrawing
          (M : HyperellipticModel E S) {ι K : Type} [Fintype ι] [Fintype K]
          (old : ι → EssentialMarkedArc M) (a : EssentialMarkedArc M)
          (e F : K → OpenPartialHomeomorph S Plane) (label : K → Option ι)
          (α β : K → ℝ) (hbounds : ∀ k, 0 < α k ∧ α k < β k ∧ β k < 1)
          (V : Set S) (hFV : ∀ k, (F k).source ⊆ V)
          (hEsub : ∀ k, (F k).source ⊆ (e k).source)
          (hEdis : ∀ i j, i ≠ j → Disjoint (F i).source (F j).source)
          (hEmarks : ∀ k, Disjoint (F k).source (M.cover.branch : Set S))
          (hEsquare : ∀ k, Plane.closedSquare 0 1 ⊆ (F k).target)
          (hcentral : ∀ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source)
          (hEends : ∀ k, F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) = Plane.mk (-1) 0 ∧
            F k ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) = Plane.mk 1 0)
          (hEcurve : ∀ k x, x ∈ (F k).source → (x ∈ a.val.image ↔ F k x 1 = 0))
          (hEslice : ∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ a.val.image =
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
          (hlabel : ∀ k j x, x ∈ (e k).source →
            (x ∈ (old j).val.image ↔ label k = some j ∧ e k x 0 = 0))
          (hends : ∀ k j, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∉ (old j).val.image ∧
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∉ (old j).val.image)
          (houtside : ∀ j, Disjoint
            (arcInterior M a \ ⋃ k, (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k))
            (old j).val.image) :
          ∃ d : EssentialMarkedArc M, ∃ H : AmbientIsotopy S,
            Quotient.mk (essentialArcSetoid M) d = Quotient.mk (essentialArcSetoid M) a ∧
            d.val.image = H.finalMap '' a.val.image ∧
            (∀ t x, x ∈ M.cover.branch → H.map (t,x)=x) ∧
            (∀ t x, x ∉ V → H.map (t,x)=x) ∧
            ∀ j, (arcInterior M d ∩ (old j).val.image).Finite ∧
              ∀ p ∈ arcInterior M d ∩ (old j).val.image, ArcSurgery.CrossesInDisk M (old j) d p := by
        have hReplacement
            {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
            [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
            (M : HyperellipticModel E S)
            (c : EssentialMarkedArc M) (K : Type) [Fintype K]
            (E : K → OpenPartialHomeomorph S Schoenflies.Plane)
            (V : Set S) (hEV : ∀ k, (E k).source ⊆ V)
            (hdis : ∀ i j, i ≠ j → Disjoint (E i).source (E j).source)
            (hmarks : ∀ k, Disjoint (E k).source (M.cover.branch : Set S))
            (hSquare : ∀ k, Schoenflies.Plane.closedSquare 0 1 ⊆ (E k).target)
            (A : Set Schoenflies.Plane)
            (hA : Schoenflies.IsArcBetween A (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0))
            (hAi : A \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
              Schoenflies.Plane.openSquare 0 1)
            (hc : ∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩
              c.val.image = {x : S | x ∈ (E k).source ∧ E k x ∈ A})
            (B : K → Set Schoenflies.Plane)
            (hB : ∀ k, Schoenflies.IsArcBetween (B k)
              (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0))
            (hBi : ∀ k, B k \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
              Schoenflies.Plane.openSquare 0 1) :
            ∃ H : AmbientIsotopy S, ∃ d : EssentialMarkedArc M,
              d.val.image = H.finalMap '' c.val.image ∧
              Quotient.mk (essentialArcSetoid M) d = Quotient.mk (essentialArcSetoid M) c ∧
              (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
              (∀ t x, x ∉ V → H.map (t,x)=x) ∧
              d.val.image =
                (c.val.image \ ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ A}) ∪
                ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ B k} := by
          classical
          letI : T2Space S := M.sphere.symm.t2Space
          letI : CompactSpace S := M.sphere.symm.compactSpace
          let Ap : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ A}
          let Bp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ B k}
          let Dp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ Plane.openSquare 0 1}
          have hAsquare : A ⊆ Plane.closedSquare 0 1 := by
            intro z hz
            by_cases he : z ∈ ({Plane.mk (-1) 0,Plane.mk 1 0} : Set Plane)
            · rcases he with rfl | he
              · norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk]
              · rw [Set.mem_singleton_iff.mp he]
                norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk]
            · exact Plane.openSquare_subset_closedSquare 0 1 (hAi ⟨hz,he⟩)
          have hApcurve (k : K) : Ap k ⊆ c.val.image := by
            intro z hz
            have hh : z ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩ c.val.image := by
              rw [hc k]
              exact hz
            exact hh.2
          have hDcurve (k : K) : Dp k ∩ c.val.image ⊆ Ap k := by
            intro x hx
            change x ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ A}
            rw [← hc k]
            exact ⟨⟨hx.1.1,Plane.openSquare_subset_closedSquare 0 1 hx.1.2⟩,hx.2⟩
          have hPull (k : K) (F : Set Plane) :
              {x : S | ∃ u : (E k).source, u.val = x ∧
                ((E k).toHomeomorphSourceTarget u : Plane) ∈ F} =
              {x : S | x ∈ (E k).source ∧ E k x ∈ F} := by
            ext x
            constructor
            · rintro ⟨u,rfl,hu⟩
              exact ⟨u.property,hu⟩
            · intro hx
              exact ⟨⟨x,hx.1⟩,rfl,hx.2⟩
          have hpatch (k : K) : ∃ G : AmbientIsotopy S,
              G.finalMap '' Ap k = Bp k ∧ ∀ t x, x ∉ Dp k → G.map (t,x) = x := by
            obtain ⟨G,hGA,hGfix⟩ := position_crosscut_surface_square_support S
              (E k).source (E k).target (E k).open_source (E k).toHomeomorphSourceTarget
              (hSquare k) A (B k) (Plane.mk (-1) 0) (Plane.mk 1 0) hA (hB k)
              (by norm_num [modelCurve,Plane.supNorm,Plane.mk])
              (by norm_num [modelCurve,Plane.supNorm,Plane.mk]) hAi (hBi k)
            rw [hPull,hPull] at hGA
            simp only [hPull] at hGfix
            exact ⟨G,hGA,hGfix⟩
          choose G hGA hGfix using hpatch
          have hGmarks (k : K) (t : Interval) (x : S) (hx : x ∈ M.cover.branch) :
              (G k).map (t,x) = x := by
            apply hGfix k t x
            intro hD
            exact Set.disjoint_left.mp (hmarks k) hD.1 hx
          have hfixRest (k : K) (x : S) (hx : x ∈ c.val.image \ Ap k) : (G k).finalMap x = x := by
            apply hGfix k ⟨1,by norm_num⟩
            intro hD
            exact hx.2 (hDcurve k ⟨hD,hx.1⟩)
          have hfixOther (k j : K) (hkj : k ≠ j) (x : S) (hx : x ∈ (E j).source) :
              (G k).finalMap x = x := by
            apply hGfix k ⟨1,by norm_num⟩
            intro hD
            exact Set.disjoint_left.mp (hdis k j hkj) hD.1 hx
          have hcompose (H G : AmbientIsotopy S) :
              ∃ K : AmbientIsotopy S, ∀ t x, K.map (t,x) = G.map (t,H.map (t,x)) := by
            refine ⟨{
              map := ⟨fun z => G.map (z.1,H.map z),
              G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
              homeomorphism_at := ?_, at_zero := ?_ },fun _ _ => rfl⟩
            · intro t
              obtain ⟨e,he⟩ := H.homeomorphism_at t
              obtain ⟨f,hf⟩ := G.homeomorphism_at t
              exact ⟨e.trans f,fun x => (hf (e x)).trans
                (congrArg (fun z => G.map (t,z)) (he x))⟩
            · intro x
              change G.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x)) = x
              rw [H.at_zero,G.at_zero]
          let As : Finset K → Set S := fun P => ⋃ k ∈ P, Ap k
          let Bs : Finset K → Set S := fun P => ⋃ k ∈ P, Bp k
          have hbuild (P : Finset K) : ∃ H : AmbientIsotopy S,
              H.finalMap '' c.val.image = (c.val.image \ As P) ∪ Bs P ∧
              (∀ t x, x ∈ M.cover.branch → H.map (t,x) = x) ∧
              (∀ t x, x ∉ V → H.map (t,x)=x) := by
            induction P using Finset.induction_on with
            | empty =>
              let H : AmbientIsotopy S := {
                map := ⟨fun z => z.2,continuous_snd⟩
                homeomorphism_at := fun _ => ⟨Homeomorph.refl S,fun _ => rfl⟩
                at_zero := fun _ => rfl }
              refine ⟨H,?_,(fun _ _ _ => rfl),(fun _ _ _ => rfl)⟩
              change (fun x : S => x) '' c.val.image = _
              simp [As,Bs]
            | @insert k P hk ih =>
              obtain ⟨H,hH,hHmarks,hHout⟩ := ih
              have hAsinsert : As (insert k P) = Ap k ∪ As P := by simp [As]
              have hBsinsert : Bs (insert k P) = Bp k ∪ Bs P := by simp [Bs]
              have hnotAs (x : S) (hx : x ∈ Ap k) : x ∉ As P := by
                intro h
                obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp h
                have hkj : k ≠ j := fun he => hk (he.symm ▸ hj)
                exact Set.disjoint_left.mp (hdis k j hkj) hx.1 hxj.1
              let R : Set S := (c.val.image \ As (insert k P)) ∪ Bs P
              have hdecomp : (c.val.image \ As P) ∪ Bs P = Ap k ∪ R := by
                ext x
                constructor
                · intro hx
                  rcases hx with hx | hx
                  · by_cases hxA : x ∈ Ap k
                    · exact Or.inl hxA
                    · exact Or.inr (Or.inl ⟨hx.1,by rw [hAsinsert]; exact fun h => h.elim hxA hx.2⟩)
                  · exact Or.inr (Or.inr hx)
                · intro hx
                  rcases hx with hx | hx
                  · exact Or.inl ⟨hApcurve k hx,hnotAs x hx⟩
                  · rcases hx with hx | hx
                    · exact Or.inl ⟨hx.1,fun h => hx.2 (hAsinsert.symm ▸ Or.inr h)⟩
                    · exact Or.inr hx
              have hRfix (x : S) (hx : x ∈ R) : (G k).finalMap x = x := by
                rcases hx with hx | hx
                · apply hfixRest k x
                  refine ⟨hx.1,?_⟩
                  intro h
                  exact hx.2 (hAsinsert.symm ▸ Or.inl h)
                · obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp hx
                  exact hfixOther k j (fun he => hk (he.symm ▸ hj)) x hxj.1
              have hGR : (G k).finalMap '' R = R := by
                ext x
                constructor
                · rintro ⟨y,hy,rfl⟩
                  simpa [hRfix y hy] using hy
                · intro hx
                  exact ⟨x,hx,hRfix x hx⟩
              have hnew : (G k).finalMap '' ((c.val.image \ As P) ∪ Bs P) =
                  (c.val.image \ As (insert k P)) ∪ Bs (insert k P) := by
                rw [hdecomp,Set.image_union,hGA k,hGR,hBsinsert]
                change Bp k ∪ ((c.val.image \ As (insert k P)) ∪ Bs P) =
                  (c.val.image \ As (insert k P)) ∪ (Bp k ∪ Bs P)
                ext x
                simp only [Set.mem_union]
                tauto
              obtain ⟨F,hF⟩ := hcompose H (G k)
              refine ⟨F,?_,?_,?_⟩
              · have hmaps : F.finalMap = (G k).finalMap ∘ H.finalMap :=
                  funext (hF ⟨1,by norm_num⟩)
                calc
                  F.finalMap '' c.val.image = (G k).finalMap '' (H.finalMap '' c.val.image) := by
                    rw [Set.image_image,hmaps]
                    rfl
                  _ = _ := by rw [hH,hnew]
              · intro t x hx
                rw [hF,hHmarks t x hx]
                exact hGmarks k t x hx
              · intro t x hx
                rw [hF,hHout t x hx]
                apply hGfix k t x
                exact fun hD => hx (hEV k hD.1)
          obtain ⟨H,hH,hHmarks,hHout⟩ := hbuild Finset.univ
          obtain ⟨h,hh⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
          have hfinal : H.finalMap = h := funext (fun x => (hh x).symm)
          have hfix : ∀ x, x ∈ M.cover.branch → h x = x := by
            intro x hx
            rw [← hfinal]
            exact hHmarks ⟨1,by norm_num⟩ x hx
          let d := c.transport h hfix
          have hd : d.val.image = H.finalMap '' c.val.image := by
            rw [hfinal]
            exact MarkedArc.transport_image c.val h hfix
          refine ⟨H,d,hd,?_,hHmarks,hHout,?_⟩
          · apply Eq.symm
            apply Quotient.sound
            exact ⟨H,hHmarks,hd.symm⟩
          · rw [hd,hH]
            simp [As,Bs,Ap,Bp]
        classical
        have hhorizontal : segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) =
            {z : Schoenflies.Plane | z ∈ Schoenflies.Plane.closedSquare 0 1 ∧ z 1 = 0} := by
          ext z
          constructor
          · intro hz
            rw [segment_eq_image_lineMap] at hz
            obtain ⟨t,ht,rfl⟩ := hz
            have h0 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
                (Schoenflies.Plane.mk 1 0) t) 0 = 2*t-1 := by
              simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
            have h1 : (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0)
                (Schoenflies.Plane.mk 1 0) t) 1 = 0 := by
              simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]
            refine ⟨?_,h1⟩
            change Schoenflies.Plane.supDist (AffineMap.lineMap (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) t) 0 ≤ 1
            simp only [Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,sub_zero]
            rw [h0,h1,abs_zero,max_le_iff]
            constructor
            · rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
            · norm_num
          · intro hz
            have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
              simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hz.1
            have hbound : |z 0| ≤ 1 :=
              (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
            rw [abs_le] at hbound
            rw [segment_eq_image_lineMap]
            refine ⟨(z 0+1)/2,⟨by linarith [hbound.1],by linarith [hbound.2]⟩,?_⟩
            ext i
            fin_cases i
            · simp [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk]; ring
            · simpa [AffineMap.lineMap_apply_module,Schoenflies.Plane.mk] using hz.2.symm
        let A : Set Schoenflies.Plane := segment ℝ (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0)
        have hA : Schoenflies.IsArcBetween A (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) :=
          Schoenflies.isArcBetween_segment (by intro h; have hh := congrArg (fun z : Schoenflies.Plane => z 0) h; norm_num [Schoenflies.Plane.mk] at hh)
        have hAi : A \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆
            Schoenflies.Plane.openSquare 0 1 := by
          intro z hz
          have hzline := hhorizontal.le hz.1
          have h0 : |z 0| ≤ 1 := by
            have hnorm : Schoenflies.Plane.supNorm z ≤ 1 := by
              simpa [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist] using hzline.1
            exact (Schoenflies.Plane.abs_zero_le_supNorm z).trans hnorm
          have hne0 : z 0 ≠ -1 := by
            intro h
            apply hz.2
            left
            ext i
            fin_cases i
            · simpa [Schoenflies.Plane.mk] using h
            · simpa [Schoenflies.Plane.mk] using hzline.2
          have hne1 : z 0 ≠ 1 := by
            intro h
            apply hz.2
            right
            apply Set.mem_singleton_iff.mpr
            ext i
            fin_cases i
            · simpa [Schoenflies.Plane.mk] using h
            · simpa [Schoenflies.Plane.mk] using hzline.2
          rw [Schoenflies.Plane.mem_openSquare_iff]
          intro i
          fin_cases i
          · simp only [PiLp.zero_apply,sub_zero]
            rw [abs_lt]
            exact ⟨lt_of_le_of_ne (abs_le.mp h0).1 hne0.symm,
              lt_of_le_of_ne (abs_le.mp h0).2 hne1⟩
          · simp [hzline.2]
        have hselected (k : K) :
            {x : S | x ∈ (F k).source ∧ F k x ∈ A} =
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
          rw [← hEslice k]
          ext x
          constructor
          · intro hx
            have hz := hhorizontal.le hx.2
            exact ⟨⟨hx.1,hz.1⟩,(hEcurve k x hx.1).mpr hz.2⟩
          · intro hx
            exact ⟨hx.1.1,hhorizontal.ge ⟨hx.1.2,(hEcurve k x hx.1.1).mp hx.2⟩⟩
        have hactual (k : K) :
            {x : S | x ∈ (F k).source ∧ F k x ∈ Schoenflies.Plane.closedSquare 0 1} ∩ a.val.image =
            {x : S | x ∈ (F k).source ∧ F k x ∈ A} := (hEslice k).trans (hselected k).symm
        let T : K → OpenPartialHomeomorph Schoenflies.Plane Schoenflies.Plane :=
          fun k => (F k).symm.trans (e k)
        have hTsquare (k : K) : Schoenflies.Plane.closedSquare 0 1 ⊆ (T k).source := by
          intro z hz
          have hzE : z ∈ (F k).target := hEsquare k hz
          exact ⟨hzE,hEsub k ((F k).symm.map_source hzE)⟩
        have hleftSource (k : K) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) ∈ (F k).source :=
          hcentral k (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr (hbounds k).2.1.le))
        have hrightSource (k : K) : (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) ∈ (F k).source :=
          hcentral k (Set.mem_image_of_mem _ (Set.right_mem_Icc.mpr (hbounds k).2.1.le))
        have hleftInv (k : K) : (F k).symm (Schoenflies.Plane.mk (-1) 0) =
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) := by
          rw [← (hEends k).1,(F k).left_inv (hleftSource k)]
        have hrightInv (k : K) : (F k).symm (Schoenflies.Plane.mk 1 0) =
            (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) := by
          rw [← (hEends k).2,(F k).left_inv (hrightSource k)]
        have hTargets (k : K) : ∃ B : Set Schoenflies.Plane,
            Schoenflies.IsArcBetween B (Schoenflies.Plane.mk (-1) 0) (Schoenflies.Plane.mk 1 0) ∧
            B \ {Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} ⊆ Schoenflies.Plane.openSquare 0 1 ∧
            ∀ j, label k = some j → ((T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0}).Finite ∧
              ∀ p ∈ (T k '' B) ∩ {z : Schoenflies.Plane | z 0 = 0},
              ∃ W : Set Schoenflies.Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ (T k).target ∧
              ∃ m : ℝ, ∀ z ∈ W, (z ∈ T k '' B ↔ z 1 = p 1 + m*z 0) := by
          cases hL : label k with
          | none =>
            refine ⟨A,hA,hAi,?_⟩
            intro j hj
            cases hj
          | some j =>
            have ha0 : T k (Schoenflies.Plane.mk (-1) 0) 0 ≠ 0 := by
              intro h0
              have hh : (e k) ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k)) 0 = 0 := by
                simpa only [T,OpenPartialHomeomorph.trans_apply,hleftInv] using h0
              exact (hends k j).1 ((hlabel k j _ (hEsub k (hleftSource k))).mpr ⟨hL,hh⟩)
            have hb0 : T k (Schoenflies.Plane.mk 1 0) 0 ≠ 0 := by
              intro h0
              have hh : (e k) ((a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k)) 0 = 0 := by
                simpa only [T,OpenPartialHomeomorph.trans_apply,hrightInv] using h0
              exact (hends k j).2 ((hlabel k j _ (hEsub k (hrightSource k))).mpr ⟨hL,hh⟩)
            obtain ⟨B,hB,hBi,hfinite,hgraph⟩ := position_proper_affine_crosscut (T k) (hTsquare k) ha0 hb0
            exact ⟨B,hB,hBi,fun _ _ => ⟨hfinite,hgraph⟩⟩
        choose B hB hBi hBcontrol using hTargets
        obtain ⟨G,d,hdimage,hdclass,hGmarks,hGout,hdreplace⟩ := hReplacement
          M a K F V hFV hEdis hEmarks hEsquare A hA hAi hactual B hB hBi
        let Bp : K → Set S := fun k => {x | x ∈ (F k).source ∧ F k x ∈ B k}
        have hfinite (k : K) (j : ι) : (Bp k ∩ (old j).val.image).Finite := by
          by_cases hj : label k = some j
          · apply (((hBcontrol k j hj).1).image (e k).symm).subset
            rintro x ⟨hx,hxold⟩
            have hxE : x ∈ (e k).source := hEsub k hx.1
            refine ⟨e k x,⟨?_,((hlabel k j x hxE).mp hxold).2⟩,(e k).left_inv hxE⟩
            refine ⟨F k x,hx.2,?_⟩
            simp only [T,OpenPartialHomeomorph.trans_apply]
            rw [(F k).left_inv hx.1]
          · apply Set.Finite.subset Set.finite_empty
            rintro x ⟨hx,hxold⟩
            exact (hj ((hlabel k j x (hEsub k hx.1)).mp hxold).1).elim
        have hfiniteD (j : ι) : (arcInterior M d ∩ (old j).val.image).Finite := by
          apply (Set.finite_iUnion (fun k => hfinite k j)).subset
          rintro x ⟨hx,hxold⟩
          have hximage : x ∈ d.val.image := hx.1
          rw [hdreplace] at hximage
          rcases hximage with hxrest | hxnew
          · have hxA : x ∈ arcInterior M a := ⟨hxrest.1,hx.2⟩
            have hxoutside : x ∈ arcInterior M a \ ⋃ k,
                (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
              refine ⟨hxA,?_⟩
              intro hh
              obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
              exact hxrest.2 (Set.mem_iUnion.mpr ⟨k,(hselected k).symm ▸ hk⟩)
            exact (Set.disjoint_left.mp (houtside j) hxoutside hxold).elim
          · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hxnew
            exact Set.mem_iUnion.mpr ⟨k,hk,hxold⟩
        have hBsq (k : K) : B k ⊆ Schoenflies.Plane.closedSquare 0 1 := by
          intro z hz
          by_cases he : z ∈ ({Schoenflies.Plane.mk (-1) 0,Schoenflies.Plane.mk 1 0} : Set Schoenflies.Plane)
          · rcases he with rfl | he
            · norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
            · rw [Set.mem_singleton_iff.mp he]
              norm_num [Schoenflies.Plane.closedSquare,Schoenflies.Plane.supDist,Schoenflies.Plane.supNorm,Schoenflies.Plane.mk]
          · exact Schoenflies.Plane.openSquare_subset_closedSquare 0 1 (hBi k ⟨hz,he⟩)
        have hd2local (k : K) (x : S) (hx : x ∈ (F k).source)
            (hxo : F k x ∈ Schoenflies.Plane.openSquare 0 1) :
            x ∈ d.val.image ↔ F k x ∈ B k := by
          rw [hdreplace]
          constructor
          · intro h
            rcases h with h | h
            · have hAselect : x ∈ {x : S | x ∈ (F k).source ∧ F k x ∈ A} := by
                rw [← hactual k]
                exact ⟨⟨hx,Schoenflies.Plane.openSquare_subset_closedSquare 0 1 hxo⟩,h.1⟩
              exact False.elim (h.2 (Set.mem_iUnion.mpr ⟨k,hAselect⟩))
            · obtain ⟨l,hl⟩ := Set.mem_iUnion.mp h
              by_cases hkl : k = l
              · subst l
                exact hl.2
              · exact False.elim (Set.disjoint_left.mp (hEdis k l hkl) hx hl.1)
          · intro h
            exact Or.inr (Set.mem_iUnion.mpr ⟨k,hx,h⟩)
        have hTimage (k : K) (x : S) (hx : x ∈ (F k).source) :
            e k x ∈ T k '' B k ↔ F k x ∈ B k := by
          constructor
          · rintro ⟨z,hz,heq⟩
            have hzT := hTsquare k (hBsq k hz)
            have hzE : z ∈ (F k).target := hzT.1
            have hze : (F k).symm z ∈ (e k).source := hzT.2
            have hsymm : (F k).symm z = x :=
              (e k).injOn hze (hEsub k hx) heq
            have hzcoord : z = F k x := by rw [← hsymm,(F k).right_inv hzE]
            exact hzcoord ▸ hz
          · intro hz
            refine ⟨F k x,hz,?_⟩
            change e k ((F k).symm (F k x)) = e k x
            rw [(F k).left_inv hx]
        refine ⟨d,G,hdclass,hdimage,hGmarks,hGout,?_⟩
        intro j
        refine ⟨hfiniteD j,?_⟩
        intro p hp
        have hpBunion : p ∈ ⋃ k, {x : S | x ∈ (F k).source ∧ F k x ∈ B k} := by
          have hpd : p ∈ d.val.image := hp.1.1
          rw [hdreplace] at hpd
          rcases hpd with hrem | hBmem
          · have hrem' : p ∈ arcInterior M a \ ⋃ k,
                (a.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
              refine ⟨⟨hrem.1,hp.1.2⟩,?_⟩
              intro hh
              obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hh
              exact hrem.2 (Set.mem_iUnion.mpr ⟨k,(hselected k).symm ▸ hk⟩)
            exact False.elim (Set.disjoint_left.mp (houtside j) hrem' hp.2)
          · exact hBmem
        obtain ⟨k,hpk⟩ := Set.mem_iUnion.mp hpBunion
        have hpe : p ∈ (e k).source := hEsub k hpk.1
        have hplabel : label k = some j := ((hlabel k j p hpe).mp hp.2).1
        have hp0 : e k p 0 = 0 := ((hlabel k j p hpe).mp hp.2).2
        have hpint : F k p ∈ Schoenflies.Plane.openSquare 0 1 := by
          apply hBi k
          refine ⟨hpk.2,?_⟩
          intro he
          rcases he with he | he
          · have hpa : p = (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (α k) := by
              rw [← hleftInv k,← he,(F k).left_inv hpk.1]
            exact (hends k j).1 (hpa ▸ hp.2)
          · have hpb : p = (a.val.map ∘ Set.projIcc 0 1 zero_le_one) (β k) := by
              rw [← hrightInv k,← Set.mem_singleton_iff.mp he,(F k).left_inv hpk.1]
            exact (hends k j).2 (hpb ▸ hp.2)
        have hpT : e k p ∈ T k '' B k := (hTimage k p hpk.1).mpr hpk.2
        obtain ⟨W,hWo,hpW,hWtarget,m,hm⟩ := (hBcontrol k j hplabel).2 (e k p) ⟨hpT,hp0⟩
        have hnear : (F k).source ∩ ((F k) ⁻¹' Schoenflies.Plane.openSquare 0 1 ∩ (e k) ⁻¹' W) ∈ nhds p :=
          Filter.inter_mem ((F k).open_source.mem_nhds hpk.1)
            (Filter.inter_mem (((F k).continuousAt hpk.1).preimage_mem_nhds
              ((Schoenflies.Plane.isOpen_openSquare 0 1).mem_nhds hpint))
              (((e k).continuousAt hpe).preimage_mem_nhds (hWo.mem_nhds hpW)))
        obtain ⟨V,hVsub,hVo,hpV⟩ := mem_nhds_iff.mp hnear
        let F := (e k).restr V
        have hFsource : F.source = (e k).source ∩ V := by
          rw [OpenPartialHomeomorph.restr_source,hVo.interior_eq]
        have hpF : p ∈ F.source := hFsource.symm ▸ ⟨hpe,hpV⟩
        apply actual_affine_graph_crosses_in_disk M (old j) d F p hpF
          ((hEmarks k).mono (fun x hx => (hVsub (hFsource.le hx).2).1) Set.Subset.rfl) hp0 m
        · intro x hx
          have hxe := (hFsource.le hx).1
          change x ∈ (old j).val.image ↔ e k x 0 = 0
          simpa only [hplabel,eq_self,true_and] using hlabel k j x hxe
        · intro x hx
          have hxV := (hFsource.le hx).2
          have hxloc := hVsub hxV
          change x ∈ d.val.image ↔ e k x 1 = e k p 1+m*e k x 0
          rw [hd2local k x hxloc.1 hxloc.2.1,← hTimage k x hxloc.1]
          exact hm (e k x) hxloc.2.2
      obtain ⟨old',a1,H0,K0,δ,hδ,hδhalf,hclassesOld,hdisOld,hclassA,hH0marks,hH0out,hK0marks,hK0out,hOldmap,hAmap,ha1V,hclear,
        η,hη,hi,n,hn,e,label,hemarks,hlabel,hchart,hends⟩ :=
        hPrepared M (actualSphereSmoothAtlas M) old hclasses hd a
          (actualRepresentative_nonloop M a ha) V hV haV
      have hlu : δ < 1-δ := by linarith
      have hu : 1-δ < 1 := by linarith
      have hη' (t : Interval) : η t = a1.val.map
          ⟨δ+((1-δ)-δ)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩ := by
        rw [hη]
        apply congrArg a1.val.map; apply Subtype.ext
        change δ+(1-2*δ)*(t:ℝ) = δ+((1-δ)-δ)*(t:ℝ)
        ring
      obtain ⟨α,β,F,hbounds,hFsub,hFV,hFdis,hFmarks,hFsq,hFends,hFflat,hFexact,hFoff,houtside⟩ :=
        hCrosscuts M old' a1 V hV ha1V δ (1-δ) hδ hlu hu η hη'
          hi.injective n hn e hemarks hchart hends hclear
      have hcentral (k : Fin n) :
          (a1.val.map ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source := by
        intro x hx
        rw [← hFexact k] at hx
        exact hx.1.1
      obtain ⟨b,G,hbclass,hbimage,hGmarks,hGout,hfinite⟩ := hRedrawing M old' a1
        e F label α β hbounds V hFV hFsub hFdis hFmarks hFsq hcentral hFends hFflat hFexact
        hlabel hFoff houtside
      have hAimage : a1.val.image = K0.finalMap '' a.val.image := by
        change Set.range a1.val.map = K0.finalMap '' Set.range a.val.map
        rw [←Set.range_comp]
        exact congrArg Set.range (funext hAmap)
      refine ⟨old',b,H0,K0.compose G,hclassesOld,hdisOld,hbclass.trans hclassA,
        hH0marks,hH0out,?_,?_,?_,?_,?_,hfinite⟩
      · intro t x hx
        change G.map (t,K0.map (t,x))=x
        rw [hK0marks t x hx,hGmarks t x hx]
      · intro t x hx
        change G.map (t,K0.map (t,x))=x
        rw [hK0out t x hx,hGout t x hx]
      · intro i
        change Set.range (old' i).val.map = H0.finalMap '' Set.range (old i).val.map
        rw [←Set.range_comp]
        exact congrArg Set.range (funext (hOldmap i))
      · rw [hbimage,hAimage,AmbientIsotopy.compose_finalMap,Set.image_comp]
      · obtain ⟨g,hg⟩ := G.homeomorphism_at 1
        have he : G.finalMap = g := funext (fun x => (hg x).symm)
        intro x hx
        rw [hbimage,he] at hx
        obtain ⟨y,hy,rfl⟩ := hx
        by_contra hn
        have hgg : g (g y)=g y := (congrFun he (g y)).symm.trans (hGout 1 _ hn)
        have hyy := g.injective hgg
        rw [hyy] at hn
        exact hn (ha1V hy)
    
    classical
    have hn (c : NonLoopArc M) :
        ¬ (actualArcLabels M).isLoop (Quotient.mk (essentialArcSetoid M) c.toEssential) := by
      change ({c.val.map 0,c.val.map 1}:Finset S).card ≠ 1
      have hc : c.val.map 0 ≠ c.val.map 1 := by convert c.property using 1
      rw [Finset.card_pair hc]
      norm_num
    obtain ⟨old',b0,H,K,hold,hdis,hbclass,hHmarks,hHout,hKmarks,hKout,hOldimage,hBimage,hBinside,hfinite⟩ :=
      hContacts M (fun _ : Unit => a.toEssential) (fun _ => hn a)
        (fun i j hij => False.elim (hij (Subsingleton.elim _ _)))
        b.toEssential (hn b) (interior N.closedSet) isOpen_interior hb
    have hna : ¬ (actualArcLabels M).isLoop
        (Quotient.mk (essentialArcSetoid M) (old' ())) := by rw [hold ()]; exact hn a
    have hnb : ¬ (actualArcLabels M).isLoop
        (Quotient.mk (essentialArcSetoid M) b0) := by rw [hbclass]; exact hn b
    let a' : NonLoopArc M := ⟨(old' ()).val,M.actualRepresentative_nonloop (old' ()) hna⟩
    let b' : NonLoopArc M := ⟨b0.val,M.actualRepresentative_nonloop b0 hnb⟩
    have hsub : ArcSurgery.crossings M a'.toEssential b'.toEssential ⊆ arcInterior M b0 ∩ (old' ()).val.image := by
      intro p hp
      exact ⟨hp.2,hp.1.1⟩
    refine ⟨a',b',H,K,hHout,hKout,hHmarks,hKmarks,(hOldimage ()).symm,hBimage.symm,?_,hBinside,
      (hfinite ()).1.subset hsub,(fun p hp => (hfinite ()).2 p (hsub hp))⟩
    obtain ⟨g,hg⟩ := H.homeomorphism_at 1
    have he : H.finalMap = g := funext (fun x => (hg x).symm)
    intro x hx
    change x ∈ (old' ()).val.image at hx
    rw [hOldimage (),he] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    by_contra hh
    have hgg : g (g y)=g y := (congrFun he (g y)).symm.trans (hHout 1 _ hh)
    have hyy := g.injective hgg
    rw [hyy] at hh
    exact hh (N.arc_inside hy)

end CurveComplex.HyperellipticModel
