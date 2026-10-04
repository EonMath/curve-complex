import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalAnnulusExtensionSourceLocal

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 16000000

-- One actual supported G3 motion of BOTH original full boundary components, preserving the entire given midpoint.
example (M : HyperellipticModel E S) (a : NonLoopArc M) (N : ArcNeighborhood a)
    (h : E ≃ₜ E)
    (T : Circle × Interval ≃ₜ h '' (M.cover.projection ⁻¹' N.closedSet))
    (hTb : Set.range (fun z : Circle => (T (z,0)).val) ∪
      Set.range (fun z : Circle => (T (z,1)).val) =
      h '' (M.cover.projection ⁻¹' N.boundary.image)) :
    ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
      H.finalMap '' (h '' (M.cover.projection ⁻¹' N.boundary.image)) =
        Set.range (fun z : Circle => (T (z,⟨1/4,by norm_num⟩)).val) ∪
          Set.range (fun z : Circle => (T (z,⟨3/4,by norm_num⟩)).val) ∧
      (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
        (T (z,⟨1/2,by norm_num⟩)).val) ∧
      (∀ t x, J (t,H.map (t,x)) = x) ∧
      (∀ t x, H.map (t,J (t,x)) = x) := by
  audit_main14_base3
    have hExtension : ∃ Q : C(Circle × Interval,E), Topology.IsEmbedding Q ∧
          (∀ z, Q (z,⟨1/3,by norm_num⟩) = (T (z,0)).val) ∧
          (∀ z, Q (z,⟨2/3,by norm_num⟩) = (T (z,1)).val) ∧
          (∀ z (s : Interval), Q (z,⟨((s:ℝ)+1)/3,by constructor <;> linarith [s.property.1,s.property.2]⟩) =
            (T (z,s)).val) ∧
          IsOpen (Q '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
      audit_main14_base3
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        let U := h '' (M.cover.projection ⁻¹' N.closedSet)
        have hfront : Set.range (fun z : Circle => (T (z,0)).val) ∪
              Set.range (fun z : Circle => (T (z,1)).val) =
              frontier (h '' (M.cover.projection ⁻¹' N.closedSet)) := by
          audit_main14_base3
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            letI : T2Space S := M.sphere.symm.t2Space
            have hopen : IsOpenMap M.cover.projection := by
              have hcl : IsClosedMap M.cover.projection := M.cover.projection_continuous.isClosedMap
              have hq := hcl.isQuotientMap M.cover.projection_continuous M.cover.projection_surjective
              intro U hU
              rw [← hq.isCoinducing.isOpen_preimage]
              have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
                  U ∪ M.cover.deck ⁻¹' U := by
                ext x
                constructor
                · rintro ⟨y,hy,hxy⟩
                  rcases (M.cover.fiber_pair x y).mp hxy.symm with hh | hh
                  · exact Or.inl (hh ▸ hy)
                  · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [hh] using hy)
                · rintro (hx | hx)
                  · exact ⟨x,hx,rfl⟩
                  · exact ⟨M.cover.deck x,hx,M.cover.projection_deck x⟩
              rw [heq]
              exact hU.union (hU.preimage M.cover.deck.continuous)
            rw [hTb,N.boundary_eq_frontier,
              hopen.preimage_frontier_eq_frontier_preimage M.cover.projection_continuous,
              h.image_frontier]
        have hCollars (U W : Set E)
            (T : Circle × Interval ≃ₜ U) (A : Circle × Interval ≃ₜ W)
            (hWdis : Disjoint W (Set.range (fun z : Circle => (T (z,0)).val) ∪
              Set.range (fun z : Circle => (T (z,1)).val))) :
            ∃ e₀ e₁ : C(Set.Ioo (-1:ℝ) 1 × Circle,E), ∃ ε₀ ε₁ : ℝ,
              Topology.IsOpenEmbedding e₀ ∧ Topology.IsOpenEmbedding e₁ ∧
              (∀ z, e₀ (⟨0,by norm_num⟩,z) = (T (z,0)).val) ∧
              (∀ z, e₁ (⟨0,by norm_num⟩,z) = (T (z,1)).val) ∧
              0 < ε₀ ∧ ε₀ < 1 ∧ 0 < ε₁ ∧ ε₁ < 1 ∧
              Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀})
                (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁}) ∧
              Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀}) W ∧
              Disjoint (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁}) W := by
          audit_main14_base3
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            letI : CompactSpace W := A.compactSpace
            have hWclosed : IsClosed W := by
              have hh := (isCompact_univ : IsCompact (Set.univ : Set W)).image
                (continuous_subtype_val : Continuous (Subtype.val : W → E))
              have he : (Subtype.val : W → E) '' Set.univ = W := by
                rw [Set.image_univ,Subtype.range_coe_subtype]
                rfl
              exact (he ▸ hh).isClosed
            let c₀ : Curve E := ⟨fun z => (T (z,0)).val,
              Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 0))⟩
            let c₁ : Curve E := ⟨fun z => (T (z,1)).val,
              Topology.IsEmbedding.subtypeVal.comp (T.isEmbedding.comp (isEmbedding_prodMkLeft 1))⟩
            have hd : Disjoint c₀.image c₁.image := by
              apply Set.disjoint_left.mpr
              rintro x ⟨z,hz⟩ ⟨w,hw⟩
              have hh := T.injective (Subtype.ext (hz.trans hw.symm))
              have hu := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
              norm_num at hu
            have hc₀ : IsClosed c₀.image := by
              simpa [Curve.image] using (isCompact_univ.image c₀.embedded.continuous).isClosed
            have hc₁ : IsClosed c₁.image := by
              simpa [Curve.image] using (isCompact_univ.image c₁.embedded.continuous).isClosed
            obtain ⟨O₀,O₁,hO₀,hO₁,hcO₀,hcO₁,hOdis⟩ := normal_separation hc₀ hc₁ hd
            let V₀ := O₀ ∩ Wᶜ
            let V₁ := O₁ ∩ Wᶜ
            have hV₀ : IsOpen V₀ := hO₀.inter hWclosed.isOpen_compl
            have hV₁ : IsOpen V₁ := hO₁.inter hWclosed.isOpen_compl
            have hcV₀ (z : Circle) : c₀.map z ∈ V₀ := by
              refine ⟨hcO₀ (Set.mem_range_self z),?_⟩
              intro hw
              exact Set.disjoint_left.mp hWdis hw (Or.inl (Set.mem_range_self z))
            have hcV₁ (z : Circle) : c₁.map z ∈ V₁ := by
              refine ⟨hcO₁ (Set.mem_range_self z),?_⟩
              intro hw
              exact Set.disjoint_left.mp hWdis hw (Or.inr (Set.mem_range_self z))
            have hcollar (c : Curve E) : ∃ e : C(Set.Ioo (-1:ℝ) 1 × Circle,E),
                Topology.IsOpenEmbedding e ∧ ∀ z, e (⟨0,by norm_num⟩,z) = c.map z := by
              rcases LocalSurgery.embedded_circle_annular_collar_or_local_reflection E c with hc | ⟨x,⟨F⟩⟩
              · exact hc
              · exact False.elim (GenusOrientationCandidate.no_local_reflection_witness 2 M.genusTwo x
                  (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) F)
            obtain ⟨e₀,he₀,hcenter₀⟩ := hcollar c₀
            obtain ⟨e₁,he₁,hcenter₁⟩ := hcollar c₁
            -- Uniform restriction is the actual G3 compact-circle clearance argument.
            have hclear (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (O : Set E)
                (hO : IsOpen O) (hcenter : ∀ z, e (⟨0,by norm_num⟩,z) ∈ O) :
                ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
                  ∀ w : Set.Ioo (-1:ℝ) 1, |(w:ℝ)| < ε → ∀ z : Circle, e (w,z) ∈ O := by
              let w0 : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
              let Ω := e ⁻¹' O
              have hΩ : IsOpen Ω := hO.preimage e.continuous
              have hbase : ({w0} : Set (Set.Ioo (-1:ℝ) 1)) ×ˢ (Set.univ : Set Circle) ⊆ Ω := by
                rintro ⟨w,z⟩ ⟨hw,_⟩
                have hh : w = w0 := hw
                subst w
                exact hcenter z
              obtain ⟨P,Q,hP,hQ,h0,hall,hPQ⟩ :=
                generalized_tube_lemma isCompact_singleton
                  (isCompact_univ : IsCompact (Set.univ : Set Circle)) hΩ hbase
              have hw0 : w0 ∈ P := h0 (Set.mem_singleton w0)
              obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hP.mem_nhds hw0)
              let ε := min δ (1/2)
              have hε : 0 < ε := lt_min hδ (by norm_num)
              refine ⟨ε,hε,lt_of_le_of_lt (min_le_right _ _) (by norm_num),?_⟩
              intro w hw z
              have hwd : |(w:ℝ)| < δ := lt_of_lt_of_le hw (min_le_left _ _)
              have hwP : w ∈ P := hball (by
                change dist (w:ℝ) (w0:ℝ) < δ
                simpa [w0,Real.dist_eq] using hwd)
              exact hPQ ⟨hwP,hall (Set.mem_univ z)⟩
            obtain ⟨ε₀,hε₀,hε₀one,hclear₀⟩ := hclear e₀ V₀ hV₀ (fun z => by rw [hcenter₀]; exact hcV₀ z)
            obtain ⟨ε₁,hε₁,hε₁one,hclear₁⟩ := hclear e₁ V₁ hV₁ (fun z => by rw [hcenter₁]; exact hcV₁ z)
            refine ⟨e₀,e₁,ε₀,ε₁,he₀,he₁,hcenter₀,hcenter₁,hε₀,hε₀one,hε₁,hε₁one,?_,?_,?_⟩
            · apply Set.disjoint_left.mpr
              rintro x ⟨p,hp,hpe⟩ ⟨q,hq,hqe⟩
              have h0 := (hclear₀ p.1 hp p.2).1
              have h1 := (hclear₁ q.1 hq q.2).1
              rw [hpe] at h0
              rw [hqe] at h1
              exact Set.disjoint_left.mp hOdis h0 h1
            · apply Set.disjoint_left.mpr
              rintro x ⟨p,hp,rfl⟩ hw
              exact (hclear₀ p.1 hp p.2).2 hw
            · apply Set.disjoint_left.mpr
              rintro x ⟨p,hp,rfl⟩ hw
              exact (hclear₁ p.1 hp p.2).2 hw
        have hSide (U : Set E)
            (T : Circle × Interval ≃ₜ U)
            (hfront : Set.range (fun z : Circle => (T (z,0)).val) ∪
              Set.range (fun z : Circle => (T (z,1)).val) = frontier U)
            (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
            (hcenter : ∀ z, e (⟨0,by norm_num⟩,z) = (T (z,0)).val)
            (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
            (hclear : Disjoint (e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε})
              (Set.range (fun z : Circle => (T (z,1)).val))) :
            (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∈ interior U) ∧
              (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U) ∨
            (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∧
              (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∈ interior U) := by
          audit_main14_side_base3
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            letI : CompactSpace U := T.compactSpace
            have hclosed : IsClosed U := by
              have hh := (isCompact_univ : IsCompact (Set.univ : Set U)).image
                (continuous_subtype_val : Continuous (Subtype.val : U → E))
              have hr : (Subtype.val : U → E) '' Set.univ = U := by
                rw [Set.image_univ,Subtype.range_coe_subtype]
                rfl
              exact (hr ▸ hh).isClosed
            have actual_embedded_annulus_interior_isOpen
                (B : Circle × Interval → E) (hB : IsEmbedding B) :
                IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
              rw [isOpen_iff_forall_mem_open]
              rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
              have hu0 : (0:ℝ) < (u : ℝ) := hu.1
              have hu1 : (u : ℝ) < 1 := hu.2
              let lo : ℝ := (u : ℝ)/2
              let hi : ℝ := ((u : ℝ)+1)/2
              have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
              have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
              have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
              have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
              have hlh : lo ≤ hi := (hlu.trans huh).le
              let width : ℝ → Interval := fun s =>
                ⟨(Set.projIcc lo hi hlh s : ℝ),
                  ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                    le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
              have hwc : Continuous width :=
                (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
              let θ := Complex.arg (z : ℂ)
              let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
              have hfc : Continuous f := hB.continuous.comp
                ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
              let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
                {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
              have hΩ : IsOpen Ω :=
                (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
              have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
                  (width (x 0) : ℝ) = x 0 :=
                congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
              have hfi : Set.InjOn f Ω := by
                intro x hx w hw he
                have hp := hB.injective he
                have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
                  (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
                  ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
                have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
                change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
                rw [hclip x hx,hclip w hw] at hwidth
                ext i
                fin_cases i
                · exact hwidth
                · exact hangle
              have hopen : IsOpen (f '' Ω) :=
                CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
              have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
                rintro q ⟨x,hx,rfl⟩
                refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
                · change 0 < (width (x 0) : ℝ)
                  rw [hclip x hx]
                  exact hl0.trans hx.1.1
                · change (width (x 0) : ℝ) < 1
                  rw [hclip x hx]
                  exact hx.1.2.trans hh1
              let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
              have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
              have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
              have hx : x ∈ Ω := by
                refine ⟨?_,?_⟩
                · rw [hx0]; exact ⟨hlu,huh⟩
                · rw [hx1]; constructor <;> linarith [Real.pi_pos]
              have hwu : width (u : ℝ) = u := by
                apply Subtype.ext
                change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
                exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
              have hpoint : f x = B (z,u) := by
                dsimp [f]
                rw [hx0,hx1,hwu,Circle.exp_arg]
              exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
            let f : Circle × Interval → E := fun p => (T p).val
            have hfe : Topology.IsEmbedding f := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
            let I := f '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
            have hIo : IsOpen I := actual_embedded_annulus_interior_isOpen f hfe
            have hIU : I ⊆ U := by rintro x ⟨p,hp,rfl⟩; exact (T p).property
            have hIint : I ⊆ interior U := hIo.subset_interior_iff.mpr hIU
            have hdense : U ⊆ closure (interior U) := by
              intro x hx
              let p := T.symm ⟨x,hx⟩
              have hp : p ∈ closure ((Set.univ : Set Circle) ×ˢ Set.Ioo (0:Interval) 1) := by
                rw [closure_prod_eq,closure_univ,closure_Ioo (show (0:Interval) ≠ 1 by norm_num)]
                exact ⟨Set.mem_univ _,p.2.property.1,p.2.property.2⟩
              have him : f p ∈ closure I := image_closure_subset_closure_image hfe.continuous ⟨p,hp,rfl⟩
              have heq : f p = x := congrArg Subtype.val (T.apply_symm_apply ⟨x,hx⟩)
              rw [heq] at him
              exact closure_mono hIint him
            let w0 : Set.Ioo (-1:ℝ) 1 := ⟨0,by norm_num⟩
            let wp : Set.Ioo (-1:ℝ) 1 := ⟨ε,by constructor <;> linarith⟩
            let wn : Set.Ioo (-1:ℝ) 1 := ⟨-ε,by constructor <;> linarith⟩
            let P := e '' (Set.Ioo w0 wp ×ˢ (Set.univ : Set Circle))
            let Q := e '' (Set.Ioo wn w0 ×ˢ (Set.univ : Set Circle))
            let O := e '' (Set.Ioo wn wp ×ˢ (Set.univ : Set Circle))
            have h0p : w0 < wp := hε
            have hn0 : wn < w0 := by change -ε < 0; linarith
            have hInterval (a b : Set.Ioo (-1:ℝ) 1) (hab : a < b) : IsConnected (Set.Ioo a b) := by
              letI : ConnectedSpace (Set.Ioo (a:ℝ) (b:ℝ)) := Subtype.connectedSpace (isConnected_Ioo (show (a:ℝ) < (b:ℝ) from hab))
              let inc : Set.Ioo (a:ℝ) (b:ℝ) → Set.Ioo (-1:ℝ) 1 := fun x =>
                ⟨x.val,⟨a.property.1.trans x.property.1,x.property.2.trans b.property.2⟩⟩
              have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
              have hr : Set.range inc = Set.Ioo a b := by
                ext x
                constructor
                · rintro ⟨y,rfl⟩
                  exact y.property
                · intro hx
                  exact ⟨⟨x.val,hx⟩,Subtype.ext rfl⟩
              rw [← hr]
              exact isConnected_range hinc
            have hP : IsPreconnected P :=
              ((hInterval w0 wp h0p).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
            have hQ : IsPreconnected Q :=
              ((hInterval wn w0 hn0).prod isConnected_univ).isPreconnected.image e e.continuous.continuousOn
            have hO : IsOpen O := he.isOpenMap _ (isOpen_Ioo.prod isOpen_univ)
            have hOcenter (z : Circle) : e (w0,z) ∈ O :=
              ⟨(w0,z),⟨⟨hn0,h0p⟩,Set.mem_univ _⟩,rfl⟩
            have hAvoid (w : Set.Ioo (-1:ℝ) 1) (hw : |(w:ℝ)| < ε)
                (hn : (w:ℝ) ≠ 0) (z : Circle) : e (w,z) ∉ frontier U := by
              intro hx
              rw [← hfront] at hx
              rcases hx with ⟨v,hv⟩ | hx
              · have hh : e (w,z) = e (w0,v) := by rw [hcenter]; exact hv.symm
                have heq := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => (p.1:ℝ))
                  (he.injective hh)
                exact hn heq
              · exact Set.disjoint_left.mp hclear ⟨(w,z),hw,rfl⟩ hx
            have hPavoid : P ⊆ (frontier U)ᶜ := by
              rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
              have hw0 : 0 < (w:ℝ) := hw.1
              have hwε : (w:ℝ) < ε := hw.2
              exact hAvoid w (by rw [abs_of_pos hw0]; exact hwε) hw0.ne' z
            have hQavoid : Q ⊆ (frontier U)ᶜ := by
              rintro x ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩
              have hw0 : (w:ℝ) < 0 := hw.2
              have hwε : -ε < (w:ℝ) := hw.1
              exact hAvoid w (by rw [abs_of_neg hw0]; linarith) hw0.ne z
            have hsub (D : Set E) (hD : D ⊆ (frontier U)ᶜ) : D ⊆ interior U ∪ Uᶜ := by
              intro x hx
              by_cases hxu : x ∈ U
              · apply Or.inl
                by_contra hn
                exact hD hx ((mem_frontier_iff_notMem_interior hxu).mpr hn)
              · exact Or.inr hxu
            have hid : Disjoint (interior U) Uᶜ := Set.disjoint_left.mpr
              (fun x hx hn => hn (interior_subset hx))
            have hPd : P ⊆ interior U ∨ P ⊆ Uᶜ :=
              IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub P hPavoid) hP
            have hQd : Q ⊆ interior U ∨ Q ⊆ Uᶜ :=
              IsPreconnected.subset_or_subset isOpen_interior hclosed.isOpen_compl hid (hsub Q hQavoid) hQ
            have hcenterFront (z : Circle) : e (w0,z) ∈ frontier U := by
              rw [hcenter,← hfront]
              exact Or.inl (Set.mem_range_self z)
            have hsplit (x : E) (hx : x ∈ O) : x ∈ P ∨ x ∈ Q ∨ ∃ z, x = e (w0,z) := by
              obtain ⟨⟨w,z⟩,⟨hw,_⟩,rfl⟩ := hx
              rcases lt_trichotomy w w0 with hh | hh | hh
              · exact Or.inr (Or.inl ⟨(w,z),⟨⟨hw.1,hh⟩,Set.mem_univ _⟩,rfl⟩)
              · exact Or.inr (Or.inr ⟨z,by rw [hh]⟩)
              · exact Or.inl ⟨(w,z),⟨⟨hh,hw.2⟩,Set.mem_univ _⟩,rfl⟩
            have hnotbothin : ¬ (P ⊆ interior U ∧ Q ⊆ interior U) := by
              rintro ⟨hp,hq⟩
              have hOU : O ⊆ U := by
                intro x hx
                rcases hsplit x hx with hx | hx | ⟨z,rfl⟩
                · exact interior_subset (hp hx)
                · exact interior_subset (hq hx)
                · rw [hcenter]
                  exact (T (z,0)).property
              have hint : e (w0,1) ∈ interior U := hO.subset_interior_iff.mpr hOU (hOcenter 1)
              exact Set.disjoint_left.mp disjoint_interior_frontier hint (hcenterFront 1)
            have hnotbothout : ¬ (P ⊆ Uᶜ ∧ Q ⊆ Uᶜ) := by
              rintro ⟨hp,hq⟩
              have hcU : e (w0,1) ∈ U := by rw [hcenter]; exact (T (1,0)).property
              have hccl := hdense hcU
              obtain ⟨x,hxO,hxi⟩ := mem_closure_iff.mp hccl O hO (hOcenter 1)
              rcases hsplit x hxO with hx | hx | ⟨z,rfl⟩
              · exact hp hx (interior_subset hxi)
              · exact hq hx (interior_subset hxi)
              · exact Set.disjoint_left.mp disjoint_interior_frontier hxi (hcenterFront z)
            have hPmem (w : Set.Ioo (-1:ℝ) 1) (h0 : 0 < (w:ℝ)) (h1 : (w:ℝ) < ε) (z : Circle) :
                e (w,z) ∈ P := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
            have hQmem (w : Set.Ioo (-1:ℝ) 1) (h0 : -ε < (w:ℝ)) (h1 : (w:ℝ) < 0) (z : Circle) :
                e (w,z) ∈ Q := ⟨(w,z),⟨⟨h0,h1⟩,Set.mem_univ _⟩,rfl⟩
            rcases hPd with hp | hp <;> rcases hQd with hq | hq
            · exact False.elim (hnotbothin ⟨hp,hq⟩)
            · exact Or.inl ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
            · exact Or.inr ⟨fun w h0 h1 z => hp (hPmem w h0 h1 z),fun w h0 h1 z => hq (hQmem w h0 h1 z)⟩
            · exact False.elim (hnotbothout ⟨hp,hq⟩)
        have hHalf (U : Set E)
            (e : C(Set.Ioo (-1:ℝ) 1 × Circle,E)) (he : Topology.IsOpenEmbedding e)
            (ε : ℝ) (hε : 0 < ε) (hεone : ε < 1)
            (hchoice : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε → ∀ z, e (w,z) ∉ U) ∨
              (∀ w : Set.Ioo (-1:ℝ) 1, -ε < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e (w,z) ∉ U)) :
            ∃ L : C(Circle × Interval,E), Topology.IsEmbedding L ∧
              (∀ z, L (z,0) = e (⟨0,by norm_num⟩,z)) ∧
              (∀ (z : Circle) (u : Interval), 0 < (u:ℝ) → L (z,u) ∉ U) ∧
              Set.range L ⊆ e '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε} := by
          audit_main14_base3
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            obtain ⟨σ,hσ,hout⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
                ∀ w : Set.Ioo (-1:ℝ) 1, 0 < σ*(w:ℝ) → σ*(w:ℝ) < ε → ∀ z, e (w,z) ∉ U := by
              rcases hchoice with hp | hn
              · exact ⟨1,Or.inl rfl,fun w h0 h1 z => hp w (by simpa using h0) (by simpa using h1) z⟩
              · refine ⟨-1,Or.inr rfl,?_⟩
                intro w h0 h1 z
                exact hn w (by linarith) (by linarith) z
            let q : Interval → Set.Ioo (-1:ℝ) 1 := fun u =>
              ⟨σ*ε/2*(u:ℝ),by rcases hσ with hs | hs <;> rw [hs] <;>
                constructor <;> nlinarith [u.property.1,u.property.2]⟩
            have hqc : Continuous q := by dsimp [q]; fun_prop
            have hqi : Function.Injective q := by
              intro u v h
              apply Subtype.ext
              have hh := congrArg Subtype.val h
              change σ*ε/2*(u:ℝ) = σ*ε/2*(v:ℝ) at hh
              rcases hσ with hs | hs <;> rw [hs] at hh <;> nlinarith
            have hq0 : q 0 = ⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [q]; ring
            have hqabs (u : Interval) : |(q u:ℝ)| < ε := by
              rw [abs_lt]
              dsimp [q]
              rcases hσ with hs | hs <;> rw [hs] <;> constructor <;>
                nlinarith [u.property.1,u.property.2]
            let L : C(Circle × Interval,E) := ⟨fun p => e (q p.2,p.1),
              e.continuous.comp ((hqc.comp continuous_snd).prodMk continuous_fst)⟩
            have hLi : Function.Injective L := by
              intro p w h
              have hh := he.injective h
              apply Prod.ext
              · have hz := congrArg (fun p : Set.Ioo (-1:ℝ) 1 × Circle => p.2) hh
                exact hz
              · exact hqi (congrArg Prod.fst hh)
            refine ⟨L,(L.continuous.isClosedEmbedding hLi).isEmbedding,?_,?_,?_⟩
            · intro z
              change e (q 0,z) = _
              rw [hq0]
            · intro z u hu
              apply hout (q u)
              · dsimp [q]
                rcases hσ with hs | hs <;> rw [hs] <;> nlinarith
              · dsimp [q]
                rcases hσ with hs | hs <;> rw [hs] <;> nlinarith [u.property.2]
            · rintro x ⟨p,rfl⟩
              exact ⟨(q p.2,p.1),hqabs p.2,rfl⟩
        have hGlue (U : Set E)
            (T : Circle × Interval ≃ₜ U)
            (L R : C(Circle × Interval,E)) (hL : Topology.IsEmbedding L) (hR : Topology.IsEmbedding R)
            (hLzero : ∀ z, L (z,0) = (T (z,0)).val)
            (hRzero : ∀ z, R (z,0) = (T (z,1)).val)
            (hLoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → L (z,t) ∉ U)
            (hRoutside : ∀ (z : Circle) (t : Interval), 0 < (t:ℝ) → R (z,t) ∉ U)
            (hLR : Disjoint (Set.range L) (Set.range R)) :
            ∃ g : C(Circle × Set.Icc (-1:ℝ) 2,E), Topology.IsEmbedding g ∧
              (∀ z, g (z,⟨0,by norm_num⟩) = (T (z,0)).val) ∧
              (∀ z, g (z,⟨1,by norm_num⟩) = (T (z,1)).val) ∧
              ∀ p : Circle × Set.Icc (-1:ℝ) 2,
                ∀ hp0 : 0 ≤ (p.2:ℝ), ∀ hp1 : (p.2:ℝ) ≤ 1,
                  g p = (T (p.1,⟨p.2.val,hp0,hp1⟩)).val := by
          audit_main14_base3
            letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
            let q : C(Circle × Interval,E) := ⟨fun p => (T p).val,continuous_subtype_val.comp T.continuous⟩
            have hq : Topology.IsEmbedding q := Topology.IsEmbedding.subtypeVal.comp T.isEmbedding
            have hLq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
                (he : L (z,t) = q (w,v)) : t = 0 ∧ v = 0 ∧ z = w := by
              by_cases ht : t = 0
              · rw [ht,hLzero] at he
                have hh := T.injective (Subtype.ext he)
                have hv := congrArg (fun p : Circle × Interval => p.2) hh
                have hz := congrArg (fun p : Circle × Interval => p.1) hh
                exact ⟨ht,hv.symm,hz⟩
              · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
                exact False.elim (hLoutside z t htp (he.symm ▸ (T (w,v)).property))
            have hRq (z : Circle) (t : Interval) (w : Circle) (v : Interval)
                (he : R (z,t) = q (w,v)) : t = 0 ∧ v = 1 ∧ z = w := by
              by_cases ht : t = 0
              · rw [ht,hRzero] at he
                have hh := T.injective (Subtype.ext he)
                have hv := congrArg (fun p : Circle × Interval => p.2) hh
                have hz := congrArg (fun p : Circle × Interval => p.1) hh
                exact ⟨ht,hv.symm,hz⟩
              · have htp : 0 < (t:ℝ) := lt_of_le_of_ne t.property.1 (fun hn => ht (Subtype.ext hn.symm))
                exact False.elim (hRoutside z t htp (he.symm ▸ (T (w,v)).property))
            let X := Set.Icc (-1 : ℝ) 2
            let τL : X → Interval := fun r => projIcc 0 1 zero_le_one (-(r:ℝ))
            let τQ : X → Interval := fun r => projIcc 0 1 zero_le_one (r:ℝ)
            let τR : X → Interval := fun r => projIcc 0 1 zero_le_one (((r:ℝ)-1))
            have hτL (r : X) (hr : (r:ℝ) ≤ 0) : (τL r:ℝ) = -(r:ℝ) := by
              dsimp only [τL]
              rw [projIcc_of_mem zero_le_one (show -(r:ℝ) ∈ Icc (0:ℝ) 1 by
                constructor <;> linarith [r.property.1])]
            have hτQ (r : X) (hr0 : 0 ≤ (r:ℝ)) (hr1 : (r:ℝ) ≤ 1) : (τQ r:ℝ) = r := by
              dsimp only [τQ]; rw [projIcc_of_mem zero_le_one ⟨hr0,hr1⟩]
            have hτR (r : X) (hr : 1 ≤ (r:ℝ)) : (τR r:ℝ) = ((r:ℝ)-1) := by
              dsimp only [τR]
              rw [projIcc_of_mem zero_le_one (show ((r:ℝ)-1) ∈ Icc (0:ℝ) 1 by
                constructor <;> linarith [r.property.2])]
            let ℓ : Circle × X → E := fun p => L (p.1,τL p.2)
            let m : Circle × X → E := fun p => q (p.1,τQ p.2)
            let r : Circle × X → E := fun p => R (p.1,τR p.2)
            have hℓcont : Continuous ℓ := L.continuous.comp
              (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
            have hmcont : Continuous m := q.continuous.comp
              (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
            have hrcont : Continuous r := R.continuous.comp
              (continuous_fst.prodMk (continuous_projIcc.comp (by fun_prop)))
            let k : Circle × X → E := fun p => if (p.2:ℝ) ≤ 1 then m p else r p
            have hkcont : Continuous k := by
              apply continuous_if_le (by fun_prop) continuous_const hmcont.continuousOn hrcont.continuousOn
              intro p hp
              have hq1 : τQ p.2 = 1 := Subtype.ext (by rw [hτQ p.2 (by linarith) hp.le]; exact hp)
              have hr0 : τR p.2 = 0 := Subtype.ext (by rw [hτR p.2 hp.ge]; simp [hp])
              dsimp only [m,r]
              rw [hq1,hr0,hRzero]
              rfl
            let G : Circle × X → E := fun p => if (p.2:ℝ) ≤ 0 then ℓ p else k p
            have hGcont : Continuous G := by
              apply continuous_if_le (by fun_prop) continuous_const hℓcont.continuousOn hkcont.continuousOn
              intro p hp
              have hL0 : τL p.2 = 0 := Subtype.ext (by rw [hτL p.2 hp.le]; simp [hp])
              have hq0 : τQ p.2 = 0 := Subtype.ext (by rw [hτQ p.2 hp.ge (by linarith)]; exact hp)
              dsimp only [ℓ,k]
              rw [ite_eq_left (show (p.2:ℝ) ≤ 1 by linarith)]
              dsimp only [m]
              rw [hL0,hq0,hLzero]
              rfl
            have hℓinj (p s : Circle × X) (hp : (p.2:ℝ) ≤ 0) (hs : (s.2:ℝ) ≤ 0)
                (he : ℓ p = ℓ s) : p = s := by
              have hh := hL.injective he
              have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
              apply Prod.ext hz
              apply Subtype.ext
              have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
              change (τL p.2:ℝ) = (τL s.2:ℝ) at hval
              rw [hτL p.2 hp,hτL s.2 hs] at hval
              linarith
            have hminj (p s : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1)
                (hs0 : 0 ≤ (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) (he : m p = m s) : p = s := by
              have hh := hq.injective he
              have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
              apply Prod.ext hz
              apply Subtype.ext
              have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
              change (τQ p.2:ℝ) = (τQ s.2:ℝ) at hval
              rwa [hτQ p.2 hp0 hp1,hτQ s.2 hs0 hs1] at hval
            have hrinj (p s : Circle × X) (hp : 1 ≤ (p.2:ℝ)) (hs : 1 ≤ (s.2:ℝ))
                (he : r p = r s) : p = s := by
              have hh := hR.injective he
              have hz : p.1 = s.1 := congrArg (fun p : Circle × Interval => p.1) hh
              apply Prod.ext hz
              apply Subtype.ext
              have hval := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
              change (τR p.2:ℝ) = (τR s.2:ℝ) at hval
              rw [hτR p.2 hp,hτR s.2 hs] at hval
              linarith
            have hℓm (p s : Circle × X) (hs0 : 0 < (s.2:ℝ)) (hs1 : (s.2:ℝ) ≤ 1) : ℓ p ≠ m s := by
              intro he
              have hh := (hLq p.1 (τL p.2) s.1 (τQ s.2) he).2.1
              have hv := congrArg Subtype.val hh
              change (τQ s.2:ℝ) = 0 at hv
              rw [hτQ s.2 hs0.le hs1] at hv
              linarith
            have hmr (p s : Circle × X) (hs : 1 < (s.2:ℝ)) : m p ≠ r s := by
              intro he
              have hh := (hRq s.1 (τR s.2) p.1 (τQ p.2) he.symm).1
              have hv := congrArg Subtype.val hh
              change (τR s.2:ℝ) = 0 at hv
              rw [hτR s.2 hs.le] at hv
              linarith
            have hℓr (p s : Circle × X) : ℓ p ≠ r s := by
              intro he
              exact Set.disjoint_left.mp hLR (Set.mem_range_self (p.1,τL p.2))
                ⟨(s.1,τR s.2),he.symm⟩
            have hGinj : Function.Injective G := by
              intro p s he
              dsimp only [G,k] at he
              by_cases hp0 : (p.2:ℝ) ≤ 0
              · rw [ite_eq_left hp0] at he
                by_cases hs0 : (s.2:ℝ) ≤ 0
                · rw [ite_eq_left hs0] at he; exact hℓinj p s hp0 hs0 he
                · rw [ite_eq_right hs0] at he
                  by_cases hs1 : (s.2:ℝ) ≤ 1
                  · rw [ite_eq_left hs1] at he; exact False.elim (hℓm p s (by linarith) hs1 he)
                  · rw [ite_eq_right hs1] at he; exact False.elim (hℓr p s he)
              · rw [ite_eq_right hp0] at he
                by_cases hp1 : (p.2:ℝ) ≤ 1
                · rw [ite_eq_left hp1] at he
                  by_cases hs0 : (s.2:ℝ) ≤ 0
                  · rw [ite_eq_left hs0] at he; exact False.elim (hℓm s p (by linarith) hp1 he.symm)
                  · rw [ite_eq_right hs0] at he
                    by_cases hs1 : (s.2:ℝ) ≤ 1
                    · rw [ite_eq_left hs1] at he; exact hminj p s (by linarith) hp1 (by linarith) hs1 he
                    · rw [ite_eq_right hs1] at he; exact False.elim (hmr p s (by linarith) he)
                · rw [ite_eq_right hp1] at he
                  by_cases hs0 : (s.2:ℝ) ≤ 0
                  · rw [ite_eq_left hs0] at he; exact False.elim (hℓr s p he.symm)
                  · rw [ite_eq_right hs0] at he
                    by_cases hs1 : (s.2:ℝ) ≤ 1
                    · rw [ite_eq_left hs1] at he; exact False.elim (hmr s p (by linarith) he.symm)
                    · rw [ite_eq_right hs1] at he; exact hrinj p s (by linarith) (by linarith) he
            let g : C(Circle × X,E) := ⟨G,hGcont⟩
            have hg : Topology.IsEmbedding g := (hGcont.isClosedEmbedding hGinj).isEmbedding
            have hg0 (z : Circle) : g (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0) := by
              change G (z,⟨0,by dsimp [X]; norm_num⟩) = q (z,0)
              simp only [G,le_refl,if_true,ℓ,τL,neg_zero,
                projIcc_of_mem zero_le_one (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)]
              exact hLzero z
            have hg1 (z : Circle) : g (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1) := by
              change G (z,⟨1,by dsimp [X]; norm_num⟩) = q (z,1)
              simp only [G,show ¬(1:ℝ)≤0 by norm_num,if_false,k,le_refl,if_true,m,τQ,
                projIcc_of_mem zero_le_one (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)]
              congr 1
            have hgmid (p : Circle × X) (hp0 : 0 ≤ (p.2:ℝ)) (hp1 : (p.2:ℝ) ≤ 1) :
                g p = q (p.1,⟨p.2.val,hp0,hp1⟩) := by
              by_cases hp : (p.2:ℝ) = 0
              · have he : p.2 = ⟨0,by dsimp [X]; norm_num⟩ := Subtype.ext hp
                calc
                  g p = g (p.1,⟨0,by dsimp [X]; norm_num⟩) := congrArg g (Prod.ext rfl he)
                  _ = q (p.1,0) := hg0 p.1
                  _ = q (p.1,⟨p.2.val,hp0,hp1⟩) := congrArg q (Prod.ext rfl (Subtype.ext hp.symm))
              · change G p = _
                have hpp : 0 < (p.2:ℝ) := lt_of_le_of_ne hp0 (Ne.symm hp)
                dsimp only [G,k]
                rw [ite_eq_right (not_le_of_gt hpp),ite_eq_left hp1]
                change q (p.1,τQ p.2) = _
                congr 1
                apply Prod.ext
                · rfl
                · apply Subtype.ext; exact hτQ p.2 hp0 hp1
            exact ⟨g,hg,hg0,hg1,hgmid⟩
        have actual_embedded_annulus_interior_isOpen
            (B : Circle × Interval → E) (hB : IsEmbedding B) :
            IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
          rw [isOpen_iff_forall_mem_open]
          rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
          have hu0 : (0:ℝ) < (u : ℝ) := hu.1
          have hu1 : (u : ℝ) < 1 := hu.2
          let lo : ℝ := (u : ℝ)/2
          let hi : ℝ := ((u : ℝ)+1)/2
          have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
          have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
          have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
          have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
          have hlh : lo ≤ hi := (hlu.trans huh).le
          let width : ℝ → Interval := fun s =>
            ⟨(Set.projIcc lo hi hlh s : ℝ),
              ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
          have hwc : Continuous width :=
            (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
          let θ := Complex.arg (z : ℂ)
          let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
          have hfc : Continuous f := hB.continuous.comp
            ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
          let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
            {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
          have hΩ : IsOpen Ω :=
            (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
          have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
              (width (x 0) : ℝ) = x 0 :=
            congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
          have hfi : Set.InjOn f Ω := by
            intro x hx w hw he
            have hp := hB.injective he
            have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
              (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
              ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
            have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
            change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
            rw [hclip x hx,hclip w hw] at hwidth
            ext i
            fin_cases i
            · exact hwidth
            · exact hangle
          have hopen : IsOpen (f '' Ω) :=
            CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
          have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
            rintro q ⟨x,hx,rfl⟩
            refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
            · change 0 < (width (x 0) : ℝ)
              rw [hclip x hx]
              exact hl0.trans hx.1.1
            · change (width (x 0) : ℝ) < 1
              rw [hclip x hx]
              exact hx.1.2.trans hh1
          let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
          have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
          have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
          have hx : x ∈ Ω := by
            refine ⟨?_,?_⟩
            · rw [hx0]; exact ⟨hlu,huh⟩
            · rw [hx1]; constructor <;> linarith [Real.pi_pos]
          have hwu : width (u : ℝ) = u := by
            apply Subtype.ext
            change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
            exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
          have hpoint : f x = B (z,u) := by
            dsimp [f]
            rw [hx0,hx1,hwu,Circle.exp_arg]
          exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
        let q : Interval → Interval := fun u => ⟨1/4+(u:ℝ)/2,by constructor <;> linarith [u.property.1,u.property.2]⟩
        let f : Circle × Interval → E := fun p => (T (p.1,q p.2)).val
        have hfc : Continuous f := by dsimp [f,q]; fun_prop
        have hfi : Function.Injective f := by
          intro p w he
          have hh := T.injective (Subtype.ext he)
          apply Prod.ext
          · have hz := congrArg (fun p : Circle × Interval => p.1) hh
            exact hz
          · apply Subtype.ext
            have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
            change 1/4+(p.2:ℝ)/2 = 1/4+(w.2:ℝ)/2 at hv
            linarith
        have hfe : Topology.IsEmbedding f := (hfc.isClosedEmbedding hfi).isEmbedding
        let W := Set.range f
        let A : Circle × Interval ≃ₜ W := hfe.toHomeomorph
        have hWdis : Disjoint W (Set.range (fun z : Circle => (T (z,0)).val) ∪
            Set.range (fun z : Circle => (T (z,1)).val)) := by
          apply Set.disjoint_left.mpr
          rintro x ⟨p,rfl⟩ (⟨z,he⟩ | ⟨z,he⟩)
          · have hh := T.injective (Subtype.ext he)
            have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
            change 0 = 1/4+(p.2:ℝ)/2 at hv
            linarith [p.2.property.1]
          · have hh := T.injective (Subtype.ext he)
            have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
            change 1 = 1/4+(p.2:ℝ)/2 at hv
            linarith [p.2.property.2]
        obtain ⟨e₀,e₁,ε₀,ε₁,he₀,he₁,hcenter₀,hcenter₁,hε₀,hε₀one,hε₁,hε₁one,hedis,heW₀,heW₁⟩ :=
          hCollars U W T A hWdis
        have hclear₀ : Disjoint (e₀ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₀})
            (Set.range (fun z : Circle => (T (z,1)).val)) := by
          apply hedis.mono_right
          rintro x ⟨z,rfl⟩
          exact ⟨(⟨0,by norm_num⟩,z),by simpa using hε₁,hcenter₁ z⟩
        have hclear₁ : Disjoint (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁})
            (Set.range (fun z : Circle => (T (z,0)).val)) := by
          apply hedis.symm.mono_right
          rintro x ⟨z,rfl⟩
          exact ⟨(⟨0,by norm_num⟩,z),by simpa using hε₀,hcenter₀ z⟩
        have hs₀ := hSide U T hfront e₀ he₀ hcenter₀ ε₀ hε₀ hε₀one hclear₀
        have hc₀ : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε₀ → ∀ z, e₀ (w,z) ∉ U) ∨
            (∀ w : Set.Ioo (-1:ℝ) 1, -ε₀ < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e₀ (w,z) ∉ U) := by
          rcases hs₀ with ⟨hin,hout⟩ | ⟨hout,hin⟩
          · exact Or.inr hout
          · exact Or.inl hout
        let T' := (Homeomorph.prodCongr (Homeomorph.refl Circle) unitInterval.symmHomeomorph).trans T
        have hT'₀ (z : Circle) : (T' (z,0)).val = (T (z,1)).val := by simp [T',unitInterval.symmHomeomorph,unitInterval.symm]
        have hT'₁ (z : Circle) : (T' (z,1)).val = (T (z,0)).val := by simp [T',unitInterval.symmHomeomorph,unitInterval.symm]
        have hfront' : Set.range (fun z : Circle => (T' (z,0)).val) ∪
            Set.range (fun z : Circle => (T' (z,1)).val) = frontier U := by
          simp_rw [hT'₀,hT'₁]
          rw [Set.union_comm]
          exact hfront
        have hcenter₁' (z : Circle) : e₁ (⟨0,by norm_num⟩,z) = (T' (z,0)).val :=
          (hcenter₁ z).trans (hT'₀ z).symm
        have hclear₁' : Disjoint (e₁ '' {p : Set.Ioo (-1:ℝ) 1 × Circle | |(p.1:ℝ)| < ε₁})
            (Set.range (fun z : Circle => (T' (z,1)).val)) := by
          simp_rw [hT'₁]
          exact hclear₁
        have hs₁ := hSide U T' hfront' e₁ he₁ hcenter₁' ε₁ hε₁ hε₁one hclear₁'
        have hc₁ : (∀ w : Set.Ioo (-1:ℝ) 1, 0 < (w:ℝ) → (w:ℝ) < ε₁ → ∀ z, e₁ (w,z) ∉ U) ∨
            (∀ w : Set.Ioo (-1:ℝ) 1, -ε₁ < (w:ℝ) → (w:ℝ) < 0 → ∀ z, e₁ (w,z) ∉ U) := by
          rcases hs₁ with ⟨hin,hout⟩ | ⟨hout,hin⟩
          · exact Or.inr hout
          · exact Or.inl hout
        obtain ⟨L,hL,hL0,hLout,hLsub⟩ := hHalf U e₀ he₀ ε₀ hε₀ hε₀one hc₀
        obtain ⟨R,hR,hR0,hRout,hRsub⟩ := hHalf U e₁ he₁ ε₁ hε₁ hε₁one hc₁
        have hLzero (z : Circle) : L (z,0) = (T (z,0)).val := (hL0 z).trans (hcenter₀ z)
        have hRzero (z : Circle) : R (z,0) = (T (z,1)).val := (hR0 z).trans (hcenter₁ z)
        have hLR : Disjoint (Set.range L) (Set.range R) := hedis.mono hLsub hRsub
        obtain ⟨g,hg,hg0,hg1,hgmid⟩ := hGlue U T L R hL hR hLzero hRzero hLout hRout hLR
        let k : Interval → Set.Icc (-1:ℝ) 2 := fun u =>
          ⟨3*(u:ℝ)-1,by constructor <;> linarith [u.property.1,u.property.2]⟩
        let Q : C(Circle × Interval,E) := ⟨fun p => g (p.1,k p.2),
          g.continuous.comp (continuous_fst.prodMk (by dsimp [k]; fun_prop))⟩
        have hQi : Function.Injective Q := by
          intro p w he
          have hh := hg.injective he
          apply Prod.ext
          · have hz := congrArg (fun p : Circle × Set.Icc (-1:ℝ) 2 => p.1) hh
            exact hz
          · apply Subtype.ext
            have hv := congrArg (fun p : Circle × Set.Icc (-1:ℝ) 2 => (p.2:ℝ)) hh
            change 3*(p.2:ℝ)-1 = 3*(w.2:ℝ)-1 at hv
            linarith
        have hQ : Topology.IsEmbedding Q := (Q.continuous.isClosedEmbedding hQi).isEmbedding
        have hQold (z : Circle) (s : Interval) :
            Q (z,⟨((s:ℝ)+1)/3,by constructor <;> linarith [s.property.1,s.property.2]⟩) = (T (z,s)).val := by
          have hk : k ⟨((s:ℝ)+1)/3,by constructor <;> linarith [s.property.1,s.property.2]⟩ =
              ⟨s.val,by constructor <;> linarith [s.property.1,s.property.2]⟩ := by
            apply Subtype.ext
            dsimp [k]
            ring
          change g (z,k _) = _
          rw [hk]
          exact hgmid _ s.property.1 s.property.2
        refine ⟨Q,hQ,?_,?_,hQold,actual_embedded_annulus_interior_isOpen Q hQ⟩
        · intro z
          simpa using hQold z 0
        · intro z
          have hh := hQold z 1
          norm_num at hh
          exact hh
    have hMove (U : Set E)
        (T : Circle × Interval ≃ₜ U) :
        ∃ H : AmbientIsotopy E, ∃ J : C(Interval × E,E),
          H.finalMap ''
            (Set.range (fun z : Circle => (T (z,⟨1/6,by norm_num⟩)).val) ∪
              Set.range (fun z : Circle => (T (z,⟨5/6,by norm_num⟩)).val)) =
            Set.range (fun z : Circle => (T (z,⟨1/3,by norm_num⟩)).val) ∪
              Set.range (fun z : Circle => (T (z,⟨2/3,by norm_num⟩)).val) ∧
          (∀ t z, H.map (t,(T (z,⟨1/2,by norm_num⟩)).val) =
            (T (z,⟨1/2,by norm_num⟩)).val) ∧
          (∀ t x, x ∉ U → H.map (t,x) = x) ∧
          (∀ t x, J (t,H.map (t,x)) = x) ∧
          (∀ t x, H.map (t,J (t,x)) = x) := by
      audit_main14_base3
        letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
        have actual_embedded_annulus_interior_isOpen
            (B : Circle × Interval → E) (hB : IsEmbedding B) :
            IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)) := by
          rw [isOpen_iff_forall_mem_open]
          rintro y ⟨⟨z,u⟩,⟨hz,hu⟩,rfl⟩
          have hu0 : (0:ℝ) < (u : ℝ) := hu.1
          have hu1 : (u : ℝ) < 1 := hu.2
          let lo : ℝ := (u : ℝ)/2
          let hi : ℝ := ((u : ℝ)+1)/2
          have hlu : lo < (u : ℝ) := by dsimp [lo]; exact half_lt_self (by exact hu.1)
          have huh : (u : ℝ) < hi := by dsimp [hi]; linarith [hu1]
          have hl0 : 0 < lo := by dsimp [lo]; exact half_pos (by exact hu.1)
          have hh1 : hi < 1 := by dsimp [hi]; linarith [hu1]
          have hlh : lo ≤ hi := (hlu.trans huh).le
          let width : ℝ → Interval := fun s =>
            ⟨(Set.projIcc lo hi hlh s : ℝ),
              ⟨le_trans hl0.le (Set.projIcc lo hi hlh s).property.1,
                le_trans (Set.projIcc lo hi hlh s).property.2 hh1.le⟩⟩
          have hwc : Continuous width :=
            (continuous_subtype_val.comp continuous_projIcc).subtype_mk _
          let θ := Complex.arg (z : ℂ)
          let f : EuclideanSpace ℝ (Fin 2) → E := fun x => B (Circle.exp (x 1),width (x 0))
          have hfc : Continuous f := hB.continuous.comp
            ((Circle.exp.continuous.comp (by fun_prop)).prodMk (hwc.comp (by fun_prop)))
          let Ω : Set (EuclideanSpace ℝ (Fin 2)) :=
            {x | x 0 ∈ Set.Ioo lo hi ∧ x 1 ∈ Set.Ioo (θ-Real.pi/2) (θ+Real.pi/2)}
          have hΩ : IsOpen Ω :=
            (isOpen_Ioo.preimage (by fun_prop)).inter (isOpen_Ioo.preimage (by fun_prop))
          have hclip (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Ω) :
              (width (x 0) : ℝ) = x 0 :=
            congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hx.1.1.le,hx.1.2.le⟩)
          have hfi : Set.InjOn f Ω := by
            intro x hx w hw he
            have hp := hB.injective he
            have hangle : x 1 = w 1 := Circle.exp_injOn_Icc
              (a := θ-Real.pi/2) (b := θ+Real.pi/2) (by linarith [Real.pi_pos])
              ⟨hx.2.1.le,hx.2.2.le⟩ ⟨hw.2.1.le,hw.2.2.le⟩ (congrArg Prod.fst hp)
            have hwidth := congrArg (fun p : Circle × Interval => p.2.val) hp
            change (width (x 0) : ℝ) = (width (w 0) : ℝ) at hwidth
            rw [hclip x hx,hclip w hw] at hwidth
            ext i
            fin_cases i
            · exact hwidth
            · exact hangle
          have hopen : IsOpen (f '' Ω) :=
            CurveComplex.surface_invariance_of_domain_probe f Ω hΩ hfc.continuousOn hfi
          have hsub : f '' Ω ⊆ B '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1) := by
            rintro q ⟨x,hx,rfl⟩
            refine ⟨(Circle.exp (x 1),width (x 0)),⟨Set.mem_univ _,?_,?_⟩,rfl⟩
            · change 0 < (width (x 0) : ℝ)
              rw [hclip x hx]
              exact hl0.trans hx.1.1
            · change (width (x 0) : ℝ) < 1
              rw [hclip x hx]
              exact hx.1.2.trans hh1
          let x : EuclideanSpace ℝ (Fin 2) := Schoenflies.Plane.mk (u : ℝ) θ
          have hx0 : x 0 = (u : ℝ) := by simp [x,Schoenflies.Plane.mk]
          have hx1 : x 1 = θ := by simp [x,Schoenflies.Plane.mk]
          have hx : x ∈ Ω := by
            refine ⟨?_,?_⟩
            · rw [hx0]; exact ⟨hlu,huh⟩
            · rw [hx1]; constructor <;> linarith [Real.pi_pos]
          have hwu : width (u : ℝ) = u := by
            apply Subtype.ext
            change (Set.projIcc lo hi hlh (u : ℝ) : ℝ) = (u : ℝ)
            exact congrArg Subtype.val (Set.projIcc_of_mem hlh ⟨hlu.le,huh.le⟩)
          have hpoint : f x = B (z,u) := by
            dsimp [f]
            rw [hx0,hx1,hwu,Circle.exp_arg]
          exact ⟨f '' Ω,hsub,hopen,⟨x,hx,hpoint⟩⟩
        let L : Circle × Interval → E := fun p =>
          (T (p.1,⟨(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
        let R : Circle × Interval → E := fun p =>
          (T (p.1,⟨1-(p.2 : ℝ)/2,by constructor <;> linarith [p.2.property.1,p.2.property.2]⟩)).val
        have hLc : Continuous L := by dsimp [L]; fun_prop
        have hRc : Continuous R := by dsimp [R]; fun_prop
        have hLi : Function.Injective L := by
          intro p q he
          have hh := T.injective (Subtype.ext he)
          apply Prod.ext
          · have hx := congrArg (fun x : Circle × Interval => x.1) hh
            exact hx
          · apply Subtype.ext
            have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
            change (p.2 : ℝ)/2 = (q.2 : ℝ)/2 at hc
            linarith
        have hRi : Function.Injective R := by
          intro p q he
          have hh := T.injective (Subtype.ext he)
          apply Prod.ext
          · have hx := congrArg (fun x : Circle × Interval => x.1) hh
            exact hx
          · apply Subtype.ext
            have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
            change 1-(p.2 : ℝ)/2 = 1-(q.2 : ℝ)/2 at hc
            linarith
        have hL : Topology.IsEmbedding L := (hLc.isClosedEmbedding hLi).isEmbedding
        have hR : Topology.IsEmbedding R := (hRc.isClosedEmbedding hRi).isEmbedding
        let UL := L '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
        let UR := R '' (Set.univ ×ˢ Set.Ioo (0:Interval) 1)
        have hUL : IsOpen UL := actual_embedded_annulus_interior_isOpen L hL
        have hUR : IsOpen UR := actual_embedded_annulus_interior_isOpen R hR
        obtain ⟨K,V,hleft,hright,hzero,hone,hfinal⟩ := CurveComplex.G3Review.actual_circle_band_ambient_motion
        have hfixL (t : Interval) (y : Circle × Interval) (hy : L y ∉ UL) : K.map (t,y) = y := by
          by_cases hy0 : y.2 = 0
          · rw [show y = (y.1,0) from Prod.ext rfl hy0]
            exact hzero t y.1
          by_cases hy1 : y.2 = 1
          · rw [show y = (y.1,1) from Prod.ext rfl hy1]
            exact hone t y.1
          have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
          have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
          exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
        have hfixR (t : Interval) (y : Circle × Interval) (hy : R y ∉ UR) : K.map (t,y) = y := by
          by_cases hy0 : y.2 = 0
          · rw [show y = (y.1,0) from Prod.ext rfl hy0]
            exact hzero t y.1
          by_cases hy1 : y.2 = 1
          · rw [show y = (y.1,1) from Prod.ext rfl hy1]
            exact hone t y.1
          have h0 : (0 : Interval) < y.2 := lt_of_le_of_ne (by exact y.2.property.1) (fun he => hy0 he.symm)
          have h1 : y.2 < (1 : Interval) := lt_of_le_of_ne (by exact y.2.property.2) hy1
          exact False.elim (hy ⟨y,⟨Set.mem_univ _,h0,h1⟩,rfl⟩)
        obtain ⟨HL,JL,hHL,hLout,hJLleft,hJLright⟩ :=
          CurveComplex.G3Review.actual_compact_embedded_motion_extension L hL UL hUL
            (Set.image_subset_range _ _) K V hleft hright hfixL
        obtain ⟨HR,JR,hHR,hRout,hJRleft,hJRright⟩ :=
          CurveComplex.G3Review.actual_compact_embedded_motion_extension R hR UR hUR
            (Set.image_subset_range _ _) K V hleft hright hfixR
        have hLow (z : Circle) (u : Interval) (hu : (u : ℝ) ≤ 1/2) : (T (z,u)).val ∉ UR := by
          rintro ⟨p,⟨_,hp⟩,he⟩
          have hh := T.injective (Subtype.ext he)
          have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
          change 1-(p.2 : ℝ)/2 = (u : ℝ) at hc
          have hp1 : (p.2 : ℝ) < 1 := hp.2
          linarith
        have hHigh (z : Circle) (u : Interval) (hu : 1/2 ≤ (u : ℝ)) : (T (z,u)).val ∉ UL := by
          rintro ⟨p,⟨_,hp⟩,he⟩
          have hh := T.injective (Subtype.ext he)
          have hc := congrArg (fun x : Circle × Interval => (x.2 : ℝ)) hh
          change (p.2 : ℝ)/2 = (u : ℝ) at hc
          have hp1 : (p.2 : ℝ) < 1 := hp.2
          linarith
        let H : AmbientIsotopy E := {
          map := ⟨fun p => HR.map (p.1,HL.map (p.1,p.2)),HR.map.continuous.comp
            (continuous_fst.prodMk (HL.map.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨l,hl⟩ := HL.homeomorphism_at t
            obtain ⟨r,hr⟩ := HR.homeomorphism_at t
            exact ⟨l.trans r,fun x => by change r (l x) = HR.map (t,HL.map (t,x)); rw [hl,hr]⟩
          at_zero := by
            intro x
            change HR.map (⟨0,by norm_num⟩,HL.map (⟨0,by norm_num⟩,x)) = x
            rw [HL.at_zero,HR.at_zero] }
        let J : C(Interval × E,E) := ⟨fun p => JL (p.1,JR (p.1,p.2)),JL.continuous.comp
          (continuous_fst.prodMk (JR.continuous.comp (continuous_fst.prodMk continuous_snd)))⟩
        have hLf (z : Circle) : HL.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
            (T (z,⟨1/3,by norm_num⟩)).val := by
          have h := hHL 1 (z,⟨1/3,by norm_num⟩)
          have hk := hfinal z
          change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
          rw [hk] at h
          norm_num [AmbientIsotopy.finalMap,L] at h ⊢
          exact h
        have hRf (z : Circle) : HR.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
            (T (z,⟨2/3,by norm_num⟩)).val := by
          have h := hHR 1 (z,⟨1/3,by norm_num⟩)
          have hk := hfinal z
          change K.map (1,(z,⟨1/3,by norm_num⟩)) = (z,⟨2/3,by norm_num⟩) at hk
          rw [hk] at h
          norm_num [AmbientIsotopy.finalMap,R] at h ⊢
          exact h
        have hHfL (z : Circle) : H.finalMap (T (z,⟨1/6,by norm_num⟩)).val =
            (T (z,⟨1/3,by norm_num⟩)).val := by
          change HR.finalMap (HL.finalMap _) = _
          rw [hLf]
          exact hRout 1 _ (hLow z _ (by norm_num))
        have hHfR (z : Circle) : H.finalMap (T (z,⟨5/6,by norm_num⟩)).val =
            (T (z,⟨2/3,by norm_num⟩)).val := by
          change HR.finalMap (HL.finalMap _) = _
          rw [show HL.finalMap (T (z,⟨5/6,by norm_num⟩)).val = (T (z,⟨5/6,by norm_num⟩)).val from
            hLout 1 _ (hHigh z _ (by norm_num))]
          exact hRf z
        refine ⟨H,J,?_,?_,?_,?_,?_⟩
        · rw [Set.image_union,← Set.range_comp,← Set.range_comp]
          exact congrArg₂ Set.union (congrArg Set.range (funext hHfL)) (congrArg Set.range (funext hHfR))
        · intro t z
          change HR.map (t,HL.map (t,_)) = _
          rw [hLout t _ (hHigh z _ (by norm_num)),hRout t _ (hLow z _ (by norm_num))]
        · intro t x hx
          have hxL : x ∉ UL := by
            rintro ⟨p,hp,rfl⟩
            exact hx (T _).property
          have hxR : x ∉ UR := by
            rintro ⟨p,hp,rfl⟩
            exact hx (T _).property
          change HR.map (t,HL.map (t,x)) = x
          rw [hLout t x hxL,hRout t x hxR]
        · intro t x
          change JL (t,JR (t,HR.map (t,HL.map (t,x)))) = x
          rw [hJRleft,hJLleft]
        · intro t x
          change HR.map (t,HL.map (t,JL (t,JR (t,x)))) = x
          rw [hJLright,hJRright]
    obtain ⟨Q,hQ,hQ0,hQ1,hQold,hQopen⟩ := hExtension
    let q : Interval → Interval := fun u => ⟨1/4+(u:ℝ)/2,by constructor <;> linarith [u.property.1,u.property.2]⟩
    let B : Circle × Interval → E := fun p => Q (p.1,q p.2)
    have hBc : Continuous B := by dsimp [B,q]; fun_prop
    have hBi : Function.Injective B := by
      intro p w he
      have hh := hQ.injective he
      apply Prod.ext
      · have hz := congrArg (fun p : Circle × Interval => p.1) hh
        exact hz
      · apply Subtype.ext
        have hv := congrArg (fun p : Circle × Interval => (p.2:ℝ)) hh
        change 1/4+(p.2:ℝ)/2 = 1/4+(w.2:ℝ)/2 at hv
        linarith
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    have hBe : Topology.IsEmbedding B := (hBc.isClosedEmbedding hBi).isEmbedding
    let V := Set.range B
    let TB : Circle × Interval ≃ₜ V := hBe.toHomeomorph
    have hTB0 (z : Circle) : (TB (z,⟨1/6,by norm_num⟩)).val = (T (z,0)).val := by
      change Q (z,q ⟨1/6,by norm_num⟩) = _
      rw [show q ⟨1/6,by norm_num⟩ = ⟨1/3,by norm_num⟩ from Subtype.ext (by norm_num [q])]
      exact hQ0 z
    have hTB1 (z : Circle) : (TB (z,⟨5/6,by norm_num⟩)).val = (T (z,1)).val := by
      change Q (z,q ⟨5/6,by norm_num⟩) = _
      rw [show q ⟨5/6,by norm_num⟩ = ⟨2/3,by norm_num⟩ from Subtype.ext (by norm_num [q])]
      exact hQ1 z
    have hTB2 (z : Circle) : (TB (z,⟨1/3,by norm_num⟩)).val = (T (z,⟨1/4,by norm_num⟩)).val := by
      change Q (z,q ⟨1/3,by norm_num⟩) = _
      rw [show q ⟨1/3,by norm_num⟩ = ⟨5/12,by norm_num⟩ from Subtype.ext (by norm_num [q])]
      have hh := hQold z ⟨1/4,by norm_num⟩
      norm_num at hh
      exact hh
    have hTB3 (z : Circle) : (TB (z,⟨2/3,by norm_num⟩)).val = (T (z,⟨3/4,by norm_num⟩)).val := by
      change Q (z,q ⟨2/3,by norm_num⟩) = _
      rw [show q ⟨2/3,by norm_num⟩ = ⟨7/12,by norm_num⟩ from Subtype.ext (by norm_num [q])]
      have hh := hQold z ⟨3/4,by norm_num⟩
      norm_num at hh
      exact hh
    have hTBmid (z : Circle) : (TB (z,⟨1/2,by norm_num⟩)).val = (T (z,⟨1/2,by norm_num⟩)).val := by
      change Q (z,q ⟨1/2,by norm_num⟩) = _
      rw [show q ⟨1/2,by norm_num⟩ = ⟨1/2,by norm_num⟩ from Subtype.ext (by norm_num [q])]
      have hh := hQold z ⟨1/2,by norm_num⟩
      norm_num at hh
      exact hh
    obtain ⟨H,J,hPair,hCore,hOutside,hLeft,hRight⟩ := hMove V TB
    simp_rw [hTB0,hTB1,hTB2,hTB3] at hPair
    simp_rw [hTBmid] at hCore
    rw [hTb] at hPair
    exact ⟨H,J,hPair,hCore,hLeft,hRight⟩

end CurveComplex.HyperellipticModel
