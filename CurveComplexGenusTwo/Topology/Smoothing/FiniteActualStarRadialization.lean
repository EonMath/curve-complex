import CurveComplexGenusTwo.Topology.Smoothing.FiniteStarSeed
import CurveComplexGenusTwo.Topology.Smoothing.FirstExitPrefixHeader
import CurveComplexGenusTwo.Topology.Smoothing.ConvexSectorChartHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
import CurveComplexGenusTwo.Topology.Smoothing.RadialSectorSplitHeader
import CurveComplexGenusTwo.Topology.Smoothing.SectorBoundaryInvariantHeader
import CurveComplexGenusTwo.Topology.Smoothing.SectorSplitNonemptyHeader
import Mathlib.Topology.Algebra.Module.FiniteDimension
open Set Metric Schoenflies CurveComplex Bornology
set_option maxHeartbeats 2600000
namespace CurveComplex.FiniteStarGeometry

theorem finite_actual_star_radialization
    {J : Type} [Fintype J] (γ : J → I → Plane) (o : Plane)
    (hγ : ∀ j, Topology.IsClosedEmbedding (γ j))
    (hstart : ∀ j, γ j zeroI = o)
    (hmeet : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {o})
    (V : Set Plane) (hV : IsOpen V) (hoV : o ∈ V) :
    Nonempty (RadializedStar γ o V) := by

  classical
  have zeroCase {J : Type} [Fintype J] (γ : J → I → Plane)
      (hγ : ∀ j, Topology.IsClosedEmbedding (γ j)) (hstart : ∀ j, γ j zeroI = 0)
      (hmeet : ∀ i j, i ≠ j → range (γ i) ∩ range (γ j) = {0})
      (hcard : 1 < Fintype.card J)
      (V : Set Plane) (hV : IsOpen V) (hoV : (0:Plane) ∈ V) :
      Nonempty (RadializedStar γ 0 V) := by
    classical
    have complete {J : Type} [Fintype J] (γ : J → I → Plane)
        (hγ : ∀ j, Topology.IsClosedEmbedding (γ j)) (hstart : ∀ j, γ j zeroI = 0)
        (hmeet : ∀ i j, i ≠ j → range (γ i) ∩ range (γ j) = {0})
        (R R₀ : ℝ) (hR : 0 < R) (hRR₀ : R ≤ R₀) :
        let fan : Finset J → (J → Plane) → Set Plane := fun S w => ⋃ j, ⋃ (_ : j ∈ S), segment ℝ (0:Plane) (w j)
        let Cells : Finset J → (J → Plane) → Prop := fun S w =>
          ∃ (K : Type) (Q : K → Set Plane),
            (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
            (∀ k, (0:Plane) ∈ Q k) ∧ (∀ k, Q k ⊆ closedBall (0:Plane) R) ∧
            (closedBall (0:Plane) R ⊆ ⋃ k, Q k) ∧
            (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
            (∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ fan S w) ∧
            (∀ k, (interior (Q k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q k)) ∧
            (∀ k, Disjoint (interior (Q k)) (fan S w)) ∧
            (∀ k, ∃ L : Plane →L[ℝ] ℝ,
              (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ fan S w))
        ∀ (S₀ : Finset J) (H₀ : Plane ≃ₜ Plane) (c₀ : J → I) (w₀ : J → Plane),
          H₀ 0 = 0 → (∀ x, x ∉ ball (0:Plane) R₀ → H₀ x = x) →
          (∀ j, H₀ (γ j oneI) ∉ closedBall (0:Plane) R) →
          (∀ j ∈ S₀, 0 < (c₀ j).val ∧ (c₀ j).val < 1 ∧ ‖w₀ j‖ = R ∧
            H₀ '' (γ j '' Icc 0 (c₀ j)) = segment ℝ (0:Plane) (w₀ j)) →
          Cells S₀ w₀ →
          ∃ (H : Plane ≃ₜ Plane) (c : J → I) (w : J → Plane),
            H 0 = 0 ∧ (∀ x, x ∉ ball (0:Plane) R₀ → H x = x) ∧
            ∀ j, 0 < (c j).val ∧ (c j).val < 1 ∧ ‖w j‖ = R ∧
              H '' (γ j '' Icc 0 (c j)) = segment ℝ (0:Plane) (w j) := by
      classical
      intro fan Cells S₀ H₀ c₀ w₀ hH₀ hfix₀ hend₀ hprefix₀ hCells₀
      have insertArm {J K : Type} (Q : K → Set Plane) (v : J → Plane)
          (R : ℝ) (hR : 0 < R)
          (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
          (hzero : ∀ k, (0:Plane) ∈ Q k)
          (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
          (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
          (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
          (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ ⋃ j, segment ℝ (0:Plane) (v j))
          (hcellne : ∀ k, (interior (Q k)).Nonempty)
          (hcenter : ∀ k, (0:Plane) ∈ frontier (Q k))
          (hfan : ∀ k, Disjoint (interior (Q k)) (⋃ j, segment ℝ (0:Plane) (v j)))
          (hv : ∀ j, ‖v j‖ = R)
          {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
          (ha : a ∉ closedBall (0:Plane) R)
          (havoid : ∀ t : I, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
          ∃ (F : Plane ≃ₜ Plane) (c : I) (k : K),
            0 < c.val ∧ c.val < 1 ∧ ‖α c‖ = R ∧
            α c ∈ frontier (Q k) ∧
            segment ℝ (0:Plane) (α c) \ {0,α c} ⊆ interior (Q k) ∧
            F '' (α '' Icc 0 c) = segment ℝ (0:Plane) (α c) ∧
            F 0 = 0 ∧ (∀ x, x ∉ interior (Q k) → F x = x) ∧
            (∀ x, x ∉ ball (0:Plane) R → F x = x) ∧
            (∀ x ∈ ⋃ j, segment ℝ (0:Plane) (v j), F x = x) := by
        have firstExit {J K : Type} (Q : K → Set Plane) (v : J → Plane)
            (R : ℝ) (hR : 0 < R)
            (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
            (hzero : ∀ k, (0:Plane) ∈ Q k)
            (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
            (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
            (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
            (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ ⋃ j, segment ℝ (0:Plane) (v j))
            (hv : ∀ j, ‖v j‖ = R)
            {a : Plane} (α : Path (0:Plane) a) (hα : Function.Injective α)
            (ha : a ∉ closedBall (0:Plane) R)
            (havoid : ∀ t : I, 0 < t.val → α t ∉ ⋃ j, segment ℝ (0:Plane) (v j)) :
            ∃ (c : I) (k : K), 0 < c.val ∧ c.val < 1 ∧
              ‖α c‖ = R ∧ α c ∈ frontier (Q k) ∧
              IsArcBetween (α '' Icc 0 c) 0 (α c) ∧
              (α '' Icc 0 c) \ {0,α c} ⊆ interior (Q k) ∧
              segment ℝ (0:Plane) (α c) \ {0,α c} ⊆ interior (Q k) := by
          classical
          have select (U : K → Set Plane) (hU : ∀ k, IsOpen (U k))
              (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
              (c t₀ : I) (ht₀ : t₀ ∈ Ioo zeroI c)
              (hc : ∀ t ∈ Ioo zeroI c, α t ∈ ⋃ k, U k) :
              ∃ k, ∀ t ∈ Ioo zeroI c, α t ∈ U k := by
            obtain ⟨k,hk⟩ := mem_iUnion.mp (hc t₀ ht₀)
            let W := ⋃ (j : K) (_ : j ≠ k), U j
            have hW : IsOpen W := isOpen_iUnion (fun j => isOpen_iUnion (fun _ => hU j))
            have hdW : Disjoint (U k) W := by
              apply Set.disjoint_left.mpr
              intro x hx hxW
              obtain ⟨j,hj⟩ := mem_iUnion.mp hxW
              obtain ⟨hne,hxj⟩ := mem_iUnion.mp hj
              exact Set.disjoint_left.mp (hd hne.symm) hx hxj
            have hp : α '' Ioo zeroI c ⊆ U k ∪ W := by
              rintro x ⟨t,ht,rfl⟩
              obtain ⟨j,hj⟩ := mem_iUnion.mp (hc t ht)
              by_cases he : j = k
              · exact Or.inl (he ▸ hj)
              · exact Or.inr (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨he,hj⟩⟩)
            have hsel : α '' Ioo zeroI c ⊆ U k :=
              (isPreconnected_Ioo.image α α.continuous.continuousOn).subset_left_of_subset_union
                (hU k) hW hdW hp ⟨α t₀,⟨⟨t₀,ht₀,rfl⟩,hk⟩⟩
            exact ⟨k,fun t ht => hsel ⟨t,ht,rfl⟩⟩
          have nonsphere {x : Plane} (hb : x ∈ ball (0:Plane) R) : x ∉ sphere (0:Plane) R := by
            simp only [mem_ball,mem_sphere,dist_zero_right] at *
            exact ne_of_lt hb
          have haopen : a ∉ ball (0:Plane) R := fun hm => ha (ball_subset_closedBall hm)
          obtain ⟨c,hc,γ,hex,hγ,himage,hbefore⟩ :=
            CurveComplex.SeedProbeHeaders.embedded_first_exit_prefix α hα
              (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
          have heR : ‖α c‖ = R := by
            rw [frontier_ball (0:Plane) (ne_of_gt hR)] at hex
            simpa only [mem_sphere,dist_zero_right] using hex
          have hc1 : c < 1 := by
            apply lt_of_le_of_ne c.property.2
            intro he
            apply ha
            rw [show c = 1 from Subtype.ext he] at heR
            simpa only [α.target,mem_closedBall,dist_zero_right] using heR.le
          have hrawbefore : ∀ t : I, t < c → α t ∈ ball (0:Plane) R := by
            obtain ⟨d,hd,hdf,hdb⟩ := CurveComplex.path_first_exit_frontier α
              (ball (0:Plane) R) isOpen_ball (by simpa using hR) haopen
            have hdle : d ≤ c := by
              by_contra hn
              have hm := hdb c (lt_of_not_ge hn)
              exact (show α c ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hex.2) hm
            have hcd : c ≤ d := by
              by_contra hn
              have hdγ : α d ∈ range γ := by
                rw [himage]
                exact ⟨d,⟨d.property.1,(lt_of_not_ge hn).le⟩,rfl⟩
              obtain ⟨s,hs⟩ := hdγ
              have hs1 : s < 1 := by
                apply lt_of_le_of_ne s.property.2
                intro he
                have hsone : s = 1 := Subtype.ext he
                have hdc : d = c := hα (hs.symm.trans (hsone ▸ γ.target))
                exact (ne_of_lt (lt_of_not_ge hn)) hdc
              have hm := hbefore s hs1
              rw [hs] at hm
              exact (show α d ∉ ball (0:Plane) R from by simpa only [frontier,isOpen_ball.interior_eq] using hdf.2) hm
            exact fun t ht => hdb t (ht.trans_le hcd)
          have hcellcover : ∀ t ∈ Ioo zeroI c, α t ∈ ⋃ k, interior (Q k) := by
            intro t ht
            have hb := hrawbefore t ht.2
            obtain ⟨k,hk⟩ := mem_iUnion.mp (hcover (ball_subset_closedBall hb))
            refine mem_iUnion.mpr ⟨k,?_⟩
            by_contra hn
            have hfr : α t ∈ frontier (Q k) := by
              rw [(hclosed k).frontier_eq]
              exact ⟨hk,hn⟩
            rcases hfront k hfr with hs | hf
            · exact (nonsphere hb) hs
            · exact havoid t ht.1 hf
          let t₀ : I := ⟨c.val/2,by constructor <;> nlinarith [c.property.1,c.property.2]⟩
          have ht₀ : t₀ ∈ Ioo zeroI c := by
            have hcr : 0 < c.val := hc
            constructor
            · change 0 < c.val/2
              linarith
            · change c.val/2 < c.val
              linarith
          obtain ⟨k,hk⟩ := select (fun k => interior (Q k)) (fun _ => isOpen_interior)
            hdisj c t₀ ht₀ hcellcover
          have heQ : α c ∈ Q k := by
            have hcc : c ∈ closure (Ioo zeroI c : Set I) := by
              rw [closure_Ioo (show zeroI ≠ c from ne_of_lt hc)]
              exact ⟨hc.le,le_rfl⟩
            have hsub : Ioo zeroI c ⊆ α ⁻¹' Q k := by
              intro t ht
              change α t ∈ Q k
              exact interior_subset (hk t ht)
            exact ((hclosed k).preimage α.continuous).closure_subset_iff.mpr hsub hcc
          have hefront : α c ∈ frontier (Q k) := by
            rw [(hclosed k).frontier_eq]
            refine ⟨heQ,?_⟩
            intro hm
            have hb : α c ∈ interior (closedBall (0:Plane) R) := interior_mono (hinside k) hm
            rw [interior_closedBall (0:Plane) (ne_of_gt hR)] at hb
            exact (nonsphere hb) (by simpa only [mem_sphere,dist_zero_right] using heR)
          have hArc : IsArcBetween (α '' Icc 0 c) 0 (α c) := by
            refine ⟨γ.extend,γ.continuous_extend.continuousOn,?_,?_,γ.extend_zero,γ.extend_one⟩
            · intro s hs t ht he
              rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
              exact congrArg Subtype.val (hγ he)
            · exact (γ.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans himage
          refine ⟨c,k,hc,hc1,heR,hefront,hArc,?_,?_⟩
          · rintro x ⟨⟨t,ht,rfl⟩,hne⟩
            have ht0 : zeroI < t := by
              apply lt_of_le_of_ne t.property.1
              intro he
              have he0 : t = 0 := Subtype.ext he.symm
              exact hne (by simp [he0,α.source])
            have htc : t < c := by
              apply lt_of_le_of_ne ht.2
              intro he
              exact hne (by simp [he])
            exact hk t ⟨ht0,htc⟩
          · intro x hx
            have hxQ : x ∈ Q k := (hconvex k).segment_subset (hzero k) heQ hx.1
            have hxne0 : x ≠ 0 := by intro he; exact hx.2 (by simp [he])
            have hxnee : x ≠ α c := by intro he; exact hx.2 (by simp [he])
            have hxo : x ∈ openSegment ℝ (0:Plane) (α c) :=
              mem_openSegment_of_ne_left_right hxne0.symm hxnee.symm hx.1
            obtain ⟨a,b,ha,hb,hab,hxb⟩ := hxo
            have hxb' : x = b • α c := by simpa using hxb.symm
            have hxball : x ∈ ball (0:Plane) R := by
              rw [mem_ball,dist_zero_right,hxb',norm_smul,Real.norm_eq_abs,abs_of_pos hb,heR]
              have hb1 : b < 1 := by linarith
              nlinarith
            by_contra hn
            have hxfr : x ∈ frontier (Q k) := by
              rw [(hclosed k).frontier_eq]
              exact ⟨hxQ,hn⟩
            rcases hfront k hxfr with hs | hf
            · exact (nonsphere hxball) hs
            · obtain ⟨j,hj⟩ := mem_iUnion.mp hf
              have hejne : α c ≠ v j := by
                intro he
                apply havoid c hc
                exact mem_iUnion.mpr ⟨j,he ▸ right_mem_segment ℝ 0 (v j)⟩
              have hmeet := LeanEval.Topology.ClassificationOfSurfaces.Moise.radial_segments_inter
                (center := (0:Plane)) (p := α c) (q := v j) (radius := R) hR
                (by simpa only [dist_zero_right] using heR)
                (by simpa only [dist_zero_right] using hv j) hejne
              have hxzero : x ∈ ({0} : Set Plane) := hmeet ▸ ⟨hx.1,hj⟩
              exact hxne0 hxzero
        obtain ⟨c,k,hc,hc1,heR,hefront,hA,hAi,hBi⟩ :=
          firstExit Q v R hR hclosed hconvex hzero hinside hcover hdisj hfront hv α hα ha havoid
        have hbounded : Bornology.IsBounded (Q k) :=
          isBounded_closedBall.subset (hinside k)
        obtain ⟨E,hEi,hEQ,hEf,hJ⟩ := convex_sector_ambient_square_chart (Q k) (hconvex k) (hclosed k) (hcellne k) hbounded
        have hclint : closure (interior (Q k)) = Q k := by
          exact ((hconvex k).closure_interior_eq_closure_of_nonempty_interior (hcellne k)).trans (hclosed k).closure_eq
        have hfrontint : frontier (interior (Q k)) = frontier (Q k) := by
          simp only [frontier,isOpen_interior.interior_eq,hclint,(hclosed k).closure_eq]
        have hinsideEq : interior (Q k) = inside (frontier (Q k)) :=
          bounded_jordan_frontier_region_eq_inside hJ isOpen_interior ((hconvex k).interior.isConnected (hcellne k))
            (hbounded.subset interior_subset) hfrontint
        have hene : (0:Plane) ≠ α c := by
          intro he
          rw [← he,norm_zero] at heR
          linarith
        have hB : IsArcBetween (segment ℝ (0:Plane) (α c)) 0 (α c) := isArcBetween_segment hene
        obtain ⟨aMap⟩ := exists_arcHomeo hA hB
        obtain ⟨F,hpoint,himage,hfix⟩ := jordan_sector_prescribed_crosscut_ambient_extension hJ (hcenter k) hefront hA hB
          (by simpa only [← hinsideEq] using hAi)
          (by simpa only [← hinsideEq] using hBi) aMap
        have hfixQ : ∀ x, x ∉ interior (Q k) → F x = x := by
          simpa only [← hinsideEq] using hfix
        refine ⟨F,c,k,hc,hc1,heR,hefront,hBi,himage,?_,hfixQ,?_,?_⟩
        · apply hfixQ
          have hz : (0:Plane) ∈ Q k \ interior (Q k) := (hclosed k).frontier_eq ▸ hcenter k
          exact hz.2
        · intro x hx
          apply hfixQ
          intro hi
          have hb : x ∈ interior (closedBall (0:Plane) R) := interior_mono (hinside k) hi
          rw [interior_closedBall (0:Plane) (ne_of_gt hR)] at hb
          exact hx hb
        · intro x hx
          apply hfixQ
          intro hi
          exact Set.disjoint_left.mp (hfan k) hi hx
      have insertCells {K : Type} (Q : K → Set Plane) (F : Set Plane)
          (R : ℝ) (hR : 0 < R)
          (hclosed : ∀ k, IsClosed (Q k)) (hconvex : ∀ k, Convex ℝ (Q k))
          (hzero : ∀ k, (0:Plane) ∈ Q k) (hinside : ∀ k, Q k ⊆ closedBall (0:Plane) R)
          (hcover : closedBall (0:Plane) R ⊆ ⋃ k, Q k)
          (hdisj : Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l))))
          (hfront : ∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪ F)
          (hcellne : ∀ k, (interior (Q k)).Nonempty)
          (hcenter : ∀ k, (0:Plane) ∈ frontier (Q k))
          (hfan : ∀ k, Disjoint (interior (Q k)) F)
          (hsupport : ∀ k, ∃ L : Plane →L[ℝ] ℝ,
            (∀ x ∈ Q k, 0 ≤ L x) ∧ (∀ x ∈ Q k, L x = 0 → x ∈ F))
          (k₀ : K) (e : Plane) (heQ : e ∈ Q k₀) (heR : ‖e‖ = R) (heF : e ∉ F)
          (hproper : segment ℝ (0:Plane) e \ {0,e} ⊆ interior (Q k₀)) :
          ∃ (K' : Type) (Q' : K' → Set Plane),
            (∀ k, IsClosed (Q' k)) ∧ (∀ k, Convex ℝ (Q' k)) ∧
            (∀ k, (0:Plane) ∈ Q' k) ∧ (∀ k, Q' k ⊆ closedBall (0:Plane) R) ∧
            (closedBall (0:Plane) R ⊆ ⋃ k, Q' k) ∧
            (Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l)))) ∧
            (∀ k, frontier (Q' k) ⊆ sphere (0:Plane) R ∪ (F ∪ segment ℝ (0:Plane) e)) ∧
            (∀ k, (interior (Q' k)).Nonempty) ∧ (∀ k, (0:Plane) ∈ frontier (Q' k)) ∧
            (∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e)) ∧
            (∀ k, ∃ L : Plane →L[ℝ] ℝ,
              (∀ x ∈ Q' k, 0 ≤ L x) ∧
              (∀ x ∈ Q' k, L x = 0 → x ∈ F ∪ segment ℝ (0:Plane) e)) := by
        classical
        have halfInt (e : Plane) (he : e ≠ 0) :
            interior {x : Plane | 0 ≤ Plane.det e x} = {x | 0 < Plane.det e x} ∧
            interior {x : Plane | Plane.det e x ≤ 0} = {x | Plane.det e x < 0} := by
          let D : Plane →ₗ[ℝ] ℝ := {
            toFun := fun x => Plane.det e x
            map_add' := Plane.det_add_right e
            map_smul' := fun r x => Plane.det_smul_right r e x }
          have hcont : Continuous D := by
            change Continuous (fun x : Plane => Plane.det e x)
            unfold Plane.det
            exact (continuous_const.mul (Plane.continuous_coord 1)).sub
              (continuous_const.mul (Plane.continuous_coord 0))
          have hnorm : ‖e‖^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr he))
          have hsurj : Function.Surjective D := by
            intro r
            refine ⟨(r / ‖e‖^2) • Plane.perp e,?_⟩
            change Plane.det e ((r / ‖e‖^2) • Plane.perp e) = r
            rw [Plane.det_smul_right,Plane.det_perp_self]
            exact div_mul_cancel₀ r hnorm
          have hopen : IsOpenMap D := D.isOpenMap_of_finiteDimensional hsurj
          constructor
          · change interior (D ⁻¹' Ici (0:ℝ)) = D ⁻¹' Ioi (0:ℝ)
            rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Ici]
          · change interior (D ⁻¹' Iic (0:ℝ)) = D ⁻¹' Iio (0:ℝ)
            rw [← hopen.preimage_interior_eq_interior_preimage hcont,interior_Iic]
        have hen : e ≠ 0 := by intro he; simp [he] at heR; linarith
        obtain ⟨L,hL,hker⟩ := hsupport k₀
        have heL : 0 < L e := lt_of_le_of_ne (hL e heQ) (fun hz => heF (hker e heQ hz.symm))
        let A := Q k₀ ∩ {x | 0 ≤ Plane.det e x}
        let B := Q k₀ ∩ {x | Plane.det e x ≤ 0}
        obtain ⟨hab,hinter,hca,hcb⟩ := radial_sector_determinant_split
          (Q k₀) (hconvex k₀) R hR (hinside k₀) (hzero k₀) e heQ heR L hL heL
        have hcont : Continuous (fun x : Plane => Plane.det e x) := by
          unfold Plane.det
          exact (continuous_const.mul (Plane.continuous_coord 1)).sub
            (continuous_const.mul (Plane.continuous_coord 0))
        have haClosed : IsClosed A := (hclosed k₀).inter (isClosed_le continuous_const hcont)
        have hbClosed : IsClosed B := (hclosed k₀).inter (isClosed_le hcont continuous_const)
        obtain ⟨hfa,hfb,hdab⟩ := sector_split_frontier_invariant (Q k₀) (hclosed k₀) e hen hinter
        have hhalf : (1/2:ℝ) • e ∈ segment ℝ (0:Plane) e \ {0,e} := by
          refine ⟨⟨1/2,1/2,by norm_num,by norm_num,by norm_num,by simp⟩,?_⟩
          intro hh
          have hh' : (1/2:ℝ) • e = 0 ∨ (1/2:ℝ) • e = e := by simpa using hh
          rcases hh' with hh|hh
          · exact hen ((smul_eq_zero.mp hh).resolve_left (by norm_num))
          · have hz : (-1/2:ℝ) • e = 0 := by calc
              (-1/2:ℝ) • e = (1/2:ℝ) • e - e := by module
              _ = 0 := by rw [hh,sub_self]
            exact hen ((smul_eq_zero.mp hz).resolve_left (by norm_num))
        obtain ⟨hneA,hneB⟩ := sector_split_interiors_nonempty (Q k₀) ((1/2:ℝ) • e) e
          (hproper hhalf) hen (by simp)
        let K' := Sum {k : K // k ≠ k₀} Bool
        let Q' : K' → Set Plane := Sum.elim (fun k => Q k.val) (fun b => if b then B else A)
        have hnewclosed : ∀ k, IsClosed (Q' k) := by
          intro k
          cases k with
          | inl k => exact hclosed k.val
          | inr b => cases b; exact haClosed; exact hbClosed
        have hmona : interior A ⊆ interior (Q k₀) := interior_mono inter_subset_left
        have hmonb : interior B ⊆ interior (Q k₀) := interior_mono inter_subset_left
        have hnewzero : ∀ k, (0:Plane) ∈ Q' k := by
          intro k
          cases k with
          | inl k => exact hzero k.val
          | inr b => cases b <;> exact ⟨hzero k₀,by simp [Plane.det]⟩
        have newSubsetOld : ∀ k : K', ∃ j : K, Q' k ⊆ Q j := by
          intro k
          cases k with
          | inl k => exact ⟨k.val,Subset.refl _⟩
          | inr b => cases b <;> exact ⟨k₀,inter_subset_left⟩
        have hnewinside : ∀ k, Q' k ⊆ closedBall (0:Plane) R := by
          intro k
          obtain ⟨j,hj⟩ := newSubsetOld k
          exact hj.trans (hinside j)
        have hnewcenter : ∀ k, (0:Plane) ∈ frontier (Q' k) := by
          intro k
          rw [(hnewclosed k).frontier_eq]
          refine ⟨hnewzero k,?_⟩
          intro hi
          obtain ⟨j,hj⟩ := newSubsetOld k
          have hj0 : (0:Plane) ∉ interior (Q j) := by
            have hh : (0:Plane) ∈ Q j \ interior (Q j) := (hclosed j).frontier_eq ▸ hcenter j
            exact hh.2
          exact hj0 (interior_mono hj hi)
        have hnewdisj : Pairwise (fun k l => Disjoint (interior (Q' k)) (interior (Q' l))) := by
          intro k l hkl
          cases k with
          | inl k =>
            cases l with
            | inl l => exact hdisj (fun he => hkl (congrArg Sum.inl (Subtype.ext he)))
            | inr b => cases b; exact (hdisj k.property).mono_right hmona; exact (hdisj k.property).mono_right hmonb
          | inr b =>
            cases l with
            | inl l => cases b; exact (hdisj l.property.symm).mono_left hmona; exact (hdisj l.property.symm).mono_left hmonb
            | inr c => cases b <;> cases c
                       · exact False.elim (hkl rfl)
                       · exact hdab
                       · exact hdab.symm
                       · exact False.elim (hkl rfl)
        have hnewfan : ∀ k, Disjoint (interior (Q' k)) (F ∪ segment ℝ (0:Plane) e) := by
          intro k
          apply Set.disjoint_left.mpr
          intro x hi hx
          obtain ⟨j,hj⟩ := newSubsetOld k
          rcases hx with hf|hr
          · exact Set.disjoint_left.mp (hfan j) (interior_mono hj hi) hf
          · have hd : Plane.det e x = 0 := by
              obtain ⟨a,b,ha,hb,hab,hx⟩ := hr
              rw [← hx]
              simp
            cases k with
            | inl k =>
              by_cases hx0 : x = 0
              · have hh : x ∈ frontier (Q' (.inl k)) := hx0.symm ▸ hnewcenter (.inl k)
                have hh' : x ∈ Q' (.inl k) \ interior (Q' (.inl k)) := (hnewclosed _).frontier_eq ▸ hh
                exact hh'.2 hi
              by_cases hxe : x = e
              · have hb : e ∈ ball (0:Plane) R := by
                  have hh := interior_mono (hinside k.val) (show x ∈ interior (Q k.val) from hi)
                  rw [interior_closedBall (0:Plane) (ne_of_gt hR),hxe] at hh
                  exact hh
                have hh : ‖e‖ < R := by simpa only [mem_ball,dist_zero_right] using hb
                exact (ne_of_lt hh) heR
              have hip : x ∈ interior (Q k₀) := hproper ⟨hr,by simpa using And.intro hx0 hxe⟩
              exact Set.disjoint_left.mp (hdisj k.property) hi hip
            | inr b =>
              cases b
              · have hp := interior_mono (show A ⊆ {x | 0 ≤ Plane.det e x} from inter_subset_right) hi
                rw [(halfInt e hen).1] at hp
                exact (ne_of_gt (show 0 < Plane.det e x from hp)) hd
              · have hn := interior_mono (show B ⊆ {x | Plane.det e x ≤ 0} from inter_subset_right) hi
                rw [(halfInt e hen).2] at hn
                exact (ne_of_lt (show Plane.det e x < 0 from hn)) hd
        refine ⟨K',Q',hnewclosed,?_,hnewzero,hnewinside,?_,hnewdisj,?_,?_,hnewcenter,hnewfan,?_⟩
        · intro k
          cases k with
          | inl k => exact hconvex k.val
          | inr b => cases b; exact hca; exact hcb
        · intro x hx
          obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hx)
          by_cases hje : j = k₀
          · subst j
            have hxAB : x ∈ A ∪ B := hab.symm ▸ hj
            rcases hxAB with hxA|hxB
            · exact mem_iUnion.mpr ⟨.inr false,hxA⟩
            · exact mem_iUnion.mpr ⟨.inr true,hxB⟩
          · exact mem_iUnion.mpr ⟨.inl ⟨j,hje⟩,hj⟩
        · intro k x hx
          cases k with
          | inl k =>
            rcases hfront k.val hx with hs|hf
            · exact Or.inl hs
            · exact Or.inr (Or.inl hf)
          | inr b =>
            have hh : x ∈ frontier (Q k₀) ∪ segment ℝ (0:Plane) e := by
              cases b; exact hfa hx; exact hfb hx
            rcases hh with hfr|hr
            · rcases hfront k₀ hfr with hs|hf
              · exact Or.inl hs
              · exact Or.inr (Or.inl hf)
            · exact Or.inr (Or.inr hr)
        · intro k
          cases k with
          | inl k => exact hcellne k.val
          | inr b => cases b; exact hneA; exact hneB
        · intro k
          obtain ⟨j,hj⟩ := newSubsetOld k
          obtain ⟨Lj,hLj,hkj⟩ := hsupport j
          exact ⟨Lj,fun x hx => hLj x (hj hx),fun x hx he => Or.inl (hkj x (hj hx) he)⟩
      let State : Finset J → Prop := fun S =>
        ∃ (H : Plane ≃ₜ Plane) (c : J → I) (w : J → Plane),
          H 0 = 0 ∧ (∀ x, x ∉ ball (0:Plane) R₀ → H x = x) ∧
          (∀ j, H (γ j oneI) ∉ closedBall (0:Plane) R) ∧
          (∀ j ∈ S, 0 < (c j).val ∧ (c j).val < 1 ∧ ‖w j‖ = R ∧
            H '' (γ j '' Icc 0 (c j)) = segment ℝ (0:Plane) (w j)) ∧ Cells S w
      have hbase : State S₀ := ⟨H₀,c₀,w₀,hH₀,hfix₀,hend₀,hprefix₀,hCells₀⟩
      have fanSubtype (S : Finset J) (w : J → Plane) :
          fan S w = ⋃ i : {i : J // i ∈ S}, segment ℝ (0:Plane) (w i.val) := by
        ext x
        simp [fan]
      have step (S : Finset J) (hS : State S) (j : J) (hj : j ∉ S) : State (insert j S) := by
        obtain ⟨H,c,w,hH,hfix,hend,hprefix,hCells⟩ := hS
        obtain ⟨K,Q,hclosed,hconvex,hzero,hinside,hcover,hdisj,hfront,hcellne,hcenter,hfan,hsupport⟩ := hCells
        have hzeroI : (0:I) = zeroI := by apply Subtype.ext; rfl
        let α : Path (0:Plane) (H (γ j oneI)) := {
          toFun := H ∘ γ j
          continuous_toFun := H.continuous.comp (hγ j).continuous
          source' := by
            change H (γ j 0) = 0
            rw [hzeroI,hstart j,hH]
          target' := rfl }
        have hα : Function.Injective α := H.injective.comp (hγ j).injective
        have havoid : ∀ t : I, 0 < t.val → α t ∉ fan S w := by
          intro t ht hm
          obtain ⟨i,hm⟩ := mem_iUnion.mp hm
          obtain ⟨hi,hmi⟩ := mem_iUnion.mp hm
          rw [← (hprefix i hi).2.2.2] at hmi
          obtain ⟨x,⟨s,hs,rfl⟩,he⟩ := hmi
          have he' : γ j t = γ i s := (H.injective he).symm
          have hji : j ≠ i := by intro he; exact hj (he.symm ▸ hi)
          have hz : γ j t = 0 := by
            have hp : γ j t ∈ range (γ j) ∩ range (γ i) := ⟨⟨t,rfl⟩,⟨s,he'.symm⟩⟩
            rw [hmeet j i hji] at hp
            exact hp
          have htzero : t = zeroI := (hγ j).injective (hz.trans (hstart j).symm)
          have hh : t.val = 0 := congrArg Subtype.val htzero
          linarith
        obtain ⟨T,d,k,hd,hd1,heR,hefront,hproper,himage,hT,hTQ,hTR,hTF⟩ :=
          insertArm Q (fun i : {i : J // i ∈ S} => w i.val) R hR
            hclosed hconvex hzero hinside hcover hdisj
            (by simpa only [← fanSubtype S w] using hfront) hcellne hcenter
            (by simpa only [← fanSubtype S w] using hfan)
            (fun i => (hprefix i.val i.property).2.2.1) α hα (hend j)
            (by simpa only [← fanSubtype S w] using havoid)
        have hTF' : ∀ x ∈ fan S w, T x = x := by
          simpa only [← fanSubtype S w] using hTF
        have heQ : α d ∈ Q k := (hclosed k).closure_eq ▸ frontier_subset_closure hefront
        have heF : α d ∉ fan S w := havoid d hd
        obtain ⟨K',Q',hclosed',hconvex',hzero',hinside',hcover',hdisj',hfront',hcellne',hcenter',hfan',hsupport'⟩ :=
          insertCells Q (fan S w) R hR hclosed hconvex hzero hinside hcover hdisj
            hfront hcellne hcenter hfan hsupport k (α d) heQ heR heF hproper
        let H' := H.trans T
        let c' : J → I := Function.update c j d
        let w' : J → Plane := Function.update w j (α d)
        have hfanEq : fan (insert j S) w' = fan S w ∪ segment ℝ (0:Plane) (α d) := by
          ext x
          constructor
          · intro hx
            obtain ⟨i,hx⟩ := mem_iUnion.mp hx
            obtain ⟨hi,hxi⟩ := mem_iUnion.mp hx
            rcases Finset.mem_insert.mp hi with he|hi
            · subst i
              exact Or.inr (by simpa [w'] using hxi)
            · have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
              exact Or.inl (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,by simpa [w',Function.update_of_ne hij] using hxi⟩⟩)
          · rintro (hx|hx)
            · obtain ⟨i,hx⟩ := mem_iUnion.mp hx
              obtain ⟨hi,hxi⟩ := mem_iUnion.mp hx
              have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
              exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hi,by simpa [w',Function.update_of_ne hij] using hxi⟩⟩
            · exact mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨Finset.mem_insert_self _ _,by simpa [w'] using hx⟩⟩
        refine ⟨H',c',w',?_,?_,?_,?_,?_⟩
        · change T (H 0) = 0
          rw [hH,hT]
        · intro x hx
          have hxR : x ∉ ball (0:Plane) R := fun hh => hx ((ball_subset_ball hRR₀) hh)
          change T (H x) = x
          rw [hfix x hx,hTR x hxR]
        · intro i
          change T (H (γ i oneI)) ∉ closedBall (0:Plane) R
          rw [hTR _ (fun hh => hend i (ball_subset_closedBall hh))]
          exact hend i
        · intro i hi
          rcases Finset.mem_insert.mp hi with he|hi
          · subst i
            refine ⟨by simpa [c'] using hd,by simpa [c'] using hd1,by simpa [w'] using heR,?_⟩
            simp only [c',w',Function.update_self]
            change (T ∘ H) '' (γ j '' Icc 0 d) = segment ℝ 0 (α d)
            rw [image_comp]
            have hαimage : H '' (γ j '' Icc 0 d) = α '' Icc 0 d := (image_comp H (γ j) _).symm
            rw [hαimage]
            exact himage
          · have hij : i ≠ j := by intro he; exact hj (he ▸ hi)
            have hcEq : c' i = c i := Function.update_of_ne hij _ _
            have hwEq : w' i = w i := Function.update_of_ne hij _ _
            obtain ⟨hip,hi1,hin,hiim⟩ := hprefix i hi
            refine ⟨by simpa only [hcEq] using hip,by simpa only [hcEq] using hi1,
              by simpa only [hwEq] using hin,?_⟩
            rw [hcEq,hwEq]
            change (T ∘ H) '' (γ i '' Icc 0 (c i)) = segment ℝ 0 (w i)
            rw [image_comp,hiim]
            have hEq : EqOn T id (segment ℝ (0:Plane) (w i)) := by
              intro x hx
              exact hTF' x (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,hx⟩⟩)
            simpa only [image_id] using hEq.image_eq
        · refine ⟨K',Q',hclosed',hconvex',hzero',hinside',hcover',hdisj',?_,hcellne',hcenter',?_,?_⟩
          · simpa only [hfanEq] using hfront'
          · simpa only [hfanEq] using hfan'
          · simpa only [hfanEq] using hsupport'
      have finish (T : Finset J) : State (S₀ ∪ T) := by
        induction T using Finset.induction_on with
        | empty => simpa using hbase
        | @insert j T hjT ih =>
          by_cases hjS : j ∈ S₀ ∪ T
          · have heq : S₀ ∪ insert j T = S₀ ∪ T := by
              ext i
              simp only [Finset.mem_union,Finset.mem_insert]
              grind
            exact heq.symm ▸ ih
          · have heq : S₀ ∪ insert j T = insert j (S₀ ∪ T) := by
              ext i
              simp only [Finset.mem_union,Finset.mem_insert]
              tauto
            exact heq.symm ▸ step (S₀ ∪ T) ih j hjS
      obtain ⟨H,c,w,hH,hfix,hend,hprefix,hCells⟩ := finish Finset.univ
      refine ⟨H,c,w,hH,hfix,?_⟩
      intro j
      exact hprefix j (by simp)
    have halfCells (v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ = R) :
        ∃ Q : Bool → Set Plane,
          (∀ k, IsClosed (Q k)) ∧ (∀ k, Convex ℝ (Q k)) ∧
          (∀ k, (0:Plane) ∈ Q k) ∧ (∀ k, Q k ⊆ closedBall (0:Plane) R) ∧
          (closedBall (0:Plane) R ⊆ ⋃ k, Q k) ∧
          (Pairwise (fun k l => Disjoint (interior (Q k)) (interior (Q l)))) ∧
          (∀ k, frontier (Q k) ⊆ sphere (0:Plane) R ∪
            (segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) ∧
          (∀ k, (interior (Q k)).Nonempty) ∧
          (∀ k, (0:Plane) ∈ frontier (Q k)) ∧
          (∀ k, Disjoint (interior (Q k))
            (segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) ∧
          (∀ k, ∃ L : Plane →L[ℝ] ℝ,
            (∀ x ∈ Q k, 0 ≤ L x) ∧
            (∀ x ∈ Q k, L x = 0 → x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v))) := by
      have hvne : v ≠ 0 := by intro he; simp [he] at hv; linarith
      let D : Plane →ₗ[ℝ] ℝ := {
        toFun := fun x => Plane.det v x
        map_add' := Plane.det_add_right v
        map_smul' := fun r x => Plane.det_smul_right r v x }
      let L : Bool → Plane →L[ℝ] ℝ := fun b => if b then -D.toContinuousLinearMap else D.toContinuousLinearMap
      let Q : Bool → Set Plane := fun b => closedBall (0:Plane) R ∩ {x | 0 ≤ L b x}
      have hclosed : ∀ b, IsClosed (Q b) := fun b =>
        isClosed_closedBall.inter (isClosed_le continuous_const (L b).continuous)
      have hconvex : ∀ b, Convex ℝ (Q b) := by
        intro b
        apply (convex_closedBall (0:Plane) R).inter
        intro x hx y hy a b ha hb hab
        change 0 ≤ L _ (a • x + b • y)
        simp only [map_add,map_smul,smul_eq_mul]
        exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
      have hzero : ∀ b, (0:Plane) ∈ Q b := by
        intro b
        exact ⟨by simpa using hR.le,by simp⟩
      have hinside : ∀ b, Q b ⊆ closedBall (0:Plane) R := fun _ => inter_subset_left
      have hlinearInt : ∀ b, interior {x | 0 ≤ L b x} = {x | 0 < L b x} := by
        intro b
        have hsurj : Function.Surjective (L b) := by
          intro r
          cases b
          · refine ⟨(r / ‖v‖^2) • Plane.perp v,?_⟩
            change Plane.det v ((r / ‖v‖^2) • Plane.perp v) = r
            rw [Plane.det_smul_right,Plane.det_perp_self]
            exact div_mul_cancel₀ r (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hvne)))
          · refine ⟨(-r / ‖v‖^2) • Plane.perp v,?_⟩
            change -Plane.det v ((-r / ‖v‖^2) • Plane.perp v) = r
            rw [Plane.det_smul_right,Plane.det_perp_self,div_mul_cancel₀ _
              (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hvne))),neg_neg]
        have hopen := (L b).toLinearMap.isOpenMap_of_finiteDimensional hsurj
        change IsOpenMap (L b) at hopen
        change interior ((L b) ⁻¹' Ici (0:ℝ)) = (L b) ⁻¹' Ioi (0:ℝ)
        rw [← hopen.preimage_interior_eq_interior_preimage (L b).continuous,interior_Ici]
      have hInt : ∀ b, interior (Q b) = ball (0:Plane) R ∩ {x | 0 < L b x} := by
        intro b
        rw [interior_inter,interior_closedBall (0:Plane) (ne_of_gt hR),hlinearInt]
      have kernelFan {x : Plane} (hx : x ∈ closedBall (0:Plane) R)
          (hdet : Plane.det v x = 0) : x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v) := by
        obtain ⟨r,hr⟩ := (Plane.det_eq_zero_iff_smul v x hvne).mp hdet
        have hnr : |r| ≤ 1 := by
          have hh : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
          rw [hr,norm_smul,Real.norm_eq_abs,hv] at hh
          nlinarith
        rcases le_total 0 r with hp|hn
        · apply Or.inl
          rw [hr]
          have hr1 : r ≤ 1 := le_trans (le_abs_self r) hnr
          exact ⟨1-r,r,sub_nonneg.mpr hr1,hp,by ring,by simp⟩
        · apply Or.inr
          have hr1 : -r ≤ 1 := le_trans (neg_le_abs r) hnr
          have hxneg : x = (-r) • (-v) := by rw [hr]; module
          rw [hxneg]
          exact ⟨1-(-r),-r,sub_nonneg.mpr hr1,neg_nonneg.mpr hn,by ring,by simp⟩
      have hker : ∀ b x, L b x = 0 → Plane.det v x = 0 := by
        intro b x hx
        cases b
        · exact hx
        · change -Plane.det v x = 0 at hx
          exact neg_eq_zero.mp hx
      have hfanD : ∀ x ∈ segment ℝ (0:Plane) v ∪ segment ℝ (0:Plane) (-v), Plane.det v x = 0 := by
        intro x hx
        rcases hx with hx|hx <;> obtain ⟨a,b,ha,hb,hab,hx⟩ := hx <;> rw [← hx] <;> simp [Plane.det] <;> ring
      refine ⟨Q,hclosed,hconvex,hzero,hinside,?_,?_,?_,?_,?_,?_,?_⟩
      · intro x hx
        rcases le_total 0 (Plane.det v x) with hp|hn
        · exact mem_iUnion.mpr ⟨false,hx,hp⟩
        · exact mem_iUnion.mpr ⟨true,hx,by change 0 ≤ -Plane.det v x; linarith⟩
      · intro b c hbc
        apply Set.disjoint_left.mpr
        intro x hxb hxc
        rw [hInt b] at hxb
        rw [hInt c] at hxc
        cases b <;> cases c
        · exact hbc rfl
        · have hp : 0 < Plane.det v x := hxb.2
          have hn : 0 < -Plane.det v x := hxc.2
          linarith
        · have hn : 0 < -Plane.det v x := hxb.2
          have hp : 0 < Plane.det v x := hxc.2
          linarith
        · exact hbc rfl
      · intro b x hx
        rcases frontier_inter_subset (closedBall (0:Plane) R) {x | 0 ≤ L b x} hx with hball|hline
        · exact Or.inl ((frontier_closedBall (0:Plane) (ne_of_gt hR)) ▸ hball.1)
        · apply Or.inr
          have hxQ : x ∈ Q b := (hclosed b).closure_eq ▸ frontier_subset_closure hx
          exact kernelFan hxQ.1 (hker b x (frontier_le_subset_eq continuous_const (L b).continuous hline.2).symm)
      · intro b
        cases b
        · refine ⟨(1/2:ℝ) • Plane.perp v,?_⟩
          rw [hInt]
          constructor
          · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),Plane.norm_perp,hv]
            linarith
          · change 0 < Plane.det v ((1/2:ℝ) • Plane.perp v)
            rw [Plane.det_smul_right,Plane.det_perp_self]
            exact mul_pos (by norm_num) (sq_pos_of_pos (norm_pos_iff.mpr hvne))
        · refine ⟨(-1/2:ℝ) • Plane.perp v,?_⟩
          rw [hInt]
          constructor
          · simp only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_neg (by norm_num : (-1/2:ℝ)<0),Plane.norm_perp,hv]
            linarith
          · change 0 < -Plane.det v ((-1/2:ℝ) • Plane.perp v)
            rw [Plane.det_smul_right,Plane.det_perp_self]
            nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hvne)]
      · intro b
        rw [(hclosed b).frontier_eq]
        refine ⟨hzero b,?_⟩
        rw [hInt b]
        rintro ⟨_,hh⟩
        simpa using hh
      · intro b
        apply Set.disjoint_left.mpr
        intro x hx hf
        rw [hInt b] at hx
        have hd := hfanD x hf
        cases b
        · have hp : 0 < Plane.det v x := hx.2
          linarith
        · have hn : 0 < -Plane.det v x := hx.2
          linarith
      · intro b
        refine ⟨L b,fun x hx => hx.2,?_⟩
        intro x hx hd
        exact kernelFan hx.1 (hker b x hd)
    have shorten (γ : I → Plane) (hγ : Topology.IsClosedEmbedding γ)
        (hstart : γ zeroI = 0) (H : Plane ≃ₜ Plane) (hH : H 0 = 0)
        (c : I) (hc : 0 < c.val) (hc1 : c.val < 1) (v : Plane) (hv : v ≠ 0)
        (hrad : H '' (γ '' Icc 0 c) = segment ℝ (0:Plane) v)
        (r : ℝ) (hr : 0 < r) (hrv : r < ‖v‖) :
        ∃ d : I, 0 < d.val ∧ d.val < 1 ∧ d.val ≤ c.val ∧
          H '' (γ '' Icc 0 d) = segment ℝ (0:Plane) ((r/‖v‖) • v) := by
      have pullback {p b q r s : Plane} (γ : Path p b) (hγ : Function.Injective γ)
          (F : Plane ≃ₜ Plane) (B C : Set Plane)
          (hC : IsArcBetween C r s) (hB : IsArcBetween B (F p) q)
          (hFC : F '' range γ ⊆ C) (hBC : B ⊆ C)
          (hq : q ∈ F '' range γ) (hqp : q ≠ F p) :
          ∃ c : I, 0 < c ∧ c ≤ 1 ∧ F '' (γ '' Icc 0 c) = B := by
        obtain ⟨x,⟨c,rfl⟩,hcq⟩ := hq
        have hc0 : c ≠ 0 := by intro he; subst c; exact hqp (hcq.symm.trans (congrArg F γ.source))
        have hc : 0 < c := lt_of_le_of_ne c.property.1 hc0.symm
        let k : I → I := fun t => ⟨(c:ℝ)*(t:ℝ), by
          constructor
          · exact mul_nonneg c.property.1 t.property.1
          · nlinarith [c.property.1,c.property.2,t.property.1,t.property.2]⟩
        let η : Path (F p) q := {
          toFun := F ∘ γ ∘ k
          continuous_toFun := F.continuous.comp (γ.continuous.comp (by fun_prop))
          source' := by simp [k,γ.source]
          target' := by simpa [k] using hcq }
        have hη : Function.Injective η := by
          intro u v he
          have hh := congrArg Subtype.val (hγ (F.injective he))
          change (c:ℝ)*(u:ℝ) = (c:ℝ)*(v:ℝ) at hh
          exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hc) hh)
        have hrange : range η = F '' (γ '' Icc 0 c) := by
          ext y
          constructor
          · rintro ⟨t,rfl⟩
            refine ⟨γ (k t),⟨k t,?_,rfl⟩,rfl⟩
            exact ⟨(k t).property.1,by change (c:ℝ)*(t:ℝ) ≤ c; nlinarith [c.property.1,t.property.2]⟩
          · rintro ⟨_,⟨u,hu,rfl⟩,rfl⟩
            let t : I := ⟨(u:ℝ)/(c:ℝ),by
              constructor
              · exact div_nonneg u.property.1 hc.le
              · exact (div_le_one hc).mpr hu.2⟩
            refine ⟨t,?_⟩
            change F (γ (k t)) = F (γ u)
            congr 2
            apply Subtype.ext
            change (c:ℝ)*((u:ℝ)/(c:ℝ)) = u
            field_simp [ne_of_gt hc]
        have hA : IsArcBetween (range η) (F p) q := by
          refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
          · intro u hu v hv he
            rw [Path.extend_apply _ hu,Path.extend_apply _ hv] at he
            exact congrArg Subtype.val (hη he)
          · exact η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))
        have hAC : range η ⊆ C := by
          rw [hrange]
          exact (image_mono (image_subset_range _ _)).trans hFC
        refine ⟨c,hc,c.property.2,?_⟩
        exact hrange.symm.trans (hA.eq_of_subset_arc hB hC hAC hBC)
      have productImage {X : Type} (γ : I → X) (c d : I) (hc : 0 < c) :
          let k : I → I := fun t => ⟨(c:ℝ)*(t:ℝ),by
            constructor
            · exact mul_nonneg c.property.1 t.property.1
            · nlinarith [c.property.1,c.property.2,t.property.1,t.property.2]⟩
          let cd : I := ⟨(c:ℝ)*(d:ℝ),by
            constructor
            · exact mul_nonneg c.property.1 d.property.1
            · nlinarith [c.property.1,c.property.2,d.property.1,d.property.2]⟩
          (γ ∘ k) '' Icc 0 d = γ '' Icc 0 cd := by
        dsimp only
        ext x
        constructor
        · rintro ⟨t,ht,rfl⟩
          refine ⟨⟨(c:ℝ)*(t:ℝ),by
            constructor
            · exact mul_nonneg c.property.1 t.property.1
            · nlinarith [c.property.1,c.property.2,t.property.1,t.property.2]⟩,?_,rfl⟩
          exact ⟨by change 0 ≤ (c:ℝ)*(t:ℝ); exact mul_nonneg hc.le t.property.1,
            by change (c:ℝ)*(t:ℝ) ≤ (c:ℝ)*(d:ℝ); exact mul_le_mul_of_nonneg_left ht.2 hc.le⟩
        · rintro ⟨s,hs,rfl⟩
          have hsreal : (s:ℝ) ≤ (c:ℝ)*(d:ℝ) := hs.2
          let t : I := ⟨(s:ℝ)/(c:ℝ),by
            constructor
            · exact div_nonneg s.property.1 hc.le
            · apply (div_le_one hc).mpr
              exact hsreal.trans (by nlinarith [c.property.1,d.property.2])⟩
          refine ⟨t,⟨t.property.1,?_⟩,?_⟩
          · change (s:ℝ)/(c:ℝ) ≤ d
            apply (div_le_iff₀ hc).mpr
            simpa [mul_comm] using hsreal
          · change γ ⟨(c:ℝ)*((s:ℝ)/(c:ℝ)),_⟩ = γ s
            congr 1
            apply Subtype.ext
            change (c:ℝ)*((s:ℝ)/(c:ℝ)) = s
            field_simp [ne_of_gt hc]
      let k : I → I := fun t => ⟨c.val*t.val,by
        constructor
        · exact mul_nonneg c.property.1 t.property.1
        · nlinarith [c.property.1,c.property.2,t.property.1,t.property.2]⟩
      let α : Path (0:Plane) (γ c) := {
        toFun := γ ∘ k
        continuous_toFun := hγ.continuous.comp (by fun_prop)
        source' := by simpa [k] using hstart
        target' := by simp [k] }
      have hα : Function.Injective α := by
        intro s t he
        have hh := congrArg Subtype.val (hγ.injective he)
        change c.val*s.val = c.val*t.val at hh
        exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hc) hh)
      have hrange : range α = γ '' Icc 0 c := by
        have hi : (γ ∘ k) '' Icc 0 (1:I) = γ '' Icc 0 c := by
          have hh := productImage γ c (1:I) hc
          simpa [k] using hh
        have hI : (Icc (0:I) 1 : Set I) = univ := by
          ext t
          simp only [mem_Icc,mem_univ,iff_true]
          exact ⟨t.property.1,t.property.2⟩
        change range (γ ∘ k) = γ '' Icc 0 c
        simpa only [hI,image_univ] using hi
      have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
      let q : Plane := (r/‖v‖) • v
      have hqnorm : ‖q‖ = r := by
        simp only [q,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hvnorm)]
        exact div_mul_cancel₀ r (ne_of_gt hvnorm)
      have hqC : q ∈ segment ℝ (0:Plane) v := by
        have hs0 : 0 ≤ r/‖v‖ := (div_pos hr hvnorm).le
        have hs1 : r/‖v‖ ≤ 1 := (div_le_one hvnorm).mpr hrv.le
        exact ⟨1-r/‖v‖,r/‖v‖,sub_nonneg.mpr hs1,hs0,by ring,by simp [q]⟩
      have hqne : q ≠ 0 := by intro he; rw [he,norm_zero] at hqnorm; linarith
      have hB : IsArcBetween (segment ℝ (0:Plane) q) (H 0) q := by
        rw [hH]
        exact isArcBetween_segment hqne.symm
      have hBC : segment ℝ (0:Plane) q ⊆ segment ℝ (0:Plane) v :=
        (convex_segment (0:Plane) v).segment_subset (left_mem_segment ℝ 0 v) hqC
      have hqimage : q ∈ H '' range α := by rw [hrange,hrad]; exact hqC
      obtain ⟨d,hd,hd1,hdimage⟩ := pullback α hα H
        (segment ℝ (0:Plane) q) (segment ℝ (0:Plane) v)
        (isArcBetween_segment hv.symm) hB
        (by rw [hrange,hrad]) hBC hqimage (by simpa only [hH] using hqne)
      let cd : I := ⟨c.val*d.val,by
        constructor
        · exact mul_nonneg c.property.1 d.property.1
        · nlinarith [c.property.1,c.property.2,d.property.1,d.property.2]⟩
      have hcdpos : 0 < cd.val := mul_pos hc hd
      have hcdle : cd.val ≤ c.val := by
        change c.val*d.val ≤ c.val
        have hdreal : d.val ≤ 1 := hd1
        nlinarith [c.property.1]
      refine ⟨cd,hcdpos,hcdle.trans_lt hc1,hcdle,?_⟩
      have hp := productImage γ c d hc
      change (γ ∘ k) '' Icc 0 d = γ '' Icc 0 cd at hp
      change H '' ((γ ∘ k) '' Icc 0 d) = segment ℝ 0 q at hdimage
      exact hp ▸ hdimage
    have tailCore {J : Type} [Fintype J] (γ : J → I → EuclideanSpace ℝ (Fin 2))
        (hγ : ∀ j, Topology.IsClosedEmbedding (γ j)) (o : EuclideanSpace ℝ (Fin 2))
        (hstart : ∀ j, γ j 0 = o) (F : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
        (hFo : F o = o) (cut : J → I) (hcut : ∀ j, 0 < cut j)
        (v : J → EuclideanSpace ℝ (Fin 2)) (hv : ∀ j, v j ≠ 0)
        (R : ℝ) (hR : 0 < R) :
        ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ (∀ j, ρ < ‖v j‖) ∧
          ∀ j, Disjoint (F '' (γ j '' {t : I | cut j ≤ t})) (closedBall o ρ) := by
      classical
      let K : J → Set (EuclideanSpace ℝ (Fin 2)) := fun j =>
        F '' (γ j '' {t : I | cut j ≤ t})
      have hK : ∀ j, IsCompact (K j) := by
        intro j
        have hc : IsCompact {t : I | cut j ≤ t} := (isClosed_le continuous_const continuous_id).isCompact
        exact (hc.image (hγ j).continuous).image F.continuous
      have hoK : o ∉ ⋃ j, K j := by
        intro hm
        obtain ⟨j,_,⟨t,ht,rfl⟩,he⟩ := mem_iUnion.mp hm
        have hh : γ j t = o := F.injective (he.trans hFo.symm)
        have ht0 : t = 0 := (hγ j).injective (hh.trans (hstart j).symm)
        have hcle : cut j ≤ 0 := ht0 ▸ ht
        exact not_le_of_gt (hcut j) hcle
      have hU : IsOpen (⋃ j, K j)ᶜ := (isCompact_iUnion hK).isClosed.isOpen_compl
      obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hoK)
      have small (s : Finset J) : ∃ b : ℝ, 0 < b ∧ ∀ j ∈ s, b < ‖v j‖ := by
        induction s using Finset.induction_on with
        | empty => exact ⟨1,by norm_num,by simp⟩
        | @insert j s hj ih =>
          obtain ⟨b,hb,hbs⟩ := ih
          refine ⟨min b (‖v j‖/2),lt_min hb (half_pos (norm_pos_iff.mpr (hv j))),?_⟩
          intro k hk
          rcases Finset.mem_insert.mp hk with hkj | hk
          · subst k
            exact (min_le_right _ _).trans_lt (half_lt_self (norm_pos_iff.mpr (hv j)))
          · exact (min_le_left _ _).trans_lt (hbs k hk)
      obtain ⟨b,hb,hbs⟩ := small Finset.univ
      let ρ : ℝ := min R (min ε b) / 2
      have hρ : 0 < ρ := half_pos (lt_min hR (lt_min hε hb))
      have hρR : ρ < R := (half_lt_self (lt_min hR (lt_min hε hb))).trans_le (min_le_left _ _)
      have hρε : ρ < ε := (half_lt_self (lt_min hR (lt_min hε hb))).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))
      have hρb : ρ < b := (half_lt_self (lt_min hR (lt_min hε hb))).trans_le
        ((min_le_right _ _).trans (min_le_right _ _))
      refine ⟨ρ,hρ,hρR,fun j => hρb.trans (hbs j (Finset.mem_univ j)),?_⟩
      intro j
      apply Set.disjoint_left.mpr
      intro x hxK hxB
      have hxε : x ∈ ball o ε := closedBall_subset_ball hρε hxB
      exact (hball hxε) (mem_iUnion.mpr ⟨j,hxK⟩)
    have prefixSet (b : I) : {t : I | t.val ≤ b.val} = Icc 0 b := by
      ext t
      change t.val ≤ b.val ↔ 0 ≤ t.val ∧ t.val ≤ b.val
      exact ⟨fun ht => ⟨t.property.1,ht⟩,fun ht => ht.2⟩
    obtain ⟨j₀,j₁,hjne⟩ := Fintype.one_lt_card_iff.mp hcard
    let δ : Bool → I → Plane := fun b => if b then γ j₁ else γ j₀
    have hδ : ∀ b, Topology.IsClosedEmbedding (δ b) := by
      intro b
      cases b; exact hγ j₀; exact hγ j₁
    have hδstart : ∀ b, δ b zeroI = 0 := by
      intro b
      cases b; exact hstart j₀; exact hstart j₁
    have hδmeet : ∀ b c, b ≠ c → range (δ b) ∩ range (δ c) = {0} := by
      intro b c hbc
      cases b <;> cases c
      · exact False.elim (hbc rfl)
      · exact hmeet j₀ j₁ hjne
      · exact hmeet j₁ j₀ hjne.symm
      · exact False.elim (hbc rfl)
    obtain ⟨seed,hop⟩ := pointed_one_or_two_arm_relative_seed δ 0 hδ hδstart hδmeet
      (Or.inr (by simp)) V hV hoV
    have hnormEndpoint : ∀ j, 0 < ‖seed.H (γ j oneI)‖ := by
      intro j
      apply norm_pos_iff.mpr
      intro he
      have hh : γ j oneI = 0 := seed.H.injective (he.trans seed.fixes_center.symm)
      have hi : oneI = zeroI := (hγ j).injective (hh.trans (hstart j).symm)
      have hf : (1:ℝ) = 0 := congrArg Subtype.val hi
      norm_num at hf
    have small (s : Finset J) : ∃ b : ℝ, 0 < b ∧ ∀ j ∈ s, b < ‖seed.H (γ j oneI)‖ := by
      induction s using Finset.induction_on with
      | empty => exact ⟨1,by norm_num,by simp⟩
      | @insert j s hj ih =>
        obtain ⟨b,hb,hbs⟩ := ih
        refine ⟨min b (‖seed.H (γ j oneI)‖/2),lt_min hb (half_pos (hnormEndpoint j)),?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with he|hi
        · subst i
          exact (min_le_right _ _).trans_lt (by linarith [hnormEndpoint j])
        · exact (min_le_left _ _).trans_lt (hbs i hi)
    obtain ⟨b,hb,hball⟩ := small Finset.univ
    let v₀ := seed.vector false
    let v₁ := seed.vector true
    have hv₀ : 0 < ‖v₀‖ := norm_pos_iff.mpr (seed.vector_nonzero false)
    have hv₁ : 0 < ‖v₁‖ := norm_pos_iff.mpr (seed.vector_nonzero true)
    let r : ℝ := min b (min ‖v₀‖ (min ‖v₁‖ seed.supportRadius)) / 2
    have hr : 0 < r := half_pos (lt_min hb (lt_min hv₀ (lt_min hv₁ seed.support_pos)))
    have hrb : r < b := by
      have hh := min_le_left b (min ‖v₀‖ (min ‖v₁‖ seed.supportRadius))
      dsimp [r]
      linarith
    have hr₀ : r < ‖v₀‖ := by
      have hh := (min_le_right b (min ‖v₀‖ (min ‖v₁‖ seed.supportRadius))).trans
        (min_le_left ‖v₀‖ (min ‖v₁‖ seed.supportRadius))
      dsimp [r]
      linarith
    have hr₁ : r < ‖v₁‖ := by
      have hh := (min_le_right b (min ‖v₀‖ (min ‖v₁‖ seed.supportRadius))).trans
        ((min_le_right ‖v₀‖ (min ‖v₁‖ seed.supportRadius)).trans (min_le_left ‖v₁‖ seed.supportRadius))
      dsimp [r]
      linarith
    have hrR : r < seed.supportRadius := by
      have hh := (min_le_right b (min ‖v₀‖ (min ‖v₁‖ seed.supportRadius))).trans
        ((min_le_right ‖v₀‖ (min ‖v₁‖ seed.supportRadius)).trans (min_le_right ‖v₁‖ seed.supportRadius))
      dsimp [r]
      linarith [seed.support_pos]
    obtain ⟨d₀,hd₀,hd₀1,hd₀c,him₀⟩ := shorten (γ j₀) (hγ j₀) (hstart j₀)
      seed.H seed.fixes_center (seed.cut false) (seed.cut_pos false) (seed.cut_lt_one false)
      v₀ (seed.vector_nonzero false) (by simpa only [δ,armPrefix,prefixSet,v₀,Bool.false_eq_true,ite_false,zero_add] using seed.prefix_image false) r hr hr₀
    obtain ⟨d₁,hd₁,hd₁1,hd₁c,him₁⟩ := shorten (γ j₁) (hγ j₁) (hstart j₁)
      seed.H seed.fixes_center (seed.cut true) (seed.cut_pos true) (seed.cut_lt_one true)
      v₁ (seed.vector_nonzero true) (by simpa only [δ,armPrefix,prefixSet,v₁,ite_true,zero_add] using seed.prefix_image true) r hr hr₁
    let q₀ := (r/‖v₀‖) • v₀
    let q₁ := (r/‖v₁‖) • v₁
    have hq₀ : ‖q₀‖ = r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hv₀)]
      exact div_mul_cancel₀ r (ne_of_gt hv₀)
    have hq₁ : ‖q₁‖ = r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hr hv₁)]
      exact div_mul_cancel₀ r (ne_of_gt hv₁)
    obtain ⟨a,ha,hopposite⟩ := hop false true (by decide)
    have hvrel : v₁ = -a • v₀ := hopposite
    have hqrel : q₁ = -q₀ := by
      dsimp [q₁,q₀]
      rw [hvrel,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos ha,smul_smul]
      have hs : r / (a * ‖v₀‖) * -a = -(r/‖v₀‖) := by
        field_simp [ne_of_gt ha,ne_of_gt hv₀] <;> ring
      rw [hs,neg_smul]
    let S₀ : Finset J := {j₀,j₁}
    let c₀ : J → I := fun j => if j = j₀ then d₀ else d₁
    let w₀ : J → Plane := fun j => if j = j₀ then q₀ else q₁
    have hprefix : ∀ j ∈ S₀, 0 < (c₀ j).val ∧ (c₀ j).val < 1 ∧ ‖w₀ j‖ = r ∧
        seed.H '' (γ j '' Icc 0 (c₀ j)) = segment ℝ (0:Plane) (w₀ j) := by
      intro j hj
      have hj' : j = j₀ ∨ j = j₁ := by simpa [S₀] using hj
      rcases hj' with rfl|rfl
      · simpa [c₀,w₀,q₀] using And.intro hd₀ (And.intro hd₀1 (And.intro hq₀ him₀))
      · simpa [c₀,w₀,q₁,hjne.symm] using And.intro hd₁ (And.intro hd₁1 (And.intro hq₁ him₁))
    have hend : ∀ j, seed.H (γ j oneI) ∉ closedBall (0:Plane) r := by
      intro j hj
      have hn : ‖seed.H (γ j oneI)‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hj
      exact (not_le_of_gt (hrb.trans (hball j (Finset.mem_univ _)))) hn
    have hfanEq : (⋃ j, ⋃ (_ : j ∈ S₀), segment ℝ (0:Plane) (w₀ j)) =
        segment ℝ (0:Plane) q₀ ∪ segment ℝ (0:Plane) (-q₀) := by
      ext x
      constructor
      · intro hx
        obtain ⟨j,hx⟩ := mem_iUnion.mp hx
        obtain ⟨hj,hx⟩ := mem_iUnion.mp hx
        have hj' : j = j₀ ∨ j = j₁ := by simpa [S₀] using hj
        rcases hj' with rfl|rfl
        · exact Or.inl (by simpa [w₀] using hx)
        · exact Or.inr (by simpa [w₀,hjne.symm,hqrel] using hx)
      · rintro (hx|hx)
        · exact mem_iUnion.mpr ⟨j₀,mem_iUnion.mpr ⟨by simp [S₀],by simpa [w₀] using hx⟩⟩
        · exact mem_iUnion.mpr ⟨j₁,mem_iUnion.mpr ⟨by simp [S₀],by simpa [w₀,hjne.symm,hqrel] using hx⟩⟩
    obtain ⟨Q,hclosed,hconvex,hzero,hinside,hcover,hdisj,hfront,hne,hcenter,hfan,hsupport⟩ := halfCells q₀ r hr hq₀
    obtain ⟨H,c,w,hH,hfix,hprefixall⟩ := complete γ hγ hstart hmeet r seed.supportRadius hr hrR.le
      S₀ seed.H c₀ w₀ seed.fixes_center seed.fixes_exterior hend hprefix
      ⟨Bool,Q,hclosed,hconvex,hzero,hinside,hcover,hdisj,
        by simpa only [hfanEq] using hfront,hne,hcenter,
        by simpa only [hfanEq] using hfan,by simpa only [hfanEq] using hsupport⟩
    have hwne : ∀ j, w j ≠ 0 := by
      intro j he
      have hh := (hprefixall j).2.2.1
      rw [he,norm_zero] at hh
      linarith
    obtain ⟨ρ,hρ,hρR,hρw,htails⟩ := tailCore γ hγ 0 (by simpa [zeroI] using hstart)
      H hH c (fun j => (hprefixall j).1) w hwne seed.supportRadius seed.support_pos
    let result : RadializedStar γ 0 V := {
      H := H
      supportRadius := seed.supportRadius
      support_pos := seed.support_pos
      support_subset := seed.support_subset
      fixes_center := hH
      fixes_exterior := hfix
      cut := c
      cut_pos := fun j => (hprefixall j).1
      cut_lt_one := fun j => (hprefixall j).2.1
      vector := w
      vector_nonzero := hwne
      prefix_image := by
        intro j
        simpa only [armPrefix,prefixSet,zero_add] using (hprefixall j).2.2.2
      distinct_rays := by
        intro i j hij
        apply Set.disjoint_left.mpr
        intro x hxi hxj
        have hiim := (hprefixall i).2.2.2
        have hjim := (hprefixall j).2.2.2
        simp only [zero_add] at hxi hxj
        rw [← hiim] at hxi
        rw [← hjim] at hxj
        obtain ⟨⟨_,⟨s,hs,rfl⟩,hxs⟩,hxne⟩ := hxi
        obtain ⟨⟨_,⟨t,ht,rfl⟩,hxt⟩,_⟩ := hxj
        have he : γ i s = γ j t := H.injective (hxs.trans hxt.symm)
        have hz : γ i s = 0 := by
          have hh : γ i s ∈ range (γ i) ∩ range (γ j) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
          rw [hmeet i j hij] at hh
          exact hh
        exact hxne (by simpa only [mem_singleton_iff,← hxs,hz] using hH)
      coreRadius := ρ
      core_pos := hρ
      core_lt_support := hρR
      core_lt_length := hρw
      excludes_tails := by
        intro j
        have htailSet : {t : I | (c j).val ≤ t.val} = {t : I | c j ≤ t} := by ext t; rfl
        simpa only [tail,htailSet] using htails j }
    exact ⟨result⟩
  have tailCore {J : Type} [Fintype J] (γ : J → I → EuclideanSpace ℝ (Fin 2))
      (hγ : ∀ j, Topology.IsClosedEmbedding (γ j)) (o : EuclideanSpace ℝ (Fin 2))
      (hstart : ∀ j, γ j 0 = o) (F : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2))
      (hFo : F o = o) (cut : J → I) (hcut : ∀ j, 0 < cut j)
      (v : J → EuclideanSpace ℝ (Fin 2)) (hv : ∀ j, v j ≠ 0)
      (R : ℝ) (hR : 0 < R) :
      ∃ ρ : ℝ, 0 < ρ ∧ ρ < R ∧ (∀ j, ρ < ‖v j‖) ∧
        ∀ j, Disjoint (F '' (γ j '' {t : I | cut j ≤ t})) (closedBall o ρ) := by
    classical
    let K : J → Set (EuclideanSpace ℝ (Fin 2)) := fun j =>
      F '' (γ j '' {t : I | cut j ≤ t})
    have hK : ∀ j, IsCompact (K j) := by
      intro j
      have hc : IsCompact {t : I | cut j ≤ t} := (isClosed_le continuous_const continuous_id).isCompact
      exact (hc.image (hγ j).continuous).image F.continuous
    have hoK : o ∉ ⋃ j, K j := by
      intro hm
      obtain ⟨j,_,⟨t,ht,rfl⟩,he⟩ := mem_iUnion.mp hm
      have hh : γ j t = o := F.injective (he.trans hFo.symm)
      have ht0 : t = 0 := (hγ j).injective (hh.trans (hstart j).symm)
      have hcle : cut j ≤ 0 := ht0 ▸ ht
      exact not_le_of_gt (hcut j) hcle
    have hU : IsOpen (⋃ j, K j)ᶜ := (isCompact_iUnion hK).isClosed.isOpen_compl
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hoK)
    have small (s : Finset J) : ∃ b : ℝ, 0 < b ∧ ∀ j ∈ s, b < ‖v j‖ := by
      induction s using Finset.induction_on with
      | empty => exact ⟨1,by norm_num,by simp⟩
      | @insert j s hj ih =>
        obtain ⟨b,hb,hbs⟩ := ih
        refine ⟨min b (‖v j‖/2),lt_min hb (half_pos (norm_pos_iff.mpr (hv j))),?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with hkj | hk
        · subst k
          exact (min_le_right _ _).trans_lt (half_lt_self (norm_pos_iff.mpr (hv j)))
        · exact (min_le_left _ _).trans_lt (hbs k hk)
    obtain ⟨b,hb,hbs⟩ := small Finset.univ
    let ρ : ℝ := min R (min ε b) / 2
    have hρ : 0 < ρ := half_pos (lt_min hR (lt_min hε hb))
    have hρR : ρ < R := (half_lt_self (lt_min hR (lt_min hε hb))).trans_le (min_le_left _ _)
    have hρε : ρ < ε := (half_lt_self (lt_min hR (lt_min hε hb))).trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
    have hρb : ρ < b := (half_lt_self (lt_min hR (lt_min hε hb))).trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨ρ,hρ,hρR,fun j => hρb.trans (hbs j (Finset.mem_univ j)),?_⟩
    intro j
    apply Set.disjoint_left.mpr
    intro x hxK hxB
    have hxε : x ∈ ball o ε := closedBall_subset_ball hρε hxB
    exact (hball hxε) (mem_iUnion.mpr ⟨j,hxK⟩)
  by_cases hsmall : Fintype.card J = 1 ∨ Fintype.card J = 2
  · obtain ⟨R,_⟩ := pointed_one_or_two_arm_relative_seed γ o hγ hstart hmeet hsmall V hV hoV
    exact ⟨R⟩
  by_cases hempty : Fintype.card J = 0
  · haveI : IsEmpty J := Fintype.card_eq_zero_iff.mp hempty
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hoV)
    have hsub : closedBall o (ε/2) ⊆ V := by
      intro x hx
      apply hball
      have hx' : dist x o ≤ ε/2 := mem_closedBall.mp hx
      exact mem_ball.mpr (by linarith)
    exact ⟨{
      H := Homeomorph.refl Plane
      supportRadius := ε/2
      support_pos := half_pos hε
      support_subset := hsub
      fixes_center := rfl
      fixes_exterior := fun _ _ => rfl
      cut := fun j => isEmptyElim j
      cut_pos := fun j => isEmptyElim j
      cut_lt_one := fun j => isEmptyElim j
      vector := fun j => isEmptyElim j
      vector_nonzero := fun j => isEmptyElim j
      prefix_image := fun j => isEmptyElim j
      distinct_rays := fun i => isEmptyElim i
      coreRadius := ε/4
      core_pos := by linarith
      core_lt_support := by linarith
      core_lt_length := fun j => isEmptyElim j
      excludes_tails := fun j => isEmptyElim j }⟩
  have hcard : 1 < Fintype.card J := by omega
  let E : Plane ≃ₜ Plane := Homeomorph.addLeft (-o)
  have hEo : E o = 0 := by simp [E]
  have hEinv : ∀ x, E.symm x = o + x := by
    intro x
    apply E.injective
    rw [E.apply_symm_apply]
    simp [E,add_assoc]
  have hEinv0 : E.symm 0 = o := by rw [hEinv,add_zero]
  have hdist : ∀ x, dist (E x) 0 = dist x o := by
    intro x
    simp [E,dist_eq_norm,sub_eq_add_neg,add_comm]
  let δ : J → I → Plane := fun j => E ∘ γ j
  have hδ : ∀ j, Topology.IsClosedEmbedding (δ j) := fun j =>
    E.isClosedEmbedding.comp (hγ j)
  have hδstart : ∀ j, δ j zeroI = 0 := by
    intro j
    change E (γ j zeroI) = 0
    rw [hstart j,hEo]
  have hδmeet : ∀ i j, i ≠ j → range (δ i) ∩ range (δ j) = {0} := by
    intro i j hij
    change range (E ∘ γ i) ∩ range (E ∘ γ j) = {0}
    rw [range_comp,range_comp,← image_inter E.injective,hmeet i j hij,image_singleton,hEo]
  let U := E '' V
  have hU : IsOpen U := E.isOpenMap V hV
  have h0U : (0:Plane) ∈ U := ⟨o,hoV,hEo⟩
  obtain ⟨R⟩ := zeroCase δ hδ hδstart hδmeet hcard U hU h0U
  let H : Plane ≃ₜ Plane := (E.trans R.H).trans E.symm
  have hHo : H o = o := by
    change E.symm (R.H (E o)) = o
    rw [hEo,R.fixes_center,hEinv0]
  have hfix : ∀ x, x ∉ ball o R.supportRadius → H x = x := by
    intro x hx
    have hxE : E x ∉ ball (0:Plane) R.supportRadius := by
      simpa only [mem_ball,hdist] using hx
    change E.symm (R.H (E x)) = x
    rw [R.fixes_exterior _ hxE,E.symm_apply_apply]
  have hsupport : closedBall o R.supportRadius ⊆ V := by
    intro x hx
    have hxE : E x ∈ closedBall (0:Plane) R.supportRadius := by
      simpa only [mem_closedBall,hdist] using hx
    obtain ⟨y,hy,he⟩ := R.support_subset hxE
    exact E.injective he ▸ hy
  have hprefix : ∀ j, H '' armPrefix γ j (R.cut j) = segment ℝ o (o + R.vector j) := by
    intro j
    change (E.symm ∘ R.H ∘ E) '' armPrefix γ j (R.cut j) = _
    rw [image_comp,image_comp]
    have hδimage : E '' armPrefix γ j (R.cut j) = armPrefix δ j (R.cut j) := by
      exact (image_comp E (γ j) {t : I | t.val ≤ (R.cut j).val}).symm
    rw [hδimage,R.prefix_image,zero_add]
    have hfun : (E.symm : Plane → Plane) = (fun x => o + x) := funext hEinv
    rw [hfun]
    simpa only [add_zero] using segment_translate_image ℝ o (0:Plane) (R.vector j)
  obtain ⟨ρ,hρ,hρR,hρv,htails⟩ := tailCore γ hγ o (by
      intro j
      have hz : (0:I) = zeroI := by apply Subtype.ext; rfl
      rw [hz,hstart j]) H hHo R.cut (fun j => R.cut_pos j)
    R.vector R.vector_nonzero R.supportRadius R.support_pos
  exact ⟨{
    H := H
    supportRadius := R.supportRadius
    support_pos := R.support_pos
    support_subset := hsupport
    fixes_center := hHo
    fixes_exterior := hfix
    cut := R.cut
    cut_pos := R.cut_pos
    cut_lt_one := R.cut_lt_one
    vector := R.vector
    vector_nonzero := R.vector_nonzero
    prefix_image := hprefix
    distinct_rays := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro x hxi hxj
      rw [← hprefix i] at hxi
      rw [← hprefix j] at hxj
      obtain ⟨⟨_,⟨s,hs,rfl⟩,hxs⟩,hxne⟩ := hxi
      obtain ⟨⟨_,⟨t,ht,rfl⟩,hxt⟩,_⟩ := hxj
      have he : γ i s = γ j t := H.injective (hxs.trans hxt.symm)
      have hz : γ i s = o := by
        have hh : γ i s ∈ range (γ i) ∩ range (γ j) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
        rw [hmeet i j hij] at hh
        exact hh
      exact hxne (by simpa only [mem_singleton_iff,← hxs,hz] using hHo)
    coreRadius := ρ
    core_pos := hρ
    core_lt_support := hρR
    core_lt_length := hρv
    excludes_tails := by
      intro j
      have htailSet : {t : I | (R.cut j).val ≤ t.val} = {t : I | R.cut j ≤ t} := by ext t; rfl
      simpa only [tail,htailSet] using htails j }⟩

end CurveComplex.FiniteStarGeometry
#print axioms CurveComplex.FiniteStarGeometry.finite_actual_star_radialization
