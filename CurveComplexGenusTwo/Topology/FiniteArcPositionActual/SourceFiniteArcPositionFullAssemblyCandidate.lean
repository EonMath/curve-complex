import CurveComplexGenusTwo.Topology.Smoothing.FiniteIntervalCompatibleChartsProof
import CurveComplexGenusTwo.Topology.GeometricPosition.ProperAffineCrosscut
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedIntervalMesh
import Mathlib
import CurveComplexGenusTwo.Topology.Smoothing.PointedPlaneIsotopyProof
import CurveComplexGenusTwo.Topology.ChartLift
import Schoenflies.Concatenate
import Schoenflies.ArcCollars
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Normed.Module.Connected
import CurveComplexGenusTwo.Topology.Smoothing.MarkedIntervalCrosscutChartProof
import CurveComplexGenusTwo.Topology.Orientation.SurfaceLocalization
import Mathlib.Topology.Homotopy.Path
import CurveComplexGenusTwo.Dictionary.Genus
import CurveComplexGenusTwo.Foundations.SourceRealization
import CurveComplexGenusTwo.Topology.Basic

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CurveComplex.ArcFinitePosition Set _root_.Topology Schoenflies unitInterval
open scoped NNReal

-- Exact reviewed and protected source finite-position declaration; proof in progress.
-- The input arcs are actual paths constructed by chart straightening.
theorem source_finite_embedded_arcs_finite_position
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (g : ℕ) (hg : 2 ≤ g) (hS : IsGenus S g)
    (m : ℕ) (a b : Fin m → S)
    (p : (i : Fin m) → Path (a i) (b i))
    (hne : ∀ i, a i ≠ b i) (hp : ∀ i, Function.Injective (p i)) :
    ∃ q : (i : Fin m) → Path (a i) (b i),
      (∀ i, Path.Homotopic (p i) (q i)) ∧
      (∀ i, Function.Injective (q i)) ∧
      ∀ i j, i ≠ j → (Set.range (q i) ∩ Set.range (q j)).Finite := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
  -- Actual local surface-position producer: old paths remain fixed, with
  -- fixed-endpoint homotopy of the new embedded path and finite whole contacts.
  have extend (B : Finset (Fin m))
      (r : (i : Fin m) → Path (a i) (b i))
      (hi : ∀ i, Function.Injective (r i))
      (hf : ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
        (Set.range (r i) ∩ Set.range (r j)).Finite)
      (v : Fin m) (hv : v ∉ B) :
      ∃ d : Path (a v) (b v), Path.Homotopic (r v) d ∧
        Function.Injective d ∧
        ∀ i ∈ B, (Set.range (r i) ∩ Set.range d).Finite := by
    have avoid {a b : S} (p : Path a b) (hp : Function.Injective p)
        (P : Finset S) (hP : ∀ z ∈ P, z ≠ a ∧ z ≠ b) :
        ∃ q : Path a b, Path.Homotopic p q ∧ Function.Injective q ∧
          Disjoint (Set.range q) (P : Set S) := by
      classical
      have avoidance (P : Finset S) (W : Set S) (hW : IsOpen W)
          (hPW : (P : Set S) ⊆ W) (haW : a ∉ W) (hbW : b ∉ W) :
          ∃ H : AmbientIsotopy S,
            (∀ z ∈ P, H.finalMap z ∉ Set.range p) ∧
            ∀ t x, x ∉ W → H.map (t,x) = x := by
        classical
        have point (z : S) (hz : z ∈ Set.range p) (hza : z ≠ a) (hzb : z ≠ b)
            (W : Set S) (hW : IsOpen W) (hzW : z ∈ W) :
            ∃ G : AmbientIsotopy S, G.finalMap z ∉ Set.range p ∧
              ∀ t x, x ∉ W → G.map (t,x) = x := by
          classical
          obtain ⟨τ,rfl⟩ := hz
          have hτ0 : 0 < τ.val := by
            by_contra hh
            have he : τ = 0 := Subtype.ext (le_antisymm (le_of_not_gt hh) τ.property.1)
            exact hza (by rw [he]; exact p.source)
          have hτ1 : τ.val < 1 := by
            by_contra hh
            have he : τ = 1 := Subtype.ext (le_antisymm τ.property.2 (le_of_not_gt hh))
            exact hzb (by rw [he]; exact p.target)
          have chart (τ : I) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1)
              (W : Set S) (hW : IsOpen W) (hpW : p τ ∈ W) :
              ∃ E : OpenPartialHomeomorph S Plane,
                p τ ∈ E.source ∧ E.source ⊆ W ∧
                ∀ x ∈ E.source, x ∈ Set.range p ↔ E x 1 = 0 := by
            classical
            let e := chartAt Plane (p τ)
            have he : p τ ∈ e.source := mem_chart_source Plane (p τ)
            let q : ℝ → S := p ∘ Set.projIcc 0 1 zero_le_one
            have hqc : Continuous q := p.continuous.comp continuous_projIcc
            have hqt : q (τ : ℝ) = p τ := by
              dsimp [q]
              congr 1
              exact Subtype.ext (by simp [Set.projIcc_of_mem, τ.property])
            have hn : q ⁻¹' (W ∩ e.source) ∈ nhds (τ : ℝ) :=
              hqc.continuousAt.preimage_mem_nhds (by
                rw [hqt]
                exact (hW.inter e.open_source).mem_nhds ⟨hpW,he⟩)
            obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hn
            let ε : ℝ := min ρ (min (τ:ℝ) (1-(τ:ℝ))) / 2
            have hε : 0 < ε := by dsimp [ε]; positivity
            have hερ : ε < ρ := by dsimp [ε]; linarith [min_le_left ρ (min (τ:ℝ) (1-(τ:ℝ)))]
            have hετ : ε < (τ:ℝ) := by
              have hh := (min_le_right ρ (min (τ:ℝ) (1-(τ:ℝ)))).trans
                (min_le_left (τ:ℝ) (1-(τ:ℝ)))
              dsimp [ε]; linarith
            have hε1 : ε < 1-(τ:ℝ) := by
              have hh := (min_le_right ρ (min (τ:ℝ) (1-(τ:ℝ)))).trans
                (min_le_right (τ:ℝ) (1-(τ:ℝ)))
              dsimp [ε]; linarith
            let l : ℝ := (τ:ℝ)-ε
            let r : ℝ := (τ:ℝ)+ε
            have hl : 0 < l := by dsimp [l]; linarith
            have hlr : l < r := by dsimp [l,r]; linarith
            have hr : r < 1 := by dsimp [r]; linarith
            have hs : q '' Set.Icc l r ⊆ W ∩ e.source := by
              rintro _ ⟨t,ht,rfl⟩
              apply hball
              rw [Metric.mem_ball, Real.dist_eq, abs_lt]
              dsimp [l,r] at ht
              constructor <;> linarith [ht.1,ht.2]
            obtain ⟨E,hEW,hSquare,hseg,hleft,hright,haxis,hbox⟩ :=
              actual_interval_subarc_crosscut_chart (S:=S) p p.continuous
                (fun t u h => Or.inl (hp h)) l r hl hlr hr e W hW hs
            refine ⟨E,?_,fun x hx => (hEW hx).1,haxis⟩
            apply hseg
            exact ⟨(τ:ℝ),by dsimp [l,r]; constructor <;> linarith,hqt⟩
          have push (U : Set S) (V : Set Plane) (hU : IsOpen U) (e : U ≃ₜ V)
              (p v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < 1)
              (hCV : Metric.closedBall p (2*R) ⊆ V) :
              ∃ G : AmbientIsotopy S,
                (∀ t (x : U), dist (e x).val p ≤ R →
                  ∃ y : U, G.map (t,x.val) = y.val ∧
                    (e y).val = (e x).val + (t:ℝ) • (R • v)) ∧
                (∀ t x, x ∉ U → G.map (t,x) = x) := by
            have push (p v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < 1) :
                ∃ H : AmbientIsotopy Plane,
                  (∀ t x, dist x p ≤ R → H.map (t,x) = x + (t:ℝ) • (R • v)) ∧
                  (∀ t x, 2*R ≤ dist x p → H.map (t,x) = x) := by
              classical
              have hsmall (f : Plane → Plane)
                    (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
                    ∃ H : AmbientIsotopy Plane,
                      (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
                      (∀ t x, f x = 0 → H.map (t, x) = x) := by
                classical
                let F : I × Plane → Plane :=
                  fun p => p.2 + (p.1 : ℝ) • f p.2
                have hF : Continuous F := continuous_snd.add
                  ((continuous_subtype_val.comp continuous_fst).smul
                    (hf.continuous.comp continuous_snd))
                refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
                  fun t x => rfl, ?_⟩
                · intro t
                  have happ : ApproximatesLinearOn (fun x => F (t, x))
                      (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane)
                      Set.univ c := by
                    intro x _ y _
                    have heq : F (t, x) - F (t, y) - (x - y) =
                        (t : ℝ) • (f x - f y) := by dsimp [F]; module
                    change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
                    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
                    calc
                      (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
                        mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
                      _ ≤ c * ‖x - y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
                  let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
                  exact ⟨e, fun x => rfl⟩
                · intro x
                  simp [F]
                · intro t x hx
                  change x + (t : ℝ) • f x = x
                  simp [hx]
            
              let b : Plane → ℝ := fun x => max (min (2*R - dist x p) R) 0
              have hb0 : LipschitzWith 1 (fun x : Plane => 2*R - dist x p) := by
                apply LipschitzWith.of_dist_le_mul
                intro x y
                simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
                  sub_sub_sub_cancel_left, abs_sub_comm] using abs_dist_sub_le x y p
              have hb : LipschitzWith 1 b := (hb0.min_const R).max_const 0
              let f : Plane → Plane := fun x => b x • v
              have hf : LipschitzWith ‖v‖₊ f := by
                apply LipschitzWith.of_dist_le_mul
                intro x y
                change ‖b x • v - b y • v‖ ≤ ‖v‖ * dist x y
                rw [← sub_smul, norm_smul, Real.norm_eq_abs]
                have h := hb.dist_le_mul x y
                simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
                calc
                  |b x - b y| * ‖v‖ ≤ dist x y * ‖v‖ :=
                    mul_le_mul_of_nonneg_right h (norm_nonneg _)
                  _ = ‖v‖ * dist x y := mul_comm _ _
              obtain ⟨H,hH,hfix⟩ := hsmall f ‖v‖₊ hv hf
              refine ⟨H, ?_, ?_⟩
              · intro t x hx
                rw [hH]
                have hb : b x = R := by
                  simp only [b, min_eq_right (by linarith : R ≤ 2*R-dist x p),
                    max_eq_left hR.le]
                simp only [f,hb]
              · intro t x hx
                apply hfix
                have hm : min (2*R-dist x p) R ≤ 0 :=
                  (min_le_left _ _).trans (by linarith)
                simp only [f,b,max_eq_right hm,zero_smul]
            obtain ⟨H,hH,hfix⟩ := push p v R hR hv
            obtain ⟨K,G,hcoord,hGU,hGfix⟩ := position_surface_chart_lift S U V hU e
              (Metric.closedBall p (2*R)) (isCompact_closedBall _ _) hCV H (by
                intro t x hx
                apply hfix
                exact le_of_lt (lt_of_not_ge (by simpa only [Metric.mem_closedBall] using hx)))
            refine ⟨G, ?_, hGfix⟩
            intro t x hx
            refine ⟨K.map (t,x), hGU t x, ?_⟩
            rw [hcoord]
            exact hH t (e x).val hx
          obtain ⟨E,hpE,hEW,haxis⟩ := chart τ hτ0 hτ1 W hW hzW
          obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
            (E.open_target.mem_nhds (E.map_source hpE))
          let R : ℝ := δ/4
          have hR : 0 < R := by dsimp [R]; positivity
          have hCV : Metric.closedBall (E (p τ)) (2*R) ⊆ E.target := by
            apply Set.Subset.trans (Metric.closedBall_subset_ball ?_) hball
            dsimp [R]
            linarith
          let v : Plane := Plane.mk 0 (1/2)
          have hv : ‖v‖ < 1 := by
            norm_num [v, EuclideanSpace.norm_eq, Fin.sum_univ_two, Plane.mk]
          obtain ⟨G,hmove,hfix⟩ := push E.source E.target E.open_source
            E.toHomeomorphSourceTarget (E (p τ)) v R hR hv hCV
          obtain ⟨y,hy,hEy⟩ := hmove (1 : I) ⟨p τ,hpE⟩ (by simp; exact hR.le)
          have hz0 : E (p τ) 1 = 0 := (haxis _ hpE).mp ⟨τ,rfl⟩
          have hEq : E y.val = E (p τ) + R • v := by simpa using hEy
          refine ⟨G,?_,fun t x hx => hfix t x (fun he => hx (hEW he))⟩
          intro hm
          change G.map (1,p τ) ∈ Set.range p at hm
          rw [hy] at hm
          have hy0 : E y.val 1 = 0 := (haxis _ y.property).mp hm
          have hh := congrArg (fun x : Plane => x 1) hEq
          simp [v,Plane.mk,hz0,hy0] at hh
          linarith
        have hid : ∃ H : AmbientIsotopy S, ∀ t x, H.map (t,x) = x := by
          refine ⟨{
            map := ⟨fun z => z.2, continuous_snd⟩
            homeomorphism_at := fun t => ⟨Homeomorph.refl S,fun x => rfl⟩
            at_zero := fun x => rfl },fun t x => rfl⟩
        have hcomp (H G : AmbientIsotopy S) :
            ∃ K : AmbientIsotopy S, ∀ t x, K.map (t,x) = G.map (t,H.map (t,x)) := by
          refine ⟨{
            map := ⟨fun z => G.map (z.1,H.map z),
              G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩
            homeomorphism_at := ?_
            at_zero := ?_ },fun t x => rfl⟩
          · intro t
            obtain ⟨e,he⟩ := H.homeomorphism_at t
            obtain ⟨f,hf⟩ := G.homeomorphism_at t
            exact ⟨e.trans f,fun x => (hf (e x)).trans
              (congrArg (fun y => G.map (t,y)) (he x))⟩
          · intro x
            change G.map (0,H.map (0,x)) = x
            exact (congrArg (fun y => G.map (0,y)) (H.at_zero x)).trans (G.at_zero x)
        have hstay (H : AmbientIsotopy S) (A : Set S)
            (hfix : ∀ t x, x ∉ A → H.map (t,x) = x)
            (z : S) (hz : z ∈ A) : H.finalMap z ∈ A := by
          by_contra hn
          obtain ⟨e,he⟩ := H.homeomorphism_at (1 : I)
          have hh : e (H.finalMap z) = e z := by
            rw [he,he]
            exact hfix 1 _ hn
          exact hn ((e.injective hh).symm ▸ hz)
        induction P using Finset.induction_on with
        | empty =>
          obtain ⟨H,hH⟩ := hid
          exact ⟨H,by simp,fun t x hx => hH t x⟩
        | @insert z P hzP ih =>
          have hPW' : (P : Set S) ⊆ W := fun x hx => hPW (Finset.mem_insert_of_mem hx)
          obtain ⟨H,hH,hHfix⟩ := ih hPW'
          let q := H.finalMap z
          have hzW : z ∈ W := hPW (Finset.mem_insert_self _ _)
          have hqW : q ∈ W := hstay H W hHfix z hzW
          by_cases hqmem : q ∈ Set.range p
          · let old : Set S := H.finalMap '' (P : Set S)
            have holdfinite : old.Finite := P.finite_toSet.image _
            have hqold : q ∉ old := by
              rintro ⟨x,hx,hxq⟩
              obtain ⟨e,he⟩ := H.homeomorphism_at (1 : I)
              have heq : e x = e z := by
                change H.map (1,x) = H.map (1,z) at hxq
                exact (he x).trans (hxq.trans (he z).symm)
              exact hzP ((e.injective heq) ▸ hx)
            let V : Set S := W ∩ oldᶜ
            obtain ⟨G,hG,hGfix⟩ := point q hqmem
              (fun h => haW (h ▸ hqW)) (fun h => hbW (h ▸ hqW))
              V (hW.inter holdfinite.isClosed.isOpen_compl) ⟨hqW,hqold⟩
            obtain ⟨K,hK⟩ := hcomp H G
            refine ⟨K,?_,?_⟩
            · intro x hx
              rw [AmbientIsotopy.finalMap,hK]
              change G.finalMap (H.finalMap x) ∉ Set.range p
              rcases Finset.mem_insert.mp hx with rfl | hxP
              · exact hG
              · have hfixq : G.finalMap (H.finalMap x) = H.finalMap x := by
                  apply hGfix
                  intro hxV
                  exact hxV.2 ⟨x,hxP,rfl⟩
                rw [hfixq]
                exact hH x hxP
            · intro t x hx
              rw [hK,hHfix t x hx]
              apply hGfix
              exact fun h => hx h.1
          · refine ⟨H,?_,hHfix⟩
            intro x hx
            rcases Finset.mem_insert.mp hx with rfl | hxP
            · exact hqmem
            · exact hH x hxP
      have transport (H : AmbientIsotopy S)
          (ha : ∀ t, H.map (t,a) = a) (hb : ∀ t, H.map (t,b) = b) :
          ∃ q : Path a b, Path.Homotopic p q ∧ Function.Injective q ∧
            Set.range q = H.finalMap '' Set.range p := by
        let q : Path a b := {
          toContinuousMap := ⟨fun t => H.finalMap (p t),
            H.map.continuous.comp (continuous_const.prodMk p.continuous)⟩
          source' := by change H.map (1,p 0) = a; rw [p.source,ha]
          target' := by change H.map (1,p 1) = b; rw [p.target,hb] }
        have hhom : Path.Homotopic p q := by
          refine ⟨{
            toHomotopy := {
              toContinuousMap := ⟨fun z => H.map (z.1,p z.2),
                H.map.continuous.comp (continuous_fst.prodMk (p.continuous.comp continuous_snd))⟩
              map_zero_left := fun t => H.at_zero (p t)
              map_one_left := fun t => rfl }
            prop' := ?_ }⟩
          intro t u hu
          rcases hu with rfl | hu
          · change H.map (t,p 0) = p 0
            rw [p.source,ha]
          · rw [Set.mem_singleton_iff] at hu
            subst u
            change H.map (t,p 1) = p 1
            rw [p.target,hb]
        have hi : Function.Injective q := by
          obtain ⟨e,he⟩ := H.homeomorphism_at (1 : I)
          intro t u h
          apply hp
          apply e.injective
          change H.map (1,p t) = H.map (1,p u) at h
          exact (he (p t)).trans (h.trans (he (p u)).symm)
        refine ⟨q,hhom,hi,?_⟩
        apply Set.Subset.antisymm
        · rintro _ ⟨t,rfl⟩
          exact ⟨p t,⟨t,rfl⟩,rfl⟩
        · rintro _ ⟨x,⟨t,rfl⟩,rfl⟩
          exact ⟨t,rfl⟩
      let W : Set S := ({a,b} : Set S)ᶜ
      have hW : IsOpen W := ((Set.finite_singleton b).insert a).isClosed.isOpen_compl
      have hPW : (P : Set S) ⊆ W := by
        intro z hz
        simpa only [W,Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or]
          using hP z hz
      have haW : a ∉ W := by simp [W]
      have hbW : b ∉ W := by simp [W]
      obtain ⟨H,hH,hHfix⟩ := avoidance P W hW hPW haW hbW
      obtain ⟨e,he⟩ := H.homeomorphism_at (1 : I)
      let G : AmbientIsotopy S := {
        map := ⟨fun z => H.map (unitInterval.symm z.1,e.symm z.2),
          H.map.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
            (e.symm.continuous.comp continuous_snd))⟩
        homeomorphism_at := by
          intro t
          obtain ⟨f,hf⟩ := H.homeomorphism_at (unitInterval.symm t)
          exact ⟨e.symm.trans f,fun x => hf (e.symm x)⟩
        at_zero := by
          intro x
          change H.map (unitInterval.symm 0,e.symm x) = x
          rw [unitInterval.symm_zero]
          exact (he (e.symm x)).symm.trans (e.apply_symm_apply x) }
      have hGfix (t : I) (x : S) (hx : x ∉ W) : G.map (t,x) = x := by
        have hefix : e x = x := (he x).trans (hHfix 1 x hx)
        have hs : e.symm x = x := by
          apply e.injective
          exact (e.apply_symm_apply x).trans hefix.symm
        change H.map (unitInterval.symm t,e.symm x) = x
        rw [hs]
        exact hHfix _ x hx
      have hinv (x : S) : H.finalMap (G.finalMap x) = x := by
        change H.finalMap (H.map (unitInterval.symm 1,e.symm x)) = x
        rw [unitInterval.symm_one]
        have hx : H.map (0,e.symm x) = e.symm x := H.at_zero _
        rw [hx]
        exact (he (e.symm x)).symm.trans (e.apply_symm_apply x)
      obtain ⟨q,hq,hi,hrange⟩ := transport G
        (fun t => hGfix t a haW) (fun t => hGfix t b hbW)
      refine ⟨q,hq,hi,?_⟩
      rw [Set.disjoint_left]
      intro x hxq hxP
      rw [hrange] at hxq
      obtain ⟨y,hy,rfl⟩ := hxq
      exact hH _ hxP (by rw [hinv]; exact hy)
    let J := {i : Fin m // i ∈ B}
    let Pair := {ij : J × J // ij.1.val ≠ ij.2.val}
    let vertices : Set S :=
      (⋃ i : J, ({a i.val,b i.val} : Set S)) ∪
      ⋃ ij : Pair, Set.range (r ij.val.1.val) ∩ Set.range (r ij.val.2.val)
    have hvertices : vertices.Finite :=
      (Set.finite_iUnion (fun i : J => (Set.finite_singleton (b i.val)).insert (a i.val))).union
        (Set.finite_iUnion (fun ij : Pair => hf ij.val.1.val ij.val.1.property
          ij.val.2.val ij.val.2.property ij.property))
    have hPfinite : (vertices \ ({a v,b v} : Set S)).Finite := hvertices.sdiff
    let P : Finset S := hPfinite.toFinset
    have hP : ∀ z ∈ P, z ≠ a v ∧ z ≠ b v := by
      intro z hz
      have hh : z ∈ vertices \ ({a v,b v} : Set S) :=
        hPfinite.mem_toFinset.mp hz
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using hh.2
    obtain ⟨q,hq,hiq,hqdis⟩ := avoid (r v) (hi v) P hP
    have endpointProducer {S J : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
        [ChartedSpace Plane S] [Fintype J]
        (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
        (hi : ∀ i, Function.Injective (old i))
        (hf : ∀ i j, i ≠ j → (Set.range (old i) ∩ Set.range (old j)).Finite)
        {a b : S} (p : Path a b) (hp : Function.Injective p) (hne : a ≠ b)
        (P : Set S) (hPf : P.Finite) (hpp : Disjoint (Set.range p) P) :
        ∃ d : Path a b, Path.Homotopic p d ∧ Function.Injective d ∧
          Disjoint (Set.range d) P ∧
          ∃ lo hi : I, 0 < lo.val ∧ lo.val < hi.val ∧ hi.val < 1 ∧
            (∀ i, (Set.range (old i) ∩ d '' Set.Icc 0 lo).Finite) ∧
            (∀ i, (Set.range (old i) ∩ d '' Set.Icc hi 1).Finite) := by
      classical
      have prefixProducer {S J : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S]
          [ChartedSpace Plane S] [Fintype J]
          (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
          (hi : ∀ i, Function.Injective (old i))
          (hf : ∀ i j, i ≠ j → (Set.range (old i) ∩ Set.range (old j)).Finite)
          {a b : S} (p : Path a b) (hp : Function.Injective p) (hne : a ≠ b)
          (P : Set S) (hPf : P.Finite) (hpp : Disjoint (Set.range p) P) :
          ∃ d : Path a b, Path.Homotopic p d ∧ Function.Injective d ∧
            Disjoint (Set.range d) P ∧
            ∃ lo : I, 0 < lo.val ∧ lo.val < 1 ∧
              (∀ i, (Set.range (old i) ∩ d '' Set.Icc 0 lo).Finite) ∧
              ∀ β : I, β.val < 1 → ∃ η : I, 0 < η.val ∧ η.val < 1 ∧
                d '' Set.Icc η 1 ⊆ p '' Set.Icc β 1 := by
        classical
        have coreProducer {S J : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [Fintype J]
            (a b : J → S) (p : (i : J) → Path (a i) (b i)) (hp : ∀ i, Function.Injective (p i))
            (hf : ∀ i j, i ≠ j → (Set.range (p i) ∩ Set.range (p j)).Finite)
            (x : S) (e : OpenPartialHomeomorph S Plane) (hxS : x ∈ e.source) :
            let Incident := {i : J // x ∈ Set.range (p i)}
            letI : Fintype Incident := Fintype.ofFinite Incident
            let ai : Incident → S := fun i => a i.val
            let bi : Incident → S := fun i => b i.val
            let pi : (i : Incident) → Path (ai i) (bi i) := fun i => p i.val
            ∃ τ : Incident → I, (∀ i, pi i (τ i) = x) ∧
            let Branch := {k : Incident × Bool // if k.2 then (τ k.1).val < 1 else 0 < (τ k.1).val}
            let endI : Branch → I := fun k => if k.val.2 then 1 else 0
            ∃ arms : (k : Branch) → Path x (pi k.val.1 (endI k)),
              (∀ k, Set.range (arms k) = Set.range ((pi k.val.1).subpath (τ k.val.1) (endI k))) ∧
              (∀ i t, pi i t ≠ x → ∃ k : Branch, k.val.1 = i ∧ pi i t ∈ Set.range (arms k)) ∧
              ∃ (cut : Branch → I) (U : Set S),
                (∀ k, 0 < (cut k).val ∧ (cut k).val < 1) ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ e.source ∧
                (∀ i : J, x ∉ Set.range (p i) → Disjoint U (Set.range (p i))) ∧
                (∀ k, Disjoint U ((arms k) '' Set.Icc (cut k) 1)) ∧
                ∃ R : FiniteStarGeometry.RadializedStar
                  (fun k t => e (((arms k).subpath 0 (cut k)) t)) (e x) (e '' U),
                ∃ G : AmbientIsotopy S,
                  (∀ t, G.map (t,x) = x) ∧ (∀ t z, z ∉ U → G.map (t,z) = z) ∧
                  (∀ z ∈ e.source, G.finalMap z ∈ e.source ∧ e (G.finalMap z) = R.H (e z)) ∧
                  ∀ i t, G.finalMap (p i t) ∈ e.source →
                    e (G.finalMap (p i t)) ∈ Metric.closedBall (e x) R.coreRadius →
                    e (G.finalMap (p i t)) = e x ∨
                      ∃ k, e (G.finalMap (p i t)) ∈ segment ℝ (e x) (e x + R.vector k) := by
          classical
          have vertexProducer {S J : Type} [TopologicalSpace S] [T2Space S] [Fintype J]
              (a b : J → S) (p : (i : J) → Path (a i) (b i))
              (hf : ∀ i j, i ≠ j → (Set.range (p i) ∩ Set.range (p j)).Finite)
              (x : S) :
              ∃ W : Set S, IsOpen W ∧ x ∈ W ∧
                (∀ i j, i ≠ j → ∀ y ∈ W, y ∈ Set.range (p i) →
                  y ∈ Set.range (p j) → y = x) ∧
                (∀ i, x ∉ Set.range (p i) → Disjoint W (Set.range (p i))) ∧
                (∀ i, a i ∈ W → a i = x) ∧ (∀ i, b i ∈ W → b i = x) := by
            classical
            let Pair := {ij : J × J // ij.1 ≠ ij.2}
            let contacts : Set S := ⋃ ij : Pair, Set.range (p ij.val.1) ∩ Set.range (p ij.val.2)
            have hc : contacts.Finite := Set.finite_iUnion (fun ij => hf _ _ ij.property)
            let vertices := contacts ∪ (Set.range a ∪ Set.range b)
            have hv : vertices.Finite := hc.union ((Set.finite_range a).union (Set.finite_range b))
            let bad := vertices \ {x}
            have hbad : bad.Finite := hv.sdiff
            let Absent := {i : J // x ∉ Set.range (p i)}
            let absent : Set S := ⋃ i : Absent, Set.range (p i.val)
            have haC : IsClosed absent := isClosed_iUnion_of_finite (fun i =>
              (isCompact_range (p i.val).continuous).isClosed)
            let W := (bad ∪ absent)ᶜ
            have hxW : x ∈ W := by
              intro hh
              rcases hh with hh | hh
              · exact hh.2 (Set.mem_singleton x)
              · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
                exact i.property hi
            have outside (y : S) (hy : y ∈ W) (hv : y ∈ vertices) : y = x := by
              by_contra hn
              exact hy (Or.inl ⟨hv,by simpa using hn⟩)
            refine ⟨W,(hbad.isClosed.union haC).isOpen_compl,hxW,?_,?_,?_,?_⟩
            · intro i j hij y hy hi hj
              apply outside y hy
              exact Or.inl (Set.mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hi,hj⟩)
            · intro i hi
              apply Set.disjoint_left.mpr
              intro y hy hpy
              exact hy (Or.inr (Set.mem_iUnion.mpr ⟨⟨i,hi⟩,hpy⟩))
            · intro i hi
              exact outside _ hi (Or.inr (Or.inl ⟨i,rfl⟩))
            · intro i hi
              exact outside _ hi (Or.inr (Or.inr ⟨i,rfl⟩))
          have starProducer {S J : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [Fintype J]
              (a b : J → S) (p : (i : J) → Path (a i) (b i)) (hp : ∀ i, Function.Injective (p i))
              (x : S) (τ : J → I) (hτ : ∀ i, p i (τ i) = x)
              (e : OpenPartialHomeomorph S Plane)
              (W : Set S) (hW : IsOpen W) (hxW : x ∈ W) (hWS : W ⊆ e.source)
              (hmeet : ∀ i j, i ≠ j → ∀ y ∈ W, y ∈ Set.range (p i) → y ∈ Set.range (p j) → y = x)
              (haW : ∀ i, a i ∈ W → a i = x) (hbW : ∀ i, b i ∈ W → b i = x) :
              let Branch := {k : J × Bool // if k.2 then (τ k.1).val < 1 else 0 < (τ k.1).val}
              let endI : Branch → I := fun k => if k.val.2 then 1 else 0
              ∃ arms : (k : Branch) → Path x (p k.val.1 (endI k)),
                (∀ k, Set.range (arms k) = Set.range ((p k.val.1).subpath (τ k.val.1) (endI k))) ∧
                (∀ i t, p i t ≠ x → ∃ k : Branch, k.val.1 = i ∧ p i t ∈ Set.range (arms k)) ∧
                ∃ (cut : Branch → I) (U : Set S),
                  (∀ k, 0 < (cut k).val ∧ (cut k).val < 1) ∧ IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
                  (∀ k, Disjoint U ((arms k) '' Set.Icc (cut k) 1)) ∧
                  ∃ R : FiniteStarGeometry.RadializedStar
                    (fun k t => e (((arms k).subpath 0 (cut k)) t)) (e x) (e '' U),
                  ∃ G : AmbientIsotopy S,
                    (∀ t, G.map (t,x) = x) ∧ (∀ t z, z ∉ U → G.map (t,z) = z) ∧
                    ∀ z ∈ e.source, G.finalMap z ∈ e.source ∧ e (G.finalMap z) = R.H (e z) := by
            classical
            have branchProducer {S J : Type} [TopologicalSpace S] [T2Space S] [Fintype J]
                (a b : J → S) (p : (i : J) → Path (a i) (b i))
                (hp : ∀ i, Function.Injective (p i))
                (x : S) (τ : J → I) (hτ : ∀ i, p i (τ i) = x)
                (W : Set S)
                (hmeet : ∀ i j, i ≠ j → ∀ y ∈ W, y ∈ Set.range (p i) →
                  y ∈ Set.range (p j) → y = x) :
                let Branch := {k : J × Bool // if k.2 then (τ k.1).val < 1 else 0 < (τ k.1).val}
                let endI : Branch → I := fun k => if k.val.2 then 1 else 0
                ∃ arms : (k : Branch) → Path x (p k.val.1 (endI k)),
                  (∀ k, Set.range (arms k) = Set.range ((p k.val.1).subpath (τ k.val.1) (endI k))) ∧
                  (∀ k, Function.Injective (arms k)) ∧
                  (∀ k l, k ≠ l → ∀ y ∈ W, y ∈ Set.range (arms k) →
                    y ∈ Set.range (arms l) → y = x) ∧
                  ∀ i t, p i t ≠ x → ∃ k : Branch, k.val.1 = i ∧ p i t ∈ Set.range (arms k) := by
              classical
              have splitArc {S : Type} [TopologicalSpace S] {a b : S}
                  (p : Path a b) (hp : Function.Injective p) (τ : I) :
                  (0 < τ.val → Function.Injective (p.subpath τ 0)) ∧
                  (τ.val < 1 → Function.Injective (p.subpath τ 1)) ∧
                  Set.range (p.subpath τ 0) ∩ Set.range (p.subpath τ 1) = {p τ} ∧
                  Set.range (p.subpath τ 0) ∪ Set.range (p.subpath τ 1) = Set.range p := by
                have subinj (u v : I) (hne : u ≠ v) : Function.Injective (p.subpath u v) := by
                  intro s t he
                  have hh := congrArg Subtype.val (hp he)
                  simp only [Icc.coe_convexComb] at hh
                  have hd : v.val-u.val ≠ 0 := by
                    intro he
                    apply hne
                    exact Subtype.ext (by linarith)
                  have hmul : (s.val-t.val)*(v.val-u.val) = 0 := by nlinarith [hh]
                  have hst := (mul_eq_zero.mp hmul).resolve_right hd
                  apply Subtype.ext
                  linarith
                have hleft : Set.range (p.subpath τ 0) = p '' Set.Icc 0 τ :=
                  Path.range_subpath_of_ge p τ 0 τ.property.1
                have hright : Set.range (p.subpath τ 1) = p '' Set.Icc τ 1 :=
                  Path.range_subpath_of_le p τ 1 τ.property.2
                refine ⟨?_,?_,?_,?_⟩
                · intro hτ
                  apply subinj
                  intro hh
                  have hz := congrArg Subtype.val hh
                  exact hτ.ne' hz
                · intro hτ
                  apply subinj
                  intro hh
                  have hz := congrArg Subtype.val hh
                  exact hτ.ne hz
                · rw [hleft,hright]
                  apply Set.Subset.antisymm
                  · rintro y ⟨⟨s,hs,he⟩,⟨t,ht,hty⟩⟩
                    have hst : s = t := hp (he.trans hty.symm)
                    have hsτ : s = τ := le_antisymm hs.2 (hst ▸ ht.1)
                    exact Set.mem_singleton_iff.mpr (he.symm.trans (congrArg p hsτ))
                  · rintro y (rfl : y = p τ)
                    constructor
                    · exact ⟨τ,⟨τ.property.1,le_rfl⟩,rfl⟩
                    · exact ⟨τ,⟨le_rfl,τ.property.2⟩,rfl⟩
                · rw [hleft,hright]
                  apply Set.Subset.antisymm
                  · rintro y (⟨t,ht,he⟩ | ⟨t,ht,he⟩) <;> exact ⟨t,he⟩
                  · rintro y ⟨t,rfl⟩
                    by_cases ht : t ≤ τ
                    · exact Or.inl ⟨t,⟨t.property.1,ht⟩,rfl⟩
                    · exact Or.inr ⟨t,⟨(not_le.mp ht).le,t.property.2⟩,rfl⟩
              intro Branch endI
              let arms (k : Branch) : Path x (p k.val.1 (endI k)) :=
                ((p k.val.1).subpath (τ k.val.1) (endI k)).cast (hτ k.val.1).symm rfl
              have hrange (k : Branch) : Set.range (arms k) =
                  Set.range ((p k.val.1).subpath (τ k.val.1) (endI k)) := rfl
              have hi (k : Branch) : Function.Injective (arms k) := by
                obtain ⟨hl,hr,_,_⟩ := splitArc (p k.val.1) (hp k.val.1) (τ k.val.1)
                by_cases hb : k.val.2 = true
                · have hh : (τ k.val.1).val < 1 := by simpa [hb] using k.property
                  change Function.Injective ((p k.val.1).subpath (τ k.val.1) (if k.val.2 then 1 else 0))
                  rw [if_pos hb]
                  exact hr hh
                · have hh : k.val.2 = false := Bool.eq_false_of_not_eq_true hb
                  have hpos : 0 < (τ k.val.1).val := by simpa [hh] using k.property
                  change Function.Injective ((p k.val.1).subpath (τ k.val.1) (if k.val.2 then 1 else 0))
                  rw [hh]
                  exact hl hpos
              have hsub (k : Branch) : Set.range (arms k) ⊆ Set.range (p k.val.1) := by
                rw [hrange,Path.range_subpath]
                rintro y ⟨t,ht,rfl⟩
                exact ⟨t,rfl⟩
              refine ⟨arms,hrange,hi,?_,?_⟩
              · intro k l hkl y hy hk hl
                by_cases hidx : k.val.1 = l.val.1
                · have hside : k.val.2 ≠ l.val.2 := by
                    intro hh
                    apply hkl
                    exact Subtype.ext (Prod.ext hidx hh)
                  have hsame (v : I) : Set.range ((p l.val.1).subpath (τ l.val.1) v) =
                      Set.range ((p k.val.1).subpath (τ k.val.1) v) := by
                    apply congrArg Set.range
                    funext t
                    change p l.val.1 (Icc.convexComb (τ l.val.1) v t) =
                      p k.val.1 (Icc.convexComb (τ k.val.1) v t)
                    simp only [hidx]
                    exact congrFun (congrArg (fun i : J => fun t : I => p i t) hidx.symm) _
                  have hp0 := (splitArc (p k.val.1) (hp k.val.1) (τ k.val.1)).2.2.1
                  have hmember : y ∈ Set.range ((p k.val.1).subpath (τ k.val.1) 0) ∩
                      Set.range ((p k.val.1).subpath (τ k.val.1) 1) := by
                    rw [hrange] at hk hl
                    rw [show endI k = (if k.val.2 then 1 else 0) from rfl] at hk
                    rw [show endI l = (if l.val.2 then 1 else 0) from rfl] at hl
                    cases hb : k.val.2 <;> cases hc : l.val.2
                    · exact False.elim (hside (hb.trans hc.symm))
                    · constructor
                      · simpa [endI,hb] using hk
                      · rw [show (if l.val.2 then (1 : I) else 0) = 1 from by rw [hc]; rfl] at hl
                        rwa [hsame 1] at hl
                    · constructor
                      · rw [show (if l.val.2 then (1 : I) else 0) = 0 from by rw [hc]; rfl] at hl
                        rwa [hsame 0] at hl
                      · simpa [endI,hb] using hk
                    · exact False.elim (hside (hb.trans hc.symm))
                  rw [hp0] at hmember
                  exact (Set.mem_singleton_iff.mp hmember).trans (hτ _)
                · exact hmeet _ _ hidx y hy (hsub k hk) (hsub l hl)
              · intro i t htx
                have htn : t ≠ τ i := by intro he; exact htx (he ▸ hτ i)
                by_cases ht : t < τ i
                · have hpos : 0 < (τ i).val := lt_of_le_of_lt t.property.1 ht
                  let k : Branch := ⟨(i,false),by simpa using hpos⟩
                  refine ⟨k,rfl,?_⟩
                  rw [hrange]
                  change p i t ∈ Set.range ((p i).subpath (τ i) 0)
                  rw [Path.range_subpath_of_ge _ _ _ (τ i).property.1]
                  exact ⟨t,⟨t.property.1,ht.le⟩,rfl⟩
                · have ht' : τ i < t := lt_of_le_of_ne (not_lt.mp ht) (Ne.symm htn)
                  have hlt : (τ i).val < 1 := lt_of_lt_of_le ht' t.property.2
                  let k : Branch := ⟨(i,true),by simpa using hlt⟩
                  refine ⟨k,rfl,?_⟩
                  rw [hrange]
                  change p i t ∈ Set.range ((p i).subpath (τ i) 1)
                  rw [Path.range_subpath_of_le _ _ _ (τ i).property.2]
                  exact ⟨t,⟨ht'.le,t.property.2⟩,rfl⟩
            have radialProducer {S J : Type} [TopologicalSpace S] [T2Space S] [Fintype J]
                (x : S) (endpt : J → S) (p : (j : J) → Path x (endpt j))
                (hp : ∀ j, Function.Injective (p j))
                (e : OpenPartialHomeomorph S Plane)
                (W : Set S) (hW : IsOpen W) (hxW : x ∈ W) (hWS : W ⊆ e.source)
                (hend : ∀ j, endpt j ∉ W)
                (hmeet : ∀ i j, i ≠ j → ∀ y ∈ W,
                  y ∈ Set.range (p i) → y ∈ Set.range (p j) → y = x) :
                ∃ (cut : J → I) (U : Set S),
                  (∀ j, 0 < (cut j).val ∧ (cut j).val < 1) ∧
                  IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
                  (∀ j, Disjoint U ((p j) '' Set.Icc (cut j) 1)) ∧
                  Nonempty (FiniteStarGeometry.RadializedStar
                    (fun j t => e (((p j).subpath 0 (cut j)) t)) (e x) (e '' U)) := by
              have prepare {S J : Type} [TopologicalSpace S] [T2Space S] [Fintype J]
                  (x : S) (endpt : J → S) (p : (j : J) → Path x (endpt j))
                  (hp : ∀ j, Function.Injective (p j))
                  (W : Set S) (hW : IsOpen W) (hxW : x ∈ W)
                  (hend : ∀ j, endpt j ∉ W)
                  (hmeet : ∀ i j, i ≠ j → ∀ y ∈ W,
                    y ∈ Set.range (p i) → y ∈ Set.range (p j) → y = x) :
                  ∃ cut : J → I,
                    (∀ j, 0 < (cut j).val ∧ (cut j).val < 1) ∧
                    (∀ j, Function.Injective ((p j).subpath 0 (cut j))) ∧
                    (∀ j, Set.range ((p j).subpath 0 (cut j)) ⊆ W) ∧
                    (∀ i j, i ≠ j → Set.range ((p i).subpath 0 (cut i)) ∩
                      Set.range ((p j).subpath 0 (cut j)) = {x}) ∧
                    ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ U ⊆ W ∧
                      ∀ j, Disjoint U ((p j) '' Set.Icc (cut j) 1) := by
                classical
                have exits (j : J) := path_first_exit_frontier (p j) W hW hxW (hend j)
                choose c hc0 hcfront hcpre using exits
                have hc0v (j : J) : 0 < (c j).val := by simpa using hc0 j
                let cut (j : J) : I := ⟨(c j).val/2,by constructor <;> linarith [(c j).property.1,(c j).property.2]⟩
                have hcut (j : J) : 0 < (cut j).val ∧ (cut j).val < 1 := by
                  dsimp [cut]
                  constructor <;> linarith [hc0v j,(c j).property.2]
                have hpc (j : J) : Set.range ((p j).subpath 0 (cut j)) ⊆ W := by
                  rintro y ⟨t,rfl⟩
                  apply hcpre j
                  change (Icc.convexComb 0 (cut j) t).val < (c j).val
                  simp only [Icc.coe_convexComb]
                  norm_num
                  dsimp [cut]
                  nlinarith [t.property.1,t.property.2,hc0v j]
                have hpi (j : J) : Function.Injective ((p j).subpath 0 (cut j)) := by
                  intro t u he
                  have hh := congrArg Subtype.val (hp j he)
                  simp only [Icc.coe_convexComb] at hh
                  norm_num at hh
                  apply Subtype.ext
                  rcases hh with hh | hh
                  · exact hh
                  · have hz := congrArg Subtype.val hh
                    exact False.elim ((hcut j).1.ne' hz)
                let tails : Set S := ⋃ j, (p j) '' Set.Icc (cut j) 1
                have htclosed : IsClosed tails := isClosed_iUnion_of_finite (fun j =>
                  (isCompact_Icc.image (p j).continuous).isClosed)
                have hxt : x ∉ tails := by
                  intro hh
                  obtain ⟨j,t,ht,he⟩ := Set.mem_iUnion.mp hh
                  have ht0 : t = 0 := hp j (he.trans (p j).source.symm)
                  have hs := ht.1
                  rw [ht0] at hs
                  exact (not_le_of_gt (hcut j).1) hs
                let U := W ∩ tailsᶜ
                refine ⟨cut,hcut,hpi,hpc,?_,U,hW.inter htclosed.isOpen_compl,⟨hxW,hxt⟩,
                  Set.inter_subset_left,?_⟩
                · intro i j hij
                  apply Set.Subset.antisymm
                  · intro y hy
                    exact Set.mem_singleton_iff.mpr (hmeet i j hij y (hpc i hy.1)
                      (by obtain ⟨t,ht⟩ := hy.1; exact ⟨_,ht⟩)
                      (by obtain ⟨t,ht⟩ := hy.2; exact ⟨_,ht⟩))
                  · rintro y (rfl : y = x)
                    constructor <;> exact ⟨0,by simp⟩
                · intro j
                  apply Set.disjoint_left.mpr
                  intro y hy ht
                  exact hy.2 (Set.mem_iUnion.mpr ⟨j,ht⟩)
              obtain ⟨cut,hcut,hpi,hpc,hpair,U,hU,hxU,hUW,hdisj⟩ :=
                prepare x endpt p hp W hW hxW hend hmeet
              let γ : J → I → Plane := fun j t => e (((p j).subpath 0 (cut j)) t)
              have hγ (j : J) : _root_.Topology.IsClosedEmbedding (γ j) := by
                have hc : Continuous (γ j) := e.continuousOn.comp_continuous
                  ((p j).subpath 0 (cut j)).continuous (fun t => hWS (hpc j ⟨t,rfl⟩))
                apply hc.isClosedEmbedding
                intro t u he
                apply hpi j
                exact e.injOn (hWS (hpc j ⟨t,rfl⟩)) (hWS (hpc j ⟨u,rfl⟩)) he
              have hstart (j : J) : γ j FiniteStarGeometry.zeroI = e x := by simp [γ]
              have hγpair (i j : J) (hij : i ≠ j) :
                  Set.range (γ i) ∩ Set.range (γ j) = {e x} := by
                apply Set.Subset.antisymm
                · rintro y ⟨⟨t,ht⟩,⟨u,hu⟩⟩
                  have he : ((p i).subpath 0 (cut i)) t = ((p j).subpath 0 (cut j)) u :=
                    e.injOn (hWS (hpc i ⟨t,rfl⟩)) (hWS (hpc j ⟨u,rfl⟩)) (ht.trans hu.symm)
                  have hpoint : ((p i).subpath 0 (cut i)) t = x := by
                    have hh : ((p i).subpath 0 (cut i)) t ∈
                        Set.range ((p i).subpath 0 (cut i)) ∩ Set.range ((p j).subpath 0 (cut j)) :=
                      ⟨⟨t,rfl⟩,⟨u,he.symm⟩⟩
                    rw [hpair i j hij] at hh
                    exact Set.mem_singleton_iff.mp hh
                  exact Set.mem_singleton_iff.mpr (ht.symm.trans (congrArg e hpoint))
                · rintro y (rfl : y = e x)
                  constructor <;> exact ⟨0,by simp [γ]⟩
              have hV : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU (hUW.trans hWS)
              have hoV : e x ∈ e '' U := ⟨x,hxU,rfl⟩
              have hR := FiniteStarGeometry.finite_actual_star_radialization γ (e x) hγ hstart hγpair
                (e '' U) hV hoV
              exact ⟨cut,U,hcut,hU,hxU,hUW,hdisj,hR⟩
            have liftProducer {S J : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] [Fintype J]
                (e : OpenPartialHomeomorph S Plane) (x : S) (hxS : x ∈ e.source)
                (U : Set S) (hUS : U ⊆ e.source)
                (γ : J → I → Plane)
                (R : FiniteStarGeometry.RadializedStar γ (e x) (e '' U)) :
                ∃ G : AmbientIsotopy S,
                  (∀ t, G.map (t,x) = x) ∧
                  (∀ t z, z ∉ U → G.map (t,z) = z) ∧
                  ∀ z ∈ e.source, G.finalMap z ∈ e.source ∧
                    e (G.finalMap z) = R.H (e z) := by
              obtain ⟨H,hH,hpoint,hfix⟩ := supported_pointed_plane_isotopy (e x)
                R.supportRadius R.support_pos R.H R.fixes_center R.fixes_exterior
              let C := Metric.closedBall (e x) R.supportRadius
              have hCT : C ⊆ e.target := by
                intro y hy
                obtain ⟨z,hz,rfl⟩ := R.support_subset hy
                exact e.map_source (hUS hz)
              obtain ⟨K,G,hcoord,hGU,hGfix⟩ := position_surface_chart_lift S e.source e.target
                e.open_source e.toHomeomorphSourceTarget C (isCompact_closedBall _ _) hCT H (by
                  intro t y hy
                  apply hfix
                  exact fun hh => hy (Metric.ball_subset_closedBall hh))
              have hmaps (t : I) (z : S) (hz : z ∈ e.source) : G.map (t,z) ∈ e.source := by
                rw [hGU t ⟨z,hz⟩]
                exact (K.map (t,⟨z,hz⟩)).property
              have hco (t : I) (z : S) (hz : z ∈ e.source) :
                  e (G.map (t,z)) = H.map (t,e z) := by
                rw [hGU t ⟨z,hz⟩]
                exact hcoord t ⟨z,hz⟩
              refine ⟨G,?_,?_,?_⟩
              · intro t
                apply e.injOn (hmaps t x hxS) hxS
                exact (hco t x hxS).trans (hpoint t)
              · intro t z hzU
                by_cases hzS : z ∈ e.source
                · have hzC : e z ∉ C := by
                    intro hzC
                    obtain ⟨u,hu,he⟩ := R.support_subset hzC
                    have huz : u = z := e.injOn (hUS hu) hzS he
                    exact hzU (huz ▸ hu)
                  apply e.injOn (hmaps t z hzS) hzS
                  rw [hco t z hzS]
                  exact hfix t (e z) (fun h => hzC (Metric.ball_subset_closedBall h))
                · exact hGfix t z hzS
              · intro z hz
                refine ⟨hmaps 1 z hz,?_⟩
                have hh := hco 1 z hz
                change e (G.finalMap z) = H.finalMap (e z) at hh
                rwa [hH] at hh
            intro Branch endI
            obtain ⟨arms,hrange,hi,hmeet,hcover⟩ := branchProducer a b p hp x τ hτ W hmeet
            let endpt (k : Branch) := p k.val.1 (endI k)
            have hend (k : Branch) : endpt k ∉ W := by
              intro hh
              have hneq : endI k ≠ τ k.val.1 := by
                by_cases hb : k.val.2 = true
                · have hk : (τ k.val.1).val < 1 := by simpa [hb] using k.property
                  intro he
                  have hv := congrArg Subtype.val he
                  change (if k.val.2 then (1 : I) else 0).val = (τ k.val.1).val at hv
                  rw [if_pos hb] at hv
                  exact hk.ne hv.symm
                · have hb' := Bool.eq_false_of_not_eq_true hb
                  have hk : 0 < (τ k.val.1).val := by simpa [hb'] using k.property
                  intro he
                  have hv := congrArg Subtype.val he
                  change (if k.val.2 then (1 : I) else 0).val = (τ k.val.1).val at hv
                  rw [hb'] at hv
                  exact hk.ne (by simpa using hv)
              apply hneq
              apply hp k.val.1
              rw [hτ]
              by_cases hb : k.val.2 = true
              · have he : endpt k = b k.val.1 := by dsimp [endpt,endI]; rw [if_pos hb]; exact (p _).target
                exact he.trans (hbW _ (he ▸ hh))
              · have hb' := Bool.eq_false_of_not_eq_true hb
                have he : endpt k = a k.val.1 := by dsimp [endpt,endI]; rw [hb']; exact (p _).source
                exact he.trans (haW _ (he ▸ hh))
            obtain ⟨cut,U,hcut,hU,hxU,hUW,hdisj,⟨R⟩⟩ :=
              radialProducer x endpt arms hi e W hW hxW hWS hend hmeet
            obtain ⟨G,hGx,hGfix,hGcoord⟩ := liftProducer e x (hWS hxW) U (hUW.trans hWS)
              (fun k t => e (((arms k).subpath 0 (cut k)) t)) R
            exact ⟨arms,hrange,hcover,cut,U,hcut,hU,hxU,hUW,hdisj,R,G,hGx,hGfix,hGcoord⟩
          have wholeCore {S J : Type} [TopologicalSpace S] [Fintype J]
              (e : OpenPartialHomeomorph S Plane) (x : S)
              (U : Set S) (hUS : U ⊆ e.source)
              (endpt : J → S) (arms : (j : J) → Path x (endpt j))
              (cut : J → I) (hcpos : ∀ j, 0 < (cut j).val)
              (hdisj : ∀ j, Disjoint U ((arms j) '' Set.Icc (cut j) 1))
              (R : FiniteStarGeometry.RadializedStar
                (fun j t => e (((arms j).subpath 0 (cut j)) t)) (e x) (e '' U))
              (G : AmbientIsotopy S)
              (hfix : ∀ z, z ∉ U → G.finalMap z = z)
              (hco : ∀ z ∈ e.source, e (G.finalMap z) = R.H (e z)) :
              ∀ j t, G.finalMap (arms j t) ∈ e.source →
                e (G.finalMap (arms j t)) ∈ Metric.closedBall (e x) R.coreRadius →
                e (G.finalMap (arms j t)) ∈ segment ℝ (e x) (e x + R.vector j) := by
            have fullCore {J : Type} [Fintype J] (γ : J → I → Plane) (o : Plane) (V : Set Plane)
                (R : FiniteStarGeometry.RadializedStar γ o V) (j : J) :
                (R.H '' Set.range (γ j)) ∩ Metric.closedBall o R.coreRadius ⊆
                  segment ℝ o (o + R.vector j) := by
              rintro y ⟨⟨z,⟨t,rfl⟩,rfl⟩,hy⟩
              by_cases ht : t.val ≤ (R.cut j).val
              · rw [← R.prefix_image j]
                exact ⟨γ j t,⟨t,ht,rfl⟩,rfl⟩
              · have htail : R.H (γ j t) ∈ R.H '' FiniteStarGeometry.tail γ j (R.cut j) :=
                  ⟨γ j t,⟨t,(not_le.mp ht).le,rfl⟩,rfl⟩
                exact False.elim (Set.disjoint_left.mp (R.excludes_tails j) htail hy)
            intro j t hyS hycore
            have hcoreU : G.finalMap (arms j t) ∈ U := by
              have hsup : e (G.finalMap (arms j t)) ∈ Metric.closedBall (e x) R.supportRadius :=
                (Metric.closedBall_subset_closedBall R.core_lt_support.le) hycore
              obtain ⟨u,hu,he⟩ := R.support_subset hsup
              have huy : u = G.finalMap (arms j t) := e.injOn (hUS hu) hyS he
              exact huy ▸ hu
            have hpreU : arms j t ∈ U := by
              by_contra hn
              exact hn (hfix _ hn ▸ hcoreU)
            have ht : t.val < (cut j).val := by
              by_contra hn
              exact Set.disjoint_left.mp (hdisj j) hpreU ⟨t,⟨not_lt.mp hn,t.property.2⟩,rfl⟩
            let s : I := ⟨t.val/(cut j).val,by
              constructor
              · exact div_nonneg t.property.1 (hcpos j).le
              · exact (div_le_one (hcpos j)).mpr ht.le⟩
            have hparam : Icc.convexComb 0 (cut j) s = t := by
              apply Subtype.ext
              simp only [Icc.coe_convexComb]
              change (1-s.val)*(0:ℝ)+s.val*(cut j).val = t.val
              dsimp [s]
              field_simp [(hcpos j).ne']
              ring
            have hpoint : e (((arms j).subpath 0 (cut j)) s) = e (arms j t) := by
              change e (arms j (Icc.convexComb 0 (cut j) s)) = e (arms j t)
              rw [hparam]
            rw [hco _ (hUS hpreU)] at hycore ⊢
            apply fullCore _ _ _ R j
            refine ⟨?_,hycore⟩
            exact ⟨e (((arms j).subpath 0 (cut j)) s),⟨s,rfl⟩,congrArg R.H hpoint⟩
          intro Incident ai bi pi
          letI : Fintype Incident := Fintype.ofFinite Incident
          have hpre (i : Incident) : ∃ t : I, pi i t = x := i.property
          choose τ hτ using hpre
          obtain ⟨V,hV,hxV,hmeet,habsent,haV,hbV⟩ := vertexProducer a b p hf x
          let W := V ∩ e.source
          have hW : IsOpen W := hV.inter e.open_source
          have hxW : x ∈ W := ⟨hxV,hxS⟩
          have hWS : W ⊆ e.source := Set.inter_subset_right
          have hmeetI : ∀ i j : Incident, i ≠ j → ∀ y ∈ W,
              y ∈ Set.range (pi i) → y ∈ Set.range (pi j) → y = x := by
            intro i j hij y hy hi hj
            exact hmeet i.val j.val (fun he => hij (Subtype.ext he)) y hy.1 hi hj
          have haWI (i : Incident) (hi : ai i ∈ W) : ai i = x := haV i.val hi.1
          have hbWI (i : Incident) (hi : bi i ∈ W) : bi i = x := hbV i.val hi.1
          obtain ⟨arms,hrange,hcover,cut,U,hcut,hU,hxU,hUW,hdisj,R,G,hGx,hGfix,hGcoord⟩ :=
            starProducer ai bi pi (fun i => hp i.val) x τ hτ e W hW hxW hWS hmeetI haWI hbWI
          have hNoG (i : J) (hi : x ∉ Set.range (p i)) : Disjoint U (Set.range (p i)) :=
            (habsent i hi).mono (hUW.trans Set.inter_subset_left) Set.Subset.rfl
          refine ⟨τ,hτ,arms,hrange,hcover,cut,U,hcut,hU,hxU,hUW.trans hWS,hNoG,
            hdisj,R,G,hGx,hGfix,hGcoord,?_⟩
          intro i t hyS hycore
          have hcoreU : G.finalMap (p i t) ∈ U := by
            have hsup : e (G.finalMap (p i t)) ∈ Metric.closedBall (e x) R.supportRadius :=
              (Metric.closedBall_subset_closedBall R.core_lt_support.le) hycore
            obtain ⟨u,hu,he⟩ := R.support_subset hsup
            have huy : u = G.finalMap (p i t) := e.injOn (hUW.trans hWS hu) hyS he
            exact huy ▸ hu
          have hpreU : p i t ∈ U := by
            by_contra hn
            have hzz : G.finalMap (p i t) = p i t := hGfix 1 _ hn
            exact hn (hzz ▸ hcoreU)
          by_cases hx : p i t = x
          · left
            rw [hx]
            have hh : G.finalMap x = x := hGx 1
            rw [hh]
          · right
            have hincident : x ∈ Set.range (p i) := by
              by_contra hn
              exact Set.disjoint_left.mp (hNoG i hn) hpreU ⟨t,rfl⟩
            let j : Incident := ⟨i,hincident⟩
            obtain ⟨k,hki,hmem⟩ := hcover j t hx
            change p i t ∈ Set.range (arms k) at hmem
            obtain ⟨u,he⟩ := hmem
            refine ⟨k,?_⟩
            have hh := wholeCore e x U (hUW.trans hWS) _ arms cut (fun j => (hcut j).1)
              hdisj R G (fun z hz => hGfix 1 z hz) (fun z hz => (hGcoord z hz).2) k u
            rw [he] at hh
            exact hh hyS hycore
        have prefixProducer {S J K : Type} [TopologicalSpace S] [T2Space S] [Fintype J] [Fintype K]
            (e : OpenPartialHomeomorph S Plane) {a b : S} (p : Path a b) (hp : Function.Injective p)
            (ha : a ∈ e.source) (hb : b ∉ e.source)
            (v : J → Plane) (hv : ∀ j, v j ≠ 0)
            (core big : ℝ) (hcore : 0 < core) (hbig : core < big)
            (hBT : Metric.closedBall (e a) big ⊆ e.target)
            (old : K → Set S)
            (hOld : ∀ i z, z ∈ old i → z ∈ e.source →
              e z ∈ Metric.closedBall (e a) core → e z = e a ∨
                ∃ j, e z ∈ segment ℝ (e a) (e a + v j))
            (P : Set S) (hPsrc : Disjoint e.source P) (hpp : Disjoint (Set.range p) P) :
            ∃ d : Path a b, Path.Homotopic p d ∧ Function.Injective d ∧
              Disjoint (Set.range d) P ∧
              ∃ lo : I, 0 < lo.val ∧ lo.val < 1 ∧
                (∀ i, (old i ∩ d '' Set.Icc 0 lo).Finite) ∧
                ∀ β : I, β.val < 1 → ∃ η : I, 0 < η.val ∧ η.val < 1 ∧
                  d '' Set.Icc η 1 ⊆ p '' Set.Icc β 1 := by
          classical
          have boundedExit {S : Type} [TopologicalSpace S] [T2Space S] {a b : S}
              (p : Path a b) (hp : Function.Injective p)
              (u : I) (hu : 0 < u.val)
              (e : OpenPartialHomeomorph S Plane) (ha : a ∈ e.source)
              (cap : ℝ) (hcap : 0 < cap) :
              ∃ R : ℝ, ∃ τ : I, 0 < R ∧ R < cap ∧ 0 < τ.val ∧ τ.val < u.val ∧
                Metric.closedBall (e a) R ⊆ e.target ∧
                p τ ∈ frontier (e.symm '' Metric.closedBall (e a) R) ∧
                (∀ t : I, τ.val < t.val → p t ∉ e.symm '' Metric.closedBall (e a) R) ∧
                Disjoint (e.symm '' Metric.closedBall (e a) R) (p '' Set.Icc u 1) := by
            have disk {S : Type} [TopologicalSpace S] [T2Space S]
                (e : OpenPartialHomeomorph S Plane) (a : S) (ha : a ∈ e.source)
                (F : Set S) (hF : IsClosed F) (haF : a ∉ F)
                (cap : ℝ) (hcap : 0 < cap) :
                ∃ R : ℝ, 0 < R ∧ R < cap ∧
                  Metric.closedBall (e a) R ⊆ e.target ∧
                  IsCompact (e.symm '' Metric.closedBall (e a) R) ∧
                  a ∈ interior (e.symm '' Metric.closedBall (e a) R) ∧
                  e.symm '' Metric.closedBall (e a) R ⊆ e.source ∧
                  Disjoint (e.symm '' Metric.closedBall (e a) R) F := by
              let V := e '' (e.source ∩ Fᶜ)
              have hV : IsOpen V := e.isOpen_image_source_inter hF.isOpen_compl
              have heaV : e a ∈ V := ⟨a,⟨ha,haF⟩,rfl⟩
              obtain ⟨δ,hδ,hδV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds heaV)
              let R := min δ cap/2
              have hR : 0 < R := by dsimp [R]; positivity
              have hRδ : R < δ := by dsimp [R]; linarith [min_le_left δ cap]
              have hRcap : R < cap := by dsimp [R]; linarith [min_le_right δ cap]
              have hRV : Metric.closedBall (e a) R ⊆ V :=
                (Metric.closedBall_subset_ball hRδ).trans hδV
              have hVT : V ⊆ e.target := by
                rintro y ⟨x,hx,rfl⟩
                exact e.map_source hx.1
              have hRT := hRV.trans hVT
              let K := e.symm '' Metric.closedBall (e a) R
              have hKcompact : IsCompact K :=
                (isCompact_closedBall (e a) R).image_of_continuousOn (e.symm.continuousOn.mono hRT)
              have hsmall : Metric.ball (e a) R ⊆ e.target := Metric.ball_subset_closedBall.trans hRT
              have hopen : IsOpen (e.symm '' Metric.ball (e a) R) :=
                e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hsmall
              have hmem : a ∈ e.symm '' Metric.ball (e a) R :=
                ⟨e a,Metric.mem_ball_self hR,e.left_inv ha⟩
              have hinterior : a ∈ interior K :=
                (interior_mono (Set.image_mono Metric.ball_subset_closedBall))
                  (by rw [hopen.interior_eq]; exact hmem)
              have hKS : K ⊆ e.source := by
                rintro x ⟨y,hy,rfl⟩
                exact e.map_target (hRT hy)
              have hdisj : Disjoint K F := by
                apply Set.disjoint_left.mpr
                rintro x ⟨y,hy,rfl⟩ hxF
                obtain ⟨z,hz,he⟩ := hRV hy
                have hinv : e.symm y = z := by rw [← he]; exact e.left_inv hz.1
                exact hz.2 (hinv ▸ hxF)
              exact ⟨R,hR,hRcap,hRT,hKcompact,hinterior,hKS,hdisj⟩
            have lastExit {S : Type} [TopologicalSpace S] {a b : S} (p : Path a b)
                (K : Set S) (hK : IsClosed K) (ha : a ∈ interior K) (hb : b ∉ K) :
                ∃ τ : I, 0 < τ ∧ τ < 1 ∧ p τ ∈ frontier K ∧
                  ∀ t : I, τ < t → p t ∉ K := by
              obtain ⟨c,hc0,hfront,hbefore⟩ := path_first_exit_frontier p.symm Kᶜ
                hK.isOpen_compl hb (by exact fun h => h (interior_subset ha))
              have hcne : c ≠ 1 := by
                intro he
                have hf : a ∈ frontier K := by simpa [he] using hfront
                exact Set.disjoint_left.mp disjoint_interior_frontier ha hf
              have hc1 : c < 1 := lt_of_le_of_ne (unitInterval.le_one c) hcne
              refine ⟨unitInterval.symm c,?_,?_,?_,?_⟩
              · have hh : unitInterval.symm 1 < unitInterval.symm c :=
                  unitInterval.symm_lt_symm.mpr hc1
                simpa using hh
              · have hh : unitInterval.symm c < unitInterval.symm 0 :=
                  unitInterval.symm_lt_symm.mpr hc0
                simpa using hh
              · simpa only [Path.symm_apply,Function.comp_apply,frontier_compl] using hfront
              · intro t ht
                have hh : unitInterval.symm t < c := by
                  simpa only [unitInterval.symm_symm] using unitInterval.symm_lt_symm.mpr ht
                simpa only [Path.symm_apply,Function.comp_apply,unitInterval.symm_symm,Set.mem_compl_iff] using hbefore _ hh
            let F := p '' Set.Icc u 1
            have hFc : IsCompact F := isCompact_Icc.image p.continuous
            have haF : a ∉ F := by
              rintro ⟨t,ht,he⟩
              have ht0 : t = 0 := hp (he.trans p.source.symm)
              have hh := ht.1
              rw [ht0] at hh
              exact (not_le_of_gt hu) hh
            obtain ⟨R,hR,hRcap,hRT,hKc,haK,hKS,hKF⟩ := disk e a ha F hFc.isClosed haF cap hcap
            let K := e.symm '' Metric.closedBall (e a) R
            have hbF : b ∈ F := ⟨1,⟨u.property.2,le_rfl⟩,p.target⟩
            have hbK : b ∉ K := fun h => Set.disjoint_left.mp hKF h hbF
            obtain ⟨τ,hτ0,hτ1,hfront,hafter⟩ := lastExit p K hKc.isClosed haK hbK
            have hτK : p τ ∈ K := by
              have hh := frontier_subset_closure hfront
              rwa [hKc.isClosed.closure_eq] at hh
            have hτu : τ.val < u.val := by
              by_contra hh
              have hmem : p τ ∈ F := ⟨τ,⟨not_lt.mp hh,τ.property.2⟩,rfl⟩
              exact Set.disjoint_left.mp hKF hτK hmem
            exact ⟨R,τ,hR,hRcap,hτ0,hτu,hRT,hfront,hafter,hKF⟩
          have frontierCoordinate {S : Type} [TopologicalSpace S] [T2Space S]
              (e : OpenPartialHomeomorph S Plane) (center : Plane) (R : ℝ)
              (hRT : Metric.closedBall center R ⊆ e.target)
              (x : S) (hx : x ∈ frontier (e.symm '' Metric.closedBall center R)) :
              x ∈ e.source ∧ ‖e x-center‖ = R := by
            let K := e.symm '' Metric.closedBall center R
            have hKc : IsCompact K :=
              (isCompact_closedBall center R).image_of_continuousOn (e.symm.continuousOn.mono hRT)
            have hxK : x ∈ K := by
              have hh := frontier_subset_closure hx
              rwa [hKc.isClosed.closure_eq] at hh
            obtain ⟨y,hy,he⟩ := hxK
            have hxS : x ∈ e.source := he ▸ e.map_target (hRT hy)
            have hexy : e x = y := by rw [← he]; exact e.right_inv (hRT hy)
            have hle : dist (e x) center ≤ R := by
              rw [hexy]
              exact hy
            have hnlt : ¬ dist (e x) center < R := by
              intro hlt
              have hball : Metric.ball center R ⊆ e.target := Metric.ball_subset_closedBall.trans hRT
              have hopen := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hball
              have hmem : x ∈ e.symm '' Metric.ball center R :=
                ⟨e x,hlt,e.left_inv hxS⟩
              have hi : x ∈ interior K :=
                (interior_mono (Set.image_mono Metric.ball_subset_closedBall))
                  (by rw [hopen.interior_eq]; exact hmem)
              exact Set.disjoint_left.mp disjoint_interior_frontier hi hx
            refine ⟨hxS,?_⟩
            rw [← dist_eq_norm]
            exact le_antisymm hle (not_lt.mp hnlt)
          have finiteArc {S J K : Type} [TopologicalSpace S] [Fintype J] [Fintype K]
              (e : OpenPartialHomeomorph S Plane) (x y : S) (hx : x ∈ e.source) (hy : y ∈ e.source)
              (v : J → Plane) (hv : ∀ j, v j ≠ 0)
              (R : ℝ) (hR : 0 < R) (hyR : ‖e y-e x‖ = R)
              (hRT : Metric.closedBall (e x) R ⊆ e.target)
              (old : K → Set S)
              (hOld : ∀ i z, z ∈ old i → z ∈ e.source →
                e z ∈ Metric.closedBall (e x) R → e z = e x ∨
                  ∃ j, e z ∈ segment ℝ (e x) (e x + v j)) :
              ∃ q : Path x y, Function.Injective q ∧
                (∀ t, q t ∈ e.source ∧ ‖e (q t)-e x‖ ≤ R) ∧
                ∀ i, (old i ∩ Set.range q).Finite := by
            classical
            have bendProducer {J : Type} [Fintype J] (v : J → Plane) (hv : ∀ j, v j ≠ 0)
                (o z : Plane) (R : ℝ) (hR : 0 < R) (hzR : ‖z-o‖ = R) :
                ∃ arc : Path o z, Function.Injective arc ∧
                  (∀ t, ‖arc t-o‖ ≤ R) ∧
                  ∀ j, (Set.range arc ∩ segment ℝ o (o + v j)).Finite := by
              have zeroProducer {J : Type} [Fintype J] (v : J → Plane) (hv : ∀ j, v j ≠ 0)
                  (z : Plane) (R : ℝ) (hR : 0 < R) (hzR : ‖z‖ = R) :
                  ∃ arc : Path (0 : Plane) z, Function.Injective arc ∧
                    (∀ t, ‖arc t‖ ≤ R) ∧
                    ∀ j, (Set.range arc ∩ segment ℝ (0 : Plane) (v j)).Finite := by
                classical
                have bend {J : Type} [Fintype J] (v : J → Plane) (hv : ∀ j, v j ≠ 0)
                    (z : Plane) (hz : z ≠ 0) (R : ℝ) (hR : 0 < R) :
                    ∃ w : Plane, ‖w‖ = R/2 ∧
                      (∀ j, (v j) 0*w 1-(v j) 1*w 0 ≠ 0) ∧ z 0*w 1-z 1*w 0 ≠ 0 := by
                  classical
                  let det (y : Plane) : Module.Dual ℝ Plane := {
                    toFun := fun x => y 0*x 1-y 1*x 0
                    map_add' := by
                      intro x x'
                      change y 0*(x 1+x' 1)-y 1*(x 0+x' 0) =
                        (y 0*x 1-y 1*x 0)+(y 0*x' 1-y 1*x' 0)
                      ring
                    map_smul' := by
                      intro c x
                      change y 0*(c*x 1)-y 1*(c*x 0) = c*(y 0*x 1-y 1*x 0)
                      ring }
                  let u : Option J → Plane := fun i => i.elim z v
                  have hu (i : Option J) : u i ≠ 0 := by cases i <;> simp [u,hz,hv]
                  have hex (i : Option J) : ∃ x, det (u i) x ≠ 0 := by
                    by_cases h0 : u i 0 = 0
                    · have h1 : u i 1 ≠ 0 := by
                        intro hh
                        apply hu i
                        ext k
                        fin_cases k <;> simp [h0,hh]
                      refine ⟨Plane.mk 1 0,?_⟩
                      simpa [det,Plane.mk] using neg_ne_zero.mpr h1
                    · refine ⟨Plane.mk 0 1,?_⟩
                      simpa [det,Plane.mk] using h0
                  obtain ⟨w0,hw0⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
                    (fun i : Option J => det (u i)) hex
                  have hw0ne : w0 ≠ 0 := by
                    intro he
                    have hh := hw0 none
                    rw [he,map_zero] at hh
                    exact hh rfl
                  have hn : 0 < ‖w0‖ := norm_pos_iff.mpr hw0ne
                  let c : ℝ := R/(2*‖w0‖)
                  have hc : 0 < c := by dsimp [c]; positivity
                  let w : Plane := c • w0
                  have hw (i : Option J) : det (u i) w ≠ 0 := by
                    change det (u i) (c • w0) ≠ 0
                    rw [map_smul,smul_eq_mul]
                    exact mul_ne_zero hc.ne' (hw0 i)
                  refine ⟨w,?_,?_,?_⟩
                  · rw [show w=c • w0 from rfl,norm_smul,Real.norm_eq_abs,abs_of_pos hc]
                    dsimp [c]
                    field_simp [hn.ne']
                  · intro j
                    exact hw (some j)
                  · exact hw none
                have finiteLinear (f : Plane →ₗ[ℝ] ℝ) (u v : Plane) (hu : f u ≠ 0) :
                    (segment ℝ u v ∩ {x | f x = 0}).Finite := by
                  have formula (t : ℝ) : f (AffineMap.lineMap u v t) =
                      f u+t*(f v-f u) := by
                    simp [AffineMap.lineMap_apply_module]
                    ring
                  by_cases hd : f v-f u = 0
                  · apply (Set.finite_empty : (∅ : Set Plane).Finite).subset
                    rintro x ⟨hx,hfx⟩
                    rw [segment_eq_image_lineMap] at hx
                    obtain ⟨t,ht,rfl⟩ := hx
                    change f (AffineMap.lineMap u v t) = 0 at hfx
                    rw [formula,hd,mul_zero,add_zero] at hfx
                    exact False.elim (hu hfx)
                  · apply (Set.finite_singleton (AffineMap.lineMap u v (-f u/(f v-f u)))).subset
                    rintro x ⟨hx,hfx⟩
                    rw [segment_eq_image_lineMap] at hx
                    obtain ⟨t,ht,rfl⟩ := hx
                    change f (AffineMap.lineMap u v t) = 0 at hfx
                    have he : t = -f u/(f v-f u) := by
                      apply (eq_div_iff hd).mpr
                      rw [formula] at hfx
                      linarith
                    rw [he]
                    exact Set.mem_singleton _
                let det (y : Plane) : Module.Dual ℝ Plane := {
                  toFun := fun x => y 0*x 1-y 1*x 0
                  map_add' := by
                    intro x x'
                    change y 0*(x 1+x' 1)-y 1*(x 0+x' 0) =
                      (y 0*x 1-y 1*x 0)+(y 0*x' 1-y 1*x' 0)
                    ring
                  map_smul' := by
                    intro c x
                    change y 0*(c*x 1)-y 1*(c*x 0) = c*(y 0*x 1-y 1*x 0)
                    ring }
                have hz : z ≠ 0 := by intro he; rw [he,norm_zero] at hzR; linarith
                obtain ⟨w,hwn,hwv,hwz⟩ := bend v hv z hz R hR
                have h0w : (0 : Plane) ≠ w := by
                  intro he
                  rw [← he,norm_zero] at hwn
                  linarith
                have hww : det w w = 0 := by dsimp [det]; ring
                have hwz' : det w z ≠ 0 := by
                  intro he
                  apply hwz
                  change w 0*z 1-w 1*z 0 = 0 at he
                  nlinarith
                have hWZ : w ≠ z := by
                  intro he
                  apply hwz'
                  rw [← he]
                  exact hww
                let A : Set Plane := segment ℝ (0 : Plane) w ∪ segment ℝ w z
                have hArc : IsArcBetween A (0 : Plane) z := by
                  apply (isArcBetween_segment h0w).concatenate (isArcBetween_segment hWZ)
                  intro x hx hy
                  have hfx : det w x = 0 := by
                    rw [segment_eq_image_lineMap] at hx
                    obtain ⟨s,hs,rfl⟩ := hx
                    simp [AffineMap.lineMap_apply_module,hww]
                  rw [segment_eq_image_lineMap] at hy
                  obtain ⟨t,ht,he⟩ := hy
                  have htf : t * det w z = 0 := by
                    have hh := congrArg (det w) he
                    simpa [AffineMap.lineMap_apply_module,hww,hfx] using hh
                  have ht0 : t = 0 := (mul_eq_zero.mp htf).resolve_right hwz'
                  rw [ht0] at he
                  simpa using he.symm
                have h0ball : (0 : Plane) ∈ Metric.closedBall 0 R := by
                  simp [Metric.mem_closedBall,hR.le]
                have hwball : w ∈ Metric.closedBall (0 : Plane) R := by
                  simp only [Metric.mem_closedBall,dist_zero_right,hwn]
                  linarith
                have hzball : z ∈ Metric.closedBall (0 : Plane) R := by
                  simp [Metric.mem_closedBall,dist_zero_right,hzR]
                have hAball : A ⊆ Metric.closedBall 0 R := by
                  intro x hx
                  rcases hx with hx | hx
                  · exact (convex_closedBall (0 : Plane) R).segment_subset h0ball hwball hx
                  · exact (convex_closedBall (0 : Plane) R).segment_subset hwball hzball hx
                have hAfin (j : J) : (A ∩ segment ℝ (0 : Plane) (v j)).Finite := by
                  have first : (segment ℝ (0 : Plane) w ∩ {x | det (v j) x = 0}).Finite := by
                    rw [segment_symm]
                    exact finiteLinear (det (v j)) w 0 (hwv j)
                  have second : (segment ℝ w z ∩ {x | det (v j) x = 0}).Finite :=
                    finiteLinear (det (v j)) w z (hwv j)
                  have ray : segment ℝ (0 : Plane) (v j) ⊆ {x | det (v j) x = 0} := by
                    intro x hx
                    rw [segment_eq_image_lineMap] at hx
                    obtain ⟨t,ht,rfl⟩ := hx
                    change det (v j) (AffineMap.lineMap (0 : Plane) (v j) t) = 0
                    have hh : det (v j) (v j) = 0 := by dsimp [det]; ring
                    simp [AffineMap.lineMap_apply_module,hh]
                  apply (first.union second).subset
                  rintro x ⟨hx,hr⟩
                  rcases hx with hx | hx
                  · exact Or.inl ⟨hx,ray hr⟩
                  · exact Or.inr ⟨hx,ray hr⟩
                obtain ⟨f,hfc,hfi,hfr,hf0,hf1⟩ := hArc
                let arc : Path (0 : Plane) z := {
                  toFun := fun t => f t
                  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp hfc
                  source' := hf0
                  target' := hf1 }
                have hrange : Set.range arc = A := by
                  apply Set.Subset.antisymm
                  · rintro _ ⟨t,rfl⟩
                    rw [← hfr]
                    exact ⟨(t:ℝ),t.property,rfl⟩
                  · intro x hx
                    rw [← hfr] at hx
                    obtain ⟨t,ht,rfl⟩ := hx
                    exact ⟨⟨t,ht⟩,rfl⟩
                refine ⟨arc,?_,?_,?_⟩
                · intro t u he
                  exact Subtype.ext (hfi t.property u.property he)
                · intro t
                  have hh : arc t ∈ Metric.closedBall (0 : Plane) R :=
                    hAball (hrange ▸ Set.mem_range_self t)
                  simpa only [Metric.mem_closedBall,dist_zero_right] using hh
                · intro j
                  rw [hrange]
                  exact hAfin j
              obtain ⟨arc0,hi,hball,hfin⟩ := zeroProducer v hv (z-o) R hR hzR
              let arc : Path o z := {
                toFun := fun t => arc0 t+o
                continuous_toFun := arc0.continuous.add continuous_const
                source' := by rw [arc0.source,zero_add]
                target' := by rw [arc0.target,sub_add_cancel] }
              refine ⟨arc,?_,?_,?_⟩
              · intro t u he
                exact hi (add_right_cancel he)
              · intro t
                change ‖arc0 t+o-o‖ ≤ R
                simpa using hball t
              · intro j
                apply ((hfin j).image (fun y => y+o)).subset
                rintro y ⟨⟨t,rfl⟩,hr⟩
                have hs : arc0 t ∈ segment ℝ (0 : Plane) (v j) := by
                  apply (mem_segment_translate ℝ o).mp
                  simpa [arc,add_comm] using hr
                exact ⟨arc0 t,⟨⟨t,rfl⟩,hs⟩,rfl⟩
            obtain ⟨arc,hi,hball,hfin⟩ := bendProducer v hv (e x) (e y) R hR hyR
            have hArcT (t : I) : arc t ∈ e.target := hRT (by
              rw [Metric.mem_closedBall,dist_eq_norm]
              exact hball t)
            let q : Path x y := {
              toFun := fun t => e.symm (arc t)
              continuous_toFun := e.symm.continuousOn.comp_continuous arc.continuous hArcT
              source' := by rw [arc.source,e.left_inv hx]
              target' := by rw [arc.target,e.left_inv hy] }
            have hqS (t : I) : q t ∈ e.source := e.map_target (hArcT t)
            have hqco (t : I) : e (q t) = arc t := e.right_inv (hArcT t)
            let C : Set Plane := (Set.range arc ∩ {e x}) ∪
              ⋃ j, Set.range arc ∩ segment ℝ (e x) (e x + v j)
            have hC : C.Finite :=
              ((Set.finite_singleton (e x)).subset Set.inter_subset_right).union
                (Set.finite_iUnion hfin)
            refine ⟨q,?_,?_,?_⟩
            · intro t u he
              exact hi (e.symm.injOn (hArcT t) (hArcT u) he)
            · intro t
              exact ⟨hqS t,by rw [hqco]; exact hball t⟩
            · intro i
              apply (hC.image e.symm).subset
              rintro z ⟨hzold,⟨t,rfl⟩⟩
              have hqball : e (q t) ∈ Metric.closedBall (e x) R := by
                rw [hqco,Metric.mem_closedBall,dist_eq_norm]
                exact hball t
              have hc : arc t ∈ C := by
                rcases hOld i (q t) hzold (hqS t) hqball with he | ⟨j,hj⟩
                · exact Or.inl ⟨⟨t,rfl⟩,Set.mem_singleton_iff.mpr ((hqco t).symm.trans he)⟩
                · exact Or.inr (Set.mem_iUnion.mpr ⟨j,⟨⟨t,rfl⟩,by rwa [hqco] at hj⟩⟩)
              exact ⟨arc t,hc,rfl⟩
          have splice {S : Type} [TopologicalSpace S] {a b : S}
              (p : Path a b) (hp : Function.Injective p)
              (τ : I) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1)
              (K : Set S) (hafter : ∀ t : I, τ.val < t.val → p t ∉ K)
              (q : Path (p 0) (p τ)) (hqi : Function.Injective q)
              (hqK : ∀ t, q t ∈ K)
              (e : OpenPartialHomeomorph S Plane) (center : Plane) (r : ℝ) (hr : 0 < r)
              (hball : Metric.ball center r ⊆ e.target)
              (hpball : ∀ t, (p.subpath 0 τ) t ∈ e.source ∧
                e ((p.subpath 0 τ) t) ∈ Metric.ball center r)
              (hqball : ∀ t, q t ∈ e.source ∧ e (q t) ∈ Metric.ball center r) :
              ∃ d : Path a b, Path.Homotopic p d ∧ Function.Injective d ∧
                Set.range d = Set.range q ∪ p '' Set.Icc τ 1 ∧
                (∀ t : I, t.val ≤ 1/2 → d t ∈ Set.range q) ∧
                ∀ β : I, β.val < 1 → ∃ η : I, 0 < η.val ∧ η.val < 1 ∧
                  d '' Set.Icc η 1 ⊆ p '' Set.Icc β 1 := by
            have chartHomotopy {S : Type} [TopologicalSpace S]
                (e : OpenPartialHomeomorph S Plane)
                (center : Plane) (r : ℝ) (hr : 0 < r)
                (hball : Metric.ball center r ⊆ e.target)
                {a b : S} (p q : Path a b)
                (hp : ∀ t, p t ∈ e.source ∧ e (p t) ∈ Metric.ball center r)
                (hq : ∀ t, q t ∈ e.source ∧ e (q t) ∈ Metric.ball center r) :
                Path.Homotopic p q := by
              have ha : a ∈ e.source ∧ e a ∈ Metric.ball center r := by simpa using hp 0
              have hb : b ∈ e.source ∧ e b ∈ Metric.ball center r := by simpa using hp 1
              let B := Metric.ball center r
              let lift (path : Path a b)
                  (hpath : ∀ t, path t ∈ e.source ∧ e (path t) ∈ B) :
                  Path (⟨e a,ha.2⟩ : B) (⟨e b,hb.2⟩ : B) := {
                toFun := fun t => ⟨e (path t),(hpath t).2⟩
                continuous_toFun := (e.continuousOn.comp_continuous path.continuous
                  (fun t => (hpath t).1)).subtype_mk _
                source' := by apply Subtype.ext; simp
                target' := by apply Subtype.ext; simp }
              let inverse : C(B,S) := ⟨fun x => e.symm x,
                e.symm.continuousOn.comp_continuous continuous_subtype_val (fun x => hball x.property)⟩
              have hea : a = inverse ⟨e a,ha.2⟩ := (e.left_inv ha.1).symm
              have heb : b = inverse ⟨e b,hb.2⟩ := (e.left_inv hb.1).symm
              letI : ContractibleSpace B := Metric.contractibleSpace_ball hr
              have H := Path.Homotopic.pathCast
                ((SimplyConnectedSpace.paths_homotopic (lift p hp) (lift q hq)).map inverse) hea heb
              have hP : ((lift p hp).map inverse.continuous).cast hea heb = p := by
                ext t
                exact e.left_inv (hp t).1
              have hQ : ((lift q hq).map inverse.continuous).cast hea heb = q := by
                ext t
                exact e.left_inv (hq t).1
              rwa [hP,hQ] at H
            have concatInjective {S : Type} [TopologicalSpace S] {a b c : S}
                (p : Path a b) (q : Path b c)
                (hp : Function.Injective p) (hq : Function.Injective q)
                (hcross : ∀ t u, p t = q u → t = 1 ∧ u = 0) :
                Function.Injective (p.trans q) := by
              intro t u he
              rw [Path.trans_apply,Path.trans_apply] at he
              split_ifs at he with ht hu hu
              · have hh := congrArg Subtype.val (hp he)
                apply Subtype.ext
                dsimp at hh
                linarith
              · obtain ⟨h1,h0⟩ := hcross _ _ he
                have h1v := congrArg Subtype.val h1
                have h0v := congrArg Subtype.val h0
                apply Subtype.ext
                dsimp at h1v h0v
                linarith
              · obtain ⟨h1,h0⟩ := hcross _ _ he.symm
                have h1v := congrArg Subtype.val h1
                have h0v := congrArg Subtype.val h0
                apply Subtype.ext
                dsimp at h1v h0v
                linarith
              · have hh := congrArg Subtype.val (hq he)
                apply Subtype.ext
                dsimp at hh
                linarith
            let tail := p.subpath τ 1
            have htail : Function.Injective tail := by
              intro t u he
              have hh := congrArg Subtype.val (hp he)
              simp only [Icc.coe_convexComb] at hh
              norm_num at hh
              apply Subtype.ext
              nlinarith
            have hcross : ∀ t u, q t = tail u → t = 1 ∧ u = 0 := by
              intro t u he
              have hu : u = 0 := by
                by_contra hn
                have hup : 0 < u.val := lt_of_le_of_ne u.property.1
                  (fun hh => hn (Subtype.ext hh.symm))
                have hc : τ.val < (Icc.convexComb τ 1 u).val := by
                  simp only [Icc.coe_convexComb]
                  norm_num
                  nlinarith
                exact hafter _ hc (he ▸ hqK t)
              refine ⟨?_,hu⟩
              apply hqi
              simpa [hu,tail] using he
            let d : Path a b := (q.trans tail).cast p.source.symm p.target.symm
            have hH := (Path.Homotopic.subpath_trans_subpath p 0 τ 1).symm.trans
              ((chartHomotopy e center r hr hball (p.subpath 0 τ) q hpball hqball).hcomp
                (Path.Homotopic.refl tail))
            have hcast := hH.pathCast p.source.symm p.target.symm
            have hold : (p.subpath 0 1).cast p.source.symm p.target.symm = p := by
              ext t
              simp
            refine ⟨d,?_,?_,?_,?_,?_⟩
            · simpa only [hold] using hcast
            · exact concatInjective q tail hqi htail hcross
            · change Set.range (q.trans tail) = _
              rw [Path.trans_range,Path.range_subpath_of_le p τ 1 τ.property.2]
            · intro t ht
              change (q.trans tail) t ∈ Set.range q
              rw [Path.trans_apply,dif_pos ht]
              exact ⟨_,rfl⟩
            · intro β hβ
              let η : I := ⟨(β.val+3)/4,by constructor <;> linarith [β.property.1,β.property.2]⟩
              have hη0 : 0 < η.val := by dsimp [η]; linarith [β.property.1]
              have hη1 : η.val < 1 := by dsimp [η]; linarith
              refine ⟨η,hη0,hη1,?_⟩
              rintro z ⟨t,ht,rfl⟩
              have htr : ¬ t.val ≤ 1/2 := by
                have hh := ht.1
                change (β.val+3)/4 ≤ t.val at hh
                linarith [β.property.1]
              change (q.trans tail) t ∈ p '' Set.Icc β 1
              rw [Path.trans_apply,dif_neg htr]
              let w : I := ⟨2*t.val-1,unitInterval.two_mul_sub_one_mem_iff.mpr
                ⟨(not_le.mp htr).le,t.property.2⟩⟩
              refine ⟨Icc.convexComb τ 1 w,⟨?_,(Icc.convexComb τ 1 w).property.2⟩,rfl⟩
              change β.val ≤ (Icc.convexComb τ 1 w).val
              simp only [Icc.coe_convexComb]
              norm_num
              have hw : β.val ≤ w.val := by
                have hh := ht.1
                change (β.val+3)/4 ≤ t.val at hh
                dsimp [w]
                linarith [β.property.2]
              nlinarith [w.property.2,τ.property.1]
          have hbigpos : 0 < big := lt_trans hcore hbig
          let W := e.symm '' Metric.ball (e a) big
          have hballT : Metric.ball (e a) big ⊆ e.target := Metric.ball_subset_closedBall.trans hBT
          have hW : IsOpen W := e.isOpen_image_symm_of_subset_target Metric.isOpen_ball hballT
          have haW : a ∈ W := ⟨e a,Metric.mem_ball_self hbigpos,e.left_inv ha⟩
          have hWS : W ⊆ e.source := by
            rintro z ⟨y,hy,rfl⟩
            exact e.map_target (hballT hy)
          have hbW : b ∉ W := fun h => hb (hWS h)
          obtain ⟨c,hc0,hcfront,hcpre⟩ := path_first_exit_frontier p W hW haW hbW
          have hc0v : 0 < c.val := by simpa using hc0
          let u : I := ⟨c.val/2,by constructor <;> linarith [c.property.1,c.property.2]⟩
          have hu : 0 < u.val := by dsimp [u]; linarith
          obtain ⟨ρ,τ,hρ,hρcore,hτ0,hτu,hρT,hfront,hafter,hKtail⟩ :=
            boundedExit p hp u hu e ha core hcore
          have hτ1 : τ.val < 1 := lt_of_lt_of_le hτu u.property.2
          obtain ⟨hτS,hτnorm⟩ := frontierCoordinate e (e a) ρ hρT (p τ) hfront
          have hOldρ : ∀ i z, z ∈ old i → z ∈ e.source →
              e z ∈ Metric.closedBall (e a) ρ → e z = e a ∨
                ∃ j, e z ∈ segment ℝ (e a) (e a + v j) := by
            intro i z hi hz hρz
            exact hOld i z hi hz ((Metric.closedBall_subset_closedBall hρcore.le) hρz)
          obtain ⟨q,hqi,hq,hfin⟩ := finiteArc e a (p τ) ha hτS v hv ρ hρ hτnorm hρT old hOldρ
          let q0 : Path (p 0) (p τ) := q.cast p.source rfl
          have hq0i : Function.Injective q0 := hqi
          have hqK (t : I) : q0 t ∈ e.symm '' Metric.closedBall (e a) ρ := by
            refine ⟨e (q t),?_,e.left_inv (hq t).1⟩
            rw [Metric.mem_closedBall,dist_eq_norm]
            exact (hq t).2
          have hpb (t : I) : (p.subpath 0 τ) t ∈ e.source ∧
              e ((p.subpath 0 τ) t) ∈ Metric.ball (e a) big := by
            have hs : (Icc.convexComb 0 τ t).val < c.val := by
              simp only [Icc.coe_convexComb]
              norm_num
              have huC : u.val < c.val := by dsimp [u]; linarith
              nlinarith [t.property.1,t.property.2,τ.property.1,hτu]
            have hw := hcpre (Icc.convexComb 0 τ t) hs
            obtain ⟨z,hz,he⟩ := hw
            have hpoint : (p.subpath 0 τ) t = e.symm z := he.symm
            rw [hpoint]
            exact ⟨e.map_target (hballT hz),by rwa [e.right_inv (hballT hz)]⟩
          have hqb (t : I) : q0 t ∈ e.source ∧ e (q0 t) ∈ Metric.ball (e a) big := by
            refine ⟨(hq t).1,?_⟩
            rw [Metric.mem_ball,dist_eq_norm]
            exact lt_of_le_of_lt (hq t).2 (lt_trans hρcore hbig)
          obtain ⟨d,hd,hdi,hrange,hgerm,hretained⟩ := splice p hp τ hτ0 hτ1
            (e.symm '' Metric.closedBall (e a) ρ) hafter q0 hq0i hqK
            e (e a) big hbigpos hballT hpb hqb
          have hdP : Disjoint (Set.range d) P := by
            apply Set.disjoint_left.mpr
            intro z hz hzP
            rw [hrange] at hz
            rcases hz with ⟨t,rfl⟩ | ⟨t,ht,rfl⟩
            · exact Set.disjoint_left.mp hPsrc (hq t).1 hzP
            · exact Set.disjoint_left.mp hpp ⟨t,rfl⟩ hzP
          let lo : I := ⟨1/2,by norm_num⟩
          refine ⟨d,hd,hdi,hdP,lo,by norm_num [lo],by norm_num [lo],?_,hretained⟩
          intro i
          apply (hfin i).subset
          rintro z ⟨hz,⟨t,ht,he⟩⟩
          exact ⟨hz,he ▸ hgerm t ht.2⟩
        let A := P ∪ {b}
        have hAf : A.Finite := hPf.union (Set.finite_singleton b)
        have haP : a ∉ P := fun hh => Set.disjoint_left.mp hpp ⟨0,p.source⟩ hh
        have haA : a ∉ A := by
          rintro (hh | hh)
          · exact haP hh
          · exact hne (Set.mem_singleton_iff.mp hh)
        let e0 := chartAt Plane a
        let e := e0.restr Aᶜ
        have hASopen : IsOpen Aᶜ := hAf.isClosed.isOpen_compl
        have heSource : e.source = e0.source ∩ Aᶜ := e0.restr_source' Aᶜ hASopen
        have haS : a ∈ e.source := by rw [heSource]; exact ⟨mem_chart_source Plane a,haA⟩
        have heA : e.source ⊆ Aᶜ := by rw [heSource]; exact Set.inter_subset_right
        have hbS : b ∉ e.source := fun hh => heA hh (Or.inr (Set.mem_singleton b))
        have hPsrc : Disjoint e.source P := Set.disjoint_left.mpr (fun z hz hP => heA hz (Or.inl hP))
        letI : Fintype {i : J // a ∈ Set.range (old i)} := Fintype.ofFinite _
        obtain ⟨τ,hτ,arms,hrange,hcover,cut,U,hcut,hU,haU,hUS,hNo,hdisj,R,G,hGa,hGfix,hGcoord,hGcore⟩ :=
          coreProducer oa ob old hi hf a e haS
        obtain ⟨F,hF⟩ := G.homeomorphism_at (1 : I)
        have hFfinal : (F : S → S) = G.finalMap := funext hF
        have haF : F a = a := (hF a).trans (hGa 1)
        have hbF : F b = b := (hF b).trans (hGfix 1 b (fun h => hbS (hUS h)))
        have hFP (z : S) (hz : z ∈ P) : F z = z := (hF z).trans (hGfix 1 z (by
          intro h
          exact Set.disjoint_left.mp hPsrc (hUS h) hz))
        let p' : Path a b := (p.map F.continuous).cast haF.symm hbF.symm
        have hp' : Function.Injective p' := by
          intro t u he
          exact hp (F.injective he)
        have hpP' : Disjoint (Set.range p') P := by
          apply Set.disjoint_left.mpr
          rintro z ⟨t,rfl⟩ hz
          have he : p t = p' t := F.injective ((hFP _ hz).symm)
          exact Set.disjoint_left.mp hpp ⟨t,rfl⟩ (he.symm ▸ hz)
        let old' (i : J) := F '' Set.range (old i)
        have hOld : ∀ i z, z ∈ old' i → z ∈ e.source →
            e z ∈ Metric.closedBall (e a) R.coreRadius → e z = e a ∨
              ∃ k, e z ∈ segment ℝ (e a) (e a + R.vector k) := by
          rintro i z ⟨w,⟨t,rfl⟩,rfl⟩ hz hball
          rw [hFfinal] at hz hball ⊢
          exact hGcore i t hz hball
        have hBT : Metric.closedBall (e a) R.supportRadius ⊆ e.target := by
          intro z hz
          obtain ⟨u,hu,rfl⟩ := R.support_subset hz
          exact e.map_source (hUS hu)
        obtain ⟨d',hH,hdi,hdP,lo,hlo0,hlo1,hfin,htail⟩ := prefixProducer e p' hp' haS hbS
          R.vector R.vector_nonzero R.coreRadius R.supportRadius R.core_pos R.core_lt_support
          hBT old' hOld P hPsrc hpP'
        have hasym : F.symm a = a := by
          apply F.injective
          rw [F.apply_symm_apply,haF]
        have hbsym : F.symm b = b := by
          apply F.injective
          rw [F.apply_symm_apply,hbF]
        let d : Path a b := (d'.map F.symm.continuous).cast hasym.symm hbsym.symm
        have hHinv := (hH.map (⟨F.symm,F.symm.continuous⟩ : C(S,S))).pathCast hasym.symm hbsym.symm
        have hpInv : (p'.map F.symm.continuous).cast hasym.symm hbsym.symm = p := by
          ext t
          exact F.symm_apply_apply (p t)
        have hHd : Path.Homotopic p d := by rwa [hpInv] at hHinv
        have hdi' : Function.Injective d := by
          intro t u he
          exact hdi (F.symm.injective he)
        have hdP' : Disjoint (Set.range d) P := by
          apply Set.disjoint_left.mpr
          rintro z ⟨t,rfl⟩ hz
          have he : d' t = d t := (F.apply_symm_apply (d' t)).symm.trans (hFP _ hz)
          exact Set.disjoint_left.mp hdP ⟨t,rfl⟩ (he.symm ▸ hz)
        refine ⟨d,hHd,hdi',hdP',lo,hlo0,hlo1,?_,?_⟩
        · intro i
          apply ((hfin i).image F.symm).subset
          rintro z ⟨hz,⟨t,ht,rfl⟩⟩
          exact ⟨d' t,⟨⟨d t,hz,F.apply_symm_apply _⟩,⟨t,ht,rfl⟩⟩,rfl⟩
        · intro β hβ
          obtain ⟨η,hη0,hη1,hsubset⟩ := htail β hβ
          refine ⟨η,hη0,hη1,?_⟩
          rintro z ⟨t,ht,rfl⟩
          obtain ⟨u,hu,he⟩ := hsubset ⟨t,ht,rfl⟩
          refine ⟨u,hu,?_⟩
          change p u = F.symm (d' t)
          rw [← he]
          exact (F.symm_apply_apply (p u)).symm
      obtain ⟨p1,hH1,hp1,hP1,l1,hl10,hl11,hfin1,htail1⟩ :=
        prefixProducer oa ob old hi hf p hp hne P hPf hpp
      have hp1r : Function.Injective p1.symm := by
        intro t u he
        exact unitInterval.symm_bijective.injective (hp1 he)
      have hP1r : Disjoint (Set.range p1.symm) P := by rwa [Path.symm_range]
      obtain ⟨r,hHr,hri,hPr,l2,hl20,hl21,hfin2,htail2⟩ :=
        prefixProducer oa ob old hi hf p1.symm hp1r hne.symm P hPf hP1r
      let d := r.symm
      have hHd : Path.Homotopic p d := hH1.trans (by simpa only [Path.symm_symm] using hHr.symm₂)
      have hdi : Function.Injective d := by
        intro t u he
        exact unitInterval.symm_bijective.injective (hri he)
      have hPd : Disjoint (Set.range d) P := by rwa [Path.symm_range]
      have hβ : (unitInterval.symm l1).val < 1 := by change 1-l1.val < 1; linarith
      obtain ⟨η,hη0,hη1,hret⟩ := htail2 (unitInterval.symm l1) hβ
      have hηsym : 0 < (unitInterval.symm η).val := by change 0 < 1-η.val; linarith
      let lo : I := ⟨(unitInterval.symm η).val/2,by constructor <;> linarith [(unitInterval.symm η).property.1,(unitInterval.symm η).property.2]⟩
      let high : I := ⟨1-l2.val/2,by constructor <;> linarith [l2.property.1,l2.property.2]⟩
      have hlo0 : 0 < lo.val := by dsimp [lo]; linarith
      have hlogap : lo.val < high.val := by
        dsimp [lo,high]
        linarith [(unitInterval.symm η).property.2,l2.property.2]
      have hhigh1 : high.val < 1 := by dsimp [high]; linarith
      refine ⟨d,hHd,hdi,hPd,lo,high,hlo0,hlogap,hhigh1,?_,?_⟩
      · intro i
        apply (hfin1 i).subset
        rintro z ⟨hz,⟨t,ht,rfl⟩⟩
        have htη : η ≤ unitInterval.symm t := by
          change η.val ≤ 1-t.val
          have htt := ht.2
          change t.val ≤ (1-η.val)/2 at htt
          linarith [hη1]
        obtain ⟨u,hu,he⟩ := hret ⟨unitInterval.symm t,⟨htη,(unitInterval.symm t).property.2⟩,rfl⟩
        refine ⟨hz,unitInterval.symm u,⟨(unitInterval.symm u).property.1,?_⟩,he⟩
        change 1-u.val ≤ l1.val
        have huu := hu.1
        change 1-l1.val ≤ u.val at huu
        linarith
      · intro i
        apply (hfin2 i).subset
        rintro z ⟨hz,⟨t,ht,rfl⟩⟩
        refine ⟨hz,unitInterval.symm t,⟨(unitInterval.symm t).property.1,?_⟩,rfl⟩
        change 1-t.val ≤ l2.val
        have htt := ht.1
        change 1-l2.val/2 ≤ t.val at htt
        linarith [hl20]
    have hfJ (i j : J) (hij : i ≠ j) :
        (Set.range (r i.val) ∩ Set.range (r j.val)).Finite :=
      hf i.val i.property j.val j.property (fun he => hij (Subtype.ext he))
    obtain ⟨q1,hq1,hiq1,hq1dis,lo,high,hlo0,hlohigh,hhigh1,hprefix,hsuffix⟩ :=
      endpointProducer (fun i : J => a i.val) (fun i : J => b i.val)
        (fun i : J => r i.val) (fun i : J => hi i.val) hfJ q hiq (hne v)
        (P : Set S) P.finite_toSet hqdis
    -- Both fixed-endpoint germs now have finite whole contacts against every
    -- actual old path. The remaining goal is the compact middle chart mesh.
    suffices ∃ d : Path (a v) (b v), Path.Homotopic q1 d ∧
        Function.Injective d ∧
        ∀ i ∈ B, (Set.range (r i) ∩ Set.range d).Finite by
      obtain ⟨d,hd,hdi,hdf⟩ := this
      exact ⟨d,hq.trans (hq1.trans hd),hdi,hdf⟩
    have clearParameter {S J : Type} [TopologicalSpace S] [Fintype J]
        {a b : S} (p : Path a b) (hp : Function.Injective p)
        (old : J → Set S) (lo high : I) (hgap : lo.val < high.val)
        (hfinite : ∀ i, (old i ∩ p '' Set.Icc lo high).Finite) :
        ∃ t : I, lo.val < t.val ∧ t.val < high.val ∧ ∀ i, p t ∉ old i := by
      classical
      let bad : Set I := ⋃ i, p ⁻¹' (old i ∩ p '' Set.Icc lo high)
      have hbad : bad.Finite := Set.finite_iUnion (fun i => (hfinite i).preimage hp.injOn)
      have hloI : lo < high := hgap
      have hinf : (Set.Ioo lo high).Infinite := Set.Ioo_infinite hloI
      obtain ⟨t,ht⟩ := (hinf.diff hbad).nonempty
      refine ⟨t,ht.1.1,ht.1.2,?_⟩
      intro i hi
      apply ht.2
      exact Set.mem_iUnion.mpr ⟨i,hi,t,⟨ht.1.1.le,ht.1.2.le⟩,rfl⟩
    have meshProducer {S J : Type} [TopologicalSpace S] [T2Space S]
        [ChartedSpace Plane S] [Fintype J]
        (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
        (hi : ∀ i, Function.Injective (old i))
        {a b : S} (p : Path a b) (hp : Function.Injective p)
        (havoid : Disjoint (Set.range p)
          (((⋃ i, ({oa i,ob i} : Set S)) ∪
             ⋃ ij : {ij : J × J // ij.1 ≠ ij.2},
               Set.range (old ij.val.1) ∩ Set.range (old ij.val.2)) \ {a,b}))
        (lo high : I) (hlo : 0 < lo.val) (hgap : lo.val < high.val)
        (hhigh : high.val < 1) :
        ∃ n : ℕ, ∃ hn : 0 < n,
          ∃ E : Fin n → OpenPartialHomeomorph S Plane,
          ∃ tag : Fin n → Option J,
          (∀ k, Set.range ((p.subpath lo high) ∘ intervalMeshParameter n hn k) ⊆ (E k).source) ∧
          ∀ k j z, z ∈ (E k).source →
            (z ∈ Set.range (old j) ↔ tag k = some j ∧ E k z 0 = 0) := by
      classical
      have interiorChart {S J : Type} [TopologicalSpace S] [T2Space S]
          [ChartedSpace Plane S] [Fintype J]
          (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
          (hi : ∀ i, Function.Injective (old i))
          {a b : S} (p : Path a b) (hp : Function.Injective p)
          (havoid : Disjoint (Set.range p)
            (((⋃ i, ({oa i,ob i} : Set S)) ∪
               ⋃ ij : {ij : J × J // ij.1 ≠ ij.2},
                 Set.range (old ij.val.1) ∩ Set.range (old ij.val.2)) \ {a,b}))
          (t : I) (ht0 : 0 < t.val) (ht1 : t.val < 1)
          (W : Set S) (hW : IsOpen W) (htW : p t ∈ W) :
          ∃ E : OpenPartialHomeomorph S Plane,
            p t ∈ E.source ∧ E.source ⊆ W ∧
            ∃ tag : Option J, ∀ j z, z ∈ E.source →
              (z ∈ Set.range (old j) ↔ tag = some j ∧ E z 0 = 0) := by
        classical
        have chartProducer {S J : Type} [TopologicalSpace S] [T2Space S]
            [ChartedSpace Plane S] [Fintype J]
            (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
            (hi : ∀ i, Function.Injective (old i))
            (x : S) (hend : ∀ i, x ≠ oa i ∧ x ≠ ob i)
            (hunique : ∀ i j, x ∈ Set.range (old i) → x ∈ Set.range (old j) → i = j)
            (W : Set S) (hW : IsOpen W) (hxW : x ∈ W) :
            ∃ E : OpenPartialHomeomorph S Plane,
              x ∈ E.source ∧ E.source ⊆ W ∧
              ∃ tag : Option J, ∀ j z, z ∈ E.source →
                (z ∈ Set.range (old j) ↔ tag = some j ∧ E z 0 = 0) := by
          classical
          have chartProducer (S : Type) [TopologicalSpace S]
              [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [T2Space S]
              {a b : S} (p : Path a b) (hp : Function.Injective p)
              (τ : I) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1)
              (W : Set S) (hW : IsOpen W) (hpW : p τ ∈ W) :
              ∃ E : OpenPartialHomeomorph S Plane,
                p τ ∈ E.source ∧ E.source ⊆ W ∧
                ∀ x ∈ E.source, x ∈ Set.range p ↔ E x 1 = 0 := by
            classical
            let e := chartAt Plane (p τ)
            have he : p τ ∈ e.source := mem_chart_source Plane (p τ)
            let q : ℝ → S := p ∘ Set.projIcc 0 1 zero_le_one
            have hqc : Continuous q := p.continuous.comp continuous_projIcc
            have hqt : q (τ : ℝ) = p τ := by
              dsimp [q]
              congr 1
              exact Subtype.ext (by simp [Set.projIcc_of_mem, τ.property])
            have hn : q ⁻¹' (W ∩ e.source) ∈ nhds (τ : ℝ) :=
              hqc.continuousAt.preimage_mem_nhds (by
                rw [hqt]
                exact (hW.inter e.open_source).mem_nhds ⟨hpW,he⟩)
            obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hn
            let ε : ℝ := min ρ (min (τ:ℝ) (1-(τ:ℝ))) / 2
            have hε : 0 < ε := by dsimp [ε]; positivity
            have hερ : ε < ρ := by dsimp [ε]; linarith [min_le_left ρ (min (τ:ℝ) (1-(τ:ℝ)))]
            have hετ : ε < (τ:ℝ) := by
              have hh := (min_le_right ρ (min (τ:ℝ) (1-(τ:ℝ)))).trans
                (min_le_left (τ:ℝ) (1-(τ:ℝ)))
              dsimp [ε]; linarith
            have hε1 : ε < 1-(τ:ℝ) := by
              have hh := (min_le_right ρ (min (τ:ℝ) (1-(τ:ℝ)))).trans
                (min_le_right (τ:ℝ) (1-(τ:ℝ)))
              dsimp [ε]; linarith
            let l : ℝ := (τ:ℝ)-ε
            let r : ℝ := (τ:ℝ)+ε
            have hl : 0 < l := by dsimp [l]; linarith
            have hlr : l < r := by dsimp [l,r]; linarith
            have hr : r < 1 := by dsimp [r]; linarith
            have hs : q '' Set.Icc l r ⊆ W ∩ e.source := by
              rintro _ ⟨t,ht,rfl⟩
              apply hball
              rw [Metric.mem_ball, Real.dist_eq, abs_lt]
              dsimp [l,r] at ht
              constructor <;> linarith [ht.1,ht.2]
            obtain ⟨E,hEW,hSquare,hseg,hleft,hright,haxis,hbox⟩ :=
              actual_interval_subarc_crosscut_chart (S:=S) p p.continuous
                (fun t u h => Or.inl (hp h)) l r hl hlr hr e W hW hs
            refine ⟨E,?_,fun x hx => (hEW hx).1,haxis⟩
            apply hseg
            exact ⟨(τ:ℝ),by dsimp [l,r]; constructor <;> linarith,hqt⟩
          have hclosed (j : J) : IsClosed (Set.range (old j)) :=
            (isCompact_range (old j).continuous).isClosed
          let L : Plane ≃ₜ ℝ × ℝ :=
            ((EuclideanSpace.equiv (Fin 2) ℝ).trans
              (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
          let flip : Plane ≃ₜ Plane := (L.trans (Homeomorph.prodComm ℝ ℝ)).trans L.symm
          have hflip (z : Plane) : flip z 0 = z 1 := rfl
          by_cases hex : ∃ i : J, x ∈ Set.range (old i)
          · obtain ⟨i,hxi⟩ := hex
            let other : Set S := ⋃ j : {j : J // j ≠ i}, Set.range (old j.val)
            have hother : IsClosed other := isClosed_iUnion_of_finite (fun j => hclosed j.val)
            have hxother : x ∉ other := by
              intro hh
              obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
              exact j.property (hunique j.val i hj hxi)
            obtain ⟨τ,hτ⟩ := hxi
            have hτ0 : 0 < τ.val := by
              have hn : τ.val ≠ 0 := by
                intro he
                have heτ : τ = 0 := Subtype.ext he
                rw [heτ,(old i).source] at hτ
                exact (hend i).1 hτ.symm
              exact lt_of_le_of_ne τ.property.1 hn.symm
            have hτ1 : τ.val < 1 := by
              have hn : τ.val ≠ 1 := by
                intro he
                have heτ : τ = 1 := Subtype.ext he
                rw [heτ,(old i).target] at hτ
                exact (hend i).2 hτ.symm
              exact lt_of_le_of_ne τ.property.2 hn
            obtain ⟨E0,hpE0,hE0W,hflat⟩ := chartProducer S (old i) (hi i) τ hτ0 hτ1
              (W ∩ otherᶜ) (hW.inter hother.isOpen_compl) (hτ.symm ▸ ⟨hxW,hxother⟩)
            let E := E0.trans flip.toOpenPartialHomeomorph
            have hsource : E.source = E0.source := by ext z; simp [E,OpenPartialHomeomorph.trans_source]
            refine ⟨E,?_,?_,some i,?_⟩
            · rw [hsource,← hτ]; exact hpE0
            · intro z hz
              exact (hE0W (hsource ▸ hz)).1
            · intro j z hz
              have hz0 : z ∈ E0.source := hsource ▸ hz
              have hcoord : E z 0 = E0 z 1 := hflip (E0 z)
              by_cases hij : i = j
              · subst j
                simpa only [Option.some.injEq,eq_self,true_and,hcoord] using hflat z hz0
              · have hnot : z ∉ Set.range (old j) := by
                  intro hj
                  exact (hE0W hz0).2 (Set.mem_iUnion.mpr ⟨⟨j,Ne.symm hij⟩,hj⟩)
                simp only [Option.some.injEq,hij,false_and,iff_false]
                exact hnot
          · let other : Set S := ⋃ j, Set.range (old j)
            have hother : IsClosed other := isClosed_iUnion_of_finite hclosed
            have hxother : x ∉ other := by
              intro hh
              obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
              exact hex ⟨j,hj⟩
            let O := W ∩ otherᶜ
            have hO : IsOpen O := hW.inter hother.isOpen_compl
            let e0 := chartAt Plane x
            let E := e0.restr O
            have hsource : E.source = e0.source ∩ O := e0.restr_source' O hO
            refine ⟨E,?_,?_,none,?_⟩
            · rw [hsource]; exact ⟨mem_chart_source Plane x,hxW,hxother⟩
            · intro z hz
              exact (hsource ▸ hz).2.1
            · intro j z hz
              have hnot : z ∉ Set.range (old j) := fun hj =>
                (hsource ▸ hz).2.2 (Set.mem_iUnion.mpr ⟨j,hj⟩)
              constructor
              · intro hj; exact False.elim (hnot hj)
              · rintro ⟨h,_⟩; cases h
        have hpa : p t ≠ a := by
          intro h
          have he : t = 0 := hp (h.trans p.source.symm)
          have hv := congrArg Subtype.val he
          change t.val = (0 : ℝ) at hv
          linarith
        have hpb : p t ≠ b := by
          intro h
          have he : t = 1 := hp (h.trans p.target.symm)
          have hv := congrArg Subtype.val he
          change t.val = (1 : ℝ) at hv
          linarith
        have hnot : p t ∉ (((⋃ i, ({oa i,ob i} : Set S)) ∪
               ⋃ ij : {ij : J × J // ij.1 ≠ ij.2},
                 Set.range (old ij.val.1) ∩ Set.range (old ij.val.2))) := by
          intro hh
          apply Set.disjoint_left.mp havoid (Set.mem_range_self t)
          exact ⟨hh, by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using And.intro hpa hpb⟩
        have hend : ∀ i, p t ≠ oa i ∧ p t ≠ ob i := by
          intro i
          constructor
          · intro h
            apply hnot
            exact Or.inl (Set.mem_iUnion.mpr ⟨i,Or.inl h⟩)
          · intro h
            apply hnot
            exact Or.inl (Set.mem_iUnion.mpr ⟨i,Or.inr (Set.mem_singleton_iff.mpr h)⟩)
        have hunique : ∀ i j, p t ∈ Set.range (old i) → p t ∈ Set.range (old j) → i = j := by
          intro i j hi hj
          by_contra hij
          apply hnot
          exact Or.inr (Set.mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hi,hj⟩)
        exact chartProducer oa ob old hi (p t) hend hunique W hW htW
      have meshProducer {S A : Type} [TopologicalSpace S]
          (η : C(I,S)) (U : A → Set S) (hU : ∀ i, IsOpen (U i))
          (hcover : Set.range η ⊆ ⋃ i, U i) :
          ∃ n : ℕ, ∃ hn : 0 < n, ∀ k : Fin n, ∃ i : A,
            Set.range (η ∘ intervalMeshParameter n hn k) ⊆ U i := by
        classical
        let V : A → Set I := fun i => η ⁻¹' U i
        have hV : ∀ i, IsOpen (V i) := fun i => (hU i).preimage η.continuous
        have hc : Set.univ ⊆ ⋃ i, V i := by
          intro t ht
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hcover (Set.mem_range_self t))
          exact Set.mem_iUnion.mpr ⟨i,hi⟩
        obtain ⟨δ,hδ,hballs⟩ := lebesgue_number_lemma_of_metric isCompact_univ hV hc
        obtain ⟨N,hN⟩ := exists_nat_one_div_lt hδ
        let n := N+1
        have hn : 0 < n := by dsimp [n]; omega
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hnδ : 1 / (n : ℝ) < δ := by simpa only [n,Nat.cast_add,Nat.cast_one] using hN
        refine ⟨n,hn,?_⟩
        intro k
        obtain ⟨i,hi⟩ := hballs (intervalMeshParameter n hn k 0) (Set.mem_univ _)
        refine ⟨i,?_⟩
        rintro _ ⟨t,rfl⟩
        apply hi
        rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
        have he : ((intervalMeshParameter n hn k t : I) : ℝ) -
            ((intervalMeshParameter n hn k 0 : I) : ℝ) = (t:ℝ)/n := by
          change ((k.val:ℝ)+(t:ℝ))/n - ((k.val:ℝ)+0)/n = (t:ℝ)/n
          ring
        rw [he,abs_of_nonneg (div_nonneg t.property.1 hnR.le)]
        exact (div_le_div_of_nonneg_right t.property.2 hnR.le).trans_lt hnδ
      let τ : I → I := fun t => ⟨(1-(t:ℝ))*lo.val+(t:ℝ)*high.val,by
        constructor
        · nlinarith [lo.property.1,t.property.1,t.property.2,high.property.1]
        · nlinarith [lo.property.2,t.property.1,t.property.2,high.property.2]⟩
      have hτ0 (t : I) : 0 < (τ t).val := by
        dsimp [τ]
        nlinarith [t.property.1,t.property.2]
      have hτ1 (t : I) : (τ t).val < 1 := by
        dsimp [τ]
        nlinarith [t.property.1,t.property.2]
      have hsub (t : I) : (p.subpath lo high) t = p (τ t) := rfl
      have hcharts : ∀ t : I, ∃ E : OpenPartialHomeomorph S Plane,
          (p.subpath lo high) t ∈ E.source ∧
          ∃ tag : Option J, ∀ j z, z ∈ E.source →
            (z ∈ Set.range (old j) ↔ tag = some j ∧ E z 0 = 0) := by
        intro t
        obtain ⟨E,hE,_,tag,htag⟩ := interiorChart oa ob old hi p hp havoid
          (τ t) (hτ0 t) (hτ1 t) Set.univ isOpen_univ (Set.mem_univ _)
        exact ⟨E,hsub t ▸ hE,tag,htag⟩
      choose e he tags htags using hcharts
      let η : C(I,S) := (p.subpath lo high).toContinuousMap
      have hcover : Set.range η ⊆ ⋃ t : I, (e t).source := by
        rintro _ ⟨t,rfl⟩
        exact Set.mem_iUnion.mpr ⟨t,he t⟩
      obtain ⟨n,hn,hmesh⟩ := meshProducer η (fun t => (e t).source)
        (fun t => (e t).open_source) hcover
      choose center hcenter using hmesh
      exact ⟨n,hn,fun k => e (center k),fun k => tags (center k),hcenter,
        fun k => htags (center k)⟩
    have internalSeamProducer {S J : Type} [TopologicalSpace S]
        [ChartedSpace Plane S] [ClosedSurface S] [Fintype J]
        (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
        (hi : ∀ i, Function.Injective (old i))
        {a b : S} (p : Path a b) (hp : Function.Injective p)
        (havoid : Disjoint (Set.range p)
          (((⋃ i, ({oa i,ob i} : Set S)) ∪
             ⋃ ij : {ij : J × J // ij.1 ≠ ij.2},
               Set.range (old ij.val.1) ∩ Set.range (old ij.val.2)) \ {a,b}))
        (lo high : I) (hlo : 0 < lo.val) (hgap : lo.val < high.val)
        (hhigh : high.val < 1)
        (n : ℕ) (hn : 0 < n) (e : Fin n → OpenPartialHomeomorph S Plane)
        (hends : ∀ i, p lo ∉ Set.range (old i) ∧ p high ∉ Set.range (old i))
        (hchart : ∀ k, Set.range ((p.subpath lo high) ∘ intervalMeshParameter n hn k) ⊆ (e k).source) :
        ∃ H : AmbientIsotopy S,
          (∀ t u : I, u.val ≤ lo.val ∨ high.val ≤ u.val → H.map (t,p u) = p u) ∧
          (∀ k, H.finalMap ((p.subpath lo high) (intervalMeshParameter n hn k 0)) ∉ ⋃ i, Set.range (old i)) ∧
          (∀ k, H.finalMap ((p.subpath lo high) (intervalMeshParameter n hn k 1)) ∉ ⋃ i, Set.range (old i)) ∧
          ∀ k t, (fun x => H.map (t,x)) '' Set.range ((p.subpath lo high) ∘ intervalMeshParameter n hn k) ⊆ (e k).source := by
      classical
      have seamProducer {S J K L : Type} [TopologicalSpace S]
          [ChartedSpace Plane S] [ClosedSurface S] [Fintype J] [Fintype K] [Fintype L]
          (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
          (hi : ∀ i, Function.Injective (old i))
          (p : K → S) (hpi : Function.Injective p)
          (hend : ∀ k i, p k ≠ oa i ∧ p k ≠ ob i)
          (hunique : ∀ k i j, p k ∈ Set.range (old i) → p k ∈ Set.range (old j) → i = j)
          (arc : L → C(I,S)) (e : L → OpenPartialHomeomorph S Plane)
          (hchart : ∀ i, Set.range (arc i) ⊆ (e i).source)
          (W : K → Set S) (hW : ∀ k, IsOpen (W k))
          (hseamW : ∀ k, p k ∈ W k) :
          ∃ U : K → Set S, ∃ H : AmbientIsotopy S,
            (∀ k, IsOpen (U k)) ∧
            (∀ k, p k ∈ U k) ∧ (∀ k, U k ⊆ W k) ∧
            (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
            (∀ k i, p k ∈ Set.range (arc i) → U k ⊆ (e i).source) ∧
            (∀ k i, p k ∉ Set.range (arc i) → Disjoint (U k) (Set.range (arc i))) ∧
            (∀ k j, H.finalMap (p k) ∉ Set.range (old j)) ∧
            (∀ t x, x ∉ ⋃ k, U k → H.map (t,x) = x) ∧
            (∀ k t x, x ∈ U k → H.map (t,x) ∈ U k) ∧
            (∀ i t, (fun x => H.map (t,x)) '' Set.range (arc i) ⊆ (e i).source) := by
        classical
        have familyMover {S J : Type} [TopologicalSpace S]
            [ChartedSpace Plane S] [ClosedSurface S] [Fintype J]
            (oa ob : J → S) (old : (i : J) → Path (oa i) (ob i))
            (hi : ∀ i, Function.Injective (old i))
            (x : S) (hend : ∀ i, x ≠ oa i ∧ x ≠ ob i)
            (hunique : ∀ i j, x ∈ Set.range (old i) → x ∈ Set.range (old j) → i = j)
            (W : Set S) (hW : IsOpen W) (hxW : x ∈ W) :
            ∃ G : AmbientIsotopy S,
              (∀ i, G.finalMap x ∉ Set.range (old i)) ∧
              (∀ t y, y ∉ W → G.map (t,y) = y) := by
          classical
          have oneArcMover (S : Type) [TopologicalSpace S]
              [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [ClosedSurface S]
              {a b : S} (p : Path a b) (hp : Function.Injective p)
              (z : S) (hz : z ∈ Set.range p) (hza : z ≠ a) (hzb : z ≠ b)
              (W : Set S) (hW : IsOpen W) (hzW : z ∈ W) :
              ∃ G : AmbientIsotopy S, G.finalMap z ∉ Set.range p ∧
                ∀ t x, x ∉ W → G.map (t,x) = x := by
            classical
            obtain ⟨τ,rfl⟩ := hz
            have hτ0 : 0 < τ.val := by
              by_contra hh
              have he : τ = 0 := Subtype.ext (le_antisymm (le_of_not_gt hh) τ.property.1)
              exact hza (by rw [he]; exact p.source)
            have hτ1 : τ.val < 1 := by
              by_contra hh
              have he : τ = 1 := Subtype.ext (le_antisymm τ.property.2 (le_of_not_gt hh))
              exact hzb (by rw [he]; exact p.target)
            have chart (τ : I) (hτ0 : 0 < τ.val) (hτ1 : τ.val < 1)
                (W : Set S) (hW : IsOpen W) (hpW : p τ ∈ W) :
                ∃ E : OpenPartialHomeomorph S Plane,
                  p τ ∈ E.source ∧ E.source ⊆ W ∧
                  ∀ x ∈ E.source, x ∈ Set.range p ↔ E x 1 = 0 := by
              classical
              let e := chartAt Plane (p τ)
              have he : p τ ∈ e.source := mem_chart_source Plane (p τ)
              let q : ℝ → S := p ∘ Set.projIcc 0 1 zero_le_one
              have hqc : Continuous q := p.continuous.comp continuous_projIcc
              have hqt : q (τ : ℝ) = p τ := by
                dsimp [q]
                congr 1
                exact Subtype.ext (by simp [Set.projIcc_of_mem, τ.property])
              have hn : q ⁻¹' (W ∩ e.source) ∈ nhds (τ : ℝ) :=
                hqc.continuousAt.preimage_mem_nhds (by
                  rw [hqt]
                  exact (hW.inter e.open_source).mem_nhds ⟨hpW,he⟩)
              obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hn
              let ε : ℝ := min ρ (min (τ:ℝ) (1-(τ:ℝ))) / 2
              have hε : 0 < ε := by dsimp [ε]; positivity
              have hερ : ε < ρ := by dsimp [ε]; linarith [min_le_left ρ (min (τ:ℝ) (1-(τ:ℝ)))]
              have hετ : ε < (τ:ℝ) := by
                have hh := (min_le_right ρ (min (τ:ℝ) (1-(τ:ℝ)))).trans
                  (min_le_left (τ:ℝ) (1-(τ:ℝ)))
                dsimp [ε]; linarith
              have hε1 : ε < 1-(τ:ℝ) := by
                have hh := (min_le_right ρ (min (τ:ℝ) (1-(τ:ℝ)))).trans
                  (min_le_right (τ:ℝ) (1-(τ:ℝ)))
                dsimp [ε]; linarith
              let l : ℝ := (τ:ℝ)-ε
              let r : ℝ := (τ:ℝ)+ε
              have hl : 0 < l := by dsimp [l]; linarith
              have hlr : l < r := by dsimp [l,r]; linarith
              have hr : r < 1 := by dsimp [r]; linarith
              have hs : q '' Set.Icc l r ⊆ W ∩ e.source := by
                rintro _ ⟨t,ht,rfl⟩
                apply hball
                rw [Metric.mem_ball, Real.dist_eq, abs_lt]
                dsimp [l,r] at ht
                constructor <;> linarith [ht.1,ht.2]
              obtain ⟨E,hEW,hSquare,hseg,hleft,hright,haxis,hbox⟩ :=
                actual_interval_subarc_crosscut_chart (S:=S) p p.continuous
                  (fun t u h => Or.inl (hp h)) l r hl hlr hr e W hW hs
              refine ⟨E,?_,fun x hx => (hEW hx).1,haxis⟩
              apply hseg
              exact ⟨(τ:ℝ),by dsimp [l,r]; constructor <;> linarith,hqt⟩
            have push (U : Set S) (V : Set Plane) (hU : IsOpen U) (e : U ≃ₜ V)
                (p v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < 1)
                (hCV : Metric.closedBall p (2*R) ⊆ V) :
                ∃ G : AmbientIsotopy S,
                  (∀ t (x : U), dist (e x).val p ≤ R →
                    ∃ y : U, G.map (t,x.val) = y.val ∧
                      (e y).val = (e x).val + (t:ℝ) • (R • v)) ∧
                  (∀ t x, x ∉ U → G.map (t,x) = x) := by
              have push (p v : Plane) (R : ℝ) (hR : 0 < R) (hv : ‖v‖ < 1) :
                  ∃ H : AmbientIsotopy Plane,
                    (∀ t x, dist x p ≤ R → H.map (t,x) = x + (t:ℝ) • (R • v)) ∧
                    (∀ t x, 2*R ≤ dist x p → H.map (t,x) = x) := by
                classical
                have hsmall (f : Plane → Plane)
                      (c : ℝ≥0) (hc : (c : ℝ) < 1) (hf : LipschitzWith c f) :
                      ∃ H : AmbientIsotopy Plane,
                        (∀ t x, H.map (t, x) = x + (t : ℝ) • f x) ∧
                        (∀ t x, f x = 0 → H.map (t, x) = x) := by
                  classical
                  let F : Interval × Plane → Plane :=
                    fun p => p.2 + (p.1 : ℝ) • f p.2
                  have hF : Continuous F := continuous_snd.add
                    ((continuous_subtype_val.comp continuous_fst).smul
                      (hf.continuous.comp continuous_snd))
                  refine ⟨{ map := ⟨F, hF⟩, homeomorphism_at := ?_, at_zero := ?_ },
                    fun t x => rfl, ?_⟩
                  · intro t
                    have happ : ApproximatesLinearOn (fun x => F (t, x))
                        (ContinuousLinearEquiv.refl ℝ Plane : Plane →L[ℝ] Plane)
                        Set.univ c := by
                      intro x _ y _
                      have heq : F (t, x) - F (t, y) - (x - y) =
                          (t : ℝ) • (f x - f y) := by dsimp [F]; module
                      change ‖F (t, x) - F (t, y) - (x - y)‖ ≤ _
                      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
                      calc
                        (t : ℝ) * ‖f x - f y‖ ≤ 1 * ‖f x - f y‖ :=
                          mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
                        _ ≤ c * ‖x - y‖ := by simpa [dist_eq_norm] using hf.dist_le_mul x y
                    let e := happ.toHomeomorph (fun x => F (t, x)) (Or.inr (by simpa using hc))
                    exact ⟨e, fun x => rfl⟩
                  · intro x
                    simp [F]
                  · intro t x hx
                    change x + (t : ℝ) • f x = x
                    simp [hx]
              
                let b : Plane → ℝ := fun x => max (min (2*R - dist x p) R) 0
                have hb0 : LipschitzWith 1 (fun x : Plane => 2*R - dist x p) := by
                  apply LipschitzWith.of_dist_le_mul
                  intro x y
                  simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
                    sub_sub_sub_cancel_left, abs_sub_comm] using abs_dist_sub_le x y p
                have hb : LipschitzWith 1 b := (hb0.min_const R).max_const 0
                let f : Plane → Plane := fun x => b x • v
                have hf : LipschitzWith ‖v‖₊ f := by
                  apply LipschitzWith.of_dist_le_mul
                  intro x y
                  change ‖b x • v - b y • v‖ ≤ ‖v‖ * dist x y
                  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
                  have h := hb.dist_le_mul x y
                  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h
                  calc
                    |b x - b y| * ‖v‖ ≤ dist x y * ‖v‖ :=
                      mul_le_mul_of_nonneg_right h (norm_nonneg _)
                    _ = ‖v‖ * dist x y := mul_comm _ _
                obtain ⟨H,hH,hfix⟩ := hsmall f ‖v‖₊ hv hf
                refine ⟨H, ?_, ?_⟩
                · intro t x hx
                  rw [hH]
                  have hb : b x = R := by
                    simp only [b, min_eq_right (by linarith : R ≤ 2*R-dist x p),
                      max_eq_left hR.le]
                  simp only [f,hb]
                · intro t x hx
                  apply hfix
                  have hm : min (2*R-dist x p) R ≤ 0 :=
                    (min_le_left _ _).trans (by linarith)
                  simp only [f,b,max_eq_right hm,zero_smul]
              obtain ⟨H,hH,hfix⟩ := push p v R hR hv
              obtain ⟨K,G,hcoord,hGU,hGfix⟩ := position_surface_chart_lift S U V hU e
                (Metric.closedBall p (2*R)) (isCompact_closedBall _ _) hCV H (by
                  intro t x hx
                  apply hfix
                  exact le_of_lt (lt_of_not_ge (by simpa only [Metric.mem_closedBall] using hx)))
              refine ⟨G, ?_, hGfix⟩
              intro t x hx
              refine ⟨K.map (t,x), hGU t x, ?_⟩
              rw [hcoord]
              exact hH t (e x).val hx
            obtain ⟨E,hpE,hEW,haxis⟩ := chart τ hτ0 hτ1 W hW hzW
            obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
              (E.open_target.mem_nhds (E.map_source hpE))
            let R : ℝ := δ/4
            have hR : 0 < R := by dsimp [R]; positivity
            have hCV : Metric.closedBall (E (p τ)) (2*R) ⊆ E.target := by
              apply Set.Subset.trans (Metric.closedBall_subset_ball ?_) hball
              dsimp [R]
              linarith
            let v : Plane := Plane.mk 0 (1/2)
            have hv : ‖v‖ < 1 := by
              norm_num [v, EuclideanSpace.norm_eq, Fin.sum_univ_two, Plane.mk]
            obtain ⟨G,hmove,hfix⟩ := push E.source E.target E.open_source
              E.toHomeomorphSourceTarget (E (p τ)) v R hR hv hCV
            obtain ⟨y,hy,hEy⟩ := hmove (1 : I) ⟨p τ,hpE⟩ (by simp; exact hR.le)
            have hz0 : E (p τ) 1 = 0 := (haxis _ hpE).mp ⟨τ,rfl⟩
            have hEq : E y.val = E (p τ) + R • v := by simpa using hEy
            refine ⟨G,?_,fun t x hx => hfix t x (fun he => hx (hEW he))⟩
            intro hm
            change G.map (1,p τ) ∈ Set.range p at hm
            rw [hy] at hm
            have hy0 : E y.val 1 = 0 := (haxis _ y.property).mp hm
            have hh := congrArg (fun x : Plane => x 1) hEq
            simp [v,Plane.mk,hz0,hy0] at hh
            linarith
          by_cases hex : ∃ i, x ∈ Set.range (old i)
          · obtain ⟨i,hxi⟩ := hex
            let other : Set S := ⋃ j : {j : J // j ≠ i}, Set.range (old j.val)
            have hother : IsClosed other := isClosed_iUnion_of_finite (fun j =>
              (isCompact_range (old j.val).continuous).isClosed)
            have hxother : x ∉ other := by
              intro hh
              obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
              exact j.property (hunique j.val i hj hxi)
            let V := W ∩ otherᶜ
            have hV : IsOpen V := hW.inter hother.isOpen_compl
            obtain ⟨G,hG,hfix⟩ := oneArcMover S (old i) (hi i) x hxi
              (hend i).1 (hend i).2 V hV ⟨hxW,hxother⟩
            have hstay : G.finalMap x ∈ V := by
              by_contra hn
              obtain ⟨e,he⟩ := G.homeomorphism_at (1:I)
              have heq : e (G.finalMap x) = e x := by
                rw [he,he]
                exact hfix 1 (G.finalMap x) hn
              have hxV : x ∈ V := ⟨hxW,hxother⟩
              exact hn ((e.injective heq).symm ▸ hxV)
            refine ⟨G,?_,?_⟩
            · intro j
              by_cases hij : j = i
              · subst j; exact hG
              · intro hj
                exact hstay.2 (Set.mem_iUnion.mpr ⟨⟨j,hij⟩,hj⟩)
            · intro t y hy
              exact hfix t y (fun hv => hy hv.1)
          · let G : AmbientIsotopy S :=
              { map := ⟨fun z => z.2, continuous_snd⟩
                homeomorphism_at := fun t => ⟨Homeomorph.refl S,fun y => rfl⟩
                at_zero := fun y => rfl }
            refine ⟨G,?_,fun t y hy => rfl⟩
            intro i hi
            exact hex ⟨i,hi⟩
        have hCclosed (i : L) : IsClosed (Set.range (arc i)) :=
          (isCompact_range (arc i).continuous).isClosed
        let V : K → L → Set S := fun k i =>
          if p k ∈ Set.range (arc i) then (e i).source else (Set.range (arc i))ᶜ
        have hVopen (k : K) (i : L) : IsOpen (V k i) := by
          dsimp [V]
          split
          · exact (e i).open_source
          · exact (hCclosed i).isOpen_compl
        have hpV (k : K) (i : L) : p k ∈ V k i := by
          dsimp [V]
          split
          · rename_i h; exact hchart i h
          · assumption
        obtain ⟨D,hD,hDdis⟩ := (Set.finite_range p).t2_separation
        let U : K → Set S := fun k => W k ∩ (D (p k) ∩ ⋂ i, V k i)
        have hUopen (k : K) : IsOpen (U k) :=
          (hW k).inter ((hD (p k)).2.inter (isOpen_iInter_of_finite (hVopen k)))
        have hpU (k : K) : p k ∈ U k :=
          ⟨hseamW k,(hD (p k)).1,Set.mem_iInter.mpr (hpV k)⟩
        have hUW (k : K) : U k ⊆ W k := Set.inter_subset_left
        have hUdis (k l : K) (hkl : k ≠ l) : Disjoint (U k) (U l) :=
          (hDdis (Set.mem_range_self k) (Set.mem_range_self l)
            (fun h => hkl (hpi h))).mono
            (fun x hx => hx.2.1) (fun x hx => hx.2.1)
        have hinc (k : K) (i : L) (hki : p k ∈ Set.range (arc i)) : U k ⊆ (e i).source := by
          intro x hx
          have hv := Set.mem_iInter.mp hx.2.2 i
          simpa only [V,if_pos hki] using hv
        have hmiss (k : K) (i : L) (hki : p k ∉ Set.range (arc i)) :
            Disjoint (U k) (Set.range (arc i)) := by
          rw [Set.disjoint_left]
          intro x hx hxi
          have hv := Set.mem_iInter.mp hx.2.2 i
          have hn : x ∉ Set.range (arc i) := by simpa only [V,if_neg hki,Set.mem_compl_iff] using hv
          exact hn hxi
        have hid : ∃ H : AmbientIsotopy S, ∀ t x, H.map (t,x) = x := by
          exact ⟨{ map := ⟨fun z => z.2, continuous_snd⟩,
                    homeomorphism_at := fun t => ⟨Homeomorph.refl S,fun x => rfl⟩,
                    at_zero := fun x => rfl },fun t x => rfl⟩
        have hcomp (H G : AmbientIsotopy S) :
            ∃ K : AmbientIsotopy S, ∀ t x, K.map (t,x) = G.map (t,H.map (t,x)) := by
          refine ⟨{ map := ⟨fun z => G.map (z.1,H.map z),
            G.map.continuous.comp (continuous_fst.prodMk H.map.continuous)⟩,
                    homeomorphism_at := ?_,at_zero := ?_ },fun t x => rfl⟩
          · intro t
            obtain ⟨e,he⟩ := H.homeomorphism_at t
            obtain ⟨f,hf⟩ := G.homeomorphism_at t
            exact ⟨e.trans f,fun x => (hf (e x)).trans
              (congrArg (fun y => G.map (t,y)) (he x))⟩
          · intro x
            change G.map (⟨0,by norm_num⟩,H.map (⟨0,by norm_num⟩,x)) = x
            rw [H.at_zero,G.at_zero]
        have hstay (G : AmbientIsotopy S) (k : K)
            (hfix : ∀ t x, x ∉ U k → G.map (t,x) = x) :
            ∀ t x, x ∈ U k → G.map (t,x) ∈ U k := by
          intro t x hx
          by_contra hn
          obtain ⟨e,he⟩ := G.homeomorphism_at t
          have heq : e (G.map (t,x)) = e x := by
            rw [he,he]
            exact hfix t (G.map (t,x)) hn
          exact hn ((e.injective heq).symm ▸ hx)
        have hbuild (P : Finset K) : ∃ H : AmbientIsotopy S,
            (∀ k ∈ P, ∀ j, H.finalMap (p k) ∉ Set.range (old j)) ∧
            (∀ t x, x ∉ ⋃ k, U k → H.map (t,x) = x) ∧
            (∀ k t x, x ∈ U k → H.map (t,x) ∈ U k) ∧
            (∀ k, k ∉ P → ∀ t, H.map (t,p k) = p k) := by
          induction P using Finset.induction_on with
          | empty =>
            obtain ⟨H,hH⟩ := hid
            refine ⟨H,by simp,?_,?_,?_⟩
            · intro t x hx; exact hH t x
            · intro k t x hx; rwa [hH]
            · intro k hk t; exact hH t (p k)
          | @insert k P hkP ih =>
            obtain ⟨H,hHavoid,hHfix,hHstay,hHunprocessed⟩ := ih
            obtain ⟨G,hGavoid,hGfix⟩ := familyMover oa ob old hi
              (p k) (hend k) (hunique k) (U k) (hUopen k) (hpU k)
            have hGstay := hstay G k hGfix
            obtain ⟨K,hK⟩ := hcomp H G
            refine ⟨K,?_,?_,?_,?_⟩
            · intro l hl j
              rw [AmbientIsotopy.finalMap,hK]
              change G.finalMap (H.finalMap (p l)) ∉ Set.range (old j)
              rcases Finset.mem_insert.mp hl with rfl | hlP
              · have hHpk : H.finalMap (p l) = p l := hHunprocessed l hkP ⟨1,by norm_num⟩
                rw [hHpk]
                exact hGavoid j
              · have hlk : l ≠ k := by intro he; exact hkP (he ▸ hlP)
                have hpHU : H.finalMap (p l) ∈ U l := hHstay l ⟨1,by norm_num⟩ (p l) (hpU l)
                have hnUk : H.finalMap (p l) ∉ U k := fun hm =>
                  Set.disjoint_left.mp (hUdis l k hlk) hpHU hm
                have hGsame : G.finalMap (H.finalMap (p l)) = H.finalMap (p l) :=
                  hGfix ⟨1,by norm_num⟩ _ hnUk
                rw [hGsame]
                exact hHavoid l hlP j
            · intro t x hx
              rw [hK,hHfix t x hx]
              apply hGfix
              intro hxk
              exact hx (Set.mem_iUnion.mpr ⟨k,hxk⟩)
            · intro l t x hx
              rw [hK]
              have hxHU := hHstay l t x hx
              by_cases hlk : l = k
              · subst l; exact hGstay t _ hxHU
              · have hnUk : H.map (t,x) ∉ U k := fun hm =>
                  Set.disjoint_left.mp (hUdis l k hlk) hxHU hm
                rw [hGfix t _ hnUk]
                exact hxHU
            · intro l hl t
              have hlP : l ∉ P := fun h => hl (Finset.mem_insert_of_mem h)
              have hlk : l ≠ k := by intro h; exact hl (h ▸ Finset.mem_insert_self k P)
              rw [hK,hHunprocessed l hlP t]
              apply hGfix
              exact fun hm => Set.disjoint_left.mp (hUdis l k hlk) (hpU l) hm
        obtain ⟨H,hHavoid,hHfix,hHstay,hHunprocessed⟩ := hbuild Finset.univ
        refine ⟨U,H,hUopen,hpU,hUW,hUdis,hinc,hmiss,?_,hHfix,hHstay,?_⟩
        · intro k j; exact hHavoid k (Finset.mem_univ k) j
        · intro i t y hy
          obtain ⟨x,hx,rfl⟩ := hy
          by_cases hxU : x ∈ ⋃ k, U k
          · obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hxU
            have hpC : p k ∈ Set.range (arc i) := by
              by_contra hn
              exact Set.disjoint_left.mp (hmiss k i hn) hk hx
            exact hinc k i hpC (hHstay k t x hk)
          · change H.map (t,x) ∈ (e i).source
            rw [hHfix t x hxU]
            exact hchart i hx

      have hnR : (0:ℝ) < n := by exact_mod_cast hn
      let vertex : Fin (n-1) → I := fun j => ⟨((j.val:ℝ)+1)/n,by
        constructor
        · positivity
        · apply (div_le_one hnR).mpr
          exact_mod_cast (show j.val+1 ≤ n by omega)⟩
      let τ : Fin (n-1) → I := fun j => ⟨(1-(vertex j:ℝ))*lo.val+(vertex j:ℝ)*high.val,by
        constructor <;> nlinarith [(vertex j).property.1,(vertex j).property.2,lo.property.1,lo.property.2,high.property.1,high.property.2]⟩
      let point : Fin (n-1) → S := fun j => p (τ j)
      have hτlo (j) : lo.val < (τ j).val := by dsimp [τ,vertex]; have hj : 0 < ((j.val:ℝ)+1)/n := div_pos (by positivity) hnR; nlinarith
      have hτhigh (j) : (τ j).val < high.val := by dsimp [τ,vertex]; have hj : ((j.val:ℝ)+1)/n < 1 := (div_lt_one hnR).mpr (by exact_mod_cast (show j.val+1 < n by omega)); nlinarith
      have hpi : Function.Injective point := by
        intro j k h
        have hh := congrArg Subtype.val (hp h)
        change (1-(vertex j:ℝ))*lo.val+(vertex j:ℝ)*high.val =
          (1-(vertex k:ℝ))*lo.val+(vertex k:ℝ)*high.val at hh
        have hv : (vertex j:ℝ) = (vertex k:ℝ) := by nlinarith
        change ((j.val:ℝ)+1)/n = ((k.val:ℝ)+1)/n at hv
        have hhval := (div_left_inj' hnR.ne').mp hv
        exact Fin.ext (Nat.cast_injective (add_right_cancel hhval))
      have hpa (j) : point j ≠ a := by
        intro h
        have hh := congrArg Subtype.val (hp (h.trans p.source.symm))
        change (τ j).val = 0 at hh
        linarith [hτlo j]
      have hpb (j) : point j ≠ b := by
        intro h
        have hh := congrArg Subtype.val (hp (h.trans p.target.symm))
        change (τ j).val = 1 at hh
        linarith [hτhigh j]
      have hnot (j) : point j ∉ ((⋃ i, ({oa i,ob i} : Set S)) ∪
             ⋃ ij : {ij : J × J // ij.1 ≠ ij.2},
               Set.range (old ij.val.1) ∩ Set.range (old ij.val.2)) := by
        intro hh
        apply Set.disjoint_left.mp havoid (Set.mem_range_self (τ j))
        exact ⟨hh,by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using And.intro (hpa j) (hpb j)⟩
      have hend : ∀ j i, point j ≠ oa i ∧ point j ≠ ob i := by
        intro j i
        constructor
        · intro hh; exact hnot j (Or.inl (Set.mem_iUnion.mpr ⟨i,Or.inl hh⟩))
        · intro hh; exact hnot j (Or.inl (Set.mem_iUnion.mpr ⟨i,Or.inr hh⟩))
      have hunique : ∀ j i k, point j ∈ Set.range (old i) → point j ∈ Set.range (old k) → i = k := by
        intro j i k hi hk
        by_contra h
        exact hnot j (Or.inr (Set.mem_iUnion.mpr ⟨⟨(i,k),h⟩,hi,hk⟩))
      let T : Set I := {u | u.val ≤ lo.val ∨ high.val ≤ u.val}
      have hTc : IsClosed T := (isClosed_le continuous_subtype_val continuous_const).union
        (isClosed_le continuous_const continuous_subtype_val)
      let F : Set S := p '' T
      have hFc : IsClosed F := (hTc.isCompact.image p.continuous).isClosed
      have hpF (j) : point j ∉ F := by
        rintro ⟨u,hu,he⟩
        have hh : u = τ j := hp he
        rw [hh] at hu
        rcases hu with hu | hu <;> linarith [hτlo j,hτhigh j]
      let arc : Fin n → C(I,S) := fun k => ⟨(p.subpath lo high) ∘ intervalMeshParameter n hn k,
        (p.subpath lo high).continuous.comp (intervalMeshParameter_continuous n hn k)⟩
      obtain ⟨U,H,hU,hpoint,hUF,hdis,hinc,hmiss,hoff,hfix,hstay,hcharts⟩ :=
        seamProducer oa ob old hi point hpi hend hunique arc e hchart
          (fun _ => Fᶜ) (fun _ => hFc.isOpen_compl) hpF
      have hfixF : ∀ t u : I, u ∈ T → H.map (t,p u) = p u := by
        intro t u hu
        apply hfix
        intro hh
        obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
        exact hUF j hj ⟨u,hu,rfl⟩
      have hleft (k : Fin n) :
          H.finalMap ((p.subpath lo high) (intervalMeshParameter n hn k 0)) ∉ ⋃ i, Set.range (old i) := by
        by_cases hk : k.val = 0
        · have ht : intervalMeshParameter n hn k 0 = 0 := by
            apply Subtype.ext; simp [intervalMeshParameter,hk]
          rw [ht,(p.subpath lo high).source]
          change H.map (1,p lo) ∉ ⋃ i, Set.range (old i)
          rw [hfixF 1 lo (Or.inl le_rfl)]
          intro hh
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
          exact (hends i).1 hi
        · let j : Fin (n-1) := ⟨k.val-1,by omega⟩
          have hjv : (j.val:ℝ)+1 = k.val := by
            exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ k.val by omega))
          have heq : (p.subpath lo high) (intervalMeshParameter n hn k 0) = point j := by
            change p _ = p (τ j)
            congr 1
            apply Subtype.ext
            simp [τ,vertex,intervalMeshParameter,hjv]
          rw [heq]
          intro hh
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
          exact hoff j i hi
      have hright (k : Fin n) :
          H.finalMap ((p.subpath lo high) (intervalMeshParameter n hn k 1)) ∉ ⋃ i, Set.range (old i) := by
        by_cases hk : k.val+1 = n
        · have ht : intervalMeshParameter n hn k 1 = 1 := by
            apply Subtype.ext
            change ((k.val:ℝ)+1)/n = 1
            have hkr : (k.val:ℝ)+1 = n := by exact_mod_cast hk
            rw [hkr,div_self hnR.ne']
          rw [ht,(p.subpath lo high).target]
          change H.map (1,p high) ∉ ⋃ i, Set.range (old i)
          rw [hfixF 1 high (Or.inr le_rfl)]
          intro hh
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
          exact (hends i).2 hi
        · let j : Fin (n-1) := ⟨k.val,by omega⟩
          have heq : (p.subpath lo high) (intervalMeshParameter n hn k 1) = point j := by
            rfl
          rw [heq]
          intro hh
          obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hh
          exact hoff j i hi
      exact ⟨H,hfixF,hleft,hright,hcharts⟩
    have transportProducer {S : Type} [TopologicalSpace S] {a b : S}
        (p : Path a b) (hp : Function.Injective p) (H : AmbientIsotopy S)
        (ha : ∀ t, H.map (t,a) = a) (hb : ∀ t, H.map (t,b) = b) :
        ∃ q : Path a b, Path.Homotopic p q ∧ Function.Injective q ∧
          Set.range q = H.finalMap '' Set.range p ∧ ∀ t, q t = H.finalMap (p t) := by
      let q : Path a b := {
        toContinuousMap := ⟨fun t => H.finalMap (p t),
          H.map.continuous.comp (continuous_const.prodMk p.continuous)⟩
        source' := by change H.map (1,p 0) = a; rw [p.source,ha]
        target' := by change H.map (1,p 1) = b; rw [p.target,hb] }
      have hhom : Path.Homotopic p q := by
        refine ⟨{
          toHomotopy := {
            toContinuousMap := ⟨fun z => H.map (z.1,p z.2),
              H.map.continuous.comp (continuous_fst.prodMk (p.continuous.comp continuous_snd))⟩
            map_zero_left := fun t => H.at_zero (p t)
            map_one_left := fun t => rfl }
          prop' := ?_ }⟩
        intro t u hu
        rcases hu with rfl | hu
        · change H.map (t,p 0) = p 0
          rw [p.source,ha]
        · rw [Set.mem_singleton_iff] at hu
          subst u
          change H.map (t,p 1) = p 1
          rw [p.target,hb]
      have hi : Function.Injective q := by
        obtain ⟨e,he⟩ := H.homeomorphism_at (1 : I)
        intro t u h
        apply hp
        apply e.injective
        change H.map (1,p t) = H.map (1,p u) at h
        exact (he (p t)).trans (h.trans (he (p u)).symm)
      refine ⟨q,hhom,hi,?_,fun t => rfl⟩
      apply Set.Subset.antisymm
      · rintro _ ⟨t,rfl⟩
        exact ⟨p t,⟨t,rfl⟩,rfl⟩
      · rintro _ ⟨x,⟨t,rfl⟩,rfl⟩
        exact ⟨t,rfl⟩
    have havoidJ : Disjoint (Set.range q1)
        (((⋃ i : J, ({a i.val,b i.val} : Set S)) ∪
          ⋃ ij : {ij : J × J // ij.1 ≠ ij.2},
            Set.range (r ij.val.1.val) ∩ Set.range (r ij.val.2.val)) \ {a v,b v}) := by
      apply hq1dis.mono_right
      intro x hx
      change x ∈ P
      apply hPfinite.mem_toFinset.mpr
      refine ⟨?_,hx.2⟩
      rcases hx.1 with hh | hh
      · exact Or.inl hh
      · obtain ⟨ij,hij⟩ := Set.mem_iUnion.mp hh
        apply Or.inr
        exact Set.mem_iUnion.mpr ⟨⟨ij.val,fun h => ij.property (Subtype.ext h)⟩,hij⟩
    obtain ⟨l,hl0,hllo,hlclear⟩ := clearParameter q1 hiq1
      (fun i : J => Set.range (r i.val)) 0 lo hlo0 hprefix
    obtain ⟨u,hhighu,hu1,huclear⟩ := clearParameter q1 hiq1
      (fun i : J => Set.range (r i.val)) high 1 hhigh1 hsuffix
    have hlu : l.val < u.val := lt_trans hllo (lt_trans hlohigh hhighu)
    obtain ⟨n,hn,e,tag,hchart,haxis⟩ := meshProducer
      (fun i : J => a i.val) (fun i : J => b i.val)
      (fun i : J => r i.val) (fun i : J => hi i.val)
      q1 hiq1 havoidJ l u hl0 hlu hu1
    obtain ⟨H,hfix,hleft,hright,hcharts⟩ := internalSeamProducer
      (fun i : J => a i.val) (fun i : J => b i.val)
      (fun i : J => r i.val) (fun i : J => hi i.val)
      q1 hiq1 havoidJ l u hl0 hlu hu1 n hn e
      (fun i => ⟨hlclear i,huclear i⟩) hchart
    have hHa : ∀ t, H.map (t,a v) = a v := by
      intro t
      have hh := hfix t 0 (Or.inl l.property.1)
      simpa only [q1.source] using hh
    have hHb : ∀ t, H.map (t,b v) = b v := by
      intro t
      have hh := hfix t 1 (Or.inr u.property.2)
      simpa only [q1.target] using hh
    obtain ⟨q2,hq2,hiq2,hq2range,hq2point⟩ := transportProducer q1 hiq1 H hHa hHb
    suffices ∃ d : Path (a v) (b v), Path.Homotopic q2 d ∧
        Function.Injective d ∧ ∀ i ∈ B, (Set.range (r i) ∩ Set.range d).Finite by
      obtain ⟨d,hd,hdi,hdf⟩ := this
      exact ⟨d,hq2.trans hd,hdi,hdf⟩
    have repairedDataProducer {S J : Type} [TopologicalSpace S]
        {a b : S} (p q : Path a b) (hq : Function.Injective q)
        (old : J → Set S) (lo high : I) (hlo : 0 < lo.val)
        (hgap : lo.val < high.val) (hhigh : high.val < 1)
        (hleftFinite : ∀ j, (old j ∩ p '' Set.Icc 0 lo).Finite)
        (hrightFinite : ∀ j, (old j ∩ p '' Set.Icc high 1).Finite)
        (H : AmbientIsotopy S) (hpoint : ∀ t, q t = H.finalMap (p t))
        (hfix : ∀ t u : I, u.val ≤ lo.val ∨ high.val ≤ u.val → H.map (t,p u) = p u)
        (n : ℕ) (hn : 0 < n) (e : Fin n → OpenPartialHomeomorph S Plane)
        (hleft : ∀ k, H.finalMap ((p.subpath lo high) (intervalMeshParameter n hn k 0)) ∉ ⋃ i, old i)
        (hright : ∀ k, H.finalMap ((p.subpath lo high) (intervalMeshParameter n hn k 1)) ∉ ⋃ i, old i)
        (hcharts : ∀ k t, (fun x => H.map (t,x)) '' Set.range ((p.subpath lo high) ∘ intervalMeshParameter n hn k) ⊆ (e k).source) :
        ∃ η : C(I,S),
          Function.Injective η ∧
          (∀ t, η t = q ⟨lo.val+(high.val-lo.val)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩) ∧
          (Set.range η = q '' Set.Icc lo high) ∧
          (∀ k t, η (intervalMeshParameter n hn k t) ∈ (e k).source) ∧
          (∀ k j, η (intervalMeshParameter n hn k 0) ∉ old j ∧ η (intervalMeshParameter n hn k 1) ∉ old j) ∧
          (∀ j, (old j ∩ q '' Set.Icc 0 lo).Finite) ∧
          (∀ j, (old j ∩ q '' Set.Icc high 1).Finite) := by
      let η : C(I,S) := (q.subpath lo high).toContinuousMap
      have hηpoint (t : I) : η t = H.finalMap ((p.subpath lo high) t) := by
        change q _ = H.finalMap (p _)
        exact hpoint _
      refine ⟨η,?_,?_,?_,?_,?_,?_,?_⟩
      · intro t v h
        have hh := congrArg Subtype.val (hq h)
        change (1-t.val)*lo.val+t.val*high.val = (1-v.val)*lo.val+v.val*high.val at hh
        apply Subtype.ext
        nlinarith
      · intro t
        change q _ = q _
        congr 1
        apply Subtype.ext
        change (1-t.val)*lo.val+t.val*high.val = lo.val+(high.val-lo.val)*t.val
        ring
      · exact q.range_subpath_of_le lo high hgap.le
      · intro k t
        rw [hηpoint]
        exact hcharts k 1 ⟨(p.subpath lo high) (intervalMeshParameter n hn k t),⟨t,rfl⟩,rfl⟩
      · intro k j
        constructor
        · rw [hηpoint]
          exact fun hh => hleft k (Set.mem_iUnion.mpr ⟨j,hh⟩)
        · rw [hηpoint]
          exact fun hh => hright k (Set.mem_iUnion.mpr ⟨j,hh⟩)
      · intro j
        apply (hleftFinite j).subset
        rintro z ⟨hz,t,ht,rfl⟩
        refine ⟨hz,t,ht,?_⟩
        rw [hpoint]
        exact (hfix 1 t (Or.inl ht.2)).symm
      · intro j
        apply (hrightFinite j).subset
        rintro z ⟨hz,t,ht,rfl⟩
        refine ⟨hz,t,ht,?_⟩
        rw [hpoint]
        exact (hfix 1 t (Or.inr ht.1)).symm
    have clearCollarsProducer {S J K : Type} [TopologicalSpace S] [Fintype J] [Fintype K]
        (old : J → Set S) (hclosed : ∀ j, IsClosed (old j))
        (arc : K → C(I,S))
        (hends : ∀ k j, arc k 0 ∉ old j ∧ arc k 1 ∉ old j) :
        ∃ ε : ℝ, 0 < ε ∧ ε < 1/2 ∧
          ∀ k (t : I), (t:ℝ) ≤ ε ∨ 1-ε ≤ (t:ℝ) → ∀ j, arc k t ∉ old j := by
      classical
      let zero : I := ⟨0,by norm_num⟩
      let one : I := ⟨1,by norm_num⟩
      let bad : Set I := ⋃ k, ⋃ j, (arc k) ⁻¹' old j
      have hbad : IsClosed bad := isClosed_iUnion_of_finite (fun k =>
        isClosed_iUnion_of_finite (fun j =>
          (hclosed j).preimage (arc k).continuous))
      have hzero : zero ∈ badᶜ := by
        intro h
        obtain ⟨k,j,hkj⟩ := Set.mem_iUnion₂.mp h
        exact (hends k j).1 hkj
      have hone : one ∈ badᶜ := by
        intro h
        obtain ⟨k,j,hkj⟩ := Set.mem_iUnion₂.mp h
        exact (hends k j).2 hkj
      obtain ⟨δ₀,hδ₀,hball₀⟩ := Metric.isOpen_iff.mp hbad.isOpen_compl zero hzero
      obtain ⟨δ₁,hδ₁,hball₁⟩ := Metric.isOpen_iff.mp hbad.isOpen_compl one hone
      let ε : ℝ := min (1/4) (min δ₀ δ₁) / 2
      have hε : 0 < ε := by dsimp [ε]; positivity
      have hεhalf : ε < 1/2 := by
        have := min_le_left (1/4:ℝ) (min δ₀ δ₁)
        dsimp [ε]; linarith
      have hεδ₀ : ε < δ₀ := by
        have := (min_le_right (1/4:ℝ) (min δ₀ δ₁)).trans (min_le_left δ₀ δ₁)
        dsimp [ε]; linarith
      have hεδ₁ : ε < δ₁ := by
        have := (min_le_right (1/4:ℝ) (min δ₀ δ₁)).trans (min_le_right δ₀ δ₁)
        dsimp [ε]; linarith
      have hcollar (k : K) (t : I) (ht : (t:ℝ) ≤ ε ∨ 1-ε ≤ (t:ℝ)) :
          ∀ j, arc k t ∉ old j := by
        have htgood : t ∈ badᶜ := by
          rcases ht with ht | ht
          · apply hball₀
            rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
            change |(t:ℝ)-0| < δ₀
            rw [sub_zero,abs_of_nonneg t.property.1]
            exact ht.trans_lt hεδ₀
          · apply hball₁
            rw [Metric.mem_ball,Subtype.dist_eq,Real.dist_eq]
            change |(t:ℝ)-1| < δ₁
            rw [abs_of_nonpos (by linarith [t.property.2])]
            linarith
        intro j h
        exact htgood (Set.mem_iUnion₂.mpr ⟨k,j,h⟩)
      exact ⟨ε,hε,hεhalf,hcollar⟩
    have trimChartsProducer {S : Type} [TopologicalSpace S] [T2Space S] [NormalSpace S]
        {a b : S} (p : Path a b) (hp : Function.Injective p)
        (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
        (η : C(I,S))
        (hη : ∀ t, η t = p ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩)
        (hi : Function.Injective η) (n : ℕ) (hn : 0 < n)
        (e : Fin n → OpenPartialHomeomorph S Plane)
        (hchart : ∀ k t, η (intervalMeshParameter n hn k t) ∈ (e k).source)
        (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) :
        ∃ α β : Fin n → ℝ, ∃ F : Fin n → OpenPartialHomeomorph S Plane,
          (∀ k, 0 < α k ∧ α k < β k ∧ β k < 1) ∧
          (∀ k, (F k).source ⊆ (e k).source) ∧
          (∀ i j, i ≠ j → Disjoint (F i).source (F j).source) ∧
          (∀ k, Plane.closedSquare 0 1 ⊆ (F k).target) ∧
          (∀ k, (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source) ∧
          (∀ k, F k ((p ∘ Set.projIcc 0 1 zero_le_one) (α k)) = Plane.mk (-1) 0 ∧
            F k ((p ∘ Set.projIcc 0 1 zero_le_one) (β k)) = Plane.mk 1 0) ∧
          (∀ k x, x ∈ (F k).source → (x ∈ Set.range p ↔ F k x 1 = 0)) ∧
          (∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ Set.range p =
            (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k)) ∧
          (∀ k, (η ∘ intervalMeshParameter n hn k) '' {t : I | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε} =
            (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k)) ∧
          (∀ k, a ∉ (F k).source ∧ b ∉ (F k).source) ∧
          (∀ k, (p ∘ Set.projIcc 0 1 zero_le_one) (α k) =
            η (intervalMeshParameter n hn k ⟨ε,⟨hε.le,by linarith⟩⟩)) ∧
          (∀ k, (p ∘ Set.projIcc 0 1 zero_le_one) (β k) =
            η (intervalMeshParameter n hn k ⟨1-ε,⟨by linarith,by linarith⟩⟩)) := by
      classical
      have chartProducer {S : Type} [TopologicalSpace S] [T2Space S] [NormalSpace S]
          {a b : S} (p : Path a b) (hp : Function.Injective p)
          (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
          (η : C(I,S))
          (hη : ∀ t, η t = p ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩)
          (hi : Function.Injective η) (n : ℕ) (hn : 0 < n)
          (e : Fin n → OpenPartialHomeomorph S Plane)
          (hchart : ∀ k t, η (intervalMeshParameter n hn k t) ∈ (e k).source)
          (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) :
          ∃ α β : Fin n → ℝ, ∃ F : Fin n → OpenPartialHomeomorph S Plane,
            (∀ k, 0 < α k ∧ α k < β k ∧ β k < 1) ∧
            (∀ k, (F k).source ⊆ (e k).source) ∧
            (∀ i j, i ≠ j → Disjoint (F i).source (F j).source) ∧
            (∀ k, Plane.closedSquare 0 1 ⊆ (F k).target) ∧
            (∀ k, (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (F k).source) ∧
            (∀ k, F k ((p ∘ Set.projIcc 0 1 zero_le_one) (α k)) = Plane.mk (-1) 0 ∧
              F k ((p ∘ Set.projIcc 0 1 zero_le_one) (β k)) = Plane.mk 1 0) ∧
            (∀ k x, x ∈ (F k).source → (x ∈ Set.range p ↔ F k x 1 = 0)) ∧
            (∀ k, {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ Set.range p =
              (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k)) ∧
            (∀ k, (η ∘ intervalMeshParameter n hn k) '' {t : I | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε} =
              (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k)) ∧
            (∀ k, (p ∘ Set.projIcc 0 1 zero_le_one) (α k) =
              η (intervalMeshParameter n hn k ⟨ε,⟨hε.le,by linarith⟩⟩)) ∧
            (∀ k, (p ∘ Set.projIcc 0 1 zero_le_one) (β k) =
              η (intervalMeshParameter n hn k ⟨1-ε,⟨by linarith,by linarith⟩⟩)) := by
        classical
        have sliceImage {S : Type} [TopologicalSpace S] {a b : S} (p : Path a b)
            (l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < 1)
            (η : C(I,S))
            (hη : ∀ t, η t = p ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩)
            (A B : ℝ) (hA : 0 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1) :
            (η ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc A B =
              (p ∘ Set.projIcc 0 1 zero_le_one) ''
                Set.Icc (l+(u-l)*A) (l+(u-l)*B) := by
          have hpos : 0 < u-l := sub_pos.mpr hlu
          ext x
          constructor
          · rintro ⟨t,ht,rfl⟩
            have ht0 : 0 ≤ t := hA.trans ht.1
            have ht1 : t ≤ 1 := ht.2.trans hB
            refine ⟨l+(u-l)*t,⟨by nlinarith [ht.1],by nlinarith [ht.2]⟩,?_⟩
            have hp : Set.projIcc 0 1 zero_le_one t = (⟨t,⟨ht0,ht1⟩⟩:I) := Set.projIcc_of_mem _ _
            have htglobal : l+(u-l)*t ∈ Set.Icc (0:ℝ) 1 := by constructor <;> nlinarith
            simp only [Function.comp_apply]
            rw [hp,hη]
            exact congrArg p (Set.projIcc_of_mem zero_le_one htglobal)
          · rintro ⟨t,ht,rfl⟩
            let s : ℝ := (t-l)/(u-l)
            have hslow : A ≤ s := by
              dsimp [s]
              apply (le_div_iff₀ hpos).mpr
              nlinarith [ht.1]
            have hshigh : s ≤ B := by
              dsimp [s]
              apply (div_le_iff₀ hpos).mpr
              nlinarith [ht.2]
            have hs0 : 0 ≤ s := hA.trans hslow
            have hs1 : s ≤ 1 := hshigh.trans hB
            have ht0 : 0 ≤ t := by nlinarith [ht.1]
            have ht1 : t ≤ 1 := by nlinarith [ht.2]
            refine ⟨s,⟨hslow,hshigh⟩,?_⟩
            rw [Function.comp_apply,Set.projIcc_of_mem zero_le_one ⟨hs0,hs1⟩,hη,
              Function.comp_apply,Set.projIcc_of_mem zero_le_one ⟨ht0,ht1⟩]
            apply congrArg p
            apply Subtype.ext
            change l+(u-l)*((t-l)/(u-l)) = t
            field_simp
            ring

        have hnR : (0:ℝ) < n := by exact_mod_cast hn
        let A : Fin n → ℝ := fun k => ((k.val:ℝ)+ε)/n
        let B : Fin n → ℝ := fun k => ((k.val:ℝ)+(1-ε))/n
        have hA (k : Fin n) : 0 < A k := div_pos (by positivity) hnR
        have hAB (k : Fin n) : A k < B k := (div_lt_div_iff_of_pos_right hnR).mpr (by linarith)
        have hB (k : Fin n) : B k < 1 := by
          apply (div_lt_one hnR).mpr
          have hk : (k.val:ℝ)+1 ≤ (n:ℝ) := by exact_mod_cast k.isLt
          linarith
        let α : Fin n → ℝ := fun k => l+(u-l)*A k
        let β : Fin n → ℝ := fun k => l+(u-l)*B k
        have hbounds (k : Fin n) : 0 < α k ∧ α k < β k ∧ β k < 1 := by
          have ha := hA k; have hab := hAB k; have hb := hB k
          dsimp [α,β]
          constructor
          · nlinarith
          · constructor <;> nlinarith
        let coreParams : Set I := {t | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε}
        have hcore (k : Fin n) : (η ∘ intervalMeshParameter n hn k) '' coreParams =
            (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) := by
          calc
            _ = η '' (intervalMeshParameter n hn k '' coreParams) := (Set.image_image _ _ _).symm
            _ = η '' (Set.projIcc 0 1 zero_le_one '' Set.Icc (A k) (B k)) := by
              rw [actual_trimmed_interval_mesh_parameter_image n hn k ε hε hεhalf]
            _ = (η ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (A k) (B k) := Set.image_image _ _ _
            _ = _ := sliceImage p l u hl hlu hu η hη
              (A k) (B k) (hA k).le (hAB k).le (hB k).le
        have hsub (k : Fin n) :
            (p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) ⊆ (e k).source := by
          rw [← hcore k]
          rintro x ⟨t,_,rfl⟩
          exact hchart k t
        have hdis : ∀ i j : Fin n, i ≠ j → Disjoint
            ((p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α i) (β i))
            ((p ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α j) (β j)) := by
          intro i j hij
          rw [← hcore i,← hcore j]
          exact actual_trimmed_interval_mesh_disjoint η hi n hn ε hε hεhalf i j hij
        obtain ⟨F,hFsub,hFdis,hFsq,hFcentral,hFends,hFflat,hFexact⟩ :=
          finite_actual_interval_compatible_crosscut_charts (Fin n) (fun _ => p)
            (fun _ => p.continuous) (fun _ t v h => Or.inl (hp h))
            α β (fun k => (hbounds k).1) (fun k => (hbounds k).2.1)
            (fun k => (hbounds k).2.2) e hsub hdis
        refine ⟨α,β,F,hbounds,hFsub,hFdis,hFsq,hFcentral,hFends,hFflat,hFexact,hcore,?_,?_⟩
        · intro k
          simp only [Function.comp_apply]
          rw [Set.projIcc_of_mem zero_le_one ⟨(hbounds k).1.le,by linarith [(hbounds k).2.1,(hbounds k).2.2]⟩,hη]
          rfl
        · intro k
          simp only [Function.comp_apply]
          rw [Set.projIcc_of_mem zero_le_one ⟨by linarith [(hbounds k).1,(hbounds k).2.1],(hbounds k).2.2.le⟩,hη]
          rfl
      have hηoff (t : I) : η t ≠ a ∧ η t ≠ b := by
        let τ : I := ⟨l+(u-l)*t.val,by constructor <;> nlinarith [t.property.1,t.property.2]⟩
        have hτ0 : 0 < τ.val := by dsimp [τ]; nlinarith [t.property.1]
        have hτ1 : τ.val < 1 := by dsimp [τ]; nlinarith [t.property.2]
        have he : η t = p τ := hη t
        constructor
        · intro ha
          have hh := congrArg Subtype.val (hp (he.symm.trans (ha.trans p.source.symm)))
          change τ.val = 0 at hh
          linarith
        · intro hb
          have hh := congrArg Subtype.val (hp (he.symm.trans (hb.trans p.target.symm)))
          change τ.val = 1 at hh
          linarith
      let O : Set S := ({a,b} : Set S)ᶜ
      have hO : IsOpen O := ((Set.finite_singleton b).insert a).isClosed.isOpen_compl
      let e1 : Fin n → OpenPartialHomeomorph S Plane := fun k => (e k).restr O
      have hsource (k) : (e1 k).source = (e k).source ∩ O := (e k).restr_source' O hO
      have hchart1 : ∀ k t, η (intervalMeshParameter n hn k t) ∈ (e1 k).source := by
        intro k t
        rw [hsource]
        refine ⟨hchart k t,?_⟩
        change η (intervalMeshParameter n hn k t) ∉ ({a,b} : Set S)
        simpa only [Set.mem_compl_iff,Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using
          hηoff (intervalMeshParameter n hn k t)
      obtain ⟨α,β,F,hbounds,hFsub,hFdis,hFsq,hFcentral,hFends,hFflat,hFexact,hcore,hα,hβ⟩ :=
        chartProducer p hp l u hl hlu hu η hη hi n hn e1 hchart1 ε hε hεhalf
      refine ⟨α,β,F,hbounds,?_,hFdis,hFsq,hFcentral,hFends,hFflat,hFexact,hcore,?_,hα,hβ⟩
      · intro k x hx
        have hh := hFsub k hx
        rw [hsource] at hh
        exact hh.1
      · intro k
        constructor
        · intro ha
          have hh := hFsub k ha
          rw [hsource] at hh
          exact hh.2 (Or.inl rfl)
        · intro hb
          have hh := hFsub k hb
          rw [hsource] at hh
          exact hh.2 (Or.inr rfl)
    have properTargetProducer {S J : Type} [TopologicalSpace S]
        (old : J → Set S) (e E : OpenPartialHomeomorph S Plane)
        (hsub : E.source ⊆ e.source)
        (hSquare : Plane.closedSquare 0 1 ⊆ E.target)
        (tag : Option J)
        (haxis : ∀ j x, x ∈ e.source → (x ∈ old j ↔ tag = some j ∧ e x 0 = 0))
        (hleft : ∀ j, E.symm (Plane.mk (-1) 0) ∉ old j)
        (hright : ∀ j, E.symm (Plane.mk 1 0) ∉ old j) :
        ∃ B : Set Plane,
          IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
          B \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
          ∀ j, (old j ∩ {x : S | x ∈ E.source ∧ E x ∈ B}).Finite := by
      classical
      have finitePullback {S J : Type} [TopologicalSpace S]
          (old : J → Set S) (e E : OpenPartialHomeomorph S Plane)
          (hsub : E.source ⊆ e.source)
          (tag : Option J)
          (haxis : ∀ j x, x ∈ e.source → (x ∈ old j ↔ tag = some j ∧ e x 0 = 0))
          (B : Set Plane)
          (hfinite : tag = none ∨
            (((E.symm.trans e) '' B) ∩ {z : Plane | z 0 = 0}).Finite) :
          ∀ j, (old j ∩ {x : S | x ∈ E.source ∧ E x ∈ B}).Finite := by
        intro j
        rcases hfinite with hnone | hfinite
        · have hempty : old j ∩ {x : S | x ∈ E.source ∧ E x ∈ B} = ∅ := by
            ext x
            simp only [Set.mem_empty_iff_false,iff_false]
            intro hx
            have htag := ((haxis j x (hsub hx.2.1)).mp hx.1).1
            rw [hnone] at htag
            cases htag
          rw [hempty]
          exact Set.finite_empty
        · have himage : (e '' (old j ∩ {x : S | x ∈ E.source ∧ E x ∈ B})).Finite := by
            apply hfinite.subset
            rintro _ ⟨x,hx,rfl⟩
            refine ⟨⟨E x,hx.2.2,?_⟩,((haxis j x (hsub hx.2.1)).mp hx.1).2⟩
            change e (E.symm (E x)) = e x
            rw [E.left_inv hx.2.1]
          exact himage.of_finite_image (fun x hx y hy h =>
            e.injOn (hsub hx.2.1) (hsub hy.2.1) h)
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
      let T : OpenPartialHomeomorph Plane Plane := E.symm.trans e
      have hTsquare : Plane.closedSquare 0 1 ⊆ T.source := by
        intro z hz
        exact ⟨hSquare hz,hsub (E.symm.map_source (hSquare hz))⟩
      cases htag : tag with
      | none =>
        exact ⟨A,hA,hAi,finitePullback old e E hsub tag haxis A (Or.inl htag)⟩
      | some j =>
        have hlSource : E.symm (Plane.mk (-1) 0) ∈ e.source :=
          hsub (E.symm.map_source (hSquare (by norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk])))
        have hrSource : E.symm (Plane.mk 1 0) ∈ e.source :=
          hsub (E.symm.map_source (hSquare (by norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk])))
        have ha0 : T (Plane.mk (-1) 0) 0 ≠ 0 := by
          intro h
          exact hleft j ((haxis j _ hlSource).mpr ⟨htag,h⟩)
        have hb0 : T (Plane.mk 1 0) 0 ≠ 0 := by
          intro h
          exact hright j ((haxis j _ hrSource).mpr ⟨htag,h⟩)
        obtain ⟨B,hB,hBi,hfinite,_⟩ := position_proper_affine_crosscut T hTsquare ha0 hb0
        exact ⟨B,hB,hBi,finitePullback old e E hsub tag haxis B (Or.inr hfinite)⟩
    have horizontalPatchProducer {S : Type} [TopologicalSpace S]
        (E : OpenPartialHomeomorph S Plane) (p C : Set S)
        (hflat : ∀ x, x ∈ E.source → (x ∈ p ↔ E x 1 = 0))
        (hexact : {x : S | x ∈ E.source ∧ E x ∈ Plane.closedSquare 0 1} ∩ p = C) :
        let A := segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
        IsArcBetween A (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
          A \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
          {x : S | x ∈ E.source ∧ E x ∈ A} = C := by
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
      refine ⟨hA,hAi,?_⟩
      rw [← hexact]
      ext x
      constructor
      · intro hx
        have hz := hhorizontal.le hx.2
        exact ⟨⟨hx.1,hz.1⟩,(hflat x hx.1).mpr hz.2⟩
      · intro hx
        exact ⟨hx.1.1,hhorizontal.ge ⟨hx.1.2,(hflat x hx.1.1).mp hx.2⟩⟩
    have contactReplacementProducer (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
        {a b : S} (p : Path a b) (hp : Function.Injective p) (K : Type) [Fintype K]
        (E : K → OpenPartialHomeomorph S Plane)
        (hdis : ∀ i j, i ≠ j → Disjoint (E i).source (E j).source)
        (haout : ∀ k, a ∉ (E k).source) (hbout : ∀ k, b ∉ (E k).source)
        (hSquare : ∀ k, Plane.closedSquare 0 1 ⊆ (E k).target)
        (A : K → Set Plane) (u v : K → Plane)
        (hu : ∀ k, u k ∈ modelCurve) (hv : ∀ k, v k ∈ modelCurve)
        (hA : ∀ k, IsArcBetween (A k) (u k) (v k))
        (hAi : ∀ k, A k \ {u k,v k} ⊆ Plane.openSquare 0 1)
        (hc : ∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩
          Set.range p = {x : S | x ∈ (E k).source ∧ E k x ∈ A k})
        (B : K → Set Plane) (hB : ∀ k, IsArcBetween (B k) (u k) (v k))
        (hBi : ∀ k, B k \ {u k,v k} ⊆ Plane.openSquare 0 1)
        (J : Type) (old : J → Set S)
        (hrest : ∀ j, (old j ∩ (Set.range p \ ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ A k})).Finite)
        (hnew : ∀ j k, (old j ∩ {x : S | x ∈ (E k).source ∧ E k x ∈ B k}).Finite) :
        ∃ d : Path a b, Path.Homotopic p d ∧ Function.Injective d ∧
          ∀ j, (old j ∩ Set.range d).Finite := by
      classical
      have replacementProducer (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
          {a b : S} (p : Path a b) (hp : Function.Injective p) (K : Type) [Fintype K]
          (E : K → OpenPartialHomeomorph S Plane)
          (hdis : ∀ i j, i ≠ j → Disjoint (E i).source (E j).source)
          (haout : ∀ k, a ∉ (E k).source) (hbout : ∀ k, b ∉ (E k).source)
          (hSquare : ∀ k, Plane.closedSquare 0 1 ⊆ (E k).target)
          (A : K → Set Plane) (u v : K → Plane)
          (hu : ∀ k, u k ∈ modelCurve) (hv : ∀ k, v k ∈ modelCurve)
          (hA : ∀ k, IsArcBetween (A k) (u k) (v k))
          (hAi : ∀ k, A k \ {u k,v k} ⊆ Plane.openSquare 0 1)
          (hc : ∀ k, {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩
            Set.range p = {x : S | x ∈ (E k).source ∧ E k x ∈ A k})
          (B : K → Set Plane) (hB : ∀ k, IsArcBetween (B k) (u k) (v k))
          (hBi : ∀ k, B k \ {u k,v k} ⊆ Plane.openSquare 0 1) :
          ∃ d : Path a b, Path.Homotopic p d ∧ Function.Injective d ∧
            Set.range d =
              (Set.range p \ ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ A k}) ∪
              ⋃ k, {x : S | x ∈ (E k).source ∧ E k x ∈ B k} := by
        have transport {S : Type} [TopologicalSpace S] {a b : S}
            (p : Path a b) (hp : Function.Injective p) (H : AmbientIsotopy S)
            (ha : ∀ t, H.map (t,a) = a) (hb : ∀ t, H.map (t,b) = b) :
            ∃ q : Path a b, Path.Homotopic p q ∧ Function.Injective q ∧
              Set.range q = H.finalMap '' Set.range p := by
          let q : Path a b := {
            toContinuousMap := ⟨fun t => H.finalMap (p t),
              H.map.continuous.comp (continuous_const.prodMk p.continuous)⟩
            source' := by change H.map (1,p 0) = a; rw [p.source,ha]
            target' := by change H.map (1,p 1) = b; rw [p.target,hb] }
          have hhom : Path.Homotopic p q := by
            refine ⟨{
              toHomotopy := {
                toContinuousMap := ⟨fun z => H.map (z.1,p z.2),
                  H.map.continuous.comp (continuous_fst.prodMk (p.continuous.comp continuous_snd))⟩
                map_zero_left := fun t => H.at_zero (p t)
                map_one_left := fun t => rfl }
              prop' := ?_ }⟩
            intro t u hu
            rcases hu with rfl | hu
            · change H.map (t,p 0) = p 0
              rw [p.source,ha]
            · rw [Set.mem_singleton_iff] at hu
              subst u
              change H.map (t,p 1) = p 1
              rw [p.target,hb]
          have hi : Function.Injective q := by
            obtain ⟨e,he⟩ := H.homeomorphism_at (1 : I)
            intro t u h
            apply hp
            apply e.injective
            change H.map (1,p t) = H.map (1,p u) at h
            exact (he (p t)).trans (h.trans (he (p u)).symm)
          refine ⟨q,hhom,hi,?_⟩
          apply Set.Subset.antisymm
          · rintro _ ⟨t,rfl⟩
            exact ⟨p t,⟨t,rfl⟩,rfl⟩
          · rintro _ ⟨x,⟨t,rfl⟩,rfl⟩
            exact ⟨t,rfl⟩
        classical
        let Ap : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ A k}
        let Bp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ B k}
        let Dp : K → Set S := fun k => {x | x ∈ (E k).source ∧ E k x ∈ Plane.openSquare 0 1}
        have hAsquare (k : K) : A k ⊆ Plane.closedSquare 0 1 := by
          intro z hz
          by_cases he : z ∈ ({u k,v k} : Set Plane)
          · rcases he with he | he
            · rw [he]
              simpa [Plane.closedSquare,Plane.supDist,modelCurve] using (le_of_eq (hu k) : Plane.supNorm (u k) ≤ 1)
            · rw [Set.mem_singleton_iff.mp he]
              simpa [Plane.closedSquare,Plane.supDist,modelCurve] using (le_of_eq (hv k) : Plane.supNorm (v k) ≤ 1)
          · exact Plane.openSquare_subset_closedSquare 0 1 (hAi k ⟨hz,he⟩)
        have hApcurve (k : K) : Ap k ⊆ Set.range p := by
          intro z hz
          have hh : z ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ Plane.closedSquare 0 1} ∩ Set.range p := by
            rw [hc k]
            exact hz
          exact hh.2
        have hDcurve (k : K) : Dp k ∩ Set.range p ⊆ Ap k := by
          intro x hx
          change x ∈ {x : S | x ∈ (E k).source ∧ E k x ∈ A k}
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
            (hSquare k) (A k) (B k) (u k) (v k) (hA k) (hB k) (hu k) (hv k) (hAi k) (hBi k)
          rw [hPull,hPull] at hGA
          simp only [hPull] at hGfix
          exact ⟨G,hGA,hGfix⟩
        choose G hGA hGfix using hpatch
        have hfixRest (k : K) (x : S) (hx : x ∈ Set.range p \ Ap k) : (G k).finalMap x = x := by
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
            (∀ t, H.map (t,a) = a) ∧ (∀ t, H.map (t,b) = b) ∧ H.finalMap '' Set.range p = (Set.range p \ As P) ∪ Bs P := by
          induction P using Finset.induction_on with
          | empty =>
            let H : AmbientIsotopy S := {
              map := ⟨fun z => z.2,continuous_snd⟩
              homeomorphism_at := fun _ => ⟨Homeomorph.refl S,fun _ => rfl⟩
              at_zero := fun _ => rfl }
            refine ⟨H,(fun _ => rfl),(fun _ => rfl),?_⟩
            change (fun x : S => x) '' Set.range p = _
            simp [As,Bs]
          | @insert k P hk ih =>
            obtain ⟨H,hHa,hHb,hH⟩ := ih
            have hAsinsert : As (insert k P) = Ap k ∪ As P := by simp [As]
            have hBsinsert : Bs (insert k P) = Bp k ∪ Bs P := by simp [Bs]
            have hnotAs (x : S) (hx : x ∈ Ap k) : x ∉ As P := by
              intro h
              obtain ⟨j,hj,hxj⟩ := Set.mem_iUnion₂.mp h
              have hkj : k ≠ j := fun he => hk (he.symm ▸ hj)
              exact Set.disjoint_left.mp (hdis k j hkj) hx.1 hxj.1
            let R : Set S := (Set.range p \ As (insert k P)) ∪ Bs P
            have hdecomp : (Set.range p \ As P) ∪ Bs P = Ap k ∪ R := by
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
            have hnew : (G k).finalMap '' ((Set.range p \ As P) ∪ Bs P) =
                (Set.range p \ As (insert k P)) ∪ Bs (insert k P) := by
              rw [hdecomp,Set.image_union,hGA k,hGR,hBsinsert]
              change Bp k ∪ ((Set.range p \ As (insert k P)) ∪ Bs P) =
                (Set.range p \ As (insert k P)) ∪ (Bp k ∪ Bs P)
              ext x
              simp only [Set.mem_union]
              tauto
            obtain ⟨F,hF⟩ := hcompose H (G k)
            refine ⟨F,?_,?_,?_⟩
            · intro t
              rw [hF,hHa]
              exact hGfix k t a (fun hh => haout k hh.1)
            · intro t
              rw [hF,hHb]
              exact hGfix k t b (fun hh => hbout k hh.1)
            have hmaps : F.finalMap = (G k).finalMap ∘ H.finalMap :=
              funext (hF ⟨1,by norm_num⟩)
            calc
              F.finalMap '' Set.range p = (G k).finalMap '' (H.finalMap '' Set.range p) := by
                rw [Set.image_image,hmaps]
                rfl
              _ = _ := by rw [hH,hnew]

        obtain ⟨H,hHa,hHb,hH⟩ := hbuild Finset.univ
        obtain ⟨d,hd,hdi,hrange⟩ := transport p hp H hHa hHb
        refine ⟨d,hd,hdi,?_⟩
        rw [hrange,hH]
        simp [As,Bs,Ap,Bp]
      obtain ⟨d,hd,hdi,hrange⟩ := replacementProducer S p hp K E hdis haout hbout hSquare A u v hu hv hA hAi hc B hB hBi
      refine ⟨d,hd,hdi,?_⟩
      intro j
      rw [hrange,Set.inter_union_distrib_left,Set.inter_iUnion]
      exact (hrest j).union (Set.finite_iUnion (hnew j))
    have outerRemainderProducer {S J : Type} [TopologicalSpace S]
        {a b : S} (p : Path a b) (old : J → Set S)
        (lo high : I) (η : C(I,S))
        (hmiddle : Set.range η = p '' Set.Icc lo high)
        (hleft : ∀ j, (old j ∩ p '' Set.Icc 0 lo).Finite)
        (hright : ∀ j, (old j ∩ p '' Set.Icc high 1).Finite)
        (n : ℕ) (hn : 0 < n) (ε : ℝ)
        (hcollar : ∀ k : Fin n, ∀ t : I,
          (t:ℝ) ≤ ε ∨ 1-ε ≤ (t:ℝ) → ∀ j,
          η (intervalMeshParameter n hn k t) ∉ old j) :
        ∀ j, (old j ∩ (Set.range p \ ⋃ k : Fin n,
          (η ∘ intervalMeshParameter n hn k) '' {t : I | ε ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1-ε})).Finite := by
      intro j
      apply ((hleft j).union (hright j)).subset
      rintro x ⟨hx,⟨⟨t,ht⟩,hout⟩⟩
      by_cases hl : t ≤ lo
      · exact Or.inl ⟨hx,t,⟨t.property.1,hl⟩,ht⟩
      by_cases hh : high ≤ t
      · exact Or.inr ⟨hx,t,⟨hh,t.property.2⟩,ht⟩
      have hxmid : x ∈ Set.range η := by
        rw [hmiddle]
        exact ⟨t,⟨(lt_of_not_ge hl).le,(lt_of_not_ge hh).le⟩,ht⟩
      obtain ⟨s,hs⟩ := hxmid
      obtain ⟨k,u,hu⟩ := intervalMeshParameter_cover n hn s
      have hnotcore : ¬ (ε ≤ (u:ℝ) ∧ (u:ℝ) ≤ 1-ε) := by
        intro hcore
        exact hout (Set.mem_iUnion.mpr ⟨k,u,hcore,by simp [Function.comp_def,hu,hs]⟩)
      have hcol : (u:ℝ) ≤ ε ∨ 1-ε ≤ (u:ℝ) := by
        rcases lt_or_ge (u:ℝ) ε with hl | hl
        · exact Or.inl hl.le
        · exact Or.inr (le_of_not_ge (fun hh => hnotcore ⟨hl,hh⟩))
      exact False.elim (hcollar k u hcol j (by rw [hu,hs]; exact hx))
    have hleft1 (i : J) : (Set.range (r i.val) ∩ q1 '' Set.Icc 0 l).Finite := by
      apply (hprefix i).subset
      rintro x ⟨hx,t,ht,rfl⟩
      exact ⟨hx,t,⟨ht.1,ht.2.trans hllo.le⟩,rfl⟩
    have hright1 (i : J) : (Set.range (r i.val) ∩ q1 '' Set.Icc u 1).Finite := by
      apply (hsuffix i).subset
      rintro x ⟨hx,t,ht,rfl⟩
      exact ⟨hx,t,⟨hhighu.le.trans ht.1,ht.2⟩,rfl⟩
    obtain ⟨η,hiη,hη,hmiddle,hηchart,hηends,hleft2,hright2⟩ :=
      repairedDataProducer q1 q2 hiq2 (fun i : J => Set.range (r i.val))
        l u hl0 hlu hu1 hleft1 hright1 H hq2point hfix n hn e hleft hright hcharts
    let arc : Fin n → C(I,S) := fun k => ⟨η ∘ intervalMeshParameter n hn k,
      η.continuous.comp (intervalMeshParameter_continuous n hn k)⟩
    obtain ⟨ε,hε,hεhalf,hcollar⟩ := clearCollarsProducer
      (fun i : J => Set.range (r i.val))
      (fun i => (isCompact_range (r i.val).continuous).isClosed) arc hηends
    obtain ⟨α,β,F,hbounds,hFsub,hFdis,hFsq,hFcentral,hFends,hFflat,hFexact,hcore,hFoff,hα,hβ⟩ :=
      trimChartsProducer q2 hiq2 l.val u.val hl0 hlu hu1 η hη hiη n hn e hηchart ε hε hεhalf
    have hFinvLeft (k : Fin n) : (F k).symm (Plane.mk (-1) 0) =
        (q2 ∘ Set.projIcc 0 1 zero_le_one) (α k) := by
      rw [← (hFends k).1,(F k).left_inv
        (hFcentral k (Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr (hbounds k).2.1.le)))]
    have hFinvRight (k : Fin n) : (F k).symm (Plane.mk 1 0) =
        (q2 ∘ Set.projIcc 0 1 zero_le_one) (β k) := by
      rw [← (hFends k).2,(F k).left_inv
        (hFcentral k (Set.mem_image_of_mem _ (Set.right_mem_Icc.mpr (hbounds k).2.1.le)))]
    have htargets (k : Fin n) : ∃ Bk : Set Plane,
        IsArcBetween Bk (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
        Bk \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
        ∀ i : J, (Set.range (r i.val) ∩ {x : S | x ∈ (F k).source ∧ F k x ∈ Bk}).Finite := by
      apply properTargetProducer (fun i : J => Set.range (r i.val)) (e k) (F k)
        (hFsub k) (hFsq k) (tag k) (haxis k)
      · intro i
        rw [hFinvLeft,hα]
        exact hcollar k _ (Or.inl le_rfl) i
      · intro i
        rw [hFinvRight,hβ]
        exact hcollar k _ (Or.inr le_rfl) i
    choose targets htargetArc htargetInside htargetFinite using htargets
    let A : Set Plane := segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)
    have hsourceArc (k : Fin n) : IsArcBetween A (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
        A \ {Plane.mk (-1) 0,Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
        {x : S | x ∈ (F k).source ∧ F k x ∈ A} =
          (q2 ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k) :=
      horizontalPatchProducer (F k) (Set.range q2)
        ((q2 ∘ Set.projIcc 0 1 zero_le_one) '' Set.Icc (α k) (β k)) (hFflat k) (hFexact k)
    have hactual (k : Fin n) :
        {x : S | x ∈ (F k).source ∧ F k x ∈ Plane.closedSquare 0 1} ∩ Set.range q2 =
          {x : S | x ∈ (F k).source ∧ F k x ∈ A} :=
      (hFexact k).trans (hsourceArc k).2.2.symm
    have hrest (i : J) : (Set.range (r i.val) ∩
        (Set.range q2 \ ⋃ k : Fin n, {x : S | x ∈ (F k).source ∧ F k x ∈ A})).Finite := by
      simp_rw [(hsourceArc _).2.2]
      simp_rw [← hcore]
      exact outerRemainderProducer q2 (fun i : J => Set.range (r i.val))
        l u η hmiddle hleft2 hright2 n hn ε hcollar i
    have hmodelLeft : Plane.mk (-1) 0 ∈ modelCurve := by norm_num [modelCurve,Plane.supNorm,Plane.mk]
    have hmodelRight : Plane.mk 1 0 ∈ modelCurve := by norm_num [modelCurve,Plane.supNorm,Plane.mk]
    obtain ⟨d,hd,hdi,hdf⟩ := contactReplacementProducer S q2 hiq2 (Fin n) F hFdis
      (fun k => (hFoff k).1) (fun k => (hFoff k).2) hFsq
      (fun _ => A) (fun _ => Plane.mk (-1) 0) (fun _ => Plane.mk 1 0)
      (fun _ => hmodelLeft) (fun _ => hmodelRight)
      (fun k => (hsourceArc k).1) (fun k => (hsourceArc k).2.1) hactual
      targets htargetArc htargetInside J (fun i : J => Set.range (r i.val))
      hrest (fun i k => htargetFinite k i)
    exact ⟨d,hd,hdi,fun i hi => hdf ⟨i,hi⟩⟩
  have build (B : Finset (Fin m)) :
      ∃ r : (i : Fin m) → Path (a i) (b i),
        (∀ i, Path.Homotopic (p i) (r i)) ∧
        (∀ i, Function.Injective (r i)) ∧
        ∀ i ∈ B, ∀ j ∈ B, i ≠ j →
          (Set.range (r i) ∩ Set.range (r j)).Finite := by
    induction B using Finset.induction_on with
    | empty => exact ⟨p, fun i => Path.Homotopic.refl _, hp, by simp⟩
    | @insert v B hv ih =>
      obtain ⟨r,hr,hi,hf⟩ := ih
      obtain ⟨d,hd,hdi,hdf⟩ := extend B r hi hf v hv
      let r' : (i : Fin m) → Path (a i) (b i) := Function.update r v d
      have hv' : r' v = d := by simp [r']
      have ho (i : Fin m) (hiv : i ≠ v) : r' i = r i :=
        Function.update_of_ne hiv _ _
      refine ⟨r',?_,?_,?_⟩
      · intro i
        by_cases hiv : i = v
        · subst i
          rw [hv']
          exact (hr v).trans hd
        · rw [ho i hiv]
          exact hr i
      · intro i
        by_cases hiv : i = v
        · subst i
          rw [hv']
          exact hdi
        · rw [ho i hiv]
          exact hi i
      · intro i hiB j hjB hij
        by_cases hiv : i = v
        · subst i
          have hjv : j ≠ v := Ne.symm hij
          have hj : j ∈ B := (Finset.mem_insert.mp hjB).resolve_left hjv
          rw [hv',ho j hjv,Set.inter_comm]
          exact hdf j hj
        · have hi : i ∈ B := (Finset.mem_insert.mp hiB).resolve_left hiv
          by_cases hjv : j = v
          · subst j
            rw [ho i hiv,hv']
            exact hdf i hi
          · have hj : j ∈ B := (Finset.mem_insert.mp hjB).resolve_left hjv
            rw [ho i hiv,ho j hjv]
            exact hf i hi j hj hij
  obtain ⟨r,hr,hi,hf⟩ := build Finset.univ
  exact ⟨r,hr,hi,fun i j hij => hf i (Finset.mem_univ _) j (Finset.mem_univ _) hij⟩

end CurveComplexGenusTwo.SourceTopology
