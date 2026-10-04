import CurveComplexGenusTwo.Topology.Smoothing.PointedCrosscutHeader
import CurveComplexGenusTwo.Topology.Smoothing.JoinedArmsHeader
import CurveComplexGenusTwo.Topology.Smoothing.SeedFirstExitDependency
import Schoenflies.SquareMesh
import Schoenflies.ArcComplementPrep
import Schoenflies.BoundaryContinuity2
import CurveComplexGenusTwo.Topology.Extraction
import ClassificationOfSurfaces.Moise.GraphPolygonalization
import Mathlib.Topology.Subpath
import CurveComplexGenusTwo.Topology.Smoothing.ActualSmoothChartStar
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarIntersection
import Schoenflies.CrosscutCells
import Mathlib.Logic.Equiv.Fin.Rotate

set_option autoImplicit false
open Set Metric Schoenflies
namespace CurveComplex.FiniteStarGeometry

abbrev I := CurveComplex.Interval
abbrev zeroI : I := ⟨0, by norm_num⟩
abbrev oneI : I := ⟨1, by norm_num⟩

def armPrefix {J : Type} (γ : J → I → Plane) (j : J) (b : I) : Set Plane :=
  γ j '' {t : I | t.val ≤ b.val}

def tail {J : Type} (γ : J → I → Plane) (j : J) (b : I) : Set Plane :=
  γ j '' {t : I | b.val ≤ t.val}

noncomputable def circlePoint (o : Plane) (ρ θ : ℝ) : Plane :=
  o + ρ • Plane.mk (Real.cos θ) (Real.sin θ)

/-- Supported actual geometric output, not a normalization input assumption.
Tails of the original full arms may reenter arbitrary round disks. The final
core radius is produced only AFTER all prefixes are straightened. -/
structure RadializedStar {J : Type} [Fintype J]
    (γ : J → I → Plane) (o : Plane) (V : Set Plane) where
  H : Plane ≃ₜ Plane
  supportRadius : ℝ
  support_pos : 0 < supportRadius
  support_subset : closedBall o supportRadius ⊆ V
  fixes_center : H o = o
  fixes_exterior : ∀ x, x ∉ ball o supportRadius → H x = x
  cut : J → I
  cut_pos : ∀ j, 0 < (cut j).val
  cut_lt_one : ∀ j, (cut j).val < 1
  vector : J → Plane
  vector_nonzero : ∀ j, vector j ≠ 0
  prefix_image : ∀ j, H '' armPrefix γ j (cut j) = segment ℝ o (o + vector j)
  distinct_rays : ∀ i j, i ≠ j →
    Disjoint (segment ℝ o (o + vector i) \ {o})
      (segment ℝ o (o + vector j) \ {o})
  coreRadius : ℝ
  core_pos : 0 < coreRadius
  core_lt_support : coreRadius < supportRadius
  core_lt_length : ∀ j, coreRadius < ‖vector j‖
  excludes_tails : ∀ j,
    Disjoint (H '' tail γ j (cut j)) (closedBall o coreRadius)

/-- Pointed one/two-arm seed in an arbitrary prescribed open neighborhood.
No complementary Jordan arc, initial straightness, single metric-disk crossing,
or supported pointed extension is assumed. -/
theorem pointed_one_or_two_arm_relative_seed
    {J : Type} [Fintype J] (γ : J → I → Plane) (o : Plane)
    (hγ : ∀ j, Topology.IsClosedEmbedding (γ j))
    (hstart : ∀ j, γ j zeroI = o)
    (hmeet : ∀ i j, i ≠ j → Set.range (γ i) ∩ Set.range (γ j) = {o})
    (hcard : Fintype.card J = 1 ∨ Fintype.card J = 2)
    (V : Set Plane) (hV : IsOpen V) (hoV : o ∈ V) :
    ∃ R : RadializedStar γ o V,
      ∀ i j, i ≠ j → ∃ a : ℝ, 0 < a ∧ R.vector j = -a • R.vector i := by
  classical
  have twoArm {o a b : Plane} (α : Path o a) (β : Path o b)
      (hα : Function.Injective α) (hβ : Function.Injective β)
      (hmeet : range α ∩ range β = {o})
      (V : Set Plane) (hV : IsOpen V) (hoV : o ∈ V) :
      ∃ (F : Plane ≃ₜ Plane) (R : ℝ) (c d : I) (v : Plane),
        0 < R ∧ closedBall o R ⊆ V ∧ F o = o ∧
        (∀ x, x ∉ ball o R → F x = x) ∧
        0 < c ∧ c < 1 ∧ 0 < d ∧ d < 1 ∧ v ≠ 0 ∧
        F '' (α '' Icc 0 c) = segment ℝ o (o+v) ∧
        F '' (β '' Icc 0 d) = segment ℝ o (o-v) := by
    have square {a b : Plane} (α : Path 0 a) (β : Path 0 b)
        (hα : Function.Injective α) (hβ : Function.Injective β)
        (hmeet : range α ∩ range β = {0})
        (ha : a ∉ Plane.openSquare 0 1) (hb : b ∉ Plane.openSquare 0 1) :
        ∃ (F : Plane ≃ₜ Plane) (c d : I) (v : Plane),
          F 0 = 0 ∧ (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
          0 < c ∧ c < 1 ∧ 0 < d ∧ d < 1 ∧ v ≠ 0 ∧
          F '' (α '' Icc 0 c) = segment ℝ 0 v ∧
          F '' (β '' Icc 0 d) = segment ℝ 0 (-v) := by
      have nonanti {a b : Schoenflies.Plane} (α : Path 0 a) (β : Path 0 b)
          (hα : Function.Injective α) (hβ : Function.Injective β)
          (hmeet : range α ∩ range β = {0})
          (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
          (hαi : ∀ t : I, t < 1 → α t ∈ Schoenflies.Plane.openSquare 0 1)
          (hβi : ∀ t : I, t < 1 → β t ∈ Schoenflies.Plane.openSquare 0 1)
          (hind : ∀ r s : ℝ, r • a = s • b → r = 0 ∧ s = 0) :
          ∃ (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (c d : I),
            F 0 = 0 ∧ (∀ x, x ∉ Schoenflies.Plane.openSquare 0 1 → F x = x) ∧
            0 < c ∧ c < 1 ∧ 0 < d ∧ d < 1 ∧
            F '' (α '' Icc 0 c) = segment ℝ 0 ((1/4:ℝ) • a) ∧
            F '' (β '' Icc 0 d) = segment ℝ 0 ((-1/4:ℝ) • a) := by
        have pointed {A B : Set Plane} {a b p : Plane}
            (hA : IsArcBetween A a b) (hB : IsArcBetween B a b)
            (hpA : p ∈ A \ {a,b}) (hpB : p ∈ B \ {a,b})
            (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
            (hAi : A \ {a,b} ⊆ Plane.openSquare 0 1)
            (hBi : B \ {a,b} ⊆ Plane.openSquare 0 1) :
            ∃ F : Plane ≃ₜ Plane, F p = p ∧ F '' A = B ∧
              ∀ x, x ∉ Plane.openSquare 0 1 → F x = x := by
          obtain ⟨e⟩ := exists_arcHomeo hA hB
          have hpE : e.toFun p ∈ B \ {a,b} := by
            refine ⟨e.mapsTo hpA.1, ?_⟩
            intro hm
            have hcases : e.toFun p = a ∨ e.toFun p = b := by simpa using hm
            rcases hcases with he | he
            · have hpa : p = a := e.injOn hpA.1 hA.left_mem (he.trans e.map_left.symm)
              exact hpA.2 (by simp [hpa])
            · have hpb : p = b := e.injOn hpA.1 hA.right_mem (he.trans e.map_right.symm)
              exact hpA.2 (by simp [hpb])
          obtain ⟨g, hgp⟩ := exists_marked_arcHomeo hB hpE hpB
          let h : ArcHomeo A B a b a b := {
            toFun := g.toFun ∘ e.toFun
            invFun := e.invFun ∘ g.invFun
            continuousOn_toFun := g.continuousOn_toFun.comp e.continuousOn_toFun e.mapsTo
            continuousOn_invFun := e.continuousOn_invFun.comp g.continuousOn_invFun g.mapsTo_invFun
            leftInvOn := by
              intro x hx
              change e.invFun (g.invFun (g.toFun (e.toFun x))) = x
              rw [g.leftInvOn (e.mapsTo hx), e.leftInvOn hx]
            rightInvOn := by
              intro x hx
              change g.toFun (e.toFun (e.invFun (g.invFun x))) = x
              rw [e.rightInvOn (g.mapsTo_invFun hx), g.rightInvOn hx]
            image_eq := by rw [image_comp, e.image_eq, g.image_eq]
            map_left := by change g.toFun (e.toFun a) = a; rw [e.map_left,g.map_left]
            map_right := by change g.toFun (e.toFun b) = b; rw [e.map_right,g.map_right] }
          obtain ⟨F, hF, hFB, hfix⟩ :=
            prescribed_relative_crosscut_replacement A B a b hA hB ha hb hAi hBi h
          refine ⟨F, ?_, hFB, hfix⟩
          exact (hF p hpA.1).trans hgp
        have joined {a p b : Schoenflies.Plane} (γ : Path a p) (δ : Path p b)
            (hγ : Function.Injective γ) (hδ : Function.Injective δ)
            (hinter : range γ ∩ range δ = {p}) :
            IsArcBetween (range γ ∪ range δ) a b ∧
              p ∈ (range γ ∪ range δ) \ {a,b} := by
          let η := γ.trans δ
          have hη : Function.Injective η := LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter γ δ hγ hδ hinter
          constructor
          · refine ⟨η.extend, η.continuous_extend.continuousOn, ?_, ?_, η.extend_zero, η.extend_one⟩
            · intro s hs t ht he
              rw [Path.extend_apply _ hs, Path.extend_apply _ ht] at he
              exact congrArg Subtype.val (hη he)
            · exact (η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans (Path.trans_range γ δ)
          · refine ⟨Or.inl ⟨1,γ.target⟩, ?_⟩
            intro hp
            have hcases : p = a ∨ p = b := by simpa using hp
            rcases hcases with ha | hb
            · have he : (1 : I) = 0 := hγ (γ.target.trans (ha.trans γ.source.symm))
              exact one_ne_zero he
            · have he : (0 : I) = 1 := hδ (δ.source.trans (hb.trans δ.target.symm))
              exact zero_ne_one he
        have target (a b : Schoenflies.Plane) (ε : ℝ)
            (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
            (hε : 0 < ε) (hε1 : ε < 1)
            (hind : ∀ r s : ℝ, r • a = s • b → r = 0 ∧ s = 0) :
            let B := segment ℝ a (-ε • a) ∪ segment ℝ (-ε • a) b
            IsArcBetween B a b ∧ 0 ∈ B \ {a,b} ∧
              B \ {a,b} ⊆ Schoenflies.Plane.openSquare 0 1 := by
          let q : Schoenflies.Plane := -ε • a
          have hqa : Schoenflies.Plane.supNorm q = ε := by
            change Schoenflies.Plane.supNorm (-ε • a) = ε
            rw [Schoenflies.Plane.supNorm_smul, abs_neg, abs_of_pos hε]
            rw [show Schoenflies.Plane.supNorm a = 1 from ha, mul_one]
          have haN : Schoenflies.Plane.supNorm a = 1 := ha
          have hbN : Schoenflies.Plane.supNorm b = 1 := hb
          have haq : a ≠ q := by intro he; rw [he,hqa] at haN; linarith
          have hqb : q ≠ b := by intro he; rw [he,hbN] at hqa; linarith
          have hinter : segment ℝ a q ∩ segment ℝ q b = {q} := by
            ext x
            constructor
            · rintro ⟨hx,hx'⟩
              obtain ⟨r,s,hr,hs,hrs,hx⟩ := hx
              obtain ⟨u,v,hu,hv,huv,hx'⟩ := hx'
              have he : (r - s * ε + u * ε) • a = v • b := by
                calc
                  (r - s * ε + u * ε) • a = (r • a + s • q) - u • q := by dsimp [q]; module
                  _ = v • b := by rw [hx, ← hx']; module
              have hv0 := (hind _ _ he).2
              have hu1 : u = 1 := by linarith
              have hxe : x = q := by rw [← hx',hv0,hu1]; simp
              simpa using hxe
            · intro hx
              have hxe : x = q := by simpa using hx
              subst x
              exact ⟨right_mem_segment _ _ _,left_mem_segment _ _ _⟩
          let γ := Path.segment a q
          let δ := Path.segment q b
          have hη : Function.Injective (γ.trans δ) :=
            LeanEval.Topology.ClassificationOfSurfaces.Moise.Path.trans_injective_of_range_inter γ δ (Path.segment_injective_of_ne haq)
              (Path.segment_injective_of_ne hqb) (by simpa [γ,δ,Path.range_segment] using hinter)
          let η := γ.trans δ
          have hA : IsArcBetween (segment ℝ a q ∪ segment ℝ q b) a b := by
            refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
            · intro s hs t ht he
              rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
              exact congrArg Subtype.val (hη he)
            · exact (η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans
                (by simpa [η,γ,δ,Path.range_segment] using Path.trans_range γ δ)
          have ha0 : a ≠ 0 := by
            intro he
            have hh := (hind 1 0 (by simp [he])).1
            norm_num at hh
          have hb0 : b ≠ 0 := by
            intro he
            have hh := (hind 0 1 (by simp [he])).2
            norm_num at hh
          have hzero : (0 : Schoenflies.Plane) ∈ segment ℝ a q := by
            refine ⟨ε/(1+ε), 1/(1+ε), by positivity, by positivity, ?_, ?_⟩
            · field_simp [ne_of_gt (show 0 < 1+ε by positivity)]
              ring
            · dsimp [q]
              module
          have hqi : q ∈ interior (Schoenflies.Plane.closedSquare 0 1) := by
            rw [interior_closedSquare_zero_one,mem_openSquare_zero_one,hqa]
            exact hε1
          have hac : a ∈ Schoenflies.Plane.closedSquare 0 1 := mem_closedSquare_zero_one.mpr haN.le
          have hbc : b ∈ Schoenflies.Plane.closedSquare 0 1 := mem_closedSquare_zero_one.mpr hbN.le
          refine ⟨hA, ⟨Or.inl hzero,by simpa using ⟨Ne.symm ha0,Ne.symm hb0⟩⟩, ?_⟩
          intro x hx
          have hxa : x ≠ a := by intro he; exact hx.2 (by simp [he])
          have hxb : x ≠ b := by intro he; exact hx.2 (by simp [he])
          by_cases hxq : x = q
          · simpa [hxq,interior_closedSquare_zero_one] using hqi
          · rw [← interior_closedSquare_zero_one]
            rcases hx.1 with hx | hx
            · exact (Schoenflies.Plane.convex_closedSquare 0 1).openSegment_self_interior_subset_interior
                hac hqi (mem_openSegment_of_ne_left_right hxa.symm (Ne.symm hxq) hx)
            · exact (Schoenflies.Plane.convex_closedSquare 0 1).openSegment_interior_self_subset_interior
                hqi hbc (mem_openSegment_of_ne_left_right (Ne.symm hxq) hxb.symm hx)
        have pullback {p b q r s : Plane} (γ : Path p b) (hγ : Function.Injective γ)
            (F : Plane ≃ₜ Plane) (B C : Set Plane)
            (hC : IsArcBetween C r s) (hB : IsArcBetween B (F p) q)
            (hFC : F '' range γ ⊆ C) (hBC : B ⊆ C)
            (hq : q ∈ F '' range γ) (hqp : q ≠ F p) (hqb : q ≠ F b) :
            ∃ c : I, 0 < c ∧ c < 1 ∧ F '' (γ '' Icc 0 c) = B := by
          obtain ⟨x,⟨c,rfl⟩,hcq⟩ := hq
          have hc0 : c ≠ 0 := by intro he; subst c; exact hqp (hcq.symm.trans (congrArg F γ.source))
          have hc1 : c ≠ 1 := by intro he; subst c; exact hqb (hcq.symm.trans (congrArg F γ.target))
          have hc : 0 < c := lt_of_le_of_ne c.property.1 hc0.symm
          have hclt : c < 1 := lt_of_le_of_ne c.property.2 hc1
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
          refine ⟨c,hc,hclt,?_⟩
          exact hrange.symm.trans (hA.eq_of_subset_arc hB hC hAC hBC)
        have ha0 : a ≠ 0 := by
          intro he
          have hh := (hind 1 0 (by simp [he])).1
          norm_num at hh
        have hb0 : b ≠ 0 := by
          intro he
          have hh := (hind 0 1 (by simp [he])).2
          norm_num at hh
        have hαrev : Function.Injective α.symm := by
          intro s t he
          have hh := congrArg Subtype.val (hα he)
          change 1-(s:ℝ) = 1-(t:ℝ) at hh
          apply Subtype.ext
          linarith
        obtain ⟨hA,h0A⟩ := joined α.symm β hαrev hβ (by simpa [Path.symm_range] using hmeet)
        have hA' : IsArcBetween (range α ∪ range β) a b := by simpa [Path.symm_range] using hA
        have h0A' : (0 : Plane) ∈ (range α ∪ range β) \ {a,b} := by simpa [Path.symm_range] using h0A
        have hAi : (range α ∪ range β) \ {a,b} ⊆ Plane.openSquare 0 1 := by
          intro x hx
          rcases hx.1 with ⟨t,rfl⟩ | ⟨t,rfl⟩
          · apply hαi
            have ht : t ≠ 1 := by intro he; subst t; exact hx.2 (by simp [α.target])
            exact lt_of_le_of_ne t.property.2 ht
          · apply hβi
            have ht : t ≠ 1 := by intro he; subst t; exact hx.2 (by simp [β.target])
            exact lt_of_le_of_ne t.property.2 ht
        let q : Plane := -(1/2:ℝ) • a
        let B := segment ℝ a q ∪ segment ℝ q b
        obtain ⟨hB,h0B,hBi⟩ := target a b (1/2) ha hb (by norm_num) (by norm_num) hind
        change IsArcBetween B a b at hB
        change (0 : Plane) ∈ B \ {a,b} at h0B
        change B \ {a,b} ⊆ Plane.openSquare 0 1 at hBi
        obtain ⟨F,hF0,hFB,hfix⟩ := pointed hA' hB h0A' h0B ha hb hAi hBi
        have haout : a ∉ Plane.openSquare 0 1 := by
          intro hm
          have hn := mem_openSquare_zero_one.mp hm
          have haN : Plane.supNorm a = 1 := ha
          rw [haN] at hn
          exact lt_irrefl _ hn
        have hbout : b ∉ Plane.openSquare 0 1 := by
          intro hm
          have hn := mem_openSquare_zero_one.mp hm
          have hbN : Plane.supNorm b = 1 := hb
          rw [hbN] at hn
          exact lt_irrefl _ hn
        have hFa : F a = a := hfix a haout
        have hFb : F b = b := hfix b hbout
        have imageArc {u v : Plane} (γ : Path u v) (hγ : Function.Injective γ) :
            IsArcBetween (F '' range γ) (F u) (F v) := by
          let η : Path (F u) (F v) := {
            toFun := F ∘ γ
            continuous_toFun := F.continuous.comp γ.continuous
            source' := congrArg F γ.source
            target' := congrArg F γ.target }
          have hη : Function.Injective η := fun s t he => hγ (F.injective he)
          refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
          · intro s hs t ht he
            rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
            exact congrArg Subtype.val (hη he)
          · exact (η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans
              (by exact range_comp F γ)
        have hFα : IsArcBetween (F '' range α) 0 a := by simpa [hF0,hFa] using imageArc α hα
        have hFβ : IsArcBetween (F '' range β) 0 b := by simpa [hF0,hFb] using imageArc β hβ
        have hFαB : F '' range α ⊆ B := by rw [←hFB]; exact image_mono subset_union_left
        have hFβB : F '' range β ⊆ B := by rw [←hFB]; exact image_mono subset_union_right
        have h0aq : (0 : Plane) ∈ segment ℝ a q := by
          refine ⟨(1/3:ℝ),(2/3:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
          dsimp [q]
          module
        have h0aB : segment ℝ 0 a ⊆ B :=
          ((convex_segment a q).segment_subset h0aq (left_mem_segment ℝ a q)).trans subset_union_left
        have h0qB : segment ℝ 0 q ⊆ B :=
          ((convex_segment a q).segment_subset h0aq (right_mem_segment ℝ a q)).trans subset_union_left
        have hαimage : F '' range α = segment ℝ 0 a :=
          hFα.eq_of_subset_arc (isArcBetween_segment ha0.symm) hB hFαB h0aB
        have hq0 : q ≠ 0 := by
          intro he
          have hh : (-1/2:ℝ) = 0 := (hind (-1/2) 0 (by simpa [q] using he)).1
          norm_num at hh
        have hqb : q ≠ b := by
          intro he
          have hh : (1:ℝ) = 0 := (hind (-1/2) 1 (by
            have hh : (-1/2:ℝ) • a = q := by dsimp [q]; module
            simpa using hh.trans he)).2
          norm_num at hh
        have hmeet2 : segment ℝ 0 q ∩ segment ℝ q b = {q} := by
          ext x
          constructor
          · rintro ⟨hx,hx'⟩
            obtain ⟨r,s,hr,hs,hrs,hx⟩ := hx
            obtain ⟨u,v,hu,hv,huv,hx'⟩ := hx'
            have he : ((u-s)/2) • a = v • b := by
              calc
                ((u-s)/2) • a = (r • (0:Plane) + s • q) - u • q := by dsimp [q]; module
                _ = v • b := by rw [hx,←hx']; module
            have hv0 := (hind _ _ he).2
            have hu1 : u = 1 := by linarith
            have hxe : x = q := by rw [←hx',hv0,hu1]; simp
            simpa using hxe
          · intro hx
            have hxe : x = q := by simpa using hx
            subst x
            exact ⟨right_mem_segment _ _ _,left_mem_segment _ _ _⟩
        have hB2 : IsArcBetween (segment ℝ 0 q ∪ segment ℝ q b) 0 b := by
          simpa [Path.range_segment] using (joined (Path.segment 0 q) (Path.segment q b)
            (Path.segment_injective_of_ne hq0.symm) (Path.segment_injective_of_ne hqb)
            (by simpa [Path.range_segment] using hmeet2)).1
        have hB2B : segment ℝ 0 q ∪ segment ℝ q b ⊆ B := union_subset h0qB subset_union_right
        have hβimage : F '' range β = segment ℝ 0 q ∪ segment ℝ q b :=
          hFβ.eq_of_subset_arc hB2 hB hFβB hB2B
        let z : Plane := (1/4:ℝ) • a
        let w : Plane := (-1/4:ℝ) • a
        have hz0 : z ≠ 0 := by
          intro he
          have hh : (1/4:ℝ) = 0 := (hind (1/4) 0 (by simpa [z] using he)).1
          norm_num at hh
        have hw0 : w ≠ 0 := by
          intro he
          have hh : (-1/4:ℝ) = 0 := (hind (-1/4) 0 (by simpa [w] using he)).1
          norm_num at hh
        have hza : z ≠ a := by
          intro he
          have hh : (1/4:ℝ) = 1 := by
            apply smul_left_injective ℝ ha0
            simpa [z] using he
          norm_num at hh
        have hwb : w ≠ b := by
          intro he
          have hh : (1:ℝ) = 0 := (hind (-1/4) 1 (by simpa [w] using he)).2
          norm_num at hh
        have hzaSeg : z ∈ segment ℝ 0 a := by
          refine ⟨(3/4:ℝ),(1/4:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
          simp [z]
        have hwqSeg : w ∈ segment ℝ 0 q := by
          refine ⟨(1/2:ℝ),(1/2:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
          dsimp [w,q]
          module
        have hzB : segment ℝ 0 z ⊆ B :=
          ((convex_segment 0 a).segment_subset (left_mem_segment ℝ 0 a) hzaSeg).trans h0aB
        have hwB : segment ℝ 0 w ⊆ B :=
          ((convex_segment 0 q).segment_subset (left_mem_segment ℝ 0 q) hwqSeg).trans h0qB
        obtain ⟨c,hc,hc1,hcim⟩ := pullback α hα F (segment ℝ 0 z) B hB
          (by simpa [hF0] using isArcBetween_segment hz0.symm) hFαB hzB
          (by rw [hαimage]; exact hzaSeg) (by simpa [hF0] using hz0) (by simpa [hFa] using hza)
        obtain ⟨d,hd,hd1,hdim⟩ := pullback β hβ F (segment ℝ 0 w) B hB
          (by simpa [hF0] using isArcBetween_segment hw0.symm) hFβB hwB
          (by rw [hβimage]; exact Or.inl hwqSeg) (by simpa [hF0] using hw0) (by simpa [hFb] using hwb)
        exact ⟨F,c,d,hF0,hfix,hc,hc1,hd,hd1,hcim,hdim⟩
      have anti {a b : Schoenflies.Plane} (α : Path 0 a) (β : Path 0 b)
          (hα : Function.Injective α) (hβ : Function.Injective β)
          (hmeet : range α ∩ range β = {0})
          (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
          (hαi : ∀ t : I, t < 1 → α t ∈ Schoenflies.Plane.openSquare 0 1)
          (hβi : ∀ t : I, t < 1 → β t ∈ Schoenflies.Plane.openSquare 0 1)
          (hanti : b = -a) :
          ∃ (F : Schoenflies.Plane ≃ₜ Schoenflies.Plane) (c d : I),
            F 0 = 0 ∧ (∀ x, x ∉ Schoenflies.Plane.openSquare 0 1 → F x = x) ∧
            0 < c ∧ c < 1 ∧ 0 < d ∧ d < 1 ∧
            F '' (α '' Icc 0 c) = segment ℝ 0 ((1/4:ℝ) • a) ∧
            F '' (β '' Icc 0 d) = segment ℝ 0 ((-1/4:ℝ) • a) := by
        have pullback {p b q r s : Plane} (γ : Path p b) (hγ : Function.Injective γ)
            (F : Plane ≃ₜ Plane) (B C : Set Plane)
            (hC : IsArcBetween C r s) (hB : IsArcBetween B (F p) q)
            (hFC : F '' range γ ⊆ C) (hBC : B ⊆ C)
            (hq : q ∈ F '' range γ) (hqp : q ≠ F p) (hqb : q ≠ F b) :
            ∃ c : I, 0 < c ∧ c < 1 ∧ F '' (γ '' Icc 0 c) = B := by
          obtain ⟨x,⟨c,rfl⟩,hcq⟩ := hq
          have hc0 : c ≠ 0 := by intro he; subst c; exact hqp (hcq.symm.trans (congrArg F γ.source))
          have hc1 : c ≠ 1 := by intro he; subst c; exact hqb (hcq.symm.trans (congrArg F γ.target))
          have hc : 0 < c := lt_of_le_of_ne c.property.1 hc0.symm
          have hclt : c < 1 := lt_of_le_of_ne c.property.2 hc1
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
          refine ⟨c,hc,hclt,?_⟩
          exact hrange.symm.trans (hA.eq_of_subset_arc hB hC hAC hBC)
        have haN : Plane.supNorm a = 1 := ha
        have hbN : Plane.supNorm b = 1 := hb
        have ha0 : a ≠ 0 := by intro he; simp [he,Plane.supNorm] at haN
        have hb0 : b ≠ 0 := by intro he; simp [he,Plane.supNorm] at hbN
        have hab : a ≠ b := by
          intro he
          have hh : (1:ℝ) • a = (-1:ℝ) • a := by simpa [hanti] using he
          have hh' := smul_left_injective ℝ ha0 hh
          norm_num at hh'
        have hαrev : Function.Injective α.symm := by
          intro s t he
          have hh := congrArg Subtype.val (hα he)
          change 1-(s:ℝ) = 1-(t:ℝ) at hh
          apply Subtype.ext
          linarith
        obtain ⟨hA,h0A⟩ := SeedProbeHeaders.joined_embedded_arms_arc α.symm β hαrev hβ
          (by simpa [Path.symm_range] using hmeet)
        have hA' : IsArcBetween (range α ∪ range β) a b := by simpa [Path.symm_range] using hA
        have h0A' : (0 : Plane) ∈ (range α ∪ range β) \ {a,b} := by simpa [Path.symm_range] using h0A
        have hAi : (range α ∪ range β) \ {a,b} ⊆ Plane.openSquare 0 1 := by
          intro x hx
          rcases hx.1 with ⟨t,rfl⟩ | ⟨t,rfl⟩
          · apply hαi
            have ht : t ≠ 1 := by intro he; subst t; exact hx.2 (by simp [α.target])
            exact lt_of_le_of_ne t.property.2 ht
          · apply hβi
            have ht : t ≠ 1 := by intro he; subst t; exact hx.2 (by simp [β.target])
            exact lt_of_le_of_ne t.property.2 ht
        let B := segment ℝ a b
        have hB : IsArcBetween B a b := isArcBetween_segment hab
        have hzero : (0 : Plane) ∈ B := by
          refine ⟨(1/2:ℝ),(1/2:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
          rw [hanti]
          module
        have h0B : (0 : Plane) ∈ B \ {a,b} := ⟨hzero, by simp [ha0.symm,hb0.symm]⟩
        have hBi : B \ {a,b} ⊆ Plane.openSquare 0 1 := by
          intro x hx
          obtain ⟨r,s,hr,hs,hrs,he⟩ := hx.1
          have hr0 : r ≠ 0 := by
            intro he0
            have hs1 : s = 1 := by linarith
            have hxb : x = b := by rw [he0,hs1] at he; simpa using he.symm
            exact hx.2 (by simp [hxb])
          have hs0 : s ≠ 0 := by
            intro he0
            have hr1 : r = 1 := by linarith
            have hxa : x = a := by rw [he0,hr1] at he; simpa using he.symm
            exact hx.2 (by simp [hxa])
          have hrpos := lt_of_le_of_ne hr hr0.symm
          have hspos := lt_of_le_of_ne hs hs0.symm
          have hxe : x = (r-s) • a := by rw [←he,hanti]; module
          rw [mem_openSquare_zero_one,hxe,Plane.supNorm_smul,haN,mul_one]
          rw [abs_lt]
          constructor <;> linarith
        obtain ⟨F,hF0,hFB,hfix⟩ := SeedProbeHeaders.pointed_relative_crosscut_replacement
          hA' hB h0A' h0B ha hb hAi hBi
        have haout : a ∉ Plane.openSquare 0 1 := by
          intro hm
          have hn := mem_openSquare_zero_one.mp hm
          rw [haN] at hn
          exact lt_irrefl _ hn
        have hbout : b ∉ Plane.openSquare 0 1 := by
          intro hm
          have hn := mem_openSquare_zero_one.mp hm
          rw [hbN] at hn
          exact lt_irrefl _ hn
        have hFa : F a = a := hfix a haout
        have hFb : F b = b := hfix b hbout
        have imageArc {u v : Plane} (γ : Path u v) (hγ : Function.Injective γ) :
            IsArcBetween (F '' range γ) (F u) (F v) := by
          let η : Path (F u) (F v) := {
            toFun := F ∘ γ
            continuous_toFun := F.continuous.comp γ.continuous
            source' := congrArg F γ.source
            target' := congrArg F γ.target }
          have hη : Function.Injective η := fun s t he => hγ (F.injective he)
          refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
          · intro s hs t ht he
            rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
            exact congrArg Subtype.val (hη he)
          · exact (η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))).trans (range_comp F γ)
        have hFα : IsArcBetween (F '' range α) 0 a := by simpa [hF0,hFa] using imageArc α hα
        have hFβ : IsArcBetween (F '' range β) 0 b := by simpa [hF0,hFb] using imageArc β hβ
        have hFαB : F '' range α ⊆ B := by rw [←hFB]; exact image_mono subset_union_left
        have hFβB : F '' range β ⊆ B := by rw [←hFB]; exact image_mono subset_union_right
        have h0aB : segment ℝ 0 a ⊆ B :=
          (convex_segment a b).segment_subset hzero (left_mem_segment ℝ a b)
        have h0bB : segment ℝ 0 b ⊆ B :=
          (convex_segment a b).segment_subset hzero (right_mem_segment ℝ a b)
        have hαimage : F '' range α = segment ℝ 0 a :=
          hFα.eq_of_subset_arc (isArcBetween_segment ha0.symm) hB hFαB h0aB
        have hβimage : F '' range β = segment ℝ 0 b :=
          hFβ.eq_of_subset_arc (isArcBetween_segment hb0.symm) hB hFβB h0bB
        let z : Plane := (1/4:ℝ) • a
        let w : Plane := (-1/4:ℝ) • a
        have hz0 : z ≠ 0 := smul_ne_zero (by norm_num) ha0
        have hw0 : w ≠ 0 := smul_ne_zero (by norm_num) ha0
        have hza : z ≠ a := by
          intro he
          have hh : (1/4:ℝ) = 1 := smul_left_injective ℝ ha0 (by simpa [z] using he)
          norm_num at hh
        have hwb : w ≠ b := by
          intro he
          have hh : (-1/4:ℝ) = -1 := smul_left_injective ℝ ha0 (by simpa [w,hanti] using he)
          norm_num at hh
        have hzaSeg : z ∈ segment ℝ 0 a := by
          refine ⟨(3/4:ℝ),(1/4:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
          simp [z]
        have hwbSeg : w ∈ segment ℝ 0 b := by
          refine ⟨(3/4:ℝ),(1/4:ℝ),by norm_num,by norm_num,by norm_num,?_⟩
          rw [hanti]
          dsimp [w]
          module
        have hzB : segment ℝ 0 z ⊆ B :=
          ((convex_segment 0 a).segment_subset (left_mem_segment ℝ 0 a) hzaSeg).trans h0aB
        have hwB : segment ℝ 0 w ⊆ B :=
          ((convex_segment 0 b).segment_subset (left_mem_segment ℝ 0 b) hwbSeg).trans h0bB
        obtain ⟨c,hc,hc1,hcim⟩ := pullback α hα F (segment ℝ 0 z) B hB
          (by simpa [hF0] using isArcBetween_segment hz0.symm) hFαB hzB
          (by rw [hαimage]; exact hzaSeg) (by simpa [hF0] using hz0) (by simpa [hFa] using hza)
        obtain ⟨d,hd,hd1,hdim⟩ := pullback β hβ F (segment ℝ 0 w) B hB
          (by simpa [hF0] using isArcBetween_segment hw0.symm) hFβB hwB
          (by rw [hβimage]; exact hwbSeg) (by simpa [hF0] using hw0) (by simpa [hFb] using hwb)
        exact ⟨F,c,d,hF0,hfix,hc,hc1,hd,hd1,hcim,hdim⟩
      have indep (a b : Plane) (ha : a ∈ modelCurve) (hb : b ∈ modelCurve)
          (hab : a ≠ b) (hanti : b ≠ -a) :
          ∀ r s : ℝ, r • a = s • b → r = 0 ∧ s = 0 := by
        intro r s he
        have hnorm : |r| = |s| := by
          have hn := congrArg Plane.supNorm he
          rw [Plane.supNorm_smul,Plane.supNorm_smul,
            show Plane.supNorm a = 1 from ha, show Plane.supNorm b = 1 from hb,
            mul_one,mul_one] at hn
          exact hn
        by_cases hs : s = 0
        · refine ⟨?_,hs⟩
          rw [hs,abs_zero] at hnorm
          exact abs_eq_zero.mp hnorm
        · exfalso
          rcases abs_eq_abs.mp hnorm with hrs | hrs
          · rw [hrs] at he
            exact hab (smul_right_injective Plane hs he)
          · have hh : s • a = s • (-b) := by
              rw [hrs] at he
              calc
                s • a = -((-s) • a) := by simp
                _ = -(s • b) := congrArg Neg.neg he
                _ = s • (-b) := (smul_neg s b).symm
            have haeq := smul_right_injective Plane hs hh
            apply hanti
            rw [haeq,neg_neg]
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
      have hzero : (0 : Plane) ∈ Plane.openSquare 0 1 := by
        rw [mem_openSquare_zero_one]
        simp [Plane.supNorm]
      obtain ⟨tα,htα,hfrontα,hbeforeα⟩ := path_first_exit_frontier α _ (Plane.isOpen_openSquare 0 1) hzero ha
      obtain ⟨tβ,htβ,hfrontβ,hbeforeβ⟩ := path_first_exit_frontier β _ (Plane.isOpen_openSquare 0 1) hzero hb
      let kα : I → I := fun t => ⟨(tα:ℝ)*(t:ℝ),by
        constructor
        · exact mul_nonneg tα.property.1 t.property.1
        · nlinarith [tα.property.1,tα.property.2,t.property.1,t.property.2]⟩
      let kβ : I → I := fun t => ⟨(tβ:ℝ)*(t:ℝ),by
        constructor
        · exact mul_nonneg tβ.property.1 t.property.1
        · nlinarith [tβ.property.1,tβ.property.2,t.property.1,t.property.2]⟩
      let γ : Path 0 (α tα) := {
        toFun := α ∘ kα
        continuous_toFun := α.continuous.comp (by fun_prop)
        source' := by simp [kα,α.source]
        target' := by simp [kα] }
      let δ : Path 0 (β tβ) := {
        toFun := β ∘ kβ
        continuous_toFun := β.continuous.comp (by fun_prop)
        source' := by simp [kβ,β.source]
        target' := by simp [kβ] }
      have hγ : Function.Injective γ := by
        intro s t he
        have hh := congrArg Subtype.val (hα he)
        change (tα:ℝ)*(s:ℝ) = (tα:ℝ)*(t:ℝ) at hh
        exact Subtype.ext (mul_left_cancel₀ (ne_of_gt htα) hh)
      have hδ : Function.Injective δ := by
        intro s t he
        have hh := congrArg Subtype.val (hβ he)
        change (tβ:ℝ)*(s:ℝ) = (tβ:ℝ)*(t:ℝ) at hh
        exact Subtype.ext (mul_left_cancel₀ (ne_of_gt htβ) hh)
      have hγδ : range γ ∩ range δ = {0} := by
        ext x
        constructor
        · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
          have hm : x ∈ range α ∩ range β := ⟨⟨kα s,hs⟩,⟨kβ t,ht⟩⟩
          exact hmeet ▸ hm
        · intro hx
          have hx0 : x = 0 := by simpa using hx
          subst x
          exact ⟨⟨0,γ.source⟩,⟨0,δ.source⟩⟩
      have hγα : ∀ t : I, t < 1 → γ t ∈ Plane.openSquare 0 1 := by
        intro t ht
        apply hbeforeα
        change (tα:ℝ)*(t:ℝ) < tα
        exact mul_lt_of_lt_one_right htα ht
      have hδβ : ∀ t : I, t < 1 → δ t ∈ Plane.openSquare 0 1 := by
        intro t ht
        apply hbeforeβ
        change (tβ:ℝ)*(t:ℝ) < tβ
        exact mul_lt_of_lt_one_right htβ ht
      have hαboundary : α tα ∈ modelCurve := by
        rw [modelCurve_eq_frontier]
        exact Plane.frontier_openSquare_subset 0 1 hfrontα
      have hβboundary : β tβ ∈ modelCurve := by
        rw [modelCurve_eq_frontier]
        exact Plane.frontier_openSquare_subset 0 1 hfrontβ
      have hαzero : α tα ≠ 0 := by
        intro he
        have hh : tα = 0 := hα (he.trans α.source.symm)
        exact ne_of_gt htα hh
      have hexits : α tα ≠ β tβ := by
        intro he
        have hm : α tα ∈ range α ∩ range β := ⟨⟨tα,rfl⟩,⟨tβ,he.symm⟩⟩
        have hm0 : α tα ∈ ({0} : Set Plane) := hmeet ▸ hm
        have h0 : α tα = 0 := by simpa using hm0
        exact hαzero h0
      have hseed : ∃ (F : Plane ≃ₜ Plane) (c d : I),
          F 0 = 0 ∧ (∀ x, x ∉ Plane.openSquare 0 1 → F x = x) ∧
          0 < c ∧ c < 1 ∧ 0 < d ∧ d < 1 ∧
          F '' (γ '' Icc 0 c) = segment ℝ 0 ((1/4:ℝ) • α tα) ∧
          F '' (δ '' Icc 0 d) = segment ℝ 0 ((-1/4:ℝ) • α tα) := by
        by_cases hanti : β tβ = -(α tα)
        · exact anti γ δ hγ hδ hγδ hαboundary hβboundary hγα hδβ hanti
        · exact nonanti γ δ hγ hδ hγδ hαboundary hβboundary hγα hδβ
            (indep _ _ hαboundary hβboundary hexits hanti)
      obtain ⟨F,c,d,hF0,hfix,hc,hc1,hd,hd1,hcim,hdim⟩ := hseed
      let c' : I := ⟨(tα:ℝ)*(c:ℝ),by
        constructor
        · exact mul_nonneg tα.property.1 c.property.1
        · nlinarith [tα.property.1,tα.property.2,c.property.1,c.property.2]⟩
      let d' : I := ⟨(tβ:ℝ)*(d:ℝ),by
        constructor
        · exact mul_nonneg tβ.property.1 d.property.1
        · nlinarith [tβ.property.1,tβ.property.2,d.property.1,d.property.2]⟩
      have hc' : 0 < c' := mul_pos htα hc
      have hd' : 0 < d' := mul_pos htβ hd
      have hc1' : c' < 1 := by
        change (tα:ℝ)*(c:ℝ) < 1
        exact (mul_le_mul_of_nonneg_right tα.property.2 c.property.1).trans_lt (by simpa using hc1)
      have hd1' : d' < 1 := by
        change (tβ:ℝ)*(d:ℝ) < 1
        exact (mul_le_mul_of_nonneg_right tβ.property.2 d.property.1).trans_lt (by simpa using hd1)
      have hγimage : γ '' Icc 0 c = α '' Icc 0 c' := by
          change (α ∘ kα) '' Icc 0 c = α '' Icc 0 c'
          exact productImage (fun t => α t) tα c htα
      have hδimage : δ '' Icc 0 d = β '' Icc 0 d' := by
          change (β ∘ kβ) '' Icc 0 d = β '' Icc 0 d'
          exact productImage (fun t => β t) tβ d htβ
      refine ⟨F,c',d',(1/4:ℝ) • α tα,hF0,hfix,hc',hc1',hd',hd1',
        smul_ne_zero (by norm_num) hαzero,?_,?_⟩
      · rw [←hγimage]
        exact hcim
      · rw [←hδimage]
        convert hdim using 2 <;> module
    have window (o a b : Plane) (ha : a ≠ o) (hb : b ≠ o)
        (V : Set Plane) (hV : IsOpen V) (hoV : o ∈ V) :
        ∃ (E : Plane ≃ₜ Plane) (R scale : ℝ), 0 < R ∧ 0 < scale ∧
          closedBall o R ⊆ V ∧ E o = 0 ∧
          E a ∉ Plane.openSquare 0 1 ∧ E b ∉ Plane.openSquare 0 1 ∧
          (∀ x, E x ∈ Plane.openSquare 0 1 → x ∈ ball o R) ∧
          ∀ y, E.symm y = scale • y + o := by
      obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hoV)
      have pos (x : Plane) (hx : x ≠ o) : 0 < Plane.supNorm (x-o) := by
        have hnorm : 0 < ‖x-o‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
        have hbound := Plane.norm_le_sqrt_two_mul_supNorm (x-o)
        by_contra hn
        have hprod : Real.sqrt 2 * Plane.supNorm (x-o) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) (not_lt.mp hn)
        linarith
      let R := ε/2
      let scale := min (R/4) (min (Plane.supNorm (a-o)) (Plane.supNorm (b-o))) / 2
      have hR : 0 < R := half_pos hε
      have hscale : 0 < scale := half_pos (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))
      have hscaleR : scale < R/4 :=
        (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le (min_le_left _ _)
      have hscalea : scale < Plane.supNorm (a-o) :=
        (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le
          ((min_le_right _ _).trans (min_le_left _ _))
      have hscaleb : scale < Plane.supNorm (b-o) :=
        (half_lt_self (lt_min (by positivity) (lt_min (pos a ha) (pos b hb)))).trans_le
          ((min_le_right _ _).trans (min_le_right _ _))
      let E : Plane ≃ₜ Plane := {
        toEquiv := {
          toFun := fun x => scale⁻¹ • (x-o)
          invFun := fun y => scale • y + o
          left_inv := by
            intro x
            dsimp only
            rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hscale),one_smul]
            abel
          right_inv := by
            intro y
            dsimp only
            rw [add_sub_cancel_right,smul_smul,inv_mul_cancel₀ (ne_of_gt hscale),one_smul] }
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      have hEo : E o = 0 := by simp [E]
      have houtside (x : Plane) (hx : scale < Plane.supNorm (x-o)) : E x ∉ Plane.openSquare 0 1 := by
        intro hm
        have hn := mem_openSquare_zero_one.mp hm
        change Plane.supNorm (scale⁻¹ • (x-o)) < 1 at hn
        rw [Plane.supNorm_smul,abs_of_pos (inv_pos.mpr hscale)] at hn
        have hh : Plane.supNorm (x-o) < scale := by
          have ht := mul_lt_mul_of_pos_left hn hscale
          rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt hscale),one_mul,mul_one] at ht
          exact ht
        exact not_lt_of_gt hx hh
      have hinside (x : Plane) (hx : E x ∈ Plane.openSquare 0 1) : x ∈ ball o R := by
        have hsup := mem_openSquare_zero_one.mp hx
        have hsqrt : Real.sqrt 2 < 2 := by
          have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
          have hp := Real.sqrt_nonneg (2:ℝ)
          nlinarith
        have hn : ‖E x‖ < 2 := by
          have hbound := Plane.norm_le_sqrt_two_mul_supNorm (E x)
          have hp := Plane.supNorm_nonneg (E x)
          nlinarith [Real.sqrt_nonneg (2:ℝ)]
        have hxe : x-o = scale • E x := by
          have hh := E.symm_apply_apply x
          change scale • E x + o = x at hh
          have hs := congrArg (fun y : Plane => y-o) hh
          simpa only [add_sub_cancel_right] using hs.symm
        rw [mem_ball,dist_eq_norm,hxe,norm_smul,Real.norm_eq_abs,abs_of_pos hscale]
        exact (mul_lt_mul_of_pos_left hn hscale).trans (by linarith)
      refine ⟨E,R,scale,hR,hscale,?_,hEo,houtside a hscalea,houtside b hscaleb,hinside,fun _ => rfl⟩
      exact (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεV
    have ha : a ≠ o := by
      intro he
      have h10 : (1:I) = 0 := hα (α.target.trans (he.trans α.source.symm))
      exact one_ne_zero h10
    have hb : b ≠ o := by
      intro he
      have h10 : (1:I) = 0 := hβ (β.target.trans (he.trans β.source.symm))
      exact one_ne_zero h10
    obtain ⟨E,R,scale,hR,hscale,hRV,hEo,hEa,hEb,hinside,hinv⟩ := window o a b ha hb V hV hoV
    let α' : Path 0 (E a) := {
      toFun := E ∘ α
      continuous_toFun := E.continuous.comp α.continuous
      source' := (congrArg E α.source).trans hEo
      target' := congrArg E α.target }
    let β' : Path 0 (E b) := {
      toFun := E ∘ β
      continuous_toFun := E.continuous.comp β.continuous
      source' := (congrArg E β.source).trans hEo
      target' := congrArg E β.target }
    have hα' : Function.Injective α' := fun s t he => hα (E.injective he)
    have hβ' : Function.Injective β' := fun s t he => hβ (E.injective he)
    have hrα : range α' = E '' range α := range_comp E α
    have hrβ : range β' = E '' range β := range_comp E β
    have hmeet' : range α' ∩ range β' = {0} := by
      rw [hrα,hrβ,←image_inter E.injective,hmeet,image_singleton,hEo]
    obtain ⟨G,c,d,v,hG0,hfix,hc,hc1,hd,hd1,hv,hαim,hβim⟩ := square α' β' hα' hβ' hmeet' hEa hEb
    let F : Plane ≃ₜ Plane := (E.trans G).trans E.symm
    have hFo : F o = o := by
      change E.symm (G (E o)) = o
      rw [hEo,hG0,←hEo,E.symm_apply_apply]
    have hFfixed (x : Plane) (hx : x ∉ ball o R) : F x = x := by
      have hEx : E x ∉ Plane.openSquare 0 1 := fun hm => hx (hinside x hm)
      change E.symm (G (E x)) = x
      rw [hfix (E x) hEx,E.symm_apply_apply]
    let A : Plane →ᵃ[ℝ] Plane := {
      toFun := fun y => scale • y + o
      linear := scale • LinearMap.id
      map_vadd' := by
        intro x y
        change scale • (y+x) + o = scale • y + (scale • x + o)
        module }
    have hA : (E.symm : Plane → Plane) = (A : Plane → Plane) := funext hinv
    have himage (K : Set Plane) : F '' K = E.symm '' (G '' (E '' K)) := by
      rw [←image_comp,←image_comp]
      rfl
    have hα'prefix : α' '' Icc 0 c = E '' (α '' Icc 0 c) := image_comp E α _
    have hβ'prefix : β' '' Icc 0 d = E '' (β '' Icc 0 d) := image_comp E β _
    refine ⟨F,R,c,d,scale • v,hR,hRV,hFo,hFfixed,hc,hc1,hd,hd1,
      smul_ne_zero (ne_of_gt hscale) hv,?_,?_⟩
    · rw [himage,←hα'prefix,hαim,hA,image_segment]
      simp [A,add_comm]
    · rw [himage,←hβ'prefix,hβim,hA,image_segment]
      simp [A,sub_eq_add_neg,add_comm]
  have auxiliary {o a : Plane} (α : Path o a) (hα : Function.Injective α) :
      ∃ (u : Plane) (δ : Path o u), Function.Injective δ ∧
        range α ∩ range δ = {o} ∧ u ∉ range α := by
    have hA : IsArcBetween (range α) o a := by
      refine ⟨α.extend,α.continuous_extend.continuousOn,?_,?_,α.extend_zero,α.extend_one⟩
      · intro s hs t ht he
        rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
        exact congrArg Subtype.val (hα he)
      · exact α.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))
    obtain ⟨E,u,hE,hu,havoid⟩ := endpoint_access_of_isArcBetween hA
    obtain ⟨f,hf,hi,himage,hf0,hf1⟩ := hE
    let δ : Path o u := {
      toFun := fun t => f t
      continuous_toFun := continuousOn_iff_continuous_restrict.mp hf
      source' := hf0
      target' := hf1 }
    have hδ : Function.Injective δ := by
      intro s t he
      exact Subtype.ext (hi s.property t.property he)
    have hδrange : range δ = E := by
      rw [←himage]
      ext x
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨t,t.property,rfl⟩
      · rintro ⟨t,ht,rfl⟩
        exact ⟨⟨t,ht⟩,rfl⟩
    refine ⟨u,δ,hδ,?_,hu⟩
    ext x
    constructor
    · intro hx
      by_cases hxo : x = o
      · simpa using hxo
      · have hxE : x ∈ E := hδrange ▸ hx.2
        exact False.elim ((havoid ⟨hxE,by simpa using hxo⟩) hx.1)
    · intro hx
      have hxo : x = o := by simpa using hx
      subst x
      exact ⟨⟨0,α.source⟩,⟨0,δ.source⟩⟩
  have core {J : Type} [Fintype J] (γ : J → I → EuclideanSpace ℝ (Fin 2))
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
  let path (j : J) : Path o (γ j oneI) := {
    toFun := γ j
    continuous_toFun := (hγ j).continuous
    source' := hstart j
    target' := rfl }
  have setcut (c : I) : {t : I | t.val ≤ c.val} = Icc 0 c := by
    ext t
    exact ⟨fun h => ⟨t.property.1,h⟩,fun h => h.2⟩
  rcases hcard with hone | htwo
  · obtain ⟨j0,hj⟩ := Fintype.card_eq_one_iff.mp hone
    obtain ⟨u,δ,hδ,hinter,hu⟩ := auxiliary (path j0) (hγ j0).injective
    obtain ⟨F,R,c,d,v,hR,hRV,hFo,hfix,hc,hc1,hd,hd1,hv,hαim,hδim⟩ :=
      twoArm (path j0) δ (hγ j0).injective hδ hinter V hV hoV
    let cuts : J → I := fun _ => c
    let vectors : J → Plane := fun _ => v
    obtain ⟨ρ,hρ,hρR,hρlen,hρtail⟩ := core γ hγ o hstart F hFo cuts
      (fun _ => hc) vectors (fun _ => hv) R hR
    let result : RadializedStar γ o V := {
      H := F
      supportRadius := R
      support_pos := hR
      support_subset := hRV
      fixes_center := hFo
      fixes_exterior := hfix
      cut := cuts
      cut_pos := fun _ => hc
      cut_lt_one := fun _ => hc1
      vector := vectors
      vector_nonzero := fun _ => hv
      prefix_image := by
        intro j
        rw [hj j]
        change F '' (γ j0 '' {t : I | t.val ≤ c.val}) = segment ℝ o (o+v)
        rw [setcut]
        exact hαim
      distinct_rays := by
        intro i j hij
        exact False.elim (hij ((hj i).trans (hj j).symm))
      coreRadius := ρ
      core_pos := hρ
      core_lt_support := hρR
      core_lt_length := hρlen
      excludes_tails := hρtail }
    refine ⟨result,?_⟩
    intro i j hij
    exact False.elim (hij ((hj i).trans (hj j).symm))
  · let e : J ≃ Fin 2 := Fintype.equivFinOfCardEq htwo
    let j0 := e.symm 0
    let j1 := e.symm 1
    have h01 : j0 ≠ j1 := by
      intro he
      have hh : (0:Fin 2) = 1 := e.symm.injective he
      exact (by decide : (0:Fin 2) ≠ 1) hh
    have hall : ∀ j : J, j = j0 ∨ j = j1 := by
      intro j
      obtain ⟨k,rfl⟩ := e.symm.surjective j
      fin_cases k <;> simp [j0,j1]
    obtain ⟨F,R,c,d,v,hR,hRV,hFo,hfix,hc,hc1,hd,hd1,hv,hαim,hβim⟩ :=
      twoArm (path j0) (path j1) (hγ j0).injective (hγ j1).injective
        (hmeet j0 j1 h01) V hV hoV
    let cuts : J → I := fun j => if j = j0 then c else d
    let vectors : J → Plane := fun j => if j = j0 then v else -v
    have hcuts : ∀ j, 0 < cuts j := by intro j; dsimp [cuts]; split <;> assumption
    have hcuts1 : ∀ j, (cuts j).val < 1 := by intro j; dsimp [cuts]; split <;> assumption
    have hvec : ∀ j, vectors j ≠ 0 := by
      intro j
      dsimp [vectors]
      split
      · exact hv
      · exact neg_ne_zero.mpr hv
    obtain ⟨ρ,hρ,hρR,hρlen,hρtail⟩ := core γ hγ o hstart F hFo cuts hcuts vectors hvec R hR
    have hneq : o+v ≠ o-v := by
      intro he
      have hh : v = -v := by simpa [sub_eq_add_neg] using he
      have hh' : (1:ℝ) • v = (-1:ℝ) • v := by simpa using hh
      have hh'' := smul_left_injective ℝ hv hh'
      norm_num at hh''
    have hdis : Disjoint (segment ℝ o (o+v) \ {o}) (segment ℝ o (o-v) \ {o}) :=
      LeanEval.Topology.ClassificationOfSurfaces.Moise.disjoint_radial_segments_away_center
        (norm_pos_iff.mpr hv) (by simp [dist_eq_norm])
        (by simp [dist_eq_norm,sub_eq_add_neg]) hneq
    let result : RadializedStar γ o V := {
      H := F
      supportRadius := R
      support_pos := hR
      support_subset := hRV
      fixes_center := hFo
      fixes_exterior := hfix
      cut := cuts
      cut_pos := hcuts
      cut_lt_one := hcuts1
      vector := vectors
      vector_nonzero := hvec
      prefix_image := by
        intro j
        rcases hall j with rfl | rfl
        · change F '' (γ j0 '' {t : I | t.val ≤ (cuts j0).val}) = segment ℝ o (o+vectors j0)
          simp only [cuts,vectors,ite_true]
          rw [setcut]
          exact hαim
        · change F '' (γ j1 '' {t : I | t.val ≤ (cuts j1).val}) = segment ℝ o (o+vectors j1)
          simp only [cuts,vectors,if_neg (Ne.symm h01)]
          rw [setcut]
          simpa [sub_eq_add_neg,path] using hβim
      distinct_rays := by
        intro i j hij
        rcases hall i with rfl | rfl <;> rcases hall j with rfl | rfl
        · exact False.elim (hij rfl)
        · simpa [vectors,h01.symm,sub_eq_add_neg] using hdis
        · simpa [vectors,h01.symm,sub_eq_add_neg] using hdis.symm
        · exact False.elim (hij rfl)
      coreRadius := ρ
      core_pos := hρ
      core_lt_support := hρR
      core_lt_length := hρlen
      excludes_tails := hρtail }
    refine ⟨result,?_⟩
    intro i j hij
    rcases hall i with rfl | rfl <;> rcases hall j with rfl | rfl
    · exact False.elim (hij rfl)
    · refine ⟨1,by norm_num,?_⟩
      simp [result,vectors,h01.symm]
    · refine ⟨1,by norm_num,?_⟩
      simp [result,vectors,h01.symm]
    · exact False.elim (hij rfl)

end CurveComplex.FiniteStarGeometry

#print axioms CurveComplex.FiniteStarGeometry.pointed_one_or_two_arm_relative_seed
