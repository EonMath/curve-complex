import CurveComplexGenusTwo.Topology.SDRStaticModel.StaticAnnulusPROVED
import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.TerminalAnnulusMotionPROVED
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import Mathlib.Topology.Homotopy.Basic

open Set Topology CurveComplex

namespace CurveComplex.SDRModelAnnulusReview

/-- Source: sdr_static_local_extension/BLOCKER_REPORT.md, model-annulus request.
Only the endpoint image is extended; the input family is retained literally. -/
theorem actual_model_annulus_embedded_circle_family_boundary_fixed_endpoint_extension
    (F : C(Interval × Circle, Circle × Interval))
    (hF : ∀ t : Interval, IsEmbedding (fun z : Circle => F (t, z)))
    (hInterior : ∀ (t : Interval) (z : Circle),
      F (t, z) ∈ Set.univ ×ˢ Set.Ioo (0 : Interval) 1)
    (hInitial : ∀ z : Circle, F (0, z) = (z, ⟨1 / 2, by norm_num⟩)) :
    ∃ H : AmbientIsotopy (Circle × Interval),
      (∀ (t : Interval) (z : Circle), H.map (t, (z, 0)) = (z, 0)) ∧
      (∀ (t : Interval) (z : Circle), H.map (t, (z, 1)) = (z, 1)) ∧
      H.finalMap '' Set.range (fun z : Circle =>
        (z, (⟨1 / 2, by norm_num⟩ : Interval))) =
        Set.range (fun z : Circle => F (1, z)) := by
  let g : Interval × Circle → ℝ := fun q => (F q).2.val
  have hg : Continuous g := F.continuous.snd.subtype_val
  obtain ⟨q, hq, hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hg.continuousOn
  have hq1 : g q < 1 := (hInterior q.1 q.2).2.2
  have hhalf : (1 / 2 : ℝ) ≤ g q := by
    have hh := hmax (show (0, (1 : Circle)) ∈ Set.univ by trivial)
    change g (0,1) ≤ g q at hh
    have hh0 : g (0,1) = 1/2 := by dsimp [g]; rw [hInitial]
    rw [hh0] at hh
    exact hh
  let r : Interval := ⟨(g q + 1) / 2, by constructor <;> linarith⟩
  have hr0 : (0 : Interval) < r := by change 0 < (g q + 1) / 2; linarith
  have hr1 : r < (1 : Interval) := by change (g q + 1) / 2 < 1; linarith
  have hbelow (t : Interval) (z : Circle) : (F (t,z)).2 < r := by
    have hh := hmax (show (t,z) ∈ Set.univ by trivial)
    change g (t,z) ≤ g q at hh
    change g (t,z) < (g q + 1) / 2
    linarith
  let c (t : Interval) : Curve (Circle × Interval) :=
    ⟨fun z => F (t,z), hF t⟩
  let d : Curve (Circle × Interval) :=
    ⟨fun z => (z,r), isEmbedding_prodMkLeft r⟩
  have hangular (t : Interval) : ContinuousMap.Homotopic
      (ContinuousMap.id Circle) (⟨fun z => (c t).map z |>.1,
        (c t).embedded.continuous.fst⟩ : C(Circle,Circle)) := by
    let a : Interval → Interval := fun u =>
      ⟨t.val * u.val, by
        constructor
        · exact mul_nonneg t.property.1 u.property.1
        · calc
            t.val * u.val ≤ t.val * 1 := mul_le_mul_of_nonneg_left u.property.2 t.property.1
            _ ≤ 1 := by simpa using t.property.2⟩
    have ha : Continuous a := (continuous_const.mul continuous_subtype_val).subtype_mk _
    refine ⟨{ toFun := fun uz => (F (a uz.1,uz.2)).1
              continuous_toFun := (F.continuous.comp
                ((ha.comp continuous_fst).prodMk continuous_snd)).fst
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      have ha0 : a 0 = 0 := Subtype.ext (by simp [a])
      simp [ha0, hInitial]
    · intro z
      have ha1 : a 1 = t := Subtype.ext (by simp [a])
      simp [ha1,c]
  -- Static geometric leaf: a homotopically essential embedded circle below
  -- the disjoint reference level has a confined collared annulus to that level.
  -- This is not angular bijectivity and does not ask for a parametric extension.
  have hgeometry (b : Curve (Circle × Interval))
      (hb : ∀ z, b.map z ∈ Set.univ ×ˢ Set.Ioo (0 : Interval) r)
      (hbh : ContinuousMap.Homotopic (ContinuousMap.id Circle)
        (⟨fun z => (b.map z).1,b.embedded.continuous.fst⟩ : C(Circle,Circle))) :
      ∃ B : Circle × Interval → Circle × Interval, IsEmbedding B ∧
        Set.range (fun z : Circle => B (z,⟨1/3,by norm_num⟩)) = b.image ∧
        Set.range (fun z : Circle => B (z,⟨2/3,by norm_num⟩)) = d.image ∧
        IsOpen (B '' (Set.univ ×ˢ Set.Ioo (0 : Interval) 1)) ∧
        Set.range B ⊆ Set.univ ×ˢ Set.Ioo (0 : Interval) 1 := by
    exact actual_model_essential_circle_confined_collared_annulus_to_outer_level r hr0 hr1 b hb hbh
  have halign (t : Interval) :
      ∃ H : AmbientIsotopy (Circle × Interval),
        ∃ J : C(Interval × (Circle × Interval),Circle × Interval),
          H.finalMap '' (c t).image = d.image ∧
          (∀ u z, H.map (u,(z,0))=(z,0)) ∧
          (∀ u z, H.map (u,(z,1))=(z,1)) ∧
          (∀ u x, J (u,H.map (u,x))=x) ∧
          (∀ u x, H.map (u,J (u,x))=x) := by
    obtain ⟨B,hB,hc,hd,hopen,hsub⟩ := hgeometry (c t)
      (fun z => ⟨Set.mem_univ _, (hInterior t z).2.1, hbelow t z⟩) (hangular t)
    obtain ⟨H,J,hend,hfix,hleft,hright⟩ :=
      G3Review.actual_collared_annulus_ambient_alignment (c t) d B hB hc hd hopen
    have hboundary (u : Interval) (z : Circle) (v : Interval)
        (hv : v = 0 ∨ v = 1) : H.map (u,(z,v))=(z,v) := by
      apply hfix
      rintro ⟨y,hy,he⟩
      have hin := hsub ⟨y,he⟩
      rcases hv with rfl | rfl
      · exact (lt_irrefl (0 : Interval)) hin.2.1
      · exact (lt_irrefl (1 : Interval)) hin.2.2
    exact ⟨H,J,hend,fun u z => hboundary u z 0 (Or.inl rfl),
      fun u z => hboundary u z 1 (Or.inr rfl),hleft,hright⟩
  obtain ⟨H₀,J₀,hend₀,hzero₀,hone₀,hleft₀,hright₀⟩ := halign 0
  obtain ⟨H₁,J₁,hend₁,hzero₁,hone₁,hleft₁,hright₁⟩ := halign 1
  let K : AmbientIsotopy (Circle × Interval) := {
    map := J₁
    homeomorphism_at := by
      intro t
      obtain ⟨e,he⟩ := H₁.homeomorphism_at t
      refine ⟨e.symm,?_⟩
      intro x
      have hh := hleft₁ t (e.symm x)
      rw [← he, e.apply_symm_apply] at hh
      exact hh.symm
    at_zero := by
      intro x
      have hh := hleft₁ 0 x
      have h0 : H₁.map (0,x)=x := H₁.at_zero x
      rw [h0] at hh
      exact hh }
  have hKzero (t : Interval) (z : Circle) : K.map (t,(z,0))=(z,0) := by
    have hh := hleft₁ t (z,0)
    simpa only [hzero₁] using hh
  have hKone (t : Interval) (z : Circle) : K.map (t,(z,1))=(z,1) := by
    have hh := hleft₁ t (z,1)
    simpa only [hone₁] using hh
  refine ⟨H₀.compose K,?_,?_,?_⟩
  · intro t z
    change K.map (t,H₀.map (t,(z,0)))=(z,0)
    rw [hzero₀,hKzero]
  · intro t z
    change K.map (t,H₀.map (t,(z,1)))=(z,1)
    rw [hone₀,hKone]
  · have hcore : (c 0).image = Set.range (fun z : Circle =>
        (z,(⟨1/2,by norm_num⟩ : Interval))) := by
      change Set.range (fun z => F (0,z)) = _
      exact congrArg Set.range (funext hInitial)
    rw [AmbientIsotopy.compose_finalMap,Set.image_comp,← hcore,hend₀,← hend₁,Set.image_image]
    have hinverse : K.finalMap ∘ H₁.finalMap = id := funext (hleft₁ 1)
    change (K.finalMap ∘ H₁.finalMap) '' (c 1).image = Set.range (fun z => F (1,z))
    rw [hinverse,Set.image_id]
    rfl

end CurveComplex.SDRModelAnnulusReview
