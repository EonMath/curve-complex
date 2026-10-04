import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic

open Set

theorem actual_two_direction_compact_regular_parameters
    (f g h : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hh : ContDiffOn ℝ 1 h U)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) :
    IsOpen {p : ℝ × ℝ | ∀ x ∈ K,
      f x + p.1 • g x + p.2 • h x = 0 →
        (fderiv ℝ (fun z => f z + p.1 • g z + p.2 • h z) x).det ≠ 0} := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K × (ℝ × ℝ) → ℂ := fun p =>
    f p.1.val + p.2.1 • g p.1.val + p.2.2 • h p.1.val
  let G : K × (ℝ × ℝ) → ℂ := fun p =>
    ((fderiv ℝ f p.1.val + p.2.1 • fderiv ℝ g p.1.val +
      p.2.2 • fderiv ℝ h p.1.val).det : ℝ)
  have hxcont : Continuous (fun p : K × (ℝ × ℝ) => (p.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hc1 : Continuous (fun p : K × (ℝ × ℝ) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hc2 : Continuous (fun p : K × (ℝ × ℝ) => p.2.2) :=
    continuous_snd.comp continuous_snd
  have hfcont : Continuous (fun p : K × (ℝ × ℝ) => f p.1.val) :=
    hf.continuousOn.comp_continuous hxcont (fun p => hKU p.1.property)
  have hgcont : Continuous (fun p : K × (ℝ × ℝ) => g p.1.val) :=
    hg.continuousOn.comp_continuous hxcont (fun p => hKU p.1.property)
  have hhcont : Continuous (fun p : K × (ℝ × ℝ) => h p.1.val) :=
    hh.continuousOn.comp_continuous hxcont (fun p => hKU p.1.property)
  have hF : Continuous F := (hfcont.add (hc1.smul hgcont)).add (hc2.smul hhcont)
  have hdf : Continuous (fun p : K × (ℝ × ℝ) => fderiv ℝ f p.1.val) :=
    (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp_continuous
      hxcont (fun p => hKU p.1.property)
  have hdg : Continuous (fun p : K × (ℝ × ℝ) => fderiv ℝ g p.1.val) :=
    (hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp_continuous
      hxcont (fun p => hKU p.1.property)
  have hdh : Continuous (fun p : K × (ℝ × ℝ) => fderiv ℝ h p.1.val) :=
    (hh.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp_continuous
      hxcont (fun p => hKU p.1.property)
  have hG : Continuous G := by
    apply Complex.continuous_ofReal.comp
    apply ContinuousLinearMap.continuous_det.comp
    exact (hdf.add (hc1.smul hdg)).add (hc2.smul hdh)
  let B : Set (K × (ℝ × ℝ)) := {u | F u = 0 ∧ G u = 0}
  have hB : IsClosed B :=
    (isClosed_singleton.preimage hF).inter (isClosed_singleton.preimage hG)
  have hproj : IsClosed (Prod.snd '' B) := isClosedMap_snd_of_compactSpace B hB
  have hderiv (p : ℝ × ℝ) (x : K) :
      fderiv ℝ (fun z => f z + p.1 • g z + p.2 • h z) x.val =
        fderiv ℝ f x.val + p.1 • fderiv ℝ g x.val +
          p.2 • fderiv ℝ h x.val := by
    have hxU : x.val ∈ U := hKU x.property
    have hfdiff : DifferentiableAt ℝ f x.val :=
      ((hf x.val hxU).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
    have hgdiff : DifferentiableAt ℝ g x.val :=
      ((hg x.val hxU).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
    have hhdiff : DifferentiableAt ℝ h x.val :=
      ((hh x.val hxU).contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num)
    change fderiv ℝ (f + p.1 • g + p.2 • h) x.val = _
    rw [fderiv_add (hfdiff.add (hgdiff.const_smul p.1)) (hhdiff.const_smul p.2)]
    rw [fderiv_add hfdiff (hgdiff.const_smul p.1)]
    rw [fderiv_const_smul hgdiff p.1, fderiv_const_smul hhdiff p.2]
  have heq : {p : ℝ × ℝ | ∀ x ∈ K,
      f x + p.1 • g x + p.2 • h x = 0 →
        (fderiv ℝ (fun z => f z + p.1 • g z + p.2 • h z) x).det ≠ 0} =
      (Prod.snd '' B)ᶜ := by
    ext p
    constructor
    · intro hp hbad
      obtain ⟨u, hu, hup⟩ := hbad
      have hzero : f u.1.val + p.1 • g u.1.val + p.2 • h u.1.val = 0 := by
        simpa only [F, hup] using hu.1
      have hdet : (fderiv ℝ
          (fun z => f z + p.1 • g z + p.2 • h z) u.1.val).det = 0 := by
        rw [hderiv p u.1]
        exact Complex.ofReal_eq_zero.mp (by simpa only [G, hup] using hu.2)
      exact hp u.1.val u.1.property hzero hdet
    · intro hp x hx hzero hdet
      apply hp
      refine ⟨(⟨x, hx⟩, p), ?_, rfl⟩
      constructor
      · exact hzero
      · change ((fderiv ℝ f x + p.1 • fderiv ℝ g x +
          p.2 • fderiv ℝ h x).det : ℂ) = 0
        rw [← hderiv p ⟨x, hx⟩]
        exact Complex.ofReal_eq_zero.mpr hdet
  rw [heq]
  exact hproj.isOpen_compl

