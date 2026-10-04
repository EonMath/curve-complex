import Mathlib
import Mathlib.Analysis.Complex.BranchLogRoot

namespace CurveComplex.Hyperbolic
open Set Topology

 def logLeftHalfPlane (A : ℝ) : Set ℂ := {z | z.re < A}

theorem logLeftHalfPlane_isOpen (A : ℝ) : IsOpen (logLeftHalfPlane A) := by
  exact isOpen_lt Complex.continuous_re continuous_const

theorem logLeftHalfPlane_convex (A : ℝ) : Convex ℝ (logLeftHalfPlane A) := by
  exact convex_halfSpace_lt ⟨by intros; simp, by intros; simp⟩ A

theorem logLeftHalfPlane_nonempty (A : ℝ) : (logLeftHalfPlane A).Nonempty := by
  refine ⟨((A - 1 : ℝ) : ℂ), ?_⟩
  change A - 1 < A
  linarith

theorem logLeftHalfPlane_isSimplyConnected (A : ℝ) : IsSimplyConnected (logLeftHalfPlane A) := by
  letI := (logLeftHalfPlane_convex A).contractibleSpace (logLeftHalfPlane_nonempty A)
  change SimplyConnectedSpace (logLeftHalfPlane A)
  infer_instance

theorem local_plane_homeomorphism_log_lift
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (hzero : h 0 = 0) :
    ∃ A : ℝ, ∃ F : ℂ → ℂ, ContinuousOn F (logLeftHalfPlane A) ∧
      (∀ z ∈ logLeftHalfPlane A, Complex.exp z ∈ h.source) ∧
      (∀ z ∈ logLeftHalfPlane A, h (Complex.exp z) ≠ 0) ∧
      ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp h.open_source 0 hsource
  let A := Real.log r
  have hmaps : ∀ z ∈ logLeftHalfPlane A, Complex.exp z ∈ h.source := by
    intro z hz
    apply hsub
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_exp]
    change z.re < Real.log r at hz
    have he := Real.exp_lt_exp.mpr hz
    rwa [Real.exp_log hr] at he
  have hnonzero : ∀ z ∈ logLeftHalfPlane A, h (Complex.exp z) ≠ 0 := by
    intro z hz hbad
    have heq : h (Complex.exp z) = h 0 := hbad.trans hzero.symm
    exact Complex.exp_ne_zero z (h.injOn (hmaps z hz) hsource heq)
  have hcont : ContinuousOn (fun z => h (Complex.exp z)) (logLeftHalfPlane A) :=
    h.continuousOn.comp Complex.continuous_exp.continuousOn hmaps
  obtain ⟨F, hF, heq⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (logLeftHalfPlane_isSimplyConnected A) (logLeftHalfPlane_isOpen A) hcont
    (by rintro ⟨z, hz, heq⟩; exact hnonzero z hz heq)
  exact ⟨A, F, hF, hmaps, hnonzero, heq⟩

end CurveComplex.Hyperbolic
