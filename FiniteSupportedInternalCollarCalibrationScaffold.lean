import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualInternalCollarCalibration
import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualFiniteInteriorAxisFraming

namespace CurveComplex
open Set Topology Schoenflies

set_option autoImplicit false

/-- Finite local calibration of the supplied strip by one supported ambient homeomorphism. -/
theorem source_finite_supported_internal_collar_calibration
    {S K : Type} [TopologicalSpace S] [T2Space S] [Fintype K]
    (f : C(Interval, S)) (hf : IsEmbedding f)
    (N : C(Interval × Set.Icc (-1 : ℝ) 1, S)) (hN : IsEmbedding N)
    (hcenter : ∀ t, N (t, ⟨0, by norm_num⟩) = f t)
    (θ : K → Interval) (hθ : Function.Injective θ)
    (hint : ∀ k, 0 < (θ k : ℝ) ∧ (θ k : ℝ) < 1)
    (D : K → OpenPartialHomeomorph S Plane)
    (hpD : ∀ k, f (θ k) ∈ (D k).source)
    (hD0 : ∀ k, D k (f (θ k)) = 0)
    (haxis : ∀ k t, f t ∈ (D k).source → D k (f t) 1 = 0)
    (U : K → Set S) (hU : ∀ k, IsOpen (U k))
    (hpoint : ∀ k, f (θ k) ∈ U k)
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    ∃ H : S ≃ₜ S, ∃ ω lam η σ : K → ℝ,
      (∀ k, 0 < ω k ∧ ω k ≤ 1 ∧ 0 < lam k ∧ 0 < η k ∧
        (σ k = -1 ∨ σ k = 1)) ∧
      (∀ t, H (f t) = f t) ∧
      (∀ x, x ∉ ⋃ k, U k → H x = x) ∧
      ∀ k (t : Interval) (u : Set.Icc (-1 : ℝ) 1),
        |(t : ℝ) - (θ k : ℝ)| < η k → |(u : ℝ)| ≤ ω k →
        H (N (t, u)) ∈ (D k).source ∩ U k ∧
        D k (H (N (t, u))) = Plane.mk (D k (f t) 0) (σ k * lam k * (u : ℝ)) := by
  classical
  let Calibrated (A : Finset K) : Prop :=
    ∃ H : S ≃ₜ S, ∃ ω lam η σ : K → ℝ,
      (∀ k ∈ A, 0 < ω k ∧ ω k ≤ 1 ∧ 0 < lam k ∧ 0 < η k ∧
        (σ k = -1 ∨ σ k = 1)) ∧
      (∀ t, H (f t) = f t) ∧
      (∀ x, (∀ k ∈ A, x ∉ U k) → H x = x) ∧
      ∀ k ∈ A, ∀ (t : Interval) (u : Set.Icc (-1 : ℝ) 1),
        |(t : ℝ) - (θ k : ℝ)| < η k → |(u : ℝ)| ≤ ω k →
        H (N (t, u)) ∈ (D k).source ∩ U k ∧
        D k (H (N (t, u))) = Plane.mk (D k (f t) 0) (σ k * lam k * (u : ℝ))
  have hfinite : ∀ A : Finset K, Calibrated A := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨Homeomorph.refl S, (fun _ => 1), (fun _ => 1), (fun _ => 1),
        (fun _ => 1), ?_, ?_, ?_, ?_⟩
      · intro k hk
        simp at hk
      · intro t
        rfl
      · intro x _
        rfl
      · intro k hk
        simp at hk
    | @insert k A hk hA =>
      obtain ⟨H, ω, lam, η, σ, hparams, hcenterH, hfixH, hformula⟩ := hA
      let M : C(Interval × Set.Icc (-1 : ℝ) 1, S) :=
        ⟨fun p => H (N p), H.continuous.comp N.continuous⟩
      have hM : IsEmbedding M := H.isEmbedding.comp hN
      have hMcenter : ∀ t, M (t, ⟨0, by norm_num⟩) = f t := by
        intro t
        change H (N (t, ⟨0, by norm_num⟩)) = f t
        rw [hcenter, hcenterH]
      let Dk := (D k).restr (U k)
      have hDkSource : Dk.source = (D k).source ∩ U k := by
        exact (D k).restr_source' (U k) (hU k)
      have hpointDk : f (θ k) ∈ Dk.source := by
        rw [hDkSource]
        exact ⟨hpD k, hpoint k⟩
      have hDkZero : Dk (f (θ k)) = 0 := hD0 k
      have hDkAxis : ∀ t, f t ∈ Dk.source → Dk (f t) 1 = 0 := by
        intro t ht
        change D k (f t) 1 = 0
        apply haxis k t
        exact (hDkSource ▸ ht).1
      obtain ⟨widthFactor, hw, sgn, δ, ηnew, F, hsgn, hδ, hηnew,
        hFcenter, hFfix, hFcoords⟩ :=
        source_internal_collar_calibration f hf M hM hMcenter (θ k) (hint k)
          Dk hpointDk hDkZero hDkAxis Set.univ (U k) isOpen_univ
          (hU k) (Set.subset_univ _) (hpoint k) (Set.subset_univ _)
      have hraw (t : Interval) (u : Set.Icc (-1 : ℝ) 1)
          (ht : |(t : ℝ) - (θ k : ℝ)| < ηnew)
          (hu : |(u : ℝ)| ≤ widthFactor) :
          F (M (t,u)) ∈ (D k).source ∩ U k ∧
          D k (F (M (t,u))) =
            Plane.mk (D k (f t) 0) (sgn * (δ / widthFactor) * (u : ℝ)) := by
        let w : Set.Icc (-1 : ℝ) 1 :=
          ⟨(u : ℝ) / widthFactor, by
            have habs := abs_le.mp hu
            constructor
            · apply (le_div_iff₀ hw.1).2
              linarith
            · apply (div_le_iff₀ hw.1).2
              linarith⟩
        have hwEq : (⟨widthFactor * (w : ℝ), by
            constructor <;> nlinarith [w.property.1, w.property.2, hw.1, hw.2]⟩ :
            Set.Icc (-1 : ℝ) 1) = u := by
          apply Subtype.ext
          change widthFactor * ((u : ℝ) / widthFactor) = (u : ℝ)
          field_simp [hw.1.ne']
        have hh := hFcoords t w ht
        rw [hwEq] at hh
        have hsource : F (M (t,u)) ∈ (D k).source ∩ U k := by
          rw [hDkSource] at hh
          exact hh.1
        refine ⟨hsource, ?_⟩
        have hsecond : sgn * δ * (w : ℝ) =
            sgn * (δ / widthFactor) * (u : ℝ) := by
          change sgn * δ * ((u : ℝ) / widthFactor) = _
          field_simp [hw.1.ne']
        have hcoords := hh.2
        change D k (F (M (t,u))) =
          Plane.mk (D k (f t) 0) (sgn * δ * (w : ℝ)) at hcoords
        rw [hsecond] at hcoords
        exact hcoords
      let Hnew : S ≃ₜ S := H.trans F
      let ωnew : K → ℝ := fun i => if i = k then widthFactor else ω i
      let lamnew : K → ℝ := fun i => if i = k then δ / widthFactor else lam i
      let ηnext : K → ℝ := fun i => if i = k then ηnew else η i
      let σnew : K → ℝ := fun i => if i = k then sgn else σ i
      refine ⟨Hnew, ωnew, lamnew, ηnext, σnew, ?_, ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · subst i
          simpa [ωnew, lamnew, ηnext, σnew] using
            (show 0 < widthFactor ∧ widthFactor ≤ 1 ∧
              0 < δ / widthFactor ∧ 0 < ηnew ∧ (sgn = -1 ∨ sgn = 1) from
              ⟨hw.1, hw.2, div_pos hδ hw.1, hηnew, hsgn⟩)
        · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hik
          simpa [ωnew, lamnew, ηnext, σnew, hik] using hparams i hiA
      · intro t
        change F (H (f t)) = f t
        rw [hcenterH, hFcenter]
      · intro x hx
        have hxk : x ∉ U k := hx k (by simp)
        have hxA : ∀ i ∈ A, x ∉ U i := by
          intro i hi
          exact hx i (by simp [hi])
        change F (H x) = x
        rw [hfixH x hxA, hFfix x hxk]
      · intro i hi t u htime hu
        by_cases hik : i = k
        · subst i
          have htnew : |(t : ℝ) - (θ k : ℝ)| < ηnew := by
            simpa [ηnext] using htime
          have hunew : |(u : ℝ)| ≤ widthFactor := by
            simpa [ωnew] using hu
          simpa [Hnew, M, lamnew, σnew] using hraw t u htnew hunew
        · have hiA : i ∈ A := (Finset.mem_insert.mp hi).resolve_left hik
          have hti : |(t : ℝ) - (θ i : ℝ)| < η i := by
            simpa [ηnext, hik] using htime
          have hui : |(u : ℝ)| ≤ ω i := by
            simpa [ωnew, hik] using hu
          have hold := hformula i hiA t u hti hui
          have hnot : H (N (t,u)) ∉ U k := by
            intro hkU
            exact (Set.disjoint_left.mp (hdisj i k hik)) hold.1.2 hkU
          have hfixed := hFfix (H (N (t,u))) hnot
          change F (H (N (t,u))) ∈ (D i).source ∩ U i ∧
            D i (F (H (N (t,u)))) =
              Plane.mk (D i (f t) 0) (σnew i * lamnew i * (u : ℝ))
          rw [hfixed]
          simpa [σnew, lamnew, hik] using hold
  obtain ⟨H, ω, lam, η, σ, hparams, hcenterH, hfixH, hformula⟩ :=
    hfinite Finset.univ
  refine ⟨H, ω, lam, η, σ, ?_, hcenterH, ?_, ?_⟩
  · intro k
    exact hparams k (Finset.mem_univ k)
  · intro x hx
    apply hfixH
    intro k _ hk
    exact hx (Set.mem_iUnion.mpr ⟨k, hk⟩)
  · intro k t u ht hu
    exact hformula k (Finset.mem_univ k) t u ht hu

end CurveComplex
