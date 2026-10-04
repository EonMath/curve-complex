import Mathlib.Geometry.Manifold.Instances.Real
import ClassificationOfSurfaces.Moise.Brouwer
import Mathlib.Topology.Piecewise

open Set Topology
set_option autoImplicit false

/-- A topological embedding of an open subset of the actual two-dimensional
half-space, preserving zero normal coordinate in both directions, is an open
embedding relative to that half-space. -/
theorem halfspace_boundary_preserving_embedding_isOpenEmbedding
    (U : Set (EuclideanHalfSpace 2)) (hU : IsOpen U)
    (f : C(↥U, EuclideanHalfSpace 2)) (hf : IsEmbedding f)
    (hzero : ∀ u : ↥U, (f u).val 0 = 0 ↔ u.val.val 0 = 0) :
    IsOpenEmbedding f := by
  classical
  let E := EuclideanSpace ℝ (Fin 2)
  let reflect : E → E := fun x ↦
    WithLp.toLp 2 (fun i ↦ if i = 0 then -x i else x i)
  let fold : E → EuclideanHalfSpace 2 := fun x ↦
    ⟨WithLp.toLp 2 (fun i ↦ if i = 0 then |x i| else x i), by
      change 0 ≤ |x 0|
      exact abs_nonneg _⟩
  have hreflect : Continuous reflect := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · simp only [hi, eq_self, ite_true]
      exact continuous_neg.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0)
    · simpa [hi] using PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i
  have hfold : Continuous fold := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · simpa [hi] using (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).abs
    · simpa [hi] using PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) i
  have hfold_pos (x : E) (hx : 0 ≤ x 0) : (fold x).val = x := by
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · simp [fold, hi, abs_of_nonneg hx]
    · simp [fold, hi]
  have hreflect_invol (x : E) : reflect (reflect x) = x := by
    apply PiLp.ext
    intro i
    by_cases hi : i = 0 <;> simp [reflect, hi]
  have hreflect_zero (x : E) (hx : x 0 = 0) : reflect x = x := by
    apply PiLp.ext
    intro i
    by_cases hi : i = 0 <;> simp [reflect, hi, hx]
  let D : Set E := fold ⁻¹' U
  have hD : IsOpen D := hU.preimage hfold
  let toU : D → U := fun x ↦ ⟨fold x.val, x.property⟩
  have htoU : Continuous toU :=
    (hfold.comp continuous_subtype_val).subtype_mk _
  let A : D → E := fun x ↦ (f (toU x)).val
  have hA : Continuous A :=
    continuous_subtype_val.comp (f.continuous.comp htoU)
  let g : D → E := fun x ↦ if 0 ≤ x.val 0 then A x else reflect (A x)
  have hg : Continuous g := by
    apply hA.if_le (hreflect.comp hA) continuous_const
      ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_subtype_val)
    intro x hx
    apply Eq.symm
    apply hreflect_zero
    apply (hzero (toU x)).2
    change |x.val 0| = 0
    exact abs_eq_zero.mpr hx.symm
  have hg_sign (x : D) : 0 ≤ g x 0 ↔ 0 ≤ x.val 0 := by
    have ha : 0 ≤ A x 0 := (f (toU x)).property
    by_cases hx : 0 ≤ x.val 0
    · simp [g, hx, ha]
    · have hax : A x 0 ≠ 0 := by
        intro hz
        have h := (hzero (toU x)).1 hz
        change |x.val 0| = 0 at h
        have := abs_eq_zero.mp h
        exact hx (by simp [this])
      have hap : 0 < A x 0 := lt_of_le_of_ne ha (Ne.symm hax)
      simp [g, hx, reflect, not_le.mpr (neg_neg_of_pos hap)]
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have hs : (0 ≤ x.val 0) ↔ (0 ≤ y.val 0) := by
      rw [← hg_sign x, ← hg_sign y, hxy]
    have ha : A x = A y := by
      by_cases hx : 0 ≤ x.val 0
      · simpa [g, hx, hs.mp hx] using hxy
      · have hy : ¬0 ≤ y.val 0 := fun hy ↦ hx (hs.mpr hy)
        have hr : reflect (A x) = reflect (A y) := by simpa [g, hx, hy] using hxy
        simpa only [hreflect_invol] using congrArg reflect hr
    have hu : toU x = toU y := hf.injective (Subtype.ext ha)
    have he : (fold x.val).val = (fold y.val).val :=
      congrArg (fun u : U ↦ u.val.val) hu
    apply Subtype.ext
    apply PiLp.ext
    intro i
    have hi := congrArg (fun z : E ↦ z i) he
    by_cases hi0 : i = 0
    · subst i
      change |x.val 0| = |y.val 0| at hi
      by_cases hx : 0 ≤ x.val 0
      · simpa [abs_of_nonneg hx, abs_of_nonneg (hs.mp hx)] using hi
      · have hy : ¬0 ≤ y.val 0 := fun hy ↦ hx (hs.mpr hy)
        rw [abs_of_neg (lt_of_not_ge hx), abs_of_neg (lt_of_not_ge hy)] at hi
        exact neg_injective hi
    · simpa [fold, hi0] using hi
  have hgrange : IsOpen (range g) :=
    LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isOpen_range_of_isOpen_of_continuous_injective
      (modelWithCornersSelf ℝ E) hD g hg hg_inj
  have hrange : range f = (Subtype.val : EuclideanHalfSpace 2 → E) ⁻¹' range g := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      have hfold_u : fold u.val.val = u.val := Subtype.ext (hfold_pos u.val.val u.val.property)
      let x : D := ⟨u.val.val, by change fold u.val.val ∈ U; rw [hfold_u]; exact u.property⟩
      have hxu : toU x = u := Subtype.ext hfold_u
      refine ⟨x, ?_⟩
      change g x = (f u).val
      simp only [g, show 0 ≤ x.val 0 from u.val.property, ite_true, A, hxu]
    · rintro ⟨x, hx⟩
      have hxp : 0 ≤ x.val 0 := (hg_sign x).1 (by rw [hx]; exact z.property)
      have hax : A x = z.val := by simpa [g, hxp] using hx
      exact ⟨toU x, Subtype.ext hax⟩
  exact ⟨hf, hrange ▸ hgrange.preimage continuous_subtype_val⟩
