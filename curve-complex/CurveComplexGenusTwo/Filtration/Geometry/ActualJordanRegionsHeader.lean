import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import CurveComplexGenusTwo.Dependencies.ChartClosure
namespace CurveComplex.HyperellipticModel
open Set
theorem sphereJordan_two_regions (c : CurveComplex.SpherePort.JordanCurve) (P : CurveComplex.SpherePort.Chart c) :
    ∃ SU SV : Set CurveComplex.SpherePort.Sphere,
      IsComplementComponent c.image SU ∧ IsComplementComponent c.image SV ∧
      IsOpen SU ∧ IsOpen SV ∧ Disjoint SU SV ∧ SU ≠ SV ∧
      SU ∪ SV = c.imageᶜ ∧ frontier SU = c.image ∧ frontier SV = c.image := by
  classical
  let C := P.planeImage c
  have hC : Schoenflies.IsJordanCurve C := CurveComplex.SpherePort.chart_image_jordan c P
  have hsep := Schoenflies.jordan_curve_theorem hC
  let F : OnePoint Schoenflies.Plane ≃ₜ CurveComplex.SpherePort.Sphere :=
    CurveComplex.SpherePort.chartOnePoint c P
  let B : Set (OnePoint Schoenflies.Plane) := OnePoint.some '' C
  let U : Set (OnePoint Schoenflies.Plane) := OnePoint.some '' Schoenflies.inside C
  let V : Set (OnePoint Schoenflies.Plane) :=
    {OnePoint.infty} ∪ OnePoint.some '' Schoenflies.outside C
  have hBimage : F '' B = c.image := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨y, hy, hzy⟩ := hz
      change (P.plane.symm z).val ∈ c.image
      rw [← hzy, P.plane.symm_apply_apply]
      exact hy
    · intro hx
      let y : {x : CurveComplex.SpherePort.Sphere // x ≠ P.puncture} :=
        ⟨x, fun he => P.avoids (he ▸ hx)⟩
      refine ⟨OnePoint.some (P.plane y), ⟨P.plane y, ⟨y, hx, rfl⟩, rfl⟩, ?_⟩
      change (P.plane.symm (P.plane y)).val = x
      rw [P.plane.symm_apply_apply]
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hx hy
    cases x with
    | infty => simpa [U] using hx
    | coe z =>
      have hzU : z ∈ Schoenflies.inside C := by simpa [U] using hx
      have hzV : z ∈ Schoenflies.outside C := by simpa [V] using hy
      exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hzU hzV
  have hcover : U ∪ V = Bᶜ := by
    ext x
    cases x with
    | infty => simp [U, V, B]
    | coe z =>
      have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
      simpa [U, V, B] using hz
  have hclU0 : closure U = OnePoint.some '' closure (Schoenflies.inside C) := by
    have hk : IsCompact (closure (Schoenflies.inside C)) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
    apply Set.Subset.antisymm
    · exact closure_minimal (Set.image_mono subset_closure) (hk.image OnePoint.continuous_coe).isClosed
    · exact image_closure_subset_closure_image OnePoint.continuous_coe
  have hclU : closure U = U ∪ B := by
    rw [hclU0, (Schoenflies.IsRegionOf.inside C).closure_eq hsep, Set.image_union]
  have hclV : closure V = V ∪ B := by
    change closure (CurveComplex.SpherePort.compactifiedOutside (Schoenflies.outside C)) = _
    rw [CurveComplex.SpherePort.closure_compactifiedOutside,
      (Schoenflies.IsRegionOf.outside C).closure_eq hsep]
    simp only [CurveComplex.SpherePort.compactifiedOutside, Set.image_union]
    exact Set.union_assoc _ _ _ |>.symm
  have hUcomp : closure U = Vᶜ := by
    rw [hclU]
    ext x
    cases x with
    | infty => simp [U, V, B]
    | coe z =>
      have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
      have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
        fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
      have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
      have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
      have hz' : z ∈ Schoenflies.inside C ∨ z ∈ C ↔ z ∉ Schoenflies.outside C := by
        simp only [Set.mem_union, Set.mem_compl_iff] at hz
        tauto
      simpa [U, V, B] using hz'
  have hVcomp : closure V = Uᶜ := by
    rw [hclV]
    ext x
    cases x with
    | infty => simp [U, V, B]
    | coe z =>
      have hz := Set.ext_iff.mp (Schoenflies.inside_union_outside C) z
      have hd : z ∈ Schoenflies.inside C → z ∉ Schoenflies.outside C :=
        fun hz => Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz
      have hi : z ∈ Schoenflies.inside C → z ∉ C := fun hz => Schoenflies.inside_subset_compl hz
      have ho : z ∈ Schoenflies.outside C → z ∉ C := fun hz => Schoenflies.outside_subset_compl hz
      have hz' : z ∈ Schoenflies.outside C ∨ z ∈ C ↔ z ∉ Schoenflies.inside C := by
        simp only [Set.mem_union, Set.mem_compl_iff] at hz
        tauto
      simpa [U, V, B] using hz'
  have hopenU : IsOpen U := by
    rw [← compl_compl U, ← hVcomp]
    exact isClosed_closure.isOpen_compl
  have hopenV : IsOpen V := by
    rw [← compl_compl V, ← hUcomp]
    exact isClosed_closure.isOpen_compl
  have hintU : interior (closure U) = U := by
    rw [hUcomp, interior_compl, hVcomp, compl_compl]
  have hintV : interior (closure V) = V := by
    rw [hVcomp, interior_compl, hUcomp, compl_compl]
  have hboundU : frontier U = B := by
    rw [hopenU.frontier_eq, hclU]
    ext x
    have hn : x ∈ U → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inl hx)
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto
  have hboundV : frontier V = B := by
    rw [hopenV.frontier_eq, hclV]
    ext x
    have hn : x ∈ V → x ∉ B := fun hx => (Set.ext_iff.mp hcover x).mp (Or.inr hx)
    simp only [Set.mem_sdiff, Set.mem_union]
    tauto

  have hconnU : IsConnected U := hsep.isConnected_inside.image
    OnePoint.some OnePoint.continuous_coe.continuousOn
  have hconnV0 : IsConnected (OnePoint.some '' Schoenflies.outside C) :=
    hsep.isConnected_outside.image OnePoint.some OnePoint.continuous_coe.continuousOn
  have hinfty : (OnePoint.infty : OnePoint Schoenflies.Plane) ∈
      closure (OnePoint.some '' Schoenflies.outside C) := by
    by_contra hn
    have hsub : closure (OnePoint.some '' Schoenflies.outside C) ⊆ Set.range OnePoint.some := by
      intro x hx
      cases x with
      | infty => exact False.elim (hn hx)
      | coe y => exact ⟨y, rfl⟩
    have hk := OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage'
      isClosed_closure.isCompact hsub
    apply hsep.not_isBounded_outside
    exact hk.isBounded.subset (fun x hx => subset_closure ⟨x, hx, rfl⟩)
  have hconnV : IsConnected V := hconnV0.subset_closure Set.subset_union_right (by
    rintro x (hx | hx)
    · exact Set.mem_singleton_iff.mp hx ▸ hinfty
    · exact subset_closure hx)
  let SU := F '' U
  let SV := F '' V
  have hsconnU : IsConnected SU := hconnU.image F F.continuous.continuousOn
  have hsconnV : IsConnected SV := hconnV.image F F.continuous.continuousOn
  have hsopenU : IsOpen SU := F.isOpenMap U hopenU
  have hsopenV : IsOpen SV := F.isOpenMap V hopenV
  have hsdisj : Disjoint SU SV := (Set.disjoint_image_iff F.injective).mpr hdisj
  have hscover : SU ∪ SV = c.imageᶜ := by
    rw [← Set.image_union, hcover, F.image_compl, hBimage]
  have hsboundU : frontier SU = c.image := by
    rw [← F.image_frontier, hboundU, hBimage]
  have hsboundV : frontier SV = c.image := by
    rw [← F.image_frontier, hboundV, hBimage]
  have hmaximal : ∀ T R : Set CurveComplex.SpherePort.Sphere, IsConnected T →
      IsOpen T → IsOpen R → Disjoint T R → T ∪ R = c.imageᶜ →
      IsComplementComponent c.image T := by
    intro T R hT hTopen hRopen hTR hc
    refine ⟨hT.nonempty, hT, (fun x hx => hc ▸ Or.inl hx), ?_⟩
    intro W hW hTW hWc
    have hsplit := hW.isPreconnected.subset_or_subset hTopen hRopen hTR (hc.symm ▸ hWc)
    rcases hsplit with hWT | hWR
    · exact Set.Subset.antisymm hWT hTW
    · obtain ⟨x, hx⟩ := hT.nonempty
      exact False.elim (Set.disjoint_left.mp hTR hx (hWR (hTW hx)))
  have hcU := hmaximal SU SV hsconnU hsopenU hsopenV hsdisj hscover
  have hcV := hmaximal SV SU hsconnV hsopenV hsopenU hsdisj.symm
    ((Set.union_comm SV SU).trans hscover)
  have hdistinct : SU ≠ SV := by
    intro heq
    obtain ⟨x, hx⟩ := hsconnU.nonempty
    exact Set.disjoint_left.mp hsdisj hx (heq ▸ hx)
  exact ⟨SU, SV, hcU, hcV, hsopenU, hsopenV, hsdisj, hdistinct,
    hscover, hsboundU, hsboundV⟩
end CurveComplex.HyperellipticModel
