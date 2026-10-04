import CurveComplexGenusTwo.Topology.FirstReturnCorner.ActualLocalizedCornerSquare

namespace CurveComplex
open Set Topology Schoenflies

/-- Construct the actual connector between signed nonzero first/closing
ports. Each coordinate axis is met at most once. A positive port gives no
contact with its axis, and the original crossing is always avoided. The signs
are independent, so a mismatch adds at most one crossing for each old curve. -/
theorem source_signed_corner_connector
    {S : Type} [TopologicalSpace S] [T2Space S]
    (a b : Curve S) (E : OpenPartialHomeomorph S Plane)
    (hsquare : Plane.closedSquare 0 1 ⊆ E.target)
    (ha : ∀ x ∈ E.source, x ∈ a.image ↔ E x 0 = 0)
    (hb : ∀ x ∈ E.source, x ∈ b.image ↔ E x 1 = 0)
    (σ τ : Bool) (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ < 1/2) :
    ∃ f : C(Interval,S),
      IsEmbedding f ∧ Set.range f ⊆ E.source ∧
      E (f 0) = Plane.mk ((if σ then -1 else 1)*δ) (1/2) ∧
      E (f 1) = Plane.mk (1/2) ((if τ then -1 else 1)*δ) ∧
      (Set.range f ∩ a.image).Finite ∧ (Set.range f ∩ b.image).Finite ∧
      (Set.range f ∩ a.image).ncard ≤ 1 ∧ (Set.range f ∩ b.image).ncard ≤ 1 ∧
      (σ = false → Disjoint (Set.range f) a.image) ∧
      (τ = false → Disjoint (Set.range f) b.image) ∧
      ∀ u : Interval, E (f u) ≠ 0 := by
  let sx : ℝ := if σ then -1 else 1
  let sy : ℝ := if τ then -1 else 1
  have hsx : sx = -1 ∨ sx = 1 := by cases σ <;> simp [sx]
  have hsy : sy = -1 ∨ sy = 1 := by cases τ <;> simp [sy]
  have hdx : 0 < (1/2:ℝ)-sx*δ := by rcases hsx with h | h <;> rw [h] <;> nlinarith
  have hdy : 0 < (1/2:ℝ)-sy*δ := by rcases hsy with h | h <;> rw [h] <;> nlinarith
  let z : Interval → Plane := fun t => Plane.mk
    ((1-(t:ℝ))*sx*δ+(t:ℝ)*(1/2))
    ((1-(t:ℝ))*(1/2)+(t:ℝ)*sy*δ)
  have hz0 (t : Interval) : z t 0 = sx*δ+(t:ℝ)*((1/2)-sx*δ) := by dsimp [z,Plane.mk]; ring
  have hz1 (t : Interval) : z t 1 = (1/2)-(t:ℝ)*((1/2)-sy*δ) := by dsimp [z,Plane.mk]; ring
  have hzsquare (t : Interval) : z t ∈ Plane.closedSquare 0 1 := by
    have hx : |z t 0| ≤ 1/2 := by
      rw [hz0,abs_le]
      rcases hsx with h | h <;> rw [h] <;> constructor <;>
        nlinarith [t.property.1,t.property.2]
    have hy : |z t 1| ≤ 1/2 := by
      rw [hz1,abs_le]
      rcases hsy with h | h <;> rw [h] <;> constructor <;>
        nlinarith [t.property.1,t.property.2]
    change Plane.supNorm (z t-0) ≤ 1
    rw [sub_zero]
    exact max_le (hx.trans (by norm_num)) (hy.trans (by norm_num))
  have hztarget (t : Interval) : z t ∈ E.target := hsquare (hzsquare t)
  have hzc : Continuous z := by dsimp [z]; fun_prop
  let f : C(Interval,S) := ⟨E.symm ∘ z,
    E.continuousOn_symm.comp_continuous hzc hztarget⟩
  have hfs (t : Interval) : f t ∈ E.source := E.symm.map_source (hztarget t)
  have hcoord (t : Interval) : E (f t) = z t := E.right_inv (hztarget t)
  have hinj : Function.Injective f := by
    intro t u he
    have he0 := congrArg (fun x => E x 0) he
    rw [hcoord,hcoord,hz0,hz0] at he0
    apply Subtype.ext
    nlinarith
  have hsuba : (Set.range f ∩ a.image).Subsingleton := by
    rintro x ⟨⟨t,rfl⟩,ht⟩ y ⟨⟨u,rfl⟩,hu⟩
    have ht0 := (ha (f t) (hfs t)).mp ht
    have hu0 := (ha (f u) (hfs u)).mp hu
    rw [hcoord,hz0] at ht0 hu0
    have htu : t = u := Subtype.ext (by nlinarith)
    rw [htu]
  have hsubb : (Set.range f ∩ b.image).Subsingleton := by
    rintro x ⟨⟨t,rfl⟩,ht⟩ y ⟨⟨u,rfl⟩,hu⟩
    have ht0 := (hb (f t) (hfs t)).mp ht
    have hu0 := (hb (f u) (hfs u)).mp hu
    rw [hcoord,hz1] at ht0 hu0
    have htu : t = u := Subtype.ext (by nlinarith)
    rw [htu]
  refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_,
    hsuba.finite,hsubb.finite,?_,?_,?_,?_,?_⟩
  · rintro x ⟨t,rfl⟩; exact hfs t
  · rw [hcoord]; simp [z,sx,sy,Plane.mk]
  · rw [hcoord]; simp [z,sx,sy,Plane.mk]
  · exact (Set.ncard_le_one hsuba.finite).mpr (fun _ hx _ hy => hsuba hx hy)
  · exact (Set.ncard_le_one hsubb.finite).mpr (fun _ hx _ hy => hsubb hx hy)
  · intro hσ
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ hxa
    have ht0 := (ha (f t) (hfs t)).mp hxa
    rw [hcoord,hz0] at ht0
    have hsx1 : sx = 1 := by simp [sx,hσ]
    rw [hsx1] at ht0
    nlinarith [t.property.1]
  · intro hτ
    apply Set.disjoint_left.mpr
    rintro x ⟨t,rfl⟩ hxb
    have ht0 := (hb (f t) (hfs t)).mp hxb
    rw [hcoord,hz1] at ht0
    have hsy1 : sy = 1 := by simp [sy,hτ]
    rw [hsy1] at ht0
    have htpos : 0 < (1/2:ℝ)-(t:ℝ)*((1/2)-δ) := by
      nlinarith [t.property.2]
    linarith
  · intro t hzero
    have hx := congrArg (fun z : Plane => z 0) hzero
    have hy := congrArg (fun z : Plane => z 1) hzero
    rw [hcoord,hz0] at hx
    rw [hcoord,hz1] at hy
    change sx*δ+(t:ℝ)*((1/2)-sx*δ) = 0 at hx
    change (1/2:ℝ)-(t:ℝ)*((1/2)-sy*δ) = 0 at hy
    rcases hsx with hsx | hsx <;> rcases hsy with hsy | hsy <;>
      rw [hsx] at hx <;> rw [hsy] at hy <;>
      nlinarith [t.property.1,t.property.2]

end CurveComplex
#print axioms CurveComplex.source_signed_corner_connector
