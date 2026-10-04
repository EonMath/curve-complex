import CurveComplexGenusTwo.Topology.ThetaRetention.ActualInternalSurfaceSides
import CurveComplexGenusTwo.Topology.ThetaRetention.ActualSourceSurgeryBranches

namespace CurveComplex
open Set Topology Schoenflies

/-- A local infinite instance used solely to select endpoints avoiding a given
circle point. The injection is certified on an interval shorter than one turn. -/
theorem source_circle_infinite : Infinite Circle := by
  letI : Infinite ↥(Icc (0:ℝ) Real.pi) := (Set.Icc_infinite Real.pi_pos).to_subtype
  apply Infinite.of_injective (fun u : ↥(Icc (0:ℝ) Real.pi) => Circle.exp u)
  intro u v he
  apply Subtype.ext
  exact Circle.exp_injOn_Icc (by linarith [Real.pi_pos]) u.property v.property he

/-- Any actual embedded source circle has dense complement in the surface.
The proof isolates an arc containing the chosen point away from both endpoints
and uses the actual local band to obtain complementary tracks approaching it. -/
theorem source_curve_complement_dense
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (c : Curve S) : Dense c.imageᶜ := by
  letI : Infinite Circle := source_circle_infinite
  have hpoint : ∀ z : Circle, c.map z ∈ closure c.imageᶜ := by
    intro z
    obtain ⟨s,hs⟩ := (Set.toFinite ({z} : Set Circle)).exists_notMem
    obtain ⟨t,ht⟩ := (Set.toFinite ({s,z} : Set Circle)).exists_notMem
    have hsz : s ≠ z := by simpa using hs
    have hts : t ≠ s := by intro he; exact ht (Or.inl he)
    have htz : t ≠ z := by intro he; exact ht (Or.inr he)
    have hxy : c.map s ≠ c.map t := fun he => hts (c.embedded.injective he).symm
    have hzs : c.map z ≠ c.map s := fun he => hsz (c.embedded.injective he).symm
    have hzt : c.map z ≠ c.map t := fun he => htz (c.embedded.injective he).symm
    obtain ⟨p,q,hp,hq,hp0,hq0,hp1,hq1,hcover,hinter⟩ :=
      source_curve_complementary_arcs c (c.map s) (c.map t) (Set.mem_range_self s) (Set.mem_range_self t) hxy
    have hprod (p q : C(Interval,S)) (hp : IsEmbedding p)
        (hp0 : p 0 = c.map s) (hp1 : p 1 = c.map t)
        (hcover : Set.range p ∪ Set.range q = c.image)
        (hinter : Set.range p ∩ Set.range q = {c.map s,c.map t})
        (hzp : c.map z ∈ Set.range p) : c.map z ∈ closure c.imageᶜ := by
      have hzq : c.map z ∉ Set.range q := by
        intro he
        have he' : c.map z ∈ ({c.map s,c.map t} : Set S) := hinter ▸ ⟨hzp,he⟩
        exact he'.elim hzs (fun he => hzt (Set.mem_singleton_iff.mp he))
      obtain ⟨u,hu⟩ := hzp
      have hu0 : u ≠ 0 := by intro he; exact hzs (hu.symm.trans (he ▸ hp0))
      have hu1 : u ≠ 1 := by intro he; exact hzt (hu.symm.trans (he ▸ hp1))
      let D : Set S := (Set.range q)ᶜ
      have hD : IsOpen D := (isCompact_range q.continuous).isClosed.isOpen_compl
      let pp : Path (p 0) (p 1) := ⟨p,rfl,rfl⟩
      obtain ⟨C,hCu⟩ := source_embedded_path_internal_local_sides pp hp u
        (lt_of_le_of_ne u.property.1 hu0.symm) (lt_of_le_of_ne u.property.2 hu1)
        D hD (hu ▸ hzq)
      have hleft : C.left ⊆ c.imageᶜ := by
        intro x hx
        have hd := C.left_subset_diff hx
        intro hc
        rw [← hcover] at hc
        exact hc.elim hd.2 hd.1
      have hxC : c.map z ∈ C.nbhd := hu ▸ hCu
      have hpC : c.map z ∈ Set.range pp := ⟨u,hu⟩
      exact closure_mono hleft (C.limit_left ⟨hxC,hpC⟩)
    have hzCover : c.map z ∈ Set.range p ∪ Set.range q := hcover.symm ▸ Set.mem_range_self z
    rcases hzCover with hzp | hzq
    · exact hprod p q hp hp0 hp1 hcover hinter hzp
    · exact hprod q p hq hq0 hq1
        (by simpa only [Set.union_comm] using hcover)
        (by simpa only [Set.inter_comm] using hinter) hzq
  intro x
  by_cases hx : x ∈ c.image
  · obtain ⟨z,rfl⟩ := hx
    exact hpoint z
  · exact subset_closure hx

end CurveComplex
#print axioms CurveComplex.source_curve_complement_dense
