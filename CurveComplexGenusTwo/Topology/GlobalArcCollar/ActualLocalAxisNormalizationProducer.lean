import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualAxisLongitudinalNormalization
namespace CurveComplex
open Set Topology Schoenflies

/-- Actual longitudinal normalization at an internal point of a chart-contained
axis arc; both the radius and inverse parameter selections are produced. -/
theorem source_local_axis_normalization
    {S : Type} [TopologicalSpace S] [T2Space S]
    (p : C(Interval,S)) (hp : IsEmbedding p)
    (e : OpenPartialHomeomorph S Plane) (hps : Set.range p ⊆ e.source)
    (haxis : ∀ a, e (p a) 1 = 0)
    (t : Interval) (ht0 : 0 < (t:ℝ)) (ht1 : (t:ℝ) < 1)
    (ht : e (p t) 0 = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧
      ∃ j J : C(Set.Icc (-1 : ℝ) 1,Interval),
        IsEmbedding j ∧ IsEmbedding J ∧
        (∀ x, e (p (j x)) = Plane.mk (r*(x:ℝ)) 0) ∧
        (∀ x, e (p (J x)) = Plane.mk (2*r*(x:ℝ)) 0) := by
  let g : Interval → ℝ := fun a => e (p a) 0
  have hgc : Continuous g := by
    have he : Continuous (e ∘ p) :=
      e.continuousOn.comp_continuous p.continuous
        (fun a => hps (Set.mem_range_self a))
    exact (by fun_prop : Continuous (fun z : Plane => z 0)).comp he
  have hgi : Function.Injective g := by
    intro a b he
    apply hp.injective
    apply e.injOn (hps (Set.mem_range_self a)) (hps (Set.mem_range_self b))
    apply PiLp.ext
    intro i
    fin_cases i
    · exact he
    · change e (p a) 1 = e (p b) 1
      rw [haxis a,haxis b]
  have select (a b : Interval) (ha : g a < 0) (hb : 0 < g b) :
      ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧
        ∃ j J : C(Set.Icc (-1 : ℝ) 1,Interval),
          IsEmbedding j ∧ IsEmbedding J ∧
          (∀ x, e (p (j x)) = Plane.mk (r*(x:ℝ)) 0) ∧
          (∀ x, e (p (J x)) = Plane.mk (2*r*(x:ℝ)) 0) := by
    let d := min ε (min (-g a) (g b))
    have hd : 0 < d := lt_min hε (lt_min (by linarith) hb)
    have hdε : d ≤ ε := min_le_left _ _
    have hda : d ≤ -g a := (min_le_right _ _).trans (min_le_left _ _)
    have hdb : d ≤ g b := (min_le_right _ _).trans (min_le_right _ _)
    let r := d/4
    have hr : 0 < r := by dsimp [r]; positivity
    have har : e (p a) 0 ≤ -r := by change g a ≤ -r; dsimp [r]; linarith
    have hbr : r ≤ e (p b) 0 := by change r ≤ g b; dsimp [r]; linarith
    have ha2 : e (p a) 0 ≤ -(2*r) := by change g a ≤ -(2*r); dsimp [r]; linarith
    have hb2 : 2*r ≤ e (p b) 0 := by change 2*r ≤ g b; dsimp [r]; linarith
    obtain ⟨j,hj,hjf⟩ := source_axis_longitudinal_inverse p hp e hps haxis r hr a b har hbr
    obtain ⟨J,hJ,hJf⟩ := source_axis_longitudinal_inverse p hp e hps haxis (2*r)
      (by positivity) a b ha2 hb2
    exact ⟨r,hr,by dsimp [r]; linarith,j,J,hj,hJ,hjf,hJf⟩
  have h0t : (0:Interval) < t := ht0
  have htone : t < (1:Interval) := ht1
  have hgt : g t = 0 := ht
  rcases hgc.strictMono_of_inj_boundedOrder' hgi with hm | hm
  · apply select 0 1
    · have hh := hm h0t
      rwa [hgt] at hh
    · have hh := hm htone
      rwa [hgt] at hh
  · apply select 1 0
    · have hh := hm htone
      rwa [hgt] at hh
    · have hh := hm h0t
      rwa [hgt] at hh
end CurveComplex
#print axioms CurveComplex.source_local_axis_normalization
