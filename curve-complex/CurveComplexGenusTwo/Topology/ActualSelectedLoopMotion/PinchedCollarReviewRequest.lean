import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.ActualSelectedLoopZeroContactTerminalSector
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.UnmarkedComplementaryHalfCollar
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.PinchedStripExteriorSides
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.PinchedHalfCollarGluing
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.OpenPinchedCore

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/- Exact two-sided extension required by the original ambient-motion consumer.
   Matching complete boundary ranges is enough; no reparametrization is hidden.
   The geometric collar is an output, and P is the literal closed obstacle. -/
theorem pinched_strip_closed_obstacle_two_sided_collar
    (M : HyperellipticModel E S) (P : Set S) (hP : IsClosed P)
    (base : S) (hbase : base ∈ P) (G : C(Interval × Interval, S))
    (hends : ∀ t, G (0,t) = base ∧ G (1,t) = base)
    (hinj : ∀ s t s' t', G (s,t) = G (s',t') →
      (s = s' ∧ t = t') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (havoid : ∀ s t, G (s,t) ≠ base → G (s,t) ∉ P) :
    ∃ N : C(Interval × Interval,S),
      (∀ t, N (0,t) = base ∧ N (1,t) = base) ∧
      (∀ s t s' t', N (s,t) = N (s',t') →
        (s = s' ∧ t = t') ∨
        ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) ∧
      IsOpen (N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1)) ∧
      (∀ s t, N (s,t) ≠ base → N (s,t) ∉ P) ∧
      Set.range (fun s => N (s,⟨1/3,by norm_num⟩)) =
        Set.range (fun s => G (s,0)) ∧
      Set.range (fun s => N (s,⟨2/3,by norm_num⟩)) =
        Set.range (fun s => G (s,1)) := by
  let a : C(Interval,S) := ⟨fun s => G (s,0),G.continuous.comp (by fun_prop)⟩
  let b : C(Interval,S) := ⟨fun s => G (s,1),G.continuous.comp (by fun_prop)⟩
  have ha : ∀ s, a s = G (s,0) := fun _ => rfl
  have hb : ∀ s, b s = G (s,1) := fun _ => rfl
  have habase : a 0 = base := (hends 0).1
  have hbbase : b 0 = base := (hends 1).1
  have haloop : a 0 = a 1 := (hends 0).1.trans (hends 0).2.symm
  have hbloop : b 0 = b 1 := (hends 1).1.trans (hends 1).2.symm
  have hainj : ∀ s s', a s = a s' →
      s = s' ∨ ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) := by
    intro s s' he
    rcases hinj s 0 s' 0 he with he | he
    · exact Or.inl he.1
    · exact Or.inr he
  have hbinj : ∀ s s', b s = b s' →
      s = s' ∨ ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)) := by
    intro s s' he
    rcases hinj s 1 s' 1 he with he | he
    · exact Or.inl he.1
    · exact Or.inr he
  have haavoid : ∀ x ∈ Set.range a, x ≠ a 0 → x ∉ P := by
    rintro x ⟨s,rfl⟩ hne
    exact havoid s 0 (by simpa only [habase,ha] using hne)
  have hbavoid : ∀ x ∈ Set.range b, x ≠ b 0 → x ∉ P := by
    rintro x ⟨s,rfl⟩ hne
    exact havoid s 1 (by simpa only [hbbase,hb] using hne)
  obtain ⟨U,V,⟨DU⟩,⟨DV⟩,hUV,hGU,hGV⟩ :=
    pinched_strip_exterior_disc_sides M base G hends hinj a b ha hb
  obtain ⟨L,hL0,hLend,hLinj,hLavoid,hLU⟩ :=
    unmarked_complementary_disk_relative_half_collar M a haloop hainj U DU
      P hP (habase.symm ▸ hbase) haavoid
  obtain ⟨R,hR0,hRend,hRinj,hRavoid,hRV⟩ :=
    unmarked_complementary_disk_relative_half_collar M b hbloop hbinj V DV
      P hP (hbbase.symm ▸ hbase) hbavoid
  rw [habase] at hLend hLavoid
  rw [hbbase] at hRend hRavoid
  obtain ⟨N,hNend,hNinj,hNone,hNtwo,hNrange⟩ :=
    glue_exterior_half_collars base G L R U V hends hLend hRend
      hinj hLinj hRinj hL0 hR0 hLU hRV hUV hGU hGV
  refine ⟨N,hNend,hNinj,pinched_band_strict_core_open M base N hNend hNinj,?_,?_,?_⟩
  · intro s w hne
    rcases hNrange (Set.mem_range_self (s,w)) with (hl | hg) | hr
    · rcases hl with ⟨⟨u,v⟩,he⟩
      rw [← he] at hne ⊢
      exact hLavoid u v hne
    · rcases hg with ⟨⟨u,v⟩,he⟩
      rw [← he] at hne ⊢
      exact havoid u v hne
    · rcases hr with ⟨⟨u,v⟩,he⟩
      rw [← he] at hne ⊢
      exact hRavoid u v hne
  · exact congrArg Set.range (funext hNone)
  · exact congrArg Set.range (funext hNtwo)

end CurveComplex.HyperellipticModel
