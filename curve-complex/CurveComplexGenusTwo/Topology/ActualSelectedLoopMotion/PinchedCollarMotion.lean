import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.CompactFiberMotionExtension
import CurveComplexGenusTwo.Topology.ActualSelectedLoopMotion.SquareBandMotion

namespace CurveComplex
open Set Topology

/-- The common collapsed angular edge is handled by compact quotient descent;
no neighborhood of that common point is assumed free of obstacles. -/
theorem pinched_collared_band_ambient_motion
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (base : X) (N : C(Interval × Interval,X))
    (hends : ∀ w, N (0,w) = base ∧ N (1,w) = base)
    (hinj : ∀ s w s' w', N (s,w) = N (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hopen : IsOpen (N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1))) :
    ∃ H : AmbientIsotopy X,
      H.finalMap '' Set.range (fun s => N (s,⟨1/3,by norm_num⟩)) =
        Set.range (fun s => N (s,⟨2/3,by norm_num⟩)) ∧
      (∀ t x, x ∉ N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1) →
        H.map (t,x) = x) ∧
      (∀ t, H.map (t,base) = base) := by
  obtain ⟨K,V,hleft,hright,hfirst,hzero,hone,hfinal⟩ := square_band_ambient_motion
  let U := N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1)
  have hedge (z : Interval × Interval) (hz : z.1 = 0 ∨ z.1 = 1) : N z = base := by
    rcases hz with hz | hz
    · rw [show z = (0,z.2) from Prod.ext hz rfl]
      exact (hends z.2).1
    · rw [show z = (1,z.2) from Prod.ext hz rfl]
      exact (hends z.2).2
  have hKedge (t : Interval) (z : Interval × Interval)
      (hz : z.1 = 0 ∨ z.1 = 1) : N (K.map (t,z)) = base := by
    apply hedge
    rwa [hfirst]
  have hfiber (t : Interval) (y z : Interval × Interval) :
      N (K.map (t,y)) = N (K.map (t,z)) ↔ N y = N z := by
    constructor
    · intro he
      rcases hinj _ _ _ _ he with h | h
      · have heK : K.map (t,y) = K.map (t,z) := Prod.ext h.1 h.2
        obtain ⟨k,hk⟩ := K.homeomorphism_at t
        have hyz : y = z := k.injective (by simpa only [hk] using heK)
        exact congrArg N hyz
      · change ((K.map (t,y)).1 = 0 ∨ (K.map (t,y)).1 = 1) ∧
          ((K.map (t,z)).1 = 0 ∨ (K.map (t,z)).1 = 1) at h
        rw [hfirst,hfirst] at h
        exact (hedge y h.1).trans (hedge z h.2).symm
    · intro he
      rcases hinj _ _ _ _ he with h | h
      · exact congrArg (fun z => N (K.map (t,z))) (Prod.ext h.1 h.2)
      · exact (hKedge t y h.1).trans (hKedge t z h.2).symm
  have hfix (t : Interval) (z : Interval × Interval) (hz : N z ∉ U) :
      N (K.map (t,z)) = N z := by
    by_cases hs0 : z.1 = 0
    · exact (hKedge t z (Or.inl hs0)).trans (hedge z (Or.inl hs0)).symm
    by_cases hs1 : z.1 = 1
    · exact (hKedge t z (Or.inr hs1)).trans (hedge z (Or.inr hs1)).symm
    by_cases hw0 : z.2 = 0
    · rw [show z = (z.1,0) from Prod.ext rfl hw0,hzero]
    by_cases hw1 : z.2 = 1
    · rw [show z = (z.1,1) from Prod.ext rfl hw1,hone]
    exact False.elim (hz ⟨z,⟨⟨bot_lt_iff_ne_bot.mpr hs0,lt_top_iff_ne_top.mpr hs1⟩,
      ⟨bot_lt_iff_ne_bot.mpr hw0,lt_top_iff_ne_top.mpr hw1⟩⟩,rfl⟩)
  obtain ⟨H,hH,hout⟩ := compact_fiber_motion_extension N U hopen
    (Set.image_subset_range _ _) K hfiber hfix
  have hbase : base ∉ U := by
    rintro ⟨z,hz,hzbase⟩
    have he : N z = N (0,0) := hzbase.trans (hends 0).1.symm
    rcases hinj _ _ _ _ he with he | he
    · exact (ne_of_gt hz.1.1) he.1
    · rcases he.1 with he | he
      · exact (ne_of_gt hz.1.1) he
      · exact (ne_of_lt hz.1.2) he
  refine ⟨H,?_,hout,fun t => hout t base hbase⟩
  have hlevel (s : Interval) :
      H.finalMap (N (s,⟨1/3,by norm_num⟩)) = N (s,⟨2/3,by norm_num⟩) := by
    change H.map (1,N (s,⟨1/3,by norm_num⟩)) = _
    rw [hH]
    exact congrArg N (hfinal s)
  rw [← Set.range_comp]
  exact congrArg Set.range (funext hlevel)

/-- Every closed obstacle meeting this collar only at its common base is fixed
at every time by the actual descended ambient motion. -/
theorem pinched_collared_band_motion_fixes_obstacle
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (P : Set X) (base : X) (N : C(Interval × Interval,X))
    (hends : ∀ w, N (0,w) = base ∧ N (1,w) = base)
    (hinj : ∀ s w s' w', N (s,w) = N (s',w') →
      (s = s' ∧ w = w') ∨
      ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (hopen : IsOpen (N '' (Set.Ioo (0 : Interval) 1 ×ˢ Set.Ioo (0 : Interval) 1)))
    (havoid : ∀ s w, N (s,w) ≠ base → N (s,w) ∉ P) :
    ∃ H : AmbientIsotopy X,
      (∀ t x, x ∈ P → H.map (t,x) = x) ∧
      H.finalMap '' Set.range (fun s => N (s,⟨1/3,by norm_num⟩)) =
        Set.range (fun s => N (s,⟨2/3,by norm_num⟩)) := by
  obtain ⟨H,hmove,houtside,hbase⟩ :=
    pinched_collared_band_ambient_motion base N hends hinj hopen
  refine ⟨H,?_,hmove⟩
  intro t x hx
  by_cases he : x = base
  · simpa only [he] using hbase t
  · apply houtside
    rintro ⟨⟨s,w⟩,_,hN⟩
    exact havoid s w (hN ▸ he) (hN.symm ▸ hx)

end CurveComplex
