import CurveComplexGenusTwo.Topology.GeometricPosition.ProperAffineCrosscut

open Set Schoenflies
namespace CurveComplex

/-- A literal straight chord between two axis-free tails creates at most one
contact, and that contact is affine in the original plane coordinates. -/
theorem countControlledArcInChordAndAxisFreeTails
    (L T D : Set Plane) (a u v b : Plane)
    (hL : IsArcBetween L a u) (hT : IsArcBetween T v b)
    (hau : a ≠ v) (hab : a ≠ b) (huv : u ≠ v)
    (hLaxis : ∀ z ∈ L, z 0 ≠ 0) (hTaxis : ∀ z ∈ T, z 0 ≠ 0)
    (hLD : L \ {a,b} ⊆ D) (hTD : T \ {a,b} ⊆ D)
    (hchordD : segment ℝ u v ⊆ D) (hD : IsOpen D) :
    ∃ C : Set Plane, IsArcBetween C a b ∧
      C ⊆ (L ∪ segment ℝ u v) ∪ T ∧ C \ {a,b} ⊆ D ∧
      (C ∩ {z : Plane | z 0 = 0}).Finite ∧
      (C ∩ {z : Plane | z 0 = 0}).ncard ≤ 1 ∧
      ∀ p ∈ C ∩ {z : Plane | z 0 = 0},
        ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ D ∧
        ∃ m : ℝ, ∀ z ∈ W, (z ∈ C ↔ z 1 = p 1 + m*z 0) := by
  classical
  have hsegmentLine (x y p : Plane) (hx : x 0 ≠ 0)
      (hp : p ∈ segment ℝ x y) (hp0 : p 0 = 0) :
      ∃ m : ℝ, ∀ z ∈ segment ℝ x y, z 1 = p 1 + m * z 0 := by
    rw [segment_eq_image_lineMap] at hp
    obtain ⟨s, hs, hsp⟩ := hp
    have hpcoord (i : Fin 2) : p i = (1-s) * x i + s * y i := by
      rw [← hsp]
      simp [AffineMap.lineMap_apply_module]
    have hxy : y 0 - x 0 ≠ 0 := by
      intro h
      have hh := hpcoord 0
      have hyx := sub_eq_zero.mp h
      rw [hyx, hp0] at hh
      exact hx (by nlinarith)
    refine ⟨(y 1 - x 1) / (y 0 - x 0), ?_⟩
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t, ht, htz⟩ := hz
    have hzcoord (i : Fin 2) : z i = (1-t) * x i + t * y i := by
      rw [← htz]
      simp [AffineMap.lineMap_apply_module]
    rw [hzcoord 0, hzcoord 1, hpcoord 1]
    have hh := hpcoord 0
    rw [hp0] at hh
    field_simp
    nlinarith [congrArg (fun a : ℝ => a * (y 1-x 1)) hh]
  have hsegmentFinite (x y : Plane) (hx : x 0 ≠ 0) :
      (segment ℝ x y ∩ {z : Plane | z 0 = 0}).Finite := by
    apply Set.Subsingleton.finite
    intro p hp q hq
    rw [segment_eq_image_lineMap] at hp hq
    obtain ⟨s, hs, hsp⟩ := hp.1
    obtain ⟨t, ht, htq⟩ := hq.1
    have hcoord : ∀ u : ℝ, (AffineMap.lineMap x y u) 0 =
        (1-u) * x 0 + u * y 0 := by
      intro u
      simp [AffineMap.lineMap_apply_module]
    have hps : (1-s) * x 0 + s * y 0 = 0 := by
      rw [← hcoord, hsp]; exact hp.2
    have hqt : (1-t) * x 0 + t * y 0 = 0 := by
      rw [← hcoord, htq]; exact hq.2
    have hxy : y 0 - x 0 ≠ 0 := by
      intro h
      have hh := sub_eq_zero.mp h
      rw [hh] at hps
      exact hx (by nlinarith)
    have hst : s = t := by
      have hh : (s-t) * (y 0-x 0) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hxy)
    rw [← hsp, ← htq, hst]
  have hu0 : u 0 ≠ 0 := hLaxis u hL.right_mem
  obtain ⟨C0,hC0sub,hC0arc⟩ := exists_arc_in_union_of_arcs hL
    (isArcBetween_segment huv) hau
  obtain ⟨C,hCsub,hCarc⟩ := exists_arc_in_union_of_arcs hC0arc hT hab
  have hcover : C ⊆ (L ∪ segment ℝ u v) ∪ T :=
    hCsub.trans (union_subset_union hC0sub subset_rfl)
  have hcontact : C ∩ {z : Plane | z 0 = 0} ⊆
      segment ℝ u v ∩ {z : Plane | z 0 = 0} := by
    intro z hz
    rcases hcover hz.1 with (hzL | hzChord) | hzT
    · exact False.elim (hLaxis z hzL hz.2)
    · exact ⟨hzChord,hz.2⟩
    · exact False.elim (hTaxis z hzT hz.2)
  have hcf := (hsegmentFinite u v hu0).subset hcontact
  have hcount : (C ∩ {z : Plane | z 0 = 0}).ncard ≤ 1 := by
    apply (Set.ncard_le_one hcf).mpr
    intro p hp q hq
    have hsub : (segment ℝ u v ∩ {z : Plane | z 0 = 0}).Subsingleton := by
      intro x hx y hy
      rw [segment_eq_image_lineMap] at hx hy
      obtain ⟨s,hs,hsx⟩ := hx.1
      obtain ⟨t,ht,hty⟩ := hy.1
      have hc (r : ℝ) : (AffineMap.lineMap u v r) 0 = (1-r)*u 0+r*v 0 := by
        simp [AffineMap.lineMap_apply_module]
      have hs0 : (1-s)*u 0+s*v 0=0 := by rw [← hc,hsx]; exact hx.2
      have ht0 : (1-t)*u 0+t*v 0=0 := by rw [← hc,hty]; exact hy.2
      have hne : v 0-u 0 ≠ 0 := by
        intro he
        have he' := sub_eq_zero.mp he
        rw [he'] at hs0
        exact hu0 (by nlinarith)
      have he : s=t := by
        apply sub_eq_zero.mp
        exact (mul_eq_zero.mp (show (s-t)*(v 0-u 0)=0 by nlinarith)).resolve_right hne
      rw [← hsx,← hty,he]
    exact hsub (hcontact hp) (hcontact hq)
  have hproper : C \ {a,b} ⊆ D := by
    intro z hz
    rcases hcover hz.1 with (hzL | hzChord) | hzT
    · exact hLD ⟨hzL,hz.2⟩
    · exact hchordD hzChord
    · exact hTD ⟨hzT,hz.2⟩
  refine ⟨C,hCarc,hcover,hproper,hcf,hcount,?_⟩
  intro p hp
  have hp0 : p 0 = 0 := hp.2
  obtain ⟨m,hm⟩ := hsegmentLine u v p hu0 (hcontact hp).1 hp.2
  let V : Set Plane := (L ∪ T)ᶜ ∩ D
  have hVo : IsOpen V :=
    (hL.isArc.isCompact.union hT.isArc.isCompact).isClosed.isOpen_compl.inter hD
  have hpV : p ∈ V := by
    refine ⟨?_,hchordD (hcontact hp).1⟩
    rintro (h | h)
    · exact hLaxis p h hp.2
    · exact hTaxis p h hp.2
  have hpa : p ≠ a := by
    intro he
    exact hLaxis a hL.left_mem (he ▸ hp.2)
  have hpb : p ≠ b := by
    intro he
    exact hTaxis b hT.right_mem (he ▸ hp.2)
  obtain ⟨W,hWo,hpW,hWV,hline⟩ := position_arc_local_affine hCarc hp.1 hpa hpb
    hVo hpV m (by
      intro z hz
      have hzChord : z ∈ segment ℝ u v := by
        rcases hcover hz.1 with (h | h) | h
        · exact False.elim (hz.2.1 (Or.inl h))
        · exact h
        · exact False.elim (hz.2.1 (Or.inr h))
      simpa [hp0] using hm z hzChord)
  refine ⟨W,hWo,hpW,fun z hz => (hWV hz).2,m,?_⟩
  intro z hz
  simpa [hp0] using hline z hz

/-- Singleton-contact special case of the assigned count-controlled producer.
This is an intermediate candidate, not the protected finite-contact target. -/
theorem countControlledProperCrosscutOfOneContact
    (E : OpenPartialHomeomorph Plane Plane)
    (hSquare : Plane.closedSquare 0 1 ⊆ E.source)
    (ha : E (Plane.mk (-1) 0) 0 ≠ 0)
    (hb : E (Plane.mk 1 0) 0 ≠ 0)
    (hf : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
      {z : Plane | z 0 = 0}).Finite)
    (hSingle : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
      {z : Plane | z 0 = 0}).Subsingleton)
    (hNonempty : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
      {z : Plane | z 0 = 0}).Nonempty) :
    ∃ B : Set Plane,
      IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
      B \ {Plane.mk (-1) 0, Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
      ((E '' B) ∩ {z : Plane | z 0 = 0}).Finite ∧
      ((E '' B) ∩ {z : Plane | z 0 = 0}).ncard ≤
        ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
          {z : Plane | z 0 = 0}).ncard ∧
      (∀ p ∈ (E '' B) ∩ {z : Plane | z 0 = 0},
        ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ E.target ∧
        ∃ m : ℝ, ∀ z ∈ W, (z ∈ E '' B ↔ z 1 = p 1 + m * z 0)) := by
  classical
  let g : ℝ → Plane := fun t => Plane.mk (2*t-1) 0
  have hg : Continuous g := by
    unfold g
    exact PiLp.continuous_toLp 2 _ |>.comp
      (continuous_pi (fun i => by fin_cases i <;> simp <;> fun_prop))
  have hgSquare (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      g t ∈ Plane.closedSquare 0 1 := by
    change Plane.supDist (g t) 0 ≤ 1
    simp only [g, Plane.supDist, Plane.supNorm, Plane.mk, sub_zero, max_le_iff]
    constructor
    · change |2*t-1| ≤ 1
      rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
    · norm_num
  have hgOpen (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      g t ∈ Plane.openSquare 0 1 := by
    rw [Plane.mem_openSquare_iff]
    intro i
    fin_cases i
    · simp only [g, PiLp.zero_apply, sub_zero]
      change |2*t-1| < 1
      rw [abs_lt]; constructor <;> linarith [ht.1,ht.2]
    · norm_num [g,Plane.mk]
  let D : Set Plane := E '' Plane.openSquare 0 1
  have hOpenSource : Plane.openSquare 0 1 ⊆ E.source :=
    (Plane.openSquare_subset_closedSquare 0 1).trans hSquare
  have hDopen : IsOpen D := E.isOpen_image_of_subset_source
    (Plane.isOpen_openSquare 0 1) hOpenSource
  have hDconn : IsPreconnected D := (Plane.convex_openSquare 0 1).isPreconnected.image
    E (E.continuousOn.mono hOpenSource)
  let f : ℝ → Plane := fun t => E (g t)
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 1) :=
    E.continuousOn.comp hg.continuousOn (fun t ht => hSquare (hgSquare t ht))
  have hfinj : Set.InjOn f (Icc (0 : ℝ) 1) := by
    intro s hs t ht h
    have hh := E.injOn (hSquare (hgSquare s hs)) (hSquare (hgSquare t ht)) h
    have hh0 := congrArg (fun z : Plane => z 0) hh
    change 2*s-1 = 2*t-1 at hh0
    linarith
  have hfD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : f t ∈ D :=
    ⟨g t,hgOpen t ht,rfl⟩
  have hf0 : f 0 = E (Plane.mk (-1) 0) := by simp [f,g]
  have hf1 : f 1 = E (Plane.mk 1 0) := by norm_num [f,g]
  have hline (t : ℝ) : g t = AffineMap.lineMap (Plane.mk (-1) 0) (Plane.mk 1 0) t := by
    ext i
    fin_cases i <;> simp [g,Plane.mk,AffineMap.lineMap_apply_module] <;> ring
  have hgrange : g '' Icc (0:ℝ) 1 = segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := by
    rw [segment_eq_image_lineMap]
    exact congrArg (fun h : ℝ → Plane => h '' Icc (0:ℝ) 1) (funext hline)
  have hfrange : f '' Icc (0:ℝ) 1 = E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0) := by
    rw [← hgrange,Set.image_image]
  have hOriginalPositive := Set.ncard_pos hf |>.mpr hNonempty
  obtain ⟨p,hp⟩ := hNonempty
  have hpimage : p ∈ f '' Icc (0:ℝ) 1 := hfrange.symm ▸ hp.1
  obtain ⟨t,htI,htp⟩ := hpimage
  have ht0 : 0 < t := by
    apply lt_of_le_of_ne htI.1
    intro he
    have he' : t=0 := he.symm
    exact ha (by simpa [← htp,he',hf0] using hp.2)
  have ht1 : t < 1 := by
    apply lt_of_le_of_ne htI.2
    intro he
    exact hb (by simpa [← htp,he,hf1] using hp.2)
  have hpD : p ∈ D := htp ▸ hfD t ⟨ht0,ht1⟩
  obtain ⟨ρ,hρ,hballD⟩ := Metric.isOpen_iff.mp hDopen p hpD
  have hfc : ContinuousAt f t :=
    (E.continuousAt (hSquare (hgSquare t htI))).comp hg.continuousAt
  have hnear : f ⁻¹' Metric.ball p ρ ∈ nhds t :=
    hfc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (by rw [htp]; exact Metric.mem_ball_self hρ))
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let δ : ℝ := min ε (min t (1-t))/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ < ε := by dsimp [δ]; linarith [min_le_left ε (min t (1-t))]
  have hδt : δ < t := by
    have hh := (min_le_right ε (min t (1-t))).trans (min_le_left t (1-t))
    dsimp [δ]; linarith
  have hδ1 : δ < 1-t := by
    have hh := (min_le_right ε (min t (1-t))).trans (min_le_right t (1-t))
    dsimp [δ]; linarith
  let s := t-δ
  let r := t+δ
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hst : s < t := by dsimp [s]; linarith
  have htr : t < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hsI : s ∈ Icc (0:ℝ) 1 := ⟨hs0.le,(hst.trans ht1).le⟩
  have hrI : r ∈ Icc (0:ℝ) 1 := ⟨(ht0.trans htr).le,hr1.le⟩
  have hsball : f s ∈ Metric.ball p ρ := by
    apply hεsub
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [s]; constructor <;> linarith
  have hrball : f r ∈ Metric.ball p ρ := by
    apply hεsub
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [r]; constructor <;> linarith
  let L := f '' Icc 0 s
  let T := f '' Icc r 1
  have hL : IsArcBetween L (f 0) (f s) := by
    simpa [L,uIcc_of_le hs0.le] using isArcBetween_subarc_of_injOn_I
      hfcont hfinj (show (0:ℝ) ∈ unitInterval from by simp) hsI (ne_of_lt hs0)
  have hT : IsArcBetween T (f r) (f 1) := by
    simpa [T,uIcc_of_le hr1.le] using isArcBetween_subarc_of_injOn_I
      hfcont hfinj hrI (show (1:ℝ) ∈ unitInterval from by simp) (ne_of_lt hr1)
  have hLaxis : ∀ z ∈ L, z 0 ≠ 0 := by
    rintro z ⟨q,hq,rfl⟩ he
    have hqI : q ∈ Icc (0:ℝ) 1 := ⟨hq.1,hq.2.trans hsI.2⟩
    have heq : f q=p := hSingle ⟨hfrange ▸ ⟨q,hqI,rfl⟩,he⟩ hp
    have hqt := hfinj hqI htI (heq.trans htp.symm)
    linarith [hq.2]
  have hTaxis : ∀ z ∈ T, z 0 ≠ 0 := by
    rintro z ⟨q,hq,rfl⟩ he
    have hqI : q ∈ Icc (0:ℝ) 1 := ⟨hrI.1.trans hq.1,hq.2⟩
    have heq : f q=p := hSingle ⟨hfrange ▸ ⟨q,hqI,rfl⟩,he⟩ hp
    have hqt := hfinj hqI htI (heq.trans htp.symm)
    linarith [hq.1]
  have hLD : L \ {f 0,f 1} ⊆ D := by
    rintro z ⟨⟨q,hq,rfl⟩,hne⟩
    have hq0 : 0 < q := lt_of_le_of_ne hq.1 (fun he => hne (Or.inl (by rw [← he])))
    exact hfD q ⟨hq0,hq.2.trans_lt (hst.trans ht1)⟩
  have hTD : T \ {f 0,f 1} ⊆ D := by
    rintro z ⟨⟨q,hq,rfl⟩,hne⟩
    have hq1 : q < 1 := lt_of_le_of_ne hq.2 (fun he => hne (Or.inr (by simp [he])))
    exact hfD q ⟨(ht0.trans htr).trans_le hq.1,hq1⟩
  have h0r : f 0 ≠ f r := by
    intro he
    have hh := hfinj (by simp) hrI he
    linarith
  have h01 : f 0 ≠ f 1 := by
    intro he
    have hh := hfinj (by simp) (by simp) he
    norm_num at hh
  have hsr : f s ≠ f r := by
    intro he
    have hh := hfinj hsI hrI he
    linarith
  have hchordD : segment ℝ (f s) (f r) ⊆ D :=
    ((convex_ball p ρ).segment_subset hsball hrball).trans hballD
  obtain ⟨C,hCarc,hcover,hCproper,hCfinite,hCone,hCgraph⟩ :=
    countControlledArcInChordAndAxisFreeTails L T D (f 0) (f s) (f r) (f 1)
      hL hT h0r h01 hsr hLaxis hTaxis hLD hTD hchordD hDopen
  have hCcount : (C ∩ {z : Plane | z 0 = 0}).ncard ≤
      ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩ {z : Plane | z 0 = 0}).ncard := by
    omega
  have hCtarget : C ⊆ E.target := by
    intro z hz
    by_cases hze : z ∈ ({f 0,f 1} : Set Plane)
    · rcases hze with rfl | hz
      · exact E.map_source (hSquare (hgSquare 0 (by simp)))
      · rw [Set.mem_singleton_iff.mp hz]
        exact E.map_source (hSquare (hgSquare 1 (by simp)))
    · obtain ⟨x,hx,rfl⟩ := hCproper ⟨hz,hze⟩
      exact E.map_source (hOpenSource hx)
  have hCregular : ∀ p ∈ C ∩ {z : Plane | z 0 = 0},
      ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ E.target ∧
      ∃ m : ℝ, ∀ z ∈ W, (z ∈ C ↔ z 1 = p 1 + m*z 0) := by
    intro q hq
    obtain ⟨W,hWo,hqW,hWD,m,hm⟩ := hCgraph q hq
    refine ⟨W,hWo,hqW,?_,m,hm⟩
    intro z hz
    obtain ⟨x,hx,rfl⟩ := hWD hz
    exact E.map_source (hOpenSource hx)
  let B : Set Plane := E.symm '' C
  have hBimage : E '' B = C := by
    ext z
    constructor
    · rintro ⟨x,⟨y,hy,rfl⟩,rfl⟩
      simpa [E.right_inv (hCtarget hy)] using hy
    · intro hz
      exact ⟨E.symm z,⟨z,hz,rfl⟩,E.right_inv (hCtarget hz)⟩
  have hBsource : B ⊆ E.source := by
    rintro z ⟨x,hx,rfl⟩
    exact E.symm.map_source (hCtarget hx)
  have hB0 : E.symm (f 0) = Plane.mk (-1) 0 := by
    rw [hf0]
    exact E.left_inv (by simpa [g] using hSquare (hgSquare 0 (by simp)))
  have hB1 : E.symm (f 1) = Plane.mk 1 0 := by
    rw [hf1]
    exact E.left_inv (by convert hSquare (hgSquare 1 (by simp)) using 1 <;> norm_num [g])
  have hBarc : IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) := by
    rw [← hB0,← hB1]
    exact hCarc.image_of_injOn hCtarget E.symm.continuousOn E.symm.injOn
  refine ⟨B,hBarc,?_,by simpa [hBimage] using hCfinite,by simpa [hBimage] using hCcount,?_⟩
  · intro z hz
    obtain ⟨x,hx,hxz⟩ := hz.1
    have hxe : x ∉ ({f 0,f 1} : Set Plane) := by
      intro he
      rcases he with he | he
      · apply hz.2
        left
        rw [← hxz,he,hB0]
      · apply hz.2
        right
        rw [← hxz,Set.mem_singleton_iff.mp he,hB1]
        exact Set.mem_singleton _
    obtain ⟨y,hy,hyx⟩ := hCproper ⟨hx,hxe⟩
    have he : E.symm x = y := by rw [← hyx,E.left_inv (hOpenSource hy)]
    rwa [← hxz,he]
  · simpa [hBimage] using hCregular

/-- The zero-contact case uses the literal original center segment. -/
theorem countControlledProperCrosscutOfNoContact
    (E : OpenPartialHomeomorph Plane Plane)
    (hNo : ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
      {z : Plane | z 0 = 0}) = ∅) :
    ∃ B : Set Plane,
      IsArcBetween B (Plane.mk (-1) 0) (Plane.mk 1 0) ∧
      B \ {Plane.mk (-1) 0, Plane.mk 1 0} ⊆ Plane.openSquare 0 1 ∧
      ((E '' B) ∩ {z : Plane | z 0 = 0}).Finite ∧
      ((E '' B) ∩ {z : Plane | z 0 = 0}).ncard ≤
        ((E '' segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0)) ∩
          {z : Plane | z 0 = 0}).ncard ∧
      (∀ p ∈ (E '' B) ∩ {z : Plane | z 0 = 0},
        ∃ W : Set Plane, IsOpen W ∧ p ∈ W ∧ W ⊆ E.target ∧
        ∃ m : ℝ, ∀ z ∈ W, (z ∈ E '' B ↔ z 1 = p 1 + m * z 0)) := by
  refine ⟨segment ℝ (Plane.mk (-1) 0) (Plane.mk 1 0),
    isArcBetween_segment (by intro he; have hh := congrArg (fun z : Plane => z 0) he; norm_num [Plane.mk] at hh),
    ?_,by rw [hNo]; exact finite_empty,le_rfl,?_⟩
  · intro z hz
    rw [segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz.1
    have ht0 : 0 < t := by
      apply lt_of_le_of_ne ht.1
      intro he
      apply hz.2
      left
      simp [← he]
    have ht1 : t < 1 := by
      apply lt_of_le_of_ne ht.2
      intro he
      apply hz.2
      right
      simp [he]
    rw [Plane.mem_openSquare_iff]
    intro i
    fin_cases i
    · simp only [AffineMap.lineMap_apply_module,PiLp.zero_apply,sub_zero]
      change |(1-t)*(-1)+t*1| < 1
      rw [abs_lt]
      constructor <;> linarith
    · simp [AffineMap.lineMap_apply_module,Plane.mk]
  · intro p hp
    rw [hNo] at hp
    exact False.elim hp

end CurveComplex
