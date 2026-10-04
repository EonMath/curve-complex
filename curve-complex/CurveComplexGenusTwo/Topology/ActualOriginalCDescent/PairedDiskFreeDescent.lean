import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.PairedCircle24Assembly
import CurveComplexGenusTwo.Topology.ActualMain14CNext.actual_original_circle24_paired_transverse_preparationNamedPROVED

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
open scoped Manifold ContDiff
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Schoenflies.Plane E]
set_option maxHeartbeats 10000000

private structure PairedDiskFreeState
    (M : HyperellipticModel E S) (cOrig dOrig : Circle24 M) where
  c : Circle24 M
  d : Circle24 M
  a0 : EssentialCurve E
  a1 : EssentialCurve E
  b0 : EssentialCurve E
  b1 : EssentialCurve E
  H : AmbientIsotopy E
  cMarked : MarkedIsotopyRel M cOrig.val.image c.val.image
  dMarked : MarkedIsotopyRel M dOrig.val.image d.val.image
  baseTransverse : Transverse c.val.curve d.val.curve
  aFull : a0.val.image ∪ a1.val.image = M.cover.projection ⁻¹' c.val.image
  bFull : b0.val.image ∪ b1.val.image = M.cover.projection ⁻¹' d.val.image
  aDisjoint : Disjoint a0.val.image a1.val.image
  bDisjoint : Disjoint b0.val.image b1.val.image
  aDeck : M.cover.deck '' a0.val.image = a1.val.image
  bDeck : M.cover.deck '' b0.val.image = b1.val.image
  H0 : H.finalMap '' a0.val.image = b0.val.image
  H1 : H.finalMap '' a1.val.image = b1.val.image
  ap0 : Set.BijOn M.cover.projection a0.val.image c.val.image
  ap1 : Set.BijOn M.cover.projection a1.val.image c.val.image
  bp0 : Set.BijOn M.cover.projection b0.val.image d.val.image
  bp1 : Set.BijOn M.cover.projection b1.val.image d.val.image
  ac0 : IsConnected a0.val.imageᶜ
  ac1 : IsConnected a1.val.imageᶜ
  bc0 : IsConnected b0.val.imageᶜ
  bc1 : IsConnected b1.val.imageᶜ
  t00 : Transverse a0.val b0.val
  t01 : Transverse a0.val b1.val
  t10 : Transverse a1.val b0.val
  t11 : Transverse a1.val b1.val

private noncomputable def PairedDiskFreeState.energy {M : HyperellipticModel E S}
    {cOrig dOrig : Circle24 M} (s : PairedDiskFreeState M cOrig dOrig) : Nat :=
  ((s.a0.val.image ∪ s.a1.val.image) ∩
    (s.b0.val.image ∪ s.b1.val.image)).ncard

private def PairedDiskFreeState.terminal {M : HyperellipticModel E S}
    {cOrig dOrig : Circle24 M} (s : PairedDiskFreeState M cOrig dOrig) : Prop :=
  IsEmpty (LocalSurgery.TwoCurveDisk s.a0.val s.b0.val) ∧
  IsEmpty (LocalSurgery.TwoCurveDisk s.a0.val s.b1.val) ∧
  IsEmpty (LocalSurgery.TwoCurveDisk s.a1.val s.b0.val) ∧
  IsEmpty (LocalSurgery.TwoCurveDisk s.a1.val s.b1.val)

private theorem PairedDiskFreeState.step {M : HyperellipticModel E S}
    {cOrig dOrig : Circle24 M} (s : PairedDiskFreeState M cOrig dOrig)
    (hDisk : Nonempty (LocalSurgery.TwoCurveDisk s.a0.val s.b0.val) ∨
      Nonempty (LocalSurgery.TwoCurveDisk s.a0.val s.b1.val) ∨
      Nonempty (LocalSurgery.TwoCurveDisk s.a1.val s.b0.val) ∨
      Nonempty (LocalSurgery.TwoCurveDisk s.a1.val s.b1.val)) :
    ∃ s' : PairedDiskFreeState M cOrig dOrig, s'.energy < s.energy := by
  obtain ⟨c',d',hc',hd',htbase,a0',a1',b0',b1',H',ha',hb',hAd',hBd',
    hDA',hDB',hH0',hH1',hap0',hap1',hbp0',hbp1',hAc0',hAc1',hBc0',hBc1',
    ht00',ht01',ht10',ht11',hstrict⟩ :=
    actual_circle24_paired_multicurve_strict_step M s.c s.d
      s.a0 s.a1 s.b0 s.b1 s.H s.aFull s.bFull s.aDisjoint s.bDisjoint
      s.aDeck s.bDeck s.H0 s.H1 s.ap0 s.ap1 s.bp0 s.bp1
      s.ac0 s.ac1 s.bc0 s.bc1 s.baseTransverse
      s.t00 s.t01 s.t10 s.t11 hDisk
  refine ⟨{
    c := c', d := d', a0 := a0', a1 := a1', b0 := b0', b1 := b1', H := H',
    cMarked := (markedIsotopy_equivalence M).trans s.cMarked hc',
    dMarked := (markedIsotopy_equivalence M).trans s.dMarked hd',
    baseTransverse := htbase,
    aFull := ha', bFull := hb', aDisjoint := hAd', bDisjoint := hBd',
    aDeck := hDA', bDeck := hDB', H0 := hH0', H1 := hH1',
    ap0 := hap0', ap1 := hap1', bp0 := hbp0', bp1 := hbp1',
    ac0 := hAc0', ac1 := hAc1', bc0 := hBc0', bc1 := hBc1',
    t00 := ht00', t01 := ht01', t10 := ht10', t11 := ht11'
  }, ?_⟩
  exact hstrict

private theorem PairedDiskFreeState.terminal_exists {M : HyperellipticModel E S}
    {cOrig dOrig : Circle24 M} (s : PairedDiskFreeState M cOrig dOrig) :
    ∃ s' : PairedDiskFreeState M cOrig dOrig, s'.terminal := by
  have hdesc : ∀ n : Nat, ∀ s : PairedDiskFreeState M cOrig dOrig,
      s.energy = n → ∃ s' : PairedDiskFreeState M cOrig dOrig, s'.terminal := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      by_cases hDisk :
          Nonempty (LocalSurgery.TwoCurveDisk s.a0.val s.b0.val) ∨
          Nonempty (LocalSurgery.TwoCurveDisk s.a0.val s.b1.val) ∨
          Nonempty (LocalSurgery.TwoCurveDisk s.a1.val s.b0.val) ∨
          Nonempty (LocalSurgery.TwoCurveDisk s.a1.val s.b1.val)
      · obtain ⟨s', hlt⟩ := s.step hDisk
        exact ih s'.energy (hs ▸ hlt) s' rfl
      · refine ⟨s, ?_⟩
        simp only [PairedDiskFreeState.terminal]
        push Not at hDisk
        rcases hDisk with ⟨h00,h01,h10,h11⟩
        exact ⟨h00, h01, h10, h11⟩
  exact hdesc s.energy s rfl

theorem actual_original_circle24_paired_four_crosspair_disk_free_preparation
    (M : HyperellipticModel E S) (c d : Circle24 M)
    (hup : AmbientIsotopy.Rel (M.cover.projection ⁻¹' c.val.image)
      (M.cover.projection ⁻¹' d.val.image)) :
    ∃ c' d' : Circle24 M, MarkedIsotopyRel M c.val.image c'.val.image ∧ MarkedIsotopyRel M d.val.image d'.val.image ∧
      Transverse c'.val.curve d'.val.curve ∧
      ∃ a0 a1 b0 b1 : EssentialCurve E, ∃ H : AmbientIsotopy E,
        a0.val.image ∪ a1.val.image=M.cover.projection ⁻¹' c'.val.image ∧
        b0.val.image ∪ b1.val.image=M.cover.projection ⁻¹' d'.val.image ∧
        Disjoint a0.val.image a1.val.image ∧ Disjoint b0.val.image b1.val.image ∧
        M.cover.deck '' a0.val.image=a1.val.image ∧ M.cover.deck '' b0.val.image=b1.val.image ∧
        H.finalMap '' a0.val.image=b0.val.image ∧ H.finalMap '' a1.val.image=b1.val.image ∧
        Set.BijOn M.cover.projection a0.val.image c'.val.image ∧
        Set.BijOn M.cover.projection a1.val.image c'.val.image ∧
        Set.BijOn M.cover.projection b0.val.image d'.val.image ∧
        Set.BijOn M.cover.projection b1.val.image d'.val.image ∧
        IsConnected a0.val.imageᶜ ∧ IsConnected a1.val.imageᶜ ∧
        IsConnected b0.val.imageᶜ ∧ IsConnected b1.val.imageᶜ ∧
        Transverse a0.val b0.val ∧ Transverse a0.val b1.val ∧
        Transverse a1.val b0.val ∧ Transverse a1.val b1.val ∧
        IsEmpty (LocalSurgery.TwoCurveDisk a0.val b0.val) ∧
        IsEmpty (LocalSurgery.TwoCurveDisk a0.val b1.val) ∧
        IsEmpty (LocalSurgery.TwoCurveDisk a1.val b0.val) ∧
        IsEmpty (LocalSurgery.TwoCurveDisk a1.val b1.val) := by
  obtain ⟨d0,hdi,htbase,a0,a1,b0,b1,H,ha,hb,hAd,hBd,hDA,hDB,
    hH0,hH1,hap0,hap1,hbp0,hbp1,hAc0,hAc1,hBc0,hBc1,
    ht00,ht01,ht10,ht11⟩ :=
      M.actual_original_circle24_paired_transverse_preparation c d hup
  let s : PairedDiskFreeState M c d := {
    c := c, d := d0, a0 := a0, a1 := a1, b0 := b0, b1 := b1, H := H,
    cMarked := (markedIsotopy_equivalence M).refl _, dMarked := hdi,
    baseTransverse := htbase, aFull := ha, bFull := hb,
    aDisjoint := hAd, bDisjoint := hBd, aDeck := hDA, bDeck := hDB,
    H0 := hH0, H1 := hH1, ap0 := hap0, ap1 := hap1, bp0 := hbp0,
    bp1 := hbp1, ac0 := hAc0, ac1 := hAc1, bc0 := hBc0, bc1 := hBc1,
    t00 := ht00, t01 := ht01, t10 := ht10, t11 := ht11
  }
  obtain ⟨s', hterm⟩ := s.terminal_exists
  exact ⟨s'.c, s'.d, s'.cMarked, s'.dMarked, s'.baseTransverse,
    s'.a0, s'.a1, s'.b0, s'.b1, s'.H,
    s'.aFull, s'.bFull, s'.aDisjoint, s'.bDisjoint,
    s'.aDeck, s'.bDeck, s'.H0, s'.H1,
    s'.ap0, s'.ap1, s'.bp0, s'.bp1,
    s'.ac0, s'.ac1, s'.bc0, s'.bc1,
    s'.t00, s'.t01, s'.t10, s'.t11,
    hterm.1, hterm.2.1, hterm.2.2.1, hterm.2.2.2⟩

end CurveComplex.HyperellipticModel
