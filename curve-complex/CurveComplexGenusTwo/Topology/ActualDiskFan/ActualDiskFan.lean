import ClassificationOfSurfaces.Moise.LineSubdivision
import ClassificationOfSurfaces.TriangleCell
import ClassificationOfSurfaces.DiskSquare
import ClassificationOfSurfaces.RepresentativeCarrier
import Mathlib
set_option maxRecDepth 3000
set_option maxHeartbeats 1500000
open Set Topology Filter
namespace CurveComplex.Hyperbolic
open LeanEval.Topology.ClassificationOfSurfaces
/-- Independent disk-fan assembly interface. It contains only radial cuts;
none of the original c-seams is identified in this carrier. -/
theorem actual_zero_handle_boundary_disk_fan (n : ℕ) (hn : 3 ≤ n) :
    ∃ (e : Fin n → PolygonCell 5 → Complex.ClosedUnitDisc),
      (∀ i, Topology.IsEmbedding (e i)) ∧
      (Set.range (fun z : Fin n × PolygonCell 5 => e z.1 z.2)=Set.univ) ∧
      (∀ (i : Fin n) (t : unitInterval),
        e i (PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) =
          e (finRotate n i) (PolygonCell.side (0 : Fin 5) t)) ∧
      (∀ (i : Fin n) (k : Fin 3) (t : unitInterval),
        e i (PolygonCell.side (⟨k.val+1,by omega⟩ : Fin 5) t) =
          Complex.ClosedUnitDisc.bdyPtOfReal
            (-((3*(i.val : ℝ))+(k.val : ℝ)+(t : ℝ))/(3*(n : ℝ)))) ∧
      (∀ u v : Fin n × PolygonCell 5,
        e u.1 u.2=e v.1 v.2 ↔ Relation.EqvGen
          (fun a b : Fin n × PolygonCell 5 => ∃ (i : Fin n) (t : unitInterval),
            a=(i,PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) ∧
            b=(finRotate n i,PolygonCell.side (0 : Fin 5) t)) u v) := by
  classical
  have hn2 : 2 ≤ n := by omega
  let weightsFan : List ℕ := [3,1,1,1,3]
  have hwFan : ∀ w∈weightsFan,0<w := by simp [weightsFan]
  have hneFan : weightsFan≠[] := by simp [weightsFan]
  let ew := WeightedCircle.circleHomeomorph weightsFan hwFan hneFan
  let triChart : PolygonCell 5 ≃ₜ TriangleCell.StandardTriangle :=
    (PolygonCell.radialHomeomorph (n:=5) (m:=3) ew).trans TriangleCell.cellHomeomorph
  have hFanAngle (i : Fin 5) (t : unitInterval) :
      ew (Circle.exp (PolygonCell.sideAngle i t)) =
        Circle.exp (2*Real.pi/9*
          (((weightsFan.take i.val).sum : ℕ)+(weightsFan[i.val]'(by simpa [weightsFan] using i.isLt) : ℝ)*(t : ℝ))) := by
    have he : PolygonCell.sideAngle i t =
        2*Real.pi/(weightsFan.length : ℝ)*((i.val : ℝ)+(t : ℝ)) := by
      simp [PolygonCell.sideAngle,weightsFan]; ring
    rw [he]
    exact WeightedCircle.circleHomeomorph_exp_index_add' weightsFan hwFan hneFan
      (⟨i.val,by simpa [weightsFan] using i.isLt⟩ : Fin weightsFan.length) t
  have hMiddleTriangle (k : Fin 3) (t : unitInterval) :
      triChart (PolygonCell.side (⟨k.val+1,by omega⟩ : Fin 5) t) =
      TriangleCell.cellHomeomorph (PolygonCell.side (1 : Fin 3)
        ⟨((k.val : ℝ)+(t : ℝ))/3, by
          have hk : (k.val : ℝ)≤2 := by exact_mod_cast (show k.val≤2 by omega)
          constructor <;> linarith [t.property.1,t.property.2,Nat.cast_nonneg (α:=ℝ) k.val]⟩) := by
    dsimp only [triChart,Homeomorph.trans_apply]
    apply congrArg TriangleCell.cellHomeomorph
    change PolygonCell.radialHomeomorph ew
      (PolygonCell.ofCircle 5 (Circle.exp (PolygonCell.sideAngle ⟨k.val+1,by omega⟩ t))) = _
    rw [PolygonCell.radialHomeomorph_ofCircle,hFanAngle]
    apply congrArg (PolygonCell.ofCircle 3)
    congr 1
    fin_cases k <;> norm_num [weightsFan,PolygonCell.sideAngle] <;> ring
  have hFirstTriangle (t : unitInterval) :
      triChart (PolygonCell.side (0 : Fin 5) t)=
        TriangleCell.cellHomeomorph (PolygonCell.side (0 : Fin 3) t) := by
    dsimp only [triChart,Homeomorph.trans_apply]
    apply congrArg TriangleCell.cellHomeomorph
    change PolygonCell.radialHomeomorph ew
      (PolygonCell.ofCircle 5 (Circle.exp (PolygonCell.sideAngle 0 t))) = _
    rw [PolygonCell.radialHomeomorph_ofCircle,hFanAngle]
    apply congrArg (PolygonCell.ofCircle 3)
    congr 1
    norm_num [weightsFan,PolygonCell.sideAngle]
    ring
  have hLastTriangle (t : unitInterval) :
      triChart (PolygonCell.side (4 : Fin 5) t)=
        TriangleCell.cellHomeomorph (PolygonCell.side (2 : Fin 3) t) := by
    dsimp only [triChart,Homeomorph.trans_apply]
    apply congrArg TriangleCell.cellHomeomorph
    change PolygonCell.radialHomeomorph ew
      (PolygonCell.ofCircle 5 (Circle.exp (PolygonCell.sideAngle 4 t))) = _
    rw [PolygonCell.radialHomeomorph_ofCircle,hFanAngle]
    apply congrArg (PolygonCell.ofCircle 3)
    congr 1
    norm_num [weightsFan,PolygonCell.sideAngle]
    ring
  let T := {z : ℝ × ℝ | 0≤z.1 ∧ 0≤z.2 ∧ z.1+z.2≤1}
  let rad (z : T) : ℝ := z.val.1+z.val.2
  let frac (z : T) : ℝ := z.val.2/rad z
  have hRad (z : T) : 0≤rad z ∧ rad z≤1 := ⟨add_nonneg z.property.1 z.property.2.1,z.property.2.2⟩
  have hFrac (z : T) : 0≤frac z ∧ frac z≤1 := by
    by_cases hr : rad z=0
    · simp [frac,hr]
    · have hp := lt_of_le_of_ne (hRad z).1 (Ne.symm hr)
      exact ⟨div_nonneg z.property.2.1 hp.le,
        (div_le_iff₀ hp).mpr (by dsimp [rad]; linarith [z.property.1])⟩
  let fan (i : Fin n) (z : T) : ℂ :=
    ((rad z : ℝ):ℂ)*(Real.fourierChar (-((i.val : ℝ)+frac z)/(n : ℝ)) : ℂ)
  have hFanNorm (i : Fin n) (z : T) : ‖fan i z‖=rad z := by
    simp only [fan,norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (hRad z).1]
  have hRadCont : Continuous rad := by fun_prop
  have hFanCont (i : Fin n) : Continuous (fan i) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hr : rad z=0
    · have hzero : fan i z=0 := by simp [fan,hr]
      change Tendsto (fan i) (𝓝 z) (𝓝 (fan i z))
      rw [hzero,tendsto_zero_iff_norm_tendsto_zero]
      simp only [hFanNorm]
      simpa [hr] using (hRadCont.continuousAt (x:=z)).tendsto
    · have hc : ContinuousAt frac z :=
        (continuous_snd.comp continuous_subtype_val).continuousAt.div hRadCont.continuousAt hr
      exact (Complex.continuous_ofReal.comp hRadCont).continuousAt.mul
        (continuous_subtype_val.continuousAt.comp
          (Real.continuous_fourierChar.continuousAt.comp
            (((continuousAt_const.add hc).neg).div_const (n : ℝ))))
  have hFanInj (i : Fin n) : Function.Injective (fan i) := by
    intro z w he
    have hr : rad z=rad w := by
      have hh := congrArg norm he
      rwa [hFanNorm,hFanNorm] at hh
    by_cases hzero : rad z=0
    · have hz0 : z.val.1=0 ∧ z.val.2=0 := by
        dsimp [rad] at hzero
        constructor <;> linarith [z.property.1,z.property.2.1]
      have hwzero : rad w=0 := hr ▸ hzero
      have hw0 : w.val.1=0 ∧ w.val.2=0 := by
        dsimp [rad] at hwzero
        constructor <;> linarith [w.property.1,w.property.2.1]
      apply Subtype.ext
      apply Prod.ext <;> linarith [hz0.1,hz0.2,hw0.1,hw0.2]
    · have hnreal : (2 : ℝ)≤n := by exact_mod_cast hn2
      have hnp : 0<(n : ℝ) := by linarith
      have hc : Real.fourierChar (-((i.val : ℝ)+frac z)/(n : ℝ)) =
          Real.fourierChar (-((i.val : ℝ)+frac w)/(n : ℝ)) := by
        apply Subtype.ext
        apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hzero)
        simpa only [fan,← hr] using he
      rw [Real.fourierChar_apply',Real.fourierChar_apply'] at hc
      obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp hc
      have hf : frac z=frac w-(k : ℝ)*(n : ℝ) := by
        have hh : -((i.val : ℝ)+frac z)/(n : ℝ) =
            -((i.val : ℝ)+frac w)/(n : ℝ)+(k : ℝ) := by nlinarith [Real.pi_pos]
        have hm := congrArg (fun t : ℝ => t*(n : ℝ)) hh
        rw [add_mul,div_mul_cancel₀ _ hnp.ne',div_mul_cancel₀ _ hnp.ne'] at hm
        linarith
      have hklo : (-1 : ℝ)<(k : ℝ) := by nlinarith [(hFrac z).1,(hFrac z).2,(hFrac w).1,(hFrac w).2]
      have hkhi : (k : ℝ)<1 := by nlinarith [(hFrac z).1,(hFrac z).2,(hFrac w).1,(hFrac w).2]
      have hklo' : (-1 : ℤ)<k := by exact_mod_cast hklo
      have hkhi' : k<(1 : ℤ) := by exact_mod_cast hkhi
      have hk0 : k=0 := by omega
      simp only [hk0,Int.cast_zero,zero_mul,sub_zero] at hf
      have hy : z.val.2=w.val.2 := by
        dsimp [frac] at hf
        rw [← hr] at hf
        exact (div_left_inj' hzero).mp hf
      apply Subtype.ext
      apply Prod.ext _ hy
      dsimp [rad] at hr
      linarith
  have hTriCoords (z : TriangleCell.StandardTriangle) :
      0≤z.val 0 ∧ 0≤z.val 1 ∧ z.val 0+z.val 1≤1 := by
    have hz : z.val∈convexHull ℝ (Set.range Moise.standardTriangleVertex) := by
      rw [← Moise.standardTrianglePlaneComplex_support]
      exact z.property
    apply (Moise.mem_standardTriangle_iff z.val).mp
    simpa [Moise.standardTriangleVertex,Moise.planePoint] using hz
  let toTriangleCoords (z : TriangleCell.StandardTriangle) : T :=
    ⟨(z.val 0,z.val 1),hTriCoords z⟩
  have hTriCoordsCont : Continuous toTriangleCoords := by
    apply Continuous.subtype_mk
    exact ((PiLp.continuous_apply (p:=2) (β:=fun _ : Fin 2 => ℝ) 0).comp continuous_subtype_val).prodMk
      ((PiLp.continuous_apply (p:=2) (β:=fun _ : Fin 2 => ℝ) 1).comp continuous_subtype_val)
  have hTriCoordsInj : Function.Injective toTriangleCoords := by
    intro z w he
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    · exact congrArg (fun a : T => a.val.1) he
    · exact congrArg (fun a : T => a.val.2) he
  let rawCut (i : Fin n) (z : PolygonCell 5) : Complex.ClosedUnitDisc :=
    ⟨fan i (toTriangleCoords (triChart z)),by
      rw [Metric.mem_closedBall,dist_zero_right]
      rw [hFanNorm]
      exact (hRad _).2⟩
  have hRawCutCont (i : Fin n) : Continuous (rawCut i) :=
    ((hFanCont i).comp (hTriCoordsCont.comp triChart.continuous)).subtype_mk _
  have hRawCutInj (i : Fin n) : Function.Injective (rawCut i) := by
    intro z w he
    apply triChart.injective
    apply hTriCoordsInj
    exact hFanInj i (congrArg Subtype.val he)
  letI : CompactSpace (PolygonCell 5) :=
    (PolygonCell.closedUnitDiscHomeomorph 5).symm.compactSpace
  have hRawCutEmbedding (i : Fin n) : Topology.IsClosedEmbedding (rawCut i) :=
    (hRawCutCont i).isClosedEmbedding (hRawCutInj i)
  have hRawCutOldBoundary (i : Fin n) (k : Fin 3) (t : unitInterval) :
      rawCut i (PolygonCell.side (⟨k.val+1,by omega⟩ : Fin 5) t)=
        Complex.ClosedUnitDisc.bdyPtOfReal
          (-((3*(i.val : ℝ))+(k.val : ℝ)+(t : ℝ))/(3*(n : ℝ))) := by
    apply Subtype.ext
    change fan i (toTriangleCoords (triChart (PolygonCell.side ⟨k.val+1,by omega⟩ t))) = _
    rw [hMiddleTriangle,TriangleCell.cellHomeomorph_side]
    dsimp [fan,toTriangleCoords,rad,frac,Moise.standardTriangleVertex]
    simp only [Fin.isValue,finRotate_apply,Fin.val_one,Nat.reduceAdd,Nat.reduceMod]
    norm_num [AffineMap.lineMap_apply,AffineMap.lineMap,Moise.planePoint]
    apply congrArg (fun c : Circle => (c : ℂ))
    congr 1
    ring
  have hRawCutFirst (i : Fin n) (t : unitInterval) :
      (rawCut i (PolygonCell.side (0 : Fin 5) t)).val =
        ((t : ℝ):ℂ)*(Real.fourierChar (-(i.val : ℝ)/(n : ℝ)) : ℂ) := by
    change fan i (toTriangleCoords (triChart (PolygonCell.side 0 t))) = _
    rw [hFirstTriangle,TriangleCell.cellHomeomorph_side]
    dsimp [fan,toTriangleCoords,rad,frac,Moise.standardTriangleVertex]
    norm_num [AffineMap.lineMap_apply,AffineMap.lineMap,Moise.planePoint]
  have hRawCutLast (i : Fin n) (t : unitInterval) :
      (rawCut i (PolygonCell.side (4 : Fin 5) (unitInterval.symm t))).val =
        ((t : ℝ):ℂ)*(Real.fourierChar (-((i.val : ℝ)+1)/(n : ℝ)) : ℂ) := by
    change fan i (toTriangleCoords (triChart (PolygonCell.side 4 (unitInterval.symm t)))) = _
    rw [hLastTriangle,TriangleCell.cellHomeomorph_side]
    dsimp [fan,toTriangleCoords,rad,frac,Moise.standardTriangleVertex]
    norm_num [AffineMap.lineMap_apply,AffineMap.lineMap,Moise.planePoint,unitInterval.symm]
    by_cases ht : (t : ℝ)=0
    · simp [ht]
      right
      exact Subtype.ext ht
    · simp [ht]
  have hRawCutRadialSeam (i : Fin n) (t : unitInterval) :
      rawCut i (PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) =
        rawCut (finRotate n i) (PolygonCell.side (0 : Fin 5) t) := by
    apply Subtype.ext
    rw [hRawCutLast,hRawCutFirst]
    congr 1
    apply congrArg (fun c : Circle => (c : ℂ))
    by_cases hi : i.val+1<n
    · have hnext : (finRotate n i).val=i.val+1 := by
        letI : NeZero n := ⟨by omega⟩
        rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1<n by omega),Nat.mod_eq_of_lt hi]
      rw [hnext]
      push_cast
      rfl
    · have hlast : i.val+1=n := by omega
      have hnext : (finRotate n i).val=0 := by
        letI : NeZero n := ⟨by omega⟩
        rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1<n by omega),hlast,Nat.mod_self]
      have he : (i.val : ℝ)+1=(n : ℝ) := by exact_mod_cast hlast
      have hnzero : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
      rw [hnext,he]
      rw [Real.fourierChar_apply',Real.fourierChar_apply']
      apply Circle.exp_eq_exp.mpr
      refine ⟨-1,?_⟩
      simp [hnzero]
  have hTriCoordsSurj : Function.Surjective toTriangleCoords := by
    intro z
    let v : Moise.Plane := Moise.planePoint z.val.1 z.val.2
    have hv : v ∈ Moise.standardTrianglePlaneComplex.support := by
      rw [Moise.standardTrianglePlaneComplex_support]
      apply (Moise.mem_standardTriangle_iff v).mpr
      change 0≤z.val.1 ∧ 0≤z.val.2 ∧ z.val.1+z.val.2≤1
      exact z.property
    exact ⟨⟨v,hv⟩,by apply Subtype.ext; rfl⟩
  have hPolar (c : Circle) : ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ Real.fourierChar (-q)=c := by
    obtain ⟨a,ha⟩ := Circle.exp_surjective c
    let x : ℝ := -a/(2*Real.pi)
    refine ⟨Int.fract x,Int.fract_nonneg _,Int.fract_lt_one _,?_⟩
    rw [Real.fourierChar_apply']
    apply Eq.trans _ ha
    apply Circle.exp_eq_exp.mpr
    refine ⟨Int.floor x,?_⟩
    have hx : (2*Real.pi)*x = -a := by dsimp [x]; field_simp
    change 2*Real.pi*(-(x-(Int.floor x : ℝ)))=a+(Int.floor x : ℝ)*(2*Real.pi)
    nlinarith
  have hFanCover : ∀ w : Complex.ClosedUnitDisc, ∃ i z, fan i z=w.val := by
    intro w
    have hw : ‖w.val‖ ≤ 1 := by
      have hh := w.property
      rwa [Metric.mem_closedBall,dist_zero_right] at hh
    by_cases hz : w.val=0
    · refine ⟨⟨0,by omega⟩,⟨(0,0),by exact ⟨by norm_num,by norm_num,by norm_num⟩⟩,?_⟩
      simp [fan,rad,hz]
    · let r : ℝ := ‖w.val‖
      have hr : 0<r := norm_pos_iff.mpr hz
      let c : Circle := ⟨w.val/(r : ℂ),by
        change w.val/(r : ℂ) ∈ Metric.sphere (0 : ℂ) 1
        rw [Metric.mem_sphere,dist_zero_right]
        rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
        exact div_self hr.ne'⟩
      obtain ⟨q,hq0,hq1,hq⟩ := hPolar c
      have hnpos : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
      let i : Fin n := ⟨⌊q*(n : ℝ)⌋₊,(Nat.floor_lt (mul_nonneg hq0 hnpos.le)).mpr (by nlinarith)⟩
      let f : ℝ := q*(n : ℝ)-(i.val : ℝ)
      have hf0 : 0≤f := by dsimp [f,i]; exact sub_nonneg.mpr (Nat.floor_le (mul_nonneg hq0 hnpos.le))
      have hf1 : f≤1 := by dsimp [f,i]; exact (Nat.self_sub_floor_lt_one _).le
      let z : T := ⟨(r*(1-f),r*f),by
        refine ⟨mul_nonneg hr.le (by linarith),mul_nonneg hr.le hf0,?_⟩
        nlinarith⟩
      refine ⟨i,z,?_⟩
      have hzrad : rad z=r := by dsimp [rad,z]; ring
      have hzfrac : frac z=f := by dsimp [frac]; rw [hzrad]; dsimp [z]; field_simp
      dsimp only [fan]
      rw [hzrad,hzfrac]
      have he : -((i.val : ℝ)+f)/(n : ℝ) = -q := by dsimp [f]; field_simp; ring
      rw [he,hq]
      change (r : ℂ)*(w.val/(r : ℂ))=w.val
      exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')
  have hCoverage : Set.range (fun z : Fin n × PolygonCell 5 => rawCut z.1 z.2)=Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    obtain ⟨i,z,hz⟩ := hFanCover w
    obtain ⟨v,hv⟩ := hTriCoordsSurj z
    refine ⟨(i,triChart.symm v),?_⟩
    apply Subtype.ext
    change fan i (toTriangleCoords (triChart (triChart.symm v)))=w.val
    simpa [hv] using hz
  let R (a b : Fin n × PolygonCell 5) : Prop := ∃ (i : Fin n) (t : unitInterval),
    a=(i,PolygonCell.side (4 : Fin 5) (unitInterval.symm t)) ∧
    b=(finRotate n i,PolygonCell.side (0 : Fin 5) t)
  have hSound : ∀ u v, Relation.EqvGen R u v → rawCut u.1 u.2=rawCut v.1 v.2 := by
    intro u v h
    induction h with
    | rel a b h =>
      obtain ⟨i,t,rfl,rfl⟩ := h
      exact hRawCutRadialSeam i t
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  have hStep (i : Fin n) (t : unitInterval) : Relation.EqvGen R
      (i,PolygonCell.side (4 : Fin 5) (unitInterval.symm t))
      (finRotate n i,PolygonCell.side (0 : Fin 5) t) :=
    Relation.EqvGen.rel _ _ ⟨i,t,rfl,rfl⟩
  have hAtFirst (i : Fin n) (z : PolygonCell 5)
      (hf : frac (toTriangleCoords (triChart z))=0) :
      z=PolygonCell.side (0 : Fin 5) ⟨rad (toTriangleCoords (triChart z)),hRad _⟩ := by
    apply hRawCutInj i
    apply Subtype.ext
    rw [hRawCutFirst]
    change fan i (toTriangleCoords (triChart z)) = _
    simp only [fan,hf,add_zero]
  have hAtLast (i : Fin n) (z : PolygonCell 5)
      (hf : frac (toTriangleCoords (triChart z))=1) :
      z=PolygonCell.side (4 : Fin 5) (unitInterval.symm ⟨rad (toTriangleCoords (triChart z)),hRad _⟩) := by
    apply hRawCutInj i
    apply Subtype.ext
    rw [hRawCutLast]
    change fan i (toTriangleCoords (triChart z)) = _
    simp only [fan,hf]
  have hAtCenter (i : Fin n) (z : PolygonCell 5)
      (hr : rad (toTriangleCoords (triChart z))=0) : z=PolygonCell.side (0 : Fin 5) 0 := by
    apply hRawCutInj i
    apply Subtype.ext
    rw [hRawCutFirst]
    change fan i (toTriangleCoords (triChart z)) = _
    simp [fan,hr]
  have hCenterLast (i : Fin n) : PolygonCell.side (0 : Fin 5) 0=
      PolygonCell.side (4 : Fin 5) (unitInterval.symm 0) := by
    apply hRawCutInj i
    apply Subtype.ext
    rw [hRawCutFirst,hRawCutLast]
    simp
  have hNext (i j : Fin n) (hij : i.val+1=j.val) : finRotate n i=j := by
    apply Fin.ext
    letI : NeZero n := ⟨by omega⟩
    rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1<n by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact hij
  have hWrap (i j : Fin n) (hi : i.val+1=n) (hj : j.val=0) : finRotate n i=j := by
    apply Fin.ext
    letI : NeZero n := ⟨by omega⟩
    rw [finRotate_apply,Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (show 1<n by omega),hi,Nat.mod_self,hj]
  have hCenters (i j : Fin n) : Relation.EqvGen R
      (i,PolygonCell.side (0 : Fin 5) 0) (j,PolygonCell.side (0 : Fin 5) 0) := by
    have hz (j : Fin n) : Relation.EqvGen R
        (⟨0,by omega⟩,PolygonCell.side (0 : Fin 5) 0) (j,PolygonCell.side (0 : Fin 5) 0) := by
      induction hv : j.val generalizing j with
      | zero =>
        have hj : j=(⟨0,by omega⟩ : Fin n) := Fin.ext hv
        rw [hj]
        exact Relation.EqvGen.refl _
      | succ k ih =>
        let a : Fin n := ⟨k,by omega⟩
        have ha : Relation.EqvGen R (⟨0,by omega⟩,PolygonCell.side (0 : Fin 5) 0)
            (a,PolygonCell.side (0 : Fin 5) 0) := ih a rfl
        have hs := hStep a 0
        rw [← hCenterLast a,hNext a j (by dsimp [a]; omega)] at hs
        exact Relation.EqvGen.trans _ _ _ ha hs
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hz i)) (hz j)
  have hAngleClass (i j : Fin n) (f g : ℝ) (hf : 0≤f ∧ f≤1) (hg : 0≤g ∧ g≤1)
      (he : Real.fourierChar (-((i.val : ℝ)+f)/(n : ℝ)) =
        Real.fourierChar (-((j.val : ℝ)+g)/(n : ℝ))) :
      i=j ∨ (finRotate n i=j ∧ f=1 ∧ g=0) ∨ (finRotate n j=i ∧ f=0 ∧ g=1) := by
    have hnpos : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
    have hi0 : 0≤(i.val : ℝ) := Nat.cast_nonneg _
    have hj0 : 0≤(j.val : ℝ) := Nat.cast_nonneg _
    have hi1 : (i.val : ℝ)+1≤n := by exact_mod_cast i.isLt
    have hj1 : (j.val : ℝ)+1≤n := by exact_mod_cast j.isLt
    rw [Real.fourierChar_apply',Real.fourierChar_apply'] at he
    obtain ⟨k,hk⟩ := Circle.exp_eq_exp.mp he
    have hd : (i.val : ℝ)+f=((j.val : ℝ)+g)-(k : ℝ)*(n : ℝ) := by
      have hh : -((i.val : ℝ)+f)/(n : ℝ) = -((j.val : ℝ)+g)/(n : ℝ)+(k : ℝ) := by
        nlinarith [Real.pi_pos]
      have hm := congrArg (fun t : ℝ => t*(n : ℝ)) hh
      rw [add_mul,div_mul_cancel₀ _ hnpos.ne',div_mul_cancel₀ _ hnpos.ne'] at hm
      linarith
    have hklo : (-1 : ℝ)≤(k : ℝ) := by nlinarith
    have hkhi : (k : ℝ)≤1 := by nlinarith
    have hklo' : (-1 : ℤ)≤k := by exact_mod_cast hklo
    have hkhi' : k≤(1 : ℤ) := by exact_mod_cast hkhi
    have hkcases : k=-1 ∨ k=0 ∨ k=1 := by omega
    rcases hkcases with hkm|hk0|hkp
    · subst k
      norm_num at hd
      have hi : i.val+1=n := by
        have hh : (i.val : ℝ)+1=(n : ℝ) := by linarith
        exact_mod_cast hh
      have hj : j.val=0 := by
        have hh : (j.val : ℝ)=0 := by linarith
        exact_mod_cast hh
      exact Or.inr (Or.inl ⟨hWrap i j hi hj,by linarith,by linarith⟩)
    · subst k
      norm_num at hd
      rcases lt_trichotomy i.val j.val with hij|hij|hij
      · have hreal : (i.val : ℝ)+1 ≤ (j.val : ℝ) := by exact_mod_cast hij
        have hv : i.val+1=j.val := by
          have hh : (i.val : ℝ)+1=(j.val : ℝ) := by linarith
          exact_mod_cast hh
        exact Or.inr (Or.inl ⟨hNext i j hv,by linarith,by linarith⟩)
      · exact Or.inl (Fin.ext hij)
      · have hreal : (j.val : ℝ)+1 ≤ (i.val : ℝ) := by exact_mod_cast hij
        have hv : j.val+1=i.val := by
          have hh : (j.val : ℝ)+1=(i.val : ℝ) := by linarith
          exact_mod_cast hh
        exact Or.inr (Or.inr ⟨hNext j i hv,by linarith,by linarith⟩)
    · subst k
      norm_num at hd
      have hj : j.val+1=n := by
        have hh : (j.val : ℝ)+1=(n : ℝ) := by linarith
        exact_mod_cast hh
      have hi : i.val=0 := by
        have hh : (i.val : ℝ)=0 := by linarith
        exact_mod_cast hh
      exact Or.inr (Or.inr ⟨hWrap j i hj hi,by linarith,by linarith⟩)
  have hComplete : ∀ u v, rawCut u.1 u.2=rawCut v.1 v.2 → Relation.EqvGen R u v := by
    rintro ⟨i,z⟩ ⟨j,w⟩ he
    have hv := congrArg Subtype.val he
    change fan i (toTriangleCoords (triChart z))=fan j (toTriangleCoords (triChart w)) at hv
    have hr : rad (toTriangleCoords (triChart z))=rad (toTriangleCoords (triChart w)) := by
      have hh := congrArg norm hv
      rwa [hFanNorm,hFanNorm] at hh
    by_cases hz : rad (toTriangleCoords (triChart z))=0
    · rw [hAtCenter i z hz,hAtCenter j w (hr ▸ hz)]
      exact hCenters i j
    · have hc : Real.fourierChar (-((i.val : ℝ)+frac (toTriangleCoords (triChart z)))/(n : ℝ)) =
          Real.fourierChar (-((j.val : ℝ)+frac (toTriangleCoords (triChart w)))/(n : ℝ)) := by
        apply Subtype.ext
        apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hz)
        simpa only [fan,← hr] using hv
      rcases hAngleClass i j _ _ (hFrac _) (hFrac _) hc with hij|⟨hij,hf,hg⟩|⟨hji,hf,hg⟩
      · subst j
        have hzw : z=w := hRawCutInj i he
        subst w
        exact Relation.EqvGen.refl _
      · rw [hAtLast i z hf,hAtFirst j w hg]
        have ht : (⟨rad (toTriangleCoords (triChart z)),hRad _⟩ : unitInterval)=
            ⟨rad (toTriangleCoords (triChart w)),hRad _⟩ := Subtype.ext hr
        rw [← ht,← hij]
        exact hStep i _
      · rw [hAtFirst i z hf,hAtLast j w hg]
        have ht : (⟨rad (toTriangleCoords (triChart z)),hRad _⟩ : unitInterval)=
            ⟨rad (toTriangleCoords (triChart w)),hRad _⟩ := Subtype.ext hr
        rw [ht,← hji]
        exact Relation.EqvGen.symm _ _ (hStep j _)
  refine ⟨rawCut,fun i => (hRawCutEmbedding i).isEmbedding,hCoverage,
    hRawCutRadialSeam,hRawCutOldBoundary,?_⟩
  intro u v
  exact ⟨hComplete u v,hSound u v⟩
end CurveComplex.Hyperbolic
