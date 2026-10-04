import CurveComplexGenusTwo.Cover.ActualWholeBankSectorSide
import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import CurveComplexGenusTwo.Topology.FrontierCircle.FrontierGeometry
import Mathlib
open Set Metric Topology
open scoped Topology
namespace AlternatingSphereCover
set_option maxHeartbeats 800000
theorem actual_pinned_north_five_source_edge_tree_whole_strip (H : StandardDisk ≃ₜ closedBall (0 : ℝ × ℝ) 1)
    (hImages : ∀ i : Fin 6,
      H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
        closedArcSector i p ∧ v=diskBoundaryPoint p hp} =
      {z : closedBall (0 : ℝ × ℝ) 1 | match i.val with
      | 0 => z.val.1=1
      | 1 => z.val.2=1 ∧ 0≤z.val.1
      | 2 => z.val.2=1 ∧ z.val.1≤0
      | 3 => z.val.1= -1
      | 4 => z.val.2= -1 ∧ z.val.1≤0
      | _ => z.val.2= -1 ∧ 0≤z.val.1}) :
    let D := Set.Icc (-2:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let K : Set D := {v | v.1.val=0 ∧ |v.2.val|≤1}
    ∃ E : C(D,Total), IsEmbedding E ∧
      E '' K = northDiskFace true ''
        {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
          (∃ i : Fin 6, i≠0 ∧ closedArcSector i p) ∧ v=diskBoundaryPoint p hp} ∧
      (∀ v, (|v.1.val|<2 ∧ |v.2.val|<2) → E v∈interior (Set.range E)) := by
  letI : T2Space Total := actual_t2Space
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Total := actualChartedSpace
  have endpoint :
        ∃ f : C(Icc (-1/4:ℝ) (13/4),Total), IsEmbedding f ∧
          (∀ t, ∃ v : StandardDisk, f t=northDiskFace true v ∧
            (H v).val=(min 1 (max (-1) (max (1-2*t.val) (2*t.val-5))),
              min 1 (max (-1) (3-2*t.val))+2*min t.val 0+2*max (t.val-3) 0)) ∧
          f '' {t | 0≤t.val ∧ t.val≤3} = northDiskFace true ''
            {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
              (∃ i : Fin 6, i≠0 ∧ closedArcSector i p) ∧ v=diskBoundaryPoint p hp}
      := by
      letI : T2Space Total := actual_t2Space
      let X (t : ℝ) := max (-1:ℝ) (max (1-2*t) (2*t-5))
      let Y (t : ℝ) := min (1:ℝ) (max (-1) (3-2*t))
      have hxy (t : Icc (0:ℝ) 3) : (X t.val,Y t.val) ∈ closedBall (0 : ℝ × ℝ) 1 := by
        rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
        dsimp [X,Y]
        constructor
        · constructor
          · exact le_max_left _ _
          · exact max_le (by norm_num) (max_le (by linarith [t.property.1]) (by linarith [t.property.2]))
        · constructor
          · exact le_min (by norm_num) (le_max_left _ _)
          · exact min_le_left _ _
      let q : C(Icc (0:ℝ) 3,closedBall (0 : ℝ × ℝ) 1) :=
        ⟨fun t => ⟨(X t.val,Y t.val),hxy t⟩,by dsimp [X,Y];fun_prop⟩
      have htop (t : ℝ) (h : t≤1) : X t=1-2*t ∧ Y t=1 := by
        dsimp [X,Y]
        rw [max_eq_left (by linarith : 2*t-5≤1-2*t),max_eq_right (by linarith : -1≤1-2*t),
          max_eq_right (by linarith : -1≤3-2*t),min_eq_left (by linarith : 1≤3-2*t)]
        exact ⟨rfl,rfl⟩
      have hmid (t : ℝ) (h : 1≤t) (hh : t≤2) : X t= -1 ∧ Y t=3-2*t := by
        dsimp [X,Y]
        rw [max_eq_left (max_le (by linarith) (by linarith)),
          max_eq_right (by linarith : -1≤3-2*t),min_eq_right (by linarith : 3-2*t≤1)]
        exact ⟨rfl,rfl⟩
      have hbottom (t : ℝ) (h : 2≤t) : X t=2*t-5 ∧ Y t= -1 := by
        dsimp [X,Y]
        rw [max_eq_right (by linarith : 1-2*t≤2*t-5),max_eq_right (by linarith : -1≤2*t-5),
          max_eq_left (by linarith : 3-2*t≤ -1)]
        norm_num
      have hqi : Function.Injective q := by
        intro t u he
        have hx := congrArg (fun z => z.val.1) he
        have hy := congrArg (fun z => z.val.2) he
        change X t.val=X u.val at hx
        change Y t.val=Y u.val at hy
        apply Subtype.ext
        rcases le_or_gt t.val 1 with ht|ht
        · obtain ⟨tx,ty⟩ := htop t.val ht
          rcases le_or_gt u.val 1 with hu|hu
          · obtain ⟨ux,uy⟩ := htop u.val hu;rw [tx,ux] at hx;linarith
          · rcases le_or_gt u.val 2 with hu2|hu2
            · obtain ⟨ux,uy⟩ := hmid u.val hu.le hu2;rw [ty,uy] at hy;linarith
            · obtain ⟨ux,uy⟩ := hbottom u.val hu2.le;rw [ty,uy] at hy;norm_num at hy
        · rcases le_or_gt t.val 2 with ht2|ht2
          · obtain ⟨tx,ty⟩ := hmid t.val ht.le ht2
            rcases le_or_gt u.val 1 with hu|hu
            · obtain ⟨ux,uy⟩ := htop u.val hu;rw [tx,ux] at hx;linarith
            · rcases le_or_gt u.val 2 with hu2|hu2
              · obtain ⟨ux,uy⟩ := hmid u.val hu.le hu2;rw [ty,uy] at hy;linarith
              · obtain ⟨ux,uy⟩ := hbottom u.val hu2.le;rw [tx,ux] at hx;linarith
          · obtain ⟨tx,ty⟩ := hbottom t.val ht2.le
            rcases le_or_gt u.val 1 with hu|hu
            · obtain ⟨ux,uy⟩ := htop u.val hu;rw [ty,uy] at hy;norm_num at hy
            · rcases le_or_gt u.val 2 with hu2|hu2
              · obtain ⟨ux,uy⟩ := hmid u.val hu.le hu2;rw [tx,ux] at hx;linarith
              · obtain ⟨ux,uy⟩ := hbottom u.val hu2.le;rw [tx,ux] at hx;linarith
      have hqr : Set.range q = {z : closedBall (0 : ℝ × ℝ) 1 | z.val.1= -1 ∨ z.val.2=1 ∨ z.val.2= -1} := by
        ext z
        constructor
        · rintro ⟨t,rfl⟩
          rcases le_or_gt t.val 1 with ht|ht
          · right;left;exact (htop t.val ht).2
          · rcases le_or_gt t.val 2 with ht2|ht2
            · left;exact (hmid t.val ht.le ht2).1
            · right;right;exact (hbottom t.val ht2.le).2
        · intro hz
          have hb : (-1≤z.val.1 ∧ z.val.1≤1) ∧ (-1≤z.val.2 ∧ z.val.2≤1) := by
            simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using z.property
          rcases hz with hx|hy|hy
          · let t : Icc (0:ℝ) 3 := ⟨(3-z.val.2)/2,⟨by linarith [hb.2.2],by linarith [hb.2.1]⟩⟩
            have ht1 : 1≤t.val := by dsimp [t];linarith [hb.2.2]
            have ht2 : t.val≤2 := by dsimp [t];linarith [hb.2.1]
            refine ⟨t,?_⟩
            apply Subtype.ext;apply Prod.ext
            · change X t.val=z.val.1;rw [(hmid t.val ht1 ht2).1,hx]
            · change Y t.val=z.val.2;rw [(hmid t.val ht1 ht2).2];dsimp [t];ring
          · let t : Icc (0:ℝ) 3 := ⟨(1-z.val.1)/2,⟨by linarith [hb.1.2],by linarith [hb.1.1]⟩⟩
            have ht : t.val≤1 := by dsimp [t];linarith [hb.1.1]
            refine ⟨t,?_⟩
            apply Subtype.ext;apply Prod.ext
            · change X t.val=z.val.1;rw [(htop t.val ht).1];dsimp [t];ring
            · change Y t.val=z.val.2;rw [(htop t.val ht).2,hy]
          · let t : Icc (0:ℝ) 3 := ⟨(z.val.1+5)/2,⟨by linarith [hb.1.1],by linarith [hb.1.2]⟩⟩
            have ht : 2≤t.val := by dsimp [t];linarith [hb.1.1]
            refine ⟨t,?_⟩
            apply Subtype.ext;apply Prod.ext
            · change X t.val=z.val.1;rw [(hbottom t.val ht).1];dsimp [t];ring
            · change Y t.val=z.val.2;rw [(hbottom t.val ht).2,hy]
      let Xe (t : ℝ) := min (1:ℝ) (X t)
      let Ye (t : ℝ) := Y t+2*min t 0+2*max (t-3) 0
      have hlow (t : ℝ) (ht : t≤0) : Xe t=1 ∧ Ye t=1+2*t := by
        obtain ⟨hx,hy⟩ := htop t (by linarith)
        dsimp [Xe,Ye]
        rw [hx,hy,min_eq_left (by linarith : 1≤1-2*t),
          min_eq_left ht,max_eq_right (by linarith : t-3≤0)]
        constructor <;> ring
      have hhigh (t : ℝ) (ht : 3≤t) : Xe t=1 ∧ Ye t=2*t-7 := by
        obtain ⟨hx,hy⟩ := hbottom t (by linarith)
        dsimp [Xe,Ye]
        rw [hx,hy,min_eq_left (by linarith : 1≤2*t-5),
          min_eq_right (by linarith : 0≤t),max_eq_left (by linarith : 0≤t-3)]
        constructor <;> ring
      have hcore (t : ℝ) (hl : 0≤t) (hr : t≤3) : Xe t=X t ∧ Ye t=Y t := by
        have hb : (-1≤X t ∧ X t≤1) ∧ (-1≤Y t ∧ Y t≤1) := by
          simpa only [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_le_iff,abs_le] using hxy ⟨t,⟨hl,hr⟩⟩
        have hh : X t≤1 := hb.1.2
        dsimp [Xe,Ye]
        rw [min_eq_right hh,min_eq_right hl,max_eq_right (by linarith : t-3≤0)]
        constructor <;> ring
      have hXone (t : ℝ) (hx : Xe t=1) : t≤0 ∨ 3≤t := by
        have hh : 1≤X t := by
          have hm : Xe t≤X t := min_le_right _ _
          rw [hx] at hm;exact hm
        dsimp [X] at hh
        rcases le_max_iff.mp hh with h|h
        · linarith
        · rcases le_max_iff.mp h with h|h
          · left;linarith
          · right;linarith
      have hExy (t : Icc (-1/4:ℝ) (13/4)) : (Xe t.val,Ye t.val) ∈ closedBall (0 : ℝ × ℝ) 1 := by
        rcases le_or_gt t.val 0 with ht|ht
        · rw [(hlow t.val ht).1,(hlow t.val ht).2]
          rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
          constructor <;> constructor <;> linarith [t.property.1]
        · rcases le_or_gt 3 t.val with ht3|ht3
          · rw [(hhigh t.val ht3).1,(hhigh t.val ht3).2]
            rw [mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff,abs_le,abs_le]
            constructor <;> constructor <;> linarith [t.property.2]
          · rw [(hcore t.val ht.le ht3.le).1,(hcore t.val ht.le ht3.le).2]
            exact hxy ⟨t.val,⟨ht.le,ht3.le⟩⟩
      let qe : C(Icc (-1/4:ℝ) (13/4),closedBall (0 : ℝ × ℝ) 1) :=
        ⟨fun t => ⟨(Xe t.val,Ye t.val),hExy t⟩,by dsimp [Xe,Ye,X,Y];fun_prop⟩
      have hqei : Function.Injective qe := by
        intro t u he
        have hx := congrArg (fun z => z.val.1) he
        have hy := congrArg (fun z => z.val.2) he
        change Xe t.val=Xe u.val at hx
        change Ye t.val=Ye u.val at hy
        apply Subtype.ext
        rcases le_or_gt t.val 0 with ht|ht
        · have hu := hXone u.val (hx.symm.trans (hlow t.val ht).1)
          rcases hu with hu|hu
          · rw [(hlow t.val ht).2,(hlow u.val hu).2] at hy;linarith
          · rw [(hlow t.val ht).2,(hhigh u.val hu).2] at hy
            linarith [t.property.1,u.property.2]
        · rcases le_or_gt 3 t.val with ht3|ht3
          · have hu := hXone u.val (hx.symm.trans (hhigh t.val ht3).1)
            rcases hu with hu|hu
            · rw [(hhigh t.val ht3).2,(hlow u.val hu).2] at hy
              linarith [t.property.2,u.property.1]
            · rw [(hhigh t.val ht3).2,(hhigh u.val hu).2] at hy;linarith
          · rcases le_or_gt u.val 0 with hu|hu
            · rcases hXone t.val (hx.trans (hlow u.val hu).1) with hh|hh <;> linarith
            · rcases le_or_gt 3 u.val with hu3|hu3
              · rcases hXone t.val (hx.trans (hhigh u.val hu3).1) with hh|hh <;> linarith
              · rw [(hcore t.val ht.le ht3.le).1,(hcore u.val hu.le hu3.le).1] at hx
                rw [(hcore t.val ht.le ht3.le).2,(hcore u.val hu.le hu3.le).2] at hy
                have he0 : q ⟨t.val,⟨ht.le,ht3.le⟩⟩=q ⟨u.val,⟨hu.le,hu3.le⟩⟩ :=
                  Subtype.ext (Prod.ext hx hy)
                exact congrArg (fun z : Icc (0:ℝ) 3 => z.val) (hqi he0)
      have hqeCore : qe '' {t | 0≤t.val ∧ t.val≤3}=Set.range q := by
        ext z
        constructor
        · rintro ⟨t,⟨hl,hr⟩,rfl⟩
          refine ⟨⟨t.val,⟨hl,hr⟩⟩,?_⟩
          apply Subtype.ext;apply Prod.ext
          · exact (hcore t.val hl hr).1.symm
          · exact (hcore t.val hl hr).2.symm
        · rintro ⟨t,rfl⟩
          let te : Icc (-1/4:ℝ) (13/4) := ⟨t.val,⟨by linarith [t.property.1],by linarith [t.property.2]⟩⟩
          refine ⟨te,⟨t.property.1,t.property.2⟩,?_⟩
          apply Subtype.ext;apply Prod.ext
          · exact (hcore t.val t.property.1 t.property.2).1
          · exact (hcore t.val t.property.1 t.property.2).2
      let f : C(Icc (-1/4:ℝ) (13/4),Total) := ⟨fun t => northDiskFace true (H.symm (qe t)),
        (northDiskFace_continuous true).comp (H.symm.continuous.comp qe.continuous)⟩
      have hfim : f '' {t | 0≤t.val ∧ t.val≤3}=northDiskFace true '' (H.symm ''
          {z : closedBall (0 : ℝ × ℝ) 1 | z.val.1= -1 ∨ z.val.2=1 ∨ z.val.2= -1}) := by
        rw [←hqr,←hqeCore]
        ext z
        constructor
        · rintro ⟨t,ht,rfl⟩
          exact ⟨H.symm (qe t),⟨qe t,⟨t,ht,rfl⟩,rfl⟩,rfl⟩
        · rintro ⟨v,⟨w,⟨t,ht,rfl⟩,rfl⟩,rfl⟩
          exact ⟨t,ht,rfl⟩
      let A : Set StandardDisk := {v | ∃ p : Sphere, ∃ hp : height p=0,
        (∃ i : Fin 6, i≠0 ∧ closedArcSector i p) ∧ v=diskBoundaryPoint p hp}
      let B : Set (closedBall (0 : ℝ × ℝ) 1) := {z | z.val.1= -1 ∨ z.val.2=1 ∨ z.val.2= -1}
      have hAB : H '' A=B := by
        ext z
        constructor
        · rintro ⟨v,⟨p,hp,⟨i,hi,hsec⟩,rfl⟩,rfl⟩
          have hh : H (diskBoundaryPoint p hp) ∈ H ''
              {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                closedArcSector i p ∧ v=diskBoundaryPoint p hp} :=
            ⟨_,⟨p,hp,hsec,rfl⟩,rfl⟩
          rw [hImages] at hh
          fin_cases i
          · exact False.elim (hi rfl)
          · norm_num at hh;exact Or.inr (Or.inl hh.1)
          · norm_num at hh;exact Or.inr (Or.inl hh.1)
          · norm_num at hh;exact Or.inl hh
          · norm_num at hh;exact Or.inr (Or.inr hh.1)
          · norm_num at hh;exact Or.inr (Or.inr hh.1)
        · intro hz
          have recover (i : Fin 6) (hi : i≠0)
              (hz : z ∈ H '' {v : StandardDisk | ∃ p : Sphere, ∃ hp : height p=0,
                closedArcSector i p ∧ v=diskBoundaryPoint p hp}) : z ∈ H '' A := by
            obtain ⟨v,⟨p,hp,hsec,rfl⟩,he⟩ := hz
            exact ⟨_,⟨p,hp,⟨i,hi,hsec⟩,rfl⟩,he⟩
          rcases hz with hx|hy|hy
          · apply recover 3 (by decide)
            rw [hImages];exact hx
          · rcases le_or_gt 0 z.val.1 with hx|hx
            · apply recover 1 (by decide)
              rw [hImages];exact ⟨hy,hx⟩
            · apply recover 2 (by decide)
              rw [hImages];exact ⟨hy,hx.le⟩
          · rcases le_or_gt z.val.1 0 with hx|hx
            · apply recover 4 (by decide)
              rw [hImages];exact ⟨hy,hx⟩
            · apply recover 5 (by decide)
              rw [hImages];exact ⟨hy,hx.le⟩
      have hBA : H.symm '' B=A := by
        rw [←hAB]
        ext v
        constructor
        · rintro ⟨w,⟨u,hu,rfl⟩,rfl⟩
          simpa only [H.symm_apply_apply] using hu
        · intro hv
          exact ⟨H v,⟨v,hv,rfl⟩,H.symm_apply_apply v⟩
      refine ⟨f,(f.continuous.isClosedEmbedding ((northDiskFace_injective true).comp (H.symm.injective.comp hqei))).isEmbedding,?_,?_⟩
      · intro t
        exact ⟨H.symm (qe t),rfl,congrArg Subtype.val (H.apply_symm_apply (qe t))⟩
      · change f '' {t | 0≤t.val ∧ t.val≤3}=northDiskFace true '' A
        rw [←hBA]
        exact hfim
  obtain ⟨f,hf,hpins,hcore⟩ := endpoint
  let a : C(unitInterval,Icc (-1/4:ℝ) (13/4)) :=
    ⟨fun u => ⟨-1/4+(7/2)*u.val,⟨by linarith [u.property.1],by linarith [u.property.2]⟩⟩,
      by fun_prop⟩
  have hai : Function.Injective a := by
    intro u v he
    have hh := congrArg Subtype.val he
    apply Subtype.ext
    change -1/4+(7/2)*u.val= -1/4+(7/2)*v.val at hh
    linarith
  let f' : C(unitInterval,Total) := f.comp a
  have hf' : IsEmbedding f' :=
    (f'.continuous.isClosedEmbedding (hf.injective.comp hai)).isEmbedding
  obtain ⟨B,hB,hcenter,hBU⟩ := CurveComplex.source_whole_embedded_arc_strip
    f' hf' Set.univ isOpen_univ (Set.subset_univ _)
  let T (y : ℝ) := (y+1)/4+(5/4)*min 2 (max 0 (y+1))
  have hTc : Continuous T := by dsimp [T];fun_prop
  have hTi : StrictMono T := by
    intro y z hyz
    have hm : min (2:ℝ) (max 0 (y+1)) ≤ min 2 (max 0 (z+1)) :=
      min_le_min le_rfl (max_le_max le_rfl (by linarith))
    dsimp [T];linarith
  have hTm : T (-2)=(-1/4:ℝ) := by norm_num [T]
  have hTp : T 2=(13/4:ℝ) := by norm_num [T]
  have hTrange : T '' Icc (-2:ℝ) 2=Icc (-1/4:ℝ) (13/4) := by
    rw [hTc.image_Icc_of_strictMono hTi,hTm,hTp]
  have hTcore (y : ℝ) (hy : -1≤y ∧ y≤1) : T y=(3/2)*(y+1) := by
    dsimp [T]
    rw [max_eq_right (by linarith : 0≤y+1),min_eq_right (by linarith : y+1≤2)]
    ring
  let J := Icc (-2:ℝ) 2
  have hTbound (y : J) : -1/4≤T y.val ∧ T y.val≤13/4 := by
    constructor
    · rw [←hTm];exact hTi.monotone y.property.1
    · rw [←hTp];exact hTi.monotone y.property.2
  let ψ : C(J,unitInterval) :=
    ⟨fun y => ⟨(T y.val+1/4)/(7/2),⟨by linarith [(hTbound y).1],by linarith [(hTbound y).2]⟩⟩,
      by dsimp [T];fun_prop⟩
  have hψi : Function.Injective ψ := by
    intro y z he
    have hh := congrArg Subtype.val he
    have hT : T y.val=T z.val := by
      change (T y.val+1/4)/(7/2)=(T z.val+1/4)/(7/2) at hh
      linarith
    exact Subtype.ext (hTi.injective hT)
  have hψs : Function.Surjective ψ := by
    intro u
    have ht : -1/4+(7/2)*u.val ∈ Icc (-1/4:ℝ) (13/4) :=
      ⟨by linarith [u.property.1],by linarith [u.property.2]⟩
    rw [←hTrange] at ht
    obtain ⟨y,hy,he⟩ := ht
    refine ⟨⟨y,hy⟩,?_⟩
    apply Subtype.ext
    change (T y+1/4)/(7/2)=u.val
    rw [he];ring
  let w : C(J,Set.Icc (-1:ℝ) 1) :=
    ⟨fun x => ⟨x.val/2,⟨by linarith [x.property.1],by linarith [x.property.2]⟩⟩,
      by fun_prop⟩
  have hwi : Function.Injective w := by
    intro x y he
    have hh := congrArg Subtype.val he
    apply Subtype.ext
    change x.val/2=y.val/2 at hh;linarith
  have hws : Function.Surjective w := by
    intro u
    refine ⟨⟨2*u.val,⟨by linarith [u.property.1],by linarith [u.property.2]⟩⟩,?_⟩
    apply Subtype.ext;change (2*u.val)/2=u.val;ring
  let k : C(J × J,unitInterval × Set.Icc (-1:ℝ) 1) :=
    ⟨fun v => (ψ v.2,w v.1),(ψ.continuous.comp continuous_snd).prodMk (w.continuous.comp continuous_fst)⟩
  have hki : Function.Injective k := by
    intro v u he
    exact Prod.ext (hwi (congrArg Prod.snd he)) (hψi (congrArg Prod.fst he))
  have hks : Function.Surjective k := by
    intro z
    obtain ⟨y,hy⟩ := hψs z.1
    obtain ⟨x,hx⟩ := hws z.2
    exact ⟨(x,y),Prod.ext hy hx⟩
  let E : C(J × J,Total) := ⟨B ∘ k,hB.continuous.comp k.continuous⟩
  have hEi : IsEmbedding E := (E.continuous.isClosedEmbedding (hB.injective.comp hki)).isEmbedding
  have hEr : Set.range E=Set.range B := by
    ext z
    constructor
    · rintro ⟨v,rfl⟩;exact ⟨k v,rfl⟩
    · rintro ⟨u,rfl⟩
      obtain ⟨v,hv⟩ := hks u
      exact ⟨v,congrArg B hv⟩
  have haxis (y : J) : E (⟨0,by norm_num [J]⟩,y)=f (a (ψ y)) := by
    change B (ψ y,w ⟨0,by norm_num [J]⟩)=_
    have hw0 : w ⟨0,by norm_num [J]⟩=⟨0,by norm_num [J]⟩ := Subtype.ext (by norm_num [w])
    rw [hw0,hcenter]
    rfl
  have haψ (y : J) : (a (ψ y)).val=T y.val := by
    change -1/4+(7/2)*((T y.val+1/4)/(7/2))=T y.val
    ring
  refine ⟨E,hEi,?_,?_⟩
  · rw [←hcore]
    ext z
    constructor
    · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
      have hx0 : x=⟨0,by norm_num [J]⟩ := Subtype.ext hx
      rw [hx0,haxis]
      refine ⟨a (ψ y),?_,rfl⟩
      change 0≤(a (ψ y)).val ∧ (a (ψ y)).val≤3
      rw [haψ,hTcore y.val (abs_le.mp hy)]
      constructor <;> linarith [abs_le.mp hy |>.1,abs_le.mp hy |>.2]
    · rintro ⟨t,⟨hl,hr⟩,rfl⟩
      let y : J := ⟨(2/3)*t.val-1,⟨by linarith,by linarith⟩⟩
      have hy : |y.val|≤1 := abs_le.mpr ⟨by dsimp [y];linarith,by dsimp [y];linarith⟩
      refine ⟨(⟨0,by norm_num [J]⟩,y),⟨rfl,hy⟩,?_⟩
      rw [haxis]
      apply congrArg f
      apply Subtype.ext
      rw [haψ,hTcore y.val (abs_le.mp hy)]
      dsimp [y];ring
  · intro v hv
    rw [hEr]
    apply CurveComplex.embedded_band_open_rectangle_interior B hB (ψ v.2) (w v.1)
    · have hh := hTi (abs_lt.mp hv.2).1
      rw [hTm] at hh
      change 0<(T v.2.val+1/4)/(7/2);linarith
    · have hh := hTi (abs_lt.mp hv.2).2
      rw [hTp] at hh
      change (T v.2.val+1/4)/(7/2)<1;linarith
    · change -1<v.1.val/2;linarith [abs_lt.mp hv.1 |>.1]
    · change v.1.val/2<1;linarith [abs_lt.mp hv.1 |>.2]
end AlternatingSphereCover
