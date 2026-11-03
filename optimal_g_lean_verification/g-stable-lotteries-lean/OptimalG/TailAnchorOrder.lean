import OptimalG.TailReanchor

/-! Monotonicity removes the anchor-height coordinate from direct tail
residuals. The remaining anchor-score dependence is affine. -/
namespace OptimalG
open Set

theorem tailScore_antitone_anchor_height {a Ylo Yhi H r : ℝ}
    (ha : a<1) (hr : r∈Icc a 1) (hY : Ylo≤Yhi) :
    tailScore a Yhi H r≤tailScore a Ylo H r := by
  have hd : 0<1-a := sub_pos.mpr ha
  have ht : tailCoord a r∈Icc (0:ℝ) 1 := by
    unfold tailCoord
    exact ⟨div_nonneg (sub_nonneg.mpr hr.1) hd.le,
      (div_le_one hd).mpr (by linarith only [hr.2])⟩
  have hid : (1-a)*(tailScore a Ylo H r-tailScore a Yhi H r)=
      6*(Yhi-Ylo)*tailCoord a r*(1-tailCoord a r) := by
    unfold tailScore tailOne tailTwo
    field_simp [hd.ne']
    ring
  have hh : 0≤(1-a)*(tailScore a Ylo H r-tailScore a Yhi H r) := by
    rw [hid]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (by norm_num : (0:ℝ)≤6) (sub_nonneg.mpr hY)) ht.1)
      (sub_nonneg.mpr ht.2)
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hh hd)

theorem weighted_tail_antitone_anchor_height {a Ylo Yhi H r J D : ℝ}
    (ha : a<1) (hr : r∈Icc a 1) (hY : Ylo≤Yhi) (hJ : 0≤J) (hD : 0≤D) :
    D*tailScore a Yhi H r-J*tailPrimitive a Yhi H r≤
      D*tailScore a Ylo H r-J*tailPrimitive a Ylo H r := by
  have hs := mul_le_mul_of_nonneg_left (tailScore_antitone_anchor_height (H:=H) ha hr hY) hD
  have hp := mul_le_mul_of_nonneg_left (tailPrimitive_mono_anchor (Hlo:=H) (Hhi:=H) ha hr hY le_rfl) hJ
  linarith only [hs,hp]

/-- Both anchor-score endpoints at the lower anchor height cover the full
anchor box. The other terms of the residual are absorbed into C. -/
theorem weighted_tail_nonpos_of_anchor_endpoints {a Ylo Y Hlo Hhi H r C J D : ℝ}
    (ha : a<1) (hr : r∈Icc a 1) (hY : Ylo≤Y) (hH : H∈Icc Hlo Hhi)
    (hJ : 0≤J) (hD : 0≤D)
    (hlo : C+D*tailScore a Ylo Hlo r-J*tailPrimitive a Ylo Hlo r≤0)
    (hhi : C+D*tailScore a Ylo Hhi r-J*tailPrimitive a Ylo Hhi r≤0) :
    C+D*tailScore a Y H r-J*tailPrimitive a Y H r≤0 := by
  have hm := weighted_tail_antitone_anchor_height (H:=H) ha hr hY hJ hD
  suffices hh : C+D*tailScore a Ylo H r-J*tailPrimitive a Ylo H r≤0 by
    linarith only [hh,hm]
  rcases eq_or_lt_of_le (hH.1.trans hH.2) with heq | hlt
  · have he : H=Hlo := by linarith only [hH.1,hH.2,heq]
    simpa only [he] using hlo
  · have hl := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hH.2) hlo
    have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hH.1) hhi
    have hid : (Hhi-Hlo)*(C+D*tailScore a Ylo H r-J*tailPrimitive a Ylo H r)=
        (Hhi-H)*(C+D*tailScore a Ylo Hlo r-J*tailPrimitive a Ylo Hlo r)+
        (H-Hlo)*(C+D*tailScore a Ylo Hhi r-J*tailPrimitive a Ylo Hhi r) := by
      unfold tailScore tailPrimitive tailOne tailTwo
      ring
    have hn : (Hhi-Hlo)*(C+D*tailScore a Ylo H r-J*tailPrimitive a Ylo H r)≤0 := by
      rw [hid]
      exact add_nonpos hl hh
    exact nonpos_of_mul_nonpos_right hn (sub_pos.mpr hlt)

end OptimalG
