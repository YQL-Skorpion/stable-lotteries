import OptimalG.ExtendedSelectedAnalytic

/-! The finite endpoint conditions cover the deficit coordinate and the
triangular cap-shift region without sampling intermediate points. -/
namespace OptimalG
open Set Certificates.ExtendedSelectedExpressions Certificates.ExtendedLocalExpressions

theorem nonpos_of_affine_endpoint_identity {f : ℝ→ℝ} {B e : ℝ}
    (hB : 0<B) (he : e∈Icc (0:ℝ) B)
    (hid : B*f e=(B-e)*f 0+e*f B) (h0 : f 0≤0) (h1 : f B≤0) : f e≤0 := by
  have ha := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr he.2) h0
  have hb := mul_nonpos_of_nonneg_of_nonpos he.1 h1
  have hh : B*f e≤0 := by rw [hid]; exact add_nonpos ha hb
  exact nonpos_of_mul_nonpos_right hh hB

theorem headGainCleared_deficit_nonpos {lam S p t z e : ℝ}
    (he : e∈Icc (0:ℝ) (17/5000))
    (h0 : headGainCleared lam S p t z 0≤0)
    (h1 : headGainCleared lam S p t z (17/5000)≤0) :
    headGainCleared lam S p t z e≤0 := by
  apply nonpos_of_affine_endpoint_identity (by norm_num : (0:ℝ)<17/5000) he _ h0 h1
  unfold headGainCleared localCore
  ring

theorem highRankCore_deficit_nonpos {lam S p t z e q : ℝ}
    (he : e∈Icc (0:ℝ) (17/5000))
    (h0 : highRankCore lam S p t z 0 q≤0)
    (h1 : highRankCore lam S p t z (17/5000) q≤0) :
    highRankCore lam S p t z e q≤0 := by
  apply nonpos_of_affine_endpoint_identity (by norm_num : (0:ℝ)<17/5000) he _ h0 h1
  unfold highRankCore localCore
  ring

theorem capCoreCleared_deficit_nonpos {lam S p t z e q : ℝ}
    (he : e∈Icc (0:ℝ) (17/5000))
    (h0 : capCoreCleared lam S p t z 0 q≤0)
    (h1 : capCoreCleared lam S p t z (17/5000) q≤0) :
    capCoreCleared lam S p t z e q≤0 := by
  apply nonpos_of_affine_endpoint_identity (by norm_num : (0:ℝ)<17/5000) he _ h0 h1
  unfold capCoreCleared headCore localCore
  ring

theorem exists_unit_affine_parameter {a b z : ℝ} (hz : z∈Icc a b) :
    ∃ u∈Icc (0:ℝ) 1,z=a+(b-a)*u := by
  rcases eq_or_lt_of_le (hz.1.trans hz.2) with hab | hab
  · refine ⟨0,by norm_num,?_⟩
    linarith only [hz.1,hz.2,hab]
  · have hd := sub_pos.mpr hab
    refine ⟨(z-a)/(b-a),⟨div_nonneg (sub_nonneg.mpr hz.1) hd.le,
      (div_le_one hd).mpr (by linarith only [hz.2])⟩,?_⟩
    field_simp [(sub_pos.mpr hab).ne']
    ring

end OptimalG
