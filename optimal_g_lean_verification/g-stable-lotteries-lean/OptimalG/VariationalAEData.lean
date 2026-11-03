import OptimalG.VariationalContinuation

/-! All variational data and continuations depend only on the almost-everywhere
class of the low score. This justifies selecting regular representatives. -/
namespace OptimalG.Variational
open Set MeasureTheory Filter

theorem lowPrimitive_congr_ae {d e : LowRankData} (lam : ℝ) (hS : d.S=e.S)
    (hphi : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) {r : ℝ} (hr : r ∈ Icc ell tEnd) :
    lowPrimitive lam d r = lowPrimitive lam e r := by
  unfold lowPrimitive
  rw [hS]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_of_ae_restrict_of_subset _ hphi
  rw [uIoc_of_le hr.1]
  exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hr.2)

theorem primitive_congr_ae {d e : LowRankData} (lam : ℝ) (hS : d.S=e.S)
    (hphi : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) (r : ℝ) :
    primitive lam d r = primitive lam e r := by
  unfold primitive
  split_ifs with he ht
  · rw [hS]
  · exact lowPrimitive_congr_ae lam hS hphi ⟨(lt_of_not_ge he).le,ht⟩
  · rw [hS]

theorem Admissible.congr_data {lam : ℝ} {d e : LowRankData} (hd : Admissible lam d)
    (hS : d.S=e.S) (hphi : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) : Admissible lam e := by
  refine ⟨hd.1,by simpa only [← hS] using hd.2.1,(memLp_congr_ae hphi).mp hd.2.2.1,?_,?_,?_⟩
  · filter_upwards [hd.2.2.2.1,hphi] with r hr he
    rwa [← he]
  · rw [← lowPrimitive_congr_ae lam hS hphi (by norm_num [ell,tEnd]),← hS]
    exact hd.2.2.2.2.1
  · intro r hr
    rw [← lowPrimitive_congr_ae lam hS hphi hr,← hS]
    exact hd.2.2.2.2.2 r hr

theorem controlH_congr_ae {d e : LowRankData} (lam z u : ℝ) (hS : d.S=e.S)
    (hphi : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) :
    controlH lam d z u =ᵐ[controlMeasure] controlH lam e z u := by
  filter_upwards [ae_control_lowRanks (fun r => d.phi r=e.phi r) hphi] with c hc
  unfold controlH controlDeterminant
  rw [primitive_congr_ae lam hS hphi c.1,hS,hc.1,hc.2]

theorem vectorField_congr_ae {d e : LowRankData} (lam z u : ℝ) (hS : d.S=e.S)
    (hphi : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) :
    vectorField lam d z u = vectorField lam e z u := by
  unfold vectorField
  rw [essInf_congr_ae (controlH_congr_ae lam z u hS hphi)]

theorem IsContinuation.congr_data {lam : ℝ} {d e : LowRankData} {Y : ℝ → ℝ}
    (hY : IsContinuation lam d Y) (hS : d.S=e.S)
    (hphi : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) : IsContinuation lam e Y := by
  refine ⟨by simpa only [← hS] using hY.1,?_⟩
  intro z hz
  rw [← vectorField_congr_ae lam z (Y z) hS hphi]
  exact hY.2 z hz

theorem Admissible.continuation_congr_ae {lam : ℝ} {d e : LowRankData} (hd : Admissible lam d)
    (hS : d.S=e.S) (hphi : d.phi =ᵐ[volume.restrict (Icc ell tEnd)] e.phi) :
    EqOn (continuation lam d) (continuation lam e) (Icc zStart zEnd) :=
  (hd.congr_data hS hphi).continuation_unique (hd.isContinuation.congr_data hS hphi)
    (hd.congr_data hS hphi).isContinuation

end OptimalG.Variational
