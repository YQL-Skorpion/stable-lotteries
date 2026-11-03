import OptimalG.Certificates.StaticSmallMassCapCertificate

/-! The two strict finite minimizer checks exclude every low head/cap rank
with score above capScore(.28); the minimizer is not assumed to be selected
continuously. -/
namespace OptimalG.Certificates.SmallMassExpressions
open Set

theorem static_cap_minimizer_score {phi : ℝ→ℝ} {p slope x : ℝ}
    (h : VerifierCurve phi (StaticLow.lam:ℝ))
    (hL : (StaticLow.lam:ℝ)∈Icc (22493/40000:ℝ) (56233/100000))
    (hS : (StaticLow.slack:ℝ)∈Icc (227179/10000000:ℝ) (11677/500000))
    (hp : p∈Icc (1/5:ℝ) (527/2000))
    (hhead : ∀ r∈Icc (0:ℝ) (527/2000),phi r=score (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r)
    (haffine : ∀ r∈Icc (0:ℝ) (527/2000),phi r=phi 0+slope*r)
    (hcap : ∀ r∈Icc (527/2000:ℝ) (7/25),phi r=Variational.capScore (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) r)
    (hw : phi (1459/5000)=cap2918 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))
    (hx : x∈Ico (0:ℝ) (StaticLow.lam:ℝ))
    (hmin : supportMinimum phi (StaticLow.lam:ℝ) (smallMassTarget (curvePrimitive phi) (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p)=
      (smallMassTarget (curvePrimitive phi) (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-x)/phi x) :
    phi x≤cap28 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by
  have hD := denominator_pos hL hS (p:=p) ⟨by linarith only [hp.1],hp.2⟩
  have hF : 0 < initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by linarith only [(initial_bounds hL hS).1]
  have hM := cap28_pos hL hS
  have hW := cap2918_pos hL hS
  have ht := StaticSmallMassLinks.CapMinimizerTwo.coefficient_positive hL hS hp hD hF hM hW
  have hz := StaticSmallMassLinks.CapMinimizerHeadZero.coefficient_positive hL hS hp hD hF hM hW
  have hzero : phi 0=initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by
    simpa [score] using hhead 0 ⟨le_rfl,by norm_num⟩
  have hpr : p∈Icc (0:ℝ) (527/2000) := ⟨by linarith only [hp.1],hp.2⟩
  have he := (coefficients_agree (affine_head_agrees h hhead p hpr) (hhead p hpr)).2.2.1
  have htwo : target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-1459/5000≤2*cap2918 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by
    have hh : etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p≤2 := by linarith only [ht]
    exact (div_le_iff₀ hW).mp hh
  have hheadzero : (target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-1459/5000)*initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)<
      target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*cap2918 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) := by
    have hh : etaWitness (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p*initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)<target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p := by
      linarith only [hz]
    change ((target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p-1459/5000)/cap2918 (StaticLow.lam:ℝ) (StaticLow.slack:ℝ))*initial (StaticLow.lam:ℝ) (StaticLow.slack:ℝ)<target (StaticLow.lam:ℝ) (StaticLow.slack:ℝ) p at hh
    rw [div_mul_eq_mul_div] at hh
    exact (div_lt_iff₀ hW).mp hh
  apply h.supportMinimum_minimizer_score_le_cap_of_scalars
    (show (StaticLow.lam:ℝ)∈Icc (1/2:ℝ) (57/100) by constructor <;> linarith only [hL.1,hL.2])
    (show (StaticLow.slack:ℝ)∈Icc (0:ℝ) (3/100) by constructor <;> linarith only [hS.1,hS.2])
    (static_cap_transport_checks h hL hS hp hhead hw).target haffine hcap
    (w:=1459/5000) (by constructor <;> linarith only [hL.1])
    (by simpa only [he,hw] using htwo)
    (by simpa only [he,hw,hzero] using hheadzero) hx hmin

end OptimalG.Certificates.SmallMassExpressions
