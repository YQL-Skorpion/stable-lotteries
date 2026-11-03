import OptimalG.VariationalThetaRefinement
import OptimalG.VariationalThetaUpper

/-! Bounds for balanced supporting coefficients do not require the associated
control to attain the high continuation field. -/
namespace OptimalG.Variational
open Set

theorem supporting_weighted_test {lam p R P eta beta theta t s f g : ℝ}
    (hR : 0≤R) (hP : 0≤P) (heta : 0<eta) (heq : eta*theta=1)
    (ht : t+eta*f≤2*lam-beta*P)
    (hs : s+eta*g≤lam-p+beta*R) :
    R*f+P*g≤theta*((2*lam-t)*R+(lam-p-s)*P) := by
  have htheta : 0<theta := pos_of_mul_pos_right (by rw [heq]; norm_num) heta.le
  have ht' := mul_le_mul_of_nonneg_left ht hR
  have hs' := mul_le_mul_of_nonneg_left hs hP
  have hw : eta*(R*f+P*g)≤(2*lam-t)*R+(lam-p-s)*P := by
    nlinarith only [ht',hs']
  have hm := mul_le_mul_of_nonneg_left hw htheta.le
  have hid : theta*(eta*(R*f+P*g))=R*f+P*g := by
    calc
      theta*(eta*(R*f+P*g))=(eta*theta)*(R*f+P*g) := by ring
      _=R*f+P*g := by rw [heq,one_mul]
  rwa [hid] at hm

theorem balanced_eta_bounds {phi : ℝ→ℝ} {lam p eta beta x y : ℝ} {d : LowRankData}
    (hd : Admissible lam d) (hS : d.S≤(0.023354:ℝ))
    (hp : p∈Icc (527/2000:ℝ) (9/25)) (heta : 0<eta)
    (hJ : curvePrimitive phi p=primitive lam d p)
    (hP : curvePrimitive phi (1-p)=quadratic lam (1-p)-d.S)
    (hcap : phi (1459/5000)=capScore lam d.S (1459/5000))
    (hband : (1459/5000:ℝ)≤p → lam-p-11/500≤phi p)
    (hsupport1 : ∀ r∈Icc (57/200:ℝ) (19/50),
      r+eta*phi r≤2*lam-beta*curvePrimitive phi (1-p))
    (hsupport2 : ∀ r∈Icc (max (57/200) p) (19/50),
      r+eta*phi r≤lam-p+beta*curvePrimitive phi p)
    (hv : ((p,x,y),phi x,phi y)∈controlFeatureSupport d)
    (heq : eta*featureTheta lam d ((p,x,y),phi x,phi y)=1) :
    (50/39:ℝ)<eta ∧ eta<1000/691 := by
  have hp' : p∈Icc pLo pHi := by
    constructor <;> norm_num [pLo,pHi] at * <;> linarith only [hp.1,hp.2]
  have hR0 : 0≤primitive lam d p := by linarith only [hd.control_R_lower hp']
  have hP0 : 0≤quadratic lam (1-p)-d.S := (hd.control_P_bounds hp').1
  have ht := hsupport1 (1459/5000) (by constructor <;> norm_num)
  rw [hcap,hP] at ht
  have htheta := hd.theta_gt_691_of_test_bounds hS hp'
    (theta:=featureTheta lam d ((p,x,y),phi x,phi y))
    (by
      intro hpe
      have hs := hsupport2 (1459/5000)
        ⟨max_le (by norm_num) (by linarith only [hpe]),by norm_num⟩
      rw [hcap,hJ] at hs
      convert! supporting_weighted_test hR0 hP0 heta heq ht hs using 1 <;> norm_num)
    (by
      intro hpl
      have hs := hsupport2 p ⟨max_le (by linarith only [hpl]) le_rfl,by linarith only [hp.2]⟩
      rw [hJ] at hs
      have hfloor := mul_le_mul_of_nonneg_left (hband (by linarith only [hpl])) heta.le
      have hs' : p+eta*(lam-p-11/500)≤lam-p+beta*primitive lam d p := by
        linarith only [hs,hfloor]
      convert! supporting_weighted_test hR0 hP0 heta heq ht hs' using 1 <;> norm_num)
  have hupper := hd.featureTheta_lt_78 hS hv
  have hlo := mul_lt_mul_of_pos_left hupper heta
  have hhi := mul_lt_mul_of_pos_left htheta heta
  rw [heq] at hlo hhi
  constructor <;> linarith only [hlo,hhi]

end OptimalG.Variational
