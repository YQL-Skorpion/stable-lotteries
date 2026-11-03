import OptimalG.HighMassGeometry
import OptimalG.VariationalRecovery

/-! Exact reductions for the mixed high-mass test. Every comparison keeps
track of the sign multiplying the actual score deficit and the normalized
coefficient; a smaller beta is used only after proving a nonpositive K term. -/
namespace OptimalG

 theorem mixed_residual_of_deficit_bounds {p q z lam Jp R K K0 t e score : ℝ}
    (hp : 0≤p) (hJ : 0<Jp) (hJR : Jp≤R)
    (hK : K≤K0+t*(lam-z-score)/2)
    (hcoef : (p/Jp)*t/2≤1) (he : e≤lam-z-score)
    (hKtop : K0+t*e/2≤0)
    (hcheck : q-e+(p/R)*(K0+t*e/2)≤0) :
    z+q-lam+(p/Jp)*K+score≤0 := by
  have hbeta : 0≤p/Jp := div_nonneg hp hJ.le
  have hbetas := div_le_div_of_nonneg_left hp hJ hJR
  have hscaled := mul_le_mul_of_nonneg_left hK hbeta
  have hdef := mul_nonneg (sub_nonneg.mpr hcoef) (sub_nonneg.mpr he)
  have hnegative := mul_le_mul_of_nonpos_right hbetas hKtop
  nlinarith only [hscaled,hdef,hnegative,hcheck]

 theorem normalized_mixed_K_nonpos {q e beta K : ℝ}
    (hbeta : 0<beta) (hqe : e≤q) (hcheck : q-e+beta*K≤0) : K≤0 := by
  by_contra hn
  have hh := mul_pos hbeta (lt_of_not_ge hn)
  linarith only [hh,hcheck,hqe]

 theorem mixed_deficit_numerator_identity {lam S p q z du dl t e : ℝ}
    (hR : Variational.quadratic lam p-S≠0) :
    (Variational.quadratic lam p-S)*
      (q-e+(p/(Variational.quadratic lam p-S))*
        (Variational.quadratic lam (z-p+q)-Variational.quadratic lam z-
          Variational.quadratic lam q+S+du-dl+t*e/2))=
      (p-q)*(p*(z-p)-(Variational.quadratic lam p-S))+p*(du-dl)-
        (Variational.quadratic lam p-S-p*t/2)*e := by
  field_simp [hR]
  unfold Variational.quadratic
  ring

/-- The finite polynomial check is divided only by a proved positive
primitive cap; the actual beta comparison is handled separately above. -/
 theorem mixed_deficit_check_of_numerator {lam S p q z du dl t e : ℝ}
    (hR : 0<Variational.quadratic lam p-S)
    (hn : (p-q)*(p*(z-p)-(Variational.quadratic lam p-S))+p*(du-dl)-
      (Variational.quadratic lam p-S-p*t/2)*e≤0) :
    q-e+(p/(Variational.quadratic lam p-S))*
      (Variational.quadratic lam (z-p+q)-Variational.quadratic lam z-
        Variational.quadratic lam q+S+du-dl+t*e/2)≤0 := by
  have he := mixed_deficit_numerator_identity (lam:=lam) (S:=S) (p:=p)
    (q:=q) (z:=z) (du:=du) (dl:=dl) (t:=t) (e:=e) hR.ne'
  rw [←he] at hn
  exact nonpos_of_mul_nonpos_right hn hR

end OptimalG
