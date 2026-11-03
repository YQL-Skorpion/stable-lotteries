import OptimalG.VariationalDiagonalAlgebra

/-! Actual chain-rule derivative of a control along the boundary y=p. -/
namespace OptimalG.Variational
open Set

noncomputable def diagonalValue (lam S z u x A : ℝ) (J psi : ℝ → ℝ) (p : ℝ) : ℝ :=
  Certificates.Control.value (z-lam) (2*lam-x) (2*p-lam) (J p)
    (quadratic lam (1-p)-S) (quadratic lam (z-p)-S-u) A (psi p)

theorem diagonalValue_hasDerivAt {lam S z u x A p slope : ℝ} {J psi : ℝ → ℝ}
    (hJ : HasDerivAt J (psi p) p) (hpsi : HasDerivAt psi slope p)
    (hD : Certificates.Control.det (2*lam-x) (2*p-lam) (J p) (quadratic lam (1-p)-S) ≠ 0) :
    HasDerivAt (diagonalValue lam S z u x A J psi)
      (Certificates.Control.diagonalDerivativeNumerator (z-lam) (2*lam-x) (2*p-lam) (J p)
        (quadratic lam (1-p)-S) (quadratic lam (z-p)-S-u) A (psi p) slope
        (1-p-lam) (z-p-lam) /
        (Certificates.Control.det (2*lam-x) (2*p-lam) (J p) (quadratic lam (1-p)-S))^2) p := by
  let U := z-lam
  let h := 2*lam-x
  let k := 2*p-lam
  let R := J p
  let P := quadratic lam (1-p)-S
  let K := quadratic lam (z-p)-S-u
  let B := psi p
  let Pp := 1-p-lam
  let Kp := z-p-lam
  let M := Certificates.Control.alphaNumerator h k A B
  let D := Certificates.Control.det h k R P
  have hP : HasDerivAt (fun t => quadratic lam (1-t)-S) Pp p := by
    have hh := ((quadratic_hasDerivAt lam (1-p)).comp p ((hasDerivAt_id p).const_sub 1)).sub_const S
    change HasDerivAt (fun t => quadratic lam (1-t)-S) ((lam-(1-p))*(-1)) p at hh
    have he : (lam-(1-p))*(-1) = Pp := by dsimp [Pp]; ring
    rwa [he] at hh
  have hK : HasDerivAt (fun t => quadratic lam (z-t)-S-u) Kp p := by
    have hh := (((quadratic_hasDerivAt lam (z-p)).comp p ((hasDerivAt_id p).const_sub z)).sub_const S).sub_const u
    change HasDerivAt (fun t => quadratic lam (z-t)-S-u) ((lam-(z-p))*(-1)) p at hh
    have he : (lam-(z-p))*(-1) = Kp := by dsimp [Kp]; ring
    rwa [he] at hh
  have hk : HasDerivAt (fun t : ℝ => 2*t-lam) 2 p := by
    convert! ((hasDerivAt_id p).const_mul (2:ℝ)).sub_const lam using 1 <;> simp
  have hM := (hk.mul_const A).add (hpsi.const_mul h)
  have hN := (((hJ.mul_const A).add (hP.mul hpsi)).const_mul U).add (hK.mul hM)
  have hDen := (hJ.const_mul h).sub (hk.mul hP)
  have hder := hN.neg.div hDen hD
  let Nd := U*(B*A+(Pp*B+P*slope))+(Kp*M+K*(2*A+h*slope))
  let N := U*(R*A+P*B)+K*M
  let Dd := h*B-(2*P+k*Pp)
  change HasDerivAt (diagonalValue lam S z u x A J psi) ((-Nd*D-(-N)*Dd)/D^2) p at hder
  have he : (-Nd*D-(-N)*Dd)/D^2 =
      Certificates.Control.diagonalDerivativeNumerator U h k R P K A B slope Pp Kp/D^2 := by
    unfold Certificates.Control.diagonalDerivativeNumerator
    dsimp [Nd,N,Dd,D,M]
    ring
  rw [he] at hder
  exact hder

end OptimalG.Variational
