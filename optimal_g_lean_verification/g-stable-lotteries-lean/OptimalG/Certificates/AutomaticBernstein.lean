import OptimalG.Certificates.RationalPolynomial

/-! A computable Bernstein proposal generator. Correctness is still established by
checking the exact reconstructed polynomial, so the proposal formula is outside
the trust boundary of the positivity theorem. -/
namespace OptimalG.Certificates.RationalPolynomial

def proposeBernstein (p : RationalPolynomial) : List ℚ :=
  let n:=p.length-1
  (List.range p.length).map fun k =>
    (List.range (k+1)).foldl
      (fun s j => s+(p[j]?.getD 0)*(Nat.choose k j:ℚ)/(Nat.choose n j:ℚ)) 0

def automaticCheck (p : RationalPolynomial) : Bool := bernsteinCheck p (proposeBernstein p)

theorem automaticCheck_sound {p : RationalPolynomial} (hc : automaticCheck p=true)
    {t : ℝ} (ht : t∈Set.Icc 0 1) : 0≤p.eval t := bernsteinCheck_sound hc ht

end OptimalG.Certificates.RationalPolynomial
