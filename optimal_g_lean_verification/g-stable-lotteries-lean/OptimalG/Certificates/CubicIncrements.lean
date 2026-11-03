import OptimalG.Certificates.CubicSupport

/-! Finite score increments of an explicit checked cubic chain. These bounds
use only the polynomial shape and join certificates, with no minimization or
variational regularity premise. -/
namespace OptimalG.Certificates
open Set

theorem cubicAssemblyCheck_increment {L S : ℚ} {p : CubicPiece}
    {ps : List CubicPiece} (hc : cubicAssemblyCheck L S (p::ps)=true)
    {r s : ℝ} (hr : (p.lo:ℝ)≤r) (hrs : r≤s) :
    -(s-r)≤cubicScore L (p::ps) s-cubicScore L (p::ps) r ∧
      cubicScore L (p::ps) s-cubicScore L (p::ps) r≤p.slope 0*(s-r) := by
  have hs : (p.lo:ℝ)≤s := hr.trans hrs
  have hupper := cubicAssemblyCheck_support hc hr hs
  have hlower := cubicAssemblyCheck_support hc hs hr
  have hu := mul_le_mul_of_nonneg_right (cubicAssemblyCheck_slope_bound hc hr).2
    (sub_nonneg.mpr hrs)
  have hl := mul_le_mul_of_nonpos_right (cubicAssemblyCheck_slope_bound hc hs).1
    (sub_nonpos.mpr hrs)
  constructor <;> linarith only [hupper,hlower,hu,hl]

theorem cubicAssemblyCheck_strong_increment {L S : ℚ} {p : CubicPiece}
    {ps : List CubicPiece} {theta : ℝ}
    (hc : cubicAssemblyCheck L S (p::ps)=true) (hp : p.slope 0≤-theta)
    {r s : ℝ} (hr : (p.lo:ℝ)≤r) (hrs : r≤s) :
    -(s-r)≤cubicScore L (p::ps) s-cubicScore L (p::ps) r ∧
      cubicScore L (p::ps) s-cubicScore L (p::ps) r≤-theta*(s-r) := by
  have hh := cubicAssemblyCheck_increment hc hr hrs
  exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_right hp (sub_nonneg.mpr hrs))⟩

end OptimalG.Certificates
