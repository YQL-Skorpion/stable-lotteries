import OptimalG.Certificates.TerminalShapePolynomials
import OptimalG.Certificates.NatTensorBernstein5

/-! Exact whole-box Bernstein certificate. All coefficients are natural
numbers; the polynomial identity is checked by Lean. -/
namespace OptimalG.Certificates.TerminalShapeData.Box0SquareLower
open Set TerminalShape
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def certificate : NatTensorBernstein5 := [
  ⟨2044012336800975,0,2,0,1,0,4,0,0,0,0⟩,
  ⟨6065395417895150,0,2,0,1,1,3,0,0,0,0⟩,
  ⟨6011801972559475,0,2,0,1,2,2,0,0,0,0⟩,
  ⟨2002449728292400,0,2,0,1,3,1,0,0,0,0⟩,
  ⟨12035012877100,0,2,0,1,4,0,0,0,0,0⟩,
  ⟨2084475299625875,0,2,1,0,0,4,0,0,0,0⟩,
  ⟨6230260831110750,0,2,1,0,1,3,0,0,0,0⟩,
  ⟨6263546902096875,0,2,1,0,2,2,0,0,0,0⟩,
  ⟨2173195199020000,0,2,1,0,3,1,0,0,0,0⟩,
  ⟨55438004458000,0,2,1,0,4,0,0,0,0,0⟩,
  ⟨4086901131722580,1,1,0,1,0,4,0,0,0,0⟩,
  ⟨12126289329180720,1,1,0,1,1,3,0,0,0,0⟩,
  ⟨12016841339633580,1,1,0,1,2,2,0,0,0,0⟩,
  ⟨4000384593012320,1,1,0,1,3,1,0,0,0,0⟩,
  ⟨22939802936880,1,1,0,1,4,0,0,0,0,0⟩,
  ⟨4167835187493700,1,1,1,0,0,4,0,0,0,0⟩,
  ⟨12456052589587600,1,1,1,0,1,3,0,0,0,0⟩,
  ⟨12520379719907500,1,1,1,0,2,2,0,0,0,0⟩,
  ⟨4341907795424000,1,1,1,0,3,1,0,0,0,0⟩,
  ⟨109753829710400,1,1,1,0,4,0,0,0,0,0⟩,
  ⟨2042888784981676,2,0,0,1,0,4,0,0,0,0⟩,
  ⟨6060893871776264,2,0,0,1,1,3,0,0,0,0⟩,
  ⟨6005039308184316,2,0,0,1,2,2,0,0,0,0⟩,
  ⟨1997934825708544,2,0,0,1,3,1,0,0,0,0⟩,
  ⟨10904780368816,2,0,0,1,4,0,0,0,0,0⟩,
  ⟨2083359877953340,2,0,1,0,0,4,0,0,0,0⟩,
  ⟨6225791719069320,2,0,1,0,1,3,0,0,0,0⟩,
  ⟨6256832759073500,2,0,1,0,2,2,0,0,0,0⟩,
  ⟨2168712557494400,2,0,1,0,3,1,0,0,0,0⟩,
  ⟨54315815586880,2,0,1,0,4,0,0,0,0,0⟩
]

theorem polynomial_identity (a b c : ℝ) : certificate.eval a b c 0 0 = 800000000000000000 * (
    let L := (0.562325:ℝ)+(0.562330-0.562325)*a
    let S := (0.02271790:ℝ)+(0.023354-0.02271790)*b
    let q := (0.2635:ℝ)+(0.272-0.2635)*c
    (contactNumerator L S q-(0.1335:ℝ)^2*denominator q)-0.0000001) := by
  norm_num [certificate,NatTensorBernstein5.eval,NatTensorBernsteinTerm5.eval,
    joinNumerator,tailNumerator,contactNumerator,slackNumerator,deficitNumerator,denominator] <;> ring

theorem positive {L S q : ℝ}
    (hL : L∈Icc (0.562325:ℝ) 0.562330)
    (hS : S∈Icc (0.02271790:ℝ) 0.023354)
    (hq : q∈Icc (0.2635:ℝ) 0.272) : 0<(contactNumerator L S q-(0.1335:ℝ)^2*denominator q) := by
  have ha := normalized_coordinate_mem (by norm_num : (0.562325:ℝ)<0.562330) hL
  have hb := normalized_coordinate_mem (by norm_num : (0.02271790:ℝ)<0.023354) hS
  have hc := normalized_coordinate_mem (by norm_num : (0.2635:ℝ)<0.272) hq
  have hh := certificate.eval_nonneg ha hb hc
    (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
    (show (0:ℝ)∈Icc 0 1 by constructor <;> norm_num)
  rw [polynomial_identity] at hh
  dsimp only at hh
  have hLi : (0.562325:ℝ)+(0.562330-0.562325)*((L-0.562325)/(0.562330-0.562325))=L := by ring
  have hSi : (0.02271790:ℝ)+(0.023354-0.02271790)*((S-0.02271790)/(0.023354-0.02271790))=S := by ring
  have hqi : (0.2635:ℝ)+(0.272-0.2635)*((q-0.2635)/(0.272-0.2635))=q := by ring
  rw [hLi,hSi,hqi] at hh
  linarith only [hh]

end OptimalG.Certificates.TerminalShapeData.Box0SquareLower
