import OptimalG.Certificates.BivariatePolynomial
import OptimalG.Certificates.TensorBernstein
import Mathlib.Tactic
/-! Exact support-slope upper margin on the complete λ and mass rectangles. -/
namespace OptimalG.Certificates.ThetaUpperData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Set
def phase0 : BivariatePolynomial3 := ⟨[(18208467579 / 8000000000000),(-7523161 / 20000000000000),(-1 / 1600000000000)],[(-12029594423 / 16000000000000),(1275589 / 40000000000000),(273 / 400000000000000)],[(-40607623 / 160000000000),(2989 / 800000000000),(0 / 1)],[(13377 / 800000000),(0 / 1),(0 / 1)]⟩
def phase0Cert : BivariateCertificate3 := ⟨[(18208467579 / 8000000000000),(45517407367 / 20000000000000),(22756822887 / 10000000000000)],[(97221211051 / 48000000000000),(81010365313 / 40000000000000),(607522910507 / 300000000000000)],[(10141356791 / 6000000000000),(67601972217 / 40000000000000),(253480871827 / 150000000000000)],[(4118823687 / 3200000000000),(25739242723 / 20000000000000),(128679187017 / 100000000000000)]⟩
theorem phase0_checked : phase0.check phase0Cert = true := by decide +kernel
theorem phase0_margin {L p : ℝ} (hL : L ∈ Icc (0.562325:ℝ) 0.562330)
    (hp : p ∈ Icc ((1 / 4):ℝ) ((57 / 200):ℝ)) :
    (0.0002:ℝ) ≤ (0.56*L+0.0627)*(L*p-p^2/2-0.023354)+(0.22*(0.285:ℝ)-0.78*p-0.22*L)*(L*(1-p)-(1-p)^2/2-0.023354) := by
  have ht : (L-0.562325)/0.000005 ∈ Icc (0:ℝ) 1 := by
    convert! normalized_coordinate_mem (by norm_num : (0.562325:ℝ)<0.562330) hL using 1 <;> norm_num
  have hu : (p-((1 / 4):ℝ))/((7 / 200):ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> nlinarith [hp.1,hp.2]
  have hh := BivariatePolynomial3.check_sound phase0_checked ht hu
  have he : phase0.eval ((L-0.562325)/0.000005) ((p-((1 / 4):ℝ))/((7 / 200):ℝ)) =
      (0.56*L+0.0627)*(L*p-p^2/2-0.023354)+(0.22*(0.285:ℝ)-0.78*p-0.22*L)*(L*(1-p)-(1-p)^2/2-0.023354)-(0.0002:ℝ) := by
    norm_num [phase0,BivariatePolynomial3.eval,RationalPolynomial.eval] <;> ring
  rw [he] at hh
  linarith
def phase1 : BivariatePolynomial3 := ⟨[(4118823687 / 3200000000000),(-13621283 / 40000000000000),(23 / 400000000000000)],[(-1792751667 / 3200000000000),(1146681 / 8000000000000),(117 / 80000000000000)],[(-4775157 / 6400000000),(351 / 32000000000),(0 / 1)],[(189 / 1600000),(0 / 1),(0 / 1)]⟩
def phase1Cert : BivariateCertificate3 := ⟨[(4118823687 / 3200000000000),(25739242723 / 20000000000000),(128679187017 / 100000000000000)],[(1760619899 / 1600000000000),(44009642401 / 40000000000000),(27502367093 / 25000000000000)],[(2127796409 / 3200000000000),(26592628731 / 40000000000000),(66469505977 / 100000000000000)],[(3956169 / 40000000000),(988111109 / 10000000000000),(1233974979 / 12500000000000)]⟩
theorem phase1_checked : phase1.check phase1Cert = true := by decide +kernel
theorem phase1_margin {L p : ℝ} (hL : L ∈ Icc (0.562325:ℝ) 0.562330)
    (hp : p ∈ Icc ((57 / 200):ℝ) ((9 / 25):ℝ)) :
    (0.0002:ℝ) ≤ (0.56*L+0.0627)*(L*p-p^2/2-0.023354)+(0.22*p-0.78*p-0.22*L)*(L*(1-p)-(1-p)^2/2-0.023354) := by
  have ht : (L-0.562325)/0.000005 ∈ Icc (0:ℝ) 1 := by
    convert! normalized_coordinate_mem (by norm_num : (0.562325:ℝ)<0.562330) hL using 1 <;> norm_num
  have hu : (p-((57 / 200):ℝ))/((3 / 40):ℝ) ∈ Icc (0:ℝ) 1 := by constructor <;> nlinarith [hp.1,hp.2]
  have hh := BivariatePolynomial3.check_sound phase1_checked ht hu
  have he : phase1.eval ((L-0.562325)/0.000005) ((p-((57 / 200):ℝ))/((3 / 40):ℝ)) =
      (0.56*L+0.0627)*(L*p-p^2/2-0.023354)+(0.22*p-0.78*p-0.22*L)*(L*(1-p)-(1-p)^2/2-0.023354)-(0.0002:ℝ) := by
    norm_num [phase1,BivariatePolynomial3.eval,RationalPolynomial.eval] <;> ring
  rw [he] at hh
  linarith
end OptimalG.Certificates.ThetaUpperData
