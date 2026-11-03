import OptimalG.Certificates.StaticLowParameters
import OptimalG.PolynomialCompletion
namespace OptimalG.Certificates.StaticHigh
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def contact : ℚ := (86242083/100000000)
def contactRank : ℚ := (2701077/10000000)
def contactValue : ℚ := (926025781547341956237553359/10505733354677500000000000000)
def contactScore : ℚ := (-4349395049129789235823881549/12280038256362299233000000000)
def departure : ℚ := (476702922192249787929669977/608399077368484033301900000)
def tailSlope : ℚ := (73007649770178841681629084241326593/11621845408858657719542102937460685)
def tailCurvature : ℚ := (369061685386390111204388964516266190000000/31978476904381695527373906043808058998629)
theorem parameter_bounds :
    (0.85:ℚ)<contact ∧ contact<(0.875:ℚ) ∧
    (0.2635:ℚ)<contactRank ∧ contactRank<(0.2764:ℚ) ∧
    (0.782:ℚ)<departure ∧ departure<(0.784:ℚ) ∧
    (6.18:ℚ)≤tailSlope ∧ tailSlope≤6.42 ∧
    (10.77:ℚ)≤tailCurvature ∧ tailCurvature≤12.73 := by decide +kernel
end OptimalG.Certificates.StaticHigh
