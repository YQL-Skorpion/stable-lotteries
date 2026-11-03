import OptimalG.Certificates.TransportHessianCleanTaylor
import OptimalG.Certificates.HessianStepIntegral
namespace OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def scale : ℕ := 1208925819614629174706176
def params : Transport.FrozenParameters := ⟨(22493/40000),(27/200),(2303623505254907/100000000000000000)⟩
def start : ℤ := 26563490904813003992945
def finish : ℤ := 32218253759819039417707
def timeStart : ℚ := (7835342428237777/10000000000000000)
def timeFinish : ℚ := (8624179577667147/10000000000000000)
def slabs : List IntegerInterval := [⟨26563490904813003992945,27977181618564512849135⟩,⟨27977181618564512849135,29390872332316021705326⟩,⟨29390872332316021705326,30804563046067530561516⟩,⟨30804563046067530561516,32218253759819039417707⟩]
theorem scale_pos : 0<scale := by decide +kernel
theorem endpoints_ordered : start<finish := by decide +kernel
theorem slabs_checked : integerSlabCoverCheck start finish slabs=true := by decide +kernel
end OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow
