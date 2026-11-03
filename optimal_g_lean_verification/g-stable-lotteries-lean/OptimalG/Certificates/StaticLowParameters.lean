import OptimalG.Certificates.UpperProfileData

/-! Exact retargeting constants for the static upper certificate. The old
central score is scaled and tilted; the two endpoint values and central area
are preserved for the new parameter. No new list of 242 cubics is required. -/
namespace OptimalG.Certificates.StaticLow

def lam : ℚ := 56233/100000
def slack : ℚ := 1936100805801358073341014781/84045866837420000000000000000
def leftContact : ℚ := UpperProfileData.leftContact
def rightContact : ℚ := UpperProfileData.rightContact
def width : ℚ := rightContact-leftContact

def capQ (L S r : ℚ) : ℚ := L^2-L/2+L*r/2-L*S/(1-r)
def capScoreQ (L S r : ℚ) : ℚ := L/2-L*S/(1-r)^2
def quadraticQ (L r : ℚ) : ℚ := L*r-r^2/2
def oldStart : ℚ := capScoreQ UpperProfileData.lam UpperProfileData.slack leftContact
def oldEnd : ℚ := UpperProfileData.lam-rightContact
def oldArea : ℚ := quadraticQ UpperProfileData.lam rightContact-UpperProfileData.slack-
  capQ UpperProfileData.lam UpperProfileData.slack leftContact
def newStart : ℚ := capScoreQ lam slack leftContact
def newEnd : ℚ := lam-rightContact
def newArea : ℚ := quadraticQ lam rightContact-slack-capQ lam slack leftContact
def scale : ℚ := (newArea-width*(newStart+newEnd)/2)/
  (oldArea-width*(oldStart+oldEnd)/2)
def offset : ℚ := newStart-scale*oldStart
def tilt : ℚ := (newEnd-scale*oldEnd-offset)/width
def primitiveOffset : ℚ := capQ lam slack leftContact-
  scale*capQ UpperProfileData.lam UpperProfileData.slack leftContact

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem parameter_bounds :
    (0.02271790:ℚ)≤slack ∧ slack≤0.023354 ∧
    (0.2918:ℚ)<leftContact ∧ leftContact<(0.305:ℚ) ∧
    leftContact<rightContact ∧ rightContact<(0.35945:ℚ) := by decide +kernel

theorem retarget_bounds :
    (0:ℚ)<scale ∧ -1≤-scale+tilt ∧ -(7/10:ℚ)*scale+tilt≤-(691/1000:ℚ) := by
  decide +kernel

theorem retarget_endpoints :
    scale*oldStart+offset=newStart ∧
    scale*oldEnd+offset+tilt*width=newEnd ∧
    scale*oldArea+offset*width+tilt*width^2/2=newArea := by decide +kernel

end OptimalG.Certificates.StaticLow
