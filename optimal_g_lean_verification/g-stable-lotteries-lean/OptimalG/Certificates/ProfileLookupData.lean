import OptimalG.Certificates.ContinuousLayerPolynomials
import OptimalG.Certificates.CubicLookup

/-! Exact lookup and range facts for the 242 checked profile pieces. -/
namespace OptimalG.Certificates
open UpperProfileData
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def profileLookupChecks : Bool := (List.range 242).all fun i =>
  cubicLookupCheck (profilePiece i) pieces && decide
    (leftContact≤(profilePiece i).lo ∧ (profilePiece i).hi≤rightContact)

theorem profile_lookup_checked : profileLookupChecks=true := by decide +kernel

theorem profile_piece_lookup {i : ℕ} (hi : i<242) :
    cubicLookupCheck (profilePiece i) pieces=true ∧
      leftContact≤(profilePiece i).lo ∧ (profilePiece i).hi≤rightContact := by
  have h := List.all_eq_true.mp profile_lookup_checked i (List.mem_range.mpr hi)
  simpa only [Bool.and_eq_true,decide_eq_true_eq] using h

theorem all_hi_le_right : pieces.all (fun p => decide (p.hi≤rightContact))=true := by decide +kernel

end OptimalG.Certificates
