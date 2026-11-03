import OptimalG.UniversalLPData.Rows
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cachedTerms : Array Terms := checkedRows.map (·.terms)
def cachedRhs : Array ℚ := checkedRows.map (·.rhs)
theorem cache_checked : DualProposal.checkRowCache rows cachedTerms cachedRhs = true := checkedRows_cache checkedRows
end OptimalG.UniversalLP.Data
