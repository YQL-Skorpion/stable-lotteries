import OptimalG.CheckedRowCache
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def checkedRow64 : CheckedRow where
  tag := .momentUp 81
  terms := [(283, 200), (282, -200), (81, -1)]
  rhs := (46699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow65 : CheckedRow where
  tag := .momentLow 81
  terms := [(283, -200), (282, 200), (82, 1)]
  rhs := (46199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow66 : CheckedRow where
  tag := .slope 82
  terms := [(83, 200), (82, -200)]
  rhs := (14983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow67 : CheckedRow where
  tag := .momentUp 82
  terms := [(284, 200), (283, -200), (82, -1)]
  rhs := (45199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow68 : CheckedRow where
  tag := .momentLow 82
  terms := [(284, -200), (283, 200), (83, 1)]
  rhs := (44699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow69 : CheckedRow where
  tag := .slope 83
  terms := [(84, 200), (83, -200)]
  rhs := (14483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow70 : CheckedRow where
  tag := .momentUp 83
  terms := [(285, 200), (284, -200), (83, -1)]
  rhs := (43699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow71 : CheckedRow where
  tag := .momentLow 83
  terms := [(285, -200), (284, 200), (84, 1)]
  rhs := (43199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow72 : CheckedRow where
  tag := .slope 84
  terms := [(85, 200), (84, -200)]
  rhs := (13983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow73 : CheckedRow where
  tag := .momentUp 84
  terms := [(286, 200), (285, -200), (84, -1)]
  rhs := (42199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow74 : CheckedRow where
  tag := .momentLow 84
  terms := [(286, -200), (285, 200), (85, 1)]
  rhs := (41699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow75 : CheckedRow where
  tag := .slope 85
  terms := [(86, 200), (85, -200)]
  rhs := (13483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow76 : CheckedRow where
  tag := .momentUp 85
  terms := [(287, 200), (286, -200), (85, -1)]
  rhs := (40699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow77 : CheckedRow where
  tag := .momentLow 85
  terms := [(287, -200), (286, 200), (86, 1)]
  rhs := (40199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow78 : CheckedRow where
  tag := .slope 86
  terms := [(87, 200), (86, -200)]
  rhs := (12983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow79 : CheckedRow where
  tag := .momentUp 86
  terms := [(288, 200), (287, -200), (86, -1)]
  rhs := (39199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow80 : CheckedRow where
  tag := .momentLow 86
  terms := [(288, -200), (287, 200), (87, 1)]
  rhs := (38699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow81 : CheckedRow where
  tag := .slope 87
  terms := [(88, 200), (87, -200)]
  rhs := (12483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow82 : CheckedRow where
  tag := .momentUp 87
  terms := [(289, 200), (288, -200), (87, -1)]
  rhs := (37699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow83 : CheckedRow where
  tag := .momentLow 87
  terms := [(289, -200), (288, 200), (88, 1)]
  rhs := (37199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow84 : CheckedRow where
  tag := .slope 88
  terms := [(89, 200), (88, -200)]
  rhs := (11983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow85 : CheckedRow where
  tag := .momentUp 88
  terms := [(290, 200), (289, -200), (88, -1)]
  rhs := (36199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow86 : CheckedRow where
  tag := .momentLow 88
  terms := [(290, -200), (289, 200), (89, 1)]
  rhs := (35699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow87 : CheckedRow where
  tag := .slope 89
  terms := [(90, 200), (89, -200)]
  rhs := (11483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow88 : CheckedRow where
  tag := .momentUp 89
  terms := [(291, 200), (290, -200), (89, -1)]
  rhs := (34699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow89 : CheckedRow where
  tag := .momentLow 89
  terms := [(291, -200), (290, 200), (90, 1)]
  rhs := (34199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow90 : CheckedRow where
  tag := .slope 90
  terms := [(91, 200), (90, -200)]
  rhs := (10983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow91 : CheckedRow where
  tag := .momentUp 90
  terms := [(292, 200), (291, -200), (90, -1)]
  rhs := (33199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow92 : CheckedRow where
  tag := .momentLow 90
  terms := [(292, -200), (291, 200), (91, 1)]
  rhs := (32699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow93 : CheckedRow where
  tag := .slope 91
  terms := [(92, 200), (91, -200)]
  rhs := (10483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow94 : CheckedRow where
  tag := .momentUp 91
  terms := [(293, 200), (292, -200), (91, -1)]
  rhs := (31699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow95 : CheckedRow where
  tag := .momentLow 91
  terms := [(293, -200), (292, 200), (92, 1)]
  rhs := (31199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
end OptimalG.UniversalLP.Data
