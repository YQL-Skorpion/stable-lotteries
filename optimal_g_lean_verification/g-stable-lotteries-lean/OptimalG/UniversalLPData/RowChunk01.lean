import OptimalG.CheckedRowCache
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def checkedRow32 : CheckedRow where
  tag := .momentLow 70
  terms := [(272, -200), (271, 200), (71, 1)]
  rhs := (62699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow33 : CheckedRow where
  tag := .slope 71
  terms := [(72, 200), (71, -200)]
  rhs := (20483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow34 : CheckedRow where
  tag := .momentUp 71
  terms := [(273, 200), (272, -200), (71, -1)]
  rhs := (61699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow35 : CheckedRow where
  tag := .momentLow 71
  terms := [(273, -200), (272, 200), (72, 1)]
  rhs := (61199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow36 : CheckedRow where
  tag := .slope 72
  terms := [(73, 200), (72, -200)]
  rhs := (19983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow37 : CheckedRow where
  tag := .momentUp 72
  terms := [(274, 200), (273, -200), (72, -1)]
  rhs := (60199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow38 : CheckedRow where
  tag := .momentLow 72
  terms := [(274, -200), (273, 200), (73, 1)]
  rhs := (59699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow39 : CheckedRow where
  tag := .slope 73
  terms := [(74, 200), (73, -200)]
  rhs := (19483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow40 : CheckedRow where
  tag := .momentUp 73
  terms := [(275, 200), (274, -200), (73, -1)]
  rhs := (58699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow41 : CheckedRow where
  tag := .momentLow 73
  terms := [(275, -200), (274, 200), (74, 1)]
  rhs := (58199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow42 : CheckedRow where
  tag := .slope 74
  terms := [(75, 200), (74, -200)]
  rhs := (18983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow43 : CheckedRow where
  tag := .momentUp 74
  terms := [(276, 200), (275, -200), (74, -1)]
  rhs := (57199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow44 : CheckedRow where
  tag := .momentLow 74
  terms := [(276, -200), (275, 200), (75, 1)]
  rhs := (56699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow45 : CheckedRow where
  tag := .slope 75
  terms := [(76, 200), (75, -200)]
  rhs := (18483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow46 : CheckedRow where
  tag := .momentUp 75
  terms := [(277, 200), (276, -200), (75, -1)]
  rhs := (55699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow47 : CheckedRow where
  tag := .momentLow 75
  terms := [(277, -200), (276, 200), (76, 1)]
  rhs := (55199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow48 : CheckedRow where
  tag := .slope 76
  terms := [(77, 200), (76, -200)]
  rhs := (17983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow49 : CheckedRow where
  tag := .momentUp 76
  terms := [(278, 200), (277, -200), (76, -1)]
  rhs := (54199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow50 : CheckedRow where
  tag := .momentLow 76
  terms := [(278, -200), (277, 200), (77, 1)]
  rhs := (53699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow51 : CheckedRow where
  tag := .slope 77
  terms := [(78, 200), (77, -200)]
  rhs := (17483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow52 : CheckedRow where
  tag := .momentUp 77
  terms := [(279, 200), (278, -200), (77, -1)]
  rhs := (52699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow53 : CheckedRow where
  tag := .momentLow 77
  terms := [(279, -200), (278, 200), (78, 1)]
  rhs := (52199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow54 : CheckedRow where
  tag := .slope 78
  terms := [(79, 200), (78, -200)]
  rhs := (16983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow55 : CheckedRow where
  tag := .momentUp 78
  terms := [(280, 200), (279, -200), (78, -1)]
  rhs := (51199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow56 : CheckedRow where
  tag := .momentLow 78
  terms := [(280, -200), (279, 200), (79, 1)]
  rhs := (50699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow57 : CheckedRow where
  tag := .slope 79
  terms := [(80, 200), (79, -200)]
  rhs := (16483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow58 : CheckedRow where
  tag := .momentUp 79
  terms := [(281, 200), (280, -200), (79, -1)]
  rhs := (49699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow59 : CheckedRow where
  tag := .momentLow 79
  terms := [(281, -200), (280, 200), (80, 1)]
  rhs := (49199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow60 : CheckedRow where
  tag := .slope 80
  terms := [(81, 200), (80, -200)]
  rhs := (15983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow61 : CheckedRow where
  tag := .momentUp 80
  terms := [(282, 200), (281, -200), (80, -1)]
  rhs := (48199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow62 : CheckedRow where
  tag := .momentLow 80
  terms := [(282, -200), (281, 200), (81, 1)]
  rhs := (47699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow63 : CheckedRow where
  tag := .slope 81
  terms := [(82, 200), (81, -200)]
  rhs := (15483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
end OptimalG.UniversalLP.Data
