import OptimalG.CheckedRowCache
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def checkedRow320 : CheckedRow where
  tag := .momentUp 167
  terms := [(369, 200), (368, -200), (167, -1)]
  rhs := (-82301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow321 : CheckedRow where
  tag := .momentLow 167
  terms := [(369, -200), (368, 200), (168, 1)]
  rhs := (-82801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow322 : CheckedRow where
  tag := .momentUp 168
  terms := [(370, 200), (369, -200), (168, -1)]
  rhs := (-83801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow323 : CheckedRow where
  tag := .momentLow 168
  terms := [(370, -200), (369, 200), (169, 1)]
  rhs := (-84301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow324 : CheckedRow where
  tag := .momentUp 169
  terms := [(371, 200), (370, -200), (169, -1)]
  rhs := (-85301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow325 : CheckedRow where
  tag := .momentLow 169
  terms := [(371, -200), (370, 200), (170, 1)]
  rhs := (-85801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow326 : CheckedRow where
  tag := .momentUp 170
  terms := [(372, 200), (371, -200), (170, -1)]
  rhs := (-86801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow327 : CheckedRow where
  tag := .momentLow 170
  terms := [(372, -200), (371, 200), (171, 1)]
  rhs := (-87301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow328 : CheckedRow where
  tag := .momentUp 171
  terms := [(373, 200), (372, -200), (171, -1)]
  rhs := (-88301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow329 : CheckedRow where
  tag := .momentLow 171
  terms := [(373, -200), (372, 200), (172, 1)]
  rhs := (-88801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow330 : CheckedRow where
  tag := .momentUp 172
  terms := [(374, 200), (373, -200), (172, -1)]
  rhs := (-89801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow331 : CheckedRow where
  tag := .momentLow 177
  terms := [(379, -200), (378, 200), (178, 1)]
  rhs := (-97801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow332 : CheckedRow where
  tag := .momentLow 186
  terms := [(388, -200), (387, 200), (187, 1)]
  rhs := (-111301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow333 : CheckedRow where
  tag := .binary 137 0
  terms := [(63, (137 / 200)), (0, (-137 / 200)), (137, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow334 : CheckedRow where
  tag := .binary 138 0
  terms := [(62, (69 / 100)), (0, (-69 / 100)), (138, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow335 : CheckedRow where
  tag := .binary 139 0
  terms := [(61, (139 / 200)), (0, (-139 / 200)), (139, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow336 : CheckedRow where
  tag := .binaryIntegral 139 0
  terms := [(263, 139), (262, -139), (202, -139), (201, 139), (139, (-55983 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow337 : CheckedRow where
  tag := .binary 139 1
  terms := [(62, (139 / 200)), (1, (-139 / 200)), (139, (-55733 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow338 : CheckedRow where
  tag := .binary 140 0
  terms := [(60, (7 / 10)), (0, (-7 / 10)), (140, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow339 : CheckedRow where
  tag := .binary 141 0
  terms := [(59, (141 / 200)), (0, (-141 / 200)), (141, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow340 : CheckedRow where
  tag := .binaryIntegral 141 3
  terms := [(264, 141), (263, -141), (205, -141), (204, 141), (141, (-54483 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow341 : CheckedRow where
  tag := .binary 142 0
  terms := [(58, (71 / 100)), (0, (-71 / 100)), (142, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow342 : CheckedRow where
  tag := .binary 143 0
  terms := [(57, (143 / 200)), (0, (-143 / 200)), (143, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow343 : CheckedRow where
  tag := .binary 144 0
  terms := [(56, (18 / 25)), (0, (-18 / 25)), (144, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow344 : CheckedRow where
  tag := .binaryIntegral 144 8
  terms := [(266, 144), (265, -144), (210, -144), (209, 144), (144, (-51983 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow345 : CheckedRow where
  tag := .binary 145 0
  terms := [(55, (29 / 40)), (0, (-29 / 40)), (145, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow346 : CheckedRow where
  tag := .binaryIntegral 145 10
  terms := [(267, 145), (266, -145), (212, -145), (211, 145), (145, (-50983 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow347 : CheckedRow where
  tag := .binary 146 0
  terms := [(54, (73 / 100)), (0, (-73 / 100)), (146, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow348 : CheckedRow where
  tag := .binaryIntegral 146 9
  terms := [(265, 146), (264, -146), (211, -146), (210, 146), (146, (-51483 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow349 : CheckedRow where
  tag := .binary 147 0
  terms := [(53, (147 / 200)), (0, (-147 / 200)), (147, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow350 : CheckedRow where
  tag := .binary 147 14
  terms := [(67, (147 / 200)), (14, (-147 / 200)), (147, (-49233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow351 : CheckedRow where
  tag := .binary 148 0
  terms := [(52, (37 / 50)), (0, (-37 / 50)), (148, (-56233 / 100000))]
  rhs := 0
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
end OptimalG.UniversalLP.Data
