import OptimalG.CheckedRowCache
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def checkedRow160 : CheckedRow where
  tag := .momentUp 113
  terms := [(315, 200), (314, -200), (113, -1)]
  rhs := (-1301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow161 : CheckedRow where
  tag := .momentLow 113
  terms := [(315, -200), (314, 200), (114, 1)]
  rhs := (-1801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow162 : CheckedRow where
  tag := .slope 114
  terms := [(115, 200), (114, -200)]
  rhs := (-1017 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow163 : CheckedRow where
  tag := .momentUp 114
  terms := [(316, 200), (315, -200), (114, -1)]
  rhs := (-2801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow164 : CheckedRow where
  tag := .momentLow 114
  terms := [(316, -200), (315, 200), (115, 1)]
  rhs := (-3301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow165 : CheckedRow where
  tag := .slope 115
  terms := [(116, 200), (115, -200)]
  rhs := (-1517 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow166 : CheckedRow where
  tag := .momentUp 115
  terms := [(317, 200), (316, -200), (115, -1)]
  rhs := (-4301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow167 : CheckedRow where
  tag := .momentLow 115
  terms := [(317, -200), (316, 200), (116, 1)]
  rhs := (-4801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow168 : CheckedRow where
  tag := .slope 116
  terms := [(117, 200), (116, -200)]
  rhs := (-2017 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow169 : CheckedRow where
  tag := .momentUp 116
  terms := [(318, 200), (317, -200), (116, -1)]
  rhs := (-5801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow170 : CheckedRow where
  tag := .momentLow 116
  terms := [(318, -200), (317, 200), (117, 1)]
  rhs := (-6301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow171 : CheckedRow where
  tag := .slope 117
  terms := [(118, 200), (117, -200)]
  rhs := (-2517 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow172 : CheckedRow where
  tag := .momentUp 117
  terms := [(319, 200), (318, -200), (117, -1)]
  rhs := (-7301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow173 : CheckedRow where
  tag := .momentLow 117
  terms := [(319, -200), (318, 200), (118, 1)]
  rhs := (-7801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow174 : CheckedRow where
  tag := .momentUp 118
  terms := [(320, 200), (319, -200), (118, -1)]
  rhs := (-8801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow175 : CheckedRow where
  tag := .momentLow 118
  terms := [(320, -200), (319, 200), (119, 1)]
  rhs := (-9301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow176 : CheckedRow where
  tag := .slope 119
  terms := [(120, 200), (119, -200)]
  rhs := (-3517 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow177 : CheckedRow where
  tag := .momentUp 119
  terms := [(321, 200), (320, -200), (119, -1)]
  rhs := (-10301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow178 : CheckedRow where
  tag := .momentLow 119
  terms := [(321, -200), (320, 200), (120, 1)]
  rhs := (-10801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow179 : CheckedRow where
  tag := .slope 120
  terms := [(121, 200), (120, -200)]
  rhs := (-4017 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow180 : CheckedRow where
  tag := .momentUp 120
  terms := [(322, 200), (321, -200), (120, -1)]
  rhs := (-11801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow181 : CheckedRow where
  tag := .momentLow 120
  terms := [(322, -200), (321, 200), (121, 1)]
  rhs := (-12301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow182 : CheckedRow where
  tag := .slope 121
  terms := [(122, 200), (121, -200)]
  rhs := (-4517 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow183 : CheckedRow where
  tag := .momentUp 121
  terms := [(323, 200), (322, -200), (121, -1)]
  rhs := (-13301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow184 : CheckedRow where
  tag := .momentLow 121
  terms := [(323, -200), (322, 200), (122, 1)]
  rhs := (-13801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow185 : CheckedRow where
  tag := .slope 122
  terms := [(123, 200), (122, -200)]
  rhs := (-5017 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow186 : CheckedRow where
  tag := .momentUp 122
  terms := [(324, 200), (323, -200), (122, -1)]
  rhs := (-14801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow187 : CheckedRow where
  tag := .momentLow 122
  terms := [(324, -200), (323, 200), (123, 1)]
  rhs := (-15301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow188 : CheckedRow where
  tag := .slope 123
  terms := [(124, 200), (123, -200)]
  rhs := (-5517 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow189 : CheckedRow where
  tag := .momentUp 123
  terms := [(325, 200), (324, -200), (123, -1)]
  rhs := (-16301 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow190 : CheckedRow where
  tag := .momentLow 123
  terms := [(325, -200), (324, 200), (124, 1)]
  rhs := (-16801 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow191 : CheckedRow where
  tag := .slope 124
  terms := [(125, 200), (124, -200)]
  rhs := (-6017 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
end OptimalG.UniversalLP.Data
