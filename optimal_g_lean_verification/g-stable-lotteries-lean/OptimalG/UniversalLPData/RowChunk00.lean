import OptimalG.CheckedRowCache
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def checkedRow0 : CheckedRow where
  tag := .slope 60
  terms := [(61, 200), (60, -200)]
  rhs := (25983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow1 : CheckedRow where
  tag := .momentUp 60
  terms := [(262, 200), (261, -200), (60, -1)]
  rhs := (78199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow2 : CheckedRow where
  tag := .momentLow 60
  terms := [(262, -200), (261, 200), (61, 1)]
  rhs := (77699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow3 : CheckedRow where
  tag := .slope 61
  terms := [(62, 200), (61, -200)]
  rhs := (25483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow4 : CheckedRow where
  tag := .momentUp 61
  terms := [(263, 200), (262, -200), (61, -1)]
  rhs := (76699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow5 : CheckedRow where
  tag := .momentLow 61
  terms := [(263, -200), (262, 200), (62, 1)]
  rhs := (76199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow6 : CheckedRow where
  tag := .slope 62
  terms := [(63, 200), (62, -200)]
  rhs := (24983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow7 : CheckedRow where
  tag := .momentUp 62
  terms := [(264, 200), (263, -200), (62, -1)]
  rhs := (75199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow8 : CheckedRow where
  tag := .momentLow 62
  terms := [(264, -200), (263, 200), (63, 1)]
  rhs := (74699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow9 : CheckedRow where
  tag := .slope 63
  terms := [(64, 200), (63, -200)]
  rhs := (24483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow10 : CheckedRow where
  tag := .momentUp 63
  terms := [(265, 200), (264, -200), (63, -1)]
  rhs := (73699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow11 : CheckedRow where
  tag := .momentLow 63
  terms := [(265, -200), (264, 200), (64, 1)]
  rhs := (73199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow12 : CheckedRow where
  tag := .slope 64
  terms := [(65, 200), (64, -200)]
  rhs := (23983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow13 : CheckedRow where
  tag := .momentUp 64
  terms := [(266, 200), (265, -200), (64, -1)]
  rhs := (72199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow14 : CheckedRow where
  tag := .momentLow 64
  terms := [(266, -200), (265, 200), (65, 1)]
  rhs := (71699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow15 : CheckedRow where
  tag := .slope 65
  terms := [(66, 200), (65, -200)]
  rhs := (23483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow16 : CheckedRow where
  tag := .momentUp 65
  terms := [(267, 200), (266, -200), (65, -1)]
  rhs := (70699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow17 : CheckedRow where
  tag := .momentLow 65
  terms := [(267, -200), (266, 200), (66, 1)]
  rhs := (70199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow18 : CheckedRow where
  tag := .slope 66
  terms := [(67, 200), (66, -200)]
  rhs := (22983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow19 : CheckedRow where
  tag := .momentUp 66
  terms := [(268, 200), (267, -200), (66, -1)]
  rhs := (69199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow20 : CheckedRow where
  tag := .momentLow 66
  terms := [(268, -200), (267, 200), (67, 1)]
  rhs := (68699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow21 : CheckedRow where
  tag := .slope 67
  terms := [(68, 200), (67, -200)]
  rhs := (22483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow22 : CheckedRow where
  tag := .momentUp 67
  terms := [(269, 200), (268, -200), (67, -1)]
  rhs := (67699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow23 : CheckedRow where
  tag := .momentLow 67
  terms := [(269, -200), (268, 200), (68, 1)]
  rhs := (67199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow24 : CheckedRow where
  tag := .slope 68
  terms := [(69, 200), (68, -200)]
  rhs := (21983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow25 : CheckedRow where
  tag := .momentUp 68
  terms := [(270, 200), (269, -200), (68, -1)]
  rhs := (66199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow26 : CheckedRow where
  tag := .momentLow 68
  terms := [(270, -200), (269, 200), (69, 1)]
  rhs := (65699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow27 : CheckedRow where
  tag := .slope 69
  terms := [(70, 200), (69, -200)]
  rhs := (21483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow28 : CheckedRow where
  tag := .momentUp 69
  terms := [(271, 200), (270, -200), (69, -1)]
  rhs := (64699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow29 : CheckedRow where
  tag := .momentLow 69
  terms := [(271, -200), (270, 200), (70, 1)]
  rhs := (64199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow30 : CheckedRow where
  tag := .slope 70
  terms := [(71, 200), (70, -200)]
  rhs := (20983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow31 : CheckedRow where
  tag := .momentUp 70
  terms := [(272, 200), (271, -200), (70, -1)]
  rhs := (63199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
end OptimalG.UniversalLP.Data
