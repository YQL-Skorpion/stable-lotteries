import OptimalG.CheckedRowCache
namespace OptimalG.UniversalLP.Data
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def checkedRow96 : CheckedRow where
  tag := .slope 92
  terms := [(93, 200), (92, -200)]
  rhs := (9983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow97 : CheckedRow where
  tag := .momentUp 92
  terms := [(294, 200), (293, -200), (92, -1)]
  rhs := (30199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow98 : CheckedRow where
  tag := .momentLow 92
  terms := [(294, -200), (293, 200), (93, 1)]
  rhs := (29699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow99 : CheckedRow where
  tag := .slope 93
  terms := [(94, 200), (93, -200)]
  rhs := (9483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow100 : CheckedRow where
  tag := .momentUp 93
  terms := [(295, 200), (294, -200), (93, -1)]
  rhs := (28699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow101 : CheckedRow where
  tag := .momentLow 93
  terms := [(295, -200), (294, 200), (94, 1)]
  rhs := (28199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow102 : CheckedRow where
  tag := .slope 94
  terms := [(95, 200), (94, -200)]
  rhs := (8983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow103 : CheckedRow where
  tag := .momentUp 94
  terms := [(296, 200), (295, -200), (94, -1)]
  rhs := (27199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow104 : CheckedRow where
  tag := .momentLow 94
  terms := [(296, -200), (295, 200), (95, 1)]
  rhs := (26699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow105 : CheckedRow where
  tag := .slope 95
  terms := [(96, 200), (95, -200)]
  rhs := (8483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow106 : CheckedRow where
  tag := .momentUp 95
  terms := [(297, 200), (296, -200), (95, -1)]
  rhs := (25699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow107 : CheckedRow where
  tag := .momentLow 95
  terms := [(297, -200), (296, 200), (96, 1)]
  rhs := (25199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow108 : CheckedRow where
  tag := .slope 96
  terms := [(97, 200), (96, -200)]
  rhs := (7983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow109 : CheckedRow where
  tag := .momentUp 96
  terms := [(298, 200), (297, -200), (96, -1)]
  rhs := (24199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow110 : CheckedRow where
  tag := .momentLow 96
  terms := [(298, -200), (297, 200), (97, 1)]
  rhs := (23699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow111 : CheckedRow where
  tag := .slope 97
  terms := [(98, 200), (97, -200)]
  rhs := (7483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow112 : CheckedRow where
  tag := .momentUp 97
  terms := [(299, 200), (298, -200), (97, -1)]
  rhs := (22699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow113 : CheckedRow where
  tag := .momentLow 97
  terms := [(299, -200), (298, 200), (98, 1)]
  rhs := (22199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow114 : CheckedRow where
  tag := .slope 98
  terms := [(99, 200), (98, -200)]
  rhs := (6983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow115 : CheckedRow where
  tag := .momentUp 98
  terms := [(300, 200), (299, -200), (98, -1)]
  rhs := (21199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow116 : CheckedRow where
  tag := .momentLow 98
  terms := [(300, -200), (299, 200), (99, 1)]
  rhs := (20699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow117 : CheckedRow where
  tag := .slope 99
  terms := [(100, 200), (99, -200)]
  rhs := (6483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow118 : CheckedRow where
  tag := .momentUp 99
  terms := [(301, 200), (300, -200), (99, -1)]
  rhs := (19699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow119 : CheckedRow where
  tag := .momentLow 99
  terms := [(301, -200), (300, 200), (100, 1)]
  rhs := (19199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow120 : CheckedRow where
  tag := .slope 100
  terms := [(101, 200), (100, -200)]
  rhs := (5983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow121 : CheckedRow where
  tag := .momentUp 100
  terms := [(302, 200), (301, -200), (100, -1)]
  rhs := (18199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow122 : CheckedRow where
  tag := .momentLow 100
  terms := [(302, -200), (301, 200), (101, 1)]
  rhs := (17699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow123 : CheckedRow where
  tag := .slope 101
  terms := [(102, 200), (101, -200)]
  rhs := (5483 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow124 : CheckedRow where
  tag := .momentUp 101
  terms := [(303, 200), (302, -200), (101, -1)]
  rhs := (16699 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow125 : CheckedRow where
  tag := .momentLow 101
  terms := [(303, -200), (302, 200), (102, 1)]
  rhs := (16199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow126 : CheckedRow where
  tag := .slope 102
  terms := [(103, 200), (102, -200)]
  rhs := (4983 / 100000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
def checkedRow127 : CheckedRow where
  tag := .momentUp 102
  terms := [(304, 200), (303, -200), (102, -1)]
  rhs := (15199 / 120000000)
  terms_eq := by decide +kernel
  rhs_eq := by decide +kernel
end OptimalG.UniversalLP.Data
