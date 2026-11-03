import OptimalG.UniversalDual

/-! Exact row and box encoding of the 200-bin universal certificate. -/
namespace OptimalG.UniversalLP

abbrev Variables := Fin 402
abbrev Terms := List (ℕ × ℚ)

def L : ℚ := 56233 / 100000
def node (i : ℕ) : ℚ := (i : ℚ) / 200
def Q (r : ℚ) : ℚ := L * r - r ^ 2 / 2
def VQ (r : ℚ) : ℚ := L * r ^ 2 / 2 - r ^ 3 / 6
def turn : ℚ := 2 * L - 1

def upper (j : Variables) : ℚ :=
  if j.val = 0 ∨ j.val = 200 ∨ j.val = 201 then 0
  else if j.val ≤ 200 then Q (node j.val) else VQ (node (j.val - 201))

def lower (j : Variables) : ℚ :=
  if j.val ≤ 200 then max 0 (Q (node j.val) - Q 1)
  else let r := node (j.val - 201)
       if turn < r then VQ r - VQ turn - Q 1 * (r - turn) else 0

inductive RowTag where
  | slope (j : ℕ)
  | momentUp (j : ℕ)
  | momentLow (j : ℕ)
  | binary (i j : ℕ)
  | binaryIntegral (i j : ℕ)
  | moving (pi i j k l z0 z1 : ℕ) (x y : ℚ)
  deriving DecidableEq, Repr, Inhabited

def rowTerms : RowTag → Terms
  | .slope j => [(j + 1, 200), (j, -200)]
  | .momentUp j => [(201 + j + 1, 200), (201 + j, -200), (j, -1)]
  | .momentLow j => [(201 + j + 1, -200), (201 + j, 200), (j + 1, 1)]
  | .binary i j =>
    [(200 - i + j, node i), (j, -node i), (i, -(L - node j))]
  | .binaryIntegral i j =>
    [(201 + (200 - i + j + 1), node i * 200),
     (201 + (200 - i + j), -node i * 200),
     (201 + j + 1, -node i * 200), (201 + j, node i * 200),
     (i, -(L - ((j : ℚ) + 1 / 2) / 200))]
  | .moving pi i j k l z0 z1 x y =>
    let r := 1 - node pi
    let U := ((z0 : ℚ) + z1) / 400 - L
    let h := 2 * L - ((i : ℚ) + j) / 400
    let kap := r + ((k : ℚ) + l) / 400 - L
    [(j, (U + kap * y) * 200 / ((j : ℚ) - i)),
     (i, -(U + kap * y) * 200 / ((j : ℚ) - i)),
     (l, (U * x + h * y) * 200 / ((l : ℚ) - k)),
     (k, -(U * x + h * y) * 200 / ((l : ℚ) - k)),
     (z1, (h - kap * x) * 200 / ((z1 : ℚ) - z0)),
     (z0, -(h - kap * x) * 200 / ((z1 : ℚ) - z0))]

def rowRhs : RowTag → ℚ
  | .slope j => L - ((j : ℚ) + 1 / 2) / 200
  | .momentUp j => (L - node j) / 400 - (1 / 200 : ℚ) ^ 2 / 6
  | .momentLow j => (L - node j) / 400 - (1 / 200 : ℚ) ^ 2 / 3
  | _ => 0

def coeff (terms : Terms) (j : Variables) : ℚ :=
  (terms.map (fun t => if t.1 = j.val then t.2 else 0)).sum

def rowCoeff (tag : RowTag) : Variables → ℚ := coeff (rowTerms tag)

def RowHolds (tag : RowTag) (w : Variables → ℝ) : Prop :=
  ∑ j, (rowCoeff tag j : ℝ) * w j ≤ rowRhs tag

end OptimalG.UniversalLP
