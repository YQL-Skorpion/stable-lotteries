import OptimalG.Certificates.UpperSupport

/-! Exact rational evaluation of the checked score and primitive. -/
namespace OptimalG.Certificates

 def cubicScoreQ (L : ℚ) : List CubicPiece → ℚ → ℚ
  | [], r => L-r
  | p::ps, r => if r≤p.hi then p.scoreQ (r-p.lo) else cubicScoreQ L ps r

def cubicPrimitiveQ (L S : ℚ) : List CubicPiece → ℚ → ℚ
  | [], r => L*r-r^2/2-S
  | p::ps, r => if r≤p.hi then p.primitiveQ (r-p.lo) else cubicPrimitiveQ L S ps r

def cubicSlopeQ : List CubicPiece → ℚ → ℚ
  | [], _ => -1
  | p::ps, r => if r≤p.hi then p.slopeQ (r-p.lo) else cubicSlopeQ ps r

@[simp] theorem cubicScoreQ_cast (L r : ℚ) (ps : List CubicPiece) :
    (cubicScoreQ L ps r:ℝ)=cubicScore L ps r := by
  induction ps with
  | nil => simp [cubicScoreQ,cubicScore]
  | cons p ps ih =>
    by_cases h : r≤p.hi
    · have h' : (r:ℝ)≤p.hi := by exact_mod_cast h
      simp [cubicScoreQ,cubicScore,h,h']
    · have h' : ¬(r:ℝ)≤p.hi := by exact_mod_cast h
      simp [cubicScoreQ,cubicScore,h,h',ih]

@[simp] theorem cubicPrimitiveQ_cast (L S r : ℚ) (ps : List CubicPiece) :
    (cubicPrimitiveQ L S ps r:ℝ)=cubicPrimitive L S ps r := by
  induction ps with
  | nil => simp [cubicPrimitiveQ,cubicPrimitive]
  | cons p ps ih =>
    by_cases h : r≤p.hi
    · have h' : (r:ℝ)≤p.hi := by exact_mod_cast h
      simp [cubicPrimitiveQ,cubicPrimitive,h,h']
    · have h' : ¬(r:ℝ)≤p.hi := by exact_mod_cast h
      simp [cubicPrimitiveQ,cubicPrimitive,h,h',ih]

@[simp] theorem cubicSlopeQ_cast (r : ℚ) (ps : List CubicPiece) :
    (cubicSlopeQ ps r:ℝ)=cubicSlope ps r := by
  induction ps with
  | nil => simp [cubicSlopeQ,cubicSlope]
  | cons p ps ih =>
    by_cases h : r≤p.hi
    · have h' : (r:ℝ)≤p.hi := by exact_mod_cast h
      simp [cubicSlopeQ,cubicSlope,h,h']
    · have h' : ¬(r:ℝ)≤p.hi := by exact_mod_cast h
      simp [cubicSlopeQ,cubicSlope,h,h',ih]

namespace UpperTrial
open UpperProfileData

def scoreQ (r : ℚ) : ℚ :=
  if r≤leftContact then lam/2-lam*slack/(1-r)^2 else cubicScoreQ lam pieces r

def primitiveQ (r : ℚ) : ℚ :=
  if r≤leftContact then lam^2-lam/2+lam*r/2-lam*slack/(1-r)
  else cubicPrimitiveQ lam slack pieces r

def slopeQ (r : ℚ) : ℚ := cubicSlopeQ pieces r

@[simp] theorem scoreQ_cast (r : ℚ) : (scoreQ r:ℝ)=score r := by
  by_cases h : r≤leftContact
  · have h' : (r:ℝ)≤leftContact := by exact_mod_cast h
    simp [scoreQ,score,capCubicScore,capSlope,h,h']
  · have h' : ¬(r:ℝ)≤leftContact := by exact_mod_cast h
    simp [scoreQ,score,capCubicScore,h,h']

@[simp] theorem primitiveQ_cast (r : ℚ) : (primitiveQ r:ℝ)=primitive r := by
  by_cases h : r≤leftContact
  · have h' : (r:ℝ)≤leftContact := by exact_mod_cast h
    simp [primitiveQ,primitive,capCubicPrimitive,cap,h,h']
  · have h' : ¬(r:ℝ)≤leftContact := by exact_mod_cast h
    simp [primitiveQ,primitive,capCubicPrimitive,h,h']

@[simp] theorem slopeQ_cast (r : ℚ) : (slopeQ r:ℝ)=slope r := by
  simp [slopeQ,slope]

end UpperTrial
end OptimalG.Certificates
