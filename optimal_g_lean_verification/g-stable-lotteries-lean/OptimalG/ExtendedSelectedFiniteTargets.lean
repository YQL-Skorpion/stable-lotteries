import OptimalG.ExtendedSelectedAssembly
import OptimalG.ExtendedSelectedInterpolation

/-! A fixed list of explicit scalar polynomial families suffices for all
selected-high endpoint conditions. This is the semantic interface for the
nineteen generated certificates, before their numerical instantiation. -/
namespace OptimalG
open Set Certificates.ExtendedSelectedExpressions Certificates.ExtendedLocalExpressions
open Certificates.ExtendedScalarExpressions

structure ExtendedSelectedPolynomialSigns (lam S p t : ℝ) : Prop where
  transport : ∀ z∈Icc (391/500:ℝ) (7/8),∀ e∈({0,17/5000}:Set ℝ),localCore lam S p t z e≤0
  early : ∀ e∈({0,17/5000}:Set ℝ),headGainCleared lam S p t (391/500) e≤0
  late : 9/20≤p→∀ e∈({0,17/5000}:Set ℝ),headGainCleared lam S p t (7/8) e≤0
  inactive : p≤9/20→headLinear lam S p t (7/8)≤0
  high : ∀ z∈Icc (391/500:ℝ) (7/8),∀ e∈({0,17/5000}:Set ℝ),
    highRankCore lam S p t z e (527/2000)≤0 ∧ highRankCore lam S p t z e p≤0
  triangle : p∈Icc (211/500:ℝ) (103/200)→∀ u∈Icc (0:ℝ) 1,∀ e∈({0,17/5000}:Set ℝ),
    let z := 391/500+u*(p-211/500)
    capCoreCleared lam S p t z e 0≤0 ∧ capCoreCleared lam S p t z e (9/25-z+p)≤0
  rectangle : 103/200≤p→∀ u∈Icc (0:ℝ) 1,∀ e∈({0,17/5000}:Set ℝ),
    let z := 391/500+(93/1000)*u
    capCoreCleared lam S p t z e 0≤0 ∧ capCoreCleared lam S p t z e (9/25-z+p)≤0

theorem ExtendedSelectedPolynomialSigns.toChecks {lam S p t : ℝ}
    (hn : ExtendedSelectedPolynomialSigns lam S p t)
    (hp : 19/50≤p) (hJ : 0<betaNumerator lam p t)
    (hs : 0<1+Certificates.SmallMassExpressions.slope lam S) :
    ExtendedSelectedChecks lam S p t := by
  have he0 : (0:ℝ)∈({0,17/5000}:Set ℝ) := by simp
  have he1 : (17/5000:ℝ)∈({0,17/5000}:Set ℝ) := by simp
  have hT (z : ℝ) (hz : z∈Icc (391/500:ℝ) (7/8)) (e : ℝ)
      (he : e∈Icc (0:ℝ) (17/5000)) : localCore lam S p t z e≤0 := by
    exact nonpos_of_affine_endpoint_identity (by norm_num) he
      (deficit_affine lam S p t z e) (hn.transport z hz 0 he0) (hn.transport z hz _ he1)
  have hcap (z : ℝ) (hz : z∈Icc (391/500:ℝ) (7/8)) (harg : z-p≤9/25)
      (e : ℝ) (he : e∈({0,17/5000}:Set ℝ)) :
      capCoreCleared lam S p t z e 0≤0 ∧ capCoreCleared lam S p t z e (9/25-z+p)≤0 := by
    by_cases hp515 : p≤103/200
    · have hp422 : 211/500≤p := by linarith only [hz.1,harg]
      obtain ⟨u,hu,hzu⟩ := exists_unit_affine_parameter
        (a:=391/500) (b:=p+9/25) (z:=z) ⟨hz.1,by linarith only [harg]⟩
      have hz' : z=391/500+u*(p-211/500) := by
        calc
          z=391/500+(p+9/25-391/500)*u := hzu
          _=_ := by ring
      simpa only [←hz'] using hn.triangle ⟨hp422,hp515⟩ u hu e he
    · obtain ⟨u,hu,hzu⟩ := exists_unit_affine_parameter hz
      have hz' : z=391/500+(93/1000)*u := by
        calc
          z=391/500+(7/8-391/500)*u := hzu
          _=_ := by ring
      simpa only [←hz'] using hn.rectangle (le_of_not_ge hp515) u hu e he
  constructor
  · intro e he
    apply extended_headGain_of_cleared (by linarith only [hp]) hJ hs
      (hT _ (by norm_num) e he)
    exact headGainCleared_deficit_nonpos he (hn.early 0 he0) (hn.early _ he1)
  · intro e he
    by_cases hp45 : p≤9/20
    · exact extended_headGain_of_inactive (by linarith only [hp])
        (hT _ (by norm_num) e he) (hn.inactive hp45)
    · apply extended_headGain_of_cleared (by linarith only [hp]) hJ hs
        (hT _ (by norm_num) e he)
      exact headGainCleared_deficit_nonpos he
        (hn.late (le_of_not_ge hp45) 0 he0) (hn.late (le_of_not_ge hp45) _ he1)
  · intro z hz e he
    exact ⟨highRankCore_deficit_nonpos he (hn.high z hz 0 he0).1 (hn.high z hz _ he1).1,
      highRankCore_deficit_nonpos he (hn.high z hz 0 he0).2 (hn.high z hz _ he1).2⟩
  · intro z hz e he harg
    have h0 := hcap z hz harg 0 he0
    have h1 := hcap z hz harg (17/5000) he1
    constructor
    · exact capCore_nonpos_of_cleared (by linarith only [harg])
        (capCoreCleared_deficit_nonpos he h0.1 h1.1)
    · exact capCore_nonpos_of_cleared (by linarith)
        (capCoreCleared_deficit_nonpos he h0.2 h1.2)

end OptimalG
