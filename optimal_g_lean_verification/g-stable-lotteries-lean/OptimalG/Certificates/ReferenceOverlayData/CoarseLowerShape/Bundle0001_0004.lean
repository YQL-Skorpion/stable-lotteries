import OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Parameters
import OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0000
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Bundle0001_0004
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0011
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0012
import OptimalG.Certificates.ReferenceFluxData.CoarseLowerShape.Bundle0001_0004
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0013
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0014
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0005
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0015
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0006
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0016
import OptimalG.Certificates.ReferenceDensityData.CoarseLowerShape.Batch0017

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0001
open Set Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell32 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell32.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell32.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell167_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell19_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell32.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell32.weight⟩
def cell33 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell33.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell33.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell167_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell20_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell33.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell33.weight⟩
def cell34 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell34.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell34.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell167_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell21_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell34.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell34.weight⟩
def cell35 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell35.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell35.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell168_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell21_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell35.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell35.weight⟩
def cell36 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell36.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell36.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell168_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell22_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell36.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell36.weight⟩
def cell37 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell37.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell37.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell168_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell23_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell37.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell37.weight⟩
def cell38 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell38.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell38.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell169_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell23_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell38.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell38.weight⟩
def cell39 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell39.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell39.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell169_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell24_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell39.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell39.weight⟩
def cell40 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell40.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell40.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell169_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell25_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell40.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell40.weight⟩
def cell41 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell41.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell41.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell170_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell25_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell41.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell41.weight⟩
def cell42 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell42.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell42.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell170_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell26_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell42.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell42.weight⟩
def cell43 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell43.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell43.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell170_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell27_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell43.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell43.weight⟩
def cell44 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell44.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell44.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell171_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell27_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell44.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell44.weight⟩
def cell45 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell45.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell45.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell171_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell28_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell45.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell45.weight⟩
def cell46 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell46.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell46.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell171_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell29_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell46.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell46.weight⟩
def cell47 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell47.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell47.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell172_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell29_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell47.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell47.weight⟩
def cell48 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell48.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell48.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0011.cell172_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell30_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell48.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell48.weight⟩
def cell49 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell49.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell49.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell173_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell30_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell49.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell49.weight⟩
def cell50 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell50.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell50.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell173_0,ReferenceDensityData.CoarseLowerShape.Batch0001.cell31_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell50.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell50.weight⟩
def cell51 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell51.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell51.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell173_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell32_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell51.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell51.weight⟩
def cell52 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell52.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell52.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell174_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell32_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell52.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell52.weight⟩
def cell53 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell53.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell53.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell174_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell33_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell53.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell53.weight⟩
def cell54 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell54.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell54.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell174_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell34_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell54.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell54.weight⟩
def cell55 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell55.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell55.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell175_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell34_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell55.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell55.weight⟩
def cell56 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell56.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell56.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell175_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell35_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell56.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell56.weight⟩
def cell57 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell57.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell57.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell175_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell36_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell57.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell57.weight⟩
def cell58 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell58.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell58.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell176_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell36_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell58.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell58.weight⟩
def cell59 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell59.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell59.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell176_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell37_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell59.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell59.weight⟩
def cell60 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell60.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell60.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell176_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell38_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell60.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell60.weight⟩
def cell61 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell61.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell61.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell177_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell38_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell61.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell61.weight⟩
def cell62 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell62.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell62.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell177_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell39_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell62.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell62.weight⟩
def cell63 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0001.cell63.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0001.cell63.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell177_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell40_1],ReferenceFluxData.CoarseLowerShape.Batch0001.cell63.position,ReferenceFluxData.CoarseLowerShape.Batch0001.cell63.weight⟩
def cells : List Transport.ReferenceOverlayCell := [cell32,cell33,cell34,cell35,cell36,cell37,cell38,cell39,cell40,cell41,cell42,cell43,cell44,cell45,cell46,cell47,cell48,cell49,cell50,cell51,cell52,cell53,cell54,cell55,cell56,cell57,cell58,cell59,cell60,cell61,cell62,cell63]
theorem checked : cells.all Transport.ReferenceOverlayCell.check=true := by decide +kernel
theorem positions_linked : cells.map (·.position) = ReferenceFluxData.CoarseLowerShape.Batch0001.cells.map (·.position) := by rfl
theorem weights_linked : cells.map (·.weight) = ReferenceFluxData.CoarseLowerShape.Batch0001.cells.map (·.weight) := by rfl
theorem intervals_linked : cells.map (fun c => (c.lo,c.hi)) = ReferenceFluxData.CoarseLowerShape.Batch0001.cells.map (fun c => (c.interval.lo,c.interval.hi)) := by rfl
theorem actual32_bounds {r : ℝ} (hr : r∈Ioo (cell32.lo:ℝ) cell32.hi) :
    cell32.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell32.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell32.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell32.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell32 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell32.checked_sums hc
  · intro d hd
    have hi := cell32.checked_images hc hd hr
    simp only [cell32,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual167_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual19_1 hi).1
  · intro d hd
    have hi := cell32.checked_images hc hd hr
    simp only [cell32,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual167_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual19_1 hi).2
theorem actual33_bounds {r : ℝ} (hr : r∈Ioo (cell33.lo:ℝ) cell33.hi) :
    cell33.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell33.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell33.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell33.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell33 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell33.checked_sums hc
  · intro d hd
    have hi := cell33.checked_images hc hd hr
    simp only [cell33,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual167_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual20_1 hi).1
  · intro d hd
    have hi := cell33.checked_images hc hd hr
    simp only [cell33,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual167_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual20_1 hi).2
theorem actual34_bounds {r : ℝ} (hr : r∈Ioo (cell34.lo:ℝ) cell34.hi) :
    cell34.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell34.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell34.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell34.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell34 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell34.checked_sums hc
  · intro d hd
    have hi := cell34.checked_images hc hd hr
    simp only [cell34,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual167_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual21_1 hi).1
  · intro d hd
    have hi := cell34.checked_images hc hd hr
    simp only [cell34,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual167_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual21_1 hi).2
theorem actual35_bounds {r : ℝ} (hr : r∈Ioo (cell35.lo:ℝ) cell35.hi) :
    cell35.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell35.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell35.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell35.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell35 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell35.checked_sums hc
  · intro d hd
    have hi := cell35.checked_images hc hd hr
    simp only [cell35,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual168_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual21_1 hi).1
  · intro d hd
    have hi := cell35.checked_images hc hd hr
    simp only [cell35,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual168_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual21_1 hi).2
theorem actual36_bounds {r : ℝ} (hr : r∈Ioo (cell36.lo:ℝ) cell36.hi) :
    cell36.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell36.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell36.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell36.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell36 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell36.checked_sums hc
  · intro d hd
    have hi := cell36.checked_images hc hd hr
    simp only [cell36,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual168_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual22_1 hi).1
  · intro d hd
    have hi := cell36.checked_images hc hd hr
    simp only [cell36,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual168_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual22_1 hi).2
theorem actual37_bounds {r : ℝ} (hr : r∈Ioo (cell37.lo:ℝ) cell37.hi) :
    cell37.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell37.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell37.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell37.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell37 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell37.checked_sums hc
  · intro d hd
    have hi := cell37.checked_images hc hd hr
    simp only [cell37,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual168_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual23_1 hi).1
  · intro d hd
    have hi := cell37.checked_images hc hd hr
    simp only [cell37,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual168_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual23_1 hi).2
theorem actual38_bounds {r : ℝ} (hr : r∈Ioo (cell38.lo:ℝ) cell38.hi) :
    cell38.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell38.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell38.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell38.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell38 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell38.checked_sums hc
  · intro d hd
    have hi := cell38.checked_images hc hd hr
    simp only [cell38,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual169_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual23_1 hi).1
  · intro d hd
    have hi := cell38.checked_images hc hd hr
    simp only [cell38,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual169_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual23_1 hi).2
theorem actual39_bounds {r : ℝ} (hr : r∈Ioo (cell39.lo:ℝ) cell39.hi) :
    cell39.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell39.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell39.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell39.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell39 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell39.checked_sums hc
  · intro d hd
    have hi := cell39.checked_images hc hd hr
    simp only [cell39,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual169_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual24_1 hi).1
  · intro d hd
    have hi := cell39.checked_images hc hd hr
    simp only [cell39,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual169_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual24_1 hi).2
theorem actual40_bounds {r : ℝ} (hr : r∈Ioo (cell40.lo:ℝ) cell40.hi) :
    cell40.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell40.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell40.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell40.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell40 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell40.checked_sums hc
  · intro d hd
    have hi := cell40.checked_images hc hd hr
    simp only [cell40,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual169_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual25_1 hi).1
  · intro d hd
    have hi := cell40.checked_images hc hd hr
    simp only [cell40,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual169_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual25_1 hi).2
theorem actual41_bounds {r : ℝ} (hr : r∈Ioo (cell41.lo:ℝ) cell41.hi) :
    cell41.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell41.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell41.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell41.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell41 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell41.checked_sums hc
  · intro d hd
    have hi := cell41.checked_images hc hd hr
    simp only [cell41,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual170_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual25_1 hi).1
  · intro d hd
    have hi := cell41.checked_images hc hd hr
    simp only [cell41,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual170_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual25_1 hi).2
theorem actual42_bounds {r : ℝ} (hr : r∈Ioo (cell42.lo:ℝ) cell42.hi) :
    cell42.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell42.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell42.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell42.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell42 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell42.checked_sums hc
  · intro d hd
    have hi := cell42.checked_images hc hd hr
    simp only [cell42,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual170_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual26_1 hi).1
  · intro d hd
    have hi := cell42.checked_images hc hd hr
    simp only [cell42,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual170_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual26_1 hi).2
theorem actual43_bounds {r : ℝ} (hr : r∈Ioo (cell43.lo:ℝ) cell43.hi) :
    cell43.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell43.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell43.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell43.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell43 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell43.checked_sums hc
  · intro d hd
    have hi := cell43.checked_images hc hd hr
    simp only [cell43,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual170_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual27_1 hi).1
  · intro d hd
    have hi := cell43.checked_images hc hd hr
    simp only [cell43,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual170_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual27_1 hi).2
theorem actual44_bounds {r : ℝ} (hr : r∈Ioo (cell44.lo:ℝ) cell44.hi) :
    cell44.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell44.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell44.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell44.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell44 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell44.checked_sums hc
  · intro d hd
    have hi := cell44.checked_images hc hd hr
    simp only [cell44,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual171_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual27_1 hi).1
  · intro d hd
    have hi := cell44.checked_images hc hd hr
    simp only [cell44,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual171_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual27_1 hi).2
theorem actual45_bounds {r : ℝ} (hr : r∈Ioo (cell45.lo:ℝ) cell45.hi) :
    cell45.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell45.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell45.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell45.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell45 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell45.checked_sums hc
  · intro d hd
    have hi := cell45.checked_images hc hd hr
    simp only [cell45,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual171_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual28_1 hi).1
  · intro d hd
    have hi := cell45.checked_images hc hd hr
    simp only [cell45,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual171_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual28_1 hi).2
theorem actual46_bounds {r : ℝ} (hr : r∈Ioo (cell46.lo:ℝ) cell46.hi) :
    cell46.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell46.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell46.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell46.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell46 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell46.checked_sums hc
  · intro d hd
    have hi := cell46.checked_images hc hd hr
    simp only [cell46,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual171_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual29_1 hi).1
  · intro d hd
    have hi := cell46.checked_images hc hd hr
    simp only [cell46,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual171_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual29_1 hi).2
theorem actual47_bounds {r : ℝ} (hr : r∈Ioo (cell47.lo:ℝ) cell47.hi) :
    cell47.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell47.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell47.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell47.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell47 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell47.checked_sums hc
  · intro d hd
    have hi := cell47.checked_images hc hd hr
    simp only [cell47,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual172_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual29_1 hi).1
  · intro d hd
    have hi := cell47.checked_images hc hd hr
    simp only [cell47,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual172_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual29_1 hi).2
theorem actual48_bounds {r : ℝ} (hr : r∈Ioo (cell48.lo:ℝ) cell48.hi) :
    cell48.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell48.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell48.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell48.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell48 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell48.checked_sums hc
  · intro d hd
    have hi := cell48.checked_images hc hd hr
    simp only [cell48,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual172_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual30_1 hi).1
  · intro d hd
    have hi := cell48.checked_images hc hd hr
    simp only [cell48,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0011.actual172_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual30_1 hi).2
theorem actual49_bounds {r : ℝ} (hr : r∈Ioo (cell49.lo:ℝ) cell49.hi) :
    cell49.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell49.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell49.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell49.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell49 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell49.checked_sums hc
  · intro d hd
    have hi := cell49.checked_images hc hd hr
    simp only [cell49,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual173_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual30_1 hi).1
  · intro d hd
    have hi := cell49.checked_images hc hd hr
    simp only [cell49,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual173_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual30_1 hi).2
theorem actual50_bounds {r : ℝ} (hr : r∈Ioo (cell50.lo:ℝ) cell50.hi) :
    cell50.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell50.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell50.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell50.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell50 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell50.checked_sums hc
  · intro d hd
    have hi := cell50.checked_images hc hd hr
    simp only [cell50,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual173_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual31_1 hi).1
  · intro d hd
    have hi := cell50.checked_images hc hd hr
    simp only [cell50,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual173_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0001.actual31_1 hi).2
theorem actual51_bounds {r : ℝ} (hr : r∈Ioo (cell51.lo:ℝ) cell51.hi) :
    cell51.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell51.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell51.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell51.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell51 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell51.checked_sums hc
  · intro d hd
    have hi := cell51.checked_images hc hd hr
    simp only [cell51,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual173_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual32_1 hi).1
  · intro d hd
    have hi := cell51.checked_images hc hd hr
    simp only [cell51,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual173_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual32_1 hi).2
theorem actual52_bounds {r : ℝ} (hr : r∈Ioo (cell52.lo:ℝ) cell52.hi) :
    cell52.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell52.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell52.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell52.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell52 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell52.checked_sums hc
  · intro d hd
    have hi := cell52.checked_images hc hd hr
    simp only [cell52,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual174_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual32_1 hi).1
  · intro d hd
    have hi := cell52.checked_images hc hd hr
    simp only [cell52,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual174_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual32_1 hi).2
theorem actual53_bounds {r : ℝ} (hr : r∈Ioo (cell53.lo:ℝ) cell53.hi) :
    cell53.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell53.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell53.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell53.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell53 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell53.checked_sums hc
  · intro d hd
    have hi := cell53.checked_images hc hd hr
    simp only [cell53,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual174_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual33_1 hi).1
  · intro d hd
    have hi := cell53.checked_images hc hd hr
    simp only [cell53,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual174_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual33_1 hi).2
theorem actual54_bounds {r : ℝ} (hr : r∈Ioo (cell54.lo:ℝ) cell54.hi) :
    cell54.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell54.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell54.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell54.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell54 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell54.checked_sums hc
  · intro d hd
    have hi := cell54.checked_images hc hd hr
    simp only [cell54,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual174_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual34_1 hi).1
  · intro d hd
    have hi := cell54.checked_images hc hd hr
    simp only [cell54,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual174_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual34_1 hi).2
theorem actual55_bounds {r : ℝ} (hr : r∈Ioo (cell55.lo:ℝ) cell55.hi) :
    cell55.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell55.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell55.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell55.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell55 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell55.checked_sums hc
  · intro d hd
    have hi := cell55.checked_images hc hd hr
    simp only [cell55,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual175_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual34_1 hi).1
  · intro d hd
    have hi := cell55.checked_images hc hd hr
    simp only [cell55,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual175_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual34_1 hi).2
theorem actual56_bounds {r : ℝ} (hr : r∈Ioo (cell56.lo:ℝ) cell56.hi) :
    cell56.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell56.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell56.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell56.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell56 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell56.checked_sums hc
  · intro d hd
    have hi := cell56.checked_images hc hd hr
    simp only [cell56,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual175_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual35_1 hi).1
  · intro d hd
    have hi := cell56.checked_images hc hd hr
    simp only [cell56,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual175_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual35_1 hi).2
theorem actual57_bounds {r : ℝ} (hr : r∈Ioo (cell57.lo:ℝ) cell57.hi) :
    cell57.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell57.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell57.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell57.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell57 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell57.checked_sums hc
  · intro d hd
    have hi := cell57.checked_images hc hd hr
    simp only [cell57,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual175_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual36_1 hi).1
  · intro d hd
    have hi := cell57.checked_images hc hd hr
    simp only [cell57,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual175_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual36_1 hi).2
theorem actual58_bounds {r : ℝ} (hr : r∈Ioo (cell58.lo:ℝ) cell58.hi) :
    cell58.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell58.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell58.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell58.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell58 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell58.checked_sums hc
  · intro d hd
    have hi := cell58.checked_images hc hd hr
    simp only [cell58,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual176_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual36_1 hi).1
  · intro d hd
    have hi := cell58.checked_images hc hd hr
    simp only [cell58,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual176_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual36_1 hi).2
theorem actual59_bounds {r : ℝ} (hr : r∈Ioo (cell59.lo:ℝ) cell59.hi) :
    cell59.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell59.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell59.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell59.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell59 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell59.checked_sums hc
  · intro d hd
    have hi := cell59.checked_images hc hd hr
    simp only [cell59,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual176_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual37_1 hi).1
  · intro d hd
    have hi := cell59.checked_images hc hd hr
    simp only [cell59,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual176_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual37_1 hi).2
theorem actual60_bounds {r : ℝ} (hr : r∈Ioo (cell60.lo:ℝ) cell60.hi) :
    cell60.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell60.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell60.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell60.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell60 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell60.checked_sums hc
  · intro d hd
    have hi := cell60.checked_images hc hd hr
    simp only [cell60,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual176_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual38_1 hi).1
  · intro d hd
    have hi := cell60.checked_images hc hd hr
    simp only [cell60,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual176_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual38_1 hi).2
theorem actual61_bounds {r : ℝ} (hr : r∈Ioo (cell61.lo:ℝ) cell61.hi) :
    cell61.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell61.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell61.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell61.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell61 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell61.checked_sums hc
  · intro d hd
    have hi := cell61.checked_images hc hd hr
    simp only [cell61,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual177_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual38_1 hi).1
  · intro d hd
    have hi := cell61.checked_images hc hd hr
    simp only [cell61,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual177_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual38_1 hi).2
theorem actual62_bounds {r : ℝ} (hr : r∈Ioo (cell62.lo:ℝ) cell62.hi) :
    cell62.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell62.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell62.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell62.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell62 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell62.checked_sums hc
  · intro d hd
    have hi := cell62.checked_images hc hd hr
    simp only [cell62,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual177_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual39_1 hi).1
  · intro d hd
    have hi := cell62.checked_images hc hd hr
    simp only [cell62,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual177_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual39_1 hi).2
theorem actual63_bounds {r : ℝ} (hr : r∈Ioo (cell63.lo:ℝ) cell63.hi) :
    cell63.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell63.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell63.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell63.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell63 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell63.checked_sums hc
  · intro d hd
    have hi := cell63.checked_images hc hd hr
    simp only [cell63,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual177_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual40_1 hi).1
  · intro d hd
    have hi := cell63.checked_images hc hd hr
    simp only [cell63,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual177_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual40_1 hi).2
theorem selected32_checked : cell32.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 32=true := by decide +kernel
theorem actual32_full_bounds {r : ℝ} (hr : r∈Ioo (cell32.lo:ℝ) cell32.hi) :
    cell32.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell32.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected32_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 32<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected32_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 32<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell32.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual32_bounds hr).1
  · change cell32.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual32_bounds hr).2
theorem selected33_checked : cell33.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 33=true := by decide +kernel
theorem actual33_full_bounds {r : ℝ} (hr : r∈Ioo (cell33.lo:ℝ) cell33.hi) :
    cell33.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell33.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected33_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 33<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected33_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 33<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell33.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual33_bounds hr).1
  · change cell33.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual33_bounds hr).2
theorem selected34_checked : cell34.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 34=true := by decide +kernel
theorem actual34_full_bounds {r : ℝ} (hr : r∈Ioo (cell34.lo:ℝ) cell34.hi) :
    cell34.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell34.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected34_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 34<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected34_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 34<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell34.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual34_bounds hr).1
  · change cell34.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual34_bounds hr).2
theorem selected35_checked : cell35.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 35=true := by decide +kernel
theorem actual35_full_bounds {r : ℝ} (hr : r∈Ioo (cell35.lo:ℝ) cell35.hi) :
    cell35.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell35.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected35_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 35<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected35_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 35<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell35.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual35_bounds hr).1
  · change cell35.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual35_bounds hr).2
theorem selected36_checked : cell36.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 36=true := by decide +kernel
theorem actual36_full_bounds {r : ℝ} (hr : r∈Ioo (cell36.lo:ℝ) cell36.hi) :
    cell36.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell36.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected36_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 36<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected36_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 36<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell36.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual36_bounds hr).1
  · change cell36.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual36_bounds hr).2
theorem selected37_checked : cell37.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 37=true := by decide +kernel
theorem actual37_full_bounds {r : ℝ} (hr : r∈Ioo (cell37.lo:ℝ) cell37.hi) :
    cell37.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell37.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected37_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 37<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected37_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 37<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell37.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual37_bounds hr).1
  · change cell37.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual37_bounds hr).2
theorem selected38_checked : cell38.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 38=true := by decide +kernel
theorem actual38_full_bounds {r : ℝ} (hr : r∈Ioo (cell38.lo:ℝ) cell38.hi) :
    cell38.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell38.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected38_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 38<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected38_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 38<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell38.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual38_bounds hr).1
  · change cell38.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual38_bounds hr).2
theorem selected39_checked : cell39.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 39=true := by decide +kernel
theorem actual39_full_bounds {r : ℝ} (hr : r∈Ioo (cell39.lo:ℝ) cell39.hi) :
    cell39.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell39.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected39_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 39<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected39_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 39<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell39.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual39_bounds hr).1
  · change cell39.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual39_bounds hr).2
theorem selected40_checked : cell40.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 40=true := by decide +kernel
theorem actual40_full_bounds {r : ℝ} (hr : r∈Ioo (cell40.lo:ℝ) cell40.hi) :
    cell40.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell40.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected40_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 40<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected40_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 40<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell40.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual40_bounds hr).1
  · change cell40.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual40_bounds hr).2
theorem selected41_checked : cell41.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 41=true := by decide +kernel
theorem actual41_full_bounds {r : ℝ} (hr : r∈Ioo (cell41.lo:ℝ) cell41.hi) :
    cell41.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell41.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected41_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 41<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected41_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 41<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell41.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual41_bounds hr).1
  · change cell41.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual41_bounds hr).2
theorem selected42_checked : cell42.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 42=true := by decide +kernel
theorem actual42_full_bounds {r : ℝ} (hr : r∈Ioo (cell42.lo:ℝ) cell42.hi) :
    cell42.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell42.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected42_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 42<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected42_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 42<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell42.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual42_bounds hr).1
  · change cell42.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual42_bounds hr).2
theorem selected43_checked : cell43.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 43=true := by decide +kernel
theorem actual43_full_bounds {r : ℝ} (hr : r∈Ioo (cell43.lo:ℝ) cell43.hi) :
    cell43.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell43.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected43_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 43<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected43_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 43<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell43.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual43_bounds hr).1
  · change cell43.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual43_bounds hr).2
theorem selected44_checked : cell44.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 44=true := by decide +kernel
theorem actual44_full_bounds {r : ℝ} (hr : r∈Ioo (cell44.lo:ℝ) cell44.hi) :
    cell44.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell44.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected44_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 44<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected44_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 44<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell44.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual44_bounds hr).1
  · change cell44.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual44_bounds hr).2
theorem selected45_checked : cell45.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 45=true := by decide +kernel
theorem actual45_full_bounds {r : ℝ} (hr : r∈Ioo (cell45.lo:ℝ) cell45.hi) :
    cell45.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell45.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected45_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 45<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected45_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 45<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell45.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual45_bounds hr).1
  · change cell45.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual45_bounds hr).2
theorem selected46_checked : cell46.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 46=true := by decide +kernel
theorem actual46_full_bounds {r : ℝ} (hr : r∈Ioo (cell46.lo:ℝ) cell46.hi) :
    cell46.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell46.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected46_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 46<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected46_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 46<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell46.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual46_bounds hr).1
  · change cell46.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual46_bounds hr).2
theorem selected47_checked : cell47.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 47=true := by decide +kernel
theorem actual47_full_bounds {r : ℝ} (hr : r∈Ioo (cell47.lo:ℝ) cell47.hi) :
    cell47.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell47.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected47_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 47<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected47_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 47<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell47.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual47_bounds hr).1
  · change cell47.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual47_bounds hr).2
theorem selected48_checked : cell48.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 48=true := by decide +kernel
theorem actual48_full_bounds {r : ℝ} (hr : r∈Ioo (cell48.lo:ℝ) cell48.hi) :
    cell48.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell48.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected48_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 48<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected48_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 48<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell48.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual48_bounds hr).1
  · change cell48.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual48_bounds hr).2
theorem selected49_checked : cell49.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 49=true := by decide +kernel
theorem actual49_full_bounds {r : ℝ} (hr : r∈Ioo (cell49.lo:ℝ) cell49.hi) :
    cell49.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell49.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected49_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 49<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected49_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 49<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell49.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual49_bounds hr).1
  · change cell49.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual49_bounds hr).2
theorem selected50_checked : cell50.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 50=true := by decide +kernel
theorem actual50_full_bounds {r : ℝ} (hr : r∈Ioo (cell50.lo:ℝ) cell50.hi) :
    cell50.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell50.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected50_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 50<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected50_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 50<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell50.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual50_bounds hr).1
  · change cell50.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual50_bounds hr).2
theorem selected51_checked : cell51.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 51=true := by decide +kernel
theorem actual51_full_bounds {r : ℝ} (hr : r∈Ioo (cell51.lo:ℝ) cell51.hi) :
    cell51.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell51.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected51_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 51<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected51_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 51<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell51.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual51_bounds hr).1
  · change cell51.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual51_bounds hr).2
theorem selected52_checked : cell52.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 52=true := by decide +kernel
theorem actual52_full_bounds {r : ℝ} (hr : r∈Ioo (cell52.lo:ℝ) cell52.hi) :
    cell52.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell52.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected52_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 52<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected52_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 52<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell52.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual52_bounds hr).1
  · change cell52.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual52_bounds hr).2
theorem selected53_checked : cell53.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 53=true := by decide +kernel
theorem actual53_full_bounds {r : ℝ} (hr : r∈Ioo (cell53.lo:ℝ) cell53.hi) :
    cell53.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell53.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected53_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 53<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected53_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 53<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell53.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual53_bounds hr).1
  · change cell53.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual53_bounds hr).2
theorem selected54_checked : cell54.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 54=true := by decide +kernel
theorem actual54_full_bounds {r : ℝ} (hr : r∈Ioo (cell54.lo:ℝ) cell54.hi) :
    cell54.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell54.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected54_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 54<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected54_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 54<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell54.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual54_bounds hr).1
  · change cell54.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual54_bounds hr).2
theorem selected55_checked : cell55.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 55=true := by decide +kernel
theorem actual55_full_bounds {r : ℝ} (hr : r∈Ioo (cell55.lo:ℝ) cell55.hi) :
    cell55.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell55.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected55_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 55<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected55_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 55<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell55.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual55_bounds hr).1
  · change cell55.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual55_bounds hr).2
theorem selected56_checked : cell56.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 56=true := by decide +kernel
theorem actual56_full_bounds {r : ℝ} (hr : r∈Ioo (cell56.lo:ℝ) cell56.hi) :
    cell56.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell56.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected56_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 56<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected56_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 56<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell56.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual56_bounds hr).1
  · change cell56.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual56_bounds hr).2
theorem selected57_checked : cell57.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 57=true := by decide +kernel
theorem actual57_full_bounds {r : ℝ} (hr : r∈Ioo (cell57.lo:ℝ) cell57.hi) :
    cell57.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell57.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected57_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 57<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected57_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 57<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell57.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual57_bounds hr).1
  · change cell57.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual57_bounds hr).2
theorem selected58_checked : cell58.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 58=true := by decide +kernel
theorem actual58_full_bounds {r : ℝ} (hr : r∈Ioo (cell58.lo:ℝ) cell58.hi) :
    cell58.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell58.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected58_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 58<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected58_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 58<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell58.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual58_bounds hr).1
  · change cell58.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual58_bounds hr).2
theorem selected59_checked : cell59.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 59=true := by decide +kernel
theorem actual59_full_bounds {r : ℝ} (hr : r∈Ioo (cell59.lo:ℝ) cell59.hi) :
    cell59.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell59.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected59_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 59<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected59_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 59<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell59.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual59_bounds hr).1
  · change cell59.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual59_bounds hr).2
theorem selected60_checked : cell60.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 60=true := by decide +kernel
theorem actual60_full_bounds {r : ℝ} (hr : r∈Ioo (cell60.lo:ℝ) cell60.hi) :
    cell60.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell60.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected60_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 60<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected60_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 60<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell60.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual60_bounds hr).1
  · change cell60.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual60_bounds hr).2
theorem selected61_checked : cell61.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 61=true := by decide +kernel
theorem actual61_full_bounds {r : ℝ} (hr : r∈Ioo (cell61.lo:ℝ) cell61.hi) :
    cell61.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell61.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected61_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 61<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected61_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 61<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell61.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual61_bounds hr).1
  · change cell61.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual61_bounds hr).2
theorem selected62_checked : cell62.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 62=true := by decide +kernel
theorem actual62_full_bounds {r : ℝ} (hr : r∈Ioo (cell62.lo:ℝ) cell62.hi) :
    cell62.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell62.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected62_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 62<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected62_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 62<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell62.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual62_bounds hr).1
  · change cell62.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual62_bounds hr).2
theorem selected63_checked : cell63.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 63=true := by decide +kernel
theorem actual63_full_bounds {r : ℝ} (hr : r∈Ioo (cell63.lo:ℝ) cell63.hi) :
    cell63.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell63.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected63_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 63<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected63_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 63<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell63.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual63_bounds hr).1
  · change cell63.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual63_bounds hr).2
theorem actual_flux_bounds : ∀ c∈ReferenceFluxData.CoarseLowerShape.Batch0001.cells,∀ r∈Ioo (c.interval.lo:ℝ) c.interval.hi,
    c.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧ c.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  intro c hc r hr
  simp only [ReferenceFluxData.CoarseLowerShape.Batch0001.cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact actual32_full_bounds hr
  · exact actual33_full_bounds hr
  · exact actual34_full_bounds hr
  · exact actual35_full_bounds hr
  · exact actual36_full_bounds hr
  · exact actual37_full_bounds hr
  · exact actual38_full_bounds hr
  · exact actual39_full_bounds hr
  · exact actual40_full_bounds hr
  · exact actual41_full_bounds hr
  · exact actual42_full_bounds hr
  · exact actual43_full_bounds hr
  · exact actual44_full_bounds hr
  · exact actual45_full_bounds hr
  · exact actual46_full_bounds hr
  · exact actual47_full_bounds hr
  · exact actual48_full_bounds hr
  · exact actual49_full_bounds hr
  · exact actual50_full_bounds hr
  · exact actual51_full_bounds hr
  · exact actual52_full_bounds hr
  · exact actual53_full_bounds hr
  · exact actual54_full_bounds hr
  · exact actual55_full_bounds hr
  · exact actual56_full_bounds hr
  · exact actual57_full_bounds hr
  · exact actual58_full_bounds hr
  · exact actual59_full_bounds hr
  · exact actual60_full_bounds hr
  · exact actual61_full_bounds hr
  · exact actual62_full_bounds hr
  · exact actual63_full_bounds hr
end OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0001

namespace OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0002
open Set Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell64 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell64.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell64.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell178_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell40_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell64.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell64.weight⟩
def cell65 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell65.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell65.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell178_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell41_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell65.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell65.weight⟩
def cell66 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell66.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell66.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell179_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell41_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell66.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell66.weight⟩
def cell67 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell67.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell67.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell179_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell42_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell67.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell67.weight⟩
def cell68 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell68.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell68.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell179_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell43_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell68.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell68.weight⟩
def cell69 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell69.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell69.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell180_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell43_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell69.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell69.weight⟩
def cell70 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell70.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell70.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell180_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell44_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell70.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell70.weight⟩
def cell71 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell71.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell71.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0012.cell180_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell45_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell71.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell71.weight⟩
def cell72 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell72.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell72.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell181_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell45_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell72.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell72.weight⟩
def cell73 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell73.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell73.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell181_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell46_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell73.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell73.weight⟩
def cell74 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell74.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell74.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell181_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell47_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell74.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell74.weight⟩
def cell75 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell75.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell75.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell182_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell47_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell75.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell75.weight⟩
def cell76 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell76.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell76.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell183_0,ReferenceDensityData.CoarseLowerShape.Batch0002.cell47_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell76.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell76.weight⟩
def cell77 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell77.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell77.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell184_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell48_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell77.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell77.weight⟩
def cell78 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell78.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell78.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell184_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell49_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell78.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell78.weight⟩
def cell79 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell79.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell79.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell184_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell50_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell79.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell79.weight⟩
def cell80 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell80.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell80.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell185_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell50_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell80.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell80.weight⟩
def cell81 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell81.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell81.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell185_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell51_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell81.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell81.weight⟩
def cell82 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell82.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell82.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell186_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell51_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell82.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell82.weight⟩
def cell83 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell83.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell83.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell186_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell52_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell83.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell83.weight⟩
def cell84 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell84.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell84.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell186_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell53_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell84.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell84.weight⟩
def cell85 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell85.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell85.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell187_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell53_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell85.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell85.weight⟩
def cell86 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell86.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell86.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell187_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell54_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell86.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell86.weight⟩
def cell87 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell87.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell87.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell187_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell55_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell87.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell87.weight⟩
def cell88 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell88.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell88.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell187_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell56_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell88.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell88.weight⟩
def cell89 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell89.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell89.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell188_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell56_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell89.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell89.weight⟩
def cell90 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell90.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell90.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0013.cell188_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell57_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell90.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell90.weight⟩
def cell91 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell91.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell91.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell189_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell57_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell91.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell91.weight⟩
def cell92 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell92.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell92.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell189_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell58_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell92.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell92.weight⟩
def cell93 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell93.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell93.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell190_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell58_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell93.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell93.weight⟩
def cell94 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell94.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell94.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell190_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell59_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell94.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell94.weight⟩
def cell95 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0002.cell95.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0002.cell95.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell190_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell60_1],ReferenceFluxData.CoarseLowerShape.Batch0002.cell95.position,ReferenceFluxData.CoarseLowerShape.Batch0002.cell95.weight⟩
def cells : List Transport.ReferenceOverlayCell := [cell64,cell65,cell66,cell67,cell68,cell69,cell70,cell71,cell72,cell73,cell74,cell75,cell76,cell77,cell78,cell79,cell80,cell81,cell82,cell83,cell84,cell85,cell86,cell87,cell88,cell89,cell90,cell91,cell92,cell93,cell94,cell95]
theorem checked : cells.all Transport.ReferenceOverlayCell.check=true := by decide +kernel
theorem positions_linked : cells.map (·.position) = ReferenceFluxData.CoarseLowerShape.Batch0002.cells.map (·.position) := by rfl
theorem weights_linked : cells.map (·.weight) = ReferenceFluxData.CoarseLowerShape.Batch0002.cells.map (·.weight) := by rfl
theorem intervals_linked : cells.map (fun c => (c.lo,c.hi)) = ReferenceFluxData.CoarseLowerShape.Batch0002.cells.map (fun c => (c.interval.lo,c.interval.hi)) := by rfl
theorem actual64_bounds {r : ℝ} (hr : r∈Ioo (cell64.lo:ℝ) cell64.hi) :
    cell64.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell64.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell64.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell64.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell64 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell64.checked_sums hc
  · intro d hd
    have hi := cell64.checked_images hc hd hr
    simp only [cell64,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual178_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual40_1 hi).1
  · intro d hd
    have hi := cell64.checked_images hc hd hr
    simp only [cell64,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual178_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual40_1 hi).2
theorem actual65_bounds {r : ℝ} (hr : r∈Ioo (cell65.lo:ℝ) cell65.hi) :
    cell65.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell65.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell65.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell65.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell65 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell65.checked_sums hc
  · intro d hd
    have hi := cell65.checked_images hc hd hr
    simp only [cell65,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual178_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual41_1 hi).1
  · intro d hd
    have hi := cell65.checked_images hc hd hr
    simp only [cell65,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual178_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual41_1 hi).2
theorem actual66_bounds {r : ℝ} (hr : r∈Ioo (cell66.lo:ℝ) cell66.hi) :
    cell66.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell66.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell66.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell66.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell66 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell66.checked_sums hc
  · intro d hd
    have hi := cell66.checked_images hc hd hr
    simp only [cell66,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual179_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual41_1 hi).1
  · intro d hd
    have hi := cell66.checked_images hc hd hr
    simp only [cell66,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual179_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual41_1 hi).2
theorem actual67_bounds {r : ℝ} (hr : r∈Ioo (cell67.lo:ℝ) cell67.hi) :
    cell67.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell67.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell67.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell67.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell67 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell67.checked_sums hc
  · intro d hd
    have hi := cell67.checked_images hc hd hr
    simp only [cell67,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual179_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual42_1 hi).1
  · intro d hd
    have hi := cell67.checked_images hc hd hr
    simp only [cell67,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual179_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual42_1 hi).2
theorem actual68_bounds {r : ℝ} (hr : r∈Ioo (cell68.lo:ℝ) cell68.hi) :
    cell68.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell68.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell68.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell68.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell68 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell68.checked_sums hc
  · intro d hd
    have hi := cell68.checked_images hc hd hr
    simp only [cell68,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual179_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual43_1 hi).1
  · intro d hd
    have hi := cell68.checked_images hc hd hr
    simp only [cell68,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual179_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual43_1 hi).2
theorem actual69_bounds {r : ℝ} (hr : r∈Ioo (cell69.lo:ℝ) cell69.hi) :
    cell69.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell69.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell69.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell69.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell69 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell69.checked_sums hc
  · intro d hd
    have hi := cell69.checked_images hc hd hr
    simp only [cell69,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual180_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual43_1 hi).1
  · intro d hd
    have hi := cell69.checked_images hc hd hr
    simp only [cell69,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual180_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual43_1 hi).2
theorem actual70_bounds {r : ℝ} (hr : r∈Ioo (cell70.lo:ℝ) cell70.hi) :
    cell70.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell70.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell70.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell70.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell70 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell70.checked_sums hc
  · intro d hd
    have hi := cell70.checked_images hc hd hr
    simp only [cell70,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual180_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual44_1 hi).1
  · intro d hd
    have hi := cell70.checked_images hc hd hr
    simp only [cell70,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual180_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual44_1 hi).2
theorem actual71_bounds {r : ℝ} (hr : r∈Ioo (cell71.lo:ℝ) cell71.hi) :
    cell71.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell71.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell71.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell71.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell71 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell71.checked_sums hc
  · intro d hd
    have hi := cell71.checked_images hc hd hr
    simp only [cell71,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual180_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual45_1 hi).1
  · intro d hd
    have hi := cell71.checked_images hc hd hr
    simp only [cell71,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0012.actual180_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual45_1 hi).2
theorem actual72_bounds {r : ℝ} (hr : r∈Ioo (cell72.lo:ℝ) cell72.hi) :
    cell72.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell72.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell72.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell72.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell72 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell72.checked_sums hc
  · intro d hd
    have hi := cell72.checked_images hc hd hr
    simp only [cell72,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual181_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual45_1 hi).1
  · intro d hd
    have hi := cell72.checked_images hc hd hr
    simp only [cell72,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual181_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual45_1 hi).2
theorem actual73_bounds {r : ℝ} (hr : r∈Ioo (cell73.lo:ℝ) cell73.hi) :
    cell73.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell73.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell73.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell73.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell73 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell73.checked_sums hc
  · intro d hd
    have hi := cell73.checked_images hc hd hr
    simp only [cell73,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual181_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual46_1 hi).1
  · intro d hd
    have hi := cell73.checked_images hc hd hr
    simp only [cell73,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual181_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual46_1 hi).2
theorem actual74_bounds {r : ℝ} (hr : r∈Ioo (cell74.lo:ℝ) cell74.hi) :
    cell74.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell74.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell74.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell74.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell74 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell74.checked_sums hc
  · intro d hd
    have hi := cell74.checked_images hc hd hr
    simp only [cell74,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual181_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual47_1 hi).1
  · intro d hd
    have hi := cell74.checked_images hc hd hr
    simp only [cell74,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual181_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual47_1 hi).2
theorem actual75_bounds {r : ℝ} (hr : r∈Ioo (cell75.lo:ℝ) cell75.hi) :
    cell75.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell75.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell75.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell75.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell75 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell75.checked_sums hc
  · intro d hd
    have hi := cell75.checked_images hc hd hr
    simp only [cell75,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual182_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual47_1 hi).1
  · intro d hd
    have hi := cell75.checked_images hc hd hr
    simp only [cell75,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual182_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual47_1 hi).2
theorem actual76_bounds {r : ℝ} (hr : r∈Ioo (cell76.lo:ℝ) cell76.hi) :
    cell76.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell76.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell76.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell76.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell76 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell76.checked_sums hc
  · intro d hd
    have hi := cell76.checked_images hc hd hr
    simp only [cell76,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual183_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual47_1 hi).1
  · intro d hd
    have hi := cell76.checked_images hc hd hr
    simp only [cell76,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual183_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0002.actual47_1 hi).2
theorem actual77_bounds {r : ℝ} (hr : r∈Ioo (cell77.lo:ℝ) cell77.hi) :
    cell77.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell77.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell77.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell77.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell77 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell77.checked_sums hc
  · intro d hd
    have hi := cell77.checked_images hc hd hr
    simp only [cell77,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual184_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual48_1 hi).1
  · intro d hd
    have hi := cell77.checked_images hc hd hr
    simp only [cell77,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual184_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual48_1 hi).2
theorem actual78_bounds {r : ℝ} (hr : r∈Ioo (cell78.lo:ℝ) cell78.hi) :
    cell78.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell78.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell78.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell78.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell78 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell78.checked_sums hc
  · intro d hd
    have hi := cell78.checked_images hc hd hr
    simp only [cell78,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual184_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual49_1 hi).1
  · intro d hd
    have hi := cell78.checked_images hc hd hr
    simp only [cell78,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual184_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual49_1 hi).2
theorem actual79_bounds {r : ℝ} (hr : r∈Ioo (cell79.lo:ℝ) cell79.hi) :
    cell79.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell79.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell79.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell79.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell79 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell79.checked_sums hc
  · intro d hd
    have hi := cell79.checked_images hc hd hr
    simp only [cell79,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual184_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual50_1 hi).1
  · intro d hd
    have hi := cell79.checked_images hc hd hr
    simp only [cell79,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual184_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual50_1 hi).2
theorem actual80_bounds {r : ℝ} (hr : r∈Ioo (cell80.lo:ℝ) cell80.hi) :
    cell80.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell80.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell80.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell80.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell80 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell80.checked_sums hc
  · intro d hd
    have hi := cell80.checked_images hc hd hr
    simp only [cell80,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual185_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual50_1 hi).1
  · intro d hd
    have hi := cell80.checked_images hc hd hr
    simp only [cell80,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual185_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual50_1 hi).2
theorem actual81_bounds {r : ℝ} (hr : r∈Ioo (cell81.lo:ℝ) cell81.hi) :
    cell81.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell81.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell81.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell81.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell81 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell81.checked_sums hc
  · intro d hd
    have hi := cell81.checked_images hc hd hr
    simp only [cell81,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual185_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual51_1 hi).1
  · intro d hd
    have hi := cell81.checked_images hc hd hr
    simp only [cell81,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual185_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual51_1 hi).2
theorem actual82_bounds {r : ℝ} (hr : r∈Ioo (cell82.lo:ℝ) cell82.hi) :
    cell82.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell82.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell82.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell82.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell82 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell82.checked_sums hc
  · intro d hd
    have hi := cell82.checked_images hc hd hr
    simp only [cell82,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual186_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual51_1 hi).1
  · intro d hd
    have hi := cell82.checked_images hc hd hr
    simp only [cell82,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual186_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual51_1 hi).2
theorem actual83_bounds {r : ℝ} (hr : r∈Ioo (cell83.lo:ℝ) cell83.hi) :
    cell83.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell83.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell83.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell83.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell83 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell83.checked_sums hc
  · intro d hd
    have hi := cell83.checked_images hc hd hr
    simp only [cell83,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual186_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual52_1 hi).1
  · intro d hd
    have hi := cell83.checked_images hc hd hr
    simp only [cell83,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual186_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual52_1 hi).2
theorem actual84_bounds {r : ℝ} (hr : r∈Ioo (cell84.lo:ℝ) cell84.hi) :
    cell84.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell84.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell84.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell84.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell84 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell84.checked_sums hc
  · intro d hd
    have hi := cell84.checked_images hc hd hr
    simp only [cell84,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual186_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual53_1 hi).1
  · intro d hd
    have hi := cell84.checked_images hc hd hr
    simp only [cell84,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual186_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual53_1 hi).2
theorem actual85_bounds {r : ℝ} (hr : r∈Ioo (cell85.lo:ℝ) cell85.hi) :
    cell85.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell85.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell85.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell85.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell85 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell85.checked_sums hc
  · intro d hd
    have hi := cell85.checked_images hc hd hr
    simp only [cell85,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual53_1 hi).1
  · intro d hd
    have hi := cell85.checked_images hc hd hr
    simp only [cell85,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual53_1 hi).2
theorem actual86_bounds {r : ℝ} (hr : r∈Ioo (cell86.lo:ℝ) cell86.hi) :
    cell86.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell86.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell86.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell86.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell86 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell86.checked_sums hc
  · intro d hd
    have hi := cell86.checked_images hc hd hr
    simp only [cell86,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual54_1 hi).1
  · intro d hd
    have hi := cell86.checked_images hc hd hr
    simp only [cell86,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual54_1 hi).2
theorem actual87_bounds {r : ℝ} (hr : r∈Ioo (cell87.lo:ℝ) cell87.hi) :
    cell87.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell87.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell87.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell87.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell87 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell87.checked_sums hc
  · intro d hd
    have hi := cell87.checked_images hc hd hr
    simp only [cell87,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual55_1 hi).1
  · intro d hd
    have hi := cell87.checked_images hc hd hr
    simp only [cell87,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual55_1 hi).2
theorem actual88_bounds {r : ℝ} (hr : r∈Ioo (cell88.lo:ℝ) cell88.hi) :
    cell88.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell88.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell88.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell88.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell88 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell88.checked_sums hc
  · intro d hd
    have hi := cell88.checked_images hc hd hr
    simp only [cell88,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual56_1 hi).1
  · intro d hd
    have hi := cell88.checked_images hc hd hr
    simp only [cell88,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual187_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual56_1 hi).2
theorem actual89_bounds {r : ℝ} (hr : r∈Ioo (cell89.lo:ℝ) cell89.hi) :
    cell89.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell89.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell89.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell89.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell89 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell89.checked_sums hc
  · intro d hd
    have hi := cell89.checked_images hc hd hr
    simp only [cell89,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual188_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual56_1 hi).1
  · intro d hd
    have hi := cell89.checked_images hc hd hr
    simp only [cell89,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual188_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual56_1 hi).2
theorem actual90_bounds {r : ℝ} (hr : r∈Ioo (cell90.lo:ℝ) cell90.hi) :
    cell90.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell90.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell90.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell90.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell90 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell90.checked_sums hc
  · intro d hd
    have hi := cell90.checked_images hc hd hr
    simp only [cell90,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual188_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual57_1 hi).1
  · intro d hd
    have hi := cell90.checked_images hc hd hr
    simp only [cell90,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0013.actual188_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual57_1 hi).2
theorem actual91_bounds {r : ℝ} (hr : r∈Ioo (cell91.lo:ℝ) cell91.hi) :
    cell91.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell91.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell91.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell91.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell91 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell91.checked_sums hc
  · intro d hd
    have hi := cell91.checked_images hc hd hr
    simp only [cell91,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual189_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual57_1 hi).1
  · intro d hd
    have hi := cell91.checked_images hc hd hr
    simp only [cell91,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual189_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual57_1 hi).2
theorem actual92_bounds {r : ℝ} (hr : r∈Ioo (cell92.lo:ℝ) cell92.hi) :
    cell92.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell92.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell92.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell92.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell92 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell92.checked_sums hc
  · intro d hd
    have hi := cell92.checked_images hc hd hr
    simp only [cell92,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual189_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual58_1 hi).1
  · intro d hd
    have hi := cell92.checked_images hc hd hr
    simp only [cell92,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual189_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual58_1 hi).2
theorem actual93_bounds {r : ℝ} (hr : r∈Ioo (cell93.lo:ℝ) cell93.hi) :
    cell93.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell93.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell93.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell93.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell93 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell93.checked_sums hc
  · intro d hd
    have hi := cell93.checked_images hc hd hr
    simp only [cell93,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual190_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual58_1 hi).1
  · intro d hd
    have hi := cell93.checked_images hc hd hr
    simp only [cell93,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual190_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual58_1 hi).2
theorem actual94_bounds {r : ℝ} (hr : r∈Ioo (cell94.lo:ℝ) cell94.hi) :
    cell94.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell94.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell94.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell94.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell94 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell94.checked_sums hc
  · intro d hd
    have hi := cell94.checked_images hc hd hr
    simp only [cell94,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual190_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual59_1 hi).1
  · intro d hd
    have hi := cell94.checked_images hc hd hr
    simp only [cell94,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual190_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual59_1 hi).2
theorem actual95_bounds {r : ℝ} (hr : r∈Ioo (cell95.lo:ℝ) cell95.hi) :
    cell95.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell95.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell95.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell95.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell95 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell95.checked_sums hc
  · intro d hd
    have hi := cell95.checked_images hc hd hr
    simp only [cell95,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual190_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual60_1 hi).1
  · intro d hd
    have hi := cell95.checked_images hc hd hr
    simp only [cell95,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual190_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual60_1 hi).2
theorem selected64_checked : cell64.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 64=true := by decide +kernel
theorem actual64_full_bounds {r : ℝ} (hr : r∈Ioo (cell64.lo:ℝ) cell64.hi) :
    cell64.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell64.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected64_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 64<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected64_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 64<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell64.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual64_bounds hr).1
  · change cell64.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual64_bounds hr).2
theorem selected65_checked : cell65.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 65=true := by decide +kernel
theorem actual65_full_bounds {r : ℝ} (hr : r∈Ioo (cell65.lo:ℝ) cell65.hi) :
    cell65.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell65.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected65_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 65<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected65_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 65<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell65.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual65_bounds hr).1
  · change cell65.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual65_bounds hr).2
theorem selected66_checked : cell66.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 66=true := by decide +kernel
theorem actual66_full_bounds {r : ℝ} (hr : r∈Ioo (cell66.lo:ℝ) cell66.hi) :
    cell66.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell66.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected66_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 66<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected66_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 66<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell66.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual66_bounds hr).1
  · change cell66.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual66_bounds hr).2
theorem selected67_checked : cell67.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 67=true := by decide +kernel
theorem actual67_full_bounds {r : ℝ} (hr : r∈Ioo (cell67.lo:ℝ) cell67.hi) :
    cell67.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell67.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected67_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 67<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected67_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 67<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell67.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual67_bounds hr).1
  · change cell67.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual67_bounds hr).2
theorem selected68_checked : cell68.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 68=true := by decide +kernel
theorem actual68_full_bounds {r : ℝ} (hr : r∈Ioo (cell68.lo:ℝ) cell68.hi) :
    cell68.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell68.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected68_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 68<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected68_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 68<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell68.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual68_bounds hr).1
  · change cell68.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual68_bounds hr).2
theorem selected69_checked : cell69.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 69=true := by decide +kernel
theorem actual69_full_bounds {r : ℝ} (hr : r∈Ioo (cell69.lo:ℝ) cell69.hi) :
    cell69.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell69.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected69_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 69<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected69_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 69<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell69.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual69_bounds hr).1
  · change cell69.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual69_bounds hr).2
theorem selected70_checked : cell70.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 70=true := by decide +kernel
theorem actual70_full_bounds {r : ℝ} (hr : r∈Ioo (cell70.lo:ℝ) cell70.hi) :
    cell70.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell70.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected70_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 70<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected70_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 70<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell70.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual70_bounds hr).1
  · change cell70.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual70_bounds hr).2
theorem selected71_checked : cell71.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 71=true := by decide +kernel
theorem actual71_full_bounds {r : ℝ} (hr : r∈Ioo (cell71.lo:ℝ) cell71.hi) :
    cell71.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell71.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected71_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 71<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected71_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 71<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell71.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual71_bounds hr).1
  · change cell71.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual71_bounds hr).2
theorem selected72_checked : cell72.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 72=true := by decide +kernel
theorem actual72_full_bounds {r : ℝ} (hr : r∈Ioo (cell72.lo:ℝ) cell72.hi) :
    cell72.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell72.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected72_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 72<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected72_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 72<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell72.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual72_bounds hr).1
  · change cell72.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual72_bounds hr).2
theorem selected73_checked : cell73.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 73=true := by decide +kernel
theorem actual73_full_bounds {r : ℝ} (hr : r∈Ioo (cell73.lo:ℝ) cell73.hi) :
    cell73.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell73.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected73_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 73<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected73_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 73<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell73.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual73_bounds hr).1
  · change cell73.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual73_bounds hr).2
theorem selected74_checked : cell74.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 74=true := by decide +kernel
theorem actual74_full_bounds {r : ℝ} (hr : r∈Ioo (cell74.lo:ℝ) cell74.hi) :
    cell74.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell74.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected74_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 74<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected74_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 74<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell74.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual74_bounds hr).1
  · change cell74.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual74_bounds hr).2
theorem selected75_checked : cell75.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 75=true := by decide +kernel
theorem actual75_full_bounds {r : ℝ} (hr : r∈Ioo (cell75.lo:ℝ) cell75.hi) :
    cell75.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell75.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected75_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 75<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected75_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 75<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell75.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual75_bounds hr).1
  · change cell75.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual75_bounds hr).2
theorem selected76_checked : cell76.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 76=true := by decide +kernel
theorem actual76_full_bounds {r : ℝ} (hr : r∈Ioo (cell76.lo:ℝ) cell76.hi) :
    cell76.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell76.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected76_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 76<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected76_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 76<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell76.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual76_bounds hr).1
  · change cell76.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual76_bounds hr).2
theorem selected77_checked : cell77.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 77=true := by decide +kernel
theorem actual77_full_bounds {r : ℝ} (hr : r∈Ioo (cell77.lo:ℝ) cell77.hi) :
    cell77.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell77.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected77_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 77<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected77_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 77<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell77.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual77_bounds hr).1
  · change cell77.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual77_bounds hr).2
theorem selected78_checked : cell78.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 78=true := by decide +kernel
theorem actual78_full_bounds {r : ℝ} (hr : r∈Ioo (cell78.lo:ℝ) cell78.hi) :
    cell78.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell78.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected78_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 78<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected78_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 78<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell78.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual78_bounds hr).1
  · change cell78.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual78_bounds hr).2
theorem selected79_checked : cell79.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 79=true := by decide +kernel
theorem actual79_full_bounds {r : ℝ} (hr : r∈Ioo (cell79.lo:ℝ) cell79.hi) :
    cell79.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell79.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected79_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 79<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected79_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 79<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell79.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual79_bounds hr).1
  · change cell79.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual79_bounds hr).2
theorem selected80_checked : cell80.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 80=true := by decide +kernel
theorem actual80_full_bounds {r : ℝ} (hr : r∈Ioo (cell80.lo:ℝ) cell80.hi) :
    cell80.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell80.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected80_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 80<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected80_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 80<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell80.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual80_bounds hr).1
  · change cell80.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual80_bounds hr).2
theorem selected81_checked : cell81.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 81=true := by decide +kernel
theorem actual81_full_bounds {r : ℝ} (hr : r∈Ioo (cell81.lo:ℝ) cell81.hi) :
    cell81.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell81.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected81_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 81<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected81_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 81<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell81.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual81_bounds hr).1
  · change cell81.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual81_bounds hr).2
theorem selected82_checked : cell82.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 82=true := by decide +kernel
theorem actual82_full_bounds {r : ℝ} (hr : r∈Ioo (cell82.lo:ℝ) cell82.hi) :
    cell82.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell82.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected82_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 82<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected82_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 82<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell82.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual82_bounds hr).1
  · change cell82.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual82_bounds hr).2
theorem selected83_checked : cell83.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 83=true := by decide +kernel
theorem actual83_full_bounds {r : ℝ} (hr : r∈Ioo (cell83.lo:ℝ) cell83.hi) :
    cell83.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell83.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected83_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 83<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected83_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 83<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell83.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual83_bounds hr).1
  · change cell83.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual83_bounds hr).2
theorem selected84_checked : cell84.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 84=true := by decide +kernel
theorem actual84_full_bounds {r : ℝ} (hr : r∈Ioo (cell84.lo:ℝ) cell84.hi) :
    cell84.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell84.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected84_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 84<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected84_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 84<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell84.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual84_bounds hr).1
  · change cell84.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual84_bounds hr).2
theorem selected85_checked : cell85.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 85=true := by decide +kernel
theorem actual85_full_bounds {r : ℝ} (hr : r∈Ioo (cell85.lo:ℝ) cell85.hi) :
    cell85.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell85.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected85_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 85<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected85_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 85<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell85.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual85_bounds hr).1
  · change cell85.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual85_bounds hr).2
theorem selected86_checked : cell86.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 86=true := by decide +kernel
theorem actual86_full_bounds {r : ℝ} (hr : r∈Ioo (cell86.lo:ℝ) cell86.hi) :
    cell86.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell86.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected86_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 86<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected86_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 86<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell86.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual86_bounds hr).1
  · change cell86.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual86_bounds hr).2
theorem selected87_checked : cell87.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 87=true := by decide +kernel
theorem actual87_full_bounds {r : ℝ} (hr : r∈Ioo (cell87.lo:ℝ) cell87.hi) :
    cell87.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell87.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected87_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 87<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected87_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 87<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell87.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual87_bounds hr).1
  · change cell87.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual87_bounds hr).2
theorem selected88_checked : cell88.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 88=true := by decide +kernel
theorem actual88_full_bounds {r : ℝ} (hr : r∈Ioo (cell88.lo:ℝ) cell88.hi) :
    cell88.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell88.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected88_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 88<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected88_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 88<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell88.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual88_bounds hr).1
  · change cell88.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual88_bounds hr).2
theorem selected89_checked : cell89.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 89=true := by decide +kernel
theorem actual89_full_bounds {r : ℝ} (hr : r∈Ioo (cell89.lo:ℝ) cell89.hi) :
    cell89.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell89.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected89_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 89<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected89_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 89<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell89.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual89_bounds hr).1
  · change cell89.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual89_bounds hr).2
theorem selected90_checked : cell90.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 90=true := by decide +kernel
theorem actual90_full_bounds {r : ℝ} (hr : r∈Ioo (cell90.lo:ℝ) cell90.hi) :
    cell90.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell90.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected90_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 90<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected90_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 90<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell90.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual90_bounds hr).1
  · change cell90.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual90_bounds hr).2
theorem selected91_checked : cell91.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 91=true := by decide +kernel
theorem actual91_full_bounds {r : ℝ} (hr : r∈Ioo (cell91.lo:ℝ) cell91.hi) :
    cell91.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell91.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected91_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 91<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected91_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 91<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell91.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual91_bounds hr).1
  · change cell91.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual91_bounds hr).2
theorem selected92_checked : cell92.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 92=true := by decide +kernel
theorem actual92_full_bounds {r : ℝ} (hr : r∈Ioo (cell92.lo:ℝ) cell92.hi) :
    cell92.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell92.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected92_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 92<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected92_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 92<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell92.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual92_bounds hr).1
  · change cell92.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual92_bounds hr).2
theorem selected93_checked : cell93.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 93=true := by decide +kernel
theorem actual93_full_bounds {r : ℝ} (hr : r∈Ioo (cell93.lo:ℝ) cell93.hi) :
    cell93.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell93.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected93_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 93<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected93_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 93<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell93.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual93_bounds hr).1
  · change cell93.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual93_bounds hr).2
theorem selected94_checked : cell94.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 94=true := by decide +kernel
theorem actual94_full_bounds {r : ℝ} (hr : r∈Ioo (cell94.lo:ℝ) cell94.hi) :
    cell94.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell94.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected94_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 94<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected94_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 94<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell94.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual94_bounds hr).1
  · change cell94.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual94_bounds hr).2
theorem selected95_checked : cell95.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 95=true := by decide +kernel
theorem actual95_full_bounds {r : ℝ} (hr : r∈Ioo (cell95.lo:ℝ) cell95.hi) :
    cell95.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell95.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected95_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 95<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected95_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 95<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell95.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual95_bounds hr).1
  · change cell95.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual95_bounds hr).2
theorem actual_flux_bounds : ∀ c∈ReferenceFluxData.CoarseLowerShape.Batch0002.cells,∀ r∈Ioo (c.interval.lo:ℝ) c.interval.hi,
    c.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧ c.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  intro c hc r hr
  simp only [ReferenceFluxData.CoarseLowerShape.Batch0002.cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact actual64_full_bounds hr
  · exact actual65_full_bounds hr
  · exact actual66_full_bounds hr
  · exact actual67_full_bounds hr
  · exact actual68_full_bounds hr
  · exact actual69_full_bounds hr
  · exact actual70_full_bounds hr
  · exact actual71_full_bounds hr
  · exact actual72_full_bounds hr
  · exact actual73_full_bounds hr
  · exact actual74_full_bounds hr
  · exact actual75_full_bounds hr
  · exact actual76_full_bounds hr
  · exact actual77_full_bounds hr
  · exact actual78_full_bounds hr
  · exact actual79_full_bounds hr
  · exact actual80_full_bounds hr
  · exact actual81_full_bounds hr
  · exact actual82_full_bounds hr
  · exact actual83_full_bounds hr
  · exact actual84_full_bounds hr
  · exact actual85_full_bounds hr
  · exact actual86_full_bounds hr
  · exact actual87_full_bounds hr
  · exact actual88_full_bounds hr
  · exact actual89_full_bounds hr
  · exact actual90_full_bounds hr
  · exact actual91_full_bounds hr
  · exact actual92_full_bounds hr
  · exact actual93_full_bounds hr
  · exact actual94_full_bounds hr
  · exact actual95_full_bounds hr
end OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0002

namespace OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0003
open Set Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell96 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell96.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell96.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell191_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell60_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell96.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell96.weight⟩
def cell97 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell97.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell97.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell191_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell61_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell97.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell97.weight⟩
def cell98 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell98.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell98.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell191_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell62_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell98.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell98.weight⟩
def cell99 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell99.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell99.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell192_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell62_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell99.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell99.weight⟩
def cell100 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell100.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell100.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell192_0,ReferenceDensityData.CoarseLowerShape.Batch0003.cell63_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell100.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell100.weight⟩
def cell101 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell101.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell101.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell192_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell64_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell101.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell101.weight⟩
def cell102 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell102.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell102.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell192_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell65_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell102.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell102.weight⟩
def cell103 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell103.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell103.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell193_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell65_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell103.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell103.weight⟩
def cell104 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell104.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell104.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell193_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell66_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell104.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell104.weight⟩
def cell105 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell105.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell105.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell193_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell67_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell105.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell105.weight⟩
def cell106 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell106.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell106.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell194_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell67_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell106.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell106.weight⟩
def cell107 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell107.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell107.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell194_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell68_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell107.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell107.weight⟩
def cell108 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell108.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell108.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell194_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell69_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell108.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell108.weight⟩
def cell109 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell109.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell109.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell195_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell69_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell109.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell109.weight⟩
def cell110 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell110.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell110.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell195_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell70_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell110.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell110.weight⟩
def cell111 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell111.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell111.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell195_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell71_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell111.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell111.weight⟩
def cell112 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell112.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell112.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell196_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell71_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell112.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell112.weight⟩
def cell113 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell113.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell113.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell196_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell72_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell113.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell113.weight⟩
def cell114 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell114.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell114.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0014.cell196_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell73_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell114.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell114.weight⟩
def cell115 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell115.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell115.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell197_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell73_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell115.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell115.weight⟩
def cell116 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell116.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell116.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell197_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell74_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell116.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell116.weight⟩
def cell117 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell117.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell117.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell198_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell74_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell117.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell117.weight⟩
def cell118 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell118.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell118.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell198_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell75_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell118.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell118.weight⟩
def cell119 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell119.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell119.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell198_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell76_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell119.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell119.weight⟩
def cell120 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell120.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell120.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell198_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell77_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell120.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell120.weight⟩
def cell121 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell121.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell121.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell199_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell77_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell121.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell121.weight⟩
def cell122 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell122.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell122.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell199_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell78_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell122.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell122.weight⟩
def cell123 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell123.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell123.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell199_0,ReferenceDensityData.CoarseLowerShape.Batch0004.cell79_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell123.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell123.weight⟩
def cell124 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell124.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell124.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell199_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell80_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell124.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell124.weight⟩
def cell125 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell125.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell125.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell200_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell80_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell125.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell125.weight⟩
def cell126 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell126.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell126.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell200_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell81_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell126.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell126.weight⟩
def cell127 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0003.cell127.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0003.cell127.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell200_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell82_1],ReferenceFluxData.CoarseLowerShape.Batch0003.cell127.position,ReferenceFluxData.CoarseLowerShape.Batch0003.cell127.weight⟩
def cells : List Transport.ReferenceOverlayCell := [cell96,cell97,cell98,cell99,cell100,cell101,cell102,cell103,cell104,cell105,cell106,cell107,cell108,cell109,cell110,cell111,cell112,cell113,cell114,cell115,cell116,cell117,cell118,cell119,cell120,cell121,cell122,cell123,cell124,cell125,cell126,cell127]
theorem checked : cells.all Transport.ReferenceOverlayCell.check=true := by decide +kernel
theorem positions_linked : cells.map (·.position) = ReferenceFluxData.CoarseLowerShape.Batch0003.cells.map (·.position) := by rfl
theorem weights_linked : cells.map (·.weight) = ReferenceFluxData.CoarseLowerShape.Batch0003.cells.map (·.weight) := by rfl
theorem intervals_linked : cells.map (fun c => (c.lo,c.hi)) = ReferenceFluxData.CoarseLowerShape.Batch0003.cells.map (fun c => (c.interval.lo,c.interval.hi)) := by rfl
theorem actual96_bounds {r : ℝ} (hr : r∈Ioo (cell96.lo:ℝ) cell96.hi) :
    cell96.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell96.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell96.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell96.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell96 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell96.checked_sums hc
  · intro d hd
    have hi := cell96.checked_images hc hd hr
    simp only [cell96,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual191_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual60_1 hi).1
  · intro d hd
    have hi := cell96.checked_images hc hd hr
    simp only [cell96,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual191_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual60_1 hi).2
theorem actual97_bounds {r : ℝ} (hr : r∈Ioo (cell97.lo:ℝ) cell97.hi) :
    cell97.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell97.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell97.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell97.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell97 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell97.checked_sums hc
  · intro d hd
    have hi := cell97.checked_images hc hd hr
    simp only [cell97,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual191_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual61_1 hi).1
  · intro d hd
    have hi := cell97.checked_images hc hd hr
    simp only [cell97,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual191_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual61_1 hi).2
theorem actual98_bounds {r : ℝ} (hr : r∈Ioo (cell98.lo:ℝ) cell98.hi) :
    cell98.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell98.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell98.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell98.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell98 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell98.checked_sums hc
  · intro d hd
    have hi := cell98.checked_images hc hd hr
    simp only [cell98,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual191_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual62_1 hi).1
  · intro d hd
    have hi := cell98.checked_images hc hd hr
    simp only [cell98,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual191_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual62_1 hi).2
theorem actual99_bounds {r : ℝ} (hr : r∈Ioo (cell99.lo:ℝ) cell99.hi) :
    cell99.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell99.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell99.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell99.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell99 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell99.checked_sums hc
  · intro d hd
    have hi := cell99.checked_images hc hd hr
    simp only [cell99,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual62_1 hi).1
  · intro d hd
    have hi := cell99.checked_images hc hd hr
    simp only [cell99,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual62_1 hi).2
theorem actual100_bounds {r : ℝ} (hr : r∈Ioo (cell100.lo:ℝ) cell100.hi) :
    cell100.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell100.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell100.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell100.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell100 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell100.checked_sums hc
  · intro d hd
    have hi := cell100.checked_images hc hd hr
    simp only [cell100,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual63_1 hi).1
  · intro d hd
    have hi := cell100.checked_images hc hd hr
    simp only [cell100,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0003.actual63_1 hi).2
theorem actual101_bounds {r : ℝ} (hr : r∈Ioo (cell101.lo:ℝ) cell101.hi) :
    cell101.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell101.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell101.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell101.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell101 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell101.checked_sums hc
  · intro d hd
    have hi := cell101.checked_images hc hd hr
    simp only [cell101,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual64_1 hi).1
  · intro d hd
    have hi := cell101.checked_images hc hd hr
    simp only [cell101,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual64_1 hi).2
theorem actual102_bounds {r : ℝ} (hr : r∈Ioo (cell102.lo:ℝ) cell102.hi) :
    cell102.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell102.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell102.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell102.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell102 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell102.checked_sums hc
  · intro d hd
    have hi := cell102.checked_images hc hd hr
    simp only [cell102,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual65_1 hi).1
  · intro d hd
    have hi := cell102.checked_images hc hd hr
    simp only [cell102,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual192_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual65_1 hi).2
theorem actual103_bounds {r : ℝ} (hr : r∈Ioo (cell103.lo:ℝ) cell103.hi) :
    cell103.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell103.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell103.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell103.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell103 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell103.checked_sums hc
  · intro d hd
    have hi := cell103.checked_images hc hd hr
    simp only [cell103,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual193_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual65_1 hi).1
  · intro d hd
    have hi := cell103.checked_images hc hd hr
    simp only [cell103,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual193_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual65_1 hi).2
theorem actual104_bounds {r : ℝ} (hr : r∈Ioo (cell104.lo:ℝ) cell104.hi) :
    cell104.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell104.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell104.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell104.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell104 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell104.checked_sums hc
  · intro d hd
    have hi := cell104.checked_images hc hd hr
    simp only [cell104,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual193_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual66_1 hi).1
  · intro d hd
    have hi := cell104.checked_images hc hd hr
    simp only [cell104,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual193_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual66_1 hi).2
theorem actual105_bounds {r : ℝ} (hr : r∈Ioo (cell105.lo:ℝ) cell105.hi) :
    cell105.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell105.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell105.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell105.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell105 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell105.checked_sums hc
  · intro d hd
    have hi := cell105.checked_images hc hd hr
    simp only [cell105,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual193_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual67_1 hi).1
  · intro d hd
    have hi := cell105.checked_images hc hd hr
    simp only [cell105,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual193_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual67_1 hi).2
theorem actual106_bounds {r : ℝ} (hr : r∈Ioo (cell106.lo:ℝ) cell106.hi) :
    cell106.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell106.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell106.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell106.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell106 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell106.checked_sums hc
  · intro d hd
    have hi := cell106.checked_images hc hd hr
    simp only [cell106,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual194_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual67_1 hi).1
  · intro d hd
    have hi := cell106.checked_images hc hd hr
    simp only [cell106,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual194_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual67_1 hi).2
theorem actual107_bounds {r : ℝ} (hr : r∈Ioo (cell107.lo:ℝ) cell107.hi) :
    cell107.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell107.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell107.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell107.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell107 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell107.checked_sums hc
  · intro d hd
    have hi := cell107.checked_images hc hd hr
    simp only [cell107,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual194_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual68_1 hi).1
  · intro d hd
    have hi := cell107.checked_images hc hd hr
    simp only [cell107,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual194_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual68_1 hi).2
theorem actual108_bounds {r : ℝ} (hr : r∈Ioo (cell108.lo:ℝ) cell108.hi) :
    cell108.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell108.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell108.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell108.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell108 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell108.checked_sums hc
  · intro d hd
    have hi := cell108.checked_images hc hd hr
    simp only [cell108,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual194_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual69_1 hi).1
  · intro d hd
    have hi := cell108.checked_images hc hd hr
    simp only [cell108,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual194_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual69_1 hi).2
theorem actual109_bounds {r : ℝ} (hr : r∈Ioo (cell109.lo:ℝ) cell109.hi) :
    cell109.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell109.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell109.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell109.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell109 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell109.checked_sums hc
  · intro d hd
    have hi := cell109.checked_images hc hd hr
    simp only [cell109,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual195_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual69_1 hi).1
  · intro d hd
    have hi := cell109.checked_images hc hd hr
    simp only [cell109,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual195_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual69_1 hi).2
theorem actual110_bounds {r : ℝ} (hr : r∈Ioo (cell110.lo:ℝ) cell110.hi) :
    cell110.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell110.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell110.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell110.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell110 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell110.checked_sums hc
  · intro d hd
    have hi := cell110.checked_images hc hd hr
    simp only [cell110,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual195_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual70_1 hi).1
  · intro d hd
    have hi := cell110.checked_images hc hd hr
    simp only [cell110,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual195_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual70_1 hi).2
theorem actual111_bounds {r : ℝ} (hr : r∈Ioo (cell111.lo:ℝ) cell111.hi) :
    cell111.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell111.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell111.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell111.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell111 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell111.checked_sums hc
  · intro d hd
    have hi := cell111.checked_images hc hd hr
    simp only [cell111,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual195_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual71_1 hi).1
  · intro d hd
    have hi := cell111.checked_images hc hd hr
    simp only [cell111,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual195_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual71_1 hi).2
theorem actual112_bounds {r : ℝ} (hr : r∈Ioo (cell112.lo:ℝ) cell112.hi) :
    cell112.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell112.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell112.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell112.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell112 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell112.checked_sums hc
  · intro d hd
    have hi := cell112.checked_images hc hd hr
    simp only [cell112,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual196_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual71_1 hi).1
  · intro d hd
    have hi := cell112.checked_images hc hd hr
    simp only [cell112,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual196_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual71_1 hi).2
theorem actual113_bounds {r : ℝ} (hr : r∈Ioo (cell113.lo:ℝ) cell113.hi) :
    cell113.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell113.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell113.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell113.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell113 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell113.checked_sums hc
  · intro d hd
    have hi := cell113.checked_images hc hd hr
    simp only [cell113,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual196_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual72_1 hi).1
  · intro d hd
    have hi := cell113.checked_images hc hd hr
    simp only [cell113,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual196_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual72_1 hi).2
theorem actual114_bounds {r : ℝ} (hr : r∈Ioo (cell114.lo:ℝ) cell114.hi) :
    cell114.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell114.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell114.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell114.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell114 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell114.checked_sums hc
  · intro d hd
    have hi := cell114.checked_images hc hd hr
    simp only [cell114,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual196_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual73_1 hi).1
  · intro d hd
    have hi := cell114.checked_images hc hd hr
    simp only [cell114,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0014.actual196_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual73_1 hi).2
theorem actual115_bounds {r : ℝ} (hr : r∈Ioo (cell115.lo:ℝ) cell115.hi) :
    cell115.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell115.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell115.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell115.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell115 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell115.checked_sums hc
  · intro d hd
    have hi := cell115.checked_images hc hd hr
    simp only [cell115,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual197_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual73_1 hi).1
  · intro d hd
    have hi := cell115.checked_images hc hd hr
    simp only [cell115,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual197_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual73_1 hi).2
theorem actual116_bounds {r : ℝ} (hr : r∈Ioo (cell116.lo:ℝ) cell116.hi) :
    cell116.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell116.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell116.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell116.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell116 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell116.checked_sums hc
  · intro d hd
    have hi := cell116.checked_images hc hd hr
    simp only [cell116,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual197_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual74_1 hi).1
  · intro d hd
    have hi := cell116.checked_images hc hd hr
    simp only [cell116,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual197_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual74_1 hi).2
theorem actual117_bounds {r : ℝ} (hr : r∈Ioo (cell117.lo:ℝ) cell117.hi) :
    cell117.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell117.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell117.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell117.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell117 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell117.checked_sums hc
  · intro d hd
    have hi := cell117.checked_images hc hd hr
    simp only [cell117,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual74_1 hi).1
  · intro d hd
    have hi := cell117.checked_images hc hd hr
    simp only [cell117,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual74_1 hi).2
theorem actual118_bounds {r : ℝ} (hr : r∈Ioo (cell118.lo:ℝ) cell118.hi) :
    cell118.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell118.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell118.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell118.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell118 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell118.checked_sums hc
  · intro d hd
    have hi := cell118.checked_images hc hd hr
    simp only [cell118,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual75_1 hi).1
  · intro d hd
    have hi := cell118.checked_images hc hd hr
    simp only [cell118,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual75_1 hi).2
theorem actual119_bounds {r : ℝ} (hr : r∈Ioo (cell119.lo:ℝ) cell119.hi) :
    cell119.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell119.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell119.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell119.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell119 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell119.checked_sums hc
  · intro d hd
    have hi := cell119.checked_images hc hd hr
    simp only [cell119,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual76_1 hi).1
  · intro d hd
    have hi := cell119.checked_images hc hd hr
    simp only [cell119,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual76_1 hi).2
theorem actual120_bounds {r : ℝ} (hr : r∈Ioo (cell120.lo:ℝ) cell120.hi) :
    cell120.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell120.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell120.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell120.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell120 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell120.checked_sums hc
  · intro d hd
    have hi := cell120.checked_images hc hd hr
    simp only [cell120,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual77_1 hi).1
  · intro d hd
    have hi := cell120.checked_images hc hd hr
    simp only [cell120,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual198_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual77_1 hi).2
theorem actual121_bounds {r : ℝ} (hr : r∈Ioo (cell121.lo:ℝ) cell121.hi) :
    cell121.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell121.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell121.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell121.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell121 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell121.checked_sums hc
  · intro d hd
    have hi := cell121.checked_images hc hd hr
    simp only [cell121,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual77_1 hi).1
  · intro d hd
    have hi := cell121.checked_images hc hd hr
    simp only [cell121,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual77_1 hi).2
theorem actual122_bounds {r : ℝ} (hr : r∈Ioo (cell122.lo:ℝ) cell122.hi) :
    cell122.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell122.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell122.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell122.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell122 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell122.checked_sums hc
  · intro d hd
    have hi := cell122.checked_images hc hd hr
    simp only [cell122,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual78_1 hi).1
  · intro d hd
    have hi := cell122.checked_images hc hd hr
    simp only [cell122,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual78_1 hi).2
theorem actual123_bounds {r : ℝ} (hr : r∈Ioo (cell123.lo:ℝ) cell123.hi) :
    cell123.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell123.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell123.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell123.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell123 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell123.checked_sums hc
  · intro d hd
    have hi := cell123.checked_images hc hd hr
    simp only [cell123,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual79_1 hi).1
  · intro d hd
    have hi := cell123.checked_images hc hd hr
    simp only [cell123,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0004.actual79_1 hi).2
theorem actual124_bounds {r : ℝ} (hr : r∈Ioo (cell124.lo:ℝ) cell124.hi) :
    cell124.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell124.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell124.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell124.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell124 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell124.checked_sums hc
  · intro d hd
    have hi := cell124.checked_images hc hd hr
    simp only [cell124,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual80_1 hi).1
  · intro d hd
    have hi := cell124.checked_images hc hd hr
    simp only [cell124,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual199_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual80_1 hi).2
theorem actual125_bounds {r : ℝ} (hr : r∈Ioo (cell125.lo:ℝ) cell125.hi) :
    cell125.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell125.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell125.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell125.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell125 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell125.checked_sums hc
  · intro d hd
    have hi := cell125.checked_images hc hd hr
    simp only [cell125,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual200_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual80_1 hi).1
  · intro d hd
    have hi := cell125.checked_images hc hd hr
    simp only [cell125,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual200_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual80_1 hi).2
theorem actual126_bounds {r : ℝ} (hr : r∈Ioo (cell126.lo:ℝ) cell126.hi) :
    cell126.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell126.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell126.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell126.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell126 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell126.checked_sums hc
  · intro d hd
    have hi := cell126.checked_images hc hd hr
    simp only [cell126,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual200_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual81_1 hi).1
  · intro d hd
    have hi := cell126.checked_images hc hd hr
    simp only [cell126,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual200_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual81_1 hi).2
theorem actual127_bounds {r : ℝ} (hr : r∈Ioo (cell127.lo:ℝ) cell127.hi) :
    cell127.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell127.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell127.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell127.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell127 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell127.checked_sums hc
  · intro d hd
    have hi := cell127.checked_images hc hd hr
    simp only [cell127,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual200_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual82_1 hi).1
  · intro d hd
    have hi := cell127.checked_images hc hd hr
    simp only [cell127,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual200_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual82_1 hi).2
theorem selected96_checked : cell96.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 96=true := by decide +kernel
theorem actual96_full_bounds {r : ℝ} (hr : r∈Ioo (cell96.lo:ℝ) cell96.hi) :
    cell96.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell96.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected96_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 96<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected96_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 96<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell96.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual96_bounds hr).1
  · change cell96.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual96_bounds hr).2
theorem selected97_checked : cell97.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 97=true := by decide +kernel
theorem actual97_full_bounds {r : ℝ} (hr : r∈Ioo (cell97.lo:ℝ) cell97.hi) :
    cell97.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell97.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected97_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 97<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected97_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 97<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell97.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual97_bounds hr).1
  · change cell97.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual97_bounds hr).2
theorem selected98_checked : cell98.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 98=true := by decide +kernel
theorem actual98_full_bounds {r : ℝ} (hr : r∈Ioo (cell98.lo:ℝ) cell98.hi) :
    cell98.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell98.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected98_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 98<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected98_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 98<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell98.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual98_bounds hr).1
  · change cell98.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual98_bounds hr).2
theorem selected99_checked : cell99.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 99=true := by decide +kernel
theorem actual99_full_bounds {r : ℝ} (hr : r∈Ioo (cell99.lo:ℝ) cell99.hi) :
    cell99.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell99.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected99_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 99<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected99_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 99<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell99.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual99_bounds hr).1
  · change cell99.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual99_bounds hr).2
theorem selected100_checked : cell100.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 100=true := by decide +kernel
theorem actual100_full_bounds {r : ℝ} (hr : r∈Ioo (cell100.lo:ℝ) cell100.hi) :
    cell100.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell100.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected100_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 100<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected100_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 100<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell100.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual100_bounds hr).1
  · change cell100.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual100_bounds hr).2
theorem selected101_checked : cell101.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 101=true := by decide +kernel
theorem actual101_full_bounds {r : ℝ} (hr : r∈Ioo (cell101.lo:ℝ) cell101.hi) :
    cell101.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell101.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected101_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 101<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected101_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 101<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell101.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual101_bounds hr).1
  · change cell101.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual101_bounds hr).2
theorem selected102_checked : cell102.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 102=true := by decide +kernel
theorem actual102_full_bounds {r : ℝ} (hr : r∈Ioo (cell102.lo:ℝ) cell102.hi) :
    cell102.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell102.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected102_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 102<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected102_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 102<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell102.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual102_bounds hr).1
  · change cell102.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual102_bounds hr).2
theorem selected103_checked : cell103.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 103=true := by decide +kernel
theorem actual103_full_bounds {r : ℝ} (hr : r∈Ioo (cell103.lo:ℝ) cell103.hi) :
    cell103.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell103.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected103_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 103<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected103_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 103<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell103.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual103_bounds hr).1
  · change cell103.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual103_bounds hr).2
theorem selected104_checked : cell104.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 104=true := by decide +kernel
theorem actual104_full_bounds {r : ℝ} (hr : r∈Ioo (cell104.lo:ℝ) cell104.hi) :
    cell104.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell104.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected104_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 104<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected104_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 104<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell104.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual104_bounds hr).1
  · change cell104.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual104_bounds hr).2
theorem selected105_checked : cell105.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 105=true := by decide +kernel
theorem actual105_full_bounds {r : ℝ} (hr : r∈Ioo (cell105.lo:ℝ) cell105.hi) :
    cell105.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell105.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected105_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 105<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected105_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 105<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell105.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual105_bounds hr).1
  · change cell105.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual105_bounds hr).2
theorem selected106_checked : cell106.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 106=true := by decide +kernel
theorem actual106_full_bounds {r : ℝ} (hr : r∈Ioo (cell106.lo:ℝ) cell106.hi) :
    cell106.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell106.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected106_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 106<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected106_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 106<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell106.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual106_bounds hr).1
  · change cell106.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual106_bounds hr).2
theorem selected107_checked : cell107.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 107=true := by decide +kernel
theorem actual107_full_bounds {r : ℝ} (hr : r∈Ioo (cell107.lo:ℝ) cell107.hi) :
    cell107.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell107.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected107_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 107<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected107_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 107<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell107.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual107_bounds hr).1
  · change cell107.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual107_bounds hr).2
theorem selected108_checked : cell108.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 108=true := by decide +kernel
theorem actual108_full_bounds {r : ℝ} (hr : r∈Ioo (cell108.lo:ℝ) cell108.hi) :
    cell108.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell108.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected108_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 108<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected108_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 108<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell108.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual108_bounds hr).1
  · change cell108.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual108_bounds hr).2
theorem selected109_checked : cell109.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 109=true := by decide +kernel
theorem actual109_full_bounds {r : ℝ} (hr : r∈Ioo (cell109.lo:ℝ) cell109.hi) :
    cell109.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell109.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected109_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 109<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected109_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 109<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell109.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual109_bounds hr).1
  · change cell109.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual109_bounds hr).2
theorem selected110_checked : cell110.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 110=true := by decide +kernel
theorem actual110_full_bounds {r : ℝ} (hr : r∈Ioo (cell110.lo:ℝ) cell110.hi) :
    cell110.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell110.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected110_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 110<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected110_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 110<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell110.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual110_bounds hr).1
  · change cell110.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual110_bounds hr).2
theorem selected111_checked : cell111.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 111=true := by decide +kernel
theorem actual111_full_bounds {r : ℝ} (hr : r∈Ioo (cell111.lo:ℝ) cell111.hi) :
    cell111.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell111.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected111_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 111<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected111_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 111<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell111.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual111_bounds hr).1
  · change cell111.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual111_bounds hr).2
theorem selected112_checked : cell112.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 112=true := by decide +kernel
theorem actual112_full_bounds {r : ℝ} (hr : r∈Ioo (cell112.lo:ℝ) cell112.hi) :
    cell112.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell112.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected112_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 112<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected112_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 112<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell112.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual112_bounds hr).1
  · change cell112.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual112_bounds hr).2
theorem selected113_checked : cell113.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 113=true := by decide +kernel
theorem actual113_full_bounds {r : ℝ} (hr : r∈Ioo (cell113.lo:ℝ) cell113.hi) :
    cell113.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell113.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected113_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 113<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected113_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 113<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell113.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual113_bounds hr).1
  · change cell113.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual113_bounds hr).2
theorem selected114_checked : cell114.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 114=true := by decide +kernel
theorem actual114_full_bounds {r : ℝ} (hr : r∈Ioo (cell114.lo:ℝ) cell114.hi) :
    cell114.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell114.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected114_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 114<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected114_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 114<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell114.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual114_bounds hr).1
  · change cell114.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual114_bounds hr).2
theorem selected115_checked : cell115.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 115=true := by decide +kernel
theorem actual115_full_bounds {r : ℝ} (hr : r∈Ioo (cell115.lo:ℝ) cell115.hi) :
    cell115.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell115.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected115_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 115<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected115_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 115<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell115.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual115_bounds hr).1
  · change cell115.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual115_bounds hr).2
theorem selected116_checked : cell116.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 116=true := by decide +kernel
theorem actual116_full_bounds {r : ℝ} (hr : r∈Ioo (cell116.lo:ℝ) cell116.hi) :
    cell116.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell116.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected116_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 116<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected116_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 116<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell116.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual116_bounds hr).1
  · change cell116.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual116_bounds hr).2
theorem selected117_checked : cell117.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 117=true := by decide +kernel
theorem actual117_full_bounds {r : ℝ} (hr : r∈Ioo (cell117.lo:ℝ) cell117.hi) :
    cell117.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell117.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected117_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 117<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected117_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 117<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell117.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual117_bounds hr).1
  · change cell117.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual117_bounds hr).2
theorem selected118_checked : cell118.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 118=true := by decide +kernel
theorem actual118_full_bounds {r : ℝ} (hr : r∈Ioo (cell118.lo:ℝ) cell118.hi) :
    cell118.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell118.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected118_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 118<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected118_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 118<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell118.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual118_bounds hr).1
  · change cell118.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual118_bounds hr).2
theorem selected119_checked : cell119.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 119=true := by decide +kernel
theorem actual119_full_bounds {r : ℝ} (hr : r∈Ioo (cell119.lo:ℝ) cell119.hi) :
    cell119.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell119.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected119_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 119<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected119_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 119<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell119.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual119_bounds hr).1
  · change cell119.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual119_bounds hr).2
theorem selected120_checked : cell120.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 120=true := by decide +kernel
theorem actual120_full_bounds {r : ℝ} (hr : r∈Ioo (cell120.lo:ℝ) cell120.hi) :
    cell120.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell120.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected120_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 120<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected120_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 120<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell120.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual120_bounds hr).1
  · change cell120.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual120_bounds hr).2
theorem selected121_checked : cell121.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 121=true := by decide +kernel
theorem actual121_full_bounds {r : ℝ} (hr : r∈Ioo (cell121.lo:ℝ) cell121.hi) :
    cell121.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell121.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected121_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 121<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected121_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 121<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell121.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual121_bounds hr).1
  · change cell121.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual121_bounds hr).2
theorem selected122_checked : cell122.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 122=true := by decide +kernel
theorem actual122_full_bounds {r : ℝ} (hr : r∈Ioo (cell122.lo:ℝ) cell122.hi) :
    cell122.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell122.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected122_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 122<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected122_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 122<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell122.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual122_bounds hr).1
  · change cell122.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual122_bounds hr).2
theorem selected123_checked : cell123.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 123=true := by decide +kernel
theorem actual123_full_bounds {r : ℝ} (hr : r∈Ioo (cell123.lo:ℝ) cell123.hi) :
    cell123.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell123.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected123_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 123<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected123_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 123<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell123.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual123_bounds hr).1
  · change cell123.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual123_bounds hr).2
theorem selected124_checked : cell124.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 124=true := by decide +kernel
theorem actual124_full_bounds {r : ℝ} (hr : r∈Ioo (cell124.lo:ℝ) cell124.hi) :
    cell124.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell124.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected124_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 124<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected124_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 124<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell124.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual124_bounds hr).1
  · change cell124.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual124_bounds hr).2
theorem selected125_checked : cell125.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 125=true := by decide +kernel
theorem actual125_full_bounds {r : ℝ} (hr : r∈Ioo (cell125.lo:ℝ) cell125.hi) :
    cell125.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell125.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected125_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 125<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected125_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 125<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell125.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual125_bounds hr).1
  · change cell125.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual125_bounds hr).2
theorem selected126_checked : cell126.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 126=true := by decide +kernel
theorem actual126_full_bounds {r : ℝ} (hr : r∈Ioo (cell126.lo:ℝ) cell126.hi) :
    cell126.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell126.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected126_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 126<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected126_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 126<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell126.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual126_bounds hr).1
  · change cell126.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual126_bounds hr).2
theorem selected127_checked : cell127.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 127=true := by decide +kernel
theorem actual127_full_bounds {r : ℝ} (hr : r∈Ioo (cell127.lo:ℝ) cell127.hi) :
    cell127.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell127.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected127_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 127<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected127_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 127<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell127.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual127_bounds hr).1
  · change cell127.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual127_bounds hr).2
theorem actual_flux_bounds : ∀ c∈ReferenceFluxData.CoarseLowerShape.Batch0003.cells,∀ r∈Ioo (c.interval.lo:ℝ) c.interval.hi,
    c.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧ c.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  intro c hc r hr
  simp only [ReferenceFluxData.CoarseLowerShape.Batch0003.cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact actual96_full_bounds hr
  · exact actual97_full_bounds hr
  · exact actual98_full_bounds hr
  · exact actual99_full_bounds hr
  · exact actual100_full_bounds hr
  · exact actual101_full_bounds hr
  · exact actual102_full_bounds hr
  · exact actual103_full_bounds hr
  · exact actual104_full_bounds hr
  · exact actual105_full_bounds hr
  · exact actual106_full_bounds hr
  · exact actual107_full_bounds hr
  · exact actual108_full_bounds hr
  · exact actual109_full_bounds hr
  · exact actual110_full_bounds hr
  · exact actual111_full_bounds hr
  · exact actual112_full_bounds hr
  · exact actual113_full_bounds hr
  · exact actual114_full_bounds hr
  · exact actual115_full_bounds hr
  · exact actual116_full_bounds hr
  · exact actual117_full_bounds hr
  · exact actual118_full_bounds hr
  · exact actual119_full_bounds hr
  · exact actual120_full_bounds hr
  · exact actual121_full_bounds hr
  · exact actual122_full_bounds hr
  · exact actual123_full_bounds hr
  · exact actual124_full_bounds hr
  · exact actual125_full_bounds hr
  · exact actual126_full_bounds hr
  · exact actual127_full_bounds hr
end OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0003

namespace OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0004
open Set Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cell128 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell128.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell128.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell201_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell82_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell128.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell128.weight⟩
def cell129 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell129.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell129.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell201_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell83_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell129.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell129.weight⟩
def cell130 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell130.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell130.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell201_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell84_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell130.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell130.weight⟩
def cell131 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell131.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell131.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell202_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell84_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell131.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell131.weight⟩
def cell132 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell132.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell132.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell202_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell85_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell132.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell132.weight⟩
def cell133 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell133.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell133.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell202_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell86_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell133.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell133.weight⟩
def cell134 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell134.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell134.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell203_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell86_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell134.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell134.weight⟩
def cell135 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell135.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell135.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell203_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell87_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell135.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell135.weight⟩
def cell136 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell136.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell136.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell204_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell87_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell136.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell136.weight⟩
def cell137 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell137.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell137.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell204_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell88_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell137.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell137.weight⟩
def cell138 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell138.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell138.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0015.cell204_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell89_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell138.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell138.weight⟩
def cell139 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell139.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell139.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell205_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell89_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell139.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell139.weight⟩
def cell140 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell140.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell140.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell205_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell90_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell140.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell140.weight⟩
def cell141 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell141.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell141.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell206_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell90_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell141.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell141.weight⟩
def cell142 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell142.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell142.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell206_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell91_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell142.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell142.weight⟩
def cell143 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell143.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell143.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell207_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell91_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell143.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell143.weight⟩
def cell144 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell144.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell144.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell207_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell92_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell144.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell144.weight⟩
def cell145 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell145.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell145.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell207_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell93_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell145.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell145.weight⟩
def cell146 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell146.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell146.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell208_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell94_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell146.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell146.weight⟩
def cell147 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell147.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell147.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell208_0,ReferenceDensityData.CoarseLowerShape.Batch0005.cell95_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell147.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell147.weight⟩
def cell148 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell148.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell148.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell208_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell96_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell148.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell148.weight⟩
def cell149 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell149.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell149.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell209_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell96_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell149.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell149.weight⟩
def cell150 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell150.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell150.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell209_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell97_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell150.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell150.weight⟩
def cell151 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell151.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell151.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell210_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell97_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell151.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell151.weight⟩
def cell152 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell152.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell152.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell210_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell98_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell152.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell152.weight⟩
def cell153 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell153.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell153.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell210_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell99_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell153.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell153.weight⟩
def cell154 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell154.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell154.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell211_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell99_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell154.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell154.weight⟩
def cell155 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell155.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell155.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell211_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell100_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell155.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell155.weight⟩
def cell156 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell156.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell156.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell211_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell101_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell156.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell156.weight⟩
def cell157 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell157.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell157.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell212_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell101_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell157.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell157.weight⟩
def cell158 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell158.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell158.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0016.cell212_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell102_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell158.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell158.weight⟩
def cell159 : Transport.ReferenceOverlayCell := ⟨ReferenceFluxData.CoarseLowerShape.Batch0004.cell159.interval.lo,ReferenceFluxData.CoarseLowerShape.Batch0004.cell159.interval.hi,[ReferenceDensityData.CoarseLowerShape.Batch0017.cell213_0,ReferenceDensityData.CoarseLowerShape.Batch0006.cell102_1],ReferenceFluxData.CoarseLowerShape.Batch0004.cell159.position,ReferenceFluxData.CoarseLowerShape.Batch0004.cell159.weight⟩
def cells : List Transport.ReferenceOverlayCell := [cell128,cell129,cell130,cell131,cell132,cell133,cell134,cell135,cell136,cell137,cell138,cell139,cell140,cell141,cell142,cell143,cell144,cell145,cell146,cell147,cell148,cell149,cell150,cell151,cell152,cell153,cell154,cell155,cell156,cell157,cell158,cell159]
theorem checked : cells.all Transport.ReferenceOverlayCell.check=true := by decide +kernel
theorem positions_linked : cells.map (·.position) = ReferenceFluxData.CoarseLowerShape.Batch0004.cells.map (·.position) := by rfl
theorem weights_linked : cells.map (·.weight) = ReferenceFluxData.CoarseLowerShape.Batch0004.cells.map (·.weight) := by rfl
theorem intervals_linked : cells.map (fun c => (c.lo,c.hi)) = ReferenceFluxData.CoarseLowerShape.Batch0004.cells.map (fun c => (c.interval.lo,c.interval.hi)) := by rfl
theorem actual128_bounds {r : ℝ} (hr : r∈Ioo (cell128.lo:ℝ) cell128.hi) :
    cell128.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell128.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell128.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell128.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell128 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell128.checked_sums hc
  · intro d hd
    have hi := cell128.checked_images hc hd hr
    simp only [cell128,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual201_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual82_1 hi).1
  · intro d hd
    have hi := cell128.checked_images hc hd hr
    simp only [cell128,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual201_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual82_1 hi).2
theorem actual129_bounds {r : ℝ} (hr : r∈Ioo (cell129.lo:ℝ) cell129.hi) :
    cell129.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell129.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell129.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell129.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell129 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell129.checked_sums hc
  · intro d hd
    have hi := cell129.checked_images hc hd hr
    simp only [cell129,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual201_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual83_1 hi).1
  · intro d hd
    have hi := cell129.checked_images hc hd hr
    simp only [cell129,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual201_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual83_1 hi).2
theorem actual130_bounds {r : ℝ} (hr : r∈Ioo (cell130.lo:ℝ) cell130.hi) :
    cell130.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell130.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell130.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell130.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell130 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell130.checked_sums hc
  · intro d hd
    have hi := cell130.checked_images hc hd hr
    simp only [cell130,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual201_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual84_1 hi).1
  · intro d hd
    have hi := cell130.checked_images hc hd hr
    simp only [cell130,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual201_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual84_1 hi).2
theorem actual131_bounds {r : ℝ} (hr : r∈Ioo (cell131.lo:ℝ) cell131.hi) :
    cell131.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell131.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell131.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell131.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell131 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell131.checked_sums hc
  · intro d hd
    have hi := cell131.checked_images hc hd hr
    simp only [cell131,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual202_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual84_1 hi).1
  · intro d hd
    have hi := cell131.checked_images hc hd hr
    simp only [cell131,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual202_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual84_1 hi).2
theorem actual132_bounds {r : ℝ} (hr : r∈Ioo (cell132.lo:ℝ) cell132.hi) :
    cell132.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell132.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell132.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell132.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell132 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell132.checked_sums hc
  · intro d hd
    have hi := cell132.checked_images hc hd hr
    simp only [cell132,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual202_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual85_1 hi).1
  · intro d hd
    have hi := cell132.checked_images hc hd hr
    simp only [cell132,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual202_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual85_1 hi).2
theorem actual133_bounds {r : ℝ} (hr : r∈Ioo (cell133.lo:ℝ) cell133.hi) :
    cell133.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell133.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell133.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell133.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell133 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell133.checked_sums hc
  · intro d hd
    have hi := cell133.checked_images hc hd hr
    simp only [cell133,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual202_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual86_1 hi).1
  · intro d hd
    have hi := cell133.checked_images hc hd hr
    simp only [cell133,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual202_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual86_1 hi).2
theorem actual134_bounds {r : ℝ} (hr : r∈Ioo (cell134.lo:ℝ) cell134.hi) :
    cell134.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell134.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell134.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell134.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell134 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell134.checked_sums hc
  · intro d hd
    have hi := cell134.checked_images hc hd hr
    simp only [cell134,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual203_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual86_1 hi).1
  · intro d hd
    have hi := cell134.checked_images hc hd hr
    simp only [cell134,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual203_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual86_1 hi).2
theorem actual135_bounds {r : ℝ} (hr : r∈Ioo (cell135.lo:ℝ) cell135.hi) :
    cell135.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell135.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell135.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell135.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell135 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell135.checked_sums hc
  · intro d hd
    have hi := cell135.checked_images hc hd hr
    simp only [cell135,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual203_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual87_1 hi).1
  · intro d hd
    have hi := cell135.checked_images hc hd hr
    simp only [cell135,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual203_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual87_1 hi).2
theorem actual136_bounds {r : ℝ} (hr : r∈Ioo (cell136.lo:ℝ) cell136.hi) :
    cell136.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell136.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell136.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell136.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell136 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell136.checked_sums hc
  · intro d hd
    have hi := cell136.checked_images hc hd hr
    simp only [cell136,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual204_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual87_1 hi).1
  · intro d hd
    have hi := cell136.checked_images hc hd hr
    simp only [cell136,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual204_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual87_1 hi).2
theorem actual137_bounds {r : ℝ} (hr : r∈Ioo (cell137.lo:ℝ) cell137.hi) :
    cell137.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell137.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell137.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell137.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell137 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell137.checked_sums hc
  · intro d hd
    have hi := cell137.checked_images hc hd hr
    simp only [cell137,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual204_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual88_1 hi).1
  · intro d hd
    have hi := cell137.checked_images hc hd hr
    simp only [cell137,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual204_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual88_1 hi).2
theorem actual138_bounds {r : ℝ} (hr : r∈Ioo (cell138.lo:ℝ) cell138.hi) :
    cell138.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell138.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell138.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell138.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell138 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell138.checked_sums hc
  · intro d hd
    have hi := cell138.checked_images hc hd hr
    simp only [cell138,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual204_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual89_1 hi).1
  · intro d hd
    have hi := cell138.checked_images hc hd hr
    simp only [cell138,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0015.actual204_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual89_1 hi).2
theorem actual139_bounds {r : ℝ} (hr : r∈Ioo (cell139.lo:ℝ) cell139.hi) :
    cell139.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell139.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell139.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell139.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell139 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell139.checked_sums hc
  · intro d hd
    have hi := cell139.checked_images hc hd hr
    simp only [cell139,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual205_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual89_1 hi).1
  · intro d hd
    have hi := cell139.checked_images hc hd hr
    simp only [cell139,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual205_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual89_1 hi).2
theorem actual140_bounds {r : ℝ} (hr : r∈Ioo (cell140.lo:ℝ) cell140.hi) :
    cell140.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell140.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell140.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell140.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell140 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell140.checked_sums hc
  · intro d hd
    have hi := cell140.checked_images hc hd hr
    simp only [cell140,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual205_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual90_1 hi).1
  · intro d hd
    have hi := cell140.checked_images hc hd hr
    simp only [cell140,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual205_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual90_1 hi).2
theorem actual141_bounds {r : ℝ} (hr : r∈Ioo (cell141.lo:ℝ) cell141.hi) :
    cell141.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell141.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell141.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell141.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell141 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell141.checked_sums hc
  · intro d hd
    have hi := cell141.checked_images hc hd hr
    simp only [cell141,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual206_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual90_1 hi).1
  · intro d hd
    have hi := cell141.checked_images hc hd hr
    simp only [cell141,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual206_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual90_1 hi).2
theorem actual142_bounds {r : ℝ} (hr : r∈Ioo (cell142.lo:ℝ) cell142.hi) :
    cell142.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell142.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell142.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell142.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell142 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell142.checked_sums hc
  · intro d hd
    have hi := cell142.checked_images hc hd hr
    simp only [cell142,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual206_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual91_1 hi).1
  · intro d hd
    have hi := cell142.checked_images hc hd hr
    simp only [cell142,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual206_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual91_1 hi).2
theorem actual143_bounds {r : ℝ} (hr : r∈Ioo (cell143.lo:ℝ) cell143.hi) :
    cell143.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell143.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell143.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell143.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell143 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell143.checked_sums hc
  · intro d hd
    have hi := cell143.checked_images hc hd hr
    simp only [cell143,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual207_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual91_1 hi).1
  · intro d hd
    have hi := cell143.checked_images hc hd hr
    simp only [cell143,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual207_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual91_1 hi).2
theorem actual144_bounds {r : ℝ} (hr : r∈Ioo (cell144.lo:ℝ) cell144.hi) :
    cell144.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell144.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell144.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell144.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell144 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell144.checked_sums hc
  · intro d hd
    have hi := cell144.checked_images hc hd hr
    simp only [cell144,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual207_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual92_1 hi).1
  · intro d hd
    have hi := cell144.checked_images hc hd hr
    simp only [cell144,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual207_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual92_1 hi).2
theorem actual145_bounds {r : ℝ} (hr : r∈Ioo (cell145.lo:ℝ) cell145.hi) :
    cell145.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell145.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell145.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell145.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell145 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell145.checked_sums hc
  · intro d hd
    have hi := cell145.checked_images hc hd hr
    simp only [cell145,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual207_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual93_1 hi).1
  · intro d hd
    have hi := cell145.checked_images hc hd hr
    simp only [cell145,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual207_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual93_1 hi).2
theorem actual146_bounds {r : ℝ} (hr : r∈Ioo (cell146.lo:ℝ) cell146.hi) :
    cell146.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell146.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell146.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell146.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell146 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell146.checked_sums hc
  · intro d hd
    have hi := cell146.checked_images hc hd hr
    simp only [cell146,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual208_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual94_1 hi).1
  · intro d hd
    have hi := cell146.checked_images hc hd hr
    simp only [cell146,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual208_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual94_1 hi).2
theorem actual147_bounds {r : ℝ} (hr : r∈Ioo (cell147.lo:ℝ) cell147.hi) :
    cell147.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell147.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell147.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell147.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell147 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell147.checked_sums hc
  · intro d hd
    have hi := cell147.checked_images hc hd hr
    simp only [cell147,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual208_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual95_1 hi).1
  · intro d hd
    have hi := cell147.checked_images hc hd hr
    simp only [cell147,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual208_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0005.actual95_1 hi).2
theorem actual148_bounds {r : ℝ} (hr : r∈Ioo (cell148.lo:ℝ) cell148.hi) :
    cell148.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell148.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell148.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell148.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell148 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell148.checked_sums hc
  · intro d hd
    have hi := cell148.checked_images hc hd hr
    simp only [cell148,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual208_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual96_1 hi).1
  · intro d hd
    have hi := cell148.checked_images hc hd hr
    simp only [cell148,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual208_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual96_1 hi).2
theorem actual149_bounds {r : ℝ} (hr : r∈Ioo (cell149.lo:ℝ) cell149.hi) :
    cell149.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell149.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell149.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell149.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell149 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell149.checked_sums hc
  · intro d hd
    have hi := cell149.checked_images hc hd hr
    simp only [cell149,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual209_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual96_1 hi).1
  · intro d hd
    have hi := cell149.checked_images hc hd hr
    simp only [cell149,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual209_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual96_1 hi).2
theorem actual150_bounds {r : ℝ} (hr : r∈Ioo (cell150.lo:ℝ) cell150.hi) :
    cell150.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell150.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell150.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell150.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell150 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell150.checked_sums hc
  · intro d hd
    have hi := cell150.checked_images hc hd hr
    simp only [cell150,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual209_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual97_1 hi).1
  · intro d hd
    have hi := cell150.checked_images hc hd hr
    simp only [cell150,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual209_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual97_1 hi).2
theorem actual151_bounds {r : ℝ} (hr : r∈Ioo (cell151.lo:ℝ) cell151.hi) :
    cell151.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell151.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell151.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell151.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell151 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell151.checked_sums hc
  · intro d hd
    have hi := cell151.checked_images hc hd hr
    simp only [cell151,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual210_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual97_1 hi).1
  · intro d hd
    have hi := cell151.checked_images hc hd hr
    simp only [cell151,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual210_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual97_1 hi).2
theorem actual152_bounds {r : ℝ} (hr : r∈Ioo (cell152.lo:ℝ) cell152.hi) :
    cell152.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell152.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell152.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell152.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell152 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell152.checked_sums hc
  · intro d hd
    have hi := cell152.checked_images hc hd hr
    simp only [cell152,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual210_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual98_1 hi).1
  · intro d hd
    have hi := cell152.checked_images hc hd hr
    simp only [cell152,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual210_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual98_1 hi).2
theorem actual153_bounds {r : ℝ} (hr : r∈Ioo (cell153.lo:ℝ) cell153.hi) :
    cell153.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell153.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell153.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell153.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell153 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell153.checked_sums hc
  · intro d hd
    have hi := cell153.checked_images hc hd hr
    simp only [cell153,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual210_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual99_1 hi).1
  · intro d hd
    have hi := cell153.checked_images hc hd hr
    simp only [cell153,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual210_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual99_1 hi).2
theorem actual154_bounds {r : ℝ} (hr : r∈Ioo (cell154.lo:ℝ) cell154.hi) :
    cell154.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell154.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell154.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell154.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell154 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell154.checked_sums hc
  · intro d hd
    have hi := cell154.checked_images hc hd hr
    simp only [cell154,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual211_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual99_1 hi).1
  · intro d hd
    have hi := cell154.checked_images hc hd hr
    simp only [cell154,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual211_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual99_1 hi).2
theorem actual155_bounds {r : ℝ} (hr : r∈Ioo (cell155.lo:ℝ) cell155.hi) :
    cell155.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell155.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell155.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell155.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell155 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell155.checked_sums hc
  · intro d hd
    have hi := cell155.checked_images hc hd hr
    simp only [cell155,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual211_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual100_1 hi).1
  · intro d hd
    have hi := cell155.checked_images hc hd hr
    simp only [cell155,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual211_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual100_1 hi).2
theorem actual156_bounds {r : ℝ} (hr : r∈Ioo (cell156.lo:ℝ) cell156.hi) :
    cell156.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell156.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell156.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell156.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell156 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell156.checked_sums hc
  · intro d hd
    have hi := cell156.checked_images hc hd hr
    simp only [cell156,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual211_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual101_1 hi).1
  · intro d hd
    have hi := cell156.checked_images hc hd hr
    simp only [cell156,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual211_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual101_1 hi).2
theorem actual157_bounds {r : ℝ} (hr : r∈Ioo (cell157.lo:ℝ) cell157.hi) :
    cell157.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell157.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell157.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell157.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell157 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell157.checked_sums hc
  · intro d hd
    have hi := cell157.checked_images hc hd hr
    simp only [cell157,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual212_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual101_1 hi).1
  · intro d hd
    have hi := cell157.checked_images hc hd hr
    simp only [cell157,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual212_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual101_1 hi).2
theorem actual158_bounds {r : ℝ} (hr : r∈Ioo (cell158.lo:ℝ) cell158.hi) :
    cell158.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell158.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell158.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell158.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell158 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell158.checked_sums hc
  · intro d hd
    have hi := cell158.checked_images hc hd hr
    simp only [cell158,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual212_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual102_1 hi).1
  · intro d hd
    have hi := cell158.checked_images hc hd hr
    simp only [cell158,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0016.actual212_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual102_1 hi).2
theorem actual159_bounds {r : ℝ} (hr : r∈Ioo (cell159.lo:ℝ) cell159.hi) :
    cell159.position.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell159.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.force d r)).sum) ∧
    cell159.weight.Contains ReferenceDensityData.CoarseLowerShape.scale ((cell159.components.map (fun d=>ReferenceDensityData.CoarseLowerShape.weight d r)).sum) := by
  have hc := List.all_eq_true.mp checked cell159 (by simp only [cells,List.mem_cons,List.mem_singleton]; tauto)
  apply cell159.checked_sums hc
  · intro d hd
    have hi := cell159.checked_images hc hd hr
    simp only [cell159,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0017.actual213_0 hi).1
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual102_1 hi).1
  · intro d hd
    have hi := cell159.checked_images hc hd hr
    simp only [cell159,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl | rfl
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0017.actual213_0 hi).2
    · exact (ReferenceDensityData.CoarseLowerShape.Batch0006.actual102_1 hi).2
theorem selected128_checked : cell128.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 128=true := by decide +kernel
theorem actual128_full_bounds {r : ℝ} (hr : r∈Ioo (cell128.lo:ℝ) cell128.hi) :
    cell128.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell128.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected128_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 128<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected128_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 128<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell128.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual128_bounds hr).1
  · change cell128.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual128_bounds hr).2
theorem selected129_checked : cell129.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 129=true := by decide +kernel
theorem actual129_full_bounds {r : ℝ} (hr : r∈Ioo (cell129.lo:ℝ) cell129.hi) :
    cell129.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell129.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected129_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 129<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected129_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 129<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell129.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual129_bounds hr).1
  · change cell129.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual129_bounds hr).2
theorem selected130_checked : cell130.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 130=true := by decide +kernel
theorem actual130_full_bounds {r : ℝ} (hr : r∈Ioo (cell130.lo:ℝ) cell130.hi) :
    cell130.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell130.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected130_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 130<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected130_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 130<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell130.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual130_bounds hr).1
  · change cell130.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual130_bounds hr).2
theorem selected131_checked : cell131.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 131=true := by decide +kernel
theorem actual131_full_bounds {r : ℝ} (hr : r∈Ioo (cell131.lo:ℝ) cell131.hi) :
    cell131.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell131.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected131_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 131<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected131_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 131<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell131.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual131_bounds hr).1
  · change cell131.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual131_bounds hr).2
theorem selected132_checked : cell132.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 132=true := by decide +kernel
theorem actual132_full_bounds {r : ℝ} (hr : r∈Ioo (cell132.lo:ℝ) cell132.hi) :
    cell132.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell132.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected132_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 132<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected132_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 132<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell132.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual132_bounds hr).1
  · change cell132.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual132_bounds hr).2
theorem selected133_checked : cell133.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 133=true := by decide +kernel
theorem actual133_full_bounds {r : ℝ} (hr : r∈Ioo (cell133.lo:ℝ) cell133.hi) :
    cell133.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell133.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected133_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 133<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected133_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 133<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell133.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual133_bounds hr).1
  · change cell133.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual133_bounds hr).2
theorem selected134_checked : cell134.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 134=true := by decide +kernel
theorem actual134_full_bounds {r : ℝ} (hr : r∈Ioo (cell134.lo:ℝ) cell134.hi) :
    cell134.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell134.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected134_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 134<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected134_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 134<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell134.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual134_bounds hr).1
  · change cell134.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual134_bounds hr).2
theorem selected135_checked : cell135.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 135=true := by decide +kernel
theorem actual135_full_bounds {r : ℝ} (hr : r∈Ioo (cell135.lo:ℝ) cell135.hi) :
    cell135.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell135.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected135_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 135<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected135_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 135<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell135.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual135_bounds hr).1
  · change cell135.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual135_bounds hr).2
theorem selected136_checked : cell136.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 136=true := by decide +kernel
theorem actual136_full_bounds {r : ℝ} (hr : r∈Ioo (cell136.lo:ℝ) cell136.hi) :
    cell136.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell136.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected136_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 136<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected136_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 136<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell136.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual136_bounds hr).1
  · change cell136.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual136_bounds hr).2
theorem selected137_checked : cell137.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 137=true := by decide +kernel
theorem actual137_full_bounds {r : ℝ} (hr : r∈Ioo (cell137.lo:ℝ) cell137.hi) :
    cell137.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell137.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected137_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 137<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected137_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 137<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell137.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual137_bounds hr).1
  · change cell137.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual137_bounds hr).2
theorem selected138_checked : cell138.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 138=true := by decide +kernel
theorem actual138_full_bounds {r : ℝ} (hr : r∈Ioo (cell138.lo:ℝ) cell138.hi) :
    cell138.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell138.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected138_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 138<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected138_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 138<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell138.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual138_bounds hr).1
  · change cell138.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual138_bounds hr).2
theorem selected139_checked : cell139.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 139=true := by decide +kernel
theorem actual139_full_bounds {r : ℝ} (hr : r∈Ioo (cell139.lo:ℝ) cell139.hi) :
    cell139.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell139.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected139_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 139<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected139_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 139<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell139.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual139_bounds hr).1
  · change cell139.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual139_bounds hr).2
theorem selected140_checked : cell140.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 140=true := by decide +kernel
theorem actual140_full_bounds {r : ℝ} (hr : r∈Ioo (cell140.lo:ℝ) cell140.hi) :
    cell140.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell140.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected140_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 140<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected140_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 140<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell140.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual140_bounds hr).1
  · change cell140.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual140_bounds hr).2
theorem selected141_checked : cell141.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 141=true := by decide +kernel
theorem actual141_full_bounds {r : ℝ} (hr : r∈Ioo (cell141.lo:ℝ) cell141.hi) :
    cell141.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell141.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected141_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 141<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected141_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 141<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell141.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual141_bounds hr).1
  · change cell141.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual141_bounds hr).2
theorem selected142_checked : cell142.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 142=true := by decide +kernel
theorem actual142_full_bounds {r : ℝ} (hr : r∈Ioo (cell142.lo:ℝ) cell142.hi) :
    cell142.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell142.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected142_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 142<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected142_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 142<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell142.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual142_bounds hr).1
  · change cell142.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual142_bounds hr).2
theorem selected143_checked : cell143.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 143=true := by decide +kernel
theorem actual143_full_bounds {r : ℝ} (hr : r∈Ioo (cell143.lo:ℝ) cell143.hi) :
    cell143.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell143.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected143_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 143<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected143_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 143<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell143.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual143_bounds hr).1
  · change cell143.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual143_bounds hr).2
theorem selected144_checked : cell144.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 144=true := by decide +kernel
theorem actual144_full_bounds {r : ℝ} (hr : r∈Ioo (cell144.lo:ℝ) cell144.hi) :
    cell144.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell144.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected144_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 144<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected144_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 144<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell144.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual144_bounds hr).1
  · change cell144.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual144_bounds hr).2
theorem selected145_checked : cell145.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 145=true := by decide +kernel
theorem actual145_full_bounds {r : ℝ} (hr : r∈Ioo (cell145.lo:ℝ) cell145.hi) :
    cell145.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell145.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected145_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 145<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected145_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 145<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell145.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual145_bounds hr).1
  · change cell145.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual145_bounds hr).2
theorem selected146_checked : cell146.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 146=true := by decide +kernel
theorem actual146_full_bounds {r : ℝ} (hr : r∈Ioo (cell146.lo:ℝ) cell146.hi) :
    cell146.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell146.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected146_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 146<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected146_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 146<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell146.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual146_bounds hr).1
  · change cell146.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual146_bounds hr).2
theorem selected147_checked : cell147.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 147=true := by decide +kernel
theorem actual147_full_bounds {r : ℝ} (hr : r∈Ioo (cell147.lo:ℝ) cell147.hi) :
    cell147.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell147.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected147_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 147<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected147_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 147<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell147.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual147_bounds hr).1
  · change cell147.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual147_bounds hr).2
theorem selected148_checked : cell148.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 148=true := by decide +kernel
theorem actual148_full_bounds {r : ℝ} (hr : r∈Ioo (cell148.lo:ℝ) cell148.hi) :
    cell148.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell148.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected148_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 148<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected148_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 148<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell148.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual148_bounds hr).1
  · change cell148.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual148_bounds hr).2
theorem selected149_checked : cell149.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 149=true := by decide +kernel
theorem actual149_full_bounds {r : ℝ} (hr : r∈Ioo (cell149.lo:ℝ) cell149.hi) :
    cell149.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell149.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected149_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 149<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected149_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 149<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell149.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual149_bounds hr).1
  · change cell149.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual149_bounds hr).2
theorem selected150_checked : cell150.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 150=true := by decide +kernel
theorem actual150_full_bounds {r : ℝ} (hr : r∈Ioo (cell150.lo:ℝ) cell150.hi) :
    cell150.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell150.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected150_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 150<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected150_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 150<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell150.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual150_bounds hr).1
  · change cell150.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual150_bounds hr).2
theorem selected151_checked : cell151.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 151=true := by decide +kernel
theorem actual151_full_bounds {r : ℝ} (hr : r∈Ioo (cell151.lo:ℝ) cell151.hi) :
    cell151.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell151.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected151_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 151<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected151_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 151<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell151.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual151_bounds hr).1
  · change cell151.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual151_bounds hr).2
theorem selected152_checked : cell152.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 152=true := by decide +kernel
theorem actual152_full_bounds {r : ℝ} (hr : r∈Ioo (cell152.lo:ℝ) cell152.hi) :
    cell152.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell152.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected152_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 152<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected152_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 152<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell152.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual152_bounds hr).1
  · change cell152.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual152_bounds hr).2
theorem selected153_checked : cell153.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 153=true := by decide +kernel
theorem actual153_full_bounds {r : ℝ} (hr : r∈Ioo (cell153.lo:ℝ) cell153.hi) :
    cell153.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell153.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected153_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 153<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected153_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 153<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell153.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual153_bounds hr).1
  · change cell153.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual153_bounds hr).2
theorem selected154_checked : cell154.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 154=true := by decide +kernel
theorem actual154_full_bounds {r : ℝ} (hr : r∈Ioo (cell154.lo:ℝ) cell154.hi) :
    cell154.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell154.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected154_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 154<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected154_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 154<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell154.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual154_bounds hr).1
  · change cell154.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual154_bounds hr).2
theorem selected155_checked : cell155.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 155=true := by decide +kernel
theorem actual155_full_bounds {r : ℝ} (hr : r∈Ioo (cell155.lo:ℝ) cell155.hi) :
    cell155.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell155.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected155_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 155<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected155_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 155<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell155.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual155_bounds hr).1
  · change cell155.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual155_bounds hr).2
theorem selected156_checked : cell156.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 156=true := by decide +kernel
theorem actual156_full_bounds {r : ℝ} (hr : r∈Ioo (cell156.lo:ℝ) cell156.hi) :
    cell156.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell156.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected156_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 156<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected156_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 156<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell156.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual156_bounds hr).1
  · change cell156.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual156_bounds hr).2
theorem selected157_checked : cell157.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 157=true := by decide +kernel
theorem actual157_full_bounds {r : ℝ} (hr : r∈Ioo (cell157.lo:ℝ) cell157.hi) :
    cell157.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell157.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected157_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 157<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected157_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 157<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell157.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual157_bounds hr).1
  · change cell157.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual157_bounds hr).2
theorem selected158_checked : cell158.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 158=true := by decide +kernel
theorem actual158_full_bounds {r : ℝ} (hr : r∈Ioo (cell158.lo:ℝ) cell158.hi) :
    cell158.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell158.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected158_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 158<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected158_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 158<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell158.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual158_bounds hr).1
  · change cell158.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual158_bounds hr).2
theorem selected159_checked : cell159.selectedCheck ReferenceOverlayGeometryData.CoarseLowerShape.segments ReferenceOverlayGeometryData.CoarseLowerShape.arrays 159=true := by decide +kernel
theorem actual159_full_bounds {r : ℝ} (hr : r∈Ioo (cell159.lo:ℝ) cell159.hi) :
    cell159.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧
    cell159.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  have hp := ReferenceOverlayCell.selectedCheck_density selected159_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 159<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr (ReferencePositionData.CoarseLowerShape.force 1) (ReferencePositionData.CoarseLowerShape.force 2)
  have hw := ReferenceOverlayCell.selectedCheck_density selected159_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.geometry_checked
    ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.r_frame_checked ReferenceOverlayGeometryData.CoarseLowerShape.Assembly.a_frame_checked
    (by decide +kernel : 159<ReferenceOverlayGeometryData.CoarseLowerShape.arrays.cellCount) hr
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 0 z+ReferenceAdjointData.CoarseLowerShape.weight 2 z)
    (fun z=>ReferenceAdjointData.CoarseLowerShape.weight 1 z+ReferenceAdjointData.CoarseLowerShape.weight 3 z)
  change _ ∧ _
  constructor
  · change cell159.position.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.f _ _ _ r)
    rw [Transport.f,hp]
    exact (actual159_bounds hr).1
  · change cell159.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (Transport.W _ _ _ r)
    rw [Transport.W,hw]
    exact (actual159_bounds hr).2
theorem actual_flux_bounds : ∀ c∈ReferenceFluxData.CoarseLowerShape.Batch0004.cells,∀ r∈Ioo (c.interval.lo:ℝ) c.interval.hi,
    c.position.Contains ReferenceDensityData.CoarseLowerShape.scale (force r) ∧ c.weight.Contains ReferenceDensityData.CoarseLowerShape.scale (weight r) := by
  intro c hc r hr
  simp only [ReferenceFluxData.CoarseLowerShape.Batch0004.cells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact actual128_full_bounds hr
  · exact actual129_full_bounds hr
  · exact actual130_full_bounds hr
  · exact actual131_full_bounds hr
  · exact actual132_full_bounds hr
  · exact actual133_full_bounds hr
  · exact actual134_full_bounds hr
  · exact actual135_full_bounds hr
  · exact actual136_full_bounds hr
  · exact actual137_full_bounds hr
  · exact actual138_full_bounds hr
  · exact actual139_full_bounds hr
  · exact actual140_full_bounds hr
  · exact actual141_full_bounds hr
  · exact actual142_full_bounds hr
  · exact actual143_full_bounds hr
  · exact actual144_full_bounds hr
  · exact actual145_full_bounds hr
  · exact actual146_full_bounds hr
  · exact actual147_full_bounds hr
  · exact actual148_full_bounds hr
  · exact actual149_full_bounds hr
  · exact actual150_full_bounds hr
  · exact actual151_full_bounds hr
  · exact actual152_full_bounds hr
  · exact actual153_full_bounds hr
  · exact actual154_full_bounds hr
  · exact actual155_full_bounds hr
  · exact actual156_full_bounds hr
  · exact actual157_full_bounds hr
  · exact actual158_full_bounds hr
  · exact actual159_full_bounds hr
end OptimalG.Certificates.ReferenceOverlayData.CoarseLowerShape.Batch0004
