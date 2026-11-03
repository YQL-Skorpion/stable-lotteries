import OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Bundle0040_0043
import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Assembly
namespace OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Assembly
open Set MeasureTheory Transport
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def batches : List (List (ReferenceScalarCell×HessianCell)) := [Batch0000.sources,Batch0001.sources,Batch0002.sources,Batch0003.sources,Batch0004.sources,Batch0005.sources,Batch0006.sources,Batch0007.sources,Batch0008.sources,Batch0009.sources,Batch0010.sources,Batch0011.sources,Batch0012.sources,Batch0013.sources,Batch0014.sources,Batch0015.sources,Batch0016.sources,Batch0017.sources,Batch0018.sources,Batch0019.sources,Batch0020.sources,Batch0021.sources,Batch0022.sources,Batch0023.sources,Batch0024.sources,Batch0025.sources,Batch0026.sources,Batch0027.sources,Batch0028.sources,Batch0029.sources,Batch0030.sources,Batch0031.sources,Batch0032.sources,Batch0033.sources,Batch0034.sources,Batch0035.sources,Batch0036.sources,Batch0037.sources,Batch0038.sources,Batch0039.sources,Batch0040.sources,Batch0041.sources,Batch0042.sources,Batch0043.sources]
def sources : List (ReferenceScalarCell×HessianCell) := batches.flatten
theorem source_cells : sources.map (fun p=>p.1.flow)=ReferenceActualData.CoarseLowerShape.cells := by
  simp only [sources,batches,ReferenceActualData.CoarseLowerShape.cells,ReferenceActualData.CoarseLowerShape.certificates,ReferenceSensitivityData.CoarseLowerShape.Assembly.certificates,ReferenceSensitivityData.CoarseLowerShape.Assembly.batches,List.map_flatten,List.map_cons,List.map_nil,Batch0000.sources_cells,Batch0001.sources_cells,Batch0002.sources_cells,Batch0003.sources_cells,Batch0004.sources_cells,Batch0005.sources_cells,Batch0006.sources_cells,Batch0007.sources_cells,Batch0008.sources_cells,Batch0009.sources_cells,Batch0010.sources_cells,Batch0011.sources_cells,Batch0012.sources_cells,Batch0013.sources_cells,Batch0014.sources_cells,Batch0015.sources_cells,Batch0016.sources_cells,Batch0017.sources_cells,Batch0018.sources_cells,Batch0019.sources_cells,Batch0020.sources_cells,Batch0021.sources_cells,Batch0022.sources_cells,Batch0023.sources_cells,Batch0024.sources_cells,Batch0025.sources_cells,Batch0026.sources_cells,Batch0027.sources_cells,Batch0028.sources_cells,Batch0029.sources_cells,Batch0030.sources_cells,Batch0031.sources_cells,Batch0032.sources_cells,Batch0033.sources_cells,Batch0034.sources_cells,Batch0035.sources_cells,Batch0036.sources_cells,Batch0037.sources_cells,Batch0038.sources_cells,Batch0039.sources_cells,Batch0040.sources_cells,Batch0041.sources_cells,Batch0042.sources_cells,Batch0043.sources_cells]
theorem source_hessians : sources.map Prod.snd=TransportHessianData.CoarseLowerShapeFlow.cells := by
  simp only [sources,batches,TransportHessianData.CoarseLowerShapeFlow.cells,TransportHessianData.CoarseLowerShapeFlow.batches,List.map_flatten,List.map_cons,List.map_nil,Batch0000.sources_hessians,Batch0001.sources_hessians,Batch0002.sources_hessians,Batch0003.sources_hessians,Batch0004.sources_hessians,Batch0005.sources_hessians,Batch0006.sources_hessians,Batch0007.sources_hessians,Batch0008.sources_hessians,Batch0009.sources_hessians,Batch0010.sources_hessians,Batch0011.sources_hessians,Batch0012.sources_hessians,Batch0013.sources_hessians,Batch0014.sources_hessians,Batch0015.sources_hessians,Batch0016.sources_hessians,Batch0017.sources_hessians,Batch0018.sources_hessians,Batch0019.sources_hessians,Batch0020.sources_hessians,Batch0021.sources_hessians,Batch0022.sources_hessians,Batch0023.sources_hessians,Batch0024.sources_hessians,Batch0025.sources_hessians,Batch0026.sources_hessians,Batch0027.sources_hessians,Batch0028.sources_hessians,Batch0029.sources_hessians,Batch0030.sources_hessians,Batch0031.sources_hessians,Batch0032.sources_hessians,Batch0033.sources_hessians,Batch0034.sources_hessians,Batch0035.sources_hessians,Batch0036.sources_hessians,Batch0037.sources_hessians,Batch0038.sources_hessians,Batch0039.sources_hessians,Batch0040.sources_hessians,Batch0041.sources_hessians,Batch0042.sources_hessians,Batch0043.sources_hessians]
theorem actual_frames : ∀ p∈sources,∀ z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z,
    ∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ) := by
  intro p hp
  obtain ⟨batch,hbatch,hp⟩ := List.mem_flatten.mp hp
  simp only [batches,List.mem_cons,List.not_mem_nil,or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.actual_frames p hp
  · exact Batch0001.actual_frames p hp
  · exact Batch0002.actual_frames p hp
  · exact Batch0003.actual_frames p hp
  · exact Batch0004.actual_frames p hp
  · exact Batch0005.actual_frames p hp
  · exact Batch0006.actual_frames p hp
  · exact Batch0007.actual_frames p hp
  · exact Batch0008.actual_frames p hp
  · exact Batch0009.actual_frames p hp
  · exact Batch0010.actual_frames p hp
  · exact Batch0011.actual_frames p hp
  · exact Batch0012.actual_frames p hp
  · exact Batch0013.actual_frames p hp
  · exact Batch0014.actual_frames p hp
  · exact Batch0015.actual_frames p hp
  · exact Batch0016.actual_frames p hp
  · exact Batch0017.actual_frames p hp
  · exact Batch0018.actual_frames p hp
  · exact Batch0019.actual_frames p hp
  · exact Batch0020.actual_frames p hp
  · exact Batch0021.actual_frames p hp
  · exact Batch0022.actual_frames p hp
  · exact Batch0023.actual_frames p hp
  · exact Batch0024.actual_frames p hp
  · exact Batch0025.actual_frames p hp
  · exact Batch0026.actual_frames p hp
  · exact Batch0027.actual_frames p hp
  · exact Batch0028.actual_frames p hp
  · exact Batch0029.actual_frames p hp
  · exact Batch0030.actual_frames p hp
  · exact Batch0031.actual_frames p hp
  · exact Batch0032.actual_frames p hp
  · exact Batch0033.actual_frames p hp
  · exact Batch0034.actual_frames p hp
  · exact Batch0035.actual_frames p hp
  · exact Batch0036.actual_frames p hp
  · exact Batch0037.actual_frames p hp
  · exact Batch0038.actual_frames p hp
  · exact Batch0039.actual_frames p hp
  · exact Batch0040.actual_frames p hp
  · exact Batch0041.actual_frames p hp
  · exact Batch0042.actual_frames p hp
  · exact Batch0043.actual_frames p hp
theorem source_geometry : ∀ p∈sources,
    p.1.params=TransportHessianData.CoarseLowerShapeFlow.params ∧ p.1.flow.late=p.2.late ∧ p.1.flow.segment.left.z=p.2.zLo ∧ p.1.flow.segment.right.z=p.2.zHi := by
  intro p hp
  obtain ⟨batch,hbatch,hp⟩ := List.mem_flatten.mp hp
  simp only [batches,List.mem_cons,List.not_mem_nil,or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.source_geometry p hp
  · exact Batch0001.source_geometry p hp
  · exact Batch0002.source_geometry p hp
  · exact Batch0003.source_geometry p hp
  · exact Batch0004.source_geometry p hp
  · exact Batch0005.source_geometry p hp
  · exact Batch0006.source_geometry p hp
  · exact Batch0007.source_geometry p hp
  · exact Batch0008.source_geometry p hp
  · exact Batch0009.source_geometry p hp
  · exact Batch0010.source_geometry p hp
  · exact Batch0011.source_geometry p hp
  · exact Batch0012.source_geometry p hp
  · exact Batch0013.source_geometry p hp
  · exact Batch0014.source_geometry p hp
  · exact Batch0015.source_geometry p hp
  · exact Batch0016.source_geometry p hp
  · exact Batch0017.source_geometry p hp
  · exact Batch0018.source_geometry p hp
  · exact Batch0019.source_geometry p hp
  · exact Batch0020.source_geometry p hp
  · exact Batch0021.source_geometry p hp
  · exact Batch0022.source_geometry p hp
  · exact Batch0023.source_geometry p hp
  · exact Batch0024.source_geometry p hp
  · exact Batch0025.source_geometry p hp
  · exact Batch0026.source_geometry p hp
  · exact Batch0027.source_geometry p hp
  · exact Batch0028.source_geometry p hp
  · exact Batch0029.source_geometry p hp
  · exact Batch0030.source_geometry p hp
  · exact Batch0031.source_geometry p hp
  · exact Batch0032.source_geometry p hp
  · exact Batch0033.source_geometry p hp
  · exact Batch0034.source_geometry p hp
  · exact Batch0035.source_geometry p hp
  · exact Batch0036.source_geometry p hp
  · exact Batch0037.source_geometry p hp
  · exact Batch0038.source_geometry p hp
  · exact Batch0039.source_geometry p hp
  · exact Batch0040.source_geometry p hp
  · exact Batch0041.source_geometry p hp
  · exact Batch0042.source_geometry p hp
  · exact Batch0043.source_geometry p hp
theorem matched_endpoints : ∀ p∈sources,∀ (S : ℝ) (J : ℝ→ℝ),Compact.LambdaRange p.1.flow.lam → S≤(3:ℝ)/100 →
    (∀ r∈Set.Icc (p.1.leftContact:ℝ) p.1.rightContact,quadratic p.1.flow.lam r-S≤J r ∧ J r≤cap p.1.flow.lam S r) →
    ReferenceProfileData.CoarseLowerShape.scalarBox.Contains ReferenceSensitivityData.CoarseLowerShape.scale S →
    ∀ t∈Icc (0:ℝ) 1,∀ r a,p.1.primitiveMatch true S J t r → p.1.primitiveMatch false S J t a →
    (if p.1.flow.late then a≤r else r≤a) →
    (p.2.fixed 0).Contains ReferenceSensitivityData.CoarseLowerShape.scale r ∧ (p.2.fixed 1).Contains ReferenceSensitivityData.CoarseLowerShape.scale a := by
  intro p hp
  obtain ⟨batch,hbatch,hp⟩ := List.mem_flatten.mp hp
  simp only [batches,List.mem_cons,List.not_mem_nil,or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.matched_endpoints p hp
  · exact Batch0001.matched_endpoints p hp
  · exact Batch0002.matched_endpoints p hp
  · exact Batch0003.matched_endpoints p hp
  · exact Batch0004.matched_endpoints p hp
  · exact Batch0005.matched_endpoints p hp
  · exact Batch0006.matched_endpoints p hp
  · exact Batch0007.matched_endpoints p hp
  · exact Batch0008.matched_endpoints p hp
  · exact Batch0009.matched_endpoints p hp
  · exact Batch0010.matched_endpoints p hp
  · exact Batch0011.matched_endpoints p hp
  · exact Batch0012.matched_endpoints p hp
  · exact Batch0013.matched_endpoints p hp
  · exact Batch0014.matched_endpoints p hp
  · exact Batch0015.matched_endpoints p hp
  · exact Batch0016.matched_endpoints p hp
  · exact Batch0017.matched_endpoints p hp
  · exact Batch0018.matched_endpoints p hp
  · exact Batch0019.matched_endpoints p hp
  · exact Batch0020.matched_endpoints p hp
  · exact Batch0021.matched_endpoints p hp
  · exact Batch0022.matched_endpoints p hp
  · exact Batch0023.matched_endpoints p hp
  · exact Batch0024.matched_endpoints p hp
  · exact Batch0025.matched_endpoints p hp
  · exact Batch0026.matched_endpoints p hp
  · exact Batch0027.matched_endpoints p hp
  · exact Batch0028.matched_endpoints p hp
  · exact Batch0029.matched_endpoints p hp
  · exact Batch0030.matched_endpoints p hp
  · exact Batch0031.matched_endpoints p hp
  · exact Batch0032.matched_endpoints p hp
  · exact Batch0033.matched_endpoints p hp
  · exact Batch0034.matched_endpoints p hp
  · exact Batch0035.matched_endpoints p hp
  · exact Batch0036.matched_endpoints p hp
  · exact Batch0037.matched_endpoints p hp
  · exact Batch0038.matched_endpoints p hp
  · exact Batch0039.matched_endpoints p hp
  · exact Batch0040.matched_endpoints p hp
  · exact Batch0041.matched_endpoints p hp
  · exact Batch0042.matched_endpoints p hp
  · exact Batch0043.matched_endpoints p hp
theorem rank_crop_checked : sources.all (fun p=>p.1.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact true && p.1.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact false)=true := by
  simp only [sources,batches,List.all_flatten,List.all_cons,List.all_nil,Batch0000.rank_crop_checked,Batch0001.rank_crop_checked,Batch0002.rank_crop_checked,Batch0003.rank_crop_checked,Batch0004.rank_crop_checked,Batch0005.rank_crop_checked,Batch0006.rank_crop_checked,Batch0007.rank_crop_checked,Batch0008.rank_crop_checked,Batch0009.rank_crop_checked,Batch0010.rank_crop_checked,Batch0011.rank_crop_checked,Batch0012.rank_crop_checked,Batch0013.rank_crop_checked,Batch0014.rank_crop_checked,Batch0015.rank_crop_checked,Batch0016.rank_crop_checked,Batch0017.rank_crop_checked,Batch0018.rank_crop_checked,Batch0019.rank_crop_checked,Batch0020.rank_crop_checked,Batch0021.rank_crop_checked,Batch0022.rank_crop_checked,Batch0023.rank_crop_checked,Batch0024.rank_crop_checked,Batch0025.rank_crop_checked,Batch0026.rank_crop_checked,Batch0027.rank_crop_checked,Batch0028.rank_crop_checked,Batch0029.rank_crop_checked,Batch0030.rank_crop_checked,Batch0031.rank_crop_checked,Batch0032.rank_crop_checked,Batch0033.rank_crop_checked,Batch0034.rank_crop_checked,Batch0035.rank_crop_checked,Batch0036.rank_crop_checked,Batch0037.rank_crop_checked,Batch0038.rank_crop_checked,Batch0039.rank_crop_checked,Batch0040.rank_crop_checked,Batch0041.rank_crop_checked,Batch0042.rank_crop_checked,Batch0043.rank_crop_checked,Bool.true_and]
theorem rank_lower_checked : sources.all (fun p=>decide ((1/4:ℚ)≤p.1.flow.segment.left.r))=true := by
  simp only [sources,batches,List.all_flatten,List.all_cons,List.all_nil,Batch0000.rank_lower_checked,Batch0001.rank_lower_checked,Batch0002.rank_lower_checked,Batch0003.rank_lower_checked,Batch0004.rank_lower_checked,Batch0005.rank_lower_checked,Batch0006.rank_lower_checked,Batch0007.rank_lower_checked,Batch0008.rank_lower_checked,Batch0009.rank_lower_checked,Batch0010.rank_lower_checked,Batch0011.rank_lower_checked,Batch0012.rank_lower_checked,Batch0013.rank_lower_checked,Batch0014.rank_lower_checked,Batch0015.rank_lower_checked,Batch0016.rank_lower_checked,Batch0017.rank_lower_checked,Batch0018.rank_lower_checked,Batch0019.rank_lower_checked,Batch0020.rank_lower_checked,Batch0021.rank_lower_checked,Batch0022.rank_lower_checked,Batch0023.rank_lower_checked,Batch0024.rank_lower_checked,Batch0025.rank_lower_checked,Batch0026.rank_lower_checked,Batch0027.rank_lower_checked,Batch0028.rank_lower_checked,Batch0029.rank_lower_checked,Batch0030.rank_lower_checked,Batch0031.rank_lower_checked,Batch0032.rank_lower_checked,Batch0033.rank_lower_checked,Batch0034.rank_lower_checked,Batch0035.rank_lower_checked,Batch0036.rank_lower_checked,Batch0037.rank_lower_checked,Batch0038.rank_lower_checked,Batch0039.rank_lower_checked,Batch0040.rank_lower_checked,Batch0041.rank_lower_checked,Batch0042.rank_lower_checked,Batch0043.rank_lower_checked,Bool.true_and]
theorem branches_checked : sources.all (fun p=>p.1.branchGeometryCheck TransportReferenceData.CoarseLowerShape.data.leftContact)=true := by
  simp only [sources,batches,List.all_flatten,List.all_cons,List.all_nil,Batch0000.branches_checked,Batch0001.branches_checked,Batch0002.branches_checked,Batch0003.branches_checked,Batch0004.branches_checked,Batch0005.branches_checked,Batch0006.branches_checked,Batch0007.branches_checked,Batch0008.branches_checked,Batch0009.branches_checked,Batch0010.branches_checked,Batch0011.branches_checked,Batch0012.branches_checked,Batch0013.branches_checked,Batch0014.branches_checked,Batch0015.branches_checked,Batch0016.branches_checked,Batch0017.branches_checked,Batch0018.branches_checked,Batch0019.branches_checked,Batch0020.branches_checked,Batch0021.branches_checked,Batch0022.branches_checked,Batch0023.branches_checked,Batch0024.branches_checked,Batch0025.branches_checked,Batch0026.branches_checked,Batch0027.branches_checked,Batch0028.branches_checked,Batch0029.branches_checked,Batch0030.branches_checked,Batch0031.branches_checked,Batch0032.branches_checked,Batch0033.branches_checked,Batch0034.branches_checked,Batch0035.branches_checked,Batch0036.branches_checked,Batch0037.branches_checked,Batch0038.branches_checked,Batch0039.branches_checked,Batch0040.branches_checked,Batch0041.branches_checked,Batch0042.branches_checked,Batch0043.branches_checked,Bool.true_and]
theorem source_rank_frames : ∀ p∈sources,∀ useR : Bool,∃ bounds : ReferenceProfileBox,
    (p.1.rankProfile useR bounds).frameCheck TransportReferenceData.CoarseLowerShape.data=true ∧
    (p.1.rankProfile useR bounds).lo≤(p.1.rankProfile useR bounds).hi := by
  intro p hp
  obtain ⟨batch,hbatch,hp⟩ := List.mem_flatten.mp hp
  simp only [batches,List.mem_cons,List.not_mem_nil,or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.source_rank_frames p hp
  · exact Batch0001.source_rank_frames p hp
  · exact Batch0002.source_rank_frames p hp
  · exact Batch0003.source_rank_frames p hp
  · exact Batch0004.source_rank_frames p hp
  · exact Batch0005.source_rank_frames p hp
  · exact Batch0006.source_rank_frames p hp
  · exact Batch0007.source_rank_frames p hp
  · exact Batch0008.source_rank_frames p hp
  · exact Batch0009.source_rank_frames p hp
  · exact Batch0010.source_rank_frames p hp
  · exact Batch0011.source_rank_frames p hp
  · exact Batch0012.source_rank_frames p hp
  · exact Batch0013.source_rank_frames p hp
  · exact Batch0014.source_rank_frames p hp
  · exact Batch0015.source_rank_frames p hp
  · exact Batch0016.source_rank_frames p hp
  · exact Batch0017.source_rank_frames p hp
  · exact Batch0018.source_rank_frames p hp
  · exact Batch0019.source_rank_frames p hp
  · exact Batch0020.source_rank_frames p hp
  · exact Batch0021.source_rank_frames p hp
  · exact Batch0022.source_rank_frames p hp
  · exact Batch0023.source_rank_frames p hp
  · exact Batch0024.source_rank_frames p hp
  · exact Batch0025.source_rank_frames p hp
  · exact Batch0026.source_rank_frames p hp
  · exact Batch0027.source_rank_frames p hp
  · exact Batch0028.source_rank_frames p hp
  · exact Batch0029.source_rank_frames p hp
  · exact Batch0030.source_rank_frames p hp
  · exact Batch0031.source_rank_frames p hp
  · exact Batch0032.source_rank_frames p hp
  · exact Batch0033.source_rank_frames p hp
  · exact Batch0034.source_rank_frames p hp
  · exact Batch0035.source_rank_frames p hp
  · exact Batch0036.source_rank_frames p hp
  · exact Batch0037.source_rank_frames p hp
  · exact Batch0038.source_rank_frames p hp
  · exact Batch0039.source_rank_frames p hp
  · exact Batch0040.source_rank_frames p hp
  · exact Batch0041.source_rank_frames p hp
  · exact Batch0042.source_rank_frames p hp
  · exact Batch0043.source_rank_frames p hp
theorem source_scalar : ∀ p∈sources,ReferenceSensitivityData.CoarseLowerShape.makeCell p.1.flow=p.1 := by
  intro p hp
  obtain ⟨batch,hbatch,hp⟩ := List.mem_flatten.mp hp
  simp only [batches,List.mem_cons,List.not_mem_nil,or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.source_scalar p hp
  · exact Batch0001.source_scalar p hp
  · exact Batch0002.source_scalar p hp
  · exact Batch0003.source_scalar p hp
  · exact Batch0004.source_scalar p hp
  · exact Batch0005.source_scalar p hp
  · exact Batch0006.source_scalar p hp
  · exact Batch0007.source_scalar p hp
  · exact Batch0008.source_scalar p hp
  · exact Batch0009.source_scalar p hp
  · exact Batch0010.source_scalar p hp
  · exact Batch0011.source_scalar p hp
  · exact Batch0012.source_scalar p hp
  · exact Batch0013.source_scalar p hp
  · exact Batch0014.source_scalar p hp
  · exact Batch0015.source_scalar p hp
  · exact Batch0016.source_scalar p hp
  · exact Batch0017.source_scalar p hp
  · exact Batch0018.source_scalar p hp
  · exact Batch0019.source_scalar p hp
  · exact Batch0020.source_scalar p hp
  · exact Batch0021.source_scalar p hp
  · exact Batch0022.source_scalar p hp
  · exact Batch0023.source_scalar p hp
  · exact Batch0024.source_scalar p hp
  · exact Batch0025.source_scalar p hp
  · exact Batch0026.source_scalar p hp
  · exact Batch0027.source_scalar p hp
  · exact Batch0028.source_scalar p hp
  · exact Batch0029.source_scalar p hp
  · exact Batch0030.source_scalar p hp
  · exact Batch0031.source_scalar p hp
  · exact Batch0032.source_scalar p hp
  · exact Batch0033.source_scalar p hp
  · exact Batch0034.source_scalar p hp
  · exact Batch0035.source_scalar p hp
  · exact Batch0036.source_scalar p hp
  · exact Batch0037.source_scalar p hp
  · exact Batch0038.source_scalar p hp
  · exact Batch0039.source_scalar p hp
  · exact Batch0040.source_scalar p hp
  · exact Batch0041.source_scalar p hp
  · exact Batch0042.source_scalar p hp
  · exact Batch0043.source_scalar p hp
theorem source_support_geometry {p : ReferenceScalarCell×HessianCell} (hp : p∈sources) :
    p.1.SupportGeometry TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact := by
  have hc := Bool.and_eq_true_iff.mp (List.all_eq_true.mp rank_crop_checked p hp)
  apply ReferenceScalarCell.supportGeometry_of_checks (List.all_eq_true.mp branches_checked p hp) hc.1 hc.2
    (of_decide_eq_true (List.all_eq_true.mp rank_lower_checked p hp))
  apply (referenceFlowCoverCheck_bounds ReferenceActualData.CoarseLowerShape.cover_checked _).2.1
  rw [←source_cells]; exact List.mem_map.mpr ⟨p,hp,rfl⟩
theorem source_checked {p : ReferenceScalarCell×HessianCell} (hp : p∈sources) : p.2.checkClean TransportHessianData.CoarseLowerShapeFlow.scale TransportHessianData.CoarseLowerShapeFlow.params TransportHessianData.CoarseLowerShapeFlow.slabs=true := by
  apply List.all_eq_true.mp TransportHessianData.CoarseLowerShapeFlow.all_checked p.2
  rw [←source_hessians]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩
theorem selected_actual_frame {z : ℝ} (hz : z∈Ioc (ReferenceActualData.CoarseLowerShape.start:ℝ) ReferenceActualData.CoarseLowerShape.finish) :
    ∃ p∈sources,z∈Ioc (p.1.flow.segment.left.z:ℝ) p.1.flow.segment.right.z ∧
      (∀ j,(p.2.fixed j).Contains ReferenceSensitivityData.CoarseLowerShape.scale (p.1.weightedInput (p.1.flow.timeParameter z) (fun i=>ReferenceAdjointData.CoarseLowerShape.weight i z) j.succ)) := by
  obtain ⟨flow,hflow,_,hzflow,_⟩ := referenceField_selected ReferenceFlowCell.actualAlpha ReferenceActualData.CoarseLowerShape.cover_checked hz
  rw [←source_cells] at hflow
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hflow
  exact ⟨p,hp,hzflow,actual_frames p hp z hzflow⟩
end OptimalG.Certificates.ReferenceTimeData.CoarseLowerShape.Assembly
