import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0085_0086
namespace OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Assembly
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def certificates : List Transport.ReferenceWeightCertificate := [Batch0000.certificates,Batch0001.certificates,Batch0002.certificates,Batch0003.certificates,Batch0004.certificates,Batch0005.certificates,Batch0006.certificates,Batch0007.certificates,Batch0008.certificates,Batch0009.certificates,Batch0010.certificates,Batch0011.certificates,Batch0012.certificates,Batch0013.certificates,Batch0014.certificates,Batch0015.certificates,Batch0016.certificates,Batch0017.certificates,Batch0018.certificates,Batch0019.certificates,Batch0020.certificates,Batch0021.certificates,Batch0022.certificates,Batch0023.certificates,Batch0024.certificates,Batch0025.certificates,Batch0026.certificates,Batch0027.certificates,Batch0028.certificates,Batch0029.certificates,Batch0030.certificates,Batch0031.certificates,Batch0032.certificates,Batch0033.certificates,Batch0034.certificates,Batch0035.certificates,Batch0036.certificates,Batch0037.certificates,Batch0038.certificates,Batch0039.certificates,Batch0040.certificates,Batch0041.certificates,Batch0042.certificates,Batch0043.certificates,Batch0044.certificates,Batch0045.certificates,Batch0046.certificates,Batch0047.certificates,Batch0048.certificates,Batch0049.certificates,Batch0050.certificates,Batch0051.certificates,Batch0052.certificates,Batch0053.certificates,Batch0054.certificates,Batch0055.certificates,Batch0056.certificates,Batch0057.certificates,Batch0058.certificates,Batch0059.certificates,Batch0060.certificates,Batch0061.certificates,Batch0062.certificates,Batch0063.certificates,Batch0064.certificates,Batch0065.certificates,Batch0066.certificates,Batch0067.certificates,Batch0068.certificates,Batch0069.certificates,Batch0070.certificates,Batch0071.certificates,Batch0072.certificates,Batch0073.certificates,Batch0074.certificates,Batch0075.certificates,Batch0076.certificates,Batch0077.certificates,Batch0078.certificates,Batch0079.certificates,Batch0080.certificates,Batch0081.certificates,Batch0082.certificates,Batch0083.certificates,Batch0084.certificates,Batch0085.certificates,Batch0086.certificates].flatten
theorem checked : certificates.all (fun c => c.checkWithError scale multiplier ((c.cell.flow.segment.right.z-c.start)/500000))=true := by
  simp only [certificates,List.all_flatten,List.all_cons,List.all_nil,Batch0000.checked,Batch0001.checked,Batch0002.checked,Batch0003.checked,Batch0004.checked,Batch0005.checked,Batch0006.checked,Batch0007.checked,Batch0008.checked,Batch0009.checked,Batch0010.checked,Batch0011.checked,Batch0012.checked,Batch0013.checked,Batch0014.checked,Batch0015.checked,Batch0016.checked,Batch0017.checked,Batch0018.checked,Batch0019.checked,Batch0020.checked,Batch0021.checked,Batch0022.checked,Batch0023.checked,Batch0024.checked,Batch0025.checked,Batch0026.checked,Batch0027.checked,Batch0028.checked,Batch0029.checked,Batch0030.checked,Batch0031.checked,Batch0032.checked,Batch0033.checked,Batch0034.checked,Batch0035.checked,Batch0036.checked,Batch0037.checked,Batch0038.checked,Batch0039.checked,Batch0040.checked,Batch0041.checked,Batch0042.checked,Batch0043.checked,Batch0044.checked,Batch0045.checked,Batch0046.checked,Batch0047.checked,Batch0048.checked,Batch0049.checked,Batch0050.checked,Batch0051.checked,Batch0052.checked,Batch0053.checked,Batch0054.checked,Batch0055.checked,Batch0056.checked,Batch0057.checked,Batch0058.checked,Batch0059.checked,Batch0060.checked,Batch0061.checked,Batch0062.checked,Batch0063.checked,Batch0064.checked,Batch0065.checked,Batch0066.checked,Batch0067.checked,Batch0068.checked,Batch0069.checked,Batch0070.checked,Batch0071.checked,Batch0072.checked,Batch0073.checked,Batch0074.checked,Batch0075.checked,Batch0076.checked,Batch0077.checked,Batch0078.checked,Batch0079.checked,Batch0080.checked,Batch0081.checked,Batch0082.checked,Batch0083.checked,Batch0084.checked,Batch0085.checked,Batch0086.checked,Bool.true_and]
theorem terminals_checked : certificates.all (fun c=>decide (c.cell.terminal=terminal))=true := by
  simp only [certificates,List.all_flatten,List.all_cons,List.all_nil,Batch0000.terminals_checked,Batch0001.terminals_checked,Batch0002.terminals_checked,Batch0003.terminals_checked,Batch0004.terminals_checked,Batch0005.terminals_checked,Batch0006.terminals_checked,Batch0007.terminals_checked,Batch0008.terminals_checked,Batch0009.terminals_checked,Batch0010.terminals_checked,Batch0011.terminals_checked,Batch0012.terminals_checked,Batch0013.terminals_checked,Batch0014.terminals_checked,Batch0015.terminals_checked,Batch0016.terminals_checked,Batch0017.terminals_checked,Batch0018.terminals_checked,Batch0019.terminals_checked,Batch0020.terminals_checked,Batch0021.terminals_checked,Batch0022.terminals_checked,Batch0023.terminals_checked,Batch0024.terminals_checked,Batch0025.terminals_checked,Batch0026.terminals_checked,Batch0027.terminals_checked,Batch0028.terminals_checked,Batch0029.terminals_checked,Batch0030.terminals_checked,Batch0031.terminals_checked,Batch0032.terminals_checked,Batch0033.terminals_checked,Batch0034.terminals_checked,Batch0035.terminals_checked,Batch0036.terminals_checked,Batch0037.terminals_checked,Batch0038.terminals_checked,Batch0039.terminals_checked,Batch0040.terminals_checked,Batch0041.terminals_checked,Batch0042.terminals_checked,Batch0043.terminals_checked,Batch0044.terminals_checked,Batch0045.terminals_checked,Batch0046.terminals_checked,Batch0047.terminals_checked,Batch0048.terminals_checked,Batch0049.terminals_checked,Batch0050.terminals_checked,Batch0051.terminals_checked,Batch0052.terminals_checked,Batch0053.terminals_checked,Batch0054.terminals_checked,Batch0055.terminals_checked,Batch0056.terminals_checked,Batch0057.terminals_checked,Batch0058.terminals_checked,Batch0059.terminals_checked,Batch0060.terminals_checked,Batch0061.terminals_checked,Batch0062.terminals_checked,Batch0063.terminals_checked,Batch0064.terminals_checked,Batch0065.terminals_checked,Batch0066.terminals_checked,Batch0067.terminals_checked,Batch0068.terminals_checked,Batch0069.terminals_checked,Batch0070.terminals_checked,Batch0071.terminals_checked,Batch0072.terminals_checked,Batch0073.terminals_checked,Batch0074.terminals_checked,Batch0075.terminals_checked,Batch0076.terminals_checked,Batch0077.terminals_checked,Batch0078.terminals_checked,Batch0079.terminals_checked,Batch0080.terminals_checked,Batch0081.terminals_checked,Batch0082.terminals_checked,Batch0083.terminals_checked,Batch0084.terminals_checked,Batch0085.terminals_checked,Batch0086.terminals_checked,Bool.true_and]
theorem positivity_checked : certificates.all (fun c=>c.cell.positivityCheck)=true := by
  simp only [certificates,List.all_flatten,List.all_cons,List.all_nil,Batch0000.positivity_checked,Batch0001.positivity_checked,Batch0002.positivity_checked,Batch0003.positivity_checked,Batch0004.positivity_checked,Batch0005.positivity_checked,Batch0006.positivity_checked,Batch0007.positivity_checked,Batch0008.positivity_checked,Batch0009.positivity_checked,Batch0010.positivity_checked,Batch0011.positivity_checked,Batch0012.positivity_checked,Batch0013.positivity_checked,Batch0014.positivity_checked,Batch0015.positivity_checked,Batch0016.positivity_checked,Batch0017.positivity_checked,Batch0018.positivity_checked,Batch0019.positivity_checked,Batch0020.positivity_checked,Batch0021.positivity_checked,Batch0022.positivity_checked,Batch0023.positivity_checked,Batch0024.positivity_checked,Batch0025.positivity_checked,Batch0026.positivity_checked,Batch0027.positivity_checked,Batch0028.positivity_checked,Batch0029.positivity_checked,Batch0030.positivity_checked,Batch0031.positivity_checked,Batch0032.positivity_checked,Batch0033.positivity_checked,Batch0034.positivity_checked,Batch0035.positivity_checked,Batch0036.positivity_checked,Batch0037.positivity_checked,Batch0038.positivity_checked,Batch0039.positivity_checked,Batch0040.positivity_checked,Batch0041.positivity_checked,Batch0042.positivity_checked,Batch0043.positivity_checked,Batch0044.positivity_checked,Batch0045.positivity_checked,Batch0046.positivity_checked,Batch0047.positivity_checked,Batch0048.positivity_checked,Batch0049.positivity_checked,Batch0050.positivity_checked,Batch0051.positivity_checked,Batch0052.positivity_checked,Batch0053.positivity_checked,Batch0054.positivity_checked,Batch0055.positivity_checked,Batch0056.positivity_checked,Batch0057.positivity_checked,Batch0058.positivity_checked,Batch0059.positivity_checked,Batch0060.positivity_checked,Batch0061.positivity_checked,Batch0062.positivity_checked,Batch0063.positivity_checked,Batch0064.positivity_checked,Batch0065.positivity_checked,Batch0066.positivity_checked,Batch0067.positivity_checked,Batch0068.positivity_checked,Batch0069.positivity_checked,Batch0070.positivity_checked,Batch0071.positivity_checked,Batch0072.positivity_checked,Batch0073.positivity_checked,Batch0074.positivity_checked,Batch0075.positivity_checked,Batch0076.positivity_checked,Batch0077.positivity_checked,Batch0078.positivity_checked,Batch0079.positivity_checked,Batch0080.positivity_checked,Batch0081.positivity_checked,Batch0082.positivity_checked,Batch0083.positivity_checked,Batch0084.positivity_checked,Batch0085.positivity_checked,Batch0086.positivity_checked,Bool.true_and]
theorem weight_bounds_checked : certificates.all (fun c=>(List.finRange 4).all (fun i=>decide ((c.cell.weights i).maxAbs≤20*scale)))=true := by
  simp only [certificates,List.all_flatten,List.all_cons,List.all_nil,Batch0000.weight_bounds_checked,Batch0001.weight_bounds_checked,Batch0002.weight_bounds_checked,Batch0003.weight_bounds_checked,Batch0004.weight_bounds_checked,Batch0005.weight_bounds_checked,Batch0006.weight_bounds_checked,Batch0007.weight_bounds_checked,Batch0008.weight_bounds_checked,Batch0009.weight_bounds_checked,Batch0010.weight_bounds_checked,Batch0011.weight_bounds_checked,Batch0012.weight_bounds_checked,Batch0013.weight_bounds_checked,Batch0014.weight_bounds_checked,Batch0015.weight_bounds_checked,Batch0016.weight_bounds_checked,Batch0017.weight_bounds_checked,Batch0018.weight_bounds_checked,Batch0019.weight_bounds_checked,Batch0020.weight_bounds_checked,Batch0021.weight_bounds_checked,Batch0022.weight_bounds_checked,Batch0023.weight_bounds_checked,Batch0024.weight_bounds_checked,Batch0025.weight_bounds_checked,Batch0026.weight_bounds_checked,Batch0027.weight_bounds_checked,Batch0028.weight_bounds_checked,Batch0029.weight_bounds_checked,Batch0030.weight_bounds_checked,Batch0031.weight_bounds_checked,Batch0032.weight_bounds_checked,Batch0033.weight_bounds_checked,Batch0034.weight_bounds_checked,Batch0035.weight_bounds_checked,Batch0036.weight_bounds_checked,Batch0037.weight_bounds_checked,Batch0038.weight_bounds_checked,Batch0039.weight_bounds_checked,Batch0040.weight_bounds_checked,Batch0041.weight_bounds_checked,Batch0042.weight_bounds_checked,Batch0043.weight_bounds_checked,Batch0044.weight_bounds_checked,Batch0045.weight_bounds_checked,Batch0046.weight_bounds_checked,Batch0047.weight_bounds_checked,Batch0048.weight_bounds_checked,Batch0049.weight_bounds_checked,Batch0050.weight_bounds_checked,Batch0051.weight_bounds_checked,Batch0052.weight_bounds_checked,Batch0053.weight_bounds_checked,Batch0054.weight_bounds_checked,Batch0055.weight_bounds_checked,Batch0056.weight_bounds_checked,Batch0057.weight_bounds_checked,Batch0058.weight_bounds_checked,Batch0059.weight_bounds_checked,Batch0060.weight_bounds_checked,Batch0061.weight_bounds_checked,Batch0062.weight_bounds_checked,Batch0063.weight_bounds_checked,Batch0064.weight_bounds_checked,Batch0065.weight_bounds_checked,Batch0066.weight_bounds_checked,Batch0067.weight_bounds_checked,Batch0068.weight_bounds_checked,Batch0069.weight_bounds_checked,Batch0070.weight_bounds_checked,Batch0071.weight_bounds_checked,Batch0072.weight_bounds_checked,Batch0073.weight_bounds_checked,Batch0074.weight_bounds_checked,Batch0075.weight_bounds_checked,Batch0076.weight_bounds_checked,Batch0077.weight_bounds_checked,Batch0078.weight_bounds_checked,Batch0079.weight_bounds_checked,Batch0080.weight_bounds_checked,Batch0081.weight_bounds_checked,Batch0082.weight_bounds_checked,Batch0083.weight_bounds_checked,Batch0084.weight_bounds_checked,Batch0085.weight_bounds_checked,Batch0086.weight_bounds_checked,Bool.true_and]
theorem starts_checked : certificates.all (fun c=>decide (c.start=ReferenceActualData.CoarseLowerShape.start))=true := by
  simp only [certificates,List.all_flatten,List.all_cons,List.all_nil,Batch0000.starts_checked,Batch0001.starts_checked,Batch0002.starts_checked,Batch0003.starts_checked,Batch0004.starts_checked,Batch0005.starts_checked,Batch0006.starts_checked,Batch0007.starts_checked,Batch0008.starts_checked,Batch0009.starts_checked,Batch0010.starts_checked,Batch0011.starts_checked,Batch0012.starts_checked,Batch0013.starts_checked,Batch0014.starts_checked,Batch0015.starts_checked,Batch0016.starts_checked,Batch0017.starts_checked,Batch0018.starts_checked,Batch0019.starts_checked,Batch0020.starts_checked,Batch0021.starts_checked,Batch0022.starts_checked,Batch0023.starts_checked,Batch0024.starts_checked,Batch0025.starts_checked,Batch0026.starts_checked,Batch0027.starts_checked,Batch0028.starts_checked,Batch0029.starts_checked,Batch0030.starts_checked,Batch0031.starts_checked,Batch0032.starts_checked,Batch0033.starts_checked,Batch0034.starts_checked,Batch0035.starts_checked,Batch0036.starts_checked,Batch0037.starts_checked,Batch0038.starts_checked,Batch0039.starts_checked,Batch0040.starts_checked,Batch0041.starts_checked,Batch0042.starts_checked,Batch0043.starts_checked,Batch0044.starts_checked,Batch0045.starts_checked,Batch0046.starts_checked,Batch0047.starts_checked,Batch0048.starts_checked,Batch0049.starts_checked,Batch0050.starts_checked,Batch0051.starts_checked,Batch0052.starts_checked,Batch0053.starts_checked,Batch0054.starts_checked,Batch0055.starts_checked,Batch0056.starts_checked,Batch0057.starts_checked,Batch0058.starts_checked,Batch0059.starts_checked,Batch0060.starts_checked,Batch0061.starts_checked,Batch0062.starts_checked,Batch0063.starts_checked,Batch0064.starts_checked,Batch0065.starts_checked,Batch0066.starts_checked,Batch0067.starts_checked,Batch0068.starts_checked,Batch0069.starts_checked,Batch0070.starts_checked,Batch0071.starts_checked,Batch0072.starts_checked,Batch0073.starts_checked,Batch0074.starts_checked,Batch0075.starts_checked,Batch0076.starts_checked,Batch0077.starts_checked,Batch0078.starts_checked,Batch0079.starts_checked,Batch0080.starts_checked,Batch0081.starts_checked,Batch0082.starts_checked,Batch0083.starts_checked,Batch0084.starts_checked,Batch0085.starts_checked,Batch0086.starts_checked,Bool.true_and]
theorem rank_crop_checked : certificates.all (fun c=>c.cell.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact true && c.cell.flow.rankCropCheck TransportReferenceData.CoarseLowerShape.data.leftContact TransportReferenceData.CoarseLowerShape.data.rightContact false)=true := by
  simp only [certificates,List.all_flatten,List.all_cons,List.all_nil,Batch0000.rank_crop_checked,Batch0001.rank_crop_checked,Batch0002.rank_crop_checked,Batch0003.rank_crop_checked,Batch0004.rank_crop_checked,Batch0005.rank_crop_checked,Batch0006.rank_crop_checked,Batch0007.rank_crop_checked,Batch0008.rank_crop_checked,Batch0009.rank_crop_checked,Batch0010.rank_crop_checked,Batch0011.rank_crop_checked,Batch0012.rank_crop_checked,Batch0013.rank_crop_checked,Batch0014.rank_crop_checked,Batch0015.rank_crop_checked,Batch0016.rank_crop_checked,Batch0017.rank_crop_checked,Batch0018.rank_crop_checked,Batch0019.rank_crop_checked,Batch0020.rank_crop_checked,Batch0021.rank_crop_checked,Batch0022.rank_crop_checked,Batch0023.rank_crop_checked,Batch0024.rank_crop_checked,Batch0025.rank_crop_checked,Batch0026.rank_crop_checked,Batch0027.rank_crop_checked,Batch0028.rank_crop_checked,Batch0029.rank_crop_checked,Batch0030.rank_crop_checked,Batch0031.rank_crop_checked,Batch0032.rank_crop_checked,Batch0033.rank_crop_checked,Batch0034.rank_crop_checked,Batch0035.rank_crop_checked,Batch0036.rank_crop_checked,Batch0037.rank_crop_checked,Batch0038.rank_crop_checked,Batch0039.rank_crop_checked,Batch0040.rank_crop_checked,Batch0041.rank_crop_checked,Batch0042.rank_crop_checked,Batch0043.rank_crop_checked,Batch0044.rank_crop_checked,Batch0045.rank_crop_checked,Batch0046.rank_crop_checked,Batch0047.rank_crop_checked,Batch0048.rank_crop_checked,Batch0049.rank_crop_checked,Batch0050.rank_crop_checked,Batch0051.rank_crop_checked,Batch0052.rank_crop_checked,Batch0053.rank_crop_checked,Batch0054.rank_crop_checked,Batch0055.rank_crop_checked,Batch0056.rank_crop_checked,Batch0057.rank_crop_checked,Batch0058.rank_crop_checked,Batch0059.rank_crop_checked,Batch0060.rank_crop_checked,Batch0061.rank_crop_checked,Batch0062.rank_crop_checked,Batch0063.rank_crop_checked,Batch0064.rank_crop_checked,Batch0065.rank_crop_checked,Batch0066.rank_crop_checked,Batch0067.rank_crop_checked,Batch0068.rank_crop_checked,Batch0069.rank_crop_checked,Batch0070.rank_crop_checked,Batch0071.rank_crop_checked,Batch0072.rank_crop_checked,Batch0073.rank_crop_checked,Batch0074.rank_crop_checked,Batch0075.rank_crop_checked,Batch0076.rank_crop_checked,Batch0077.rank_crop_checked,Batch0078.rank_crop_checked,Batch0079.rank_crop_checked,Batch0080.rank_crop_checked,Batch0081.rank_crop_checked,Batch0082.rank_crop_checked,Batch0083.rank_crop_checked,Batch0084.rank_crop_checked,Batch0085.rank_crop_checked,Batch0086.rank_crop_checked,Bool.true_and]
theorem cover_checked : Transport.referenceFlowCoverCheck ReferenceActualData.CoarseLowerShape.start ReferenceActualData.CoarseLowerShape.finish (certificates.map (fun c=>c.cell.flow))=true := by decide +kernel
theorem refined : ∀ c∈certificates,∃ parent∈ReferenceActualData.CoarseLowerShape.cells,∃ lo hi : ℚ,parent.refinementCheck c.cell.flow lo hi=true := by
  intro c hc
  unfold certificates at hc
  obtain ⟨batch,hbatch,hc⟩ := List.mem_flatten.mp hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hbatch
  rcases hbatch with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Batch0000.refined c hc
  · exact Batch0001.refined c hc
  · exact Batch0002.refined c hc
  · exact Batch0003.refined c hc
  · exact Batch0004.refined c hc
  · exact Batch0005.refined c hc
  · exact Batch0006.refined c hc
  · exact Batch0007.refined c hc
  · exact Batch0008.refined c hc
  · exact Batch0009.refined c hc
  · exact Batch0010.refined c hc
  · exact Batch0011.refined c hc
  · exact Batch0012.refined c hc
  · exact Batch0013.refined c hc
  · exact Batch0014.refined c hc
  · exact Batch0015.refined c hc
  · exact Batch0016.refined c hc
  · exact Batch0017.refined c hc
  · exact Batch0018.refined c hc
  · exact Batch0019.refined c hc
  · exact Batch0020.refined c hc
  · exact Batch0021.refined c hc
  · exact Batch0022.refined c hc
  · exact Batch0023.refined c hc
  · exact Batch0024.refined c hc
  · exact Batch0025.refined c hc
  · exact Batch0026.refined c hc
  · exact Batch0027.refined c hc
  · exact Batch0028.refined c hc
  · exact Batch0029.refined c hc
  · exact Batch0030.refined c hc
  · exact Batch0031.refined c hc
  · exact Batch0032.refined c hc
  · exact Batch0033.refined c hc
  · exact Batch0034.refined c hc
  · exact Batch0035.refined c hc
  · exact Batch0036.refined c hc
  · exact Batch0037.refined c hc
  · exact Batch0038.refined c hc
  · exact Batch0039.refined c hc
  · exact Batch0040.refined c hc
  · exact Batch0041.refined c hc
  · exact Batch0042.refined c hc
  · exact Batch0043.refined c hc
  · exact Batch0044.refined c hc
  · exact Batch0045.refined c hc
  · exact Batch0046.refined c hc
  · exact Batch0047.refined c hc
  · exact Batch0048.refined c hc
  · exact Batch0049.refined c hc
  · exact Batch0050.refined c hc
  · exact Batch0051.refined c hc
  · exact Batch0052.refined c hc
  · exact Batch0053.refined c hc
  · exact Batch0054.refined c hc
  · exact Batch0055.refined c hc
  · exact Batch0056.refined c hc
  · exact Batch0057.refined c hc
  · exact Batch0058.refined c hc
  · exact Batch0059.refined c hc
  · exact Batch0060.refined c hc
  · exact Batch0061.refined c hc
  · exact Batch0062.refined c hc
  · exact Batch0063.refined c hc
  · exact Batch0064.refined c hc
  · exact Batch0065.refined c hc
  · exact Batch0066.refined c hc
  · exact Batch0067.refined c hc
  · exact Batch0068.refined c hc
  · exact Batch0069.refined c hc
  · exact Batch0070.refined c hc
  · exact Batch0071.refined c hc
  · exact Batch0072.refined c hc
  · exact Batch0073.refined c hc
  · exact Batch0074.refined c hc
  · exact Batch0075.refined c hc
  · exact Batch0076.refined c hc
  · exact Batch0077.refined c hc
  · exact Batch0078.refined c hc
  · exact Batch0079.refined c hc
  · exact Batch0080.refined c hc
  · exact Batch0081.refined c hc
  · exact Batch0082.refined c hc
  · exact Batch0083.refined c hc
  · exact Batch0084.refined c hc
  · exact Batch0085.refined c hc
  · exact Batch0086.refined c hc
end OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Assembly
