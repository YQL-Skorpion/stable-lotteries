import OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow.Bundle0043_0043
namespace OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def batches : List (List Transport.HessianCell) := [Batch0000.cells,Batch0001.cells,Batch0002.cells,Batch0003.cells,Batch0004.cells,Batch0005.cells,Batch0006.cells,Batch0007.cells,Batch0008.cells,Batch0009.cells,Batch0010.cells,Batch0011.cells,Batch0012.cells,Batch0013.cells,Batch0014.cells,Batch0015.cells,Batch0016.cells,Batch0017.cells,Batch0018.cells,Batch0019.cells,Batch0020.cells,Batch0021.cells,Batch0022.cells,Batch0023.cells,Batch0024.cells,Batch0025.cells,Batch0026.cells,Batch0027.cells,Batch0028.cells,Batch0029.cells,Batch0030.cells,Batch0031.cells,Batch0032.cells,Batch0033.cells,Batch0034.cells,Batch0035.cells,Batch0036.cells,Batch0037.cells,Batch0038.cells,Batch0039.cells,Batch0040.cells,Batch0041.cells,Batch0042.cells,Batch0043.cells]
def cells : List Transport.HessianCell := batches.flatten
theorem all_checked : cells.all (fun c => c.checkClean scale params slabs)=true := by
  simp only [cells,List.all_flatten,batches,List.all_cons,List.all_nil,Batch0000.checked,Batch0001.checked,Batch0002.checked,Batch0003.checked,Batch0004.checked,Batch0005.checked,Batch0006.checked,Batch0007.checked,Batch0008.checked,Batch0009.checked,Batch0010.checked,Batch0011.checked,Batch0012.checked,Batch0013.checked,Batch0014.checked,Batch0015.checked,Batch0016.checked,Batch0017.checked,Batch0018.checked,Batch0019.checked,Batch0020.checked,Batch0021.checked,Batch0022.checked,Batch0023.checked,Batch0024.checked,Batch0025.checked,Batch0026.checked,Batch0027.checked,Batch0028.checked,Batch0029.checked,Batch0030.checked,Batch0031.checked,Batch0032.checked,Batch0033.checked,Batch0034.checked,Batch0035.checked,Batch0036.checked,Batch0037.checked,Batch0038.checked,Batch0039.checked,Batch0040.checked,Batch0041.checked,Batch0042.checked,Batch0043.checked,Bool.true_and]
theorem rank_nonnegative_checked : cells.all (fun c=>decide (0≤c.rankPenalty))=true := by
  simp only [cells,List.all_flatten,batches,List.all_cons,List.all_nil,Batch0000.rank_nonnegative_checked,Batch0001.rank_nonnegative_checked,Batch0002.rank_nonnegative_checked,Batch0003.rank_nonnegative_checked,Batch0004.rank_nonnegative_checked,Batch0005.rank_nonnegative_checked,Batch0006.rank_nonnegative_checked,Batch0007.rank_nonnegative_checked,Batch0008.rank_nonnegative_checked,Batch0009.rank_nonnegative_checked,Batch0010.rank_nonnegative_checked,Batch0011.rank_nonnegative_checked,Batch0012.rank_nonnegative_checked,Batch0013.rank_nonnegative_checked,Batch0014.rank_nonnegative_checked,Batch0015.rank_nonnegative_checked,Batch0016.rank_nonnegative_checked,Batch0017.rank_nonnegative_checked,Batch0018.rank_nonnegative_checked,Batch0019.rank_nonnegative_checked,Batch0020.rank_nonnegative_checked,Batch0021.rank_nonnegative_checked,Batch0022.rank_nonnegative_checked,Batch0023.rank_nonnegative_checked,Batch0024.rank_nonnegative_checked,Batch0025.rank_nonnegative_checked,Batch0026.rank_nonnegative_checked,Batch0027.rank_nonnegative_checked,Batch0028.rank_nonnegative_checked,Batch0029.rank_nonnegative_checked,Batch0030.rank_nonnegative_checked,Batch0031.rank_nonnegative_checked,Batch0032.rank_nonnegative_checked,Batch0033.rank_nonnegative_checked,Batch0034.rank_nonnegative_checked,Batch0035.rank_nonnegative_checked,Batch0036.rank_nonnegative_checked,Batch0037.rank_nonnegative_checked,Batch0038.rank_nonnegative_checked,Batch0039.rank_nonnegative_checked,Batch0040.rank_nonnegative_checked,Batch0041.rank_nonnegative_checked,Batch0042.rank_nonnegative_checked,Batch0043.rank_nonnegative_checked,Bool.true_and]
theorem time_cover_checked : Transport.hessianCellCoverCheck timeStart timeFinish cells=true := by
  have h0 := Batch0000.cover_checked
  have h1 := Transport.hessianCellCoverCheck_append h0 Batch0001.cover_checked
  have h2 := Transport.hessianCellCoverCheck_append h1 Batch0002.cover_checked
  have h3 := Transport.hessianCellCoverCheck_append h2 Batch0003.cover_checked
  have h4 := Transport.hessianCellCoverCheck_append h3 Batch0004.cover_checked
  have h5 := Transport.hessianCellCoverCheck_append h4 Batch0005.cover_checked
  have h6 := Transport.hessianCellCoverCheck_append h5 Batch0006.cover_checked
  have h7 := Transport.hessianCellCoverCheck_append h6 Batch0007.cover_checked
  have h8 := Transport.hessianCellCoverCheck_append h7 Batch0008.cover_checked
  have h9 := Transport.hessianCellCoverCheck_append h8 Batch0009.cover_checked
  have h10 := Transport.hessianCellCoverCheck_append h9 Batch0010.cover_checked
  have h11 := Transport.hessianCellCoverCheck_append h10 Batch0011.cover_checked
  have h12 := Transport.hessianCellCoverCheck_append h11 Batch0012.cover_checked
  have h13 := Transport.hessianCellCoverCheck_append h12 Batch0013.cover_checked
  have h14 := Transport.hessianCellCoverCheck_append h13 Batch0014.cover_checked
  have h15 := Transport.hessianCellCoverCheck_append h14 Batch0015.cover_checked
  have h16 := Transport.hessianCellCoverCheck_append h15 Batch0016.cover_checked
  have h17 := Transport.hessianCellCoverCheck_append h16 Batch0017.cover_checked
  have h18 := Transport.hessianCellCoverCheck_append h17 Batch0018.cover_checked
  have h19 := Transport.hessianCellCoverCheck_append h18 Batch0019.cover_checked
  have h20 := Transport.hessianCellCoverCheck_append h19 Batch0020.cover_checked
  have h21 := Transport.hessianCellCoverCheck_append h20 Batch0021.cover_checked
  have h22 := Transport.hessianCellCoverCheck_append h21 Batch0022.cover_checked
  have h23 := Transport.hessianCellCoverCheck_append h22 Batch0023.cover_checked
  have h24 := Transport.hessianCellCoverCheck_append h23 Batch0024.cover_checked
  have h25 := Transport.hessianCellCoverCheck_append h24 Batch0025.cover_checked
  have h26 := Transport.hessianCellCoverCheck_append h25 Batch0026.cover_checked
  have h27 := Transport.hessianCellCoverCheck_append h26 Batch0027.cover_checked
  have h28 := Transport.hessianCellCoverCheck_append h27 Batch0028.cover_checked
  have h29 := Transport.hessianCellCoverCheck_append h28 Batch0029.cover_checked
  have h30 := Transport.hessianCellCoverCheck_append h29 Batch0030.cover_checked
  have h31 := Transport.hessianCellCoverCheck_append h30 Batch0031.cover_checked
  have h32 := Transport.hessianCellCoverCheck_append h31 Batch0032.cover_checked
  have h33 := Transport.hessianCellCoverCheck_append h32 Batch0033.cover_checked
  have h34 := Transport.hessianCellCoverCheck_append h33 Batch0034.cover_checked
  have h35 := Transport.hessianCellCoverCheck_append h34 Batch0035.cover_checked
  have h36 := Transport.hessianCellCoverCheck_append h35 Batch0036.cover_checked
  have h37 := Transport.hessianCellCoverCheck_append h36 Batch0037.cover_checked
  have h38 := Transport.hessianCellCoverCheck_append h37 Batch0038.cover_checked
  have h39 := Transport.hessianCellCoverCheck_append h38 Batch0039.cover_checked
  have h40 := Transport.hessianCellCoverCheck_append h39 Batch0040.cover_checked
  have h41 := Transport.hessianCellCoverCheck_append h40 Batch0041.cover_checked
  have h42 := Transport.hessianCellCoverCheck_append h41 Batch0042.cover_checked
  have h43 := Transport.hessianCellCoverCheck_append h42 Batch0043.cover_checked
  simpa only [timeStart,timeFinish,cells,batches,List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using h43
end OptimalG.Certificates.TransportHessianData.CoarseLowerShapeFlow
