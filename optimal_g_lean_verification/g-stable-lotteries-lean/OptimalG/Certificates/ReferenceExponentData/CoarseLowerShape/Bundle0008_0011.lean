import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0004_0007
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0005_0008
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0009_0012

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0008
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert64 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert64,⟨233661913367115870349819,233661919570970598594431⟩,⟨0,552476719470505691298⟩⟩
def cert65 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert65,⟨233109955986802824174256,233109962178810300855686⟩,⟨0,552485499181566397992⟩⟩
def cert66 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert66,⟨232640871538455598408232,232640877723215531342510⟩,⟨0,469466137825508204586⟩⟩
def cert67 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert67,⟨232171780839099895158067,232171787016623900909803⟩,⟨0,469472624417799249640⟩⟩
def cert68 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert68,⟨231668025377791161724477,231668031546373043454522⟩,⟨0,504196286283453886692⟩⟩
def cert69 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert69,⟨231164262503393352612877,231164268663048489551923⟩,⟨0,504203991609702691488⟩⟩
def cert70 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert70,⟨230677102899809300791665,230677109051413302121366⟩,⟨0,487572433917167579826⟩⟩
def cert71 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0008.cert71,⟨230189936170277761521025,230189942313844018555142⟩,⟨0,487579824547029302509⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert64,cert65,cert66,cert67,cert68,cert69,cert70,cert71]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0008.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell64,ReferenceCumulativeData.CoarseLowerShapeTime.cell65,ReferenceCumulativeData.CoarseLowerShapeTime.cell66,ReferenceCumulativeData.CoarseLowerShapeTime.cell67,ReferenceCumulativeData.CoarseLowerShapeTime.cell68,ReferenceCumulativeData.CoarseLowerShapeTime.cell69,ReferenceCumulativeData.CoarseLowerShapeTime.cell70,ReferenceCumulativeData.CoarseLowerShapeTime.cell71] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0008

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0009
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert72 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert72,⟨229615856785840011685614,229615862916278540515830⟩,⟨0,574653594339795536994⟩⟩
def cert73 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert73,⟨229041767219805510742818,229041773337141996794944⟩,⟨0,574664209879588463128⟩⟩
def cert74 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert74,⟨228571848828516605535371,228571854938693812916667⟩,⟨0,470303656249670881360⟩⟩
def cert75 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert75,⟨228101923427689023545719,228101929530718436584131⟩,⟨0,470310904102783900990⟩⟩
def cert76 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert76,⟨227579562167634738655427,227579568260866887609739⟩,⟨0,522838011328503948842⟩⟩
def cert77 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert77,⟨227057192027154912887568,227057198110607247454999⟩,⟨0,522847219634373954452⟩⟩
def cert78 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert78,⟨226691393067971145053627,226691399148077947770299⟩,⟨0,366033003506421477223⟩⟩
def cert79 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0009.cert79,⟨226325589658231839324829,226325595734997293808202⟩,⟨0,366037566763591816253⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert72,cert73,cert74,cert75,cert76,cert77,cert78,cert79]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0009.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell72,ReferenceCumulativeData.CoarseLowerShapeTime.cell73,ReferenceCumulativeData.CoarseLowerShapeTime.cell74,ReferenceCumulativeData.CoarseLowerShapeTime.cell75,ReferenceCumulativeData.CoarseLowerShapeTime.cell76,ReferenceCumulativeData.CoarseLowerShapeTime.cell77,ReferenceCumulativeData.CoarseLowerShapeTime.cell78,ReferenceCumulativeData.CoarseLowerShapeTime.cell79] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0009

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0010
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert80 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert80,⟨225717682300214072076005,225717688361646698297659⟩,⟨0,608554810001650040738⟩⟩
def cert81 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert81,⟨225109762362282458852103,225109768408413975710614⟩,⟨0,608567908298538754417⟩⟩
def cert82 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert82,⟨224514913105156331400422,224514919136999046824025⟩,⟨0,595470231274317890753⟩⟩
def cert83 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert83,⟨223920051463604261039632,223920057481187098091078⟩,⟨0,595483102265189886189⟩⟩
def cert84 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert84,⟨223449047888033455595530,223449053898566100746332⟩,⟨0,471393421557450180633⟩⟩
def cert85 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert85,⟨222978036360709924747758,222978042364203700818304⟩,⟨0,471401615162362579196⟩⟩
def cert86 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert86,⟨222541282185791643427296,222541288183688603105999⟩,⟨0,437089798629118018990⟩⟩
def cert87 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0010.cert87,⟨222104521037027355925551,222104527029335838037620⟩,⟨0,437096965560341934904⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert80,cert81,cert82,cert83,cert84,cert85,cert86,cert87]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0010.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell80,ReferenceCumulativeData.CoarseLowerShapeTime.cell81,ReferenceCumulativeData.CoarseLowerShapeTime.cell82,ReferenceCumulativeData.CoarseLowerShapeTime.cell83,ReferenceCumulativeData.CoarseLowerShapeTime.cell84,ReferenceCumulativeData.CoarseLowerShapeTime.cell85,ReferenceCumulativeData.CoarseLowerShapeTime.cell86,ReferenceCumulativeData.CoarseLowerShapeTime.cell87] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0010

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0011
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert88 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert88,⟨221546263647003704962673,221546269627658279681528⟩,⟨0,558806569109150683442⟩⟩
def cert89 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert89,⟨220987994619940157303251,220988000588962963806490⟩,⟨0,558818610118741973279⟩⟩
def cert90 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert90,⟨220411515505805911602725,220411521462056705670036⟩,⟨0,577065669317670983580⟩⟩
def cert91 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert91,⟨219835023688387988970388,219835029631891811332786⟩,⟨0,577078818228684912727⟩⟩
def cert92 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert92,⟨219474383883687016500368,219474389824084786532974⟩,⟨0,360869601459287178978⟩⟩
def cert93 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert93,⟨219113739012871760146813,219113744950167302459891⟩,⟨0,360874776768738288968⟩⟩
def cert94 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert94,⟨219107364776557960190833,219107370713853485449565⟩,⟨0,6374308102801502200⟩⟩
def cert95 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0011.cert95,⟨219100990538649790550362,219100996475945298755125⟩,⟨0,6374309697772899507⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert88,cert89,cert90,cert91,cert92,cert93,cert94,cert95]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0011.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell88,ReferenceCumulativeData.CoarseLowerShapeTime.cell89,ReferenceCumulativeData.CoarseLowerShapeTime.cell90,ReferenceCumulativeData.CoarseLowerShapeTime.cell91,ReferenceCumulativeData.CoarseLowerShapeTime.cell92,ReferenceCumulativeData.CoarseLowerShapeTime.cell93,ReferenceCumulativeData.CoarseLowerShapeTime.cell94,ReferenceCumulativeData.CoarseLowerShapeTime.cell95] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0011
