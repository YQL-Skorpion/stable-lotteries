import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0068_0071
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0069_0072
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0073_0076

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0072
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert576 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert576,⟨112709678069288602707330,112709681433893421279552⟩,⟨0,789538531226181365575⟩⟩
def cert577 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert577,⟨111920740048026361213442,111920743396109279788110⟩,⟨0,789571783248295786043⟩⟩
def cert578 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert578,⟨111354599348550201374552,111354602690541232838248⟩,⟨0,566468108766525532704⟩⟩
def cert579 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert579,⟨110788441895033377361381,110788445230959897903946⟩,⟨0,566485038230300487403⟩⟩
def cert580 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert580,⟨110460860027718788654692,110460863362478206637064⟩,⟨0,327691285817043346708⟩⟩
def cert581 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert581,⟨110133272589834817885925,110133275923429471578143⟩,⟨0,327696889246294268236⟩⟩
def cert582 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert582,⟨109078033157152919318420,109078036451411558875873⟩,⟨0,1056380034643619334131⟩⟩
def cert583 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0072.cert583,⟨108022736342174542645778,108022739597351066591419⟩,⟨0,1056438523282302189198⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert576,cert577,cert578,cert579,cert580,cert581,cert582,cert583]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0072.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell576,ReferenceCumulativeData.CoarseLowerShapeTime.cell577,ReferenceCumulativeData.CoarseLowerShapeTime.cell578,ReferenceCumulativeData.CoarseLowerShapeTime.cell579,ReferenceCumulativeData.CoarseLowerShapeTime.cell580,ReferenceCumulativeData.CoarseLowerShapeTime.cell581,ReferenceCumulativeData.CoarseLowerShapeTime.cell582,ReferenceCumulativeData.CoarseLowerShapeTime.cell583] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0072

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0073
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert584 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert584,⟨106712921595408533003781,106712924775591772310429⟩,⟨0,1311582534304395368664⟩⟩
def cert585 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert585,⟨105403019700993955518612,105403022806793419407694⟩,⟨0,1311671814868898456660⟩⟩
def cert586 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert586,⟨104351484640840102383668,104351487708248280500889⟩,⟨0,1052681025266286867565⟩⟩
def cert587 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert587,⟨103299894222301129093162,103299897251574320531946⟩,⟨0,1052737495620770651520⟩⟩
def cert588 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert588,⟨102287756174657188879732,102287759169930505228267⟩,⟨0,1013205199038719668756⟩⟩
def cert589 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert589,⟨101275567489929245488593,101275570451424969970926⟩,⟨0,1013256834501615532443⟩⟩
def cert590 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert590,⟨99938789394854983338788,99938792278223291731189⟩,⟨0,1338650673393728782134⟩⟩
def cert591 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0073.cert591,⟨98601924254280440608754,98601927060205213818275⟩,⟨0,1338740037797425428973⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert584,cert585,cert586,cert587,cert588,cert589,cert590,cert591]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0073.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell584,ReferenceCumulativeData.CoarseLowerShapeTime.cell585,ReferenceCumulativeData.CoarseLowerShapeTime.cell586,ReferenceCumulativeData.CoarseLowerShapeTime.cell587,ReferenceCumulativeData.CoarseLowerShapeTime.cell588,ReferenceCumulativeData.CoarseLowerShapeTime.cell589,ReferenceCumulativeData.CoarseLowerShapeTime.cell590,ReferenceCumulativeData.CoarseLowerShapeTime.cell591] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0073

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0074
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert592 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert592,⟨97432115932836564231548,97432118686967271612474⟩,⟨0,1171251231624216289554⟩⟩
def cert593 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert593,⟨96262241996910634300402,96262244699653504958210⟩,⟨0,1171318412827332255205⟩⟩
def cert594 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert594,⟨95095520653179878048749,95095523304951691246025⟩,⟨0,1168165022406308775440⟩⟩
def cert595 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert595,⟨93928735002185760834778,93928737603393189087095⟩,⟨0,1168230896147162780807⟩⟩
def cert596 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert596,⟨92949486726192874774345,92949489297583695277080⟩,⟨0,980270676016912895953⟩⟩
def cert597 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert597,⟨91970193767119368299866,91970196308897644100066⟩,⟨0,980316291751163273450⟩⟩
def cert598 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert598,⟨91786045533062360170682,91786048074644988296880⟩,⟨0,184184555812598235105⟩⟩
def cert599 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0074.cert599,⟨91601895727586939657885,91601898268974178748049⟩,⟨0,184186133476474585904⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert592,cert593,cert594,cert595,cert596,cert597,cert598,cert599]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0074.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell592,ReferenceCumulativeData.CoarseLowerShapeTime.cell593,ReferenceCumulativeData.CoarseLowerShapeTime.cell594,ReferenceCumulativeData.CoarseLowerShapeTime.cell595,ReferenceCumulativeData.CoarseLowerShapeTime.cell596,ReferenceCumulativeData.CoarseLowerShapeTime.cell597,ReferenceCumulativeData.CoarseLowerShapeTime.cell598,ReferenceCumulativeData.CoarseLowerShapeTime.cell599] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0074

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0075
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert600 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert600,⟨90441074628113506053977,90441077120181056759879⟩,⟨0,1162266449737546190812⟩⟩
def cert601 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert601,⟨89280191765625143556114,89280194208780370359357⟩,⟨0,1162329778572441114875⟩⟩
def cert602 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert602,⟨88105284940323508399958,88105287332756857098055⟩,⟨0,1176396583673395982050⟩⟩
def cert603 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert603,⟨86930315777143568695547,86930318119287960689741⟩,⟨0,1176460558831876657941⟩⟩
def cert604 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert604,⟨85793297994748558835382,85793300291375947108409⟩,⟨0,1138421073787554671386⟩⟩
def cert605 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert605,⟨84656222706884721578715,84656224958379279848693⟩,⟨0,1138480074663485245094⟩⟩
def cert606 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert606,⟨83873977627329684271371,83873979864211822433967⟩,⟨0,782912409752372197914⟩⟩
def cert607 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0075.cert607,⟨83091705671495859802420,83091707893852541278606⟩,⟨0,782939775945870452199⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert600,cert601,cert602,cert603,cert604,cert605,cert606,cert607]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0075.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell600,ReferenceCumulativeData.CoarseLowerShapeTime.cell601,ReferenceCumulativeData.CoarseLowerShapeTime.cell602,ReferenceCumulativeData.CoarseLowerShapeTime.cell603,ReferenceCumulativeData.CoarseLowerShapeTime.cell604,ReferenceCumulativeData.CoarseLowerShapeTime.cell605,ReferenceCumulativeData.CoarseLowerShapeTime.cell606,ReferenceCumulativeData.CoarseLowerShapeTime.cell607] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0075
