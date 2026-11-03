import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0036_0039
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0037_0040
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0041_0044

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0040
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert320 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert320,⟨166835548389000690172322,166835553340373212711819⟩,⟨0,16497261298973685424⟩⟩
def cert321 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert321,⟨166819051730052747908533,166819056681425106034247⟩,⟨0,16497294938388971877⟩⟩
def cert322 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert322,⟨166814247454008991411339,166814252405381345497581⟩,⟨0,4804329982905735597⟩⟩
def cert323 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert323,⟨166809443175113558992077,166809448126485909043918⟩,⟨0,4804332835048166543⟩⟩
def cert324 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert324,⟨166768515735434559922501,166768520686804447176342⟩,⟨0,40931329431028912035⟩⟩
def cert325 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert325,⟨166727588090158527558540,166727593041525978186327⟩,⟨0,40931535312887825960⟩⟩
def cert326 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert326,⟨166702926627548148581670,166702931578915072348173⟩,⟨0,24662875014435773576⟩⟩
def cert327 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0040.cert327,⟨166678265090273059509800,166678270041639459681226⟩,⟨0,24662949741521107966⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert320,cert321,cert322,cert323,cert324,cert325,cert326,cert327]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0040.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell320,ReferenceCumulativeData.CoarseLowerShapeTime.cell321,ReferenceCumulativeData.CoarseLowerShapeTime.cell322,ReferenceCumulativeData.CoarseLowerShapeTime.cell323,ReferenceCumulativeData.CoarseLowerShapeTime.cell324,ReferenceCumulativeData.CoarseLowerShapeTime.cell325,ReferenceCumulativeData.CoarseLowerShapeTime.cell326,ReferenceCumulativeData.CoarseLowerShapeTime.cell327] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0040

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0041
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert328 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert328,⟨166650466257120859802358,166650471208486521498182⟩,⟨0,27800620081325854186⟩⟩
def cert329 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert329,⟨166622667329515492725676,166622672280880420956922⟩,⟨0,27800714623101120535⟩⟩
def cert330 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert330,⟨166607933622739345668269,166607938574103942484822⟩,⟨0,14734321128114073485⟩⟩
def cert331 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert331,⟨166593199883232458082812,166593204834596723149321⟩,⟨0,14734353877768624112⟩⟩
def cert332 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert332,⟨166578678660845522929551,166578683612209469002640⟩,⟨0,14521820155153222942⟩⟩
def cert333 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert333,⟨166564157406603751726854,166564162357967378490412⟩,⟨0,14521852028154173214⟩⟩
def cert334 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert334,⟨166561522499481015433968,166561527450844640290340⟩,⟨0,2634926804507611768⟩⟩
def cert335 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0041.cert335,⟨166558887591309320725821,166558892542672943674664⟩,⟨0,2634927853574543401⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert328,cert329,cert330,cert331,cert332,cert333,cert334,cert335]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0041.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell328,ReferenceCumulativeData.CoarseLowerShapeTime.cell329,ReferenceCumulativeData.CoarseLowerShapeTime.cell330,ReferenceCumulativeData.CoarseLowerShapeTime.cell331,ReferenceCumulativeData.CoarseLowerShapeTime.cell332,ReferenceCumulativeData.CoarseLowerShapeTime.cell333,ReferenceCumulativeData.CoarseLowerShapeTime.cell334,ReferenceCumulativeData.CoarseLowerShapeTime.cell335] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0041

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0042
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert336 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert336,⟨166552428023563882834531,166552432974927477662289⟩,⟨0,6459686034720703637⟩⟩
def cert337 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert337,⟨166545968449513717285346,166545973400877283979669⟩,⟨0,6459692341046958164⟩⟩
def cert338 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert338,⟨166539508869158420074436,166539513820521958623110⟩,⟨0,6459698647351099913⟩⟩
def cert339 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert339,⟨166533049282497720155054,166533054233861230545829⟩,⟨0,6459704954352300025⟩⟩
def cert340 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert340,⟨166526589689531346333718,166526594640894828554356⟩,⟨0,6459711261198563061⟩⟩
def cert341 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert341,⟨166520130090258894165493,166520135041622348203757⟩,⟨0,6459717568875297405⟩⟩
def cert342 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert342,⟨166513717427949326156157,166513722379312752204812⟩,⟨0,6412779721817600180⟩⟩
def cert343 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0042.cert343,⟨166507304759378843674349,166507309710742241721259⟩,⟨0,6412785984318354150⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert336,cert337,cert338,cert339,cert340,cert341,cert342,cert343]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0042.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell336,ReferenceCumulativeData.CoarseLowerShapeTime.cell337,ReferenceCumulativeData.CoarseLowerShapeTime.cell338,ReferenceCumulativeData.CoarseLowerShapeTime.cell339,ReferenceCumulativeData.CoarseLowerShapeTime.cell340,ReferenceCumulativeData.CoarseLowerShapeTime.cell341,ReferenceCumulativeData.CoarseLowerShapeTime.cell342,ReferenceCumulativeData.CoarseLowerShapeTime.cell343] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0042

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0043
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert344 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert344,⟨166494113788032838525971,166494118739395992562296⟩,⟨0,13191468175755384827⟩⟩
def cert345 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert345,⟨166480922790190627390491,166480927741553537205619⟩,⟨0,13191494685767493145⟩⟩
def cert346 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert346,⟨166369274009665761207117,166369278960879003490311⟩,⟨0,111684385601259432241⟩⟩
def cert347 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert347,⟨166257623329009092110433,166257628280071585698339⟩,⟨0,111686294107396107380⟩⟩
def cert348 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert348,⟨166198882585970552766471,166198887537011056670711⟩,⟨0,58750600326199464952⟩⟩
def cert349 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert349,⟨166140141316241383923206,166140146267259820121201⟩,⟨0,58751128234581461030⟩⟩
def cert350 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert350,⟨166132226071438956833778,166132231022457337849344⟩,⟨0,7915425810178540546⟩⟩
def cert351 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0043.cert351,⟨166124310816957034140237,166124315767975359946747⟩,⟨0,7915435492721327004⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert344,cert345,cert346,cert347,cert348,cert349,cert350,cert351]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0043.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell344,ReferenceCumulativeData.CoarseLowerShapeTime.cell345,ReferenceCumulativeData.CoarseLowerShapeTime.cell346,ReferenceCumulativeData.CoarseLowerShapeTime.cell347,ReferenceCumulativeData.CoarseLowerShapeTime.cell348,ReferenceCumulativeData.CoarseLowerShapeTime.cell349,ReferenceCumulativeData.CoarseLowerShapeTime.cell350,ReferenceCumulativeData.CoarseLowerShapeTime.cell351] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0043
