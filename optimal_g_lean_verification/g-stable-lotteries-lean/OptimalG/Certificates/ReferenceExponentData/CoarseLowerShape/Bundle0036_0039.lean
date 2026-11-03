import OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Bundle0032_0035
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0033_0036
import OptimalG.Certificates.ReferenceWeightData.CoarseLowerShape.Bundle0037_0040

set_option Elab.async false

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0036
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert288 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert288,⟨167125780190817080648646,167125785142232108378921⟩,⟨0,43612601987929428954⟩⟩
def cert289 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert289,⟨167082172286696565676872,167082177238079983328657⟩,⟨0,43613019643458723330⟩⟩
def cert290 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert290,⟨167061794729129050245450,167061799680509243182078⟩,⟨0,20378674644608991895⟩⟩
def cert291 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert291,⟨167041417080338827745277,167041422031715796073276⟩,⟨0,20378765914427609088⟩⟩
def cert292 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert292,⟨167039804423220543025719,167039809374597509755783⟩,⟨0,1612664114600286286⟩⟩
def cert293 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert293,⟨167038191765530673923907,167038196716907639056040⟩,⟨0,1612664686208019514⟩⟩
def cert294 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert294,⟨167038092156648277719252,167038097108025242851008⟩,⟨0,99608909083544877⟩⟩
def cert295 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0036.cert295,⟨167037992547763700812690,167037997499140665944068⟩,⟨0,99608911264252284⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert288,cert289,cert290,cert291,cert292,cert293,cert294,cert295]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0036.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell288,ReferenceCumulativeData.CoarseLowerShapeTime.cell289,ReferenceCumulativeData.CoarseLowerShapeTime.cell290,ReferenceCumulativeData.CoarseLowerShapeTime.cell291,ReferenceCumulativeData.CoarseLowerShapeTime.cell292,ReferenceCumulativeData.CoarseLowerShapeTime.cell293,ReferenceCumulativeData.CoarseLowerShapeTime.cell294,ReferenceCumulativeData.CoarseLowerShapeTime.cell295] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0036

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0037
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert296 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert296,⟨167037953606244524599372,167037958557621489730726⟩,⟨0,38941523262026619⟩⟩
def cert297 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert297,⟨167037914664725014665050,167037919616101979796380⟩,⟨0,38941523595747953⟩⟩
def cert298 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert298,⟨167037884859004922716409,167037889810381887847736⟩,⟨0,29805722308516425⟩⟩
def cert299 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert299,⟨167037855053284713326239,167037860004661678457564⟩,⟨0,29805722425958079⟩⟩
def cert300 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert300,⟨167037755189438707622908,167037760140815672754176⟩,⟨0,99863870920523554⟩⟩
def cert301 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert301,⟨167037655325591382014075,167037660276968347145286⟩,⟨0,99863872240433769⟩⟩
def cert302 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert302,⟨167037224571278828058593,167037229522655793185312⟩,⟨0,430754778598705464⟩⟩
def cert303 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0037.cert303,⟨167036793816941577854459,167036798768318542976696⟩,⟨0,430754803295337113⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert296,cert297,cert298,cert299,cert300,cert301,cert302,cert303]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0037.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell296,ReferenceCumulativeData.CoarseLowerShapeTime.cell297,ReferenceCumulativeData.CoarseLowerShapeTime.cell298,ReferenceCumulativeData.CoarseLowerShapeTime.cell299,ReferenceCumulativeData.CoarseLowerShapeTime.cell300,ReferenceCumulativeData.CoarseLowerShapeTime.cell301,ReferenceCumulativeData.CoarseLowerShapeTime.cell302,ReferenceCumulativeData.CoarseLowerShapeTime.cell303] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0037

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0038
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert304 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert304,⟨167036790031173587543193,167036794982550552665429⟩,⟨0,3785768026309101⟩⟩
def cert305 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert305,⟨167036786245405595324356,167036791196782560446591⟩,⟨0,3785768028216672⟩⟩
def cert306 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert306,⟨167034901310970284525373,167034906262347249253509⟩,⟨0,1884943359382660406⟩⟩
def cert307 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert307,⟨167033016376062073708828,167033021327439038041392⟩,⟨0,1884943832314666311⟩⟩
def cert308 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert308,⟨167024703401596266267529,167024708352973201236512⟩,⟨0,8313143871032534543⟩⟩
def cert309 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert309,⟨167016390418161818524861,167016395369538724374052⟩,⟨0,8313152842301441717⟩⟩
def cert310 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert310,⟨167006117776589632494741,167006122727966465549721⟩,⟨0,10272913658131203942⟩⟩
def cert311 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0038.cert311,⟨166995845120583423265521,166995850071960183215945⟩,⟨0,10272928097583150561⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert304,cert305,cert306,cert307,cert308,cert309,cert310,cert311]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0038.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell304,ReferenceCumulativeData.CoarseLowerShapeTime.cell305,ReferenceCumulativeData.CoarseLowerShapeTime.cell306,ReferenceCumulativeData.CoarseLowerShapeTime.cell307,ReferenceCumulativeData.CoarseLowerShapeTime.cell308,ReferenceCumulativeData.CoarseLowerShapeTime.cell309,ReferenceCumulativeData.CoarseLowerShapeTime.cell310,ReferenceCumulativeData.CoarseLowerShapeTime.cell311] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0038

namespace OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0039
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
def cert312 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert312,⟨166970907808295925566685,166970912759671619361567⟩,⟨0,24938922981139750085⟩⟩
def cert313 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert313,⟨166945970410536836038437,166945975361911453990322⟩,⟨0,24939008531043720549⟩⟩
def cert314 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert314,⟨166938562427464509998040,166938567378839112481555⟩,⟨0,7408111779320863680⟩⟩
def cert315 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert315,⟨166931154437588267386564,166931159388962854434438⟩,⟨0,7408118584957426570⟩⟩
def cert316 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert316,⟨166920559804832213821307,166920564756206756154309⟩,⟨0,10594895033968415936⟩⟩
def cert317 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert317,⟨166909965158213000650741,166909970109587498405078⟩,⟨0,10594908902122579016⟩⟩
def cert318 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert318,⟨166881005138069033646379,166881010089442622785560⟩,⟨0,28961979979345464329⟩⟩
def cert319 : Transport.ReferenceExponentCertificate := ⟨ReferenceWeightData.CoarseLowerShape.Batch0039.cert319,⟨166852045014328097539164,166852049965700785249269⟩,⟨0,28962083678384995399⟩⟩
def certificates : List Transport.ReferenceExponentCertificate := [cert312,cert313,cert314,cert315,cert316,cert317,cert318,cert319]
theorem checked : certificates.all (fun c=>c.check scale)=true := by decide +kernel
theorem weights_linked : certificates.map (·.weight)=ReferenceWeightData.CoarseLowerShape.Batch0039.certificates := by rfl
theorem intervals_linked : certificates.map (·.interval)=[ReferenceCumulativeData.CoarseLowerShapeTime.cell312,ReferenceCumulativeData.CoarseLowerShapeTime.cell313,ReferenceCumulativeData.CoarseLowerShapeTime.cell314,ReferenceCumulativeData.CoarseLowerShapeTime.cell315,ReferenceCumulativeData.CoarseLowerShapeTime.cell316,ReferenceCumulativeData.CoarseLowerShapeTime.cell317,ReferenceCumulativeData.CoarseLowerShapeTime.cell318,ReferenceCumulativeData.CoarseLowerShapeTime.cell319] := by rfl
end OptimalG.Certificates.ReferenceExponentData.CoarseLowerShape.Batch0039
