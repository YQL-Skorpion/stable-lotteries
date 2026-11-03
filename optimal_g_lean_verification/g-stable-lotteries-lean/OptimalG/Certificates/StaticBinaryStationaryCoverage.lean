import OptimalG.Certificates.IndexedBoxCover

namespace OptimalG.Certificates.StaticBinaryStationaryCoverage
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
namespace HeadShift
def rootBox : Fin 2→RatInterval := ![⟨(31/40), (17/20)⟩, ⟨0, (527/2000)⟩]
def leafBoxes : Fin 3→Fin 2→RatInterval := ![
  ![⟨(31/40), (13/16)⟩, ⟨0, (527/4000)⟩],
  ![⟨(31/40), (13/16)⟩, ⟨(527/4000), (527/2000)⟩],
  ![⟨(13/16), (17/20)⟩, ⟨0, (527/2000)⟩]]
def tree : IndexedBoxCover 2 3 := (.split 0 (13/16) (.split 1 (527/4000) (.leaf 0) (.leaf 1)) (.leaf 2))
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end HeadShift

namespace HeadZero
def rootBox : Fin 2→RatInterval := ![⟨(31/40), (17/20)⟩, ⟨0, (527/2000)⟩]
def leafBoxes : Fin 3→Fin 2→RatInterval := ![
  ![⟨(31/40), (13/16)⟩, ⟨0, (527/4000)⟩],
  ![⟨(31/40), (13/16)⟩, ⟨(527/4000), (527/2000)⟩],
  ![⟨(13/16), (17/20)⟩, ⟨0, (527/2000)⟩]]
def tree : IndexedBoxCover 2 3 := (.split 0 (13/16) (.split 1 (527/4000) (.leaf 0) (.leaf 1)) (.leaf 2))
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end HeadZero

namespace HeadEarlyLeft
def rootBox : Fin 2→RatInterval := ![⟨(31/40), (391/500)⟩, ⟨0, (527/2000)⟩]
def leafBoxes : Fin 10→Fin 2→RatInterval := ![
  ![⟨(31/40), (1557/2000)⟩, ⟨0, (527/4000)⟩],
  ![⟨(31/40), (3107/4000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(31/40), (3107/4000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(3107/4000), (1557/2000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(3107/4000), (1557/2000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(1557/2000), (391/500)⟩, ⟨0, (527/4000)⟩],
  ![⟨(1557/2000), (3121/4000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(1557/2000), (3121/4000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(3121/4000), (391/500)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(3121/4000), (391/500)⟩, ⟨(1581/8000), (527/2000)⟩]]
def tree : IndexedBoxCover 2 10 := (.split 0 (1557/2000) (.split 1 (527/4000) (.leaf 0) (.split 0 (3107/4000) (.split 1 (1581/8000) (.leaf 1) (.leaf 2)) (.split 1 (1581/8000) (.leaf 3) (.leaf 4)))) (.split 1 (527/4000) (.leaf 5) (.split 0 (3121/4000) (.split 1 (1581/8000) (.leaf 6) (.leaf 7)) (.split 1 (1581/8000) (.leaf 8) (.leaf 9)))))
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end HeadEarlyLeft

namespace HeadEarlyRight
def rootBox : Fin 2→RatInterval := ![⟨(391/500), (807/1000)⟩, ⟨0, (527/2000)⟩]
def leafBoxes : Fin 10→Fin 2→RatInterval := ![
  ![⟨(391/500), (1589/2000)⟩, ⟨0, (527/4000)⟩],
  ![⟨(391/500), (3153/4000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(391/500), (3153/4000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(3153/4000), (1589/2000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(3153/4000), (1589/2000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(1589/2000), (807/1000)⟩, ⟨0, (527/4000)⟩],
  ![⟨(1589/2000), (3203/4000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(1589/2000), (3203/4000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(3203/4000), (807/1000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(3203/4000), (807/1000)⟩, ⟨(1581/8000), (527/2000)⟩]]
def tree : IndexedBoxCover 2 10 := (.split 0 (1589/2000) (.split 1 (527/4000) (.leaf 0) (.split 0 (3153/4000) (.split 1 (1581/8000) (.leaf 1) (.leaf 2)) (.split 1 (1581/8000) (.leaf 3) (.leaf 4)))) (.split 1 (527/4000) (.leaf 5) (.split 0 (3203/4000) (.split 1 (1581/8000) (.leaf 6) (.leaf 7)) (.split 1 (1581/8000) (.leaf 8) (.leaf 9)))))
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end HeadEarlyRight

namespace HeadLate
def rootBox : Fin 2→RatInterval := ![⟨(807/1000), (17/20)⟩, ⟨0, (527/2000)⟩]
def leafBoxes : Fin 6→Fin 2→RatInterval := ![
  ![⟨(807/1000), (1657/2000)⟩, ⟨0, (527/4000)⟩],
  ![⟨(807/1000), (3271/4000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(807/1000), (3271/4000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(3271/4000), (1657/2000)⟩, ⟨(527/4000), (1581/8000)⟩],
  ![⟨(3271/4000), (1657/2000)⟩, ⟨(1581/8000), (527/2000)⟩],
  ![⟨(1657/2000), (17/20)⟩, ⟨0, (527/2000)⟩]]
def tree : IndexedBoxCover 2 6 := (.split 0 (1657/2000) (.split 1 (527/4000) (.leaf 0) (.split 0 (3271/4000) (.split 1 (1581/8000) (.leaf 1) (.leaf 2)) (.split 1 (1581/8000) (.leaf 3) (.leaf 4)))) (.leaf 5))
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end HeadLate

namespace CapShift
def rootBox : Fin 2→RatInterval := ![⟨(849/1000), (73/80)⟩, ⟨(527/2000), (1459/5000)⟩]
def leafBoxes : Fin 1→Fin 2→RatInterval := ![
  ![⟨(849/1000), (73/80)⟩, ⟨(527/2000), (1459/5000)⟩]]
def tree : IndexedBoxCover 2 1 := (.leaf 0)
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end CapShift

namespace CapZero
def rootBox : Fin 2→RatInterval := ![⟨(849/1000), (73/80)⟩, ⟨(527/2000), (1459/5000)⟩]
def leafBoxes : Fin 1→Fin 2→RatInterval := ![
  ![⟨(849/1000), (73/80)⟩, ⟨(527/2000), (1459/5000)⟩]]
def tree : IndexedBoxCover 2 1 := (.leaf 0)
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end CapZero

namespace CapCurvature
def rootBox : Fin 2→RatInterval := ![⟨(86242083/100000000), (73/80)⟩, ⟨(527/2000), (1459/5000)⟩]
def leafBoxes : Fin 1→Fin 2→RatInterval := ![
  ![⟨(86242083/100000000), (73/80)⟩, ⟨(527/2000), (1459/5000)⟩]]
def tree : IndexedBoxCover 2 1 := (.leaf 0)
theorem checked : tree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 2→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
  ∃ j,∀ i,(leafBoxes j i).Contains (x i) := tree.covers leafBoxes rootBox checked x hx
end CapCurvature

end OptimalG.Certificates.StaticBinaryStationaryCoverage
