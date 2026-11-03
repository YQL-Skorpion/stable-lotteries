import OptimalG.Certificates.IndexedBoxCover

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Head
open Set
def rootBox : Fin 5→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(1/20), (527/2000)⟩]
def leafBoxes : Fin 4→Fin 5→RatInterval := ![![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (801/1000)⟩, ⟨(97/100), (197/200)⟩, ⟨(1/20), (527/2000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (801/1000)⟩, ⟨(197/200), 1⟩, ⟨(1/20), (627/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (801/1000)⟩, ⟨(197/200), 1⟩, ⟨(627/4000), (527/2000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(801/1000), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(1/20), (527/2000)⟩]]
def coverTree : IndexedBoxCover 5 4 := (.split 2 (801/1000) (.split 3 (197/200) (.leaf 0) (.split 4 (627/4000) (.leaf 1) (.leaf 2))) (.leaf 3))
theorem checked : coverTree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 5→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
    ∃ j,∀ i,(leafBoxes j i).Contains (x i) := coverTree.covers leafBoxes rootBox checked x hx
end OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Head

namespace OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Cap
open Set
def rootBox : Fin 5→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(527/2000), (313/1000)⟩]
def leafBoxes : Fin 1→Fin 5→RatInterval := ![![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(527/2000), (313/1000)⟩]]
def coverTree : IndexedBoxCover 5 1 := (.leaf 0)
theorem checked : coverTree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 5→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
    ∃ j,∀ i,(leafBoxes j i).Contains (x i) := coverTree.covers leafBoxes rootBox checked x hx
end OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Cap

namespace OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Cone
open Set
def rootBox : Fin 5→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(313/1000), (7/20)⟩]
def leafBoxes : Fin 1→Fin 5→RatInterval := ![![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(313/1000), (7/20)⟩]]
def coverTree : IndexedBoxCover 5 1 := (.leaf 0)
theorem checked : coverTree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 5→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
    ∃ j,∀ i,(leafBoxes j i).Contains (x i) := coverTree.covers leafBoxes rootBox checked x hx
end OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Cone

namespace OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0NearLine
open Set
def rootBox : Fin 5→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(7/20), (9/25)⟩]
def leafBoxes : Fin 1→Fin 5→RatInterval := ![![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(7/20), (9/25)⟩]]
def coverTree : IndexedBoxCover 5 1 := (.leaf 0)
theorem checked : coverTree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 5→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
    ∃ j,∀ i,(leafBoxes j i).Contains (x i) := coverTree.covers leafBoxes rootBox checked x hx
end OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0NearLine

namespace OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Line
open Set
def rootBox : Fin 5→RatInterval := ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (41/50)⟩, ⟨(97/100), 1⟩, ⟨(9/25), (1227/2000)⟩]
def leafBoxes : Fin 16→Fin 5→RatInterval := ![![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (801/1000)⟩, ⟨(97/100), (197/200)⟩, ⟨(9/25), (1227/2000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (1583/2000)⟩, ⟨(197/200), (397/400)⟩, ⟨(9/25), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (1583/2000)⟩, ⟨(397/400), 1⟩, ⟨(9/25), (3387/8000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (1583/2000)⟩, ⟨(397/400), 1⟩, ⟨(3387/8000), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(1583/2000), (801/1000)⟩, ⟨(197/200), (397/400)⟩, ⟨(9/25), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(1583/2000), (801/1000)⟩, ⟨(397/400), 1⟩, ⟨(9/25), (3387/8000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(1583/2000), (801/1000)⟩, ⟨(397/400), 1⟩, ⟨(3387/8000), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(391/500), (801/1000)⟩, ⟨(197/200), 1⟩, ⟨(1947/4000), (1227/2000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(801/1000), (41/50)⟩, ⟨(97/100), (197/200)⟩, ⟨(9/25), (1227/2000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(801/1000), (1621/2000)⟩, ⟨(197/200), (397/400)⟩, ⟨(9/25), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(801/1000), (1621/2000)⟩, ⟨(397/400), 1⟩, ⟨(9/25), (3387/8000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(801/1000), (1621/2000)⟩, ⟨(397/400), 1⟩, ⟨(3387/8000), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(1621/2000), (41/50)⟩, ⟨(197/200), (397/400)⟩, ⟨(9/25), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(1621/2000), (41/50)⟩, ⟨(397/400), 1⟩, ⟨(9/25), (3387/8000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(1621/2000), (41/50)⟩, ⟨(397/400), 1⟩, ⟨(3387/8000), (1947/4000)⟩],
  ![⟨(22493/40000), (56233/100000)⟩, ⟨(227179/10000000), (11677/500000)⟩, ⟨(801/1000), (41/50)⟩, ⟨(197/200), 1⟩, ⟨(1947/4000), (1227/2000)⟩]]
def coverTree : IndexedBoxCover 5 16 := (.split 2 (801/1000) (.split 3 (197/200) (.leaf 0) (.split 4 (1947/4000) (.split 2 (1583/2000) (.split 3 (397/400) (.leaf 1) (.split 4 (3387/8000) (.leaf 2) (.leaf 3))) (.split 3 (397/400) (.leaf 4) (.split 4 (3387/8000) (.leaf 5) (.leaf 6)))) (.leaf 7))) (.split 3 (197/200) (.leaf 8) (.split 4 (1947/4000) (.split 2 (1621/2000) (.split 3 (397/400) (.leaf 9) (.split 4 (3387/8000) (.leaf 10) (.leaf 11))) (.split 3 (397/400) (.leaf 12) (.split 4 (3387/8000) (.leaf 13) (.leaf 14)))) (.leaf 15))))
theorem checked : coverTree.check leafBoxes rootBox=true := by decide +kernel
theorem covered (x : Fin 5→ℝ) (hx : ∀ i,(rootBox i).Contains (x i)) :
    ∃ j,∀ i,(leafBoxes j i).Contains (x i) := coverTree.covers leafBoxes rootBox checked x hx
end OptimalG.Certificates.HighMassTailCoverage.CurvedUpper0Line
