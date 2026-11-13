import Metastability.PairClock
import Metastability.TwoParticle

/-! Exact finite-two specializations of the source-facing definitions. -/

noncomputable section
open scoped RealInnerProductSpace
namespace Metastability.TwoParticleSource
variable {d : ℕ}

def configuration (x y : Source.Sphere d) : Source.Configuration 2 d := ![x, y]

theorem energy_eq (β : ℝ) (x y : Source.Sphere d) :
    Source.energy β (configuration x y) =
      TwoParticle.twoParticleEnergy β x.val y.val := by
  simp [Source.energy, configuration, Fin.sum_univ_two, TwoParticle.twoParticleEnergy]
  ring

theorem vectorField_zero (β : ℝ) (x y : Source.Sphere d) :
    Source.vectorField .usa β (configuration x y) 0 =
      TwoParticle.twoParticleVelocityWithSelf β x.val y.val := by
  simp [Source.vectorField, Source.coefficient, Source.projectTangent,
    configuration, Fin.sum_univ_two, TwoParticle.twoParticleVelocityWithSelf,
    TwoParticle.projection, inner_add_right, inner_smul_right]
  module

theorem vectorField_one (β : ℝ) (x y : Source.Sphere d) :
    Source.vectorField .usa β (configuration x y) 1 =
      TwoParticle.twoParticleVelocityWithSelf β y.val x.val := by
  simp [Source.vectorField, Source.coefficient, Source.projectTangent,
    configuration, Fin.sum_univ_two, TwoParticle.twoParticleVelocityWithSelf,
    TwoParticle.projection, inner_add_right, inner_smul_right]
  module

theorem angularDist_comm (x y : Source.Sphere d) :
    Source.angularDist x y = Source.angularDist y x := by
  simp [Source.angularDist, real_inner_comm]

theorem clockFactor_eq (β : ℝ) (x y : Source.Sphere d) :
    Source.clockFactor β (configuration x y) = PairClock.rate β x y := by
  classical
  have hp : Source.eligiblePairs β (configuration x y) =
      if Source.clockCutoff β < Source.angularDist x y then {(0, 1), (1, 0)} else ∅ := by
    by_cases h : Source.clockCutoff β < Source.angularDist x y <;>
      ext ⟨i,j⟩ <;> fin_cases i <;> fin_cases j <;>
      simp [Source.eligiblePairs, configuration, angularDist_comm y x, h]
  unfold Source.clockFactor
  simp only [hp]
  by_cases h : Source.clockCutoff β < Source.angularDist x y
  · simp [h, configuration, PairClock.rate, real_inner_comm x.val y.val]
  · simp [h, PairClock.rate]

end Metastability.TwoParticleSource
