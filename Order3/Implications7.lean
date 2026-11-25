import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation127_151_229_implies_Equation66 (G : Type*) [Magma G] (h127 : Equation127 G) (h151 : Equation151 G) (h229 : Equation229 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h127 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h127 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 ((X1 ◇ X0) ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l6 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l2 X1 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l5 X0 X1]
    conv => enter [1, 1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X1 (X0 ◇ X0)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l11 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l15 X1 X0]
  intro x y
  conv => enter [1]; rw [← l16 y x]

theorem Equation127_151_229_implies_Equation118 (G : Type*) [Magma G] (h127 : Equation127 G) (h151 : Equation151 G) (h229 : Equation229 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h127 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h127 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 ((X1 ◇ X0) ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l6 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l2 X1 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l5 X0 X1]
    conv => enter [1, 1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X1 (X0 ◇ X0)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l11 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l7 X1 X0]
    conv => enter [1, 2]; rw [l15 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1]; rw [l16 y (x ◇ y)]

theorem Equation127_151_229_implies_Equation212 (G : Type*) [Magma G] (h127 : Equation127 G) (h151 : Equation151 G) (h229 : Equation229 G) : Equation212 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h229 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h127 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l2 (X1 ◇ X1) (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h127 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 ((X1 ◇ X0) ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l6 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l2 X1 (X0 ◇ X0)]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l5 X0 X1]
    conv => enter [1, 1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X1 (X0 ◇ X0)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l11 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l15 X1 (X0 ◇ X1)]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l15 X1 X0]
  intro x y
  conv => enter [1]; rw [← l17 y x]
  conv => enter [1]; rw [l16 y (x ◇ (y ◇ y))]

theorem Equation108_203_264_implies_Equation56 (G : Type*) [Magma G] (h108 : Equation108 G) (h203 : Equation203 G) (h264 : Equation264 G) : Equation56 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h108 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation75_99_231_implies_Equation283 (G : Type*) [Magma G] (h75 : Equation75 G) (h99 : Equation99 G) (h231 : Equation231 G) : Equation283 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h75 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h99 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h231 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation75_264_273_implies_Equation159 (G : Type*) [Magma G] (h75 : Equation75 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation159 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h273 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 1, 1]; rw [← h75 sK1 sK0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h264 (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h273 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h273 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h264 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h264 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation53_75_264_implies_Equation159 (G : Type*) [Magma G] (h53 : Equation53 G) (h75 : Equation75 G) (h264 : Equation264 G) : Equation159 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53 ((sK1 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h264 sK1 sK0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h75 ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h53 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53 ((sK1 ◇ sK0) ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) ((sK1 ◇ sK0) ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h75 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h75 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation75_99_283_implies_Equation231 (G : Type*) [Magma G] (h75 : Equation75 G) (h99 : Equation99 G) (h283 : Equation283 G) : Equation231 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h75 ((X0 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1]
    conv => enter [1]; rw [← h283 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation56_203_264_implies_Equation108 (G : Type*) [Magma G] (h56 : Equation56 G) (h203 : Equation203 G) (h264 : Equation264 G) : Equation108 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h264 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1]
    conv => enter [1]; rw [← h56 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation75_151_212_264_implies_Equation56 (G : Type*) [Magma G] (h75 : Equation75 G) (h151 : Equation151 G) (h212 : Equation212 G) (h264 : Equation264 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h75 X0 X1]
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ (X1 ◇ X0)) X1]
  have l3 : ∀ X2 X1 X0 : G, ((X2 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ X1))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X2 (X1 ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1 X1]
    conv => enter [1]; rw [← h264 X0 (X1 ◇ (X1 ◇ X1))]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation75_127_151_203_264_implies_Equation56 (G : Type*) [Magma G] (h75 : Equation75 G) (h127 : Equation127 G) (h151 : Equation151 G) (h203 : Equation203 G) (h264 : Equation264 G) : Equation56 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h264 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h127 X0 X1]
  have l4 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h264 X0 X1]
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← l5 ((X0 ◇ X1) ◇ X1) X1]
  have l7 : ∀ X1 X0 X2 : G, (((X1 ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X2)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X2]
  have l8 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X1 X1 X0]
    conv => enter [1]; rw [← h75 X0 ((X1 ◇ X1) ◇ X1)]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1, 1]; rw [← l8 X1 X0]
    conv => enter [1, 1, 2, 1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l4 ((X1 ◇ X1) ◇ X1) X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 x y]
  conv => enter [1, 2]; rw [l0 y]

theorem Equation66_151_273_281_implies_Equation53 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h273 : Equation273 G) (h281 : Equation281 G) : Equation53 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h281 X0 X1]
    conv => enter [1]; rw [← h273 X1 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h281 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h66 (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2, 1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [h66 x x]
  conv => enter [1, 2]; rw [l3 x y]

theorem Equation53_66_151_281_implies_Equation273 (G : Type*) [Magma G] (h53 : Equation53 G) (h66 : Equation66 G) (h151 : Equation151 G) (h281 : Equation281 G) : Equation273 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h66 X0 X1]
    conv => enter [1]; rw [← h53 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h281 ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1, 2]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [h281 x x]
  conv => enter [1, 1]; rw [l3 x y]

theorem Equation66_151_264_281_implies_Equation75 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h264 : Equation264 G) (h281 : Equation281 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h281 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X1) ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h66 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2]; rw [l0 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  intro x y
  conv => enter [1]; rw [h66 x y]
  conv => enter [1, 2]; rw [l2 x y]

theorem Equation66_75_151_281_implies_Equation264 (G : Type*) [Magma G] (h66 : Equation66 G) (h75 : Equation75 G) (h151 : Equation151 G) (h281 : Equation281 G) : Equation264 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h66 X0 X1]
    conv => enter [1]; rw [← h75 (X0 ◇ (X1 ◇ X1)) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h281 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  intro x y
  conv => enter [1]; rw [h281 x y]
  conv => enter [1, 1]; rw [l2 y x]

theorem Equation66_151_203_implies_Equation99 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h203 : Equation203 G) : Equation99 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2]; rw [h203 (X0 ◇ X0)]
    conv => enter [1]; rw [← h66 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h151 X0]
  intro x
  conv => enter [1]; rw [h66 x x]
  conv => enter [1, 2]; rw [l1 x]

theorem Equation99_151_281_implies_Equation203 (G : Type*) [Magma G] (h99 : Equation99 G) (h151 : Equation151 G) (h281 : Equation281 G) : Equation203 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h99 (X0 ◇ X0)]
    conv => enter [1]; rw [← h281 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1, 1]; rw [h151 X0]
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h151 X0]
  intro x
  conv => enter [1]; rw [h281 x x]
  conv => enter [1, 1]; rw [l1 x]

theorem Equation66_167_281_implies_Equation2 (G : Type*) [Magma G] (h66 : Equation66 G) (h167 : Equation167 G) (h281 : Equation281 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← h66 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h167 X0 X0]
    conv => enter [1]; rw [← h281 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, ((((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ (X1 ◇ X1)) ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l2 X1 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation231_281_implies_Equation56 (G : Type*) [Magma G] (h231 : Equation231 G) (h281 : Equation281 G) : Equation56 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h231 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h281 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h231 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation66_108_implies_Equation283 (G : Type*) [Magma G] (h66 : Equation66 G) (h108 : Equation108 G) : Equation283 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h108 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h66 X1 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h108 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation151_212_281_implies_Equation43 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h281 : Equation281 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h281 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h151 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation66_151_212_281_implies_Equation127 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h212 : Equation212 G) (h281 : Equation281 G) : Equation127 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h281 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 (((X1 ◇ X1) ◇ (X1 ◇ X1)) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h151 X1]
  intro x y
  conv => enter [1]; rw [h66 x y]
  conv => enter [1, 2]; rw [l1 x (y ◇ y)]

theorem Equation66_127_151_implies_Equation43 (G : Type*) [Magma G] (h66 : Equation66 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation43 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h66 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h127 (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h151 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation66_127_151_281_implies_Equation212 (G : Type*) [Magma G] (h66 : Equation66 G) (h127 : Equation127 G) (h151 : Equation151 G) (h281 : Equation281 G) : Equation212 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h66 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h127 (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h151 X1]
  intro x y
  conv => enter [1]; rw [h281 x y]
  conv => enter [1, 1]; rw [l1 (y ◇ y) x]

theorem Equation66_118_222_281_implies_Equation73 (G : Type*) [Magma G] (h66 : Equation66 G) (h118 : Equation118 G) (h222 : Equation222 G) (h281 : Equation281 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h281 ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h281 X0 X1]
    conv => enter [1]; rw [← h118 ((X1 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h66 X0 X1]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l2 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h66 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X0]
    conv => enter [1, 1, 2]; rw [h118 X0 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← l4 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [← h66 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h222 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 y x]

theorem Equation66_118_222_281_implies_Equation125 (G : Type*) [Magma G] (h66 : Equation66 G) (h118 : Equation118 G) (h222 : Equation222 G) (h281 : Equation281 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h281 ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h281 X0 X1]
    conv => enter [1]; rw [← h118 ((X1 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h66 X0 X1]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l2 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h66 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X0]
    conv => enter [1, 1, 2]; rw [h118 X0 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← l4 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [← h66 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h222 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l11 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [← l13 y x]
  conv => enter [1, 2]; rw [l11 y (y ◇ x)]

theorem Equation66_118_222_281_implies_Equation127 (G : Type*) [Magma G] (h66 : Equation66 G) (h118 : Equation118 G) (h222 : Equation222 G) (h281 : Equation281 G) : Equation127 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h281 ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h281 X0 X1]
    conv => enter [1]; rw [← h118 ((X1 ◇ X1) ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h66 X0 X1]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X0 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l2 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h66 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X0]
    conv => enter [1, 1, 2]; rw [h118 X0 X0]
    conv => enter [1]; rw [← l5 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← l4 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [← h66 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h222 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 y x]
  conv => enter [1, 2]; rw [l2 y x]

theorem Equation66_151_229_implies_Equation118 (G : Type*) [Magma G] (h66 : Equation66 G) (h151 : Equation151 G) (h229 : Equation229 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h66 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h66 ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0)) X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 (X1 ◇ X0) X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h66 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2]; rw [← l1 X0 (X1 ◇ X1)]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l9 (X0 ◇ X1) X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [l9 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l9 X1 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l9 (X1 ◇ X0) X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l9 X1 (X1 ◇ (X0 ◇ X1))]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [← l13 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X1) X1]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l15 (X0 ◇ (X1 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← l15 X0 (X0 ◇ X1)]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← h66 (X0 ◇ X1) X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l19 (X1 ◇ X0) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l17 X1 X0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [l19 (X0 ◇ (X1 ◇ X1)) (X1 ◇ X0)]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l22 X0 X1]
    conv => enter [1]; rw [l21 X1 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l19 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l24 X0 X1]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l19 X0 X1]
    conv => enter [1]; rw [l25 X0 X1]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l25 X1 X0]
    conv => enter [1, 2]; rw [l26 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l25 y x]
  conv => enter [1]; rw [l27 y (x ◇ y)]

theorem Equation56_283_implies_Equation108 (G : Type*) [Magma G] (h56 : Equation56 G) (h283 : Equation283 G) : Equation108 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h283 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h56 X1 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h283 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation56_283_implies_Equation231 (G : Type*) [Magma G] (h56 : Equation56 G) (h283 : Equation283 G) : Equation231 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h56 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation56_280_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h280 : Equation280 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h280 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h56 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h56 (X1 ◇ X1) X0]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l1 X1 X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h56 X1 X1]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h56 X1 X2]
  have l5 : ∀ X1 X2 : G, (X1 ◇ X2) = X1 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h56 X2 X1]
    conv => enter [1]; rw [l4 X1 X2 X1]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l2 X1 X0 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [l5 X2 X2]
  have l8 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l7 ((X0 ◇ X0) ◇ X2) X2 X0]
    conv => enter [1]; rw [← h280 X2 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation50_283_implies_Equation2 (G : Type*) [Magma G] (h50 : Equation50 G) (h283 : Equation283 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2]; rw [← h283 (X1 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h283 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 X2 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l1 X1 X2]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  have l4 : ∀ X0 X2 X1 : G, ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X1 := by
    intro X0 X2 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h283 X1 X2]
  have l5 : ∀ X2 X1 : G, (X2 ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1, 1]; rw [h283 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l5 X2 X2]
  have l8 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l7 X2 (X2 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h50 X2 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation56_273_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [← h56 ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h56 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h56 X1 X1]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h56 X1 X2]
  have l4 : ∀ X1 X2 : G, (X1 ◇ X2) = X1 := by
    intro X1 X2
    conv => enter [1, 2]; rw [h56 X2 X1]
    conv => enter [1]; rw [l3 X1 X2 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation53_283_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h283 : Equation283 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h283 (X1 ◇ (((X0 ◇ X0) ◇ X0) ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h283 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h283 X1 X0]
  have l3 : ∀ X0 X2 X1 : G, ((((X0 ◇ X0) ◇ X0) ◇ X2) ◇ X1) = X1 := by
    intro X0 X2 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X2]
    conv => enter [1]; rw [← h283 X1 X2]
  have l4 : ∀ X2 X1 : G, (X2 ◇ X1) = X1 := by
    intro X2 X1
    conv => enter [1, 1]; rw [h283 X2 X2]
    conv => enter [1]; rw [l3 X2 X2 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation53_280_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h280 : Equation280 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h280 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 1]; rw [← h53 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 1, 2]; rw [← h280 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h53 X1 X1]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l4 X0 X0]
    conv => enter [1]; rw [← h280 X0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l7 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l9 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation50_273_implies_Equation2 (G : Type*) [Magma G] (h50 : Equation50 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X1) = (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h50 ((X1 ◇ (X0 ◇ X0)) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h273 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 1, 2, 1]; rw [← h50 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h273 X1 X1]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l4 X0 X0]
    conv => enter [1]; rw [← h50 X0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l7 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l9 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation53_151_264_273_implies_Equation66 (G : Type*) [Magma G] (h53 : Equation53 G) (h151 : Equation151 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h273 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X0) ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2, 1]; rw [← h53 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [l3 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l5 X1 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 ((X1 ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [l1 X1 X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l8 X1 X2]
  have l11 : ∀ X2 X0 X1 : G, ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 1, 2]; rw [l7 X0 X1 X1]
    conv => enter [1]; rw [l9 X2 X1]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l10 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l12 X1 X0 X2]
    conv => enter [1]; rw [← h53 X1 X0]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ ((X1 ◇ X2) ◇ X0)) ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l10 X0 (X1 ◇ X2) X1]
    conv => enter [1]; rw [l11 X1 X1 X2]
  have l15 : ∀ X1 X0 X2 : G, ((X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 1, 2, 1]; rw [l6 X0 X2]
    conv => enter [1]; rw [l14 X1 (X2 ◇ (X0 ◇ X0)) X2]
  have l16 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := by
    intro X0 X2
    conv => enter [1, 1]; rw [← l13 X0 X0 X0]
    conv => enter [1]; rw [l15 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l16 y x]

theorem Equation53_75_151_273_implies_Equation66 (G : Type*) [Magma G] (h53 : Equation53 G) (h75 : Equation75 G) (h151 : Equation151 G) (h273 : Equation273 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h53 X1 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X0 ◇ X1)) X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1, 2]; rw [← h273 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [l3 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← l5 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [l1 X1 X1]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l8 X1 X2]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [l7 X0 X1 X1]
    conv => enter [1]; rw [l9 X2 X1]
  have l12 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l10 X1 ((X0 ◇ X1) ◇ X0) X2]
  have l13 : ∀ X2 X0 X1 : G, ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l12 X0 X1 X2]
    conv => enter [1]; rw [← h273 X1 X0]
  have l14 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l10 X0 (X2 ◇ X1) X1]
    conv => enter [1]; rw [l11 X1 X1 X2]
  have l15 : ∀ X0 X2 X1 : G, (((X0 ◇ X0) ◇ X2) ◇ ((X1 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1)) = X2 := by
    intro X0 X2 X1
    conv => enter [1, 2, 1, 2]; rw [l6 X0 X2]
    conv => enter [1]; rw [l14 ((X0 ◇ X0) ◇ X2) X1 X2]
  have l16 : ∀ X0 X2 : G, (((X0 ◇ X0) ◇ X2) ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l13 X0 X0 X0]
    conv => enter [1]; rw [l15 X0 X2 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l16 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l11 X0 (X0 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l17 y x]

theorem Equation50_280_implies_Equation40 (G : Type*) [Magma G] (h50 : Equation50 G) (h280 : Equation280 G) : Equation40 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h50 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h50 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h280 ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h50 (X0 ◇ X0) sK1]
  have l2 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) = (((X0 ◇ X0) ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h50 ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← h280 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h280 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l2 X0 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h50 (X0 ◇ X0) sK1]
    conv => enter [1]; rw [← l1 X0 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l3 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation43_359_implies_Equation307 (G : Type*) [Magma G] (h43 : Equation43 G) (h359 : Equation359 G) : Equation307 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h359 X0]
    conv => enter [1]; rw [h43 (X0 ◇ X0) X0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation43_307_implies_Equation359 (G : Type*) [Magma G] (h43 : Equation43 G) (h307 : Equation307 G) : Equation359 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h307 X0]
    conv => enter [1]; rw [h43 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation43_385_implies_Equation335 (G : Type*) [Magma G] (h43 : Equation43 G) (h385 : Equation385 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_325_implies_Equation335 (G : Type*) [Magma G] (h43 : Equation43 G) (h325 : Equation325 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1, 2]; rw [h43 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [h43 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [l1 y x]
  conv => enter [1]; rw [h43 (y ◇ x) y]

theorem Equation43_384_implies_Equation335 (G : Type*) [Magma G] (h43 : Equation43 G) (h384 : Equation384 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1, 1]; rw [h43 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [l1 y x]

theorem Equation43_384_implies_Equation325 (G : Type*) [Magma G] (h43 : Equation43 G) (h384 : Equation384 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_335_implies_Equation384 (G : Type*) [Magma G] (h43 : Equation43 G) (h335 : Equation335 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1, 2]; rw [h43 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [l1 y x]

theorem Equation43_378_implies_Equation335 (G : Type*) [Magma G] (h43 : Equation43 G) (h378 : Equation378 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [h43 X1 X0]
  intro x y
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [l1 y x]

theorem Equation43_323_implies_Equation335 (G : Type*) [Magma G] (h43 : Equation43 G) (h323 : Equation323 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [h43 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [l0 y x]
  conv => enter [1]; rw [h43 (y ◇ x) y]

theorem Equation43_377_implies_Equation335 (G : Type*) [Magma G] (h43 : Equation43 G) (h377 : Equation377 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [l0 y x]

theorem Equation43_333_implies_Equation335 (G : Type*) [Magma G] (h43 : Equation43 G) (h333 : Equation333 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h333 X1 X0]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 1]; rw [h43 x y]
  conv => enter [1]; rw [h43 (y ◇ x) y]

theorem Equation43_375_implies_Equation332 (G : Type*) [Magma G] (h43 : Equation43 G) (h375 : Equation375 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_326_implies_Equation332 (G : Type*) [Magma G] (h43 : Equation43 G) (h326 : Equation326 G) : Equation332 G := by
  intro x y
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation43_367_implies_Equation310 (G : Type*) [Magma G] (h43 : Equation43 G) (h367 : Equation367 G) : Equation310 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 X0 X1]
    conv => enter [1]; rw [h43 (X1 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_310_implies_Equation367 (G : Type*) [Magma G] (h43 : Equation43 G) (h310 : Equation310 G) : Equation367 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h310 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_365_implies_Equation313 (G : Type*) [Magma G] (h43 : Equation43 G) (h365 : Equation365 G) : Equation313 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 X0 X1]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation43_313_implies_Equation365 (G : Type*) [Magma G] (h43 : Equation43 G) (h313 : Equation313 G) : Equation365 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h313 X0 X1]
    conv => enter [1]; rw [h43 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [h43 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation43_364_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h364 : Equation364 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h364 X0 X1]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation43_308_implies_Equation364 (G : Type*) [Magma G] (h43 : Equation43 G) (h308 : Equation308 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h308 X0 X1]
    conv => enter [1]; rw [h43 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [h43 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation43_362_implies_Equation313 (G : Type*) [Magma G] (h43 : Equation43 G) (h362 : Equation362 G) : Equation313 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h362 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_315_implies_Equation313 (G : Type*) [Magma G] (h43 : Equation43 G) (h315 : Equation315 G) : Equation313 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h315 X0 X1]
    conv => enter [1]; rw [h43 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 1]; rw [h43 y x]
  conv => enter [1]; rw [h43 (x ◇ y) y]

theorem Equation43_361_implies_Equation309 (G : Type*) [Magma G] (h43 : Equation43 G) (h361 : Equation361 G) : Equation309 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2]; rw [h43 x y]

theorem Equation43_361_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h361 : Equation361 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation43_309_implies_Equation361 (G : Type*) [Magma G] (h43 : Equation43 G) (h309 : Equation309 G) : Equation361 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 1]; rw [h43 y x]

theorem Equation43_307_360_implies_Equation316 (G : Type*) [Magma G] (h43 : Equation43 G) (h307 : Equation307 G) (h360 : Equation360 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h307 y]

theorem Equation43_312_implies_Equation316 (G : Type*) [Magma G] (h43 : Equation43 G) (h312 : Equation312 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [h43 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h312 y y]

theorem Equation43_312_359_implies_Equation368 (G : Type*) [Magma G] (h43 : Equation43 G) (h312 : Equation312 G) (h359 : Equation359 G) : Equation368 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 X1]
    conv => enter [1]; rw [h43 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h359 y]

theorem Equation43_370_implies_Equation311 (G : Type*) [Magma G] (h43 : Equation43 G) (h370 : Equation370 G) : Equation311 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h370 X0 X1 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X2) X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation43_311_implies_Equation370 (G : Type*) [Magma G] (h43 : Equation43 G) (h311 : Equation311 G) : Equation370 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X1) ◇ X0) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h311 X0 X2 X1]
    conv => enter [1]; rw [h43 X0 (X2 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation43_255_implies_Equation47 (G : Type*) [Magma G] (h43 : Equation43 G) (h255 : Equation255 G) : Equation47 G := by
  have l0 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation43_255_implies_Equation99 (G : Type*) [Magma G] (h43 : Equation43 G) (h255 : Equation255 G) : Equation99 G := by
  have l0 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]
  conv => enter [1, 2]; rw [h43 x (x ◇ x)]

theorem Equation43_255_implies_Equation203 (G : Type*) [Magma G] (h43 : Equation43 G) (h255 : Equation255 G) : Equation203 G := by
  have l0 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h255 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]
  conv => enter [1]; rw [h43 x (x ◇ (x ◇ x))]

theorem Equation43_47_implies_Equation255 (G : Type*) [Magma G] (h43 : Equation43 G) (h47 : Equation47 G) : Equation255 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h43 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h47 X0]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h43 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation43_203_implies_Equation47 (G : Type*) [Magma G] (h43 : Equation43 G) (h203 : Equation203 G) : Equation47 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h43 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation43_99_implies_Equation47 (G : Type*) [Magma G] (h43 : Equation43 G) (h99 : Equation99 G) : Equation47 G := by
  have l0 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h43 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l0 x]
  conv => enter [1, 1]; rw [h43 (x ◇ x) x]
  conv => enter [1]; rw [h43 (x ◇ (x ◇ x)) x]

theorem Equation43_167_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h167 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l0 X1 X2]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_166_implies_Equation153 (G : Type*) [Magma G] (h43 : Equation43 G) (h166 : Equation166 G) : Equation153 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← h166 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_166_implies_Equation156 (G : Type*) [Magma G] (h43 : Equation43 G) (h166 : Equation166 G) : Equation156 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h166 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [h43 (x ◇ x) (x ◇ y)]

theorem Equation43_166_implies_Equation152 (G : Type*) [Magma G] (h43 : Equation43 G) (h166 : Equation166 G) : Equation152 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h166 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_152_implies_Equation153 (G : Type*) [Magma G] (h43 : Equation43 G) (h152 : Equation152 G) : Equation153 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 X1 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [h43 (y ◇ x) (x ◇ x)]

theorem Equation43_152_implies_Equation156 (G : Type*) [Magma G] (h43 : Equation43 G) (h152 : Equation152 G) : Equation156 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1]; rw [← h152 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_152_implies_Equation166 (G : Type*) [Magma G] (h43 : Equation43 G) (h152 : Equation152 G) : Equation166 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 X1 X0]
    conv => enter [1]; rw [← h152 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation43_159_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h159 : Equation159 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h159 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l0 X1 X2]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_156_implies_Equation153 (G : Type*) [Magma G] (h43 : Equation43 G) (h156 : Equation156 G) : Equation153 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2]; rw [h43 x y]

theorem Equation43_156_implies_Equation152 (G : Type*) [Magma G] (h43 : Equation43 G) (h156 : Equation156 G) : Equation152 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h156 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_153_implies_Equation156 (G : Type*) [Magma G] (h43 : Equation43 G) (h153 : Equation153 G) : Equation156 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h153 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 1]; rw [h43 y x]

theorem Equation43_283_implies_Equation56 (G : Type*) [Magma G] (h43 : Equation43 G) (h283 : Equation283 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [← h283 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_56_implies_Equation283 (G : Type*) [Magma G] (h43 : Equation43 G) (h56 : Equation56 G) : Equation283 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h56 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 ((X1 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation43_280_implies_Equation50 (G : Type*) [Magma G] (h43 : Equation43 G) (h280 : Equation280 G) : Equation50 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h280 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_280_implies_Equation107 (G : Type*) [Magma G] (h43 : Equation43 G) (h280 : Equation280 G) : Equation107 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h280 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_280_implies_Equation211 (G : Type*) [Magma G] (h43 : Equation43 G) (h280 : Equation280 G) : Equation211 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h280 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [h43 x (x ◇ (y ◇ y))]

theorem Equation43_50_implies_Equation280 (G : Type*) [Magma G] (h43 : Equation43 G) (h50 : Equation50 G) : Equation280 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [← h50 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation43_264_implies_Equation73 (G : Type*) [Magma G] (h43 : Equation43 G) (h264 : Equation264 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h264 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation43_264_implies_Equation118 (G : Type*) [Magma G] (h43 : Equation43 G) (h264 : Equation264 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h264 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2]; rw [h43 y (x ◇ y)]

theorem Equation43_75_implies_Equation73 (G : Type*) [Magma G] (h43 : Equation43 G) (h75 : Equation75 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h75 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 1, 1]; rw [h43 y x]
  conv => enter [1, 1]; rw [h43 (x ◇ y) y]
  conv => enter [1]; rw [h43 (y ◇ (x ◇ y)) y]

theorem Equation43_231_implies_Equation56 (G : Type*) [Magma G] (h43 : Equation43 G) (h231 : Equation231 G) : Equation56 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h231 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_108_implies_Equation56 (G : Type*) [Magma G] (h43 : Equation43 G) (h108 : Equation108 G) : Equation56 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 ((X1 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h108 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 1]; rw [h43 (y ◇ y) y]
  conv => enter [1]; rw [h43 (y ◇ (y ◇ y)) x]

theorem Equation43_229_implies_Equation73 (G : Type*) [Magma G] (h43 : Equation43 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h229 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 2, 2]; rw [h43 y x]

theorem Equation43_229_implies_Equation118 (G : Type*) [Magma G] (h43 : Equation43 G) (h229 : Equation229 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2]; rw [h43 y (x ◇ y)]

theorem Equation43_118_implies_Equation73 (G : Type*) [Magma G] (h43 : Equation43 G) (h118 : Equation118 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1]; rw [← h118 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 1]; rw [h43 (x ◇ y) y]
  conv => enter [1]; rw [h43 (y ◇ (x ◇ y)) y]

theorem Equation43_118_implies_Equation125 (G : Type*) [Magma G] (h43 : Equation43 G) (h118 : Equation118 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h43 X1 X0]
    conv => enter [1]; rw [← h118 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [h43 ((y ◇ x) ◇ y) y]

theorem Equation43_211_implies_Equation50 (G : Type*) [Magma G] (h43 : Equation43 G) (h211 : Equation211 G) : Equation50 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h211 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_107_implies_Equation50 (G : Type*) [Magma G] (h43 : Equation43 G) (h107 : Equation107 G) : Equation50 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h107 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 1]; rw [h43 (y ◇ y) x]
  conv => enter [1]; rw [h43 (x ◇ (y ◇ y)) x]

theorem Equation43_212_implies_Equation66 (G : Type*) [Magma G] (h43 : Equation43 G) (h212 : Equation212 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h212 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation43_127_implies_Equation66 (G : Type*) [Magma G] (h43 : Equation43 G) (h127 : Equation127 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← h127 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 1]; rw [h43 (y ◇ y) x]
  conv => enter [1]; rw [h43 (x ◇ (y ◇ y)) y]

theorem Equation43_66_implies_Equation127 (G : Type*) [Magma G] (h43 : Equation43 G) (h66 : Equation66 G) : Equation127 G := by
  intro x y
  conv => enter [1]; rw [h66 x y]
  conv => enter [1, 2]; rw [h43 x (y ◇ y)]

theorem Equation40_359_implies_Equation368 (G : Type*) [Magma G] (h40 : Equation40 G) (h359 : Equation359 G) : Equation368 G := by
  intro x y
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h359 y]

theorem Equation40_307_implies_Equation316 (G : Type*) [Magma G] (h40 : Equation40 G) (h307 : Equation307 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h307 y]

theorem Equation40_361_implies_Equation371 (G : Type*) [Magma G] (h40 : Equation40 G) (h361 : Equation361 G) : Equation371 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h361 y z]

theorem Equation40_309_implies_Equation319 (G : Type*) [Magma G] (h40 : Equation40 G) (h309 : Equation309 G) : Equation319 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h309 y z]

theorem Equation40_370_implies_Equation366 (G : Type*) [Magma G] (h40 : Equation40 G) (h370 : Equation370 G) : Equation366 G := by
  intro x y z
  conv => enter [1]; rw [h40 x z]
  conv => enter [1]; rw [h370 z y x]

theorem Equation40_311_implies_Equation314 (G : Type*) [Magma G] (h40 : Equation40 G) (h311 : Equation311 G) : Equation314 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h311 y x z]

theorem Equation40_363_implies_Equation366 (G : Type*) [Magma G] (h40 : Equation40 G) (h363 : Equation363 G) : Equation366 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h363 y x z]

theorem Equation40_318_implies_Equation314 (G : Type*) [Magma G] (h40 : Equation40 G) (h318 : Equation318 G) : Equation314 G := by
  intro x y z
  conv => enter [1]; rw [h40 x z]
  conv => enter [1]; rw [h318 z y x]

theorem Equation40_255_implies_Equation280 (G : Type*) [Magma G] (h40 : Equation40 G) (h255 : Equation255 G) : Equation280 G := by
  intro x y
  conv => enter [1]; rw [h255 x]
  conv => enter [1, 1, 1]; rw [h40 x y]

theorem Equation40_47_implies_Equation50 (G : Type*) [Magma G] (h40 : Equation40 G) (h47 : Equation47 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h47 x]
  conv => enter [1, 2, 2]; rw [h40 x y]

theorem Equation40_264_273_implies_Equation11 (G : Type*) [Magma G] (h40 : Equation40 G) (h264 : Equation264 G) (h273 : Equation273 G) : Equation11 G := by
  have l0 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1, 1, 1]; rw [h40 sK0 X0]
    conv => enter [1]; rw [← h264 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h273 (sK0 ◇ sK0) sK1]
    conv => enter [1, 1, 1, 2]; rw [h40 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 1, 1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h264 ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (((sK0 ◇ sK0) ◇ sK1) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h264 (sK1 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1, 1, 1]; rw [← l3 sK0 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK2 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation40_53_75_implies_Equation31 (G : Type*) [Magma G] (h40 : Equation40 G) (h53 : Equation53 G) (h75 : Equation75 G) : Equation31 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = X0 := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [h40 sK0 X0]
    conv => enter [1]; rw [← h75 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2, 1]; rw [h40 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h75 (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK2 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h75 ((sK2 ◇ sK2) ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1 sK2]
  have l5 : ∀ sK1 sK2 : G, sK1 = ((sK2 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [← l4 sK2 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation40_203_implies_Equation211 (G : Type*) [Magma G] (h40 : Equation40 G) (h203 : Equation203 G) : Equation211 G := by
  intro x y
  conv => enter [1]; rw [h203 x]
  conv => enter [1, 1, 2]; rw [h40 x y]

theorem Equation40_99_implies_Equation107 (G : Type*) [Magma G] (h40 : Equation40 G) (h99 : Equation99 G) : Equation107 G := by
  intro x y
  conv => enter [1]; rw [h99 x]
  conv => enter [1, 2, 1]; rw [h40 x y]

theorem Equation40_231_implies_Equation246 (G : Type*) [Magma G] (h40 : Equation40 G) (h231 : Equation231 G) : Equation246 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X2) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 1, 2]; rw [h40 X0 X1]
    conv => enter [1]; rw [← h231 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation40_231_implies_Equation316 (G : Type*) [Magma G] (h40 : Equation40 G) (h231 : Equation231 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h40 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h231 (X0 ◇ (X0 ◇ X0)) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation40_108_implies_Equation109 (G : Type*) [Magma G] (h40 : Equation40 G) (h108 : Equation108 G) : Equation109 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X0) ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [h40 X0 X1]
    conv => enter [1]; rw [← h108 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l0 x y z]

theorem Equation40_108_implies_Equation368 (G : Type*) [Magma G] (h40 : Equation40 G) (h108 : Equation108 G) : Equation368 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h40 X1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h108 ((X0 ◇ X0) ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation40_205_211_221_implies_Equation246 (G : Type*) [Magma G] (h40 : Equation40 G) (h205 : Equation205 G) (h211 : Equation211 G) (h221 : Equation221 G) : Equation246 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h205 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h221 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h205 X0 X1]
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h205 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h40 X0 X1]
    conv => enter [1]; rw [l2 X1 X2]
    conv => enter [1, 2]; rw [h40 X1 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (((X2 ◇ (X0 ◇ X2)) ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 (X2 ◇ (X0 ◇ X2)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X1 X0]
    conv => enter [1, 1]; rw [← h221 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h211 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l6 z x]
  conv => enter [1, 1]; rw [l5 z y]

theorem Equation40_104_105_107_implies_Equation109 (G : Type*) [Magma G] (h40 : Equation40 G) (h104 : Equation104 G) (h105 : Equation105 G) (h107 : Equation107 G) : Equation109 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h105 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h104 X0 X1]
    conv => enter [1]; rw [l1 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h104 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X2 ◇ X1) ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h40 X0 X1]
    conv => enter [1]; rw [l2 X1 X2]
    conv => enter [1, 1]; rw [h40 X1 X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 ((X2 ◇ X0) ◇ X2)]
    conv => enter [1, 2, 1]; rw [← h105 X0 X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0 X1]
    conv => enter [1, 2]; rw [← h105 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h107 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l6 x y]
  conv => enter [1, 2]; rw [l5 y z]

theorem Equation40_205_209_211_implies_Equation2 (G : Type*) [Magma G] (h40 : Equation40 G) (h205 : Equation205 G) (h209 : Equation209 G) (h211 : Equation211 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h211 (X1 ◇ X1) X1]
    conv => enter [1, 1]; rw [h40 (X1 ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h211 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h211 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← h211 X0 X1]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l2 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l2 X0 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1, 1]; rw [← l4 X0 X0]
  have l10 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l5 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1]; rw [← l10 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l11 X0]
    conv => enter [1, 2, 2]; rw [← l11 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l12 X0]
    conv => enter [1]; rw [l3 X0 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l7 X0 X1]
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l3 X0 (X0 ◇ (X1 ◇ X1))]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l13 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l13 X1]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h40 X1 X0]
    conv => enter [1]; rw [l17 X0 X0]
  have l19 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 X0]
    conv => enter [1]; rw [l18 X0 X1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation40_104_107_117_implies_Equation2 (G : Type*) [Magma G] (h40 : Equation40 G) (h104 : Equation104 G) (h107 : Equation107 G) (h117 : Equation117 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X0) ◇ X0)]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h107 (X1 ◇ X1) X1]
    conv => enter [1, 2]; rw [h40 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h107 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X1 ◇ X1) ◇ X0)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h107 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h107 X0 X1]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l2 X0 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l8 X0]
    conv => enter [1, 2]; rw [← l4 X0 X0]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l1 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l5 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1]; rw [← l10 X0]
  have l12 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l11 X0]
    conv => enter [1, 1, 1]; rw [← l11 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l12 X0]
    conv => enter [1]; rw [l3 X0 X0]
  have l14 : ∀ X1 X0 : G, ((((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l7 X1 X0]
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ X1) ◇ X0) X0]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l13 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l14 X1 X0]
  have l16 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l13 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l13 X1]
    conv => enter [1]; rw [l16 X1 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h40 X1 X0]
    conv => enter [1]; rw [l17 X0 X0]
  have l19 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 X0]
    conv => enter [1]; rw [l18 X0 X1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation40_151_implies_Equation2 (G : Type*) [Magma G] (h40 : Equation40 G) (h151 : Equation151 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h40 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h151 X0]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h151 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation39_312_implies_Equation336 (G : Type*) [Magma G] (h39 : Equation39 G) (h312 : Equation312 G) : Equation336 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h39 X1 X0]
    conv => enter [1]; rw [h39 X1 X2]
  intro x y
  conv => enter [1]; rw [l0 x y y]
  conv => enter [1]; rw [h312 y y]

theorem Equation38_360_implies_Equation374 (G : Type*) [Magma G] (h38 : Equation38 G) (h360 : Equation360 G) : Equation374 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← h38 X1 X0]
    conv => enter [1]; rw [h38 X1 X2]
  intro x y
  conv => enter [1]; rw [l0 x y x]
  conv => enter [1]; rw [h360 x x]

theorem Equation23_333_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h333 : Equation333 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h333 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h23 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_377_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h377 : Equation377 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h377 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h8 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation23_326_implies_Equation151 (G : Type*) [Magma G] (h23 : Equation23 G) (h326 : Equation326 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h23 x]
  conv => enter [1]; rw [h326 (x ◇ x) x]

theorem Equation8_375_implies_Equation151 (G : Type*) [Magma G] (h8 : Equation8 G) (h375 : Equation375 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h8 x]
  conv => enter [1]; rw [h375 x (x ◇ x)]

theorem Equation23_325_implies_Equation151 (G : Type*) [Magma G] (h23 : Equation23 G) (h325 : Equation325 G) : Equation151 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  intro x
  conv => enter [1]; rw [h23 x]
  conv => enter [1]; rw [l0 x x]

theorem Equation8_385_implies_Equation151 (G : Type*) [Magma G] (h8 : Equation8 G) (h385 : Equation385 G) : Equation151 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  intro x
  conv => enter [1]; rw [h8 x]
  conv => enter [1]; rw [l0 x x]

theorem Equation23_315_implies_Equation72 (G : Type*) [Magma G] (h23 : Equation23 G) (h315 : Equation315 G) : Equation72 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h315 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h23 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation8_362_implies_Equation258 (G : Type*) [Magma G] (h8 : Equation8 G) (h362 : Equation362 G) : Equation258 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h362 X0 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h8 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h8 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← h362 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x]
  conv => enter [1]; rw [← l2 (x ◇ x) y]

theorem Equation23_313_implies_Equation221 (G : Type*) [Magma G] (h23 : Equation23 G) (h313 : Equation313 G) : Equation221 G := by
  intro x y
  conv => enter [1]; rw [h23 x]
  conv => enter [1, 1]; rw [h313 x y]

theorem Equation8_365_implies_Equation105 (G : Type*) [Magma G] (h8 : Equation8 G) (h365 : Equation365 G) : Equation105 G := by
  intro x y
  conv => enter [1]; rw [h8 x]
  conv => enter [1, 2]; rw [h365 x y]

theorem Equation23_312_implies_Equation218 (G : Type*) [Magma G] (h23 : Equation23 G) (h312 : Equation312 G) : Equation218 G := by
  intro x y
  conv => enter [1]; rw [h23 x]
  conv => enter [1, 1]; rw [h312 x y]

theorem Equation8_360_implies_Equation100 (G : Type*) [Magma G] (h8 : Equation8 G) (h360 : Equation360 G) : Equation100 G := by
  intro x y
  conv => enter [1]; rw [h8 x]
  conv => enter [1, 2]; rw [h360 x y]

theorem Equation23_310_implies_Equation211 (G : Type*) [Magma G] (h23 : Equation23 G) (h310 : Equation310 G) : Equation211 G := by
  intro x y
  conv => enter [1]; rw [h23 x]
  conv => enter [1, 1]; rw [h310 x y]

theorem Equation8_367_implies_Equation107 (G : Type*) [Magma G] (h8 : Equation8 G) (h367 : Equation367 G) : Equation107 G := by
  intro x y
  conv => enter [1]; rw [h8 x]
  conv => enter [1, 2]; rw [h367 x y]

theorem Equation23_309_implies_Equation208 (G : Type*) [Magma G] (h23 : Equation23 G) (h309 : Equation309 G) : Equation208 G := by
  intro x y
  conv => enter [1]; rw [h23 x]
  conv => enter [1, 1]; rw [h309 x y]

theorem Equation8_361_implies_Equation101 (G : Type*) [Magma G] (h8 : Equation8 G) (h361 : Equation361 G) : Equation101 G := by
  intro x y
  conv => enter [1]; rw [h8 x]
  conv => enter [1, 2]; rw [h361 x y]

theorem Equation23_308_implies_Equation205 (G : Type*) [Magma G] (h23 : Equation23 G) (h308 : Equation308 G) : Equation205 G := by
  intro x y
  conv => enter [1]; rw [h23 x]
  conv => enter [1, 1]; rw [h308 x y]

theorem Equation23_308_implies_Equation151 (G : Type*) [Magma G] (h23 : Equation23 G) (h308 : Equation308 G) : Equation151 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h308 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l0 X0]
    conv => enter [1]; rw [← h23 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation8_364_implies_Equation104 (G : Type*) [Magma G] (h8 : Equation8 G) (h364 : Equation364 G) : Equation104 G := by
  intro x y
  conv => enter [1]; rw [h8 x]
  conv => enter [1, 2]; rw [h364 x y]

theorem Equation8_364_implies_Equation151 (G : Type*) [Magma G] (h8 : Equation8 G) (h364 : Equation364 G) : Equation151 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [← l0 X0]
    conv => enter [1]; rw [← h8 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation231_307_implies_Equation31 (G : Type*) [Magma G] (h231 : Equation231 G) (h307 : Equation307 G) : Equation31 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h307 X1]
    conv => enter [1]; rw [← h231 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation108_359_implies_Equation11 (G : Type*) [Magma G] (h108 : Equation108 G) (h359 : Equation359 G) : Equation11 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h359 X1]
    conv => enter [1]; rw [← h108 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation23_221_231_implies_Equation31 (G : Type*) [Magma G] (h23 : Equation23 G) (h221 : Equation221 G) (h231 : Equation231 G) : Equation31 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h231 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation23_221_231_implies_Equation211 (G : Type*) [Magma G] (h23 : Equation23 G) (h221 : Equation221 G) (h231 : Equation231 G) : Equation211 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h231 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X1]
    conv => enter [1]; rw [← h221 X0 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation8_105_108_implies_Equation11 (G : Type*) [Magma G] (h8 : Equation8 G) (h105 : Equation105 G) (h108 : Equation108 G) : Equation11 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h108 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation8_105_108_implies_Equation107 (G : Type*) [Magma G] (h8 : Equation8 G) (h105 : Equation105 G) (h108 : Equation108 G) : Equation107 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (((X1 ◇ X1) ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h108 (((X1 ◇ X1) ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [← h105 X0 ((X1 ◇ X1) ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation23_219_implies_Equation14 (G : Type*) [Magma G] (h23 : Equation23 G) (h219 : Equation219 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h219 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h219 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h23 (X0 ◇ X0)]
    conv => enter [1]; rw [← h219 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation8_115_implies_Equation14 (G : Type*) [Magma G] (h8 : Equation8 G) (h115 : Equation115 G) : Equation14 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h8 (X0 ◇ X0)]
    conv => enter [1]; rw [← h115 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h115 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation218_221_implies_Equation211 (G : Type*) [Magma G] (h218 : Equation218 G) (h221 : Equation221 G) : Equation211 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h218 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h221 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation100_105_implies_Equation107 (G : Type*) [Magma G] (h100 : Equation100 G) (h105 : Equation105 G) : Equation107 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h100 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation23_211_221_313_implies_Equation242 (G : Type*) [Magma G] (h23 : Equation23 G) (h211 : Equation211 G) (h221 : Equation221 G) (h313 : Equation313 G) : Equation242 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h211 (X1 ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X1]
  intro x y z
  conv => enter [1]; rw [← l5 z x]
  conv => enter [1, 1]; rw [h313 z y]

theorem Equation23_211_221_313_implies_Equation319 (G : Type*) [Magma G] (h23 : Equation23 G) (h211 : Equation211 G) (h221 : Equation221 G) (h313 : Equation313 G) : Equation319 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← l1 X0 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h211 (X1 ◇ X1) X0]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h313 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation8_105_107_365_implies_Equation111 (G : Type*) [Magma G] (h8 : Equation8 G) (h105 : Equation105 G) (h107 : Equation107 G) (h365 : Equation365 G) : Equation111 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l2 X0 (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h107 (X1 ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X1]
  intro x y z
  conv => enter [1]; rw [← l5 x z]
  conv => enter [1, 2]; rw [h365 z y]

theorem Equation8_105_107_365_implies_Equation371 (G : Type*) [Magma G] (h8 : Equation8 G) (h105 : Equation105 G) (h107 : Equation107 G) (h365 : Equation365 G) : Equation371 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l1 X0 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h107 (X1 ◇ X1) X0]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h365 X1 X2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation23_221_310_implies_Equation246 (G : Type*) [Magma G] (h23 : Equation23 G) (h221 : Equation221 G) (h310 : Equation310 G) : Equation246 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h221 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [l3 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

theorem Equation23_221_310_implies_Equation316 (G : Type*) [Magma G] (h23 : Equation23 G) (h221 : Equation221 G) (h310 : Equation310 G) : Equation316 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h221 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h310 (X0 ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h310 y y]

theorem Equation8_105_367_implies_Equation109 (G : Type*) [Magma G] (h8 : Equation8 G) (h105 : Equation105 G) (h367 : Equation367 G) : Equation109 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h367 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← h367 X0 X1]
    conv => enter [1]; rw [l3 X2 X0]
  intro x y z
  conv => enter [1]; rw [← l4 x y z]

theorem Equation8_105_367_implies_Equation368 (G : Type*) [Magma G] (h8 : Equation8 G) (h105 : Equation105 G) (h367 : Equation367 G) : Equation368 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [h367 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l3 (X1 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h367 y y]

theorem Equation211_312_implies_Equation246 (G : Type*) [Magma G] (h211 : Equation211 G) (h312 : Equation312 G) : Equation246 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h312 X1 X0]
    conv => enter [1]; rw [← h211 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l0 z x]
  conv => enter [1, 1]; rw [h312 z y]

theorem Equation107_360_implies_Equation109 (G : Type*) [Magma G] (h107 : Equation107 G) (h360 : Equation360 G) : Equation109 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h360 X1 X0]
    conv => enter [1]; rw [← h107 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2]; rw [h360 y z]

theorem Equation218_310_implies_Equation246 (G : Type*) [Magma G] (h218 : Equation218 G) (h310 : Equation310 G) : Equation246 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h218 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

theorem Equation218_310_implies_Equation316 (G : Type*) [Magma G] (h218 : Equation218 G) (h310 : Equation310 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h310 X0 X1]
    conv => enter [1]; rw [← h218 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h310 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h310 y y]

theorem Equation100_367_implies_Equation109 (G : Type*) [Magma G] (h100 : Equation100 G) (h367 : Equation367 G) : Equation109 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h100 X1 X0]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← h367 X0 X1]
    conv => enter [1]; rw [l0 X2 X0]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

theorem Equation100_367_implies_Equation368 (G : Type*) [Magma G] (h100 : Equation100 G) (h367 : Equation367 G) : Equation368 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h367 X0 X1]
    conv => enter [1]; rw [← h100 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h367 (X1 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h367 y y]

theorem Equation23_209_implies_Equation151 (G : Type*) [Magma G] (h23 : Equation23 G) (h209 : Equation209 G) : Equation151 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_117_implies_Equation151 (G : Type*) [Magma G] (h8 : Equation8 G) (h117 : Equation117 G) : Equation151 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation208_313_implies_Equation242 (G : Type*) [Magma G] (h208 : Equation208 G) (h313 : Equation313 G) : Equation242 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h208 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

theorem Equation101_365_implies_Equation111 (G : Type*) [Magma G] (h101 : Equation101 G) (h365 : Equation365 G) : Equation111 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h101 X1 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X0)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l0 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

theorem Equation221_309_implies_Equation242 (G : Type*) [Magma G] (h221 : Equation221 G) (h309 : Equation309 G) : Equation242 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h309 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 1]; rw [h309 y z]

theorem Equation221_309_implies_Equation312 (G : Type*) [Magma G] (h221 : Equation221 G) (h309 : Equation309 G) : Equation312 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h309 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h309 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation105_361_implies_Equation111 (G : Type*) [Magma G] (h105 : Equation105 G) (h361 : Equation361 G) : Equation111 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h361 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2]; rw [h361 y z]

theorem Equation105_361_implies_Equation360 (G : Type*) [Magma G] (h105 : Equation105 G) (h361 : Equation361 G) : Equation360 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h361 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [← h361 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation23_205_implies_Equation307 (G : Type*) [Magma G] (h23 : Equation23 G) (h205 : Equation205 G) : Equation307 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h205 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 1]; rw [← h23 X0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation8_104_implies_Equation359 (G : Type*) [Magma G] (h8 : Equation8 G) (h104 : Equation104 G) : Equation359 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h104 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 2]; rw [← h8 X0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation205_323_implies_Equation25 (G : Type*) [Magma G] (h205 : Equation205 G) (h323 : Equation323 G) : Equation25 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h205 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation104_378_implies_Equation10 (G : Type*) [Magma G] (h104 : Equation104 G) (h378 : Equation378 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h104 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation205_221_313_implies_Equation242 (G : Type*) [Magma G] (h205 : Equation205 G) (h221 : Equation221 G) (h313 : Equation313 G) : Equation242 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h313 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h221 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h205 X1 (X0 ◇ X1)]
  have l4 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 1, 2]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l3 X2 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h313 (X0 ◇ (X1 ◇ X1)) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h313 ((X1 ◇ X0) ◇ (X1 ◇ X1)) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 (X1 ◇ X0) X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l4 X0 X1 X2]
    conv => enter [1]; rw [← h313 (X0 ◇ (X1 ◇ (X2 ◇ X1))) X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ (X2 ◇ X1)))]
    conv => enter [1, 1]; rw [l4 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1, 2]; rw [← l9 (X1 ◇ (X2 ◇ X1)) X0]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [← l9 (X1 ◇ (X2 ◇ X1)) X0]
  have l14 : ∀ X0 X2 : G, (X0 ◇ X0) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X2
    conv => enter [1]; rw [l12 X0 X0 X2]
    conv => enter [1, 2]; rw [← l0 X2 X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ ((X2 ◇ X1) ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1]; rw [l7 X1 (X2 ◇ X1)]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1 X0]
    conv => enter [1]; rw [← l14 (X1 ◇ X1) (X0 ◇ X1)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [← l6 X1 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l17 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l2 X1 X1]
  intro x y z
  conv => enter [1]; rw [← l18 z x]
  conv => enter [1, 1]; rw [h313 z y]

theorem Equation104_105_365_implies_Equation111 (G : Type*) [Magma G] (h104 : Equation104 G) (h105 : Equation105 G) (h365 : Equation365 G) : Equation111 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h365 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h105 X1 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h104 X1 (X1 ◇ X0)]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (((X0 ◇ X1) ◇ X0) ◇ X2)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l3 X2 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h365 ((X1 ◇ X1) ◇ X0) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h365 ((X1 ◇ X1) ◇ (X0 ◇ X1)) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l4 X0 X1 X2]
    conv => enter [1]; rw [← h365 (((X1 ◇ X2) ◇ X1) ◇ X0) X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (((((X1 ◇ X2) ◇ X1) ◇ X0) ◇ (((X1 ◇ X2) ◇ X1) ◇ X0)) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 (((X1 ◇ X2) ◇ X1) ◇ X0)]
    conv => enter [1, 2]; rw [l4 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1, 1]; rw [← l9 ((X1 ◇ X2) ◇ X1) X0]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [← l9 ((X1 ◇ X2) ◇ X1) X0]
  have l14 : ∀ X0 X2 : G, (X0 ◇ X0) = ((X2 ◇ X2) ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [l12 X0 X0 X2]
    conv => enter [1, 1]; rw [← l0 X2 X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (((X1 ◇ X2) ◇ (X1 ◇ X2)) ◇ (X1 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1]; rw [l7 (X1 ◇ X2) X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1 X0]
    conv => enter [1]; rw [← l14 (X1 ◇ X1) (X1 ◇ X0)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [← l6 X1 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l17 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l2 X1 X1]
  intro x y z
  conv => enter [1]; rw [← l18 x z]
  conv => enter [1, 2]; rw [h365 z y]

theorem Equation205_312_implies_Equation246 (G : Type*) [Magma G] (h205 : Equation205 G) (h312 : Equation312 G) : Equation246 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h312 X0 X1]
    conv => enter [1]; rw [← h205 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h312 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l1 z x]
  conv => enter [1, 1]; rw [h312 z y]

theorem Equation104_360_implies_Equation109 (G : Type*) [Magma G] (h104 : Equation104 G) (h360 : Equation360 G) : Equation109 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h360 X0 X1]
    conv => enter [1]; rw [← h104 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h360 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 2]; rw [h360 y z]

theorem Equation23_151_221_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) (h221 : Equation221 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h221 (X0 ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h151 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation8_105_151_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h105 : Equation105 G) (h151 : Equation151 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h105 (X0 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h8 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h151 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation151_218_implies_Equation28 (G : Type*) [Magma G] (h151 : Equation151 G) (h218 : Equation218 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h218 (X0 ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h151 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h218 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation100_151_implies_Equation9 (G : Type*) [Magma G] (h100 : Equation100 G) (h151 : Equation151 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h100 (X0 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h151 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h100 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation212_326_implies_Equation26 (G : Type*) [Magma G] (h212 : Equation212 G) (h326 : Equation326 G) : Equation26 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h212 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation127_375_implies_Equation16 (G : Type*) [Magma G] (h127 : Equation127 G) (h375 : Equation375 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h375 X1 X0]
    conv => enter [1]; rw [← h127 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation151_212_323_implies_Equation24 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h323 : Equation323 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h323 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 ((X0 ◇ X0) ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation127_151_378_implies_Equation13 (G : Type*) [Magma G] (h127 : Equation127 G) (h151 : Equation151 G) (h378 : Equation378 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h378 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 (X1 ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation209_325_implies_Equation26 (G : Type*) [Magma G] (h209 : Equation209 G) (h325 : Equation325 G) : Equation26 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation209_325_implies_Equation159 (G : Type*) [Magma G] (h209 : Equation209 G) (h325 : Equation325 G) : Equation159 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation117_385_implies_Equation16 (G : Type*) [Magma G] (h117 : Equation117 G) (h385 : Equation385 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation117_385_implies_Equation159 (G : Type*) [Magma G] (h117 : Equation117 G) (h385 : Equation385 G) : Equation159 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h385 X1 X0]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation209_323_implies_Equation24 (G : Type*) [Magma G] (h209 : Equation209 G) (h323 : Equation323 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h323 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h209 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation117_378_implies_Equation13 (G : Type*) [Magma G] (h117 : Equation117 G) (h378 : Equation378 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h378 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h117 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation151_208_325_implies_Equation24 (G : Type*) [Magma G] (h151 : Equation151 G) (h208 : Equation208 G) (h325 : Equation325 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h151 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation101_151_385_implies_Equation13 (G : Type*) [Magma G] (h101 : Equation101 G) (h151 : Equation151 G) (h385 : Equation385 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h101 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h151 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation23_309_326_implies_Equation153 (G : Type*) [Magma G] (h23 : Equation23 G) (h309 : Equation309 G) (h326 : Equation326 G) : Equation153 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h326 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X1) X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h23 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation8_361_375_implies_Equation156 (G : Type*) [Magma G] (h8 : Equation8 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation156 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h375 X1 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h375 X1 (X1 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h8 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation208_212_implies_Equation24 (G : Type*) [Magma G] (h208 : Equation208 G) (h212 : Equation212 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h212 X0 X1]
    conv => enter [1]; rw [← h208 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h212 ((X0 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation101_127_implies_Equation13 (G : Type*) [Magma G] (h101 : Equation101 G) (h127 : Equation127 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h127 X0 X1]
    conv => enter [1]; rw [← h101 X1 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h127 (X1 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation208_209_implies_Equation24 (G : Type*) [Magma G] (h208 : Equation208 G) (h209 : Equation209 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h208 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h209 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation101_117_implies_Equation13 (G : Type*) [Magma G] (h101 : Equation101 G) (h117 : Equation117 G) : Equation13 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h101 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation206_323_implies_Equation24 (G : Type*) [Magma G] (h206 : Equation206 G) (h323 : Equation323 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h323 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation124_378_implies_Equation13 (G : Type*) [Magma G] (h124 : Equation124 G) (h378 : Equation378 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h378 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation151_206_212_implies_Equation24 (G : Type*) [Magma G] (h151 : Equation151 G) (h206 : Equation206 G) (h212 : Equation212 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h212 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h212 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← h206 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 ((X0 ◇ (X1 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← l0 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = ((((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [l4 (X0 ◇ (X1 ◇ X1)) X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h206 X0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x y]

theorem Equation124_127_151_implies_Equation13 (G : Type*) [Magma G] (h124 : Equation124 G) (h127 : Equation127 G) (h151 : Equation151 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h127 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h127 (((X1 ◇ X1) ◇ X0) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← h124 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [l4 ((X1 ◇ X1) ◇ X0) X0]
  have l7 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h124 X0 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 y x]

theorem Equation206_208_implies_Equation24 (G : Type*) [Magma G] (h206 : Equation206 G) (h208 : Equation208 G) : Equation24 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h208 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation101_124_implies_Equation13 (G : Type*) [Magma G] (h101 : Equation101 G) (h124 : Equation124 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h101 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation205_325_implies_Equation308 (G : Type*) [Magma G] (h205 : Equation205 G) (h325 : Equation325 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation104_385_implies_Equation364 (G : Type*) [Magma G] (h104 : Equation104 G) (h385 : Equation385 G) : Equation364 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h385 ((X1 ◇ X0) ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation23_327_implies_Equation152 (G : Type*) [Magma G] (h23 : Equation23 G) (h327 : Equation327 G) : Equation152 G := by
  intro x y
  conv => enter [1]; rw [h23 x]
  conv => enter [1]; rw [h327 (x ◇ x) x y]

theorem Equation8_395_implies_Equation166 (G : Type*) [Magma G] (h8 : Equation8 G) (h395 : Equation395 G) : Equation166 G := by
  intro x y
  conv => enter [1]; rw [h8 x]
  conv => enter [1]; rw [h395 x (x ◇ x) y]

theorem Equation151_205_212_307_implies_Equation308 (G : Type*) [Magma G] (h151 : Equation151 G) (h205 : Equation205 G) (h212 : Equation212 G) (h307 : Equation307 G) : Equation308 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h307 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation104_127_151_359_implies_Equation364 (G : Type*) [Magma G] (h104 : Equation104 G) (h127 : Equation127 G) (h151 : Equation151 G) (h359 : Equation359 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h359 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation151_212_308_325_implies_Equation152 (G : Type*) [Magma G] (h151 : Equation151 G) (h212 : Equation212 G) (h308 : Equation308 G) (h325 : Equation325 G) : Equation152 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h151 X0]
    conv => enter [1]; rw [← h212 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h308 (X0 ◇ X1) (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation127_151_364_385_implies_Equation166 (G : Type*) [Magma G] (h127 : Equation127 G) (h151 : Equation151 G) (h364 : Equation364 G) (h385 : Equation385 G) : Equation166 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h151 X0]
    conv => enter [1]; rw [← h127 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h364 (X1 ◇ X0) (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation205_209_307_implies_Equation308 (G : Type*) [Magma G] (h205 : Equation205 G) (h209 : Equation209 G) (h307 : Equation307 G) : Equation308 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h205 X0 X1]
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h307 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation104_117_359_implies_Equation364 (G : Type*) [Magma G] (h104 : Equation104 G) (h117 : Equation117 G) (h359 : Equation359 G) : Equation364 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h104 X0 X1]
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h359 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation209_308_326_implies_Equation152 (G : Type*) [Magma G] (h209 : Equation209 G) (h308 : Equation308 G) (h326 : Equation326 G) : Equation152 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h308 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h326 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation117_364_375_implies_Equation166 (G : Type*) [Magma G] (h117 : Equation117 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation166 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h364 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h375 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation151_208_308_implies_Equation309 (G : Type*) [Magma G] (h151 : Equation151 G) (h208 : Equation208 G) (h308 : Equation308 G) : Equation309 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h208 X0 X1]
    conv => enter [1]; rw [← h308 (X0 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h208 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h151 (X0 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation101_151_364_implies_Equation361 (G : Type*) [Magma G] (h101 : Equation101 G) (h151 : Equation151 G) (h364 : Equation364 G) : Equation361 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h101 X0 X1]
    conv => enter [1]; rw [← h364 ((X0 ◇ X1) ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h101 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h151 ((X0 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation205_206_implies_Equation24 (G : Type*) [Magma G] (h205 : Equation205 G) (h206 : Equation206 G) : Equation24 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation104_124_implies_Equation13 (G : Type*) [Magma G] (h104 : Equation104 G) (h124 : Equation124 G) : Equation13 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation23_167_307_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h167 : Equation167 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h167 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h23 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1, 1]; rw [← h307 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h23 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

end Order3
