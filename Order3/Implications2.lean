import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation264_313_implies_Equation221 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation221 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l6 X1 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1, 1]; rw [← l12 y x]

theorem Equation264_313_implies_Equation75 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation75 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 X0 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l9 X1 X1]
    conv => enter [1]; rw [l14 X1 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X1 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l16 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l15 X0]
    conv => enter [1, 1, 1]; rw [← l15 X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l16 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l18 X1 X0]
  intro x y
  conv => enter [1]; rw [← l19 y x]
  conv => enter [1]; rw [l20 (y ◇ x) y]

theorem Equation264_313_implies_Equation159 (G : Type*) [Magma G] (h264 : Equation264 G) (h313 : Equation313 G) : Equation159 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (((X0 ◇ X2) ◇ X2) ◇ X1)) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X2) ◇ X2) X2]
    conv => enter [1, 2]; rw [← h264 X0 X2]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 1]; rw [h313 X1 X0]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 X0 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l10 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l9 X1 X1]
    conv => enter [1]; rw [l14 X1 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X1 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X2) = (X2 ◇ X0) := by
    intro X0 X2
    conv => enter [1]; rw [← l16 X0 ((X0 ◇ X2) ◇ X2)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l15 X0]
    conv => enter [1, 1, 1]; rw [← l15 X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l18 X1 X0]
    conv => enter [1]; rw [l19 (X1 ◇ X0) X0]
  intro x y
  conv => enter [1]; rw [← l20 x y]

theorem Equation75_365_implies_Equation14 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation14 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l14 X0]
    conv => enter [1, 2, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l17 y x]

theorem Equation75_365_implies_Equation66 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation66 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l14 X0]
    conv => enter [1, 2, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l17 y x]
  conv => enter [1, 2, 2]; rw [← l14 y]

theorem Equation75_365_implies_Equation115 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation115 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l14 X0]
    conv => enter [1, 2, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 x]
  conv => enter [1]; rw [← l17 y (x ◇ x)]

theorem Equation75_365_implies_Equation219 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation219 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 (X0 ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l6 X1 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1]; rw [← l12 y (x ◇ x)]

theorem Equation75_365_implies_Equation335 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation335 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l11 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X2 X2 X0]
  intro x y
  conv => enter [1]; rw [← l12 y x]

theorem Equation75_365_implies_Equation124 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation124 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 (X0 ◇ X1) X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l10 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l9 X1 X1]
    conv => enter [1]; rw [l14 X1 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X1 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l16 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X2 X2 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l15 X0]
    conv => enter [1, 2, 2]; rw [← l15 X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l16 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l18 X0 X1]
  intro x y
  conv => enter [1]; rw [← l19 y x]
  conv => enter [1, 2]; rw [l20 x y]

theorem Equation75_365_implies_Equation206 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation206 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l11 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X2 X2 X0]
  intro x y
  conv => enter [1]; rw [← l11 y x]
  conv => enter [1, 1]; rw [← l12 x y]

theorem Equation75_365_implies_Equation53 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation53 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l14 X0]
    conv => enter [1, 2, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 x]
  conv => enter [1, 2]; rw [← l17 y x]

theorem Equation75_365_implies_Equation273 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation273 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 (X0 ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l6 X1 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1, 1]; rw [← l12 y x]

theorem Equation75_365_implies_Equation105 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation105 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 (X0 ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l6 X1 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l11 x]
  conv => enter [1, 2]; rw [← l12 y x]

theorem Equation75_365_implies_Equation221 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation221 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l8 X1 X1]
    conv => enter [1]; rw [l13 X1 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l14 X0]
    conv => enter [1, 2, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 x]
  conv => enter [1, 1]; rw [← l17 y x]

theorem Equation75_365_implies_Equation264 (G : Type*) [Magma G] (h75 : Equation75 G) (h365 : Equation365 G) : Equation264 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ X1) = (X0 ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h75 X0 X2]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1, 2]; rw [h365 X1 X0]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h365 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 (X0 ◇ X1) X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l10 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ X2) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l9 X1 X1]
    conv => enter [1]; rw [l14 X1 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X1 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = (X0 ◇ X2) := by
    intro X2 X0
    conv => enter [1]; rw [← l16 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X2 X2 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l15 X0]
    conv => enter [1, 2, 2]; rw [← l15 X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l16 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l18 X0 X1]
  intro x y
  conv => enter [1]; rw [← l19 y x]
  conv => enter [1]; rw [l20 y (x ◇ y)]

theorem Equation264_312_implies_Equation2 (G : Type*) [Magma G] (h264 : Equation264 G) (h312 : Equation312 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation75_360_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h360 : Equation360 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1))]
    conv => enter [1]; rw [← h75 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation264_310_implies_Equation256 (G : Type*) [Magma G] (h264 : Equation264 G) (h310 : Equation310 G) : Equation256 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← h264 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l1 X0 X2]
  have l3 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X1) X2 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x x y]

theorem Equation75_367_implies_Equation62 (G : Type*) [Magma G] (h75 : Equation75 G) (h367 : Equation367 G) : Equation62 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h367 X2 X0]
    conv => enter [1, 1]; rw [h367 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1 ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ X0))]
    conv => enter [1, 1]; rw [← h75 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l1 X0 X2]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l2 X2 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x x]

theorem Equation264_309_implies_Equation256 (G : Type*) [Magma G] (h264 : Equation264 G) (h309 : Equation309 G) : Equation256 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h309 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X2 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x x y]

theorem Equation75_361_implies_Equation62 (G : Type*) [Magma G] (h75 : Equation75 G) (h361 : Equation361 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h361 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l0 X2 X0]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l1 X2 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x x]

theorem Equation264_283_307_implies_Equation2 (G : Type*) [Magma G] (h264 : Equation264 G) (h283 : Equation283 G) (h307 : Equation307 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h283 X0 X1]
    conv => enter [1]; rw [← h264 ((X1 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h264 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation56_75_359_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h75 : Equation75 G) (h359 : Equation359 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h56 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X1 ◇ X1)) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation264_280_implies_Equation40 (G : Type*) [Magma G] (h264 : Equation264 G) (h280 : Equation280 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h280 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation50_75_implies_Equation40 (G : Type*) [Magma G] (h50 : Equation50 G) (h75 : Equation75 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h50 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation264_274_implies_Equation73 (G : Type*) [Magma G] (h264 : Equation264 G) (h274 : Equation274 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation264_274_implies_Equation118 (G : Type*) [Magma G] (h264 : Equation264 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1, 1]; rw [← h264 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h274 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2]; rw [l0 y (y ◇ x)]
  conv => enter [1, 2]; rw [← l1 x y]

theorem Equation264_274_implies_Equation125 (G : Type*) [Magma G] (h264 : Equation264 G) (h274 : Equation274 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h274 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2]; rw [l0 y (y ◇ x)]

theorem Equation264_274_implies_Equation222 (G : Type*) [Magma G] (h264 : Equation264 G) (h274 : Equation274 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h264 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1]; rw [l0 y (y ◇ (x ◇ y))]

theorem Equation264_274_implies_Equation43 (G : Type*) [Magma G] (h264 : Equation264 G) (h274 : Equation274 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation264_274_implies_Equation75 (G : Type*) [Magma G] (h264 : Equation264 G) (h274 : Equation274 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h264 (X1 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h274 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation73_75_implies_Equation118 (G : Type*) [Magma G] (h73 : Equation73 G) (h75 : Equation75 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h75 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← h73 X1 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [l0 ((x ◇ y) ◇ y) y]

theorem Equation73_75_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h75 : Equation75 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h75 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h75 X1 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1]; rw [l0 ((y ◇ x) ◇ y) y]

theorem Equation73_75_implies_Equation222 (G : Type*) [Magma G] (h73 : Equation73 G) (h75 : Equation75 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h75 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← h73 X1 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1]; rw [l0 (x ◇ y) y]

theorem Equation73_75_implies_Equation43 (G : Type*) [Magma G] (h73 : Equation73 G) (h75 : Equation75 G) : Equation43 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h75 (X0 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation73_75_implies_Equation264 (G : Type*) [Magma G] (h73 : Equation73 G) (h75 : Equation75 G) : Equation264 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h75 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← h73 X1 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation263_325_implies_Equation258 (G : Type*) [Magma G] (h263 : Equation263 G) (h325 : Equation325 G) : Equation258 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h325 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 X0 X0]
  intro x y
  conv => enter [1]; rw [← l9 x y]

theorem Equation263_325_implies_Equation326 (G : Type*) [Magma G] (h263 : Equation263 G) (h325 : Equation325 G) : Equation326 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h325 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 X0 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [← h325 X1 ((X0 ◇ X0) ◇ X1)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← h325 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation55_385_implies_Equation72 (G : Type*) [Magma G] (h55 : Equation55 G) (h385 : Equation385 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h55 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h55 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l0 X0 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l4 X0 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation55_385_implies_Equation375 (G : Type*) [Magma G] (h55 : Equation55 G) (h385 : Equation385 G) : Equation375 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h55 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h55 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l0 X0 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l4 X0 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [← h385 (X1 ◇ (X0 ◇ X0)) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation263_323_326_implies_Equation257 (G : Type*) [Magma G] (h263 : Equation263 G) (h323 : Equation323 G) (h326 : Equation326 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h326 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h326 (X0 ◇ X0) (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1, 1]; rw [← l6 X0 X1]
    conv => enter [1, 1, 2, 1]; rw [← l6 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h326 ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 1]; rw [l4 (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h326 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [← l12 (X0 ◇ X0) X1]
  have l14 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X0]
  have l15 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l15 x y]

theorem Equation263_323_326_implies_Equation260 (G : Type*) [Magma G] (h263 : Equation263 G) (h323 : Equation323 G) (h326 : Equation326 G) : Equation260 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h326 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h326 (X0 ◇ X0) (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1, 1]; rw [← l6 X0 X1]
    conv => enter [1, 1, 2, 1]; rw [← l6 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h326 ((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (((((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 1]; rw [l4 (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h326 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← l11 X0 X1]
  intro x y
  conv => enter [1]; rw [h263 x x]
  conv => enter [1, 1]; rw [l12 x y]

theorem Equation55_375_378_implies_Equation52 (G : Type*) [Magma G] (h55 : Equation55 G) (h375 : Equation375 G) (h378 : Equation378 G) : Equation52 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h55 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h375 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h375 (X1 ◇ X0) (X0 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← l6 X1 X0]
    conv => enter [1, 2, 1, 2]; rw [← l6 X1 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h375 X0 (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [l4 (X1 ◇ X0) ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h55 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l12 (X0 ◇ X0) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l15 x y]

theorem Equation55_375_378_implies_Equation49 (G : Type*) [Magma G] (h55 : Equation55 G) (h375 : Equation375 G) (h378 : Equation378 G) : Equation49 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h55 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h375 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h375 (X1 ◇ X0) (X0 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [← l6 X1 X0]
    conv => enter [1, 2, 1, 2]; rw [← l6 X1 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h375 X0 (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [l4 (X1 ◇ X0) ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h55 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l11 X0 X1]
  intro x y
  conv => enter [1]; rw [h55 x x]
  conv => enter [1, 2]; rw [l12 x y]

theorem Equation263_313_implies_Equation14 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l1 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l6 X0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation263_313_implies_Equation332 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h313 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l8 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l9 (X1 ◇ X0)]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 2]; rw [l9 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [l14 x y]
  conv => enter [1, 2]; rw [← l9 x]

theorem Equation263_313_implies_Equation66 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l1 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l6 X0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2, 2]; rw [← l7 y]

theorem Equation263_313_implies_Equation115 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l1 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l6 X0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l7 x]
  conv => enter [1]; rw [← l8 y (x ◇ x)]

theorem Equation263_313_implies_Equation219 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation219 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h313 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l3 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l4 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l9 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l9 X0 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l10 X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X1 ◇ X2)]
    conv => enter [1, 1, 1]; rw [l0 X2 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X2 X1 X0]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l2 X0 X1]
    conv => enter [1, 2, 1]; rw [← l2 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l10 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← l13 X1 X0]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l12 X2 X0 X1]
    conv => enter [1]; rw [l10 ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 (X1 ◇ X0)]
    conv => enter [1]; rw [← l14 X0 X1]
  have l17 : ∀ X2 X1 : G, (X2 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X1
    conv => enter [1]; rw [l15 X2 X2 X1]
    conv => enter [1, 1]; rw [l11 X2 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2]; rw [l10 X1]
  have l19 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l17 X2 X1]
    conv => enter [1]; rw [l10 X2]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 1]; rw [l10 X1]
  intro x y
  conv => enter [1]; rw [← l10 x]
  conv => enter [1]; rw [← l19 y (x ◇ x)]
  conv => enter [1]; rw [l20 y (y ◇ (x ◇ x))]

theorem Equation263_313_implies_Equation72 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation72 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h313 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l8 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X1 ◇ X2)]
    conv => enter [1, 1, 1]; rw [l0 X2 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X2 X1 X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1]
    conv => enter [1]; rw [l9 ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))]
  have l13 : ∀ X2 X1 : G, (X2 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X1
    conv => enter [1]; rw [l12 X2 X2 X1]
    conv => enter [1, 1]; rw [l10 X2 X1]
  have l14 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l13 X2 X1]
    conv => enter [1]; rw [l9 X2]
  intro x y
  conv => enter [1]; rw [← l9 x]
  conv => enter [1]; rw [← l14 y (x ◇ x)]

theorem Equation263_313_implies_Equation258 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h313 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l8 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l9 (X1 ◇ X0)]
    conv => enter [1]; rw [← l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1, 2]; rw [l9 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 1]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [← l9 x]
  conv => enter [1]; rw [← l10 y (x ◇ x)]
  conv => enter [1]; rw [l15 y ((x ◇ x) ◇ y)]

theorem Equation263_313_implies_Equation315 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation315 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h313 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l8 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X1 ◇ X2)]
    conv => enter [1, 1, 1]; rw [l0 X2 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X2 X1 X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1]
    conv => enter [1]; rw [l9 ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))]
  have l13 : ∀ X2 X1 : G, (X2 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X1
    conv => enter [1]; rw [l12 X2 X2 X1]
    conv => enter [1, 1]; rw [l10 X2 X1]
  have l14 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l13 X2 X1]
    conv => enter [1]; rw [l9 X2]
  intro x y
  conv => enter [1]; rw [l9 x]
  conv => enter [1]; rw [← l14 y x]

theorem Equation263_313_implies_Equation53 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation53 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l2 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l7 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l7 X0 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l8 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]
  conv => enter [1]; rw [l0 y x]

theorem Equation263_313_implies_Equation273 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation273 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h313 ((X0 ◇ X1) ◇ X1) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l4 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l4 X1 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l10 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l10 X0 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l11 X0]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 (X1 ◇ X2)]
    conv => enter [1, 2, 1]; rw [l1 X2 X1 X0]
  have l14 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X2
    conv => enter [1, 1]; rw [← l12 X1 X1]
    conv => enter [1]; rw [l13 X1 X1 X2]
    conv => enter [1, 2, 1]; rw [l12 X1 X1]
  have l15 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X2
    conv => enter [1]; rw [l14 X1 X2]
    conv => enter [1, 1]; rw [l11 X2]
  have l16 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 (X1 ◇ X2)]
    conv => enter [1, 1, 1]; rw [l1 X2 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X2 X1 X0]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
    conv => enter [1, 2, 1]; rw [← l3 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← l17 X1 X0]
  have l19 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l16 X2 X0 X1]
    conv => enter [1]; rw [l11 ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 (X1 ◇ X0)]
    conv => enter [1]; rw [← l18 X0 X1]
  have l21 : ∀ X2 X1 : G, (X2 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X1
    conv => enter [1]; rw [l19 X2 X2 X1]
    conv => enter [1, 1]; rw [l12 X2 X1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1, 2]; rw [l11 X1]
  have l23 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l21 X2 X1]
    conv => enter [1]; rw [l11 X2]
  have l24 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 1]; rw [l11 X1]
  intro x y
  conv => enter [1]; rw [← l23 y x]
  conv => enter [1]; rw [l15 y x]
  conv => enter [1, 2]; rw [l24 y (y ◇ x)]
  conv => enter [1]; rw [l24 x ((y ◇ x) ◇ y)]

theorem Equation263_313_implies_Equation105 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation105 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X2]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h313 ((X0 ◇ X1) ◇ X1) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l4 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l4 X1 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l10 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l10 X0 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l11 X0]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 (X1 ◇ X2)]
    conv => enter [1, 2, 1]; rw [l1 X2 X1 X0]
  have l14 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = ((X2 ◇ X2) ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X2
    conv => enter [1, 1]; rw [← l12 X1 X1]
    conv => enter [1]; rw [l13 X1 X1 X2]
    conv => enter [1, 2, 1]; rw [l12 X1 X1]
  have l15 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X2
    conv => enter [1]; rw [l14 X1 X2]
    conv => enter [1, 1]; rw [l11 X2]
  have l16 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 (X1 ◇ X2)]
    conv => enter [1, 1, 1]; rw [l1 X2 X1 X0]
    conv => enter [1, 2, 1]; rw [l1 X2 X1 X0]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ X0) ◇ (X1 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
    conv => enter [1, 2, 1]; rw [← l3 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← l17 X1 X0]
  have l19 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l16 X2 X0 X1]
    conv => enter [1]; rw [l11 ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X2))]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 (X1 ◇ X0)]
    conv => enter [1]; rw [← l18 X0 X1]
  have l21 : ∀ X2 X1 : G, (X2 ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X1
    conv => enter [1]; rw [l19 X2 X2 X1]
    conv => enter [1, 1]; rw [l12 X2 X1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1, 2]; rw [l11 X1]
  have l23 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l21 X2 X1]
    conv => enter [1]; rw [l11 X2]
  have l24 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 1]; rw [l11 X1]
  intro x y
  conv => enter [1]; rw [← l23 y x]
  conv => enter [1]; rw [l15 y x]
  conv => enter [1, 2]; rw [l24 y (y ◇ x)]

theorem Equation263_313_implies_Equation221 (G : Type*) [Magma G] (h263 : Equation263 G) (h313 : Equation313 G) : Equation221 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l2 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X0]
  have l7 : ∀ X1 X0 : G, ((((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l7 X0 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ (X1 ◇ X0))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation55_365_implies_Equation14 (G : Type*) [Magma G] (h55 : Equation55 G) (h365 : Equation365 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2, 1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l2 X0 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l7 X0 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l8 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l8 X1]
    conv => enter [1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation55_365_implies_Equation332 (G : Type*) [Magma G] (h55 : Equation55 G) (h365 : Equation365 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l3 X0 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l9 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 (X0 ◇ X1)]
    conv => enter [1]; rw [← l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [l9 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1, 2]; rw [l9 X1]
  intro x y
  conv => enter [1, 1]; rw [← l9 x]
  conv => enter [1]; rw [l14 (x ◇ x) y]

theorem Equation55_365_implies_Equation66 (G : Type*) [Magma G] (h55 : Equation55 G) (h365 : Equation365 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l3 X0 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l9 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 (X0 ◇ X1)]
    conv => enter [1]; rw [← l12 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [l9 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]
  conv => enter [1, 1, 1]; rw [← l9 y]
  conv => enter [1, 1]; rw [l15 (y ◇ y) x]
  conv => enter [1]; rw [l15 (x ◇ (y ◇ y)) y]

theorem Equation55_365_implies_Equation115 (G : Type*) [Magma G] (h55 : Equation55 G) (h365 : Equation365 G) : Equation115 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2, 1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l3 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l4 X0 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l9 X0 X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l10 X0]
  have l12 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l1 X2 (X2 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l0 X2 X1 X0]
    conv => enter [1, 1, 2]; rw [l0 X2 X1 X0]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1, 1, 2]; rw [← l2 X0 X1]
  have l14 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l13 X0 X1]
  have l15 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l12 X2 X1 X0]
    conv => enter [1]; rw [l10 ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l10 (X0 ◇ X1)]
    conv => enter [1]; rw [← l14 X1 X0]
  have l17 : ∀ X2 X1 : G, (X2 ◇ X2) = ((X2 ◇ X1) ◇ X1) := by
    intro X2 X1
    conv => enter [1]; rw [l15 X2 X1 X2]
    conv => enter [1, 2]; rw [l11 X2 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 1]; rw [l10 X1]
  have l19 : ∀ X2 X1 : G, ((X2 ◇ X1) ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1]; rw [← l17 X2 X1]
    conv => enter [1]; rw [l10 X2]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1, 2]; rw [l10 X1]
  intro x y
  conv => enter [1]; rw [← l10 x]
  conv => enter [1]; rw [← l19 (x ◇ x) y]
  conv => enter [1]; rw [l20 ((x ◇ x) ◇ y) y]

theorem Equation55_365_implies_Equation219 (G : Type*) [Magma G] (h55 : Equation55 G) (h365 : Equation365 G) : Equation219 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2, 1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X0 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l6 X0 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l7 x]
  conv => enter [1]; rw [← l8 y (x ◇ x)]

theorem Equation55_365_implies_Equation72 (G : Type*) [Magma G] (h55 : Equation55 G) (h365 : Equation365 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l3 X0 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X1) (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l9 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l9 (X0 ◇ X1)]
    conv => enter [1]; rw [← l12 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [l9 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [← l9 x]
  conv => enter [1]; rw [← l10 y (x ◇ x)]
  conv => enter [1]; rw [l15 (y ◇ (x ◇ x)) y]

theorem Equation55_365_implies_Equation258 (G : Type*) [Magma G] (h55 : Equation55 G) (h365 : Equation365 G) : Equation258 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l3 X0 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l8 X0 X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l1 X2 (X2 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l0 X2 X1 X0]
    conv => enter [1, 1, 2]; rw [l0 X2 X1 X0]
  have l12 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l11 X2 X1 X0]
    conv => enter [1]; rw [l9 ((X2 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))]
  have l13 : ∀ X2 X1 : G, (X2 ◇ X2) = ((X2 ◇ X1) ◇ X1) := by
    intro X2 X1
    conv => enter [1]; rw [l12 X2 X1 X2]
    conv => enter [1, 2]; rw [l10 X2 X1]
  have l14 : ∀ X2 X1 : G, ((X2 ◇ X1) ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1]; rw [← l13 X2 X1]
    conv => enter [1]; rw [l9 X2]
  intro x y
  conv => enter [1]; rw [← l9 x]
  conv => enter [1]; rw [← l14 (x ◇ x) y]

theorem Equation263_312_implies_Equation5 (G : Type*) [Magma G] (h263 : Equation263 G) (h312 : Equation312 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h312 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h263 X0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h312 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation55_360_implies_Equation4 (G : Type*) [Magma G] (h55 : Equation55 G) (h360 : Equation360 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h360 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h55 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h55 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h360 X0 X1]
    conv => enter [1]; rw [l1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation263_309_326_implies_Equation257 (G : Type*) [Magma G] (h263 : Equation263 G) (h309 : Equation309 G) (h326 : Equation326 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h326 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X1) X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l9 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h309 ((X1 ◇ X1) ◇ X1) X0]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← l8 ((X1 ◇ X1) ◇ X1) X1]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l3 X0 X1]
  have l13 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l7 (X1 ◇ X0) ((X0 ◇ X0) ◇ X0)]
  have l14 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 1]; rw [← l12 ((X0 ◇ X1) ◇ X1) X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 1]; rw [← l14 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l0 (((X0 ◇ X1) ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← l17 X0 X1]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l8 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) X0]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 1]; rw [← l12 (((X0 ◇ X1) ◇ X1) ◇ X1) (X0 ◇ X1) X1]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 1]; rw [← l12 (((X0 ◇ X1) ◇ X1) ◇ X1) X0 X1]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 1]; rw [← h263 (X0 ◇ X1) X1]
  have l23 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [← l22 (X0 ◇ X0) X1]
  have l24 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X0]
  have l25 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1]; rw [l2 X0 X0]
  intro x y
  conv => enter [1]; rw [← l25 x y]

theorem Equation263_309_326_implies_Equation260 (G : Type*) [Magma G] (h263 : Equation263 G) (h309 : Equation309 G) (h326 : Equation326 G) : Equation260 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X0) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h326 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X1) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l8 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h309 ((X1 ◇ X1) ◇ X1) X0]
  have l9 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← l7 ((X1 ◇ X1) ◇ X1) X1]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [l6 (X1 ◇ X0) ((X0 ◇ X0) ◇ X0)]
  have l13 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 1]; rw [← l11 ((X0 ◇ X1) ◇ X1) X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 1]; rw [← l13 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l0 (((X0 ◇ X1) ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← l16 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← l7 ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) X0]
  have l19 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 1]; rw [← l11 (((X0 ◇ X1) ◇ X1) ◇ X1) (X0 ◇ X1) X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 1]; rw [← l11 (((X0 ◇ X1) ◇ X1) ◇ X1) X0 X1]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 1]; rw [← h263 (X0 ◇ X1) X1]
  have l22 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l21 X0 X1]
    conv => enter [1]; rw [← h263 X0 X0]
  intro x y
  conv => enter [1]; rw [← l22 x y]

theorem Equation263_309_326_implies_Equation323 (G : Type*) [Magma G] (h263 : Equation263 G) (h309 : Equation309 G) (h326 : Equation326 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X0) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h326 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X1) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l8 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ ((X1 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h309 ((X1 ◇ X1) ◇ X1) X0]
  have l9 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = (((X1 ◇ X1) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← l7 ((X1 ◇ X1) ◇ X1) X1]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h263 X1 X1]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h326 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X0) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [l6 (X1 ◇ X0) ((X0 ◇ X0) ◇ X0)]
  have l13 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 1]; rw [← l11 ((X0 ◇ X1) ◇ X1) X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 1]; rw [← l13 X0 X1]
  have l17 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 (((X0 ◇ X1) ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1, 1]; rw [← l16 X0 X1]
  have l18 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← l11 (((X0 ◇ X0) ◇ X0) ◇ X0) (X0 ◇ X1) X1]
  have l19 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l11 (((X0 ◇ X0) ◇ X0) ◇ X0) X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X0]
    conv => enter [1]; rw [← l19 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [← l11 (((X0 ◇ X1) ◇ X1) ◇ X1) (X0 ◇ X1) X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [← l11 (((X0 ◇ X1) ◇ X1) ◇ X1) X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← l22 X0 X1]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation55_361_375_implies_Equation52 (G : Type*) [Magma G] (h55 : Equation55 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation52 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h55 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h375 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h375 X1 (X1 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← h361 (X1 ◇ (X1 ◇ X1)) X0]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← l8 X1 (X1 ◇ (X1 ◇ X1))]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l12 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h375 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l7 (X0 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [l3 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← l12 X1 X0 (X1 ◇ (X1 ◇ X0))]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [← l14 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l17 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 1, 2]; rw [← l17 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l8 X0 ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l12 X1 (X1 ◇ X0) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 2]; rw [← l12 X1 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 2]; rw [← h55 (X1 ◇ X0) X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l22 (X0 ◇ X0) X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1]; rw [l2 X0 X0]
  intro x y
  conv => enter [1]; rw [← l25 x y]

theorem Equation55_361_375_implies_Equation49 (G : Type*) [Magma G] (h55 : Equation55 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation49 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h375 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h375 X1 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← h361 (X1 ◇ (X1 ◇ X1)) X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← l7 X1 (X1 ◇ (X1 ◇ X1))]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l11 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h375 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2]; rw [← l11 X1 X0 (X1 ◇ (X1 ◇ X0))]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← l13 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [l0 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 1, 2]; rw [← l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← l7 X0 ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2]; rw [← l11 X1 (X1 ◇ X0) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l11 X1 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 2]; rw [← h55 (X1 ◇ X0) X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l21 X0 X1]
    conv => enter [1]; rw [← h55 X0 X0]
  intro x y
  conv => enter [1]; rw [← l22 x y]

theorem Equation55_361_375_implies_Equation378 (G : Type*) [Magma G] (h55 : Equation55 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation378 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h375 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h375 X1 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← h361 (X1 ◇ (X1 ◇ X1)) X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← l7 X1 (X1 ◇ (X1 ◇ X1))]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h55 X1 X1]
  have l11 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = ((X1 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h375 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2]; rw [← l11 X1 X0 (X1 ◇ (X1 ◇ X0))]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← l13 X1 X0]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 (X1 ◇ (X1 ◇ (X1 ◇ X0))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l16 X0 X1]
  have l18 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1]; rw [← l11 X1 (X1 ◇ X0) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1]; rw [← l11 X1 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h55 X0 X0]
    conv => enter [1]; rw [← l19 X1 X0]
  have l21 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [← l11 X1 (X1 ◇ X0) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l11 X1 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
  have l23 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← l22 X1 X0]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation263_308_implies_Equation258 (G : Type*) [Magma G] (h263 : Equation263 G) (h308 : Equation308 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h308 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
    conv => enter [1, 2, 1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X2]
  have l4 : ∀ X0 X2 : G, (((X0 ◇ X0) ◇ X2) ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 X0 X2]
    conv => enter [1]; rw [l1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation263_308_implies_Equation261 (G : Type*) [Magma G] (h263 : Equation263 G) (h308 : Equation308 G) : Equation261 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h308 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h308 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X0) ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h308 (X0 ◇ X0) (X0 ◇ X1)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
    conv => enter [1, 2, 1]; rw [← h263 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = (((X0 ◇ X0) ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X2]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l5 X0 X2]
  have l8 : ∀ X0 X2 : G, (((X0 ◇ X0) ◇ X2) ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 X0 X2]
    conv => enter [1]; rw [l2 X0 X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [l8 X0 X1]
    conv => enter [1, 2, 1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l8 X0 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l7 ((X0 ◇ X0) ◇ X1) X1 X2]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2]; rw [l8 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [← l12 X0 X1 ((X0 ◇ X0) ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l8 x y]
  conv => enter [1, 1]; rw [l14 x y]

theorem Equation55_364_implies_Equation72 (G : Type*) [Magma G] (h55 : Equation55 G) (h364 : Equation364 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h364 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h55 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
    conv => enter [1, 1, 2]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l2 X2 (X0 ◇ X0)]
  have l4 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := by
    intro X2 X0
    conv => enter [1]; rw [← l3 X2 X0 X2]
    conv => enter [1]; rw [l1 X2 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

end Order3
