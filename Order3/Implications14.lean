import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation228_274_implies_Equation118 (G : Type*) [Magma G] (h228 : Equation228 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h274 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ (X1 ◇ X0)) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2]; rw [l4 y x]

theorem Equation73_102_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h102 : Equation102 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h73 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X1) (((X0 ◇ X1) ◇ X1) ◇ X0)]
    conv => enter [1, 2, 1, 1]; rw [l1 X0 X1]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]
  conv => enter [1, 1]; rw [l4 x y]
  conv => enter [1]; rw [l5 y (y ◇ x)]

theorem Equation3_221_270_385_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h270 : Equation270 G) (h385 : Equation385 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h270 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h385 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h221 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_48_105_325_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h105 : Equation105 G) (h325 : Equation325 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h48 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h325 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation3_105_118_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h118 : Equation118 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h118 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [← h118 X0 X1]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ X1) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_117_118_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h117 : Equation117 G) (h118 : Equation118 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h118 X0 X1]
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 ((X1 ◇ X0) ◇ X1) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h117 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h117 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation3_208_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h208 : Equation208 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h208 X0 X1]
    conv => enter [1]; rw [← h274 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_73_101_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h101 : Equation101 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h101 X0 X1]
    conv => enter [1]; rw [← h73 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h73 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_206_264_325_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h264 : Equation264 G) (h325 : Equation325 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation3_75_124_385_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h124 : Equation124 G) (h385 : Equation385 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h124 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h75 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation206_261_325_326_implies_Equation4 (G : Type*) [Magma G] (h206 : Equation206 G) (h261 : Equation261 G) (h325 : Equation325 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h326 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation65_124_375_385_implies_Equation5 (G : Type*) [Magma G] (h65 : Equation65 G) (h124 : Equation124 G) (h375 : Equation375 G) (h385 : Equation385 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h385 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h375 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_206_261_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h261 : Equation261 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h274 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h3 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h274 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_65_73_124_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h73 : Equation73 G) (h124 : Equation124 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h65 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h73 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h3 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h73 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation167_229_326_375_implies_Equation73 (G : Type*) [Magma G] (h167 : Equation167 G) (h229 : Equation229 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h229 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (((X0 ◇ (X1 ◇ X1)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h326 (X0 ◇ (X1 ◇ X1)) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ (X1 ◇ X1)) X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h326 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h229 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h229 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation118_167_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h167 : Equation167 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h118 (((X1 ◇ X0) ◇ X0) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation167_209_261_implies_Equation118 (G : Type*) [Magma G] (h167 : Equation167 G) (h209 : Equation209 G) (h261 : Equation261 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ X1) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← l1 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2]; rw [l3 y x]

theorem Equation65_117_167_implies_Equation73 (G : Type*) [Magma G] (h65 : Equation65 G) (h117 : Equation117 G) (h167 : Equation167 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h167 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1]; rw [l3 (x ◇ y) y]

theorem Equation3_167_206_264_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h206 : Equation206 G) (h264 : Equation264 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h206 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h167 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 (X0 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0))]
    conv => enter [1]; rw [l2 (X1 ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h206 X1 (X0 ◇ ((X1 ◇ X0) ◇ X0))]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l4 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l5 X1 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h375 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3_75_124_167_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h124 : Equation124 G) (h167 : Equation167 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h124 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h167 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) X1]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h124 X1 ((X0 ◇ (X0 ◇ X1)) ◇ X0)]
  have l7 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (((((X1 ◇ X1) ◇ X0) ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l4 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l8 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l12 X1 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3_167_206_261_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h206 : Equation206 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h206 X1 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2]; rw [← h261 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l0 X1 (X0 ◇ ((X1 ◇ X0) ◇ X1))]
    conv => enter [1, 1, 1, 2]; rw [l2 X1 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← l6 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h3 ((X1 ◇ X0) ◇ X1)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l10 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation3_65_124_167_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h124 : Equation124 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h124 X1 ((X1 ◇ (X0 ◇ X1)) ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X0 ◇ (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h65 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l0 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 2, 2, 1]; rw [l2 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [← l6 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h3 (X1 ◇ (X0 ◇ X1))]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation3_167_206_209_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h167 : Equation167 G) (h206 : Equation206 G) (h209 : Equation209 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h206 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h167 X0 X1]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l5 X0 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h206 X0 (X1 ◇ X0)]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = ((((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X1]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l10 (((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) X0]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X0]
    conv => enter [1]; rw [l12 X1 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3_117_124_167_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h117 : Equation117 G) (h124 : Equation124 G) (h167 : Equation167 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h167 X1 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h167 X0 X1]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l5 X0 (X1 ◇ X0)]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h124 X0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = (X0 ◇ ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (((X1 ◇ X0) ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [l3 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l10 X0 ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X1 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)))]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 (((X0 ◇ X1) ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation159_261_274_326_375_implies_Equation2 (G : Type*) [Magma G] (h159 : Equation159 G) (h261 : Equation261 G) (h274 : Equation274 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h261 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [← h274 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X1)) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h326 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation65_73_159_326_375_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h73 : Equation73 G) (h159 : Equation159 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h73 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h73 X1 (X0 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h375 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation159_229_implies_Equation73 (G : Type*) [Magma G] (h159 : Equation159 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h229 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [← h229 X0 X1]
    conv => enter [1, 2]; rw [← h229 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [l6 X1 (X1 ◇ X0)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation118_159_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h159 : Equation159 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h118 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h118 X0 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [← h118 X0 X1]
    conv => enter [1, 1]; rw [← h118 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [l9 X1 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]
  conv => enter [1, 1]; rw [l10 y x]

theorem Equation3_159_206_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h159 : Equation159 G) (h206 : Equation206 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X0) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [← h274 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h206 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1, 2]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X1 ◇ ((X1 ◇ X0) ◇ X1)) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_73_124_159_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h124 : Equation124 G) (h159 : Equation159 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← h73 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h124 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1, 1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation124_274_implies_Equation2 (G : Type*) [Magma G] (h124 : Equation124 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h124 X1 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation73_206_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h206 : Equation206 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h206 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation118_206_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h206 : Equation206 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h206 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h118 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h118 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation124_159_273_implies_Equation221 (G : Type*) [Magma G] (h124 : Equation124 G) (h159 : Equation159 G) (h273 : Equation273 G) : Equation221 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation53_159_206_implies_Equation105 (G : Type*) [Magma G] (h53 : Equation53 G) (h159 : Equation159 G) (h206 : Equation206 G) : Equation105 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h159 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation3_118_273_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h118 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 (X1 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_53_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h229 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ X1) X1]
    conv => enter [1, 1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation118_271_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h118 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h118 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h271 X0 X1]
  have l2 : ∀ X0 X1 : G, ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h271 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation63_229_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h229 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h63 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h229 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_118_270_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h118 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [← h118 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_48_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h229 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h229 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_118_263_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h263 : Equation263 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h118 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_55_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h229 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation118_261_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h261 : Equation261 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h118 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h261 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation65_229_implies_Equation73 (G : Type*) [Magma G] (h65 : Equation65 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h65 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h229 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [l3 (x ◇ y) y]

theorem Equation3_118_260_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h260 : Equation260 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h260 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h118 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h118 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_49_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h229 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h229 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_118_228_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h228 : Equation228 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h118 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 2]; rw [← h118 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [h118 x y]
  conv => enter [1]; rw [l4 y (x ◇ y)]

theorem Equation3_102_229_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h229 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [← l3 y (x ◇ y)]

theorem Equation3_118_221_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h118 : Equation118 G) (h221 : Equation221 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h118 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_105_229_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h229 : Equation229 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h229 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h229 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation118_209_implies_Equation222 (G : Type*) [Magma G] (h118 : Equation118 G) (h209 : Equation209 G) : Equation222 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation117_229_implies_Equation73 (G : Type*) [Magma G] (h117 : Equation117 G) (h229 : Equation229 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h229 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [← l1 y (x ◇ y)]

theorem Equation118_205_326_375_implies_Equation2 (G : Type*) [Magma G] (h118 : Equation118 G) (h205 : Equation205 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h205 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h326 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h118 X0 (X1 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X1)]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X1)]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation104_229_326_375_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h229 : Equation229 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h104 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h375 X1 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h229 X0 (X1 ◇ X1)]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ ((X1 ◇ X1) ◇ X0)) X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_117_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h117 : Equation117 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [← h274 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h117 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h274 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h117 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_73_209_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h209 : Equation209 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h73 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h209 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h73 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation117_209_264_implies_Equation2 (G : Type*) [Magma G] (h117 : Equation117 G) (h209 : Equation209 G) (h264 : Equation264 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h264 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← h209 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 (((X1 ◇ X0) ◇ X1) ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h264 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l2 X1 (X1 ◇ ((X0 ◇ X1) ◇ X1))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation75_117_209_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h117 : Equation117 G) (h209 : Equation209 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h75 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h117 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X1 ◇ X0)]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h75 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ (X1 ◇ X0)) ◇ X1)]
  have l9 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l5 X1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation117_159_264_implies_Equation2 (G : Type*) [Magma G] (h117 : Equation117 G) (h159 : Equation159 G) (h264 : Equation264 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h264 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h264 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1]; rw [← h264 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation75_159_209_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h159 : Equation159 G) (h209 : Equation209 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h75 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ X1) (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h75 (X0 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h75 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h75 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation105_274_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h105 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h105 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation73_221_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h221 : Equation221 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h221 X1 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h221 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation105_159_206_264_implies_Equation53 (G : Type*) [Magma G] (h105 : Equation105 G) (h159 : Equation159 G) (h206 : Equation206 G) (h264 : Equation264 G) : Equation53 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h206 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h105 X1 (X0 ◇ ((X1 ◇ X0) ◇ X0))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation75_124_159_221_implies_Equation273 (G : Type*) [Magma G] (h75 : Equation75 G) (h124 : Equation124 G) (h159 : Equation159 G) (h221 : Equation221 G) : Equation273 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h124 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
  have l4 : ∀ X0 X1 : G, ((((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h221 X1 ((X0 ◇ (X0 ◇ X1)) ◇ X0)]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation104_274_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h104 X1 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation73_205_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h205 : Equation205 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h205 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_102_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h274 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h274 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h274 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_73_228_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h228 : Equation228 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h73 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h73 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h73 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation102_261_325_implies_Equation48 (G : Type*) [Magma G] (h102 : Equation102 G) (h261 : Equation261 G) (h325 : Equation325 G) : Equation48 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [← h261 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h325 X0 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h261 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l1 X0 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l4 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l6 ((X0 ◇ X1) ◇ X0) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ (X0 ◇ X1)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h261 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l11 x y]

theorem Equation65_228_385_implies_Equation270 (G : Type*) [Magma G] (h65 : Equation65 G) (h228 : Equation228 G) (h385 : Equation385 G) : Equation270 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h385 X1 X0]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h385 (X1 ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h228 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [← h65 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h385 X1 X0]
    conv => enter [1]; rw [l1 X0 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l6 (X0 ◇ (X0 ◇ X1)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h385 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [← h65 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l11 y x]

theorem Equation102_209_261_implies_Equation48 (G : Type*) [Magma G] (h102 : Equation102 G) (h209 : Equation209 G) (h261 : Equation261 G) : Equation48 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 1]; rw [← h209 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h209 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h261 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X1 ◇ X0)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ X1) (X1 ◇ X0)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 x y]

theorem Equation65_117_228_implies_Equation270 (G : Type*) [Magma G] (h65 : Equation65 G) (h117 : Equation117 G) (h228 : Equation228 G) : Equation270 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h117 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ X1)]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← l3 (X1 ◇ X0) (X0 ◇ X1)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation65_159_228_implies_Equation117 (G : Type*) [Magma G] (h65 : Equation65 G) (h159 : Equation159 G) (h228 : Equation228 G) : Equation117 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 ((X1 ◇ X0) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 (X0 ◇ X1) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h65 X0 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l8 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h159 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l9 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l10 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 y x]

theorem Equation3_101_274_326_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h101 : Equation101 G) (h274 : Equation274 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h101 X0 X1]
    conv => enter [1]; rw [← h274 ((X0 ◇ X1) ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [← h274 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h274 X1 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_73_208_326_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h208 : Equation208 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h208 X0 X1]
    conv => enter [1]; rw [← h73 (X0 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← h73 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h73 X1 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation101_206_264_implies_Equation4 (G : Type*) [Magma G] (h101 : Equation101 G) (h206 : Equation206 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h101 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h206 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1]
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation75_124_208_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h124 : Equation124 G) (h208 : Equation208 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h208 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 2]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h124 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = (((((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l1 X1 X0]
    conv => enter [1, 1, 1, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation75_167_271_375_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h167 : Equation167 G) (h271 : Equation271 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l2 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation63_167_264_326_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h167 : Equation167 G) (h264 : Equation264 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ (X0 ◇ X1)) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation75_167_261_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h167 : Equation167 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h75 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [l2 ((X0 ◇ X1) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h75 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation65_167_264_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h167 : Equation167 G) (h264 : Equation264 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h264 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h264 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [l2 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h264 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation75_159_261_implies_Equation2 (G : Type*) [Magma G] (h75 : Equation75 G) (h159 : Equation159 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h261 X1 ((X0 ◇ (X0 ◇ X1)) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h159 (X1 ◇ X0) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X0]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation65_159_264_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h159 : Equation159 G) (h264 : Equation264 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h65 X1 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h65 X1 (X0 ◇ ((X1 ◇ X0) ◇ X0))]
  have l4 : ∀ X0 X1 : G, ((((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X1 ◇ X0) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h159 (X0 ◇ X1) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← l2 X1 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l7 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [l9 X1 X0]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X0]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation3_73_273_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h73 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [l2 X1 (X1 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_53_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h274 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ X0) ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation73_271_implies_Equation125 (G : Type*) [Magma G] (h73 : Equation73 G) (h271 : Equation271 G) : Equation125 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h73 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h271 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h271 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [← h73 X0 X1]
  intro x y
  conv => enter [1]; rw [h73 x y]
  conv => enter [1, 2]; rw [l2 y x]

theorem Equation63_274_implies_Equation118 (G : Type*) [Magma G] (h63 : Equation63 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h274 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h63 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h63 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation3_73_263_implies_Equation125 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h263 : Equation263 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h73 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [l2 X1 (X1 ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2]; rw [l5 x y]

theorem Equation3_55_274_implies_Equation118 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h274 : Equation274 G) : Equation118 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h274 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [l2 ((X1 ◇ X0) ◇ X1) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]
  conv => enter [1, 1]; rw [l6 x y]
  conv => enter [1]; rw [l5 y (x ◇ y)]

theorem Equation73_261_implies_Equation2 (G : Type*) [Magma G] (h73 : Equation73 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h261 X0 X1]
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h73 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation65_274_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h65 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h65 X0 X1]
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h274 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_73_260_326_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h260 : Equation260 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h73 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h73 X0 (X1 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 ((X1 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 ((X1 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h375 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h73 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_49_274_326_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h274 : Equation274 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h49 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h274 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [h375 X1 X0]
    conv => enter [1]; rw [← h274 X0 (X1 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X1)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 ((X1 ◇ X0) ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [← h274 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation65_270_385_implies_Equation228 (G : Type*) [Magma G] (h65 : Equation65 G) (h270 : Equation270 G) (h385 : Equation385 G) : Equation228 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h65 X1 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ (X1 ◇ X0)) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h385 (X1 ◇ X0) X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h385 X0 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 (X0 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← h385 (X1 ◇ X0) X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 1]; rw [← h385 (X1 ◇ X0) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l7 X0 X1]
  have l16 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l5 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 1]; rw [← h385 (X1 ◇ X0) X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X0 X1]
    conv => enter [1]; rw [l18 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [← h65 X1 (X0 ◇ X1)]
  have l21 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 ((X1 ◇ X0) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 1]; rw [← l8 X0 X1]
  have l22 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1, 2]; rw [← l0 (X1 ◇ X0) X0]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l20 X1 X0]
    conv => enter [1]; rw [← l22 X1 X0]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
  have l25 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [l24 X0 X1]
  have l26 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 ((X1 ◇ X0) ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [← l11 X0 X1]
  have l27 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1, 2, 2]; rw [← l8 X0 X1]
  have l28 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0]
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ X0)]
  have l29 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1, 2]; rw [← l25 X1 X0]
  have l30 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l29 X1 X0]
    conv => enter [1, 1]; rw [← l19 X0 X1]
  have l31 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h385 X0 X1]
    conv => enter [1]; rw [l14 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h385 X0 X1]
  have l32 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1]; rw [← l31 X1 X0]
  have l33 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l32 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l34 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l33 X0 X1]
    conv => enter [1]; rw [← h270 X1 X0]
  intro x y
  conv => enter [1]; rw [← l34 y x]

theorem Equation48_261_325_implies_Equation102 (G : Type*) [Magma G] (h48 : Equation48 G) (h261 : Equation261 G) (h325 : Equation325 G) : Equation102 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h325 X1 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h325 X0 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l1 X1 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← h325 X0 (X0 ◇ X1)]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 2]; rw [← h325 X0 (X0 ◇ X1)]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 (X1 ◇ X0) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1, 1]; rw [l7 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
  have l17 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2, 1]; rw [l5 X0 X1]
  have l18 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 2]; rw [← h325 X0 (X0 ◇ X1)]
  have l19 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l15 X1 X0]
    conv => enter [1]; rw [l18 X1 X0]
  have l20 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← h261 X1 (X1 ◇ X0)]
  have l21 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l8 X0 X1]
  have l22 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 1]; rw [← l0 X0 (X0 ◇ X1)]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l20 X0 X1]
    conv => enter [1]; rw [← l22 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l24 X0 X1]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l11 X1 X0]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1, 1, 1]; rw [← l8 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1, 1]; rw [← l0 (X0 ◇ X1) X0]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1, 1]; rw [← l25 X0 X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1, 2]; rw [← l19 X1 X0]
  have l31 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l14 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h325 X1 X0]
  have l32 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l30 X1 X0]
    conv => enter [1]; rw [← l31 X1 X0]
  have l33 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1]; rw [← l0 X1 X0]
  have l34 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l33 X1 X0]
    conv => enter [1]; rw [← h48 X1 X0]
  intro x y
  conv => enter [1]; rw [← l34 x y]

theorem Equation3_65_263_326_375_385_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h263 : Equation263 G) (h326 : Equation326 G) (h375 : Equation375 G) (h385 : Equation385 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h385 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [l4 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1, 2]; rw [← h375 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ (X1 ◇ X0)) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation3_55_261_325_326_375_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h261 : Equation261 G) (h325 : Equation325 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h325 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ (X1 ◇ X0)) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [l4 X1 (X0 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 1]; rw [← h326 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h325 X1 ((X0 ◇ X1) ◇ X0)]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  intro x y
  conv => enter [1]; rw [← l10 x y]

theorem Equation65_228_263_375_implies_Equation5 (G : Type*) [Magma G] (h65 : Equation65 G) (h228 : Equation228 G) (h263 : Equation263 G) (h375 : Equation375 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h263 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h228 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h263 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation55_102_261_326_implies_Equation4 (G : Type*) [Magma G] (h55 : Equation55 G) (h102 : Equation102 G) (h261 : Equation261 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h102 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h55 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation3_65_167_261_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h167 : Equation167 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h167 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h65 X1 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1, 2]; rw [← h167 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← h3 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l8 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h261 X0 X1]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l10 X1 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation48_159_261_implies_Equation209 (G : Type*) [Magma G] (h48 : Equation48 G) (h159 : Equation159 G) (h261 : Equation261 G) : Equation209 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h48 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 2, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1, 2]; rw [← l3 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← h159 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h261 x y]
  conv => enter [1, 1]; rw [l6 x y]

theorem Equation65_159_261_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h159 : Equation159 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h159 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h159 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 1, 2, 1]; rw [l1 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h159 X0 X1]
  have l7 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l6 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation65_117_270_implies_Equation228 (G : Type*) [Magma G] (h65 : Equation65 G) (h117 : Equation117 G) (h270 : Equation270 G) : Equation228 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h117 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [← h65 X0 X1]
    conv => enter [1, 2]; rw [← h65 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1, 1, 1]; rw [h270 X0 X1]
    conv => enter [1]; rw [l0 ((X1 ◇ X0) ◇ X0) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (((X0 ◇ X1) ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = (X1 ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← l3 ((X0 ◇ X1) ◇ X0) X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2, 1]; rw [← l3 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l3 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l8 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2, 1]; rw [l2 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [← l3 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [← l10 X0 (X1 ◇ X0)]
  have l14 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l13 X1 (X1 ◇ X0)]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l14 X0 X1]
    conv => enter [1]; rw [← h270 X1 X0]
  intro x y
  conv => enter [1]; rw [← l15 y x]

theorem Equation48_209_261_implies_Equation102 (G : Type*) [Magma G] (h48 : Equation48 G) (h209 : Equation209 G) (h261 : Equation261 G) : Equation102 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← h209 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h209 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h261 X0 X1]
    conv => enter [1, 1]; rw [← h261 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1, 2, 2]; rw [h48 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X0 ◇ X1))]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X1]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [← l3 (X0 ◇ (X1 ◇ X0)) X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 1, 2]; rw [← l3 X0 X1]
    conv => enter [1, 1, 1, 1]; rw [← l3 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2, 1, 2]; rw [l2 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ X1) ((X0 ◇ X1) ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l10 (X0 ◇ X1) X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l13 (X0 ◇ X1) X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l14 X1 X0]
    conv => enter [1]; rw [← h48 X1 X0]
  intro x y
  conv => enter [1]; rw [← l15 x y]

theorem Equation63_167_271_326_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h167 : Equation167 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h271 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation49_167_260_implies_Equation2 (G : Type*) [Magma G] (h49 : Equation49 G) (h167 : Equation167 G) (h260 : Equation260 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h167 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h167 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h260 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h167 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h167 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l6 X0 (X1 ◇ X0)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 X0]
    conv => enter [1]; rw [← h167 X1 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation41 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation41 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation168 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation168 G := by
  intro x y z
  conv => enter [1]; rw [h2 x ((y ◇ x) ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation5 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation336 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation336 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation374 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation374 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) ((x ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation13 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation13 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation14 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation14 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation24 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation24 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation29 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation29 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation62 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation62 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation256 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation256 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((x ◇ x) ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation332 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation332 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation387 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation387 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) ((y ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation38 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation38 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation39 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation39 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation66 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation66 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation106 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation106 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ ((y ◇ x) ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation115 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation115 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ ((x ◇ x) ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation219 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation219 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ (x ◇ x)) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation224 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation224 G := by
  intro x y z
  conv => enter [1]; rw [h2 x ((y ◇ (x ◇ z)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation281 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation281 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((y ◇ y) ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation73 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation73 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation118 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation118 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ ((x ◇ y) ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation125 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation125 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ ((y ◇ x) ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation138 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation138 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ ((z ◇ y) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation215 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation215 G := by
  intro x y z
  conv => enter [1]; rw [h2 x ((x ◇ (y ◇ z)) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation222 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation222 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ (x ◇ y)) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation229 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation229 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ (y ◇ x)) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation274 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation274 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((y ◇ x) ◇ y) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation63 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation63 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation271 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation271 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((y ◇ x) ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation314 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation314 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation366 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation366 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) ((y ◇ x) ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation111 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation111 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ ((y ◇ z) ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation162 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation162 G := by
  intro x y z
  conv => enter [1]; rw [h2 x ((x ◇ y) ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation242 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation242 G := by
  intro x y z
  conv => enter [1]; rw [h2 x ((y ◇ (z ◇ y)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation335 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation335 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation384 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation384 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) ((y ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation43 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation43 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation318 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation318 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation363 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation363 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) ((x ◇ y) ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation343 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation343 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation379 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation379 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) ((x ◇ y) ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation58 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation58 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation266 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation266 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (((x ◇ y) ◇ z) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation124 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation124 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ ((y ◇ x) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation206 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation206 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ (x ◇ y)) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation327 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation327 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation329 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation329 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation381 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation381 G := by
  intro x y z
  conv => enter [1, 1]; rw [h2 x (x ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation395 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation395 G := by
  intro x y z
  conv => enter [1, 1]; rw [h2 x (z ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation109 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation109 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ ((y ◇ y) ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation246 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation246 G := by
  intro x y z
  conv => enter [1]; rw [h2 x ((y ◇ (z ◇ z)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation317 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation317 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation372 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation372 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) ((y ◇ z) ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation167 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation167 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ x) ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation72 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation72 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation258 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation258 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((x ◇ x) ◇ y) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation311 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation311 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation370 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation370 G := by
  intro x y z
  conv => enter [1, 1]; rw [h2 x (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation65 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation65 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation261 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation261 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((x ◇ y) ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation103 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation103 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ ((x ◇ y) ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation238 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation238 G := by
  intro x y z
  conv => enter [1]; rw [h2 x ((y ◇ (z ◇ x)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation319 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation319 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation371 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation371 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) ((y ◇ z) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation16 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation16 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation26 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation26 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ y) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation313 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation365 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation365 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) ((y ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation52 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation52 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation257 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation257 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((x ◇ x) ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation11 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation31 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation31 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation315 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation362 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation362 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) ((x ◇ y) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation9 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation9 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation28 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation28 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation10 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation10 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation25 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation25 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation127 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation127 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ ((y ◇ y) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation212 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation212 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ (y ◇ y)) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation53 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation53 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation273 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation273 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((y ◇ x) ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation56 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation56 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation283 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation283 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((y ◇ y) ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation316 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation368 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation368 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) ((y ◇ y) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation117 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation117 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ ((x ◇ y) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation209 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation209 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ (y ◇ x)) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation325 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation325 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation385 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation385 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation108 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation108 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ ((y ◇ y) ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation231 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation231 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ (y ◇ y)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation333 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation377 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation377 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) ((x ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation153 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation153 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ x) ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation156 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation156 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ y) ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation100 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation100 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ ((x ◇ x) ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation218 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation218 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ (x ◇ x)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation50 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation280 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation280 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((y ◇ y) ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation48 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation48 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation102 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation102 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ ((x ◇ y) ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation228 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation228 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ (y ◇ x)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation270 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation270 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((y ◇ x) ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation312 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation360 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation360 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) ((x ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation105 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation105 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ ((y ◇ x) ◇ y))]

end Order3
