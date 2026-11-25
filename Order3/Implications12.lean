import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation3_105_271_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h271 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h105 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l2 ((X1 ◇ X0) ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l2 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_63_221_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h221 : Equation221 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h221 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l2 (X0 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation105_270_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h270 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h105 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h270 X0 X1]
    conv => enter [1]; rw [l2 ((X1 ◇ X0) ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation48_221_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h221 : Equation221 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h48 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h221 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h48 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3_105_263_implies_Equation55 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h263 : Equation263 G) : Equation55 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h105 X0 ((X0 ◇ X1) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h105 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation3_55_221_implies_Equation263 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h221 : Equation221 G) : Equation263 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h221 X0 (X1 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation3_105_261_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h261 : Equation261 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h261 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation3_65_221_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h221 : Equation221 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h65 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_105_260_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h260 : Equation260 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h105 X0 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ ((X0 ◇ X1) ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l1 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h260 X0 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l10 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  intro x y
  conv => enter [1]; rw [← l11 x y]

theorem Equation3_49_221_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h221 : Equation221 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h221 X0 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 ((X0 ◇ (X1 ◇ X0)) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h49 X0 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l10 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  intro x y
  conv => enter [1]; rw [← l11 y x]

theorem Equation3_105_228_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h228 : Equation228 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_105_228_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h228 : Equation228 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [l3 X0 (X1 ◇ (X1 ◇ X0))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1, 2]; rw [h3 x]

theorem Equation3_102_221_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h221 : Equation221 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [l3 X0 ((X0 ◇ X1) ◇ X1)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1]; rw [l6 (x ◇ y) y]

theorem Equation3_102_221_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h221 : Equation221 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [l3 X0 ((X0 ◇ X1) ◇ X1)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l2 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1, 2]; rw [h3 x]

theorem Equation3_105_221_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h221 : Equation221 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_105_221_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h221 : Equation221 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_105_221_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h221 : Equation221 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 y (x ◇ x)]

theorem Equation105_208_326_implies_Equation52 (G : Type*) [Magma G] (h105 : Equation105 G) (h208 : Equation208 G) (h326 : Equation326 G) : Equation52 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h208 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h105 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2]; rw [h326 y x]

theorem Equation101_221_375_implies_Equation257 (G : Type*) [Magma G] (h101 : Equation101 G) (h221 : Equation221 G) (h375 : Equation375 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h101 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h221 X1 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h375 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1]; rw [h375 x y]

theorem Equation3_105_205_326_375_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h205 : Equation205 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 ((X1 ◇ (X0 ◇ X0)) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l0 X1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h326 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1, 2]; rw [h326 y x]

theorem Equation3_105_205_326_375_implies_Equation9 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h205 : Equation205 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h375 X0 ((X0 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ X0) ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h375 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation3_104_221_326_375_implies_Equation257 (G : Type*) [Magma G] (h3 : Equation3 G) (h104 : Equation104 G) (h221 : Equation221 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation257 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (X1 ◇ ((X0 ◇ X0) ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← l0 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h375 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1, 1]; rw [h375 x y]

theorem Equation3_104_221_326_375_implies_Equation28 (G : Type*) [Magma G] (h3 : Equation3 G) (h104 : Equation104 G) (h221 : Equation221 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h104 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h326 (X1 ◇ (X0 ◇ X0)) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l0 (X1 ◇ (X0 ◇ X0)) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [← h326 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation105_222_274_implies_Equation2 (G : Type*) [Magma G] (h105 : Equation105 G) (h222 : Equation222 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h222 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h105 X1 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1, 1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_221_229_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h229 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [← h229 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h229 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_104_273_implies_Equation28 (G : Type*) [Magma G] (h3 : Equation3 G) (h104 : Equation104 G) (h273 : Equation273 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h104 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_53_205_implies_Equation9 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h205 : Equation205 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h205 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation3_104_271_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h104 : Equation104 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h104 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_63_205_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h205 : Equation205 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h205 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h63 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation104_270_implies_Equation28 (G : Type*) [Magma G] (h104 : Equation104 G) (h270 : Equation270 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h270 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation48_205_implies_Equation9 (G : Type*) [Magma G] (h48 : Equation48 G) (h205 : Equation205 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation104_264_implies_Equation4 (G : Type*) [Magma G] (h104 : Equation104 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h104 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation75_205_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h205 : Equation205 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h205 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation104_261_implies_Equation4 (G : Type*) [Magma G] (h104 : Equation104 G) (h261 : Equation261 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h104 X1 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 x y]

theorem Equation65_205_implies_Equation5 (G : Type*) [Magma G] (h65 : Equation65 G) (h205 : Equation205 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h205 X1 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation3_104_228_implies_Equation28 (G : Type*) [Magma G] (h3 : Equation3 G) (h104 : Equation104 G) (h228 : Equation228 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h104 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_102_205_implies_Equation9 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h205 : Equation205 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h205 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation3_104_159_263_implies_Equation208 (G : Type*) [Magma G] (h3 : Equation3 G) (h104 : Equation104 G) (h159 : Equation159 G) (h263 : Equation263 G) : Equation208 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h104 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation3_55_159_205_implies_Equation101 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h159 : Equation159 G) (h205 : Equation205 G) : Equation101 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h55 X0 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation104_118_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h118 : Equation118 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h104 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation205_229_implies_Equation2 (G : Type*) [Magma G] (h205 : Equation205 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h205 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_102_273_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h273 : Equation273 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h273 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_102_273_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h273 : Equation273 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h273 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1, 2]; rw [h3 x]

theorem Equation3_102_273_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h273 : Equation273 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h273 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation3_53_228_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h228 : Equation228 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h228 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h53 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l4 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]
  conv => enter [1]; rw [l6 (x ◇ y) y]

theorem Equation3_53_228_implies_Equation332 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h228 : Equation228 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h228 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h53 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l6 x y]
  conv => enter [1, 2]; rw [h3 x]

theorem Equation3_53_228_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h228 : Equation228 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h228 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h53 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 (X0 ◇ X1)]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l4 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l7 (x ◇ x) y]
  conv => enter [1]; rw [l6 ((x ◇ x) ◇ y) y]

theorem Equation3_102_271_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h102 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((((X0 ◇ X0) ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (((X0 ◇ X0) ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_63_228_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h228 : Equation228 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h228 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h63 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ X0)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation102_270_implies_Equation2 (G : Type*) [Magma G] (h102 : Equation102 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h270 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h270 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation48_228_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h228 : Equation228 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation102_264_implies_Equation377 (G : Type*) [Magma G] (h102 : Equation102 G) (h264 : Equation264 G) : Equation377 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation75_228_implies_Equation333 (G : Type*) [Magma G] (h75 : Equation75 G) (h228 : Equation228 G) : Equation333 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h75 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_102_263_326_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h263 : Equation263 G) (h326 : Equation326 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 (x ◇ x) y]

theorem Equation3_55_228_375_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h228 : Equation228 G) (h375 : Equation375 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation102_260_326_implies_Equation4 (G : Type*) [Magma G] (h102 : Equation102 G) (h260 : Equation260 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h260 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation49_228_375_implies_Equation5 (G : Type*) [Magma G] (h49 : Equation49 G) (h228 : Equation228 G) (h375 : Equation375 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h228 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h49 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation102_228_326_375_implies_Equation14 (G : Type*) [Magma G] (h102 : Equation102 G) (h228 : Equation228 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h228 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation102_228_326_375_implies_Equation332 (G : Type*) [Magma G] (h102 : Equation102 G) (h228 : Equation228 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h228 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation3_102_228_326_375_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h228 : Equation228 G) (h326 : Equation326 G) (h375 : Equation375 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h102 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h102 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h228 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h228 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h102 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation3_102_208_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h208 : Equation208 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h208 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2, 2]; rw [h3 x]

theorem Equation3_101_228_implies_Equation257 (G : Type*) [Magma G] (h3 : Equation3 G) (h101 : Equation101 G) (h228 : Equation228 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h228 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h101 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1, 1]; rw [h3 x]

theorem Equation102_118_implies_Equation2 (G : Type*) [Magma G] (h102 : Equation102 G) (h118 : Equation118 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h102 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation228_229_implies_Equation2 (G : Type*) [Magma G] (h228 : Equation228 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h228 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h229 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation101_273_375_implies_Equation5 (G : Type*) [Magma G] (h101 : Equation101 G) (h273 : Equation273 G) (h375 : Equation375 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h101 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h273 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation53_208_326_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h208 : Equation208 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h326 (X0 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h208 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h53 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation3_101_271_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h101 : Equation101 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h101 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_63_208_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h208 : Equation208 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h63 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h208 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h63 X0 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation101_270_375_implies_Equation257 (G : Type*) [Magma G] (h101 : Equation101 G) (h270 : Equation270 G) (h375 : Equation375 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h270 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h101 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h101 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1]; rw [h375 x y]

theorem Equation48_208_326_implies_Equation52 (G : Type*) [Magma G] (h48 : Equation48 G) (h208 : Equation208 G) (h326 : Equation326 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h48 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h208 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h208 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2]; rw [h326 y x]

theorem Equation3_101_261_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h101 : Equation101 G) (h261 : Equation261 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h101 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 (x ◇ x) y]

theorem Equation3_65_208_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h208 : Equation208 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h208 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation3_101_260_implies_Equation257 (G : Type*) [Magma G] (h3 : Equation3 G) (h101 : Equation101 G) (h260 : Equation260 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h101 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h101 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1, 1]; rw [h3 x]

theorem Equation3_49_208_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h208 : Equation208 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h208 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h208 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2, 2]; rw [h3 x]

theorem Equation101_159_264_implies_Equation9 (G : Type*) [Magma G] (h101 : Equation101 G) (h159 : Equation159 G) (h264 : Equation264 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h101 X0 X1]
    conv => enter [1]; rw [← h264 X0 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation75_159_208_implies_Equation28 (G : Type*) [Magma G] (h75 : Equation75 G) (h159 : Equation159 G) (h208 : Equation208 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h208 X0 X1]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation101_159_263_implies_Equation205 (G : Type*) [Magma G] (h101 : Equation101 G) (h159 : Equation159 G) (h263 : Equation263 G) : Equation205 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h101 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← h159 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h263 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← h159 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h263 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 1, 1]; rw [← h159 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 1]; rw [← h101 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h159 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation55_159_208_implies_Equation104 (G : Type*) [Magma G] (h55 : Equation55 G) (h159 : Equation159 G) (h208 : Equation208 G) : Equation104 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h208 ((sK1 ◇ sK0) ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 1, 2]; rw [← h159 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h55 ((sK1 ◇ sK0) ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h159 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ ((((sK1 ◇ sK0) ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h55 (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) (((sK1 ◇ sK0) ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h159 ((sK1 ◇ sK0) ◇ sK0) sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [← h208 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h159 sK0 ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation101_118_implies_Equation2 (G : Type*) [Magma G] (h101 : Equation101 G) (h118 : Equation118 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h101 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation208_229_implies_Equation2 (G : Type*) [Magma G] (h208 : Equation208 G) (h229 : Equation229 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h208 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h229 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation3_101_105_264_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h101 : Equation101 G) (h105 : Equation105 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h101 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation3_75_208_221_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h208 : Equation208 G) (h221 : Equation221 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [← h208 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h75 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h75 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation75_260_implies_Equation28 (G : Type*) [Magma G] (h75 : Equation75 G) (h260 : Equation260 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X1 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation49_264_implies_Equation9 (G : Type*) [Magma G] (h49 : Equation49 G) (h264 : Equation264 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h49 X1 ((X0 ◇ X1) ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation3_75_221_270_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h221 : Equation221 G) (h270 : Equation270 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h221 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h270 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 ((X0 ◇ (X0 ◇ X1)) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l2 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h75 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l7 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h75 X1 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 1]; rw [← h270 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← l11 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 1]; rw [← l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← l13 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [← l14 y x]

theorem Equation3_48_105_264_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h105 : Equation105 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h105 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h48 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ ((X1 ◇ X0) ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [l0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = ((X1 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l2 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h264 X1 (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← l7 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h264 X1 (X1 ◇ X0)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 2]; rw [← h48 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l12 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1, 2]; rw [← l12 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l10 X1 X0]
    conv => enter [1]; rw [← l13 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  intro x y
  conv => enter [1]; rw [← l14 x y]

theorem Equation75_208_263_375_implies_Equation5 (G : Type*) [Magma G] (h75 : Equation75 G) (h208 : Equation208 G) (h263 : Equation263 G) (h375 : Equation375 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h75 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h208 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h263 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation55_101_264_326_implies_Equation4 (G : Type*) [Magma G] (h55 : Equation55 G) (h101 : Equation101 G) (h264 : Equation264 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h101 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h55 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation3_73_229_273_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h229 : Equation229 G) (h273 : Equation273 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h73 ((X1 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h229 X1 X0]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1]; rw [← h229 X1 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_53_118_274_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h118 : Equation118 G) (h274 : Equation274 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h274 (X1 ◇ (X0 ◇ X1)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h118 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h118 X1 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation73_125_229_271_implies_Equation159 (G : Type*) [Magma G] (h73 : Equation73 G) (h125 : Equation125 G) (h229 : Equation229 G) (h271 : Equation271 G) : Equation159 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h125 X0 X1]
    conv => enter [1]; rw [← h125 ((X1 ◇ X0) ◇ X1) X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h73 ((X1 ◇ X0) ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h73 (X1 ◇ X0) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [← l1 X0 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h73 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ (X1 ◇ X0)) X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 x y]

theorem Equation63_118_222_274_implies_Equation159 (G : Type*) [Magma G] (h63 : Equation63 G) (h118 : Equation118 G) (h222 : Equation222 G) (h274 : Equation274 G) : Equation159 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h222 X0 X1]
    conv => enter [1]; rw [← h222 (X1 ◇ (X0 ◇ X1)) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h274 (X0 ◇ (X0 ◇ X1)) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h274 (X0 ◇ X1) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [← l1 X0 (X1 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [← h274 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← l2 X1 X0]
  have l8 : ∀ X0 X1 : G, (((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X1 X0]
    conv => enter [1]; rw [l0 ((X0 ◇ X1) ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 x y]

theorem Equation3_73_270_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h73 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← h73 ((X1 ◇ X0) ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h73 (X1 ◇ X0) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l6 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l6 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_48_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h274 X1 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← h274 (X0 ◇ (X0 ◇ X1)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h274 (X0 ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l6 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l6 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_73_263_326_implies_Equation335 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h263 : Equation263 G) (h326 : Equation326 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h73 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_55_274_375_implies_Equation384 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h274 : Equation274 G) (h375 : Equation375 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h274 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h274 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_73_125_261_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h73 : Equation73 G) (h125 : Equation125 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h125 X0 X1]
    conv => enter [1]; rw [← h125 ((X1 ◇ X0) ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h73 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h73 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3_65_222_274_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h222 : Equation222 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h222 X0 X1]
    conv => enter [1]; rw [← h222 (X1 ◇ (X0 ◇ X1)) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2, 1]; rw [← h274 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h3 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h274 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation125_229_260_implies_Equation2 (G : Type*) [Magma G] (h125 : Equation125 G) (h229 : Equation229 G) (h260 : Equation260 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h229 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h125 X0 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h125 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation49_118_222_implies_Equation2 (G : Type*) [Magma G] (h49 : Equation49 G) (h118 : Equation118 G) (h222 : Equation222 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h222 X0 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h222 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation66_326_implies_Equation14 (G : Type*) [Magma G] (h66 : Equation66 G) (h326 : Equation326 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h66 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation3_66_326_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h66 : Equation66 G) (h326 : Equation326 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h326 X0 X1]
    conv => enter [1]; rw [← h66 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l0 y (x ◇ x)]

theorem Equation65_271_326_implies_Equation332 (G : Type*) [Magma G] (h65 : Equation65 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h65 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h271 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1, 1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X0))]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l3 X1 ((X0 ◇ X1) ◇ X1)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X1)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l4 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l9 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation65_271_implies_Equation63 (G : Type*) [Magma G] (h65 : Equation65 G) (h271 : Equation271 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h65 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h271 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h65 X0 X1]
    conv => enter [1, 1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [l1 X1 (X0 ◇ (X1 ◇ X0))]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← l3 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ ((X0 ◇ X1) ◇ X1)) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l3 X1 ((X0 ◇ X1) ◇ X1)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X1)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l4 X1 (X0 ◇ X1)]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation63_261_326_implies_Equation332 (G : Type*) [Magma G] (h63 : Equation63 G) (h261 : Equation261 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h63 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1, 2, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l3 (X1 ◇ (X1 ◇ X0)) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ (X1 ◇ X0)) X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l9 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation63_261_implies_Equation271 (G : Type*) [Magma G] (h63 : Equation63 G) (h261 : Equation261 G) : Equation271 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h63 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 X0 X1]
    conv => enter [1, 2, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l3 (X1 ◇ (X1 ◇ X0)) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 (X1 ◇ (X1 ◇ X0)) X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X0)]
  have l10 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [l9 X1 X0]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 y x]

theorem Equation65_159_273_implies_Equation263 (G : Type*) [Magma G] (h65 : Equation65 G) (h159 : Equation159 G) (h273 : Equation273 G) : Equation263 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 (sK0 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h159 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h273 ((sK0 ◇ sK1) ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 1]; rw [← h159 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h159 sK0 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) = (((((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h159 (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h273 sK0 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation53_159_261_implies_Equation55 (G : Type*) [Magma G] (h53 : Equation53 G) (h159 : Equation159 G) (h261 : Equation261 G) : Equation55 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h261 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 1, 1]; rw [← h159 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [← h159 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h159 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h159 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation65_159_270_implies_Equation117 (G : Type*) [Magma G] (h65 : Equation65 G) (h159 : Equation159 G) (h270 : Equation270 G) : Equation117 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h159 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h270 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h270 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l4 ((X0 ◇ X1) ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l4 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h159 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (((X0 ◇ X1) ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 2]; rw [l8 (X0 ◇ X1) X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2]; rw [← h270 X1 X0]
  intro x y
  conv => enter [1]; rw [h65 x y]
  conv => enter [1, 2]; rw [l11 x y]

theorem Equation102_159_261_implies_Equation209 (G : Type*) [Magma G] (h102 : Equation102 G) (h159 : Equation159 G) (h261 : Equation261 G) : Equation209 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [← h159 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h159 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h261 X0 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← l8 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h159 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h159 X0 X1]
    conv => enter [1]; rw [← l10 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h159 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l11 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 x y]

theorem Equation65_117_228_270_implies_Equation159 (G : Type*) [Magma G] (h65 : Equation65 G) (h117 : Equation117 G) (h228 : Equation228 G) (h270 : Equation270 G) : Equation159 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h270 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ (X1 ◇ X0)) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h228 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ X1)]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l8 X1 X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [← l10 x y]

theorem Equation102_209_261_implies_Equation159 (G : Type*) [Magma G] (h102 : Equation102 G) (h209 : Equation209 G) (h261 : Equation261 G) : Equation159 G := by
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
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation65_73_125_implies_Equation335 (G : Type*) [Magma G] (h65 : Equation65 G) (h73 : Equation73 G) (h125 : Equation125 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h125 X0 X1]
    conv => enter [1]; rw [← h65 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h73 (X0 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation118_261_implies_Equation384 (G : Type*) [Magma G] (h118 : Equation118 G) (h261 : Equation261 G) : Equation384 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h118 X0 X1]
    conv => enter [1]; rw [← h261 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h118 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_63_273_375_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h273 : Equation273 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
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
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 (X0 ◇ X0) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_53_271_326_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h53 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
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
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l3 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_63_270_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h270 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h270 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h63 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h63 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_48_271_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h48 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h48 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h271 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h271 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_63_263_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h263 : Equation263 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h63 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 (x ◇ x) y]

theorem Equation3_55_271_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h271 : Equation271 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h271 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation3_63_260_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h260 : Equation260 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h63 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h63 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_49_271_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h49 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [← h271 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h271 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_55_273_375_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h273 : Equation273 G) (h375 : Equation375 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h273 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation3_53_263_326_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h263 : Equation263 G) (h326 : Equation326 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 (x ◇ x) y]

theorem Equation3_55_270_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h270 : Equation270 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h270 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h55 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation3_48_263_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h263 : Equation263 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h48 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h263 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 (x ◇ x) y]

theorem Equation3_53_273_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h273 : Equation273 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h273 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h53 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_53_273_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h273 : Equation273 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h273 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h53 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_53_270_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h270 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h53 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h53 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h270 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h53 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h270 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X0 (X1 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_48_273_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h48 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h273 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 X0 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation53_260_326_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h260 : Equation260 G) (h326 : Equation326 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X1) ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h326 (X0 ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation49_273_375_implies_Equation5 (G : Type*) [Magma G] (h49 : Equation49 G) (h273 : Equation273 G) (h375 : Equation375 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 (X1 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation49_270_implies_Equation5 (G : Type*) [Magma G] (h49 : Equation49 G) (h270 : Equation270 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h270 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h49 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h270 (X1 ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation48_260_implies_Equation4 (G : Type*) [Magma G] (h48 : Equation48 G) (h260 : Equation260 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (((X0 ◇ X1) ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h48 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h260 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h48 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation48_270_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h270 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h48 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (((X1 ◇ X0) ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h48 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h270 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h270 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h270 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h48 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l4 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation3_43_273_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h43 : Equation43 G) (h273 : Equation273 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ X0)) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation3_43_53_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h43 : Equation43 G) (h53 : Equation53 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h53 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X1) ◇ X1)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1]; rw [h43 (x ◇ y) y]

theorem Equation43_271_implies_Equation63 (G : Type*) [Magma G] (h43 : Equation43 G) (h271 : Equation271 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h271 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation43_271_implies_Equation124 (G : Type*) [Magma G] (h43 : Equation43 G) (h271 : Equation271 G) : Equation124 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h271 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2]; rw [h43 x (y ◇ x)]

theorem Equation43_63_implies_Equation271 (G : Type*) [Magma G] (h43 : Equation43 G) (h63 : Equation63 G) : Equation271 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h63 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation43_270_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h43 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h270 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [h43 (X0 ◇ (X1 ◇ X0)) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ (X1 ◇ X0)) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation43_48_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h48 : Equation48 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h48 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [h43 X0 ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X1) ◇ X0)]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [h43 X0 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 X1]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation43_263_387_implies_Equation14 (G : Type*) [Magma G] (h43 : Equation43 G) (h263 : Equation263 G) (h387 : Equation387 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h387 ((X0 ◇ X1) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation43_55_332_implies_Equation14 (G : Type*) [Magma G] (h43 : Equation43 G) (h55 : Equation55 G) (h332 : Equation332 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h332 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]
  conv => enter [1]; rw [h43 (x ◇ y) y]

theorem Equation43_261_implies_Equation63 (G : Type*) [Magma G] (h43 : Equation43 G) (h261 : Equation261 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h261 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation43_65_implies_Equation63 (G : Type*) [Magma G] (h43 : Equation43 G) (h65 : Equation65 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 1, 1]; rw [h43 y x]
  conv => enter [1, 1]; rw [h43 (x ◇ y) x]
  conv => enter [1]; rw [h43 (x ◇ (x ◇ y)) y]

theorem Equation43_260_326_332_387_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h260 : Equation260 G) (h326 : Equation326 G) (h332 : Equation332 G) (h387 : Equation387 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h260 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h43 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ ((X0 ◇ X1) ◇ X0)) ((X0 ◇ X1) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [h43 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [h43 (X0 ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ (X0 ◇ X1)) X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l8 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l8 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h332 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← l12 X0 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l11 (X0 ◇ X0) X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h387 X0 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X0]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation43_49_332_375_387_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h49 : Equation49 G) (h332 : Equation332 G) (h375 : Equation375 G) (h387 : Equation387 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← h49 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ (X1 ◇ X0)) ((X0 ◇ (X1 ◇ X0)) ◇ X0)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [h43 X0 (X1 ◇ X0)]
    conv => enter [1, 1, 1]; rw [h43 X0 (X1 ◇ X0)]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1, 1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [h43 X0 ((X1 ◇ X0) ◇ X0)]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h43 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [h43 X0 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h387 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [← l12 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [l11 X1 (X0 ◇ X0)]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X0]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

end Order3
