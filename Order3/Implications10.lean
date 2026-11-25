import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation3_221_375_384_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h375 : Equation375 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation3_221_326_375_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h326 : Equation326 G) (h375 : Equation375 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 2]; rw [h326 x y]

theorem Equation3_221_375_384_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h375 : Equation375 G) (h384 : Equation384 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation3_105_326_335_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h326 : Equation326 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h335 ((X1 ◇ X0) ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1]; rw [l3 y x]

theorem Equation3_105_326_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h326 : Equation326 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h335 ((X1 ◇ X0) ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]
  conv => enter [1]; rw [l3 y x]
  conv => enter [1, 2]; rw [h326 x y]

theorem Equation3_105_326_335_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h326 : Equation326 G) (h335 : Equation335 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 ((X1 ◇ X0) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h335 ((X1 ◇ X0) ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l7 y (x ◇ x)]
  conv => enter [1]; rw [l3 y (x ◇ x)]

theorem Equation221_378_implies_Equation5 (G : Type*) [Magma G] (h221 : Equation221 G) (h378 : Equation378 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X1) X1]
    conv => enter [1, 1, 2]; rw [← h378 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h378 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h221 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l2 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h378 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation105_323_implies_Equation4 (G : Type*) [Magma G] (h105 : Equation105 G) (h323 : Equation323 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h323 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h323 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 (X1 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h323 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation3_221_377_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h377 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h377 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_105_333_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h333 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h105 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h333 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3_221_335_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h335 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_221_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h335 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_221_335_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h335 : Equation335 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h335 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 y (x ◇ x)]

theorem Equation3_105_384_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h384 ((X1 ◇ X0) ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]

theorem Equation3_105_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h384 ((X1 ◇ X0) ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_105_384_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h384 : Equation384 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h384 ((X1 ◇ X0) ◇ X1) X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l6 y (x ◇ x)]

theorem Equation3_221_333_implies_Equation257 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h333 : Equation333 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h221 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 1, 1]; rw [h3 x]

theorem Equation3_105_377_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h377 : Equation377 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h377 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2, 2]; rw [h3 x]

theorem Equation3_221_325_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h325 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation3_105_385_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h385 X0 X1]
    conv => enter [1]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h385 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation221_323_375_implies_Equation257 (G : Type*) [Magma G] (h221 : Equation221 G) (h323 : Equation323 G) (h375 : Equation375 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h221 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 1]; rw [h375 x y]

theorem Equation105_326_378_implies_Equation52 (G : Type*) [Magma G] (h105 : Equation105 G) (h326 : Equation326 G) (h378 : Equation378 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h105 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 2]; rw [h326 y x]

theorem Equation3_221_271_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h271 : Equation271 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X1 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l5 (X0 ◇ X1) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [l5 X1 ((X1 ◇ X0) ◇ X0)]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation3_63_105_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h63 : Equation63 G) (h105 : Equation105 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← h63 X0 ((X1 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [l5 X1 (X0 ◇ (X0 ◇ X1))]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X1 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l10 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation3_221_270_273_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h270 : Equation270 G) (h273 : Equation273 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h270 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h221 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h273 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h221 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation3_48_53_105_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h48 : Equation48 G) (h53 : Equation53 G) (h105 : Equation105 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h48 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h53 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]

theorem Equation3_221_261_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h261 : Equation261 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h221 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h261 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← h221 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 1]; rw [← l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h221 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2]; rw [← h261 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_65_105_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h65 : Equation65 G) (h105 : Equation105 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h105 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (((X1 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h105 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← l1 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h105 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 1]; rw [← h65 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h65 X1 (X1 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation3_221_260_273_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h221 : Equation221 G) (h260 : Equation260 G) (h273 : Equation273 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h221 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h273 X0 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_49_53_105_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h53 : Equation53 G) (h105 : Equation105 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h105 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h105 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h53 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation209_385_implies_Equation2 (G : Type*) [Magma G] (h209 : Equation209 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h385 X0 X1]
    conv => enter [1, 2, 2]; rw [← h385 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [← h209 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation117_325_implies_Equation2 (G : Type*) [Magma G] (h117 : Equation117 G) (h325 : Equation325 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h325 X1 X0]
    conv => enter [1, 1, 1]; rw [← h325 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h117 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation209_384_implies_Equation118 (G : Type*) [Magma G] (h209 : Equation209 G) (h384 : Equation384 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
    conv => enter [1, 2, 2]; rw [← h384 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2]; rw [h384 y x]

theorem Equation209_384_implies_Equation222 (G : Type*) [Magma G] (h209 : Equation209 G) (h384 : Equation384 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
    conv => enter [1, 2, 2]; rw [← h384 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2]; rw [h384 y x]
  conv => enter [1]; rw [l2 y (x ◇ y)]

theorem Equation209_384_implies_Equation167 (G : Type*) [Magma G] (h209 : Equation209 G) (h384 : Equation384 G) : Equation167 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_209_384_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h209 : Equation209 G) (h384 : Equation384 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
    conv => enter [1, 2, 2]; rw [← h384 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X1) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l8 y (x ◇ x)]

theorem Equation117_335_implies_Equation73 (G : Type*) [Magma G] (h117 : Equation117 G) (h335 : Equation335 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h335 ((X0 ◇ X1) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
    conv => enter [1, 1, 1]; rw [← h335 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]
  conv => enter [1]; rw [h335 (x ◇ y) y]

theorem Equation117_335_implies_Equation125 (G : Type*) [Magma G] (h117 : Equation117 G) (h335 : Equation335 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h335 ((X0 ◇ X1) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
    conv => enter [1, 1, 1]; rw [← h335 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]
  conv => enter [1, 1]; rw [h335 x y]
  conv => enter [1]; rw [l2 y (y ◇ x)]

theorem Equation117_335_implies_Equation167 (G : Type*) [Magma G] (h117 : Equation117 G) (h335 : Equation335 G) : Equation167 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_117_335_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h117 : Equation117 G) (h335 : Equation335 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h335 ((X0 ◇ X1) ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
    conv => enter [1, 1, 1]; rw [← h335 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1, 1]; rw [← l1 X1 X0]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l8 (x ◇ x) y]

theorem Equation209_378_implies_Equation4 (G : Type*) [Magma G] (h209 : Equation209 G) (h378 : Equation378 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h378 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h209 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation117_323_implies_Equation5 (G : Type*) [Magma G] (h117 : Equation117 G) (h323 : Equation323 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h323 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h117 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation209_377_implies_Equation9 (G : Type*) [Magma G] (h209 : Equation209 G) (h377 : Equation377 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h377 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation117_333_implies_Equation28 (G : Type*) [Magma G] (h117 : Equation117 G) (h333 : Equation333 G) : Equation28 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h333 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [← h117 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation209_335_implies_Equation261 (G : Type*) [Magma G] (h209 : Equation209 G) (h335 : Equation335 G) : Equation261 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h335 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h209 x y]
  conv => enter [1, 1]; rw [l0 x y]

theorem Equation117_384_implies_Equation65 (G : Type*) [Magma G] (h117 : Equation117 G) (h384 : Equation384 G) : Equation65 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 1]; rw [h384 X1 X0]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [h117 x y]
  conv => enter [1, 2]; rw [l0 x y]

theorem Equation209_333_implies_Equation2 (G : Type*) [Magma G] (h209 : Equation209 G) (h333 : Equation333 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h209 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h333 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation117_377_implies_Equation2 (G : Type*) [Magma G] (h117 : Equation117 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h117 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h377 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3_209_273_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h209 : Equation209 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h209 X0 ((X1 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h209 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h209 X1 (X1 ◇ X0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation3_53_117_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h117 : Equation117 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h117 X1 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation209_271_326_implies_Equation332 (G : Type*) [Magma G] (h209 : Equation209 G) (h271 : Equation271 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h209 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation209_271_implies_Equation63 (G : Type*) [Magma G] (h209 : Equation209 G) (h271 : Equation271 G) : Equation63 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h209 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation209_271_implies_Equation124 (G : Type*) [Magma G] (h209 : Equation209 G) (h271 : Equation271 G) : Equation124 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h271 X0 X1]
    conv => enter [1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [l0 ((X1 ◇ X0) ◇ X0) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [← h209 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h209 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2]; rw [l2 x y]

theorem Equation209_271_implies_Equation206 (G : Type*) [Magma G] (h209 : Equation209 G) (h271 : Equation271 G) : Equation206 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h209 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h209 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1]; rw [l3 y (x ◇ (x ◇ y))]

theorem Equation209_271_implies_Equation65 (G : Type*) [Magma G] (h209 : Equation209 G) (h271 : Equation271 G) : Equation65 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l1 X1 X0]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h209 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h209 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation63_117_326_implies_Equation332 (G : Type*) [Magma G] (h63 : Equation63 G) (h117 : Equation117 G) (h326 : Equation326 G) : Equation332 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h117 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [h326 y x]

theorem Equation63_117_implies_Equation271 (G : Type*) [Magma G] (h63 : Equation63 G) (h117 : Equation117 G) : Equation271 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h117 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation63_117_implies_Equation124 (G : Type*) [Magma G] (h63 : Equation63 G) (h117 : Equation117 G) : Equation124 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h117 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1]; rw [l3 ((y ◇ x) ◇ x) y]

theorem Equation63_117_implies_Equation206 (G : Type*) [Magma G] (h63 : Equation63 G) (h117 : Equation117 G) : Equation206 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h63 X0 X1]
    conv => enter [1, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [← h117 X1 X0]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l4 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [← h117 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 1]; rw [l2 x y]

theorem Equation63_117_implies_Equation65 (G : Type*) [Magma G] (h63 : Equation63 G) (h117 : Equation117 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ ((X1 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X1 ◇ X0) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1]; rw [← h117 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 1]; rw [l3 (y ◇ x) x]
  conv => enter [1]; rw [l3 (x ◇ (y ◇ x)) y]

theorem Equation209_270_implies_Equation2 (G : Type*) [Magma G] (h209 : Equation209 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h270 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h209 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h209 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation48_117_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h117 : Equation117 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h48 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h117 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h117 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_209_263_375_implies_Equation258 (G : Type*) [Magma G] (h3 : Equation3 G) (h209 : Equation209 G) (h263 : Equation263 G) (h375 : Equation375 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h209 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X0 ◇ X1) ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 (x ◇ x) y]

theorem Equation3_55_117_326_implies_Equation72 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h117 : Equation117 G) (h326 : Equation326 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ (X1 ◇ X0)) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l4 y (x ◇ x)]

theorem Equation209_260_375_implies_Equation4 (G : Type*) [Magma G] (h209 : Equation209 G) (h260 : Equation260 G) (h375 : Equation375 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h209 X0 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation49_117_326_implies_Equation5 (G : Type*) [Magma G] (h49 : Equation49 G) (h117 : Equation117 G) (h326 : Equation326 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h326 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h117 X0 (X1 ◇ X0)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_209_228_implies_Equation118 (G : Type*) [Magma G] (h3 : Equation3 G) (h209 : Equation209 G) (h228 : Equation228 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2]; rw [l7 y x]

theorem Equation3_209_228_implies_Equation222 (G : Type*) [Magma G] (h3 : Equation3 G) (h209 : Equation209 G) (h228 : Equation228 G) : Equation222 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [l5 (X0 ◇ (X1 ◇ X0)) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 1, 2]; rw [l6 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l5 y x]
  conv => enter [1, 2]; rw [l9 y x]
  conv => enter [1]; rw [l8 y (x ◇ y)]

theorem Equation3_209_228_implies_Equation384 (G : Type*) [Magma G] (h3 : Equation3 G) (h209 : Equation209 G) (h228 : Equation228 G) : Equation384 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h209 X0 X1]
    conv => enter [1]; rw [← h209 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h209 X0 (X1 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h209 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X1)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3_102_117_implies_Equation73 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h117 : Equation117 G) : Equation73 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ (X1 ◇ X0)) X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1]; rw [l7 (x ◇ y) y]

theorem Equation3_102_117_implies_Equation125 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h117 : Equation117 G) : Equation125 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [l5 X1 ((X0 ◇ X1) ◇ X0)]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X1 ((X1 ◇ X0) ◇ X1)]
    conv => enter [1, 2, 1]; rw [l6 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ (X1 ◇ X0)) X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 1]; rw [l9 x y]
  conv => enter [1]; rw [l8 y (y ◇ x)]

theorem Equation3_102_117_implies_Equation335 (G : Type*) [Magma G] (h3 : Equation3 G) (h102 : Equation102 G) (h117 : Equation117 G) : Equation335 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h117 X0 X1]
    conv => enter [1]; rw [← h117 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h117 X0 ((X0 ◇ X1) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h117 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h102 X0 X1]
    conv => enter [1]; rw [← l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l5 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l5 (X1 ◇ (X1 ◇ X0)) X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation208_385_implies_Equation28 (G : Type*) [Magma G] (h208 : Equation208 G) (h385 : Equation385 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h385 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h208 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation101_325_implies_Equation9 (G : Type*) [Magma G] (h101 : Equation101 G) (h325 : Equation325 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h101 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation208_384_implies_Equation2 (G : Type*) [Magma G] (h208 : Equation208 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h208 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h384 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h384 (X0 ◇ X1) X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation101_335_implies_Equation2 (G : Type*) [Magma G] (h101 : Equation101 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h101 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h335 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h335 X0 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l4 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation3_208_377_implies_Equation52 (G : Type*) [Magma G] (h3 : Equation3 G) (h208 : Equation208 G) (h377 : Equation377 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h208 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2, 2]; rw [h3 x]

theorem Equation3_101_333_implies_Equation257 (G : Type*) [Magma G] (h3 : Equation3 G) (h101 : Equation101 G) (h333 : Equation333 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h333 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h101 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 1, 1]; rw [h3 x]

theorem Equation208_335_implies_Equation2 (G : Type*) [Magma G] (h208 : Equation208 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h208 X0 X1]
    conv => enter [1]; rw [← h335 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h335 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h208 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 X0]
    conv => enter [1, 2]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation101_384_implies_Equation2 (G : Type*) [Magma G] (h101 : Equation101 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h101 X0 X1]
    conv => enter [1]; rw [← h384 ((X0 ◇ X1) ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h101 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 X1]
    conv => enter [1, 1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation208_333_implies_Equation28 (G : Type*) [Magma G] (h208 : Equation208 G) (h333 : Equation333 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h333 X1 X0]
    conv => enter [1]; rw [← h208 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation101_377_implies_Equation9 (G : Type*) [Magma G] (h101 : Equation101 G) (h377 : Equation377 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h377 X0 X1]
    conv => enter [1]; rw [← h101 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation208_273_implies_Equation28 (G : Type*) [Magma G] (h208 : Equation208 G) (h273 : Equation273 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h273 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h208 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h208 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation53_101_implies_Equation9 (G : Type*) [Magma G] (h53 : Equation53 G) (h101 : Equation101 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h53 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h101 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation208_271_375_implies_Equation2 (G : Type*) [Magma G] (h208 : Equation208 G) (h271 : Equation271 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h208 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h271 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h271 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h271 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1]; rw [← h271 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation63_101_326_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h101 : Equation101 G) (h326 : Equation326 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h101 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h63 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h326 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h63 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l0 X0 (X1 ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h63 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h63 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3_208_264_375_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h208 : Equation208 G) (h264 : Equation264 G) (h375 : Equation375 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h264 X0 X1]
    conv => enter [1]; rw [← h208 X1 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h264 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation3_75_101_326_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h101 : Equation101 G) (h326 : Equation326 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h75 X0 X1]
    conv => enter [1]; rw [← h101 X1 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h326 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation208_261_implies_Equation4 (G : Type*) [Magma G] (h208 : Equation208 G) (h261 : Equation261 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h208 X0 X1]
    conv => enter [1]; rw [← h261 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h208 X1 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation65_101_implies_Equation5 (G : Type*) [Magma G] (h65 : Equation65 G) (h101 : Equation101 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h101 X0 X1]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h101 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l0 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_208_228_263_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h208 : Equation208 G) (h228 : Equation228 G) (h263 : Equation263 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h208 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h3 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h228 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_55_101_102_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h101 : Equation101 G) (h102 : Equation102 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h101 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h102 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h55 X1 (X1 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation206_326_385_implies_Equation2 (G : Type*) [Magma G] (h206 : Equation206 G) (h326 : Equation326 G) (h385 : Equation385 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h385 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← h326 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 (X1 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h385 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation124_325_375_implies_Equation2 (G : Type*) [Magma G] (h124 : Equation124 G) (h325 : Equation325 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h325 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (((X1 ◇ X1) ◇ X0) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← h375 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h375 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h325 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation206_384_implies_Equation14 (G : Type*) [Magma G] (h206 : Equation206 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation3_206_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_206_384_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h384 : Equation384 G) : Equation115 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h384 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1) (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1, 2, 2]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l9 y (x ◇ x)]

theorem Equation124_335_implies_Equation14 (G : Type*) [Magma G] (h124 : Equation124 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h335 ((X1 ◇ X0) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h335 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [← l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
    conv => enter [1, 1, 1]; rw [← h335 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation3_124_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h124 : Equation124 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h335 ((X1 ◇ X0) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h335 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [← l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
    conv => enter [1, 1, 1]; rw [← h335 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_124_335_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h124 : Equation124 G) (h335 : Equation335 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h335 ((X1 ◇ X0) ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h335 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h335 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← l0 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X1) ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 1]; rw [← l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 1]; rw [← l1 (X1 ◇ X0) (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X1 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h335 X1 X0]
    conv => enter [1, 1, 1]; rw [← h335 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [← l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l9 y (x ◇ x)]

theorem Equation206_378_implies_Equation4 (G : Type*) [Magma G] (h206 : Equation206 G) (h378 : Equation378 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h378 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation124_323_implies_Equation5 (G : Type*) [Magma G] (h124 : Equation124 G) (h323 : Equation323 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h323 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation206_377_implies_Equation4 (G : Type*) [Magma G] (h206 : Equation206 G) (h377 : Equation377 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h377 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation124_333_implies_Equation5 (G : Type*) [Magma G] (h124 : Equation124 G) (h333 : Equation333 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h333 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation206_335_implies_Equation14 (G : Type*) [Magma G] (h206 : Equation206 G) (h335 : Equation335 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation3_206_335_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h335 : Equation335 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_206_335_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h335 : Equation335 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l1 y (x ◇ x)]

theorem Equation124_384_implies_Equation14 (G : Type*) [Magma G] (h124 : Equation124 G) (h384 : Equation384 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation3_124_384_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h124 : Equation124 G) (h384 : Equation384 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_124_384_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h124 : Equation124 G) (h384 : Equation384 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l0 y (x ◇ x)]

theorem Equation206_333_375_implies_Equation2 (G : Type*) [Magma G] (h206 : Equation206 G) (h333 : Equation333 G) (h375 : Equation375 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h333 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 ((X0 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ ((X0 ◇ X0) ◇ X1)) X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation124_326_377_implies_Equation2 (G : Type*) [Magma G] (h124 : Equation124 G) (h326 : Equation326 G) (h377 : Equation377 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h377 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h124 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h326 (X1 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ (X0 ◇ X0)) ◇ X0)]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_206_273_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h273 : Equation273 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h206 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_206_273_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h273 : Equation273 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h206 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_206_273_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h273 : Equation273 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h206 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation3_206_273_implies_Equation335 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h273 : Equation273 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = ((((X1 ◇ X0) ◇ X1) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h206 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h273 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h206 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation3_53_124_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h124 : Equation124 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h53 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_53_124_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h124 : Equation124 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h53 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_53_124_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h124 : Equation124 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h53 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation3_53_124_implies_Equation335 (G : Type*) [Magma G] (h3 : Equation3 G) (h53 : Equation53 G) (h124 : Equation124 G) : Equation335 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 1]; rw [← h53 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [l3 X0 (X1 ◇ X0)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l5 X1 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1, 1]; rw [← h124 X0 X1]
  intro x y
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1]; rw [l4 y x]

theorem Equation206_271_implies_Equation63 (G : Type*) [Magma G] (h206 : Equation206 G) (h271 : Equation271 G) : Equation63 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h206 X0 X1]
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [l1 (X0 ◇ (X0 ◇ X1)) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ (X1 ◇ X0)) ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← l4 X1 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h206 X1 (X1 ◇ (X1 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation206_271_implies_Equation124 (G : Type*) [Magma G] (h206 : Equation206 G) (h271 : Equation271 G) : Equation124 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X1 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h271 X0 X1]
    conv => enter [1]; rw [← h271 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h206 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h206 X0 X1]
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X1 ◇ X0) ((X0 ◇ X1) ◇ X1)]
    conv => enter [1, 1]; rw [l0 X1 X0]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 1]; rw [l2 X1 X0]
    conv => enter [1, 2, 2]; rw [l2 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X0)) (X1 ◇ X0)]
    conv => enter [1, 2, 1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l5 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 1]; rw [l7 X1 (X1 ◇ X0)]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 1]; rw [l8 (X1 ◇ X0) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1, 1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ (X1 ◇ X0)) ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l11 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← l11 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← l13 X1 (X1 ◇ X0)]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 1]; rw [l15 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l15 X1 X0]
    conv => enter [1]; rw [← h206 X1 (X1 ◇ (X1 ◇ X0))]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [l17 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 y x]
  conv => enter [1, 2]; rw [l18 x (y ◇ x)]

theorem Equation206_271_implies_Equation65 (G : Type*) [Magma G] (h206 : Equation206 G) (h271 : Equation271 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h271 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h206 X0 X1]
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X1)) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ (X1 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ (X1 ◇ X0)) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation63_124_implies_Equation271 (G : Type*) [Magma G] (h63 : Equation63 G) (h124 : Equation124 G) : Equation271 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h124 X0 X1]
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [l1 X1 ((X1 ◇ X0) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l2 X1 X0]
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X1 ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← l3 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X1]
  have l6 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h124 X1 ((X0 ◇ X1) ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l7 y x]

theorem Equation63_124_implies_Equation206 (G : Type*) [Magma G] (h63 : Equation63 G) (h124 : Equation124 G) : Equation206 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h124 X0 X1]
  have l2 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h63 X1 ((X1 ◇ X0) ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X1 ◇ X0) ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h124 X0 X1]
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X1 ◇ X0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1, 1, 1]; rw [l0 X1 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 ((X0 ◇ X1) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1, 1, 1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 ((X0 ◇ X1) ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 2]; rw [l2 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← l5 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [l7 (X0 ◇ X1) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [l8 X1 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l3 X1 X0]
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ ((X0 ◇ X1) ◇ X1)) X1]
  have l12 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [← l11 X1 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← l13 (X0 ◇ X1) X1]
  have l15 : ∀ X1 X0 : G, ((((X1 ◇ X0) ◇ X0) ◇ X0) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l14 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 2]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l15 X0 X1]
    conv => enter [1]; rw [← h124 X1 ((X0 ◇ X1) ◇ X1)]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 1]; rw [l17 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 x y]
  conv => enter [1, 1]; rw [l18 (x ◇ y) x]

theorem Equation206_270_implies_Equation2 (G : Type*) [Magma G] (h206 : Equation206 G) (h270 : Equation270 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [← h270 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X1)) X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h206 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation48_124_implies_Equation2 (G : Type*) [Magma G] (h48 : Equation48 G) (h124 : Equation124 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [← h48 X1 ((X1 ◇ X0) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [l0 X1 ((X1 ◇ X0) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h124 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation3_206_263_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h263 : Equation263 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h206 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h206 X0 X1]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h3 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation3_55_124_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h55 : Equation55 G) (h124 : Equation124 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h124 X0 X1]
    conv => enter [1]; rw [l2 X1 ((X1 ◇ X0) ◇ X0)]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h3 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation3_206_260_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h260 : Equation260 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h206 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 2]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h206 (X0 ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation3_49_124_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h49 : Equation49 G) (h124 : Equation124 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h124 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 1]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation206_228_implies_Equation2 (G : Type*) [Magma G] (h206 : Equation206 G) (h228 : Equation228 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h206 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation102_124_implies_Equation2 (G : Type*) [Magma G] (h102 : Equation102 G) (h124 : Equation124 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h124 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_206_221_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h221 : Equation221 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h206 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation3_206_221_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h221 : Equation221 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h206 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_206_221_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h221 : Equation221 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (((X1 ◇ (X0 ◇ X1)) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h206 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h221 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h221 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l2 y (x ◇ x)]

theorem Equation3_105_124_implies_Equation14 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h124 : Equation124 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation3_105_124_implies_Equation66 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h124 : Equation124 G) : Equation66 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]
  conv => enter [1, 2, 2]; rw [h3 y]

theorem Equation3_105_124_implies_Equation115 (G : Type*) [Magma G] (h3 : Equation3 G) (h105 : Equation105 G) (h124 : Equation124 G) : Equation115 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h124 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2, 1]; rw [← h105 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h105 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X1 ◇ X0) X1]
  intro x y
  conv => enter [1]; rw [h3 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation3_206_209_264_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h206 : Equation206 G) (h209 : Equation209 G) (h264 : Equation264 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 1]; rw [← h206 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h209 (X0 ◇ X1) X0]
    conv => enter [1, 1, 2]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [l0 (X0 ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation3_75_117_124_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h75 : Equation75 G) (h117 : Equation117 G) (h124 : Equation124 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h75 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h124 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h117 (X1 ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [l0 X1 (X1 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation205_385_implies_Equation5 (G : Type*) [Magma G] (h205 : Equation205 G) (h385 : Equation385 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h385 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation104_325_implies_Equation4 (G : Type*) [Magma G] (h104 : Equation104 G) (h325 : Equation325 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h325 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation3_205_384_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h205 : Equation205 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h205 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 2]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h205 X0 X1]
    conv => enter [1]; rw [← h384 X0 (X0 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h384 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h384 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h384 (X0 ◇ X1) X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l5 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l8 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l8 X0 X1]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h384 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l8 X0 X1]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation3_104_335_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h104 : Equation104 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h104 ((X1 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1]; rw [← h104 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 2]; rw [← h104 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X0) ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h104 X0 X1]
    conv => enter [1]; rw [← h335 ((X1 ◇ X0) ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h335 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h335 X1 X0]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ X0) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h335 X0 (X1 ◇ X0)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l8 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l5 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l8 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation205_377_implies_Equation9 (G : Type*) [Magma G] (h205 : Equation205 G) (h377 : Equation377 G) : Equation9 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h205 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation205_377_implies_Equation101 (G : Type*) [Magma G] (h205 : Equation205 G) (h377 : Equation377 G) : Equation101 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h377 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h205 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1, 2]; rw [h377 x y]

theorem Equation104_333_implies_Equation28 (G : Type*) [Magma G] (h104 : Equation104 G) (h333 : Equation333 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h333 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h104 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation104_333_implies_Equation208 (G : Type*) [Magma G] (h104 : Equation104 G) (h333 : Equation333 G) : Equation208 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h333 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h104 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 1]; rw [h333 y x]

theorem Equation205_335_implies_Equation2 (G : Type*) [Magma G] (h205 : Equation205 G) (h335 : Equation335 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h335 X1 X0]
    conv => enter [1]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h335 X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h335 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation104_384_implies_Equation2 (G : Type*) [Magma G] (h104 : Equation104 G) (h384 : Equation384 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h384 X0 X1]
    conv => enter [1]; rw [← h104 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h384 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X1]
    conv => enter [1, 1]; rw [← h384 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation205_333_implies_Equation28 (G : Type*) [Magma G] (h205 : Equation205 G) (h333 : Equation333 G) : Equation28 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X1)) ◇ X1) = X1 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h333 X0 X1]
    conv => enter [1]; rw [← h205 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h333 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation104_377_implies_Equation9 (G : Type*) [Magma G] (h104 : Equation104 G) (h377 : Equation377 G) : Equation9 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h377 X1 X0]
    conv => enter [1]; rw [← h104 X1 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h377 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation205_273_implies_Equation5 (G : Type*) [Magma G] (h205 : Equation205 G) (h273 : Equation273 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h273 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h205 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h205 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h273 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

end Order3
