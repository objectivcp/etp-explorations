import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

theorem Equation55_364_implies_Equation65 (G : Type*) [Magma G] (h55 : Equation55 G) (h364 : Equation364 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h364 X0 X1]
    conv => enter [1]; rw [← h55 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h364 (X1 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h55 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 ((X1 ◇ X0) ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ X0) (X1 ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
    conv => enter [1, 1, 2]; rw [← h55 X0 X1]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1, 1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l5 X2 (X0 ◇ X0)]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l5 X2 X0]
  have l8 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ (X0 ◇ X0))) = X0 := by
    intro X2 X0
    conv => enter [1]; rw [← l6 X2 X0 X2]
    conv => enter [1]; rw [l2 X2 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l8 X1 X0]
    conv => enter [1, 1, 2]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l10 X0 X1]
    conv => enter [1]; rw [l8 (X1 ◇ X0) X0]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l7 X1 (X1 ◇ (X0 ◇ X0)) X2]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [l8 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1, 2]; rw [← l12 X1 X0 (X1 ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l8 y x]
  conv => enter [1, 2]; rw [l14 y x]

theorem Equation263_280_307_implies_Equation5 (G : Type*) [Magma G] (h263 : Equation263 G) (h280 : Equation280 G) (h307 : Equation307 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h263 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h280 X0 X1]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h280 X0 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h263 X1 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation50_55_359_implies_Equation4 (G : Type*) [Magma G] (h50 : Equation50 G) (h55 : Equation55 G) (h359 : Equation359 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h50 X0 X1]
  have l1 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h55 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h50 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 ((X0 ◇ X0) ◇ X1)]
    conv => enter [1]; rw [← h55 X1 (X0 ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation263_264_implies_Equation256 (G : Type*) [Magma G] (h263 : Equation263 G) (h264 : Equation264 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [← h264 ((X0 ◇ X1) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X0 X2]
  intro x y
  conv => enter [1]; rw [← l2 x x y]

theorem Equation55_75_implies_Equation62 (G : Type*) [Magma G] (h55 : Equation55 G) (h75 : Equation75 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h75 X0 X1]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X2 X0]
  intro x y
  conv => enter [1]; rw [← l2 y x x]

theorem Equation261_323_implies_Equation256 (G : Type*) [Magma G] (h261 : Equation261 G) (h323 : Equation323 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h261 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h261 (X0 ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation65_378_implies_Equation62 (G : Type*) [Magma G] (h65 : Equation65 G) (h378 : Equation378 G) : Equation62 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h65 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h65 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation261_313_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h313 : Equation313 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [← h261 X1 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (((((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 ((X0 ◇ X0) ◇ X1) X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h261 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l5 X1 X2]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [← h261 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l9 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l6 X0 X0 X2]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l7 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l9 (X1 ◇ X0) (X1 ◇ X1)]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation65_365_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h365 : Equation365 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [← h65 X1 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h65 X1 (X1 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ (X0 ◇ X0))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h65 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X0)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l5 X2 X1]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l5 X0 X0]
    conv => enter [1]; rw [← h65 X0 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l9 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l8 X0 X2]
    conv => enter [1]; rw [l6 X2 X0 X2]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l7 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l9 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation261_312_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h312 : Equation312 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 ((X1 ◇ (X0 ◇ X0)) ◇ X1)]
    conv => enter [1]; rw [← h261 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation65_360_implies_Equation2 (G : Type*) [Magma G] (h65 : Equation65 G) (h360 : Equation360 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X1 ◇ ((X0 ◇ X0) ◇ X1))]
    conv => enter [1]; rw [← h65 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation261_310_implies_Equation256 (G : Type*) [Magma G] (h261 : Equation261 G) (h310 : Equation310 G) : Equation256 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X0) X1]
    conv => enter [1, 2]; rw [← h261 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

theorem Equation65_367_implies_Equation62 (G : Type*) [Magma G] (h65 : Equation65 G) (h367 : Equation367 G) : Equation62 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h367 X2 X0]
    conv => enter [1, 1]; rw [h367 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1 (X0 ◇ ((X1 ◇ X1) ◇ X0))]
    conv => enter [1, 1]; rw [← h65 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x]

theorem Equation261_309_implies_Equation256 (G : Type*) [Magma G] (h261 : Equation261 G) (h309 : Equation309 G) : Equation256 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h261 X0 X1]
    conv => enter [1]; rw [← h309 X1 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X0) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X0) X2 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x x y]

theorem Equation65_361_implies_Equation62 (G : Type*) [Magma G] (h65 : Equation65 G) (h361 : Equation361 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h65 X0 X1]
    conv => enter [1]; rw [← h361 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l0 X2 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x x]

theorem Equation261_283_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h283 : Equation283 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h261 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h283 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X1) = ((X0 ◇ ((X1 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h261 ((X1 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h283 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X1 ◇ X1)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1]
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 1, 2]; rw [← l0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1]
    conv => enter [1]; rw [← h283 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [l3 X0 X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l4 X1]
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l4 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l4 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation56_65_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h65 : Equation65 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h65 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h56 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h56 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1]
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2, 1]; rw [← l0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1]
    conv => enter [1]; rw [← h56 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [l3 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l4 X1]
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l4 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation261_280_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h280 : Equation280 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h261 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h280 (X0 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = ((X0 ◇ ((X1 ◇ X1) ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h261 ((X1 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h280 X0 X1]
  have l3 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← h261 X0 ((X0 ◇ X0) ◇ X0)]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h261 X1 ((X0 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ (X0 ◇ X2)) = X2 := by
    intro X0 X2
    conv => enter [1, 2, 1]; rw [← l4 X0 X0]
    conv => enter [1, 1, 1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l4 ((X0 ◇ X0) ◇ X0) X2]
  have l7 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l5 (X0 ◇ X2)]
    conv => enter [1]; rw [l6 X0 X2]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 ((X1 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [← h261 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation50_65_implies_Equation2 (G : Type*) [Magma G] (h50 : Equation50 G) (h65 : Equation65 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h65 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h65 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h50 X0 X1]
  have l3 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 X0]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h65 X1 (X1 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← l1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X2 X0 : G, ((X2 ◇ X0) ◇ (X2 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1, 1, 2]; rw [← l4 X0 X2]
    conv => enter [1, 2, 2]; rw [← l4 X0 X2]
    conv => enter [1]; rw [l4 X2 (X0 ◇ (X2 ◇ X2))]
  have l7 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [← l5 (X2 ◇ X0)]
    conv => enter [1]; rw [l6 X2 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h65 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation261_273_implies_Equation2 (G : Type*) [Magma G] (h261 : Equation261 G) (h273 : Equation273 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h273 X0 X1]
    conv => enter [1]; rw [← h261 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation53_65_implies_Equation2 (G : Type*) [Magma G] (h53 : Equation53 G) (h65 : Equation65 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h65 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation261_264_implies_Equation256 (G : Type*) [Magma G] (h261 : Equation261 G) (h264 : Equation264 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h264 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X1) ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [l0 (X0 ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h264 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h261 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation65_75_implies_Equation62 (G : Type*) [Magma G] (h65 : Equation65 G) (h75 : Equation75 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h75 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h75 X0 X1]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h65 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation261_263_implies_Equation258 (G : Type*) [Magma G] (h261 : Equation261 G) (h263 : Equation263 G) : Equation258 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ ((X0 ◇ X1) ◇ X1)) X0]
    conv => enter [1, 1, 2, 1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ ((X0 ◇ X1) ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l6 X0 X2]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h261 X0 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation261_263_implies_Equation308 (G : Type*) [Magma G] (h261 : Equation261 G) (h263 : Equation263 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X1) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h263 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ (((X0 ◇ X1) ◇ X1) ◇ X0)) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ ((X0 ◇ X1) ◇ X1)) X0]
    conv => enter [1, 1, 2, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ ((X0 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h261 X0 ((X0 ◇ X1) ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 (X0 ◇ ((X0 ◇ X1) ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [← l0 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [h263 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h263 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l9 X0 X2]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 2, 1]; rw [← h261 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 ((X0 ◇ X1) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h261 X0 X1]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [l11 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h263 X0 X1]
    conv => enter [1]; rw [l10 ((X0 ◇ X1) ◇ X1) X0 X2]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X1) ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2, 1]; rw [← l1 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [l11 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l17 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X1) ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l18 X0 X1]
    conv => enter [1]; rw [l10 ((X0 ◇ X1) ◇ X1) (X0 ◇ X1) X2]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1 X0]
    conv => enter [1]; rw [← l19 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation55_65_implies_Equation72 (G : Type*) [Magma G] (h55 : Equation55 G) (h65 : Equation65 G) : Equation72 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ (X1 ◇ X0)) ◇ X0)]
    conv => enter [1, 2, 1, 2]; rw [← l0 X1 X0]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 ((X1 ◇ (X1 ◇ X0)) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h55 X0 X1]
  have l4 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← l2 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l6 X0 X2]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h65 X0 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation55_65_implies_Equation364 (G : Type*) [Magma G] (h55 : Equation55 G) (h65 : Equation65 G) : Equation364 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h55 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h55 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [l0 X0 ((X1 ◇ (X1 ◇ X0)) ◇ X0)]
    conv => enter [1, 2, 1, 2]; rw [← l0 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h65 X0 (X1 ◇ (X1 ◇ X0))]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h65 ((X1 ◇ (X1 ◇ X0)) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
  have l5 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h55 X0 X1]
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h55 X0 X1]
  have l6 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← l4 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l9 X0 X2]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 1, 2]; rw [← h65 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h65 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [l11 X0 X1]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h55 X0 X1]
    conv => enter [1]; rw [l10 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l7 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 1, 2]; rw [← l1 X0 X1]
  have l16 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 1]; rw [l11 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← l16 X1 X0]
  have l18 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l17 (X1 ◇ X0) X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l19 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l18 X1 X0]
    conv => enter [1]; rw [l10 (X1 ◇ X0) (X1 ◇ (X1 ◇ X0)) X2]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0 X1]
    conv => enter [1]; rw [← l19 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation260_325_implies_Equation256 (G : Type*) [Magma G] (h260 : Equation260 G) (h325 : Equation325 G) : Equation256 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h325 X0 ((X0 ◇ X1) ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h325 X0 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h260 X0 X1]
    conv => enter [1]; rw [← l3 ((X0 ◇ X1) ◇ X0) X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 2]; rw [← h260 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l6 X0 ((X0 ◇ X1) ◇ X0)]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h325 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [← h325 X0 (X0 ◇ X1)]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l14 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← l10 X0 X1]
  have l17 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l6 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l19 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  have l20 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l19 X0 X1]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ X1) X0]
  have l22 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l23 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l20 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l21 X0 X1]
  have l25 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 1]; rw [← l24 X0 X1]
  have l26 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l23 X0 X1]
  have l27 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l23 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [l6 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1, 1, 1]; rw [← l16 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l29 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l26 X0 X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1, 1]; rw [l29 X0 X1]
  have l31 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l25 X0 X1]
    conv => enter [1]; rw [l29 X0 X1]
  have l32 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ X0)]
  have l33 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h325 X0 X0]
    conv => enter [1]; rw [← l32 X0 X1]
  have l34 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l33 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l31 X0 X0]
  intro x y
  conv => enter [1]; rw [← l34 x y]

theorem Equation49_385_implies_Equation62 (G : Type*) [Magma G] (h49 : Equation49 G) (h385 : Equation385 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h385 (X0 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h385 (X1 ◇ X0) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h49 X0 X1]
    conv => enter [1]; rw [← l3 (X0 ◇ (X1 ◇ X0)) X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 1]; rw [← h49 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = (((X0 ◇ (X1 ◇ X0)) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l6 X0 (X0 ◇ (X1 ◇ X0))]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ X0) ◇ X0)) = (((X1 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h385 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 1]; rw [← h385 (X1 ◇ X0) X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [← l3 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1]; rw [← l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← l10 X1 X0]
  have l17 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l6 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (((X0 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l19 X1 X0]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l3 (X1 ◇ X0) X0]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 1]; rw [← l16 X0 X1]
  have l23 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l20 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l21 X0 X1]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 2]; rw [← l24 X0 X1]
  have l26 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l23 X1 X0]
  have l27 : ∀ X1 X0 : G, (X1 ◇ X0) = (((X1 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l23 X0 (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l28 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0]
    conv => enter [1, 2, 2]; rw [← l16 X0 X1]
    conv => enter [1, 1]; rw [← l16 X0 X1]
  have l29 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [l26 X1 X0]
  have l30 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1, 2]; rw [l29 X1 X0]
  have l31 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l25 X1 X0]
    conv => enter [1]; rw [l29 X1 X0]
  have l32 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l30 X1 X0]
    conv => enter [1]; rw [← h385 (X0 ◇ X0) X0]
  have l33 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 X0]
    conv => enter [1]; rw [← l32 X1 X0]
  have l34 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l33 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l31 X0 X0]
  intro x y
  conv => enter [1]; rw [← l34 y x]

theorem Equation260_313_implies_Equation2 (G : Type*) [Magma G] (h260 : Equation260 G) (h313 : Equation313 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [h313 X1 X1]
    conv => enter [1, 2]; rw [h313 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h313 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 X2 : G, (((X0 ◇ (X1 ◇ X0)) ◇ X2) ◇ X2) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 1, 1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X1 ◇ X1) ◇ X0) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h313 ((X1 ◇ X1) ◇ X0) X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h313 (X0 ◇ X0) X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X1)) = ((X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 X1 X2 (X1 ◇ (X2 ◇ X1))]
    conv => enter [1, 1]; rw [h313 (X1 ◇ (X2 ◇ X1)) X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (((X1 ◇ (X2 ◇ X1)) ◇ X0) ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l4 X1 X2 X0]
    conv => enter [1]; rw [← h313 ((X1 ◇ (X2 ◇ X1)) ◇ X0) X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h313 X1 X0]
    conv => enter [1]; rw [l7 X1 X2]
    conv => enter [1, 2, 1]; rw [h313 X1 X0]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1]; rw [← l7 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 X2 : G, (X1 ◇ (X2 ◇ X1)) = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X1 X2
    conv => enter [1]; rw [l9 X1 X2 X1]
    conv => enter [1, 1]; rw [← l11 X1 X2 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← l13 (X1 ◇ X0) X0]
  have l16 : ∀ X1 X2 : G, (X1 ◇ X1) = (X1 ◇ (X2 ◇ X1)) := by
    intro X1 X2
    conv => enter [1]; rw [l15 X1 (X2 ◇ X1)]
    conv => enter [1]; rw [← l14 X1 X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X1 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [← l15 (X1 ◇ (X2 ◇ X1)) X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1 X0]
    conv => enter [1]; rw [← l15 X1 (X0 ◇ X1)]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← l16 X0 (X0 ◇ X1)]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1, 1]; rw [← l20 X0 X1]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [← l15 (X0 ◇ X1) X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← l22 X0 X1]
  have l24 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l23 X0 X0]
    conv => enter [1]; rw [← h260 X0 X0]
  have l25 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l23 X0 X0]
    conv => enter [1]; rw [l24 X0]
  have l26 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l25 X0]
    conv => enter [1]; rw [← l19 X0 X1]
    conv => enter [1]; rw [l25 X0]
  have l27 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1]; rw [l26 X0 X0]
  have l28 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l26 X0 X0]
    conv => enter [1]; rw [l27 X0 X1]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation49_365_implies_Equation2 (G : Type*) [Magma G] (h49 : Equation49 G) (h365 : Equation365 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [h365 X1 X1]
    conv => enter [1, 1]; rw [h365 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h365 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X1 ◇ X0)]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l3 X2 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h365 (X0 ◇ (X1 ◇ X1)) X0]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X0]
    conv => enter [1]; rw [h365 (X0 ◇ X0) X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X1) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l9 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 ((X1 ◇ X2) ◇ X1) X1 X2]
    conv => enter [1, 2]; rw [h365 ((X1 ◇ X2) ◇ X1) X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((X0 ◇ ((X1 ◇ X2) ◇ X1)) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l4 X0 X1 X2]
    conv => enter [1]; rw [← h365 (X0 ◇ ((X1 ◇ X2) ◇ X1)) X0]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X2 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h365 X1 X0]
    conv => enter [1]; rw [l7 X1 X2]
    conv => enter [1, 1, 2]; rw [h365 X1 X0]
  have l12 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 (X1 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ X1 X2 : G, ((X1 ◇ X2) ◇ X1) = (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) := by
    intro X1 X2
    conv => enter [1]; rw [l9 X1 X2 X1]
    conv => enter [1, 2]; rw [← l11 X1 X2 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← l13 (X0 ◇ X1) X0]
  have l16 : ∀ X1 X2 : G, (X1 ◇ X1) = ((X1 ◇ X2) ◇ X1) := by
    intro X1 X2
    conv => enter [1]; rw [l15 X1 (X1 ◇ X2)]
    conv => enter [1]; rw [← l14 X1 X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (((X1 ◇ X2) ◇ X1) ◇ ((X1 ◇ X2) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [← l15 ((X1 ◇ X2) ◇ X1) X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1 X0]
    conv => enter [1]; rw [← l15 X1 (X1 ◇ X0)]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← l16 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 (X1 ◇ X0)]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← l20 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [← l15 (X1 ◇ X0) X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← l22 X0 X1]
  have l24 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l23 X0 X0]
    conv => enter [1]; rw [← h49 X0 X0]
  have l25 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l23 X0 X0]
    conv => enter [1]; rw [l24 X0]
  have l26 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l25 X0]
    conv => enter [1]; rw [← l19 X0 X1]
    conv => enter [1]; rw [l25 X0]
  have l27 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1]; rw [l26 X0 X0]
  have l28 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l26 X0 X0]
    conv => enter [1]; rw [l27 X0 X1]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation260_312_implies_Equation280 (G : Type*) [Magma G] (h260 : Equation260 G) (h312 : Equation312 G) : Equation280 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h312 X0 X1]
    conv => enter [1]; rw [← h260 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation49_360_implies_Equation50 (G : Type*) [Magma G] (h49 : Equation49 G) (h360 : Equation360 G) : Equation50 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h360 X0 X1]
    conv => enter [1]; rw [← h49 X1 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation260_309_326_implies_Equation257 (G : Type*) [Magma G] (h260 : Equation260 G) (h309 : Equation309 G) (h326 : Equation326 G) : Equation257 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h309 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h326 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X0 ◇ X1)) = ((X1 ◇ X1) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [← l4 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h326 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h260 X0 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation260_309_326_implies_Equation263 (G : Type*) [Magma G] (h260 : Equation260 G) (h309 : Equation309 G) (h326 : Equation326 G) : Equation263 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h309 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h326 (X1 ◇ X0) X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
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
    conv => enter [1]; rw [l4 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l8 X0 X2]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0]
    conv => enter [1, 2]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [l9 ((X0 ◇ X1) ◇ X0) X0 X2]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((((X0 ◇ X1) ◇ X0) ◇ (X0 ◇ X2)) ◇ (X0 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h260 (X0 ◇ X2) X0]
    conv => enter [1, 1, 1]; rw [l9 X0 X2 X1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [← l10 (((X0 ◇ X1) ◇ X0) ◇ X2) X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h309 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l13 X0 X1 X2]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l9 (X0 ◇ X1) X0 X2]
  have l16 : ∀ X0 X2 X1 : G, (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = (((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ ((X0 ◇ X2) ◇ X0)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 ((X0 ◇ X2) ◇ X0) (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l12 X0 X1 X2]
  have l17 : ∀ X0 X2 X1 : G, (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = (((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1]; rw [← l10 ((X0 ◇ X1) ◇ (((X0 ◇ X2) ◇ X0) ◇ (X0 ◇ X1))) X0 X2]
  have l18 : ∀ X0 X2 X1 : G, (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) = (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l17 X0 X2 X1]
    conv => enter [1, 1]; rw [← h309 (X0 ◇ X1) ((X0 ◇ X2) ◇ X0)]
  have l19 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ ((X0 ◇ X2) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← l18 X0 X2 X1]
  have l20 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = (((X0 ◇ X2) ◇ X0) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1]; rw [← l10 ((X0 ◇ X2) ◇ X0) X0 X2]
  have l21 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1 X0]
    conv => enter [1]; rw [← h260 X0 X0]
  intro x y
  conv => enter [1]; rw [← l21 x y]

theorem Equation49_361_375_implies_Equation52 (G : Type*) [Magma G] (h49 : Equation49 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h361 X0 (X1 ◇ X0)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X1)) = ((X1 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h361 (X1 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h375 X1 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h375 X1 (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l4 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h375 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h49 X0 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation49_361_375_implies_Equation55 (G : Type*) [Magma G] (h49 : Equation49 G) (h361 : Equation361 G) (h375 : Equation375 G) : Equation55 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h361 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h375 X0 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
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
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [l8 X0 X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2]
    conv => enter [1, 1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [l9 (X0 ◇ (X1 ◇ X0)) X0 X2]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h49 (X2 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [l9 X0 X2 X1]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [← l10 X0 (X2 ◇ (X0 ◇ (X1 ◇ X0))) X1]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h361 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1 X2]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [l9 (X1 ◇ X0) X0 X2]
  have l16 : ∀ X0 X2 X1 : G, ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 (X0 ◇ (X2 ◇ X0)) (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l12 X1 X0 X2]
  have l17 : ∀ X0 X2 X1 : G, ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1]; rw [← l10 X0 (((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) ◇ (X1 ◇ X0)) X2]
  have l18 : ∀ X0 X2 X1 : G, ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l17 X0 X2 X1]
    conv => enter [1, 2]; rw [← h361 (X1 ◇ X0) (X0 ◇ (X2 ◇ X0))]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = ((X0 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← l18 X0 X2 X1]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1]; rw [← l10 X0 (X0 ◇ (X2 ◇ X0)) X2]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1 X0]
    conv => enter [1]; rw [← h49 X0 X0]
  intro x y
  conv => enter [1]; rw [← l21 x y]

theorem Equation260_308_326_implies_Equation256 (G : Type*) [Magma G] (h260 : Equation260 G) (h308 : Equation308 G) (h326 : Equation326 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h308 ((X0 ◇ X1) ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h260 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ (((X0 ◇ X0) ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← h326 ((X0 ◇ X0) ◇ X1) X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X2) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l2 X0 X2]
    conv => enter [1]; rw [← h326 X1 ((X0 ◇ X2) ◇ X0)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← l4 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X0) X0 X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1]; rw [← l6 (X0 ◇ X0) X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h308 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← l6 X0 X1]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 (X0 ◇ X1) X0 X0]
    conv => enter [1]; rw [← l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h326 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X1) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l9 ((X0 ◇ X0) ◇ X1) X0]
  have l12 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l9 X0 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← h260 X0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 1]; rw [← l14 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [← h308 (X0 ◇ X0) X1]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X0]
    conv => enter [1]; rw [← l17 X0 X1]
  have l19 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h326 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l18 (X0 ◇ X0) X1]
  have l20 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l9 X0 X0]
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 X0]
  have l21 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l20 X0 X1]
    conv => enter [1]; rw [← h260 X0 X0]
  intro x y
  conv => enter [1]; rw [← l21 x y]

theorem Equation49_364_375_implies_Equation62 (G : Type*) [Magma G] (h49 : Equation49 G) (h364 : Equation364 G) (h375 : Equation375 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h364 (X0 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h49 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← h375 X0 (X1 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ (X2 ◇ X0)) ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l2 X0 X2]
    conv => enter [1]; rw [← h375 (X0 ◇ (X2 ◇ X0)) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← l4 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l6 (X0 ◇ X0) X1]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h364 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [← l6 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l8 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h375 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l9 (X1 ◇ (X0 ◇ X0)) X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l9 X0 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← h49 X0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2]; rw [l13 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h49 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l13 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1, 2]; rw [← l14 X0 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← h364 (X0 ◇ X0) X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X0]
    conv => enter [1]; rw [← l17 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l18 (X0 ◇ X0) X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l9 X0 X0]
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l9 X0 X0]
  have l21 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l20 X0 X1]
    conv => enter [1]; rw [← h49 X0 X0]
  intro x y
  conv => enter [1]; rw [← l21 y x]

theorem Equation260_283_implies_Equation5 (G : Type*) [Magma G] (h260 : Equation260 G) (h283 : Equation283 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h260 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h283 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [← l2 X1 X1]
    conv => enter [1]; rw [← h283 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation49_56_implies_Equation4 (G : Type*) [Magma G] (h49 : Equation49 G) (h56 : Equation56 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h49 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h56 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X1]
    conv => enter [1]; rw [← h56 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation260_280_309_312_implies_Equation5 (G : Type*) [Magma G] (h260 : Equation260 G) (h280 : Equation280 G) (h309 : Equation309 G) (h312 : Equation312 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h260 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1, 1]; rw [← h260 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 1]; rw [← h309 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h309 X0 X1]
    conv => enter [1]; rw [← h309 (X1 ◇ X0) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h312 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = (((X0 ◇ X1) ◇ X0) ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h280 ((X0 ◇ X1) ◇ X0) X0]
    conv => enter [1, 1]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l5 X0 X0]
    conv => enter [1]; rw [← h260 X0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0]
    conv => enter [1]; rw [← h312 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l8 y x]

theorem Equation49_50_360_361_implies_Equation4 (G : Type*) [Magma G] (h49 : Equation49 G) (h50 : Equation50 G) (h360 : Equation360 G) (h361 : Equation361 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h49 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h49 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h361 X0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h361 X0 X1]
    conv => enter [1]; rw [← h361 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h360 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h50 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l4 X0 X1]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l5 X0 X0]
    conv => enter [1]; rw [← h49 X0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h360 X0 X1]
    conv => enter [1]; rw [l7 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

theorem Equation260_274_implies_Equation2 (G : Type*) [Magma G] (h260 : Equation260 G) (h274 : Equation274 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h274 X0 X1]
    conv => enter [1]; rw [← h260 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation49_73_implies_Equation2 (G : Type*) [Magma G] (h49 : Equation49 G) (h73 : Equation73 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h73 X0 X1]
    conv => enter [1]; rw [← h49 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation260_273_implies_Equation3 (G : Type*) [Magma G] (h260 : Equation260 G) (h273 : Equation273 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X0)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h273 X0 ((X0 ◇ X1) ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h260 X0 ((X0 ◇ X0) ◇ X0)]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation49_53_implies_Equation3 (G : Type*) [Magma G] (h49 : Equation49 G) (h53 : Equation53 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h49 X0 (X0 ◇ (X0 ◇ X0))]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation260_264_implies_Equation256 (G : Type*) [Magma G] (h260 : Equation260 G) (h264 : Equation264 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h260 X0 X1]
    conv => enter [1]; rw [← h264 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X2 X1]
    conv => enter [1]; rw [← h264 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x x y]

theorem Equation49_75_implies_Equation62 (G : Type*) [Magma G] (h49 : Equation49 G) (h75 : Equation75 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h49 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l0 X0 X2]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l1 X2 (X1 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h75 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x x]

theorem Equation260_263_implies_Equation323 (G : Type*) [Magma G] (h260 : Equation260 G) (h263 : Equation263 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h260 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation49_55_implies_Equation378 (G : Type*) [Magma G] (h49 : Equation49 G) (h55 : Equation55 G) : Equation378 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h49 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation258_263_323_implies_Equation256 (G : Type*) [Magma G] (h258 : Equation258 G) (h263 : Equation263 G) (h323 : Equation323 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h323 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h258 X0 ((X0 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h258 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 X2 : G, (((X0 ◇ X0) ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x x y]

theorem Equation55_72_378_implies_Equation62 (G : Type*) [Magma G] (h55 : Equation55 G) (h72 : Equation72 G) (h378 : Equation378 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h55 X0 (X1 ◇ X0)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h378 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h72 X0 (X1 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h72 (X1 ◇ X0) X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x x]

theorem Equation258_263_310_implies_Equation256 (G : Type*) [Magma G] (h258 : Equation258 G) (h263 : Equation263 G) (h310 : Equation310 G) : Equation256 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h310 X2 X0]
    conv => enter [1, 2]; rw [h310 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [← h258 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 ((X0 ◇ X0) ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [← h258 X0 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l2 (X0 ◇ X1) ((X0 ◇ X0) ◇ X1)]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h258 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation55_72_367_implies_Equation62 (G : Type*) [Magma G] (h55 : Equation55 G) (h72 : Equation72 G) (h367 : Equation367 G) : Equation62 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ X2) = (((X1 ◇ X1) ◇ X0) ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h367 X2 X0]
    conv => enter [1, 1]; rw [h367 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h72 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1 ((X1 ◇ X1) ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← h72 X0 (X1 ◇ X1)]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l2 (X1 ◇ X0) (X1 ◇ (X0 ◇ X0))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h72 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X0]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [← l5 y x]

theorem Equation258_263_309_implies_Equation256 (G : Type*) [Magma G] (h258 : Equation258 G) (h263 : Equation263 G) (h309 : Equation309 G) : Equation256 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h258 X0 X1]
    conv => enter [1]; rw [← h309 X1 ((X0 ◇ X0) ◇ X1)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l0 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X2) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 ((X0 ◇ X1) ◇ X1) X2 X0]
    conv => enter [1]; rw [← h263 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x x y]

theorem Equation55_72_361_implies_Equation62 (G : Type*) [Magma G] (h55 : Equation55 G) (h72 : Equation72 G) (h361 : Equation361 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h72 X0 X1]
    conv => enter [1]; rw [← h361 X1 (X1 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← l0 X2 X0]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l1 X2 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [← h55 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 y x x]

theorem Equation258_283_implies_Equation2 (G : Type*) [Magma G] (h258 : Equation258 G) (h283 : Equation283 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h258 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h283 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h258 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h283 ((X0 ◇ X0) ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1]; rw [← h283 X1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation56_72_implies_Equation2 (G : Type*) [Magma G] (h56 : Equation56 G) (h72 : Equation72 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h72 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h56 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h72 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h56 (X0 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h56 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation257_326_implies_Equation260 (G : Type*) [Magma G] (h257 : Equation257 G) (h326 : Equation326 G) : Equation260 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h326 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h257 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l1 ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 1, 1]; rw [l1 ((X0 ◇ X0) ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1, 1]; rw [← h257 X0 X0]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h257 X0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation257_326_implies_Equation323 (G : Type*) [Magma G] (h257 : Equation257 G) (h326 : Equation326 G) : Equation323 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h257 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h326 (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 1, 1]; rw [← h326 (X0 ◇ X0) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h326 X1 X0]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h257 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l3 ((((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = (((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1, 1]; rw [l3 ((X0 ◇ X0) ◇ X0) X0]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 1, 1]; rw [← h257 X0 X0]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = ((X0 ◇ X2) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l6 X0 X2]
  have l8 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h257 X0 X0]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X2 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l3 X2 X0]
    conv => enter [1, 2]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X0) ◇ X2) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X2]
    conv => enter [1, 1, 1]; rw [l6 X0 X1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [l7 (X0 ◇ X1) X0 X2]
  have l12 : ∀ X0 X1 X2 X3 : G, ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = ((((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) X0 X3]
    conv => enter [1, 1, 1, 1]; rw [← l11 X0 X1 X2]
    conv => enter [1, 1, 2]; rw [← l11 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 X3 : G, ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = ((((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1]; rw [← l9 (((X0 ◇ X0) ◇ X3) ◇ (X0 ◇ X0)) (X0 ◇ X1) X2]
  have l14 : ∀ X0 X1 X2 X3 : G, ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) = ((((X0 ◇ X0) ◇ X3) ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
    conv => enter [1, 1]; rw [← h326 ((X0 ◇ X0) ◇ X3) X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h257 X0 X0]
    conv => enter [1]; rw [← l14 X0 X1 X2 X0]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1]; rw [← l9 (((X0 ◇ X1) ◇ X2) ◇ (X0 ◇ X1)) (X0 ◇ X1) X2]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l16 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation52_375_implies_Equation49 (G : Type*) [Magma G] (h52 : Equation52 G) (h375 : Equation375 G) : Equation49 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h52 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l1 X0 (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X0 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2, 2]; rw [← h52 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1]; rw [← h52 X0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation52_375_implies_Equation378 (G : Type*) [Magma G] (h52 : Equation52 G) (h375 : Equation375 G) : Equation378 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h52 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h375 X0 (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h375 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h375 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h52 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l3 X0 (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2, 2]; rw [l3 X0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2]; rw [← h52 X0 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l6 X0 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h52 X0 X0]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l3 X0 X2]
    conv => enter [1, 1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2]
    conv => enter [1, 2, 2]; rw [l6 X0 X1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 (X1 ◇ X0) X1]
    conv => enter [1, 2]; rw [l7 (X1 ◇ X0) X0 X2]
  have l12 : ∀ X1 X0 X2 X3 : G, (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) = (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l11 ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) X0 X3]
    conv => enter [1, 2, 2, 2]; rw [← l11 X0 X1 X2]
    conv => enter [1, 2, 1]; rw [← l11 X0 X1 X2]
  have l13 : ∀ X1 X0 X2 X3 : G, (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) = ((X1 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l12 X1 X0 X2 X3]
    conv => enter [1]; rw [← l9 (X1 ◇ X0) ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ X0))) X2]
  have l14 : ∀ X1 X0 X2 X3 : G, (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) = ((X1 ◇ X0) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l13 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h375 X0 (X3 ◇ (X0 ◇ X0))]
  have l15 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = (((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h52 X0 X1]
    conv => enter [1]; rw [← l14 X1 X0 X2 X1]
  have l16 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l15 X1 X0 X2]
    conv => enter [1]; rw [← l9 (X1 ◇ X0) ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) X2]
  have l17 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l8 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← l16 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation257_325_implies_Equation256 (G : Type*) [Magma G] (h257 : Equation257 G) (h325 : Equation325 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h257 X0 X1]
    conv => enter [1]; rw [← h325 X0 ((X0 ◇ X0) ◇ X1)]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h325 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h325 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h325 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 2]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h257 X0 X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h325 (X0 ◇ X0) ((X0 ◇ X0) ◇ X1)]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 (X0 ◇ X0) ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 2]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h257 X0 ((X0 ◇ X0) ◇ X1)]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [l7 X0 X0]
    conv => enter [1, 2]; rw [l7 X0 X0]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l7 X0 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1, 2]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X0) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0 X1]
    conv => enter [1]; rw [← h257 X0 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h325 X0 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 (X0 ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← l8 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 1]; rw [l9 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l7 X0 X0]
  intro x y
  conv => enter [1]; rw [← l16 x y]

theorem Equation52_385_implies_Equation62 (G : Type*) [Magma G] (h52 : Equation52 G) (h385 : Equation385 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h52 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X0 ◇ X1)]
    conv => enter [1, 1]; rw [← h385 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h385 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← l0 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h52 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 (X1 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h52 X0 (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [l7 X0 X0]
    conv => enter [1, 1]; rw [l7 X0 X0]
  have l9 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [← l7 X0 X0]
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l7 X0 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ (X1 ◇ X0)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X0]
    conv => enter [1, 1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X0 X1]
    conv => enter [1]; rw [← h52 X0 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← h385 (X1 ◇ X0) X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 (X1 ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l8 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1, 2]; rw [l9 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l15 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l7 X0 X0]
  intro x y
  conv => enter [1]; rw [← l16 y x]

theorem Equation257_313_implies_Equation2 (G : Type*) [Magma G] (h257 : Equation257 G) (h313 : Equation313 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h313 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h257 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h257 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h313 (X1 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X1 (X1 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X1 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation52_365_implies_Equation2 (G : Type*) [Magma G] (h52 : Equation52 G) (h365 : Equation365 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h365 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h52 X1 ((X1 ◇ X1) ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h52 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X1 ◇ X1) ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h365 (X1 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X1) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l1 X1 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation257_312_implies_Equation5 (G : Type*) [Magma G] (h257 : Equation257 G) (h312 : Equation312 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h312 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h257 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h257 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation52_360_implies_Equation4 (G : Type*) [Magma G] (h52 : Equation52 G) (h360 : Equation360 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h360 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h52 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h52 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation257_308_implies_Equation256 (G : Type*) [Magma G] (h257 : Equation257 G) (h308 : Equation308 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h257 X0 X1]
    conv => enter [1]; rw [← h308 ((X0 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h257 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ X1) X2]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 X3 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1, 2]; rw [l2 X0 X1 X0]
    conv => enter [1, 1]; rw [l2 X0 X1 X0]
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X3 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1 X0]
  have l4 : ∀ X0 X1 X3 : G, (((X0 ◇ X0) ◇ X1) ◇ X3) = X0 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l3 X0 X1 X3]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x x y]

theorem Equation52_364_implies_Equation62 (G : Type*) [Magma G] (h52 : Equation52 G) (h364 : Equation364 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h52 X0 X1]
    conv => enter [1]; rw [← h364 (X1 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h52 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l1 X2 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 X3 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = (X3 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X3
    conv => enter [1, 1]; rw [l2 X1 X0 X1]
    conv => enter [1, 2]; rw [l2 X1 X0 X1]
    conv => enter [1]; rw [← l2 X3 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X1 X0 X1]
  have l4 : ∀ X3 X1 X0 : G, (X3 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X3 X1 X0
    conv => enter [1]; rw [← l3 X1 X0 X3]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x x]

theorem Equation257_280_implies_Equation28 (G : Type*) [Magma G] (h257 : Equation257 G) (h280 : Equation280 G) : Equation28 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h257 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h280 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation257_280_implies_Equation25 (G : Type*) [Magma G] (h257 : Equation257 G) (h280 : Equation280 G) : Equation25 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h257 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h280 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation257_280_implies_Equation333 (G : Type*) [Magma G] (h257 : Equation257 G) (h280 : Equation280 G) : Equation333 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h257 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h280 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation257_280_implies_Equation156 (G : Type*) [Magma G] (h257 : Equation257 G) (h280 : Equation280 G) : Equation156 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h257 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h280 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 2]; rw [← l0 x]

theorem Equation257_280_implies_Equation221 (G : Type*) [Magma G] (h257 : Equation257 G) (h280 : Equation280 G) : Equation221 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h257 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h280 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 1]; rw [l3 x y]

theorem Equation257_280_implies_Equation361 (G : Type*) [Magma G] (h257 : Equation257 G) (h280 : Equation280 G) : Equation361 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h257 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h280 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l1 x y]

theorem Equation257_280_implies_Equation101 (G : Type*) [Magma G] (h257 : Equation257 G) (h280 : Equation280 G) : Equation101 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h257 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h280 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h280 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h257 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ X0) X0]
    conv => enter [1, 1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [l3 (x ◇ y) x]

theorem Equation50_52_implies_Equation9 (G : Type*) [Magma G] (h50 : Equation50 G) (h52 : Equation52 G) : Equation9 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h52 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h50 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation50_52_implies_Equation10 (G : Type*) [Magma G] (h50 : Equation50 G) (h52 : Equation52 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h52 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h50 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation50_52_implies_Equation377 (G : Type*) [Magma G] (h50 : Equation50 G) (h52 : Equation52 G) : Equation377 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h52 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h50 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation50_52_implies_Equation153 (G : Type*) [Magma G] (h50 : Equation50 G) (h52 : Equation52 G) : Equation153 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h52 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h50 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1, 1]; rw [← l0 x]

theorem Equation50_52_implies_Equation105 (G : Type*) [Magma G] (h50 : Equation50 G) (h52 : Equation52 G) : Equation105 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h52 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h50 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2]; rw [l3 y x]

theorem Equation50_52_implies_Equation309 (G : Type*) [Magma G] (h50 : Equation50 G) (h52 : Equation52 G) : Equation309 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h52 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h50 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l1 x y]

theorem Equation50_52_implies_Equation208 (G : Type*) [Magma G] (h50 : Equation50 G) (h52 : Equation52 G) : Equation208 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h52 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h50 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h52 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1]; rw [l3 x (y ◇ x)]

theorem Equation257_264_307_implies_Equation256 (G : Type*) [Magma G] (h257 : Equation257 G) (h264 : Equation264 G) (h307 : Equation307 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h257 X0 X1]
    conv => enter [1]; rw [← h264 ((X0 ◇ X0) ◇ X1) X0]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1, 1]; rw [h307 X0]
    conv => enter [1]; rw [← h264 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l0 X0 (X0 ◇ X0)]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

theorem Equation52_75_359_implies_Equation62 (G : Type*) [Magma G] (h52 : Equation52 G) (h75 : Equation75 G) (h359 : Equation359 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h52 X0 X1]
    conv => enter [1]; rw [← h75 (X1 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h359 X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l0 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l0 X0 (X0 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation257_263_310_323_implies_Equation266 (G : Type*) [Magma G] (h257 : Equation257 G) (h263 : Equation263 G) (h310 : Equation310 G) (h323 : Equation323 G) : Equation266 G := by
  have l0 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK3) ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [h263 ((sK2 ◇ sK3) ◇ sK3) sK2]
    conv => enter [1, 1, 1]; rw [← h263 sK2 sK3]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [h323 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X1)]
  have l2 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ sK3) = ((((sK2 ◇ sK3) ◇ sK4) ◇ ((sK2 ◇ sK3) ◇ sK4)) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [h263 (sK2 ◇ sK3) ((sK2 ◇ sK3) ◇ sK4)]
    conv => enter [1, 1, 1]; rw [← h323 (sK2 ◇ sK3) sK4]
  have l3 : ∀ sK2 sK3 sK4 : G, (((sK2 ◇ sK3) ◇ sK4) ◇ ((sK2 ◇ sK3) ◇ sK4)) = (((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) ◇ (((sK2 ◇ sK3) ◇ sK4) ◇ ((sK2 ◇ sK3) ◇ sK4))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [h263 (((sK2 ◇ sK3) ◇ sK4) ◇ ((sK2 ◇ sK3) ◇ sK4)) (sK2 ◇ sK3)]
    conv => enter [1, 1, 1]; rw [← l2 sK2 sK3 sK4]
  have l4 : ∀ sK2 sK3 sK4 : G, (((sK2 ◇ sK3) ◇ sK4) ◇ ((sK2 ◇ sK3) ◇ sK4)) = (((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l3 sK2 sK3 sK4]
    conv => enter [1]; rw [← h310 ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) ((sK2 ◇ sK3) ◇ sK4)]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X1) ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h310 (X0 ◇ X0) (X0 ◇ X1)]
    conv => enter [1]; rw [← l5 X0 X1]
  have l7 : ∀ sK2 sK3 : G, (sK2 ◇ sK2) = ((((sK2 ◇ sK3) ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ sK3)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [h263 (sK2 ◇ sK2) ((sK2 ◇ sK3) ◇ sK3)]
    conv => enter [1, 1, 1]; rw [← l0 sK2 sK3]
  have l8 : ∀ sK2 sK3 : G, (sK2 ◇ sK2) = ((((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l7 sK2 sK3]
    conv => enter [1, 1]; rw [← l6 (sK2 ◇ sK3) sK3]
  have l9 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ sK2) = ((((sK2 ◇ sK3) ◇ sK4) ◇ ((sK2 ◇ sK3) ◇ sK4)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [l8 sK2 sK3]
    conv => enter [1, 1]; rw [← l4 sK2 sK3 sK4]
  have l10 : ∀ sK2 sK3 sK4 : G, ((sK2 ◇ sK3) ◇ sK4) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK3) ◇ sK4)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [h257 ((sK2 ◇ sK3) ◇ sK4) (sK2 ◇ sK2)]
    conv => enter [1, 1]; rw [← l9 sK2 sK3 sK4]
  have l11 : ∀ sK2 sK3 sK4 : G, sK2 = (((sK2 ◇ sK3) ◇ sK4) ◇ sK2) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [h257 sK2 ((sK2 ◇ sK3) ◇ sK4)]
    conv => enter [1, 1]; rw [← l10 sK2 sK3 sK4]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation52_55_367_378_implies_Equation58 (G : Type*) [Magma G] (h52 : Equation52 G) (h55 : Equation55 G) (h367 : Equation367 G) (h378 : Equation378 G) : Equation58 G := by
  have l0 : ∀ sK3 sK2 : G, (sK3 ◇ (sK3 ◇ sK2)) = ((sK3 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK2
    conv => enter [1]; rw [h55 (sK3 ◇ (sK3 ◇ sK2)) sK2]
    conv => enter [1, 2, 2]; rw [← h55 sK2 sK3]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h378 X1 X0]
    conv => enter [1]; rw [← h55 X0 (X1 ◇ X0)]
  have l2 : ∀ sK3 sK2 sK4 : G, (sK3 ◇ sK2) = ((sK3 ◇ sK2) ◇ ((sK4 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 sK4
    conv => enter [1]; rw [h55 (sK3 ◇ sK2) (sK4 ◇ (sK3 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← h378 sK4 (sK3 ◇ sK2)]
  have l3 : ∀ sK4 sK3 sK2 : G, ((sK4 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK3 ◇ sK2))) = (((sK4 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK3 ◇ sK2))) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) := by
    intro sK4 sK3 sK2
    conv => enter [1]; rw [h55 ((sK4 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK3 ◇ sK2))) (sK3 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l2 sK3 sK2 sK4]
  have l4 : ∀ sK4 sK3 sK2 : G, ((sK4 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK3 ◇ sK2))) = (((sK3 ◇ sK2) ◇ (sK3 ◇ sK2)) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) := by
    intro sK4 sK3 sK2
    conv => enter [1]; rw [l3 sK4 sK3 sK2]
    conv => enter [1]; rw [← h367 ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2)) (sK4 ◇ (sK3 ◇ sK2))]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (((X1 ◇ X0) ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 ((X1 ◇ X0) ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [l1 X0 X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h367 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [← l5 X1 X0]
  have l7 : ∀ sK2 sK3 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3
    conv => enter [1]; rw [h55 (sK2 ◇ sK2) (sK3 ◇ (sK3 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l0 sK3 sK2]
  have l8 : ∀ sK2 sK3 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (((sK3 ◇ sK2) ◇ (sK3 ◇ sK2)) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l7 sK2 sK3]
    conv => enter [1, 2]; rw [← l6 (sK3 ◇ sK2) sK3]
  have l9 : ∀ sK2 sK4 sK3 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK4 ◇ (sK3 ◇ sK2)) ◇ (sK4 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK4 sK3
    conv => enter [1]; rw [l8 sK2 sK3]
    conv => enter [1, 2]; rw [← l4 sK4 sK3 sK2]
  have l10 : ∀ sK4 sK3 sK2 : G, (sK4 ◇ (sK3 ◇ sK2)) = ((sK4 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK4 sK3 sK2
    conv => enter [1]; rw [h52 (sK4 ◇ (sK3 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK2 sK4 sK3]
  have l11 : ∀ sK2 sK4 sK3 : G, sK2 = (sK2 ◇ (sK4 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK4 sK3
    conv => enter [1]; rw [h52 sK2 (sK4 ◇ (sK3 ◇ sK2))]
    conv => enter [1, 2]; rw [← l10 sK4 sK3 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation257_261_implies_Equation256 (G : Type*) [Magma G] (h257 : Equation257 G) (h261 : Equation261 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ ((X0 ◇ X0) ◇ X1)) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h261 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h257 X0 X1]
  have l1 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h261 X0 ((X0 ◇ X0) ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 ((X0 ◇ X0) ◇ X1) X2]
    conv => enter [1, 1, 1]; rw [l1 X0 X1]
    conv => enter [1, 2, 1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 X3 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1, 2]; rw [l2 X0 X1 X0]
    conv => enter [1, 1]; rw [l2 X0 X1 X0]
    conv => enter [1]; rw [← l2 (X0 ◇ X0) X3 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← l2 X0 X1 X0]
  have l4 : ∀ X0 X1 X3 : G, (((X0 ◇ X0) ◇ X1) ◇ X3) = X0 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l3 X0 X1 X3]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x x y]

theorem Equation52_65_implies_Equation62 (G : Type*) [Magma G] (h52 : Equation52 G) (h65 : Equation65 G) : Equation62 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h65 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h52 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h65 X0 (X1 ◇ (X0 ◇ X0))]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l1 X2 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [l1 X1 X0]
    conv => enter [1, 1, 2]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 X3 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = (X3 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X3
    conv => enter [1, 1]; rw [l2 X1 X0 X1]
    conv => enter [1, 2]; rw [l2 X1 X0 X1]
    conv => enter [1]; rw [← l2 X3 (X1 ◇ X0) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X1 X0 X1]
  have l4 : ∀ X3 X1 X0 : G, (X3 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X3 X1 X0
    conv => enter [1]; rw [← l3 X1 X0 X3]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 y x x]

theorem Equation257_258_263_implies_Equation256 (G : Type*) [Magma G] (h257 : Equation257 G) (h258 : Equation258 G) (h263 : Equation263 G) : Equation256 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X0) ◇ X1) X0]
    conv => enter [1, 1, 1]; rw [← h257 X0 X1]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 ((X0 ◇ X0) ◇ X1) X1]
    conv => enter [1, 1, 1]; rw [← h258 X0 X1]
  have l2 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h258 X0 ((X0 ◇ X0) ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = ((((X0 ◇ X0) ◇ X1) ◇ ((X0 ◇ X0) ◇ X1)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h263 (X0 ◇ X1) ((X0 ◇ X0) ◇ X1)]
    conv => enter [1, 1, 1]; rw [← l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ (X0 ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h263 X0 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h258 (X0 ◇ X1) X0]
  have l7 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l6 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h258 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← l6 (X0 ◇ X1) ((X0 ◇ X0) ◇ X1)]
  have l9 : ∀ X0 X1 : G, (((X0 ◇ X0) ◇ X0) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l8 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 x y]

theorem Equation52_55_72_implies_Equation62 (G : Type*) [Magma G] (h52 : Equation52 G) (h55 : Equation55 G) (h72 : Equation72 G) : Equation62 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h52 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h72 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h72 X0 (X1 ◇ (X0 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h55 (X1 ◇ X0) (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [l2 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h55 X0 (X1 ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h72 (X1 ◇ X0) X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l6 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← h72 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← l6 (X1 ◇ X0) (X1 ◇ (X0 ◇ X0))]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [← l9 y x]

theorem Equation203_385_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h385 : Equation385 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h385 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h385 X0 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_325_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h325 : Equation325 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h325 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h325 X0 X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation203_378_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h378 : Equation378 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h378 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation99_323_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h323 : Equation323 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h323 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation203_377_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h377 : Equation377 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h377 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h377 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation99_333_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h333 : Equation333 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h333 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h333 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation203_375_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h375 : Equation375 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h375 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h375 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation99_326_implies_Equation3 (G : Type*) [Magma G] (h99 : Equation99 G) (h326 : Equation326 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h326 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h326 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation203_365_implies_Equation14 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation14 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l2 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]

theorem Equation203_365_implies_Equation66 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation66 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l2 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 y x]
  conv => enter [1, 2, 2]; rw [← l2 y]

theorem Equation203_365_implies_Equation115 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation115 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l2 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x]
  conv => enter [1]; rw [← l4 y (x ◇ x)]

theorem Equation203_365_implies_Equation219 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation219 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l2 x]
  conv => enter [1]; rw [← l3 y (x ◇ x)]

theorem Equation203_365_implies_Equation53 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation53 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l2 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x]
  conv => enter [1, 2]; rw [← l4 y x]

theorem Equation203_365_implies_Equation273 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation273 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l2 x]
  conv => enter [1, 1]; rw [← l3 y x]

theorem Equation203_365_implies_Equation105 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation105 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h365 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l2 x]
  conv => enter [1, 2]; rw [← l3 y x]

theorem Equation203_365_implies_Equation221 (G : Type*) [Magma G] (h203 : Equation203 G) (h365 : Equation365 G) : Equation221 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h365 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h365 X1 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h365 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l2 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x]
  conv => enter [1, 1]; rw [← l4 y x]

theorem Equation99_313_implies_Equation14 (G : Type*) [Magma G] (h99 : Equation99 G) (h313 : Equation313 G) : Equation14 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h313 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h313 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h313 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← h313 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation203_362_implies_Equation258 (G : Type*) [Magma G] (h203 : Equation203 G) (h362 : Equation362 G) : Equation258 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X2) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h362 X0 X1]
    conv => enter [1]; rw [h362 X0 X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (((X0 ◇ X1) ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← h362 X0 X1]
    conv => enter [1]; rw [h362 X0 X0]
    conv => enter [1, 1]; rw [h362 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h362 X0 X1]
    conv => enter [1]; rw [← h362 (X0 ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ ((X0 ◇ X1) ◇ X1)) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← h362 X0 X1]
    conv => enter [1]; rw [← h203 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ (X0 ◇ X0)) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ X0)) X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (((X0 ◇ X1) ◇ X1) ◇ X2) = ((X0 ◇ X2) ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h362 (X0 ◇ X2) X2]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l3 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 2, 1]; rw [← h203 X0]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [l5 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [l1 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h203 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1]; rw [← l8 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 1, 1]; rw [← l10 X0]
  have l12 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l10 X0]
    conv => enter [1]; rw [← h203 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h362 X0 X0]
    conv => enter [1]; rw [l12 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l13 X0]
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l13 X0]
  intro x y
  conv => enter [1]; rw [← l13 x]
  conv => enter [1]; rw [← l14 (x ◇ x) y]

theorem Equation99_315_implies_Equation72 (G : Type*) [Magma G] (h99 : Equation99 G) (h315 : Equation315 G) : Equation72 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X2 ◇ (X2 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [h315 X0 X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [h315 X0 X0]
    conv => enter [1, 2]; rw [h315 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h315 X0 X1]
    conv => enter [1]; rw [← h315 (X1 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [← h99 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ X0) ◇ X0) X1]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X1 ◇ X0))) = ((X2 ◇ X0) ◇ (X2 ◇ X0)) := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h315 (X2 ◇ X0) X2]
  have l6 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [← l3 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 1, 2]; rw [← h99 X0]
  have l7 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = ((((X0 ◇ X0) ◇ X0) ◇ X0) ◇ (((X0 ◇ X0) ◇ X0) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [l5 ((X0 ◇ X0) ◇ X0) (X0 ◇ X0) X0]
  have l8 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X0) X0]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = (((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [l1 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h99 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1]; rw [← l8 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2, 2]; rw [← l10 X0]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l10 X0]
    conv => enter [1]; rw [← h99 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h315 X0 X0]
    conv => enter [1]; rw [l12 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l13 X0]
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1]; rw [l13 X0]
  intro x y
  conv => enter [1]; rw [← l13 x]
  conv => enter [1]; rw [← l14 y (x ◇ x)]

theorem Equation203_361_implies_Equation257 (G : Type*) [Magma G] (h203 : Equation203 G) (h361 : Equation361 G) : Equation257 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h361 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h361 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 1, 1]; rw [← l0 x]

theorem Equation203_361_implies_Equation25 (G : Type*) [Magma G] (h203 : Equation203 G) (h361 : Equation361 G) : Equation25 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h361 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h361 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation203_361_implies_Equation156 (G : Type*) [Magma G] (h203 : Equation203 G) (h361 : Equation361 G) : Equation156 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h361 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X1) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 X0 X1]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h361 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 2]; rw [← l0 x]

theorem Equation203_361_implies_Equation101 (G : Type*) [Magma G] (h203 : Equation203 G) (h361 : Equation361 G) : Equation101 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h361 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h203 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h361 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h361 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l3 x x]
  conv => enter [1, 2]; rw [h361 x y]

theorem Equation99_309_implies_Equation52 (G : Type*) [Magma G] (h99 : Equation99 G) (h309 : Equation309 G) : Equation52 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h309 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h309 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 2, 2]; rw [← l0 x]

theorem Equation99_309_implies_Equation10 (G : Type*) [Magma G] (h99 : Equation99 G) (h309 : Equation309 G) : Equation10 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h309 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h309 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

theorem Equation99_309_implies_Equation153 (G : Type*) [Magma G] (h99 : Equation99 G) (h309 : Equation309 G) : Equation153 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h309 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h309 X0 X1]
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1, 1]; rw [← h309 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]
  conv => enter [1, 1]; rw [← l0 x]

theorem Equation99_309_implies_Equation208 (G : Type*) [Magma G] (h99 : Equation99 G) (h309 : Equation309 G) : Equation208 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h309 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h99 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h309 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h309 X0 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0)]
    conv => enter [1]; rw [← l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l3 x x]
  conv => enter [1, 1]; rw [h309 x y]

theorem Equation203_273_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h273 : Equation273 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h273 (X0 ◇ X0) X0]
    conv => enter [1, 1]; rw [← h203 X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h203 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h273 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation53_99_implies_Equation3 (G : Type*) [Magma G] (h53 : Equation53 G) (h99 : Equation99 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h53 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h99 X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h99 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h53 X0 X0]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation203_264_283_implies_Equation231 (G : Type*) [Magma G] (h203 : Equation203 G) (h264 : Equation264 G) (h283 : Equation283 G) : Equation231 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1]
    conv => enter [1]; rw [← h283 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation203_264_283_implies_Equation151 (G : Type*) [Magma G] (h203 : Equation203 G) (h264 : Equation264 G) (h283 : Equation283 G) : Equation151 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h264 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1, 1, 1]; rw [← h203 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1]; rw [l0 X1]
    conv => enter [1]; rw [← h283 X0 X1]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h264 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation56_75_99_implies_Equation108 (G : Type*) [Magma G] (h56 : Equation56 G) (h75 : Equation75 G) (h99 : Equation99 G) : Equation108 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h75 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h99 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1]
    conv => enter [1]; rw [← h56 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation56_75_99_implies_Equation151 (G : Type*) [Magma G] (h56 : Equation56 G) (h75 : Equation75 G) (h99 : Equation99 G) : Equation151 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h75 ((X0 ◇ X0) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← h99 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X1]
    conv => enter [1]; rw [← h56 X0 X1]
  have l2 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h75 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l2 x]

theorem Equation203_261_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h261 : Equation261 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h261 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation65_99_implies_Equation3 (G : Type*) [Magma G] (h65 : Equation65 G) (h99 : Equation99 G) : Equation3 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h65 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

theorem Equation203_260_implies_Equation3 (G : Type*) [Magma G] (h203 : Equation203 G) (h260 : Equation260 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h203 X0]
    conv => enter [1]; rw [← h260 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation49_99_implies_Equation3 (G : Type*) [Magma G] (h49 : Equation49 G) (h99 : Equation99 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h99 X0]
    conv => enter [1]; rw [← h49 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation231_367_implies_Equation5 (G : Type*) [Magma G] (h231 : Equation231 G) (h367 : Equation367 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h367 X1 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 1]; rw [← h231 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [← h231 X1 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h231 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation108_310_implies_Equation4 (G : Type*) [Magma G] (h108 : Equation108 G) (h310 : Equation310 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h310 X1 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1, 2]; rw [← h108 ((X0 ◇ X0) ◇ X0) X0]
  have l1 : ∀ X1 : G, (X1 ◇ X1) = X1 := by
    intro X1
    conv => enter [1]; rw [l0 X1 X1]
    conv => enter [1]; rw [← h108 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h108 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

end Order3
