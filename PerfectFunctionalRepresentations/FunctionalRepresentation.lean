-- Functional Representations
-- Core definitions: functional representations, canonical representations, perfect representability

import «PerfectFunctionalRepresentations».InfoTheory

namespace FunctionalRepresentation

open InfoTheory

-- A functional representation Z of (X, Y) satisfies:
-- 1. Y = g(X, Z) for deterministic function gp
-- 2. X is independent of Z
structure FunctionalRepresentation {X Y : Type} where
  Z : Type
  g : X → Z → Y
  pZ : Distribution Z
  -- independence: independent (fun xz => pX xz.1 * pZ xz.2)

def satisfies_equation_one {X Y Z : Type}
    (pXYZ : TripleDistribution X Y Z) : Prop :=
  let pXZ : JointDistribution X Z :=
    fun
      | (x, z) => discrete_sum (fun y : Y => pXYZ (x, y, z))
  let pY_XZ : JointDistribution (X × Z) Y :=
    fun
      | ((x, z), y) => pXYZ (x, y, z)
  mutual_information pXZ = 0 ∧ conditional_entropy pY_XZ = 0

structure CanonicalFunctionalRepresentation (X Y : Type) where
  W : Type
  pW : Distribution W
  decode : X → W → Y

noncomputable def represented_mass_integrand {X Y : Type}
    (representation : CanonicalFunctionalRepresentation X Y)
    (x : X) (y : Y) : representation.W → Probability := by
  classical
  exact fun w => if representation.decode x w = y then representation.pW w else 0

noncomputable def represented_mass {X Y : Type}
    (representation : CanonicalFunctionalRepresentation X Y) : Channel X Y := by
  exact fun x y =>
    discrete_sum (represented_mass_integrand representation x y)

theorem represented_mass_eq {X Y : Type}
    (representation : CanonicalFunctionalRepresentation X Y)
    (x : X) (y : Y) :
    represented_mass representation x y =
      discrete_sum (represented_mass_integrand representation x y) := by
  rfl

theorem represented_mass_integrand_of_eq {X Y : Type}
    (representation : CanonicalFunctionalRepresentation X Y)
    (x : X) (y : Y) (w : representation.W)
    (h : representation.decode x w = y) :
    represented_mass_integrand representation x y w = representation.pW w := by
  classical
  simp [represented_mass_integrand, h]

theorem represented_mass_integrand_of_ne {X Y : Type}
    (representation : CanonicalFunctionalRepresentation X Y)
    (x : X) (y : Y) (w : representation.W)
    (h : representation.decode x w ≠ y) :
    represented_mass_integrand representation x y w = 0 := by
  classical
  simp [represented_mass_integrand, h]

def is_canonical_functional_representation {X Y : Type}
    (pXY : JointDistribution X Y)
    (representation : CanonicalFunctionalRepresentation X Y) : Prop := by
  exact ∀ x y, pXY (x, y) = marginal_left pXY x * represented_mass representation x y

noncomputable def joint_yw_of_canonical_representation {X Y : Type}
    (pXY : JointDistribution X Y)
    (representation : CanonicalFunctionalRepresentation X Y) :
    JointDistribution Y representation.W := by
  classical
  exact fun
    | (y, w) =>
        representation.pW w *
          discrete_sum (fun x : X =>
            if representation.decode x w = y then marginal_left pXY x else 0)

noncomputable def canonical_representation_information {X Y : Type}
    (pXY : JointDistribution X Y)
    (representation : CanonicalFunctionalRepresentation X Y) : Probability :=
  mutual_information (joint_yw_of_canonical_representation pXY representation)

axiom exists_maximizing_canonical_representation {X Y : Type}
    (pXY : JointDistribution X Y) :
    ∃ representation : CanonicalFunctionalRepresentation X Y,
      is_canonical_functional_representation pXY representation ∧
        ∀ representation' : CanonicalFunctionalRepresentation X Y,
          is_canonical_functional_representation pXY representation' →
            canonical_representation_information pXY representation' ≤
              canonical_representation_information pXY representation

noncomputable def maximal_functional_representation_information {X Y : Type}
    (pXY : JointDistribution X Y) : Probability := by
  classical
  exact canonical_representation_information pXY
    (Classical.choose (exists_maximizing_canonical_representation pXY))

-- A conditional distribution pY|X is perfectly representable
def perfectly_representable {X Y : Type} (pY_X : Channel X Y) : Prop :=
  by
    exact ∃ representation : CanonicalFunctionalRepresentation X Y,
      ∀ x y, pY_X x y = represented_mass representation x y

-- Singular channel: for all y and all x₁, x₂ with p(y|x₁) > 0 and p(y|x₂) > 0,
-- we have p(y|x₁) = p(y|x₂)
def is_singular_channel {X Y : Type} (pY_X : Channel X Y) : Prop :=
  ∀ y x₁ x₂,
    0 < pY_X x₁ y →
    0 < pY_X x₂ y →
    pY_X x₁ y = pY_X x₂ y

end FunctionalRepresentation
