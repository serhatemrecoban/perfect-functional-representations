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
    (pXYZ : TripleDistribution X Y Z) : Prop := sorry

structure CanonicalFunctionalRepresentation (X Y : Type) where
  W : Type
  pW : Distribution W
  decode : X → W → Y

def is_canonical_functional_representation {X Y : Type}
    (pXY : JointDistribution X Y)
    (representation : CanonicalFunctionalRepresentation X Y) : Prop := sorry

def joint_yw_of_canonical_representation {X Y : Type}
    (pXY : JointDistribution X Y)
    (representation : CanonicalFunctionalRepresentation X Y) :
    JointDistribution Y representation.W := sorry

def canonical_representation_information {X Y : Type}
    (pXY : JointDistribution X Y) : Probability := sorry

def maximal_functional_representation_information {X Y : Type}
    (pXY : JointDistribution X Y) : Probability := sorry

-- A conditional distribution pY|X is perfectly representable
def perfectly_representable {X Y : Type} (pY_X : Channel X Y) : Prop :=
  sorry

-- Singular channel: for all y and all x₁, x₂ with p(y|x₁) > 0 and p(y|x₂) > 0,
-- we have p(y|x₁) = p(y|x₂)
def is_singular_channel {X Y : Type} (pY_X : Channel X Y) : Prop :=
  sorry

end FunctionalRepresentation
