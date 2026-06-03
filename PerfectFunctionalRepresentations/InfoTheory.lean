import Std

-- Information Theory Basics
-- Fundamental definitions: entropy, mutual information, conditional distributions

namespace InfoTheory

abbrev Probability := Rat

abbrev Distribution (α : Type) := α → Probability

abbrev JointDistribution (X Y : Type) := X × Y → Probability

abbrev TripleDistribution (X Y Z : Type) := X × Y × Z → Probability

abbrev Channel (X Y : Type) := X → Y → Probability

axiom discrete_sum {α : Type} : (α → Probability) → Probability

axiom discrete_sum_congr {α : Type} {f g : α → Probability} :
  (∀ a : α, f a = g a) → discrete_sum f = discrete_sum g

axiom discrete_sum_zero {α : Type} :
  discrete_sum (fun _ : α => 0) = 0

axiom discrete_sum_add {α : Type} (f g : α → Probability) :
  discrete_sum (fun a : α => f a + g a) = discrete_sum f + discrete_sum g

axiom discrete_sum_mul_left {α : Type} (c : Probability) (f : α → Probability) :
  discrete_sum (fun a : α => c * f a) = c * discrete_sum f

axiom discrete_sum_split_weight {α : Type} (c : Probability) (f : α → Probability) :
  discrete_sum (fun a : α => c * f a) +
    discrete_sum (fun a : α => (1 - c) * f a) =
      discrete_sum f

axiom discrete_sum_sum {α β : Type} (f : Sum α β → Probability) :
  discrete_sum f =
    discrete_sum (fun a : α => f (.inl a)) +
      discrete_sum (fun b : β => f (.inr b))

axiom discrete_sum_punit (f : PUnit → Probability) :
  discrete_sum f = f PUnit.unit

noncomputable def marginal_left {X Y : Type}
    (pXY : JointDistribution X Y) : Distribution X :=
  fun x => discrete_sum (fun y : Y => pXY (x, y))

noncomputable def marginal_right {X Y : Type}
    (pXY : JointDistribution X Y) : Distribution Y :=
  fun y => discrete_sum (fun x : X => pXY (x, y))

noncomputable def joint_xy_of_xyz {X Y Z : Type}
    (pXYZ : TripleDistribution X Y Z) : JointDistribution X Y :=
  fun
    | (x, y) => discrete_sum (fun z : Z => pXYZ (x, y, z))

noncomputable def joint_yz_of_xyz {X Y Z : Type}
    (pXYZ : TripleDistribution X Y Z) : JointDistribution Y Z :=
  fun
    | (y, z) => discrete_sum (fun x : X => pXYZ (x, y, z))

noncomputable def conditional_distribution_of_joint {X Y : Type}
    (pXY : JointDistribution X Y) : Channel X Y :=
  fun x y =>
    let pX := marginal_left pXY x
    if pX = 0 then 0 else pXY (x, y) / pX

-- Abstract scalar Shannon contribution q |-> -q log q, with the 0 log 0 convention built in.
axiom shannon_entropy_term : Probability → Probability

-- Entropy: H(Y) = Σ h(p(y)), where h(q) = -q log q.
noncomputable def entropy {Y : Type} (p : Distribution Y) : Probability :=
  discrete_sum (fun y : Y => shannon_entropy_term (p y))

-- Conditional entropy: H(Y|X)
noncomputable def conditional_entropy {X Y : Type}
    (pXY : JointDistribution X Y) : Probability :=
  let pX := marginal_left pXY
  let pY_X := conditional_distribution_of_joint pXY
  discrete_sum (fun x : X => pX x * entropy (pY_X x))

-- Mutual information: I(X;Y) = H(Y) - H(Y|X)
noncomputable def mutual_information {X Y : Type}
    (pXY : JointDistribution X Y) : Probability :=
  entropy (marginal_right pXY) - conditional_entropy pXY

-- Conditional mutual information: I(X;Z|Y)
noncomputable def conditional_mutual_information {X Y Z : Type}
    (pXYZ : TripleDistribution X Y Z) : Probability :=
  let pYZ := joint_yz_of_xyz pXYZ
  let pZ_XY : JointDistribution (X × Y) Z :=
    fun
      | ((x, y), z) => pXYZ (x, y, z)
  conditional_entropy pYZ - conditional_entropy pZ_XY

-- Independence of random variables
def independent {A B : Type} (pAB : JointDistribution A B) : Prop :=
  ∃ pA : Distribution A, ∃ pB : Distribution B, ∀ a b, pAB (a, b) = pA a * pB b

-- Markov chain: X - Y - Z means I(X;Z|Y) = 0
def markov_chain {X Y Z : Type} (pXYZ : TripleDistribution X Y Z) : Prop :=
  conditional_mutual_information pXYZ = 0

-- Total variation distance between two distributions
noncomputable def total_variation_distance {α : Type}
    (p₁ p₂ : Distribution α) : Probability :=
  discrete_sum (fun a : α => Rat.abs (p₁ a - p₂ a)) / 2

noncomputable def output_distribution {X Y : Type}
    (pX : Distribution X) (pY_X : Channel X Y) : Distribution Y :=
  fun y => discrete_sum (fun x : X => pX x * pY_X x y)

end InfoTheory
