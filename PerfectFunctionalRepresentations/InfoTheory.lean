-- Information Theory Basics
-- Fundamental definitions: entropy, mutual information, conditional distributions

namespace InfoTheory

abbrev Probability := Rat

abbrev Distribution (α : Type) := α → Probability

abbrev JointDistribution (X Y : Type) := X × Y → Probability

abbrev TripleDistribution (X Y Z : Type) := X × Y × Z → Probability

abbrev Channel (X Y : Type) := X → Y → Probability

def marginal_left {X Y : Type} (pXY : JointDistribution X Y) : Distribution X := sorry

def marginal_right {X Y : Type} (pXY : JointDistribution X Y) : Distribution Y := sorry

def joint_xy_of_xyz {X Y Z : Type} (pXYZ : TripleDistribution X Y Z) : JointDistribution X Y := sorry

def joint_yz_of_xyz {X Y Z : Type} (pXYZ : TripleDistribution X Y Z) : JointDistribution Y Z := sorry

def conditional_distribution_of_joint {X Y : Type} (pXY : JointDistribution X Y) : Channel X Y := sorry

-- Entropy: H(Y) = -Σ p(y) log p(y)
def entropy {Y : Type} (p : Distribution Y) : Probability := sorry

-- Conditional entropy: H(Y|X)
def conditional_entropy {X Y : Type} (pXY : JointDistribution X Y) : Probability := sorry

-- Mutual information: I(X;Y) = H(Y) - H(Y|X)
def mutual_information {X Y : Type} (pXY : JointDistribution X Y) : Probability := sorry

-- Conditional mutual information: I(X;Z|Y)
def conditional_mutual_information {X Y Z : Type}
    (pXYZ : TripleDistribution X Y Z) : Probability := sorry

-- Independence of random variables
def independent {A B : Type} (pAB : JointDistribution A B) : Prop :=
  ∃ pA : Distribution A, ∃ pB : Distribution B, ∀ a b, pAB (a, b) = pA a * pB b

-- Markov chain: X - Y - Z means I(X;Z|Y) = 0
def markov_chain {X Y Z : Type} (pXYZ : TripleDistribution X Y Z) : Prop :=
  conditional_mutual_information pXYZ = 0

-- Total variation distance between two distributions
def total_variation_distance {α : Type}
    (p₁ p₂ : Distribution α) : Probability := sorry

def output_distribution {X Y : Type}
    (pX : Distribution X) (pY_X : Channel X Y) : Distribution Y := sorry

end InfoTheory
