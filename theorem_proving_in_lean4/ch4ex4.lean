def even (n : Nat) : Prop := ∃ k: Nat, n=k*2

def prime (n : Nat) : Prop :=
  ¬(∃ l m: Nat, (m != 1 ∧ l != n) → n = m * l)

def infinitely_many_primes : Prop :=
  (∀ n : Nat, ∃ x: Nat, x >= n ∧ (prime x))

def Fermat_prime (n : Nat) : Prop :=
  (prime n) ∧ (∃ k, n=2^(2^k) + 1)

def infinitely_many_Fermat_primes : Prop :=
  (∀ n : Nat, ∃ x: Nat, x >= n ∧ (Fermat_prime x))

def goldbach_conjecture : Prop :=
  (∀ n : Nat, ((n > 2) ∧ (even n)) →
    (∃ l m : Nat, ((prime l) ∧ (prime m)) → n = l + m))

def Goldbach's_weak_conjecture : Prop :=
  (∀ n : Nat, ((n > 5) ∧ ¬(even n)) →
    (∃ k l m: Nat, ((prime k) ∧ (prime l) ∧ (prime m)) → n = k + l + m))

def Fermat's_last_theorem : Prop :=
  (∀ n : Nat, (n > 2) → (¬∃ x y z : Nat, x^n + y^n = z^n))
