open import Data.Nat
open import Data.Nat.Induction
open import Data.Sum
open import Data.Product
open import Data.Bool using (Bool ; true ; false)
open import Data.Unit using (⊤)
open import Data.Bool using (if_then_else_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_ ; yes ; no)
open import Relation.Nullary.Decidable
open import Function.Base using (case_of_ ; case_return_of_)
open import Function using (_∋_)
open import Relation.Binary.PropositionalEquality
open import Level using (0ℓ)

open ≡-Reasoning

record Position : Set where
    constructor pos
    field
        x : ℕ
        y : ℕ

example1 : {p₁ p₂ : Position} → ¬(p₁ ≡ p₂) → ¬(Position.x p₁ ≡ Position.x p₂) ⊎ ¬(Position.y p₁ ≡ Position.y p₂)
example1 {pos x₁ y₁} {pos x₂ y₂} neq with x₁ ≟ x₂
... | yes x₁≡x₂ with y₁ ≟ y₂
...     | yes y₁≡y₂ = case (neq (cong₂ pos x₁≡x₂ y₁≡y₂)) of λ {()}
...     | no  y₁≢y₂ = inj₂ y₁≢y₂
example1 _ _ _ | no x₁≢x₂ = inj₁ x₁≢x₂

example2 : {x y : ℕ} → (y ≡ x + 7) → (2 * y ≡ 2 * (x + 7))
example2 refl = refl

example3 : {a b : ℕ} → (suc a ≡ b) → (suc (suc a) ≡ suc b)
example3 refl = refl

postulate
    add_suc_hypot : ∀ (a d : ℕ) → a + suc d ≡ suc (a + d)
    add_zero_hypot : ∀ (a : ℕ) → (a + 0 ≡ a)

symmetric≡ : ∀ {a b : ℕ} → a ≡ b → b ≡ a
symmetric≡ refl = refl

transitive≡ : ∀ {a b c : ℕ} → (a ≡ b) → (b ≡ c) → (a ≡ c)
transitive≡ refl refl = refl

congruence : ∀ {a b : ℕ} {T : Set} → a ≡ b → (f : ℕ → T) → (f a ≡ f b)
congruence refl f = refl

example4 : ∀ (a : ℕ) → a + suc 0 ≡ suc a
example4 a = t4 where
    t1 : a + 0 ≡ a
    t1 = add_zero_hypot a
    t2 : a + suc 0 ≡ suc (a + 0)
    t2 = add_suc_hypot a 0
    t3 : suc (a + 0) ≡ suc a
    t3 = congruence t1 suc
    t4 = transitive≡ t2 t3

zero_add : ∀ (a : ℕ) → (0 + a ≡ a)
zero_add a = refl

add_zero : ∀ (n : ℕ) → n + 0 ≡ n
add_zero = rec P cases where
    P : ℕ → Set
    P = (λ x → x + 0 ≡ x)
    baseCase : 0 + 0 ≡ 0
    baseCase = refl
    indStep : ∀ (x : ℕ) → x + 0 ≡ x → (suc x) + 0 ≡ suc x
    indStep x eq = congruence eq suc
    cases : ∀ (x : ℕ) → Rec 0ℓ P x → P x
    cases 0 tt = baseCase
    cases (suc x) prevCase = indStep x prevCase

add_zero2 : ∀ (n : ℕ) → n + 0 ≡ n
add_zero2 0 = refl
add_zero2 (suc n) = indStep n (add_zero2 n) where
    indStep : ∀ (x : ℕ) → x + 0 ≡ x → (suc x) + 0 ≡ suc x
    indStep x eq = congruence eq suc

add_assoc : ∀ (a b c : ℕ) → a + (b + c) ≡ (a + b) + c
add_assoc 0 b c = refl
add_assoc (suc a) b c = let
    lhs : (suc a) + (b + c) ≡ suc (a + (b + c))
    lhs = refl
    rhs : ((suc a) + b) + c ≡ suc ((a + b) + c)
    rhs = refl
    prev : (a + (b + c)) ≡ ((a + b) + c)
    prev = add_assoc a b c
    in congruence prev suc

add_suc : ∀ (a b : ℕ) → a + suc b ≡ suc (a + b)
add_suc 0 b = refl
add_suc (suc a) b = let
    lhs : suc a + suc b ≡ suc (a + suc b)
    lhs = refl
    rhs : suc (suc a + b) ≡ suc (suc (a + b))
    rhs = refl
    prev : a + suc b ≡ suc (a + b)
    prev = add_suc a b
    lhs2 : suc (a + suc b) ≡ suc (suc (a + b))
    lhs2 = congruence prev suc
    in transitive≡ (transitive≡ lhs lhs2) rhs

add_comm : ∀ (a b : ℕ) → a + b ≡ b + a
add_comm 0 b = let
    lhs : 0 + b ≡ b
    lhs = refl
    rhs : b + 0 ≡ b
    rhs = add_zero2 b
    in transitive≡ lhs (symmetric≡ rhs)
add_comm (suc a) b = let
    lhs : suc a + b ≡ suc (a + b)
    lhs = refl
    rhs : b + suc a ≡ suc (b + a)
    rhs = add_suc b a
    prev : a + b ≡ b + a
    prev = add_comm a b
    eq1 : suc (a + b) ≡ suc (b + a)
    eq1 = congruence prev suc
    in transitive≡ (transitive≡ lhs eq1) (symmetric≡ rhs)

add5 : ∀ (n : ℕ) → suc n ≡ n + 1
add5 0 = refl
add5 (suc n) = let
    -- target : suc (suc n) ≡ suc n + 1
    rhs : suc n + 1 ≡ suc (n + 1)
    rhs = refl
    prev : suc n ≡ n + 1
    prev = add5 n
    prev_lifted : suc (suc n) ≡ suc (n + 1)
    prev_lifted = congruence prev suc
    in symmetric≡ (transitive≡ rhs (symmetric≡ prev_lifted))

add6 : ∀ (a b c : ℕ) → a + b + c ≡ a + c + b
add6 a b c = let
    eq1 : a + c + b ≡ c + a + b
    eq1 = congruence (add_comm a c) (λ x → x + b)
    eq2 : c + a + b ≡ c + (a + b)
    eq2 = symmetric≡ (add_assoc c a b)
    eq3 : c + (a + b) ≡ a + b + c
    eq3 = add_comm c (a + b)
    in symmetric≡ (transitive≡ (transitive≡ eq1 eq2) eq3)

mul_zero : ∀ (m : ℕ) → m * 0 ≡ 0
mul_zero 0 = refl
mul_zero (suc m) = let
    eq1 : (suc m) * 0 ≡ m * 0
    eq1 = refl
    in transitive≡ eq1 (mul_zero m)

one_mul : ∀ (m : ℕ) → 1 * m ≡ m
one_mul m = let
    eq1 : 1 * m ≡ m + 0
    eq1 = refl
    eq2 : m + 0 ≡ m
    eq2 = add_comm m 0
    in (transitive≡ eq1 eq2)

one_mul2 : ∀ (m : ℕ) → 1 * m ≡ m
one_mul2 m = transitive≡ refl (add_comm m 0)

mul_one : ∀ (m : ℕ) → m * 1 ≡ m
mul_one 0 = refl
mul_one (suc m) = let
    eq1 : (suc m) * 1 ≡ 1 + m * 1
    eq1 = refl
    prev : m * 1 ≡ m
    prev = mul_one m
    in transitive≡ eq1 (congruence prev (λ x → 1 + x))

mul_right_distrib : ∀ (a b t : ℕ) → (a + b) * t ≡ a * t + b * t
mul_right_distrib 0 b t = refl
mul_right_distrib (suc a) b t = let
    eq1 : suc (a + b) ≡ suc a + b
    eq1 = refl
    eq5 = subst (λ x → t + x ≡ t + a * t + b * t) ((sym (mul_right_distrib a b t))) ((add_assoc t ((a * t)) ((b * t))))
    eq4 = subst (λ x → t + (a + b) * t ≡ x + b * t) (t + a * t ≡ suc a * t ∋ refl) eq5
    eq3 = trans (suc (a + b) * t ≡ t + (a + b) * t ∋ refl) eq4
    in subst (λ x → x * t ≡ suc a * t + b * t) eq1 eq3

mul_assoc : ∀ (a b c : ℕ) → a * b * c ≡ a * (b * c)
mul_assoc 0 b c = refl
mul_assoc (suc a) b c = subst (λ x → x * c ≡ suc a * (b * c)) (b + a * b ≡ suc a * b ∋ refl) eq1 where
    eq3 = cong (λ x → b * c + x) (mul_assoc a b c)
    eq2 = sym ( trans (mul_right_distrib b (a * b) c) eq3 )
    eq1 = sym (trans (suc a * (b * c) ≡ b * c + a * (b * c) ∋ refl) eq2)

mul_suc : ∀ (a b : ℕ) → a * suc b ≡ a + a * b
mul_suc 0 b = refl
mul_suc (suc a) b = trans (suc a * suc b ≡ suc b + a * suc b ∋ refl) eq1 where
    eq7 = cong (λ x → x + a * b) (add_comm b a)
    eq6 = sym (trans (add_assoc b a (a * b)) eq7)
    eq5 = cong suc (trans (add_assoc a b (a * b)) eq6)
    eq4 = sym (trans (suc a + (b + a * b) ≡ suc (a + (b + a * b)) ∋ refl) eq5)
    eq3 = trans (suc b + (a + a * b) ≡ suc (b + (a + a * b)) ∋ refl) eq4
    eq2 = subst (λ x → suc b + x ≡ suc a + (b + a * b)) (sym (mul_suc a b)) eq3
    eq1 = subst (λ x → suc b + a * suc b ≡ suc a + x) (b + a * b ≡ suc a * b ∋ refl) eq2

mul_suc2 : ∀ (a b : ℕ) → a * suc b ≡ a + a * b
mul_suc2 0 b = refl
mul_suc2 (suc a) b =
    suc a * suc b
    ≡⟨ suc a * suc b ≡ suc (b + a * suc b) ∋ refl ⟩
    suc (b + a * suc b)
    ≡⟨ cong suc (
        b + a * suc b
        ≡⟨ cong (λ x → b + x) (mul_suc2 a b) ⟩
        b + (a + a * b)
        ≡⟨ add_assoc b a (a * b) ⟩
        b + a + a * b
        ∎
    )⟩
    sym (
        suc a + suc a * b
        ≡⟨ (suc a + suc a * b ≡ suc (a + (b + a * b)) ∋ refl) ⟩
        cong suc (
            a + (b + a * b)
            ≡⟨ add_assoc a b (a * b) ⟩
            cong (λ x → x + a * b) (add_comm a b)
        )
    )

mul_suc3 : ∀ (a b : ℕ) → a * suc b ≡ a + a * b
mul_suc3 0 b = refl
mul_suc3 (suc a) b = suc a * suc b
    ≡⟨ suc a * suc b ≡ suc (b + a * suc b) ∋ refl ⟩
    sym (
        suc a + suc a * b
        ≡⟨ suc a + suc a * b ≡ suc (a + (b + a * b)) ∋ refl ⟩
        eq1
    )
    where
        eq2 : suc (a + b + a * b) ≡ suc (b + a + a * b)
        eq2 rewrite (add_comm a b) = refl
        eq1 : suc (a + (b + a * b)) ≡ suc (b + a * suc b)
        eq1 rewrite (mul_suc3 a b) | add_assoc a b (a * b) | add_assoc b a (a * b) = eq2

mul_suc4 : ∀ (a b : ℕ) → a * suc b ≡ a + a * b
mul_suc4 0 b = refl
mul_suc4 (suc a) b = suc a * suc b
    ≡⟨ suc a * suc b ≡ suc (b + a * suc b) ∋ refl ⟩
    suc (b + a * suc b)
    ≡⟨ sym (
        suc a + suc a * b
        ≡⟨ suc a + suc a * b ≡ suc (a + (b + a * b)) ∋ refl ⟩
        suc (a + (b + a * b))
        ≡⟨ eq1 ⟩
        suc (b + a * suc b) ∎
    )⟩
    suc a + suc a * b ∎
    where
        eq2 : suc (a + b + a * b) ≡ suc (b + a + a * b)
        eq2 rewrite (add_comm a b) = refl
        eq1 : suc (a + (b + a * b)) ≡ suc (b + a * suc b)
        eq1 rewrite (mul_suc4 a b) | add_assoc a b (a * b) | add_assoc b a (a * b) = eq2

mul_suc5 : ∀ (a b : ℕ) → a * suc b ≡ a + a * b
mul_suc5 0 b = refl
mul_suc5 (suc a) b = eq1 where
    eq1 : suc a * suc b ≡ suc a + suc a * b
    eq1 rewrite suc a * suc b ≡ suc (b + a * suc b) ∋ refl |
                suc a + suc a * b ≡ suc (a + (b + a * b)) ∋ refl = eq2 where
        eq2 : suc (b + a * suc b) ≡ suc (a + (b + a * b))
        eq2 rewrite (mul_suc5 a b) = eq3 where
            eq3 : suc (b + (a + a * b)) ≡ suc (a + (b + a * b))
            eq3 rewrite (add_assoc b a (a * b)) | add_assoc a b (a * b) | add_comm a b = refl

mul_add : ∀ (t a b : ℕ) → t * (a + b) ≡ t * a + t * b
mul_add 0 a b = refl
mul_add (suc t) a b = eq1 where
    eq1 : suc t * (a + b) ≡ suc t * a + suc t * b
    eq1 rewrite suc t * (a + b) ≡ a + b + t * (a + b) ∋ refl |
                suc t * a ≡ a + t * a ∋ refl |
                suc t * b ≡ b + t * b ∋ refl = eq2 where
        eq2 : a + b + t * (a + b) ≡ a + t * a + (b + t * b)
        eq2 rewrite (mul_add t a b) = eq3 where
            eq3 : a + b + (t * a + t * b) ≡ a + t * a + (b + t * b)
            eq3 rewrite sym (add_assoc a (t * a) (b + t * b)) |
                        add_assoc (t * a) b (t * b) |
                        add_comm (t * a) b |
                        sym (add_assoc b (t * a) (t * b)) |
                        add_assoc a b (t * a + t * b) = refl

mul_comm : ∀ (a b : ℕ) → a * b ≡ b * a
mul_comm 0 b rewrite (0 * b ≡ 0 ∋ refl) |
    b * 0 ≡ 0 ∋ mul_zero b = refl
mul_comm (suc a) b = eq1 where
    eq1 : suc a * b ≡ b * suc a
    eq1 rewrite suc a * b ≡ b + a * b ∋ refl |
                b * suc a ≡ b + b * a ∋ mul_suc5 b a = eq2 where
        eq2 : b + a * b ≡ b + b * a
        eq2 rewrite mul_comm a b = refl

mul_left_comm : ∀ (a b c : ℕ) → c * b * a ≡ c * a * b
mul_left_comm a b c rewrite mul_assoc c b a |
    mul_assoc c a b |
    mul_comm a b = refl

zero_pow_zero : 0 ^ 0 ≡ 1
zero_pow_zero = refl

zero_pow_suc : ∀ (n : ℕ) → 0 ^ suc n ≡ 0
zero_pow_suc n = 0 ^ suc n
    ≡⟨ 0 ^ suc n ≡ 0 * 0 ^ n ∋ refl ⟩
    0 * 0 ^ n
    ≡⟨ 0 * 0 ^ n ≡ 0 ∋ refl ⟩
    0 ∎

pow_one : ∀ (a : ℕ) → a ^ 1 ≡ a
pow_one a = a ^ 1 ≡⟨ refl ⟩ a * a ^ 0 ≡⟨ eq1 ⟩ a ∎ where
    eq1 : a * a ^ 0 ≡ a
    eq1 rewrite a ^ 0 ≡ 1 ∋ refl |
                a * 1 ≡ a ∋ mul_one a = refl

one_pow : ∀ (n : ℕ) → 1 ^ n ≡ 1
one_pow 0 = refl
one_pow (suc n) = 1 ^ suc n ≡⟨ refl ⟩ 1 * 1 ^ n ≡⟨ one_mul (1 ^ n) ⟩ 1 ^ n ≡⟨ one_pow n ⟩ 1 ∎

pow_add : ∀ (a m n : ℕ) → a ^ (m + n) ≡ a ^ m * a ^ n
pow_add a 0 n = a ^ (0 + n)
    ≡⟨ refl ⟩
    a ^ n
    ≡⟨ eq1 ⟩
    1 * a ^ n
    ≡⟨ eq2 ⟩
    a ^ 0 * a ^ n ∎
    where
        eq1 : a ^ n ≡ 1 * a ^ n
        eq1 rewrite one_mul (a ^ n) = refl
        eq2 : 1 * a ^ n ≡ a ^ 0 * a ^ n
        eq2 rewrite a ^ 0 ≡ 1 ∋ refl = refl
pow_add a (suc m) n = a ^ (suc m + n)
    ≡⟨ refl ⟩
    a ^ suc (m + n)
    ≡⟨ refl ⟩
    a * a ^ (m + n)
    ≡⟨ eq1 ⟩
    a * (a ^ m * a ^ n)
    ≡⟨ sym (mul_assoc a (a ^ m) (a ^ n)) ⟩
    a * a ^ m * a ^ n
    ≡⟨ refl ⟩
    a ^ suc m * a ^ n ∎
    where
        eq1 : a * a ^ (m + n) ≡ a * (a ^ m * a ^ n)
        eq1 rewrite pow_add a m n = refl

mul_pow : ∀ (a b n : ℕ) → (a * b) ^ n ≡ a ^ n * b ^ n
mul_pow a b 0 = refl
mul_pow a b (suc n) =
    (a * b) ^ suc n
    ≡⟨ refl ⟩
    (a * b) * (a * b) ^ n
    ≡⟨ eq1 ⟩
    (a * b) * (a ^ n * b ^ n)
    ≡⟨ eq2 ⟩
    (a * a ^ n) * (b * b ^ n)
    ≡⟨ refl ⟩
    a ^ suc n * b ^ suc n ∎
    where
        eq1 : (a * b) * (a * b) ^ n ≡ (a * b) * (a ^ n * b ^ n)
        eq1 rewrite mul_pow a b n = refl
        eq2 : (a * b) * (a ^ n * b ^ n) ≡ (a * a ^ n) * (b * b ^ n)
        eq2 rewrite mul_assoc a b (a ^ n * b ^ n) |
                    sym (mul_assoc b (a ^ n) (b ^ n)) |
                    mul_comm b (a ^ n) |
                    mul_assoc (a ^ n) b (b ^ n) |
                    mul_assoc a (a ^ n) (b * b ^ n) = refl

pow_pow : ∀ (a m n : ℕ) → (a ^ m) ^ n ≡ a ^ (m * n)
pow_pow a m 0 =
    (a ^ m) ^ 0
    ≡⟨ refl ⟩
    1
    ≡⟨ eq1 ⟩
    a ^ (m * zero) ∎
    where
        eq1 : 1 ≡ a ^ (m * zero)
        eq1 rewrite mul_zero m = refl
pow_pow a m (suc n) =
    (a ^ m) ^ suc n
    ≡⟨ refl ⟩
    a ^ m * (a ^ m) ^ n
    ≡⟨ eq1 ⟩
    a ^ m * a ^ (m * n)
    ≡⟨ eq2 ⟩
    a ^ (m * suc n) ∎
    where
        eq1 : a ^ m * (a ^ m) ^ n ≡ a ^ m * a ^ (m * n)
        eq1 rewrite pow_pow a m n = refl
        eq2 : a ^ m * a ^ (m * n) ≡ a ^ (m * suc n)
        eq2 rewrite sym (pow_add a m (m * n)) |
                    mul_suc m n = refl

add_squared : ∀ (a b : ℕ) → (a + b) ^ 2 ≡ a ^ 2 + b ^ 2 + 2 * a * b
add_squared a b =
    (a + b) ^ 2
    ≡⟨ refl ⟩
    (a + b) * ((a + b) * 1)
    ≡⟨ eq1 ⟩
    (a + b) * (a + b)
    ≡⟨ mul_right_distrib a b (a + b) ⟩
    a * (a + b) + b * (a + b)
    ≡⟨ eq3 ⟩
    (a * a + b * a) + (a * b + b * b)
    ≡⟨ eq4 ⟩
    a * a + b * b + (b * a + a * b)
    ≡⟨ eq5 ⟩
    a ^ 2 + b ^ 2 + 2 * a * b ∎
    where
        eq1 : (a + b) * ((a + b) * 1) ≡ (a + b) * (a + b)
        eq1 rewrite mul_one (a + b) = refl
        eq3 : a * (a + b) + b * (a + b) ≡ (a * a + b * a) + (a * b + b * b)
        eq3 rewrite mul_comm a (a + b) |
                    mul_comm b (a + b) |
                    mul_right_distrib a b a |
                    mul_right_distrib a b b = refl
        eq4 : (a * a + b * a) + (a * b + b * b) ≡ a * a + b * b + (b * a + a * b)
        eq4 rewrite add_comm (a * b) (b * b) |
                    sym (add_assoc (a * a) (b * a) (b * b + a * b)) |
                    add_assoc (b * a) (b * b) (a * b) |
                    add_comm (b * a) (b * b) |
                    sym (add_assoc (b * b) (b * a) (a * b)) |
                    add_assoc (a * a) (b * b) (b * a + a * b) = refl
        eq5a : 2 * a * b ≡ a * b + a * b
        eq5a = 2 * a * b
            ≡⟨ refl ⟩
            (a + 1 * a) * b
            ≡⟨ eq5aa ⟩
            (a + a) * b
            ≡⟨ mul_right_distrib a a b ⟩
            a * b + a * b ∎ where
                eq5aa : (a + 1 * a) * b ≡ (a + a) * b
                eq5aa rewrite one_mul a = refl
        eq5 : a * a + b * b + (b * a + a * b) ≡ a ^ 2 + b ^ 2 + 2 * a * b
        eq5 rewrite eq5a | mul_one a | mul_one b | mul_comm a b = refl

and_sym : ∀ {A B : Set} → A × B → B × A
and_sym (a , b) = (b , a)

and_trans : ∀ {P Q R : Set} → P × Q → Q × R → P × R
and_trans (p , q1) (q2 , r) = (p , r)

record PropositionalEquivalence (A B : Set) : Set where
    constructor cons⇔
    field
        from : A → B
        to : B → A

_⇔_ : Set → Set → Set
A ⇔ B = PropositionalEquivalence A B

iff_trans : {P Q R : Set} → P ⇔ Q → Q ⇔ R → P ⇔ R
iff_trans (cons⇔ p→q q→p) (cons⇔ q→r r→q) =
    cons⇔ (λ x → q→r (p→q x)) (λ x → q→p (r→q x))

example⊎ : {P Q : Set} → Q → P ⊎ Q
example⊎ q = inj₂ q

or_sym : {P Q : Set} → (P ⊎ Q) ⇔ (Q ⊎ P)
or_sym {P} {Q} = cons⇔ f1 f2 where
    f1 : P ⊎ Q → Q ⊎ P
    f1 (inj₁ p) = inj₂ p
    f1 (inj₂ q) = inj₁ q
    f2 : Q ⊎ P → P ⊎ Q
    f2 (inj₁ q) = inj₂ q
    f2 (inj₂ p) = inj₁ p

and_or_distrib_left : {P Q R : Set} → (P × (Q ⊎ R)) ⇔ ((P × Q) ⊎ (P × R))
and_or_distrib_left {P} {Q} {R} = cons⇔ f1 f2 where
    f1 : (P × (Q ⊎ R)) → ((P × Q) ⊎ (P × R))
    f1 (p , q⊎r) = case q⊎r of λ {
        (inj₁ q) → inj₁ (p , q) ;
        (inj₂ r) → inj₂ (p , r) }
    f2 : ((P × Q) ⊎ (P × R)) → (P × (Q ⊎ R))
    f2 (inj₁ (p , q)) = (p , inj₁ q)
    f2 (inj₂ (p , r)) = (p , inj₂ r)

contra : {P Q : Set} → P × ¬ P → Q
contra (p , ¬p) = case ¬p p of λ {()}

suc_inj : ∀ {a b : ℕ} → suc a ≡ suc b → a ≡ b
suc_inj refl = refl

suc_suc_inj : ∀ {a b : ℕ} → suc (suc a) ≡ suc (suc b) → a ≡ b
suc_suc_inj refl = refl

suc_eq_suc_of_eq : ∀ {a b : ℕ} → a ≡ b → suc a ≡ suc b
suc_eq_suc_of_eq refl = refl

eq_iff_succ_eq_succ : ∀ {a b : ℕ} → (a ≡ b) ⇔ (suc a ≡ suc b)
eq_iff_succ_eq_succ = cons⇔ (λ {refl → refl}) (λ {refl → refl})

add_right_cancel : (a t b : ℕ) → a + t ≡ b + t → a ≡ b
add_right_cancel a 0 b eq1 = a
    ≡⟨ refl ⟩ 0 + a ≡⟨ add_comm 0 a ⟩ a + 0 ≡⟨ eq1 ⟩ b + 0
    ≡⟨ add_comm b 0 ⟩ 0 + b ≡⟨ refl ⟩ b ∎
add_right_cancel a (suc t) b eq1 = eq0 where
    eq2 : suc (a + t) ≡ suc (b + t)
    eq2 = suc (a + t) ≡⟨ eq1a a t ⟩ a + suc t ≡⟨ eq1 ⟩ b + suc t ≡˘⟨ eq1a b t ⟩ suc (b + t) ∎ where
        eq1a : (x y : ℕ) → suc (x + y) ≡ x + suc y
        eq1a x y rewrite add_comm x y | add_comm x (suc y) = refl
    eq3 : a + t ≡ b + t
    eq3 = (({x y : ℕ} → suc x ≡ suc y → x ≡ y) ∋ λ {refl → refl}) eq2
    eq0 : a ≡ b
    eq0 = add_right_cancel a t b eq3

add_left_cancel : {a t b : ℕ} → t + a ≡ t + b → a ≡ b
add_left_cancel {a} {t} {b} eq1 = eq3 where
    eq2 : a + t ≡ b + t
    eq2 rewrite add_comm a t | add_comm b t = eq1
    eq3 : a ≡ b
    eq3 = add_right_cancel a t b eq2

add_right_cancel_iff : (t a b : ℕ) → (a + t ≡ b + t) ⇔ (a ≡ b)
add_right_cancel_iff t a b = cons⇔ (add_right_cancel a t b) f2 where
    f2 : a ≡ b → a + t ≡ b + t
    f2 eq1 rewrite eq1 = refl

eq_zero_of_add_right_eq_self : {a b : ℕ} → a + b ≡ a → b ≡ 0
eq_zero_of_add_right_eq_self {a} {b} eq1 = eqN where
    eq2 : a + b ≡ a + 0
    eq2 = a + b ≡⟨ eq1 ⟩ a ≡⟨ refl ⟩ 0 + a ≡⟨ add_comm 0 a ⟩ a + 0 ∎
    eqN : b ≡ 0
    eqN = add_left_cancel eq2

test_ne : 0 ≢ 1
test_ne ()

zero_ne_suc : {a : ℕ} → 0 ≢ suc a
zero_ne_suc ()

suc_ne_zero : {a : ℕ} → suc a ≢ 0
suc_ne_zero ()

add_right_eq_zero : {a b : ℕ} → a + b ≡ 0 → a ≡ 0
add_right_eq_zero {zero} {zero} _ = refl

-- these are not necessary -- agda somehow infers
add_right_eq_zero {zero} {suc _} ()
add_right_eq_zero {suc _} {zero} ()
add_right_eq_zero {suc _} {suc _} ()

add_left_eq_zero : {a b : ℕ} → a + b ≡ 0 → b ≡ 0
add_left_eq_zero {zero} {zero} _ = refl

add_one_eq_suc : {d : ℕ} → suc d ≡ d + 1
add_one_eq_suc {d} rewrite add_comm d 1 = refl

-- what is this magic?
ne_suc_self : {n : ℕ} → n ≢ suc n
ne_suc_self ()

mul_either_zero : {a b : ℕ} → a * b ≡ 0 → a ≡ 0 ⊎ b ≡ 0
mul_either_zero {zero} {_} _ = inj₁ refl
mul_either_zero {_} {zero} _ = inj₂ refl

nonzero_mul_nonzero : {a b : ℕ} → a ≢ 0 → b ≢ 0 → a * b ≢ 0
nonzero_mul_nonzero {a} {b} a≢0 b≢0 ab≡0 = case (mul_either_zero ab≡0) of λ {
    (inj₁ a≡0) → a≢0 a≡0 ;
    (inj₂ b≡0) → b≢0 b≡0 }

mul_right_cancel : {a b c : ℕ} → a ≢ 0 → b * a ≡ c * a → b ≡ c
mul_right_cancel {0} {_} {_} a≢0 = case (a≢0 refl) of λ {()}
mul_right_cancel {suc a} {0} {0} _ _ = refl
mul_right_cancel {suc a} {0} {suc c} _ ()
mul_right_cancel {suc a} {suc b} {0} _ ()
mul_right_cancel {suc a} {suc b} {suc c} sa≢0 sbsa≡scsa = eqN where
    eq1 : suc (a + b * suc a) ≡ suc (a + c * suc a)
    eq1 = suc (a + b * suc a) ≡⟨ refl ⟩ suc b * suc a ≡⟨ sbsa≡scsa ⟩ suc c * suc a ≡⟨ refl ⟩ suc (a + c * suc a) ∎
    eq2 : b * suc a ≡ c * suc a
    eq2 = add_left_cancel (suc_inj eq1)
    eqN : suc b ≡ suc c
    eqN = cong suc (mul_right_cancel sa≢0 eq2)

_≤'_ : ℕ → ℕ → Set
a ≤' b = ∃ (λ x → x + a ≡ b)

one_add_le_self : ∀ (x : ℕ) → x ≤' (1 + x)
one_add_le_self x = 1 , refl

le_refl : ∀ (x : ℕ) → x ≤' x
le_refl x = 0 , refl

le_suc : ∀ (a b : ℕ) → a ≤' b → a ≤' suc b
le_suc a b (x , x+a≡b) = (1 + x , eqN) where
    eqN : (1 + x) + a ≡ suc b
    eqN = (1 + x) + a
        ≡⟨ add_assoc 1 x a ⟩
        1 + (x + a)
        ≡⟨ refl ⟩
        suc (x + a)
        ≡⟨ cong suc x+a≡b ⟩
        suc b ∎

zero_le : ∀ (a : ℕ) → 0 ≤' a
zero_le a = (a , add_comm a 0)

le_trans : ∀ {a b c : ℕ} → a ≤' b → b ≤' c → a ≤' c
le_trans {a} {b} {c} (d1 , d1+a≡b) (d2 , d2+b≡c) = (d2 + d1 , eqN) where
    eq1 : d2 + (d1 + a) ≡ d2 + b
    eq1 rewrite d1+a≡b = refl
    eqN : (d2 + d1) + a ≡ c
    eqN = (d2 + d1) + a
        ≡˘⟨ add_assoc d2 d1 a ⟩
        d2 + (d1 + a)
        ≡⟨ eq1 ⟩
        d2 + b
        ≡⟨ d2+b≡c ⟩
        c ∎

le_antisym : ∀ {a b : ℕ} → a ≤' b → b ≤' a → a ≡ b
le_antisym {a} {b} (d1 , d1+a≡b) (d2 , d2+b≡a) = eqN where
    eq1_a : d2 + (d1 + a) ≡ d2 + b
    eq1_a rewrite d1+a≡b = refl
    eq1 : (d2 + d1) + a ≡ a
    eq1 = (d2 + d1) + a
        ≡˘⟨ add_assoc d2 d1 a ⟩
        d2 + (d1 + a)
        ≡⟨ eq1_a ⟩
        d2 + b
        ≡⟨ d2+b≡a ⟩
        a ∎
    eq2 : d2 + d1 ≡ 0
    eq2 = add_right_cancel (d2 + d1) a 0 eq1    -- TODO is it possible to do inline?
    eq3 : d2 ≡ 0
    eq3 = add_right_eq_zero eq2     -- TODO is it possible to do inline?
    eq4 : d2 + b ≡ b
    eq4 rewrite eq3 = refl
    eqN : a ≡ b
    eqN = a ≡˘⟨ d2+b≡a ⟩ d2 + b ≡⟨ eq4 ⟩ b ∎

le_zero : ∀ {a : ℕ} → a ≤' 0 → a ≡ 0
le_zero {a} (zero , 0+a≡0) = 0+a≡0
le_zero {a} (suc d , ())

suc_le_suc : ∀ {a b : ℕ} → a ≤' b → suc a ≤' suc b
suc_le_suc {a} {b} (d , d+a≡b) = (d , eqN) where
    eqN : d + suc a ≡ suc b
    eqN = d + suc a
        ≡⟨ add_comm d (suc a) ⟩
        suc a + d
        ≡⟨ refl ⟩
        suc (a + d)
        ≡⟨ cong suc (add_comm a d) ⟩
        suc (d + a)
        ≡⟨ cong suc d+a≡b ⟩
        suc b ∎

le_total : ∀ (a b : ℕ) → a ≤' b ⊎ b ≤' a
le_total zero b = inj₁ (b , add_comm b 0)
le_total a zero = inj₂ (a , add_comm a 0)
le_total (suc a) (suc b) = case (le_total a b) of λ {
    (inj₁ a≤b) → inj₁ (suc_le_suc a≤b) ;
    (inj₂ b≤a) → inj₂ (suc_le_suc b≤a) }

le_suc_self : ∀ (a : ℕ) → a ≤' suc a
le_suc_self a = (1 , refl)

add_le_add_left : ∀ {a b : ℕ} → a ≤' b → ∀ (t : ℕ) → (t + a) ≤' (t + b)
add_le_add_left {a} {b} a≤b zero = a≤b
add_le_add_left {a} {b} a≤b (suc t) = suc_le_suc (add_le_add_left a≤b t)

le_of_suc_le_suc : ∀ {a b : ℕ} → suc a ≤' suc b → a ≤' b
le_of_suc_le_suc {a} {b} (d , d+sa≡sb) = (d , d+a≡b) where
    eq1 : suc (d + a) ≡ suc b
    eq1 = suc (d + a)
        ≡⟨ cong suc (add_comm d a) ⟩
        suc (a + d)
        ≡⟨ refl ⟩
        suc a + d
        ≡⟨ add_comm (suc a) d ⟩
        d + suc a
        ≡⟨ d+sa≡sb ⟩
        suc b ∎
    d+a≡b : d + a ≡ b
    d+a≡b = suc_inj eq1

not_suc_le_self : ∀ {a : ℕ} → ¬(suc a ≤' a)
not_suc_le_self {a} sa≤a = case (le_antisym (le_suc_self a) sa≤a) of λ {()}

add_le_add_right : ∀ {a b : ℕ} → a ≤' b → ∀ (t : ℕ) → (a + t) ≤' (b + t)
add_le_add_right {a} {b} a≤b t rewrite (add_comm a t) | (add_comm b t) = add_le_add_left a≤b t

lt_aux_one : ∀ {a b : ℕ} → a ≤' b × ¬(b ≤' a) → suc a ≤' b
lt_aux_one {a} {b} (a≤b , ¬b≤a) with a≤b
... | (zero , a≡b) = case (¬b≤a (0 , sym a≡b)) of λ {()}
... | (suc d , sd+a≡b) = (d , d+sa≡b) where
    d+sa≡b : d + suc a ≡ b
    d+sa≡b = d + suc a
        ≡⟨ add_comm d (suc a) ⟩
        -- suc a + d
        -- ≡⟨ refl ⟩
        suc (a + d)
        ≡⟨ cong suc (add_comm a d) ⟩
        -- suc (d + a)
        -- ≡⟨ refl ⟩
        suc d + a
        ≡⟨ sd+a≡b ⟩
        b ∎

lt_aux_two : ∀ {a b : ℕ} → suc a ≤' b → a ≤' b × ¬(b ≤' a)
lt_aux_two {a} {b} sa≤b = (a≤b , ¬b≤a) where
    a≤b : a ≤' b
    a≤b = le_trans (le_suc_self a) sa≤b
    ¬b≤a : ¬(b ≤' a)
    ¬b≤a b≤a = case (not_suc_le_self (le_trans sa≤b b≤a)) of λ {()}

_<'_ : ℕ → ℕ → Set
a <' b = a ≤' b × ¬(b ≤' a)

lt_iff_suc_le : ∀ (a b : ℕ) → (a <' b) ⇔ (suc a ≤' b)
lt_iff_suc_le a b = cons⇔ lt_aux_one lt_aux_two