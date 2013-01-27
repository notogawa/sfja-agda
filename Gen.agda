module Gen where

open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst₂)
open import Function


-- doubleの単射とかgeneralize dependent関するギロンに対してはやることないかな


{-
練習問題: ★★★ (gen_dep_practice)

mに関する帰納法で以下を示しなさい。
-}
-- 再定義から
+-assoc : {n m p : ℕ} → n + (m + p) ≡ (n + m) + p
+-assoc {0} = refl
+-assoc {suc n} = cong suc (+-assoc {n})

0+n≡n : {n : ℕ} → 0 + n ≡ n
0+n≡n = refl

n+0≡n : {n : ℕ} → n + 0 ≡ n
n+0≡n {0} = refl
n+0≡n {suc n} = cong suc (n+0≡n {n})

+-comm : {n m : ℕ} → n + m ≡ m + n
+-comm {0}     {m} = 0+n≡n {m} ⟨ trans ⟩ sym (n+0≡n {m})
+-comm {suc n} {m} = cong suc (+-comm {n} {m}) ⟨ trans ⟩ Sn+m≡n+Sm {m} {n}
  where
    Sn+m≡n+Sm : {n m : ℕ} → suc (n + m) ≡ n + (suc m)
    Sn+m≡n+Sm {0}   {m} = refl
    Sn+m≡n+Sm {suc n} {m} = cong suc (Sn+m≡n+Sm {n} {m})

suc-inversion : ∀{n m} → suc n ≡ suc m → n ≡ m
suc-inversion {.m} {m} refl = refl

Sn+Sn≡SSn+n : ∀{n} → suc n + suc n ≡ suc (suc (n + n))
Sn+Sn≡SSn+n {n} = +-assoc {suc n} {1} {n} ⟨ trans ⟩ cong (λ a → suc (a + n)) (+-comm {n} {1})

n+n-injective-take2 : ∀{n m} → n + n ≡ m + m → n ≡ m
n+n-injective-take2 {n} {zero} eq = n+n-injective-take2-0 {n} eq
  where
    n+n-injective-take2-0 : ∀{n} → n + n ≡ 0 + 0 → n ≡ 0
    n+n-injective-take2-0 {zero} refl = refl
    n+n-injective-take2-0 {suc n} ()
n+n-injective-take2 {n} {suc m} eq = n+n-injective-take2-Sm {n} eq
  where
    n+n-injective-take2-Sm : ∀{n} → n + n ≡ suc m + suc m → n ≡ suc m
    n+n-injective-take2-Sm {zero} ()
    n+n-injective-take2-Sm {suc n} eq = cong suc $ ind $ drop-suc2 $ drop-suc1 $ toSS eq
      where
        ind = n+n-injective-take2 {n} {m}
        drop-suc1 = suc-inversion {suc (n + n)} {suc (m + m)}
        drop-suc2 = suc-inversion {n + n} {m + m}
        toSS = subst₂ (_≡_) (Sn+Sn≡SSn+n {n}) (Sn+Sn≡SSn+n {m})

-- 再定義
ℕ-eq : ℕ → ℕ → Bool
ℕ-eq zero zero = true
ℕ-eq zero (suc m) = false
ℕ-eq (suc n) zero = false
ℕ-eq (suc n) (suc m) = ℕ-eq n m

ℕ-eq-refl : (n : ℕ) → ℕ-eq n n ≡ true
ℕ-eq-refl 0 = refl
ℕ-eq-refl (suc n) = ℕ-eq-refl n

ℕ-eq-sym : (n m : ℕ) → ℕ-eq n m ≡ ℕ-eq m n
ℕ-eq-sym 0 0 = refl
ℕ-eq-sym 0 (suc m) = refl
ℕ-eq-sym (suc n) 0 = refl
ℕ-eq-sym (suc n) (suc m) = ℕ-eq-sym n m

-- option を Maybe に
index : ∀{x} {X : Set x} → ℕ → List X → Maybe X
index n [] = nothing
index n (x ∷ xs) = if ℕ-eq 0 n then just x else index (pred n) xs

index-after-last : ∀{x} {X : Set x} →
                   (n : ℕ) → (xs : List X) →
                   length xs ≡ n → index (suc n) xs ≡ nothing
index-after-last n [] eq = refl
index-after-last n (x ∷ xs) eq = index-after-last' n eq
  where
    index-after-last' : (n : ℕ) → length (x ∷ xs) ≡ n → index (suc n) (x ∷ xs) ≡ nothing
    index-after-last' zero ()
    index-after-last' (suc n) eq = index-after-last n xs $ suc-inversion eq

{-
練習問題: ★★★, optional (index_after_last_informal)

index_after_lastのCoqによる証明に対応する非形式的な証明を書きなさい。
-}
-- 略

{-
練習問題: ★★★, optional (gen_dep_practice_opt)

lに関する帰納法で示しなさい。
-}
length-∷ʳ : ∀{x} {X : Set x} →
                 (n : ℕ) → (v : X) → (xs : List X) →
                 length xs ≡ n → length (xs ∷ʳ v) ≡ suc n
length-∷ʳ {x} {X} n v [] eq = length-∷ʳ-[] {x} {X} n eq
  where
    length-∷ʳ-[] : ∀ {x} {X} → (n : ℕ) → length {x} {X} [] ≡ n → length ([] ∷ʳ v) ≡ suc n
    length-∷ʳ-[] zero eq₁ = refl
    length-∷ʳ-[] (suc n₁) ()
length-∷ʳ n v (x ∷ xs) eq = length-∷ʳ-∷ n eq
  where
    length-∷ʳ-∷ : (n : ℕ) → length (x ∷ xs) ≡ n → length ((x ∷ xs) ∷ʳ v) ≡ suc n
    length-∷ʳ-∷ zero ()
    length-∷ʳ-∷ (suc n₁) eq₁ =
        begin
           length ((x ∷ xs) ∷ʳ v)
        ≡⟨ refl ⟩
           suc (length (xs ++ v ∷ []))
        ≡⟨ cong suc (length-++ xs) ⟩
           suc (length xs + 1)
        ≡⟨ cong suc (+-comm {length xs} {1}) ⟩
           suc (1 + length xs)
        ≡⟨ refl ⟩
           suc (length (x ∷ xs))
        ≡⟨ cong suc eq₁ ⟩
           suc (suc n₁)
        ∎
        where
          open Relation.Binary.PropositionalEquality.≡-Reasoning
          open import Data.List.Properties

{-
練習問題: ★★★, optional (app_length_cons)

app_lengthを使わずにl1に関する帰納法で示しなさい。
-}
++-length-∷ : ∀{x} {X : Set x} →
              (l1 l2 : List X) → (x : X) → (n : ℕ) →
              length (l1 ++ (x ∷ l2)) ≡ n → suc (length (l1 ++ l2)) ≡ n
++-length-∷ [] l2 x n eq = eq
++-length-∷ (l ∷ l1) l2 x n eq =
  begin
     suc (length ((l ∷ l1) ++ l2))
  ≡⟨ refl ⟩
     suc (suc (length (l1 ++ l2)))
  ≡⟨ cong suc (++-length-∷ l1 l2 x (length (l1 ++ x ∷ l2)) refl) ⟩
     length ((l ∷ l1) ++ (x ∷ l2))
  ≡⟨ eq ⟩
     n
  ∎
  where
    open Relation.Binary.PropositionalEquality.≡-Reasoning

{-
練習問題: ★★★★, optional (app_length_twice)

app_lengthを使わずにl1に関する帰納法で示しなさい。
-}
++-length-twice : ∀{x} {X : Set x} →
                  (n : ℕ) → (ls : List X) →
                  length ls ≡ n → length (ls ++ ls) ≡ n + n
++-length-twice {x} {X} n [] eq = ++-length-twice-[] {x} {X} n eq
  where
    ++-length-twice-[] : ∀{x} {X : Set x} → (n : ℕ) → length {x} {X} [] ≡ n → length {x} {X} ([] ++ []) ≡ n + n
    ++-length-twice-[] zero eq₁ = refl
    ++-length-twice-[] (suc n₁) ()
++-length-twice n (l ∷ ls) eq = ++-length-twice-∷ n eq
  where
    ++-length-twice-∷ : (n : ℕ) → length (l ∷ ls) ≡ n → length ((l ∷ ls) ++ (l ∷ ls)) ≡ n + n
    ++-length-twice-∷ zero ()
    ++-length-twice-∷ (suc n₁) eq₁ =
      begin
         length ((l ∷ ls) ++ (l ∷ ls))
      ≡⟨ refl ⟩
         suc (length (ls ++ l ∷ ls))
      ≡⟨ cong suc (sym (++-length-∷ ls ls l (length (ls ++ l ∷ ls)) refl)) ⟩
         suc (suc (length (ls ++ ls)))
      ≡⟨ cong (suc ∘ suc) (++-length-twice n₁ ls (suc-inversion {length ls} {n₁} eq₁)) ⟩
         suc (suc (n₁ + n₁))
      ≡⟨ refl ⟩
         suc (suc n₁ + n₁)
      ≡⟨ cong suc (+-comm {suc n₁} {n₁}) ⟩
         suc n₁ + suc n₁
      ∎
      where
        open Relation.Binary.PropositionalEquality.≡-Reasoning
