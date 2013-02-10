module Gen_J where

open import Function
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; cong; sym; trans; subst₂)

open import Basics_J
open import Lists_J
open import Poly_J

-- doubleの単射とかgeneralize dependent関するギロンに対してはやることないかな


{-
練習問題: ★★★ (gen_dep_practice)

mに関する帰納法で以下を示しなさい。
-}
n+n-injective-take2 : ∀{n m} → n + n ≡ m + m → n ≡ m
n+n-injective-take2 {n} {0} eq = n+n-injective-take2-0 {n} eq
  where
    n+n-injective-take2-0 : ∀{n} → n + n ≡ 0 + 0 → n ≡ 0
    n+n-injective-take2-0 {0} refl = refl
    n+n-injective-take2-0 {S n} ()
n+n-injective-take2 {n} {S m} eq = n+n-injective-take2-Sm {n} eq
  where
    n+n-injective-take2-Sm : ∀{n} → n + n ≡ S m + S m → n ≡ S m
    n+n-injective-take2-Sm {0} ()
    n+n-injective-take2-Sm {S n} eq = cong S $ ind $ drop-S2 $ drop-S1 $ toSS eq
      where
        ind = n+n-injective-take2 {n} {m}
        drop-S1 = eq-add-S {S (n + n)} {S (m + m)}
        drop-S2 = eq-add-S {n + n} {m + m}
        toSS = subst₂ (_≡_) (Sn+Sn≡SSn+n {n}) (Sn+Sn≡SSn+n {m})

index-after-last : ∀{x} {X : Set x} →
                   (n : nat) → (xs : list X) →
                   length xs ≡ n → index (S n) xs ≡ None
index-after-last n [] eq = refl
index-after-last n (x ∷ xs) eq = index-after-last' n eq
  where
    index-after-last' : (n : nat) → length (x ∷ xs) ≡ n → index (S n) (x ∷ xs) ≡ None
    index-after-last' 0 ()
    index-after-last' (S n) eq = index-after-last n xs $ eq-add-S eq

{-
練習問題: ★★★, optional (index_after_last_informal)

index_after_lastのCoqによる証明に対応する非形式的な証明を書きなさい。
-}
-- 略

{-
練習問題: ★★★, optional (gen_dep_practice_opt)

lに関する帰納法で示しなさい。
-}
length-snoc : ∀{x} {X : Set x} →
                 (n : nat) → (v : X) → (xs : list X) →
                 length xs ≡ n → length (snoc xs v) ≡ S n
length-snoc {x} {X} n v [] eq = length-snoc-[] {x} {X} n eq
  where
    length-snoc-[] : ∀ {x} {X} → (n : nat) → length {x} {X} [] ≡ n → length (snoc [] v) ≡ S n
    length-snoc-[] 0 eq₁ = refl
    length-snoc-[] (S n₁) ()
length-snoc n v (x ∷ xs) eq = length-snoc-∷ n eq
  where
    length-snoc-∷ : (n : nat) → length (x ∷ xs) ≡ n → length (snoc (x ∷ xs) v) ≡ S n
    length-snoc-∷ 0 ()
    length-snoc-∷ (S n₁) eq₁
      rewrite length-snoc n₁ v xs (eq-add-S eq₁)
            = refl

{-
練習問題: ★★★, optional (app_length_cons)

app_lengthを使わずにl1に関する帰納法で示しなさい。
-}
app-length-cons : ∀{x} {X : Set x} →
              (l1 l2 : list X) → (x : X) → (n : nat) →
              length (l1 ++ (x ∷ l2)) ≡ n → S (length (l1 ++ l2)) ≡ n
app-length-cons [] l2 x n eq = eq
app-length-cons (l ∷ l1) l2 x n eq
  rewrite app-length-cons l1 l2 x (length (l1 ++ x ∷ l2)) refl
        | eq
        = refl

{-
練習問題: ★★★★, optional (app_length_twice)

app_lengthを使わずにl1に関する帰納法で示しなさい。
-}
app-length-twice : ∀{x} {X : Set x} →
                  (n : nat) → (ls : list X) →
                  length ls ≡ n → length (ls ++ ls) ≡ n + n
app-length-twice {x} {X} n [] eq = app-length-twice-[] {x} {X} n eq
  where
    app-length-twice-[] : ∀{x} {X : Set x} → (n : nat) → length {x} {X} [] ≡ n → length {x} {X} ([] ++ []) ≡ n + n
    app-length-twice-[] 0 eq₁ = refl
    app-length-twice-[] (S n₁) ()
app-length-twice n (l ∷ ls) eq = app-length-twice-∷ n eq
  where
    app-length-twice-∷ : (n : nat) → length (l ∷ ls) ≡ n → length ((l ∷ ls) ++ (l ∷ ls)) ≡ n + n
    app-length-twice-∷ 0 ()
    app-length-twice-∷ (S n₁) eq₁
      rewrite sym (app-length-cons ls ls l (length (ls ++ l ∷ ls)) refl)
            | app-length-twice n₁ ls (eq-add-S {length ls} {n₁} eq₁)
            | plus-comm (S n₁) (n₁)
            = refl
