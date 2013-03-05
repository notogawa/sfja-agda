module Imp-J where

------ Sflib ------------------------------------------------------------------
open import SfLib-J

-- 算術式とブール式 -----------------------------------------------------------
module AExp where

---- 構文 ---------------------------------------------------------------------
  data aexp : Set where
    ANum : ℕ → aexp
    APlus : aexp → aexp → aexp
    AMinus : aexp → aexp → aexp
    AMult : aexp → aexp → aexp

  data bexp : Set where
    BTrue : bexp
    BFalse : bexp
    BEq : aexp → aexp → bexp
    BLe : aexp → aexp → bexp
    BNot : bexp → bexp
    BAnd : bexp → bexp → bexp

---- 評価 ---------------------------------------------------------------------
  aeval : aexp → ℕ
  aeval (ANum n) = n
  aeval (APlus exp₁ exp₂) = aeval exp₁ + aeval exp₂
  aeval (AMinus exp₁ exp₂) = aeval exp₁ ∸ aeval exp₂
  aeval (AMult exp₁ exp₂) = aeval exp₁ * aeval exp₂

  test-aeval1 : aeval (APlus (ANum 2) (ANum 2)) ≡ 4
  test-aeval1 = refl

  beval : bexp → Bool
  beval BTrue = true
  beval BFalse = false
  beval (BEq exp₁ exp₂) = beq-nat (aeval exp₁) (aeval exp₂)
  beval (BLe exp₁ exp₂) = ble-nat (aeval exp₁) (aeval exp₂)
  beval (BNot exp) = not (beval exp)
  beval (BAnd exp₁ exp₂) = beval exp₁ ∧ beval exp₂

---- 最適化(Optimization) -----------------------------------------------------
  optimize-0plus : aexp → aexp
  optimize-0plus (ANum n) = ANum n
  optimize-0plus (APlus (ANum 0) exp₂) = optimize-0plus exp₂
  optimize-0plus (APlus exp₁ exp₂) = APlus (optimize-0plus exp₁) (optimize-0plus exp₂)
  optimize-0plus (AMinus exp₁ exp₂) = AMinus (optimize-0plus exp₁) (optimize-0plus exp₂)
  optimize-0plus (AMult exp₁ exp₂) = AMult (optimize-0plus exp₁) (optimize-0plus exp₂)

  test-optimize-0plus : optimize-0plus
                          (APlus (ANum 2) (APlus (ANum 0) (APlus (ANum 0) (ANum 1))))
                          ≡ APlus (ANum 2) (ANum 1)
  test-optimize-0plus = refl

  optimize-0plus-sound : ∀ e → aeval (optimize-0plus e) ≡ aeval e
  optimize-0plus-sound (ANum x) = refl
  optimize-0plus-sound (APlus (ANum zero) exp₂) = optimize-0plus-sound exp₂
  optimize-0plus-sound (APlus (ANum (suc n)) exp₂)
    rewrite optimize-0plus-sound exp₂
          = refl
  optimize-0plus-sound (APlus (APlus exp₁ exp₂) exp₃)
    rewrite optimize-0plus-sound (APlus exp₁ exp₂)
          | optimize-0plus-sound exp₃
          = refl
  optimize-0plus-sound (APlus (AMinus exp₁ exp₂) exp₃)
    rewrite optimize-0plus-sound (AMinus exp₁ exp₂)
          | optimize-0plus-sound exp₃
          = refl
  optimize-0plus-sound (APlus (AMult exp₁ exp₂) exp₃)
    rewrite optimize-0plus-sound (AMult exp₁ exp₂)
          | optimize-0plus-sound exp₃
          = refl
  optimize-0plus-sound (AMinus exp₁ exp₂)
    rewrite optimize-0plus-sound exp₁
          | optimize-0plus-sound exp₂
          = refl
  optimize-0plus-sound (AMult exp₁ exp₂)
    rewrite optimize-0plus-sound exp₁
          | optimize-0plus-sound exp₂
          = refl

-- Coq の自動化 ---------------------------------------------------------------

-- このへんからAgdaだとキツくなってくる予感

---- タクティカル(Tacticals) --------------------------------------------------

------ tryタクティカル --------------------------------------------------------

------ ;タクティカル ----------------------------------------------------------

--- NEEEEEEEEEEEEEEEEEEE

---- 新しいタクティック記法を定義する -----------------------------------------
----- 場合分けを万全にする ----------------------------------------------------

{-
練習問題: ★★★ (optimize_0plus_b)

optimize_0plusの変換がaexpの値を変えないことから、 bexpの値を変えずに、bexpに現れるaexpをすべて変換するために optimize_0plusが適用できるべきでしょう。 bexpについてこの変換をする関数を記述しなさい。そして、 それが健全であることを証明しなさい。 ここまで見てきたタクティカルを使って証明を可能な限りエレガントにしなさい。
-}
  optimize-0plus-b : bexp → bexp
  optimize-0plus-b BTrue = BTrue
  optimize-0plus-b BFalse = BFalse
  optimize-0plus-b (BEq exp₁ exp₂) = BEq (optimize-0plus exp₁) (optimize-0plus exp₂)
  optimize-0plus-b (BLe exp₁ exp₂) = BLe (optimize-0plus exp₁) (optimize-0plus exp₂)
  optimize-0plus-b (BNot exp) = BNot (optimize-0plus-b exp)
  optimize-0plus-b (BAnd exp₁ exp₂) = BAnd (optimize-0plus-b exp₁) (optimize-0plus-b exp₂)

  optimize-0plus-b-sound : ∀ e → beval (optimize-0plus-b e) ≡ beval e
  optimize-0plus-b-sound BTrue = refl
  optimize-0plus-b-sound BFalse = refl
  optimize-0plus-b-sound (BEq exp₁ exp₂)
    rewrite optimize-0plus-sound exp₁
          | optimize-0plus-sound exp₂
          = refl
  optimize-0plus-b-sound (BLe exp₁ exp₂)
    rewrite optimize-0plus-sound exp₁
          | optimize-0plus-sound exp₂
          = refl
  optimize-0plus-b-sound (BNot exp₁)
    rewrite optimize-0plus-b-sound exp₁
          = refl
  optimize-0plus-b-sound (BAnd exp₁ exp₂)
    rewrite optimize-0plus-b-sound exp₁
          | optimize-0plus-b-sound exp₂
          = refl
{-
練習問題: ★★★★, optional (optimizer)

設計練習: 定義したoptimize_0plus関数で実装された最適化は、 算術式やブール式に対して考えられるいろいろな最適化の単なる1つに過ぎません。 より洗練された最適化関数を記述し、その正しさを証明しなさい。
-}
  optimize-false-and-b : bexp → bexp
  optimize-false-and-b BTrue = BTrue
  optimize-false-and-b BFalse = BFalse
  optimize-false-and-b (BEq exp₁ exp₂) = BEq exp₁ exp₂
  optimize-false-and-b (BLe exp₁ exp₂) = BLe exp₁ exp₂
  optimize-false-and-b (BNot exp₁) = BNot (optimize-false-and-b exp₁)
  optimize-false-and-b (BAnd BTrue exp₂) = exp₂
  optimize-false-and-b (BAnd BFalse exp₂) = BFalse
  optimize-false-and-b (BAnd exp₁ exp₂) = BAnd (optimize-false-and-b exp₁) (optimize-false-and-b exp₂)

  optimize-false-and-b-sound : ∀ e → beval (optimize-false-and-b e) ≡ beval e
  optimize-false-and-b-sound BTrue = refl
  optimize-false-and-b-sound BFalse = refl
  optimize-false-and-b-sound (BEq x x₁) = refl
  optimize-false-and-b-sound (BLe x x₁) = refl
  optimize-false-and-b-sound (BNot exp₁)
    rewrite optimize-false-and-b-sound exp₁
          = refl
  optimize-false-and-b-sound (BAnd BTrue exp₂) = refl
  optimize-false-and-b-sound (BAnd BFalse exp₂) = refl
  optimize-false-and-b-sound (BAnd (BEq x x₁) exp₂)
    rewrite optimize-false-and-b-sound exp₂
          = refl
  optimize-false-and-b-sound (BAnd (BLe x x₁) exp₂)
    rewrite optimize-false-and-b-sound exp₂
          = refl
  optimize-false-and-b-sound (BAnd (BNot exp₁) exp₂)
    rewrite optimize-false-and-b-sound (BNot exp₁)
          | optimize-false-and-b-sound exp₂
          = refl
  optimize-false-and-b-sound (BAnd (BAnd exp₁ exp₂) exp₃)
    rewrite optimize-false-and-b-sound (BAnd exp₁ exp₂)
          | optimize-false-and-b-sound exp₃
          = refl

---- omegaタクティック --------------------------------------------------------
--- 甘え

---- 便利なタクティックをさらにいくつか ---------------------------------------
--- 甘え

-- 関係としての評価 -----------------------------------------------------------
  module aevalR-first-try where

    data aevalR : aexp → ℕ → Set where
      E-ANum : ∀ n → aevalR (ANum n) n
      E-APlus : ∀ e1 e2 n1 n2 → aevalR e1 n1 → aevalR e2 n2 → aevalR (APlus e1 e2) (n1 + n2)
      E-AMinus : ∀ e1 e2 n1 n2 → aevalR e1 n1 → aevalR e2 n2 → aevalR (AMinus e1 e2) (n1 ∸ n2)
      E-AMult : ∀ e1 e2 n1 n2 → aevalR e1 n1 → aevalR e2 n2 → aevalR (AMult e1 e2) (n1 * n2)

    _⇓_ = aevalR

  data _aeval⇓_ : aexp → ℕ → Set where
    E-ANum : ∀ n → ANum n aeval⇓ n
    E-APlus : ∀ e1 e2 n1 n2 → e1 aeval⇓ n1 → e2 aeval⇓ n2 → APlus e1 e2 aeval⇓ (n1 + n2)
    E-AMinus : ∀ e1 e2 n1 n2 → e1 aeval⇓ n1 → e2 aeval⇓ n2 → AMinus e1 e2 aeval⇓ (n1 ∸ n2)
    E-AMult : ∀ e1 e2 n1 n2 → e1 aeval⇓ n1 → e2 aeval⇓ n2 → AMult e1 e2 aeval⇓ (n1 * n2)

  open import Function.Equivalence hiding (sym)

  aeval-iff-aeval⇓ : ∀ a n → (a aeval⇓ n) ⇔ aeval a ≡ n
  aeval-iff-aeval⇓ = λ a n → equivalence (left a n) (right a n)
    where
      left : ∀ a n → a aeval⇓ n → aeval a ≡ n
      left .(ANum b) b (E-ANum .b) = refl
      left .(APlus e1 e2) .(n1 + n2) (E-APlus e1 e2 n1 n2 aaeval⇓n aaeval⇓n₁)
        rewrite left e1 n1 aaeval⇓n
              | left e2 n2 aaeval⇓n₁
              = refl
      left .(AMinus e1 e2) .(n1 ∸ n2) (E-AMinus e1 e2 n1 n2 aaeval⇓n aaeval⇓n₁)
        rewrite left e1 n1 aaeval⇓n
              | left e2 n2 aaeval⇓n₁
              = refl
      left .(AMult e1 e2) .(n1 * n2) (E-AMult e1 e2 n1 n2 aaeval⇓n aaeval⇓n₁)
        rewrite left e1 n1 aaeval⇓n
              | left e2 n2 aaeval⇓n₁
              = refl
      right : ∀ a n → aeval a ≡ n → a aeval⇓ n
      right (ANum x) n eq
        rewrite eq
              = E-ANum n
      right (APlus a a₁) n eq
        rewrite sym eq
              = E-APlus a a₁ (aeval a) (aeval a₁) (right a (aeval a) refl)
                  (right a₁ (aeval a₁) refl)
      right (AMinus a a₁) n eq
        rewrite sym eq
              = E-AMinus a a₁ (aeval a) (aeval a₁) (right a (aeval a) refl)
                  (right a₁ (aeval a₁) refl)
      right (AMult a a₁) n eq
        rewrite sym eq
              = E-AMult a a₁ (aeval a) (aeval a₁) (right a (aeval a) refl)
                  (right a₁ (aeval a₁) refl)
{-
練習問題: ★★, optional (bevalR)

関係bevalRをaevalRと同じスタイルで記述し、 それがbevalと同値であることを証明しなさい。
-}
  data _beval⇓_ : bexp → Bool → Set where
    E-BTrue : BTrue beval⇓ true
    E-BFalse : BFalse beval⇓ false
    E-BEq : ∀ e1 e2 n1 n2 → e1 aeval⇓ n1 → e2 aeval⇓ n2 → BEq e1 e2 beval⇓ (beq-nat n1 n2)
    E-BLe : ∀ e1 e2 n1 n2 → e1 aeval⇓ n1 → e2 aeval⇓ n2 → BLe e1 e2 beval⇓ (ble-nat n1 n2)
    E-BNot : ∀ e b → e beval⇓ b → BNot e beval⇓ (not b)
    E-BAnd : ∀ e1 e2 b1 b2 → e1 beval⇓ b1 → e2 beval⇓ b2 → BAnd e1 e2 beval⇓ (b1 ∧ b2)

  open import Function.Equality

  beval-iff-beval⇓ : ∀ e b → (e beval⇓ b) ⇔ beval e ≡ b
  beval-iff-beval⇓ = λ e b → equivalence (left e b) (right e b)
    where
      left : ∀ e b → e beval⇓ b → beval e ≡ b
      left .BTrue .true E-BTrue = refl
      left .BFalse .false E-BFalse = refl
      left .(BEq e1 e2) .(beq-nat n1 n2) (E-BEq e1 e2 n1 n2 x x₁)
        rewrite Equivalence.to (aeval-iff-aeval⇓ e1 n1) Π.⟨$⟩ x
              | Equivalence.to (aeval-iff-aeval⇓ e2 n2) Π.⟨$⟩ x₁
              = refl
      left .(BLe e1 e2) .(ble-nat n1 n2) (E-BLe e1 e2 n1 n2 x x₁)
        rewrite Equivalence.to (aeval-iff-aeval⇓ e1 n1) Π.⟨$⟩ x
              | Equivalence.to (aeval-iff-aeval⇓ e2 n2) Π.⟨$⟩ x₁
              = refl
      left .(BNot e) .(not b) (E-BNot e b e⇓b)
        rewrite left e b e⇓b
              = refl
      left .(BAnd e1 e2) .(b1 ∧ b2) (E-BAnd e1 e2 b1 b2 e⇓b e⇓b₁)
        rewrite left e1 b1 e⇓b
              | left e2 b2 e⇓b₁
              = refl
      right : ∀ e b → beval e ≡ b → e beval⇓ b
      right BTrue b eq rewrite sym eq = E-BTrue
      right BFalse b eq rewrite sym eq = E-BFalse
      right (BEq x x₁) b eq
        rewrite sym eq
              = E-BEq x x₁ (aeval x) (aeval x₁)
                  (Equivalence.from (aeval-iff-aeval⇓ x (aeval x)) ⟨$⟩ refl)
                  (Equivalence.from (aeval-iff-aeval⇓ x₁ (aeval x₁)) ⟨$⟩ refl)
      right (BLe x x₁) b eq
        rewrite sym eq
              = E-BLe x x₁ (aeval x) (aeval x₁)
                  (Equivalence.from (aeval-iff-aeval⇓ x (aeval x)) ⟨$⟩ refl)
                  (Equivalence.from (aeval-iff-aeval⇓ x₁ (aeval x₁)) ⟨$⟩ refl)
      right (BNot e) b eq
        rewrite sym eq
              = E-BNot e (beval e) (right e (beval e) refl)
      right (BAnd e e₁) b eq
        rewrite sym eq
              = E-BAnd e e₁ (beval e) (beval e₁) (right e (beval e) refl)
                  (right e₁ (beval e₁) refl)

---- 推論規則記法 -------------------------------------------------------------
