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
