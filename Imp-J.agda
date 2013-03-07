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

-- 変数を持つ式 ---------------------------------------------------------------

---- 識別子 -------------------------------------------------------------------

---- 状態 ---------------------------------------------------------------------
state : Set
state = ident → ℕ

empty-state : state
empty-state = const 0

update : state → ident → ℕ → state
update st x n x' = if beq-id x x' then n else st x'

{-
練習問題: ★★, optional (update_eq)
-}
update-eq : ∀ n X st → update st X n X ≡ n
update-eq n X st
  rewrite sym (beq-id-refl X)
        = refl
{-
練習問題: ★★, optional (update_neq)
-}
update-neq : ∀ V2 V1 n st → beq-id V2 V1 ≡ false → update st V2 n V1 ≡ st V1
update-neq V2 V1 n st x
  rewrite x
        = refl

{-
練習問題: ★★, optional (update_example)

タクティックを使って遊び始める前に、 定理が言っていることを正確に理解していることを確認しなさい!
-}
update-example : ∀ n →  update empty-state (Ident 2) n (Ident 3) ≡ 0
update-example = λ n → refl

{-
練習問題: ★★ (update_shadow)
-}
update-shadow : ∀ x1 x2 k1 k2 f → update (update f k2 x1) k2 x2 k1 ≡ update f k2 x2 k1
update-shadow x1 x2 k1 k2 f with beq-id k2 k1
update-shadow x1 x2 k1 k2 f | true = refl
update-shadow x1 x2 k1 k2 f | false = refl

{-
練習問題: ★★, optional (update_same)
-}
-- これ f k1 = x1 ってあるけど f k2 = x1 だよね？
update-same : ∀ x1 k1 k2 f → f k2 ≡ x1 → update f k1 x1 k2 ≡ f k2
update-same x1 k1 k2 f eq rewrite eq with beq-id k1 k2
update-same x1 k1 k2 f eq | true = refl
update-same x1 k1 k2 f eq | false = refl

{-
練習問題: ★★, optional (update_permute)
-}
update-permute : ∀ x1 x2 k1 k2 k3 f → beq-id k2 k1 ≡ false →
                 update (update f k2 x1) k1 x2 k3 ≡ update (update f k1 x2) k2 x1 k3
update-permute x1 x2 k1 k2 k3 f x = update-permute' x1 x2 k1 k2 k3 f x (b≡t∨b≡f (beq-id k2 k3)) (b≡t∨b≡f (beq-id k1 k3))
  where
    b≡t∨b≡f : ∀ b → b ≡ true ⊎ b ≡ false
    b≡t∨b≡f true = inj₁ refl
    b≡t∨b≡f false = inj₂ refl
    update-permute' : ∀ x1 x2 k1 k2 k3 f → beq-id k2 k1 ≡ false →
                      beq-id k2 k3 ≡ true ⊎ beq-id k2 k3 ≡ false →
                      beq-id k1 k3 ≡ true ⊎ beq-id k1 k3 ≡ false →
                      update (update f k2 x1) k1 x2 k3 ≡ update (update f k1 x2) k2 x1 k3
    update-permute' x1 x2 k1 k2 k3 f x (inj₁ x₂) (inj₁ x₃)
      = ⊥-elim (beq-id-false-not-eq k2 k1 x (beq-id-eq k2 k3 (sym x₂) ⟨ trans ⟩ sym (beq-id-eq k1 k3 (sym x₃)) ))
    update-permute' x1 x2 k1 k2 k3 f x (inj₁ x₂) (inj₂ y)
      rewrite x₂
            | y
            | x
            = refl
    update-permute' x1 x2 k1 k2 k3 f x (inj₂ y) (inj₁ x₂)
      rewrite x₂
            | y
            | x
            = refl
    update-permute' x1 x2 k1 k2 k3 f x (inj₂ y) (inj₂ y₁)
      rewrite y
            | y₁
            | x
            = refl

---- 構文 ---------------------------------------------------------------------
data aexp : Set where
  ANum : ℕ → aexp
  AId : ident → aexp
  APlus : aexp → aexp → aexp
  AMinus : aexp → aexp → aexp
  AMult : aexp → aexp → aexp

X : ident
X = Ident 0
Y : ident
Y = Ident 1
Z : ident
Z = Ident 2

data bexp : Set where
  BTrue : bexp
  BFalse : bexp
  BEq : aexp → aexp → bexp
  BLe : aexp → aexp → bexp
  BNot : bexp → bexp
  BAnd : bexp → bexp → bexp

---- 評価 ---------------------------------------------------------------------
aeval : state → aexp → ℕ
aeval st (ANum n) = n
aeval st (AId X) = st X
aeval st (APlus exp₁ exp₂) = aeval st exp₁ + aeval st exp₂
aeval st (AMinus exp₁ exp₂) = aeval st exp₁ ∸ aeval st exp₂
aeval st (AMult exp₁ exp₂) = aeval st exp₁ * aeval st exp₂

beval : state → bexp → Bool
beval st BTrue = true
beval st BFalse = false
beval st (BEq exp₁ exp₂) = beq-nat (aeval st exp₁) (aeval st exp₂)
beval st (BLe exp₁ exp₂) = ble-nat (aeval st exp₁) (aeval st exp₂)
beval st (BNot exp) = not (beval st exp)
beval st (BAnd exp₁ exp₂) = beval st exp₁ ∧ beval st exp₂

aexp1 : aeval (update empty-state X 5) (APlus (ANum 3) (AMult (AId X) (ANum 2))) ≡ 13
aexp1 = refl

bexp1 : beval (update empty-state X 5) (BAnd BTrue (BNot (BLe (AId X) (ANum 4)))) ≡ true
bexp1 = refl

-- コマンド -------------------------------------------------------------------
infixl 5 _∷=_
infixr 4 _#_

-- Agdaは;が演算子に使えない
data com : Set where
  SKIP : com
  _∷=_ : ident → aexp → com
  _#_ : com → com → com
  IFB_THEN_ELSE_FI : bexp → com → com → com
  WHILE_DO_END : bexp → com → com

fact-in-coq : com
fact-in-coq =
  Z ∷= AId X #
  Y ∷= ANum 1 #
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ∷= AMult (AId Y) (AId Z) #
    Z ∷= AMinus (AId Z) (ANum 1)
  END

---- 例 -----------------------------------------------------------------------
plus2 : com
plus2 =
  X ∷= APlus (AId X) (ANum 2)

XtimesYinZ : com
XtimesYinZ =
  Z ∷= AMult (AId X) (AId Y)

subtract-slowly-body : com
subtract-slowly-body =
  Z ∷= AMinus (AId Z) (ANum 1) #
  X ∷= AMinus (AId X) (ANum 1)

subtract-slowly : com
subtract-slowly =
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract-slowly-body
  END

subtract-3-from-5-slowly : com
subtract-3-from-5-slowly =
  X ∷= ANum 3 #
  Z ∷= ANum 5 #
  subtract-slowly

loop : com
loop =
  WHILE BTrue DO
    SKIP
  END

fact-body : com
fact-body =
  Y ∷= AMult (AId Y) (AId Z) #
  Z ∷= AMinus (AId Z) (ANum 1)

fact-loop : com
fact-loop =
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact-body
  END

fact-com : com
fact-com =
  Z ∷= AId X #
  Y ∷= ANum 1 #
  fact-loop

-- 評価 -----------------------------------------------------------------------

---- 評価関数 -----------------------------------------------------------------

ceval-step1 : state → com → state
ceval-step1 st SKIP = st
ceval-step1 st (x ∷= x₁) = update st x (aeval st x₁)
ceval-step1 st (com # com₁) = ceval-step1 (ceval-step1 st com) com₁
ceval-step1 st IFB x THEN com ELSE com₁ FI = if beval st x
                                             then ceval-step1 st com
                                             else ceval-step1 st com₁
ceval-step1 st WHILE x DO com END = st -- まぁ止まらんかね．

ceval-step2 : state → com → ℕ → state
ceval-step2 st com zero = empty-state
ceval-step2 st SKIP (suc i) = st
ceval-step2 st (x ∷= x₁) (suc i) = update st x (aeval st x₁)
ceval-step2 st (com # com₁) (suc i) = ceval-step2 (ceval-step2 st com i) com₁ i
ceval-step2 st IFB x THEN com ELSE com₁ FI (suc i) =
  if beval st x
    then ceval-step2 st com i
    else ceval-step2 st com₁ i
ceval-step2 st WHILE x DO com END (suc i) =
  if beval st x
    then ceval-step2 (ceval-step2 st com i) (WHILE x DO com END) i
    else st

ceval-step3 : state → com → ℕ → Maybe state
ceval-step3 st com zero = nothing
ceval-step3 st SKIP (suc i) = just st
ceval-step3 st (x ∷= x₁) (suc i) = just (update st x (aeval st x₁))
ceval-step3 st (com # com₁) (suc i) =
  case ceval-step3 st com i of λ
  { (just st') → ceval-step3 st' com₁ i
  ; nothing → nothing
  }
ceval-step3 st IFB x THEN com ELSE com₁ FI (suc i) =
  if beval st x
    then ceval-step3 st com i
    else ceval-step3 st com₁ i
ceval-step3 st WHILE x DO com END (suc i) =
  if beval st x
    then (case (ceval-step3 st com i) of λ
          { (just st') → ceval-step3 st' (WHILE x DO com END) i
          ; nothing → nothing
          })
    else just st

-- LETOPT は どうみてもMonadのbindだし，みんなCategory.Monad使うよネー
ceval-step : state → com → ℕ → Maybe state
ceval-step st com zero = nothing
ceval-step st SKIP (suc i) = just st
ceval-step st (x ∷= x₁) (suc i) = just (update st x (aeval st x₁))
ceval-step st (com # com₁) (suc i) =
  ceval-step st com i >>= λ st' → ceval-step st' com₁ i
  where
    open import Category.Monad
    open import Data.Maybe using (monad)
    open RawMonad monad
ceval-step st IFB x THEN com ELSE com₁ FI (suc i) =
  if beval st x
    then ceval-step st com i
    else ceval-step st com₁ i
ceval-step st WHILE x DO com END (suc i) =
  if beval st x
    then (ceval-step st com i >>= λ st' → ceval-step st' (WHILE x DO com END) i)
    else just st
  where
    open import Category.Monad
    open import Data.Maybe using (monad)
    open RawMonad monad

-- 何故直前でMonadのbind使っててこっちをFunctorにしないのか？
test-ceval : state → com → Maybe (ℕ × ℕ × ℕ)
test-ceval st c = f <$> ceval-step st c 500
  where
    f : state → ℕ × ℕ × ℕ
    f st = st X , st Y , st Z
    open import Category.Functor
    open import Data.Maybe using (functor)
    open RawFunctor functor

{-
練習問題: ★★, recommended (pup_to_n)

1 から X までの整数を変数 Y に足す (つまり 1 + 2 + ... + X) Imp プログラムを書きなさい。下に示したテストを満たすことを確認しなさい。
-}
pup-to-n : com
pup-to-n =
  Y ∷= ANum 0 #
  Z ∷= ANum 0 #
  WHILE BLe (AId Z) (AId X) DO
    Y ∷= APlus (AId Y) (AId Z) #
    Z ∷= APlus (AId Z) (ANum 1)
  END

-- 下に示したテスト？
test-pup-to-2 : test-ceval (update empty-state X 2) pup-to-n ≡ just (_ , 3 , _)
test-pup-to-2 = refl

{-
練習問題: ★★, optional (peven)

X が偶数だったら Z に 0 を、そうでなければ Z に 1 をセットする While プログラムを書きなさい。テストには ceval_test を使いなさい。
-}
peven : com
peven =
  Z ∷= AId X #
  WHILE BLe (ANum 2) (AId Z) DO
    Z ∷= AMinus (AId Z) (ANum 2)
  END

test-peven-3 : test-ceval (update empty-state X 3) peven ≡ just (_ , _ , 1)
test-peven-3 = refl
test-peven-4 : test-ceval (update empty-state X 4) peven ≡ just (_ , _ , 0)
test-peven-4 = refl

---- 関係としての評価 ---------------------------------------------------------
data _/_⇓_ : com → state → state → Set where
  E-Skip : ∀ st →
           SKIP / st ⇓ st
  E-Ass : ∀ st a1 n l → aeval st a1 ≡ n →
          (l ∷= a1) / st ⇓ update st l n
  E-Seq : ∀ c1 c2 st st' st'' → c1 / st ⇓ st' → c2 / st' ⇓ st'' →
          (c1 # c2) / st ⇓ st''
  E-IfTrue : ∀ st st' b1 c1 c2 → beval st b1 ≡ true → c1 / st ⇓ st' →
             IFB b1 THEN c1 ELSE c2 FI / st ⇓ st'
  E-IfFalse : ∀ st st' b1 c1 c2 → beval st b1 ≡ false → c2 / st ⇓ st' →
              IFB b1 THEN c1 ELSE c2 FI / st ⇓ st'
  E-WhileEnd : ∀ b1 st c1 → beval st b1 ≡ false →
               WHILE b1 DO c1 END / st ⇓ st
  E-WhileLoop : ∀ st st' st'' b1 c1 → beval st b1 ≡ true → c1 / st ⇓ st' →
                WHILE b1 DO c1 END / st' ⇓ st'' →
                WHILE b1 DO c1 END / st ⇓ st''

ceval-example1 : (X ∷= ANum 2 #
                  IFB BLe (AId X) (ANum 1)
                    THEN Y ∷= ANum 3
                    ELSE Z ∷= ANum 4
                  FI) / empty-state ⇓ update (update empty-state X 2) Z 4
-- ceval-example1 = ? から c-c c-a でウワァァァ
ceval-example1 = E-Seq (Ident zero ∷= ANum (suc (suc zero)))
                   IFB BLe (AId (Ident zero)) (ANum (suc zero)) THEN
                   Ident (suc zero) ∷= ANum (suc (suc (suc zero))) ELSE
                   Ident (suc (suc zero)) ∷= ANum (suc (suc (suc (suc zero)))) FI
                   (λ _ → zero)
                   (λ z → if beq-id (Ident zero) z then suc (suc zero) else zero)
                   (λ z →
                      if beq-id (Ident (suc (suc zero))) z then
                      suc (suc (suc (suc zero))) else
                      (if beq-id (Ident zero) z then suc (suc zero) else zero))
                   (E-Ass (λ _ → zero) (ANum (suc (suc zero))) (suc (suc zero))
                    (Ident zero) refl)
                   (E-IfFalse
                    (λ z → if beq-id (Ident zero) z then suc (suc zero) else zero)
                    (λ z →
                       if beq-id (Ident (suc (suc zero))) z then
                       suc (suc (suc (suc zero))) else
                       (if beq-id (Ident zero) z then suc (suc zero) else zero))
                    (BLe (AId (Ident zero)) (ANum (suc zero)))
                    (Ident (suc zero) ∷= ANum (suc (suc (suc zero))))
                    (Ident (suc (suc zero)) ∷= ANum (suc (suc (suc (suc zero))))) refl
                    (E-Ass
                     (λ z → if beq-id (Ident zero) z then suc (suc zero) else zero)
                     (ANum (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero))))
                     (Ident (suc (suc zero))) refl))
{-
練習問題: ★★ (ceval_example2)
-}
ceval-example2 : (X ∷= ANum 0 # Y ∷= ANum 1 # Z ∷= ANum 2) / empty-state ⇓
                 update (update (update empty-state X 0) Y 1) Z 2
ceval-example2 = E-Seq (Ident zero ∷= ANum zero)
                   (Ident (suc zero) ∷= ANum (suc zero) #
                    Ident (suc (suc zero)) ∷= ANum (suc (suc zero)))
                   (λ _ → zero) (λ z → if beq-id (Ident zero) z then zero else zero)
                   (λ z →
                      if beq-id (Ident (suc (suc zero))) z then suc (suc zero) else
                      (if beq-id (Ident (suc zero)) z then suc zero else
                       (if beq-id (Ident zero) z then zero else zero)))
                   (E-Ass (λ _ → zero) (ANum zero) zero (Ident zero) refl)
                   (E-Seq (Ident (suc zero) ∷= ANum (suc zero))
                    (Ident (suc (suc zero)) ∷= ANum (suc (suc zero)))
                    (λ z → if beq-id (Ident zero) z then zero else zero)
                    (λ z →
                       if beq-id (Ident (suc zero)) z then suc zero else
                       (if beq-id (Ident zero) z then zero else zero))
                    (λ z →
                       if beq-id (Ident (suc (suc zero))) z then suc (suc zero) else
                       (if beq-id (Ident (suc zero)) z then suc zero else
                        (if beq-id (Ident zero) z then zero else zero)))
                    (E-Ass (λ z → if beq-id (Ident zero) z then zero else zero)
                     (ANum (suc zero)) (suc zero) (Ident (suc zero)) refl)
                    (E-Ass
                     (λ z →
                        if beq-id (Ident (suc zero)) z then suc zero else
                        (if beq-id (Ident zero) z then zero else zero))
                     (ANum (suc (suc zero))) (suc (suc zero)) (Ident (suc (suc zero)))
                     refl))

---- 関係による評価とステップ指数を利用した評価の等価性 -----------------------
ceval-step→ceval : ∀ c st st' →
                   (∃ λ i → ceval-step st c i ≡ just st') →
                   c / st ⇓ st'
ceval-step→ceval c st st' (i , jst≡jst') = ceval-step→ceval' c st st' i jst≡jst'
  where
    just-inversion : ∀ {a} {X : Set a} {x y : X} → Maybe.just x ≡ just y → x ≡ y
    just-inversion refl = refl

    just-inversion' : ∀ {a} {X : Set a} {y : X} → Maybe.nothing ≡ just y → ⊥
    just-inversion' = λ ()

    maybe-remember : ∀ {a} {X : Set a} (x : Maybe X) → (∃ λ a → x ≡ just a) ⊎ x ≡ nothing
    maybe-remember (just x) = inj₁ (x , refl)
    maybe-remember nothing = inj₂ refl

    bool-remember : ∀ b → b ≡ true ⊎ b ≡ false
    bool-remember true = inj₁ refl
    bool-remember false = inj₂ refl

    ceval-step→ceval' : ∀ c st st' i →
                       ceval-step st c i ≡ just st' →
                       c / st ⇓ st'
    ceval-step→ceval' c st st' zero ()
    ceval-step→ceval' SKIP st st' (suc i) jst≡jst'
      rewrite just-inversion jst≡jst'
            = E-Skip st'
    ceval-step→ceval' (x ∷= x₁) st st' (suc i) jst≡jst'
      rewrite sym (just-inversion jst≡jst')
            = E-Ass st x₁ (aeval st x₁) x refl
    ceval-step→ceval' (c # c₁) st st' (suc i) jst≡jst' with maybe-remember (ceval-step st c i)
    ceval-step→ceval' (c # c₁) st st' (suc i) jst≡jst' | inj₁ (st'' , x)
      rewrite x
            = E-Seq c c₁ st st'' st'
                (ceval-step→ceval' c st st'' i x)
                (ceval-step→ceval' c₁ st'' st' i jst≡jst')
    ceval-step→ceval' (c # c₁) st st' (suc i) jst≡jst' | inj₂ y
      rewrite y
            = ⊥-elim (just-inversion' jst≡jst')
    ceval-step→ceval' IFB x THEN c ELSE c₁ FI st st' (suc i) jst≡jst' with bool-remember (beval st x)
    ceval-step→ceval' IFB x THEN c ELSE c₁ FI st st' (suc i) jst≡jst' | inj₁ x₁
      rewrite x₁
            = E-IfTrue st st' x c c₁ x₁ (ceval-step→ceval' c st st' i jst≡jst')
    ceval-step→ceval' IFB x THEN c ELSE c₁ FI st st' (suc i) jst≡jst' | inj₂ y
      rewrite y
            = E-IfFalse st st' x c c₁ y (ceval-step→ceval' c₁ st st' i jst≡jst')
    ceval-step→ceval' WHILE x DO c END st st' (suc i) jst≡jst' with bool-remember (beval st x)
    ceval-step→ceval' WHILE x DO c END st st' (suc i) jst≡jst' | inj₁ x₁ with maybe-remember (ceval-step st c i)
    ceval-step→ceval' WHILE x DO c END st st' (suc i) jst≡jst' | inj₁ x₁ | inj₁ (st'' , proj₂)
      rewrite x₁
            | proj₂
            = E-WhileLoop st st'' st' x c x₁
                (ceval-step→ceval' c st st'' i proj₂)
                (ceval-step→ceval' WHILE x DO c END st'' st' i jst≡jst')
    ceval-step→ceval' WHILE x DO c END st st' (suc i) jst≡jst' | inj₁ x₁ | inj₂ y
      rewrite x₁
            | y
            = ⊥-elim (just-inversion' jst≡jst')
    ceval-step→ceval' WHILE x DO c END st st' (suc i) jst≡jst' | inj₂ y
      rewrite y
            | sym (just-inversion jst≡jst')
            = E-WhileEnd x st c y
