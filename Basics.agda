module Basics where

open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; cong₂; subst)
open import Relation.Nullary

data Day : Set where
  Monday : Day
  Tuesday : Day
  Wednesday : Day
  Thursday : Day
  Friday : Day
  Saturday : Day
  Sunday : Day

nextWeekday : Day → Day
nextWeekday Monday = Tuesday
nextWeekday Tuesday = Wednesday
nextWeekday Wednesday = Thursday
nextWeekday Thursday = Friday
nextWeekday Friday = Monday
nextWeekday Saturday = Monday
nextWeekday Sunday = Monday

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> nextWeekday Friday
Monday
Main> nextWeekday (nextWeekday Saturday)
Tuesday
-}

test_nextWeekday : nextWeekday (nextWeekday Saturday) ≡ Tuesday
test_nextWeekday = refl

data Bool : Set where
  True : Bool
  False : Bool

{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN TRUE  True  #-}
{-# BUILTIN FALSE False #-}

negb : Bool → Bool
negb True = False
negb False = True

andb : Bool → Bool → Bool
andb True b = b
andb False _ = False

orb : Bool → Bool → Bool
orb True _ = True
orb False b = b

test_orb1 : orb True False ≡ True
test_orb1 = refl
test_orb2 : orb False False ≡ False
test_orb2 = refl
test_orb3 : orb False True ≡ True
test_orb3 = refl
test_orb4 : orb True True ≡ True
test_orb4 = refl

-- Agdaのadmitって何だろう？
-- admit = {!!}

{-
練習問題: ★ (nandb)

次の定義を完成させ、Exampleで記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。

この関数はどちらか、もしくは両方がFalseになったときにTrueを返すものである。
-}
nandb : Bool → Bool → Bool
nandb True b = negb b
nandb False _ = True

{-
下の定義からAdmitted.を取り去り、代わりに"Proof. simpl. reflexivity. Qed."で検証できるようなコードを記述しなさい。
-}
test_nandb1 : nandb True False ≡ True
test_nandb1 = refl
test_nandb2 : nandb False False ≡ True
test_nandb2 = refl
test_nandb3 : nandb False True ≡ True
test_nandb3 = refl
test_nandb4 : nandb True True ≡ False
test_nandb4 = refl

{-
練習問題: ★ (andb3)
-}
andb3 : Bool → Bool → Bool → Bool
andb3 a b c = andb a (andb b c)

test_andb31 : andb3 True True True ≡ True
test_andb31 = refl
test_andb32 : andb3 False True True ≡ False
test_andb32 = refl
test_andb33 : andb3 True False True ≡ False
test_andb33 = refl
test_andb34 : andb3 True True False ≡ False
test_andb34 = refl

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> :typeOf negb True
Bool
Main> :typeOf negb
Bool → Bool
-}

data Nat : Set where
  O : Nat
  S : Nat → Nat

{- アラビア数字を使うため -}
{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO    O   #-}
{-# BUILTIN SUC     S   #-}

pred : Nat → Nat
pred O = O
pred (S n) = n

minustwo : Nat → Nat
minustwo O = O
minustwo (S O) = O
minustwo (S (S n)) = n

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> :typeOf (S (S (S (S O))))
Nat
Main> minustwo 4
2
Main> :typeOf S
Nat → Nat
Main> :typeOf pred
Nat → Nat
Main> :typeOf minustwo
Nat → Nat
-}

evenb : Nat → Bool
evenb O = True
evenb (S O) = False
evenb (S (S n)) = evenb n

oddb : Nat → Bool
oddb n = negb (evenb n)

test_oddb1 : oddb (S O) ≡ True
test_oddb1 = refl
test_oddb2 : oddb (S (S (S (S O)))) ≡ False
test_oddb2 = refl

plus : Nat → Nat → Nat
plus O m = m
plus (S n) m = S (plus n m)

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> plus (S (S (S O))) (S (S O))
5
-}

mult : Nat → Nat → Nat
mult O m = O
mult (S n) m = plus m (mult n m)

minus : Nat → Nat → Nat
minus O _ = O
minus (S n) O = S n
minus (S n) (S m) = minus n m

exp : Nat → Nat → Nat
exp base O = S O
exp base (S power) = mult base (exp base power)

test_mult1 : mult 3 3 ≡ 9
test_mult1 = refl

{-
演習問題: ★ (factorial)

再帰を使用した、一般的なfactorical（階乗）の定義を思い出してください :

factorial(0)  =  1
factorial(n)  =  n * factorial(n-1)     (if n>0)

これをCoqでの定義に書き直しなさい。
-}

-- Agdaだとそのまんますぎるー
factorial : Nat → Nat
factorial O = S O
factorial (S n) = mult (S n) (factorial n)

test_factorial1 : factorial 3 ≡ 6
test_factorial1 = refl
test_factorial2 : factorial 5 ≡ mult 10 12
test_factorial2 = refl

-- Notationというかこれも単なる関数だし，nat_scopeみたいなのは無いかな
_+_ : Nat → Nat → Nat
n + m = plus n m
infixl 6 _+_
_-_ : Nat → Nat → Nat
n - m = minus n m
infixl 6 _-_
_*_ : Nat → Nat → Nat
n * m = mult n m
infixl 7 _*_

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> (0 + 1) + 1
2
-}

beq_nat : Nat → Nat → Bool
beq_nat O O = True
beq_nat O (S _) = False
beq_nat (S _) O = False
beq_nat (S n) (S m) = beq_nat n m

ble_nat : Nat → Nat → Bool
ble_nat O _ = True
ble_nat (S n) O = False
ble_nat (S n) (S m) = ble_nat n m

test_ble_nat1 : ble_nat 2 2 ≡ True
test_ble_nat1 = refl
test_ble_nat2 : ble_nat 2 4 ≡ True
test_ble_nat2 = refl
test_ble_nat3 : ble_nat 4 2 ≡ False
test_ble_nat3 = refl

{-
練習問題: ★★ (blt_nat)

blt_nat関数は、自然数を比較して小さい、ということを調べてbool値を生成します（ natural numbers for less-than）。Fixpointを使用して１から作成するのではなく、すでにこれまで定義した関数を利用して定義しなさい。

注：simplタクティックを使ってうまくいかない場合は、代わりにcomputeを試してください。それはよりうまく作られたsimplと言えるものですが、そもそもシンプルでエレガントな解が書けていれば、simplで十分に評価できるはずです。
-}
blt_nat : Nat → Nat → Bool
blt_nat n m = andb (ble_nat n m) (negb (beq_nat n m))

test_blt_nat1 : blt_nat 2 2 ≡ False
test_blt_nat1 = refl
test_blt_nat2 : blt_nat 2 4 ≡ True
test_blt_nat2 = refl
test_blt_nat3 : blt_nat 4 2 ≡ False
test_blt_nat3 = refl


O+n≡n : {n : Nat} → 0 + n ≡ n
O+n≡n = refl

O+n'≡n : {n : Nat} → 0 + n ≡ n
O+n'≡n = refl

{-
練習問題: ★, optional (simpl_plus)

この問い合わせの結果、Coqが返す応答はなにか？

Eval simpl in (∀ n:nat, n + 0 = n).

また次のものの場合はどうか？

Eval simpl in (∀ n:nat, 0 + n = n).

この二つの違いを示せ。
-}
{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> {n : Nat} -> n + 0 ≡ n
{n : Nat} → plus n 0 ≡ n
(未証明)
Main> {n : Nat} -> 0 + n ≡ n
{n : Nat} → n ≡ n
(証明済み)
-}


-- Tactic入ってこられてもAgdaさん的にどうしようという気分になるよね
O+n''≡n : {n : Nat} → 0 + n ≡ n
O+n''≡n = refl

1+l≡Sn : {n : Nat} → 1 + n ≡ S n
1+l≡Sn = refl

0*l≡0 : {n : Nat} → 0 * n ≡ 0
0*l≡0 = refl

-- グワー
plus_id_example : {n m : Nat} → n ≡ m → n + n ≡ m + m
plus_id_example {n} {m} eq = cong₂ (_+_) {n} {m} {n} {m} eq eq

{-
練習問題: ★ (plus_id_exercise)

Admitted.を削除し、証明を完成させなさい。
-}
plus_id_exercise : {n m o : Nat} → n ≡ m → m ≡ o → n + m ≡ m + o
plus_id_exercise {n} {m} {o} = cong₂ (_+_) {n} {m} {m} {o}

mult_zero_plus : {n m : Nat} → (0 + n) * m ≡ n * m
mult_zero_plus {n} {m} = cong (\a → a * m) (O+n≡n {n})
-- mult_zero_plus = refl -- でもいいけど

{-
練習問題: ★★, recommended (mult_1_plus)
-}
mult_one_plus : {n m : Nat} → (1 + n) * m ≡ m + (n * m)
mult_one_plus = refl


plus_one_neq_zero_firsttry : {n : Nat} → beq_nat (n + 1) 0 ≡ False
plus_one_neq_zero_firsttry {0} = refl
plus_one_neq_zero_firsttry {S n} = refl

negb_involutive : {b : Bool} → negb (negb b) ≡ b
negb_involutive {True} = refl
negb_involutive {False} = refl

zero_nbeq_plus_one : {n : Nat} → beq_nat 0 (n + 1) ≡ False
zero_nbeq_plus_one {0} = refl
zero_nbeq_plus_one {S n} = refl

¬-negb : {a b : Bool} → a ≡ b →  a ≢ negb b
¬-negb {True} refl ()
¬-negb {False} refl ()

andb_true_elim1 : {b c : Bool} → andb b c ≡ True → b ≡ True
andb_true_elim1 {True} _ = refl
andb_true_elim1 {False} eq = ⊥-elim (¬-negb eq refl)

{-
練習問題: ★★ (andb_true_elim2)

destructを使い、case（もしくはsubcase）を作成して、以下の証明andb_true_elim2を完成させなさい。
-}
-- そんなもんネーヨ!
andb_true_elim2 : {b c : Bool} → andb b c ≡ True → c ≡ True
andb_true_elim2 {_} {True} eq = refl
andb_true_elim2 {True} {False} eq = ⊥-elim (¬-negb eq refl)
andb_true_elim2 {False} {False} eq = ⊥-elim (¬-negb eq refl)
