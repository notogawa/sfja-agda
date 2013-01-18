module Basics where

open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)
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

test-nextWeekday : nextWeekday (nextWeekday Saturday) ≡ Tuesday
test-nextWeekday = refl

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
andb False - = False

orb : Bool → Bool → Bool
orb True - = True
orb False b = b

test-orb1 : orb True False ≡ True
test-orb1 = refl
test-orb2 : orb False False ≡ False
test-orb2 = refl
test-orb3 : orb False True ≡ True
test-orb3 = refl
test-orb4 : orb True True ≡ True
test-orb4 = refl

-- Agdaのadmitって何だろう？
-- admit = {!!}

{-
練習問題: ★ (nandb)

次の定義を完成させ、Exampleで記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。

この関数はどちらか、もしくは両方がFalseになったときにTrueを返すものである。
-}
nandb : Bool → Bool → Bool
nandb True b = negb b
nandb False - = True

{-
下の定義からAdmitted.を取り去り、代わりに"Proof. simpl. reflexivity. Qed."で検証できるようなコードを記述しなさい。
-}
test-nandb1 : nandb True False ≡ True
test-nandb1 = refl
test-nandb2 : nandb False False ≡ True
test-nandb2 = refl
test-nandb3 : nandb False True ≡ True
test-nandb3 = refl
test-nandb4 : nandb True True ≡ False
test-nandb4 = refl

{-
練習問題: ★ (andb3)
-}
andb3 : Bool → Bool → Bool → Bool
andb3 a b c = andb a (andb b c)

test-andb31 : andb3 True True True ≡ True
test-andb31 = refl
test-andb32 : andb3 False True True ≡ False
test-andb32 = refl
test-andb33 : andb3 True False True ≡ False
test-andb33 = refl
test-andb34 : andb3 True True False ≡ False
test-andb34 = refl

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

test-oddb1 : oddb (S O) ≡ True
test-oddb1 = refl
test-oddb2 : oddb (S (S (S (S O)))) ≡ False
test-oddb2 = refl

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
minus O - = O
minus (S n) O = S n
minus (S n) (S m) = minus n m

exp : Nat → Nat → Nat
exp base O = S O
exp base (S power) = mult base (exp base power)

test-mult1 : mult 3 3 ≡ 9
test-mult1 = refl

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

test-factorial1 : factorial 3 ≡ 6
test-factorial1 = refl
test-factorial2 : factorial 5 ≡ mult 10 12
test-factorial2 = refl

-- Notationというかこれも単なる関数だし，nat-scopeみたいなのは無いかな
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

beq-nat : Nat → Nat → Bool
beq-nat O O = True
beq-nat O (S -) = False
beq-nat (S -) O = False
beq-nat (S n) (S m) = beq-nat n m

ble-nat : Nat → Nat → Bool
ble-nat O - = True
ble-nat (S n) O = False
ble-nat (S n) (S m) = ble-nat n m

test-ble-nat1 : ble-nat 2 2 ≡ True
test-ble-nat1 = refl
test-ble-nat2 : ble-nat 2 4 ≡ True
test-ble-nat2 = refl
test-ble-nat3 : ble-nat 4 2 ≡ False
test-ble-nat3 = refl

{-
練習問題: ★★ (blt-nat)

blt-nat関数は、自然数を比較して小さい、ということを調べてbool値を生成します（ natural numbers for less-than）。Fixpointを使用して１から作成するのではなく、すでにこれまで定義した関数を利用して定義しなさい。

注：simplタクティックを使ってうまくいかない場合は、代わりにcomputeを試してください。それはよりうまく作られたsimplと言えるものですが、そもそもシンプルでエレガントな解が書けていれば、simplで十分に評価できるはずです。
-}
blt-nat : Nat → Nat → Bool
blt-nat n m = andb (ble-nat n m) (negb (beq-nat n m))

test-blt-nat1 : blt-nat 2 2 ≡ False
test-blt-nat1 = refl
test-blt-nat2 : blt-nat 2 4 ≡ True
test-blt-nat2 = refl
test-blt-nat3 : blt-nat 4 2 ≡ False
test-blt-nat3 = refl


O+n≡n : {n : Nat} → 0 + n ≡ n
O+n≡n = refl

O+n'≡n : {n : Nat} → 0 + n ≡ n
O+n'≡n = refl

{-
練習問題: ★, optional (simpl-plus)

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
plus-id-example : {n m : Nat} → n ≡ m → n + n ≡ m + m
plus-id-example {n} {m} eq = cong₂ (_+_) {n} {m} {n} {m} eq eq

{-
練習問題: ★ (plus-id-exercise)

Admitted.を削除し、証明を完成させなさい。
-}
plus-id-exercise : {n m o : Nat} → n ≡ m → m ≡ o → n + m ≡ m + o
plus-id-exercise {n} {m} {o} = cong₂ (_+_) {n} {m} {m} {o}

mult-zero-plus : {n m : Nat} → (0 + n) * m ≡ n * m
mult-zero-plus {n} {m} = cong (\a → a * m) (O+n≡n {n})
-- mult-zero-plus = refl -- でもいいけど

{-
練習問題: ★★, recommended (mult-1-plus)
-}
mult-one-plus : {n m : Nat} → (1 + n) * m ≡ m + (n * m)
mult-one-plus = refl


plus-one-neq-zero-firsttry : {n : Nat} → beq-nat (n + 1) 0 ≡ False
plus-one-neq-zero-firsttry {0} = refl
plus-one-neq-zero-firsttry {S n} = refl

negb-involutive : {b : Bool} → negb (negb b) ≡ b
negb-involutive {True} = refl
negb-involutive {False} = refl

zero-nbeq-plus-one : {n : Nat} → beq-nat 0 (n + 1) ≡ False
zero-nbeq-plus-one {0} = refl
zero-nbeq-plus-one {S n} = refl

¬-negb : {a b : Bool} → a ≡ b →  a ≢ negb b
¬-negb {True} refl ()
¬-negb {False} refl ()

andb-true-elim1 : {b c : Bool} → andb b c ≡ True → b ≡ True
andb-true-elim1 {True} - = refl
andb-true-elim1 {False} eq = ⊥-elim (¬-negb eq refl)

{-
練習問題: ★★ (andb-true-elim2)

destructを使い、case（もしくはsubcase）を作成して、以下の証明andb-true-elim2を完成させなさい。
-}
-- そんなもんネーヨ!
andb-true-elim2 : {b c : Bool} → andb b c ≡ True → c ≡ True
andb-true-elim2 {_} {True} eq = refl
andb-true-elim2 {True} {False} eq = ⊥-elim (¬-negb eq refl)
andb-true-elim2 {False} {False} eq = ⊥-elim (¬-negb eq refl)


n+O≡n : {n : Nat} → n + 0 ≡ n
n+O≡n {0} = refl
n+O≡n {S n} = cong S (n+O≡n {n})

minus-diag : {n : Nat} → minus n n ≡ 0
minus-diag {0} = refl
minus-diag {S n} = trans refl (minus-diag {n})

{-
練習問題: ★★, recommended (basic-induction)
-}
n*O≡O : {n : Nat} → n * 0 ≡ 0
n*O≡O {0} = refl
n*O≡O {S n} = trans (trans (mult-one-plus {n} {0}) (O+n≡n {n * 0})) (n*O≡O {n})

plus-n-Sm : {n m : Nat} → S (n + m) ≡ n + (S m)
plus-n-Sm {0}   {m} = refl
plus-n-Sm {S n} {m} = cong S (plus-n-Sm {n} {m})

plus-comm : {n m : Nat} → n + m ≡ m + n
plus-comm {0}   {m} = trans (O+n≡n {m}) (sym (n+O≡n {m}))
plus-comm {S n} {m} = trans (cong S (plus-comm {n} {m})) (plus-n-Sm {m} {n})


double : Nat → Nat
double 0 = 0
double (S n) = S (S (double n))

{-
練習問題: ★★ (double-plus)
-}
double-plus : {n : Nat} → double n ≡ n + n
double-plus {0} = refl
double-plus {S n} = trans (cong (\x → S (S x)) (double-plus {n})) (cong S (plus-n-Sm {n} {n}))

{-
練習問題: ★ (destruct-induction)

destructとinductionの違いを短く説明しなさい。
-}
-- base case で証明した結果を step case で使えるかどうか．
-- なんだろうけどAgdaの場合あんまり気にしないからなー


plus-assoc : {n m p : Nat} → n + (m + p) ≡ (n + m) + p
plus-assoc {0} = refl
plus-assoc {S n} = cong S (plus-assoc {n})

{-
練習問題: ★★ (plus-comm-informal)

plus-commの証明を、非形式的な証明に書き換えなさい。

定理：加法は可換である。
-}
-- 略

{-
練習問題: ★★, optional (beq-nat-refl-informal)

次の証明を、plus-assoc の非形式的な証明を参考に書き換えなさい。Coqのタクティックを単に言い換えただけにならないように！

定理：true=beq-nat n n forany n.（任意のnについて、nはnと等しいという命題がtrueとなる）
-}
-- 略

{-
練習問題: ★, optional (beq-nat-refl)
-}
beq-nat-refl : {n : Nat} → True ≡ beq-nat n n
beq-nat-refl {0} = refl
beq-nat-refl {S n} = beq-nat-refl {n}



mult-zero-plus' : {n m : Nat} → (0 + n) * m ≡ n * m
mult-zero-plus' {n} {m} = cong (\a → a * m) assert
  where -- assert相当ならwhereかなぁ?
    assert : 0 + n ≡ n
    assert = refl

plus-rearrange : {n m p q : Nat} → (n + m) + (p + q) ≡ (m + n) + (p + q)
plus-rearrange {n} {m} {p} {q} = cong (\a → a + (p + q)) assert
  where
    assert : n + m ≡ m + n
    assert = plus-comm {n} {m}

{-
練習問題: ★★★★ (mult-comm)

assertを使用して以下の証明を完成させなさい。ただしinduction（帰納法）を使用しないこと。
-}
plus-swap : {n m p : Nat} → n + (m + p) ≡ m + (n + p)
plus-swap {n} {m} {p} = trans (trans assert1 assert2) assert3
  where
    assert1 : n + (m + p) ≡ (n + m) + p
    assert1 = plus-assoc {n} {m} {p}
    assert2 : (n + m) + p ≡ (m + n) + p
    assert2 = cong (\a → a + p) (plus-comm {n} {m})
    assert3 : (m + n) + p ≡ m + (n + p)
    assert3 = sym (plus-assoc {m} {n} {p})
{-
では、乗法が可換であることを証明しましょう。おそらく、補助的な定理を定義し、それを使って全体を証明することになると思います。先ほど証明したplus-swapが便利に使えるでしょう。
-}
mult-comm : {m n : Nat} → m * n ≡ n * m
mult-comm {0} {n} = trans (0*l≡0 {n}) (sym (n*O≡O {n}))
mult-comm {S m} {n} = trans (cong (\a → n + a) (mult-comm {m} {n})) (mult-one-plus' {n} {m})
  where
    mult-one-plus' : {n m : Nat} → n + n * m ≡ n * (1 + m)
    mult-one-plus' {0} {m} = refl
    mult-one-plus' {S n} {m} = trans assert1' (trans assert2' (trans assert3' assert4'))
      where
        assert1' : (1 + n) + (m + n * m) ≡ m + (1 + n + n * m)
        assert1' = plus-swap {1 + n} {m}
        assert2' : m + (1 + n + n * m) ≡ m + (1 + n * (1 + m))
        assert2' = cong (\a → m + (1 + a)) (mult-one-plus' {n} {m})
        assert3' : m + (1 + n * (1 + m)) ≡ (m + 1) + n * (1 + m)
        assert3' = plus-assoc {m} {1} {n * (1 + m)}
        assert4' : (m + 1) + n * (1 + m) ≡ (1 + m) + n * (1 + m)
        assert4' = cong (\a → a + n * (1 + m)) (plus-comm {m} {1})

{-
練習問題: ★★, optional (evenb-n--oddb-Sn)
-}
evenb-n-oddb-Sn : {n : Nat} → evenb n ≡ negb (evenb (S n))
evenb-n-oddb-Sn {0} = refl
evenb-n-oddb-Sn {1} = refl
evenb-n-oddb-Sn {S (S n)} = evenb-n-oddb-Sn {n}

{-
練習問題: ★★★, optional (more-exercises)

紙を何枚か用意して、下に続く定理が(a)簡約と書き換えだけで証明可能か、(b)destructを使ったcase分割が必要になるか、(c)帰納法が必要となるか、のいずれに属すかを、紙の上だけで考えなさい。予測を紙に書いたら、実際に証明を完成させなさい。証明にはCoqを用いてかまいません。最初に紙を使ったのは「初心忘れるべからず」といった理由です。
-}
ble-nat-refl : {n : Nat} → True ≡ ble-nat n n
ble-nat-refl {0} = refl
ble-nat-refl {S n} = ble-nat-refl {n}

zero-nbeq-S : {n : Nat} → beq-nat 0 (S n) ≡ False
zero-nbeq-S = refl

andb-false-r : {b : Bool} → andb b False ≡ False
andb-false-r {True} = refl
andb-false-r {False} = refl

plus-ble-compat-l : {n m p : Nat} → ble-nat n m ≡ True → ble-nat (p + n) (p + m) ≡ True
plus-ble-compat-l {n} {m} {0} eq = eq
plus-ble-compat-l {n} {m} {S p} eq = trans refl (plus-ble-compat-l {n} {m} {p} eq)

S-nbeq-0 : {n : Nat} → beq-nat (S n) 0 ≡ False
S-nbeq-0 = refl

mult-1-l : {n : Nat} → 1 * n ≡ n
mult-1-l = n+O≡n

all3-spec : {b c : Bool} → orb (andb b c) (orb (negb b) (negb c)) ≡ True
all3-spec {True} {True} = refl
all3-spec {True} {False} = refl
all3-spec {False} {True} = refl
all3-spec {False} {False} = refl

mult-plus-distr-r : {n m p : Nat} → (n + m) * p ≡ (n * p) + (m * p)
mult-plus-distr-r {0} {m} {p} = refl
mult-plus-distr-r {S n} {m} {p} = trans (cong (\a → p + a) (mult-plus-distr-r {n} {m} {p})) (plus-assoc {p} {n * p} {m * p})

mult-assoc : {n m p : Nat} → n * (m * p) ≡ (n * m) * p
mult-assoc {0} {m} {p} = refl
mult-assoc {S n} {m} {p} = trans (cong (\a → m * p + a) (mult-assoc {n} {m} {p})) (sym (mult-plus-distr-r {m} {n * m} {p}))

{-
練習問題: ★★, optional (plus_swap')

replaceタクティックは、特定のサブタームを置き換えたいものと置き換えることができます。もう少し正確に言うと、replace (t) with (u)は、ゴールにあるtという式を全てuにかきかえ、t = uというサブゴールを追加します。この機能は、通常のrewriteがゴールの思い通りの場所に作用してくれない場合に有効です。

replaceタクティックを使用してplus_swap'の証明をしなさい。ただしplus_swapのようにassert (n + m = m + n)を使用しないで証明を完成させなさい。
-}
-- Agda的に意味無さそうなので略

{-
練習問題: ★★★★, recommended (binary)

これまでとは異なる、通常表記の自然数ではなく2進のシステムで、自然数のより効率的な表現を考えなさい。それは自然数をゼロとゼロに1を加える加算器からなるものを定義する代わりに、以下のような2進の形で表すものです。2進数とは、

  ゼロであるか,
  2進数を2倍したものか,
  2進数を2倍したものに1を加えたもの.

(a) まず、以下のnatの定義に対応するような2進型binの帰納的な定義を完成させなさい。 (ヒント: nat型の定義を思い出してください。

    Inductive nat : Type :=
      | O : nat
      | S : nat → nat.

nat型の定義OやSの意味が何かを語るものではなく、（Oが実際に何であろうが）Oがnatであって、nがnatならSが何であろうとS nはnatである、ということを示しているだけです。「Oがゼロで、Sは1を加える」という実装がそれを自然数としてみて実際に関数を書き、実行したり証明したりしてみてはじめて実際に意識されます。ここで定義するbinも同様で、次に書く関数が書かれてはじめて型binに実際の数学的な意味が与えられます。)
-}
data Bin : Set where
  Zero : Bin
  Shift : Bin → Bin
  ShiftInc : Bin → Bin

{-
(b) 先に定義したbin型の値をインクリメントする関数を作成しなさい。また、bin型をnat型に変換する関数も作成しなさい。
-}
inc-bin : Bin → Bin
inc-bin Zero = ShiftInc Zero
inc-bin (Shift n) = ShiftInc n
inc-bin (ShiftInc n) = Shift (inc-bin n)

bin→nat : Bin → Nat
bin→nat Zero = O
bin→nat (Shift n) = double (bin→nat n)
bin→nat (ShiftInc n) = S (double (bin→nat n))

{-
(c) 最後にbで作成したインクリメント関数と、2進→自然数関数が可換であることを証明しなさい。これを証明するには、bin値をまずインクリメントしたものを自然数に変換したものが、先に自然数変換した後にインクリメントしたものの値と等しいことを証明すればよい。
-}
inc-bin-commute-bin→nat : {n : Bin} → bin→nat (inc-bin n) ≡ S (bin→nat n)
inc-bin-commute-bin→nat {Zero} = refl
inc-bin-commute-bin→nat {Shift n} = refl
inc-bin-commute-bin→nat {ShiftInc n} = cong double (inc-bin-commute-bin→nat {n})

{-
練習問題: ★★★★★ (binary_inverse)

この練習問題は前の問題の続きで、2進数に関するものである。前の問題で作成された定義や定理をここで用いてもよい。

(a) まず自然数を2進数に変換する関数を書きなさい。そして「任意の自然数からスタートし、それを2進数にコンバートし、それをさらに自然数にコンバートすると、スタート時の自然数に戻ることを証明しなさい。
-}
nat→bin : Nat → Bin
nat→bin 0 = Zero
nat→bin (S n) = inc-bin (nat→bin n)

nat→bin→nat : {n : Nat} → bin→nat (nat→bin n) ≡ n
nat→bin→nat {0} = refl
nat→bin→nat {S n} = trans (inc-bin-commute-bin→nat {nat→bin n}) (cong S (nat→bin→nat {n}))

{-
(b) あなたはきっと、逆方向についての証明をしたほうがいいのでは、と考えているでしょう。それは、任意の2進数から始まり、それを自然数にコンバートしてから、また2進数にコンバートし直したものが、元の自然数と一致する、という証明です。しかしながら、この結果はtrueにはなりません。！！その原因を説明しなさい。
-}
{-
Zero = Shift Zero = Shift (Shift Zero) = ... であり，表現が一意に定まらないため．
-}

{-
(c) 2進数を引数として取り、それを一度自然数に変換した後、また2進数に変換したものを返すnormalize関数を作成し、証明しなさい。
-}
-- 何をだ？normalizeってことは羃等性か？
normalize : Bin → Bin
normalize n = nat→bin (bin→nat n)

normalize-idempotent : {n : Bin} → normalize (normalize n) ≡ normalize n
normalize-idempotent {n} = cong (\a → nat→bin a) (nat→bin→nat {bin→nat n})

{-
練習問題: ★★, optional (decreasing)

各関数の引数のいくつかが"減少的"でなければならない、という要求仕様は、Coqのデザインにおいて基礎となっているものです。特に、そのことによって、Coq上で作成された関数が、どんな入力を与えられても必ずいつか終了する、ということが保障されています。しかし、Coqの"減少的な解析"が「とても洗練されているとまではいえない」ため、時には不自然な書き方で関数を定義しなければならない、ということもあります。

これを具体的に感じるため、Fixpointで定義された、より「微妙な」関数の書き方を考えてみましょう（自然数に関する簡単な関数でかまいません）。それが全ての入力で停止することと、Coqがそれを、この制限のため受け入れてくれないことを確認しなさい。
-}

{- こういうのとか？(でもこれWF-Recとかでちゃんと書けば止まるはず)
f : Nat → Nat
f 0 = 0
f (S n) = f (div2 n)
  where
    div2 : Nat → Nat
    div2 0 = 0
    div2 1 = 0
    div2 (S (S n)) = S (div2 n)
-}
