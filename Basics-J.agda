module Basics-J where

-- 等価性の証明のための標準ライブラリ
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; sym; cong; trans)

-- 列挙型 ---------------------------------------------------------------------

---- 曜日の表し方 -------------------------------------------------------------

data day : Set where
  monday : day
  tuesday : day
  wednesday : day
  thursday : day
  friday : day
  saturday : day
  sunday : day

{-
まず，
  next-weekday : day → day
と書いた後，次の行で，
  next-weekday day = ?
として c-c c-l すると
  next-weekday day = { }0
となるのでこのゴールで，c-c c-c day すると day に関して場合分けされ，
  next-weekday monday = { }0
  next-weekday tuesday = { }1
  next-weekday wednesday = { }2
  next-weekday thursday = { }3
  next-weekday friday = { }4
  next-weekday saturday = { }5
  next-weekday sunday = { }6
となり，ゴール0にtuesdayと書いて
  next-weekday monday = {tuesday }0
c-c c-r すると
  next-weekday monday = tuesday
と確定される．他についても同様に．
-}
next-weekday : day → day
next-weekday monday = tuesday
next-weekday tuesday = wednesday
next-weekday wednesday = thursday
next-weekday thursday = friday
next-weekday friday = monday
next-weekday saturday = monday
next-weekday sunday = monday

{-
Eval simpl in (next_weekday friday).
Eval simpl in (next_weekday (next_weekday saturday)).

はagdaのインタラクティブモード(もうあんま動作保証しないらしいが)で見るなど．

$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> next-weekday friday
monday
Main> next-weekday (next-weekday saturday)
tuesday
-}

-- 例示して検証は以下に対応
test-next-weekday : next-weekday (next-weekday saturday) ≡ tuesday
test-next-weekday = refl


---- ブール型 -----------------------------------------------------------------

data bool : Set where
  true : bool
  false : bool

{-# BUILTIN BOOL  bool  #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}

negb : bool → bool
negb true = false
negb false = true

andb : bool → bool → bool
andb true b = b
andb false _ = false

orb : bool → bool → bool
orb true _ = true
orb false b = b

test-orb1 : orb true false ≡ true
test-orb1 = refl
test-orb2 : orb false false ≡ false
test-orb2 = refl
test-orb3 : orb false true ≡ true
test-orb3 = refl
test-orb4 : orb true true ≡ true
test-orb4 = refl

-- Agdaのadmitって何だろう？
-- admit = {!!}

{-
練習問題: ★ (nandb)

次の定義を完成させ、Exampleで記述された確認内容がCoqのチェックをすべて通過することを確認しなさい。

この関数はどちらか、もしくは両方がfalseになったときにtrueを返すものである。
-}
nandb : bool → bool → bool
nandb true b = negb b
nandb false _ = true

{-
下の定義からAdmitted.を取り去り、代わりに"Proof. simpl. reflexivity. Qed."で検証できるようなコードを記述しなさい。
-}
test-nandb1 : nandb true false ≡ true
test-nandb1 = refl
test-nandb2 : nandb false false ≡ true
test-nandb2 = refl
test-nandb3 : nandb false true ≡ true
test-nandb3 = refl
test-nandb4 : nandb true true ≡ false
test-nandb4 = refl

{-
練習問題: ★ (andb3)
-}
andb3 : bool → bool → bool → bool
andb3 a b c = andb a (andb b c)

test-andb31 : andb3 true true true ≡ true
test-andb31 = refl
test-andb32 : andb3 false true true ≡ false
test-andb32 = refl
test-andb33 : andb3 true false true ≡ false
test-andb33 = refl
test-andb34 : andb3 true true false ≡ false
test-andb34 = refl

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> :typeOf negb true
bool
Main> :typeOf negb
bool → bool
-}

---- 関数の型 -----------------------------------------------------------------
{-
型を推論させるには c-c c-d で式を与える．
  c-c c-d negb true
なら bool と推論される．
  c-c c-d negb
なら bool → bool と推論
-}

---- 数値 ---------------------------------------------------------------------

-- Agdaにも内部モジュールはあるけど，
-- そもそも標準ライブラリの自然数の名前がnatじゃなくℕなのでかぶらない．
-- module Playground1 where

data nat : Set where
  O : nat
  S : nat → nat

{- アラビア数字を使うため -}
{-# BUILTIN NATURAL nat #-}
{-# BUILTIN ZERO    O   #-}
{-# BUILTIN SUC     S   #-}

pred : nat → nat
pred O = O
pred (S n) = n


minustwo : nat → nat
minustwo O = O
minustwo (S O) = O
minustwo (S (S n)) = n

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> :typeOf (S (S (S (S O))))
nat
Main> minustwo 4
2
Main> :typeOf S
nat → nat
Main> :typeOf pred
nat → nat
Main> :typeOf minustwo
nat → nat
-}

evenb : nat → bool
evenb O = true
evenb (S O) = false
evenb (S (S n)) = evenb n

oddb : nat → bool
oddb n = negb (evenb n)

test-oddb1 : oddb (S O) ≡ true
test-oddb1 = refl
test-oddb2 : oddb (S (S (S (S O)))) ≡ false
test-oddb2 = refl

plus : nat → nat → nat
plus O m = m
plus (S n) m = S (plus n m)

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> plus (S (S (S O))) (S (S O))
5
-}

mult : nat → nat → nat
mult O m = O
mult (S n) m = plus m (mult n m)

minus : nat → nat → nat
minus O _ = O
minus (S n) O = S n
minus (S n) (S m) = minus n m

exp : nat → nat → nat
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
factorial : nat → nat
factorial O = S O
factorial (S n) = mult (S n) (factorial n)

test-factorial1 : factorial 3 ≡ 6
test-factorial1 = refl
test-factorial2 : factorial 5 ≡ mult 10 12
test-factorial2 = refl

-- Notationというかこれも単なる関数だし，nat-scopeみたいなのは無いかな
_+_ : nat → nat → nat
n + m = plus n m
infixl 6 _+_
_-_ : nat → nat → nat
n - m = minus n m
infixl 6 _-_
_*_ : nat → nat → nat
n * m = mult n m
infixl 7 _*_

{-
$ agda -I -i/usr/share/agda-stdlib -i. Basics.agda
Main> (0 + 1) + 1
2
-}

beq-nat : nat → nat → bool
beq-nat O O = true
beq-nat O (S _) = false
beq-nat (S _) O = false
beq-nat (S n) (S m) = beq-nat n m

ble-nat : nat → nat → bool
ble-nat O _ = true
ble-nat (S n) O = false
ble-nat (S n) (S m) = ble-nat n m

test-ble-nat1 : ble-nat 2 2 ≡ true
test-ble-nat1 = refl
test-ble-nat2 : ble-nat 2 4 ≡ true
test-ble-nat2 = refl
test-ble-nat3 : ble-nat 4 2 ≡ false
test-ble-nat3 = refl

{-
練習問題: ★★ (blt-nat)

blt-nat関数は、自然数を比較して小さい、ということを調べてbool値を生成します（ natural numbers for less-than）。Fixpointを使用して１から作成するのではなく、すでにこれまで定義した関数を利用して定義しなさい。

注：simplタクティックを使ってうまくいかない場合は、代わりにcomputeを試してください。それはよりうまく作られたsimplと言えるものですが、そもそもシンプルでエレガントな解が書けていれば、simplで十分に評価できるはずです。
-}
blt-nat : nat → nat → bool
blt-nat n m = andb (ble-nat n m) (negb (beq-nat n m))

test-blt-nat1 : blt-nat 2 2 ≡ false
test-blt-nat1 = refl
test-blt-nat2 : blt-nat 2 4 ≡ true
test-blt-nat2 = refl
test-blt-nat3 : blt-nat 4 2 ≡ false
test-blt-nat3 = refl

-- 簡約を用いた証明 -----------------------------------------------------------

O+n≡n : (n : nat) → 0 + n ≡ n
O+n≡n n = refl

O+n'≡n : (n : nat) → 0 + n ≡ n
O+n'≡n n = refl

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
Main> (n : nat) -> n + 0 ≡ n
(n : nat) → plus n 0 ≡ n
(未証明)
Main> (n : nat) -> 0 + n ≡ n
(n : nat) → n ≡ n
(証明済み)
-}

-- introsタクティック ---------------------------------------------------------

-- Tactic入ってこられてもAgdaさん的にどうしようという気分になるよね

-- 結局introsは
-- P = λ x → Hoge が証明すべきモノのときに，
-- P x = Hoge を証明すべきモノに変えるもの

O+n''≡n : (n : nat) → 0 + n ≡ n
O+n''≡n n = refl

1+l≡Sn : (n : nat) → 1 + n ≡ S n
1+l≡Sn n = refl

0*l≡0 : (n : nat) → 0 * n ≡ 0
0*l≡0 n = refl

-- 書き換え（Rewriting）による証明 --------------------------------------------

-- Coqではゴールに対する書き換えで証明を進めていくが，
-- Agdaではゴールの式を仮定からどう構築するかを考えていくことになる．

-- rewrite を使う
plus-id-example : (n m : nat) → n ≡ m → n + n ≡ m + m
plus-id-example n m eq
  rewrite eq
        = refl

{-
練習問題: ★ (plus-id-exercise)

Admitted.を削除し、証明を完成させなさい。
-}
-- 複数使う場合は | で
plus-id-exercise : (n m o : nat) → n ≡ m → m ≡ o → n + m ≡ m + o
plus-id-exercise n m o eq1 eq2
  rewrite eq1
        | eq2
        = refl

-- 標準ライブラリのcong(congruence)を使う．
-- congの所で M-. すれば定義に飛べる．
-- a ≡ b → f a ≡ f b のカタチのequivalenceはみんなcongであり，
-- 結局 f a を a ≡ b で rewrite → したら f b だよねと言うのと同じ．
mult-0-plus : (n m : nat) → (0 + n) * m ≡ n * m
mult-0-plus n m = cong (λ a → a * m) (O+n≡n n)
-- まぁこの式なら mult-0-plus = refl でもいいけど

{-
練習問題: ★★, recommended (mult-1-plus)
-}
mult-1-plus : (n m : nat) → (1 + n) * m ≡ m + (n * m)
mult-1-plus n m = refl

-- Case分析 -------------------------------------------------------------------

{-
場合分けもただのパターンマッチ
next-weekday でやったのと同様に c-c c-c で場合分けすると．
  plus-1-neq-0-firsttry O = { }0
  plus-1-neq-0-firsttry (S n) = { }1
となってくれる．
-}
plus-1-neq-0-firsttry : (n : nat) → beq-nat (n + 1) 0 ≡ false
plus-1-neq-0-firsttry 0 = refl
plus-1-neq-0-firsttry (S n) = refl

negb-involutive : (b : bool) → negb (negb b) ≡ b
negb-involutive true = refl
negb-involutive false = refl

zero-nbeq-plus-1 : (n : nat) → beq-nat 0 (n + 1) ≡ false
zero-nbeq-plus-1 0 = refl
zero-nbeq-plus-1 (S n) = refl

-- Caseへのネーミング ---------------------------------------------------------

-- Case？なにそれおいしいの？

-- 以下のbがfalseのケースでは，
-- andb false c ≡ true な c は無いので⊥になりその型の値は存在しない．
-- こうなったらそこに()を書いてそのケースは終わりでよい．
andb-true-elim1 : (b c : bool) → andb b c ≡ true → b ≡ true
andb-true-elim1 true _ _ = refl
andb-true-elim1 false _ ()

{-
練習問題: ★★ (andb-true-elim2)

destructを使い、case（もしくはsubcase）を作成して、以下の証明andb-true-elim2を完成させなさい。
-}
andb-true-elim2 : (b c : bool) → andb b c ≡ true → c ≡ true
andb-true-elim2 _ true eq = refl
andb-true-elim2 true false ()
andb-true-elim2 false false ()

-- 帰納法 ---------------------------------------------------------------------

-- 帰納法はパターンマッチからの再帰関数
n+O≡n : (n : nat) → n + 0 ≡ n
n+O≡n 0 = refl
n+O≡n (S n)
  rewrite n+O≡n n
        = refl

minus-diag : (n : nat) → minus n n ≡ 0
minus-diag 0 = refl
minus-diag (S n) = minus-diag n

{-
練習問題: ★★, recommended (basic-induction)
-}
n*O≡O : (n : nat) → n * 0 ≡ 0
n*O≡O 0 = refl
n*O≡O (S n)
  rewrite n*O≡O n
        = refl

plus-n-Sm : (n m : nat) → S (n + m) ≡ n + (S m)
plus-n-Sm 0     m = refl
plus-n-Sm (S n) m
  rewrite plus-n-Sm n m
        = refl

plus-comm : (n m : nat) → n + m ≡ m + n
plus-comm 0 m
  rewrite n+O≡n m
        = refl
plus-comm (S n) m
  rewrite plus-comm n m
        = plus-n-Sm m n


double : nat → nat
double 0 = 0
double (S n) = S (S (double n))

{-
練習問題: ★★ (double-plus)
-}
double-plus : (n : nat) → double n ≡ n + n
double-plus 0 = refl
double-plus (S n)
  rewrite double-plus n
        | plus-n-Sm n n
        = refl

{-
練習問題: ★ (destruct-induction)

destructとinductionの違いを短く説明しなさい。
-}
-- base case で証明した結果を step case で使えるかどうか．
-- なんだろうけどAgdaの場合あんまり気にしないからなー


-- 形式的証明と非形式的証明 ---------------------------------------------------


plus-assoc : (n m p : nat) → n + (m + p) ≡ (n + m) + p
plus-assoc 0 m p = refl
plus-assoc (S n) m p
  rewrite plus-assoc n m p
        = refl

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
beq-nat-refl : (n : nat) → true ≡ beq-nat n n
beq-nat-refl 0 = refl
beq-nat-refl (S n) = beq-nat-refl n


-- 証明の中で行う証明 ---------------------------------------------------------

mult-0-plus' : (n m : nat) → (0 + n) * m ≡ n * m
mult-0-plus' n m = cong (λ a → a * m) assert
  where -- assert相当ならwhereかなぁ?
    assert : 0 + n ≡ n
    assert = refl

plus-rearrange : (n m p q : nat) → (n + m) + (p + q) ≡ (m + n) + (p + q)
plus-rearrange n m p q = cong (λ a → a + (p + q)) assert
  where
    assert : n + m ≡ m + n
    assert = plus-comm n m

{-
練習問題: ★★★★ (mult-comm)

assertを使用して以下の証明を完成させなさい。ただしinduction（帰納法）を使用しないこと。
-}
-- 標準ライブラリから trans(transitivity) で a ≡ b → b ≡ c → a ≡ c
plus-swap : (n m p : nat) → n + (m + p) ≡ m + (n + p)
plus-swap n m p = trans (trans assert1 assert2) assert3
  where
    assert1 : n + (m + p) ≡ (n + m) + p
    assert1 = plus-assoc n m p
    assert2 : (n + m) + p ≡ (m + n) + p
    assert2 = cong (λ a → a + p) (plus-comm n m)
    assert3 : (m + n) + p ≡ m + (n + p)
    assert3 = sym (plus-assoc m n p)

-- このへんから流石に何やってんだになってくるかもなので，
-- 等価性の推移律(trans)を連打するよりも≡-Reasoningで書いたほうが証明の仕上がりが良い
plus-swap' : (n m p : nat) → n + (m + p) ≡ m + (n + p)
plus-swap' n m p =
  begin
     n + (m + p)
  ≡⟨ plus-assoc n m p ⟩
     (n + m) + p
  ≡⟨ cong (λ a → a + p) (plus-comm n m) ⟩
     (m + n) + p
-- 標準ライブラリから sym(symmetricity) で a ≡ b → b ≡ a
  ≡⟨ sym (plus-assoc m n p) ⟩
     m + (n + p)
  ∎
  where
    open PropEq.≡-Reasoning

{-
では、乗法が可換であることを証明しましょう。おそらく、補助的な定理を定義し、それを使って全体を証明することになると思います。先ほど証明したplus-swapが便利に使えるでしょう。
-}
mult-comm : (m n : nat) → m * n ≡ n * m
mult-comm 0 n = trans (0*l≡0 n) (sym (n*O≡O n))
mult-comm (S m) n = trans (cong (λ a → n + a) (mult-comm m n)) (mult-1-plus' n m)
  where
    mult-1-plus' : (n m : nat) → n + n * m ≡ n * (1 + m)
    mult-1-plus' 0 m = refl
    mult-1-plus' (S n) m = trans assert1' (trans assert2' (trans assert3' assert4'))
      where
        assert1' : (1 + n) + (m + n * m) ≡ m + (1 + n + n * m)
        assert1' = plus-swap (1 + n) m (n * m)
        assert2' : m + (1 + n + n * m) ≡ m + (1 + n * (1 + m))
        assert2' = cong (λ a → m + (1 + a)) (mult-1-plus' n m)
        assert3' : m + (1 + n * (1 + m)) ≡ (m + 1) + n * (1 + m)
        assert3' = plus-assoc m 1 (n * (1 + m))
        assert4' : (m + 1) + n * (1 + m) ≡ (1 + m) + n * (1 + m)
        assert4' = cong (λ a → a + n * (1 + m)) (plus-comm m 1)
    -- ≡-Reasoningで
    mult-1-plus'' : (n m : nat) → n + n * m ≡ n * (1 + m)
    mult-1-plus'' 0 m = refl
    mult-1-plus'' (S n) m =
      begin
        S n + S n * m
      ≡⟨ refl ⟩ -- Reasoningがreflの変形は別に書く必要は無いが可読性のため
        S n + (m + n * m)
      ≡⟨ plus-swap (S n) m (n * m) ⟩
        m + (S n + n * m)
      ≡⟨ refl ⟩
        m + ((1 + n) + n * m)
      ≡⟨ refl ⟩
        m + (1 + (n + n * m))
      ≡⟨ cong (λ a → m + (1 + a)) (mult-1-plus'' n m) ⟩
        m + (1 + n * (1 + m))
      ≡⟨ plus-assoc m 1 (n * (1 + m)) ⟩
        (m + 1) + n * (1 + m)
      ≡⟨ cong (λ a → a + n * (1 + m)) (plus-comm m 1) ⟩
        (1 + m) + n * (1 + m)
      ≡⟨ refl ⟩
        S n * (1 + m)
      ∎
      where
        open PropEq.≡-Reasoning
    -- rewriteだともっとシンプルにシュッとした感じになる
    -- 途中どのように式変形されたかはコードから一見わからない．
    -- ただ，congとかsymとかtransとか殆ど気にしないので書くにはラク
    mult-1-plus''' : (n m : nat) → n + n * m ≡ n * (1 + m)
    mult-1-plus''' 0 m = refl
    mult-1-plus''' (S n) m
      rewrite plus-swap (S n) m (n * m)
            | mult-1-plus'' n m
            | plus-assoc m 1 (n * (1 + m))
            | plus-comm m 1
            = refl

{-
練習問題: ★★, optional (evenb-n--oddb-Sn)
-}
evenb-n-oddb-Sn : (n : nat) → evenb n ≡ negb (evenb (S n))
evenb-n-oddb-Sn 0 = refl
evenb-n-oddb-Sn 1 = refl
evenb-n-oddb-Sn (S (S n)) = evenb-n-oddb-Sn n

-- さらなる練習問題 -----------------------------------------------------------

{-
練習問題: ★★★, optional (more-exercises)

紙を何枚か用意して、下に続く定理が(a)簡約と書き換えだけで証明可能か、(b)destructを使ったcase分割が必要になるか、(c)帰納法が必要となるか、のいずれに属すかを、紙の上だけで考えなさい。予測を紙に書いたら、実際に証明を完成させなさい。証明にはCoqを用いてかまいません。最初に紙を使ったのは「初心忘れるべからず」といった理由です。
-}
ble-nat-refl : (n : nat) → true ≡ ble-nat n n
ble-nat-refl 0 = refl
ble-nat-refl (S n) = ble-nat-refl n

zero-nbeq-S : (n : nat) → beq-nat 0 (S n) ≡ false
zero-nbeq-S n = refl

andb-false-r : (b : bool) → andb b false ≡ false
andb-false-r true = refl
andb-false-r false = refl

plus-ble-compat-l : (n m p : nat) → ble-nat n m ≡ true → ble-nat (p + n) (p + m) ≡ true
plus-ble-compat-l n m 0 eq = eq
plus-ble-compat-l n m (S p) eq = plus-ble-compat-l n m p eq

S-nbeq-0 : (n : nat) → beq-nat (S n) 0 ≡ false
S-nbeq-0 n = refl

mult-1-l : (n : nat) → 1 * n ≡ n
mult-1-l = n+O≡n

all3-spec : (b c : bool) → orb (andb b c) (orb (negb b) (negb c)) ≡ true
all3-spec true true = refl
all3-spec true false = refl
all3-spec false true = refl
all3-spec false false = refl

mult-plus-distr-r : (n m p : nat) → (n + m) * p ≡ (n * p) + (m * p)
mult-plus-distr-r 0 m p = refl
mult-plus-distr-r (S n) m p
  rewrite mult-plus-distr-r n m p
        = plus-assoc p (n * p) (m * p)

mult-assoc : (n m p : nat) → n * (m * p) ≡ (n * m) * p
mult-assoc 0 m p = refl
mult-assoc (S n) m p
  rewrite mult-assoc n m p
        | mult-plus-distr-r m (n * m) p
        = refl


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
data bin : Set where
  Zero : bin
  Shift : bin → bin
  ShiftInc : bin → bin

{-
(b) 先に定義したbin型の値をインクリメントする関数を作成しなさい。また、bin型をnat型に変換する関数も作成しなさい。
-}
inc-bin : bin → bin
inc-bin Zero = ShiftInc Zero
inc-bin (Shift n) = ShiftInc n
inc-bin (ShiftInc n) = Shift (inc-bin n)

bin→nat : bin → nat
bin→nat Zero = O
bin→nat (Shift n) = double (bin→nat n)
bin→nat (ShiftInc n) = S (double (bin→nat n))

{-
(c) 最後にbで作成したインクリメント関数と、2進→自然数関数が可換であることを証明しなさい。これを証明するには、bin値をまずインクリメントしたものを自然数に変換したものが、先に自然数変換した後にインクリメントしたものの値と等しいことを証明すればよい。
-}
inc-bin-commute-bin→nat : (n : bin) → bin→nat (inc-bin n) ≡ S (bin→nat n)
inc-bin-commute-bin→nat Zero = refl
inc-bin-commute-bin→nat (Shift n) = refl
inc-bin-commute-bin→nat (ShiftInc n)
  rewrite inc-bin-commute-bin→nat n
        = refl

{-
練習問題: ★★★★★ (binary_inverse)

この練習問題は前の問題の続きで、2進数に関するものである。前の問題で作成された定義や定理をここで用いてもよい。

(a) まず自然数を2進数に変換する関数を書きなさい。そして「任意の自然数からスタートし、それを2進数にコンバートし、それをさらに自然数にコンバートすると、スタート時の自然数に戻ることを証明しなさい。
-}
nat→bin : nat → bin
nat→bin 0 = Zero
nat→bin (S n) = inc-bin (nat→bin n)

nat→bin→nat : (n : nat) → bin→nat (nat→bin n) ≡ n
nat→bin→nat 0 = refl
nat→bin→nat (S n)
  rewrite inc-bin-commute-bin→nat (nat→bin n)
        | nat→bin→nat n
        = refl

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
normalize : bin → bin
normalize n = nat→bin (bin→nat n)

normalize-idempotent : (n : bin) → normalize (normalize n) ≡ normalize n
normalize-idempotent n
  rewrite nat→bin→nat (bin→nat n)
        = refl

{-
練習問題: ★★, optional (decreasing)

各関数の引数のいくつかが"減少的"でなければならない、という要求仕様は、Coqのデザインにおいて基礎となっているものです。特に、そのことによって、Coq上で作成された関数が、どんな入力を与えられても必ずいつか終了する、ということが保障されています。しかし、Coqの"減少的な解析"が「とても洗練されているとまではいえない」ため、時には不自然な書き方で関数を定義しなければならない、ということもあります。

これを具体的に感じるため、Fixpointで定義された、より「微妙な」関数の書き方を考えてみましょう（自然数に関する簡単な関数でかまいません）。それが全ての入力で停止することと、Coqがそれを、この制限のため受け入れてくれないことを確認しなさい。
-}

{- こういうのとか？(でもこれWF-Recとかでちゃんと書けば止まるはず)
f : nat → nat
f 0 = 0
f (S n) = f (div2 n)
  where
    div2 : nat → nat
    div2 0 = 0
    div2 1 = 0
    div2 (S (S n)) = S (div2 n)
-}
