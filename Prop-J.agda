-- Prop って予約されてたっけ？無くなったよな？
module Prop-J where

open import Level
open import Function
-- open import Data.Bool
-- open import Data.Nat
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; cong₂; trans; subst)

open import Basics-J
open import Poly-J

-- 命題によるプログラミング ---------------------------------------------------

2+2≡4 : 2 + 2 ≡ 4
2+2≡4 = refl

plus-fact : Set
plus-fact = 2 + 2 ≡ 4

plus-fact-is-true : plus-fact
plus-fact-is-true = refl

strange-prop1 : Set
strange-prop1 = 2 + 2 ≡ 5 → 99 + 26 ≡ 42

strange-prop2 : Set
strange-prop2 = ∀ n → beq-nat n 17 ≡ true → beq-nat n 99 ≡ true

even : nat → Set
even n = evenb n ≡ true

even-n→even-SSn : nat → Set
even-n→even-SSn n = even n → even (S (S n))

between : (n m o : nat) → Set
between n m o = andb (beq-nat n o) (beq-nat o m) ≡ true

teen : nat → Set
teen = between 13 19

true-for-zero : (nat → Set) → Set
true-for-zero P = P 0

preserved-by-S : (nat → Set) → Set
preserved-by-S P = ∀ n → P n → P (S n)

true-for-all-numbers : (nat → Set) → Set
true-for-all-numbers P = ∀ n → P n

our-nat-induction : (nat → Set) → Set
our-nat-induction P = true-for-zero P → preserved-by-S P → true-for-all-numbers P

-- Coqのnat_ind相当？
nat-ind : (P : nat → Set) → our-nat-induction P
nat-ind P base step 0 = base
nat-ind P base step (S n) = nat-ind (P ∘ S) (step 0 base) (step ∘ S) n

-- 根拠 -----------------------------------------------------------------------

---- 帰納的に定義された命題 ---------------------------------------------------

data good-day : day → Set where
  gd-sat : good-day saturday
  gd-sun : good-day sunday

gds : good-day sunday
gds = gd-sun

data day-before : day → day → Set where
  db-tue : day-before tuesday monday
  db-wed : day-before wednesday tuesday
  db-thu : day-before thursday wednesday
  db-fri : day-before friday thursday
  db-sat : day-before saturday friday
  db-sun : day-before sunday saturday
  db-mon : day-before monday sunday

data fine-day-for-singing : day → Set where
  fdfs-any : ∀ d → fine-day-for-singing d

fdfs-wed : fine-day-for-singing wednesday
fdfs-wed = fdfs-any wednesday

---- 証明オブジェクト ---------------------------------------------------------

data ok-day : day → Set where
  okd-gd : ∀ d → good-day d → ok-day d
  okd-before : ∀ d1 d2 → ok-day d2 → day-before d2 d1 → ok-day d1

-- okdw = ? からのc-c c-aで
okdw : ok-day wednesday
okdw = okd-before wednesday thursday
         (okd-before thursday friday
          (okd-before friday saturday (okd-gd saturday gd-sat) db-sat)
          db-fri)
         db-thu

---- カリー・ハワード対応 -----------------------------------------------------

---- 含意 ---------------------------------------------------------------------

{-
練習問題: ★, optional (okd_before2_valid)
-}
okd-before2-valid : ∀ d1 d2 d3 → ok-day d3 → day-before d2 d1 → day-before d3 d2 → ok-day d1
okd-before2-valid = λ d1 d2 d3 z z₁ z₂ → okd-before d1 d2 (okd-before d2 d3 z z₂) z₁

{-
練習問題: ★, optional (okd_before2_valid_defn)
-}
-- 略

---- 帰納的に定義された型に対する帰納法の原理 ---------------------------------

-- こういうことかな．
n*0≡0 : ∀ n → n * 0 ≡ 0
n*0≡0 = nat-ind (λ n₁ → n₁ * 0 ≡ 0) refl (λ n₁ z → z)
-- つまり，coq の apply nat_ind の動きとしては，
-- ゴールの"∀をλに機械的に置換したもの"をPとして nat-ind に食わせる．
-- そして base case と step case をサブゴールに入れた形を作るわけね．
-- induction も単純なラッパーというか，まぁ殆ど同じ．

{-
練習問題: ★★ (plus_one_r')

induction タクティックを使わずに、下記の証明を完成させなさい。
-}
n+1≡Sn : ∀ n → n + 1 ≡ S n
n+1≡Sn = nat-ind (λ n → n + 1 ≡ S n) refl (λ n → cong S)

{-
練習問題: ★ (rgb)

次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。 紙に答えを書いたのち、Coqの出力と比較しなさい。
-}
-- 略

data natlist : Set where
  nnil : natlist
  ncons : nat → natlist → natlist

true-for-nnil : (natlist → Set) → Set
true-for-nnil P = P nnil

preserved-by-ncons : (natlist → Set) → Set
preserved-by-ncons P = ∀ x xs → P xs → P (ncons x xs)

true-for-all-natlists : (natlist → Set) → Set
true-for-all-natlists P = ∀ xs → P xs

our-natlist-induction : (natlist → Set) → Set
our-natlist-induction P = true-for-nnil P → preserved-by-ncons P → true-for-all-natlists P

natlist-ind : (P : natlist → Set) → our-natlist-induction P
natlist-ind P base step nnil = base
natlist-ind P base step (ncons x xs) = step x xs (natlist-ind P base step xs)

{-
練習問題: ★ (natlist1)

上記の定義をすこし変えたとしましょう。
-}
data natlist1 : Set where
  nnil1 : natlist1
  nsnoc1 : natlist1 → nat → natlist1
{-
このとき、帰納法の原理はどのようになるでしょうか？
-}
true-for-nnil1 : (natlist1 → Set) → Set
true-for-nnil1 P = P nnil1

preserved-by-nsnoc1 : (natlist1 → Set) → Set
preserved-by-nsnoc1 P = ∀ xs x → P xs → P (nsnoc1 xs x)

true-for-all-natlist1s : (natlist1 → Set) → Set
true-for-all-natlist1s P = ∀ xs → P xs

our-natlist1-induction : (natlist1 → Set) → Set
our-natlist1-induction P = true-for-nnil1 P → preserved-by-nsnoc1 P → true-for-all-natlist1s P

natlist1-ind : (P : natlist1 → Set) → our-natlist1-induction P
natlist1-ind P base step nnil1 = base
natlist1-ind P base step (nsnoc1 xs x) = step xs x (natlist1-ind P base step xs)

{-
練習問題: ★ (ExSet)

帰納的に定義された集合に対する帰納法の原理が次のようなものだとします。

      ExSet_ind :
               ∀ P : ExSet → Prop,
                     (∀ b : bool, P (con1 b)) →
                     (∀ (n : nat) (e : ExSet), P e → P (con2 n e)) →
                     ∀ e : ExSet, P e

ExSet の帰納的な定義を示しなさい。

-}
data ExSet : Set where
  con1 : bool → ExSet
  con2 : nat → ExSet → ExSet


true-for-[] : ∀{x} {X : Set x} → (list X → Set x) → Set x
true-for-[] P = P []

preserved-by-∷ : ∀{x} {X : Set x} → (list X → Set x) → Set x
preserved-by-∷ P = ∀ x xs → P xs → P (x ∷ xs)

true-for-all-lists : ∀{x} {X : Set x} → (list X → Set x) → Set x
true-for-all-lists P = ∀ xs → P xs

our-list-induction : ∀{x} {X : Set x} → (list X → Set x) → Set x
our-list-induction P = true-for-[] P → preserved-by-∷ P → true-for-all-lists P

list-ind : ∀{x} {X : Set x} → (P : list X → Set x) → our-list-induction P
list-ind P base step [] = base
list-ind P base step (x ∷ xs) = step x xs (list-ind P base step xs)

{-
練習問題: ★ (tree)

次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。 答えが書けたら、それをCoqの出力と比較しなさい。
-}
data tree {x} (X : Set x) : Set x where
  leaf : X → tree X
  node : tree X → tree X → tree X
{-
予想
   tree_ind :
     ∀ (X : Type) (P : tree X → Prop),
       (∀ (x : X), P (leaf x)) →
       (∀ (l : tree X) (r : tree X), P l → P r → P (node l r)) →
       ∀ t : tree X, P t
-}

true-for-leaf : ∀{x} {X : Set x} → (tree X → Set x) → Set x
true-for-leaf P = ∀ x → P (leaf x)

preserved-by-node : ∀{x} {X : Set x} → (tree X → Set x) → Set x
preserved-by-node P = ∀ l r → P l → P r → P (node l r)

true-for-all-trees : ∀{x} {X : Set x} → (tree X → Set x) → Set x
true-for-all-trees P = ∀ t → P t

our-tree-induction : ∀{x} {X : Set x} → (tree X → Set x) → Set x
our-tree-induction P = true-for-leaf P → preserved-by-node P → true-for-all-trees P

tree-ind : ∀{x} {X : Set x} → (P : tree X → Set x) → our-tree-induction P
tree-ind P base step (leaf x) = base x
tree-ind P base step (node l r) = step l r (tree-ind P base step l) (tree-ind P base step r)

{-
練習問題: ★ (mytype)

以下の帰納法の原理を生成する帰納的定義を探しなさい。

      mytype_ind :
        ∀ (X : Type) (P : mytype X → Prop),
           (∀ x : X, P (constr1 X x)) →
           (∀ n : nat, P (constr2 X n)) →
           (∀ m : mytype X, P m →
           ∀ n : nat, P (constr3 X m n)) →
           ∀ m : mytype X, P m
-}
data mytype {x} (X : Set x) : Set x where
  constr1 : X → mytype X
  constr2 : nat → mytype X
  constr3 : mytype X → nat → mytype X

{-
練習問題: ★, optional (foo)

以下の帰納法の原理を生成する帰納的定義を探しなさい。

      foo_ind :
        ∀ (X Y : Type) (P : foo X Y → Prop),
          (∀ x : X, P (bar X Y x)) →
          (∀ y : Y, P (baz X Y y)) →
          (∀ f1 : nat → foo X Y,
          (∀ n : nat, P (f1 n)) → P (quux X Y f1)) →
          ∀ f2 : foo X Y, P f2
-}
data foo {x y} (X : Set x) (Y : Set y) : Set (x ⊔ y) where
  bar : X → foo X Y
  baz : Y → foo X Y
  quux : (nat → foo X Y) → foo X Y

{-
練習問題: ★, optional (foo')
-}
-- 略

---- 帰納法の仮定 -------------------------------------------------------------

---- 偶数について再び ---------------------------------------------------------
data ev : nat → Set where
  ev-0 : ev O
  ev-SS : {n : nat} → ev n → ev (S (S n))


{-
練習問題: ★, optional (four_ev)

4が偶数であることをタクティックによる証明と証明オブジェクトによる証明で示しなさい。
-}
four-ev : ev 4
four-ev = ev-SS (ev-SS ev-0)

{-
練習問題: ★★ (ev_plus4)

n が偶数ならば 4+n も偶数であることをタクティックによる証明と証明オブジェクトによる証明で示しなさい。
-}
ev-plus4 : ∀ n → ev n → ev (4 + n)
ev-plus4 n evn = ev-SS (ev-SS evn)

{-
練習問題: ★★ (double_even)

次の命題をタクティックによって証明しなさい。
-}
double-even : ∀ n → ev (double n)
double-even = nat-ind (λ n₁ → ev (double n₁)) ev-0 (λ n₁ → ev-SS)

{-
練習問題: ★★★★, optional (double_even_pfobj)

上記のタクティックによる証明でどのような証明オブジェクトが構築されるかを予想しなさい。 (答を確かめる前に、Case を除去しましょう。 これがあると証明オブジェクトが少し見づらくなります。)
-}
-- 略

---- 根拠に対する帰納法の推論 -------------------------------------------------

-- ev-minus2 n evn = ? で c-c c-l してから
-- c-c evn で evn を destruct して，
-- あとは各ゴールで c-c c-a
ev-minus2 : ∀ n → ev n → ev (pred (pred n))
ev-minus2 .0 ev-0 = ev-0
ev-minus2 .(S (S n)) (ev-SS {n} evn) = evn

{-
練習問題: ★ (ev_minus2_n)

E の代わりに n に対して destruct するとどうなるでしょうか?
-}
-- 略

ev-even : ∀ n → ev n → even n
ev-even .0 ev-0 = refl
ev-even .(S (S n)) (ev-SS {n} evn) = ev-even n evn

{-
練習問題: ★ (ev_even_n)

この証明を E でなく n に対する帰納法として実施できますか?
-}
-- 奇数で⊥になるので，全てのnでそうなることを示すnの帰納法ではできない

{-
練習問題: ★ (l_fails)

次の証明はうまくいきません。

     Theorem l : ∀ n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...

理由を簡潔に説明しない。
-}
-- 奇数がevじゃないから定理が間違ってる

{-
練習問題: ★★ (ev_sum)

帰納法が必要な別の練習問題をやってみましょう。
-}
ev-sum : ∀ n m → ev n → ev m → ev (n + m)
ev-sum .0 m ev-0 evm = evm
ev-sum .(S (S n)) m (ev-SS {n} evn) evm = ev-SS (ev-sum n m evn evm)


SSev-even : ∀ n → ev (S (S n)) → ev n
SSev-even n (ev-SS evSSn) = evSSn

{-
練習問題: ★ (inversion_practice)
-}
SSSSev-even : ∀ n → ev (S (S (S (S n)))) → ev n
SSSSev-even n (ev-SS (ev-SS evSSSSn)) = evSSSSn



even5-nonsense : ev 5 → 2 + 2 ≡ 9
even5-nonsense (ev-SS (ev-SS ()))

{-
練習問題: ★★★ (ev_ev_even)

何に対して帰納法を行えばいいかを探しなさい。(ちょっとトリッキーですが)
-}
-- ev n だね
ev-ev-even : ∀ n m → ev (n + m) → ev n → ev m
ev-ev-even .0 m evn+m ev-0 = evn+m
ev-ev-even .(S (S n)) m evn+m (ev-SS {n} evn) = ev-ev-even n m (SSev-even (n + m) evn+m) evn

{-
練習問題: ★★★, optional (ev_plus_plus)

既存の補題を適用する必要のある練習問題です。 帰納法も場合分けも不要ですが、書き換えのうちいくつかはちょっと大変です。 Basics_J.v の plus_swap' で使った replace タクティックを使うとよいかもしれません。
-}
ev-plus-plus : ∀ n m p → ev (n + m) → ev (n + p) → ev (m + p)
ev-plus-plus n m p evn+m evn+p = ev-ev-even (n + n) (m + p) evn+n+m+p evn+n
  where
    evn+n+m+p : ev (n + n + (m + p))
    evn+n+m+p
      rewrite sym (plus-assoc n n (m + p))
            | plus-assoc n m p
            | plus-comm n m
            | sym (plus-assoc m n p)
            | plus-assoc n m (n + p)
            = ev-sum (n + m) (n + p) evn+m evn+p
    evn+n : ev (n + n)
    evn+n
      rewrite sym (double-plus n)
            = double-even n

---- なぜ命題を帰納的に定義するのか? ------------------------------------------