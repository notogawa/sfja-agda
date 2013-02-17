-- Prop って予約されてたっけ？無くなったよな？
module Prop-J where

open import Level
open import Function
-- open import Data.Bool
-- open import Data.Nat
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; sym; cong; trans)

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
data MyProp : nat → Set where
  MyProp1 : MyProp 4
  MyProp2 : ∀ n → MyProp n → MyProp (4 + n)
  MyProp3 : ∀ n → MyProp (2 + n) → MyProp n

MyProp-ten : MyProp 10
MyProp-ten = MyProp2 (S (S (S (S (S (S O))))))
               (MyProp2 (S (S O)) (MyProp3 (S (S O)) MyProp1))

{-
練習問題: ★★ (MyProp)

MyPropに関する便利な2つの事実があります。 証明はあなたのために残してあります。
-}
MyProp-0 : MyProp 0
MyProp-0 = MyProp3 O (MyProp3 (S (S O)) MyProp1)

MyProp-plustwo : ∀ n → MyProp n → MyProp (S (S n))
MyProp-plustwo n propn = MyProp3 (S (S n)) (MyProp2 n propn)

-- 奇数？偶数だよね？
MyProp-ev : ∀ n → ev n → MyProp n
MyProp-ev .0 ev-0 = MyProp-0
MyProp-ev .(S (S n)) (ev-SS {n} evn) = MyProp-plustwo n $ MyProp-ev n evn

{-
練習問題: ★★★ (ev_MyProp)
-}
ev-MyProp : ∀ n → MyProp n → ev n
ev-MyProp .4 MyProp1 = ev-SS (ev-SS ev-0)
ev-MyProp .(S (S (S (S n)))) (MyProp2 n propn) = ev-SS (ev-SS (ev-MyProp n propn))
ev-MyProp n (MyProp3 .n propn) = ev-minus2 (S (S n)) (ev-MyProp (S (S n)) propn)

{-
練習問題: ★★★, optional (ev_MyProp_informal)
-}
-- 略


-- 全体像: Coqの2つの空間 -----------------------------------------------------

---- 値 -----------------------------------------------------------------------

---- 帰納的定義 ---------------------------------------------------------------

---- 型とカインド -------------------------------------------------------------

---- 命題 vs. ブール値 --------------------------------------------------------

---- 関数 vs. 限量子 ----------------------------------------------------------

---- 関数 vs. 含意 ------------------------------------------------------------

-- 非形式的な証明 -------------------------------------------------------------

---- 帰納法による非形式的な証明 -----------------------------------------------

------ 帰納的に定義された集合についての帰納法 ---------------------------------

------ 帰納的に定義された命題についての帰納法 ---------------------------------

-- 選択課題 -------------------------------------------------------------------

---- induction タクティックについてもう少し -----------------------------------
{-
練習問題: ★, optional (plus_explicit_prop)

plus_assoc' と plus_comm' を、その証明とともに上の mult_0_r'' と 同じスタイルになるよう書き直しなさい。このことは、それぞれの定理が 帰納法で証明された命題に明確な定義を与え、この定義された命題から定理と 証明を示しています。
-}
plus-assoc' : ∀ n m p → n + (m + p) ≡ (n + m) + p
plus-assoc' n = nat-ind (λ n → ∀ m p → n + (m + p) ≡ (n + m) + p) base step n
  where
    base = λ m p → refl
    step : ∀ n  → (∀ m p → n + (m + p) ≡ (n + m) + p) → (∀ m p → S n + (m + p) ≡ (S n + m) + p)
    step n eq m p
      rewrite eq m p
            = refl

plus-comm' : ∀ n m → n + m ≡ m + n
plus-comm' n = nat-ind (λ n → ∀ m → n + m ≡ m + n) base step n
  where
    base = sym ∘ n+O≡n
    step : ∀ n → (∀ m → n + m ≡ m + n) → (∀ m → S n + m ≡ m + S n)
    step n eq m
      rewrite eq m
            | plus-n-Sm m n
            = refl

{-
練習問題: ★★★★, optional (true_upto_n__true_everywhere)

true_upto_n_example を満たすような再帰関数 true_upto_n__true_everywhere を定義しなさい。
-}
-- true_upto_n_example？

---- Prop における帰納法の原理 ------------------------------------------------

{-
練習問題: ★★★, optional (prop_ind)

帰納的に定義された list と MyProp に対し、Coq がどのような帰納法の原理を 生成するか、予想して書き出し、次の行を実行した結果と比較しなさい。
-}
-- 略

{-
練習問題: ★★★, optional (ev_MyProp')

もう一度 ev_MyProp を証明しなさい。ただし、今度は induction タクティックの代わりに apply MyProp_ind を使いなさい。
-}
-- 略

{-
練習問題: ★★★★, optional (MyProp_pfobj)

もう一度 MyProp_ev と ev_MyProp を証明しなさい。ただし今度は、明確な 証明オブジェクトを手作業で構築（上の ev_plus4 でやったように）することで 証明しなさい。
-}
-- 略

-- このへんAgda的にはあんまり

{-
練習問題: ★★★, optional (p_provability)

次の、帰納的に定義された命題について考えてみてください。：

  Inductive p : (tree nat) → nat → Prop :=
    c1 : ∀ n, p (leaf _ n) 1
    c2 : ∀ t1 t2 n1 n2, p t1 n1 → p t2 n2 → p (node _ t1 t2) (n1 + n2)
    c3 : ∀ t n, p t n → p t (S n).

これについて、どのような時に p t n が証明可能であるか、その 条件をを自然言語で説明しなさい。
-}
-- tree t 任意のnodeかleafにおいて，対応するnがその子孫の要素の数以上

-- 追加練習問題 ---------------------------------------------------------------

{-
練習問題: ★★★★ (palindromes)

palindrome（回文）は、最初から読んでも逆から読んでも同じになるような シーケンスです。

list X でパラメータ化され、それが palindrome であることを示すような帰納的

命題 pal を定義しなさい。（ヒント：これには三つのケースが必要です。この定義は、 リストの構造に基いたものとなるはずです。まず一つのコンストラクタ、

   c : ∀ l, l = rev l → pal l

 は明らかですが、これはあまりうまくいきません。）
-}
data pal {x} {X : Set x} : list X → Set x where
  pal-nil : pal []
  pal-singleton : ∀ x → pal (x ∷ [])
  pal-cons : ∀ x ls → pal ls → pal (x ∷ snoc ls x)
{-

 以下を証明しなさい。

   ∀ l, pal (l ++ rev l).
-}
pal-l++rev-l : ∀ {x} {X : Set x} → (ls : list X) → pal (ls ++ rev ls)
pal-l++rev-l [] = pal-nil
pal-l++rev-l (x ∷ ls)
  rewrite sym (snoc-with-append x ls (rev ls))
        = pal-cons x (ls ++ rev ls) (pal-l++rev-l ls)
{-

 以下を証明しなさい。

   ∀ l, pal l → l = rev l.
-}
pal-l→l≡rev-l : ∀ {x} {X : Set x} → (ls : list X) → pal ls → ls ≡ rev ls
pal-l→l≡rev-l .[] pal-nil = refl
pal-l→l≡rev-l .(x ∷ []) (pal-singleton x) = refl
pal-l→l≡rev-l .(x ∷ snoc ls x) (pal-cons x ls palls)
  rewrite rev-snoc x ls
        | sym (pal-l→l≡rev-l ls palls)
        = refl

{-
練習問題: ★★★★★, optional (palindrome_converse)

一つ前の練習問題で定義した pal を使って、これを証明しなさい。
     ∀ l, l = rev l → pal l.
-} -- l₁ ∷ l₂ ∷ ls ≡ a ∷ snoc xs b → a ≡ b ∧ xs ≡ rev xs
private
  module Proof where
    last : ∀ {x} {X : Set x} → (xs : list X) → beq-nat 0 (length xs) ≡ false → X
    last [] ()
    last (x ∷ []) refl = x
    last (_ ∷ x' ∷ xs) refl = last (x' ∷ xs) refl
    init : ∀ {x} {X : Set x} → (xs : list X) → beq-nat 0 (length xs) ≡ false → list X
    init [] ()
    init (_ ∷ []) refl = []
    init (x ∷ x' ∷ xs) refl = x ∷ init (x' ∷ xs) refl
    length-snoc : ∀ {x} {X : Set x} →
                  (l : X) → (ls : list X) →
                  beq-nat 0 (length (snoc ls l)) ≡ false
    length-snoc _ [] = refl
    length-snoc _ (_ ∷ _) = refl
    length-init : ∀ {x} {X : Set x} → (x : X) → (xs : list X) →
                  length (init (x ∷ xs) refl) ≡ length xs
    length-init _ [] = refl
    length-init _ (x₁ ∷ xs) = cong S (length-init _ xs)
    xs→snoc-init-xs-last-xs : ∀ {x} {X : Set x} → (xs : list X) → (eq : beq-nat 0 (length xs) ≡ false) → xs ≡ snoc (init xs eq) (last xs eq)
    xs→snoc-init-xs-last-xs [] ()
    xs→snoc-init-xs-last-xs (x ∷ []) refl = refl
    xs→snoc-init-xs-last-xs (x ∷ x' ∷ xs) refl = cong (_∷_ x) $ xs→snoc-init-xs-last-xs (x' ∷ xs) refl
    head-inversion : ∀{x} {X : Set x} →
                     (a b : X) → (as bs : list X) →
                     a ∷ as ≡ b ∷ bs → a ≡ b
    head-inversion .b b .bs bs refl = refl
    tail-inversion : ∀{x} {X : Set x} →
                     (a b : X) → (as bs : list X) →
                     a ∷ as ≡ b ∷ bs → as ≡ bs
    tail-inversion .b b .bs bs refl = refl
    rev-snoc-commute-rev-cons : ∀{x} {X : Set x} → (n : X) (ls : list X) → rev (snoc ls n) ≡ n ∷ rev ls
    rev-snoc-commute-rev-cons n [] = refl
    rev-snoc-commute-rev-cons n (x ∷ xs) = cong (λ as → snoc as x) (rev-snoc-commute-rev-cons n xs)
    rev-involutive : ∀{x} {X : Set x} → (l : list X) → rev (rev l) ≡ l
    rev-involutive [] = refl
    rev-involutive (x ∷ xs)
      rewrite rev-snoc-commute-rev-cons x (rev xs)
            | rev-involutive xs
            = refl
    rev-injective : ∀{x} {X : Set x} → (l1 l2 : list X) → rev l1 ≡ rev l2 → l1 ≡ l2
    rev-injective xs ys eq = rev-injective' (cong rev eq)
      where
        rev-injective' : rev (rev xs) ≡ rev (rev ys) → xs ≡ ys
        rev-injective' eq
          rewrite rev-involutive xs
                | rev-involutive ys
                = eq

    -- 止まんねー
{-
    l≡rev-l→pal-l : ∀ {x} {X : Set x} →
                    (ls : list X) → ls ≡ rev ls → pal ls
    l≡rev-l→pal-l [] eq = pal-nil
    l≡rev-l→pal-l (x₁ ∷ []) eq = pal-singleton x₁
    l≡rev-l→pal-l (x₁ ∷ x₂ ∷ xs) eq
      rewrite cong (λ as → rev (x₁ ∷ as)) (xs→snoc-init-xs-last-xs (x₂ ∷ xs) refl)
            | rev-snoc (last (x₂ ∷ xs) refl) (init (x₂ ∷ xs) refl)
            | cong (λ as → x₁ ∷ as) (xs→snoc-init-xs-last-xs (x₂ ∷ xs) refl)
            | sym (head-inversion _ _ _ _ eq)
            = pal-cons x₁ init-xs $
              l≡rev-l→pal-l init-xs $ -- initだから小さくなってることがわからないのか
              rev-injective init-xs (rev init-xs) $
              tail-inversion last-xs x₁ _ _ $
              (sym (rev-snoc last-xs init-xs) ⟨ trans ⟩
               cong rev (tail-inversion _ _ _ _ eq) ⟨ trans ⟩
               rev-snoc x₁ (rev init-xs))
      where
        init-xs = init (x₂ ∷ xs) refl
        last-xs = last (x₂ ∷ xs) refl

l≡rev-l→pal-l = Proof.l≡rev-l→pal-l
-}

{-
練習問題: ★★★★ (subsequence)

あるリストが、別のリストのサブシーケンス（ subsequence ）であるとは、 最初のリストの要素が全て二つ目のリストに同じ順序で現れるということです。 ただし、その間に何か別の要素が入ってもかまいません。例えば、

    [1,2,3]

は、次のいずれのリストのサブシーケンスでもあります。

    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]

しかし、次のいずれのリストのサブシーケンスでもありません。

    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

list nat 上に、そのリストがサブシーケンスであることを意味するような命題 subseq を定義しなさい。（ヒント：三つのケースが必要になります）
-}
data subseq : list nat → list nat → Set where
  subseq-nil : subseq [] []
  subseq-seq : ∀ {ss xs} x → subseq ss xs → subseq ss (x ∷ xs)
  subseq-both : ∀ {ss xs} x → subseq ss xs → subseq (x ∷ ss) (x ∷ xs)
{-
サブシーケンスである、という関係が「反射的」であることを証明しなさい。つまり、どのようなリストも、それ自身のサブシーケンスであるということです。
-}
subseq-refl : ∀ xs → subseq xs xs
subseq-refl [] = subseq-nil
subseq-refl (x ∷ xs) = subseq-both x (subseq-refl xs)
{-
任意のリスト l1、 l2、 l3 について、もし l1 が l2 のサブシーケンスならば、 l1 は l2 ++ l3 のサブシーケンスでもある、ということを証明しなさい。.
-}
app-nil : ∀{x} {X : Set x} →
          (l : list X) → l ++ [] ≡ l
app-nil [] = refl
app-nil (x₁ ∷ xs) = cong (_∷_ x₁) (app-nil xs)

subseq-++ : ∀ l1 l2 l3 → subseq l1 l2 → subseq l1 (l2 ++ l3)
subseq-++ l1 l2 [] ss
  rewrite app-nil l2
        = ss
subseq-++ .[] .[] (x ∷ l3) subseq-nil = subseq-seq x (subseq-++ [] [] l3 subseq-nil)
subseq-++ l1 .(x₁ ∷ xs) (x ∷ l3) (subseq-seq {.l1} {xs} x₁ ss) = subseq-seq x₁ (subseq-++ l1 xs (x ∷ l3) ss)
subseq-++ .(x₁ ∷ ss) .(x₁ ∷ xs) (x ∷ l3) (subseq-both {ss} {xs} x₁ ss₁) = subseq-both x₁ (subseq-++ ss xs (x ∷ l3) ss₁)
{-
（これは少し難しいですので、任意とします）サブシーケンスという関係は推移的である、つまり、 l1 が l2 のサブシーケンスであり、 l2 が l3 のサブシーケンスであるなら、 l1 は l3 のサブシーケンスである、というような関係であることを証明しなさい。（ヒント：何について帰納法を適用するか、よくよく注意して下さい。）
-}
-- 全部c-c c-aだった
subseq-trans : ∀ l1 l2 l3 → subseq l1 l2 → subseq l2 l3 → subseq l1 l3
subseq-trans .[] .[] l3 subseq-nil ss23 = ss23
subseq-trans l1 .(x ∷ xs) .(x₁ ∷ xs₁) (subseq-seq {.l1} {xs} x ss12) (subseq-seq {.(x ∷ xs)} {xs₁} x₁ ss23) = subseq-seq x₁
                                                                                                                (subseq-trans l1 (x ∷ xs) xs₁ (subseq-seq x ss12) ss23)
subseq-trans l1 .(x ∷ xs) .(x ∷ xs₁) (subseq-seq {.l1} {xs} x ss12) (subseq-both {.xs} {xs₁} .x ss23) = subseq-seq x (subseq-trans l1 xs xs₁ ss12 ss23)
subseq-trans .(x ∷ ss) .(x ∷ xs) .(x₁ ∷ xs₁) (subseq-both {ss} {xs} x ss12) (subseq-seq {.(x ∷ xs)} {xs₁} x₁ ss23) = subseq-seq x₁
                                                                                                                       (subseq-trans (x ∷ ss) (x ∷ xs) xs₁ (subseq-both x ss12) ss23)
subseq-trans .(x ∷ ss) .(x ∷ xs) .(x ∷ xs₁) (subseq-both {ss} {xs} x ss12) (subseq-both {.xs} {xs₁} .x ss23) = subseq-both x (subseq-trans ss xs xs₁ ss12 ss23)

{-
練習問題: ★★, optional (foo_ind_principle)
-}
-- 略

{-
練習問題: ★★, optional (bar_ind_principle)
-}
-- 略

{-
練習問題: ★★, optional (no_longer_than_ind)
-}
-- 略

{-
練習問題: ★★, optional (R_provability)
-}
-- Rは「リスト長が数値以上の何か」なので証明可能なのは．
-- R 2 [1,0]
-- R 1 [1,2,1,0]
