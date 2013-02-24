module Logic-J where

open import Level
open import Function
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl; sym; cong; trans)

open import Basics-J
open import Poly-J
open import Prop-J

-- 全称記号 と ならば ---------------------------------------------------------

postulate
  funny-prop1 : ∀ n (E : ev n) → ev (n + 4)
  funny-prop1' : ∀ n (_ : ev n) → ev (n + 4)
  funny-prop1'' : ∀ n → ev n → ev (n + 4)

-- 論理積、連言（Conjunction、AND） -------------------------------------------

-- ていうかペアと一緒なので．

and-example : ev 0 × ev 4
and-example = ev-0 , ev-SS (ev-SS ev-0)

and-example' : ev 0 × ev 4
and-example' = left , right
  where
    left = ev-0
    right = ev-SS (ev-SS ev-0)

proj₁ : ∀ {x y} {P : Set x} {Q : Set y} → P × Q → P
proj₁ (p , _) = p

{-
練習問題: ★, optional (proj2)
-}
proj₂ : ∀ {x y} {P : Set x} {Q : Set y} → P × Q → Q
proj₂ (_ , q) = q

and-commut : ∀ {x y} {P : Set x} {Q : Set y} → P × Q → Q × P
and-commut (p , q) = q , p

{-
練習問題: ★★ (and_assoc)

次の証明では、inversionが、入れ子構造になった命題H : P ∧ (Q ∧ R)を どのようにHP: P, HQ : Q, HR : R に分解するか、という点に注意しなが がら証明を完成させなさい。
-}
and-assoc : ∀ {x y z} {P : Set x} {Q : Set y} {R : Set z} → P × (Q × R) → (P × Q) × R
and-assoc (p , (q , r)) = (p , q) , r

{-
練習問題: ★★, recommended (even_ev)

今度は、前の章で棚上げしていた even と ev の等価性をが別の方向から 証明してみましょう。 ここで左側のandは我々が実際に注目すべきものです。右のandは帰納法の仮定と なって帰納法による証明に結びついていくことになるでしょう。なぜこれが必要と なるかは、左側のandをそれ自身で証明しようとして、行き詰まってみると かるでしょう。
-}
even-ev : ∀ n → (even n → ev n) × (even (S n) → ev (S n))
even-ev O = (λ x → ev-0) , (λ ())
even-ev (S O) = (λ ()) , (λ x → ev-SS ev-0)
even-ev (S (S n)) = (ev-SS ∘ proj₁ (even-ev n)) , (ev-SS ∘ proj₁ (even-ev (S n)))

{-
練習問題: ★★

次の命題の証明を示すオブジェクトを作成しなさい。
-}
conj-fact : ∀ {x y z} {P : Set x} {Q : Set y} {R : Set z} → P × Q → Q × R → P × R
conj-fact (p , _) (_ , r) = (p , r)

---- Iff （両含意） -----------------------------------------------------------
infix 3 _↔_

_↔_ : ∀ {x y} → Set x → Set y → Set (x ⊔ y)
P ↔ Q = (P → Q) × (Q → P)

iff-implies : ∀ {x y} {P : Set x} {Q : Set y} → P ↔ Q → P → Q
iff-implies = proj₁

iff-sym : ∀ {x y} {P : Set x} {Q : Set y} → P ↔ Q → Q ↔ P
iff-sym (x₁ , x₂) = x₂ , x₁

{-
練習問題: ★ (iff_properties)

上の、 ↔ が対称であることを示す証明 (iff_sym) を使い、それが反射的で あること、推移的であることを証明しなさい。
-}
iff-refl : ∀ {x} {P : Set x} → P ↔ P
iff-refl = iff-sym ((λ x → x) , (λ x → x))

iff-trans : ∀ {x y z} {P : Set x} {Q : Set y} {R : Set z} → P ↔ Q → Q ↔ R → P ↔ R
iff-trans (x₁ , x₂) (x₃ , x₄) = iff-sym (x₂ ∘ x₄ , x₃ ∘ x₁)

{-
練習問題: ★★ (MyProp_iff_ev)

ここまで、MyProp や ev が これらの命題がある種の数値を特徴づける（偶数、などの） ことを見てきました。 次の MyProp n ↔ ev n が任意の nで成り立つことを証明しなさい。 お遊びのつもりでかまわないので、その証明を、単純明快な証明、タクティックを 使わないにような証明に書き換えてください。（ヒント：以前に使用した定理をうまく 使えば、１行だけでかけるはずです！）
-}
MyProp-iff-ev : ∀ n → MyProp n ↔ ev n
MyProp-iff-ev n = ev-MyProp n , MyProp-ev n

-- 論理和、選言（Disjunction、OR） --------------------------------------------

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

or-commut : ∀ {x y} {P : Set x} {Q : Set y} → P ⊎ Q → Q ⊎ P
or-commut (inj₁ x₁) = inj₂ x₁
or-commut (inj₂ x₁) = inj₁ x₁

{-
練習問題: ★★ optional (or_commut'')

or_commut の証明オブジェクトの型がどのようになるか、書き出してみて ください。（ただし、定義済みの証明オブジェクトを Print を使って 見てみたりしないこと。）
-}
-- 略

or-distributes-over-and-1 : ∀ {x y z} {P : Set x} {Q : Set y} {R : Set z} →
                            P ⊎ (Q × R) → (P ⊎ Q) × (P ⊎ R)
or-distributes-over-and-1 (inj₁ x₁) = inj₁ x₁ , inj₁ x₁
or-distributes-over-and-1 (inj₂ (x₁ , x₂)) = inj₂ x₁ , inj₂ x₂

{-
練習問題: ★★, recommended (or_distributes_over_and_2)
-}
or-distributes-over-and-2 : ∀ {x y z} {P : Set x} {Q : Set y} {R : Set z} →
                            (P ⊎ Q) × (P ⊎ R) → P ⊎ (Q × R)
or-distributes-over-and-2 (x₁ , inj₁ x₂) = inj₁ x₂
or-distributes-over-and-2 (inj₁ x₁ , inj₂ x₂) = inj₁ x₁
or-distributes-over-and-2 (inj₂ x₁ , inj₂ x₂) = inj₂ (x₁ , x₂)

{-
練習問題: ★ (or_distributes_over_and)
-}
or-distributes-over-and : ∀ {x y z} {P : Set x} {Q : Set y} {R : Set z} →
                          (P ⊎ (Q × R)) ↔ ((P ⊎ Q) × (P ⊎ R))
or-distributes-over-and = or-distributes-over-and-1 , or-distributes-over-and-2

---- ∧ 、 ∨ のandb 、orb への関連付け -----------------------------------------
andb-true-and : ∀ b c → andb b c ≡ true → b ≡ true × c ≡ true
andb-true-and true true eq = refl , refl
andb-true-and true false eq = refl , eq
andb-true-and false true eq = eq , refl
andb-true-and false false eq = eq , eq

and-andb-true : ∀ b c → b ≡ true × c ≡ true → andb b c ≡ true
and-andb-true true true eq = refl
and-andb-true true false (x , x₁) = x₁
and-andb-true false true (x , x₁) = x
and-andb-true false false (x , x₁) = x₁

{-
練習問題: ★ (bool_prop)
-}
andb-false : ∀ b c → andb b c ≡ false → (b ≡ false) ⊎ (c ≡ false)
andb-false true true eq = inj₁ eq
andb-false true false eq = inj₂ refl
andb-false false c eq = inj₁ refl

orb-true : ∀ b c → orb b c ≡ true → (b ≡ true) ⊎ (c ≡ true)
orb-true true c eq = inj₁ refl
orb-true false true eq = inj₂ refl
orb-true false false eq = inj₁ eq

orb-false : ∀ b c → orb b c ≡ false → (b ≡ false) × (c ≡ false)
orb-false true true eq = eq , eq
orb-false true false eq = eq , refl
orb-false false c eq = refl , eq

-- 偽であるということ ---------------------------------------------------------

-- AgdaだとData.Emptyの⊥だね，普通はそっちをimportして使う
data False : Set where

False-implies-nonsense : False → 2 + 2 ≡ 5
False-implies-nonsense ()

nonsense-implies-False : 2 + 2 ≡ 5 → False
nonsense-implies-False ()

ex-falso-quodlibet : ∀ {x} (P : Set x) → False → P
ex-falso-quodlibet P ()

---- 真であるということ -------------------------------------------------------

{-
練習問題: ★★ (True_induction)

True を、帰納的な命題として定義しなさい。あなたの定義に対してCoqはどのような 帰納的原理を生成してくれるでしょうか。 （直観的には True はただ当たり前のように 根拠を示される命題であるべきです。代わりに、帰納的原理から帰納的な定義を逆に たどっていくほうが近道だと気づくかもしれません。）
-}
-- AgdaだとData.Unitの⊤だね
record True : Set where
  constructor tt

-- 否定 -----------------------------------------------------------------------

infix 3 ~_

~_ : ∀ {x} → Set x → Set x
~ P = P → False

not-False : ~ False
not-False = λ z → z

contradiction-implies-anything : ∀ {x y} {P : Set x} {Q : Set y} →
                                 (P × (~ P)) → Q
contradiction-implies-anything {Q = Q} (x₁ , x₂) = ex-falso-quodlibet Q (x₂ x₁)

double-neg : ∀ {x} {P : Set x} → P → ~ (~ P)
double-neg p = λ z → z p

{-
練習問題: ★★, recommended (double_neg_inf)

double_neg の非形式的な証明を書きなさい。
-}
-- 略

{-
練習問題: ★★, recommended (contrapositive)
-}
contrapositive : ∀ {x y} {P : Set x} {Q : Set y} → (P → Q) → ((~ Q) → (~ P))
contrapositive z z₁ z₂ = z₁ (z z₂)

{-
練習問題: ★ (not_both_true_and_false)
-}
not-both-true-and-false : ∀ {x} {P : Set x} → ~ (P × (~ P))
not-both-true-and-false (x₁ , x₂) = x₂ x₁


five-not-even : ~ ev 5
five-not-even (ev-SS (ev-SS ()))

{-
練習問題: ★ ev_not_ev_S

定理 five_not_even は、「５は偶数ではない」というようなとても当たり前の 事実を確認するものです。今度はもう少し面白い例です。
-}
ev-not-ev-S : ∀ n → ev n → ~ ev (S n)
ev-not-ev-S .(S n) evn (ev-SS {n} evSn) = ev-not-ev-S n evSn evn

{-
練習問題: ★ (informal_not_PNP)

命題 ∀ P : Prop, ~(P ∧ ~P) の形式的でない証明を（英語で）書きなさい。
-}
-- 着

postulate
  classic-double-neg : ∀ {x} {P : Set x} → ~ (~ P) → P

{-
練習問題: ★★★★★, optional (classical_axioms)

さらなる挑戦を求める人のために、 Coq'Art book (p. 123) から一つ練習問題を 取り上げてみます。次の五つの文は、よく「古典論理の特性」と考えられている もの（Coqにビルトインされている構成的論理の対極にあるもの）です。 これらをCoqで証明することはできませんが、古典論理を使うことが必要なら、 矛盾なく「証明されていない公理」として道具に加えることができます。 これら五つの命題が等価であることを証明しなさい。
-}
{-
postulate
  peirce : ∀ {x y} {P : Set x} {Q : Set y} → ((P → Q) → P) → P
  classic : ∀ {x} {P : Set x} → ~ (~ P) → P
  excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
  de-morgan-not-and-not : ∀ {x y} {P : Set x} {Q : Set y} → ~ ((~ P) × (~ Q)) → P ⊎ Q
  implies_to_or : ∀ {x y} {P : Set x} {Q : Set y} → (P → Q) → ((~ P) ⊎ Q)
-}
either : ∀ {x y z} {P : Set x} {Q : Set y} {R : Set z} → (P → R) → (Q → R) → P ⊎ Q → R
either P→R Q→R (inj₁ p) = P→R p
either P→R Q→R (inj₂ q) = Q→R q

excluded-middle→classic : ∀ {x} {P : Set x} → ~ (~ P) → P
excluded-middle→classic {P = P} ~~P = either (λ p → p) (ex-falso-quodlibet P ∘ ~~P) excluded-middle
  where
    postulate
      excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P

classic→excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
classic→excluded-middle {P = P} = classic (λ z → z (inj₂ (z ∘ inj₁)))
  where
    postulate
      classic : ∀ {x} {P : Set x} → ~ (~ P) → P

excluded-middle→peirce : ∀ {x y} {P : Set x} {Q : Set y} → ((P → Q) → P) → P
excluded-middle→peirce {P = P} {Q} pp = either (λ p → p) (λ ~p → pp (ex-falso-quodlibet Q ∘ ~p)) excluded-middle
  where
    postulate
      excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P

peirce→excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
peirce→excluded-middle = peirce (λ z → inj₂ (λ x → z (inj₁ x)))
  where
    postulate
      peirce : ∀ {x y} {P : Set x} {Q : Set y} → ((P → Q) → P) → P

excluded-middle→implies_to_or : ∀ {x y} {P : Set x} {Q : Set y} → (P → Q) → ((~ P) ⊎ Q)
excluded-middle→implies_to_or {P = P} {Q} pq = either (inj₂ ∘ pq) inj₁ excluded-middle
  where
    postulate
      excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P

implies_to_or→excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
implies_to_or→excluded-middle = or-commut $ implies_to_or (λ z → z)
  where
    postulate
      implies_to_or : ∀ {x y} {P : Set x} {Q : Set y} → (P → Q) → ((~ P) ⊎ Q)

de-morgan-not-and-not→classic : ∀ {x} {P : Set x} → ~ (~ P) → P
de-morgan-not-and-not→classic {P = P} ~~P = either (λ z → z) (λ z → z) $
                                            de-morgan-not-and-not (~~P ∘ proj₁)
  where
    postulate
      de-morgan-not-and-not : ∀ {x y} {P : Set x} {Q : Set y} → ~ ((~ P) × (~ Q)) → P ⊎ Q

classic→de-morgan-not-and-not : ∀ {x y} {P : Set x} {Q : Set y} → ~ ((~ P) × (~ Q)) → P ⊎ Q
classic→de-morgan-not-and-not = classic ∘ contrapositive (λ z → (z ∘ inj₁ , z ∘ inj₂))
  where
    postulate
      classic : ∀ {x} {P : Set x} → ~ (~ P) → P

---- 不等であるということ -----------------------------------------------------

_≢_ : ∀ {a} {A : Set a} → A → A → Set a
x ≢ y = ~ (x ≡ y)

not-false-then-true : (b : bool) → b ≢ false → b ≡ true
not-false-then-true b b≢f = either (λ z → z) (ex-falso-quodlibet (b ≡ true) ∘ b≢f) (b≡t⊎b≡f b)
  where
    b≡t⊎b≡f : ∀ b → b ≡ true ⊎ b ≡ false
    b≡t⊎b≡f true = inj₁ refl
    b≡t⊎b≡f false = inj₂ refl

{-
練習問題: ★★, recommended (not_eq_beq_false)
-}
not-eq-beq-false : (n n' : nat) → n ≢ n' → beq-nat n n' ≡ false
not-eq-beq-false O O n≢n' = ex-falso-quodlibet (beq-nat O O ≡ false) (n≢n' refl)
not-eq-beq-false O (S n') n≢n' = refl
not-eq-beq-false (S n) O n≢n' = refl
not-eq-beq-false (S n) (S n') n≢n' = not-eq-beq-false n n' (n≢n' ∘ cong S)

{-
練習問題: ★★, optional (beq_false_not_eq)
-}
beq-false-not-eq : (n m : nat) → false ≡ beq-nat n m → n ≢ m
beq-false-not-eq O O ()
beq-false-not-eq O (S m) eq = λ ()
beq-false-not-eq (S n) O eq = λ ()
beq-false-not-eq (S n) (S m) eq = beq-false-not-eq n m eq ∘ eq-add-S

-- 存在量化子 -----------------------------------------------------------------

data ∃ {x y} {X : Set x} (P : X → Set y) : Set (x ⊔ y) where
  ex-intro : (witness : X) → P witness → ∃ P

some-nat-is-even : ∃ λ n → ev n
some-nat-is-even = ex-intro 4 (ev-SS (ev-SS ev-0))

-- 標準ライブラリの∃使うのがいいけどね．
-- open import Data.Product using (∃)

exists-example-1 : ∃ λ n → n + (n * n) ≡ 6
exists-example-1 = ex-intro 2 refl

-- 標準ライブラリの∃使った場合は，
-- open import Data.Product using (∃)
-- exists-example-1 : ∃ λ n → n + (n * n) ≡ 6
-- exists-example-1 = 2 , refl
-- と，(満たす値 ，根拠) の組が証明オブジェクト
-- だから "Data.Product" に入っている．

exists-example-2 : ∀ n → (∃ λ m → n ≡ 4 + m) → (∃ λ o → n ≡ 2 + o)
--exists-example-2 n H = ? として，c-c c-c H
--exists-example-2 n (ex-intro witness x) = ? になるので c-c c-aで終わり
exists-example-2 n (ex-intro witness x) = ex-intro (S (S witness)) x

{-
練習問題: ★ (english_exists)

英語では、以下の命題は何を意味しているでしょうか？
      ex nat (fun n => ev (S n))
-}
-- 略
{-
次の証明オブジェクトの定義を完成させなさい
-}
p : ∃ λ n → ev (S n)
p = ex-intro 1 (ev-SS ev-0)

{-
練習問題: ★ (dist_not_exists)

"全ての x についてP が成り立つ" ということと " P を満たさない x は 存在しない" ということが等価であることを証明しなさい。
-}
dist-not-exists : ∀ {x y} (X : Set x) (P : X → Set y) →
                  (∀ x → P x) → ~ (∃ λ x → ~ P x)
dist-not-exists X P fa (ex-intro witness x₁) = x₁ (fa witness)

{-
練習問題: ★★★, optional (not_exists_dist)

一方、古典論理の「排中律（law of the excluded middle）」が必要とされる 場合もあります。
-}
not-exists-dist : ∀ {x y} (X : Set x) (P : X → Set y) →
                  ~ (∃ λ x → ~ P x) → (∀ x → P x)
not-exists-dist X P ~ex a = either (λ z → z) (ex-falso-quodlibet (P a) ∘ ~ex ∘ ex-intro a) (excluded-middle {P = P a})
  where
    postulate
      excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
{-
練習問題: ★★ (dist_exists_or)

存在量化子が論理和において分配法則を満たすことを証明しなさい。
-}
dist-exists-or : ∀ {x y} (X : Set x) (P Q : X → Set y) →
                 (∃ λ x → P x ⊎ Q x) ↔ ((∃ λ x → P x) ⊎ (∃ λ x → Q x))
dist-exists-or X P Q = left , right
  where
    left : (∃ λ x → P x ⊎ Q x) → ((∃ λ x → P x) ⊎ (∃ λ x → Q x))
    left (ex-intro witness (inj₁ x)) = inj₁ (ex-intro witness x)
    left (ex-intro witness (inj₂ x)) = inj₂ (ex-intro witness x)
    right : ((∃ λ x → P x) ⊎ (∃ λ x → Q x)) → (∃ λ x → P x ⊎ Q x)
    right (inj₁ (ex-intro witness x)) = ex-intro witness (inj₁ x)
    right (inj₂ (ex-intro witness x)) = ex-intro witness (inj₂ x)

-- 等しいということ（同値性） -------------------------------------------------
module MyEquality where

  data eq {a} {A : Set a} : A → A → Set a where
    refl-equal : ∀ x → eq x x

  -- Agda標準ライブラリの_≡_もこっちだね
  data eq' {a} {X : Set a} (x : X) : X → Set a where
    refl-equal' : eq' x x

  {-
  練習問題: ★★★, optional (two_defs_of_eq_coincide)

  これら二つの定義が等価であることを確認しなさい。
  -}
  two-defs-of-eq-coincide : ∀ {a} (X : Set a) (x y : X) →
                            eq x y ↔ eq' x y
  two-defs-of-eq-coincide X x y = left x y , right x y
    where
      left : (x y : X) → eq x y → eq' x y
      left .y₁ y₁ (refl-equal .y₁) = refl-equal'
      right : (x y : X) → eq' x y → eq x y
      right .y₁ y₁ refl-equal' = refl-equal y₁

  four : eq (2 + 2) (1 + 3)
  four = refl-equal 4

---- Inversion 再び -----------------------------------------------------------

-- 命題としての関係 -----------------------------------------------------------
module LeFirstTry where

  data _≤_ : nat → nat → Set where
    le-n : ∀ n → n ≤ n
    le-S : ∀ n m → n ≤ m → n ≤ (S m)

infix 4 _≤_

data _≤_ (n : nat) : nat → Set where
  le-n : n ≤ n
  le-S : ∀ {m} → n ≤ m → n ≤ S m

test-le1 : 3 ≤ 3
test-le1 = le-n

test-le2 : 3 ≤ 6
test-le2 = le-S (le-S (le-S le-n))

test-le3 : ~ (2 ≤ 1)
test-le3 (le-S ())

infix 4 _<_

_<_ : ∀ n m → Set
n < m = S n ≤ m

data square-of : nat → nat → Set where
  sq : ∀ n → square-of n (n * n)

data next-nat (n : nat) : nat → Set where
  nn : next-nat n (S n)

data next-even (n : nat) : nat → Set where
  ne-1 : ev (S n) → next-even n (S n)
  ne-2 : ev (S (S n)) → next-even n (S (S n))

{-
練習問題: ★★, recommended (total_relation)

二つの自然数のペア同士の間に成り立つ帰納的な関係 total_relation を 定義しなさい。
-}
-- ? どういうこと ?

{-
練習問題: ★★ (empty_relation)

自然数の間では決して成り立たない関係 empty_relation を帰納的に 定義しなさい。
-}
-- ? なんでもいいの ?

{-
練習問題: ★★★, recommended (R_provability)

次は三つや四つの値の間に成り立つ関係を同じように定義してみましょう。 例えば、次のような数値の三項関係が考えられます。
-}
module R where
  data R : nat → nat → nat → Set where
    c1 : R 0 0 0
    c2 : ∀ {m n o} → R m n o → R (S m) n (S o)
    c3 : ∀ {m n o} → R m n o → R m (S n) (S o)
    c4 : ∀ {m n o} → R (S m) (S n) (S (S o)) → R m n o
    c5 : ∀ {m n o} → R m n o → R n m o

{-
次の命題のうち、この関係を満たすと証明できると言えるのはどれでしょうか。
-}
-- R 1 1 2
  test1 : R 1 1 2
  test1 = c2 (c3 c1)
-- Rはn+m=oと保つため． R 2 2 6 を満たす証明オブジェクトは作れない．
{-
この関係 R の定義からコンストラクタ c5 を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。
-}
-- 変わらない．
{-
この関係 R の定義からコンストラクタ c4 を取り除くと、証明可能な命題の範囲はどのように変わるでしょうか？端的に（１文で）説明しなさい。
-}
-- 変わらない．

{-
練習問題: ★★★, optional (R_fact)

関係 R の、等値性に関する特性をあげ、それを証明しなさい。 それは、 もし R m n o が true なら m についてどんなことが言えるでしょうか？ n や o についてはどうでしょうか？その逆は？
-}
  R-fact : ∀ m n o → R m n o ↔ m + n ≡ o
  R-fact m n o = left m n o , right m n o
    where
      left : ∀ m n o → R m n o → m + n ≡ o
      left .0 .0 .0 c1 = refl
      left .(S m₁) n₁ .(S o₁) (c2 {m₁} {.n₁} {o₁} Rmno)
        rewrite left m₁ n₁ o₁ Rmno
              = refl
      left m₁ .(S n₁) .(S o₁) (c3 {.m₁} {n₁} {o₁} Rmno)
        rewrite sym (left m₁ n₁ o₁ Rmno)
              | plus-assoc m₁ 1 n₁
              | plus-comm m₁ 1
              = refl
      left m₁ n₁ o₁ (c4 Rmno) =
        eq-add-S $ eq-add-S (sym (cong (S ∘ S) (plus-comm n₁ m₁)) ⟨ trans ⟩
                             sym (cong S (plus-comm m₁ (S n₁))) ⟨ trans ⟩
                             left (S m₁) (S n₁) (S (S o₁)) Rmno)
      left m₁ n₁ o₁ (c5 Rmno)
        rewrite plus-comm m₁ n₁
              | left n₁ m₁ o₁ Rmno
              = refl
      right : ∀ m n o → m + n ≡ o → R m n o
      right O O .0 refl = c1
      right O (S n₁) .(S n₁) refl = c3 (right 0 n₁ n₁ refl)
      right (S m₁) n₁ .(S (plus m₁ n₁)) refl = c2 (right m₁ n₁ (m₁ + n₁) refl)

{-
練習問題: ★★★, recommended (all_forallb)

リストに関する属性 all を定義しなさい。それは、型 X と属性 P : X → Prop をパラメータとし、 all X P l が「リスト l の全ての要素が 属性 P} を満たす」とするものです。
-}
data all {a} {X : Set a} (P : X → Set a) : list X → Set a where
  all-nil : all P []
  all-cons : ∀ x xs → P x → all P xs → all P (x ∷ xs)

all-forallb : ∀ {X : Set} (xs : list X) test →
              all (λ x → test x ≡ true) xs ↔ forallb test xs ≡ true
all-forallb xs test = left xs test , right xs test
  where
    left : ∀ {X : Set} (xs : list X) test →
           all (λ x → test x ≡ true) xs → forallb test xs ≡ true
    left .[] test all-nil = refl
    left .(x ∷ xs) test (all-cons x xs Px all)
      rewrite Px
            | left xs test all
            = refl
    right : ∀ {X : Set} (xs : list X) test →
            forallb test xs ≡ true → all (λ x → test x ≡ true) xs
    right [] test₁ fa = all-nil
    right (x ∷ xs₁) test₁ fa = all-cons x xs₁ (proj₁ assert) (right xs₁ test₁ (proj₂ assert))
      where
        assert = andb-true-and (test₁ x) (forallb test₁ xs₁) fa

{-
練習問題: ★★★★, optional (filter_challenge)

Coq の主な目的の一つは、プログラムが特定の仕様を満たしていることを 証明することです。それがどういうことか、filter 関数の定義が仕様を満たすか証明 してみましょう。まず、その関数の仕様を非形式的に書き出してみます。

集合 X と関数 test: X→bool、リストl とその型 list X を想定する。 さらに、l が二つのリスト l1 と l2 が順序を維持したままマージされたもので、 リスト l1 の要素はすべて test を満たし、 l2 の要素はすべて満たさないと すると、filter test l = l1 が成り立つ。

課題は、この仕様をCoq の定理の形に書き直し、それを証明することです。 （ヒント：まず、一つのりすとが二つのリストをマージしたものとなっている、 ということを示す定義を書く必要がありますが、これは帰納的な関係であって、 Fixpoint で書くようなものではありません。）
-}
data merge {a} {X : Set a} : list X → list X → list X → Set a where
  merge-nil : merge [] [] []
  merge-cons1 : ∀ x as bs xs → merge as bs xs → merge (x ∷ as) bs (x ∷ xs)
  merge-cons2 : ∀ x as bs xs → merge as bs xs → merge as (x ∷ bs) (x ∷ xs)

filter-challenge : ∀ {X : Set} (l1 l2 ls : list X) test →
                   merge l1 l2 ls →
                   all (λ x → test x ≡ true) l1 →
                   all (λ x → test x ≡ false) l2 →
                   filter test ls ≡ l1
filter-challenge .[] .[] .[] test merge-nil al1 al2 = refl
filter-challenge .(x ∷ as) l2 .(x ∷ xs) test (merge-cons1 x as .l2 xs m) (all-cons .x .as Px al1) al2
  rewrite Px
        | filter-challenge as l2 xs test m al1 al2
        = refl
filter-challenge l1 .(x ∷ bs) .(x ∷ xs) test (merge-cons2 x .l1 bs xs m) al1 (all-cons .x .bs Px al2)
  rewrite Px
        | filter-challenge l1 bs xs test m al1 al2
        = refl

{-
練習問題: ★★★★★, optional (filter_challenge_2)

filter の振る舞いに関する特性を別の切り口で表すとこうなります。 「test の結果が true なる要素だけでできた、リスト l の すべての部分リストの中で、filter test l が最も長いリストである。」 これを形式的に記述し、それを証明しなさい。
-}
data sublist {a} {X : Set a}: list X → list X → Set a where
  sublist-nil : sublist [] []
  sublist-seq : ∀ {ss xs} x → sublist ss xs → sublist ss (x ∷ xs)
  sublist-both : ∀ {ss xs} x → sublist ss xs → sublist (x ∷ ss) (x ∷ xs)

filter-challenge-2 : ∀ {X : Set} (ls ss : list X) test →
                     all (λ x → test x ≡ true) ls →
                     sublist ss ls →
                     length ss ≤ length (filter test ls)
filter-challenge-2 .[] .[] test all sublist-nil = le-n
filter-challenge-2 .(x ∷ xs) ss test (all-cons .x .xs Px all) (sublist-seq {.ss} {xs} x sub)
  rewrite Px
        = le-S (filter-challenge-2 xs ss test all sub)
filter-challenge-2 .(x ∷ xs) .(x ∷ ss) test (all-cons .x .xs Px all) (sublist-both {ss} {xs} x sub)
  rewrite Px
        = n≤m→Sn≤Sm (filter-challenge-2 xs ss test all sub)
  where
    n≤m→Sn≤Sm : ∀ {n m} → n ≤ m → S n ≤ S m
    n≤m→Sn≤Sm le-n = le-n
    n≤m→Sn≤Sm (le-S n≤m) = le-S (n≤m→Sn≤Sm n≤m)

{-
練習問題: ★★★★, optional (no_repeats)

次の、帰納的に定義された命題を見て、

Inductive appears_in {X:Type} (a:X) : list X → Prop :=
  | ai_here : ∀ l, appears_in a (a::l)
  | ai_later : ∀ b l, appears_in a l → appears_in a (b::l).

値 a が、少なくとも一度はリスト l の中に現れるということを、 厳密に表現する方法を考えなさい。
-}
data appears-in {x} {X : Set x} (a : X) : list X → Set x where
  ai-here : ∀ ls → appears-in a (a ∷ ls)
  ai-later : ∀ b ls → appears-in a ls → appears-in a (b ∷ ls)
{-
appears_in に関するウォームアップ問題としてもう一つ、
-}
appears-in-app : ∀ {a} {X : Set a} (xs ys : list X) (x : X) →
                 appears-in x (xs ++ ys) → appears-in x xs ⊎ appears-in x ys
appears-in-app [] .(x ∷ ls) x (ai-here ls) = inj₂ (ai-here ls)
appears-in-app [] .(b ∷ ls) x (ai-later b ls appin) = inj₂ (ai-later b ls appin)
appears-in-app (x ∷ xs) ys .x (ai-here .(xs ++ ys)) = inj₁ (ai-here xs)
appears-in-app (x ∷ xs) ys x₁ (ai-later .x .(xs ++ ys) appin) with appears-in-app xs ys x₁ appin
appears-in-app (x₂ ∷ xs) ys x₁ (ai-later .x₂ .(xs ++ ys) appin) | inj₁ x = inj₁ (ai-later x₂ xs x)
appears-in-app (x₂ ∷ xs) ys x₁ (ai-later .x₂ .(xs ++ ys) appin) | inj₂ x = inj₂ x

app-appears-in : ∀ {a} {X : Set a} (xs ys : list X) (x : X) →
                 appears-in x xs ⊎ appears-in x ys → appears-in x (xs ++ ys)
app-appears-in .(x ∷ ls) ys x (inj₁ (ai-here ls)) = ai-here (ls ++ ys)
app-appears-in .(b ∷ ls) ys x (inj₁ (ai-later b ls in-xs)) = ai-later b (ls ++ ys) (app-appears-in ls ys x (inj₁ in-xs))
app-appears-in [] .(x ∷ ls) x (inj₂ (ai-here ls)) = ai-here ls
app-appears-in (x ∷ xs) .(x₁ ∷ ls) x₁ (inj₂ (ai-here ls)) = ai-later x (xs ++ x₁ ∷ ls) (app-appears-in xs (x₁ ∷ ls) x₁ (inj₂ (ai-here ls)))
app-appears-in [] .(b ∷ ls) x (inj₂ (ai-later b ls in-ys)) = ai-later b ls in-ys
app-appears-in (x ∷ xs) .(b ∷ ls) x₁ (inj₂ (ai-later b ls in-ys)) = ai-later x (xs ++ b ∷ ls) (app-appears-in xs (b ∷ ls) x₁ (inj₂ (ai-later b ls in-ys)))

{-
では、 appears_in を使って命題 disjoint X l1 l2 を定義してください。 これは、型 X の二つのリスト l1 、 l2 が共通の要素を持たない場合 にのみ証明可能な命題です。
-}
disjoint : ∀ {a} {X : Set a} (l1 l2 : list X) → Set a
disjoint l1 l2 = ∀ x → (appears-in x l1 → ~ appears-in x l2) × (appears-in x l2 → ~ appears-in x l1)

{-
次は、 appears_in を使って帰納的な命題 no_repeats X l を定義して ください。これは, 型 X のリスト l の中のどの要素も、他の要素と 異なっている場合のみ証明できるような命題です。例えば、 no_repeats nat [1,2,3,4] や no_repeats bool [] は証明可能ですが、 no_repeats nat [1,2,1] や no_repeats bool [true,true] は証明 できないようなものです。
-}
no-repeats : ∀ {a} {X : Set a} (ls : list X) → Set a
no-repeats {X = X} [] = X
no-repeats (x ∷ ls) = (~ appears-in x ls) × no-repeats ls

{-
最後に、disjoint、 no_repeats、 ++ （リストの結合）の三つを使った、 何か面白い定理を考えて、それを証明してください。
-}
no-repeats-disjoint-is-no-repeats : ∀ {a} {X : Set a} (xs ys : list X) →
                                    no-repeats xs →
                                    no-repeats ys →
                                    disjoint xs ys →
                                    no-repeats (xs ++ ys)
no-repeats-disjoint-is-no-repeats [] ys nr-xs nr-ys disj = nr-ys
no-repeats-disjoint-is-no-repeats {X = X} (x ∷ xs) ys nr-xs nr-ys disj = (left ∘ appears-in-app xs ys x) , right
  where
    left : appears-in x xs ⊎ appears-in x ys → False
    left (inj₁ x₁) = proj₁ nr-xs x₁
    left (inj₂ x₁) = proj₁ (disj x) (ai-here xs) x₁
    right : no-repeats (xs ++ ys)
    right = no-repeats-disjoint-is-no-repeats xs ys (proj₂ nr-xs) nr-ys (λ x₁ → (λ x₂ x₃ → proj₁ (disj x₁) (ai-later x xs x₂) x₃) , (λ x₂ x₃ → proj₁ (disj x₁) (ai-later x xs x₃) x₂))

---- 少し脱線: <= と < についてのさらなる事実 ---------------------------------

{-
練習問題: ★★, optional (le_exercises)
-}
0≤n : ∀ n → 0 ≤ n
0≤n O = le-n
0≤n (S n) = le-S (0≤n n)

n≤m→Sn≤Sm : ∀ n m → n ≤ m → S n ≤ S m
n≤m→Sn≤Sm .m m le-n = le-n
n≤m→Sn≤Sm n .(S m) (le-S {m} n≤m) = le-S (n≤m→Sn≤Sm n m n≤m)

Sn≤Sm→n≤m : ∀ n m → S n ≤ S m → n ≤ m
Sn≤Sm→n≤m .m m le-n = le-n
Sn≤Sm→n≤m n O (le-S ())
Sn≤Sm→n≤m n (S m) (le-S Sn≤Sm) = le-S (Sn≤Sm→n≤m n m Sn≤Sm)

a≤a+b : ∀ a b → a ≤ a + b
a≤a+b a O
  rewrite n+O≡n a
        = le-n
a≤a+b a (S b)
  rewrite plus-comm a (S b)
        | plus-comm b a
        = le-S (a≤a+b a b)

n<m→n≤m : ∀ n m → n < m → n ≤ m
n<m→n≤m n .(S n) le-n = le-S le-n
n<m→n≤m n .(S m) (le-S {m} n<m) = le-S (n<m→n≤m n m n<m)

plus-lt : ∀ n1 n2 m → n1 + n2 < m → n1 < m × n2 < m
plus-lt = λ n1 n2 m n1+n2<m → left n1 n2 m n1+n2<m , right n1 n2 m n1+n2<m
  where
    left : ∀ n1 n2 m → n1 + n2 < m → n1 < m
    left n1 O m n1+n2<m
      rewrite n+O≡n n1
            = n1+n2<m
    left n1 (S n2) m n1+n2<m
      rewrite plus-comm n1 (S n2)
            | plus-comm n2 n1
            = left n1 n2 m (n<m→n≤m (S (plus n1 n2)) m n1+n2<m)
    right : ∀ n1 n2 m → n1 + n2 < m → n2 < m
    right O n2 m n1+n2<m = n1+n2<m
    right (S n1) n2 m n1+n2<m = right n1 n2 m (n<m→n≤m (S (plus n1 n2)) m n1+n2<m)

n<m→n<Sm : ∀ n m → n < m → n < S m
n<m→n<Sm n .(S n) le-n = le-S le-n
n<m→n<Sm n .(S m) (le-S {m} n<m) = le-S (n<m→n<Sm n m n<m)

ble-nat-true : ∀ n m → ble-nat n m ≡ true → n ≤ m
ble-nat-true O m ble = 0≤n m
ble-nat-true (S n) O ()
ble-nat-true (S n) (S m) ble = n≤m→Sn≤Sm n m (ble-nat-true n m ble)

≤→ble-nat-true : ∀ n m → n ≤ m → ble-nat n m ≡ true
≤→ble-nat-true .m m le-n = sym (ble-nat-refl m)
≤→ble-nat-true O .(S m) (le-S {m} n≤m) = refl
≤→ble-nat-true (S n) .(S m) (le-S {m} n≤m) = ≤→ble-nat-true n m (Sn≤Sm→n≤m n m (le-S n≤m))

ble-nat-n-Sn-false : ∀ n m → ble-nat n (S m) ≡ false → ble-nat n m ≡ false
ble-nat-n-Sn-false O m ble = ble
ble-nat-n-Sn-false (S n) O ble = refl
ble-nat-n-Sn-false (S n) (S m) ble = ble-nat-n-Sn-false n m ble

ble-nat-false : ∀ n m → ble-nat n m ≡ false → ~ (n ≤ m)
ble-nat-false O m ()
ble-nat-false (S n) O ble = λ ()
ble-nat-false (S n) (S m) ble = ble-nat-false n m ble ∘ Sn≤Sm→n≤m n m
