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
excluded-middle→peirce : ∀ {x y} {P : Set x} {Q : Set y} → ((P → Q) → P) → P
excluded-middle→peirce {P = P} {Q} pp = assert excluded-middle
  where
    postulate
      excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
    assert : P ⊎ ~ P → P
    assert (inj₁ p) = p
    assert (inj₂ ¬p) = pp (ex-falso-quodlibet Q ∘ ¬p)

peirce→excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
peirce→excluded-middle = peirce (λ z → inj₂ (λ x → z (inj₁ x)))
  where
    postulate
      peirce : ∀ {x y} {P : Set x} {Q : Set y} → ((P → Q) → P) → P

excluded-middle→implies_to_or : ∀ {x y} {P : Set x} {Q : Set y} → (P → Q) → ((~ P) ⊎ Q)
excluded-middle→implies_to_or {P = P} {Q} pq = assert excluded-middle
  where
    postulate
      excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
    assert : P ⊎ ~ P → ((~ P) ⊎ Q)
    assert (inj₁ p) = inj₂ (pq p)
    assert (inj₂ ¬p) = inj₁ ¬p

implies_to_or→excluded-middle : ∀ {x} {P : Set x} → P ⊎ ~ P
implies_to_or→excluded-middle {P = P} = or-commut $ implies_to_or {P = P} {P} (λ z → z)
  where
    postulate
      implies_to_or : ∀ {x y} {P : Set x} {Q : Set y} → (P → Q) → ((~ P) ⊎ Q)
