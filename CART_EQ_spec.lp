require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7617066 [A B] : Prf (∀ (λ x : El (cart A B), (∀ (λ y : El (cart A B), (= (= x y) (∀ (λ i : El num, (⇒ (∧ (<= (NUMERAL (BIT1 _0)) i) (<= i ((@dimindex B) (@UNIV B)))) (= ((@﹩ A B) x i) ((@﹩ A B) y i))))))))));
