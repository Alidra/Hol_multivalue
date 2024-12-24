require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1587738 : Prf (∀ (λ x : El real, (∀ (λ y : El real, (⇒ (= (real_mul x y) (real_of_num (NUMERAL (BIT1 _0)))) (= (real_inv y) x))))));
