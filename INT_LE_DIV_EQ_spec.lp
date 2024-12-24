require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2611393 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∀ (λ c : El int, (⇒ (int_lt (int_of_num (NUMERAL _0)) a) (= (int_le c (div b a)) (int_le (int_mul a c) b)))))))));
