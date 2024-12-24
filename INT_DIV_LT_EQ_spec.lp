require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2611267 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∀ (λ c : El int, (⇒ (int_lt (int_of_num (NUMERAL _0)) a) (= (int_lt (div b a) c) (int_lt b (int_mul a c))))))))));
