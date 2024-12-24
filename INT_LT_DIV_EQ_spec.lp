require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2611645 : Prf (∀ (λ a : El int, (∀ (λ b : El int, (∀ (λ c : El int, (⇒ (int_lt (int_of_num (NUMERAL _0)) a) (= (int_lt c (div b a)) (int_le (int_mul a (int_add c (int_of_num (NUMERAL (BIT1 _0))))) b)))))))));
