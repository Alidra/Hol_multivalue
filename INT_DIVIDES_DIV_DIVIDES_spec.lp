require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem2737101 : Prf (∀ (λ n : El int, (∀ (λ d : El int, (∀ (λ e : El int, (⇒ (∧ (int_divides d n) (⇒ (= n (int_of_num (NUMERAL _0))) (= e (int_of_num (NUMERAL _0))))) (= (int_divides (div n d) e) (int_divides n (int_mul d e))))))))));
