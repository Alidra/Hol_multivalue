require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3112880 : Prf (∀ (λ n : El num, (∀ (λ d : El num, (∀ (λ e : El num, (⇒ (∧ (num_divides d n) (⇒ (= n (NUMERAL _0)) (= e (NUMERAL _0)))) (= (num_divides (DIV n d) e) (num_divides n (* d e))))))))));
