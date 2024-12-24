require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem528181 : Prf (∧ (∀ (λ n : El num, (= (SUC (BIT0 n)) (BIT1 n)))) (∀ (λ n : El num, (= (SUC (BIT1 n)) (BIT0 (SUC n))))));
