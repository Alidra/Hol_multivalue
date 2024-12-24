require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem523716 : Prf (∧ (= (EVEN _0) T) (∧ (∀ (λ n : El num, (= (EVEN (BIT0 n)) T))) (∀ (λ n : El num, (= (EVEN (BIT1 n)) F)))));
