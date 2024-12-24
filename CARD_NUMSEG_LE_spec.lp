require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4622061 : Prf (∀ (λ n : El num, (= ((@CARD num) ((@GSPEC num) (λ GEN_PVAR_190 : El num, (∃ (λ m : El num, ((@SETSPEC num) GEN_PVAR_190 (<= m n) m)))))) (+ n (NUMERAL (BIT1 _0))))));
