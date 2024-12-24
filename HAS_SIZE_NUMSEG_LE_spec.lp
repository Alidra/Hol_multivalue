require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4621936 : Prf (∀ (λ n : El num, ((@HAS_SIZE num) ((@GSPEC num) (λ GEN_PVAR_188 : El num, (∃ (λ m : El num, ((@SETSPEC num) GEN_PVAR_188 (<= m n) m))))) (+ n (NUMERAL (BIT1 _0))))));
