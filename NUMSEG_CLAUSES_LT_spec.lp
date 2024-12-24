require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4621002 : Prf (∧ (= ((@GSPEC num) (λ GEN_PVAR_179 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_179 (< i (NUMERAL _0)) i))))) (@EMPTY num)) (∀ (λ k : El num, (= ((@GSPEC num) (λ GEN_PVAR_180 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_180 (< i (SUC k)) i))))) ((@INSERT num) k ((@GSPEC num) (λ GEN_PVAR_181 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_181 (< i k) i))))))))));
