require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4621860 : Prf (∧ (= ((@GSPEC num) (λ GEN_PVAR_185 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_185 (<= i (NUMERAL _0)) i))))) ((@INSERT num) (NUMERAL _0) (@EMPTY num))) (∀ (λ k : El num, (= ((@GSPEC num) (λ GEN_PVAR_186 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_186 (<= i (SUC k)) i))))) ((@INSERT num) (SUC k) ((@GSPEC num) (λ GEN_PVAR_187 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_187 (<= i k) i))))))))));
