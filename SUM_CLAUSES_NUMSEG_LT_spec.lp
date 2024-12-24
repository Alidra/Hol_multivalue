require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7221862 (f : El (fun num real)) : Prf (∧ (= ((@sum num) ((@GSPEC num) (λ GEN_PVAR_334 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_334 (< i (NUMERAL _0)) i))))) f) (real_of_num (NUMERAL _0))) (∀ (λ k : El num, (= ((@sum num) ((@GSPEC num) (λ GEN_PVAR_335 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_335 (< i (SUC k)) i))))) f) (real_add ((@sum num) ((@GSPEC num) (λ GEN_PVAR_336 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_336 (< i k) i))))) f) (f k))))));
