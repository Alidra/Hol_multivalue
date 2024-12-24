require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5490796 : Prf (∀ (λ n : El num, (= ((@GSPEC num) (λ GEN_PVAR_232 : El num, (∃ (λ x : El num, ((@SETSPEC num) GEN_PVAR_232 (< x n) x))))) ((@COND (fun num bool)) (= n (NUMERAL _0)) (@EMPTY num) (… (NUMERAL _0) (- n (NUMERAL (BIT1 _0))))))));
