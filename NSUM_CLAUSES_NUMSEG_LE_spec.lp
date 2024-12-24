require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7047542 (f : El (fun num num)) : Prf (∧ (= ((@nsum num) ((@GSPEC num) (λ GEN_PVAR_306 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_306 (<= i (NUMERAL _0)) i))))) f) (f (NUMERAL _0))) (∀ (λ k : El num, (= ((@nsum num) ((@GSPEC num) (λ GEN_PVAR_307 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_307 (<= i (SUC k)) i))))) f) (+ ((@nsum num) ((@GSPEC num) (λ GEN_PVAR_308 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_308 (<= i k) i))))) f) (f (SUC k)))))));
