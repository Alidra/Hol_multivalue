require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7047417 (f : El (fun num num)) : Prf (∧ (= ((@nsum num) ((@GSPEC num) (λ GEN_PVAR_303 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_303 (< i (NUMERAL _0)) i))))) f) (NUMERAL _0)) (∀ (λ k : El num, (= ((@nsum num) ((@GSPEC num) (λ GEN_PVAR_304 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_304 (< i (SUC k)) i))))) f) (+ ((@nsum num) ((@GSPEC num) (λ GEN_PVAR_305 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_305 (< i k) i))))) f) (f k))))));
