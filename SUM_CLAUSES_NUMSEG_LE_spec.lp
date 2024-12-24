require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7221987 (f : El (fun num real)) : Prf (∧ (= ((@sum num) ((@GSPEC num) (λ GEN_PVAR_337 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_337 (<= i (NUMERAL _0)) i))))) f) (f (NUMERAL _0))) (∀ (λ k : El num, (= ((@sum num) ((@GSPEC num) (λ GEN_PVAR_338 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_338 (<= i (SUC k)) i))))) f) (real_add ((@sum num) ((@GSPEC num) (λ GEN_PVAR_339 : El num, (∃ (λ i : El num, ((@SETSPEC num) GEN_PVAR_339 (<= i k) i))))) f) (f (SUC k)))))));
