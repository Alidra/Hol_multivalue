require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4597289 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ n : El num, (⇒ ((@HAS_SIZE A) s n) ((@HAS_SIZE (fun A bool)) ((@GSPEC (fun A bool)) (λ GEN_PVAR_153 : El (fun A bool), (∃ (λ t : El (fun A bool), ((@SETSPEC (fun A bool)) GEN_PVAR_153 ((@SUBSET A) t s) t))))) (EXP (NUMERAL (BIT0 (BIT1 _0))) n)))))));
