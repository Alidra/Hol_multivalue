require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4600502 [A] : Prf (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) s) (= ((@CARD (fun A bool)) ((@GSPEC (fun A bool)) (λ GEN_PVAR_154 : El (fun A bool), (∃ (λ t : El (fun A bool), ((@SETSPEC (fun A bool)) GEN_PVAR_154 ((@SUBSET A) t s) t)))))) (EXP (NUMERAL (BIT0 (BIT1 _0))) ((@CARD A) s))))));
