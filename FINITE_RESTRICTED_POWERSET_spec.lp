require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4617672 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ n : El num, (= ((@FINITE (fun A bool)) ((@GSPEC (fun A bool)) (λ GEN_PVAR_174 : El (fun A bool), (∃ (λ t : El (fun A bool), ((@SETSPEC (fun A bool)) GEN_PVAR_174 (∧ ((@SUBSET A) t s) ((@HAS_SIZE A) t n)) t)))))) (∨ ((@FINITE A) s) (= n (NUMERAL _0))))))));
