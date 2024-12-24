require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3465181 [A] : Prf (∀ (λ P : El (fun A bool), (= ((@UNIONS A) ((@GSPEC (fun A bool)) (λ GEN_PVAR_61 : El (fun A bool), (∃ (λ x : El A, ((@SETSPEC (fun A bool)) GEN_PVAR_61 (P x) ((@INSERT A) x (@EMPTY A)))))))) ((@GSPEC A) (λ GEN_PVAR_62 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_62 (P x) x))))))));
