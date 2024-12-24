require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3193179 [A] : Prf (∀ (λ s : El (fun A bool), (∀ (λ x : El A, (= ((@DELETE A) s x) ((@GSPEC A) (λ GEN_PVAR_6 : El A, (∃ (λ y : El A, ((@SETSPEC A) GEN_PVAR_6 (∧ ((@IN A) y s) (¬ (= y x))) y))))))))));
