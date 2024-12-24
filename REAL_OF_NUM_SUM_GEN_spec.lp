require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7210021 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ ((@FINITE A) ((@GSPEC A) (λ GEN_PVAR_333 : El A, (∃ (λ i : El A, ((@SETSPEC A) GEN_PVAR_333 (∧ ((@IN A) i s) (¬ (= (f i) (NUMERAL _0)))) i)))))) (= (real_of_num ((@nsum A) s f)) ((@sum A) s (λ x : El A, (real_of_num (f x))))))))));
