require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6990944 [A] : Prf (∀ (λ P : El (fun A bool), (∀ (λ s : El (fun A bool), (∀ (λ f : El (fun A num), (= ((@nsum A) ((@GSPEC A) (λ GEN_PVAR_287 : El A, (∃ (λ x : El A, ((@SETSPEC A) GEN_PVAR_287 (∧ ((@IN A) x s) (P x)) x))))) f) ((@nsum A) s (λ x : El A, ((@COND num) (P x) (f x) (NUMERAL _0)))))))))));
