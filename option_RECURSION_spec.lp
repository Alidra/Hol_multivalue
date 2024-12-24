require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1070449 [A Z] : Prf (∀ (λ NONE' : El Z, (∀ (λ SOME' : El (fun A Z), (∃ (λ fn : El (fun (option A) Z), (∧ (= (fn (@NONE A)) NONE') (∀ (λ a : El A, (= (fn ((@SOME A) a)) (SOME' a)))))))))));
