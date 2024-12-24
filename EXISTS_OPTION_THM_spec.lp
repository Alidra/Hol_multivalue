require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1073365 [A] : Prf (∀ (λ P : El (fun (option A) bool), (= (∃ (λ x : El (option A), (P x))) (∨ (P (@NONE A)) (∃ (λ a : El A, (P ((@SOME A) a))))))));
