require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1073843 [A] : Prf (∀ (λ a : El A, (∀ (λ a' : El A, (= (= ((@SOME A) a) ((@SOME A) a')) (= a a'))))));
