require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4333570 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (= ((@INFINITE (prod A B)) ((@CROSS B A) s t)) (∨ (∧ (¬ (= s (@EMPTY A))) ((@INFINITE B) t)) (∧ ((@INFINITE A) s) (¬ (= t (@EMPTY B))))))))));
