require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4330214 [A B] : Prf (∀ (λ s : El (fun A bool), (∀ (λ t : El (fun B bool), (= ((@FINITE (prod A B)) ((@CROSS B A) s t)) (∨ (= s (@EMPTY A)) (∨ (= t (@EMPTY B)) (∧ ((@FINITE A) s) ((@FINITE B) t)))))))));
