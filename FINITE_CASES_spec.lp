require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3197566 [A] : Prf (∀ (λ a : El (fun A bool), (= ((@FINITE A) a) (∨ (= a (@EMPTY A)) (∃ (λ x : El A, (∃ (λ s : El (fun A bool), (∧ (= a ((@INSERT A) x s)) ((@FINITE A) s))))))))));
