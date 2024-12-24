require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4118304 [A] : Prf (∀ (λ s : El (fun A bool), (= (∧ ((@FINITE A) s) (<= ((@CARD A) s) (NUMERAL (BIT1 _0)))) (∃ (λ a : El A, ((@SUBSET A) s ((@INSERT A) a (@EMPTY A))))))));
