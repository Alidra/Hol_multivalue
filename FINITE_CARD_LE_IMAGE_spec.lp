require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4010101 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ s : El (fun A bool), (∀ (λ n : El num, (⇒ (∧ ((@FINITE A) s) (<= ((@CARD A) s) n)) (∧ ((@FINITE B) ((@IMAGE A B) f s)) (<= ((@CARD B) ((@IMAGE A B) f s)) n)))))))));
