require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9121 [A B] : Prf (∀ (λ t : El (fun A B), (= (λ x : El A, (t x)) t)));
