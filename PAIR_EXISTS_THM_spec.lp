require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem44416 [A B] : Prf (∃ (λ x : El (fun A (fun B bool)), (∃ (λ a : El A, (∃ (λ b : El B, (= x ((@mk_pair A B) a b))))))));
