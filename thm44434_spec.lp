require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem44434 [A B] (r : El (fun A (fun B bool))) : Prf (= (∃ (λ a : El A, (∃ (λ b : El B, (= r ((@mk_pair A B) a b)))))) (= ((@REP_prod A B) ((@ABS_prod A B) r)) r));
