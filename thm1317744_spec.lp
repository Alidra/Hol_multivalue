require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1317744 (r : El (fun nadd bool)) : Prf (= (∃ (λ x : El nadd, (= r (nadd_eq x)))) (= (dest_hreal (mk_hreal r)) r));
