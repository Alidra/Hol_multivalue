require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1317734 (x : El nadd) : Prf ((λ s : El (fun nadd bool), (∃ (λ x' : El nadd, (= s (nadd_eq x'))))) (nadd_eq x));
