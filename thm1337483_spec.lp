require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1337483 (x : El (prod hreal hreal)) : Prf ((λ s : El (fun (prod hreal hreal) bool), (∃ (λ x' : El (prod hreal hreal), (= s (treal_eq x'))))) (treal_eq x));
