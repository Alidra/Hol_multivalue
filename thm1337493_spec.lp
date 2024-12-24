require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1337493 (r : El (fun (prod hreal hreal) bool)) : Prf (= (∃ (λ x : El (prod hreal hreal), (= r (treal_eq x)))) (= (dest_real (mk_real r)) r));
