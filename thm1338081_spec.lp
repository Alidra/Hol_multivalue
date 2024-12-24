require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1338081 (x : El (prod hreal hreal)) : Prf (= (= (real_inv (mk_real (treal_eq x))) (mk_real (treal_eq (treal_inv x)))) (= (mk_real (treal_eq (treal_inv x))) (real_inv (mk_real (treal_eq x)))));
