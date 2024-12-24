require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1337622 (x1 : El (prod hreal hreal)) : Prf (= (real_neg (mk_real (treal_eq x1))) (mk_real (treal_eq (treal_neg x1))));
