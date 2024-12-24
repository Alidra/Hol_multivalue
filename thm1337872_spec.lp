require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1337872 (x1 : El (prod hreal hreal)) (y1 : El (prod hreal hreal)) : Prf (= (real_mul (mk_real (treal_eq x1)) (mk_real (treal_eq y1))) (mk_real (treal_eq (treal_mul x1 y1))));
