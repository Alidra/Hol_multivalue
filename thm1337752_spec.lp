require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1337752 (x1 : El (prod hreal hreal)) (y1 : El (prod hreal hreal)) : Prf (= (= (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq y1))) (mk_real (treal_eq (treal_add x1 y1)))) (= (mk_real (treal_eq (treal_add x1 y1))) (real_add (mk_real (treal_eq x1)) (mk_real (treal_eq y1)))));
