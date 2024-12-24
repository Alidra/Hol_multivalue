require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1338112 (x : El (prod hreal hreal)) (y : El (prod hreal hreal)) : Prf ((λ y' : El (prod hreal hreal), (= (treal_eq x y') (= (mk_real (treal_eq x)) (mk_real (treal_eq y'))))) y);
