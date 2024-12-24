require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El (prod hreal hreal), (∀ (λ y1 : El (prod hreal hreal), (= (treal_eq y0 y1) (= (mk_real (treal_eq y0)) (mk_real (treal_eq y1))))))));
symbol term2 (x0: El (prod hreal hreal)) ≔ (∀ (λ y0 : El (prod hreal hreal), (= (treal_eq x0 y0) (= (mk_real (treal_eq x0)) (mk_real (treal_eq y0))))));
symbol term3 (x0: El (prod hreal hreal)) (x1: El (prod hreal hreal)) ≔ ((λ y0 : El (prod hreal hreal), (= (treal_eq x0 y0) (= (mk_real (treal_eq x0)) (mk_real (treal_eq y0))))) x1);
symbol term1 (x0: El (prod hreal hreal)) ≔ ((λ y0 : El (prod hreal hreal), (∀ (λ y1 : El (prod hreal hreal), (= (treal_eq y0 y1) (= (mk_real (treal_eq y0)) (mk_real (treal_eq y1))))))) x0);
