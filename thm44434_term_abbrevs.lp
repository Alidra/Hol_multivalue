require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (type1413 a0 a1)) ≔ ((@REP_prod a0 a1) ((@ABS_prod a0 a1) x0));
symbol term2 a0 a1 (x0: El (type1413 a0 a1)) ≔ (∃ (λ y0 : El a0, (∃ (λ y1 : El a1, (= x0 ((@mk_pair a0 a1) y0 y1))))));
symbol term0 a0 a1 (x0: El (type1413 a0 a1)) ≔ ((λ y0 : El (type1413 a0 a1), (∃ (λ y1 : El a0, (∃ (λ y2 : El a1, (= y0 ((@mk_pair a0 a1) y1 y2))))))) x0);
symbol term4 a0 a1 (x0: El (type1413 a0 a1)) ≔ ((@= bool) (∃ (λ y0 : El a0, (∃ (λ y1 : El a1, (= x0 ((@mk_pair a0 a1) y0 y1)))))));
symbol term3 a0 a1 (x0: El (type1413 a0 a1)) ≔ ((@= bool) ((λ y0 : El (type1413 a0 a1), (∃ (λ y1 : El a0, (∃ (λ y2 : El a1, (= y0 ((@mk_pair a0 a1) y1 y2))))))) x0));
