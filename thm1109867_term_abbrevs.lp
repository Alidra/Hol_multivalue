require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∀ (λ y0 : El a1, (∀ (λ y1 : El (type1470 a0 a1), (∀ (λ y2 : El (list a1), (∀ (λ y3 : El (list a0), (= ((@ALLPAIRS a0 a1) y1 ((@CONS a1) y0 y2) y3) (∧ ((@ALL a0) (y1 y0) y3) ((@ALLPAIRS a0 a1) y1 y2 y3)))))))))));
