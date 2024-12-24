require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El (type1413 a0 a1), (∀ (λ y2 : El (list a0), (∀ (λ y3 : El (list a1), (= ((@ALL2 a0 a1) y1 ((@CONS a0) y0 y2) y3) ((@COND bool) (= y3 (@NIL a1)) F (∧ (y1 y0 ((@HD a1) y3)) ((@ALL2 a0 a1) y1 y2 ((@TL a1) y3)))))))))))));
