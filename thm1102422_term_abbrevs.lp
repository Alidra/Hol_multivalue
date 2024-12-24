require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (∀ (λ y0 : El a1, (∀ (λ y1 : El (type1467 a0 a1), (∀ (λ y2 : El (list a1), (∀ (λ y3 : El a0, (= ((@ITLIST a0 a1) y1 ((@CONS a1) y0 y2) y3) (y1 y0 ((@ITLIST a0 a1) y1 y2 y3)))))))))));
