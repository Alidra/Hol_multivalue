require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El a0, (∀ (λ y1 : El (type1402 a0), (∀ (λ y2 : El (list a0), (= ((@PAIRWISE a0) y1 ((@CONS a0) y0 y2)) (∧ ((@ALL a0) (y1 y0) y2) ((@PAIRWISE a0) y1 y2)))))))));
