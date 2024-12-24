require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ (λ y0 : El a0, (λ y1 : El (type1413 a0 a1), ((@COND a1) ((@∃! a1) (y1 y0)) ((@ε a1) (y1 y0)) ((@ε a1) (λ y2 : El a1, F)))));
