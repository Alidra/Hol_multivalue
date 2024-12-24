require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (type1470 a0 a1)) (x1: El a1) (x2: El (type1470 a0 a1)) ≔ ((@COND a0) (∃ (λ y0 : El a0, (x0 x1 y0))) ((@_MATCH a1 a0) x1 x0) ((@_MATCH a1 a0) x1 x2));
symbol term0 a0 a1 (x0: El a1) (x1: El (type1470 a0 a1)) (x2: El (type1470 a0 a1)) ≔ ((@_MATCH a1 a0) x0 ((@_SEQPATTERN a0 a1) x1 x2));
