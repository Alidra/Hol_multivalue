require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 (x0: El (type24 a0 a1)) (x1: El (type24 a0 a2)) (x2: El (type16 a0 a1 a2)) ≔ (∃ (λ y0 : El (type2 a0 a1 a2), (∧ ((@IN (cart a0 (finite_sum a1 a2))) y0 ((@PCROSS a0 a1 a2) x0 x1)) (x2 y0))));
symbol term1 a0 a1 a2 (x0: El (type24 a0 a1)) (x1: El (type24 a0 a2)) (x2: El (type16 a0 a1 a2)) ≔ (∃ (λ y0 : El (cart a0 a1), (∃ (λ y1 : El (cart a0 a2), (∧ ((@IN (cart a0 a1)) y0 x0) (∧ ((@IN (cart a0 a2)) y1 x1) (x2 ((@pastecart a0 a1 a2) y0 y1))))))));
