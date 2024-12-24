require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 a1 (x0: El (type1333 a0 a1)) (x1: El (type1431 a0 a1)) ≔ (∀ (λ y0 : El a0, (x0 (x1 y0))));
symbol term2 a0 a1 (x0: El (type1333 a0 a1)) (x1: El (type1431 a0 a1)) (x2: El a0) ≔ ((λ y0 : El a0, (x0 (x1 y0))) x2);
symbol term3 a0 a1 (x0: El (type1333 a0 a1)) (x1: El (type1431 a0 a1)) (x2: El a0) ≔ (x0 (x1 x2));
symbol term0 a0 a1 (x0: El (type1431 a0 a1)) (x1: El (type1479 a0 a1)) ≔ (λ y0 : El (type1677 a0 a1), (∀ (λ y1 : El (type1333 a0 a1), (⇒ (∀ (λ y2 : El (type1677 a0 a1), (⇒ (∨ (∃ (λ y3 : El a0, (= y2 (x0 y3)))) (∃ (λ y3 : El a1, (= y2 (x1 y3))))) (y1 y2)))) (y1 y0)))));
