require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El (recspace a0)) (x1: El (type1338 a0)) (x2: El (type1432 a0)) ≔ (∧ (x1 x0) (∀ (λ y0 : El a0, (x1 (x2 y0)))));
symbol term0 a0 (x0: El (recspace a0)) (x1: El (type1432 a0)) ≔ (λ y0 : El (recspace a0), (∀ (λ y1 : El (type1338 a0), (⇒ (∀ (λ y2 : El (recspace a0), (⇒ (∨ (= y2 x0) (∃ (λ y3 : El a0, (= y2 (x1 y3))))) (y1 y2)))) (y1 y0)))));
