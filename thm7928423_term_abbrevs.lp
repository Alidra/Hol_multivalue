require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 (x0: El (type1329 a0)) (x1: El (type39 a0)) (x2: El (type6 a0)) ≔ ((λ y0 : El (type6 a0), (x0 (x1 y0))) x2);
symbol term0 a0 (x0: El (type39 a0)) ≔ (λ y0 : El (type1675 a0), (∀ (λ y1 : El (type1329 a0), (⇒ (∀ (λ y2 : El (type1675 a0), (⇒ (∃ (λ y3 : El (type6 a0), (= y2 (x0 y3)))) (y1 y2)))) (y1 y0)))));
symbol term2 a0 (x0: El (type1329 a0)) (x1: El (type39 a0)) (x2: El (type6 a0)) ≔ (x0 (x1 x2));
