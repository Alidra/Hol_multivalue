require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (type45 a0)) ≔ (λ y0 : El (type1676 a0), (∀ (λ y1 : El (type1331 a0), (⇒ (∀ (λ y2 : El (type1676 a0), (⇒ (∃ (λ y3 : El (finite_sum a0 a0), (= y2 (x0 y3)))) (y1 y2)))) (y1 y0)))));
symbol term1 a0 (x0: El (type45 a0)) (x1: El (type1331 a0)) ≔ (∀ (λ y0 : El (type1331 a0), (⇒ (∀ (λ y1 : El (finite_sum a0 a0), (y0 (x0 y1)))) (∀ (λ y1 : El (type1676 a0), (⇒ (x1 y1) (y0 y1)))))));
