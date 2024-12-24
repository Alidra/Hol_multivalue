require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El bool) ≔ (⇒ (¬ x0) F);
symbol term2 a0 a1 a2 (x0: El (type16 a0 a1 a2)) ≔ (∀ (λ y0 : El (cart a0 a1), (∀ (λ y1 : El (cart a0 a2), (x0 ((@pastecart a0 a1 a2) y0 y1))))));
symbol term1 a0 a1 a2 (x0: El (type16 a0 a1 a2)) ≔ (∀ (λ y0 : El (type2 a0 a1 a2), (x0 y0)));
symbol term3 a0 a1 a2 (x0: El (type16 a0 a1 a2)) ≔ (⇒ (¬ (= (∀ (λ y0 : El (type2 a0 a1 a2), (x0 y0))) (∀ (λ y0 : El (cart a0 a1), (∀ (λ y1 : El (cart a0 a2), (x0 ((@pastecart a0 a1 a2) y0 y1)))))))) F);
