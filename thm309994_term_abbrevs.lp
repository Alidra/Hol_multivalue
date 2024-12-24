require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El (type1413 a0 a1)) ≔ ((λ y0 : El (type1413 a0 a1), (= (∀ (λ y1 : El a0, (∃ (λ y2 : El a1, (y0 y1 y2))))) (∃ (λ y1 : El (fun a0 a1), (∀ (λ y2 : El a0, (y0 y2 (y1 y2)))))))) x0);
