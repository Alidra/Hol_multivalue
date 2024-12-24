require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El (fun num bool)) ≔ ((λ y0 : El (fun num bool), (= (∃ (λ y1 : El num, (y0 y1))) (∃ (λ y1 : El num, (∧ (y0 y1) (∀ (λ y2 : El num, (⇒ (< y2 y1) (¬ (y0 y2)))))))))) x0);
