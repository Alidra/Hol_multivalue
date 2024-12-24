require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 (x0: El (fun num bool)) ≔ ((λ y0 : El (fun num bool), ((@ε num) (λ y1 : El num, (∧ (y0 y1) (∀ (λ y2 : El num, (⇒ (< y2 y1) (¬ (y0 y2))))))))) x0);
symbol term2 (x0: El (fun num bool)) ≔ ((@ε num) (λ y0 : El num, (∧ (x0 y0) (∀ (λ y1 : El num, (⇒ (< y1 y0) (¬ (x0 y1))))))));
symbol term3 ≔ (∀ (λ y0 : El (fun num bool), (= (minimal y0) ((@ε num) (λ y1 : El num, (∧ (y0 y1) (∀ (λ y2 : El num, (⇒ (< y2 y1) (¬ (y0 y2)))))))))));
symbol term0 ≔ (λ y0 : El (fun num bool), ((@ε num) (λ y1 : El num, (∧ (y0 y1) (∀ (λ y2 : El num, (⇒ (< y2 y1) (¬ (y0 y2)))))))));
symbol term4 (x0: El (fun num bool)) ≔ ((λ y0 : El (fun num bool), (= (minimal y0) ((@ε num) (λ y1 : El num, (∧ (y0 y1) (∀ (λ y2 : El num, (⇒ (< y2 y1) (¬ (y0 y2)))))))))) x0);
