require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∀ (λ y0 : El (fun num real), (∀ (λ y1 : El (fun num real), (∀ (λ y2 : El num, (∀ (λ y3 : El num, (⇒ (∀ (λ y4 : El num, (⇒ (∧ (<= y2 y4) (<= y4 y3)) (= (y0 y4) (y1 y4))))) (= ((@sum num) (… y2 y3) (λ y4 : El num, (y0 y4))) ((@sum num) (… y2 y3) y1)))))))))));
