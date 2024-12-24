require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El type1539) ≔ (λ y0 : El type1678, (∀ (λ y1 : El type1335, (⇒ (∀ (λ y2 : El type1678, (⇒ (∃ (λ y3 : El bool, (∃ (λ y4 : El bool, (∃ (λ y5 : El bool, (∃ (λ y6 : El bool, (∃ (λ y7 : El bool, (∃ (λ y8 : El bool, (∃ (λ y9 : El bool, (∃ (λ y10 : El bool, (= y2 (x0 y3 y4 y5 y6 y7 y8 y9 y10)))))))))))))))))) (y1 y2)))) (y1 y0)))));
symbol term1 (x0: El type1539) (x1: El type1335) ≔ (∀ (λ y0 : El type1335, (⇒ (∀ (λ y1 : El bool, (∀ (λ y2 : El bool, (∀ (λ y3 : El bool, (∀ (λ y4 : El bool, (∀ (λ y5 : El bool, (∀ (λ y6 : El bool, (∀ (λ y7 : El bool, (∀ (λ y8 : El bool, (y0 (x0 y1 y2 y3 y4 y5 y6 y7 y8)))))))))))))))))) (∀ (λ y1 : El type1678, (⇒ (x1 y1) (y0 y1)))))));
