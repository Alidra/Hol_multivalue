require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term4 (x0: El (fun real bool)) ≔ ((λ y0 : El (fun real bool), (= (inf y0) ((@ε real) (λ y1 : El real, (∧ (∀ (λ y2 : El real, (⇒ ((@IN real) y2 y0) (real_le y1 y2)))) (∀ (λ y2 : El real, (⇒ (∀ (λ y3 : El real, (⇒ ((@IN real) y3 y0) (real_le y2 y3)))) (real_le y2 y1))))))))) x0);
symbol term3 ≔ (∀ (λ y0 : El (fun real bool), (= (inf y0) ((@ε real) (λ y1 : El real, (∧ (∀ (λ y2 : El real, (⇒ ((@IN real) y2 y0) (real_le y1 y2)))) (∀ (λ y2 : El real, (⇒ (∀ (λ y3 : El real, (⇒ ((@IN real) y3 y0) (real_le y2 y3)))) (real_le y2 y1))))))))));
symbol term0 ≔ (λ y0 : El (fun real bool), ((@ε real) (λ y1 : El real, (∧ (∀ (λ y2 : El real, (⇒ ((@IN real) y2 y0) (real_le y1 y2)))) (∀ (λ y2 : El real, (⇒ (∀ (λ y3 : El real, (⇒ ((@IN real) y3 y0) (real_le y2 y3)))) (real_le y2 y1))))))));
symbol term2 (x0: El (fun real bool)) ≔ ((@ε real) (λ y0 : El real, (∧ (∀ (λ y1 : El real, (⇒ ((@IN real) y1 x0) (real_le y0 y1)))) (∀ (λ y1 : El real, (⇒ (∀ (λ y2 : El real, (⇒ ((@IN real) y2 x0) (real_le y1 y2)))) (real_le y1 y0)))))));
symbol term1 (x0: El (fun real bool)) ≔ ((λ y0 : El (fun real bool), ((@ε real) (λ y1 : El real, (∧ (∀ (λ y2 : El real, (⇒ ((@IN real) y2 y0) (real_le y1 y2)))) (∀ (λ y2 : El real, (⇒ (∀ (λ y3 : El real, (⇒ ((@IN real) y3 y0) (real_le y2 y3)))) (real_le y2 y1)))))))) x0);
