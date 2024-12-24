require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (∀ (λ y0 : El (fun ind bool), (⇒ (∧ (y0 IND_0) (∀ (λ y1 : El ind, (⇒ (y0 y1) (y0 (IND_SUC y1)))))) (∀ (λ y1 : El ind, (⇒ (NUM_REP y1) (y0 y1))))))) (∀ (λ y0 : El ind, (= (NUM_REP y0) (∨ (= y0 IND_0) (∃ (λ y1 : El ind, (∧ (= y0 (IND_SUC y1)) (NUM_REP y1)))))))));
