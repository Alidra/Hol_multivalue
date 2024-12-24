require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 ≔ (∀ (λ y0 : El (type686 a0), (⇒ (∧ (y0 (@EMPTY a0)) (∀ (λ y1 : El a0, (∀ (λ y2 : El (fun a0 bool), (⇒ (y0 y2) (y0 ((@INSERT a0) y1 y2)))))))) (∀ (λ y1 : El (fun a0 bool), (⇒ ((@FINITE a0) y1) (y0 y1)))))));
