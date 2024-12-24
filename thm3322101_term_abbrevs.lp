require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term1 a0 ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 ((@UNIONS a0) (@EMPTY (fun a0 bool)))) ((@IN a0) y0 (@EMPTY a0)))));
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 bool)) ≔ (∀ (λ y0 : El a0, (= ((@IN a0) y0 x0) ((@IN a0) y0 x1))));
