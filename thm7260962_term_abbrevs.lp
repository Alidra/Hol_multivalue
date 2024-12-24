require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 (x0: El (fun a0 bool)) (x1: El (fun a0 real)) (x2: El (fun a0 real)) ≔ (∀ (λ y0 : El a0, (⇒ ((@IN a0) y0 x0) (= (x1 y0) (x2 y0)))));
