require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El num) ≔ (∀ (λ y0 : El num, (= (… x0 (SUC y0)) ((@COND (fun num bool)) (<= x0 (SUC y0)) ((@INSERT num) (SUC y0) (… x0 y0)) (… x0 y0)))));
