require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 a2 a3 (x0: El a3) (x1: El a2) ≔ ((λ y0 : El a2, (= ((@CASEWISE a0 a1 a2 a3) (@NIL (prod (fun a1 a2) (fun a3 (fun a1 a0)))) x0 y0) ((@ε a0) (λ y1 : El a0, T)))) x1);
symbol term1 a0 ≔ ((@ε a0) (λ y0 : El a0, T));
