require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 (x0: El nadd) ≔ (λ y0 : El num, (DIV (* y0 y0) (dest_nadd x0 y0)));
symbol term3 ≔ (∀ (λ y0 : El nadd, (= (nadd_rinv y0) (λ y1 : El num, (DIV (* y1 y1) (dest_nadd y0 y1))))));
symbol term1 (x0: El nadd) ≔ ((λ y0 : El nadd, (λ y1 : El num, (DIV (* y1 y1) (dest_nadd y0 y1)))) x0);
symbol term4 (x0: El nadd) ≔ ((λ y0 : El nadd, (= (nadd_rinv y0) (λ y1 : El num, (DIV (* y1 y1) (dest_nadd y0 y1))))) x0);
symbol term0 ≔ (λ y0 : El nadd, (λ y1 : El num, (DIV (* y1 y1) (dest_nadd y0 y1))));
