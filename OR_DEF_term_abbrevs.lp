require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (λ y0 : El bool, (λ y1 : El bool, (∀ (λ y2 : El bool, (⇒ (⇒ y0 y2) (⇒ (⇒ y1 y2) y2))))));
