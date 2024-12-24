require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∧ (NUM_REP IND_0) (∀ (λ y0 : El ind, (⇒ (NUM_REP y0) (NUM_REP (IND_SUC y0))))));
