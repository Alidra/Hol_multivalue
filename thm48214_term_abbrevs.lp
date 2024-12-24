require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 (x0: El a0) (x1: El a1) ≔ ((λ y0 : El a1, (= ((@SND a0 a1) ((@̦‚ a0 a1) x0 y0)) y0)) x1);
symbol term1 a0 a1 (x0: El a0) (x1: El a1) ≔ ((@SND a0 a1) ((@̦‚ a0 a1) x0 x1));
