require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 ≔ (∃ (λ y0 : El (fun ind ind), (∧ ((@ONE_ONE ind ind) y0) (¬ ((@ONTO ind ind) y0)))));
