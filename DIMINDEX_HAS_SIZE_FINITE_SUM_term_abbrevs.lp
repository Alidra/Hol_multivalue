require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 a0 a1 ≔ ((@HAS_SIZE (finite_sum a0 a1)) (@UNIV (finite_sum a0 a1)) (+ ((@dimindex a0) (@UNIV a0)) ((@dimindex a1) (@UNIV a1))));
