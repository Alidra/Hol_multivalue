require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term0 (x0: El bool) ≔ (⇒ (¬ x0) F);
symbol term2 a0 (x0: El num) ≔ (⇒ (¬ (⇒ ((@HAS_SIZE a0) (@UNIV a0) x0) (= ((@dimindex a0) (@UNIV a0)) x0))) F);
symbol term1 a0 (x0: El num) ≔ (⇒ ((@HAS_SIZE a0) (@UNIV a0) x0) (= ((@dimindex a0) (@UNIV a0)) x0));
