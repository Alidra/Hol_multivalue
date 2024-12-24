require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_type_abbrevs;
require open hol-light.hol_terms;
symbol term2 ≔ (⇒ ((@HAS_SIZE 1) (@UNIV 1) (NUMERAL (BIT1 _0))) (= ((@dimindex 1) (@UNIV 1)) (NUMERAL (BIT1 _0))));
symbol term1 (x0: El num) ≔ (⇒ ((@HAS_SIZE 1) (@UNIV 1) x0) (= ((@dimindex 1) (@UNIV 1)) x0));
symbol term0 a0 (x0: El num) ≔ (⇒ ((@HAS_SIZE a0) (@UNIV a0) x0) (= ((@dimindex a0) (@UNIV a0)) x0));
symbol term3 ≔ (NUMERAL (BIT1 _0));
